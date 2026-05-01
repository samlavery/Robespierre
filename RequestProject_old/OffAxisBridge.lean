import Mathlib
import RequestProject.OffAxisTheoremDefs
import RequestProject.OffAxisTheorem

/-! # Off-Axis Bridge API

A simple, unconditional API for querying the rotated density detector on
sets of candidate zeta zeros. No hypothesis about `riemannZeta` is needed
for any of the detector results — the detector is purely geometric, testing
whether `ρ.re = 1/2` via rotation symmetry.

## Terminology

* **online** — a complex number with `ρ.re = 1/2` (on the critical line).
* **offline** — a complex number with `ρ.re ≠ 1/2`.
* **conspiring** — a subset of offline points that might evade other
  detection methods. The detector still fires on them geometrically,
  but these methods alone cannot prove the subset is empty.

## Main results

* `bridge_all_online` — detector silent on a fully online set.
* `bridge_offline_detected` — detector fires if any element is offline.
* `bridge_partition` — given online/offline partition, fires iff offline nonempty.
* `bridge_monotone` — detector firing is monotone under set inclusion.
* `bridge_conspiracy_detected` — conspiring offline zeros still fire the
  detector; the detector is blind to *why* a zero is offline.
* `bridge_conspiracy_limitation` — the detector cannot distinguish an
  all-online set from an empty one; it gives no information about *which*
  zeros are offline, only *that* some are.
-/

open ArithmeticFunction Real

noncomputable section

/-- Off-line nontrivial zeros: those with `Re(s) ≠ 1/2`. -/

def NontrivialZeros : Set ℂ :=
  { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }

def OffLineZeros : Set ℂ :=
  { s ∈ NontrivialZeros | s.re ≠ 1 / 2 }
/-! ## Predicates for online/offline membership -/

/-- A complex number is **online** (on the critical line). -/
def IsOnline (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- A complex number is **offline** (off the critical line). -/
def IsOffline (ρ : ℂ) : Prop := ρ.re ≠ 1 / 2

theorem isOnline_iff (ρ : ℂ) : IsOnline ρ ↔ ρ.re = 1 / 2 := Iff.rfl
theorem isOffline_iff (ρ : ℂ) : IsOffline ρ ↔ ρ.re ≠ 1 / 2 := Iff.rfl
theorem isOffline_iff_not_isOnline (ρ : ℂ) : IsOffline ρ ↔ ¬ IsOnline ρ := Iff.rfl

/-! ## Core bridge: detector ↔ existence of offline element -/

/-- **The fundamental bridge**: the detector fires on `S` if and only if
    `S` contains at least one offline element. Unconditional. -/
theorem bridge_iff (S : Set ℂ) :
    RotatedPrimeDensityDetectorEvent S ↔ ∃ ρ ∈ S, IsOffline ρ :=
  rotatedPrimeDensityDetectorEvent_iff S



/-! ## Case 1: All online → detector silent -/

/-- If every element of `S` is on the critical line, the detector is silent. -/
theorem bridge_all_online (S : Set ℂ) (h : ∀ ρ ∈ S, IsOnline ρ) :
    ¬ RotatedPrimeDensityDetectorEvent S := by
  rw [bridge_iff]
  push_neg
  exact fun ρ hρ => (isOffline_iff_not_isOnline ρ).not_left.mpr (h ρ hρ)

/-! ## Case 2: Some offline → detector fires -/

/-- If `S` contains at least one offline element, the detector fires. -/
theorem bridge_offline_detected (S : Set ℂ) (ρ : ℂ) (hρS : ρ ∈ S) (hoff : IsOffline ρ) :
    RotatedPrimeDensityDetectorEvent S :=
  (bridge_iff S).mpr ⟨ρ, hρS, hoff⟩

/-! ## Case 3: Partition into online ∪ offline -/

/-- Given a partition `S = A ∪ B` where `A` is all-online and `B` is all-offline,
    the detector fires on `S` iff `B` is nonempty. -/
theorem bridge_partition (A B : Set ℂ)
    (hA : ∀ ρ ∈ A, IsOnline ρ)
    (hB : ∀ ρ ∈ B, IsOffline ρ) :
    RotatedPrimeDensityDetectorEvent (A ∪ B) ↔ B.Nonempty := by
  rw [bridge_iff]
  constructor
  · rintro ⟨ρ, hρ, hoff⟩
    rcases hρ with hρA | hρB
    · exact absurd (hA ρ hρA) hoff
    · exact ⟨ρ, hρB⟩
  · rintro ⟨ρ, hρB⟩
    exact ⟨ρ, Set.mem_union_right A hρB, hB ρ hρB⟩

/-! ## Monotonicity -/

/-- If the detector fires on a subset, it fires on any superset. -/
theorem bridge_monotone {S T : Set ℂ} (hST : S ⊆ T) :
    RotatedPrimeDensityDetectorEvent S → RotatedPrimeDensityDetectorEvent T := by
  rintro ⟨ρ, hρS, hf⟩
  exact ⟨ρ, hST hρS, hf⟩

/-- Adding elements to a firing set keeps it firing. -/
theorem bridge_union_left (S T : Set ℂ) :
    RotatedPrimeDensityDetectorEvent S → RotatedPrimeDensityDetectorEvent (S ∪ T) :=
  bridge_monotone Set.subset_union_left

/-- The detector fires on a union iff it fires on at least one component. -/
theorem bridge_union_iff (S T : Set ℂ) :
    RotatedPrimeDensityDetectorEvent (S ∪ T) ↔
      RotatedPrimeDensityDetectorEvent S ∨ RotatedPrimeDensityDetectorEvent T := by
  simp only [bridge_iff]
  constructor
  · rintro ⟨ρ, hρ, hoff⟩
    rcases hρ with hS | hT
    · exact Or.inl ⟨ρ, hS, hoff⟩
    · exact Or.inr ⟨ρ, hT, hoff⟩
  · rintro (⟨ρ, hS, hoff⟩ | ⟨ρ, hT, hoff⟩)
    · exact ⟨ρ, Set.mem_union_left T hS, hoff⟩
    · exact ⟨ρ, Set.mem_union_right S hT, hoff⟩

/-! ## Case 4: Conspiring-in-the-void offline zeros -/

/-- **Conspiracy detection**: even if `C` is a set of "conspiring" offline
    zeros — zeros that evade other detection methods — the rotated density
    detector still fires on any set containing them, because the detector
    is purely geometric (it checks `ρ.re ≠ 1/2`).

    The hypotheses are:
    * `C ⊆ S` — the conspiring zeros are part of the candidate set.
    * `hC` — every element of `C` is offline.
    * `hne` — `C` is nonempty (at least one conspirator exists).

    No hypothesis about `riemannZeta` is needed. -/
theorem bridge_conspiracy_detected (S C : Set ℂ)
    (hCS : C ⊆ S)
    (hC : ∀ ρ ∈ C, IsOffline ρ)
    (hne : C.Nonempty) :
    RotatedPrimeDensityDetectorEvent S := by
  obtain ⟨ρ, hρC⟩ := hne
  exact bridge_offline_detected S ρ (hCS hρC) (hC ρ hρC)

/-- **Conspiracy limitation**: the detector is silent on any all-online set,
    so it gives no evidence that conspiring offline zeros *don't* exist
    somewhere outside `S`. You cannot rule out conspiracy by silence alone.

    More precisely: for any set `S` of online zeros, the detector is silent,
    regardless of whether offline zeros exist elsewhere. -/
theorem bridge_conspiracy_limitation (S : Set ℂ) (hS : ∀ ρ ∈ S, IsOnline ρ) :
    ¬ RotatedPrimeDensityDetectorEvent S :=
  bridge_all_online S hS

/-! ## Full three-way decomposition -/

/-- **Three-way bridge**: given `S = Online ∪ Detected ∪ Conspiring` where
    `Online` is on the critical line and both `Detected` and `Conspiring`
    are offline, the detector fires on `S` iff `Detected ∪ Conspiring` is
    nonempty. The detector makes no distinction between "detected" and
    "conspiring" offline zeros — it sees both equally. -/
theorem bridge_three_way (Online Detected Conspiring : Set ℂ)
    (hOn : ∀ ρ ∈ Online, IsOnline ρ)
    (hDet : ∀ ρ ∈ Detected, IsOffline ρ)
    (hCon : ∀ ρ ∈ Conspiring, IsOffline ρ) :
    RotatedPrimeDensityDetectorEvent (Online ∪ Detected ∪ Conspiring) ↔
      (Detected ∪ Conspiring).Nonempty := by
  have hAllOffline : ∀ ρ ∈ Detected ∪ Conspiring, IsOffline ρ := by
    rintro ρ (hD | hC)
    · exact hDet ρ hD
    · exact hCon ρ hC
  rw [Set.union_assoc]
  exact bridge_partition Online (Detected ∪ Conspiring) hOn hAllOffline

/-! ## Per-element bridge -/

/-- The per-element detector fires iff the element is offline. -/
theorem bridge_element (ρ : ℂ) :
    rotatedPrimeDensityFires ρ ↔ IsOffline ρ :=
  rotatedPrimeDensityFires_iff ρ

/-- The singleton bridge: the detector fires on `{ρ}` iff `ρ` is offline. -/
theorem bridge_singleton (ρ : ℂ) :
    RotatedPrimeDensityDetectorEvent {ρ} ↔ IsOffline ρ := by
  rw [bridge_iff]
  simp [IsOffline]

/-! ## Empty set -/

/-- The detector is silent on the empty set. -/
theorem bridge_empty : ¬ RotatedPrimeDensityDetectorEvent (∅ : Set ℂ) := by
  rw [bridge_iff]
  simp

/-! ## Connection to the legacy scalar detector -/

/-- The legacy scalar detector `rotatedPrimeDensityDetectorPasses σ` agrees
    with the set-based detector: it passes iff `σ = 1/2` (i.e. online). -/
theorem bridge_legacy_iff (σ : ℝ) :
    rotatedPrimeDensityDetectorPasses σ ↔ IsOnline (⟨σ, 0⟩ : ℂ) := by
  rw [rotatedPrimeDensityDetector_iff, isOnline_iff]

/-! ## Integration with the zeta singularity bridge -/

/-- **Full bridge with singularity**: if `ρ` is a zeta zero, offline,
    and not the pole at `1`, then:
    1. The prime Dirichlet series has a singularity at `ρ` (order −1).
    2. The detector fires on any set containing `ρ`.

    This combines the analytic content (`riemannZeta ρ = 0` forces a
    singularity) with the geometric content (offline forces the detector). -/
theorem bridge_full_singularity (S : Set ℂ) (ρ : ℂ)
    (hρS : ρ ∈ S)
    (hz : riemannZeta ρ = 0)
    (hoff : IsOffline ρ)
    (hρ1 : ρ ≠ 1) :
    (¬ ContinuousAt (fun s ↦ -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹) ρ)
    ∧ RotatedPrimeDensityDetectorEvent S := by
  exact ⟨(offaxis_with_bridge ρ hz hoff hρ1).1,
         bridge_offline_detected S ρ hρS hoff⟩



end
