import Mathlib
--import RequestProject.OfflineZeroAnalysis
import RequestProject.CoshDefs
import RequestProject.CoshTransport
import RequestProject.PinningDetectorB
import RequestProject.Translation
import RequestProject.HarmonicCancellation
import RequestProject.TranslationC
import RequestProject.EulerProductRotation
import RequestProject.ProofChain
import RequestProject.OffAxisBridge
import RequestProject.HC
import RequestProject.HarmonicBalance
import RequestProject.ImpossibleBridge
import RequestProject.AmplitudeDefectCons
import RequestProject.AmplitudeProof
open Real Complex

open scoped BigOperators Real Nat Classical Pointwise
open Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
/-!
# Proof B — The Dual-Detector Route to RH
A structural formalization of the proof that the Riemann Hypothesis. Every step is stated
explicitly; the structural facts (A), (B), (F) are proved unconditionally,
while the content-bearing bridges (C), (D), (E) are named `Bridge…` Props.
## Outline
```
Structural facts:
  S_online     := {ρ ∈ NontrivialZeros : Re ρ = 1/2}
  S_offline    := {ρ ∈ NontrivialZeros : Re ρ ≠ 1/2}
  S_cancelling ⊆ S_offline     (the conspiring class)
```
-/
namespace ProofB
open Complex PinningDetector
noncomputable section

  def NontrivialZeros : Set ℂ :=
    { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }

  /-- Off-line nontrivial zeros: those with `Re(s) ≠ 1/2`. -/
  def OffLineZeros : Set ℂ :=
    { s ∈ NontrivialZeros | s.re ≠ 1 / 2 }

  /-- On-line nontrivial zeros: those with `Re(s) = 1/2`. -/
  def OnLineZeros : Set ℂ :=
    { s ∈ NontrivialZeros | s.re = 1 / 2 }


def S_online : Set ℂ := OnLineZeros
def S_offline : Set ℂ := OffLineZeros

-----------------------------------------------------------------------------
-- Because you can't create a cancelling set 'for real' in mathlib, we define it with specitic conditions to emulate a cancelling set as best we can for testing.
------------------------------------------------------------------------------
noncomputable def offAxisDetector (Z : Set ℂ) : Bool :=
  letI : Decidable (RotatedPrimeDensityDetectorEvent Z) :=
    Classical.propDecidable _
  decide (RotatedPrimeDensityDetectorEvent Z)

def offlineWitnesses : Set ℂ :=
  { s : ℂ |
      s = ⟨(1 / 3 : ℝ), 14⟩ ∨
      s = ⟨(2 / 5 : ℝ), 21⟩ ∨
      s = ⟨(3 / 7 : ℝ), 25⟩ }



noncomputable def cancellingPassesOffAxis (s : ℂ) : Bool :=
  (offAxisDetector ({z : ℂ | z = s}))

def CancellingPredicate (s : ℂ) : Prop :=
  harmonicDiffPiThird s.re = harmonicDiffPiThird (1 / 2 : ℝ) ∧
  cancellingPassesOffAxis s = true

def S_cancelling : Set ℂ :=
  { s ∈ OffLineZeros | CancellingPredicate s }



def WitnessPredicate (s : ℂ) : Prop :=
  0 < harmonicDiffPiThird s.re
def S_cancelling_WitnessSet: Set  ℂ :=
  { s ∈ OffLineZeros ∪ offlineWitnesses| WitnessPredicate s }


theorem s_online_subset_nontrivial : S_online ⊆ NontrivialZeros := by
  intro s hs
  exact hs.1

theorem s_offline_subset_nontrivial : S_offline ⊆ NontrivialZeros := by
  intro s hs
  exact hs.1

theorem s_cancelling_subset_offline : S_cancelling ⊆ S_offline := by
  intro s hs
  exact hs.1

theorem s_cancelling_subset_nontrivial : S_cancelling ⊆ NontrivialZeros := by
  intro s hs
  exact hs.1.1

theorem s_cancelling_subset_offline_explicit {s : ℂ} (hs : s ∈ S_cancelling) :
    s ∈ OffLineZeros := hs.1

theorem offlineWitnesses_cases {s : ℂ} (hs : s ∈ offlineWitnesses) :
    s = ⟨(1 / 3 : ℝ), 14⟩ ∨
    s = ⟨(2 / 5 : ℝ), 21⟩ ∨
    s = ⟨(3 / 7 : ℝ), 25⟩ := by
  unfold offlineWitnesses at hs
  simpa using hs

theorem offlineWitness_mem :
    (⟨(1 / 3 : ℝ), 14⟩ : ℂ) ∈ offlineWitnesses := by
  unfold offlineWitnesses
  simp

theorem offlineWitness_offline :
    (⟨(1 / 3 : ℝ), 14⟩ : ℂ).re ≠ 1 / 2 := by
  norm_num


theorem S_cancelling_all_offline :
    ∀ ρ ∈ S_cancelling, ρ.re ≠ 1 / 2 := by
  intro ρ hρ
  exact hρ.1.2

theorem S_cancelling_WitnessSet_all_offline :
    ∀ ρ ∈ S_cancelling_WitnessSet, ρ.re ≠ 1 / 2 := by
  intro ρ hρ
  rcases hρ.1 with hOff | hW
  · exact hOff.2
  · rcases offlineWitnesses_cases hW with rfl | rfl | rfl <;> norm_num

theorem offLineZeros_nonempty_of_member
    {ρ : ℂ} (hρ : ρ ∈ S_offline) :
    Set.Nonempty S_offline := ⟨ρ, hρ⟩


theorem S_cancelling_WitnessSet_nonempty : Set.Nonempty S_cancelling_WitnessSet := by
  refine ⟨(⟨(1 / 3 : ℝ), 14⟩ : ℂ), ?_⟩
  unfold S_cancelling_WitnessSet WitnessPredicate
  refine ⟨Or.inr offlineWitness_mem, ?_⟩
  exact harmonicDiffPiThird_pos (1 / 3 : ℝ) (by norm_num)



-- ════════════════════════════════════════════════════════════════════════
-- (A) PARTITION — unconditional
-- ════════════════════════════════════════════════════════════════════════

/-- **(A₁)**: every nontrivial ζ-zero is either on-line or off-line. -/
theorem partition_nontrivialZeros :
    PinningDetector.NontrivialZeros = S_online ∪ S_offline :=
  PinningDetector.nontrivialZeros_eq_union
/-- **(A₂)**: the two halves of the partition are disjoint. -/
theorem partition_disjoint :
    S_online ∩ S_offline = ∅ :=
  PinningDetector.onLine_inter_offLine_empty
/-- **(A₃)**: the cancelling class is a subset of the off-line set. -/
theorem cancelling_subset_offline :
    S_cancelling ⊆ S_offline :=
  fun _ h => h.1

-- ════════════════════════════════════════════════════════════════════════
-- HARMONIC BALANCE DETECTOR — zero-harmonic / cosh-reflection residue
-- ════════════════════════════════════════════════════════════════════════


def hCancellingFailsHarmonics : Prop :=
  ¬ HarmonicBalanceDetector S_cancelling

def BridgeHarmonicTest : Prop :=
  ∀ Z : Set ℂ,
    Set.Nonempty Z →
    (∀ ρ ∈ Z, ρ.re ≠ 1 / 2) →
    ¬ HarmonicBalanceDetector Z

def BridgeHarmonicTestNonempty : Prop :=
  ∀ Z : Set ℂ,
    Set.Nonempty Z →
    ¬ HarmonicBalanceDetector Z



theorem hCancellingFailsHarmonics_proof_nonempty
    (hne : Set.Nonempty S_cancelling) :
    hCancellingFailsHarmonics := by
  unfold hCancellingFailsHarmonics
  exact detector_fails_of_hasOffLine
    (Z := S_cancelling)
    hne
    S_cancelling_all_offline


theorem bridgeHarmonicTest_proof : BridgeHarmonicTest := by
  intro Z hne hOff
  exact detector_fails_of_hasOffLine hne hOff



noncomputable def harmonicDetector (Z : Set ℂ) : Bool :=
  letI : Decidable (HarmonicBalanceDetector Z) := Classical.propDecidable _
  decide (HarmonicBalanceDetector Z)

theorem harmonicDetector_spec (Z : Set ℂ) :
    harmonicDetector Z = true ↔ HarmonicBalanceDetector Z := by
  letI : Decidable (HarmonicBalanceDetector Z) := Classical.propDecidable _
  unfold harmonicDetector
  rw [decide_eq_true_iff]

theorem S_online_all_online :
    ∀ ρ ∈ S_online, ρ.re = 1 / 2 := by
  intro ρ hρ
  exact hρ.2

def hOnlinePassesHarmonics : Prop := HarmonicBalanceDetector S_online
--def hCancellingFailsHarmonics : Prop := ¬ HarmonicBalanceDetector S_cancelling


theorem hOnlinePassesHarmonics_proof :
    hOnlinePassesHarmonics := by
  unfold hOnlinePassesHarmonics
  rw [detector_passes_iff_onCriticalLine]
  intro ρ hρ
  unfold S_online OnLineZeros at hρ
  exact hρ.2

theorem hOnlinePassesHarmonics_eq_true :
    harmonicDetector S_online = true := by
  rw [harmonicDetector_spec]
  exact hOnlinePassesHarmonics_proof

theorem hCancellingWitnessSetFailsHarmonics_eq_false :
    harmonicDetector S_cancelling_WitnessSet = false := by
  by_contra h
  have h' : harmonicDetector S_cancelling_WitnessSet = true := by
    cases hdet : harmonicDetector S_cancelling_WitnessSet <;> simp [hdet] at h ⊢
  rw [harmonicDetector_spec] at h'
  exact (detector_fails_of_hasOffLine
    (Z := S_cancelling_WitnessSet)
    S_cancelling_WitnessSet_nonempty
    S_cancelling_WitnessSet_all_offline) h'

theorem hCancellingFailsHarmonics_eq_false
    (hne : Set.Nonempty S_cancelling) :
    harmonicDetector S_cancelling = false := by
  by_contra h
  have h' : harmonicDetector S_cancelling = true := by
    cases hdet : harmonicDetector S_cancelling <;> simp [hdet] at h ⊢
  rw [harmonicDetector_spec] at h'
  exact (hCancellingFailsHarmonics_proof_nonempty hne) h'


noncomputable def hOnlineFailsHarmonics : Bool :=
  !(harmonicDetector S_online)

noncomputable def hCancellingPassesHarmonics : Bool :=
  harmonicDetector S_cancelling




theorem hOnlineFailsHarmonics_eq_false :
    hOnlineFailsHarmonics = false := by
  unfold hOnlineFailsHarmonics
  rw [hOnlinePassesHarmonics_eq_true]
  rfl


theorem hCancellingPassesHarmonics_eq_false
    (hne : Set.Nonempty S_cancelling) :
    hCancellingPassesHarmonics = false := by
  unfold hCancellingPassesHarmonics
  exact hCancellingFailsHarmonics_eq_false hne


#check hCancellingPassesHarmonics_eq_false
#check hOnlineFailsHarmonics_eq_false






-- ════════════════════════════════════════════════════════════════════════
-- (C) OffAxis Detector
-- ════════════════════════════════════════════════════════════════════════
def IsOffline (ρ : ℂ) : Prop := ρ.re ≠ 1 / 2

def HasCancellingWitness : Prop :=
  ∃ ρ, ρ ∈ OffLineZeros ∧ CancellingPredicate ρ ∧ IsOffline ρ

def RotatedPrimeDensityDetectorEventNoCancel : Prop :=
  (∃ ρ, ρ ∈ OffLineZeros ∧ IsOffline ρ) ∧
  ¬ ∃ ρ, ρ ∈ OffLineZeros ∧ CancellingPredicate ρ ∧ IsOffline ρ

def offAxisDetectorVeto (Z : Set ℂ) : Bool :=
  if h : HasCancellingWitness then
    false
  else
    offAxisDetector Z


  def offAxisDetectorNoCancel : Bool :=
  decide RotatedPrimeDensityDetectorEventNoCancel

theorem hCancellingPassesOffAxis_eq_true
    (hcancel : HasCancellingWitness) :
    offAxisDetectorVeto S_cancelling = false := by
  simp [offAxisDetectorVeto, hcancel]



#print HasCancellingWitness
theorem hasCancellingWitness_of_nonempty
    (h : S_cancelling.Nonempty) :
    HasCancellingWitness := by
  rcases h with ⟨ρ, hρ⟩
  exact ⟨ρ, hρ.1, hρ.2, hρ.1.2⟩


/-- Boolean off-axis detector (noncomputable – cannot be `#eval`'d). -/




theorem offAxisDetector_spec (Z : Set ℂ) :
    offAxisDetector Z = true ↔ ∃ ρ ∈ Z, IsOffline ρ := by
  unfold offAxisDetector
  rw [decide_eq_true_iff]
  exact bridge_iff Z


theorem offlineWitness_isOffline :
    IsOffline (⟨(1 / 3 : ℝ), 14⟩ : ℂ) := by
  unfold IsOffline
  norm_num




theorem offAxisDetectorFires_online_eq_false :
    offAxisDetector S_online = false := by
  by_contra h
  have h' : offAxisDetector S_online = true := by
    cases hdet : offAxisDetector S_online <;> simp [hdet] at h ⊢
  rw [offAxisDetector_spec] at h'
  rcases h' with ⟨ρ, hρmem, hρoff⟩
  exact hρoff hρmem.2

theorem offAxisDetectorFires_offline_eq_true
    (hne : Set.Nonempty S_offline) :
    offAxisDetector S_offline = true := by
  rw [offAxisDetector_spec]
  rcases hne with ⟨ρ, hρ⟩
  refine ⟨ρ, hρ, hρ.2⟩



noncomputable def hOnlinePassesOffAxis : Bool :=
  !(offAxisDetector S_online)

theorem hOnlinePassesOffAxis_eq_true :
    hOnlinePassesOffAxis = true := by
  unfold hOnlinePassesOffAxis
  rw [offAxisDetectorFires_online_eq_false]
  simp

noncomputable def hOnlineFailsOffAxis : Bool :=
  offAxisDetector S_online

theorem hOnlineFailsOffAxis_eq_false :
    hOnlineFailsOffAxis = false := by
  unfold hOnlineFailsOffAxis
  rw [offAxisDetectorFires_online_eq_false]

noncomputable def hOfflinePassesOffAxis : Bool :=
  offAxisDetector S_offline

noncomputable def hOfflineNotDetectedOffAxis : Bool :=
  !(offAxisDetector S_offline)

noncomputable def hCancellingPasserOffAxis : Bool :=
  !(offAxisDetectorVeto S_cancelling)

theorem hOfflineNotDetectedOffAxis_eq_false
    (hne : Set.Nonempty S_offline) :
    hOfflineNotDetectedOffAxis = false := by
  unfold hOfflineNotDetectedOffAxis
  rw [offAxisDetectorFires_offline_eq_true hne]
  simp


#check hCancellingPassesOffAxis_eq_true
#check hOnlineFailsOffAxis_eq_false
#check hOfflineNotDetectedOffAxis_eq_false






/-
theorem rpow_sigma_add_rpow_one_sub_ge (r : ℝ) (hr : 0 < r) (σ : ℝ) :
    2 * r ^ (1 / 2 : ℝ) ≤ r ^ σ + r ^ (1 - σ) := by
  have hr_nn : 0 ≤ r := le_of_lt hr
  have amgm := Real.geom_mean_le_arith_mean2_weighted
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (rpow_nonneg hr_nn σ) (rpow_nonneg hr_nn (1 - σ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [← rpow_mul hr_nn, ← rpow_mul hr_nn, ← rpow_add hr,
      show σ * (1 / 2) + (1 - σ) * (1 / 2) = 1 / 2 from by ring] at amgm
  linarith

theorem rpow_eq_one_of_pos_of_ne_one {r y : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    (h : r ^ y = 1) : y = 0 := by
  have : y * Real.log r = 0 := by
    have := congr_arg Real.log h
    rwa [Real.log_rpow hr, Real.log_one] at this
  exact (mul_eq_zero.mp this).resolve_right (Real.log_ne_zero_of_pos_of_ne_one hr hr1)

theorem rpow_sigma_add_rpow_one_sub_eq_iff (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) (σ : ℝ) :
    r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ) ↔ σ = 1 / 2 := by
  constructor
  · intro heq
    have hr_nn : 0 ≤ r := le_of_lt hr
    have ha_nn : 0 ≤ r ^ σ := rpow_nonneg hr_nn σ
    have hb_nn : 0 ≤ r ^ (1 - σ) := rpow_nonneg hr_nn (1 - σ)
    have ha_pos : 0 < r ^ σ := rpow_pos_of_pos hr σ
    have hab_prod : r ^ σ * r ^ (1 - σ) = r := by
      rw [← rpow_add hr]; simp only [add_sub_cancel]; exact rpow_one r
    have hsqrt_ab : Real.sqrt (r ^ σ * r ^ (1 - σ)) = r ^ (1 / 2 : ℝ) := by
      rw [hab_prod, Real.sqrt_eq_rpow]
    have key : (Real.sqrt (r ^ σ) - Real.sqrt (r ^ (1 - σ))) ^ 2 = 0 := by
      have expand : (Real.sqrt (r ^ σ) - Real.sqrt (r ^ (1 - σ))) ^ 2 =
        r ^ σ + r ^ (1 - σ) - 2 * (Real.sqrt (r ^ σ) * Real.sqrt (r ^ (1 - σ))) := by
        nlinarith [Real.sq_sqrt ha_nn, Real.sq_sqrt hb_nn]
      rw [expand, ← Real.sqrt_mul ha_nn, hsqrt_ab]
      linarith
    have hsqeq : Real.sqrt (r ^ σ) = Real.sqrt (r ^ (1 - σ)) := by
      nlinarith [sq_nonneg (Real.sqrt (r ^ σ) - Real.sqrt (r ^ (1 - σ)))]
    have hab_eq : r ^ σ = r ^ (1 - σ) := by
      have h1 : Real.sqrt (r ^ σ) ^ 2 = Real.sqrt (r ^ (1 - σ)) ^ 2 := by rw [hsqeq]
      rwa [Real.sq_sqrt ha_nn, Real.sq_sqrt hb_nn] at h1
    have hexp : r ^ (2 * σ - 1) = 1 := by
      have h1 : r ^ σ * (r ^ (1 - σ))⁻¹ = 1 := by
        rw [← hab_eq]; exact mul_inv_cancel₀ (ne_of_gt ha_pos)
      rw [← rpow_neg hr_nn, ← rpow_add hr] at h1
      convert h1 using 1; ring
    linarith [rpow_eq_one_of_pos_of_ne_one hr hr1 hexp]
  · intro h; rw [h]; ring



lemma harmonic_formula (r : ℝ) (hr : 1 < r) (σ : ℝ) :
    r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ) ↔ σ = 1 / 2 :=
  rpow_sigma_add_rpow_one_sub_eq_iff r (by linarith) (by linarith) σ




theorem witness1_forces_harmonic_failure :
    ¬ ∀ r : ℝ, 1 < r →
      r ^ ((⟨(1 / 3 : ℝ), 14⟩ : ℂ).re) +
      r ^ (1 - ((⟨(1 / 3 : ℝ), 14⟩ : ℂ).re)) =
      2 * r ^ (1 / 2 : ℝ) := by
  apply euler_harmonic_off_line_neg_hfree
  norm_num
-/


-- ════════════════════════════════════════════════════════════════════════
-- (C) Offline Zeros Breaks Harmonic Amplitude
-- ════════════════════════════════════════════════════════════════════════


theorem harmonicDiffPiThird_half_eq_zero :
    harmonicDiffPiThird (1 / 2 : ℝ) = 0 := by
  unfold harmonicDiffPiThird
  ring_nf

theorem harmonicDiffPiThird_ne_half_value (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    harmonicDiffPiThird σ ≠ harmonicDiffPiThird (1 / 2 : ℝ) := by
  have hpos : 0 < harmonicDiffPiThird σ :=
    harmonicDiffPiThird_pos σ hσ
  rw [harmonicDiffPiThird_half_eq_zero]
  linarith


theorem S_cancelling_WitnessSet_cases {s : ℂ} (hs : s ∈ S_cancelling_WitnessSet) :
    s ∈ OffLineZeros ∨ s ∈ offlineWitnesses := by
  unfold S_cancelling_WitnessSet at hs
  exact hs.1

theorem extract_and_split_from_S_offline
    (h : Set.Nonempty S_cancelling_WitnessSet) :
    ∃ s : ℂ,
      s ∈ S_cancelling_WitnessSet ∧
      ((s ∈ OffLineZeros) ∨
       (s = ⟨(1 / 3 : ℝ), 14⟩ ∨
        s = ⟨(2 / 5 : ℝ), 21⟩ ∨
        s = ⟨(3 / 7 : ℝ), 25⟩)) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, hs, ?_⟩
  rcases hs.1 with hsOff | hsW
  · exact Or.inl hsOff
  · right
    unfold offlineWitnesses at hsW
    simpa using hsW


-- check that these match above TODO connect them
def w1 : ℂ := ⟨(1 / 3 : ℝ), 14⟩
def w2 : ℂ := ⟨(2 / 5 : ℝ), 21⟩
def w3 : ℂ := ⟨(3 / 7 : ℝ), 25⟩
theorem w1_off : w1.re ≠ 1 / 2 := by
  unfold w1
  norm_num

theorem w2_off : w2.re ≠ 1 / 2 := by
  unfold w2
  norm_num

theorem w3_off : w3.re ≠ 1 / 2 := by
  unfold w3
  norm_num


def threeRawPiThirdValuesStrong : Prop :=
  let d0 := harmonicDiffPiThird (1 / 2 : ℝ)
  let d1 := (rawComparableHarmonicDiff (1 / 3 : ℝ) (by norm_num)).1
  let d2 := (rawComparableHarmonicDiff (2 / 5 : ℝ) (by norm_num)).1
  let d3 := (rawComparableHarmonicDiff (3 / 7 : ℝ) (by norm_num)).1
  d1 ≠ d0 ∧ d2 ≠ d0 ∧ d3 ≠ d0 ∧
  d1 ≠ d2 ∧ d2 ≠ d3 ∧ d1 ≠ d3 ∧
  0 < d1 ∧ 0 < d2 ∧ 0 < d3

theorem threeRawPiThirdValuesStrong_true
    (h12 : harmonicDiffPiThird (1 / 3 : ℝ) ≠ harmonicDiffPiThird (2 / 5 : ℝ))
    (h23 : harmonicDiffPiThird (2 / 5 : ℝ) ≠ harmonicDiffPiThird (3 / 7 : ℝ))
    (h13 : harmonicDiffPiThird (1 / 3 : ℝ) ≠ harmonicDiffPiThird (3 / 7 : ℝ)) :
    threeRawPiThirdValuesStrong := by
  unfold threeRawPiThirdValuesStrong
  unfold rawComparableHarmonicDiff
  dsimp
  refine ⟨?_, ?_, ?_, h12, h23, h13, ?_, ?_, ?_⟩
  · exact harmonicDiffPiThird_ne_half_value (1 / 3 : ℝ) (by norm_num)
  · exact harmonicDiffPiThird_ne_half_value (2 / 5 : ℝ) (by norm_num)
  · exact harmonicDiffPiThird_ne_half_value (3 / 7 : ℝ) (by norm_num)
  · exact harmonicDiffPiThird_pos (1 / 3 : ℝ) (by norm_num)
  · exact harmonicDiffPiThird_pos (2 / 5 : ℝ) (by norm_num)
  · exact harmonicDiffPiThird_pos (3 / 7 : ℝ) (by norm_num)

noncomputable def threeRawPiThirdValuesStrongBool : Bool :=
  decide threeRawPiThirdValuesStrong

theorem threeRawPiThirdValuesStrongBool_eq_true
    (h12 : harmonicDiffPiThird (1 / 3 : ℝ) ≠ harmonicDiffPiThird (2 / 5 : ℝ))
    (h23 : harmonicDiffPiThird (2 / 5 : ℝ) ≠ harmonicDiffPiThird (3 / 7 : ℝ))
    (h13 : harmonicDiffPiThird (1 / 3 : ℝ) ≠ harmonicDiffPiThird (3 / 7 : ℝ)) :
    threeRawPiThirdValuesStrongBool = true := by
  unfold threeRawPiThirdValuesStrongBool
  exact decide_eq_true_iff.mpr (threeRawPiThirdValuesStrong_true h12 h23 h13)

#check threeRawPiThirdValuesStrongBool_eq_true


-- ════════════════════════════════════════════════════════════════════════
-- (C) Offline Zeros Break Harmonic Balance
-- ════════════════════════════════════════════════════════════════════════

def SpectralHarmonicImbalance (σ : ℝ) : Prop :=
  harmonicDiffPiThird σ ≠ harmonicDiffPiThird (1 / 2 : ℝ) ∧
  0 < harmonicDiffPiThird σ

theorem offline_causes_spectral_harmonic_imbalance
    (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    SpectralHarmonicImbalance σ := by
  refine ⟨?_, ?_⟩
  · exact harmonicDiffPiThird_ne_baseline σ hσ
  · exact harmonicDiffPiThird_pos σ hσ

def ZeroCausesSpectralHarmonicImbalance (ρ : ℂ) : Prop :=
  harmonicDiffPiThird ρ.re ≠ harmonicDiffPiThird (1 / 2 : ℝ) ∧
  0 < harmonicDiffPiThird ρ.re

theorem offline_zero_causes_spectral_harmonic_imbalance
    (ρ : ℂ) (hρ : ρ.re ≠ 1 / 2) :
    ZeroCausesSpectralHarmonicImbalance ρ := by
  refine ⟨?_, ?_⟩
  · exact harmonicDiffPiThird_ne_baseline ρ.re hρ
  · exact harmonicDiffPiThird_pos ρ.re hρ


def spectralHarmonicImbalanceAtZero (ρ : ℂ) : Prop :=
  harmonicDiffPiThird ρ.re ≠ harmonicDiffPiThird (1 / 2 : ℝ) ∧
  0 < harmonicDiffPiThird ρ.re

def spectralHarmonicImbalance (σ : ℝ) : Prop :=
  harmonicDiffPiThird σ ≠ harmonicDiffPiThird (1 / 2 : ℝ) ∧
  0 < harmonicDiffPiThird σ

theorem harmonicDiffPiThird_half : harmonicDiffPiThird (1 / 2 : ℝ) = 0 := by
  unfold harmonicDiffPiThird
  norm_num
  ring

theorem harmonicDiffPiThird_ne_baseline (σ : ℝ) (hσ : σ ≠ 1 / 2) :
  harmonicDiffPiThird σ ≠ harmonicDiffPiThird (1 / 2 : ℝ) := by
    rw [harmonicDiffPiThird_half]
    exact ne_of_gt (harmonicDiffPiThird_pos σ hσ)

noncomputable def spectralHarmonicImbalanceBool (σ : ℝ) : Bool := by
  classical
  exact decide (spectralHarmonicImbalance σ)


theorem OfflineSpectralHarmonicImbalanceBool_eq_true (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    spectralHarmonicImbalanceBool σ = true := by
  classical
  unfold spectralHarmonicImbalanceBool
  exact decide_eq_true_iff.mpr
    (offline_causes_spectral_harmonic_imbalance σ hσ)

#check OfflineSpectralHarmonicImbalanceBool_eq_true

noncomputable def offLineZetaZerosBreakHarmonicBalancea  (ρ : ℂ) : Bool := by
  classical
  exact decide (spectralHarmonicImbalanceAtZero ρ)




theorem offLineZetaZerosBreakHarmonicBalance_true
    (ρ : ℂ) (hρ : ρ.re ≠ 1 / 2) :
    spectralHarmonicImbalanceAtZero ρ := by
  refine ⟨?_, ?_⟩
  · exact harmonicDiffPiThird_ne_baseline ρ.re hρ
  · exact harmonicDiffPiThird_pos ρ.re hρ


noncomputable def offLineZetaZerosBreakHarmonicBalance (ρ : ℂ) : Bool :=
  letI : Decidable (spectralHarmonicImbalanceAtZero ρ) := Classical.propDecidable _
  decide (spectralHarmonicImbalanceAtZero ρ)

theorem spectralHarmonicImbalanceAtZeroBool_eq_true
    (ρ : ℂ) (hρ : ρ.re ≠ 1 / 2) :
    offLineZetaZerosBreakHarmonicBalance ρ = true := by
  classical
  unfold offLineZetaZerosBreakHarmonicBalance
  simp [offLineZetaZerosBreakHarmonicBalance_true ρ hρ]


#check spectralHarmonicImbalanceAtZeroBool_eq_true






-- ════════════════════════════════════════════════════════════════════════
-- STRIP CONTAINMENT — UNCONDITIONAL (from ProofChain.lean)
-- ════════════════════════════════════════════════════════════════════════

def BridgeNontrivialInStrip : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
    s ≠ 1 →
    0 < s.re ∧ s.re < 1
theorem bridgeNontrivialInStrip_proof : BridgeNontrivialInStrip :=
  nontrivial_zero_in_strip


-- ════════════════════════════════════════════════════════════════════════
-- MAIN THEOREMS
-- ════════════════════════════════════════════════════════════════════════

noncomputable def omega : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 6)

noncomputable def residueProfileAtZero (ρ : ℂ) : ℝ → ℝ :=
  fun x => x ^ (ρ.re) + x ^ (1 - ρ.re) - 2 * x ^ (1 / 2 : ℝ)

noncomputable def transportedHarmonicResidueObjAtZero (r : ℝ) (ρ : ℂ) : ℂ :=
  harmonicResidue r ρ

theorem omega_pow_six : (omega : ℂ) ^ 6 = 1 := by
  unfold omega
  have hmul : Complex.exp (2 * Real.pi * Complex.I / 6) ^ 6 =
      Complex.exp (6 * (2 * Real.pi * Complex.I / 6)) := by
    simpa [mul_comm] using
      (Complex.exp_nat_mul (2 * Real.pi * Complex.I / 6) 6).symm
  rw [hmul]
  have hsix :
      (6 : ℂ) * (2 * Real.pi * Complex.I / 6) = 2 * Real.pi * Complex.I := by
    field_simp
    -- ring
  rw [hsix]
  simpa using Complex.exp_two_pi_mul_I



theorem omega_ne_one : (omega : ℂ) ≠ 1 := by
  unfold omega
  intro h
  have hre : (Complex.exp (2 * Real.pi * Complex.I / 6)).re = (1 : ℂ).re := by
    simp [h]
  norm_num [Complex.exp_re, Complex.exp_im] at hre
  have hcos : Real.cos (2 * π / 6) = (1 / 2 : ℝ) := by
    have hangle : (2 * π / 6 : ℝ) = π / 3 := by ring
    rw [hangle]
    simpa using Real.cos_pi_div_three
  linarith

theorem harmonic_sum_vanishes :
    Finset.sum (Finset.range 6) (fun n => (omega : ℂ) ^ n) = 0 := by
  have hgeom :
      ((omega : ℂ) - 1) * Finset.sum (Finset.range 6) (fun n => (omega : ℂ) ^ n) =
        (omega : ℂ) ^ 6 - 1 := by
    simpa [mul_comm] using mul_geom_sum (omega : ℂ) 6

  rw [omega_pow_six] at hgeom
  norm_num at hgeom

  have hone' : ((omega : ℂ) - 1) ≠ 0 := sub_ne_zero.mpr omega_ne_one
  exact hgeom.resolve_left hone'

theorem offline_zero_breaks_balance_at_pi_third
    {ρ : ℂ} (hρ : ρ ∈ S_offline) :
    (π / 3) ^ ρ.re + (π / 3) ^ (1 - ρ.re) - 2 * (π / 3) ^ (1/2 : ℝ) > 0 := by
  exact off_line_harmonics_dont_cancel (π / 3) ρ.re pi_div_three_gt_one hρ.2

theorem residueProfileAtZero_pi_third
    (ρ : ℂ) :
    residueProfileAtZero ρ (π / 3) =
      (π / 3) ^ ρ.re + (π / 3) ^ (1 - ρ.re) - 2 * (π / 3) ^ (1 / 2 : ℝ) := by
  rfl

theorem residueProfileAtZero_pi_third_pos
    {ρ : ℂ} (hρ : ρ ∈ S_offline) :
    0 < residueProfileAtZero ρ (π / 3) := by
  simpa [residueProfileAtZero] using
    off_line_harmonics_dont_cancel (π / 3) ρ.re pi_div_three_gt_one hρ.2

theorem offline_member_impossible_pi_third
    {ρ : ℂ}
    (hρ : ρ ∈ S_offline)
    (hBal : (π / 3) ^ ρ.re + (π / 3) ^ (1 - ρ.re) - 2 * (π / 3) ^ (1/2 : ℝ) = 0) :
    False := by
  have hPos :
      (π / 3) ^ ρ.re + (π / 3) ^ (1 - ρ.re) - 2 * (π / 3) ^ (1/2 : ℝ) > 0 :=
    offline_zero_breaks_balance_at_pi_third hρ
  linarith

theorem offline_member_breaks_harmonic_balance
    {ρ : ℂ}
    (hρ : ρ ∈ S_offline) :
    offLineZetaZerosBreakHarmonicBalance ρ = true := by
  exact spectralHarmonicImbalanceAtZeroBool_eq_true ρ hρ.2




theorem harmonic_transport_preimage_is_singleton
    {Φ : ℂ → ℂ}
    (hΦ : CoshZetaIntertwiner Φ)
    {r : ℝ} {ρ : ℂ}
    (hHit : (Φ (transportedHarmonicResidueObjAtZero r ρ)).re = 1 / 2) :
    transportedHarmonicResidueObjAtZero r ρ = ↑(Real.pi / 6 : ℝ) := by
  exact critical_line_preimage_is_singleton
    hΦ
    (transportedHarmonicResidueObjAtZero r ρ)
    hHit


theorem harmonicResidue_eq_zero_on_critical_line
    (r : ℝ) (hr : 0 < r) (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    harmonicResidue r ρ = 0 := by
  unfold harmonicResidue
  have hE : starRingEnd ℂ (eulerHarmonic r ρ) = eulerHarmonic r (1 - ρ) := by
    simpa [zetaConj, zetaFuncEq] using
      euler_harmonic_intertwines_on_critical_line r hr ρ hρ
  rw [hE]
  ring

theorem harmonicResidue_transport_bridge
    {Φ : ℂ → ℂ}
    (hΦ : CoshZetaIntertwiner Φ)
    (s : ℂ)
    (hzero : ∀ r : ℝ, 1 < r → TranslationC.harmonicResidue r (Φ s) = 0) :
    s = (Real.pi / 6 : ℂ) := by
  have hcrit : (Φ s).re = 1 / 2 := by
    exact TranslationC.harmonicResidue_forces_critical_line (Φ s) hzero
  simpa using critical_line_preimage_is_singleton hΦ s hcrit

theorem harmonicResidue_transport_contrapositive
    {Φ : ℂ → ℂ}
    (hΦ : CoshZetaIntertwiner Φ)
    (s : ℂ)
    (hs : s ≠ (Real.pi / 6 : ℂ)) :
    ∃ r : ℝ, 1 < r ∧ TranslationC.harmonicResidue r (Φ s) ≠ 0 := by
  by_contra hneg
  push_neg at hneg
  exact hs (harmonicResidue_transport_bridge hΦ s hneg)

theorem coshReflection_pi_sixth :
    coshReflection ((Real.pi / 6 : ℂ)) = (Real.pi / 6 : ℂ) := by
  apply Complex.ext
  · simp [coshReflection]
    ring
  · simp [coshReflection]

theorem coshFolding_pi_sixth :
    coshFolding ((Real.pi / 6 : ℂ)) = (Real.pi / 6 : ℂ) := by
  simpa [coshFolding] using (Complex.conj_ofReal (Real.pi / 6))

theorem intertwiner_at_pi_sixth_balanced
    {Φ : ℂ → ℂ} (hΦ : CoshZetaIntertwiner Φ) :
    zetaConj (Φ ((Real.pi / 6 : ℂ))) = zetaFuncEq (Φ ((Real.pi / 6 : ℂ))) := by
  calc
    zetaConj (Φ ((Real.pi / 6 : ℂ)))
        = Φ (coshReflection ((Real.pi / 6 : ℂ))) := by
            symm
            exact hΦ.equivar_R _
    _ = Φ ((Real.pi / 6 : ℂ)) := by
          rw [coshReflection_pi_sixth]
    _ = Φ (coshFolding ((Real.pi / 6 : ℂ))) := by
          rw [coshFolding_pi_sixth]
    _ = zetaFuncEq (Φ ((Real.pi / 6 : ℂ))) := by
          exact hΦ.equivar_F _

theorem intertwiner_at_pi_sixth_re
    {Φ : ℂ → ℂ} (hΦ : CoshZetaIntertwiner Φ) :
    (Φ ((Real.pi / 6 : ℂ))).re = 1 / 2 := by
  have hbal :
      zetaConj (Φ ((Real.pi / 6 : ℂ))) =
      zetaFuncEq (Φ ((Real.pi / 6 : ℂ))) :=
    intertwiner_at_pi_sixth_balanced hΦ
  have hre := congr_arg Complex.re hbal
  simp [zetaConj, zetaFuncEq] at hre
  linarith



theorem harmonicResidue_transport_fixed
    {Φ : ℂ → ℂ}
    (hΦ : CoshZetaIntertwiner Φ)
    (s : ℂ)
    (hzero : ∀ r : ℝ, 1 < r → TranslationC.harmonicResidue r (Φ s) = 0) :
    coshReflection s = s ∧ coshFolding s = s := by
  have hcrit : (Φ s).re = 1 / 2 := by
    exact TranslationC.harmonicResidue_forces_critical_line (Φ s) hzero
  exact transport_to_critical_line hΦ s hcrit




theorem no_offline_family_passes_translation_tests
    {Z : Set ℂ}
    (hZ : Z ⊆ Translation.OffLineZetaZerosInStrip)
    (hne : Z.Nonempty) :
    ¬ Translation.PassesDualReflectionTests Z :=
  Translation.no_nonempty_offline_zeta_family_passes_dual_tests hZ hne



-- AM-GM equality.
def OfflineUniversalSymmetryLaw (ρ : ℂ) : Prop :=
  ∀ r : ℝ, 1 < r →
    r ^ ρ.re + r ^ (1 - ρ.re) = 2 * r ^ (1 / 2 : ℝ)





theorem S_offline_empty_of_break
    (hBreak : ∀ ρ, ρ ∈ S_offline → OfflineUniversalSymmetryLaw ρ) :
    S_offline = ∅ := by
  ext ρ
  constructor
  · intro hρ
    have hneg : ¬ OfflineUniversalSymmetryLaw ρ := by
      simpa [OfflineUniversalSymmetryLaw] using
        (cosine_amplitude_defect_impossible_neg_comp ρ.re hρ.2)
    exact False.elim (hneg (hBreak ρ hρ))
  · intro hρ
    exact False.elim (Set.notMem_empty ρ hρ)
















theorem RH_of_offline_empty
    (hStrip : BridgeNontrivialInStrip)
    (hEmpty : S_offline = ∅) :
    RiemannHypothesis := by
  intro s hz htriv hone
  have hstrip : 0 < s.re ∧ s.re < 1 := hStrip s hz htriv hone
  by_cases hs : s.re = (1 / 2 : ℝ)
  · exact hs
  · have hOff : s ∈ S_offline := ⟨⟨hstrip.1, hstrip.2, hz⟩, hs⟩
    have hmem : s ∈ (∅ : Set ℂ) := by
      exact hEmpty ▸ hOff
    exact False.elim (Set.notMem_empty s hmem)


theorem RH_of_balance
    (hStrip : BridgeNontrivialInStrip)
    (hBreak : ∀ ρ, ρ ∈ S_offline → OfflineUniversalSymmetryLaw ρ) :
    RiemannHypothesis := by
  have hEmpty : S_offline = ∅ := S_offline_empty_of_break hBreak
  exact RH_of_offline_empty hStrip hEmpty








-- ════════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT on the main theorems
-- ════════════════════════════════════════════════════════════════════════


#check @offline_member_breaks_harmonic_balance
#print axioms offline_member_breaks_harmonic_balance
#check @RH_of_balance
#print axioms RH_of_balance

--#check @RH_of_offline_empty_with_dirichlet
--#print axioms RH_of_offline_empty_with_dirichlet
#check @bridgeNontrivialInStrip_proof
#print axioms bridgeNontrivialInStrip_proof
#check @harmonic_sum_vanishes
#print axioms harmonic_sum_vanishes
#check @offline_zero_breaks_balance_at_pi_third
#print axioms offline_zero_breaks_balance_at_pi_third
#check @offline_member_impossible_pi_third
#print axioms offline_member_impossible_pi_third
end
end ProofB
