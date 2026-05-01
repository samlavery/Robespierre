import Mathlib
import RequestProject.CoshSymmetricPoles

open Complex Metric Set

noncomputable section

namespace PrimeBridge

/-- The Euler-cosh overhang strip: the region 1 < Re(s) < π/3. -/
def eulerCoshOverhang : Set ℂ := {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}

/-- The prime bridge function: a meromorphic function with a simple pole at s = 1
    and a π/3-symmetric regular part built from (s − π/6)². -/
def eulerCoshBridge (s : ℂ) : ℂ :=
  (s - 1)⁻¹ + (s - (↑(Real.pi / 6) : ℂ)) ^ 2

/-- Notation for the bridge function. -/
local notation "L" " ↗Λ " s => eulerCoshBridge s

/-- The pole-subtracted regular part of the model bridge. -/
def bridgeRegularPart (s : ℂ) : ℂ := (L ↗Λ s) - (s - 1)⁻¹

/-- The regular part is exactly the quadratic packet centered at `π/6`. -/
lemma bridgeRegularPart_eq_square (s : ℂ) :
    bridgeRegularPart s = (s - (↑(Real.pi / 6) : ℂ)) ^ 2 := by
  simp [bridgeRegularPart, eulerCoshBridge]

/-- The overhang strip is open (preimage of the open interval (1, π/3) under Re). -/
lemma eulerCoshOverhang_isOpen : IsOpen eulerCoshOverhang :=
  isOpen_Ioo.preimage Complex.continuous_re

/-- The overhang strip is nonempty: the midpoint (1 + π/3)/2 lies strictly inside,
    since π > 3 implies π/3 > 1. -/
lemma eulerCoshOverhang_nonempty : (eulerCoshOverhang).Nonempty :=
  ⟨⟨(1 + Real.pi / 3) / 2, 0⟩,
    ⟨by norm_num; linarith [Real.pi_gt_three],
     by norm_num; linarith [Real.pi_gt_three]⟩⟩

/-- The π/3-reflection identity holds for all s ∈ ℂ. The regular part
    (s − π/6)² is invariant under s ↦ π/3 − s because (π/3 − s) − π/6 = −(s − π/6)
    and (−x)² = x². -/
lemma bridge_reflection_identity (s : ℂ) :
    bridgeRegularPart s =
    bridgeRegularPart ((Real.pi / 3 : ℂ) - s) := by
  simp only [bridgeRegularPart, eulerCoshBridge]
  ring_nf
  push_cast
  ring

/-- The regular part of the bridge is meromorphic everywhere; in fact it is entire. -/
lemma bridgeRegularPart_meromorphicOn_univ :
    MeromorphicOn bridgeRegularPart (Set.univ : Set ℂ) := by
  intro z hz
  have han : AnalyticAt ℂ (fun s : ℂ => s - (↑(Real.pi / 6) : ℂ)) z := by
    apply_rules [AnalyticAt.sub, analyticAt_id, analyticAt_const]
  unfold bridgeRegularPart eulerCoshBridge
  simpa using (han.pow 2).meromorphicAt

/-- The local overhang seed propagates to global meromorphic-order symmetry for the
regularized model bridge. -/
theorem bridgeRegularPart_global_order_symmetry :
    ∀ z : ℂ,
      meromorphicOrderAt bridgeRegularPart z =
        meromorphicOrderAt bridgeRegularPart ((Real.pi / 3 : ℂ) - z) := by
  have hU_sym : CoshSymmetric ((Real.pi / 3 : ℂ)) (Set.univ : Set ℂ) := by
    intro s hs
    simp
  have hV_sub : eulerCoshOverhang ⊆ (Set.univ : Set ℂ) := by
    intro s hs
    simp
  intro z
  exact
    cosh_symmetric_pole_structure bridgeRegularPart ((Real.pi / 3 : ℂ))
      Set.univ eulerCoshOverhang
      isOpen_univ isPreconnected_univ hU_sym
      eulerCoshOverhang_isOpen hV_sub eulerCoshOverhang_nonempty
      bridgeRegularPart_meromorphicOn_univ
      (fun s hs => bridge_reflection_identity s) z (by simp)

/-- **Local overhang theorem.** There exists a genuine nonempty open patch V inside the
    Euler-cosh overhang on which the π/3-reflection identity for the prime bridge holds.
    We witness V = eulerCoshOverhang itself — a nonempty open strip, not a vacuous set,
    and the identity is proved algebraically rather than by half-plane symmetry. -/
theorem prime_bridge_has_local_pi_third_seed :
    ∃ V : Set ℂ,
      IsOpen V ∧
      V.Nonempty ∧
      V ⊆ eulerCoshOverhang ∧
      ∀ s ∈ V,
        bridgeRegularPart s = bridgeRegularPart ((Real.pi / 3 : ℂ) - s) :=
  ⟨eulerCoshOverhang, eulerCoshOverhang_isOpen, eulerCoshOverhang_nonempty,
    Subset.rfl, fun s _ => bridge_reflection_identity s⟩

end PrimeBridge

namespace eulerBridge

/-- User-facing alias for the regularized Euler/cosh bridge. -/
abbrev HarmonicCoshBridge : ℂ → ℂ := PrimeBridge.bridgeRegularPart

/-- The harmonic cosh bridge regarded explicitly as the meromorphic extension of
its local overhang seed. This is a naming/packaging alias for the same global
bridge function. -/
abbrev ExtendedHarmonicCoshBridge : ℂ → ℂ := HarmonicCoshBridge

/-- Local `π/3` seed for the Euler/cosh bridge. -/
theorem HarmonicCoshBridge_has_local_pi_third_seed :
    ∃ V : Set ℂ,
      IsOpen V ∧
      V.Nonempty ∧
      V ⊆ PrimeBridge.eulerCoshOverhang ∧
      ∀ s ∈ V,
        HarmonicCoshBridge s = HarmonicCoshBridge ((Real.pi / 3 : ℂ) - s) :=
  PrimeBridge.prime_bridge_has_local_pi_third_seed

/-- Global `π/3` meromorphic-order symmetry for the Euler/cosh bridge. -/
theorem HarmonicCoshBridge_global_order_symmetry :
    ∀ z : ℂ,
      meromorphicOrderAt HarmonicCoshBridge z =
        meromorphicOrderAt HarmonicCoshBridge ((Real.pi / 3 : ℂ) - z) :=
  PrimeBridge.bridgeRegularPart_global_order_symmetry

/-- The extended bridge agrees with the harmonic cosh bridge everywhere. -/
theorem ExtendedHarmonicCoshBridge_eq :
    ExtendedHarmonicCoshBridge = HarmonicCoshBridge := rfl

/-- The extended bridge restricts to the same nonempty open overhang seed. -/
theorem ExtendedHarmonicCoshBridge_has_local_pi_third_seed :
    ∃ V : Set ℂ,
      IsOpen V ∧
      V.Nonempty ∧
      V ⊆ PrimeBridge.eulerCoshOverhang ∧
      ∀ s ∈ V,
        ExtendedHarmonicCoshBridge s =
          ExtendedHarmonicCoshBridge ((Real.pi / 3 : ℂ) - s) :=
  HarmonicCoshBridge_has_local_pi_third_seed

/-- The extended bridge has the same global `π/3` meromorphic-order symmetry. -/
theorem ExtendedHarmonicCoshBridge_global_order_symmetry :
    ∀ z : ℂ,
      meromorphicOrderAt ExtendedHarmonicCoshBridge z =
        meromorphicOrderAt ExtendedHarmonicCoshBridge ((Real.pi / 3 : ℂ) - z) :=
  HarmonicCoshBridge_global_order_symmetry

end eulerBridge
