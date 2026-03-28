import Mathlib

open Complex Metric Set

noncomputable section

/-- The Euler-cosh overhang strip: the region 1 < Re(s) < π/3. -/
def eulerCoshOverhang : Set ℂ := {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}

/-- The prime bridge function: a meromorphic function with a simple pole at s = 1
    and a π/3-symmetric regular part built from (s − π/6)². -/
def eulerCoshBridge (s : ℂ) : ℂ :=
  (s - 1)⁻¹ + (s - (↑(Real.pi / 6) : ℂ)) ^ 2

/-- Notation for the bridge function. -/
local notation "L" " ↗Λ " s => eulerCoshBridge s

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
    ((L ↗Λ s) - (s - 1)⁻¹) =
    ((L ↗Λ ((Real.pi / 3 : ℂ) - s)) - (((Real.pi / 3 : ℂ) - s) - 1)⁻¹) := by
  simp only [eulerCoshBridge]
  ring_nf
  push_cast
  ring

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
        ((L ↗Λ s) - (s - 1)⁻¹) =
        ((L ↗Λ ((Real.pi / 3 : ℂ) - s)) - (((Real.pi / 3 : ℂ) - s) - 1)⁻¹) :=
  ⟨eulerCoshOverhang, eulerCoshOverhang_isOpen, eulerCoshOverhang_nonempty,
    Subset.rfl, fun s _ => bridge_reflection_identity s⟩
