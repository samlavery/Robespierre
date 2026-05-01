import Mathlib
import RequestProject.MellinPathToXi
import RequestProject.WeilWholeLineIdentity
import RequestProject.WeilZeroSumSplitClosedForm
import RequestProject.PairComboClosurePaths
import RequestProject.H3SubstantiveContent

/-!
# H3 via the theta/xi route
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace ZD.WeilPositivity.H3ViaThetaXi

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.PairTestIdentity
open ZD.WeilPositivity.ZeroSumSplit

/-! ## § 1.  The pointwise theta/xi value at zeros (multiplicity-weighted)

This is the cleanest exploitation of `observable_value_at_zero`: for
every nontrivial zero `ρ`, the multiplicity-weighted value of the
theta-side observable is

```
n(ρ) · I_theta_of ψ_mellin ρ  =  - n(ρ) / (ρ·(ρ-1)).
```
-/

/-- **Pointwise zero-side identity (theta route).**  At every nontrivial
zero `ρ`, the multiplicity-weighted value of the theta-derived
observable `I_theta_of ψ_mellin` equals `-n(ρ)/(ρ·(ρ-1))`.

This is the per-summand statement of the theta-side closed form.  It is
**unconditional** (axiom-clean): it relies only on
`observable_value_at_zero` (`MellinPathToXi.lean:1234`).

Note that this gives an explicit value for the `I_theta_of ψ_mellin`
zero sum — it does *not* give a value for the
`pairTestMellin β`-based zero sum that appears in the H3 closed-form
chain. -/
theorem multZ_I_theta_value_at_zero
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    (((Classical.choose
        (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
      ZD.I_theta_of ZD.ψ_mellin ρ.val =
    - (((Classical.choose
        (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) /
      (ρ.val * (ρ.val - 1)) := by
  have h := ZD.observable_value_at_zero ρ.val ρ.property
  rw [h]
  ring

#print axioms multZ_I_theta_value_at_zero

/-- **Non-vanishing at zeros.**  At every nontrivial zero,
`I_theta_of ψ_mellin ρ ≠ 0`.  Each zero contributes a non-zero amount
to the theta-side residue sum.  This is a structural handle: any
identity equating the theta-side zero sum to zero would force
contradictions; the theta-side sum is genuinely non-trivial. -/
theorem I_theta_psi_mellin_at_zero_ne_zero
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ZD.I_theta_of ZD.ψ_mellin ρ ≠ 0 := by
  rw [ZD.observable_value_at_zero ρ hρ]
  have hρ_re_pos : 0 < ρ.re := hρ.1
  have hρ_re_lt_one : ρ.re < 1 := hρ.2.1
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hρ_re_pos; linarith
  have hρ_ne_one : ρ ≠ 1 := by
    intro h1; rw [h1, Complex.one_re] at hρ_re_lt_one; linarith
  have hρ_sub_one_ne_zero : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ_ne_one
  have hprod_ne_zero : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ_ne_zero hρ_sub_one_ne_zero
  intro h
  have h1 : (-1 : ℂ) / (ρ * (ρ - 1)) * (ρ * (ρ - 1)) = 0 * (ρ * (ρ - 1)) := by
    rw [h]
  rw [div_mul_cancel₀ (-1 : ℂ) hprod_ne_zero, zero_mul] at h1
  exact one_ne_zero (by linear_combination -h1)

#print axioms I_theta_psi_mellin_at_zero_ne_zero

/-! ## § 2.  Theta-side closed form (per-zero identity, summed)

The closest one can get to a "theta/xi route to H3" is the following
per-zero identity, which **does** give a closed form for the
*theta-side* zero observable but NOT for the cosh-Gauss zero sum
appearing in H3.
-/

/-- **Theta-side zero sum closed form (formal).**  By `tsum_congr`,
the theta-side multiplicity-weighted zero sum equals the
multiplicity-weighted `-n(ρ)/(ρ(ρ-1))` series term-by-term.

This is a **fully unconditional** identity: it holds whether or not
either side is summable.  When both are summable, they have the same
value; when neither is, both are `0` by `tsum`'s convention.

This is the cleanest, axiom-clean theta/xi-side statement that can be
extracted from the existing infrastructure. -/
theorem theta_zero_sum_eq_neg_multZ_div_sum :
    (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (((Classical.choose
          (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
        ZD.I_theta_of ZD.ψ_mellin ρ.val)
    =
    (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        - (((Classical.choose
          (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) /
          (ρ.val * (ρ.val - 1))) := by
  refine tsum_congr ?_
  intro ρ
  exact multZ_I_theta_value_at_zero ρ

#print axioms theta_zero_sum_eq_neg_multZ_div_sum

/-! ## § 3.  Σ'(β) — the multiplicity-weighted cosh-Gauss zero sum -/

/-- The multiplicity-weighted cosh-Gauss zero sum. -/
def SigmaPair (β : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    (((Classical.choose
      (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
    pairTestMellin β ρ.val

/-- **`SigmaPair` is exactly the Σ' appearing in `H3_iff_archDiff`.**
Sanity-check identity used downstream. -/
theorem SigmaPair_def (β : ℝ) :
    SigmaPair β =
    (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (((Classical.choose
        (analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ.property) : ℕ) : ℂ)) *
      pairTestMellin β ρ.val) := rfl

#print axioms SigmaPair_def

def H3_via_theta_xi_bridge : Prop :=
  ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
    ∃ V : ℂ,
      SigmaPair β = V

theorem H3_via_theta_xi_bridge_holds_trivially :
    H3_via_theta_xi_bridge := by
  intro β _hβ
  refine ⟨SigmaPair β, ?_⟩
  rfl

#print axioms H3_via_theta_xi_bridge_holds_trivially

end ZD.WeilPositivity.H3ViaThetaXi

end
