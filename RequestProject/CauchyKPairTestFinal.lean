import Mathlib
import RequestProject.CauchyKPairTestLimit
import RequestProject.CauchyKPairTestVerticalIntegrable
import RequestProject.CauchyKPairTestResidueSum
import RequestProject.CauchyKPairTestHorizontal

/-!
# Final assembly: unconditional K-twisted whole-line Weil identity

Composes chunks 1 + 2 with the four discharged chunk-2 targets to deliver
the **unconditional** K-twisted whole-line Weil identity for
`K = gaussianDefectEntireKernel_local`:

```
∫_ℝ K(2+iy)·w(M)(2+iy) dy − ∫_ℝ K(-1+iy)·w(M)(-1+iy) dy
  = 2π · (K(1)·M(β,1) − Σ' n(ρ)·K(ρ)·M(β,ρ))
```

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly

/-- Canonical multiplicity function on `ℂ`. -/
noncomputable def nMult : ℂ → ℕ := by
  classical
  exact fun ρ =>
    if hρ : ρ ∈ NontrivialZeros then
      Classical.choose (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
    else 0

lemma nMult_at_nontrivialZero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    nMult ρ = Classical.choose
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ) := by
  classical
  simp [nMult, hρ]

/-- Canonical Z_at: nontrivial zeros in `[-1, 2] × [-T, T]`, lifted to a
`Finset ℂ` from the subtype-level finite set provided by
`h_fin_unconditional`. -/
private noncomputable def ZAt : ℝ → Finset ℂ := fun T =>
  ((ZD.WeilPositivity.FinalAssembly.h_fin_unconditional T).toFinset).image
    (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => ρ.val)

private lemma ZAt_mem_iff (T : ℝ) (ρ : ℂ) :
    ρ ∈ ZAt T ↔ ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T := by
  simp only [ZAt, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨ρ', hρ'⟩, ⟨hre1, hre2, him1, him2⟩, hval⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp at hval; rw [← hval]; exact hρ'
    · simp at hval; rw [← hval]; exact hre1
    · simp at hval; rw [← hval]; exact hre2
    · simp at hval; rw [← hval]; exact him1
    · simp at hval; rw [← hval]; exact him2
  · intro ⟨hNZ, hre1, hre2, him1, him2⟩
    refine ⟨⟨ρ, hNZ⟩, ⟨hre1, hre2, him1, him2⟩, rfl⟩

/-- **Unconditional K-twisted whole-line Weil identity** for
`K = gaussianDefectEntireKernel_local`.

Combines chunks 1 + 2 with the four discharged chunk-2 targets:
- vertical at Re=2 integrable,
- vertical at Re=-1 integrable,
- residue-sum tendsto + summability (via `K_pairTestMellin_zeroSum_summable_holds`),
- horizontal vanishing.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_K_pairTestMellin_T_limit_unconditional
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∫ y : ℝ, gaussianDefectEntireKernel_local (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y : ℝ, gaussianDefectEntireKernel_local (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
    2 * ((Real.pi : ℝ) : ℂ) *
      (gaussianDefectEntireKernel_local 1 * Contour.pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          ((nMult ρ.val : ℕ) : ℂ) * gaussianDefectEntireKernel_local ρ.val *
            Contour.pairTestMellin β ρ.val) := by
  have hK_diff : Differentiable ℂ gaussianDefectEntireKernel_local := by
    unfold gaussianDefectEntireKernel_local
    have h1 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 2)) :=
      (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
    have h2 : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - (1/2 : ℂ))^2 / 8)) :=
      (((differentiable_id.sub (differentiable_const _)).pow 2).div_const _).cexp
    exact (differentiable_const _).mul (((h1.sub ((differentiable_const _).mul h2)).add
      (differentiable_const _)))
  have hZ_mem : ∀ T : ℝ, 1 < T → goodHeight T → ∀ ρ ∈ ZAt T,
      ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T ∧
      analyticOrderAt riemannZeta ρ = (nMult ρ : ℕ∞) := by
    intro T _ _ ρ hρ
    rw [ZAt_mem_iff] at hρ
    obtain ⟨hNZ, hre1, hre2, him1, him2⟩ := hρ
    refine ⟨hNZ, hre1, hre2, him1, him2, ?_⟩
    rw [nMult_at_nontrivialZero hNZ]
    exact (Classical.choose_spec
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hNZ)).2
  have hZ_complete : ∀ T : ℝ, 1 < T → goodHeight T → ∀ ρ : ℂ,
      ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ ZAt T := by
    intro T _ _ ρ hNZ hre1 hre2 him1 him2
    rw [ZAt_mem_iff]
    exact ⟨hNZ, hre1, hre2, him1, him2⟩
  have hZ_in_NTZ : ∀ T : ℝ, ∀ ρ ∈ ZAt T, ρ ∈ NontrivialZeros := fun T ρ hρ =>
    ((ZAt_mem_iff T ρ).mp hρ).1
  have hZ_complete_im : ∀ T : ℝ, ∀ ρ : ℂ,
      ρ ∈ NontrivialZeros → -T < ρ.im → ρ.im < T → ρ ∈ ZAt T := by
    intro T ρ hNZ him1 him2
    rw [ZAt_mem_iff]
    have hRe1 : (0 : ℝ) < ρ.re := hNZ.1
    have hRe2 : ρ.re < 1 := hNZ.2.1
    exact ⟨hNZ, by linarith, by linarith, him1, him2⟩
  have h_horiz := K_pairTestMellin_horizontal_vanishes_target_holds β
  have h_int_pos := K_pairTestMellin_vertical_at_two_integrable_holds β
  have h_int_neg := K_pairTestMellin_vertical_at_neg_one_integrable_holds β
  have h_summ : K_pairTestMellin_zeroSum_summable
      gaussianDefectEntireKernel_local β nMult := by
    have := K_pairTestMellin_zeroSum_summable_holds β
    convert this using 2
  have h_res_tendsto : K_pairTestMellin_residue_sum_tendsto
      gaussianDefectEntireKernel_local β nMult ZAt :=
    K_pairTestMellin_residue_sum_tendsto_of_summable
      gaussianDefectEntireKernel_local β nMult ZAt hZ_in_NTZ hZ_complete_im h_summ
  exact rectContourIntegral_K_pairTestMellin_T_limit
    gaussianDefectEntireKernel_local hK_diff β hβ nMult ZAt hZ_mem hZ_complete
    h_horiz h_int_pos h_int_neg h_res_tendsto

#print axioms rectContourIntegral_K_pairTestMellin_T_limit_unconditional

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
