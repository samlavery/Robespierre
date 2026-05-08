import Mathlib
import RequestProject.CauchyKPairTestK2Weil
import RequestProject.CauchyKPairTestK2Discharges
import RequestProject.CauchyKPairTestFubiniSwap

/-!
# Unconditional per-t K_2-twisted whole-line Weil identity

For each `t : ℝ`, `β ∈ Ioo 0 1`:
```
∫_ℝ K_2(2+iy, t)·w(M)(2+iy) dy − ∫_ℝ K_2(-1+iy, t)·w(M)(-1+iy) dy
  = 2π·(K_2(1, t)·M(β, 1) − Σ' n(ρ)·K_2(ρ, t)·M(β, ρ))
```

Composes the conditional chunk-2 theorem at `K = K_2_fn t` with the four
discharged chunk-2 targets at `K_2_fn t`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 400000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorPlancherel

open ZD.WeilPositivity
open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZD.WeilPositivity.OfflineDetectorEndpoint
open ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch

/-- Canonical multiplicity function: `nMult ρ = analyticOrderAt ρ` at zeros, 0 otherwise. -/
private noncomputable def nMult : ℂ → ℕ := by
  classical
  exact fun ρ =>
    if hρ : ρ ∈ NontrivialZeros then
      Classical.choose (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ)
    else 0

private lemma nMult_at_nontrivialZero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    nMult ρ = Classical.choose
      (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hρ) := by
  classical
  simp [nMult, hρ]

/-- Canonical Z_at: nontrivial zeros in `[-1, 2] × [-T, T]`. -/
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

/-- **Unconditional per-t K_2-twisted whole-line Weil identity.**

For each `t : ℝ`, `β ∈ Ioo 0 1`, the integral identity
```
∫_ℝ K_2(2+iy, t)·w(M)(2+iy) dy − ∫_ℝ K_2(-1+iy, t)·w(M)(-1+iy) dy
  = 2π·(K_2(1, t)·M(β, 1) − Σ' n(ρ)·K_2(ρ, t)·M(β, ρ))
```
holds with `n` the canonical multiplicity. -/
theorem rectContourIntegral_K2_pairTestMellin_T_limit_unconditional
    (t : ℝ) (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    (∫ y : ℝ, K_2_fn t (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y : ℝ, K_2_fn t (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
        weilIntegrand (Contour.pairTestMellin β) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
    2 * ((Real.pi : ℝ) : ℂ) *
      (K_2_fn t 1 * Contour.pairTestMellin β 1 -
        ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          ((nMult ρ.val : ℕ) : ℂ) * K_2_fn t ρ.val * Contour.pairTestMellin β ρ.val) := by
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
  have h_horiz := K_2_fn_horizontal_vanishes_target_holds t β
  have h_int_pos := K_2_fn_vertical_at_two_integrable t β
  have h_int_neg := K_2_fn_vertical_at_neg_one_integrable t β
  have h_summ : K_pairTestMellin_zeroSum_summable (K_2_fn t) β nMult := by
    have := K_2_fn_zeroSum_summable_holds t β
    convert this using 2
  have h_res_tendsto : K_pairTestMellin_residue_sum_tendsto
      (K_2_fn t) β nMult ZAt :=
    K_pairTestMellin_residue_sum_tendsto_of_summable
      (K_2_fn t) β nMult ZAt hZ_in_NTZ hZ_complete_im h_summ
  exact rectContourIntegral_K2_pairTestMellin_T_limit
    t β hβ nMult ZAt hZ_mem hZ_complete
    h_horiz h_int_pos h_int_neg h_res_tendsto

#print axioms rectContourIntegral_K2_pairTestMellin_T_limit_unconditional

end OfflineDetectorPlancherel
end WeilPositivity
end ZD

end
