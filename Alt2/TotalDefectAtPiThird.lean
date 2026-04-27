import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.OfflineAmplitudeMethods
-- import RequestProject.OfflineDetectorProof
import RequestProject.KleinForcerScaffold
import RequestProject.WeilZeroSumClosedForm
import RequestProject.OfflineAmplitudeMethods
import RequestProject.PairCoshGaussTest
import RequestProject.GaussianDetectorPair
import RequestProject.WeilContour
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.WeilCoshPairPositivity
import RequestProject.WeilFinalAssembly
import RequestProject.WeilExplicitFormulaFromPerC
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.GaussianClosedForm
open ZetaDefs
/-!

# Total off-line amplitude defect at scale `r = π/3`

For a finite (multi)set of nontrivial zeta zeros `Z`, this file defines the
**total amplitude defect** at the natural support-endpoint scale `r = π/3`
and gives three closed-form expressions, all manifestly nonneg per term:

```
TotalDefect_{π/3}(Z, n) := ∑_{ρ ∈ Z}  n(ρ) · amplitudeDefect (π/3) ρ.re
```

Equivalent per-summand forms (proved as separate identities below):

* **AM-GM perfect square:**
  `amplitudeDefect (π/3) β = ((π/3)^(β/2) − (π/3)^((1−β)/2))²`
* **Cosh bridge:**
  `amplitudeDefect (π/3) β = 2·(π/3)^(1/2) · (cosh((β−1/2)·log(π/3)) − 1)`
* **sinh² half-angle:**
  `amplitudeDefect (π/3) β = 4·(π/3)^(1/2) · sinh²((β−1/2)·log(π/3)/2)`

Each summand is `≥ 0`, equals `0` iff `β = 1/2`, is FE-pair invariant in
`β ↔ 1 − β`, and the sum is therefore monotone-additive in offline zero
count: **no cancellation**.
-/

open Real Finset BigOperators ZetaDefs

noncomputable section

namespace ZD
namespace TotalDefectAtPiThird

/-! ## §1. Definitions -/

/-- Total amplitude defect at scale `r = π/3`, summed over a finite set of
zeros `Z` weighted by an external multiplicity function `n : ℂ → ℕ`. -/
def total (n : ℂ → ℕ) (Z : Finset ℂ) : ℝ :=
  ∑ ρ ∈ Z, (n ρ : ℝ) * amplitudeDefect (Real.pi / 3) ρ.re

/-- Unweighted variant (all multiplicities `1`). -/
def totalUnit (Z : Finset ℂ) : ℝ :=
  ∑ ρ ∈ Z, amplitudeDefect (Real.pi / 3) ρ.re

@[simp] lemma total_one_eq_totalUnit (Z : Finset ℂ) :
    total (fun _ => 1) Z = totalUnit Z := by
  unfold total totalUnit
  simp



/-! ## §2. Auxiliary half-angle identity -/

/-- Half-angle identity `cosh y − 1 = 2 · sinh²(y/2)`. -/
private lemma cosh_sub_one_eq_two_sinh_sq_half (y : ℝ) :
    Real.cosh y - 1 = 2 * Real.sinh (y / 2) ^ 2 := by
  have h := Real.cosh_two_mul (y / 2)
  have hy : 2 * (y / 2) = y := by ring
  rw [hy] at h
  have hs := Real.cosh_sq (y / 2)
  nlinarith [h, hs]

/-! ## §3. Per-term closed forms (specialisations of the ambient repo lemmas at
`r = π/3`) -/

/-- **Perfect-square form, per term.** -/
theorem amplitudeDefect_piThird_eq_sq (β : ℝ) :
    amplitudeDefect (Real.pi / 3) β =
      ((Real.pi / 3) ^ (β / 2) - (Real.pi / 3) ^ ((1 - β) / 2)) ^ 2 :=
  amplitudeDefect_eq_sq pi_third_pos β

/-- **Cosh-bridge form, per term.** -/
theorem amplitudeDefect_piThird_eq_cosh (β : ℝ) :
    amplitudeDefect (Real.pi / 3) β =
      2 * (Real.pi / 3) ^ ((1 : ℝ) / 2) *
        (Real.cosh ((β - 1/2) * Real.log (Real.pi / 3)) - 1) := by
  have h := WeilPositivity.KleinForcer.amplitudeDefect_eq_balanced_mul_coshExcess
              (r := Real.pi / 3) pi_third_pos β
  unfold balancedEnvelope coshDetector at h
  linarith [h]

/-- **sinh² half-angle form, per term.** -/
theorem amplitudeDefect_piThird_eq_sinh_sq (β : ℝ) :
    amplitudeDefect (Real.pi / 3) β =
      4 * (Real.pi / 3) ^ ((1 : ℝ) / 2) *
        Real.sinh ((β - 1/2) * Real.log (Real.pi / 3) / 2) ^ 2 := by
  have hc := amplitudeDefect_piThird_eq_cosh β
  have hh := cosh_sub_one_eq_two_sinh_sq_half
              ((β - 1/2) * Real.log (Real.pi / 3))
  rw [hc, hh]; ring

/-! ## §4. Total-defect closed forms -/

/-- **Perfect-square form for the total.** -/
theorem total_eq_sum_sq (n : ℂ → ℕ) (Z : Finset ℂ) :
    total n Z =
      ∑ ρ ∈ Z, (n ρ : ℝ) *
        ((Real.pi / 3) ^ (ρ.re / 2)
          - (Real.pi / 3) ^ ((1 - ρ.re) / 2)) ^ 2 := by
  unfold total
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [amplitudeDefect_piThird_eq_sq]

/-- **Cosh-bridge form for the total.** -/
theorem total_eq_cosh_form (n : ℂ → ℕ) (Z : Finset ℂ) :
    total n Z =
      ∑ ρ ∈ Z, (n ρ : ℝ) *
        (2 * (Real.pi / 3) ^ ((1 : ℝ) / 2) *
          (Real.cosh ((ρ.re - 1/2) * Real.log (Real.pi / 3)) - 1)) := by
  unfold total
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [amplitudeDefect_piThird_eq_cosh]

/-- **sinh² form for the total.**  Each summand is `n(ρ) · 4·√(π/3) · sinh²(…)`. -/
theorem total_eq_sinh_sq_form (n : ℂ → ℕ) (Z : Finset ℂ) :
    total n Z =
      ∑ ρ ∈ Z, (n ρ : ℝ) *
        (4 * (Real.pi / 3) ^ ((1 : ℝ) / 2) *
          Real.sinh ((ρ.re - 1/2) * Real.log (Real.pi / 3) / 2) ^ 2) := by
  unfold total
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [amplitudeDefect_piThird_eq_sinh_sq]

/-- **sinh² form, factored.** -/
theorem total_eq_sinh_sq_form_factored (n : ℂ → ℕ) (Z : Finset ℂ) :
    total n Z =
      4 * (Real.pi / 3) ^ ((1 : ℝ) / 2) *
        ∑ ρ ∈ Z, (n ρ : ℝ) *
          Real.sinh ((ρ.re - 1/2) * Real.log (Real.pi / 3) / 2) ^ 2 := by
  rw [total_eq_sinh_sq_form, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  ring

/-! ## §5. Nonnegativity, positivity, vanishing -/

/-- **Per-term nonnegativity.** -/
theorem amplitudeDefect_piThird_nonneg (β : ℝ) :
    0 ≤ amplitudeDefect (Real.pi / 3) β :=
  amplitudeDefect_nonneg pi_third_pos β

/-- **Per-term strict positivity at off-line `β`.** -/
theorem amplitudeDefect_piThird_pos_of_offline {β : ℝ} (hβ : β ≠ 1/2) :
    0 < amplitudeDefect (Real.pi / 3) β :=
  offline_amplitude_defect_pos pi_third_pos pi_third_ne_one hβ

/-- **Per-term vanishing on-line.** -/
@[simp] theorem amplitudeDefect_piThird_at_half :
    amplitudeDefect (Real.pi / 3) (1/2 : ℝ) = 0 := by
  rw [amplitudeDefect_piThird_eq_sq]
  have hExp : ((1 : ℝ) - 1/2) / 2 = (1 : ℝ)/2 / 2 := by ring
  rw [hExp]; ring

/-- **Total nonneg.** -/
theorem total_nonneg (n : ℂ → ℕ) (Z : Finset ℂ) :
    0 ≤ total n Z := by
  unfold total
  refine Finset.sum_nonneg (fun ρ _ => ?_)
  exact mul_nonneg (Nat.cast_nonneg _) (amplitudeDefect_piThird_nonneg _)

/-- **Total strict positivity** when `Z` contains an off-line zero with positive
multiplicity. -/
theorem total_pos_of_offline_mem (n : ℂ → ℕ) {Z : Finset ℂ}
    {ρ₀ : ℂ} (hρ₀_mem : ρ₀ ∈ Z) (hρ₀_off : ρ₀.re ≠ 1/2)
    (hn₀ : 0 < n ρ₀) :
    0 < total n Z := by
  unfold total
  rw [← Finset.sum_erase_add Z _ hρ₀_mem]
  apply add_pos_of_nonneg_of_pos
  · refine Finset.sum_nonneg (fun ρ _ => ?_)
    exact mul_nonneg (Nat.cast_nonneg _) (amplitudeDefect_piThird_nonneg _)
  · exact mul_pos (by exact_mod_cast hn₀)
      (amplitudeDefect_piThird_pos_of_offline hρ₀_off)

/-- **Vanishing iff all on-line** (under positive-multiplicity hypothesis). -/
theorem total_eq_zero_iff_all_online (n : ℂ → ℕ) (Z : Finset ℂ)
    (hn : ∀ ρ ∈ Z, 0 < n ρ) :
    total n Z = 0 ↔ ∀ ρ ∈ Z, ρ.re = (1/2 : ℝ) := by
  constructor
  · intro hzero ρ hρ
    by_contra hne
    have : 0 < total n Z :=
      total_pos_of_offline_mem n hρ hne (hn ρ hρ)
    linarith
  · intro hall
    unfold total
    refine Finset.sum_eq_zero (fun ρ hρ => ?_)
    rw [hall ρ hρ, amplitudeDefect_piThird_at_half]
    simp

/-- **Unit-multiplicity specialisations.** -/
theorem totalUnit_nonneg (Z : Finset ℂ) : 0 ≤ totalUnit Z := by
  rw [← total_one_eq_totalUnit]; exact total_nonneg _ _

theorem totalUnit_pos_of_offline_mem {Z : Finset ℂ} {ρ₀ : ℂ}
    (hρ₀_mem : ρ₀ ∈ Z) (hρ₀_off : ρ₀.re ≠ 1/2) :
    0 < totalUnit Z := by
  rw [← total_one_eq_totalUnit]
  exact total_pos_of_offline_mem _ hρ₀_mem hρ₀_off Nat.one_pos

/-! ## §6. Monotonicity in `Z` (no cancellation across set growth) -/

/-- **Monotonicity in the zero set.**  Adding zeros only increases the total. -/
theorem total_mono (n : ℂ → ℕ) {Z₁ Z₂ : Finset ℂ} (hsub : Z₁ ⊆ Z₂) :
    total n Z₁ ≤ total n Z₂ := by
  unfold total
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => ?_)
  exact mul_nonneg (Nat.cast_nonneg _) (amplitudeDefect_piThird_nonneg _)

/-- **FE-pair symmetry per term.**  `amplitudeDefect (π/3) β = amplitudeDefect (π/3) (1−β)`. -/
theorem amplitudeDefect_piThird_FE_symm (β : ℝ) :
    amplitudeDefect (Real.pi / 3) β = amplitudeDefect (Real.pi / 3) (1 - β) :=
  amplitudeDefect_symm (Real.pi / 3) β

/-! ## §7. Conversion to harmonic amplitude (and back)

The **harmonic amplitude excess** at scale `r` and offset `β` is the cosh-detector
excess
```
harmonicExcess r β  :=  coshDetector β (log r) − 1   =   cosh((β − 1/2) · log r) − 1.
```
This is the prime-side / Euler-product reading: it equals zero on-line, is
strictly positive offline (for `r ≠ 1`), and is what an Euler-product test against
`Λ(n)` would amplify per scale.  The **bridge** to the AM-GM amplitude defect
is multiplication by the balanced envelope `2·r^{1/2}`:
```
amplitudeDefect r β  =  2 · r^{1/2} · harmonicExcess r β             (forward)
harmonicExcess r β   =  amplitudeDefect r β / (2 · r^{1/2})           (back)
```
Both directions are unconditional and live on top of
`PrimeBoundedness.amplitudeDefect_eq_balanced_mul_coshExcess`.
-/

/-- The harmonic-amplitude excess at scale `r`, offset `β`. -/
def harmonicExcess (r β : ℝ) : ℝ := coshDetector β (Real.log r) - 1

/-- **Forward bridge:** AM-GM defect = balanced envelope × harmonic excess. -/
theorem amplitudeDefect_eq_two_rpow_half_mul_harmonicExcess
    {r : ℝ} (hr : 0 < r) (β : ℝ) :
    amplitudeDefect r β = 2 * r ^ ((1 : ℝ) / 2) * harmonicExcess r β := by
  have h := WeilPositivity.KleinForcer.amplitudeDefect_eq_balanced_mul_coshExcess
              (r := r) hr β
  unfold balancedEnvelope harmonicExcess at *
  linarith [h]

/-- **Back bridge:** harmonic excess recovered from AM-GM defect. -/
theorem harmonicExcess_eq_amplitudeDefect_div
    {r : ℝ} (hr : 0 < r) (β : ℝ) :
    harmonicExcess r β = amplitudeDefect r β / (2 * r ^ ((1 : ℝ) / 2)) := by
  have hpos : (0 : ℝ) < 2 * r ^ ((1 : ℝ) / 2) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _)
  have h := amplitudeDefect_eq_two_rpow_half_mul_harmonicExcess hr β
  field_simp
  linarith [h]

/-- **Round-trip identity:** forward ∘ back = identity (and vice versa). -/
theorem amplitudeDefect_round_trip
    {r : ℝ} (hr : 0 < r) (β : ℝ) :
    2 * r ^ ((1 : ℝ) / 2) *
        (amplitudeDefect r β / (2 * r ^ ((1 : ℝ) / 2))) = amplitudeDefect r β := by
  have hpos : (0 : ℝ) < 2 * r ^ ((1 : ℝ) / 2) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _)
  field_simp

/-- **Per-term π/3 specialisation.** -/
theorem amplitudeDefect_piThird_eq_harmonicExcess (β : ℝ) :
    amplitudeDefect (Real.pi / 3) β =
      2 * (Real.pi / 3) ^ ((1 : ℝ) / 2) * harmonicExcess (Real.pi / 3) β :=
  amplitudeDefect_eq_two_rpow_half_mul_harmonicExcess pi_third_pos β

/-- **Total at π/3 expressed as a harmonic-excess aggregate.** -/
theorem total_eq_harmonicExcess_sum_at_piThird (n : ℂ → ℕ) (Z : Finset ℂ) :
    total n Z =
      2 * (Real.pi / 3) ^ ((1 : ℝ) / 2) *
        ∑ ρ ∈ Z, (n ρ : ℝ) * harmonicExcess (Real.pi / 3) ρ.re := by
  unfold total
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [amplitudeDefect_piThird_eq_harmonicExcess]; ring

/-! ## §8. Per-prime and per-Λ(n) aggregates -/

/-- Total amplitude defect aggregated over a finite set of primes (or any positive
scales) `P` and zeros `Z`. -/
def totalOverScales (n : ℂ → ℕ) (Z : Finset ℂ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ∑ ρ ∈ Z, (n ρ : ℝ) * amplitudeDefect (p : ℝ) ρ.re

/-- Von-Mangoldt-weighted total aggregated over scales `N` and zeros `Z`. -/
def totalLambdaWeighted (n : ℂ → ℕ) (Z : Finset ℂ) (N : Finset ℕ) : ℝ :=
  ∑ m ∈ N, (ArithmeticFunction.vonMangoldt m : ℝ) *
    ∑ ρ ∈ Z, (n ρ : ℝ) * amplitudeDefect (m : ℝ) ρ.re

/-- **Per-scale aggregate ↔ harmonic-excess aggregate** (per-prime form, all
scales `> 0`). -/
theorem totalOverScales_eq_harmonicExcess_sum
    (n : ℂ → ℕ) (Z : Finset ℂ) {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) :
    totalOverScales n Z P =
      ∑ p ∈ P, 2 * (p : ℝ) ^ ((1 : ℝ) / 2) *
        ∑ ρ ∈ Z, (n ρ : ℝ) * harmonicExcess (p : ℝ) ρ.re := by
  unfold totalOverScales
  refine Finset.sum_congr rfl (fun p hp_mem => ?_)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp_mem
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [amplitudeDefect_eq_two_rpow_half_mul_harmonicExcess hp_pos]; ring

/-- **Λ-weighted aggregate ↔ harmonic-excess aggregate** (skips `m` with `Λ(m)=0`,
i.e. non-prime-powers; over genuine `m ≥ 1`). -/
theorem totalLambdaWeighted_eq_harmonicExcess_sum
    (n : ℂ → ℕ) (Z : Finset ℂ) {N : Finset ℕ} (hN : ∀ m ∈ N, 0 < m) :
    totalLambdaWeighted n Z N =
      ∑ m ∈ N, (ArithmeticFunction.vonMangoldt m : ℝ) *
        (2 * (m : ℝ) ^ ((1 : ℝ) / 2) *
          ∑ ρ ∈ Z, (n ρ : ℝ) * harmonicExcess (m : ℝ) ρ.re) := by
  unfold totalLambdaWeighted
  refine Finset.sum_congr rfl (fun m hm_mem => ?_)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hN m hm_mem
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [amplitudeDefect_eq_two_rpow_half_mul_harmonicExcess hm_pos]; ring

/-- **Inverse aggregate:** harmonic-excess sum recovers the per-scale defect sum. -/
theorem harmonicExcess_sum_recovers_totalOverScales
    (n : ℂ → ℕ) (Z : Finset ℂ) {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P, 2 * (p : ℝ) ^ ((1 : ℝ) / 2) *
        ∑ ρ ∈ Z, (n ρ : ℝ) * harmonicExcess (p : ℝ) ρ.re) =
      totalOverScales n Z P :=
  (totalOverScales_eq_harmonicExcess_sum n Z hP).symm

/-! ## §9. Properties of the harmonic-excess form (no-cancellation read-off) -/

/-- Per-term nonneg: `harmonicExcess r β ≥ 0` for `r > 0`. -/
theorem harmonicExcess_nonneg {r : ℝ} (hr : 0 < r) (β : ℝ) :
    0 ≤ harmonicExcess r β := by
  have h := amplitudeDefect_eq_two_rpow_half_mul_harmonicExcess hr β
  have hd : 0 ≤ amplitudeDefect r β := amplitudeDefect_nonneg hr β
  have hpos : (0 : ℝ) < 2 * r ^ ((1 : ℝ) / 2) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _)
  nlinarith [h, hd, hpos]

/-- Per-term strict positivity offline at any `r > 0, r ≠ 1`. -/
theorem harmonicExcess_pos_of_offline {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {β : ℝ} (hβ : β ≠ 1/2) : 0 < harmonicExcess r β := by
  have h := amplitudeDefect_eq_two_rpow_half_mul_harmonicExcess hr β
  have hd : 0 < amplitudeDefect r β := offline_amplitude_defect_pos hr hr1 hβ
  have hpos : (0 : ℝ) < 2 * r ^ ((1 : ℝ) / 2) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _)
  nlinarith [h, hd, hpos]

/-- Per-term vanishing on-line. -/
@[simp] theorem harmonicExcess_at_half (r : ℝ) :
    harmonicExcess r (1/2 : ℝ) = 0 := by
  unfold harmonicExcess coshDetector
  rw [show ((1/2 : ℝ) - 1/2) = 0 by ring, zero_mul, Real.cosh_zero]; ring

end TotalDefectAtPiThird
end ZD

end
