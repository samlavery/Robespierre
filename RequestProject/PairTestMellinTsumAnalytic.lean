import Mathlib
import RequestProject.PairTestMellinComplexBeta
import RequestProject.PairTestMellinUniformBound
import RequestProject.NaturalKCoefficientAdmissible
import RequestProject.WeilZeroSum

/-!
# Real-analytic tsum: discharge of `tsum_analytic_pairTestMellin_target`

Discharges the Weierstrass step for the K-route admissibility chain:

```
β ↦ Σ' a_K(ρ) · pairTestMellin β ρ   is real-analytic on Set.univ
```

via the complex-β extension `pairTestMellinC` (entire in z) +
`SummableLocallyUniformlyOn.differentiableOn` (mathlib) + restriction to ℝ.

The key ingredient is the **uniform-in-c strip bound** for `coshGaussMellinC`:
for `‖c‖ ≤ R`, the Mellin transform satisfies
`‖coshGaussMellinC c ρ‖ ≤ M(R) / ‖ρ(ρ+1)(ρ+2)(ρ+3)‖` for all ρ ∈ NTZ,
with `M(R) = exp(R²/4) · ∫₀^∞ (t³+t⁴) · poly(t, R) · exp(-t²) dt` finite.

Combined with the K-coefficient bound and Jensen quartic-summability, this
gives the locally uniform majorant on every complex compact, hence
`SummableLocallyUniformlyOn`, hence `DifferentiableOn ℂ` on `Set.univ`,
hence analytic, hence real-analytic on ℝ via `restrictScalars + ofRealCLM`.
-/

set_option maxHeartbeats 800000

open Complex Real Set MeasureTheory

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-! ## §1 — Polynomial dominator for `‖coshGaussDeriv4ValC c t‖` uniform in c -/

/-- Polynomial dominator for `coshGaussDeriv4ValC c t` uniform in `‖c‖ ≤ R`. -/
def coshGaussDeriv4ValC_polyR (R : ℝ) (t : ℝ) : ℝ :=
  256 * t^4 + 384 * t^2 + 96 * R^2 * t^2 + R^4 + 24 * R^2 + 48 +
    192 * R * t + 16 * R^3 * t + 256 * R * t^3

/-- The polynomial dominator is monotone in `R` for `R ≥ 0`. -/
private lemma coshGaussDeriv4ValC_polyR_mono_in_R (R₁ R₂ : ℝ) (h₁ : 0 ≤ R₁)
    (h₁₂ : R₁ ≤ R₂) (t : ℝ) (ht : 0 ≤ t) :
    coshGaussDeriv4ValC_polyR R₁ t ≤ coshGaussDeriv4ValC_polyR R₂ t := by
  have h₂ : 0 ≤ R₂ := h₁.trans h₁₂
  unfold coshGaussDeriv4ValC_polyR
  have hR1sq : R₁^2 ≤ R₂^2 := by nlinarith
  have hR1cube : R₁^3 ≤ R₂^3 := by nlinarith [sq_nonneg R₁, sq_nonneg R₂]
  have hR1quart : R₁^4 ≤ R₂^4 := by nlinarith [sq_nonneg (R₁^2), sq_nonneg (R₂^2)]
  have ht2 : 0 ≤ t^2 := sq_nonneg t
  have ht3 : 0 ≤ t^3 := by positivity
  nlinarith [hR1sq, hR1cube, hR1quart, ht2, ht3, ht]

/-- **Pointwise norm bound on `coshGaussDeriv4ValC` uniform in `‖c‖ ≤ R`.**
Combines `norm_coshGaussDeriv4ValC_le_gauss` with monotonicity of the
polynomial in `‖c‖`. -/
theorem norm_coshGaussDeriv4ValC_uniform_in_c (R : ℝ) (hR : 0 ≤ R)
    {c : ℂ} (hc : ‖c‖ ≤ R) {t : ℝ} (ht : 0 < t) :
    ‖coshGaussDeriv4ValC c t‖ ≤
      Real.exp (R^2 / 4) * coshGaussDeriv4ValC_polyR R t * Real.exp (-t^2) := by
  have hc_nn : 0 ≤ ‖c‖ := norm_nonneg _
  have h_per_c := norm_coshGaussDeriv4ValC_le_gauss c ht
  -- Bound exp(‖c‖²/4) by exp(R²/4)
  have hc_sq_le : ‖c‖^2 ≤ R^2 := by
    have := mul_self_le_mul_self hc_nn hc
    rw [← sq, ← sq] at this; exact this
  have h_exp_le : Real.exp (‖c‖^2 / 4) ≤ Real.exp (R^2 / 4) :=
    Real.exp_le_exp.mpr (by linarith)
  -- Bound the polynomial monotonically
  have h_poly_le : (256 * t^4 + 384 * t^2 + 96 * ‖c‖^2 * t^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 +
        192 * ‖c‖ * t + 16 * ‖c‖^3 * t + 256 * ‖c‖ * t^3) ≤
      coshGaussDeriv4ValC_polyR R t :=
    coshGaussDeriv4ValC_polyR_mono_in_R ‖c‖ R hc_nn hc t ht.le
  have h_exp_neg_pos : 0 < Real.exp (-t^2) := Real.exp_pos _
  have h_poly_pos_left : 0 ≤ Real.exp (‖c‖^2 / 4) * (256 * t^4 + 384 * t^2 +
      96 * ‖c‖^2 * t^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 + 192 * ‖c‖ * t + 16 * ‖c‖^3 * t +
      256 * ‖c‖ * t^3) := by
    apply mul_nonneg (Real.exp_pos _).le
    have ht2 : 0 ≤ t^2 := sq_nonneg _
    have ht3 : 0 ≤ t^3 := by positivity
    have ht4 : 0 ≤ t^4 := by positivity
    have hc2 : 0 ≤ ‖c‖^2 := sq_nonneg _
    have hc3 : 0 ≤ ‖c‖^3 := by positivity
    have hc4 : 0 ≤ ‖c‖^4 := by positivity
    nlinarith
  have h_poly_R_nn : 0 ≤ coshGaussDeriv4ValC_polyR R t := by
    unfold coshGaussDeriv4ValC_polyR
    have ht2 : 0 ≤ t^2 := sq_nonneg _
    have ht3 : 0 ≤ t^3 := by positivity
    have ht4 : 0 ≤ t^4 := by positivity
    have hR2 : 0 ≤ R^2 := sq_nonneg _
    have hR3 : 0 ≤ R^3 := by positivity
    have hR4 : 0 ≤ R^4 := by positivity
    nlinarith
  set P_c : ℝ := 256 * t^4 + 384 * t^2 + 96 * ‖c‖^2 * t^2 + ‖c‖^4 + 24 * ‖c‖^2 + 48 +
        192 * ‖c‖ * t + 16 * ‖c‖^3 * t + 256 * ‖c‖ * t^3 with hP_c_def
  have hP_c_nn : 0 ≤ P_c := by
    have ht2 : 0 ≤ t^2 := sq_nonneg _
    have ht3 : 0 ≤ t^3 := by positivity
    have ht4 : 0 ≤ t^4 := by positivity
    have hc2 : 0 ≤ ‖c‖^2 := sq_nonneg _
    have hc3 : 0 ≤ ‖c‖^3 := by positivity
    have hc4 : 0 ≤ ‖c‖^4 := by positivity
    rw [hP_c_def]; nlinarith
  have h_step1 : ‖coshGaussDeriv4ValC c t‖ ≤
      P_c * (Real.exp (‖c‖ * t) * Real.exp (-2 * t^2)) := by
    have h_pre := norm_coshGaussDeriv4ValC_le c t
    rw [abs_of_pos ht] at h_pre
    rw [hP_c_def]; linarith [h_pre]
  have h_exp_factor : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) ≤
      Real.exp (‖c‖^2 / 4) * Real.exp (-t^2) := by
    -- exp(‖c‖·t - 2t²) ≤ exp(‖c‖²/4) · exp(-t²): complete the square.
    have heq : Real.exp (‖c‖ * t) * Real.exp (-2 * t^2) =
        Real.exp (‖c‖ * t - 2 * t^2) := by rw [← Real.exp_add]; ring_nf
    rw [heq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (‖c‖/2 - t)]
  have h_step2 : ‖coshGaussDeriv4ValC c t‖ ≤
      P_c * (Real.exp (‖c‖^2 / 4) * Real.exp (-t^2)) := by
    refine h_step1.trans ?_
    exact mul_le_mul_of_nonneg_left h_exp_factor hP_c_nn
  -- Now bound P_c ≤ polyR R t and exp(‖c‖²/4) ≤ exp(R²/4).
  have h_P_le_R : P_c ≤ coshGaussDeriv4ValC_polyR R t := by
    rw [hP_c_def]; exact coshGaussDeriv4ValC_polyR_mono_in_R ‖c‖ R hc_nn hc t ht.le
  have h_polyR_nn : 0 ≤ coshGaussDeriv4ValC_polyR R t := hP_c_nn.trans h_P_le_R
  -- Combine.
  have h_exp_pos : 0 < Real.exp (-t^2) := Real.exp_pos _
  calc ‖coshGaussDeriv4ValC c t‖
      ≤ P_c * (Real.exp (‖c‖^2 / 4) * Real.exp (-t^2)) := h_step2
    _ = P_c * Real.exp (‖c‖^2 / 4) * Real.exp (-t^2) := by ring
    _ ≤ coshGaussDeriv4ValC_polyR R t * Real.exp (R^2 / 4) * Real.exp (-t^2) := by
        apply mul_le_mul_of_nonneg_right _ h_exp_pos.le
        exact mul_le_mul h_P_le_R h_exp_le (Real.exp_pos _).le h_polyR_nn
    _ = Real.exp (R^2 / 4) * coshGaussDeriv4ValC_polyR R t * Real.exp (-t^2) := by ring

#print axioms norm_coshGaussDeriv4ValC_uniform_in_c

/-! ## §2 — Integrability of the dominator times `(t³+t⁴)` -/

/-- The integrand `(t³+t⁴) · exp(R²/4) · polyR R t · exp(-t²)` is
integrable on `(0,∞)` for every `R ≥ 0`. -/
theorem coshGaussDeriv4ValC_dominator_t34_integrable (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ =>
      (t^3 + t^4) * (Real.exp (R^2 / 4) * coshGaussDeriv4ValC_polyR R t *
        Real.exp (-t^2))) (Set.Ioi 0) volume := by
  set K : ℝ := Real.exp (R^2 / 4)
  -- Each `t^n · exp(-t^2)` is integrable on Ioi 0 (template from
  -- `coshGaussDeriv4ValC_t34_norm_integrable`).
  have h_pow_int : ∀ (n : ℕ),
      IntegrableOn (fun t : ℝ => t^n * Real.exp (-t^2)) (Set.Ioi 0) volume := by
    intro n
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) (s := (n : ℝ))
      (by norm_num : (0:ℝ) < 1)
      (by have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _; linarith)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t _
    show t^((n : ℝ)) * Real.exp (-1 * t^2) = t^n * Real.exp (-t^2)
    rw [show (-1 * t^2 : ℝ) = -t^2 from by ring,
        show ((n : ℝ)) = ((n : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  -- Expand `(t^3 + t^4) * polyR R t` into a sum of monomials t^k for k ∈ {3..8},
  -- each scaled by a constant in (R, K). Sum of integrables.
  set domF : ℝ → ℝ := fun t =>
    K * 256 * (t^7 * Real.exp (-t^2)) +
    K * 384 * (t^5 * Real.exp (-t^2)) +
    K * (96 * R^2) * (t^5 * Real.exp (-t^2)) +
    K * R^4 * (t^3 * Real.exp (-t^2)) +
    K * (24 * R^2) * (t^3 * Real.exp (-t^2)) +
    K * 48 * (t^3 * Real.exp (-t^2)) +
    K * (192 * R) * (t^4 * Real.exp (-t^2)) +
    K * (16 * R^3) * (t^4 * Real.exp (-t^2)) +
    K * (256 * R) * (t^6 * Real.exp (-t^2)) +
    K * 256 * (t^8 * Real.exp (-t^2)) +
    K * 384 * (t^6 * Real.exp (-t^2)) +
    K * (96 * R^2) * (t^6 * Real.exp (-t^2)) +
    K * R^4 * (t^4 * Real.exp (-t^2)) +
    K * (24 * R^2) * (t^4 * Real.exp (-t^2)) +
    K * 48 * (t^4 * Real.exp (-t^2)) +
    K * (192 * R) * (t^5 * Real.exp (-t^2)) +
    K * (16 * R^3) * (t^5 * Real.exp (-t^2)) +
    K * (256 * R) * (t^7 * Real.exp (-t^2)) with hdomF_def
  have h_domF_int : IntegrableOn domF (Set.Ioi 0) volume :=
    ((((((((((((((((((h_pow_int 7).const_mul (K * 256)).add
      ((h_pow_int 5).const_mul (K * 384))).add
      ((h_pow_int 5).const_mul (K * (96 * R^2)))).add
      ((h_pow_int 3).const_mul (K * R^4))).add
      ((h_pow_int 3).const_mul (K * (24 * R^2)))).add
      ((h_pow_int 3).const_mul (K * 48))).add
      ((h_pow_int 4).const_mul (K * (192 * R)))).add
      ((h_pow_int 4).const_mul (K * (16 * R^3)))).add
      ((h_pow_int 6).const_mul (K * (256 * R)))).add
      ((h_pow_int 8).const_mul (K * 256))).add
      ((h_pow_int 6).const_mul (K * 384))).add
      ((h_pow_int 6).const_mul (K * (96 * R^2)))).add
      ((h_pow_int 4).const_mul (K * R^4))).add
      ((h_pow_int 4).const_mul (K * (24 * R^2)))).add
      ((h_pow_int 4).const_mul (K * 48))).add
      ((h_pow_int 5).const_mul (K * (192 * R)))).add
      ((h_pow_int 5).const_mul (K * (16 * R^3)))).add
      ((h_pow_int 7).const_mul (K * (256 * R)))
  -- Show our integrand equals domF on Ioi 0.
  refine h_domF_int.congr_fun ?_ measurableSet_Ioi
  intro t _
  unfold coshGaussDeriv4ValC_polyR
  simp only [hdomF_def]
  ring

#print axioms coshGaussDeriv4ValC_dominator_t34_integrable

/-! ## §3 — Uniform-in-c quartic strip bound for `coshGaussMellinC` -/

/-- The uniform M-constant for `‖c‖ ≤ R`. -/
noncomputable def coshGaussMellinC_uniformBound (R : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), (t^3 + t^4) *
    (Real.exp (R^2 / 4) * coshGaussDeriv4ValC_polyR R t * Real.exp (-t^2))

/-- The uniform bound is nonneg. -/
theorem coshGaussMellinC_uniformBound_nonneg (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ coshGaussMellinC_uniformBound R := by
  unfold coshGaussMellinC_uniformBound
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have ht_pos : (0:ℝ) < t := ht
  have hP_nn : 0 ≤ coshGaussDeriv4ValC_polyR R t := by
    unfold coshGaussDeriv4ValC_polyR
    have ht2 : 0 ≤ t^2 := sq_nonneg _
    have ht3 : 0 ≤ t^3 := by positivity
    have ht4 : 0 ≤ t^4 := by positivity
    have hR2 : 0 ≤ R^2 := sq_nonneg _
    have hR3 : 0 ≤ R^3 := by positivity
    have hR4 : 0 ≤ R^4 := by positivity
    nlinarith
  positivity

/-- **Uniform-in-c quartic strip bound for `coshGaussMellinC`.**
For all `c` with `‖c‖ ≤ R` and all ρ ∈ NTZ, the Mellin transform
satisfies `‖coshGaussMellinC c ρ‖ ≤ M(R) / ‖ρ(ρ+1)(ρ+2)(ρ+3)‖`. -/
theorem coshGaussMellinC_strip_bound_uniform_in_c (R : ℝ) (hR : 0 ≤ R) :
    ∀ c : ℂ, ‖c‖ ≤ R →
      ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ‖coshGaussMellinC c ρ.val‖ ≤
          coshGaussMellinC_uniformBound R *
            (1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖) := by
  intro c hc ρ
  obtain ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
  -- IBP×4 reduces to bounding the inner Mellin integral by uniformBound.
  have h_ibp := coshGaussMellinC_ibp_four_times c (s := ρ.val) hRe_pos
  set M_unif : ℝ := coshGaussMellinC_uniformBound R with hM_def
  have hM_nn : 0 ≤ M_unif := coshGaussMellinC_uniformBound_nonneg R hR
  -- Bound the Mellin integrand pointwise.
  have h_mellin_bd : ‖mellin (coshGaussDeriv4ValC c) (ρ.val + 4)‖ ≤ M_unif := by
    unfold mellin
    have h_re_eq : (ρ.val + 4 - 1).re = ρ.val.re + 3 := by
      have : (ρ.val + 4 - 1).re = ρ.val.re + 4 - 1 := by simp
      linarith
    have h_norm_eq : ∀ t > (0:ℝ),
        ‖(t : ℂ) ^ (ρ.val + 4 - 1) • coshGaussDeriv4ValC c t‖ =
        t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ := by
      intro t ht
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, h_re_eq]
    -- Step 1: bound by integral of norm.
    have h_step1 : ‖∫ t in Set.Ioi (0:ℝ),
            (t : ℂ) ^ (ρ.val + 4 - 1) • coshGaussDeriv4ValC c t‖ ≤
        ∫ t in Set.Ioi (0:ℝ), t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ := by
      calc ‖∫ t in Set.Ioi (0:ℝ),
              (t : ℂ) ^ (ρ.val + 4 - 1) • coshGaussDeriv4ValC c t‖
          ≤ ∫ t in Set.Ioi (0:ℝ),
              ‖(t : ℂ) ^ (ρ.val + 4 - 1) • coshGaussDeriv4ValC c t‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ = ∫ t in Set.Ioi (0:ℝ), t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro t ht; exact h_norm_eq t ht
    -- Step 2: pointwise bound: t^(Reρ+3) · ‖deriv4 c t‖ ≤ (t^3+t^4) · uniform-dominator.
    have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
        t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ ≤
        (t^3 + t^4) * (Real.exp (R^2 / 4) * coshGaussDeriv4ValC_polyR R t *
          Real.exp (-t^2)) := by
      intro t ht
      have ht_pos : (0:ℝ) < t := ht
      have h_norm_bd : ‖coshGaussDeriv4ValC c t‖ ≤
          Real.exp (R^2 / 4) * coshGaussDeriv4ValC_polyR R t * Real.exp (-t^2) :=
        norm_coshGaussDeriv4ValC_uniform_in_c R hR hc ht_pos
      have h_t34_le : t^(ρ.val.re + 3) ≤ t^3 + t^4 := by
        rcases le_or_gt 1 t with ht1 | ht1
        · have h_rpow_le : t^(ρ.val.re + 3) ≤ t^(4:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
          have h_t4 : t^(4:ℝ) = t^4 := by norm_num
          rw [h_t4] at h_rpow_le
          have : 0 ≤ t^3 := by positivity
          linarith
        · have h_rpow_le : t^(ρ.val.re + 3) ≤ t^(3:ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge ht_pos ht1.le (by linarith)
          have h_t3 : t^(3:ℝ) = t^3 := by norm_num
          rw [h_t3] at h_rpow_le
          have : 0 ≤ t^4 := by positivity
          linarith
      have h_t34_nn : 0 ≤ t^3 + t^4 := by positivity
      have h_dom_nn : 0 ≤ Real.exp (R^2 / 4) * coshGaussDeriv4ValC_polyR R t *
          Real.exp (-t^2) := by
        have hP_nn : 0 ≤ coshGaussDeriv4ValC_polyR R t := by
          unfold coshGaussDeriv4ValC_polyR
          have ht2 : 0 ≤ t^2 := sq_nonneg _
          have ht3 : 0 ≤ t^3 := by positivity
          have ht4 : 0 ≤ t^4 := by positivity
          have hR2 : 0 ≤ R^2 := sq_nonneg _
          have hR3 : 0 ≤ R^3 := by positivity
          have hR4 : 0 ≤ R^4 := by positivity
          nlinarith
        positivity
      have h_norm_nn : 0 ≤ ‖coshGaussDeriv4ValC c t‖ := norm_nonneg _
      calc t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖
          ≤ (t^3 + t^4) * ‖coshGaussDeriv4ValC c t‖ :=
            mul_le_mul_of_nonneg_right h_t34_le h_norm_nn
        _ ≤ (t^3 + t^4) * (Real.exp (R^2 / 4) * coshGaussDeriv4ValC_polyR R t *
              Real.exp (-t^2)) :=
            mul_le_mul_of_nonneg_left h_norm_bd h_t34_nn
    -- Step 3: integrate to get bound by M_unif.
    have h_dom_int := coshGaussDeriv4ValC_dominator_t34_integrable R hR
    have h_lhs_int : MeasureTheory.IntegrableOn
        (fun t : ℝ => t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖) (Set.Ioi 0) volume := by
      refine MeasureTheory.Integrable.mono' h_dom_int ?_ ?_
      · refine (Real.continuous_rpow_const ?_).aestronglyMeasurable.mul
          (continuous_coshGaussDeriv4ValC c).norm.aestronglyMeasurable
        linarith
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        rw [Real.norm_of_nonneg (by have ht_pos : (0:ℝ) < t := ht; positivity)]
        exact h_pointwise t ht
    have h_step2 : ∫ t in Set.Ioi (0:ℝ), t^(ρ.val.re + 3) * ‖coshGaussDeriv4ValC c t‖ ≤
        M_unif := by
      rw [hM_def]; unfold coshGaussMellinC_uniformBound
      exact MeasureTheory.setIntegral_mono_on h_lhs_int h_dom_int measurableSet_Ioi h_pointwise
    linarith
  rw [h_ibp, norm_mul, norm_div, norm_one]
  calc 1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ *
      ‖mellin (coshGaussDeriv4ValC c) (ρ.val + 4)‖
      ≤ 1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖ * M_unif := by
        apply mul_le_mul_of_nonneg_left h_mellin_bd; positivity
    _ = M_unif * (1 / ‖ρ.val * (ρ.val + 1) * (ρ.val + 2) * (ρ.val + 3)‖) := by ring

#print axioms coshGaussMellinC_strip_bound_uniform_in_c

end Contour
end WeilPositivity
end ZD

end
