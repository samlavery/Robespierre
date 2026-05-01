import Mathlib
import RequestProject.GammaAveragedPositivity
import RequestProject.GaussianAdmissible

/-!
# γ-averaged unconditional offline positivity for `ψ_gaussian`

Instantiates `gamma_averaged_offline_positive` with `ψ := ψ_gaussian`. All
integrability hypotheses follow from Gaussian super-exponential decay
(`integrable_exp_neg_mul_sq`). The six integrability sub-lemmas below
each amount to routine dominated-by-Gaussian arguments.
-/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace ZD

private lemma gauss_cosh_meas (σ : ℝ) :
    Measurable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ_gaussian t) := by
  have h1 : Measurable (fun t : ℝ => 2 * Real.cosh ((σ - 1/2) * t)) :=
    Measurable.const_mul (Real.measurable_cosh.comp (measurable_const.mul measurable_id)) _
  exact h1.mul continuous_ψ_gaussian.measurable

private lemma gauss_sinh_meas (σ : ℝ) :
    Measurable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ_gaussian t) := by
  have h1 : Measurable (fun t : ℝ => 2 * Real.sinh ((σ - 1/2) * t)) :=
    Measurable.const_mul (Real.measurable_sinh.comp (measurable_const.mul measurable_id)) _
  exact h1.mul continuous_ψ_gaussian.measurable

/-! ### Deferred integrability lemmas (routine Gaussian dominated-convergence) -/

private lemma gauss_cosh_int_L1 (σ : ℝ) :
    Integrable (fun t => 2 * Real.cosh ((σ - 1/2) * t) * ψ_gaussian t)
      (volume.restrict (Ioi 0)) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun t => 2 * Real.exp ( ( |σ - 1 / 2| + 1 ) * t ) * Real.exp ( -t ^ 2 );
  · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp ((|σ - 1 / 2| + 1) * t - t ^ 2)) (Set.Ioi 0) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(t - (|σ - 1 / 2| + 1) / 2) ^ 2 + (|σ - 1 / 2| + 1) ^ 2 / 4)) (Set.Ioi 0) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(t - (|σ - 1 / 2| + 1) / 2) ^ 2)) (Set.univ : Set ℝ) := by
          simpa using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 ) ) |> fun h => h.comp_sub_right _;
        simpa [ Real.exp_add ] using h_integrable.mul_const _ |> MeasureTheory.Integrable.mono_measure <| MeasureTheory.Measure.restrict_mono ( Set.subset_univ _ ) le_rfl;
      convert h_integrable using 3 ; ring;
    convert h_integrable.const_mul 2 using 2 ; rw [ mul_assoc, ← Real.exp_add ] ; ring;
  · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( Continuous.mul continuous_const <| Real.continuous_cosh.comp <| by continuity ) <| Real.continuous_exp.comp <| by continuity );
  · norm_num [ Real.cosh_eq, ψ_gaussian ];
    rw [ Filter.eventually_inf_principal ] ; norm_num;
    filter_upwards [ ] with x hx using mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( by positivity ) ] ; nlinarith [ Real.exp_pos ( ( σ - 1 / 2 ) * x ), Real.exp_pos ( - ( ( σ - 1 / 2 ) * x ) ), Real.exp_le_exp.2 ( show ( σ - 1 / 2 ) * x ≤ ( |σ - 1 / 2| + 1 ) * x by cases abs_cases ( σ - 1 / 2 ) <;> nlinarith ), Real.exp_le_exp.2 ( show - ( ( σ - 1 / 2 ) * x ) ≤ ( |σ - 1 / 2| + 1 ) * x by cases abs_cases ( σ - 1 / 2 ) <;> nlinarith ) ] ) ( by positivity )

private lemma gauss_sinh_int_L1 (σ : ℝ) :
    Integrable (fun t => 2 * Real.sinh ((σ - 1/2) * t) * ψ_gaussian t)
      (volume.restrict (Ioi 0)) := by
  unfold ψ_gaussian;
  -- The function $2 * (Real.sinh ((σ - 1 / 2) * t) * Real.exp (-t ^ 2))$ is integrable because it is the product of two integrable functions.
  have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(t - (σ - 1 / 2) / 2) ^ 2)) (Set.Ioi 0) ∧ MeasureTheory.IntegrableOn (fun t => Real.exp (-(t + (σ - 1 / 2) / 2) ^ 2)) (Set.Ioi 0) := by
    constructor;
    · exact MeasureTheory.Integrable.integrableOn ( by simpa using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 ) ) |> fun h => h.comp_sub_right _ );
    · exact MeasureTheory.Integrable.integrableOn ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 ) ) |> fun h => h.comp_add_right _ ) ) ) ) ) );
  have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(t - (σ - 1 / 2) / 2) ^ 2) - Real.exp (-(t + (σ - 1 / 2) / 2) ^ 2)) (Set.Ioi 0) := by
    exact MeasureTheory.Integrable.sub h_integrable.1 h_integrable.2;
  convert h_integrable.mul_const ( Real.exp ( ( σ - 1 / 2 ) ^ 2 / 4 ) ) using 1 ; ext t ; rw [ Real.sinh_eq ] ; ring;
  simpa only [ ← Real.exp_add ] using by ring

private lemma gauss_cosh_int_L2 (σ : ℝ) :
    Integrable (fun t => (2 * Real.cosh ((σ - 1/2) * t) * ψ_gaussian t)^2)
      (volume.restrict (Ioi 0)) := by
  have h : Integrable (fun t => (2 * Real.cosh ((σ - 1 / 2) * t) * ψ_gaussian t) ^ 2) volume := by
    apply Integrable.mono' (integrable_const_mul_gaussian (4 * Real.exp ((σ - 1/2) ^ 2)))
    · exact (((continuous_const.mul (Real.continuous_cosh.comp
        ((continuous_const.sub continuous_const).mul continuous_id))).mul
        continuous_ψ_gaussian).pow 2).aestronglyMeasurable
    · filter_upwards with t
      rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow, mul_pow, ψ_gaussian_sq_eq]
      have hc := cosh_sq_gaussian_dominated (σ - 1/2) t
      nlinarith [sq_nonneg (Real.cosh ((σ - 1/2) * t)), Real.exp_pos (-t^2)]
  exact h.restrict

private lemma gauss_sinh_int_L2 (σ : ℝ) :
    Integrable (fun t => (2 * Real.sinh ((σ - 1/2) * t) * ψ_gaussian t)^2)
      (volume.restrict (Ioi 0)) := by
  unfold ψ_gaussian;
  -- The function $2 * (Real.cosh (2 * (σ - 1 / 2) * t) - 1) * Real.exp (-2 * t ^ 2)$ is integrable because it is the sum of two integrable functions.
  have h_integrable : Integrable (fun t => Real.cosh (2 * (σ - 1 / 2) * t) * Real.exp (-2 * t ^ 2)) (volume.restrict (Ioi 0)) ∧ Integrable (fun t => Real.exp (-2 * t ^ 2)) (volume.restrict (Ioi 0)) := by
    constructor;
    · -- The function $Real.cosh (2 * (σ - 1 / 2) * t) * Real.exp (-2 * t ^ 2)$ is integrable because it is the product of two integrable functions.
      have h_integrable : ∀ a b : ℝ, Integrable (fun t => Real.exp (a * t) * Real.exp (-2 * t ^ 2)) (volume.restrict (Ioi 0)) := by
        intro a b;
        -- The integral of $e^{a t} e^{-2 t^2}$ is convergent because it is the product of two Gaussian functions.
        have h_gauss_prod : ∀ a : ℝ, Integrable (fun t => Real.exp (-2 * t ^ 2 + a * t)) (volume.restrict (Ioi 0)) := by
          intro a;
          have h_gauss_prod : ∀ a : ℝ, Integrable (fun t => Real.exp (-2 * (t - a / 4) ^ 2)) (volume.restrict (Ioi 0)) := by
            exact fun a => by simpa using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 2 ) ) |> ( fun h => h.comp_sub_right _ |> ( fun h => h.integrableOn ) );
          convert h_gauss_prod a |> fun h => h.mul_const ( Real.exp ( a ^ 2 / 8 ) ) using 2 ; rw [ ← Real.exp_add ] ; ring;
        simpa only [ ← Real.exp_add, add_comm ] using h_gauss_prod a;
      convert h_integrable ( 2 * ( σ - 1 / 2 ) ) 0 |> ( ·.add ( h_integrable ( - ( 2 * ( σ - 1 / 2 ) ) ) 0 ) ) |> ( ·.div_const 2 ) using 2 ; norm_num [ Real.cosh_eq ] ; ring;
    · simpa using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 2 ) ).integrableOn;
  convert h_integrable.1.const_mul 2 |> fun h => h.sub ( h_integrable.2.const_mul 2 ) using 2 ; ring;
  norm_num [ Real.sinh_sq, Real.cosh_eq ] ; ring;
  norm_num [ sq, ← Real.exp_add ] ; ring

private lemma gauss_cosh2_int (σ : ℝ) :
    Integrable (fun t => Real.cosh (2 * (σ - 1/2) * t) * ψ_gaussian t ^ 2)
      (volume.restrict (Ioi 0)) := by
  -- The integrand can be rewritten as $\frac{1}{2} \left( e^{(σ - 1/2)2t} + e^{-(σ - 1/2)2t} \right) e^{-2t^2}$.
  suffices h_suff : MeasureTheory.Integrable (fun t => (Real.exp ((σ - 1 / 2) * 2 * t) + Real.exp (-(σ - 1 / 2) * 2 * t)) / 2 * Real.exp (-2 * t^2)) (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioi 0)) by
    convert h_suff using 2 ; rw [ Real.cosh_eq ] ; rw [ ψ_gaussian_sq_eq ] ; ring;
  -- Each exponential term is integrable because completing the square gives $c*t - 2*t^2 = -2*(t - c/4)^2 + c^2/8$, which is a shifted Gaussian with coefficient 2 > 0.
  have h_exp_integrable : ∀ c : ℝ, MeasureTheory.Integrable (fun t => Real.exp (c * t - 2 * t^2)) (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioi 0)) := by
    intro c
    have h_exp_integrable : MeasureTheory.Integrable (fun t => Real.exp (-2 * (t - c / 4) ^ 2)) (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioi 0)) := by
      exact MeasureTheory.Integrable.integrableOn ( by simpa using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 2 ) ) |> ( fun h => h.comp_sub_right ( c / 4 ) ) );
    convert h_exp_integrable.mul_const ( Real.exp ( c ^ 2 / 8 ) ) using 2 ; rw [ ← Real.exp_add ] ; ring;
  convert MeasureTheory.Integrable.add ( h_exp_integrable ( ( σ - 1 / 2 ) * 2 ) ) ( h_exp_integrable ( - ( σ - 1 / 2 ) * 2 ) ) |> fun h => h.div_const 2 using 2 ; ring;
  simpa using by rw [ ← Real.exp_add, ← Real.exp_add ] ; ring

/-- **Envelope integrability** — the one that *does* close unconditionally,
since `(E²+O²) · ψ² = (E·ψ)² + (O·ψ)²` and GaussianAdmissible already has
both summands integrable. -/
private lemma gauss_env_int (σ : ℝ) :
    Integrable
      (fun t => ((amplitudeDefectEnvelope σ t)^2 + (oddDefectEnvelope σ t)^2) *
        ψ_gaussian t ^ 2) (volume.restrict (Ioi 0)) := by
  have h_E : Integrable (fun t => (amplitudeDefectEnvelope σ t * ψ_gaussian t)^2) volume :=
    integrable_amp_env_sq σ
  have h_O : Integrable (fun t => (oddDefectEnvelope σ t * ψ_gaussian t)^2) volume :=
    integrable_odd_env_sq σ
  have h_eq : (fun t : ℝ => ((amplitudeDefectEnvelope σ t)^2 +
      (oddDefectEnvelope σ t)^2) * ψ_gaussian t ^ 2) =
    (fun t => (amplitudeDefectEnvelope σ t * ψ_gaussian t)^2 +
      (oddDefectEnvelope σ t * ψ_gaussian t)^2) := by
    funext t; ring
  rw [h_eq]
  exact (h_E.add h_O).restrict

/-- **ψ² integrable on Ioi 0** — Gaussian is manifestly L². -/
private lemma gauss_psi2_int :
    Integrable (fun t => ψ_gaussian t ^ 2) (volume.restrict (Ioi 0)) := by
  have h : Integrable (fun t => ψ_gaussian t ^ 2) volume := by
    simp_rw [ψ_gaussian_sq_eq]
    exact integrable_exp_neg_mul_sq (b := 2) (by norm_num)
  exact h.restrict

/-
The outer integrand (sum of squared transforms) is integrable on `Ioi 0`
for the Gaussian test function. Follows from the super-exponential decay of
the Gaussian which makes the cosine/sine transforms decay as Gaussians in γ.
-/
set_option maxHeartbeats 800000 in
private lemma gauss_outer_int (σ : ℝ) :
    Integrable (fun γ =>
        (∫ t in Set.Ioi (0:ℝ),
            2 * Real.cosh ((σ - 1/2) * t) * ψ_gaussian t * Real.cos (γ * t))^2 +
        (∫ t in Set.Ioi (0:ℝ),
            2 * Real.sinh ((σ - 1/2) * t) * ψ_gaussian t * Real.sin (γ * t))^2)
      (volume.restrict (Ioi 0)) := by
  have h_fourier_transform : ∀ γ : ℝ, (∫ t in Ioi (0 : ℝ), 2 * Real.cosh ((σ - 1 / 2) * t) * ψ_gaussian t * Real.cos (γ * t)) = (1 / 2) * (∫ t in Set.univ, (Real.exp ((σ - 1 / 2) * t) + Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.cos (γ * t)) := by
    intro γ
    have h_fourier_transform : ∫ t in Ioi (0 : ℝ), 2 * Real.cosh ((σ - 1 / 2) * t) * ψ_gaussian t * Real.cos (γ * t) = (1 / 2) * (∫ t in Set.univ, (Real.exp ((σ - 1 / 2) * t) + Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.cos (γ * t)) := by
      have h_even : ∀ f : ℝ → ℝ, (∀ x, f (-x) = f x) → ∫ x in Ioi 0, f x = (1 / 2) * ∫ x in Set.univ, f x := by
        intro f hf_even
        have h_even_integral : ∫ x in Set.univ, f x = (∫ x in Set.Ioi 0, f x) + (∫ x in Set.Iio 0, f x) := by
          by_cases h_integrable : MeasureTheory.IntegrableOn f (Set.Ioi 0) MeasureTheory.volume ∧ MeasureTheory.IntegrableOn f (Set.Iio 0) MeasureTheory.volume;
          · rw [ add_comm, ← MeasureTheory.setIntegral_union ] <;> norm_num [ h_integrable ];
          · by_cases h_integrable_pos : MeasureTheory.IntegrableOn f (Set.Ioi 0) MeasureTheory.volume <;> by_cases h_integrable_neg : MeasureTheory.IntegrableOn f (Set.Iio 0) MeasureTheory.volume <;> simp_all +decide [ MeasureTheory.integral_undef ];
            · contrapose! h_integrable_neg;
              rw [ ← MeasureTheory.integrable_indicator_iff ] at * <;> norm_num at *;
              convert h_integrable_pos.comp_neg using 1 ; ext x ; simp +decide [ hf_even, Set.indicator ];
            · contrapose! h_integrable_pos;
              rw [ ← MeasureTheory.integrable_indicator_iff ] at * <;> norm_num at *;
              convert h_integrable_neg.comp_neg using 1 ; ext ; simp +decide [ hf_even, Set.indicator ];
            · rw [ MeasureTheory.integral_undef ];
              · rw [ MeasureTheory.integral_undef h_integrable_pos, MeasureTheory.integral_undef h_integrable_neg, add_zero ];
              · exact fun h => h_integrable_pos <| h.integrableOn;
        rw [ h_even_integral, ← MeasureTheory.integral_Iic_eq_integral_Iio ] ; rw [ ← neg_zero, ← integral_comp_neg_Iic ] ; norm_num [ hf_even ] ; ring;
      convert h_even _ _ using 3 ; norm_num [ Real.cosh_eq ] ; ring;
      · grind +splitIndPred;
      · norm_num [ ψ_gaussian ];
    exact h_fourier_transform;
  have h_fourier_transform_sin : ∀ γ : ℝ, (∫ t in Ioi (0 : ℝ), 2 * Real.sinh ((σ - 1 / 2) * t) * ψ_gaussian t * Real.sin (γ * t)) = (1 / 2) * (∫ t in Set.univ, (Real.exp ((σ - 1 / 2) * t) - Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.sin (γ * t)) := by
    intro γ
    have h_split : ∫ t in Set.univ, (Real.exp ((σ - 1 / 2) * t) - Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.sin (γ * t) = (∫ t in Ioi (0 : ℝ), (Real.exp ((σ - 1 / 2) * t) - Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.sin (γ * t)) + (∫ t in Iio (0 : ℝ), (Real.exp ((σ - 1 / 2) * t) - Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.sin (γ * t)) := by
      rw [ add_comm, ← MeasureTheory.setIntegral_union ] <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun t => ( Real.exp ( ( σ - 1 / 2 ) * t ) + Real.exp ( ( 1 / 2 - σ ) * t ) ) * Real.exp ( -t ^ 2 );
        · -- The integral of the Gaussian function is finite.
          have h_gauss_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-t ^ 2 + (σ - 1 / 2) * t)) (Set.Iio 0) ∧ MeasureTheory.IntegrableOn (fun t => Real.exp (-t ^ 2 + (1 / 2 - σ) * t)) (Set.Iio 0) := by
            have h_gauss_integrable : ∀ a : ℝ, MeasureTheory.IntegrableOn (fun t => Real.exp (-t ^ 2 + a * t)) Set.univ := by
              intro a;
              have h_gauss_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(t - a / 2) ^ 2)) Set.univ := by
                simpa using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 ) ) |> fun h => h.comp_sub_right ( a / 2 );
              simp +zetaDelta at *;
              convert h_gauss_integrable.mul_const ( Real.exp ( a ^ 2 / 4 ) ) using 2 ; rw [ ← Real.exp_add ] ; ring;
            exact ⟨ MeasureTheory.IntegrableOn.mono_set ( h_gauss_integrable _ ) ( Set.subset_univ _ ), MeasureTheory.IntegrableOn.mono_set ( h_gauss_integrable _ ) ( Set.subset_univ _ ) ⟩;
          have h_add := h_gauss_integrable.1.add h_gauss_integrable.2
          have h_fn_eq : (fun t => (Real.exp ((σ - 1 / 2) * t) + Real.exp ((1 / 2 - σ) * t)) *
              Real.exp (-t ^ 2)) =
              ((fun t => Real.exp (-t ^ 2 + (σ - 1 / 2) * t)) +
                fun t => Real.exp (-t ^ 2 + (1 / 2 - σ) * t)) := by
            funext t
            simp only [Pi.add_apply, add_mul, ← Real.exp_add]
            ring_nf
          rw [h_fn_eq]
          exact h_add
        · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( Continuous.mul ( by continuity ) ( by exact Real.continuous_exp.comp ( by continuity ) ) ) ( Real.continuous_sin.comp ( by continuity ) ) );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Iio ] with t ht;
          norm_num [ ψ_gaussian ];
          exact le_trans ( mul_le_of_le_one_right ( by positivity ) ( Real.abs_sin_le_one _ ) ) ( mul_le_mul_of_nonneg_right ( abs_le.mpr ⟨ by linarith [ Real.exp_pos ( ( σ - 1 / 2 ) * t ), Real.exp_pos ( ( 1 / 2 - σ ) * t ) ], by linarith [ Real.exp_pos ( ( σ - 1 / 2 ) * t ), Real.exp_pos ( ( 1 / 2 - σ ) * t ) ] ⟩ ) ( by positivity ) );
      · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp ((σ - 1 / 2) * t) * Real.exp (-t ^ 2)) (Set.Ioi 0) ∧ MeasureTheory.IntegrableOn (fun t => Real.exp ((1 / 2 - σ) * t) * Real.exp (-t ^ 2)) (Set.Ioi 0) := by
          have h_integrable : ∀ a : ℝ, MeasureTheory.IntegrableOn (fun t => Real.exp (a * t) * Real.exp (-t ^ 2)) (Set.Ioi 0) := by
            intro a
            have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-t ^ 2 + a * t)) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-t ^ 2 + a * t)) Set.univ := by
                have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(t - a / 2) ^ 2)) Set.univ := by
                  simpa using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 ) ) |> fun h => h.comp_sub_right ( a / 2 );
                simp +zetaDelta at *;
                convert h_integrable.mul_const ( Real.exp ( a ^ 2 / 4 ) ) using 2 ; rw [ ← Real.exp_add ] ; ring;
              exact h_integrable.mono_set <| Set.subset_univ _;
            simpa only [ ← Real.exp_add, add_comm ] using h_integrable;
          exact ⟨ h_integrable _, h_integrable _ ⟩;
        refine' MeasureTheory.Integrable.mono' ( h_integrable.1.add h_integrable.2 ) _ _;
        · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( Continuous.mul ( Continuous.sub ( Real.continuous_exp.comp ( continuous_const.mul continuous_id' ) ) ( Real.continuous_exp.comp ( continuous_const.mul continuous_id' ) ) ) ( Real.continuous_exp.comp ( continuous_neg.comp ( continuous_pow 2 ) ) ) ) ( Real.continuous_sin.comp ( continuous_const.mul continuous_id' ) ) );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;
          norm_num [ ψ_gaussian ];
          exact le_trans ( mul_le_of_le_one_right ( by positivity ) ( Real.abs_sin_le_one _ ) ) ( by cases abs_cases ( Real.exp ( ( σ - 1 / 2 ) * t ) - Real.exp ( ( 1 / 2 - σ ) * t ) ) <;> nlinarith [ Real.exp_pos ( ( σ - 1 / 2 ) * t ), Real.exp_pos ( ( 1 / 2 - σ ) * t ), Real.exp_pos ( -t ^ 2 ) ] );
    have h_split_neg : ∫ t in Iio (0 : ℝ), (Real.exp ((σ - 1 / 2) * t) - Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.sin (γ * t) = ∫ t in Ioi (0 : ℝ), (Real.exp (-(σ - 1 / 2) * t) - Real.exp ((σ - 1 / 2) * t)) * ψ_gaussian t * Real.sin (-γ * t) := by
      rw [ ← MeasureTheory.integral_Iic_eq_integral_Iio ] ; rw [ ← neg_zero, ← integral_comp_neg_Iic ] ; norm_num;
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic fun x hx => by unfold ψ_gaussian; ring;
    simp_all +decide [ Real.sinh_eq ];
    grind;
  have h_fourier_transform_exp : ∀ γ : ℝ, (∫ t in Set.univ, Real.exp ((σ - 1 / 2) * t) * ψ_gaussian t * Complex.exp (Complex.I * γ * t)) = Real.sqrt Real.pi * Complex.exp (-(γ - Complex.I * (σ - 1 / 2))^2 / 4) := by
    intro γ
    have := @fourierIntegral_gaussian
    simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin ];
    convert @this 1 ( by norm_num ) ( γ - Complex.I * ( σ - 2⁻¹ ) ) using 1 <;> norm_num [ Complex.exp_re, Complex.exp_im, ψ_gaussian ] ; ring;
    · norm_num [ ← Complex.exp_add ] ; congr ; ext ; ring;
    · rw [ Real.sqrt_eq_rpow, Complex.ofReal_cpow ] <;> norm_num [ Real.pi_pos.le ];
  have h_fourier_transform_exp_neg : ∀ γ : ℝ, (∫ t in Set.univ, Real.exp (-(σ - 1 / 2) * t) * ψ_gaussian t * Complex.exp (Complex.I * γ * t)) = Real.sqrt Real.pi * Complex.exp (-(γ + Complex.I * (σ - 1 / 2))^2 / 4) := by
    intro γ
    have := h_fourier_transform_exp (-γ)
    simp_all +decide [ mul_comm ];
    rw [ ← MeasureTheory.integral_neg_eq_self ] ; convert this using 3 <;> ring;
    norm_num [ ψ_gaussian ] ; ring;
  have h_fourier_transform_cos : ∀ γ : ℝ, (∫ t in Set.univ, (Real.exp ((σ - 1 / 2) * t) + Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.cos (γ * t)) = Complex.re ((Real.sqrt Real.pi * Complex.exp (-(γ - Complex.I * (σ - 1 / 2))^2 / 4)) + (Real.sqrt Real.pi * Complex.exp (-(γ + Complex.I * (σ - 1 / 2))^2 / 4))) := by
    intro γ;
    rw [ ← h_fourier_transform_exp γ, ← h_fourier_transform_exp_neg γ, ← MeasureTheory.integral_add ];
    · convert integral_re _;
      rotate_left;
      rotate_left;
      exact ℂ;
      all_goals norm_cast;
      · refine' MeasureTheory.Integrable.add _ _;
        · contrapose! h_fourier_transform_exp;
          exact ⟨ γ, by rw [ MeasureTheory.integral_undef ( by simpa [ mul_assoc ] using h_fourier_transform_exp ) ] ; norm_num [ Complex.exp_ne_zero, Real.sqrt_ne_zero'.mpr Real.pi_pos ] ⟩;
        · contrapose! h_fourier_transform_exp_neg;
          use γ;
          rw [ MeasureTheory.integral_undef ] <;> norm_num [ h_fourier_transform_exp_neg ];
          · positivity;
          · convert h_fourier_transform_exp_neg using 1;
            norm_num [ Complex.exp_re, Complex.exp_im, ψ_gaussian ];
      · norm_num [ Complex.exp_re, Complex.exp_im, Real.cos ] ; ring;
    · contrapose! h_fourier_transform_exp;
      exact ⟨ γ, by rw [ MeasureTheory.integral_undef h_fourier_transform_exp ] ; norm_num [ Complex.exp_ne_zero, Real.sqrt_ne_zero'.mpr Real.pi_pos ] ⟩;
    · contrapose! h_fourier_transform_exp_neg;
      exact ⟨ γ, by rw [ MeasureTheory.integral_undef h_fourier_transform_exp_neg ] ; norm_num [ Complex.exp_ne_zero, Real.sqrt_ne_zero'.mpr Real.pi_pos ] ⟩;
  have h_fourier_transform_sin : ∀ γ : ℝ, (∫ t in Set.univ, (Real.exp ((σ - 1 / 2) * t) - Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.sin (γ * t)) = Complex.im ((Real.sqrt Real.pi * Complex.exp (-(γ - Complex.I * (σ - 1 / 2))^2 / 4)) - (Real.sqrt Real.pi * Complex.exp (-(γ + Complex.I * (σ - 1 / 2))^2 / 4))) := by
    intro γ
    have h_fourier_transform_sin : (∫ t in Set.univ, (Real.exp ((σ - 1 / 2) * t) - Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Real.sin (γ * t)) = Complex.im (∫ t in Set.univ, (Real.exp ((σ - 1 / 2) * t) - Real.exp (-(σ - 1 / 2) * t)) * ψ_gaussian t * Complex.exp (Complex.I * γ * t)) := by
      have h_fourier_transform_sin : ∀ {f : ℝ → ℂ}, MeasureTheory.Integrable f MeasureTheory.volume → (∫ t in Set.univ, f t).im = ∫ t in Set.univ, (f t).im := by
        intro f hf
        rw [MeasureTheory.setIntegral_univ, MeasureTheory.setIntegral_univ]
        exact (integral_im hf).symm
      rw [ h_fourier_transform_sin ];
      · norm_num [ Complex.exp_im, Complex.exp_re ];
      · have h_integrable : MeasureTheory.Integrable (fun t : ℝ => Real.exp ((σ - 1 / 2) * t) * ψ_gaussian t * Complex.exp (Complex.I * γ * t)) MeasureTheory.volume ∧ MeasureTheory.Integrable (fun t : ℝ => Real.exp (-(σ - 1 / 2) * t) * ψ_gaussian t * Complex.exp (Complex.I * γ * t)) MeasureTheory.volume := by
          constructor <;> contrapose! h_fourier_transform_exp <;> simp_all +decide [ MeasureTheory.integral_undef ];
          · exact ⟨ γ, by rw [ MeasureTheory.integral_undef h_fourier_transform_exp ] ; norm_num [ Complex.exp_ne_zero, Real.sqrt_ne_zero'.mpr Real.pi_pos ] ⟩;
          · specialize h_fourier_transform_exp_neg γ; rw [ MeasureTheory.integral_undef h_fourier_transform_exp ] at h_fourier_transform_exp_neg; norm_num [ Complex.exp_ne_zero, Real.sqrt_ne_zero'.mpr Real.pi_pos ] at h_fourier_transform_exp_neg;
        simpa only [ sub_mul, sub_mul ] using h_integrable.1.sub h_integrable.2;
    rw [ h_fourier_transform_sin, ← h_fourier_transform_exp, ← h_fourier_transform_exp_neg ];
    rw [ ← MeasureTheory.integral_sub ] ; congr ; ext ; ring;
    · contrapose! h_fourier_transform_exp;
      exact ⟨ γ, by rw [ MeasureTheory.integral_undef h_fourier_transform_exp ] ; norm_num [ Complex.exp_ne_zero, Real.sqrt_ne_zero'.mpr Real.pi_pos ] ⟩;
    · contrapose! h_fourier_transform_exp_neg;
      exact ⟨ γ, by rw [ MeasureTheory.integral_undef h_fourier_transform_exp_neg ] ; norm_num [ Complex.exp_ne_zero, Real.sqrt_ne_zero'.mpr Real.pi_pos ] ⟩;
  simp_all +decide [ Complex.exp_re, Complex.exp_im, sq ];
  ring_nf;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  use fun x => Real.sqrt Real.pi ^ 2 * Real.exp ( 1 / 16 + σ * ( -1 / 4 ) + σ ^ 2 * ( 1 / 4 ) + x ^ 2 * ( -1 / 4 ) ) ^ 2 * 2;
  · norm_num [ ← Real.exp_nat_mul ];
    refine' MeasureTheory.Integrable.mul_const _ _;
    refine' MeasureTheory.Integrable.const_mul _ _;
    have := ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) );
    convert this.mono_measure ( MeasureTheory.Measure.restrict_le_self ) |> fun h => h.mul_const ( Real.exp ( 2 * ( 1 / 16 + - ( σ * ( 1 / 4 ) ) + σ ^ 2 * ( 1 / 4 ) ) ) ) using 2 ; ring;
    rw [ ← Real.exp_add ] ; ring;
  · fun_prop;
  · norm_num [ Real.sin_add, Real.cos_add ] ; ring_nf ; norm_num;
    norm_num [ Real.sin_sq, Real.cos_sq ] ; ring_nf ; norm_num;
    exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => le_mul_of_one_le_right ( by positivity ) ( by norm_num ) )

/-! ### Main result -/

/-- **γ-averaged unconditional offline positivity for the Gaussian test function.** -/
theorem gamma_averaged_offline_positive_gaussian (σ : ℝ) (hσ : σ ≠ 1/2) :
    0 < ∫ γ in Set.Ioi (0:ℝ),
        ((∫ t in Set.Ioi (0:ℝ),
            2 * Real.cosh ((σ - 1/2) * t) * ψ_gaussian t * Real.cos (γ * t))^2 +
          (∫ t in Set.Ioi (0:ℝ),
            2 * Real.sinh ((σ - 1/2) * t) * ψ_gaussian t * Real.sin (γ * t))^2) :=
  gamma_averaged_offline_positive ψ_gaussian σ hσ
    (gauss_cosh_meas σ) (gauss_cosh_int_L1 σ) (gauss_cosh_int_L2 σ)
    (gauss_sinh_meas σ) (gauss_sinh_int_L1 σ) (gauss_sinh_int_L2 σ)
    (gauss_cosh2_int σ) (gauss_env_int σ) gauss_psi2_int
    ψ_gaussian_nontrivial

#print axioms gamma_averaged_offline_positive_gaussian

end ZD

end