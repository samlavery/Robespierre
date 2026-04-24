import Mathlib

/-! # Helper lemmas for the bound on completedRiemannZeta₀

We prove that `‖completedRiemannZeta₀ s‖ < 1 / (2 * √5)` for `s` with
`0 ≤ Re(s) ≤ 1` and `|Im(s)| ≤ 2`.

The proof strategy:
1. Express `completedRiemannZeta₀` as a Mellin transform of `f_modif`.
2. Bound the norm using the triangle inequality for integrals.
3. Show `f_modif` takes non-negative real values (from theta function properties).
4. Bound the resulting integral numerically.
-/

open Complex MeasureTheory Set in
/-- The Mellin transform of a function has norm bounded by the integral of norms. -/
lemma norm_mellin_le {f : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) :
    ‖mellin f s‖ ≤ ∫ t in Ioi (0 : ℝ), ‖(↑t : ℂ) ^ (s - 1) • f t‖ := by
  convert MeasureTheory.norm_integral_le_integral_norm _

open Complex in
/-- For t > 0, the norm of t^(s-1) • v equals t^(Re(s)-1) * ‖v‖. -/
lemma norm_cpow_smul {t : ℝ} (ht : 0 < t) (s : ℂ) (v : ℂ) :
    ‖(↑t : ℂ) ^ (s - 1) • v‖ = t ^ (s.re - 1) * ‖v‖ := by
  simp +decide [ Complex.normSq_eq_norm_sq, Complex.norm_cpow_of_ne_zero, ht.ne', mul_comm ];
  norm_num [ abs_of_pos ht, Complex.arg_ofReal_of_nonneg ht.le ]

/-- exp(π) > 20, which gives exp(-π) < 1/20. -/
lemma Real.exp_pi_gt_twenty : 20 < Real.exp Real.pi := by
  have h_exp_pi_gt_e3 : Real.exp Real.pi > Real.exp 3 := by
    exact Real.exp_lt_exp.mpr ( Real.pi_gt_three )
  have h_e3_gt_20 : Real.exp 3 > 20 := by
    have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show ( 3 : ℝ ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ]
  linarith [h_exp_pi_gt_e3, h_e3_gt_20]

/-- 4√5 < 9, equivalently 80 < 81. -/
lemma four_sqrt_five_lt_nine : 4 * Real.sqrt 5 < 9 := by
  nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]

/-- Numerical bound: 2/(π * 19) < 1/(2√5), after accounting for factors. -/
lemma two_div_pi_nineteen_lt : 2 / (Real.pi * 19) < 1 / (2 * Real.sqrt 5) := by
  rw [ div_lt_div_iff₀ ] <;> nlinarith [ Real.pi_gt_three, Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]

open Complex in
/-- For t ≥ 1 and σ ∈ [0, 1], we have t ^ (σ/2 - 1) ≤ 1. -/
lemma rpow_weight_le_one {t σ : ℝ} (ht : 1 ≤ t) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    t ^ (σ / 2 - 1) ≤ 1 := by
  exact le_trans ( Real.rpow_le_rpow_of_exponent_le ht ( show σ / 2 - 1 ≤ 0 by linarith ) ) ( by norm_num )

/-- For t > 0, evenKernel 0 t ≥ 1. -/
lemma HurwitzZeta.evenKernel_zero_ge_one {t : ℝ} (ht : 0 < t) :
    1 ≤ HurwitzZeta.evenKernel 0 t := by
  have h_evenKernel_zero : HurwitzZeta.evenKernel 0 t = ∑' n : ℤ, Real.exp (-Real.pi * n^2 * t) := by
    convert HurwitzZeta.evenKernel_def ( 0 : ℝ ) t using 1;
    norm_num [ jacobiTheta₂ ];
    norm_num [ jacobiTheta₂_term, Complex.ext_iff ];
    norm_num [ Complex.exp_re, Complex.exp_im, mul_assoc, mul_left_comm ];
    norm_num [ ← mul_assoc, Complex.exp_re, Complex.exp_im ];
    norm_cast ; norm_num;
  refine' h_evenKernel_zero ▸ le_trans _ ( Summable.le_tsum _ 0 fun n _ => by positivity ) ; norm_num;
  have h_summable : Summable (fun n : ℕ => Real.exp (-Real.pi * n^2 * t)) := by
    have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( show -Real.pi * t < 0 by nlinarith [ Real.pi_pos ] ) );
    exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
  have h_split : Summable (fun n : ℤ => Real.exp (-Real.pi * n^2 * t)) ↔ Summable (fun n : ℕ => Real.exp (-Real.pi * (n : ℤ)^2 * t)) ∧ Summable (fun n : ℕ => Real.exp (-Real.pi * (-n : ℤ)^2 * t)) := by
    exact summable_int_iff_summable_nat_and_neg;
  aesop

/-- Mellin convergence for the zeta pair's f_modif. -/
lemma zeta_f_modif_mellinConvergent (s : ℂ) :
    MellinConvergent (HurwitzZeta.hurwitzEvenFEPair 0).f_modif s := by
  exact ( HurwitzZeta.hurwitzEvenFEPair 0 ).toStrongFEPair.hasMellin s |>.1

/-- cosKernel 0 equals evenKernel 0 -/
lemma HurwitzZeta.cosKernel_zero_eq_evenKernel_zero (x : ℝ) :
    HurwitzZeta.cosKernel 0 x = HurwitzZeta.evenKernel 0 x := by
  unfold HurwitzZeta.evenKernel HurwitzZeta.cosKernel;
  unfold Function.Periodic.lift; norm_num;
  erw [ Quotient.liftOn'_mk, Quotient.liftOn'_mk ] ; norm_num

/-- For 0 < x, evenKernel 0 x ≥ x^(-1/2). -/
lemma HurwitzZeta.evenKernel_zero_ge_rpow {x : ℝ} (hx : 0 < x) :
    x ^ (-(1:ℝ)/2) ≤ HurwitzZeta.evenKernel 0 x := by
  have hfun : HurwitzZeta.evenKernel 0 x = 1 / x ^ (1 / 2 : ℝ) * HurwitzZeta.cosKernel 0 (1 / x) := by
    convert HurwitzZeta.evenKernel_functional_equation 0 x using 1;
  norm_num [ hfun ];
  rw [ Real.rpow_neg hx.le ];
  exact le_mul_of_one_le_right ( by positivity ) ( by simpa [ HurwitzZeta.cosKernel_zero_eq_evenKernel_zero ] using HurwitzZeta.evenKernel_zero_ge_one ( by positivity ) )

/-
Step 1: Reduce the norm of completedRiemannZeta₀ to an integral bound.
-/
lemma norm_completedRiemannZeta₀_le_mellin_norm (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ ≤
    (∫ t in Set.Ioi (0:ℝ), t ^ (s.re / 2 - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖) / 2 := by
  rw [ le_div_iff₀' ];
  · convert norm_mellin_le ( zeta_f_modif_mellinConvergent ( s / 2 ) ) using 1;
    · unfold completedRiemannZeta₀;
      unfold HurwitzZeta.completedHurwitzZetaEven₀; norm_num [ mul_comm ] ;
      unfold WeakFEPair.Λ₀; ring;
    · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
      rw [ norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht ] ; norm_num;
  · norm_num

/-
The evenKernel 0 t = tsum of exp(-π n² t)
-/
lemma HurwitzZeta.evenKernel_zero_eq_tsum (t : ℝ) :
    HurwitzZeta.evenKernel 0 t = ∑' n : ℤ, Real.exp (-Real.pi * ↑n ^ 2 * t) := by
  -- Apply the definition of `evenKernel` with `a = 0`.
  have h_evenKernel_def : evenKernel 0 t = Complex.re (jacobiTheta₂ (0 : ℂ) (Complex.I * t)) := by
    convert congr_arg Complex.re ( HurwitzZeta.evenKernel_def ( 0 : ℝ ) t ) using 1 ; norm_num [ jacobiTheta₂ ];
  convert h_evenKernel_def using 1;
  unfold jacobiTheta₂ jacobiTheta₂_term; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring;
  norm_num [ Complex.exp_re, Complex.exp_im ];
  norm_cast

/-
For t ≥ 1, evenKernel 0 t - 1 ≤ (40/19) * exp(-πt).
-/
lemma HurwitzZeta.evenKernel_zero_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    HurwitzZeta.evenKernel 0 t - 1 ≤ 40 / 19 * Real.exp (-Real.pi * t) := by
  -- Use the series expansion of evenKernel 0 t.
  have h_evenKernel_series : evenKernel 0 t = 1 + 2 * ∑' n : ℕ, Real.exp (-Real.pi * (n + 1) ^ 2 * t) := by
    rw [ HurwitzZeta.evenKernel_zero_eq_tsum ];
    rw [ ← Equiv.tsum_eq ( Equiv.intEquivNat.symm ) ];
    rw [ ← tsum_even_add_odd ] <;> norm_num [ Equiv.intEquivNat ];
    · norm_num [ Equiv.intEquivNatSumNat ];
      rw [ Summable.tsum_eq_zero_add ] <;> norm_num ; ring;
      · grind +revert;
      · have := summable_geometric_of_lt_one ( by positivity ) ( show Real.exp ( -Real.pi * t ) < 1 by rw [ Real.exp_lt_one_iff ] ; nlinarith [ Real.pi_pos ] );
        exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
    · norm_num [ Equiv.intEquivNatSumNat ];
      have := summable_geometric_of_lt_one ( by positivity ) ( show Real.exp ( -Real.pi * t ) < 1 by rw [ Real.exp_lt_one_iff ] ; nlinarith [ Real.pi_pos ] );
      exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
    · norm_num [ Equiv.intEquivNatSumNat ];
      -- We'll use the fact that the series $\sum_{n=1}^{\infty} e^{-\pi n^2 t}$ converges.
      have h_summable : Summable (fun n : ℕ => Real.exp (-Real.pi * n ^ 2 * t)) := by
        have := summable_geometric_of_lt_one ( by positivity ) ( show Real.exp ( -Real.pi * t ) < 1 by rw [ Real.exp_lt_one_iff ] ; nlinarith [ Real.pi_pos ] );
        exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
      convert h_summable.comp_injective ( show Function.Injective ( fun k : ℕ => k + 1 ) from by intros a b; aesop ) using 2 ; norm_num ; ring;
      norm_num;
  have h_sum_bound : ∑' n : ℕ, Real.exp (-Real.pi * (n + 1) ^ 2 * t) ≤ Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t)) := by
    have h_sum_bound : ∑' n : ℕ, Real.exp (-Real.pi * (n + 1) ^ 2 * t) ≤ ∑' n : ℕ, (Real.exp (-Real.pi * t)) ^ (n + 1) := by
      refine' Summable.tsum_le_tsum _ _ _;
      · intro n; rw [ ← Real.exp_nat_mul ] ; ring_nf; norm_num;
        nlinarith [ Real.pi_pos, mul_le_mul_of_nonneg_left ht Real.pi_pos.le, mul_le_mul_of_nonneg_left ( show ( n : ℝ ) ^ 2 ≥ n by norm_cast; nlinarith ) Real.pi_pos.le ];
      · have h_summable : Summable (fun n : ℕ => Real.exp (-Real.pi * n * t)) := by
          have h_summable : Summable (fun n : ℕ => (Real.exp (-Real.pi * t)) ^ n) := by
            exact summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; nlinarith [ Real.pi_pos ] );
          exact h_summable.congr fun n => by rw [ ← Real.exp_nat_mul ] ; ring;
        exact Summable.of_nonneg_of_le ( fun n => Real.exp_nonneg _ ) ( fun n => Real.exp_le_exp.mpr <| by nlinarith [ Real.pi_pos, mul_nonneg Real.pi_pos.le <| Nat.cast_nonneg n, mul_nonneg Real.pi_pos.le <| sq_nonneg <| ( n : ℝ ) ] ) h_summable;
      · exact Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; nlinarith [ Real.pi_pos ] ) ) ( Nat.succ_injective );
    exact h_sum_bound.trans_eq ( by erw [ div_eq_mul_inv ] ; erw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; nlinarith [ Real.pi_pos ] ) ] ; erw [ ← tsum_mul_left ] ; exact tsum_congr fun n => by ring );
  -- For $t \geq 1$, we have $\exp(-\pi t) \leq \exp(-\pi) < \frac{1}{20}$.
  have h_exp_bound : Real.exp (-Real.pi * t) ≤ 1 / 20 := by
    have h_exp_bound : Real.exp (-Real.pi) < 1 / 20 := by
      rw [ Real.exp_neg ];
      rw [ inv_eq_one_div, div_lt_div_iff₀ ] <;> linarith [ Real.exp_pi_gt_twenty ];
    exact le_trans ( Real.exp_le_exp.mpr ( by nlinarith [ Real.pi_pos ] ) ) h_exp_bound.le;
  rw [ le_div_iff₀ ] at h_sum_bound <;> nlinarith [ Real.exp_pos ( -Real.pi * t ) ]

/-
Step 2: The integral of the weighted norm of f_modif is bounded.
-/
lemma mellin_norm_bound (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∫ t in Set.Ioi (0:ℝ), t ^ (σ / 2 - 1) *
      ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖
    ≤ 4 / (19 * Real.pi) := by
  -- Split the integral into two parts: from 0 to 1 and from 1 to ∞.
  have h_split : ∫ t in Set.Ioi (0 : ℝ), t ^ (σ / 2 - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖ = (∫ t in Set.Ioo (0 : ℝ) 1, t ^ (σ / 2 - 1) * (HurwitzZeta.evenKernel 0 t - t ^ (-1 / 2 : ℝ))) + (∫ t in Set.Ioi (1 : ℝ), t ^ (σ / 2 - 1) * (HurwitzZeta.evenKernel 0 t - 1)) := by
    have h_split : ∫ t in Set.Ioi (0 : ℝ), t ^ (σ / 2 - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖ = (∫ t in Set.Ioo (0 : ℝ) 1, t ^ (σ / 2 - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖) + (∫ t in Set.Ioi (1 : ℝ), t ^ (σ / 2 - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖) := by
      rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.setIntegral_union ] <;> norm_num;
      · have := zeta_f_modif_mellinConvergent ( σ / 2 );
        have := this.norm;
        refine' MeasureTheory.IntegrableOn.mono_set _ ( Set.Ioc_subset_Ioi_self );
        refine' this.congr _;
        filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht ] ; norm_num [ Complex.ofReal_re ] ;
      · have := zeta_f_modif_mellinConvergent ( σ / 2 );
        refine' MeasureTheory.IntegrableOn.mono_set _ ( Set.Ioi_subset_Ioi zero_le_one );
        refine' this.norm.congr _;
        filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;
        convert norm_cpow_smul ht _ _ using 1;
        norm_num [ Complex.div_re ];
    convert h_split using 2 <;> norm_num [ HurwitzZeta.hurwitzEvenFEPair ];
    · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => _;
      unfold WeakFEPair.f_modif; norm_num [ ht.1.le, ht.2.le ] ;
      rw [ Set.indicator_of_mem ] <;> norm_num [ ht ];
      norm_cast ; norm_num [ Real.rpow_neg ht.1.le ];
      rw [ abs_of_nonneg ] <;> norm_num [ ← Real.sqrt_eq_rpow ];
      convert HurwitzZeta.evenKernel_zero_ge_rpow ht.1 using 1 ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ht.1.le ];
    · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
      unfold WeakFEPair.f_modif; norm_num [ ht.out.le ] ;
      rw [ Set.indicator_of_mem ] <;> norm_num [ ht.out ];
      norm_cast;
      exact Or.inl ( by rw [ Real.norm_of_nonneg ( sub_nonneg_of_le <| by exact le_trans ( by norm_num ) <| HurwitzZeta.evenKernel_zero_ge_one <| zero_lt_one.trans ht ) ] );
  -- For the part from 1 to ∞, we use the bound from `evenKernel_zero_sub_one_le`.
  have h_part1 : ∫ t in Set.Ioi (1 : ℝ), t ^ (σ / 2 - 1) * (HurwitzZeta.evenKernel 0 t - 1) ≤ (40 / 19) * (Real.exp (-Real.pi)) / Real.pi := by
    have h_part1 : ∫ t in Set.Ioi (1 : ℝ), t ^ (σ / 2 - 1) * (HurwitzZeta.evenKernel 0 t - 1) ≤ ∫ t in Set.Ioi (1 : ℝ), (40 / 19) * Real.exp (-Real.pi * t) := by
      refine' MeasureTheory.integral_mono_of_nonneg _ _ _ <;> norm_num +zetaDelta at *;
      · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => mul_nonneg ( Real.rpow_nonneg ( by linarith [ hx.out ] ) _ ) ( sub_nonneg.mpr ( HurwitzZeta.evenKernel_zero_ge_one ( by linarith [ hx.out ] ) ) ) );
      · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-Real.pi * t)) (Set.Ioi (0 : ℝ)) := by
          have := ( exp_neg_integrableOn_Ioi 0 Real.pi_pos ) ; aesop;
        simpa only [ neg_mul ] using MeasureTheory.Integrable.const_mul ( h_integrable.mono_set <| Set.Ioi_subset_Ioi zero_le_one ) _;
      · rw [ Filter.EventuallyLE, Filter.eventually_inf_principal ];
        filter_upwards [ ] with x hx using le_trans ( mul_le_of_le_one_left ( sub_nonneg.mpr <| HurwitzZeta.evenKernel_zero_ge_one <| by linarith [ hx.out ] ) <| by simpa using rpow_weight_le_one hx.out.le hσ0 hσ1 ) <| by simpa using HurwitzZeta.evenKernel_zero_sub_one_le hx.out.le;
    have h_part1_eval : ∫ t in Set.Ioi (1 : ℝ), Real.exp (-Real.pi * t) = (Real.exp (-Real.pi)) / Real.pi := by
      have := integral_exp_neg_mul_rpow zero_lt_one Real.pi_pos;
      -- Now use the fact that the integral of $e^{-\pi t}$ over $(1, \infty)$ is the same as the integral over $(0, \infty)$ shifted by 1.
      have h_shift : ∫ t in Set.Ioi (1 : ℝ), Real.exp (-Real.pi * t) = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-Real.pi * (t + 1)) := by
        rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
        rw [ ← MeasureTheory.integral_add_right_eq_self _ 1 ] ; congr ; ext ; rw [ Set.indicator_apply ] ; aesop;
      simp_all +decide [ div_eq_mul_inv, Real.rpow_neg_one, mul_add, Real.exp_add, MeasureTheory.integral_const_mul ];
      rw [ MeasureTheory.integral_mul_const, this ] ; norm_num ; ring;
    exact h_part1.trans_eq ( by rw [ MeasureTheory.integral_const_mul, h_part1_eval ] ; ring );
  -- For the part from 0 to 1, we use the substitution $u = 1/t$.
  have h_part2 : ∫ t in Set.Ioo (0 : ℝ) 1, t ^ (σ / 2 - 1) * (HurwitzZeta.evenKernel 0 t - t ^ (-1 / 2 : ℝ)) = ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ / 2 - 1 / 2) * (HurwitzZeta.evenKernel 0 u - 1) := by
    have h_subst : ∀ {f : ℝ → ℝ}, (∫ t in Set.Ioo (0 : ℝ) 1, f t) = (∫ u in Set.Ioi (1 : ℝ), f (1 / u) * (1 / u ^ 2)) := by
      intros f
      have h_subst : ∫ t in Set.Ioo (0 : ℝ) 1, f t = ∫ u in (Set.Ioi (1 : ℝ)), f (1 / u) * (1 / u ^ 2) := by
        have : ∫ t in Set.Ioo (0 : ℝ) 1, f t = ∫ u in (Set.image (fun t => 1 / t) (Set.Ioo (0 : ℝ) 1)), f (1 / u) * (1 / u ^ 2) := by
          rw [ MeasureTheory.integral_image_eq_integral_abs_deriv_smul ] <;> norm_num;
          any_goals intro x hx₁ hx₂; exact hasDerivAt_inv hx₁.ne' |> HasDerivAt.hasDerivWithinAt;
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [ abs_of_nonpos ( neg_nonpos_of_nonneg ( inv_nonneg.2 ( sq_nonneg x ) ) ) ] ; simp +decide [ hx.1.ne', hx.2.ne', mul_assoc, mul_comm, mul_left_comm ] ;
        convert this using 1;
        congr with x ; norm_num;
        exact ⟨ fun hx => ⟨ by linarith, inv_lt_one_of_one_lt₀ hx ⟩, fun hx => by nlinarith [ inv_mul_cancel₀ ( by linarith : x ≠ 0 ) ] ⟩;
      exact h_subst;
    rw [ h_subst ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => _ ; norm_num [ Real.rpow_neg, hu.out.le ] ; ring;
    rw [ HurwitzZeta.evenKernel_functional_equation ] ; norm_num [ Real.rpow_add, Real.rpow_neg, hu.out.le ] ; ring;
    norm_num [ ← Real.rpow_neg_one, ← Real.rpow_add ( inv_pos.mpr ( zero_lt_one.trans hu ) ), ← Real.rpow_neg ( inv_nonneg.mpr ( zero_le_one.trans hu.out.le ) ) ] ; ring;
    norm_num [ ← Real.rpow_mul ( by linarith [ hu.out ] : 0 ≤ u ), ← Real.rpow_add ( by linarith [ hu.out ] : 0 < u ) ] ; ring;
    norm_num [ sq, mul_assoc, ← Real.rpow_add ( by linarith [ hu.out ] : 0 < u ) ] ; ring;
    rw [ show ( -1 / 2 + σ * ( -1 / 2 ) : ℝ ) = ( 3 / 2 + σ * ( -1 / 2 ) ) - 2 by ring, Real.rpow_sub ( by linarith [ hu.out ] ) ] ; norm_num ; ring;
    rw [ HurwitzZeta.cosKernel_zero_eq_evenKernel_zero ] ; ring;
    norm_cast ; norm_num ; ring;
  -- For the part from 0 to 1, we use the bound from `evenKernel_zero_sub_one_le`.
  have h_part2_bound : ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ / 2 - 1 / 2) * (HurwitzZeta.evenKernel 0 u - 1) ≤ (40 / 19) * (Real.exp (-Real.pi)) / Real.pi := by
    refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
    refine' fun u => ( 40 / 19 ) * Real.exp ( -Real.pi * u );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using mul_nonneg ( Real.rpow_nonneg ( by linarith [ hu.out ] ) _ ) ( sub_nonneg.mpr ( HurwitzZeta.evenKernel_zero_ge_one ( by linarith [ hu.out ] ) ) );
    · have h_integrable : MeasureTheory.IntegrableOn (fun u => Real.exp (-Real.pi * u)) (Set.Ioi (1 : ℝ)) := by
        have := ( exp_neg_integrableOn_Ioi 0 Real.pi_pos );
        exact this.mono_set <| Set.Ioi_subset_Ioi zero_le_one;
      exact h_integrable.const_mul _;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu;
      refine' le_trans ( mul_le_mul_of_nonneg_left ( HurwitzZeta.evenKernel_zero_sub_one_le hu.out.le ) ( Real.rpow_nonneg ( by linarith [ hu.out ] ) _ ) ) _;
      exact mul_le_of_le_one_left ( by positivity ) ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le hu.out.le ( show -σ / 2 - 1 / 2 ≤ 0 by linarith ) ) ( by norm_num ) );
    · have := integral_exp_neg_mul_rpow zero_lt_one Real.pi_pos;
      norm_num [ Real.rpow_neg_one ] at this;
      -- Now use the fact that the integral of $e^{-\pi x}$ over $(1, \infty)$ is $\frac{e^{-\pi}}{\pi}$.
      have h_int : ∫ x in Set.Ioi (1 : ℝ), Real.exp (-(Real.pi * x)) = Real.exp (-Real.pi) / Real.pi := by
        have h_int : ∫ x in Set.Ioi (1 : ℝ), Real.exp (-(Real.pi * x)) = (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(Real.pi * (x + 1)))) := by
          rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
          rw [ ← MeasureTheory.integral_add_right_eq_self _ 1 ] ; congr ; ext x ; rw [ Set.indicator_apply, Set.indicator_apply ] ; aesop;
        simp_all +decide [ div_eq_mul_inv, mul_add, Real.exp_add, MeasureTheory.integral_const_mul ];
      norm_num [ div_eq_mul_inv, MeasureTheory.integral_const_mul, h_int ];
      linarith;
  -- Using the fact that $e^{-\pi} < \frac{1}{20}$, we can further bound the expression.
  have h_exp_bound : Real.exp (-Real.pi) < 1 / 20 := by
    rw [ Real.exp_neg ];
    rw [ inv_lt_comm₀ ] <;> norm_num <;> linarith [ Real.exp_pi_gt_twenty ];
  ring_nf at *; nlinarith [ Real.pi_gt_three, mul_inv_cancel₀ Real.pi_ne_zero ] ;

/-- The norm of completedRiemannZeta₀ is bounded by 2/(19π). -/
lemma completedRiemannZeta₀_norm_le {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ 2 / (19 * Real.pi) := by
  calc ‖completedRiemannZeta₀ s‖
      ≤ (∫ t in Set.Ioi (0:ℝ), t ^ (s.re / 2 - 1) *
          ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖) / 2 :=
        norm_completedRiemannZeta₀_le_mellin_norm s
    _ ≤ (4 / (19 * Real.pi)) / 2 := by
        apply div_le_div_of_nonneg_right (mellin_norm_bound s.re hs0 hs1) (by norm_num)
    _ = 2 / (19 * Real.pi) := by ring