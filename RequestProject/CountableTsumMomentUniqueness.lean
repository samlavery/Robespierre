import Mathlib

/-!
# Countable Moment Uniqueness Principle

This file proves the countable tsum moment uniqueness principle.
-/

open scoped BigOperators
open Complex

set_option maxHeartbeats 800000

noncomputable section

/-! ## Helper: summability of the exponential series -/

/-- Exponential summability implies summability of c_n * exp(α_n * z) for any z. -/
lemma summable_cexp_mul
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hc_exp_summable : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (z : ℂ) :
    Summable (fun n => c n * Complex.exp (α n * z)) := by
  by_cases hz : ‖z‖ = 0
  · refine .of_norm ?_
    simpa [show z = 0 by simpa using hz] using
      hc_exp_summable 1 zero_lt_one |>.of_nonneg_of_le (fun n => norm_nonneg _) fun n => by
        simpa using
          mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (norm_nonneg _)
  · have := hc_exp_summable ‖z‖ (by positivity)
    exact .of_norm <| by
      simpa [mul_comm] using
        this.of_nonneg_of_le (fun n => by positivity) (fun n => by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_left (Complex.norm_exp_le_exp_norm (α n * z))
              (by positivity))

/-
If all power moments vanish, then ∑ c_n exp(α_n * z) = 0 for all z.
-/
lemma tsum_cexp_eq_zero
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hc_exp_summable : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (hmoments : ∀ k : ℕ, HasSum (fun n => c n * α n ^ k) 0)
    (z : ℂ) :
    HasSum (fun n => c n * Complex.exp (α n * z)) 0 := by
  -- Using the linearity of the limit and that the series is absolutely convergent, we can interchange the order of summation.
  have : ∑' n, c n * Complex.exp (α n * z) = ∑' n, c n * (∑' k, (α n * z)^k / Nat.factorial k) := by
    norm_num [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div ];
  have h_fubini : Summable (fun p : ℕ × ℕ => ‖c p.1 * (α p.1 * z)^p.2 / Nat.factorial p.2‖) := by
    have h_fubini : Summable (fun n => ‖c n‖ * Real.exp (‖α n‖ * ‖z‖)) := by
      by_cases hz : ‖z‖ = 0;
      · simpa [ hz ] using hmoments 0 |> HasSum.summable |> Summable.norm;
      · simpa only [ mul_comm ] using hc_exp_summable ‖z‖ ( by positivity );
    have h_fubini : Summable (fun p : ℕ × ℕ => ‖c p.1‖ * (‖α p.1‖ * ‖z‖)^p.2 / Nat.factorial p.2) := by
      rw [ summable_prod_of_nonneg ];
      · simp_all +decide [ mul_div_assoc, tsum_mul_left ];
        exact ⟨ fun n => Summable.mul_left _ <| Real.summable_pow_div_factorial _, by simpa only [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ] using h_fubini ⟩;
      · exact fun _ => by positivity;
    convert h_fubini using 2 ; norm_num [ mul_pow, mul_div_assoc ];
  have h_fubini : ∑' n, c n * (∑' k, (α n * z)^k / Nat.factorial k) = ∑' k, (∑' n, c n * (α n * z)^k / Nat.factorial k) := by
    rw [ ← Summable.tsum_comm ];
    · simp +decide only [mul_div_assoc, tsum_mul_left];
    · refine' .of_norm _;
      convert h_fubini.comp_injective ( Prod.swap_injective ) using 1;
  have h_fubini : ∑' k, (∑' n, c n * (α n * z)^k / Nat.factorial k) = ∑' k, (0 * z^k / Nat.factorial k) := by
    refine' tsum_congr fun k => _;
    convert congr_arg ( fun x : ℂ => x * z ^ k / ( k.factorial : ℂ ) ) ( HasSum.tsum_eq ( hmoments k ) ) using 1 ; ring;
    rw [ ← tsum_mul_left ] ; exact tsum_congr fun _ => by ring;
  convert Summable.hasSum _ using 1;
  · aesop;
  · convert summable_cexp_mul α c hc_exp_summable z using 1

/-! ## Finite linear independence of exponentials -/

/-
Finite linear independence of exponentials: if α₁, ..., αₘ are distinct complex
    numbers and ∑ cᵢ exp(αᵢ z) = 0 for all z, then cᵢ = 0 for all i.
    Proof by induction: differentiate and subtract α₀ × original to eliminate the 0th term.
-/
lemma finite_exp_linIndep
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → ℂ) (c : ι → ℂ)
    (hα_inj : Function.Injective α)
    (h : ∀ z : ℂ, ∑ i, c i * Complex.exp (α i * z) = 0) :
    ∀ i, c i = 0 := by
  -- We proceed by induction on the number of terms.
  have h_ind : ∀ n : ℕ, ∀ (α : Fin n → ℂ) (c : Fin n → ℂ), Function.Injective α → (∀ z : ℂ, ∑ i, c i * Complex.exp (α i * z) = 0) → ∀ i, c i = 0 := by
    intro n
    induction' n with n ih;
    · simp +decide;
    · intro α c hα_inj h
      have h_diff : ∀ z : ℂ, ∑ i, c i * (α i - α 0) * Complex.exp (α i * z) = 0 := by
        intro z
        -- Compute the derivative of the finite exp sum.
        have hd : HasDerivAt (fun z : ℂ => ∑ i, c i * Complex.exp (α i * z))
            (∑ i, c i * α i * Complex.exp (α i * z)) z := by
          refine HasDerivAt.fun_sum (fun i _ => ?_)
          have h1 : HasDerivAt (fun z : ℂ => α i * z) (α i) z := by
            simpa using (hasDerivAt_id z).const_mul (α i)
          have h2 : HasDerivAt (fun z : ℂ => Complex.exp (α i * z))
              (Complex.exp (α i * z) * α i) z :=
            (Complex.hasDerivAt_exp (α i * z)).comp z h1
          have h3 := h2.const_mul (c i)
          convert h3 using 1; ring
        -- The function is identically zero, so its derivative is zero.
        have hf_zero : (fun z : ℂ => ∑ i, c i * Complex.exp (α i * z)) = fun _ => 0 :=
          funext h
        have hmom1 : ∑ i, c i * α i * Complex.exp (α i * z) = 0 := by
          have := hd.deriv
          rw [hf_zero, deriv_const'] at this
          exact this.symm
        have hmom0 : α 0 * ∑ i, c i * Complex.exp (α i * z) = 0 := by
          rw [h z]; ring
        -- Subtract: ∑ c_i (α_i - α_0) exp(α_i z) = ∑ c_i α_i exp(α_i z) - α_0 · ∑ c_i exp(α_i z).
        have hsplit : ∑ i, c i * (α i - α 0) * Complex.exp (α i * z) =
            (∑ i, c i * α i * Complex.exp (α i * z)) -
              α 0 * (∑ i, c i * Complex.exp (α i * z)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        rw [hsplit, hmom1, hmom0]; ring
      -- By the induction hypothesis, since $\alpha_i - \alpha_0 \neq 0$ for $i \neq 0$, we have $c_i = 0$ for all $i \neq 0$.
      have h_ind_hyp : ∀ i : Fin n, c (Fin.succ i) = 0 := by
        specialize ih ( fun i => α i.succ ) ( fun i => c i.succ * ( α i.succ - α 0 ) ) ( fun i j hij => by simpa [ Fin.ext_iff, hα_inj.eq_iff ] using hij ) ( fun z => by
          simp_all +decide [ Fin.sum_univ_succ ] );
        exact fun i => eq_zero_of_ne_zero_of_mul_right_eq_zero ( sub_ne_zero_of_ne <| hα_inj.ne <| ne_of_gt <| Fin.succ_pos i ) <| ih i;
      intro i; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.sum_univ_succ ] ;
  specialize h_ind ( Fintype.card ι ) ( fun i => α ( Fintype.equivFin ι |>.symm i ) ) ( fun i => c ( Fintype.equivFin ι |>.symm i ) ) ?_ ?_;
  · exact hα_inj.comp ( Equiv.injective _ );
  · exact fun z => by rw [ ← h z, ← Equiv.sum_comp ( Fintype.equivFin ι ) ] ; simp +decide ;
  · exact fun i => by simpa using h_ind ( Fintype.equivFin ι i ) ;

/-! ## Coefficient extraction from identically zero exponential sum -/

/-
Summability of c_n * α_n^k from exponential summability.
-/
lemma summable_mul_pow_of_exp_summable
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hc_exp_summable : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (k : ℕ) :
    Summable (fun n => c n * α n ^ k) := by
  have := hc_exp_summable 1 zero_lt_one;
  -- Since ‖α n‖^k ≤ k! * exp(‖α n‖) (from the Taylor series bound x^k/k! ≤ exp(x)), we have ‖c n * α n^k‖ ≤ k! * ‖c n‖ * exp(‖α n‖).
  have h_bound : ∀ n, ‖c n * α n ^ k‖ ≤ (Nat.factorial k) * ‖c n‖ * Real.exp (‖α n‖) := by
    intro n
    have h_bound : ‖α n‖ ^ k ≤ (Nat.factorial k) * Real.exp (‖α n‖) := by
      rw [ ← div_le_iff₀' ( by positivity ) ];
      rw [ Real.exp_eq_exp_ℝ ];
      rw [ NormedSpace.exp_eq_tsum_div ];
      exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) k ( fun _ _ => by positivity );
    simpa [ mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_left h_bound ( norm_nonneg ( c n ) );
  exact .of_norm <| Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => h_bound n ) <| by simpa [ mul_assoc ] using this.mul_left _;

/-
Auxiliary: the moment conditions ∑ c_n α_n^k = 0 follow from ∑ c_n exp(α_n z) = 0.
-/
lemma moments_of_exp_sum_zero
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hc_exp_summable : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (hsum_zero : ∀ z : ℂ, HasSum (fun n => c n * Complex.exp (α n * z)) 0) :
    ∀ k : ℕ, HasSum (fun n => c n * α n ^ k) 0 := by
  -- By differentiating the series term-by-term, we can show that the moments are zero.
  have h_diff : ∀ k : ℕ, HasSum (fun n => c n * (α n) ^ k) 0 := by
    intro k
    have h_deriv : ∀ z : ℂ, HasSum (fun n => c n * (α n) ^ k * Complex.exp (α n * z)) (deriv^[k] (fun z => ∑' n, c n * Complex.exp (α n * z)) z) := by
      induction' k with k ih <;> simp_all +decide [ Function.iterate_succ_apply' ];
      · exact fun z => Summable.hasSum ( hsum_zero z |> HasSum.summable );
      · intro z
        have h_deriv : HasDerivAt (fun z => ∑' n, c n * α n ^ k * Complex.exp (α n * z)) (∑' n, c n * α n ^ (k + 1) * Complex.exp (α n * z)) z := by
          rw [ hasDerivAt_iff_tendsto_slope_zero ];
          have h_deriv_step : Filter.Tendsto (fun t => ∑' n, c n * (α n) ^ k * (Complex.exp (α n * (z + t)) - Complex.exp (α n * z)) / t) (nhdsWithin 0 {0}ᶜ) (nhds (∑' n, c n * (α n) ^ (k + 1) * Complex.exp (α n * z))) := by
            refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
            use fun n => ‖c n‖ * ‖α n‖ ^ ( k + 1 ) * Real.exp ( ‖α n‖ * ( ‖z‖ + 1 ) );
            · have h_summable : Summable (fun n => ‖c n‖ * Real.exp ((‖z‖ + 2) * ‖α n‖)) := by
                exact hc_exp_summable _ ( by positivity );
              have h_summable : Summable (fun n => ‖c n‖ * Real.exp ((‖z‖ + 2) * ‖α n‖) * (‖α n‖ ^ (k + 1) * Real.exp (-‖α n‖))) := by
                have h_summable : ∃ C : ℝ, ∀ n, ‖α n‖ ^ (k + 1) * Real.exp (-‖α n‖) ≤ C := by
                  have h_summable : ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → x ^ (k + 1) * Real.exp (-x) ≤ C := by
                    have h_summable : Filter.Tendsto (fun x : ℝ => x ^ (k + 1) * Real.exp (-x)) Filter.atTop (nhds 0) := by
                      exact ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero _ );
                    have := h_summable.eventually ( ge_mem_nhds zero_lt_one );
                    obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp this;
                    exact ⟨ Max.max 1 ( SupSet.sSup ( Set.image ( fun x : ℝ => x ^ ( k + 1 ) * Real.exp ( -x ) ) ( Set.Icc 0 M ) ) ), fun x hx => if hx' : x ≤ M then le_trans ( by exact le_csSup ( by exact ( isCompact_Icc.image ( by continuity ) ) |> IsCompact.bddAbove ) <| Set.mem_image_of_mem _ <| by constructor <;> linarith ) <| le_max_right _ _ else le_trans ( hM x <| by linarith ) <| le_max_left _ _ ⟩;
                  exact ⟨ h_summable.choose, fun n => h_summable.choose_spec _ ( norm_nonneg _ ) ⟩;
                exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( mul_nonneg ( norm_nonneg _ ) ( Real.exp_nonneg _ ) ) ( mul_nonneg ( pow_nonneg ( norm_nonneg _ ) _ ) ( Real.exp_nonneg _ ) ) ) ( fun n => mul_le_mul_of_nonneg_left ( h_summable.choose_spec n ) ( mul_nonneg ( norm_nonneg _ ) ( Real.exp_nonneg _ ) ) ) ( Summable.mul_right _ ‹_› );
              convert h_summable using 2 ; ring;
              simpa only [ mul_assoc, ← Real.exp_add ] using by ring;
            · intro n; have := HasDerivAt.tendsto_slope_zero ( HasDerivAt.const_mul ( c n * α n ^ k ) ( HasDerivAt.comp 0 ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul ( α n ) ( hasDerivAt_id 0 |> HasDerivAt.const_add z ) ) ) ) ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_succ ] ;
              convert this using 2 ; ring;
            · rw [ eventually_nhdsWithin_iff ];
              rw [ Metric.eventually_nhds_iff ];
              refine' ⟨ 1, by norm_num, fun y hy hy' n => _ ⟩ ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_succ, Complex.norm_exp ];
              -- Apply the triangle inequality and the fact that $|e^{i\theta}| = 1$ for any real $\theta$.
              have h_triangle : ‖Complex.exp (α n * (z + y)) - Complex.exp (z * α n)‖ ≤ ‖α n‖ * ‖y‖ * Real.exp (‖α n‖ * (‖z‖ + 1)) := by
                have h_triangle : ‖Complex.exp (α n * (z + y)) - Complex.exp (z * α n)‖ ≤ ‖α n * y‖ * Real.exp (‖α n‖ * (‖z‖ + 1)) := by
                  have h_exp : Complex.exp (α n * (z + y)) - Complex.exp (z * α n) = ∫ t in (0 : ℝ)..1, α n * y * Complex.exp (α n * (z + t * y)) := by
                    rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
                    rotate_right;
                    use fun t => Complex.exp ( α n * ( z + t * y ) );
                    · norm_num [ mul_comm ];
                    · intro t ht; convert HasDerivAt.comp t ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul ( α n ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) ) ) using 1 ; norm_num ; ring;
                    · exact Continuous.intervalIntegrable ( by continuity ) _ _
                  rw [ h_exp, intervalIntegral.integral_of_le zero_le_one ];
                  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) _;
                  norm_num [ Complex.norm_exp ];
                  refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun t ht => mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| show ( α n |> Complex.re ) * ( z.re + t * y.re ) - ( α n |> Complex.im ) * ( z.im + t * y.im ) ≤ ‖α n‖ * ( ‖z‖ + 1 ) from _ ) <| by positivity ) _;
                  · exact Continuous.integrableOn_Ioc ( by continuity );
                  · exact Continuous.integrableOn_Ioc ( by continuity );
                  · have h_triangle : ‖α n‖ * ‖z + t * y‖ ≤ ‖α n‖ * (‖z‖ + 1) := by
                      exact mul_le_mul_of_nonneg_left ( le_trans ( norm_add_le _ _ ) ( by simpa [ abs_of_nonneg ht.1.le ] using by nlinarith [ ht.1, ht.2, norm_nonneg z, norm_nonneg y ] ) ) ( norm_nonneg _ );
                    refine' le_trans _ h_triangle;
                    convert Complex.re_le_norm ( α n * ( z + t * y ) ) using 1 ; norm_num [ Complex.normSq, Complex.norm_def ] ; ring;
                    rw [ ← add_mul, norm_mul, mul_comm ];
                  · norm_num;
                simpa only [ norm_mul ] using h_triangle;
              rw [ inv_mul_le_iff₀ ( norm_pos_iff.mpr hy' ) ];
              convert mul_le_mul_of_nonneg_left h_triangle ( by positivity : 0 ≤ ‖α n‖ ^ k * ‖c n‖ ) using 1 ; ring;
              ring;
          convert h_deriv_step using 2;
          rw [ ← Summable.tsum_sub ( ih _ |> HasSum.summable ) ( ih _ |> HasSum.summable ) ] ; norm_num [ div_eq_inv_mul, mul_sub, tsum_mul_left ];
          rw [ ← tsum_mul_left ] ; congr ; ext ; ring;
        convert h_deriv.deriv.symm ▸ Summable.hasSum _ using 1;
        · exact congr_arg ( deriv · z ) ( funext fun z => ih z |> HasSum.tsum_eq |> Eq.symm );
        · have := @summable_mul_pow_of_exp_summable;
          specialize this α ( fun n => c n * Complex.exp ( α n * z ) ) ?_ ( k + 1 ) <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, pow_succ, Complex.exp_ne_zero ];
          simp_all +decide [ Complex.norm_exp ];
          intro r hr; specialize hc_exp_summable ( r + |z.re| + |z.im| ) ( by positivity ) ; simp_all +decide [ ← Real.exp_add ] ;
          refine' .of_nonneg_of_le ( fun n => mul_nonneg ( norm_nonneg _ ) ( Real.exp_nonneg _ ) ) ( fun n => _ ) hc_exp_summable;
          exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by cases abs_cases z.re <;> cases abs_cases z.im <;> nlinarith [ abs_le.mp ( Complex.abs_re_le_norm ( α n ) ), abs_le.mp ( Complex.abs_im_le_norm ( α n ) ) ] ) ( norm_nonneg _ )
    convert h_deriv 0 using 1 ; norm_num [ show ( fun z => ∑' n, c n * Complex.exp ( α n * z ) ) = fun _ => 0 from funext fun _ => HasSum.tsum_eq ( hsum_zero _ ) ];
    rw [ show ( fun z => ∑' n, c n * cexp ( α n * z ) ) = fun _ => 0 from funext fun _ => HasSum.tsum_eq ( hsum_zero _ ) ] ; norm_num [ Function.iterate_fixed ];
  assumption

/-
Auxiliary: absolute summability of c_n (consequence of exponential summability).
-/
lemma summable_norm_of_exp_summable
    (c : ℕ → ℂ)
    (α : ℕ → ℂ)
    (hc_exp_summable : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖))) :
    Summable (fun n => ‖c n‖) := by
  exact Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => le_mul_of_one_le_right ( norm_nonneg _ ) ( Real.one_le_exp ( by positivity ) ) ) ( hc_exp_summable 1 zero_lt_one )


/-! ## Resolvent approach to coefficient extraction -/

/-
A locally finite subset of ℂ (indexed by ℕ) has closed range.
-/
lemma range_isClosed_of_loc_finite
    (α : ℕ → ℂ)
    (hα_loc_finite : ∀ R : ℝ, Set.Finite {n : ℕ | ‖α n‖ ≤ R}) :
    IsClosed (Set.range α) := by
  refine' isClosed_of_closure_subset fun x hx => _;
  -- Since x is in the closure of the range of α, for every ε > 0, there exists an element in the range of α within ε of x. But since the range is locally finite, this implies that x must be one of the elements in the range.
  have h_seq : ∃ (n : ℕ → ℕ), Filter.Tendsto (fun k => α (n k)) Filter.atTop (nhds x) := by
    rw [ mem_closure_iff_seq_limit ] at hx;
    obtain ⟨ y, hy₁, hy₂ ⟩ := hx; choose f hf using hy₁; use f; aesop;
  obtain ⟨ n, hn ⟩ := h_seq
  have h_bounded : ∃ R, ∀ k, ‖α (n k)‖ ≤ R := by
    exact ⟨ _, fun k => le_csSup ( hn.norm.bddAbove_range ) ⟨ k, rfl ⟩ ⟩;
  -- Since the range is locally finite, the sequence (α (n k)) must be finite.
  have h_finite : Set.Finite (Set.range (fun k => α (n k))) := by
    exact Set.Finite.subset ( Set.Finite.image α ( hα_loc_finite h_bounded.choose ) ) ( Set.range_subset_iff.mpr fun k => Set.mem_image_of_mem _ ( h_bounded.choose_spec k ) );
  have := h_finite.isClosed.mem_of_tendsto hn ; aesop

/-
The resolvent series ∑ c_n / (s - α_n) is summable for s outside the range of α.
-/
lemma resolvent_summable
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hc_summable : Summable (fun n => ‖c n‖))
    (hα_loc_finite : ∀ R : ℝ, Set.Finite {n : ℕ | ‖α n‖ ≤ R})
    (s : ℂ) (hs : s ∉ Set.range α) :
    Summable (fun n => c n / (s - α n)) := by
  -- For s ∉ range α, s - α n ≠ 0 for all n. We want to show Summable (fun n => c n / (s - α n)). It suffices to show Summable (fun n => ‖c n / (s - α n)‖) = Summable (fun n => ‖c n‖ / ‖s - α n‖).
  suffices h_norm_summable : Summable (fun n => ‖c n‖ / ‖s - α n‖) by
    exact .of_norm <| by simpa using h_norm_summable;
  -- Since ‖α n‖ is large for large n, we can bound ‖s - α n‖ from below.
  have h_bound : ∃ N, ∀ n ≥ N, ‖s - α n‖ ≥ 1 := by
    have h_bound : ∃ N, ∀ n ≥ N, ‖α n‖ ≥ 1 + ‖s‖ := by
      exact Set.Finite.bddAbove ( hα_loc_finite ( 1 + ‖s‖ ) ) |> fun ⟨ N, hN ⟩ => ⟨ N + 1, fun n hn => not_lt.1 fun contra => not_lt_of_ge ( hN contra.le ) hn ⟩;
    exact ⟨ h_bound.choose, fun n hn => by have := h_bound.choose_spec n hn; have := norm_sub_le ( s - α n ) s; norm_num at *; linarith ⟩;
  obtain ⟨ N, hN ⟩ := h_bound;
  rw [ ← summable_nat_add_iff N ] at *;
  exact Summable.of_nonneg_of_le ( fun n => div_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ( fun n => div_le_self ( norm_nonneg _ ) ( hN _ ( by linarith ) ) ) hc_summable

/-
The resolvent G(s) = ∑ c_n / (s - α_n) is zero for Re(s) > σ₀ + 1.
    Proof: For each finite N, ∑_{n≤N} c_n/(s-α_n) = ∫_{Ioi 0} [∑_{n≤N} c_n exp((α_n-s)t)] dt
    = -∫_{Ioi 0} [∑_{n>N} c_n exp(α_n t)] exp(-st) dt → 0 by dominated convergence.
-/
lemma resolvent_eq_zero_halfplane
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (σ₀ : ℝ) (hα_bdd_re : ∀ n, (α n).re ≤ σ₀)
    (hc_summable : Summable (fun n => ‖c n‖))
    (hc_exp_summable : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (hsum_zero : ∀ z : ℂ, HasSum (fun n => c n * Complex.exp (α n * z)) 0)
    (s : ℂ) (hs : σ₀ + 1 < s.re) :
    ∑' n, c n / (s - α n) = 0 := by
  -- By Fubini's theorem, we can interchange the sum and the integral.
  have h_fubini : ∑' (n : ℕ), c n / (s - α n) = ∫ t in Set.Ioi (0 : ℝ), (∑' (n : ℕ), c n * Complex.exp ((α n - s) * t)) := by
    rw [ MeasureTheory.integral_tsum ];
    · refine' tsum_congr fun n => _;
      have h_integral : ∫ t in Set.Ioi (0 : ℝ), Complex.exp ((α n - s) * t) = -1 / (α n - s) := by
        convert integral_exp_mul_complex_Ioi ( show ( α n - s |> Complex.re ) < 0 from by norm_num; linarith [ hα_bdd_re n ] ) 0 using 1 ; norm_num;
      have h_pull :
          ∫ t in Set.Ioi (0 : ℝ), c n * Complex.exp ((α n - s) * (t : ℂ)) =
            c n * ∫ t in Set.Ioi (0 : ℝ), Complex.exp ((α n - s) * (t : ℂ)) :=
        MeasureTheory.integral_const_mul (c n) _
      rw [h_pull, h_integral]
      -- Show c n * (-1 / (α n - s)) = c n / (s - α n).
      rw [show ((-1 : ℂ) / (α n - s)) = 1 / (s - α n) by
        rw [show (α n - s) = -(s - α n) from by ring]
        rw [div_neg]; ring]
      rw [mul_one_div]
    · exact fun n => Continuous.aestronglyMeasurable ( by continuity );
    · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun n => _ ) _ );
      use fun n => ENNReal.ofReal ( ‖c n‖ * ∫ t in Set.Ioi ( 0 : ℝ ), Real.exp ( ( α n |> Complex.re ) * t - s.re * t ) );
      · rw [ ← MeasureTheory.integral_const_mul ];
        rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · refine' MeasureTheory.lintegral_mono fun x => _;
          rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num [ Complex.norm_exp ];
          · exact le_of_eq ( by ring );
          · exact?;
          · positivity;
        · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp ((α n).re * t - s.re * t)) (Set.Ioi 0) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(s.re - (α n).re) * t)) (Set.Ioi 0) := by
              have := ( exp_neg_integrableOn_Ioi 0 ( by linarith [ hα_bdd_re n ] : 0 < s.re - ( α n |> Complex.re ) ) );
              exact this;
            exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
          exact h_integrable.const_mul _;
        · exact Filter.Eventually.of_forall fun x => by positivity;
      · -- Evaluate the integral $\int_{0}^{\infty} e^{(\alpha_n - s)t} \, dt$.
        have h_integral : ∀ n, ∫ t in Set.Ioi (0 : ℝ), Real.exp ((α n).re * t - s.re * t) = 1 / (s.re - (α n).re) := by
          intro n; have := integral_exp_neg_mul_rpow zero_lt_one ( show 0 < s.re - ( α n |> Complex.re ) by linarith [ hα_bdd_re n ] ) ; norm_num [ Real.rpow_neg_one ] at this ⊢; simp_all +decide [ sub_mul ] ;
        rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ h_integral ];
        · exact fun n => mul_nonneg ( norm_nonneg _ ) ( inv_nonneg.2 ( by linarith [ hα_bdd_re n ] ) );
        · exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( norm_nonneg _ ) ( inv_nonneg.2 ( by linarith [ hα_bdd_re n ] ) ) ) ( fun n => mul_le_mul_of_nonneg_left ( inv_le_one_of_one_le₀ ( by linarith [ hα_bdd_re n ] ) ) ( norm_nonneg _ ) ) ( hc_summable.mul_right _ );
  simp_all +decide [ sub_mul, Complex.exp_sub ];
  simp_all +decide [ ← mul_div_assoc, tsum_div_const ];
  exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => by rw [ hsum_zero t |> HasSum.tsum_eq, zero_div ] ;

/-
The resolvent G(s) = ∑ c_n / (s - α_n) is analytic on (range α)ᶜ.
    Each term is differentiable with derivative -c_n/(s-α_n)², and the derivative series
    converges locally uniformly by the Weierstrass M-test.
-/
lemma resolvent_analyticOnNhd
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hc_summable : Summable (fun n => ‖c n‖))
    (hα_loc_finite : ∀ R : ℝ, Set.Finite {n : ℕ | ‖α n‖ ≤ R}) :
    AnalyticOnNhd ℂ (fun s => ∑' n, c n / (s - α n)) (Set.range α)ᶜ := by
  apply_rules [ DifferentiableOn.analyticOnNhd, resolvent_summable ];
  · intro s hs;
    -- Since $s \notin \text{range}(\alpha)$, there exists an $\epsilon > 0$ such that for all $n$, $\|s - \alpha_n\| \geq \epsilon$.
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ n, ε ≤ ‖s - α n‖ := by
      -- Since the range of α is closed, there exists an ε > 0 such that the ball of radius ε around s does not intersect the range of α.
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ x ∈ Set.range α, ε ≤ ‖s - x‖ := by
        have := Metric.mem_nhds_iff.mp ( IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| range_isClosed_of_loc_finite α hα_loc_finite ) hs );
        exact ⟨ this.choose, this.choose_spec.1, fun x hx => le_of_not_gt fun h => this.choose_spec.2 ( mem_ball_iff_norm.mpr <| by simpa [ norm_sub_rev ] using h ) hx ⟩;
      exact ⟨ ε, hε_pos, fun n => hε _ <| Set.mem_range_self _ ⟩;
    refine' DifferentiableAt.differentiableWithinAt _;
    refine' ( HasDerivAt.differentiableAt _ );
    exact ∑' n, -c n / ( s - α n ) ^ 2;
    rw [ hasDerivAt_iff_tendsto_slope_zero ];
    -- By the properties of the series, we can interchange the limit and the summation.
    have h_interchange : Filter.Tendsto (fun t => ∑' n, (c n / (s + t - α n) - c n / (s - α n)) / t) (nhdsWithin 0 {0}ᶜ) (nhds (∑' n, -c n / (s - α n) ^ 2)) := by
      refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
      use fun n => ‖c n‖ * ( 2 / ε ^ 2 );
      · exact hc_summable.mul_right _;
      · intro n;
        have h_deriv : HasDerivAt (fun x => c n / (s + x - α n)) (-c n / (s - α n) ^ 2) 0 := by
          convert HasDerivAt.div ( hasDerivAt_const _ _ ) ( HasDerivAt.sub ( hasDerivAt_id 0 |> HasDerivAt.const_add s ) ( hasDerivAt_const _ _ ) ) _ using 1 <;> norm_num;
          exact sub_ne_zero_of_ne <| by rintro rfl; exact hs <| Set.mem_range_self _;
        simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero;
      · rw [ eventually_nhdsWithin_iff ];
        rw [ Metric.eventually_nhds_iff ];
        refine' ⟨ ε / 2, half_pos hε_pos, fun y hy hy' k => _ ⟩ ; rw [ div_sub_div ] <;> norm_num;
        · rw [ div_div, div_le_iff₀ ];
          · rw [ show c k * ( s - α k ) - ( s + y - α k ) * c k = -c k * y by ring ] ; norm_num ; ring_nf;
            -- By simplifying, we can see that this inequality holds.
            have h_simplify : ‖s + (y - α k)‖ * ‖s - α k‖ ≥ ε ^ 2 / 2 := by
              have h_simplify : ‖s + (y - α k)‖ ≥ ε / 2 := by
                have := norm_sub_le ( s + ( y - α k ) ) y ; simp_all +decide [ dist_eq_norm ];
                grind;
              nlinarith [ hε k ];
            have h_assoc : ‖s + (y - α k)‖ = ‖s + y - α k‖ := by
              congr 1; ring
            rw [h_assoc] at h_simplify
            field_simp;
            nlinarith [show 0 ≤ ‖c k‖ * ‖y‖ by positivity, h_simplify,
              show 0 ≤ ‖s + y - α k‖ from norm_nonneg _,
              show 0 ≤ ‖s - α k‖ from norm_nonneg _];
          · simp +zetaDelta at *;
            exact mul_pos ( mul_pos ( norm_pos_iff.mpr ( show s + y - α k ≠ 0 from sub_ne_zero.mpr <| by intro h; have := hε k; rw [ show s = α k - y by linear_combination' h ] at this; norm_num at this; linarith [ norm_sub_norm_le ( α k ) y ] ) ) ( norm_pos_iff.mpr ( show s - α k ≠ 0 from sub_ne_zero.mpr <| Ne.symm <| hs k ) ) ) ( norm_pos_iff.mpr hy' );
        · contrapose! hε;
          exact ⟨ k, by rw [ show s - α k = -y by linear_combination' hε ] ; simpa using hy.trans_le ( by linarith ) ⟩;
        · exact sub_ne_zero_of_ne <| by rintro rfl; exact hs <| Set.mem_range_self _;
    refine' h_interchange.congr' _;
    rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
    rw [ Metric.eventually_nhds_iff ];
    refine' ⟨ ε / 2, half_pos hε_pos, fun y hy hy' => _ ⟩;
    rw [ ← Summable.tsum_sub ];
    · simp +decide [ div_eq_inv_mul, tsum_mul_left ];
    · have h_summable : Summable (fun n => ‖c n‖ / ‖s + y - α n‖) := by
        have h_summable : ∀ n, ‖s + y - α n‖ ≥ ε / 2 := by
          intro n; specialize hε n; have := norm_sub_le ( s + y - α n ) y; simp_all +decide [ dist_eq_norm ] ;
          grind +revert;
        exact Summable.of_nonneg_of_le ( fun n => div_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ( fun n => div_le_div_of_nonneg_left ( norm_nonneg _ ) ( by positivity ) ( h_summable n ) ) ( hc_summable.mul_right _ );
      exact .of_norm <| by simpa using h_summable;
    · have := resolvent_summable α c hc_summable hα_loc_finite s hs;
      convert this using 1;
  · exact isOpen_compl_iff.mpr ( range_isClosed_of_loc_finite α hα_loc_finite )

/-
If the resolvent is identically zero on (range α)ᶜ, all coefficients are zero.
    For each n₀, from G(s) = 0 we get c_{n₀} = -∑_{n≠n₀} c_n(s-α_{n₀})/(s-α_n)
    for all s ∉ range α. The RHS has absolute value ≤ |s-α_{n₀}| · C → 0
    as s → α_{n₀}, so c_{n₀} = 0.
-/
lemma coeff_from_resolvent_eq_zero
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hα_inj : Function.Injective α)
    (hα_loc_finite : ∀ R : ℝ, Set.Finite {n : ℕ | ‖α n‖ ≤ R})
    (hc_summable : Summable (fun n => ‖c n‖))
    (hG_zero : ∀ s, s ∉ Set.range α → ∑' n, c n / (s - α n) = 0) :
    ∀ n, c n = 0 := by
  intro n;
  -- Fix n₀. We have G(s) = ∑' c_n/(s-α_n) = 0 for all s ∉ range α.
  -- Key identity: c_{n₀} = (s - α_{n₀}) · G(s) - ∑_{n ≠ n₀} c_n (s - α_{n₀})/(s - α_n). Since G(s) = 0:
  -- c_{n₀} = -∑_{n ≠ n₀} c_n (s - α_{n₀})/(s - α_n).
  have h_key_identity : ∀ s ∉ Set.range α, c n = - ∑' m, if m = n then 0 else c m * (s - α n) / (s - α m) := by
    intro s hs
    have h_key : c n = (s - α n) * ∑' m, c m / (s - α m) - ∑' m, if m = n then 0 else c m * (s - α n) / (s - α m) := by
      have h_key : c n = (s - α n) * (∑' m, c m / (s - α m)) - (∑' m, c m * (s - α n) / (s - α m) - c n * (s - α n) / (s - α n)) := by
        simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, tsum_mul_right, sub_ne_zero.mpr ( show s ≠ α n from fun h => hs <| h ▸ Set.mem_range_self _ ) ];
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left ];
      convert h_key using 2;
      rw [ eq_comm, Summable.tsum_eq_add_tsum_ite ];
      ring;
      have h_summable : Summable (fun m => c m / (s - α m)) := by
        convert resolvent_summable α c hc_summable hα_loc_finite s hs using 1;
      convert h_summable.mul_left ( s - α n ) using 2 ; ring;
    aesop;
  -- Choose s = α n + ε where ε is small enough so that s ∉ range α.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ m ≠ n, ε ≤ ‖α m - α n‖ := by
    have h_finite : Set.Finite {m | m ≠ n ∧ ‖α m - α n‖ ≤ 1} := by
      have := hα_loc_finite ( ‖α n‖ + 1 );
      refine' this.subset fun m hm => _;
      simpa using norm_add_le ( α n ) ( α m - α n ) |> le_trans <| by linarith [ hm.2 ] ;
    by_cases h_empty : {m | m ≠ n ∧ ‖α m - α n‖ ≤ 1} = ∅;
    · exact ⟨ 1, zero_lt_one, fun m hm => le_of_not_gt fun h => h_empty.subset ⟨ hm, h.le ⟩ ⟩;
    · obtain ⟨m₀, hm₀⟩ : ∃ m₀ ∈ {m | m ≠ n ∧ ‖α m - α n‖ ≤ 1}, ∀ m ∈ {m | m ≠ n ∧ ‖α m - α n‖ ≤ 1}, ‖α m₀ - α n‖ ≤ ‖α m - α n‖ := by
        apply_rules [ Set.exists_min_image ];
        exact Set.nonempty_iff_ne_empty.mpr h_empty;
      use ‖α m₀ - α n‖;
      simp_all +decide [ sub_eq_iff_eq_add, hα_inj.eq_iff ];
      exact fun m hm => if hm' : ‖α m - α n‖ ≤ 1 then hm₀.2 m hm hm' else by linarith [ norm_nonneg ( α m₀ - α n ), norm_nonneg ( α m - α n ) ] ;
  -- Choose s = α n + ε/2.
  have h_choose_s : ∀ δ : ℝ, 0 < δ ∧ δ < ε → c n = - ∑' m, if m = n then 0 else c m * (δ : ℂ) / (δ - (α m - α n)) := by
    intros δ hδ
    specialize h_key_identity (α n + δ) (by
    rintro ⟨ m, hm ⟩;
    specialize hε m ; simp_all +decide [ sub_eq_iff_eq_add ];
    exact absurd ( hε ( by rintro rfl; norm_num at hm; norm_cast at hm; linarith ) ) ( by rw [ abs_of_pos ] <;> linarith ));
    convert h_key_identity using 4 ; ring;
  -- Let δ approach 0.
  have h_delta_zero : Filter.Tendsto (fun δ : ℝ => ∑' m, if m = n then 0 else c m * (δ : ℂ) / (δ - (α m - α n))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    -- The series $\sum_{m \neq n} \frac{c_m \delta}{\delta - (\alpha_m - \alpha_n)}$ converges uniformly to $0$ as $\delta \to 0$.
    have h_uniform_converge : ∀ δ : ℝ, 0 < δ ∧ δ < ε → ∀ m ≠ n, ‖c m * (δ : ℂ) / (δ - (α m - α n))‖ ≤ ‖c m‖ * (δ / (ε - δ)) := by
      intros δ hδ m hm_ne_n
      have h_norm : ‖δ - (α m - α n)‖ ≥ ε - δ := by
        have := norm_sub_le ( δ - ( α m - α n ) ) ( δ : ℂ ) ; simp_all +decide [ abs_of_pos ];
        exact le_trans ( hε m hm_ne_n ) ( by simpa [ norm_sub_rev ] using this );
      simp_all +decide [ mul_div_assoc ];
      exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_pos hδ.1 ] ; exact div_le_div_of_nonneg_left ( by linarith ) ( by linarith ) ( by linarith ) ) ( norm_nonneg _ );
    -- The series $\sum_{m \neq n} \frac{c_m \delta}{\delta - (\alpha_m - \alpha_n)}$ is dominated by $\sum_{m \neq n} \|c_m\| \frac{\delta}{\epsilon - \delta}$.
    have h_dominate : ∀ δ : ℝ, 0 < δ ∧ δ < ε → ‖∑' m, if m = n then 0 else c m * (δ : ℂ) / (δ - (α m - α n))‖ ≤ ∑' m, ‖c m‖ * (δ / (ε - δ)) := by
      intros δ hδ
      have h_dominate : ∀ m, ‖if m = n then 0 else c m * (δ : ℂ) / (δ - (α m - α n))‖ ≤ ‖c m‖ * (δ / (ε - δ)) := by
        intro m; split_ifs <;> simp_all +decide [ abs_of_pos ] ;
      refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
      · exact Summable.of_nonneg_of_le ( fun m => norm_nonneg _ ) h_dominate ( hc_summable.mul_right _ );
      · exact Summable.tsum_le_tsum h_dominate ( by exact Summable.of_nonneg_of_le ( fun m => norm_nonneg _ ) ( fun m => h_dominate m ) ( hc_summable.mul_right _ ) ) ( by exact Summable.mul_right _ hc_summable );
    -- The series $\sum_{m \neq n} \|c_m\| \frac{\delta}{\epsilon - \delta}$ converges to $0$ as $\delta \to 0$.
    have h_series_zero : Filter.Tendsto (fun δ : ℝ => ∑' m, ‖c m‖ * (δ / (ε - δ))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simp_all +decide [ tsum_mul_right ];
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using tendsto_const_nhds.mul ( ContinuousAt.tendsto ( show ContinuousAt ( fun δ : ℝ => δ / ( ε - δ ) ) 0 by exact ContinuousAt.div continuousAt_id ( continuousAt_const.sub continuousAt_id ) ( by linarith ) ) ) );
    exact squeeze_zero_norm' ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hε_pos ⟩ ) fun δ hδ => h_dominate δ hδ ) h_series_zero;
  have := h_delta_zero.neg;
  simpa using tendsto_nhds_unique ( tendsto_const_nhds.congr' ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hε_pos ⟩ ) fun x hx => h_choose_s x hx ▸ rfl ) ) this

/-- Coefficient extraction: if ∑ c_n exp(α_n z) = 0 for all z, α injective
    with locally finite norms, bounded real parts, then c_n = 0 for all n.

    Proof via the resolvent: G(s) = ∑ c_n/(s - α_n) is shown to be zero
    on Re(s) > σ₀ + 1 via Laplace transform, analytic on (range α)ᶜ,
    and then G ≡ 0 by the identity theorem (using connectedness of ℂ \ countable).
    Finally each c_n = 0 by the residue/limit argument. -/
lemma coeff_extraction_of_exp_sum_zero
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hα_inj : Function.Injective α)
    (hα_bdd_re : ∃ σ₀ : ℝ, ∀ n, (α n).re ≤ σ₀)
    (hα_loc_finite : ∀ R : ℝ, Set.Finite {n : ℕ | ‖α n‖ ≤ R})
    (hc_exp_summable : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (hsum_zero : ∀ z : ℂ, HasSum (fun n => c n * Complex.exp (α n * z)) 0) :
    ∀ n, c n = 0 := by
  -- Derive absolute summability of c
  have hc_summable : Summable (fun n => ‖c n‖) :=
    summable_norm_of_exp_summable c α hc_exp_summable
  -- Obtain σ₀ bound
  obtain ⟨σ₀, hα_bdd_re⟩ := hα_bdd_re
  -- The resolvent G is analytic on (range α)ᶜ
  have hG_analytic := resolvent_analyticOnNhd α c hc_summable hα_loc_finite
  -- G = 0 on the half-plane Re(s) > σ₀ + 1
  have hG_halfplane := resolvent_eq_zero_halfplane α c σ₀ hα_bdd_re hc_summable hc_exp_summable hsum_zero
  -- (range α)ᶜ is preconnected (complement of countable set in dim > 1)
  have hU_conn : IsPreconnected (Set.range α : Set ℂ)ᶜ :=
    (Set.countable_range α |>.isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
  -- The half-plane {Re(s) > σ₀ + 1} is contained in (range α)ᶜ
  have hHP_sub : ∀ s : ℂ, σ₀ + 1 < s.re → s ∉ Set.range α := by
    intro s hs ⟨n, hn⟩; linarith [hα_bdd_re n, hn ▸ hs]
  -- Pick z₀ in the half-plane ∩ (range α)ᶜ
  have hz₀ : (⟨σ₀ + 2, 0⟩ : ℂ) ∈ (Set.range α)ᶜ := hHP_sub _ (by norm_num)
  -- G = 0 in a neighborhood of z₀ (the ball within the half-plane)
  have hG_local : (fun s => ∑' n, c n / (s - α n)) =ᶠ[nhds ⟨σ₀ + 2, 0⟩] 0 := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨{s | σ₀ + 1 < s.re}, ?_, ?_⟩
    · exact IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) (by norm_num)
    · intro s hs; exact hG_halfplane s hs
  -- By the identity theorem: G = 0 on all of (range α)ᶜ
  have hG_zero : ∀ s, s ∉ Set.range α → ∑' n, c n / (s - α n) = 0 := by
    intro s hs
    have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hG_analytic (analyticOnNhd_const) hU_conn hz₀ hG_local
    exact this hs
  -- Extract coefficients
  exact coeff_from_resolvent_eq_zero α c hα_inj hα_loc_finite hc_summable hG_zero

/-- The countable tsum moment uniqueness principle. -/
theorem countable_tsum_moment_uniqueness_principle
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hα_inj : Function.Injective α)
    (hα_bdd_re : ∃ σ₀ : ℝ, ∀ n, (α n).re ≤ σ₀)
    (hα_loc_finite : ∀ R : ℝ, Set.Finite {n : ℕ | ‖α n‖ ≤ R})
    (hc_exp_summable : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (hmoments : ∀ k : ℕ, HasSum (fun n => c n * α n ^ k) 0) :
    ∀ n, c n = 0 := by
  exact coeff_extraction_of_exp_sum_zero α c hα_inj hα_bdd_re hα_loc_finite hc_exp_summable
    (tsum_cexp_eq_zero α c hc_exp_summable hmoments)

end