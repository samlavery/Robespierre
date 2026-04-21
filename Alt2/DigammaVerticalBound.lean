import Mathlib

open Complex Filter Topology Asymptotics Finset

set_option maxHeartbeats 800000

noncomputable section

/-!
# Logarithmic bound on the digamma function along vertical lines

We prove that for fixed σ > 0, the digamma function ψ(s) = Γ'(s)/Γ(s)
satisfies |ψ(σ + it)| ≤ C · log(1 + |t|) for |t| ≥ 1.

## Strategy

We use the series representation:
  ψ(s) = -γ + Σ_{k≥0} (1/(k+1) - 1/(s+k))   for Re(s) > 0

and bound the series by splitting at k ≈ |t|.
-/

/-! ## Part 1: Summability of the digamma series -/

lemma ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) (k : ℕ) : s + (k : ℂ) ≠ 0 := by
  intro h
  have : (s + k).re = 0 := by rw [h]; simp
  simp [add_re] at this
  linarith

lemma digamma_series_term_eq (s : ℂ) (hs : 0 < s.re) (k : ℕ) :
    1 / ((k : ℂ) + 1) - 1 / (s + (k : ℂ)) =
      (s - 1) / (((k : ℂ) + 1) * (s + (k : ℂ))) := by
  have hk1 : (k : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hsk : s + (k : ℂ) ≠ 0 := ne_neg_nat_of_re_pos hs k
  field_simp
  ring

lemma digamma_series_summable (s : ℂ) (hs : 0 < s.re) :
    Summable (fun k : ℕ => (1 / ((k : ℂ) + 1) - 1 / (s + (k : ℂ)))) := by
      -- The series_summable_of_norm_bounded theorem can be used to show summability.
      have hsum_bound : ∃ C : ℝ, ∀ k : ℕ, k ≥ 1 → ‖(1 / ((k : ℂ) + 1) - 1 / (s + (k : ℂ)))‖ ≤ C / (k : ℝ)^2 := by
        use 2 * (‖s - 1‖ + ‖s‖^2);
        intro k hk
        have h_term_bound : ‖(s - 1) / (((k : ℂ) + 1) * (s + (k : ℂ)))‖ ≤ (‖s - 1‖ + ‖s‖^2) / ((k : ℝ) * (k : ℝ)) := by
          have h_term_bound : ‖(s - 1) / (((k : ℂ) + 1) * (s + (k : ℂ)))‖ ≤ ‖s - 1‖ / ((k : ℝ) * (k : ℝ)) := by
            norm_num [ Complex.normSq, Complex.norm_def ] at *;
            gcongr;
            · exact Real.le_sqrt_of_sq_le ( by nlinarith );
            · exact Real.le_sqrt_of_sq_le ( by nlinarith );
          exact h_term_bound.trans ( by gcongr ; nlinarith );
        convert h_term_bound.trans _ using 1;
        · rw [ div_sub_div ] <;> ring <;> norm_num [ show s + k ≠ 0 from ne_neg_nat_of_re_pos hs k ];
          norm_cast ; linarith;
        · rw [ div_le_div_iff₀ ] <;> first | positivity | nlinarith [ norm_nonneg ( s - 1 ), norm_nonneg s ] ;
      rw [ ← summable_nat_add_iff 1 ];
      exact .of_norm <| Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => hsum_bound.choose_spec _ le_add_self ) <| Summable.mul_left _ <| Real.summable_nat_pow_inv.2 one_lt_two |> Summable.comp_injective <| Nat.succ_injective

/-! ## Part 2: The digamma series representation -/

/-- The digamma series: -γ + Σ_{k≥0} (1/(k+1) - 1/(s+k)) -/
def digammaSeriesSum (s : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) +
    ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (s + (k : ℂ)))

/-
The digamma series satisfies the same recurrence as ψ:
  h(s+1) = h(s) + 1/s
-/
lemma digammaSeriesSum_add_one (s : ℂ) (hs : 0 < s.re) :
    digammaSeriesSum (s + 1) = digammaSeriesSum s + 1 / s := by
      unfold digammaSeriesSum;
      -- Use the telescoping property to simplify the difference of the two series.
      have h_telescope : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (1 / (s + k : ℂ) - 1 / (s + 1 + k : ℂ))) Filter.atTop (nhds (1 / s)) := by
        -- The series $\sum_{k=0}^{N-1} \left(\frac{1}{s+k} - \frac{1}{s+1+k}\right)$ is a telescoping series.
        have h_telescope : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 / (s + k : ℂ) - 1 / (s + 1 + k : ℂ)) = 1 / s - 1 / (s + N : ℂ) := by
          exact fun N => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
        -- Since $|s + N| \to \infty$ as $N \to \infty$, we have $1 / (s + N) \to 0$.
        have h_inv : Filter.Tendsto (fun N : ℕ => 1 / (s + N : ℂ)) Filter.atTop (nhds 0) := by
          rw [ tendsto_zero_iff_norm_tendsto_zero ];
          norm_num [ Complex.norm_def, Complex.normSq ];
          exact tendsto_inv_atTop_zero.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil <| x ^ 2 + 1 - s.re, fun n hn => Real.le_sqrt_of_sq_le <| by nlinarith [ Nat.ceil_le.mp hn ] ⟩;
        simpa only [ h_telescope, sub_zero ] using tendsto_const_nhds.sub h_inv;
      -- By definition of summability, we can split the sum into two parts.
      have h_split : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (1 / (k + 1 : ℂ) - 1 / (s + 1 + k : ℂ))) Filter.atTop (nhds (∑' k : ℕ, (1 / (k + 1 : ℂ) - 1 / (s + 1 + k : ℂ)))) ∧ Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (1 / (k + 1 : ℂ) - 1 / (s + k : ℂ))) Filter.atTop (nhds (∑' k : ℕ, (1 / (k + 1 : ℂ) - 1 / (s + k : ℂ)))) := by
        constructor <;> refine' ( Summable.hasSum _ ) |> HasSum.tendsto_sum_nat;
        · have := digamma_series_summable ( s + 1 ) ( by norm_num; linarith );
          convert this using 1;
        · exact?;
      have := h_telescope.sub ( h_split.1.sub h_split.2 ) ; simp_all +decide [ Finset.sum_add_distrib, add_assoc ] ;
      linear_combination this

/-- ψ(1) = h(1) = -γ. -/
lemma digamma_eq_series_at_one :
    Complex.digamma 1 = digammaSeriesSum 1 := by
  rw [Complex.digamma_one]
  unfold digammaSeriesSum
  have : (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((1 : ℂ) + (k : ℂ))) = fun _ => 0 := by
    ext k; ring
  rw [this, tsum_zero, add_zero]

/-- For positive real x, digamma(x) is well-defined: ∀ m, (x : ℂ) ≠ -(m : ℂ) -/
lemma real_pos_ne_neg_nat {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x : ℂ) ≠ -(m : ℂ) := by
  intro h
  have : (x : ℂ).re = (-(m : ℂ)).re := by rw [h]
  simp at this
  linarith

/-
ψ'(s+1) = ψ'(s) - 1/s² for s ∉ {0,-1,-2,...} and s+1 ∉ {0,-1,...}.
-/
lemma deriv_digamma_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ -↑m)
    (hs1 : ∀ m : ℕ, s + 1 ≠ -↑m) :
    deriv Complex.digamma (s + 1) = deriv Complex.digamma s - 1 / s ^ 2 := by
      have h_deriv_eq : deriv (fun z => Complex.digamma (z + 1)) s = deriv (fun z => Complex.digamma z + 1 / z) s := by
        refine' Filter.EventuallyEq.deriv_eq _;
        rw [ Filter.EventuallyEq, eventually_nhds_iff ];
        refine' ⟨ { z : ℂ | z ≠ 0 ∧ ∀ m : ℕ, z ≠ -m }, _, isOpen_ne.inter <| isOpen_iff_mem_nhds.mpr _, _ ⟩;
        · intro y hy; have := Complex.digamma_apply_add_one y; aesop;
        · intro z hz;
          rw [ Metric.mem_nhds_iff ];
          have h_closed : IsClosed {w : ℂ | ∃ m : ℕ, w = -m} := by
            refine' isClosed_of_closure_subset _;
            intro w hw;
            rw [ mem_closure_iff_seq_limit ] at hw;
            obtain ⟨ x, hx₁, hx₂ ⟩ := hw;
            choose m hm using hx₁;
            -- Since $m_n$ is a sequence of natural numbers, it must be bounded.
            have h_bounded : ∃ M : ℕ, ∀ n, m n ≤ M := by
              have := hx₂.norm;
              simp_all +decide [ Complex.norm_def, Complex.normSq ];
              have := this.bddAbove_range;
              exact ⟨ ⌊this.choose⌋₊, fun n => Nat.le_floor <| this.choose_spec <| Set.mem_range_self n ⟩;
            have h_finite : Set.Finite (Set.range m) := by
              exact Set.finite_iff_bddAbove.mpr ⟨ h_bounded.choose, Set.forall_mem_range.mpr h_bounded.choose_spec ⟩;
            have h_finite : Set.Finite (Set.range (fun n => -↑(m n) : ℕ → ℂ)) := by
              exact Set.Finite.subset ( h_finite.image fun n : ℕ => - ( n : ℂ ) ) fun x hx => by aesop;
            have := h_finite.isClosed.mem_of_tendsto hx₂ ; aesop;
          have := Metric.isOpen_iff.mp ( isOpen_compl_iff.mpr h_closed ) z;
          exact this ( by rintro ⟨ m, rfl ⟩ ; exact hz m rfl ) |> fun ⟨ ε, ε_pos, hε ⟩ => ⟨ ε, ε_pos, fun w hw m hm => hε hw ⟨ m, hm ⟩ ⟩;
        · exact ⟨ by rintro rfl; exact hs 0 <| by norm_num, hs ⟩;
      convert h_deriv_eq using 1;
      · exact?;
      · convert ( HasDerivAt.deriv ( HasDerivAt.add ( hasDerivAt_deriv_iff.mpr _ ) ( HasDerivAt.div ( hasDerivAt_const _ _ ) ( hasDerivAt_id s ) _ ) ) ) |> Eq.symm using 1 <;> norm_num;
        · ring;
        · refine' DifferentiableAt.div _ _ _;
          · have h_diff : DifferentiableAt ℂ (fun z => Complex.Gamma z) s := by
              apply_rules [ Complex.differentiableAt_Gamma ];
            have h_diff : AnalyticAt ℂ (fun z => Complex.Gamma z) s := by
              apply_rules [ DifferentiableOn.analyticAt, h_diff ];
              rotate_right;
              exact { z : ℂ | ¬∃ m : ℕ, z = -m };
              · intro z hz;
                refine' DifferentiableAt.differentiableWithinAt _;
                refine' Complex.differentiableAt_Gamma _ _;
                grind;
              · rw [ Metric.mem_nhds_iff ];
                have h_closed : IsClosed {z : ℂ | ∃ m : ℕ, z = -m} := by
                  refine' isClosed_of_closure_subset _;
                  intro z hz;
                  rw [ mem_closure_iff_seq_limit ] at hz;
                  obtain ⟨ x, hx₁, hx₂ ⟩ := hz;
                  choose m hm using hx₁;
                  have h_bounded : ∃ M : ℕ, ∀ n, m n ≤ M := by
                    have h_bounded : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M := by
                      exact ⟨ _, fun n => le_csSup ( hx₂.norm.bddAbove_range ) ⟨ n, rfl ⟩ ⟩;
                    exact ⟨ ⌊h_bounded.choose⌋₊, fun n => Nat.le_floor <| by simpa [ hm ] using h_bounded.choose_spec n ⟩;
                  have h_finite : Set.Finite (Set.range m) := by
                    exact Set.finite_iff_bddAbove.mpr ⟨ h_bounded.choose, Set.forall_mem_range.mpr h_bounded.choose_spec ⟩;
                  have h_finite : Set.Finite (Set.range (fun n => -↑(m n) : ℕ → ℂ)) := by
                    exact Set.Finite.subset ( h_finite.image fun n : ℕ => - ( n : ℂ ) ) fun x hx => by aesop;
                  have := h_finite.isClosed.mem_of_tendsto hx₂ ; aesop;
                exact Metric.mem_nhds_iff.mp ( h_closed.isOpen_compl.mem_nhds <| by aesop );
            exact h_diff.deriv.differentiableAt;
          · refine' Complex.differentiableAt_Gamma _ _;
            assumption;
          · exact?;
        · exact fun h => hs 0 <| by norm_num [ h ]

/-
Both ψ and h satisfy f(s+1) = f(s) + 1/s, so by induction, they agree at all positive integers.
-/
lemma digamma_eq_series_nat (n : ℕ) (hn : 1 ≤ n) :
    Complex.digamma (n : ℂ) = digammaSeriesSum (n : ℂ) := by
      refine' Nat.le_induction _ _ n hn;
      · simpa using digamma_eq_series_at_one;
      · intro n hn ih;
        -- Using the recurrence relation for the digamma function, we have:
        have h_recurrence : Complex.digamma (n + 1) = Complex.digamma n + 1 / (n : ℂ) := by
          -- Apply the recurrence relation for the digamma function: ψ(z+1) = ψ(z) + 1/z for z not a non-positive integer.
          have h_recurrence : ∀ z : ℂ, (∀ m : ℕ, z ≠ -m) → Complex.digamma (z + 1) = Complex.digamma z + 1 / z := by
            grind +suggestions;
          exact h_recurrence _ fun m => by norm_cast; aesop;
        have := digammaSeriesSum_add_one ( n : ℂ ) ( by simpa using hn ) ; aesop

/-
The real digamma function is increasing on (0,∞).
    This follows from Real.convexOn_log_Gamma (log Γ is convex).
-/
lemma digamma_re_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (Complex.digamma a).re ≤ (Complex.digamma b).re := by
      -- The real part of digamma(x : ℂ) for real x > 0 equals the derivative of log(Real.Gamma x), which is increasing because log Gamma is convex (Real.convexOn_log_Gamma).
      have h_deriv_log_gamma : ∀ x : ℝ, 0 < x → (Complex.digamma x).re = deriv (fun x => Real.log (Real.Gamma x)) x := by
        intro x hx; rw [ deriv.log ] <;> norm_num [ hx.ne', Real.differentiableAt_Gamma ] ;
        · rw [ div_eq_inv_mul, Complex.digamma ];
          rw [ logDeriv ];
          rw [ show deriv Real.Gamma x = ( deriv Gamma x |> Complex.re ) from ?_ ];
          · norm_num [ div_eq_inv_mul ];
            norm_num [ Complex.normSq, Complex.Gamma_ofReal ];
            norm_num [ sq, ne_of_gt ( Real.Gamma_pos_of_pos hx ) ];
          · have h_deriv_real : HasDerivAt (fun x : ℝ => Real.Gamma x) (deriv Gamma x |> Complex.re) x := by
              have h_deriv_complex : HasDerivAt (fun x : ℂ => Gamma x) (deriv Gamma x) x := by
                convert ( hasDerivAt_deriv_iff.mpr _ ) using 1;
                refine' differentiableAt_Gamma _ _;
                exact fun m => by norm_num [ Complex.ext_iff ] ; linarith
              rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
              convert Complex.continuous_re.continuousAt.tendsto.comp ( h_deriv_complex.comp ( show Filter.Tendsto ( fun t : ℝ => ↑t ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhdsWithin 0 { 0 } ᶜ ) from Filter.Tendsto.inf ( Complex.continuous_ofReal.tendsto 0 ) <| by simp +decide ) ) using 2 ; norm_num;
              norm_cast;
              exact Or.inl <| by congr;
            exact h_deriv_real.deriv;
        · exact Real.differentiableAt_Gamma fun m => by linarith;
        · positivity;
      -- Since log ∘ Real.Gamma is convex on Ioi 0 (by Real.convexOn_log_Gamma), its derivative is monotone increasing.
      have h_monotone_deriv : MonotoneOn (fun x => deriv (fun x => Real.log (Real.Gamma x)) x) (Set.Ioi 0) := by
        apply_rules [ ConvexOn.monotoneOn_deriv ];
        · exact ( Real.convexOn_log_Gamma );
        · exact fun x hx => DifferentiableAt.log ( Real.differentiableAt_Gamma fun m => by linarith [ hx.out ] ) ( ne_of_gt ( Real.Gamma_pos_of_pos hx ) );
      exact h_deriv_log_gamma a ha ▸ h_deriv_log_gamma b ( lt_of_lt_of_le ha hab ) ▸ h_monotone_deriv ha ( lt_of_lt_of_le ha hab ) hab

/-
For positive real x, digamma(x) is real-valued.
-/
lemma digamma_ofReal_im (x : ℝ) (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).im = 0 := by
      -- Since $x$ is positive, $\Gamma(x)$ is real and positive, and its derivative $\Gamma'(x)$ is also real. Therefore, the digamma function $\psi(x) = \frac{\Gamma'(x)}{\Gamma(x)}$ is real.
      have h_gamma_real : (Complex.Gamma (x : ℂ)).im = 0 ∧ (deriv Complex.Gamma (x : ℂ)).im = 0 := by
        have h_real : (Complex.Gamma x).im = 0 := by
          rw [ Complex.Gamma_ofReal ] ; norm_num;
        have h_deriv_real : HasDerivAt (fun x : ℝ => Complex.Gamma x) (deriv Complex.Gamma x) x := by
          have h_deriv_real : DifferentiableAt ℂ (Complex.Gamma) x := by
            refine' Complex.differentiableAt_Gamma _ _;
            exact fun m => by norm_num [ Complex.ext_iff ] ; linarith;
          convert h_deriv_real.hasDerivAt.comp_ofReal using 1;
        have h_deriv_real : HasDerivAt (fun x : ℝ => (Complex.Gamma x).im) (deriv Complex.Gamma x).im x :=
          Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h_deriv_real
        have h_deriv_real_zero : ∀ x : ℝ, x > 0 → (Complex.Gamma x).im = 0 := by
          intro x hx; have := Complex.Gamma_ofReal x; aesop;
        exact ⟨ h_real, by simpa using h_deriv_real.deriv.symm.trans ( HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) ( Filter.eventuallyEq_of_mem ( Ioi_mem_nhds hx ) fun y hy => h_deriv_real_zero y hy ) ) ) ⟩;
      unfold Complex.digamma;
      unfold logDeriv;
      simp_all +decide [ div_eq_mul_inv ]

/-
ψ(x) - h(x) is 1-periodic and equals 0 at all positive integers,
    hence equals 0 for all real x > 0.

    The proof uses:
    1. Φ(x+1) = Φ(x) (1-periodicity from both recurrences)
    2. Φ(n) = 0 at positive integers (from digamma_eq_series_nat)
    3. |ψ(x+N) - ψ(⌊x+N⌋)| ≤ 1/⌊x+N⌋ → 0 (from monotonicity: digamma_re_mono)
    4. |h(x+N) - h(⌊x+N⌋)| → 0 (from series tail bound)
    5. Therefore Φ(x) = Φ(x+N) = [ψ(x+N) - ψ(⌊x+N⌋)] - [h(x+N) - h(⌊x+N⌋)] → 0
-/
lemma digamma_eq_series_real (x : ℝ) (hx : 0 < x) :
    Complex.digamma (x : ℂ) = digammaSeriesSum (x : ℂ) := by
      -- Both $\psi(x)$ and $h(x)$ are increasing functions on $(0, \infty)$.
      have h_inc : ∀ x y : ℝ, 0 < x → x ≤ y → Complex.re (Complex.digamma x) ≤ Complex.re (Complex.digamma y) ∧ Complex.re (digammaSeriesSum x) ≤ Complex.re (digammaSeriesSum y) := by
        -- The digamma function is increasing on $(0, \infty)$.
        have h_digamma_inc : ∀ x y : ℝ, 0 < x → x ≤ y → Complex.re (Complex.digamma x) ≤ Complex.re (Complex.digamma y) := by
          -- The digamma function is increasing on $(0, \infty)$ by definition.
          intros x y hx hy
          apply digamma_re_mono hx hy;
        -- The series representation of the digamma function is also increasing on $(0, \infty)$.
        have h_series_inc : ∀ x y : ℝ, 0 < x → x ≤ y → Complex.re (digammaSeriesSum x) ≤ Complex.re (digammaSeriesSum y) := by
          intros x y hx hy
          have h_series_inc : ∀ k : ℕ, Complex.re (1 / ((k : ℂ) + 1) - 1 / (x + (k : ℂ))) ≤ Complex.re (1 / ((k : ℂ) + 1) - 1 / (y + (k : ℂ))) := by
            norm_num [ Complex.normSq, Complex.div_re ];
            exact fun k => by linarith [ inv_anti₀ ( by linarith ) ( by linarith : x + k ≤ y + k ) ] ;
          refine' add_le_add _ _;
          · norm_num;
          · rw [ Complex.re_tsum, Complex.re_tsum ];
            · apply_rules [ Summable.tsum_le_tsum ];
              · have := digamma_series_summable x hx;
                convert Complex.reCLM.summable this using 1;
              · have h_series_summable : Summable (fun k : ℕ => (1 / ((k : ℂ) + 1) - 1 / (y + (k : ℂ)))) := by
                  convert digamma_series_summable ( y : ℂ ) ( by norm_cast; linarith ) using 1;
                convert Complex.reCLM.summable h_series_summable using 1;
            · convert digamma_series_summable ( y : ℂ ) ( by norm_cast; linarith ) using 1;
            · convert digamma_series_summable ( x : ℂ ) ( by simpa ) using 1
        exact fun x y hx hy => ⟨h_digamma_inc x y hx hy, h_series_inc x y hx hy⟩;
      -- By the properties of the digamma function and the series, we have:
      have h_diff : ∀ N : ℕ, 0 < N → Complex.re (Complex.digamma x) - Complex.re (digammaSeriesSum x) = Complex.re (Complex.digamma (x + N)) - Complex.re (digammaSeriesSum (x + N)) := by
        intros N hN_pos
        have h_recurrence : ∀ n : ℕ, Complex.digamma (x + n) = Complex.digamma x + ∑ k ∈ Finset.range n, (1 / (x + k : ℂ)) ∧ digammaSeriesSum (x + n) = digammaSeriesSum x + ∑ k ∈ Finset.range n, (1 / (x + k : ℂ)) := by
          intro n
          induction' n with n ih;
          · norm_num;
          · have h_recurrence : Complex.digamma (x + n + 1) = Complex.digamma (x + n) + 1 / (x + n : ℂ) ∧ digammaSeriesSum (x + n + 1) = digammaSeriesSum (x + n) + 1 / (x + n : ℂ) := by
              apply And.intro;
              · rw [ Complex.digamma_apply_add_one ];
                · ring;
                · exact fun m => by norm_num [ Complex.ext_iff ] ; linarith;
              · convert digammaSeriesSum_add_one ( x + n ) ( by norm_cast; linarith ) using 1;
            simp_all +decide [ add_assoc, Finset.sum_range_succ ];
        aesop;
      -- Let $m = \lfloor x + N \rfloor$. Then $m \leq x + N < m + 1$.
      have h_floor : ∀ N : ℕ, 0 < N → Complex.re (Complex.digamma (x + N)) - Complex.re (digammaSeriesSum (x + N)) ≤ Complex.re (Complex.digamma (Nat.floor (x + N) + 1)) - Complex.re (digammaSeriesSum (Nat.floor (x + N))) := by
        intros N hN_pos
        set m := Nat.floor (x + N)
        have hm : (m : ℝ) ≤ x + N ∧ x + N < (m + 1 : ℝ) := by
          exact ⟨ Nat.floor_le <| by positivity, Nat.lt_floor_add_one _ ⟩;
        have := h_inc m ( x + N ) ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] ) hm.1; ( have := h_inc ( x + N ) ( m + 1 ) ( by linarith ) hm.2.le; ( norm_num at * ; linarith; ) );
      -- Since $\psi(m) = h(m)$ for all positive integers $m$, we have:
      have h_eq : ∀ m : ℕ, 0 < m → Complex.re (Complex.digamma m) = Complex.re (digammaSeriesSum m) := by
        intro m hm; have := digamma_eq_series_nat m hm; aesop;
      -- Therefore, $\psi(x) - h(x) \leq \frac{1}{m}$.
      have h_bound : ∀ N : ℕ, 0 < N → Complex.re (Complex.digamma x) - Complex.re (digammaSeriesSum x) ≤ 1 / (Nat.floor (x + N) : ℝ) := by
        intros N hN_pos
        have h_bound_step : Complex.re (Complex.digamma (Nat.floor (x + N) + 1)) - Complex.re (digammaSeriesSum (Nat.floor (x + N))) ≤ 1 / (Nat.floor (x + N) : ℝ) := by
          have := h_eq ( ⌊x + N⌋₊ + 1 ) ( Nat.succ_pos _ ) ; simp_all +decide [ digammaSeriesSum_add_one ] ;
          have := digammaSeriesSum_add_one ( ⌊x + N⌋₊ : ℂ ) ; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
          rw [ this ( Nat.floor_pos.mpr ( by linarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] ) ) ] ; norm_num;
        linarith [ h_diff N hN_pos, h_floor N hN_pos ];
      -- Similarly, we have:
      have h_bound_neg : ∀ N : ℕ, 0 < N → Complex.re (Complex.digamma x) - Complex.re (digammaSeriesSum x) ≥ -1 / (Nat.floor (x + N) : ℝ) := by
        intros N hN_pos
        have h_floor_neg : Complex.re (Complex.digamma (x + N)) - Complex.re (digammaSeriesSum (x + N)) ≥ Complex.re (Complex.digamma (Nat.floor (x + N))) - Complex.re (digammaSeriesSum (Nat.floor (x + N) + 1)) := by
          have h_floor_neg : Complex.re (Complex.digamma (x + N)) ≥ Complex.re (Complex.digamma (Nat.floor (x + N))) := by
            have := h_inc ( Nat.floor ( x + N ) ) ( x + N ) ?_ ?_ <;> norm_num at *;
            · linarith;
            · exact Nat.floor_pos.mpr ( by linarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] );
            · exact Nat.floor_le ( by positivity );
          have h_floor_neg : Complex.re (digammaSeriesSum (x + N)) ≤ Complex.re (digammaSeriesSum (Nat.floor (x + N) + 1)) := by
            have := h_inc ( x + N ) ( ⌊x + N⌋₊ + 1 ) ( by positivity ) ( by linarith [ Nat.lt_floor_add_one ( x + N ) ] ) ; aesop;
          linarith;
        have h_floor_neg_eq : Complex.re (Complex.digamma (Nat.floor (x + N))) = Complex.re (digammaSeriesSum (Nat.floor (x + N))) := by
          exact h_eq _ <| Nat.floor_pos.mpr <| by linarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] ;
        have h_floor_neg_eq : Complex.re (digammaSeriesSum (Nat.floor (x + N) + 1)) = Complex.re (digammaSeriesSum (Nat.floor (x + N))) + 1 / (Nat.floor (x + N) : ℝ) := by
          convert congr_arg Complex.re ( digammaSeriesSum_add_one ( ⌊x + N⌋₊ : ℂ ) _ ) using 1 <;> norm_num;
          exact Nat.floor_pos.mpr ( by linarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] );
        grind;
      -- Taking the limit as $N \to \infty$, we get:
      have h_lim : Filter.Tendsto (fun N : ℕ => 1 / (Nat.floor (x + N) : ℝ)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun N : ℕ => -1 / (Nat.floor (x + N) : ℝ)) Filter.atTop (nhds 0) := by
        exact ⟨ tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop.comp <| tendsto_const_nhds.add_atTop <| tendsto_natCast_atTop_atTop, tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop.comp <| tendsto_const_nhds.add_atTop <| tendsto_natCast_atTop_atTop ⟩;
      have h_lim_zero : Complex.re (Complex.digamma x) - Complex.re (digammaSeriesSum x) = 0 := by
        exact le_antisymm ( le_of_tendsto_of_tendsto tendsto_const_nhds h_lim.1 <| Filter.eventually_atTop.mpr ⟨ 1, fun N hN => h_bound N hN ⟩ ) ( le_of_tendsto_of_tendsto h_lim.2 tendsto_const_nhds <| Filter.eventually_atTop.mpr ⟨ 1, fun N hN => h_bound_neg N hN ⟩ );
      have h_im_zero : Complex.im (Complex.digamma x) = 0 ∧ Complex.im (digammaSeriesSum x) = 0 := by
        have h_im_zero : Complex.im (Complex.digamma x) = 0 := by
          convert digamma_ofReal_im x hx using 1;
        simp_all +decide [ digammaSeriesSum ];
        rw [ ← Complex.conj_eq_iff_im ];
        rw [ Complex.conj_tsum ] ; norm_num [ Complex.ext_iff ];
      exact Complex.ext ( by linarith ) ( by linarith )

/-
The key identity: ψ(s) = digammaSeriesSum(s) for Re(s) > 0.

Proved by showing equality on the positive reals (digamma_eq_series_real)
and extending to {Re > 0} by the identity theorem for analytic functions.
-/
lemma digamma_eq_series (s : ℂ) (hs : 0 < s.re) :
    Complex.digamma s = digammaSeriesSum s := by
      -- Apply the identity theorem for analytic functions.
      have h_id : AnalyticOnNhd ℂ (fun s => Complex.digamma s - digammaSeriesSum s) {s : ℂ | 0 < s.re} := by
        apply_rules [ DifferentiableOn.analyticOnNhd ];
        · refine' DifferentiableOn.sub _ _;
          · -- The Gamma function is analytic on the right half-plane, so its logarithmic derivative, the digamma function, is also analytic there.
            have h_gamma_analytic : AnalyticOn ℂ Complex.Gamma {s : ℂ | 0 < s.re} := by
              apply_rules [ DifferentiableOn.analyticOn ];
              · intro s hs; exact Complex.differentiableAt_Gamma _ ( by contrapose! hs; aesop ) |> DifferentiableAt.differentiableWithinAt;
              · exact isOpen_lt continuous_const Complex.continuous_re;
            refine' DifferentiableOn.div _ _ _;
            · apply_rules [ DifferentiableOn.deriv, h_gamma_analytic.differentiableOn ];
              exact isOpen_lt continuous_const Complex.continuous_re;
            · exact h_gamma_analytic.differentiableOn;
            · exact fun x hx => Complex.Gamma_ne_zero_of_re_pos hx;
          · -- The series representation of the digamma function is differentiable on the right half-plane.
            have h_diff : ∀ s : ℂ, 0 < s.re → HasDerivAt (fun s => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (s + (k : ℂ)))) (∑' k : ℕ, (1 / (s + (k : ℂ)) ^ 2)) s := by
              intro s hs;
              rw [ hasDerivAt_iff_tendsto_slope_zero ];
              -- We can interchange the limit and the sum because the series converges uniformly.
              have h_uniform : Filter.Tendsto (fun t : ℂ => ∑' k : ℕ, (t⁻¹ • ((1 / (k + 1 : ℂ) - 1 / (s + t + k)) - (1 / (k + 1 : ℂ) - 1 / (s + k))))) (𝓝[≠] 0) (𝓝 (∑' k : ℕ, (1 / (s + k : ℂ) ^ 2))) := by
                refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
                use fun k => 2 / ( s.re / 2 + k ) ^ 2;
                · have h_summable : Summable (fun k : ℕ => (1 : ℝ) / (s.re / 2 + k) ^ 2) := by
                    have h_summable : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) := by
                      exact Real.summable_one_div_nat_pow.2 one_lt_two;
                    rw [ ← summable_nat_add_iff 1 ] at *;
                    exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by gcongr ; linarith ) h_summable;
                  simpa using h_summable.mul_left 2;
                · intro k;
                  -- Simplify the expression inside the limit.
                  suffices h_simplify : Filter.Tendsto (fun x : ℂ => (1 / (s + x + k) - 1 / (s + k)) / x) (𝓝[≠] 0) (𝓝 (-1 / (s + k) ^ 2)) by
                    convert h_simplify.neg using 2 <;> norm_num ; ring;
                    ring;
                  have h_simplify : HasDerivAt (fun x : ℂ => 1 / (s + x + k)) (-1 / (s + k) ^ 2) 0 := by
                    convert HasDerivAt.inv ( HasDerivAt.add ( hasDerivAt_id 0 |> HasDerivAt.const_add s ) ( hasDerivAt_const _ _ ) ) _ using 1 <;> norm_num;
                    exacts [ rfl, rfl, by exact ne_of_apply_ne Complex.re ( by norm_num; linarith ) ];
                  simpa [ div_eq_inv_mul ] using h_simplify.tendsto_slope_zero;
                · rw [ eventually_nhdsWithin_iff ];
                  rw [ Metric.eventually_nhds_iff ];
                  refine' ⟨ s.re / 2, half_pos hs, fun y hy hy' k => _ ⟩ ; simp_all +decide [ div_eq_mul_inv, norm_mul, norm_inv ];
                  rw [ inv_sub_inv ] <;> norm_num;
                  · field_simp;
                    rw [ div_le_iff₀ ] <;> norm_num at *;
                    · -- We'll use the fact that ‖s + k‖ ≥ s.re + k and ‖s + y + k‖ ≥ s.re + k - ‖y‖.
                      have h_norms : ‖s + k‖ ≥ s.re + k ∧ ‖s + y + k‖ ≥ s.re + k - ‖y‖ := by
                        constructor <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
                        · exact Real.le_sqrt_of_sq_le ( by nlinarith );
                        · nlinarith [ show Real.sqrt ( ( s.re + y.re + k ) * ( s.re + y.re + k ) + ( s.im + y.im ) * ( s.im + y.im ) ) ≥ s.re + y.re + k by exact Real.le_sqrt_of_sq_le ( by nlinarith ), show Real.sqrt ( y.re * y.re + y.im * y.im ) ≥ -y.re by exact Real.le_sqrt_of_sq_le ( by nlinarith ) ];
                      nlinarith [ show ( k : ℝ ) ≥ 0 by positivity, show ( ‖y‖ : ℝ ) ≥ 0 by positivity, show ( ‖s + k‖ : ℝ ) ≥ 0 by positivity, show ( ‖s + y + k‖ : ℝ ) ≥ 0 by positivity ];
                    · exact mul_pos ( norm_pos_iff.mpr <| by exact ne_of_apply_ne Complex.re <| by norm_num; linarith ) ( norm_pos_iff.mpr <| by exact ne_of_apply_ne Complex.re <| by norm_num; linarith [ abs_le.mp ( Complex.abs_re_le_norm y ) ] );
                  · exact ne_of_apply_ne Complex.re ( by norm_num; linarith );
                  · intro H; rw [ Complex.ext_iff ] at H; norm_num at H; linarith [ abs_le.mp ( Complex.abs_re_le_norm y ), abs_le.mp ( Complex.abs_im_le_norm y ) ] ;
              refine' h_uniform.congr' _;
              rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
              rw [ Metric.eventually_nhds_iff ];
              refine' ⟨ s.re / 2, half_pos hs, fun y hy hy' => _ ⟩;
              rw [ ← Summable.tsum_sub ];
              · exact?;
              · have := digamma_series_summable ( s + y ) ?_;
                · convert this using 1;
                · norm_num at *; linarith [ abs_le.mp ( Complex.abs_re_le_norm y ) ];
              · have := digamma_series_summable s hs;
                convert this using 1;
            exact fun s hs => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( differentiableAt_const _ ) ( h_diff s hs |> HasDerivAt.differentiableAt ) );
        · exact isOpen_lt continuous_const Complex.continuous_re;
      have h_zero : ∀ x : ℝ, 0 < x → Complex.digamma (x : ℂ) - digammaSeriesSum (x : ℂ) = 0 := by
        exact fun x hx => sub_eq_zero_of_eq <| digamma_eq_series_real x hx;
      have h_id : ∀ s : ℂ, 0 < s.re → Complex.digamma s - digammaSeriesSum s = 0 := by
        apply h_id.eqOn_zero_of_preconnected_of_frequently_eq_zero;
        exact convex_halfSpace_re_gt 0 |> Convex.isPreconnected;
        exact show 0 < ( 1 : ℂ ).re from by norm_num;
        rw [ Metric.nhdsWithin_basis_ball.frequently_iff ];
        intro ε hε;
        exact ⟨ 1 + ε / 2, ⟨ by norm_num [ abs_of_pos, hε ], by norm_num [ Complex.ext_iff, hε.ne' ] ⟩, by simpa [ add_comm ] using h_zero ( 1 + ε / 2 ) ( by linarith ) ⟩;
      exact eq_of_sub_eq_zero <| h_id s hs

/-! ## Part 3: Bounding the digamma series -/

/-
For σ > 0 and |t| ≥ 1, bound each term of the digamma series.
-/
lemma digamma_series_term_norm_le (σ : ℝ) (hσ : 0 < σ) (t : ℝ) (k : ℕ) :
    ‖(1 / ((k : ℂ) + 1) - 1 / (((σ : ℂ) + ↑t * I) + (k : ℂ)))‖ ≤
      (|σ - 1| + |t|) / ((↑k + 1) * Real.sqrt ((↑k + σ) ^ 2 + t ^ 2)) := by
        rw [ div_sub_div, norm_div ];
        · gcongr <;> norm_num [ Complex.normSq, Complex.norm_def ];
          · rw [ Real.sqrt_le_left ] <;> cases abs_cases ( σ - 1 ) <;> cases abs_cases t <;> nlinarith;
          · rw [ Real.sqrt_mul_self <| by positivity ] ; ring_nf ; norm_num;
        · exact Nat.cast_add_one_ne_zero _;
        · norm_num [ Complex.ext_iff ] ; intros ; linarith

/-
Harmonic sum bound: Σ_{k=0}^{N-1} 1/(k+1) ≤ 1 + log N
-/
lemma harmonic_le_one_add_log' (N : ℕ) (hN : 0 < N) :
    (∑ k ∈ Finset.range N, (1 : ℝ) / (↑k + 1)) ≤ 1 + Real.log N := by
      induction hN <;> norm_num [ Finset.sum_range_succ ];
      rename_i k hk ih; rw [ show ( k : ℝ ) + 1 = ( k : ℝ ) * ( 1 + ( k : ℝ ) ⁻¹ ) by nlinarith [ mul_inv_cancel₀ ( show ( k : ℝ ) ≠ 0 by norm_cast; aesop ) ], Real.log_mul ( by norm_cast; aesop ) ( by positivity ) ] ; norm_num at * ; nlinarith [ inv_pos.mpr ( show ( k : ℝ ) > 0 by norm_cast ), mul_inv_cancel₀ ( show ( k : ℝ ) ≠ 0 by norm_cast; aesop ), Real.log_inv ( 1 + ( k : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( show ( 0 : ℝ ) < 1 + ( k : ℝ ) ⁻¹ by positivity ) ), inv_mul_cancel₀ ( show ( 1 + ( k : ℝ ) ⁻¹ ) ≠ 0 by positivity ) ] ;

/-
Tail sum bound: Σ_{k≥N} 1/((k+σ)²+t²) ≤ 1/max(N+σ-1, |t|) for N ≥ 1
-/
lemma tail_sum_bound (σ : ℝ) (hσ : 0 < σ) (t : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (ht : 1 ≤ |t|) :
    ∑' k : ℕ, (1 : ℝ) / ((↑(k + N) + σ) ^ 2 + t ^ 2) ≤
      2 / |t| := by
        -- We'll use the fact that $\sum_{k=0}^{\infty} \frac{1}{(k+1)^2 + t^2} \leq \int_{0}^{\infty} \frac{dx}{x^2 + t^2}$.
        have h_integral : ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 2 + t ^ 2) ≤ ∫ x in Set.Ioi 0, (1 / (x ^ 2 + t ^ 2)) := by
          -- We'll use the fact that the sum of a series is less than or equal to the integral of its terms.
          have h_integral_bound : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k + 1 : ℝ) ^ 2 + t ^ 2)) ≤ ∫ x in (0 : ℝ)..n, (1 / (x ^ 2 + t ^ 2)) := by
            intro n
            have h_integral_bound : ∀ k : ℕ, ∫ x in (k : ℝ)..((k + 1) : ℝ), (1 / (x ^ 2 + t ^ 2)) ≥ 1 / ((k + 1 : ℝ) ^ 2 + t ^ 2) := by
              intro k; refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ fun x hx => one_div_le_one_div_of_le _ <| add_le_add ( pow_le_pow_left₀ ( by linarith [ hx.1 ] ) hx.2 2 ) le_rfl ) <;> norm_num;
              · exact Continuous.intervalIntegrable ( by exact Continuous.inv₀ ( by continuity ) fun x => by nlinarith [ abs_mul_abs_self t ] ) _ _;
              · nlinarith [ abs_mul_abs_self t ];
            induction n <;> simp_all +decide [ Finset.sum_range_succ ];
            convert add_le_add ‹_› ( h_integral_bound _ ) using 1;
            rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> exact Continuous.intervalIntegrable ( by exact Continuous.inv₀ ( by continuity ) fun x => by nlinarith [ abs_mul_abs_self t ] ) _ _;
          -- Taking the limit of the integral bound as $n$ approaches infinity, we get the desired result.
          have h_integral_limit : Filter.Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..n, (1 / (x ^ 2 + t ^ 2))) Filter.atTop (nhds (∫ x in Set.Ioi 0, (1 / (x ^ 2 + t ^ 2)))) := by
            apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
            · -- We'll use the fact that $\frac{1}{x^2 + t^2}$ is integrable on $(0, \infty)$.
              have h_integrable : MeasureTheory.IntegrableOn (fun x : ℝ => (1 / (x ^ 2 + t ^ 2))) (Set.Ioi 1) := by
                have h_integral_converges : MeasureTheory.IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Set.Ioi 1) MeasureTheory.volume := by
                  have h_integral_converges : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi 1) MeasureTheory.volume := by
                    rw [ integrableOn_Ioi_rpow_iff ] <;> norm_num;
                  norm_cast at * ; aesop;
                refine' h_integral_converges.mono' _ _;
                · exact Continuous.aestronglyMeasurable ( continuous_const.div ( by continuity ) fun x => by nlinarith [ abs_mul_abs_self t ] );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact one_div_le_one_div_of_le ( sq_pos_of_pos <| zero_lt_one.trans hx ) <| by nlinarith [ abs_mul_abs_self t ] ;
              have h_integrable : MeasureTheory.IntegrableOn (fun x : ℝ => (1 / (x ^ 2 + t ^ 2))) (Set.Ioc 0 1) := by
                exact Continuous.integrableOn_Ioc ( continuous_const.div ( by continuity ) fun x => by nlinarith [ abs_mul_abs_self t ] );
              convert h_integrable.union ‹MeasureTheory.IntegrableOn ( fun x : ℝ => 1 / ( x ^ 2 + t ^ 2 ) ) ( Set.Ioi 1 ) MeasureTheory.volume› using 1 ; ext ; aesop;
            · exact tendsto_natCast_atTop_atTop;
          refine' le_of_tendsto_of_tendsto' ( Summable.hasSum ( by exact_mod_cast by { exact_mod_cast Summable.of_nonneg_of_le ( fun _ ↦ by positivity ) ( fun n ↦ by simpa using inv_anti₀ ( by positivity ) <| by nlinarith ) <| summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two } ) |> HasSum.tendsto_sum_nat ) h_integral_limit fun n ↦ h_integral_bound n;
        -- Evaluate the integral $\int_{0}^{\infty} \frac{dx}{x^2 + t^2}$.
        have h_integral_eval : ∫ x in Set.Ioi 0, (1 / (x ^ 2 + t ^ 2)) = Real.pi / (2 * |t|) := by
          -- Use the substitution $u = \frac{x}{|t|}$ to transform the integral.
          have h_subst : ∫ x in Set.Ioi 0, (1 / (x ^ 2 + t ^ 2)) = ∫ u in Set.Ioi 0, (1 / (u ^ 2 + 1)) / |t| := by
            have h_subst : ∀ {f : ℝ → ℝ}, ∫ x in Set.Ioi 0, f x = ∫ u in Set.Ioi 0, f (|t| * u) * |t| := by
              intro f; rw [ MeasureTheory.integral_mul_const ] ; rw [ MeasureTheory.integral_comp_mul_left_Ioi ] ; norm_num [ show t ≠ 0 by rintro rfl; norm_num at ht ] ;
              · rw [ inv_mul_eq_div, div_mul_cancel₀ _ ( by positivity ) ];
              · positivity;
            convert h_subst using 3 ; ring;
            grind;
          rw [ h_subst, MeasureTheory.integral_div ];
          ring_nf; norm_num [ div_eq_mul_inv ];
          ring;
        -- Since $\sum_{k=0}^{\infty} \frac{1}{(k+N+\sigma)^2 + t^2} \leq \sum_{k=0}^{\infty} \frac{1}{(k+1)^2 + t^2}$, we can conclude.
        have h_sum_le : ∑' k : ℕ, 1 / ((k + N + σ) ^ 2 + t ^ 2) ≤ ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 2 + t ^ 2) := by
          refine' Summable.tsum_le_tsum _ _ _;
          · exact fun k => one_div_le_one_div_of_le ( by positivity ) ( by ring_nf; nlinarith only [ show ( N : ℝ ) ≥ 1 by norm_cast, hσ ] );
          · exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun n => by rw [ div_le_div_iff₀ ] <;> norm_num <;> ring <;> nlinarith only [ show ( n : ℝ ) + N ≥ 1 by norm_cast; linarith, hσ, ht ] ) ( summable_nat_add_iff N |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
          · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by simpa using inv_anti₀ ( by positivity ) ( show ( ( k : ℝ ) + 1 ) ^ 2 + t ^ 2 ≥ ( k + 1 ) ^ 2 by nlinarith ) ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
        norm_num [ add_assoc ] at * ; exact h_sum_le.trans <| h_integral.trans <| h_integral_eval.le.trans <| by rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.pi_le_four, abs_nonneg t ] ;

/-
Main bounding lemma: the digamma series is O(log(1+|t|)) for |t| ≥ 1.
-/
lemma digamma_series_norm_bound (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖digammaSeriesSum ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log (1 + |t|) := by
        -- Let's choose any $t$ such that $|t| \geq 1$.
        suffices h_bound : ∀ t : ℝ, 1 ≤ |t| → ‖digammaSeriesSum (σ + t * Complex.I)‖ ≤ (|σ - 1| + 1) * (5 + Real.log (1 + |t|)) + |Real.eulerMascheroniConstant| by
          -- We can choose $C$ to be the maximum of the constants from the two parts of the bound.
          use (|σ - 1| + 1) * (5 / Real.log 2 + 1) + |Real.eulerMascheroniConstant| / Real.log 2 + 1;
          refine' ⟨ by positivity, fun t ht => le_trans ( h_bound t ht ) _ ⟩;
          ring_nf;
          have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ), Real.log_le_log ( by positivity ) ( by linarith : ( 1 + |t| ) ≥ 2 ), abs_nonneg ( -1 + σ ), abs_nonneg ( Real.eulerMascheroniConstant ), mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith : ( 1 + |t| ) ≥ 2 ) ) ( abs_nonneg ( -1 + σ ) ), mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith : ( 1 + |t| ) ≥ 2 ) ) ( abs_nonneg ( Real.eulerMascheroniConstant ) ) ];
        intro t ht
        have h_split : ‖digammaSeriesSum (σ + t * Complex.I)‖ ≤ |Real.eulerMascheroniConstant| + (∑ k ∈ Finset.range (Nat.ceil |t|), ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * Complex.I + (k : ℂ)))‖) + (∑' k : ℕ, ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) - 1 / (σ + t * Complex.I + (k + Nat.ceil |t| : ℂ)))‖) := by
          have h_split : ‖digammaSeriesSum (σ + t * Complex.I)‖ ≤ |Real.eulerMascheroniConstant| + (∑ k ∈ Finset.range (Nat.ceil |t|), ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * Complex.I + (k : ℂ)))‖) + ‖∑' k : ℕ, (1 / ((k + Nat.ceil |t| : ℂ) + 1) - 1 / (σ + t * Complex.I + (k + Nat.ceil |t| : ℂ)))‖ := by
            have h_split : digammaSeriesSum (σ + t * Complex.I) = -(Real.eulerMascheroniConstant : ℂ) + (∑ k ∈ Finset.range (Nat.ceil |t|), (1 / ((k : ℂ) + 1) - 1 / (σ + t * Complex.I + (k : ℂ)))) + (∑' k : ℕ, (1 / ((k + Nat.ceil |t| : ℂ) + 1) - 1 / (σ + t * Complex.I + (k + Nat.ceil |t| : ℂ)))) := by
              unfold digammaSeriesSum;
              rw [ ← Summable.sum_add_tsum_nat_add ];
              norm_num [ add_assoc ];
              congr! 1;
              convert digamma_series_summable ( σ + t * Complex.I ) ( by simpa [ Complex.add_re, Complex.mul_re ] using hσ ) using 1;
            rw [h_split];
            refine' le_trans ( norm_add_le _ _ ) ( add_le_add ( le_trans ( norm_add_le _ _ ) _ ) le_rfl );
            exact add_le_add ( by norm_num ) ( norm_sum_le _ _ );
          refine le_trans h_split ?_;
          gcongr;
          convert norm_tsum_le_tsum_norm _ ; norm_num;
          have := digamma_series_summable ( σ + t * Complex.I ) ( by simpa [ Complex.add_re, Complex.mul_re ] using hσ );
          convert this.norm.comp_injective ( add_left_injective ⌈|t|⌉₊ ) using 2 ; norm_num;
        -- For $k < N$, we have $\|1 / ((k : ℂ) + 1) - 1 / (σ + t * Complex.I + (k : ℂ))\| \leq (|σ - 1| + |t|) / ((k + 1) * |t|)$.
        have h_head : ∑ k ∈ Finset.range (Nat.ceil |t|), ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * Complex.I + (k : ℂ)))‖ ≤ (|σ - 1| + |t|) / |t| * (1 + Real.log (Nat.ceil |t|)) := by
          have h_head : ∀ k ∈ Finset.range (Nat.ceil |t|), ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * Complex.I + (k : ℂ)))‖ ≤ (|σ - 1| + |t|) / ((k + 1) * |t|) := by
            intro k hk
            have h_term : ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * Complex.I + (k : ℂ)))‖ ≤ (|σ - 1| + |t|) / ((k + 1) * Real.sqrt ((k + σ) ^ 2 + t ^ 2)) := by
              convert digamma_series_term_norm_le σ hσ t k using 1;
            exact h_term.trans ( by gcongr ; exact Real.abs_le_sqrt <| by nlinarith );
          refine le_trans ( Finset.sum_le_sum h_head ) ?_;
          -- We'll use the fact that $\sum_{k=1}^{N} \frac{1}{k} \leq 1 + \log N$.
          have h_harmonic : ∀ N : ℕ, 0 < N → ∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1) ≤ 1 + Real.log N := by
            exact?;
          convert mul_le_mul_of_nonneg_left ( h_harmonic ⌈|t|⌉₊ ( Nat.ceil_pos.mpr ( by positivity ) ) ) ( show 0 ≤ ( |σ - 1| + |t| ) / |t| by positivity ) using 1 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        -- For $k \geq N$, we have $\|1 / ((k + Nat.ceil |t| : ℂ) + 1) - 1 / (σ + t * Complex.I + (k + Nat.ceil |t| : ℂ))\| \leq (|σ - 1| + |t|) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t| + σ))$.
        have h_tail : ∑' k : ℕ, ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) - 1 / (σ + t * Complex.I + (k + Nat.ceil |t| : ℂ)))‖ ≤ (|σ - 1| + |t|) * (2 / |t|) := by
          have h_tail : ∑' k : ℕ, ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) - 1 / (σ + t * Complex.I + (k + Nat.ceil |t| : ℂ)))‖ ≤ (|σ - 1| + |t|) * (∑' k : ℕ, (1 : ℝ) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t| + σ))) := by
            have h_tail : ∀ k : ℕ, ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) - 1 / (σ + t * Complex.I + (k + Nat.ceil |t| : ℂ)))‖ ≤ (|σ - 1| + |t|) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t| + σ)) := by
              intro k
              have h_term : ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) - 1 / (σ + t * Complex.I + (k + Nat.ceil |t| : ℂ)))‖ = ‖(σ - 1 + t * Complex.I) / ((k + Nat.ceil |t| + 1) * (σ + t * Complex.I + (k + Nat.ceil |t|)))‖ := by
                rw [ div_sub_div ] <;> ring <;> norm_num [ Complex.ext_iff, hσ.ne' ];
                · exact mod_cast by positivity;
                · exact fun h => by linarith [ abs_nonneg t ] ;
              rw [ h_term, norm_div ];
              gcongr <;> norm_cast <;> norm_num [ Complex.normSq, Complex.norm_def ];
              · rw [ Real.sqrt_le_left ] <;> cases abs_cases ( σ - 1 ) <;> cases abs_cases t <;> nlinarith;
              · rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.le_sqrt_of_sq_le <| by nlinarith [ sq_nonneg ( σ + ( k + ⌈|t|⌉₊ ) - ( k + ⌈|t|⌉₊ + 1 ) ), abs_mul_abs_self t ] ;
            rw [ ← tsum_mul_left ];
            refine' Summable.tsum_le_tsum _ _ _;
            · simpa only [ mul_one_div ] using h_tail;
            · refine' Summable.of_nonneg_of_le ( fun k => norm_nonneg _ ) ( fun k => h_tail k ) _;
              exact Summable.mul_left _ <| Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_num <;> ring <;> nlinarith [ Nat.le_ceil ( |t| ), abs_nonneg t ] ) <| summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
            · refine' Summable.mul_left _ _;
              exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun n => by rw [ div_le_div_iff₀ ] <;> norm_num <;> ring <;> nlinarith [ Nat.le_ceil ( |t| ), abs_nonneg t ] ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
          refine le_trans h_tail ?_;
          gcongr;
          have h_tail_sum : ∑' k : ℕ, (1 : ℝ) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t| + σ)) ≤ ∑' k : ℕ, (1 : ℝ) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t|)) := by
            refine' Summable.tsum_le_tsum _ _ _;
            · exact fun k => one_div_le_one_div_of_le ( by positivity ) ( by nlinarith );
            · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by rw [ div_le_div_iff₀ ] <;> norm_num <;> ring <;> nlinarith [ Nat.le_ceil ( |t| ), abs_nonneg t ] ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
            · exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring <;> nlinarith [ Nat.ceil_pos.mpr ( show 0 < |t| by positivity ) ] ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.mpr one_lt_two );
          have h_tail_sum : ∑' k : ℕ, (1 : ℝ) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t|)) ≤ 1 / (Nat.ceil |t|) := by
            have h_tail_sum : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t|)) ≤ 1 / (Nat.ceil |t|) := by
              intro N
              have h_telescope : ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t|)) = 1 / (Nat.ceil |t|) - 1 / (N + Nat.ceil |t|) := by
                induction N <;> simp_all +decide [ Finset.sum_range_succ ];
                -- Combine and simplify the terms on the left-hand side.
                field_simp
                ring;
              exact h_telescope ▸ sub_le_self _ ( by positivity );
            exact le_of_tendsto_of_tendsto' ( Summable.hasSum ( by exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun n => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring <;> nlinarith [ Nat.ceil_pos.mpr ( show 0 < |t| by positivity ) ] ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.mpr one_lt_two ) ) |> HasSum.tendsto_sum_nat ) tendsto_const_nhds h_tail_sum;
          exact le_trans ‹_› ( h_tail_sum.trans ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ Nat.le_ceil ( |t| ), abs_nonneg t ] ) );
        -- Combine the bounds for the head and tail sums.
        have h_combined : ‖digammaSeriesSum (σ + t * Complex.I)‖ ≤ |Real.eulerMascheroniConstant| + (|σ - 1| + |t|) / |t| * (1 + Real.log (1 + |t|)) + (|σ - 1| + |t|) * (2 / |t|) := by
          refine le_trans h_split <| add_le_add_three le_rfl ( h_head.trans ?_ ) h_tail;
          gcongr;
          linarith [ Nat.ceil_lt_add_one ( show 0 ≤ |t| by positivity ) ];
        refine le_trans h_combined ?_;
        field_simp;
        nlinarith [ abs_nonneg ( Real.eulerMascheroniConstant ), abs_nonneg ( σ - 1 ), abs_nonneg t, Real.log_nonneg ( by linarith : ( 1 + |t| ) ≥ 1 ), mul_le_mul_of_nonneg_left ht ( abs_nonneg ( Real.eulerMascheroniConstant ) ), mul_le_mul_of_nonneg_left ht ( abs_nonneg ( σ - 1 ) ), mul_le_mul_of_nonneg_left ht ( abs_nonneg t ) ]

/-! ## Part 4: Main theorem -/

/-- The digamma ψ(s) = Γ'(s)/Γ(s) is the logDeriv of Gamma. -/
lemma deriv_div_eq_digamma (s : ℂ) (hs : 0 < s.re) :
    deriv Gamma s / Gamma s = Complex.digamma s := by
  rw [Complex.digamma_def, logDeriv_apply]

theorem Complex.digamma_vertical_log_bound (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * Real.log (1 + |t|) := by
  -- Rewrite using digamma
  have hre : ∀ t : ℝ, 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    intro t; simp; exact hσ
  obtain ⟨C, hC, hbound⟩ := digamma_series_norm_bound σ hσ
  exact ⟨C, hC, fun t ht => by
    rw [deriv_div_eq_digamma _ (hre t), digamma_eq_series _ (hre t)]
    exact hbound t ht⟩

#print axioms Complex.digamma_vertical_log_bound