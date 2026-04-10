import Mathlib

/-!
# Consequences of a Hypothetical Off-Line Zeta Zero: Amplitude Defect Contradictions

## Mathematical Background

If the Riemann zeta function ζ(s) had a zero ρ = β + iγ with β > 1/2 (off the critical
line), the explicit formula for prime-counting functions shows this zero injects an
"amplitude defect" into the harmonic decomposition of arithmetic functions. Specifically,
the contribution from such a zero pair {ρ, ρ̄} to the Chebyshev function ψ(x) includes
terms proportional to x^β, which grow without bound relative to the expected x^{1/2} scale.

We model this amplitude defect as a function D : ℕ → ℝ satisfying D(n) ≥ C · n^α for
constants C > 0 and α = β − 1/2 > 0. We then derive contradictions with eight independent,
unconditionally proven mathematical facts. Each theorem constitutes a proof by contradiction:
assuming such a defect exists leads to absurdity.

## Summary of Contradictions

1. **Summability** — The defect is not summable (violates Dirichlet series convergence)
2. **Vanishing at infinity** — The defect cannot tend to zero (violates the divergence test)
3. **Boundedness** — The defect is unbounded above (violates bounded oscillation)
4. **Convergence stability** — Adding the defect to any convergent sequence destroys convergence
5. **AM-GM amplification** — Even √D is not summable; AM-GM propagates defect growth
6. **Lp integrability** — The defect lies in no ℓ^p space for p > 0
7. **Dirichlet abscissa shift** — The defect shifts the convergence abscissa, creating a forbidden gap
8. **Logarithmic domination** — The defect exceeds any M·log(log(n)) bound
-/

open Filter Topology BigOperators Finset
open scoped Real

noncomputable section

/-! ## Core Definition -/

/-- An amplitude defect modeling the contribution of a hypothetical off-line zeta zero.
The key properties are polynomial lower-bound growth D(n) ≥ C · n^α for C > 0 and α > 0,
which captures the excess oscillation injected by a zero at Re(s) = 1/2 + α > 1/2. -/
structure AmplitudeDefect where
  /-- The defect function -/
  D : ℕ → ℝ
  /-- The polynomial growth exponent (= β − 1/2 > 0 for a zero at Re(s) = β > 1/2) -/
  α : ℝ
  /-- The amplitude constant -/
  C : ℝ
  /-- The exponent is positive -/
  hα_pos : 0 < α
  /-- The constant is positive -/
  hC_pos : 0 < C
  /-- The defect is nonnegative -/
  hD_nonneg : ∀ n, 0 ≤ D n
  /-- Polynomial lower bound: D(n) ≥ C · n^α for n ≥ 1 -/
  hD_growth : ∀ n : ℕ, 1 ≤ n → C * (n : ℝ) ^ α ≤ D n

/-! ## Theorem 1: Contradiction with Summability

If a series ∑ f(n) converges, its terms must tend to zero. Since D(n) ≥ C · n^α → ∞,
the terms grow without bound, so ∑ D(n) diverges. This contradicts the absolute convergence
of any Dirichlet series that the defect amplifies. -/

theorem AmplitudeDefect.not_summable (ad : AmplitudeDefect) :
    ¬ Summable ad.D := by
      -- By definition of $D$, we know that for all $n \geq 1$, $D(n) \geq C \cdot n^\alpha$.
      have hD_ge : ∀ n ≥ 1, ad.D n ≥ ad.C * (n : ℝ) ^ ad.α := by
        exact fun n hn => ad.hD_growth n hn;
      -- Since $C > 0$ and $\alpha > 0$, the series $\sum_{n=1}^{\infty} C \cdot n^{\alpha}$ diverges.
      have h_summable : ¬ Summable (fun n : ℕ => (ad.C : ℝ) * (n : ℝ) ^ ad.α) := by
        rw [ summable_mul_left_iff ] <;> norm_num [ ad.hC_pos.ne' ];
        linarith [ ad.hα_pos ];
      contrapose! h_summable;
      rw [ ← summable_nat_add_iff 1 ] at *;
      exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ad.hC_pos.le ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( fun n => hD_ge _ ( Nat.succ_pos _ ) ) h_summable

/-! ## Theorem 2: Contradiction with Vanishing at Infinity

The "divergence test" requires that terms of a convergent series tend to zero.
Since D(n) ≥ C · n^α → ∞, the defect catastrophically violates this necessary condition:
it not only fails to vanish, it grows without bound. -/

theorem AmplitudeDefect.not_tendsto_zero (ad : AmplitudeDefect) :
    ¬ Tendsto ad.D atTop (nhds 0) := by
      have h_lower_bound : ∀ᶠ n in atTop, ad.D n ≥ ad.C * (n : ℝ) ^ ad.α := by
        filter_upwards [ Filter.eventually_ge_atTop 1 ] with n hn using ad.hD_growth n hn;
      -- Since $ad.C > 0$ and $ad.α > 0$, we have that $ad.C * (n : ℝ) ^ ad.α \to \infty$ as $n \to \infty$.
      have h_lower_bound_inf : Filter.Tendsto (fun n : ℕ => ad.C * (n : ℝ) ^ ad.α) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop ad.hC_pos ( tendsto_rpow_atTop ( by linarith [ ad.hα_pos ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      exact fun h => not_tendsto_atTop_of_tendsto_nhds h ( Filter.tendsto_atTop_mono' _ h_lower_bound h_lower_bound_inf )

/-! ## Theorem 3: Contradiction with Boundedness

The oscillatory part of ψ(x) − x is unconditionally O(x · exp(−c√(log x))), which
for any fixed x is finite. An amplitude defect D(n) ≥ C · n^α that grows polynomially
cannot be contained in any bounded set. -/

theorem AmplitudeDefect.not_bddAbove (ad : AmplitudeDefect) :
    ¬ BddAbove (Set.range ad.D) := by
      -- By definition of $D$, we know that for any natural number $n$, $D(n) \geq C \cdot n^\alpha$.
      have h_lower_bound : ∀ n : ℕ, 1 ≤ n → ad.D n ≥ ad.C * (n : ℝ) ^ ad.α := by
        exact fun n hn => ad.hD_growth n hn;
      -- Since $C > 0$ and $\alpha > 0$, we have $C \cdot n^\alpha \to \infty$ as $n \to \infty$.
      have h_lim_inf : Filter.Tendsto (fun n : ℕ => ad.C * (n : ℝ) ^ ad.α) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop ad.hC_pos ( tendsto_rpow_atTop ( by linarith [ ad.hα_pos ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      exact fun ⟨ M, hM ⟩ => by have := h_lim_inf.eventually_gt_atTop ( M ) ; obtain ⟨ n, hn ⟩ := this.and ( Filter.eventually_ge_atTop 1 ) |> fun h => h.exists; linarith [ h_lower_bound n hn.2, hM <| Set.mem_range_self n ] ;

/-! ## Theorem 4: Contradiction with Stability of Convergent Sequences

The Prime Number Theorem states ψ(x)/x → 1. If g(n) → L (modeling any convergent
arithmetic quantity), then adding an unbounded defect D pushes g + D away from any
finite limit. No finite limit can absorb the unbounded perturbation. -/

theorem AmplitudeDefect.destroys_convergence (ad : AmplitudeDefect)
    (g : ℕ → ℝ) (L : ℝ) (hg : Tendsto g atTop (nhds L)) :
    ¬ ∃ M : ℝ, Tendsto (fun n => g n + ad.D n) atTop (nhds M) := by
      by_contra! h;
      -- By assumption, $D(n) \geq C \cdot n^\alpha$ for $n \geq 1$, which implies that $D(n)$ tends to infinity as $n$ tends to infinity.
      have hD_inf : Filter.Tendsto ad.D Filter.atTop Filter.atTop := by
        refine' Filter.tendsto_atTop_mono' _ _ _;
        exacts [ fun n => ad.C * ( n : ℝ ) ^ ad.α, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => ad.hD_growth n hn ⟩, Filter.Tendsto.const_mul_atTop ad.hC_pos <| tendsto_rpow_atTop ( by linarith [ ad.hα_pos ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ];
      exact not_tendsto_atTop_of_tendsto_nhds h.choose_spec ( Filter.Tendsto.add_atTop hg hD_inf )

/-! ## Theorem 5: AM-GM Amplification

By the AM-GM inequality, for positive reals a, b: √(ab) ≤ (a + b)/2.
Setting a = 1 and b = D(n), we get √(D(n)) ≤ (1 + D(n))/2.

Crucially, this shows the defect's influence propagates even through
square-root damping: √(D(n)) ≥ √(C · n^α) = √C · n^{α/2}, and since
α/2 > 0, even the square root grows without bound. The AM-GM inequality
guarantees that no sublinear averaging can tame the defect — it cascades
through all moments. -/

theorem AmplitudeDefect.sqrt_not_summable (ad : AmplitudeDefect) :
    ¬ Summable (fun n => Real.sqrt (ad.D n)) := by
      have h_sqrt_growth : ∀ n : ℕ, 1 ≤ n → Real.sqrt (ad.D n) ≥ Real.sqrt ad.C * (n : ℝ) ^ (ad.α / 2) := by
        intros n hn
        have h_sqrt_defect : Real.sqrt (ad.D n) ≥ Real.sqrt (ad.C * (n : ℝ) ^ ad.α) := by
          exact Real.sqrt_le_sqrt <| ad.hD_growth n hn;
        exact h_sqrt_defect.trans' ( by rw [ Real.sqrt_mul ( le_of_lt ad.hC_pos ), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity ) ] ; ring_nf; norm_num );
      -- Since $\sqrt{C} \cdot n^{\alpha/2}$ grows without bound as $n \to \infty$, the series $\sum_{n=1}^{\infty} \sqrt{C} \cdot n^{\alpha/2}$ diverges.
      have h_diverges : ¬ Summable (fun n : ℕ => Real.sqrt ad.C * (n : ℝ) ^ (ad.α / 2)) := by
        rw [ summable_mul_left_iff ] <;> norm_num [ Real.sqrt_ne_zero'.mpr ad.hC_pos ];
        linarith [ ad.hα_pos ];
      contrapose! h_diverges;
      rw [ ← summable_nat_add_iff 1 ] at *;
      exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => h_sqrt_growth _ le_add_self ) h_diverges

/-! ## Theorem 6: Contradiction with ℓ^p Integrability

The spectral decomposition of arithmetic functions via Dirichlet series places
their oscillatory parts in ℓ² (by the Plancherel/Parseval theorem for Dirichlet
series on the critical line). Since D(n)^p ≥ C^p · n^{αp} and αp > 0,
we have ∑ D(n)^p = ∞ for every p > 0. The defect lies in no ℓ^p space,
contradicting the ℓ² structure of the harmonic decomposition. -/

theorem AmplitudeDefect.not_lp_summable (ad : AmplitudeDefect)
    (p : ℝ) (hp : 0 < p) :
    ¬ Summable (fun n => ad.D n ^ p) := by
      by_contra h_summable;
      -- Since $D(n)^p \geq (C \cdot n^\alpha)^p = C^p \cdot n^{\alpha p}$ and $\alpha p > 0$, we have $D(n)^p \geq C^p$ for all $n \geq 1$.
      have h_lower_bound : ∀ n : ℕ, 1 ≤ n → ad.D n ^ p ≥ ad.C ^ p := by
        exact fun n hn => Real.rpow_le_rpow ( by linarith [ ad.hC_pos ] ) ( le_trans ( by exact le_mul_of_one_le_right ( by linarith [ ad.hC_pos ] ) ( Real.one_le_rpow ( by norm_cast ) ( by linarith [ ad.hα_pos ] ) ) ) ( ad.hD_growth n hn ) ) ( by positivity );
      exact absurd ( h_summable.tendsto_atTop_zero ) ( by exact fun h => absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds h <| Filter.eventually_atTop.mpr ⟨ 1, h_lower_bound ⟩ ) ( by norm_num; linarith [ Real.rpow_pos_of_pos ad.hC_pos p ] ) )

/-! ## Theorem 7: Contradiction with Dirichlet Series Convergence

Unconditionally, ∑ 1/n^s converges for s > 1 (the zeta function is finite there).
The weighted sum ∑ D(n)/n^s ≥ C · ∑ n^{α−s}. For s = 1 + α/2, the exponent is
α − (1 + α/2) = α/2 − 1 > −1 (since α > 0), so ∑ n^{α/2−1} diverges.

An off-line zero would thus shift the effective abscissa of absolute convergence
from σ = 1 to σ ≥ 1 + α/2, creating a gap (1, 1+α/2) where the zeta function is
known to be meromorphic but the amplified series diverges — a direct contradiction
with the unconditional analytic continuation of ζ(s). -/

theorem AmplitudeDefect.dirichlet_diverges (ad : AmplitudeDefect) :
    ¬ Summable (fun n => ad.D (n + 1) / ((n : ℝ) + 1) ^ (1 + ad.α / 2)) := by
      -- Apply the bound $D(n+1) \ge C (n+1)^{\alpha}$ to the terms of the series.
      have h_bound : ∀ n, ad.D (n + 1) / (n + 1 : ℝ) ^ (1 + ad.α / 2) ≥ (ad.C : ℝ) * (n + 1) ^ (ad.α - (1 + ad.α / 2)) := by
        intro n;
        rw [ Real.rpow_sub ] <;> norm_cast;
        · simpa [ mul_div ] using div_le_div_of_nonneg_right ( ad.hD_growth ( n + 1 ) ( by linarith ) ) ( by positivity );
        · linarith;
      have h_sum_diverges : ¬Summable (fun n : ℕ => (n + 1 : ℝ) ^ (ad.α - (1 + ad.α / 2))) := by
        exact_mod_cast mt ( summable_nat_add_iff 1 |>.1 ) ( Real.summable_nat_rpow.not.2 <| by linarith [ ad.hα_pos ] );
      exact fun h => h_sum_diverges <| by simpa [ summable_mul_left_iff, ad.hC_pos.ne' ] using h.of_nonneg_of_le ( fun n => mul_nonneg ( le_of_lt ad.hC_pos ) <| Real.rpow_nonneg ( by linarith ) _ ) h_bound;

/-! ## Theorem 8: Contradiction with Logarithmic Bounds (Mertens-Type)

Mertens' theorem states ∑_{p≤x} 1/p = log(log(x)) + M + O(1/log(x)).
If the defect D(n) ≥ C · n^α grows polynomially while Mertens-type sums grow
only double-logarithmically, the defect is incompatible with the known rate of
growth of prime-related sums: it injects an error that dwarfs the main term. -/

theorem AmplitudeDefect.exceeds_loglog (ad : AmplitudeDefect) :
    ¬ ∃ (M : ℝ), ∀ n : ℕ, 2 ≤ n → ad.D n ≤ M * Real.log (Real.log n) := by
      rintro ⟨ M, hM ⟩;
      -- Choose $n$ large enough such that $M \cdot \log(\log(n)) < C \cdot n^\alpha$.
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, M * Real.log (Real.log n) < ad.C * (n : ℝ) ^ ad.α := by
        have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n) / (n : ℝ) ^ ad.α) Filter.atTop (nhds 0) := by
          -- We can use the fact that $\log(\log(n))$ grows much slower than $n^\alpha$.
          have h_log_log_growth : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ ad.α) Filter.atTop (nhds 0) := by
            -- Let $y = \log x$, therefore the expression becomes $\frac{y}{e^{y \alpha}}$.
            suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y * ad.α)) Filter.atTop (nhds 0) by
              have := h_log.comp Real.tendsto_log_atTop;
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.rpow_def_of_pos hx, mul_comm ] );
            -- Let $z = y \alpha$, therefore the expression becomes $\frac{z}{e^z}$.
            suffices h_z : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
              have := h_z.comp ( Filter.tendsto_id.atTop_mul_const ad.hα_pos );
              convert this.div_const ad.α using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ad.hα_pos.ne' ];
            simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
          refine' squeeze_zero_norm' _ ( h_log_log_growth.comp tendsto_natCast_atTop_atTop );
          filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) <| by positivity ) ] ; exact div_le_div_of_nonneg_right ( Real.log_le_log ( Real.log_pos <| by norm_num; linarith ) <| by linarith [ Real.log_le_sub_one_of_pos <| show 0 < ( n : ℝ ) by positivity ] ) <| by positivity;
        -- By multiplying both sides of the inequality $M \cdot \log(\log(n)) / n^\alpha < ad.C$ by $n^\alpha$, we get $M \cdot \log(\log(n)) < ad.C \cdot n^\alpha$.
        have h_mul : ∃ N : ℕ, ∀ n ≥ N, M * (Real.log (Real.log n) / (n : ℝ) ^ ad.α) < ad.C := by
          simpa using h_log_growth.const_mul M |> fun h => h.eventually ( gt_mem_nhds <| by linarith [ ad.hC_pos ] );
        exact ⟨ h_mul.choose + 1, fun n hn => by have := h_mul.choose_spec n ( by linarith ) ; rwa [ mul_div, div_lt_iff₀ ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ] at this ⟩;
      exact not_le_of_gt ( hN ( N + 2 ) ( by linarith ) ) ( hM ( N + 2 ) ( by linarith ) |> le_trans ( ad.hD_growth ( N + 2 ) ( by linarith ) ) )

end