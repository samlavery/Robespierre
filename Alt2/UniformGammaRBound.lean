import Mathlib
import RequestProject.DigammaVerticalBound

/-!
# σ-uniform bound on `‖Γℝ'/Γℝ(σ+iT)‖` on the critical strip

For `σ ∈ (0,1)` and `T ≥ 2`, we have `‖logDeriv Γℝ(σ+iT)‖ ≤ C · log T`
with constant `C` independent of `σ`.

Strategy:
1. Uniform digamma bound: for `σ ∈ (0,1)` and `|t| ≥ 1`, bound
   `‖ψ(σ+it)‖ ≤ C_d · log(1+|t|)` (constant independent of σ).
   Proof: use `digammaSeriesSum` representation, exploit `|σ-1| ≤ 1` uniformly.
2. Bridge to `Γℝ`: use `Γℝ'/Γℝ(s) = -(log π)/2 + (1/2)·ψ(s/2)`.

Axiom footprint after completion: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-
Inlined from WeilArchPrimeIdentity.lean (which depends on missing files).
    Gammaℝ'(s)/Gammaℝ(s) = -(log π)/2 + (1/2)·(Γ'/Γ)(s/2).
-/
theorem gammaℝ_logDeriv_digamma_form :
    ∀ s : ℂ, s.Gammaℝ ≠ 0 → (∀ n : ℕ, s ≠ -(2 * (n : ℂ))) →
    deriv Complex.Gammaℝ s / s.Gammaℝ =
      -(Complex.log Real.pi) / 2 +
      (1 / 2) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) := by
  intro s hs_ne_zero hs_ne_neg_two_nat
  have h_gamma_half_ne_zero : Complex.Gamma (s / 2) ≠ 0 := by
    simp_all +decide [ Complex.Gammaℝ ];
  have h_deriv_half : deriv (fun s => Real.pi ^ (-s / 2 : ℂ) * Complex.Gamma (s / 2)) s = Real.pi ^ (-s / 2 : ℂ) * (-Real.log Real.pi / 2) * Complex.Gamma (s / 2) + Real.pi ^ (-s / 2 : ℂ) * deriv Complex.Gamma (s / 2) / 2 := by
    convert HasDerivAt.deriv ( HasDerivAt.mul ( HasDerivAt.cpow ( hasDerivAt_const _ _ ) ( HasDerivAt.div_const ( hasDerivAt_neg s ) _ ) _ ) ( HasDerivAt.comp s ( Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.hasDerivAt ) ( HasDerivAt.div_const ( hasDerivAt_id s ) _ ) ) ) using 1 <;> norm_num ; ring;
    · norm_num [ Complex.ofReal_log ( Real.pi_pos.le ) ] ; ring;
    · positivity;
    · exact fun n hn => hs_ne_neg_two_nat n <| by linear_combination' hn * 2;
  unfold Complex.Gammaℝ;
  field_simp;
  convert congr_arg ( · * 2 ) h_deriv_half using 1 <;> ring;
  norm_num [ Complex.ofReal_log Real.pi_pos.le ]

end Contour
end WeilPositivity

namespace UniformGammaR

/-! ### Part 1: σ-uniform digamma log bound -/

set_option maxHeartbeats 800000 in
/-- Each term in the digamma series is uniformly ≤ 2/(k+1) for σ ∈ (0,1), |t| ≥ 1. -/
private lemma digamma_term_uniform_bound (σ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : 1 ≤ |t|) (k : ℕ) :
    ‖(1 / ((k : ℂ) + 1) - 1 / (((σ : ℂ) + ↑t * I) + (k : ℂ)))‖ ≤
      2 / ((k : ℝ) + 1) := by
  convert digamma_series_term_norm_le σ hσ.1 t k |> le_trans <| ?_ using 1;
  field_simp;
  rw [ div_le_iff₀ ] <;> cases abs_cases ( σ - 1 ) <;> cases abs_cases t <;> nlinarith [ Real.sqrt_nonneg ( ( k + σ ) ^ 2 + t ^ 2 ), Real.mul_self_sqrt ( by positivity : 0 ≤ ( k + σ : ℝ ) ^ 2 + t ^ 2 ), hσ.1, hσ.2 ]

/-
Head sum of digamma series ≤ 2*(1 + log(1+|t|)) for σ ∈ (0,1), |t| ≥ 1.
-/
private lemma digamma_head_uniform_bound (σ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : 1 ≤ |t|) :
    (∑ k ∈ Finset.range (Nat.ceil |t|),
      ‖(1 / ((k : ℂ) + 1) - 1 / (((σ : ℂ) + ↑t * I) + (k : ℂ)))‖) ≤
      2 * (1 + Real.log (1 + |t|)) := by
  refine' le_trans ( Finset.sum_le_sum fun k hk => _ ) _;
  use fun k => 2 / ( k + 1 );
  · convert digamma_term_uniform_bound σ hσ t ht k using 1;
  · have := harmonic_le_one_add_log' ⌈|t|⌉₊ ( Nat.ceil_pos.mpr ( by positivity ) );
    norm_num [ div_eq_mul_inv, Finset.mul_sum _ _ _ ] at *;
    rw [ ← Finset.mul_sum _ _ _ ] ; exact mul_le_mul_of_nonneg_left ( this.trans ( by gcongr ; linarith [ Nat.ceil_lt_add_one ( show 0 ≤ |t| by positivity ) ] ) ) zero_le_two

/-
Tail sum of digamma series ≤ 4 for σ ∈ (0,1), |t| ≥ 1.
-/
private lemma digamma_tail_uniform_bound (σ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : 1 ≤ |t|) :
    (∑' k : ℕ,
      ‖(1 / ((↑(k + Nat.ceil |t|) : ℂ) + 1) -
        1 / (((σ : ℂ) + ↑t * I) + (↑(k + Nat.ceil |t|) : ℂ)))‖) ≤ 4 := by
  refine' le_trans ( Summable.tsum_le_tsum _ _ _ ) _;
  use fun k => 2 / ( ( k + ⌈|t|⌉₊ + σ ) * ( k + ⌈|t|⌉₊ + 1 ) ) * ( |σ - 1| + |t| );
  · intro k;
    refine' le_trans ( digamma_series_term_norm_le σ hσ.1 t ( k + ⌈|t|⌉₊ ) ) _;
    field_simp;
    gcongr <;> norm_num;
    · exact add_pos_of_nonneg_of_pos ( add_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) hσ.1;
    · linarith;
    · exact Real.le_sqrt_of_sq_le ( by nlinarith );
  · convert Summable.norm ( digamma_series_summable ( σ + t * Complex.I ) ( by simpa using hσ.1 ) |> Summable.comp_injective <| add_left_injective ⌈|t|⌉₊ ) using 1;
  · refine' Summable.mul_right _ _;
    refine' Summable.mul_left _ _;
    exact Summable.of_nonneg_of_le ( fun k => inv_nonneg.2 <| mul_nonneg ( by linarith [ hσ.1 ] ) ( by linarith [ hσ.1 ] ) ) ( fun k => by rw [ inv_le_comm₀ ] <;> norm_num <;> ring <;> nlinarith [ hσ.1, hσ.2, Nat.le_ceil ( |t| ) ] ) <| summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
  · -- The series $\sum_{k=0}^{\infty} \frac{2}{(k+N)(k+N+1)}$ is a telescoping series.
    have h_telescope : ∀ N : ℕ, N ≥ 1 → ∑' k : ℕ, (2 : ℝ) / ((k + N) * (k + N + 1)) = 2 / N := by
      intro N hN
      have h_telescope : ∀ n : ℕ, ∑ k ∈ Finset.range n, (2 : ℝ) / ((k + N) * (k + N + 1)) = 2 / N - 2 / (n + N) := by
        intro n; induction n <;> simp_all +decide [ Finset.sum_range_succ ];
        -- Combine and simplify the fractions
        field_simp
        ring;
      -- Taking the limit of the partial sum as $n$ approaches infinity, we get the sum of the series.
      have h_limit : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (2 : ℝ) / ((k + N) * (k + N + 1))) Filter.atTop (nhds (2 / N)) := by
        simpa only [ h_telescope ] using le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) <| by norm_num;
      exact tendsto_nhds_unique ( by exact ( Summable.hasSum <| by exact ( by by_contra h; exact not_tendsto_atTop_of_tendsto_nhds ( h_limit ) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h ) ) |> HasSum.tendsto_sum_nat ) h_limit;
    rw [ tsum_mul_right ];
    refine' le_trans ( mul_le_mul_of_nonneg_right ( Summable.tsum_le_tsum _ _ _ ) ( by positivity ) ) _;
    use fun k => 2 / ((k + ⌈|t|⌉₊) * (k + ⌈|t|⌉₊ + 1));
    · exact fun k => by rw [ div_le_div_iff₀ ] <;> nlinarith [ hσ.1, hσ.2, show ( ⌈|t|⌉₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.ceil_pos.mpr ( by positivity ) ), mul_self_nonneg ( k + ⌈|t|⌉₊ : ℝ ) ] ;
    · refine' Summable.mul_left _ _;
      exact Summable.of_nonneg_of_le ( fun _ => inv_nonneg.2 <| mul_nonneg ( by linarith [ hσ.1, Nat.le_ceil |t| ] ) ( by linarith [ hσ.1, Nat.le_ceil |t| ] ) ) ( fun n => by rw [ inv_le_comm₀ ] <;> norm_num <;> ring <;> nlinarith [ hσ.1, hσ.2, Nat.le_ceil |t| ] ) <| summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
    · exact ( by have := h_telescope ⌈|t|⌉₊ ( Nat.ceil_pos.mpr ( by positivity ) ) ; exact ( by contrapose! this; erw [ tsum_eq_zero_of_not_summable this ] ; positivity ) );
    · rw [ h_telescope _ ( Nat.ceil_pos.mpr ( by positivity ) ) ];
      rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ Nat.le_ceil ( |t| ), abs_nonneg ( σ - 1 ), abs_nonneg t, hσ.1, hσ.2, abs_of_neg ( by linarith [ hσ.1, hσ.2 ] : σ - 1 < 0 ) ]

/-
Uniform bound on digammaSeriesSum for σ ∈ (0,1), |t| ≥ 1.
-/
private lemma digammaSeriesSum_uniform_bound (σ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : 1 ≤ |t|) :
    ‖digammaSeriesSum ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      |Real.eulerMascheroniConstant| + 2 * (1 + Real.log (1 + |t|)) + 4 := by
  -- Split the series into head and tail.
  have h_split : digammaSeriesSum (σ + t * I) = -(Real.eulerMascheroniConstant : ℂ) + (∑ k ∈ Finset.range (Nat.ceil |t|), (1 / ((k : ℂ) + 1) - 1 / ((σ + t * I) + (k : ℂ)))) + (∑' k : ℕ, (1 / ((↑(k + Nat.ceil |t|) : ℂ) + 1) - 1 / ((σ + t * I) + (↑(k + Nat.ceil |t|) : ℂ)))) := by
    unfold digammaSeriesSum;
    rw [ ← Summable.sum_add_tsum_nat_add ];
    rw [ add_assoc ];
    convert digamma_series_summable ( σ + t * I ) ( by simpa using hσ.1 ) using 1;
  refine' le_trans ( h_split ▸ norm_add₃_le .. ) _;
  gcongr;
  · norm_num [ Complex.norm_def, Complex.normSq ];
  · exact le_trans ( norm_sum_le _ _ ) ( by simpa using digamma_head_uniform_bound σ hσ t ht );
  · refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
    · have := digamma_series_summable ( σ + t * Complex.I ) ( by simpa using hσ.1 );
      exact this.norm.comp_injective ( add_left_injective _ );
    · convert digamma_tail_uniform_bound σ hσ t ht using 1

/-
Arithmetic: |γ| + 2*(1+log(1+|t|)) + 4 ≤ 15 * log(1+|t|) for |t| ≥ 1.
-/
private lemma arith_bound (t : ℝ) (ht : 1 ≤ |t|) :
    |Real.eulerMascheroniConstant| + 2 * (1 + Real.log (1 + |t|)) + 4 ≤
      15 * Real.log (1 + |t|) := by
  have h_γ_pos : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  have h_γ_lt : Real.eulerMascheroniConstant < 2/3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have h_γ_abs_lt : |Real.eulerMascheroniConstant| < 1 := by
    rw [abs_of_pos h_γ_pos]; linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_bd : Real.log 2 ≤ Real.log (1 + |t|) :=
    Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ 1 + |t|)
  -- Tighter log 2 lower bound from Real.log_two_gt_d9: log 2 > 0.6931471803.
  have hlog2_tight : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  nlinarith [h_γ_abs_lt, hlog2_bd, hlog2_tight]

/-- **σ-uniform digamma log bound on the vertical strip `σ ∈ (0,1)`, `|t| ≥ 1`**. -/
theorem digamma_log_bound_uniform_sigma01 :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ t : ℝ, 1 ≤ |t| →
        ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
          Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * Real.log (1 + |t|) := by
  refine ⟨15, by norm_num, fun σ hσ t ht => ?_⟩
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by simp; exact hσ.1
  rw [deriv_div_eq_digamma _ hre, digamma_eq_series _ hre]
  exact (digammaSeriesSum_uniform_bound σ hσ t ht).trans (arith_bound t ht)

/-! ### Part 2: σ-uniform Γℝ'/Γℝ log bound on critical strip -/

/-- Algebra bridge: `(σ + iT)/2 = σ/2 + i(T/2)`. -/
private lemma half_eq (σ T : ℝ) :
    ((σ : ℂ) + (T : ℂ) * I) / 2 =
      ((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℝ) * I := by
  push_cast; ring

/-- **σ-uniform `Γℝ'/Γℝ` log bound on the critical strip**.
For `σ ∈ (0,1)` and `T ≥ 2`, `‖logDeriv Γℝ(σ+iT)‖ ≤ C · log T` with `C` uniform in σ.

Uses the decomposition `Γℝ'/Γℝ(s) = -(log π)/2 + (1/2)·ψ(s/2)` via
`ZD.WeilPositivity.Contour.gammaℝ_logDeriv_digamma_form` and the σ-uniform
digamma bound from `digamma_log_bound_uniform_sigma01`. -/
theorem gammaR_logDeriv_uniform_criticalStrip :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ : ℝ, σ ∈ Set.Ioo (0 : ℝ) 1 → ∀ T : ℝ, 2 ≤ T →
        ‖logDeriv Complex.Gammaℝ ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * Real.log T := by
  obtain ⟨Cd, hCd_pos, hCd_bd⟩ := digamma_log_bound_uniform_sigma01
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Choose a large uniform constant that dominates everything.
  refine ⟨(Real.log Real.pi + Cd + 1) / Real.log 2 + Cd + 1, ?_, ?_⟩
  · have hlogπ_nn : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (by linarith [Real.pi_gt_three])
    have h1 : 0 ≤ (Real.log Real.pi + Cd + 1) / Real.log 2 :=
      div_nonneg (by linarith) hlog2_pos.le
    linarith
  intro σ hσ T hT
  -- σ/2 ∈ (0, 1/2) ⊂ (0, 1) and |T/2| ≥ 1.
  have hσ2 : σ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hσ.1, hσ.2]
  have hT2_pos : 0 < T / 2 := by linarith
  have hT2_abs : |T / 2| = T / 2 := abs_of_pos hT2_pos
  have hT2_ge_one : 1 ≤ |T / 2| := by rw [hT2_abs]; linarith
  -- logDeriv Γℝ(s) = Γℝ'(s)/Γℝ(s) via logDeriv_apply
  have hT_pos : 0 < T := by linarith
  have hT_nonneg : 0 ≤ T := hT_pos.le
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  -- Write s = σ + iT.
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs_def
  have hs_re_pos : 0 < s.re := by rw [hs_def]; simp; exact hσ.1
  have hs_re_lt_1 : s.re < 1 := by rw [hs_def]; simp; exact hσ.2
  have hs_ne_zero : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hs_def] at this
    simp at this
    linarith [hσ.1]
  -- Γℝ(s) ≠ 0 for Re(s) > 0.
  have hGammaR_ne : Complex.Gammaℝ s ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos hs_re_pos
  -- Differentiability of Γℝ at s.
  have hGammaR_diff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have h_s_ne : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
      intro n h
      apply hGammaR_ne
      rw [h]
      exact Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩
    have h_s_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m h
      have : s = -(2 * (m : ℂ)) := by linear_combination 2 * h
      exact h_s_ne m this
    have hΓ_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
      Complex.differentiableAt_Gamma _ h_s_half_ne
    have hcpow_diff :
        DifferentiableAt ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2)) s := by
      refine DifferentiableAt.const_cpow
        ((differentiableAt_id.neg).div_const 2) ?_
      left
      exact_mod_cast Real.pi_pos.ne'
    have hcomp : DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (t / 2)) s :=
      hΓ_diff.comp s (differentiableAt_id.div_const 2)
    have h_eq :
        Complex.Gammaℝ = fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2) := by
      funext t
      exact Complex.Gammaℝ_def t
    rw [h_eq]
    exact hcpow_diff.mul hcomp
  -- Now unfold logDeriv and use the identity Γℝ'/Γℝ(s) = -(log π)/2 + (1/2) ψ(s/2).
  -- Directly compute via deriv of Γℝ_def.
  have h_Gammaℝ_def_at_s : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
    Complex.Gammaℝ_def s
  have h_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hGammaR_ne
    rw [h_Gammaℝ_def_at_s, h]
    rw [show (Real.pi : ℂ) ^ (-s / 2) = (Real.pi : ℂ) ^ (-s / 2) from rfl]
    rw [mul_eq_zero]
    right
    exact Complex.Gamma_neg_nat_eq_zero m
  have hΓ_half_ne : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero h_half_ne
  -- Apply hCd_bd at σ/2 and T/2.
  have h_half_eq_cast : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by
    rw [hs_def]; push_cast; ring
  have h_psi_bd :
      ‖deriv Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) /
        Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)‖
        ≤ Cd * Real.log (1 + |T / 2|) :=
    hCd_bd (σ / 2) hσ2 (T / 2) hT2_ge_one
  -- Transfer to s/2:
  have h_psi_at_half :
      deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2) =
        deriv Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) /
          Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) := by
    rw [h_half_eq_cast]
  have h_psi_norm_bd :
      ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖ ≤ Cd * Real.log (1 + |T / 2|) := by
    rw [h_psi_at_half]; exact h_psi_bd
  -- log(1 + T/2) ≤ log T for T ≥ 2.
  have h_log_bd : Real.log (1 + |T / 2|) ≤ Real.log T := by
    rw [hT2_abs]
    apply Real.log_le_log (by linarith) (by linarith)
  -- Compute logDeriv Γℝ(s) directly via existing `gammaℝ_logDeriv_digamma_form`.
  have h_ne_2n : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
    intro n h
    apply hGammaR_ne
    rw [h]
    exact Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩
  have h_form :=
    ZD.WeilPositivity.Contour.gammaℝ_logDeriv_digamma_form s hGammaR_ne h_ne_2n
  have h_Gammaℝ_logDeriv_form :
      logDeriv Complex.Gammaℝ s =
        -(Real.log Real.pi : ℂ) / 2 +
          (1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) := by
    rw [logDeriv_apply, h_form]
    have h_log_eq : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
      (Complex.ofReal_log Real.pi_pos.le).symm
    rw [h_log_eq]
  -- Bound:
  calc ‖logDeriv Complex.Gammaℝ s‖
      = ‖-(Real.log Real.pi : ℂ) / 2 +
          (1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2))‖ := by
        rw [h_Gammaℝ_logDeriv_form]
    _ ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ +
        ‖(1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2))‖ :=
          norm_add_le _ _
    _ = Real.log Real.pi / 2 +
          (1/2) * ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖ := by
        have h_logπ_nn : (0 : ℝ) ≤ Real.log Real.pi :=
          Real.log_nonneg (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
        have h_norm_first : ‖-(Real.log Real.pi : ℂ) / 2‖ = Real.log Real.pi / 2 := by
          rw [norm_div, norm_neg, show ‖(2 : ℂ)‖ = 2 from by norm_num]
          rw [show (Real.log Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) from rfl,
            Complex.norm_real]
          simp [abs_of_nonneg h_logπ_nn]
        have h_norm_second :
            ‖(1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2))‖ =
              (1/2) * ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖ := by
          rw [norm_mul]
          congr 1
          rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
          norm_num
        rw [h_norm_first, h_norm_second]
    _ ≤ Real.log Real.pi / 2 + (1/2) * (Cd * Real.log (1 + |T / 2|)) := by
          have : 0 ≤ (1/2 : ℝ) := by norm_num
          nlinarith [h_psi_norm_bd]
    _ ≤ Real.log Real.pi / 2 + (1/2) * (Cd * Real.log T) := by
          have : (1/2 : ℝ) * (Cd * Real.log (1 + |T / 2|)) ≤
              (1/2) * (Cd * Real.log T) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/2)
            apply mul_le_mul_of_nonneg_left h_log_bd hCd_pos.le
          linarith
    _ ≤ ((Real.log Real.pi + Cd + 1) / Real.log 2 + Cd + 1) * Real.log T := by
          have h_logπ_nn : 0 ≤ Real.log Real.pi :=
            Real.log_nonneg (by linarith [Real.pi_gt_three])
          have hlogT_ge_log2 : Real.log 2 ≤ Real.log T :=
            Real.log_le_log (by norm_num) hT
          -- log π / 2 ≤ (log π / log 2) * log T / 2 ≤ ((log π + Cd + 1) / log 2) * log T.
          -- (1/2) * Cd * log T ≤ Cd * log T.
          -- Sum ≤ ((log π + Cd + 1) / log 2 + Cd) * log T ≤ C * log T.
          have h_logπ_over_log2_le : Real.log Real.pi / 2 ≤
              (Real.log Real.pi / Real.log 2) * Real.log T / 2 := by
            have h1 : Real.log Real.pi = (Real.log Real.pi / Real.log 2) * Real.log 2 := by
              field_simp
            have h2 : (Real.log Real.pi / Real.log 2) * Real.log 2 ≤
                (Real.log Real.pi / Real.log 2) * Real.log T :=
              mul_le_mul_of_nonneg_left hlogT_ge_log2 (div_nonneg h_logπ_nn hlog2_pos.le)
            linarith
          have h_cd_half : (1/2 : ℝ) * (Cd * Real.log T) ≤ Cd * Real.log T := by
            have : 0 ≤ Cd * Real.log T := mul_nonneg hCd_pos.le (by linarith)
            linarith
          have h_bound_1 :
              Real.log Real.pi / 2 + 1 / 2 * (Cd * Real.log T) ≤
                (Real.log Real.pi / Real.log 2) * Real.log T / 2 + Cd * Real.log T := by
            linarith
          have h_bound_2 : (Real.log Real.pi / Real.log 2) * Real.log T / 2 +
              Cd * Real.log T ≤
              ((Real.log Real.pi + Cd + 1) / Real.log 2 + Cd + 1) * Real.log T := by
            have h_logT_nn : (0 : ℝ) ≤ Real.log T := hlogT_pos.le
            -- LHS = log T · (log π / (2 log 2) + Cd) ≤ log T · ((log π + Cd + 1)/log 2 + Cd + 1) = RHS
            have h_coeff :
                Real.log Real.pi / Real.log 2 / 2 + Cd ≤
                  (Real.log Real.pi + Cd + 1) / Real.log 2 + Cd + 1 := by
              have h_div_le : Real.log Real.pi / Real.log 2 / 2 ≤
                  Real.log Real.pi / Real.log 2 := by
                have : 0 ≤ Real.log Real.pi / Real.log 2 :=
                  div_nonneg h_logπ_nn hlog2_pos.le
                linarith
              have h_big :
                  Real.log Real.pi / Real.log 2 ≤
                    (Real.log Real.pi + Cd + 1) / Real.log 2 := by
                apply div_le_div_of_nonneg_right _ hlog2_pos.le
                linarith
              linarith
            calc (Real.log Real.pi / Real.log 2) * Real.log T / 2 + Cd * Real.log T
                = (Real.log Real.pi / Real.log 2 / 2 + Cd) * Real.log T := by ring
              _ ≤ ((Real.log Real.pi + Cd + 1) / Real.log 2 + Cd + 1) * Real.log T :=
                  mul_le_mul_of_nonneg_right h_coeff h_logT_nn
          linarith

end UniformGammaR
end ZD

end