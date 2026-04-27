import Mathlib
import RequestProject.DigammaVerticalBound

/-!
# σ-uniform digamma log bound on compact intervals

For `σ ∈ [a, b]` with `0 < a` and `|t| ≥ 1`, the digamma function satisfies
`‖ψ(σ + it)‖ ≤ C · log(1 + |t|)` with `C` independent of σ.

## Strategy

Let `M := max |a - 1| |b - 1|`. For σ ∈ [a,b], `|σ - 1| ≤ M`.
The proof follows `digamma_series_norm_bound` in `DigammaVerticalBound.lean` verbatim,
replacing every occurrence of `|σ - 1|` with `M` and adding `hM : |σ - 1| ≤ M`.

The uniform constant is
  `C_max := (M + 1) * (5 / log 2 + 1) + |γ| / log 2 + 1`
where `M = max |a - 1| |b - 1|` and `γ` is the Euler–Mascheroni constant.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Filter Topology Asymptotics Finset Real

set_option maxHeartbeats 800000

noncomputable section

/-! ## Helper: uniform digamma series bound with explicit M -/

/-- Intermediate step: split bound on digammaSeriesSum with parameter M ≥ |σ - 1|.
This follows the proof of `digamma_series_norm_bound` verbatim with M replacing |σ-1|. -/
private lemma digamma_series_uniform_aux (σ : ℝ) (hσ : 0 < σ) (M : ℝ) (hM_nn : 0 ≤ M)
    (hM : |σ - 1| ≤ M) (t : ℝ) (ht : 1 ≤ |t|) :
    ‖digammaSeriesSum ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      (M + 1) * (5 + Real.log (1 + |t|)) + |Real.eulerMascheroniConstant| := by
  -- Step 1: split digammaSeriesSum into γ part + head sum + tail sum
  have h_split : ‖digammaSeriesSum (σ + t * I)‖ ≤
      |Real.eulerMascheroniConstant| +
      (∑ k ∈ Finset.range (Nat.ceil |t|),
        ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * I + (k : ℂ)))‖) +
      (∑' k : ℕ,
        ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) -
          1 / (σ + t * I + (k + Nat.ceil |t| : ℂ)))‖) := by
    have h1 : ‖digammaSeriesSum (σ + t * I)‖ ≤
        |Real.eulerMascheroniConstant| +
        (∑ k ∈ Finset.range (Nat.ceil |t|),
          ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * I + (k : ℂ)))‖) +
        ‖∑' k : ℕ, (1 / ((k + Nat.ceil |t| : ℂ) + 1) -
          1 / (σ + t * I + (k + Nat.ceil |t| : ℂ)))‖ := by
      have h_eq : digammaSeriesSum (σ + t * I) =
          -(Real.eulerMascheroniConstant : ℂ) +
          (∑ k ∈ Finset.range (Nat.ceil |t|),
            (1 / ((k : ℂ) + 1) - 1 / (σ + t * I + (k : ℂ)))) +
          (∑' k : ℕ, (1 / ((k + Nat.ceil |t| : ℂ) + 1) -
            1 / (σ + t * I + (k + Nat.ceil |t| : ℂ)))) := by
        unfold digammaSeriesSum
        rw [← Summable.sum_add_tsum_nat_add]
        norm_num [add_assoc]
        congr! 1
        convert digamma_series_summable (σ + t * I)
          (by simpa [Complex.add_re, Complex.mul_re] using hσ) using 1
      rw [h_eq]
      refine' le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _) _) le_rfl)
      exact add_le_add (by norm_num) (norm_sum_le _ _)
    refine le_trans h1 ?_
    gcongr
    convert norm_tsum_le_tsum_norm _; norm_num
    have := digamma_series_summable (σ + t * I)
      (by simpa [Complex.add_re, Complex.mul_re] using hσ)
    convert this.norm.comp_injective (add_left_injective ⌈|t|⌉₊) using 2; norm_num
  -- Step 2: bound the head sum using M ≥ |σ-1|
  have h_head : ∑ k ∈ Finset.range (Nat.ceil |t|),
      ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * I + (k : ℂ)))‖ ≤
      (M + |t|) / |t| * (1 + Real.log (Nat.ceil |t|)) := by
    have h_term : ∀ k ∈ Finset.range (Nat.ceil |t|),
        ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * I + (k : ℂ)))‖ ≤
        (M + |t|) / ((k + 1) * |t|) := by
      intro k _
      -- First get the |σ-1| version from the existing lemma
      have h1 : ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * I + (k : ℂ)))‖ ≤
          (|σ - 1| + |t|) / ((↑k + 1) * Real.sqrt ((↑k + σ) ^ 2 + t ^ 2)) :=
        digamma_series_term_norm_le σ hσ t k
      -- Then weaken: |σ-1| ≤ M and sqrt(...) ≥ |t|
      have hsqrt_ge : |t| ≤ Real.sqrt ((↑k + σ) ^ 2 + t ^ 2) :=
        Real.abs_le_sqrt (by nlinarith)
      calc ‖(1 / ((k : ℂ) + 1) - 1 / (σ + t * I + (k : ℂ)))‖
          ≤ (|σ - 1| + |t|) / ((↑k + 1) * Real.sqrt ((↑k + σ) ^ 2 + t ^ 2)) := h1
        _ ≤ (M + |t|) / ((↑k + 1) * |t|) :=
            div_le_div₀ (by linarith [abs_nonneg t]) (by linarith [hM, abs_nonneg t])
                        (by positivity) (mul_le_mul_of_nonneg_left hsqrt_ge (by positivity))
    refine le_trans (Finset.sum_le_sum h_term) ?_
    convert mul_le_mul_of_nonneg_left
      (harmonic_le_one_add_log' ⌈|t|⌉₊ (Nat.ceil_pos.mpr (by positivity)))
      (show 0 ≤ (M + |t|) / |t| by positivity) using 1
    norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _]
  -- Step 3: bound the tail sum using M ≥ |σ-1|
  have h_tail : ∑' k : ℕ, ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) -
      1 / (σ + t * I + (k + Nat.ceil |t| : ℂ)))‖ ≤ (M + |t|) * (2 / |t|) := by
    -- First prove term-by-term bound with |σ-1| (same as original), then weaken to M
    have h_orig_bound : ∀ k : ℕ, ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) -
        1 / (σ + t * I + (k + Nat.ceil |t| : ℂ)))‖ ≤
        (|σ - 1| + |t|) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t| + σ)) := by
      intro k
      have h_term : ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) -
          1 / (σ + t * I + (k + Nat.ceil |t| : ℂ)))‖ =
          ‖(σ - 1 + t * Complex.I) /
            ((k + Nat.ceil |t| + 1) * (σ + t * Complex.I + (k + Nat.ceil |t|)))‖ := by
        rw [div_sub_div] <;> ring <;> norm_num [Complex.ext_iff, hσ.ne']
        · exact mod_cast by positivity
        · exact fun h => by linarith [abs_nonneg t]
      rw [h_term, norm_div]
      -- bound: ‖σ-1+t*I‖ / ‖denom‖ ≤ (|σ-1|+|t|) / denom_real
      have hnum : ‖(σ : ℂ) - 1 + ↑t * I‖ ≤ |σ - 1| + |t| := by
        norm_num [Complex.norm_def, Complex.normSq]
        rw [Real.sqrt_le_left (by positivity)]
        cases abs_cases (σ - 1) <;> cases abs_cases t <;> nlinarith
      have hdenom_pos : 0 < ((k : ℝ) + ⌈|t|⌉₊ + 1) * ((k : ℝ) + ⌈|t|⌉₊ + σ) := by positivity
      have hdenom_le : ((k : ℝ) + ⌈|t|⌉₊ + 1) * ((k : ℝ) + ⌈|t|⌉₊ + σ) ≤
          ‖((k : ℂ) + ↑⌈|t|⌉₊ + 1) * (↑σ + ↑t * I + ((k : ℂ) + ↑⌈|t|⌉₊))‖ := by
        norm_cast
        norm_num [Complex.norm_def, Complex.normSq]
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.le_sqrt_of_sq_le
          (by nlinarith [sq_nonneg (σ + (k + ⌈|t|⌉₊) - (k + ⌈|t|⌉₊ + 1)),
                         abs_mul_abs_self t])
      exact div_le_div₀ (by positivity) hnum (by positivity) hdenom_le
    have h_term_bound : ∀ k : ℕ, ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) -
        1 / (σ + t * I + (k + Nat.ceil |t| : ℂ)))‖ ≤
        (M + |t|) / ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t| + σ)) := fun k =>
      (h_orig_bound k).trans
        (div_le_div_of_nonneg_right (by linarith [hM, abs_nonneg t]) (by positivity))
    have h_tsum_le : ∑' k : ℕ, ‖(1 / ((k + Nat.ceil |t| : ℂ) + 1) -
        1 / (σ + t * I + (k + Nat.ceil |t| : ℂ)))‖ ≤
        (M + |t|) * (∑' k : ℕ, (1 : ℝ) /
          ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t| + σ))) := by
      rw [← tsum_mul_left]
      refine' Summable.tsum_le_tsum _ _ _
      · simpa only [mul_one_div] using h_term_bound
      · refine' Summable.of_nonneg_of_le (fun k => norm_nonneg _)
          (fun k => h_term_bound k) _
        exact Summable.mul_left _ <| Summable.of_nonneg_of_le
          (fun k => by positivity)
          (fun k => by
            rw [inv_eq_one_div, div_le_div_iff₀] <;> norm_num <;> ring <;>
            nlinarith [Nat.le_ceil (|t|), abs_nonneg t])
          (summable_nat_add_iff 1 |>.2 (Real.summable_one_div_nat_pow.2 one_lt_two))
      · refine' Summable.mul_left _ _
        exact Summable.of_nonneg_of_le
          (fun _ => by positivity)
          (fun n => by
            rw [div_le_div_iff₀] <;> norm_num <;> ring <;>
            nlinarith [Nat.le_ceil (|t|), abs_nonneg t])
          (summable_nat_add_iff 1 |>.2 (Real.summable_one_div_nat_pow.2 one_lt_two))
    refine le_trans h_tsum_le ?_
    gcongr
    have step1 : ∑' k : ℕ, (1 : ℝ) /
        ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t| + σ)) ≤
        ∑' k : ℕ, (1 : ℝ) /
          ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t|)) := by
      refine' Summable.tsum_le_tsum _ _ _
      · exact fun k => one_div_le_one_div_of_le (by positivity) (by nlinarith)
      · exact Summable.of_nonneg_of_le (fun k => by positivity)
          (fun k => by
            rw [div_le_div_iff₀] <;> norm_num <;> ring <;>
            nlinarith [Nat.le_ceil (|t|), abs_nonneg t])
          (summable_nat_add_iff 1 |>.2 (Real.summable_one_div_nat_pow.2 one_lt_two))
      · exact Summable.of_nonneg_of_le (fun k => by positivity)
          (fun k => by
            rw [div_le_div_iff₀] <;> norm_cast <;> ring <;>
            nlinarith [Nat.ceil_pos.mpr (show 0 < |t| by positivity)])
          (summable_nat_add_iff 1 |>.2 (Real.summable_one_div_nat_pow.mpr one_lt_two))
    have step2 : ∑' k : ℕ, (1 : ℝ) /
        ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t|)) ≤
        1 / (Nat.ceil |t|) := by
      have partial_le : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 : ℝ) /
          ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t|)) ≤
          1 / (Nat.ceil |t|) := by
        intro N
        have telescope : ∑ k ∈ Finset.range N, (1 : ℝ) /
            ((k + Nat.ceil |t| + 1) * (k + Nat.ceil |t|)) =
            1 / (Nat.ceil |t|) - 1 / (N + Nat.ceil |t|) := by
          induction N <;> simp_all +decide [Finset.sum_range_succ]
          field_simp; ring
        exact telescope ▸ sub_le_self _ (by positivity)
      exact le_of_tendsto_of_tendsto'
        (Summable.hasSum (by
          exact Summable.of_nonneg_of_le (fun _ => by positivity)
            (fun n => by
              rw [div_le_div_iff₀] <;> norm_cast <;> ring <;>
              nlinarith [Nat.ceil_pos.mpr (show 0 < |t| by positivity)])
            (summable_nat_add_iff 1 |>.2
              (Real.summable_one_div_nat_pow.mpr one_lt_two))) |>.tendsto_sum_nat)
        tendsto_const_nhds partial_le
    exact (step1.trans step2).trans
      (by rw [div_le_div_iff₀] <;> nlinarith [Nat.le_ceil (|t|), abs_nonneg t])
  -- Step 4: combine head + tail
  have h_combined : ‖digammaSeriesSum (σ + t * I)‖ ≤
      |Real.eulerMascheroniConstant| +
      (M + |t|) / |t| * (1 + Real.log (1 + |t|)) +
      (M + |t|) * (2 / |t|) := by
    refine le_trans h_split (add_le_add_three le_rfl (h_head.trans ?_) h_tail)
    gcongr
    linarith [Nat.ceil_lt_add_one (show 0 ≤ |t| by positivity)]
  -- Step 5: arithmetic finish: combined ≤ (M+1)*(5+log(1+|t|)) + |γ|
  refine le_trans h_combined ?_
  field_simp
  nlinarith [abs_nonneg Real.eulerMascheroniConstant, abs_nonneg t,
             Real.log_nonneg (show (1 : ℝ) ≤ 1 + |t| by linarith [abs_nonneg t]),
             mul_le_mul_of_nonneg_left ht (abs_nonneg t),
             mul_le_mul_of_nonneg_left ht hM_nn]

/-- Bound `|σ - 1| ≤ max |a - 1| |b - 1|` for `σ ∈ [a, b]`. -/
private lemma abs_sub_one_le_max_of_mem_Icc {a b σ : ℝ} (hσ : σ ∈ Set.Icc a b) :
    |σ - 1| ≤ max |a - 1| |b - 1| := by
  rcases abs_cases (σ - 1) with ⟨h_eq, _⟩ | ⟨h_eq, _⟩
  · -- σ ≥ 1: σ - 1 = |σ - 1| ≤ b - 1 = |b - 1| (since b ≥ σ ≥ 1)
    rw [h_eq]
    exact le_max_of_le_right (by
      rcases abs_cases (b - 1) with ⟨h_b, _⟩ | ⟨h_b, _⟩
      · rw [h_b]; linarith [hσ.2]
      · linarith [hσ.2, (abs_nonneg (b - 1))])
  · -- σ < 1: -(σ-1) = 1-σ ≤ 1-a = |a-1| (since a ≤ σ)
    rw [h_eq]
    refine le_max_of_le_left ?_
    rcases abs_cases (a - 1) with ⟨h_a, _⟩ | ⟨h_a, _⟩
    · linarith [hσ.1]
    · rw [h_a]; linarith [hσ.1]

/-- Uniform digamma series bound: `‖digammaSeriesSum(σ+it)‖ ≤ C_max · log(1+|t|)`
for σ ∈ [a,b], |t| ≥ 1, where C_max uses `M = max |a-1| |b-1|`. -/
private lemma digamma_series_norm_bound_compact_M
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (t : ℝ) (ht : 1 ≤ |t|) :
    ‖digammaSeriesSum ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      ((max |a - 1| |b - 1| + 1) * (5 / Real.log 2 + 1) +
        |Real.eulerMascheroniConstant| / Real.log 2 + 1) *
      Real.log (1 + |t|) := by
  set M := max |a - 1| |b - 1|
  have hσ_pos : 0 < σ := lt_of_lt_of_le ha hσ.1
  have hM_nn : 0 ≤ M := le_max_of_le_left (abs_nonneg _)
  have hM_bound : |σ - 1| ≤ M := abs_sub_one_le_max_of_mem_Icc hσ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_nn : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog_ge : Real.log 2 ≤ Real.log (1 + |t|) :=
    Real.log_le_log (by norm_num) (by linarith)
  -- Apply the auxiliary bound
  have h_aux := digamma_series_uniform_aux σ hσ_pos M hM_nn hM_bound t ht
  -- Convert: (M+1)*(5+L) + |γ| ≤ C_max * L where L = log(1+|t|), l2 = log 2.
  -- Proof: multiply both sides by l2 > 0 and use l2 ≤ L to bound (M+1)*5*l2 ≤ (M+1)*5*L
  -- and |γ|*l2 ≤ |γ|*L; the extra +l2*L on the RHS absorbs the margin.
  refine h_aux.trans ?_
  have hγ_abs := abs_nonneg Real.eulerMascheroniConstant
  have hlog_ge2 : Real.log 2 ≤ Real.log (1 + |t|) := hlog_ge
  -- Reduce to a polynomial inequality by clearing denominators via l2
  rw [← sub_nonneg]
  have hl2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have : ((M + 1) * (5 / Real.log 2 + 1) + |Real.eulerMascheroniConstant| / Real.log 2 + 1) *
      Real.log (1 + |t|) - ((M + 1) * (5 + Real.log (1 + |t|)) + |Real.eulerMascheroniConstant|) =
      ((M + 1) * 5 * Real.log (1 + |t|) + |Real.eulerMascheroniConstant| * Real.log (1 + |t|) +
        Real.log 2 * Real.log (1 + |t|) -
        (M + 1) * 5 * Real.log 2 -
        |Real.eulerMascheroniConstant| * Real.log 2) / Real.log 2 := by
    field_simp; ring
  rw [this]
  apply div_nonneg _ hlog2_pos.le
  have h1 : (M + 1) * 5 * Real.log 2 ≤ (M + 1) * 5 * Real.log (1 + |t|) :=
    mul_le_mul_of_nonneg_left hlog_ge2 (by linarith)
  have h2 : |Real.eulerMascheroniConstant| * Real.log 2 ≤
      |Real.eulerMascheroniConstant| * Real.log (1 + |t|) :=
    mul_le_mul_of_nonneg_left hlog_ge2 hγ_abs
  nlinarith [mul_nonneg hlog2_pos.le hlog_nn]

/-! ## Main theorem -/

/-- **σ-uniform digamma log bound on compact intervals**.

For `σ ∈ [a, b]` with `0 < a ≤ b` and `|t| ≥ 1`,
`‖Γ'(σ+it)/Γ(σ+it)‖ ≤ C · log(1 + |t|)` with `C` independent of σ. -/
theorem digamma_log_bound_uniform_compact (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ : ℝ, σ ∈ Set.Icc a b → ∀ t : ℝ, 1 ≤ |t| →
        ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
          Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * Real.log (1 + |t|) := by
  refine ⟨(max |a - 1| |b - 1| + 1) * (5 / Real.log 2 + 1) +
          |Real.eulerMascheroniConstant| / Real.log 2 + 1,
          by positivity, fun σ hσ t ht => ?_⟩
  have hσ_pos : 0 < σ := lt_of_lt_of_le ha hσ.1
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by simp; exact hσ_pos
  rw [deriv_div_eq_digamma _ hre, digamma_eq_series _ hre]
  exact digamma_series_norm_bound_compact_M a b ha hab σ hσ t ht

#print axioms digamma_log_bound_uniform_compact
