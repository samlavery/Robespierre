import Mathlib

/-!
# Countable Tsum Moment Uniqueness Principle
-/

open Complex Finset Filter Topology BigOperators

set_option maxHeartbeats 4000000

noncomputable section

/-- If `|c * β^k| ≤ C * q^k` for all `k` and `q < ‖β‖`, then `c = 0`. -/
lemma coeff_zero_of_pow_le {β c : ℂ} {C q : ℝ}
    (hq : q < ‖β‖) (hC : 0 ≤ C) (hq0 : 0 ≤ q)
    (h : ∀ k : ℕ, ‖c * β ^ k‖ ≤ C * q ^ k) : c = 0 := by
  have h_div : ∀ k : ℕ, ‖c‖ ≤ C * (q / ‖β‖) ^ k := by
    by_cases hβ : β = 0 <;> simp_all +decide [mul_div_cancel₀]
    · linarith
    · intro k; specialize h k; rw [div_pow, mul_div, le_div_iff₀] <;> first | positivity | linarith
  have h_lim : Filter.Tendsto (fun k : ℕ => (q / ‖β‖) ^ k) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hq0 (norm_nonneg _))
      (by rwa [div_lt_one (lt_of_le_of_lt hq0 hq)])
  exact norm_le_zero_iff.mp
    (le_of_tendsto_of_tendsto' tendsto_const_nhds (by simpa using h_lim.const_mul C) h_div)

/-- The coefficients are absolutely summable (from super-exponential decay). -/
lemma summable_norm_of_exp_decay {c : ℕ → ℂ} {α : ℕ → ℂ}
    (hexp : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖))) :
    Summable (fun n => ‖c n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by positivity)))
    (hexp 1 zero_lt_one)

/-- Exponential generating function vanishes. -/
lemma tsum_exp_eq_zero {c : ℕ → ℂ} {α : ℕ → ℂ}
    (hexp : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (hsum : ∀ k : ℕ, Summable (fun n => c n * (α n) ^ k))
    (hmom : ∀ k : ℕ, ∑' n, c n * (α n) ^ k = 0)
    (t : ℂ) : ∑' n, c n * Complex.exp (α n * t) = 0 := by
  have h_fubini : ∑' (n : ℕ), c n * Complex.exp (α n * t) = ∑' (n : ℕ), ∑' (k : ℕ), c n * (α n * t) ^ k / (Nat.factorial k) := by
    simp +decide [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div, mul_div_assoc, tsum_mul_left ];
  have h_fubini_comm : Summable (fun p : ℕ × ℕ => ‖c p.1 * (α p.1 * t) ^ p.2 / Nat.factorial p.2‖) := by
    have h1 : Summable (fun n => ‖c n‖ * Real.exp (‖α n‖ * ‖t‖)) := by
      by_cases ht : t = 0;
      · simpa [ ht ] using hsum 0 |> Summable.norm;
      · simpa [ mul_comm ] using hexp ‖t‖ ( norm_pos_iff.mpr ht );
    have h2 : ∀ n, Summable (fun k => ‖c n‖ * ‖α n‖ ^ k * ‖t‖ ^ k / Nat.factorial k) := by
      intro n; convert Summable.mul_left ( ‖c n‖ ) ( Real.summable_pow_div_factorial ( ‖α n‖ * ‖t‖ ) ) using 2; ring;
    rw [ summable_prod_of_nonneg ];
    · simp_all +decide [ mul_pow, mul_assoc, mul_div_assoc ];
      convert h1 using 2 ; rw [ Real.exp_eq_exp_ℝ ] ; rw [ NormedSpace.exp_eq_tsum_div ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left ];
      rw [ ← tsum_mul_left ] ; congr ; ext ; ring;
    · exact fun _ => norm_nonneg _;
  rw [ h_fubini, ← Summable.tsum_comm ];
  · convert tsum_zero;
    convert congr_arg ( fun x : ℂ => x * t ^ ‹_› / ( ‹_› : ℕ ).factorial ) ( hmom ‹_› ) using 1 <;> ring;
    rw [ ← tsum_mul_left ] ; exact tsum_congr fun _ => by ring;
  · exact .of_norm h_fubini_comm

/-- Beta moments vanish from F ≡ 0 via Laplace transform. -/
lemma beta_moments_zero' {c : ℕ → ℂ} {α : ℕ → ℂ} {σ₀ : ℝ}
    (hbdd : ∀ n, (α n).re ≤ σ₀)
    (hexp : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (hF : ∀ t : ℂ, ∑' n, c n * Complex.exp (α n * t) = 0)
    (σ : ℂ) (hσ : σ₀ < σ.re) (k : ℕ) :
    ∑' n, c n * (1 / (σ - α n)) ^ k = 0 := by
  sorry

/-- Layer peeling uniqueness. -/
lemma layer_peel_uniqueness
    {β c : ℕ → ℂ}
    (hβ_inj : Function.Injective β)
    (hβ_discrete : ∀ ε : ℝ, 0 < ε → {n : ℕ | ‖β n‖ ≥ ε}.Finite)
    (hc_summable : Summable (fun n => ‖c n‖))
    (hβ_sum : ∀ k : ℕ, Summable (fun n => c n * β n ^ k))
    (hβ_mom : ∀ k : ℕ, ∑' n, c n * β n ^ k = 0) :
    ∀ n, c n = 0 := by
  sorry

/-
**Countable Tsum Moment Uniqueness Principle.**
-/
theorem countable_tsum_moment_uniqueness_principle
    {α c : ℕ → ℂ}
    (hα : Function.Injective α)
    (hbdd : ∃ σ₀ : ℝ, ∀ n, (α n).re ≤ σ₀)
    (hdiscrete : ∀ R : ℝ, {n : ℕ | ‖α n‖ ≤ R}.Finite)
    (hexp : ∀ r : ℝ, 0 < r → Summable (fun n => ‖c n‖ * Real.exp (r * ‖α n‖)))
    (hsum : ∀ k : ℕ, Summable (fun n => c n * (α n) ^ k))
    (hmom : ∀ k : ℕ, ∑' n, c n * (α n) ^ k = 0) :
    ∀ i : ℕ, c i = 0 := by
  -- Set σ = σ₀ + 1 (as a complex number ↑σ₀ + 1). Set β n = 1/(σ - α n).
  obtain ⟨σ₀, hσ₀⟩ := hbdd
  set σ : ℂ := σ₀ + 1
  set β : ℕ → ℂ := fun n => 1 / (σ - α n);
  -- Apply layer_peel_uniqueness to conclude c = 0.
  apply layer_peel_uniqueness;
  any_goals exact β;
  · intro n m hnm; have := hα; aesop;
  · intro ε hε_pos
    have h_beta_bound : ∀ n, ‖β n‖ ≥ ε → ‖α n‖ ≤ ‖σ‖ + 1 / ε := by
      intro n hn
      have h_beta_bound : ‖σ - α n‖ ≤ 1 / ε := by
        simp +zetaDelta at *;
        exact le_trans ( by norm_num ) ( inv_anti₀ hε_pos hn );
      simpa using norm_sub_le ( σ ) ( σ - α n ) |> le_trans <| by simpa using h_beta_bound;
    exact Set.Finite.subset ( hdiscrete ( ‖σ‖ + 1 / ε ) ) fun n hn => h_beta_bound n hn;
  · exact summable_norm_of_exp_decay hexp;
  · intro k
    have h_summable : Summable (fun n => ‖c n‖ * ‖β n‖ ^ k) := by
      have h_summable : Summable (fun n => ‖c n‖) := by
        exact summable_norm_of_exp_decay hexp;
      have h_bound : ∀ n, ‖β n‖ ≤ 1 := by
        simp +zetaDelta at *;
        exact fun n => inv_le_one_of_one_le₀ <| Real.le_sqrt_of_sq_le <| by norm_num [ Complex.normSq ] ; nlinarith [ hσ₀ n ] ;
      exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( norm_nonneg _ ) ( pow_nonneg ( norm_nonneg _ ) _ ) ) ( fun n => mul_le_of_le_one_right ( norm_nonneg _ ) ( pow_le_one₀ ( norm_nonneg _ ) ( h_bound n ) ) ) h_summable;
    exact .of_norm <| by simpa using h_summable;
  · convert beta_moments_zero' ( fun n => hσ₀ n ) hexp _ σ _ using 1;
    · convert tsum_exp_eq_zero hexp hsum hmom using 1;
    · norm_num [ σ ]

end