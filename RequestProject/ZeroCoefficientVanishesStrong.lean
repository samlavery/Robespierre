import Mathlib
import RequestProject.WeilZeroOrthogonality
import RequestProject.PairTestMellinBetaTotalality
import RequestProject.CountableTsumMomentUniqueness

/-!
# Strong zero-coefficient vanishing via β-totality

This file packages the chain:

  per-β vanishing  →  ZeroMellinSeries vanishes on (0, ∞)  →
  exp series vanishes on ℂ  →  all coefficients vanish

Replaces the dropped `ZeroMellinSeriesUniqueness` Prop (which was false as
stated — no summability hypothesis on `a` made the antecedent vacuous via
`tsum_eq_zero_of_not_summable`).

The strong version requires:
- `Summable (ρ ↦ ‖a ρ.val‖)` — feeds `pairTestMellinBetaTotality_holds`
- An enumeration of `NontrivialZeros` that is bijective and locally finite in
  `‖ρ - 1‖`.
- Exponential summability of `a` along that enumeration — needed for
  `coeff_extraction_of_exp_sum_zero`.

Output: `∀ ρ ∈ NontrivialZeros, a ρ = 0`.
-/

open Complex Real MeasureTheory Set BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ZeroOrthogonality

/-- **Strong zero-coefficient vanishing from β-totality.**

Combines `pairTestMellinBetaTotality_holds` with
`coeff_extraction_of_exp_sum_zero` via an enumeration of the nontrivial
zeros and an exponential-summability hypothesis on `a`.

This is the unconditional replacement for the (false) dropped Prop
`ZeroMellinSeriesUniqueness`. -/
theorem ZeroCoefficientVanishes_strong
    (a : ℂ → ℂ)
    (h_summable_norm :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => ‖a ρ.val‖))
    (hsummable : ∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        a ρ.val * Contour.pairTestMellin β ρ.val))
    (hvanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0)
    (enum : ℕ → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (henum_inj : Function.Injective enum)
    (henum_surj : Function.Surjective enum)
    (h_loc_finite :
      ∀ R : ℝ, Set.Finite {n : ℕ | ‖(enum n).val - 1‖ ≤ R})
    (hc_exp_summable : ∀ r : ℝ, 0 < r →
      Summable (fun n => ‖a (enum n).val‖ *
        Real.exp (r * ‖(enum n).val - 1‖))) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0 := by
  -- Step 1: ZeroMellinSeries vanishes on (0, ∞).
  have h_zms : ∀ t : ℝ, 0 < t → ZeroMellinSeries a t = 0 :=
    pairTestMellinBetaTotality_holds a h_summable_norm hsummable hvanish
  -- Setup: ℕ-indexed coefficients and exponents.
  set b : ℕ → ℂ := fun n => a (enum n).val with hb_def
  set α : ℕ → ℂ := fun n => (enum n).val - 1 with hα_def
  -- α is injective.
  have h_α_inj : Function.Injective α := by
    intro i j hij
    have hval : (enum i).val = (enum j).val := by
      have hsub : (enum i).val - 1 = (enum j).val - 1 := hij
      linear_combination hsub
    exact henum_inj (Subtype.ext hval)
  -- Bounded real parts: re(ρ - 1) < 0 since re(ρ) ∈ (0, 1).
  have h_α_bdd_re : ∃ σ₀ : ℝ, ∀ n, (α n).re ≤ σ₀ := by
    refine ⟨0, fun n => ?_⟩
    have hρ := (enum n).property
    have hre : (enum n).val.re < 1 := hρ.2.1
    show ((enum n).val - 1).re ≤ 0
    simp [Complex.sub_re, Complex.one_re]
    linarith
  -- Bijection package for tsum reindexing.
  have henum_bij : Function.Bijective enum := ⟨henum_inj, henum_surj⟩
  let e : ℕ ≃ {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := Equiv.ofBijective enum henum_bij
  -- Step 2: Reindex ZeroMellinSeries via the enumeration.
  have h_zms_enum : ∀ t : ℝ, 0 < t →
      ∑' n : ℕ, b n * (t : ℂ) ^ ((enum n).val - 1) = 0 := by
    intro t ht
    have h1 := h_zms t ht
    unfold ZeroMellinSeries at h1
    have h2 : ∑' (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}),
        a ρ.val * (t : ℂ) ^ (ρ.val - 1) =
        ∑' n : ℕ, a (e n).val * (t : ℂ) ^ ((e n).val - 1) := by
      exact (e.tsum_eq _).symm
    rw [h2] at h1
    convert h1
  -- Step 3: Convert to exp form. For t = exp x with x : ℝ:
  --   (exp x : ℂ) ^ (ρ - 1) = exp ((ρ - 1) * x).
  have h_exp_real : ∀ x : ℝ,
      ∑' n : ℕ, b n * Complex.exp (α n * (x : ℂ)) = 0 := by
    intro x
    have hex_pos : (0 : ℝ) < Real.exp x := Real.exp_pos x
    have h1 := h_zms_enum (Real.exp x) hex_pos
    -- Each term: b n * (Real.exp x : ℂ)^((enum n).val - 1) = b n * exp(α n * x)
    have h_term : ∀ n : ℕ,
        b n * ((Real.exp x : ℝ) : ℂ) ^ ((enum n).val - 1) =
          b n * Complex.exp (α n * (x : ℂ)) := by
      intro n
      congr 1
      have hcpow_eq : ((Real.exp x : ℝ) : ℂ) ^ ((enum n).val - 1) =
          Complex.exp (((enum n).val - 1) * (x : ℂ)) := by
        have h1 : ((Real.exp x : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (Real.exp_pos x).ne'
        have him : ((x : ℝ) : ℂ).im = 0 := Complex.ofReal_im x
        rw [Complex.cpow_def_of_ne_zero h1,
          show ((Real.exp x : ℝ) : ℂ) = Complex.exp ((x : ℝ) : ℂ) by
            rw [Complex.ofReal_exp],
          Complex.log_exp (by rw [him]; exact neg_neg_iff_pos.mpr Real.pi_pos)
            (by rw [him]; exact Real.pi_pos.le)]
        ring_nf
      rw [hcpow_eq]
    have : (∑' n : ℕ, b n * ((Real.exp x : ℝ) : ℂ) ^ ((enum n).val - 1)) =
        ∑' n : ℕ, b n * Complex.exp (α n * (x : ℂ)) := by
      exact tsum_congr h_term
    rw [← this]
    convert h1
  -- Step 4: F(z) = ∑' n, b n * exp(α n * z) is entire. Vanishes on ℝ.
  -- Apply identity theorem to extend the vanishing to ℂ.
  have h_exp_complex : ∀ z : ℂ,
      HasSum (fun n => b n * Complex.exp (α n * z)) 0 := by
    -- The function F(z) = ∑' n, b n * exp(α n * z).
    set F : ℂ → ℂ := fun z => ∑' n, b n * Complex.exp (α n * z) with hF_def
    -- F is entire (uniform convergence on compacts via exp summability).
    have hF_analytic : AnalyticOnNhd ℂ F Set.univ := by
      refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
      intro c₀ _
      refine DifferentiableAt.differentiableWithinAt ?_
      -- Take open ball of radius 1 around c₀
      set R : ℝ := ‖c₀‖ + 1 with hR_def
      have hR_pos : 0 < R := by show 0 < ‖c₀‖ + 1; positivity
      set s : Set ℂ := Metric.ball c₀ 1 with hs_def
      have hs_open : IsOpen s := Metric.isOpen_ball
      have hs_mem : c₀ ∈ s := Metric.mem_ball_self one_pos
      have h_norm_le : ∀ z ∈ s, ‖z‖ ≤ R := by
        intro z hz
        have hd : dist z c₀ < 1 := hz
        have h_dist : ‖z - c₀‖ < 1 := by rwa [dist_eq_norm] at hd
        have h_tri : ‖z‖ ≤ ‖c₀‖ + ‖z - c₀‖ := norm_le_norm_add_norm_sub' z c₀
        show ‖z‖ ≤ ‖c₀‖ + 1
        linarith
      have h_diff_on : DifferentiableOn ℂ F s := by
        show DifferentiableOn ℂ (fun z => ∑' n, b n * Complex.exp (α n * z)) s
        apply Complex.differentiableOn_tsum_of_summable_norm
          (u := fun n => ‖b n‖ * Real.exp (R * ‖α n‖))
          (hc_exp_summable R hR_pos)
        · intro n
          apply DifferentiableOn.const_mul
          apply Differentiable.differentiableOn
          apply Differentiable.cexp
          exact (differentiable_const _).mul differentiable_id
        · exact hs_open
        · intro n z hz
          rw [norm_mul, Complex.norm_exp]
          have h_re_le : (α n * z).re ≤ ‖α n‖ * ‖z‖ := by
            calc (α n * z).re ≤ |((α n * z).re)| := le_abs_self _
              _ ≤ ‖α n * z‖ := Complex.abs_re_le_norm _
              _ = ‖α n‖ * ‖z‖ := norm_mul _ _
          have h_exp_le : Real.exp (α n * z).re ≤ Real.exp (‖α n‖ * R) := by
            apply Real.exp_le_exp.mpr
            calc (α n * z).re ≤ ‖α n‖ * ‖z‖ := h_re_le
              _ ≤ ‖α n‖ * R :=
                mul_le_mul_of_nonneg_left (h_norm_le z hz) (norm_nonneg _)
          have hbnn : 0 ≤ ‖b n‖ := norm_nonneg _
          calc ‖b n‖ * Real.exp (α n * z).re
              ≤ ‖b n‖ * Real.exp (‖α n‖ * R) :=
                mul_le_mul_of_nonneg_left h_exp_le hbnn
            _ = ‖b n‖ * Real.exp (R * ‖α n‖) := by rw [mul_comm ‖α n‖ R]
      exact (h_diff_on c₀ hs_mem).differentiableAt (hs_open.mem_nhds hs_mem)
    -- F vanishes on the real line.
    have hF_real : ∀ x : ℝ, F (x : ℂ) = 0 := by
      intro x
      have hsum_x : Summable (fun n => b n * Complex.exp (α n * (x : ℂ))) :=
        summable_cexp_mul α b hc_exp_summable (x : ℂ)
      have hF_x : F (x : ℂ) = ∑' n, b n * Complex.exp (α n * (x : ℂ)) := rfl
      rw [hF_x, h_exp_real x]
    -- F ≡ 0 on ℂ by identity theorem (vanishes on ℝ which has limit points).
    have hF_zero : ∀ z : ℂ, F z = 0 := by
      intro z
      have heq_real : ∀ c : ℝ, |c| < 1 → F c = (0 : ℂ) + (0 : ℂ) * c ^ 2 := by
        intro c _
        rw [hF_real c]; ring
      have := identity_theorem_extension F hF_analytic 0 0 heq_real z
      simpa using this
    intro z
    have hsum_z : Summable (fun n => b n * Complex.exp (α n * z)) :=
      summable_cexp_mul α b hc_exp_summable z
    have h_tsum_zero : ∑' n, b n * Complex.exp (α n * z) = 0 := hF_zero z
    exact h_tsum_zero ▸ hsum_z.hasSum
  -- Step 5: Apply coeff_extraction_of_exp_sum_zero.
  have h_zero : ∀ n, b n = 0 :=
    coeff_extraction_of_exp_sum_zero α b h_α_inj h_α_bdd_re h_loc_finite
      hc_exp_summable h_exp_complex
  -- Step 6: Extract every ρ via enum surjectivity.
  intro ρ hρ
  obtain ⟨n, hn⟩ := henum_surj ⟨ρ, hρ⟩
  have hρeq : ρ = (enum n).val := by
    have := congrArg Subtype.val hn
    simpa using this.symm
  rw [hρeq]
  exact h_zero n

end ZeroOrthogonality
end WeilPositivity
end ZD

end
#print axioms ZD.WeilPositivity.ZeroOrthogonality.ZeroCoefficientVanishes_strong
