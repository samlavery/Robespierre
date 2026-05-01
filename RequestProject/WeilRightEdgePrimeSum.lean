import Mathlib
import RequestProject.WeilPairIBP
import RequestProject.WeilPairTestContinuity
import RequestProject.WeilRightEdge
import RequestProject.WeilZeroSum

/-!
# Step D: Mellin inversion for `pairTestMellin β` on `Re s = σ > 0`

Building blocks needed for converting the right-edge contour integral of
`primeIntegrand β σ t` into the prime-power sum
`2π · ∑_n Λ(n) · pair_cosh_gauss_test β (n : ℝ)`. The full prime-sum identity
requires Fubini-swap of the LSeries against the Mellin transform; this file
delivers the unconditional pieces:

* `pairTestMellin_vertical_integrable` — `t ↦ pairTestMellin β (σ+tI)`
  integrable on ℝ via `pairTestMellin_global_quadratic_bound`
  + `integrable_inv_one_add_sq`.
* `mellinInv_pairTestMellin_eq` — for `x > 0`,
  `mellinInv σ (pairTestMellin β) x = (pair_cosh_gauss_test β x : ℂ)` via
  `mellinInv_mellin_eq`.
* `pairTestMellin_vertical_integral_at_pos` — the Mellin inversion integral
  rearranged to a direct integral evaluation for use in downstream Fubini.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD.WeilPositivity.Contour

-- ═══════════════════════════════════════════════════════════════════════════
-- § Vertical integrability of `pairTestMellin β` on Re s = σ > 0
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Vertical integrability of `pairTestMellin β` on `Re s = σ > 0`.**
Uses the global quadratic bound `‖pairTestMellin β (σ+tI)‖ ≤ K / (1+t²)` +
integrability of `(1+t²)⁻¹` on ℝ. -/
theorem pairTestMellin_vertical_integrable (β σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (pairTestMellin β) σ volume := by
  obtain ⟨K, hK_nn, h_bd⟩ := pairTestMellin_global_quadratic_bound β σ hσ
  unfold Complex.VerticalIntegrable
  have h_cont : Continuous
      (fun t : ℝ => pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) :=
    pairTestMellin_continuous_along_vertical β σ hσ
  have h_eq :
      (fun y : ℝ => pairTestMellin β ((σ : ℂ) + y * I)) =
      (fun t : ℝ => pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) := by
    funext t; rfl
  rw [h_eq]
  refine MeasureTheory.Integrable.mono
    ((integrable_inv_one_add_sq).const_mul K)
    h_cont.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun t => ?_
  have h_bd_t := h_bd t
  have h_rhs_nn : 0 ≤ K * (1 + t^2)⁻¹ := by
    have : 0 < 1 + t^2 := by positivity
    exact mul_nonneg hK_nn (inv_nonneg.mpr this.le)
  rw [Real.norm_of_nonneg h_rhs_nn]
  have hKdiv : K / (1 + t^2) = K * (1 + t^2)⁻¹ := by rw [div_eq_mul_inv]
  linarith [hKdiv ▸ h_bd_t]

#print axioms pairTestMellin_vertical_integrable

-- ═══════════════════════════════════════════════════════════════════════════
-- § Mellin inversion of `pairTestMellin β`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Mellin inversion for `pairTestMellin β`.** For `σ > 0` and `x > 0`,
`mellinInv σ (pairTestMellin β) x = (pair_cosh_gauss_test β x : ℂ)`. -/
theorem mellinInv_pairTestMellin_eq (β σ : ℝ) (hσ : 0 < σ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (pairTestMellin β) x = ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
  have h_conv : MellinConvergent
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) (σ : ℂ) :=
    mellinConvergent_pair β (show 0 < (σ : ℂ).re by simpa using hσ)
  have h_mellin_eq : mellin
      (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) = pairTestMellin β := by
    funext s
    rfl
  have h_vint : Complex.VerticalIntegrable
      (mellin (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ))) σ volume := by
    rw [h_mellin_eq]
    exact pairTestMellin_vertical_integrable β σ hσ
  have h_cont_ofReal :
      ContinuousAt (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) x := by
    apply Complex.continuous_ofReal.continuousAt.comp
    exact (pair_cosh_gauss_test_continuous β).continuousAt
  have := mellinInv_mellin_eq σ
    (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) hx h_conv h_vint h_cont_ofReal
  rw [h_mellin_eq] at this
  exact this

#print axioms mellinInv_pairTestMellin_eq

-- ═══════════════════════════════════════════════════════════════════════════
-- § Vertical integral explicit form at positive real `x`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Mellin inversion integral at positive `x`.** For `σ > 0` and `x > 0`,
`∫ t, (x : ℂ)^(-(σ+tI)) * pairTestMellin β (σ+tI) dt
  = 2π · (pair_cosh_gauss_test β x : ℂ)`.

This is the key building block for the right-edge → prime sum identity: at
`x = n` (a prime power), combined with LSeries expansion and Fubini swap,
this gives `∫ primeIntegrand β σ t dt
  = 2π · ∑_n Λ(n) · pair_cosh_gauss_test β (n : ℝ)`. -/
theorem pairTestMellin_vertical_integral_at_pos
    (β σ : ℝ) (hσ : 0 < σ) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, ((x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
              pairTestMellin β ((σ : ℂ) + (t : ℂ) * I) =
    (2 * Real.pi : ℂ) * ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
  have h_inv := mellinInv_pairTestMellin_eq β σ hσ hx
  -- h_inv: mellinInv σ (pairTestMellin β) x = ((pair_cosh_gauss_test β x : ℝ) : ℂ)
  -- mellinInv definition: (1/(2π)) • ∫ y : ℝ, (x : ℂ)^(-(σ+yI)) • pairTestMellin β (σ+yI)
  rw [mellinInv] at h_inv
  -- Convert inner smul (ℂ on ℂ) to multiplication.
  have h_inner :
      (fun y : ℝ => ((x : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) •
          pairTestMellin β ((σ : ℂ) + y * I)) =
      (fun t : ℝ => ((x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
          pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) := by
    funext t
    rfl
  rw [h_inner] at h_inv
  -- h_inv: (1/(2π)) • ∫ ... = (pair_cosh_gauss_test β x : ℂ)
  -- Apply Complex.real_smul to convert to multiplication.
  have h_inv' : (((1 / (2 * Real.pi) : ℝ)) : ℂ) *
      (∫ (t : ℝ), ((x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
        pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) =
      ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
    rw [← Complex.real_smul]; exact h_inv
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_mul : ((2 * Real.pi : ℝ) : ℂ) *
      ((((1 / (2 * Real.pi) : ℝ)) : ℂ) *
        (∫ (t : ℝ), ((x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
          pairTestMellin β ((σ : ℂ) + (t : ℂ) * I))) =
      ((2 * Real.pi : ℝ) : ℂ) * ((pair_cosh_gauss_test β x : ℝ) : ℂ) := by
    rw [h_inv']
  rw [← mul_assoc] at h_mul
  have h_cancel : ((2 * Real.pi : ℝ) : ℂ) * (((1 / (2 * Real.pi) : ℝ)) : ℂ) = 1 := by
    push_cast; field_simp
  rw [h_cancel, one_mul] at h_mul
  push_cast at h_mul
  linear_combination h_mul

#print axioms pairTestMellin_vertical_integral_at_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- § Per-term (per-n) integral value for the Fubini step
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Per-n term integral.** For `σ > 0` and `n ≥ 1`, the n-th Dirichlet term
of `LSeries_Λ` paired against `pairTestMellin β` evaluates to a concrete value:

```
∫ t, (Λ(n) : ℂ) · (n : ℂ)^(-(σ+tI)) · pairTestMellin β (σ+tI) dt
 = 2π · Λ(n) · pair_cosh_gauss_test β (n : ℝ).
```

This is the per-term input to the Fubini swap: summing this over `n ≥ 1` gives
(once Fubini is applied) the full right-edge prime-power sum identity. -/
theorem primeIntegrand_term_integral
    (β σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 1 ≤ n) :
    ∫ t : ℝ, (ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
              pairTestMellin β ((σ : ℂ) + (t : ℂ) * I) =
    (2 * Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_int := pairTestMellin_vertical_integral_at_pos β σ hσ hn_pos
  have h_reshape : (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
              pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) =
      (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
               pairTestMellin β ((σ : ℂ) + (t : ℂ) * I))) := by
    funext t; ring
  rw [h_reshape]
  rw [show (∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
               pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)))
        = (ArithmeticFunction.vonMangoldt n : ℂ) *
          ∫ (t : ℝ), (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
            pairTestMellin β ((σ : ℂ) + (t : ℂ) * I))
        from MeasureTheory.integral_const_mul _ _]
  have h_int_cast : (∫ (t : ℝ), ((n : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * I)) *
                      pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) =
                    2 * (Real.pi : ℂ) * ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
    have := h_int
    push_cast at this ⊢
    exact this
  rw [h_int_cast]
  ring

#print axioms primeIntegrand_term_integral

-- ═══════════════════════════════════════════════════════════════════════════
-- § Per-n integrability + summability of L¹ norms (Fubini prerequisites)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Per-n integrability** of `LSeries.term Λ (σ+tI) n · pairTestMellin β (σ+tI)`.
For σ > 1, the n-th term in the Dirichlet expansion, paired against
`pairTestMellin β`, is ℝ→ℂ integrable. -/
theorem lseries_term_pairTestMellin_integrable
    (β σ : ℝ) (hσ : 1 < σ) (n : ℕ) :
    MeasureTheory.Integrable
      (fun t : ℝ => LSeries.term
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n *
        pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have h_zero : (fun t : ℝ => LSeries.term
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) 0 *
        pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) = (fun _ : ℝ => (0 : ℂ)) := by
      funext t; rw [LSeries.term_zero]; ring
    rw [h_zero]
    exact (MeasureTheory.integrable_zero ℝ ℂ volume)
  · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hn_ne_C : (n : ℂ) ≠ 0 := by exact_mod_cast hn_ne
    -- Express the term explicitly: Λ(n) · (n : ℂ)^(-(σ+tI)).
    have h_term : ∀ t : ℝ,
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((σ : ℂ) + (t : ℂ) * I) n *
        pairTestMellin β ((σ : ℂ) + (t : ℂ) * I) =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
          pairTestMellin β ((σ : ℂ) + (t : ℂ) * I) := by
      intro t
      rw [LSeries.term_of_ne_zero hn_ne]
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
    rw [show (fun t : ℝ => LSeries.term
              (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n *
              pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) =
            (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
               pairTestMellin β ((σ : ℂ) + (t : ℂ) * I))) from by
      funext t; rw [h_term t]; ring]
    apply Integrable.const_mul
    -- Now integrability of `(n : ℂ)^(-(σ+tI)) · pairTestMellin β (σ+tI)`.
    -- |.| = n^(-σ) · ‖pairTestMellin β (σ+tI)‖ ≤ n^(-σ) · K/(1+t²).
    obtain ⟨K, hK_nn, h_pair_bd⟩ :=
      pairTestMellin_global_quadratic_bound β σ (by linarith)
    have hn_re_pos : (0 : ℝ) < ((n : ℂ)).re := by
      show (0 : ℝ) < (n : ℂ).re
      simp; exact_mod_cast hpos
    -- Continuity.
    have h_cpow_cont : Continuous
        (fun t : ℝ => ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))) := by
      have h_exp : Continuous (fun t : ℝ => -((σ : ℂ) + (t : ℂ) * I)) :=
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg
      have h_cpow_cont_z : Continuous (fun z : ℂ => (n : ℂ) ^ z) := by
        rw [continuous_iff_continuousAt]
        intro b
        exact continuousAt_const_cpow hn_ne_C
      exact h_cpow_cont_z.comp h_exp
    have h_pair_cont : Continuous
        (fun t : ℝ => pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) :=
      pairTestMellin_continuous_along_vertical β σ (by linarith)
    have h_prod_cont : Continuous
        (fun t : ℝ => ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
                       pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) :=
      h_cpow_cont.mul h_pair_cont
    -- Norm bound: ‖(n : ℂ)^(-(σ+tI))‖ = n^(-σ).
    have h_cpow_norm : ∀ t : ℝ,
        ‖((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))‖ = (n : ℝ) ^ (-σ) := by
      intro t
      rw [show -((σ : ℂ) + (t : ℂ) * I) = ((-σ : ℝ) : ℂ) + (-t : ℂ) * I from by
        push_cast; ring]
      rw [Complex.norm_natCast_cpow_of_pos hpos]
      simp
    -- Apply Integrable.mono with bound (n^(-σ) * K) * (1+t²)⁻¹.
    refine MeasureTheory.Integrable.mono
      ((integrable_inv_one_add_sq).const_mul ((n : ℝ) ^ (-σ) * K))
      h_prod_cont.aestronglyMeasurable ?_
    refine MeasureTheory.ae_of_all _ fun t => ?_
    rw [norm_mul, h_cpow_norm t]
    have h_pair_bd_t := h_pair_bd t
    have h_1plus_pos : 0 < 1 + t^2 := by positivity
    have h_nsnn : 0 ≤ (n : ℝ)^(-σ) := Real.rpow_nonneg hn_pos.le _
    have h_rhs_nn : 0 ≤ (n : ℝ)^(-σ) * K * (1 + t^2)⁻¹ :=
      mul_nonneg (mul_nonneg h_nsnn hK_nn) (inv_nonneg.mpr h_1plus_pos.le)
    rw [Real.norm_of_nonneg h_rhs_nn]
    calc (n : ℝ)^(-σ) * ‖pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ (n : ℝ)^(-σ) * (K / (1 + t^2)) :=
          mul_le_mul_of_nonneg_left h_pair_bd_t h_nsnn
      _ = (n : ℝ)^(-σ) * K * (1 + t^2)⁻¹ := by rw [div_eq_mul_inv]; ring

#print axioms lseries_term_pairTestMellin_integrable

/-- **L¹-norm bound per n.** For `σ > 1` and `n ≥ 1`,
`∫ ‖LSeries.term Λ (σ+tI) n · pairTestMellin β (σ+tI)‖ dt ≤ (Λ(n)/n^σ) · K · π`
where K is the global quadratic bound constant. -/
theorem lseries_term_pairTestMellin_L1_bounded
    (β σ : ℝ) (hσ : 1 < σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ∫ t : ℝ, ‖LSeries.term
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n *
        pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * M := by
  obtain ⟨K, hK_nn, h_pair_bd⟩ :=
    pairTestMellin_global_quadratic_bound β σ (by linarith)
  refine ⟨K * Real.pi, mul_nonneg hK_nn Real.pi_pos.le, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [LSeries.term_zero, zero_mul, norm_zero, MeasureTheory.integral_zero]
    simp [ArithmeticFunction.map_zero]
  · have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    -- ∫ ‖term · pair‖ ≤ (Λ(n) · n^(-σ)) · K · π.
    have h_bd_pt : ∀ t : ℝ,
        ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((σ : ℂ) + (t : ℂ) * I) n *
          pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * (K * (1 + t^2)⁻¹) := by
      intro t
      rw [LSeries.term_of_ne_zero hn_ne, norm_mul, norm_div]
      rw [show ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
            (ArithmeticFunction.vonMangoldt n : ℝ) from by
        rw [show ((ArithmeticFunction.vonMangoldt n : ℂ))
              = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) from rfl]
        rw [Complex.norm_real]
        exact abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [Complex.norm_natCast_cpow_of_pos hpos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      have h_pair_bd_t := h_pair_bd t
      have h_Lnn : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hns_pos : 0 < (n : ℝ)^σ := Real.rpow_pos_of_pos hn_pos _
      have hns_eq : (n : ℝ)^(-σ) = ((n : ℝ)^σ)⁻¹ :=
        Real.rpow_neg hn_pos.le _
      calc (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^σ *
            ‖pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^σ * (K / (1 + t^2)) := by
            apply mul_le_mul_of_nonneg_left h_pair_bd_t
            exact div_nonneg h_Lnn hns_pos.le
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * (K * (1 + t^2)⁻¹) := by
            rw [hns_eq, div_eq_mul_inv, div_eq_mul_inv]
    calc ∫ t : ℝ, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            ((σ : ℂ) + (t : ℂ) * I) n *
            pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) *
                   (K * (1 + t^2)⁻¹) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact MeasureTheory.ae_of_all _ fun t => norm_nonneg _
          · exact (integrable_inv_one_add_sq.const_mul K).const_mul _
          · exact MeasureTheory.ae_of_all _ h_bd_pt
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) *
          (K * ∫ t : ℝ, (1 + t^2)⁻¹) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * (K * Real.pi) := by
          rw [integral_univ_inv_one_add_sq]

#print axioms lseries_term_pairTestMellin_L1_bounded

-- ═══════════════════════════════════════════════════════════════════════════
-- § Final step-D theorem: right-edge integral = prime-power sum
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Step D final theorem: right-edge contour integral = prime-power sum.**
For `σ > 1`, the right-edge integral of `primeIntegrand β σ` evaluates to
`2π · ∑_n Λ(n) · pair_cosh_gauss_test β (n : ℝ)`.

Derivation:
1. `primeIntegrand β σ t = (∑_n LSeries.term Λ (σ+tI) n) · pairTestMellin β (σ+tI)`
   pointwise; distribute to `∑_n (term_n · pair)` via `tsum_mul_right`.
2. Fubini swap `∫ ∑ = ∑ ∫` via `MeasureTheory.integral_tsum_of_summable_integral_norm`
   using per-n integrability + summability of `∫ ‖term_n · pair‖`.
3. Per-n integral `∫ term_n · pair = 2π · Λ(n) · pair_cosh_gauss_test β n` via
   `primeIntegrand_term_integral` (for n ≥ 1; 0 for n = 0).
4. Collect `∑ 2π · Λ(n) · ... = 2π · ∑ Λ(n) · ...` via `tsum_mul_left`.

This is the **honest prime side** of Weil's explicit formula on Re s = σ > 1,
unconditional and axiom-clean. Does NOT close RH. -/
theorem primeIntegrand_integral_eq_prime_sum (β σ : ℝ) (hσ : 1 < σ) :
    ∫ t : ℝ, primeIntegrand β σ t =
      (2 * Real.pi : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
  -- Define F n t as the n-th term × pairTestMellin.
  set F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n *
      pairTestMellin β ((σ : ℂ) + (t : ℂ) * I) with hF_def
  -- Step 1: primeIntegrand β σ t = ∑' n, F n t.
  have h_pt : ∀ t : ℝ, primeIntegrand β σ t = ∑' n : ℕ, F n t := by
    intro t
    unfold primeIntegrand
    rw [show LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((σ : ℂ) + (t : ℂ) * I) =
            ∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              ((σ : ℂ) + (t : ℂ) * I) n from rfl]
    rw [tsum_mul_right]
  -- Step 2: Each F n integrable.
  have h_F_int : ∀ n : ℕ, MeasureTheory.Integrable (F n) := fun n =>
    lseries_term_pairTestMellin_integrable β σ hσ n
  -- Step 3: Summability of ∫ ‖F n‖.
  have h_F_L1_summ : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    obtain ⟨M, hM_nn, h_bd⟩ := lseries_term_pairTestMellin_L1_bounded β σ hσ
    have h_bound_summ : Summable (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * M) := by
      have h_div := summable_vonMangoldt_rpow σ hσ
      -- h_div : Summable (fun n => Λ(n) / (n)^σ)
      have h_eq : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ)^(-σ) * M) =
                  (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^σ * M) := by
        funext n
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp [ArithmeticFunction.map_zero]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
          rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv]
      rw [h_eq]
      exact h_div.mul_right M
    refine h_bound_summ.of_nonneg_of_le ?_ ?_
    · intro n; exact MeasureTheory.integral_nonneg (fun t => norm_nonneg _)
    · exact h_bd
  -- Step 4: Fubini application.
  have h_fubini : (∫ t : ℝ, ∑' n : ℕ, F n t) = ∑' n : ℕ, ∫ t : ℝ, F n t :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm h_F_int h_F_L1_summ).symm
  -- Step 5: Per-n integral.
  have h_per_n : ∀ n : ℕ, ∫ t : ℝ, F n t =
      (2 * Real.pi : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- n = 0: integrand is 0, Λ(0) = 0, everything is 0.
      subst h0
      simp only [hF_def, LSeries.term_zero, zero_mul]
      rw [MeasureTheory.integral_zero]
      simp [ArithmeticFunction.map_zero]
    · -- n ≥ 1: use primeIntegrand_term_integral.
      have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have h_term_eq : ∀ t : ℝ,
          F n t = (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
            pairTestMellin β ((σ : ℂ) + (t : ℂ) * I) := by
        intro t
        simp only [hF_def]
        rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, ← Complex.cpow_neg]
      rw [show (fun t : ℝ => F n t) = (fun t : ℝ =>
              (ArithmeticFunction.vonMangoldt n : ℂ) *
                ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) *
                pairTestMellin β ((σ : ℂ) + (t : ℂ) * I)) from by
        funext t; exact h_term_eq t]
      have h := primeIntegrand_term_integral β σ (by linarith) n hpos
      rw [h]
  -- Assembly.
  calc ∫ t : ℝ, primeIntegrand β σ t
      = ∫ t : ℝ, ∑' n : ℕ, F n t := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        exact h_pt t
    _ = ∑' n : ℕ, ∫ t : ℝ, F n t := h_fubini
    _ = ∑' n : ℕ, (2 * Real.pi : ℂ) *
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
         ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)) := by
      apply tsum_congr
      intro n
      rw [h_per_n n]; ring
    _ = (2 * Real.pi : ℂ) * ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
         ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) := by
      rw [← tsum_mul_left]

#print axioms primeIntegrand_integral_eq_prime_sum

end ZD.WeilPositivity.Contour

end
