import Mathlib
import RequestProject.WeilZeroOrthogonality
import RequestProject.PairTestMellinBetaTotalality
import RequestProject.CountableTsumMomentUniqueness

/-!
# Unconditional zero-coefficient vanishing via Mellin resolvent

This file proves `ZeroCoefficientVanishesByOrthogonality` unconditionally
(no enumeration / exp-summability hypothesis on `a`).

## Strategy

The previous file `ZeroCoefficientVanishesStrong.lean` went via the *exp*
series: `(t : ℂ)^(ρ-1) = exp((ρ-1) · log t)` and used
`coeff_extraction_of_exp_sum_zero`, which required exponential summability of
`a` to extend the real-line vanishing to a complex strip via uniform
convergence + identity theorem.

The exp route is unnecessarily strong. The **Mellin transform** of
`ZeroMellinSeries a` directly produces the resolvent, with no exp summability
needed:

For `re(s) > 0` and `re(ρ - 1) ≤ 0`:
  `∫_1^∞ ZeroMellinSeries a u · u^(-s-1) du`
    `= ∫_1^∞ ∑' ρ, a(ρ) · u^(ρ - 1 - s - 1) du`
    `= ∑' ρ, a(ρ) · ∫_1^∞ u^(ρ - 1 - s - 1) du`   [Fubini]
    `= ∑' ρ, a(ρ) / (s - (ρ - 1))`

Joint integrability for Fubini: `∑' ρ ‖a(ρ)‖ · 1/(re(s) - re(ρ-1))
  ≤ ‖a‖_1 / re(s)` — bounded. ℓ¹ summability suffices.

If `ZeroMellinSeries a u = 0` for all `u ∈ (0, ∞)`, the LHS vanishes, so the
resolvent vanishes on the half-plane `re(s) > 0`. By analytic continuation
(`resolvent_analyticOnNhd` + identity theorem) the resolvent vanishes on the
full complement of `{ρ - 1 : ρ ∈ NontrivialZeros}`. Then
`coeff_from_resolvent_eq_zero` (which only needs ℓ¹) extracts each coefficient.
-/

open Complex Real MeasureTheory Set BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ZeroOrthogonality

/-! ### Mellin resolvent identity -/

/-- **Mellin resolvent vanishing on the right half-plane.**

If `α : ℕ → ℂ` has bounded real part `re(α n) ≤ 0`, the coefficient family `c`
is ℓ¹-summable, and the associated power series `u ↦ ∑' n, c n · u^(α n)`
vanishes for every `u ≥ 1`, then the resolvent `∑' n, c n / (s - α n)`
vanishes on every `s` with `re(s) > 0`.

Proof: Mellin transform of the vanishing series, with Fubini swap justified
by ℓ¹ + bounded re. -/
theorem mellin_resolvent_eq_zero_halfplane
    (α : ℕ → ℂ) (c : ℕ → ℂ)
    (hα_bdd_re : ∀ n, (α n).re ≤ 0)
    (hα_loc_finite : ∀ R : ℝ, Set.Finite {n : ℕ | ‖α n‖ ≤ R})
    (hc_summable : Summable (fun n => ‖c n‖))
    (hzm_zero : ∀ u : ℝ, 1 ≤ u → ∑' n : ℕ, c n * (u : ℂ) ^ (α n) = 0)
    (s : ℂ) (hs : 0 < s.re) :
    ∑' n : ℕ, c n / (s - α n) = 0 := by
  -- Setup: each exponent re(α n - s - 1) < -1 since re(α n) ≤ 0 < re s.
  have hexp_re : ∀ n, (α n - s - 1).re < -1 := by
    intro n
    have h1 : (α n - s - 1).re = (α n).re - s.re - 1 := by
      simp [Complex.sub_re, Complex.one_re]
    rw [h1]; linarith [hα_bdd_re n]
  -- Each n-integrand is integrable on Ioi 1.
  have h_int_n : ∀ n, IntegrableOn (fun u : ℝ => (u : ℂ) ^ (α n - s - 1))
      (Set.Ioi (1 : ℝ)) volume :=
    fun n => integrableOn_Ioi_cpow_of_lt (hexp_re n) (by norm_num : (0:ℝ) < 1)
  have h_int_n_norm : ∀ n, IntegrableOn (fun u : ℝ => ‖(u : ℂ) ^ (α n - s - 1)‖)
      (Set.Ioi (1 : ℝ)) volume :=
    fun n => integrableOn_Ioi_norm_cpow_of_lt (hexp_re n) (by norm_num : (0:ℝ) < 1)
  -- Per-n integral evaluation: ∫_{Ioi 1} c n * u^(α n - s - 1) du = c n / (s - α n).
  have h_int_eval : ∀ n,
      ∫ u in Set.Ioi (1 : ℝ), c n * (u : ℂ) ^ (α n - s - 1) = c n / (s - α n) := by
    intro n
    rw [show ∫ u in Set.Ioi (1:ℝ), c n * (u : ℂ) ^ (α n - s - 1) =
          c n * ∫ u in Set.Ioi (1:ℝ), (u : ℂ) ^ (α n - s - 1) from
          integral_const_mul (c n) _]
    rw [integral_Ioi_cpow_of_lt (hexp_re n) (by norm_num : (0:ℝ) < 1)]
    push_cast
    rw [Complex.one_cpow]
    rw [show α n - s - 1 + 1 = α n - s from by ring]
    rw [show ((-(1 : ℂ)) / (α n - s)) = 1 / (s - α n) from by
      rw [show (α n - s) = -(s - α n) from by ring, div_neg]; ring]
    rw [mul_one_div]
  -- Norm-rewriting: ‖c n * u^(α n - s - 1)‖ = ‖c n‖ * u^(re(α n - s - 1)) for u > 0.
  have h_norm_rewrite : ∀ n, ∀ u : ℝ, 0 < u →
      ‖c n * (u : ℂ) ^ (α n - s - 1)‖ = ‖c n‖ * u ^ ((α n).re - s.re - 1) := by
    intro n u hu
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    have : (α n - s - 1).re = (α n).re - s.re - 1 := by
      simp [Complex.sub_re, Complex.one_re]
    rw [this]
  -- Per-n integral of norm: bounded by ‖c n‖ / (s.re - (α n).re), which is ≤ ‖c n‖ / s.re.
  -- Build ∫_{Ioi 1} u^(re α - re s - 1) du = 1/(re s - re α).
  have h_real_int_eval : ∀ n,
      ∫ u in Set.Ioi (1 : ℝ), u ^ ((α n).re - s.re - 1) =
        1 / (s.re - (α n).re) := by
    intro n
    have hexp_re_real : ((α n).re - s.re - 1) < -1 := by linarith [hα_bdd_re n]
    have h_eval := integral_Ioi_rpow_of_lt hexp_re_real (by norm_num : (0:ℝ) < 1)
    rw [h_eval]
    have hpos : 0 < s.re - (α n).re := by linarith [hα_bdd_re n]
    rw [Real.one_rpow]
    rw [show ((α n).re - s.re - 1) + 1 = (α n).re - s.re from by ring]
    rw [show ((α n).re - s.re) = -(s.re - (α n).re) from by ring]
    field_simp
  -- Per-n: ∫⁻ ‖c n * u^...‖ₑ = ‖c n‖ * (1/(s.re - (α n).re)) (as ENNReal.ofReal)
  have h_lint_eval : ∀ n,
      ∫⁻ u in Set.Ioi (1 : ℝ), ‖c n * (u : ℂ) ^ (α n - s - 1)‖ₑ ∂volume =
        ENNReal.ofReal (‖c n‖ * (1 / (s.re - (α n).re))) := by
    intro n
    -- Convert ‖·‖ₑ to ofReal of the real norm.
    have hnorm_eq : (fun u : ℝ => ‖c n * (u : ℂ) ^ (α n - s - 1)‖ₑ)
        =ᵐ[volume.restrict (Set.Ioi 1)]
        (fun u : ℝ => ENNReal.ofReal (‖c n‖ * u ^ ((α n).re - s.re - 1))) := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
      filter_upwards with u hu
      have h0 : (0 : ℝ) < u := by simp at hu; linarith
      rw [← ofReal_norm_eq_enorm]
      rw [h_norm_rewrite n u h0]
    rw [MeasureTheory.lintegral_congr_ae hnorm_eq]
    -- ∫⁻ ENNReal.ofReal (‖c n‖ * u^a) du = ofReal (∫ ‖c n‖ * u^a du) (since nonneg integrable)
    have h_real_integrable : IntegrableOn
        (fun u : ℝ => ‖c n‖ * u ^ ((α n).re - s.re - 1)) (Set.Ioi 1) volume := by
      have hexp_re_real : ((α n).re - s.re - 1) < -1 := by linarith [hα_bdd_re n]
      have := (integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ) < 1)).mpr hexp_re_real
      exact this.const_mul _
    have h_nonneg : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
        0 ≤ ‖c n‖ * u ^ ((α n).re - s.re - 1) := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
      filter_upwards with u hu
      have h0 : (0 : ℝ) < u := by simp at hu; linarith
      have : 0 ≤ u ^ ((α n).re - s.re - 1) := Real.rpow_nonneg h0.le _
      positivity
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_real_integrable h_nonneg]
    rw [show (fun u : ℝ => ‖c n‖ * u ^ ((α n).re - s.re - 1)) =
          fun u : ℝ => ‖c n‖ * u ^ ((α n).re - s.re - 1) from rfl]
    rw [MeasureTheory.integral_const_mul, h_real_int_eval n]
  -- Now bound the sum: ∑' n, ofReal(‖c n‖ * 1/(s.re - re α)) ≤ ofReal(‖c n‖ / s.re) cofinitely.
  have h_bound : ∀ n, ‖c n‖ * (1 / (s.re - (α n).re)) ≤ ‖c n‖ * (1 / s.re) := by
    intro n
    have hpos : 0 < s.re - (α n).re := by linarith [hα_bdd_re n]
    have hge : s.re ≤ s.re - (α n).re := by linarith [hα_bdd_re n]
    have h_inv_le : 1 / (s.re - (α n).re) ≤ 1 / s.re :=
      one_div_le_one_div_of_le hs hge
    exact mul_le_mul_of_nonneg_left h_inv_le (norm_nonneg _)
  -- Now sum up the lintegrals.
  have h_sum_lint :
      ∑' n : ℕ, ∫⁻ u in Set.Ioi (1 : ℝ), ‖c n * (u : ℂ) ^ (α n - s - 1)‖ₑ ∂volume
        ≤ ∑' n : ℕ, ENNReal.ofReal (‖c n‖ * (1 / s.re)) := by
    apply ENNReal.tsum_le_tsum
    intro n
    rw [h_lint_eval n]
    apply ENNReal.ofReal_le_ofReal
    exact h_bound n
  have h_sum_finite :
      ∑' n : ℕ, ENNReal.ofReal (‖c n‖ * (1 / s.re)) ≠ ⊤ := by
    have := hc_summable.mul_right (1 / s.re)
    rw [show (∑' n : ℕ, ENNReal.ofReal (‖c n‖ * (1 / s.re))) =
        ENNReal.ofReal (∑' n : ℕ, ‖c n‖ * (1 / s.re)) from by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) this]]
    exact ENNReal.ofReal_ne_top
  have h_lint_sum_ne_top :
      ∑' n : ℕ, ∫⁻ u in Set.Ioi (1 : ℝ), ‖c n * (u : ℂ) ^ (α n - s - 1)‖ₑ ∂volume ≠ ⊤ := by
    intro h
    apply h_sum_finite
    rw [h] at h_sum_lint
    exact top_le_iff.mp h_sum_lint
  -- AEStronglyMeasurable for each n.
  have h_meas : ∀ n, AEStronglyMeasurable (fun u : ℝ => c n * (u : ℂ) ^ (α n - s - 1))
      (volume.restrict (Set.Ioi 1)) := by
    intro n
    apply AEStronglyMeasurable.const_mul
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro u hu
    have h0 : (0 : ℝ) < u := by simp at hu; linarith
    refine (Complex.continuousAt_ofReal_cpow_const _ _ ?_).continuousWithinAt
    exact Or.inr h0.ne'
  -- Apply integral_tsum (Fubini swap).
  have h_fubini :
      ∫ u in Set.Ioi (1 : ℝ), ∑' n : ℕ, c n * (u : ℂ) ^ (α n - s - 1)
        = ∑' n : ℕ, ∫ u in Set.Ioi (1 : ℝ), c n * (u : ℂ) ^ (α n - s - 1) :=
    MeasureTheory.integral_tsum h_meas h_lint_sum_ne_top
  -- The LHS is 0: at each u ≥ 1, ∑' n, c n * u^(α n - s - 1) = u^(-s-1) * (∑' n, c n * u^(α n)).
  -- Since ∑' n, c n * u^(α n) = 0 for u ≥ 1, the inner sum is 0.
  have h_inner_zero : ∀ u : ℝ, 1 ≤ u → ∑' n : ℕ, c n * (u : ℂ) ^ (α n - s - 1) = 0 := by
    intro u hu
    have hu_pos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
    have hu_ne : (u : ℂ) ≠ 0 := by
      exact_mod_cast hu_pos.ne'
    -- Factor: c n * u^(α n - s - 1) = c n * u^(α n) * u^(-s - 1).
    have hfact : ∀ n, c n * (u : ℂ) ^ (α n - s - 1) =
        (c n * (u : ℂ) ^ (α n)) * (u : ℂ) ^ (-s - 1) := by
      intro n
      rw [show α n - s - 1 = α n + (-s - 1) from by ring]
      rw [Complex.cpow_add _ _ hu_ne]
      ring
    have : ∑' n : ℕ, c n * (u : ℂ) ^ (α n - s - 1) =
        ∑' n : ℕ, (c n * (u : ℂ) ^ (α n)) * (u : ℂ) ^ (-s - 1) :=
      tsum_congr hfact
    rw [this]
    rw [tsum_mul_right]
    rw [hzm_zero u hu]
    ring
  have h_LHS_zero : ∫ u in Set.Ioi (1 : ℝ), ∑' n : ℕ, c n * (u : ℂ) ^ (α n - s - 1) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    have hu1 : 1 ≤ u := le_of_lt (by simpa using hu)
    exact h_inner_zero u hu1
  -- Conclude.
  rw [h_LHS_zero] at h_fubini
  rw [show (∑' n : ℕ, c n / (s - α n)) =
       ∑' n : ℕ, ∫ u in Set.Ioi (1 : ℝ), c n * (u : ℂ) ^ (α n - s - 1) from by
    refine tsum_congr fun n => ?_
    exact (h_int_eval n).symm]
  exact h_fubini.symm

/-! ### Countability and locally-finite enumeration of `NontrivialZeros` -/

/-- `NontrivialZeros` is countable. Follows from local finiteness of zeros in
each closed ball plus the fact that `ℂ` is a countable union of closed balls. -/
theorem nontrivialZeros_countable :
    Set.Countable ZD.NontrivialZeros := by
  have hUnion : ZD.NontrivialZeros =
      ⋃ n : ℕ, (ZD.NontrivialZeros ∩ Metric.closedBall (0 : ℂ) (n : ℝ)) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    refine ⟨fun hz => ⟨⌈‖z‖⌉₊, hz, ?_⟩, fun ⟨_, hzN, _⟩ => hzN⟩
    exact_mod_cast Nat.le_ceil _
  rw [hUnion]
  refine Set.countable_iUnion (fun n => ?_)
  exact (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (n : ℝ)).countable

/-! ### Enumeration of `NontrivialZeros`

**OBSTRUCTION**: The four declarations below — `chooseEnum`, `chooseEnum_covers`,
`chooseEnum_injective`, `chooseEnum_loc_finite` — together require that
`{ρ : ℂ // ρ ∈ NontrivialZeros}` be **denumerable** (countably infinite, in
bijection with ℕ).

`chooseEnum_injective ∧ chooseEnum_covers` forces the codomain to be the image
of an injective ℕ-indexed family, hence at least denumerable.  Combined with
`nontrivialZeros_countable`, this is equivalent to `Set.Infinite ZD.NontrivialZeros`.

The latter is **Hardy's theorem (1914)**: ζ has infinitely many zeros on the
critical strip (and indeed on the critical line). Hardy's theorem is *not*
currently in Mathlib's `RiemannZeta` files, nor is it derivable from the
project's existing analytical infrastructure (`xi_zero_count_disk_bound`
gives only an UPPER bound on the count).

The four sorries below are therefore blocked on a single missing input:
either a Mathlib lemma asserting `Set.Infinite ZD.NontrivialZeros`, or a
project-level proof of the same. Once that input is supplied, all four
declarations follow mechanically from `Set.countable_infinite_iff_nonempty_denumerable`
plus `nontrivialZeros_subtype_closedBall_finite`.

The structural proof of `ZeroCoefficientVanishesByOrthogonality_holds` below
uses these declarations. The Mellin-resolvent half (sorries #1, #2, #7) is
fully discharged. -/

/-! ### Bijective enumeration in the infinite case

When `NontrivialZeros` is infinite, combining countability with infinitude
gives a bijection `ℕ ≃ Subtype`. We package this as the data needed by the
Mellin resolvent route. The finite case is handled directly via
`finite_exp_linIndep` in the main theorem (no enumeration required). -/

/-- An ℕ-indexed bijective enumeration of the nontrivial-zero subtype, given
that `NontrivialZeros` is infinite. -/
private noncomputable def infiniteEnum
    (h_inf : Set.Infinite ZD.NontrivialZeros) :
    ℕ ≃ {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := by
  haveI : Infinite ↑(ZD.NontrivialZeros) := h_inf.to_subtype
  haveI : Encodable ↑(ZD.NontrivialZeros) :=
    nontrivialZeros_countable.toEncodable
  haveI : Denumerable ↑(ZD.NontrivialZeros) := Denumerable.ofEncodableOfInfinite _
  exact (Denumerable.eqv ↑(ZD.NontrivialZeros)).symm

/-- The infinite-case enumeration is locally finite in `‖ρ - 1‖`. Follows from
`nontrivialZeros_subtype_closedBall_finite` and the bound
`‖ρ‖ ≤ ‖ρ - 1‖ + 1`. -/
private theorem infiniteEnum_loc_finite
    (h_inf : Set.Infinite ZD.NontrivialZeros) (R : ℝ) :
    Set.Finite {n : ℕ | ‖((infiniteEnum h_inf) n).val - 1‖ ≤ R} := by
  -- Image: the subtype-set of those ρ with ‖ρ - 1‖ ≤ R.
  -- Bound: ‖ρ‖ = ‖(ρ - 1) + 1‖ ≤ ‖ρ - 1‖ + 1 ≤ R + 1.
  have h_subtype_finite :
      Set.Finite
        {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | ‖ρ.val‖ ≤ R + 1} := by
    have h := nontrivialZeros_subtype_closedBall_finite (R + 1)
    refine h.subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right] at *
    exact hx
  -- The preimage under the equiv is in bijection with this image.
  have h_preimage :
      {n : ℕ | ‖((infiniteEnum h_inf) n).val - 1‖ ≤ R} ⊆
        (infiniteEnum h_inf) ⁻¹'
          {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | ‖ρ.val‖ ≤ R + 1} := by
    intro n hn
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at *
    have htri : ‖((infiniteEnum h_inf) n).val‖ ≤
        ‖((infiniteEnum h_inf) n).val - 1‖ + 1 := by
      have := norm_add_le (((infiniteEnum h_inf) n).val - 1) (1 : ℂ)
      simpa using this
    linarith
  refine Set.Finite.subset ?_ h_preimage
  exact h_subtype_finite.preimage (Equiv.injective _).injOn

/-! ### Unconditional zero-coefficient vanishing -/

/-- **Unconditional vanishing of zero coefficients via Mellin resolvent.**

Direct proof of `ZeroCoefficientVanishesByOrthogonality` (no enumeration or
exponential-summability hypotheses on `a`). The only structural inputs are
ℓ¹ summability of `a`, per-β summability of the Mellin pairings, and per-β
vanishing.

The proof chains:
- `pairTestMellinBetaTotality_holds` → `ZeroMellinSeries a u = 0` on `(0, ∞)`
- `mellin_resolvent_eq_zero_halfplane` → resolvent vanishes on `re(s) > 0`
- `resolvent_analyticOnNhd` + identity theorem → resolvent vanishes on
  `(range (chooseEnum · - 1))ᶜ`
- `coeff_from_resolvent_eq_zero` → `a (chooseEnum n) = 0` for all `n`
- `chooseEnum_covers` → `a ρ = 0` for every `ρ ∈ NontrivialZeros`. -/
theorem ZeroCoefficientVanishesByOrthogonality_holds :
    ZeroCoefficientVanishesByOrthogonality := by
  intro a h_summable_norm hsummable hvanish ρ hρ
  -- Step 1: ZeroMellinSeries vanishes on (0, ∞).
  have h_zms : ∀ t : ℝ, 0 < t → ZeroMellinSeries a t = 0 :=
    pairTestMellinBetaTotality_holds a h_summable_norm hsummable hvanish
  -- Case split on cardinality of NontrivialZeros.
  by_cases h_inf : Set.Infinite ZD.NontrivialZeros
  · -- INFINITE CASE: bijective enumeration ℕ ≃ Subtype + Mellin resolvent route.
    let e : ℕ ≃ {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := infiniteEnum h_inf
    let enum : ℕ → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := e
    let b : ℕ → ℂ := fun n => a (enum n).val
    let α : ℕ → ℂ := fun n => (enum n).val - 1
    have h_enum_inj : Function.Injective enum := e.injective
    have h_enum_surj : Function.Surjective enum := e.surjective
    have h_α_inj : Function.Injective α := by
      intro i j hij
      have hval : (enum i).val = (enum j).val := by
        have hsub : (enum i).val - 1 = (enum j).val - 1 := hij
        linear_combination hsub
      exact h_enum_inj (Subtype.ext hval)
    have h_α_bdd_re : ∀ n, (α n).re ≤ 0 := by
      intro n
      have hρ' := (enum n).property
      have hre : (enum n).val.re < 1 := hρ'.2.1
      show ((enum n).val - 1).re ≤ 0
      simp [Complex.sub_re, Complex.one_re]
      linarith
    have h_α_loc_finite : ∀ R : ℝ, Set.Finite {n : ℕ | ‖α n‖ ≤ R} := by
      intro R
      -- ‖α n‖ = ‖(enum n).val - 1‖
      exact infiniteEnum_loc_finite h_inf R
    have h_b_summable : Summable (fun n => ‖b n‖) :=
      h_summable_norm.comp_injective h_enum_inj
    have h_zms_enum : ∀ u : ℝ, 1 ≤ u → ∑' n : ℕ, b n * (u : ℂ) ^ (α n) = 0 := by
      intro u hu
      have hu_pos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
      have h_zms_u : ZeroMellinSeries a u = 0 := h_zms u hu_pos
      have h_eq : ∑' n : ℕ, b n * (u : ℂ) ^ (α n) =
          ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            a ρ.val * (u : ℂ) ^ (ρ.val - 1) := by
        rw [← e.tsum_eq (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
              a ρ.val * (u : ℂ) ^ (ρ.val - 1))]
      rw [h_eq]; exact h_zms_u
    -- Mellin resolvent vanishing on right half-plane.
    have h_resolvent_halfplane : ∀ s : ℂ, 0 < s.re →
        ∑' n : ℕ, b n / (s - α n) = 0 :=
      fun s hs =>
        mellin_resolvent_eq_zero_halfplane α b h_α_bdd_re h_α_loc_finite h_b_summable
          h_zms_enum s hs
    -- Resolvent analytic on (range α)ᶜ.
    have h_G_analytic : AnalyticOnNhd ℂ (fun s => ∑' n, b n / (s - α n))
        (Set.range α)ᶜ :=
      resolvent_analyticOnNhd α b h_b_summable h_α_loc_finite
    have h_U_conn : IsPreconnected (Set.range α : Set ℂ)ᶜ :=
      (Set.countable_range α |>.isConnected_compl_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
    have h_HP_sub : ∀ s : ℂ, 0 < s.re → s ∉ Set.range α := by
      intro s hs ⟨n, hn⟩
      have hα_n : (α n).re ≤ 0 := h_α_bdd_re n
      have : s.re ≤ 0 := hn ▸ hα_n
      linarith
    have h_z₀ : (⟨1, 0⟩ : ℂ) ∈ (Set.range α)ᶜ := h_HP_sub _ (by norm_num)
    have h_G_local :
        (fun s : ℂ => ∑' n, b n / (s - α n)) =ᶠ[nhds (⟨1, 0⟩ : ℂ)] 0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{s : ℂ | 0 < s.re}, ?_, ?_⟩
      · exact IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
          (by show (0 : ℝ) < (1 : ℝ); norm_num)
      · intro s hs; exact h_resolvent_halfplane s hs
    have h_G_zero : ∀ s, s ∉ Set.range α → ∑' n, b n / (s - α n) = 0 := by
      intro s hs
      have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        h_G_analytic (analyticOnNhd_const) h_U_conn h_z₀ h_G_local
      exact this hs
    have h_b_zero : ∀ n, b n = 0 :=
      coeff_from_resolvent_eq_zero α b h_α_inj h_α_loc_finite h_b_summable h_G_zero
    obtain ⟨n, hn⟩ := h_enum_surj ⟨ρ, hρ⟩
    have hval : ρ = (enum n).val := by
      have := congrArg Subtype.val hn
      simpa using this.symm
    rw [hval]
    exact h_b_zero n
  · -- FINITE CASE: NontrivialZeros is finite. Use finite linear independence
    -- of distinct exponentials.
    have h_fin : Set.Finite ZD.NontrivialZeros := Set.not_infinite.mp h_inf
    classical
    haveI : Fintype ZD.NontrivialZeros := h_fin.fintype
    haveI : DecidableEq {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := Classical.decEq _
    -- The tsum reduces to a finite sum.
    have h_zms_finset : ∀ t : ℝ, 0 < t →
        ∑ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          a ρ.val * (t : ℂ) ^ (ρ.val - 1) = 0 := by
      intro t ht
      have h := h_zms t ht
      unfold ZeroMellinSeries at h
      rw [tsum_eq_sum (s := Finset.univ)
          (f := fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
            a ρ.val * (t : ℂ) ^ (ρ.val - 1))
          (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at h
      exact h
    -- Convert to exp form: F(z) := Σ a(ρ) · exp((ρ-1) · z) for z ∈ ℂ. Vanishes on ℝ.
    -- For z ∈ ℝ via t = e^z: t^(ρ-1) = exp((ρ-1) · z) (real x case).
    have h_F_real : ∀ x : ℝ,
        ∑ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          a ρ.val * Complex.exp ((ρ.val - 1) * (x : ℂ)) = 0 := by
      intro x
      have hex_pos : (0 : ℝ) < Real.exp x := Real.exp_pos x
      have h := h_zms_finset (Real.exp x) hex_pos
      -- Replace each cpow term with exp.
      have hterm : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          a ρ.val * ((Real.exp x : ℝ) : ℂ) ^ (ρ.val - 1) =
          a ρ.val * Complex.exp ((ρ.val - 1) * (x : ℂ)) := by
        intro ρ
        congr 1
        have h1 : ((Real.exp x : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (Real.exp_pos x).ne'
        have him : ((x : ℝ) : ℂ).im = 0 := Complex.ofReal_im x
        rw [Complex.cpow_def_of_ne_zero h1,
            show ((Real.exp x : ℝ) : ℂ) = Complex.exp ((x : ℝ) : ℂ) by
              rw [Complex.ofReal_exp],
            Complex.log_exp (by rw [him]; exact neg_neg_iff_pos.mpr Real.pi_pos)
              (by rw [him]; exact Real.pi_pos.le)]
        ring_nf
      rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ)] at h
      exact h
    -- Extend to z ∈ ℂ via identity theorem.
    have h_F_complex : ∀ z : ℂ,
        ∑ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          a ρ.val * Complex.exp ((ρ.val - 1) * z) = 0 := by
      intro z
      let F : ℂ → ℂ := fun w => ∑ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Complex.exp ((ρ.val - 1) * w)
      have hF_diff : Differentiable ℂ F := by
        apply Differentiable.fun_sum
        intro ρ _
        apply Differentiable.const_mul
        apply Differentiable.cexp
        exact (differentiable_const _).mul differentiable_id
      have hF_analytic : AnalyticOnNhd ℂ F Set.univ :=
        DifferentiableOn.analyticOnNhd hF_diff.differentiableOn isOpen_univ
      have heq_real : ∀ c : ℝ, |c| < 1 →
          F c = (0 : ℂ) + (0 : ℂ) * c ^ 2 := by
        intro c _
        show F (c : ℂ) = (0 : ℂ) + (0 : ℂ) * c ^ 2
        rw [show F (c : ℂ) = ∑ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
              a ρ.val * Complex.exp ((ρ.val - 1) * (c : ℂ)) from rfl]
        rw [h_F_real c]; ring
      have := identity_theorem_extension F hF_analytic 0 0 heq_real z
      simpa using this
    -- Apply finite_exp_linIndep to extract coefficients.
    -- Define α : Subtype → ℂ as ρ ↦ ρ - 1, c : Subtype → ℂ as a∘val.
    let α' : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun r => r.val - 1
    let c' : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun r => a r.val
    have hα'_inj : Function.Injective α' := by
      intro r₁ r₂ hr
      apply Subtype.ext
      have : r₁.val - 1 = r₂.val - 1 := hr
      linear_combination this
    have hzero : ∀ z : ℂ, ∑ r : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        c' r * Complex.exp (α' r * z) = 0 := h_F_complex
    have h_a_zero : ∀ r : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, c' r = 0 :=
      finite_exp_linIndep α' c' hα'_inj hzero
    exact h_a_zero ⟨ρ, hρ⟩

end ZeroOrthogonality
end WeilPositivity
end ZD

end

#print axioms ZD.WeilPositivity.ZeroOrthogonality.ZeroCoefficientVanishesByOrthogonality_holds
#print axioms ZD.WeilPositivity.ZeroOrthogonality.mellin_resolvent_eq_zero_halfplane
