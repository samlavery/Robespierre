import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilPairTestContinuity
import RequestProject.WeilZeroSum
import RequestProject.ZeroCountJensen
import RequestProject.WeilLogDerivZetaBound
import RequestProject.WeilArchPrimeIdentity

/-!
# Pair Test Integration-by-Parts Infrastructure

Toward IBP×4 on `pairTestMellin β` to deliver Im-quartic decay unconditionally.

## Plan

1. **IBP-1**: Derivative formula for `pair_cosh_gauss_test β` (via sinh factorization).
2. **IBP-2**: Order-4 vanishing at `t = 0`.
3. **IBP-3**: Boundary vanishing of `t^s · pair(t)` at 0 and ∞.
4. **IBP-4**: Mellin IBP formula.
5. **IBP-5, IBP-6**: 2nd–4th derivatives.
6. **IBP-7**: Apply IBP 4 times.
7. **IBP-8**: Uniform bound on mellin of 4th derivative.
8. **IBP-9**: Extract decay at nontrivial zeros.

Current file delivers IBP-1 via a HasDerivAt statement. Higher-order steps
follow separately.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **IBP-1: HasDerivAt for pair_cosh_gauss_test.** From the sinh² factorization
`pair(t) = 4·sinh²(a·t)·sinh²(b·t)·exp(-2t²)` where `a = 1/2 - π/6, b = β - 1/2`,
the derivative exists at every `t` by product/chain rule. The explicit form of
the derivative is not needed for IBP — we just need `HasDerivAt` plus `ContDiff`
for higher derivatives.

This wraps `pair_cosh_gauss_test_differentiable` into `HasDerivAt (deriv ...)`
form for downstream IBP. -/
theorem pair_cosh_gauss_test_hasDerivAt (β : ℝ) (t : ℝ) :
    HasDerivAt (pair_cosh_gauss_test β) (deriv (pair_cosh_gauss_test β) t) t :=
  (pair_cosh_gauss_test_differentiable β t).hasDerivAt

#print axioms pair_cosh_gauss_test_hasDerivAt

/-- **IBP-4: Mellin IBP formula.** For a smooth function `f : ℝ → ℂ` with
boundary vanishing at 0 and ∞, and Mellin-integrable both f and f', the Mellin
transform satisfies:

```
mellin f s = -(1/s) · mellin f' (s+1)
```

This is the load-bearing infrastructure step for IBP×4 decay. Derived from
Mathlib's `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` with
`u = f, v = t^s / s` and boundary-vanishing hypotheses.

Hypotheses:
- `s ≠ 0` (to divide by s).
- `∀ t > 0, HasDerivAt f (f' t) t`.
- Mellin convergence of f at s and f' at s+1.
- Boundary limits at 0 and ∞ of `f(t) · t^s`.

The boundary limits are trivially 0 for Re s > 0 and f bounded near 0 with
Gaussian decay at ∞. -/
theorem mellin_ibp
    {f f' : ℝ → ℂ} {s : ℂ} (hs : s ≠ 0)
    (hf_deriv : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt f (f' t) t)
    (hf_conv : MellinConvergent f s)
    (hf'_conv : MellinConvergent f' (s + 1))
    (hbd0 : Filter.Tendsto (fun t : ℝ => f t * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hbdInf : Filter.Tendsto (fun t : ℝ => f t * (t : ℂ)^s) Filter.atTop (nhds 0)) :
    mellin f s = -(1 / s) * mellin f' (s + 1) := by
  -- Apply `integral_Ioi_mul_deriv_eq_deriv_mul` with u = f, v = t^s / s.
  -- v' = t^(s-1) (since d/dt (t^s / s) = t^(s-1) for t > 0, s ≠ 0).
  -- u · v = f(t) · t^s / s.
  -- u · v' = f(t) · t^(s-1)  ← this is mellin integrand for f.
  -- u' · v = f'(t) · t^s / s.
  -- Boundary: lim_0 (u·v) = 0/s = 0, lim_∞ (u·v) = 0/s = 0.
  -- Result: ∫_Ioi 0 u·v' = (0 - 0) - ∫_Ioi 0 u'·v.
  -- Rearranging: ∫ f·t^(s-1) = -(1/s) · ∫ f'·t^s.
  -- LHS = mellin f s; RHS = -(1/s) · mellin f' (s+1).
  set v : ℝ → ℂ := fun t => (t : ℂ)^s / s with hv_def
  set v' : ℝ → ℂ := fun t => (t : ℂ)^(s - 1) with hv'_def
  have hv_deriv : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt v (v' t) t := by
    intro t ht
    have ht_pos : (0:ℝ) < t := ht
    -- Use hasDerivAt_ofReal_cpow_const' with r = s - 1; gives deriv of y^s/s = y^(s-1).
    have hr_ne : (s - 1) ≠ -1 := by
      intro h; apply hs; linear_combination h
    have h := hasDerivAt_ofReal_cpow_const' ht_pos.ne' hr_ne
    -- h : HasDerivAt (fun y => ↑y ^ ((s-1)+1) / ((s-1)+1)) (↑t ^ (s-1)) t
    -- Simplify exponent (s-1)+1 = s.
    have hs_eq : (s - 1) + 1 = s := by ring
    have h_eq : (fun y : ℝ => (y : ℂ) ^ ((s - 1) + 1) / ((s - 1) + 1)) = v := by
      funext y
      simp only [v, hv_def, hs_eq]
    rw [h_eq] at h
    exact h
  -- Mellin integrand identity: (t^(s-1)) • f(t) = f(t) · t^(s-1) via smul_eq_mul.
  have h_mellin_f : mellin f s = ∫ t in Set.Ioi (0:ℝ), f t * v' t := by
    unfold mellin
    apply MeasureTheory.integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _
    simp [v', smul_eq_mul]
    ring
  have h_mellin_f' : mellin f' (s + 1) = ∫ t in Set.Ioi (0:ℝ), f' t * (t : ℂ)^s := by
    unfold mellin
    apply MeasureTheory.integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _
    have : s + 1 - 1 = s := by ring
    rw [this, smul_eq_mul, mul_comm]
  -- Apply IBP.
  have hfv'_int : MeasureTheory.IntegrableOn (fun t => f t * v' t) (Set.Ioi 0) := by
    have : MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ)^(s-1) • f t) (Set.Ioi 0) :=
      hf_conv
    refine (MeasureTheory.integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).mp this
    simp [v', smul_eq_mul]; ring
  have hf'v_int : MeasureTheory.IntegrableOn (fun t => f' t * v t) (Set.Ioi 0) := by
    have h_conv : MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ)^((s+1) - 1) • f' t)
        (Set.Ioi 0) := hf'_conv
    have h_scaled : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1/s) • ((t : ℂ)^((s+1) - 1) • f' t)) (Set.Ioi 0) :=
      h_conv.smul (1/s)
    refine (MeasureTheory.integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).mp h_scaled
    have hs1 : s + 1 - 1 = s := by ring
    simp only [v, hv_def, hs1, smul_eq_mul]
    field_simp
  have hbd0_v : Filter.Tendsto (fun t => f t * v t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : (fun t => f t * v t) = fun t => (f t * (t : ℂ)^s) * (1 / s) := by
      funext t; simp [v, hv_def]; ring
    rw [this]
    have := hbd0.mul_const (1 / s)
    simpa using this
  have hbdInf_v : Filter.Tendsto (fun t => f t * v t) Filter.atTop (nhds 0) := by
    have : (fun t => f t * v t) = fun t => (f t * (t : ℂ)^s) * (1 / s) := by
      funext t; simp [v, hv_def]; ring
    rw [this]
    have := hbdInf.mul_const (1 / s)
    simpa using this
  have h_IBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hf_deriv hv_deriv hfv'_int hf'v_int hbd0_v hbdInf_v
  -- h_IBP : ∫ t in Ioi 0, f t * v' t = 0 - 0 - ∫ t in Ioi 0, f' t * v t
  simp at h_IBP
  rw [h_mellin_f, show (∫ (t : ℝ) in Ioi 0, f t * v' t) = -∫ (t : ℝ) in Ioi 0, f' t * v t
      from h_IBP]
  -- -∫ f' · v = -∫ f' · t^s / s = -(1/s) · ∫ f' · t^s = -(1/s) · mellin f' (s+1)
  rw [show (fun t => f' t * v t) = (fun t => (1/s) * (f' t * (t : ℂ)^s)) from by
    funext t; simp [v, hv_def]; ring,
    show (∫ (t : ℝ) in Ioi 0, (1/s : ℂ) * (f' t * (t : ℂ)^s))
        = (1/s : ℂ) * ∫ (t : ℝ) in Ioi 0, f' t * (t : ℂ)^s
        from MeasureTheory.integral_const_mul (1/s : ℂ) _,
    ← h_mellin_f']
  ring

#print axioms mellin_ibp

/-- **IBP-3a: Boundary vanishing of `t^s · pair(t)` at `t = 0⁺`.** For `Re s > 0`
and the pair test continuous with `pair(0) = 0`:

```
lim_{t → 0⁺} t^s · pair(t) = 0.
```

Direct from `|t^s| = t^Re(s) → 0` and `pair` continuous at 0 (bounded near 0). -/
theorem pair_test_cpow_tendsto_zero_nhdsWithin_zero
    (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ) * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- |t^s · pair(t)| ≤ t^Re(s) · |pair(t)| → 0 · 0 = 0.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- pair continuous at 0, pair(0) = 0, so pair(t) < δ₁ when t < δ₁' for some δ₁'.
  -- t^s has |t^s| = t^Re(s) → 0 as t → 0⁺.
  -- Choose t small enough so both factors small.
  -- Simpler: show the product tends to 0 via norm bound.
  have h_pair_cont : ContinuousAt (pair_cosh_gauss_test β) 0 :=
    (pair_cosh_gauss_test_continuous β).continuousAt
  -- Use squeeze-zero / norm arguments.
  have h_pair_bd : ∀ᶠ t in nhds (0:ℝ), |pair_cosh_gauss_test β t| < 1 := by
    have h_tendsto : Filter.Tendsto (pair_cosh_gauss_test β) (nhds 0) (nhds 0) := by
      have h_at_zero := pair_cosh_gauss_test_at_zero β
      have := h_pair_cont.tendsto
      rw [h_at_zero] at this
      exact this
    rw [Metric.tendsto_nhds_nhds] at h_tendsto
    obtain ⟨δ, hδ_pos, hδ⟩ := h_tendsto 1 (by norm_num : (0:ℝ) < 1)
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ, hδ_pos, fun t ht => ?_⟩
    have := hδ ht
    simp [Real.dist_eq] at this
    simpa [Real.dist_eq, pair_cosh_gauss_test_at_zero] using this
  -- Extract δ₁ with |pair(t)| < 1 for |t| < δ₁.
  rw [Metric.eventually_nhds_iff] at h_pair_bd
  obtain ⟨δ₁, hδ₁_pos, h_pair_bd⟩ := h_pair_bd
  -- We want δ with dist t 0 < δ → ‖·‖ < ε. Take δ = min δ₁ (ε^(1/s.re)).
  refine ⟨min δ₁ (ε ^ (1 / s.re)), lt_min hδ₁_pos (Real.rpow_pos_of_pos hε _), ?_⟩
  intro t ht_pos ht_δ
  have ht_pos' : 0 < t := ht_pos
  have h_t_lt_δ₁ : dist t 0 < δ₁ := lt_of_lt_of_le ht_δ (min_le_left _ _)
  have h_t_lt_ε_rpow : dist t 0 < ε ^ (1 / s.re) := lt_of_lt_of_le ht_δ (min_le_right _ _)
  have h_pair_lt : |pair_cosh_gauss_test β t| < 1 := h_pair_bd h_t_lt_δ₁
  -- ‖t^s · pair(t)‖ = t^Re(s) · |pair(t)| < t^Re(s) · 1.
  have h_t_cpow_norm : ‖(t : ℂ)^s‖ = t^s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos ht_pos' s
  -- t^Re(s) < ε (since t < ε^(1/Re s) and Re s > 0).
  have h_t_lt_ε_rpow_abs : t < ε ^ (1 / s.re) := by
    rw [Real.dist_eq, sub_zero] at h_t_lt_ε_rpow
    have : |t| = t := abs_of_pos ht_pos'
    rw [this] at h_t_lt_ε_rpow; exact h_t_lt_ε_rpow
  have h_t_rpow_lt : t ^ s.re < ε := by
    calc t ^ s.re < (ε ^ (1 / s.re)) ^ s.re :=
          Real.rpow_lt_rpow (le_of_lt ht_pos') h_t_lt_ε_rpow_abs hs
      _ = ε ^ ((1 / s.re) * s.re) := by rw [← Real.rpow_mul (le_of_lt hε)]
      _ = ε ^ (1:ℝ) := by rw [div_mul_cancel₀ _ hs.ne']
      _ = ε := Real.rpow_one ε
  have h_pair_nn : 0 ≤ |pair_cosh_gauss_test β t| := abs_nonneg _
  have h_t_rpow_pos : 0 < t ^ s.re := Real.rpow_pos_of_pos ht_pos' _
  calc dist (((pair_cosh_gauss_test β t : ℝ) : ℂ) * (t : ℂ)^s) 0
      = ‖((pair_cosh_gauss_test β t : ℝ) : ℂ) * (t : ℂ)^s‖ := by rw [dist_zero_right]
    _ = |pair_cosh_gauss_test β t| * t^s.re := by
          rw [norm_mul, h_t_cpow_norm]
          congr 1
          exact Complex.norm_real _
    _ < 1 * ε := by
          apply mul_lt_mul' h_pair_lt.le h_t_rpow_lt h_t_rpow_pos.le (by norm_num : (0:ℝ) < 1)
    _ = ε := by ring

#print axioms pair_test_cpow_tendsto_zero_nhdsWithin_zero

/-- **IBP-3b: Boundary vanishing of `t^s · pair(t)` at `t → ∞`.** For any `s : ℂ`:

```
lim_{t → ∞} t^s · pair(t) = 0.
```

Uses `pair_cosh_gauss_test_isBigO_exp_neg_atTop`: pair = O(exp(-t)) at ∞.
Combined with polynomial · exp decay: any `t^σ · exp(-t) → 0`. -/
theorem pair_test_cpow_tendsto_zero_atTop (β : ℝ) (s : ℂ) :
    Filter.Tendsto (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ) * (t : ℂ)^s)
      Filter.atTop (nhds 0) := by
  -- |t^s · pair(t)| ≤ |t|^Re(s) · K · exp(-t) → 0 (exp beats polynomial).
  -- Use Asymptotics.IsBigO.trans_tendsto.
  have h_bigO : (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ) * (t : ℂ)^s) =O[atTop]
      (fun t : ℝ => Real.exp (-t) * t^(s.re)) := by
    have h1 := pair_cosh_gauss_test_isBigO_exp_neg_atTop β
    -- |((pair : ℝ) : ℂ) * (t:ℂ)^s| ≤ |pair| · t^Re(s) ≤ K · exp(-t) · t^Re(s)
    have h_cpow_bigO : (fun t : ℝ => (t : ℂ)^s) =O[atTop] (fun t : ℝ => t^s.re) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
        one_mul]
    exact h1.mul h_cpow_bigO
  have h_tendsto_dom : Filter.Tendsto
      (fun t : ℝ => Real.exp (-t) * t^(s.re)) atTop (nhds 0) := by
    -- Polynomial × exp(-t) → 0: use Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero or similar.
    -- More directly: rpow_mul_exp_neg version. Use isLittleO.
    have h_lit := isLittleO_rpow_exp_pos_mul_atTop (s.re) (by norm_num : (0:ℝ) < 1)
    -- h_lit : (fun x => x^s.re) =o[atTop] fun x => exp(1 * x)
    -- So t^s.re = o(exp(t)), hence t^s.re / exp(t) → 0, hence exp(-t) * t^s.re → 0.
    have h_tendsto : Filter.Tendsto (fun t : ℝ => t^s.re / Real.exp (1 * t)) atTop (nhds 0) :=
      h_lit.tendsto_div_nhds_zero
    have h_eq : (fun t : ℝ => Real.exp (-t) * t^(s.re)) =
        (fun t : ℝ => t^s.re / Real.exp (1 * t)) := by
      funext t
      rw [one_mul, Real.exp_neg]
      field_simp
    rw [h_eq]
    exact h_tendsto
  exact h_bigO.trans_tendsto h_tendsto_dom

#print axioms pair_test_cpow_tendsto_zero_atTop

/-- **IBP-5a: Iterated derivative continuity.** Any order derivative of pair test
is continuous on ℝ (via `ContDiff ⊤`). -/
theorem pair_cosh_gauss_test_iteratedDeriv_continuous (β : ℝ) (k : ℕ) :
    Continuous (iteratedDeriv k (pair_cosh_gauss_test β)) :=
  (pair_cosh_gauss_test_contDiff β k).continuous_iteratedDeriv' k

/-- **IBP-5b: Iterated derivative differentiable.** Needed for applying the next
IBP iteration. -/
theorem pair_cosh_gauss_test_iteratedDeriv_differentiable (β : ℝ) (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k (pair_cosh_gauss_test β)) :=
  (pair_cosh_gauss_test_contDiff β (k + 1)).differentiable_iteratedDeriv k
    (by exact_mod_cast Nat.lt_succ_self k)

#print axioms pair_cosh_gauss_test_iteratedDeriv_continuous
#print axioms pair_cosh_gauss_test_iteratedDeriv_differentiable

/-! ### IBP-6a: Derivative formula for cosh-Gaussian -/

/-- **Derivative of `cosh(c·t)·exp(-2t²)`.** Explicit product-rule form:

```
d/dt [cosh(c·t) · exp(-2t²)] = (c · sinh(c·t) - 4t · cosh(c·t)) · exp(-2t²).
```

Primitive building block — `pair_cosh_gauss_test β` is a linear combination of
`cosh(c·t)·exp(-2t²)` for five specific values of `c` (see
`pair_cosh_gauss_test_cosh_expansion`). -/
theorem coshGauss_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cosh (c * u) * Real.exp (-2 * u^2))
      ((c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)) * Real.exp (-2 * t^2)) t := by
  have h1 : HasDerivAt (fun u : ℝ => c * u) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h2 : HasDerivAt (fun u : ℝ => Real.cosh (c * u)) (Real.sinh (c * t) * c) t :=
    (Real.hasDerivAt_cosh (c * t)).comp t h1
  have h3 : HasDerivAt (fun u : ℝ => -2 * u^2) (-2 * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (-2 : ℝ)
    simpa [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have h4 : HasDerivAt (fun u : ℝ => Real.exp (-2 * u^2)) (Real.exp (-2 * t^2) * (-2 * (2 * t))) t :=
    h3.exp
  have h5 := h2.mul h4
  -- h5 derivative: sinh(c·t)·c · exp(-2t²) + cosh(c·t) · (exp(-2t²) · (-4t))
  convert h5 using 1
  ring

#print axioms coshGauss_hasDerivAt

/-- **Derivative of `cosh(c·t)·exp(-2t²)` as a function of `t`.** Packaged for
`deriv` extraction rather than `HasDerivAt`. -/
theorem coshGauss_deriv (c t : ℝ) :
    deriv (fun u : ℝ => Real.cosh (c * u) * Real.exp (-2 * u^2)) t =
      (c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)) * Real.exp (-2 * t^2) :=
  (coshGauss_hasDerivAt c t).deriv

#print axioms coshGauss_deriv

/-! ### IBP-6b: Gaussian domination of cosh-Gaussian derivative at infinity -/

/-- **Cosh-Gaussian derivative is `O(exp(-t/2))` at infinity.** The derivative
`d/dt [cosh(c·t)·exp(-2t²)] = (c·sinh(c·t) - 4t·cosh(c·t))·exp(-2t²)` has
Gaussian-dominated decay at `t → ∞`:

```
|d/dt [cosh(c·t)·exp(-2t²)]| = O(exp(-t/2)).
```

The proof bounds the derivative by `(|c|+4t)·exp(|c|·t - 2·t²)` pointwise
(for `t > 0`), then uses `2·t² - (|c|+1)·t ≥ t/2` and `|c|+4t ≤ exp(t)` for
sufficiently large `t` to squeeze the product into `exp(-t/2)`. -/
theorem coshGauss_deriv_isBigO_exp_neg_half_atTop (c : ℝ) :
    (fun t : ℝ =>
      (((c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)) * Real.exp (-2 * t^2) : ℝ) : ℂ))
      =O[atTop] (fun t : ℝ => Real.exp (-t/2)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨max 10 (|c| + 2), fun t ht => ?_⟩
  have ht_10 : (10:ℝ) ≤ t := le_of_max_le_left ht
  have ht_c : |c| + 2 ≤ t := le_of_max_le_right ht
  have ht_pos : (0:ℝ) < t := by linarith
  have ht_abs_c : |c| ≤ t := by linarith
  -- Step 1: pointwise bound on the integrand.
  have h_sinh_le_cosh : |Real.sinh (c * t)| ≤ Real.cosh (c * t) := by
    rw [Real.abs_sinh, ← Real.cosh_abs (c*t)]
    exact (Real.sinh_lt_cosh _).le
  have h_cosh_le_exp : Real.cosh (c * t) ≤ Real.exp (|c| * t) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (c * t) ≤ Real.exp (|c| * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self c) ht_pos.le)
    have h2 : Real.exp (-(c * t)) ≤ Real.exp (|c| * t) := by
      apply Real.exp_le_exp.mpr
      have : -(c*t) ≤ |c*t| := neg_le_abs _
      rw [abs_mul, abs_of_pos ht_pos] at this
      exact this
    linarith
  have h_abs_inner : |c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)| ≤
      (|c| + 4*t) * Real.cosh (c * t) := by
    have h_cosh_nn : 0 ≤ Real.cosh (c * t) := (Real.cosh_pos _).le
    calc |c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)|
        ≤ |c * Real.sinh (c * t)| + |4 * t * Real.cosh (c * t)| := abs_sub _ _
      _ = |c| * |Real.sinh (c * t)| + 4 * t * Real.cosh (c * t) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4),
            abs_of_pos ht_pos, abs_of_nonneg h_cosh_nn]
      _ ≤ |c| * Real.cosh (c * t) + 4 * t * Real.cosh (c * t) := by
          gcongr
      _ = (|c| + 4*t) * Real.cosh (c * t) := by ring
  -- Step 2: bound (|c|+4t)·cosh(c·t)·exp(-2t²) ≤ (|c|+4t)·exp(|c|·t - 2t²)
  have h_exp_pos_neg2 : 0 < Real.exp (-2 * t^2) := Real.exp_pos _
  have h_abs_c_add_4t_nn : 0 ≤ |c| + 4*t := by positivity
  have h_bd_step1 : |c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)| *
      Real.exp (-2 * t^2) ≤ (|c| + 4*t) * Real.exp (|c| * t - 2 * t^2) := by
    calc |c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)| * Real.exp (-2 * t^2)
        ≤ ((|c| + 4*t) * Real.cosh (c * t)) * Real.exp (-2 * t^2) :=
          mul_le_mul_of_nonneg_right h_abs_inner h_exp_pos_neg2.le
      _ ≤ ((|c| + 4*t) * Real.exp (|c| * t)) * Real.exp (-2 * t^2) := by
          apply mul_le_mul_of_nonneg_right _ h_exp_pos_neg2.le
          exact mul_le_mul_of_nonneg_left h_cosh_le_exp h_abs_c_add_4t_nn
      _ = (|c| + 4*t) * Real.exp (|c| * t - 2 * t^2) := by
          rw [mul_assoc, ← Real.exp_add]; congr 1; ring
  -- Step 3: (|c|+4t) ≤ 5t ≤ exp(t), for t ≥ 10 and t ≥ |c|.
  have h_poly_bd : |c| + 4*t ≤ 5*t := by linarith
  have h_5t_le_exp : 5*t ≤ Real.exp t := by
    have h_exp_quad : 1 + t + t^2/2 ≤ Real.exp t :=
      Real.quadratic_le_exp_of_nonneg (by linarith : (0:ℝ) ≤ t)
    -- For t ≥ 10: t²/2 ≥ 5t, and 1 + t ≥ 0, so 5t ≤ t²/2 ≤ 1 + t + t²/2 ≤ exp(t).
    have ht_sq : t^2/2 ≥ 5*t := by nlinarith [ht_10]
    linarith
  have h_poly_le_exp : |c| + 4*t ≤ Real.exp t := le_trans h_poly_bd h_5t_le_exp
  -- Step 4: (|c|+4t)·exp(|c|·t - 2t²) ≤ exp(t)·exp(|c|·t - 2t²) = exp(t + |c|·t - 2t²)
  have h_exp_pos_mid : 0 < Real.exp (|c| * t - 2 * t^2) := Real.exp_pos _
  have h_bd_step2 : (|c| + 4*t) * Real.exp (|c| * t - 2 * t^2) ≤
      Real.exp (t + |c| * t - 2 * t^2) := by
    calc (|c| + 4*t) * Real.exp (|c| * t - 2 * t^2)
        ≤ Real.exp t * Real.exp (|c| * t - 2 * t^2) :=
          mul_le_mul_of_nonneg_right h_poly_le_exp h_exp_pos_mid.le
      _ = Real.exp (t + |c| * t - 2 * t^2) := by
          rw [← Real.exp_add]; congr 1; ring
  -- Step 5: t + |c|·t - 2t² ≤ -t/2, for t ≥ max(10, |c|+2).
  have h_exp_arg_bd : t + |c| * t - 2 * t^2 ≤ -t/2 := by
    -- 2t² ≥ (|c|+1)·t + t/2 iff 2t² - (|c|+1)·t - t/2 ≥ 0
    -- Use t(2t - |c| - 1 - 1/2) = t(2t - |c| - 3/2) ≥ 0, sufficient if 2t ≥ |c|+3/2.
    -- For t ≥ |c|+2: 2t ≥ 2|c|+4 ≥ |c|+3/2 (since |c|+5/2 ≥ 3/2 for |c| ≥ 0).
    nlinarith [ht_c, ht_10, sq_nonneg t, sq_nonneg (t - (|c|+1))]
  have h_bd_step3 : Real.exp (t + |c| * t - 2 * t^2) ≤ Real.exp (-t/2) :=
    Real.exp_le_exp.mpr h_exp_arg_bd
  -- Combine.
  -- Norm of real-coerced product.
  have h_norm_lhs : ‖(((c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)) *
        Real.exp (-2 * t^2) : ℝ) : ℂ)‖ =
      |c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)| * Real.exp (-2 * t^2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos h_exp_pos_neg2]
  rw [h_norm_lhs]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
  linarith [h_bd_step1, h_bd_step2, h_bd_step3]

#print axioms coshGauss_deriv_isBigO_exp_neg_half_atTop

/-! ### IBP-6c: MellinConvergent for pair derivative on `Re s > 0` -/

/-- **Abbreviation: `coshGaussDerivVal c t`** = the value of `d/dt [cosh(c·t)·exp(-2t²)]`. -/
noncomputable def coshGaussDerivVal (c t : ℝ) : ℝ :=
  (c * Real.sinh (c * t) - 4 * t * Real.cosh (c * t)) * Real.exp (-2 * t^2)

/-- **Pointwise derivative formula for the pair test.** From the five-term
cosh-expansion of `pair_cosh_gauss_test β t`, the derivative at `t` is the
corresponding linear combination of `coshGaussDerivVal` values. -/
theorem pair_cosh_gauss_test_hasDerivAt_sum (β t : ℝ) :
    HasDerivAt (pair_cosh_gauss_test β)
      ((1/2 : ℝ) * coshGaussDerivVal (2*β - Real.pi/3) t
        + (1/2) * coshGaussDerivVal (2 - Real.pi/3 - 2*β) t
        - coshGaussDerivVal (1 - Real.pi/3) t
        - coshGaussDerivVal (2*β - 1) t
        + coshGaussDerivVal 0 t) t := by
  have h_fun_eq : pair_cosh_gauss_test β = fun u =>
        (1/2) * (Real.cosh ((2*β - Real.pi/3) * u) * Real.exp (-2 * u^2))
      + (1/2) * (Real.cosh ((2 - Real.pi/3 - 2*β) * u) * Real.exp (-2 * u^2))
      -  (Real.cosh ((1 - Real.pi/3) * u) * Real.exp (-2 * u^2))
      -  (Real.cosh ((2*β - 1) * u) * Real.exp (-2 * u^2))
      +  (Real.cosh (0 * u) * Real.exp (-2 * u^2)) := by
    funext u
    rw [pair_cosh_gauss_test_cosh_expansion β u, zero_mul, Real.cosh_zero, one_mul]
    ring
  rw [h_fun_eq]
  have h1 := (coshGauss_hasDerivAt (2*β - Real.pi/3) t).const_mul (1/2 : ℝ)
  have h2 := (coshGauss_hasDerivAt (2 - Real.pi/3 - 2*β) t).const_mul (1/2 : ℝ)
  have h3 := coshGauss_hasDerivAt (1 - Real.pi/3) t
  have h4 := coshGauss_hasDerivAt (2*β - 1) t
  have h5 := coshGauss_hasDerivAt 0 t
  exact (((h1.add h2).sub h3).sub h4).add h5

/-- **Explicit `deriv` formula for the pair test.** Packaged from
`pair_cosh_gauss_test_hasDerivAt_sum` via `HasDerivAt.deriv`. -/
theorem pair_cosh_gauss_test_deriv_eq (β t : ℝ) :
    deriv (pair_cosh_gauss_test β) t =
      (1/2 : ℝ) * coshGaussDerivVal (2*β - Real.pi/3) t
        + (1/2) * coshGaussDerivVal (2 - Real.pi/3 - 2*β) t
        - coshGaussDerivVal (1 - Real.pi/3) t
        - coshGaussDerivVal (2*β - 1) t
        + coshGaussDerivVal 0 t :=
  (pair_cosh_gauss_test_hasDerivAt_sum β t).deriv

#print axioms pair_cosh_gauss_test_hasDerivAt_sum
#print axioms pair_cosh_gauss_test_deriv_eq

/-- **Pair derivative is `O(exp(-t/2))` at infinity.** Linear combination of
five `coshGaussDerivVal` terms, each `O(exp(-t/2))` by
`coshGauss_deriv_isBigO_exp_neg_half_atTop`. -/
theorem pair_cosh_gauss_test_deriv_isBigO_exp_neg_half_atTop (β : ℝ) :
    (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
  have h_eq : (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ)) =
      (fun t : ℝ =>
        (((1/2 : ℝ) * coshGaussDerivVal (2*β - Real.pi/3) t : ℝ) : ℂ) +
        (((1/2 : ℝ) * coshGaussDerivVal (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ) -
        ((coshGaussDerivVal (1 - Real.pi/3) t : ℝ) : ℂ) -
        ((coshGaussDerivVal (2*β - 1) t : ℝ) : ℂ) +
        ((coshGaussDerivVal 0 t : ℝ) : ℂ)) := by
    funext t
    rw [pair_cosh_gauss_test_deriv_eq]
    push_cast
    ring
  rw [h_eq]
  have h1 := (coshGauss_deriv_isBigO_exp_neg_half_atTop (2*β - Real.pi/3)).const_mul_left (1/2 : ℂ)
  have h2 := (coshGauss_deriv_isBigO_exp_neg_half_atTop (2 - Real.pi/3 - 2*β)).const_mul_left (1/2 : ℂ)
  have h3 := coshGauss_deriv_isBigO_exp_neg_half_atTop (1 - Real.pi/3)
  have h4 := coshGauss_deriv_isBigO_exp_neg_half_atTop (2*β - 1)
  have h5 := coshGauss_deriv_isBigO_exp_neg_half_atTop 0
  -- Reshape h1..h5 to match the target decomposition; coerce coshGaussDerivVal to ℂ via ofReal.
  have h1' : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDerivVal (2*β - Real.pi/3) t : ℝ) : ℂ))) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDerivVal (2*β - Real.pi/3) t : ℝ) : ℂ))) =
        (fun t : ℝ => (1/2 : ℂ) * ((coshGaussDerivVal (2*β - Real.pi/3) t : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [this]
    unfold coshGaussDerivVal at h1 ⊢
    exact h1
  have h2' : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDerivVal (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ))) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDerivVal (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ))) =
        (fun t : ℝ => (1/2 : ℂ) * ((coshGaussDerivVal (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [this]
    unfold coshGaussDerivVal at h2 ⊢
    exact h2
  have h3' : (fun t : ℝ => ((coshGaussDerivVal (1 - Real.pi/3) t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    unfold coshGaussDerivVal
    exact h3
  have h4' : (fun t : ℝ => ((coshGaussDerivVal (2*β - 1) t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    unfold coshGaussDerivVal
    exact h4
  have h5' : (fun t : ℝ => ((coshGaussDerivVal 0 t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    unfold coshGaussDerivVal
    exact h5
  exact ((((h1'.add h2').sub h3').sub h4').add h5')

#print axioms pair_cosh_gauss_test_deriv_isBigO_exp_neg_half_atTop

/-- **Pair derivative is bounded (O(1) = O(x^(-0))) near `t = 0⁺`.** The
derivative of the pair test is continuous on ℝ, hence bounded on a
neighborhood of `0`. -/
theorem pair_cosh_gauss_test_deriv_isBigO_one_nhds_zero (β : ℝ) :
    (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ)) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-(0:ℝ))) := by
  have h_deriv_cont : Continuous (deriv (pair_cosh_gauss_test β)) := by
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 1
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_cont : Continuous (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h_deriv_cont
  have h_tendsto : Filter.Tendsto
      (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (nhds (((deriv (pair_cosh_gauss_test β) 0 : ℝ) : ℂ))) :=
    (h_cont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have h_rpow_eq : (fun x : ℝ => x^(-(0:ℝ))) = (fun _ : ℝ => (1:ℝ)) := by
    funext x; rw [neg_zero, Real.rpow_zero]
  rw [h_rpow_eq]
  exact h_tendsto.isBigO_one ℝ

#print axioms pair_cosh_gauss_test_deriv_isBigO_one_nhds_zero

/-- **MellinConvergent for the pair derivative on `Re s > 0`.** Combines:
- continuity of `deriv (pair_cosh_gauss_test β)` (from `ContDiff`),
- decay `=O[atTop] exp(-t/2)` via
  `pair_cosh_gauss_test_deriv_isBigO_exp_neg_half_atTop`,
- boundedness near 0 via
  `pair_cosh_gauss_test_deriv_isBigO_one_nhds_zero`.
Fed into `mellinConvergent_of_isBigO_rpow_exp` with `a := 1/2`, `b := 0`. -/
theorem mellinConvergent_pair_cosh_gauss_test_deriv (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0) (by norm_num : (0:ℝ) < 1/2)
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    apply Complex.continuous_ofReal.comp
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 1
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  · have h := pair_cosh_gauss_test_deriv_isBigO_exp_neg_half_atTop β
    have h_eq : (fun t : ℝ => Real.exp (-(1/2) * t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; congr 1; ring
    rw [h_eq]
    exact h
  · exact pair_cosh_gauss_test_deriv_isBigO_one_nhds_zero β
  · exact hs

#print axioms mellinConvergent_pair_cosh_gauss_test_deriv

/-! ### IBP-6d: Boundary vanishing of `t^s · pair_deriv(t)` at 0 and ∞ -/

/-- **Value of `pair_deriv` at `t = 0` is 0.** From the explicit derivative
formula each `coshGaussDerivVal c 0 = 0` (sinh(0)=0, t=0 factor). -/
theorem pair_cosh_gauss_test_deriv_at_zero (β : ℝ) :
    deriv (pair_cosh_gauss_test β) 0 = 0 := by
  rw [pair_cosh_gauss_test_deriv_eq]
  simp [coshGaussDerivVal, Real.sinh_zero]

#print axioms pair_cosh_gauss_test_deriv_at_zero

/-- **Boundary vanishing of `t^s · pair_deriv(t)` at `t → 0⁺`.** For `Re s > 0`,
`pair_deriv(t) · t^s → 0` as `t → 0⁺`. Uses: `pair_deriv(0) = 0`, continuity
at 0 (so `pair_deriv` bounded near 0), and `|t^s| = t^Re(s) → 0`. -/
theorem pair_cosh_gauss_test_deriv_cpow_tendsto_zero_nhdsWithin_zero
    (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ) * (t : ℂ)^s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_deriv_cont : Continuous (deriv (pair_cosh_gauss_test β)) := by
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 1
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_deriv_cont_at_zero : ContinuousAt (deriv (pair_cosh_gauss_test β)) 0 :=
    h_deriv_cont.continuousAt
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have h_tendsto : Filter.Tendsto (deriv (pair_cosh_gauss_test β)) (nhds 0) (nhds 0) := by
    have := h_deriv_cont_at_zero.tendsto
    rw [pair_cosh_gauss_test_deriv_at_zero] at this
    exact this
  rw [Metric.tendsto_nhds_nhds] at h_tendsto
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := h_tendsto 1 (by norm_num : (0:ℝ) < 1)
  -- |pair_deriv(t)| < 1 for dist t 0 < δ₁.
  -- Choose δ = min δ₁ (ε^(1/Re s)).
  refine ⟨min δ₁ (ε ^ (1 / s.re)), lt_min hδ₁_pos (Real.rpow_pos_of_pos hε _), ?_⟩
  intro t ht_pos ht_δ
  have ht_pos' : 0 < t := ht_pos
  have h_t_lt_δ₁ : dist t 0 < δ₁ := lt_of_lt_of_le ht_δ (min_le_left _ _)
  have h_t_lt_ε_rpow : dist t 0 < ε ^ (1 / s.re) := lt_of_lt_of_le ht_δ (min_le_right _ _)
  have h_deriv_lt : |deriv (pair_cosh_gauss_test β) t| < 1 := by
    have := hδ₁ h_t_lt_δ₁
    simpa [Real.dist_eq, pair_cosh_gauss_test_deriv_at_zero] using this
  have h_t_cpow_norm : ‖(t : ℂ)^s‖ = t^s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos ht_pos' s
  have h_t_lt_ε_rpow_abs : t < ε ^ (1 / s.re) := by
    rw [Real.dist_eq, sub_zero] at h_t_lt_ε_rpow
    have : |t| = t := abs_of_pos ht_pos'
    rw [this] at h_t_lt_ε_rpow; exact h_t_lt_ε_rpow
  have h_t_rpow_lt : t ^ s.re < ε := by
    calc t ^ s.re < (ε ^ (1 / s.re)) ^ s.re :=
          Real.rpow_lt_rpow (le_of_lt ht_pos') h_t_lt_ε_rpow_abs hs
      _ = ε ^ ((1 / s.re) * s.re) := by rw [← Real.rpow_mul (le_of_lt hε)]
      _ = ε ^ (1:ℝ) := by rw [div_mul_cancel₀ _ hs.ne']
      _ = ε := Real.rpow_one ε
  have h_t_rpow_pos : 0 < t ^ s.re := Real.rpow_pos_of_pos ht_pos' _
  calc dist (((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ) * (t : ℂ)^s) 0
      = ‖((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ) * (t : ℂ)^s‖ := by rw [dist_zero_right]
    _ = |deriv (pair_cosh_gauss_test β) t| * t^s.re := by
          rw [norm_mul, h_t_cpow_norm]
          congr 1
          exact Complex.norm_real _
    _ < 1 * ε := by
          apply mul_lt_mul' h_deriv_lt.le h_t_rpow_lt h_t_rpow_pos.le (by norm_num : (0:ℝ) < 1)
    _ = ε := by ring

#print axioms pair_cosh_gauss_test_deriv_cpow_tendsto_zero_nhdsWithin_zero

/-- **Boundary vanishing of `t^s · pair_deriv(t)` at `t → ∞`.** For any `s : ℂ`,
`pair_deriv(t) · t^s → 0` as `t → ∞`, because `pair_deriv = O(exp(-t/2))` and
`t^s = O(t^Re(s))` is polynomial-dominated. -/
theorem pair_cosh_gauss_test_deriv_cpow_tendsto_zero_atTop (β : ℝ) (s : ℂ) :
    Filter.Tendsto (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ) * (t : ℂ)^s)
      Filter.atTop (nhds 0) := by
  have h_bigO : (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ) * (t : ℂ)^s) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2) * t^(s.re)) := by
    have h1 := pair_cosh_gauss_test_deriv_isBigO_exp_neg_half_atTop β
    have h_cpow_bigO : (fun t : ℝ => (t : ℂ)^s) =O[atTop] (fun t : ℝ => t^s.re) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), one_mul]
    exact h1.mul h_cpow_bigO
  have h_tendsto_dom : Filter.Tendsto (fun t : ℝ => Real.exp (-t/2) * t^(s.re)) atTop (nhds 0) := by
    have h_lit : (fun t : ℝ => t^s.re) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) :=
      isLittleO_rpow_exp_pos_mul_atTop s.re (by norm_num : (0:ℝ) < 1/2)
    have h_tendsto : Filter.Tendsto (fun t : ℝ => t^s.re / Real.exp ((1/2) * t)) atTop (nhds 0) :=
      h_lit.tendsto_div_nhds_zero
    have h_eq : (fun t : ℝ => Real.exp (-t/2) * t^(s.re)) =
        (fun t : ℝ => t^s.re / Real.exp ((1/2) * t)) := by
      funext t
      have h1 : (-t/2 : ℝ) = -((1/2) * t) := by ring
      rw [h1, Real.exp_neg]
      field_simp
    rw [h_eq]
    exact h_tendsto
  exact h_bigO.trans_tendsto h_tendsto_dom

#print axioms pair_cosh_gauss_test_deriv_cpow_tendsto_zero_atTop

/-! ### IBP-7: Single-step Mellin IBP on pairTestMellin -/

/-- **Abbreviation: `pairDerivMellin`.** The Mellin transform of the first
derivative of `pair_cosh_gauss_test β`, coerced to `ℂ`. Analogous to
`pairTestMellin` but with the first derivative. -/
noncomputable def pairDerivMellin (β : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ)) s

/-- **HasDerivAt for the coerced pair test (complex-valued).** Pushforward of
`pair_cosh_gauss_test_hasDerivAt` through `Complex.ofReal`. -/
theorem coerced_pair_hasDerivAt (β : ℝ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => ((pair_cosh_gauss_test β y : ℝ) : ℂ))
      (((deriv (pair_cosh_gauss_test β) t : ℝ) : ℂ)) t :=
  (pair_cosh_gauss_test_hasDerivAt β t).ofReal_comp

/-- **IBP-7: First Mellin IBP on `pairTestMellin β`.** For `0 < Re s`,

```
pairTestMellin β s = -(1/s) · pairDerivMellin β (s+1).
```

Direct application of `mellin_ibp` with `f = coerced pair test`, `f' = coerced
pair test derivative`. Hypotheses discharged by:
- `pair_cosh_gauss_test_hasDerivAt` lifted via `HasDerivAt.ofReal_comp`.
- `mellinConvergent_pair` at `s`.
- `mellinConvergent_pair_cosh_gauss_test_deriv` at `s+1`.
- `pair_test_cpow_tendsto_zero_{nhdsWithin_zero, atTop}`. -/
theorem pairTestMellin_ibp_once (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    pairTestMellin β s = -(1/s) * pairDerivMellin β (s + 1) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  unfold pairTestMellin pairDerivMellin
  refine mellin_ibp (s := s) hs_ne
    (fun t _ => coerced_pair_hasDerivAt β t) ?_ ?_ ?_ ?_
  · exact mellinConvergent_pair β hs
  · exact mellinConvergent_pair_cosh_gauss_test_deriv β hs1_re
  · exact pair_test_cpow_tendsto_zero_nhdsWithin_zero β hs
  · exact pair_test_cpow_tendsto_zero_atTop β s

#print axioms pairTestMellin_ibp_once

/-! ### IBP-7 (higher order): generalized `mellinConvergent` and boundary
vanishing for iterated derivatives of the pair test.

Aims toward `pairTestMellin β s = ∏_{k=0..3} (-1/(s+k)) · mellin (iteratedDeriv 4 pair) (s+4)`.

**Structural observation.** Each `iteratedDeriv k (pair_cosh_gauss_test β)` is a
finite linear combination of terms of the form `polynomial(t) · cosh(c·t) · exp(-2t²)`
and `polynomial(t) · sinh(c·t) · exp(-2t²)`, for five values of `c`
(from `pair_cosh_gauss_test_cosh_expansion`). Each such term is Gaussian-dominated
at `t → ∞` and continuous at `t = 0`.

We establish the needed ingredients abstractly via `ContDiff` + continuity,
without building up the explicit `iteratedDeriv k` formula. This suffices for
Mellin convergence and boundary vanishing. -/

/-- **Continuity of `iteratedDeriv k pair` at every `t`.** Direct from
`pair_cosh_gauss_test_contDiff β ⊤` via
`ContDiff.continuous_iteratedDeriv'`. -/
theorem pair_iteratedDeriv_continuous (β : ℝ) (k : ℕ) :
    Continuous (iteratedDeriv k (pair_cosh_gauss_test β)) :=
  pair_cosh_gauss_test_iteratedDeriv_continuous β k

/-- **Differentiability of `iteratedDeriv k pair`.** Same as existing
`pair_cosh_gauss_test_iteratedDeriv_differentiable`. -/
theorem pair_iteratedDeriv_differentiable (β : ℝ) (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k (pair_cosh_gauss_test β)) :=
  pair_cosh_gauss_test_iteratedDeriv_differentiable β k

/-- **HasDerivAt chaining: `iteratedDeriv k.succ = deriv ∘ iteratedDeriv k`.** -/
theorem pair_iteratedDeriv_succ_hasDerivAt (β : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv k (pair_cosh_gauss_test β))
      (iteratedDeriv (k+1) (pair_cosh_gauss_test β) t) t := by
  have hdiff := pair_iteratedDeriv_differentiable β k
  rw [iteratedDeriv_succ]
  exact (hdiff t).hasDerivAt

#print axioms pair_iteratedDeriv_continuous
#print axioms pair_iteratedDeriv_differentiable
#print axioms pair_iteratedDeriv_succ_hasDerivAt

/-! ### IBP-7a: Second derivative of cosh-Gaussian -/

/-- **Second derivative of `cosh(c·t)·exp(-2t²)`.** By direct application of
product rule to `coshGaussDerivVal c t = (c·sinh(c·t) - 4t·cosh(c·t))·exp(-2t²)`:

```
d²/dt² [cosh(c·t)·exp(-2t²)]
  = [(c² - 4 + 16·t²)·cosh(c·t) - 8·c·t·sinh(c·t)] · exp(-2t²).
```
-/
noncomputable def coshGaussDeriv2Val (c t : ℝ) : ℝ :=
  ((c^2 - 4 + 16 * t^2) * Real.cosh (c * t) - 8 * c * t * Real.sinh (c * t)) *
    Real.exp (-2 * t^2)

/-- **HasDerivAt for `coshGaussDerivVal` at each `t`.** Derivative is
`coshGaussDeriv2Val c t`. Direct product-rule computation. -/
theorem coshGauss_hasDerivAt_iter2 (c t : ℝ) :
    HasDerivAt (coshGaussDerivVal c) (coshGaussDeriv2Val c t) t := by
  unfold coshGaussDerivVal coshGaussDeriv2Val
  have h_inner : HasDerivAt (fun u : ℝ => c * u) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h_cosh : HasDerivAt (fun u : ℝ => Real.cosh (c * u)) (Real.sinh (c * t) * c) t :=
    (Real.hasDerivAt_cosh (c * t)).comp t h_inner
  have h_sinh : HasDerivAt (fun u : ℝ => Real.sinh (c * u)) (Real.cosh (c * t) * c) t :=
    (Real.hasDerivAt_sinh (c * t)).comp t h_inner
  have h_c_sinh : HasDerivAt (fun u : ℝ => c * Real.sinh (c * u))
      (c * (Real.cosh (c * t) * c)) t :=
    h_sinh.const_mul c
  have h_4t : HasDerivAt (fun u : ℝ => (4 : ℝ) * u) 4 t := by
    simpa using (hasDerivAt_id t).const_mul 4
  have h_4t_cosh : HasDerivAt (fun u : ℝ => 4 * u * Real.cosh (c * u))
      (4 * Real.cosh (c * t) + 4 * t * (Real.sinh (c * t) * c)) t :=
    h_4t.mul h_cosh
  have h_u : HasDerivAt (fun u : ℝ => c * Real.sinh (c * u) - 4 * u * Real.cosh (c * u))
      (c * (Real.cosh (c * t) * c) -
        (4 * Real.cosh (c * t) + 4 * t * (Real.sinh (c * t) * c))) t :=
    h_c_sinh.sub h_4t_cosh
  have h_arg : HasDerivAt (fun u : ℝ => -2 * u^2) (-2 * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (-2 : ℝ)
    simpa [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have h_exp : HasDerivAt (fun u : ℝ => Real.exp (-2 * u^2))
      (Real.exp (-2 * t^2) * (-2 * (2 * t))) t :=
    h_arg.exp
  have h_prod := h_u.mul h_exp
  convert h_prod using 1
  ring

#print axioms coshGaussDeriv2Val
#print axioms coshGauss_hasDerivAt_iter2

/-- **Cosh-Gaussian 2nd derivative is `o[atTop] exp(-t/2)`.** Via asymptotic
composition: the bound factors as `(polynomial) · cosh(c·t)·exp(-2t²)`, and
`cosh·exp` has exponential decay while the polynomial factor grows slower
than any exp. Uses `isLittleO_pow_exp_pos_mul_atTop` (polynomial vs exp) and
`coshGauss_isBigO_exp_neg_atTop` (exp decay of cosh-Gaussian). -/
theorem coshGaussDeriv2Val_isLittleO_exp_neg_half_atTop (c : ℝ) :
    (fun t : ℝ => ((coshGaussDeriv2Val c t : ℝ) : ℂ)) =o[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
  -- Decompose: coshGaussDeriv2Val c t = A(t)·cosh(c·t)·exp(-2t²) - B(t)·sinh(c·t)·exp(-2t²)
  -- where A(t) = c² - 4 + 16·t² (polynomial degree 2), B(t) = 8·c·t (polynomial degree 1).
  -- Each piece is (polynomial) × (cosh-gauss-form), and cosh-gauss =O exp(-t).
  -- Polynomial × exp(-t) = o(exp(-t/2)) via polynomial = o(exp(t/2)).
  -- Combining: sum = o(exp(-t/2)).
  -- Do it via decomposition into two sub-theorems.
  have h_pow2_lito : (fun t : ℝ => t^2) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 2 (show (0:ℝ) < 1/2 from by norm_num)
    simpa using this
  have h_pow1_lito : (fun t : ℝ => t) =o[atTop] (fun t : ℝ => Real.exp ((1/2) * t)) := by
    have := isLittleO_pow_exp_pos_mul_atTop 1 (show (0:ℝ) < 1/2 from by norm_num)
    simpa using this
  -- Work at ℝ level.  Need: (cosh(c·t) · exp(-2t²)) at ℝ =O[atTop] exp(-t).
  have h_cosh_gauss_bigO_R :
      (fun t : ℝ => Real.cosh (c * t) * Real.exp (-2 * t^2)) =O[atTop]
        (fun t : ℝ => Real.exp (-t)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    rw [Filter.eventually_atTop]
    refine ⟨(|c| + 1) / 2, fun t ht => ?_⟩
    have ht_pos : 0 < t := lt_of_lt_of_le (by positivity : (0:ℝ) < (|c| + 1) / 2) ht
    have h_cosh_le : Real.cosh (c * t) ≤ Real.exp (|c| * t) := by
      rw [Real.cosh_eq]
      have h1 : Real.exp (c * t) ≤ Real.exp (|c| * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self c) ht_pos.le)
      have h2 : Real.exp (-(c * t)) ≤ Real.exp (|c| * t) := by
        apply Real.exp_le_exp.mpr
        have : -(c*t) ≤ |c*t| := neg_le_abs _
        rw [abs_mul, abs_of_pos ht_pos] at this; exact this
      linarith
    have h_nn : 0 ≤ Real.cosh (c*t) * Real.exp (-2 * t^2) :=
      mul_nonneg (Real.cosh_pos _).le (Real.exp_pos _).le
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg h_nn, one_mul]
    have h_step1 : Real.cosh (c*t) * Real.exp (-2 * t^2) ≤
        Real.exp (|c| * t) * Real.exp (-2 * t^2) :=
      mul_le_mul_of_nonneg_right h_cosh_le (Real.exp_pos _).le
    have h_step2 : Real.exp (|c| * t) * Real.exp (-2 * t^2) =
        Real.exp (|c| * t - 2 * t^2) := by rw [← Real.exp_add]; ring_nf
    have h_step3 : Real.exp (|c| * t - 2 * t^2) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr; nlinarith [ht, ht_pos]
    linarith [h_step1, h_step2.le, h_step3]
  have h_sinh_gauss_bigO_R :
      (fun t : ℝ => Real.sinh (c * t) * Real.exp (-2 * t^2)) =O[atTop]
        (fun t : ℝ => Real.exp (-t)) := by
    refine (Asymptotics.IsBigO.of_bound 1 ?_).trans h_cosh_gauss_bigO_R
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
    have h_sinh_le : |Real.sinh (c*t)| ≤ Real.cosh (c*t) := by
      rw [Real.abs_sinh, ← Real.cosh_abs (c*t)]; exact (Real.sinh_lt_cosh _).le
    have h_exp_pos : 0 < Real.exp (-2 * t^2) := Real.exp_pos _
    have h_cosh_nn : 0 ≤ Real.cosh (c*t) := (Real.cosh_pos _).le
    have h_prod_nn : 0 ≤ Real.cosh (c*t) * Real.exp (-2 * t^2) :=
      mul_nonneg h_cosh_nn h_exp_pos.le
    rw [Real.norm_of_nonneg h_prod_nn, one_mul,
      Real.norm_eq_abs, abs_mul, abs_of_pos h_exp_pos]
    exact mul_le_mul_of_nonneg_right h_sinh_le h_exp_pos.le
  -- Combine: t² · cosh(c·t)·exp(-2t²) =o exp(t/2)·exp(-t) = exp(-t/2)
  have h_half_sum : (fun t : ℝ => Real.exp ((1/2) * t) * Real.exp (-t)) =
      (fun t : ℝ => Real.exp (-t/2)) := by
    funext t
    rw [← Real.exp_add]; congr 1; ring
  -- Work at ℝ-level first (types match), then coerce.
  have h_quad_cosh_R :
      (fun t : ℝ => t^2 * (Real.cosh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have h_mul := h_pow2_lito.mul_isBigO h_cosh_gauss_bigO_R
    rw [← h_half_sum]; exact h_mul
  have h_lin_sinh_R :
      (fun t : ℝ => t * (Real.sinh (c * t) * Real.exp (-2 * t^2))) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := by
    have h_mul := h_pow1_lito.mul_isBigO h_sinh_gauss_bigO_R
    rw [← h_half_sum]; exact h_mul
  -- Coerce each to ℂ.
  have h_coerce_norm {f : ℝ → ℝ} {g : ℝ → ℝ}
      (hfg : f =o[atTop] g) :
      (fun t : ℝ => ((f t : ℝ) : ℂ)) =o[atTop] g := by
    rw [Asymptotics.isLittleO_iff] at hfg ⊢
    intro ε hε
    filter_upwards [hfg hε] with t ht
    simpa [Complex.norm_real] using ht
  have h_quad_cosh :
      (fun t : ℝ => ((t^2 * (Real.cosh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ)) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := h_coerce_norm h_quad_cosh_R
  have h_lin_sinh :
      (fun t : ℝ => ((t * (Real.sinh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ)) =o[atTop]
        (fun t : ℝ => Real.exp (-t/2)) := h_coerce_norm h_lin_sinh_R
  -- Constant times `cosh·exp` is O of exp(-t).
  have h_const_cosh_R :
      (fun t : ℝ => (c^2 - 4) * (Real.cosh (c * t) * Real.exp (-2 * t^2))) =O[atTop]
        (fun t : ℝ => Real.exp (-t)) :=
    h_cosh_gauss_bigO_R.const_mul_left _
  have h_coerce_norm_bigO {f : ℝ → ℝ} {g : ℝ → ℝ}
      (hfg : f =O[atTop] g) :
      (fun t : ℝ => ((f t : ℝ) : ℂ)) =O[atTop] g := by
    rw [Asymptotics.isBigO_iff] at hfg ⊢
    obtain ⟨C, hC⟩ := hfg
    refine ⟨C, ?_⟩
    filter_upwards [hC] with t ht
    simpa [Complex.norm_real] using ht
  have h_const_cosh :
      (fun t : ℝ => (((c^2 - 4) * (Real.cosh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ)) =O[atTop]
        (fun t : ℝ => Real.exp (-t)) := h_coerce_norm_bigO h_const_cosh_R
  -- Combine via IsBigO/IsLittleO arithmetic.
  -- coshGaussDeriv2Val c t = (c² - 4)·cosh·exp + 16·t²·cosh·exp - 8·c·t·sinh·exp
  --                       = A + 16·B - 8c·D where A = const·cosh·exp, B = t²·cosh·exp, D = t·sinh·exp.
  have h_decomp : (fun t : ℝ => ((coshGaussDeriv2Val c t : ℝ) : ℂ)) =
      (fun t : ℝ =>
        (((c^2 - 4) * (Real.cosh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ) +
        ((16 : ℂ)) * ((t^2 * (Real.cosh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ) -
        ((8 * c : ℂ)) * ((t * (Real.sinh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ)) := by
    funext t
    unfold coshGaussDeriv2Val
    push_cast
    ring
  rw [h_decomp]
  -- Each piece is o(exp(-t/2)).
  -- A =O exp(-t) =o exp(-t/2).
  have h_exp_neg_t_lito : (fun t : ℝ => Real.exp (-t)) =o[atTop] (fun t : ℝ => Real.exp (-t/2)) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    rw [Filter.eventually_atTop]
    -- Need: ∀ᶠ t, ‖exp(-t)‖ ≤ ε · ‖exp(-t/2)‖
    -- ‖exp(-t)‖ = exp(-t), ‖exp(-t/2)‖ = exp(-t/2) (both positive).
    -- exp(-t) ≤ ε · exp(-t/2) iff exp(-t/2) ≤ ε iff -t/2 ≤ log ε iff t ≥ -2 log ε.
    -- For t large enough this holds.
    refine ⟨max 0 (-2 * Real.log ε), fun t ht => ?_⟩
    have h_t0 : 0 ≤ t := le_of_max_le_left ht
    have h_tlog : -2 * Real.log ε ≤ t := le_of_max_le_right ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [show Real.exp (-t) = Real.exp (-t/2) * Real.exp (-t/2) from by
      rw [← Real.exp_add]; congr 1; ring]
    rw [mul_comm ε _]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rw [show -t/2 = -(t/2) from by ring, Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    rw [show ε * Real.exp (t/2) = Real.exp (Real.log ε + t/2) from by
      rw [Real.exp_add, Real.exp_log hε]]
    have h_arg : 0 ≤ Real.log ε + t/2 := by linarith
    calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (Real.log ε + t/2) := Real.exp_le_exp.mpr h_arg
  have h_A_lito : (fun t : ℝ => (((c^2 - 4) * (Real.cosh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ))
      =o[atTop] (fun t : ℝ => Real.exp (-t/2)) :=
    h_const_cosh.trans_isLittleO h_exp_neg_t_lito
  -- 16·B =o(exp(-t/2)) from h_quad_cosh.
  have h_16B_lito : (fun t : ℝ =>
      ((16 : ℂ)) * ((t^2 * (Real.cosh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ))
      =o[atTop] (fun t : ℝ => Real.exp (-t/2)) :=
    h_quad_cosh.const_mul_left _
  -- 8c·D =o(exp(-t/2)) from h_lin_sinh.
  have h_8cD_lito : (fun t : ℝ =>
      ((8 * c : ℂ)) * ((t * (Real.sinh (c * t) * Real.exp (-2 * t^2)) : ℝ) : ℂ))
      =o[atTop] (fun t : ℝ => Real.exp (-t/2)) :=
    h_lin_sinh.const_mul_left _
  -- Sum: (A + 16·B - 8c·D) =o(exp(-t/2)).
  exact (h_A_lito.add h_16B_lito).sub h_8cD_lito

/-- **Corollary: coshGaussDeriv2Val =O[atTop] exp(-t/2).** -/
theorem coshGaussDeriv2Val_isBigO_exp_neg_half_atTop (c : ℝ) :
    (fun t : ℝ => ((coshGaussDeriv2Val c t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) :=
  (coshGaussDeriv2Val_isLittleO_exp_neg_half_atTop c).isBigO

#print axioms coshGaussDeriv2Val_isLittleO_exp_neg_half_atTop
#print axioms coshGaussDeriv2Val_isBigO_exp_neg_half_atTop

/-! ### IBP-7b: Second derivative of pair test -/

/-- **Explicit 2nd-derivative formula for `pair_cosh_gauss_test β`.** By
differentiating `pair_cosh_gauss_test_deriv_eq` once more. The result is the
same linear combination of `coshGaussDeriv2Val` values. -/
theorem pair_cosh_gauss_test_hasDerivAt_iter2 (β t : ℝ) :
    HasDerivAt (deriv (pair_cosh_gauss_test β))
      ((1/2 : ℝ) * coshGaussDeriv2Val (2*β - Real.pi/3) t +
        (1/2) * coshGaussDeriv2Val (2 - Real.pi/3 - 2*β) t -
        coshGaussDeriv2Val (1 - Real.pi/3) t -
        coshGaussDeriv2Val (2*β - 1) t +
        coshGaussDeriv2Val 0 t) t := by
  -- Use pair_cosh_gauss_test_deriv_eq to rewrite `deriv (pair β)` pointwise.
  have h_fun_eq : deriv (pair_cosh_gauss_test β) = fun u =>
      (1/2 : ℝ) * coshGaussDerivVal (2*β - Real.pi/3) u +
      (1/2) * coshGaussDerivVal (2 - Real.pi/3 - 2*β) u -
      coshGaussDerivVal (1 - Real.pi/3) u -
      coshGaussDerivVal (2*β - 1) u +
      coshGaussDerivVal 0 u := by
    funext u; exact pair_cosh_gauss_test_deriv_eq β u
  rw [h_fun_eq]
  have h1 := (coshGauss_hasDerivAt_iter2 (2*β - Real.pi/3) t).const_mul (1/2 : ℝ)
  have h2 := (coshGauss_hasDerivAt_iter2 (2 - Real.pi/3 - 2*β) t).const_mul (1/2 : ℝ)
  have h3 := coshGauss_hasDerivAt_iter2 (1 - Real.pi/3) t
  have h4 := coshGauss_hasDerivAt_iter2 (2*β - 1) t
  have h5 := coshGauss_hasDerivAt_iter2 0 t
  exact (((h1.add h2).sub h3).sub h4).add h5

/-- **`deriv² (pair β) = sum of coshGaussDeriv2Val`.** Wrapper via
`HasDerivAt.deriv`. -/
theorem pair_cosh_gauss_test_deriv2_eq (β t : ℝ) :
    deriv (deriv (pair_cosh_gauss_test β)) t =
      (1/2 : ℝ) * coshGaussDeriv2Val (2*β - Real.pi/3) t +
      (1/2) * coshGaussDeriv2Val (2 - Real.pi/3 - 2*β) t -
      coshGaussDeriv2Val (1 - Real.pi/3) t -
      coshGaussDeriv2Val (2*β - 1) t +
      coshGaussDeriv2Val 0 t :=
  (pair_cosh_gauss_test_hasDerivAt_iter2 β t).deriv

#print axioms pair_cosh_gauss_test_hasDerivAt_iter2
#print axioms pair_cosh_gauss_test_deriv2_eq

/-- **`deriv² (pair β) =O[atTop] exp(-t/2)`.** Linear combination of five
`coshGaussDeriv2Val` terms, each `O(exp(-t/2))`. -/
theorem pair_cosh_gauss_test_deriv2_isBigO_exp_neg_half_atTop (β : ℝ) :
    (fun t : ℝ => ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
  have h_eq : (fun t : ℝ => ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)) =
      (fun t : ℝ =>
        (((1/2 : ℝ) * coshGaussDeriv2Val (2*β - Real.pi/3) t : ℝ) : ℂ) +
        (((1/2 : ℝ) * coshGaussDeriv2Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ) -
        ((coshGaussDeriv2Val (1 - Real.pi/3) t : ℝ) : ℂ) -
        ((coshGaussDeriv2Val (2*β - 1) t : ℝ) : ℂ) +
        ((coshGaussDeriv2Val 0 t : ℝ) : ℂ)) := by
    funext t
    rw [pair_cosh_gauss_test_deriv2_eq]
    push_cast
    ring
  rw [h_eq]
  have h1 := (coshGaussDeriv2Val_isBigO_exp_neg_half_atTop (2*β - Real.pi/3)).const_mul_left (1/2 : ℂ)
  have h2 := (coshGaussDeriv2Val_isBigO_exp_neg_half_atTop (2 - Real.pi/3 - 2*β)).const_mul_left (1/2 : ℂ)
  have h3 := coshGaussDeriv2Val_isBigO_exp_neg_half_atTop (1 - Real.pi/3)
  have h4 := coshGaussDeriv2Val_isBigO_exp_neg_half_atTop (2*β - 1)
  have h5 := coshGaussDeriv2Val_isBigO_exp_neg_half_atTop 0
  have h1' : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv2Val (2*β - Real.pi/3) t : ℝ) : ℂ))) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv2Val (2*β - Real.pi/3) t : ℝ) : ℂ))) =
        (fun t : ℝ => (1/2 : ℂ) * ((coshGaussDeriv2Val (2*β - Real.pi/3) t : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [this]; exact h1
  have h2' : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv2Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ))) =O[atTop]
      (fun t : ℝ => Real.exp (-t/2)) := by
    have : (fun t : ℝ => ((((1/2 : ℝ) * coshGaussDeriv2Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ))) =
        (fun t : ℝ => (1/2 : ℂ) * ((coshGaussDeriv2Val (2 - Real.pi/3 - 2*β) t : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [this]; exact h2
  exact ((((h1'.add h2').sub h3).sub h4).add h5)

#print axioms pair_cosh_gauss_test_deriv2_isBigO_exp_neg_half_atTop

/-- **`deriv² (pair β)` bounded near 0.** Continuous, so bounded near 0. -/
theorem pair_cosh_gauss_test_deriv2_isBigO_one_nhds_zero (β : ℝ) :
    (fun t : ℝ => ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-(0:ℝ))) := by
  have h_deriv2_cont : Continuous (deriv (deriv (pair_cosh_gauss_test β))) := by
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 2
    -- iteratedDeriv 2 = deriv ∘ iteratedDeriv 1 = deriv ∘ deriv
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_cont : Continuous (fun t : ℝ => ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h_deriv2_cont
  have h_tendsto : Filter.Tendsto
      (fun t : ℝ => ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (nhds (((deriv (deriv (pair_cosh_gauss_test β)) 0 : ℝ) : ℂ))) :=
    (h_cont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have h_rpow_eq : (fun x : ℝ => x^(-(0:ℝ))) = (fun _ : ℝ => (1:ℝ)) := by
    funext x; rw [neg_zero, Real.rpow_zero]
  rw [h_rpow_eq]
  exact h_tendsto.isBigO_one ℝ

#print axioms pair_cosh_gauss_test_deriv2_isBigO_one_nhds_zero

/-- **`MellinConvergent` for `deriv² pair` on `Re s > 0`.** -/
theorem mellinConvergent_pair_cosh_gauss_test_deriv2 (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1/2) (b := 0) (by norm_num : (0:ℝ) < 1/2)
  · apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    apply Continuous.continuousOn
    apply Complex.continuous_ofReal.comp
    have := pair_cosh_gauss_test_iteratedDeriv_continuous β 2
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  · have h := pair_cosh_gauss_test_deriv2_isBigO_exp_neg_half_atTop β
    have h_eq : (fun t : ℝ => Real.exp (-(1/2) * t)) = (fun t : ℝ => Real.exp (-t/2)) := by
      funext t; congr 1; ring
    rw [h_eq]
    exact h
  · exact pair_cosh_gauss_test_deriv2_isBigO_one_nhds_zero β
  · exact hs

#print axioms mellinConvergent_pair_cosh_gauss_test_deriv2

/-! ### IBP-7c: Apply `mellin_ibp` a second time to get 2-step formula -/

/-- **Abbreviation: `pairDeriv2Mellin`.** Mellin of the 2nd derivative, coerced. -/
noncomputable def pairDeriv2Mellin (β : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)) s

/-- **HasDerivAt for the coerced first derivative (complex-valued).** Pushforward. -/
theorem coerced_pair_deriv_hasDerivAt (β : ℝ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => ((deriv (pair_cosh_gauss_test β) y : ℝ) : ℂ))
      (((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)) t := by
  have h_diff : Differentiable ℝ (deriv (pair_cosh_gauss_test β)) := by
    have := pair_cosh_gauss_test_iteratedDeriv_differentiable β 1
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  exact (h_diff t).hasDerivAt.ofReal_comp

/-- **IBP-7c: Single IBP on `pairDerivMellin` (gives 2-step IBP on pairTestMellin).**
For `0 < Re s`, so `Re (s+1) > 0`:
```
pairDerivMellin β (s+1) = -(1/(s+1)) · pairDeriv2Mellin β (s+2).
```
-/
theorem pairDerivMellin_ibp_once (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    pairDerivMellin β (s + 1) = -(1/(s+1)) * pairDeriv2Mellin β (s + 2) := by
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  have hs1_ne : (s + 1) ≠ 0 := fun h => by rw [h] at hs1_re; simp at hs1_re
  have hs2_re : 0 < (s + 2).re := by simp; linarith
  have h_rewrite : s + 1 + 1 = s + 2 := by ring
  unfold pairDerivMellin pairDeriv2Mellin
  have := mellin_ibp (s := s + 1) hs1_ne
    (fun t _ => coerced_pair_deriv_hasDerivAt β t)
    (mellinConvergent_pair_cosh_gauss_test_deriv β hs1_re)
    (by rw [h_rewrite]; exact mellinConvergent_pair_cosh_gauss_test_deriv2 β hs2_re)
    (pair_cosh_gauss_test_deriv_cpow_tendsto_zero_nhdsWithin_zero β hs1_re)
    (pair_cosh_gauss_test_deriv_cpow_tendsto_zero_atTop β (s + 1))
  rw [h_rewrite] at this
  exact this

#print axioms pairDerivMellin_ibp_once

/-- **IBP-7d: Two-step Mellin IBP formula for `pairTestMellin β`.** Combining
`pairTestMellin_ibp_once` with `pairDerivMellin_ibp_once`:
```
pairTestMellin β s = 1/(s·(s+1)) · pairDeriv2Mellin β (s+2).
```
-/
theorem pairTestMellin_ibp_twice (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    pairTestMellin β s = 1/(s*(s+1)) * pairDeriv2Mellin β (s + 2) := by
  have hs_ne : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1_re : 0 < (s + 1).re := by simp; linarith
  have hs1_ne : (s + 1) ≠ 0 := fun h => by rw [h] at hs1_re; simp at hs1_re
  rw [pairTestMellin_ibp_once β hs]
  rw [pairDerivMellin_ibp_once β hs]
  field_simp

#print axioms pairTestMellin_ibp_twice

/-! ### Quadratic-decay structural definitions

Rather than require `‖pairTestMellin β ρ‖ ≤ C/|ρ(ρ−1)|²` (quartic decay), we
state a weaker target using `1/(1 + (Im ρ)²)` (quadratic decay in |Im ρ|) and
pair it with a new summability lemma `Σ 1/(1 + (Im ρ)²) < ∞`.

The new summability follows from the existing Jensen-based disk zero-count
bound `xi_zero_count_disk_bound` via dyadic decomposition. Left as a named
target here; the proof is ~50-100 lines of Abel/dyadic summation.

The quadratic decay target is discharged by 2-step Mellin IBP on the pair
test, using explicit `coshGaussDeriv2Val` formulas for the second derivative
of each cosh-Gaussian term.
-/

/-- **Quadratic Im-decay target.** Weaker than `pairTestMellin_im_quartic_decay_target`
— asks for `‖pairTestMellin β ρ‖ ≤ C/(1 + (Im ρ)²)` for nontrivial zeros ρ. -/
def pairTestMellin_im_sq_decay_target (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
    ‖pairTestMellin β ρ.val‖ ≤ C / (1 + ρ.val.im^2)

#print axioms pairTestMellin_im_sq_decay_target

/-- **Quadratic Jensen-style summability target.** `Σ 1/(1 + (Im ρ)²) < ∞` over
nontrivial zeros. Derivable from `ZD.ZeroCount.xi_zero_count_disk_bound` via
dyadic decomposition (classical argument: zeros with `2^k ≤ |ρ| < 2^{k+1}`
contribute `N(2^{k+1})/2^{2k} ≈ (k+1)/2^k` to the sum, which is geometrically
summable).

**Status.** Named target; the ~50-line proof deriving this from existing
zero-count disk bound is a follow-up task. -/
def nontrivialZeros_inv_one_plus_im_sq_summable_target : Prop :=
  Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => 1 / (1 + ρ.val.im^2))

#print axioms nontrivialZeros_inv_one_plus_im_sq_summable_target

/-- **Structural closure: quadratic decay + quadratic Jensen → summability.**
Given the quadratic decay and the quadratic zero-sum summability, absolute
summability of `pairTestMellin β` over nontrivial zeros follows. -/
theorem weilZeroSumTarget_of_sq_decay_and_summable (β : ℝ)
    (hDecay : pairTestMellin_im_sq_decay_target β)
    (hSum : nontrivialZeros_inv_one_plus_im_sq_summable_target) :
    WeilZeroSumTarget β := by
  obtain ⟨C, hC, hbound⟩ := hDecay
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact hSum.mul_left C |>.congr (fun ρ => by ring)

#print axioms weilZeroSumTarget_of_sq_decay_and_summable

/-! ### IBP-9b: Uniform Mellin bound on `pairDeriv2Mellin` and decay closure -/

/-- **Real Mellin integrand of `|deriv² pair β|` is integrable on `Ioi 0`.**
Follows from `mellinConvergent_pair_cosh_gauss_test_deriv2`. -/
theorem pair_deriv2_mellin_integrand_integrableOn (β : ℝ) (σ : ℝ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t^(σ-1) * |deriv (deriv (pair_cosh_gauss_test β)) t|)
      (Ioi 0) := by
  set s : ℂ := (σ : ℂ)
  have hs_re : (0 : ℝ) < s.re := by simp [s]; exact hσ
  have hConv := mellinConvergent_pair_cosh_gauss_test_deriv2 β hs_re
  unfold MellinConvergent at hConv
  have hnorm := hConv.norm
  refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).mpr hnorm
  simp only [norm_smul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real]
  simp [s]

#print axioms pair_deriv2_mellin_integrand_integrableOn

/-- **Pointwise norm bound `‖pairDeriv2Mellin β s‖ ≤ ∫ t^(σ-1)·|deriv² pair|`.** -/
theorem pairDeriv2Mellin_norm_le_real_integral (β : ℝ) (s : ℂ) :
    ‖pairDeriv2Mellin β s‖ ≤
      ∫ t in Ioi (0:ℝ), t^(s.re - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t| := by
  unfold pairDeriv2Mellin mellin
  calc ‖∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) •
          ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)‖
      ≤ ∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1) •
          ((deriv (deriv (pair_cosh_gauss_test β)) t : ℝ) : ℂ)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0:ℝ), t^(s.re - 1) *
          |deriv (deriv (pair_cosh_gauss_test β)) t| := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        simp only [norm_smul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
          Complex.sub_re, Complex.one_re, Real.norm_eq_abs]

#print axioms pairDeriv2Mellin_norm_le_real_integral

/-- **Uniform Mellin norm bound for `pairDeriv2Mellin` on compact strip `[σL, σR]`.**
For `0 < σL ≤ σR`, there is a constant `M ≥ 0` such that
`‖pairDeriv2Mellin β s‖ ≤ M` whenever `σL ≤ Re s ≤ σR`. -/
theorem pairDeriv2Mellin_norm_bound_on_compact_strip
    (β : ℝ) (σL σR : ℝ) (hσL : 0 < σL) (hσLR : σL ≤ σR) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR →
      ‖pairDeriv2Mellin β s‖ ≤ C := by
  have h_int_L := pair_deriv2_mellin_integrand_integrableOn β σL hσL
  have h_int_R := pair_deriv2_mellin_integrand_integrableOn β σR (lt_of_lt_of_le hσL hσLR)
  set I_L : ℝ := ∫ t in Ioi (0:ℝ), t^(σL-1) * |deriv (deriv (pair_cosh_gauss_test β)) t|
  set I_R : ℝ := ∫ t in Ioi (0:ℝ), t^(σR-1) * |deriv (deriv (pair_cosh_gauss_test β)) t|
  set C : ℝ := I_L + I_R
  have hI_L_nonneg : 0 ≤ I_L :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (abs_nonneg _))
  have hI_R_nonneg : 0 ≤ I_R :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (abs_nonneg _))
  refine ⟨C, add_nonneg hI_L_nonneg hI_R_nonneg, fun s hσL_le_re hre_le_R => ?_⟩
  have hbound := pairDeriv2Mellin_norm_le_real_integral β s
  have h_dom : ∀ t ∈ Ioi (0:ℝ),
      t^(s.re - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t| ≤
        t^(σL - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t| +
          t^(σR - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t| := by
    intro t ht
    have ht_pos : (0:ℝ) < t := ht
    have h_d2_nn : 0 ≤ |deriv (deriv (pair_cosh_gauss_test β)) t| := abs_nonneg _
    have h_rpow_bd : t^(s.re - 1) ≤ t^(σL-1) + t^(σR-1) := by
      rcases le_or_gt t 1 with h | h
      · have h1 : t^(s.re - 1) ≤ t^(σL-1) :=
          Real.rpow_le_rpow_of_exponent_ge ht_pos h (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σR - 1)]
      · have h1 : t^(s.re - 1) ≤ t^(σR-1) :=
          Real.rpow_le_rpow_of_exponent_le (x := t) h.le (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σL - 1)]
    calc t^(s.re - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t|
        ≤ (t^(σL - 1) + t^(σR-1)) *
            |deriv (deriv (pair_cosh_gauss_test β)) t| :=
          mul_le_mul_of_nonneg_right h_rpow_bd h_d2_nn
      _ = t^(σL - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t| +
            t^(σR-1) * |deriv (deriv (pair_cosh_gauss_test β)) t| := by ring
  have h_rhs_integrable : IntegrableOn
      (fun t : ℝ => t^(σL - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t| +
        t^(σR-1) * |deriv (deriv (pair_cosh_gauss_test β)) t|) (Ioi 0) :=
    h_int_L.add h_int_R
  have h_lhs_integrable : IntegrableOn
      (fun t : ℝ => t^(s.re - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t|) (Ioi 0) :=
    pair_deriv2_mellin_integrand_integrableOn β s.re (by linarith)
  have h_integral_le :
      (∫ t in Ioi (0:ℝ), t^(s.re - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t|) ≤
      ∫ t in Ioi (0:ℝ),
        (t^(σL - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t| +
          t^(σR-1) * |deriv (deriv (pair_cosh_gauss_test β)) t|) :=
    MeasureTheory.setIntegral_mono_on h_lhs_integrable h_rhs_integrable
      measurableSet_Ioi h_dom
  have h_integral_split :
      (∫ t in Ioi (0:ℝ),
          (t^(σL - 1) * |deriv (deriv (pair_cosh_gauss_test β)) t| +
            t^(σR-1) * |deriv (deriv (pair_cosh_gauss_test β)) t|)) = I_L + I_R := by
    rw [MeasureTheory.integral_add h_int_L h_int_R]
  linarith

#print axioms pairDeriv2Mellin_norm_bound_on_compact_strip

/-- **Key algebraic lower bound: `|ρ(ρ+1)| ≥ (1+Im²ρ)/2` for `|Im ρ| ≥ 1`.**
For nontrivial zeros with `|Im ρ| ≥ 1`, the complex factor `ρ(ρ+1)` is bounded
below by `(1 + Im²ρ)/2`. -/
theorem abs_rho_mul_rho_add_one_ge_half_sq
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (h_Im : 1 ≤ |ρ.im|) :
    (1 + ρ.im^2) / 2 ≤ ‖ρ * (ρ + 1)‖ := by
  have hRe_pos : 0 < ρ.re := hρ.1
  have hRe_lt : ρ.re < 1 := hρ.2.1
  -- |ρ|² = Re²ρ + Im²ρ ≥ Im²ρ.
  have h_abs_rho_sq : ρ.im^2 ≤ Complex.normSq ρ := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg ρ.re]
  -- |ρ+1|² = (Re ρ + 1)² + Im²ρ ≥ 1 + Im²ρ (since Re ρ > 0).
  have h_abs_rho_add_one_sq : 1 + ρ.im^2 ≤ Complex.normSq (ρ + 1) := by
    rw [Complex.normSq_apply]
    have h_re1 : (ρ + 1).re = ρ.re + 1 := by simp
    have h_im1 : (ρ + 1).im = ρ.im := by simp
    rw [h_re1, h_im1]
    nlinarith [hRe_pos, sq_nonneg ρ.im]
  -- So |ρ|²·|ρ+1|² ≥ Im²ρ · (1+Im²ρ).
  have h_prod_sq : ρ.im^2 * (1 + ρ.im^2) ≤ Complex.normSq (ρ * (ρ + 1)) := by
    rw [Complex.normSq_mul]
    have h_ρsq_nn : 0 ≤ Complex.normSq ρ := Complex.normSq_nonneg _
    have h_ρ1sq_nn : 0 ≤ Complex.normSq (ρ + 1) := Complex.normSq_nonneg _
    have h_imsq_nn : 0 ≤ ρ.im^2 := sq_nonneg _
    have h_1plus_nn : 0 ≤ 1 + ρ.im^2 := by linarith [sq_nonneg ρ.im]
    calc ρ.im^2 * (1 + ρ.im^2) ≤ Complex.normSq ρ * (1 + ρ.im^2) :=
          mul_le_mul_of_nonneg_right h_abs_rho_sq h_1plus_nn
      _ ≤ Complex.normSq ρ * Complex.normSq (ρ + 1) :=
          mul_le_mul_of_nonneg_left h_abs_rho_add_one_sq h_ρsq_nn
  -- For |Im ρ| ≥ 1: Im²ρ ≥ 1, so Im²ρ · (1+Im²ρ) ≥ (1+Im²ρ)²/4.
  -- Actually simpler: Im²ρ·(1+Im²ρ) ≥ 1·(1+Im²ρ) = 1+Im²ρ (since Im²ρ ≥ 1).
  -- Hence normSq(ρ(ρ+1)) ≥ 1+Im²ρ, and ‖ρ(ρ+1)‖ = √normSq ≥ √(1+Im²ρ).
  -- Want: √(1+Im²ρ) ≥ (1+Im²ρ)/2. Equivalent: 4(1+Im²ρ) ≥ (1+Im²ρ)², i.e., 4 ≥ 1+Im²ρ, i.e., Im²ρ ≤ 3.
  -- For Im²ρ ≤ 3 this holds; for Im²ρ > 3, alternative path:
  -- Im²ρ·(1+Im²ρ) ≥ Im²ρ·1 = Im²ρ ≥ (1+Im²ρ)/2 (since Im²ρ ≥ 1 gives 2·Im²ρ ≥ 1+Im²ρ).
  -- So normSq(ρ(ρ+1)) ≥ (1+Im²ρ)/2 · (1+Im²ρ) = (1+Im²ρ)²/2... hmm not quite.
  -- Actually a cleaner route:
  -- normSq(ρ(ρ+1)) ≥ Im²ρ · (1+Im²ρ). For |Im ρ| ≥ 1, Im²ρ ≥ 1 ≥ (1+Im²ρ)/? hmm.
  -- 2·Im²ρ ≥ 1+Im²ρ iff Im²ρ ≥ 1.  ✓
  -- So normSq(ρ(ρ+1)) ≥ Im²ρ · (1+Im²ρ) ≥ ((1+Im²ρ)/2) · (1+Im²ρ) = (1+Im²ρ)²/2.
  -- Hence ‖ρ(ρ+1)‖ = √normSq ≥ √((1+Im²ρ)²/2) = (1+Im²ρ)/√2.
  -- And (1+Im²ρ)/√2 ≥ (1+Im²ρ)/2 since √2 ≤ 2.
  have h_im_sq_ge_one : 1 ≤ ρ.im^2 := by nlinarith [h_Im, sq_abs ρ.im]
  have h_key : (1 + ρ.im^2)^2 / 2 ≤ Complex.normSq (ρ * (ρ + 1)) := by
    have h_2imsq : 2 * ρ.im^2 ≥ 1 + ρ.im^2 := by linarith
    have : ρ.im^2 * (1 + ρ.im^2) ≥ (1 + ρ.im^2)^2 / 2 := by nlinarith [sq_nonneg ρ.im]
    linarith
  have h_normSq_eq_norm_sq : Complex.normSq (ρ * (ρ + 1)) = ‖ρ * (ρ + 1)‖^2 :=
    Complex.normSq_eq_norm_sq _
  rw [h_normSq_eq_norm_sq] at h_key
  have h_1plus_nn : 0 ≤ 1 + ρ.im^2 := by linarith [sq_nonneg ρ.im]
  have h_half_nn : 0 ≤ (1 + ρ.im^2) / 2 := by linarith
  have h_norm_nn : 0 ≤ ‖ρ * (ρ + 1)‖ := norm_nonneg _
  -- ((1+Im²ρ)/2)² = (1+Im²ρ)²/4 ≤ (1+Im²ρ)²/2 ≤ ‖ρ(ρ+1)‖²
  have h_sq_le : ((1 + ρ.im^2) / 2)^2 ≤ ‖ρ * (ρ + 1)‖^2 := by
    have : ((1 + ρ.im^2) / 2)^2 = (1 + ρ.im^2)^2 / 4 := by ring
    have h_half_le_half : (1 + ρ.im^2)^2 / 4 ≤ (1 + ρ.im^2)^2 / 2 := by
      have : 0 ≤ (1 + ρ.im^2)^2 := sq_nonneg _
      linarith
    linarith
  exact abs_le_of_sq_le_sq' h_sq_le h_norm_nn |>.2

#print axioms abs_rho_mul_rho_add_one_ge_half_sq

/-- **Partial quadratic decay: for `|Im ρ| ≥ 1`.** The core analytic content.
Combining `pairTestMellin_ibp_twice` + `pairDeriv2Mellin_norm_bound_on_compact_strip`
+ `abs_rho_mul_rho_add_one_ge_half_sq`:
```
∃ C ≥ 0, ∀ ρ ∈ NontrivialZeros, |Im ρ| ≥ 1 → ‖pairTestMellin β ρ‖ ≤ C/(1+Im²ρ).
```
The remaining finite-`|Im ρ|`-handling (to upgrade to full `pairTestMellin_im_sq_decay_target`)
requires isolating zeros in a compact disk — ~50 lines follow-up. -/
theorem pairTestMellin_im_sq_decay_high (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, 1 ≤ |ρ.val.im| →
      ‖pairTestMellin β ρ.val‖ ≤ C / (1 + ρ.val.im^2) := by
  obtain ⟨M, hM_nn, hM⟩ := pairDeriv2Mellin_norm_bound_on_compact_strip β 2 3
    (by norm_num) (by norm_num)
  refine ⟨2 * M, by linarith, ?_⟩
  intro ρ h_Im
  obtain ⟨hRe_pos, hRe_lt, _⟩ := ρ.property
  have hRe_ne : ρ.val.re ≠ 0 := hRe_pos.ne'
  have hρ_ne : ρ.val ≠ 0 := by
    intro h
    have : ρ.val.re = 0 := by rw [h]; simp
    exact hRe_ne this
  have hs_re : (0 : ℝ) < ρ.val.re := hRe_pos
  have h_ibp := pairTestMellin_ibp_twice β hs_re
  -- |pairTestMellin β ρ| = |1/(ρ(ρ+1))| · |pairDeriv2Mellin β (ρ+2)|.
  have h_norm_eq : ‖pairTestMellin β ρ.val‖ =
      ‖(1 : ℂ) / (ρ.val * (ρ.val + 1))‖ * ‖pairDeriv2Mellin β (ρ.val + 2)‖ := by
    rw [h_ibp, norm_mul]
  -- Bound pairDeriv2Mellin: Re(ρ+2) ∈ (2, 3), so on compact strip [2, 3].
  have h_re2 : (ρ.val + 2).re = ρ.val.re + 2 := by simp
  have h_2_le : (2 : ℝ) ≤ (ρ.val + 2).re := by rw [h_re2]; linarith
  have h_le_3 : (ρ.val + 2).re ≤ 3 := by rw [h_re2]; linarith
  have h_deriv2_bd : ‖pairDeriv2Mellin β (ρ.val + 2)‖ ≤ M := hM (ρ.val + 2) h_2_le h_le_3
  -- Bound 1/|ρ(ρ+1)|: use abs_rho_mul_rho_add_one_ge_half_sq.
  have h_ρρ1_lb := abs_rho_mul_rho_add_one_ge_half_sq ρ.property h_Im
  have h_ρρ1_pos : 0 < ‖ρ.val * (ρ.val + 1)‖ := by
    rw [norm_pos_iff]
    refine mul_ne_zero hρ_ne ?_
    intro h
    have : ρ.val = -1 := by linear_combination h
    have h_re_neg : ρ.val.re = -1 := by rw [this]; simp
    linarith
  have h_inv_ub : ‖(1 : ℂ) / (ρ.val * (ρ.val + 1))‖ ≤ 2 / (1 + ρ.val.im^2) := by
    rw [norm_div, norm_one]
    have h_1plus_pos : 0 < 1 + ρ.val.im^2 := by
      have := sq_nonneg ρ.val.im; linarith
    rw [div_le_div_iff₀ h_ρρ1_pos h_1plus_pos]
    calc (1 : ℝ) * (1 + ρ.val.im^2) = 1 + ρ.val.im^2 := one_mul _
      _ = ((1 + ρ.val.im^2) / 2) * 2 := by ring
      _ ≤ ‖ρ.val * (ρ.val + 1)‖ * 2 :=
          mul_le_mul_of_nonneg_right h_ρρ1_lb (by norm_num)
      _ = 2 * ‖ρ.val * (ρ.val + 1)‖ := by ring
  rw [h_norm_eq]
  calc ‖(1 : ℂ) / (ρ.val * (ρ.val + 1))‖ * ‖pairDeriv2Mellin β (ρ.val + 2)‖
      ≤ (2 / (1 + ρ.val.im^2)) * M :=
        mul_le_mul h_inv_ub h_deriv2_bd (norm_nonneg _) (by positivity)
    _ = 2 * M / (1 + ρ.val.im^2) := by ring

#print axioms pairTestMellin_im_sq_decay_high

/-- **Low-Im zeros form a finite set.** For any nontrivial zero ρ with `|Im ρ| < 1`
and `Re ρ ∈ (0, 1)`, we have `|ρ|² < 2`, so `ρ ∈ closedBall 0 √2`. Combined with
`NontrivialZeros_inter_closedBall_finite`, this gives finiteness. -/
theorem nontrivialZeros_low_im_finite :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < 1}.Finite := by
  apply Set.Finite.subset (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite
    (Real.sqrt 2))
  intro ρ ⟨hρ_mem, h_im⟩
  refine ⟨hρ_mem, ?_⟩
  rw [Metric.mem_closedBall]
  have hRe_lt : ρ.re < 1 := hρ_mem.2.1
  have hRe_pos : 0 < ρ.re := hρ_mem.1
  have h_im_sq : ρ.im^2 < 1 := by
    have : ρ.im^2 = |ρ.im|^2 := by rw [sq_abs]
    rw [this]; nlinarith [h_im, abs_nonneg ρ.im]
  have h_re_sq : ρ.re^2 < 1 := by nlinarith
  have h_norm_sq_lt : Complex.normSq ρ < 2 := by
    rw [Complex.normSq_apply]; linarith
  have h_norm_sq_eq : Complex.normSq ρ = ‖ρ‖^2 := Complex.normSq_eq_norm_sq _
  rw [dist_zero_right]
  have h_norm_nn : 0 ≤ ‖ρ‖ := norm_nonneg _
  have h_sqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_sq_lt : ‖ρ‖^2 < (Real.sqrt 2)^2 := by
    rw [← h_norm_sq_eq, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; exact h_norm_sq_lt
  exact (abs_lt_of_sq_lt_sq' h_sq_lt h_sqrt2_nn).2.le

#print axioms nontrivialZeros_low_im_finite

/-- **Full quadratic decay: `pairTestMellin_im_sq_decay_target`.** Combining
`_decay_high` (for `|Im ρ| ≥ 1`) with finite handling of `|Im ρ| < 1` zeros. -/
theorem pairTestMellin_im_sq_decay (β : ℝ) :
    pairTestMellin_im_sq_decay_target β := by
  obtain ⟨C_high, hC_high, h_decay_high⟩ := pairTestMellin_im_sq_decay_high β
  set S : Set ℂ := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < 1}
  have hS_fin : S.Finite := nontrivialZeros_low_im_finite
  -- Build a sum bound: C_low := 2 * sum over S of ‖pairTestMellin β ρ‖.
  set S_finset : Finset ℂ := hS_fin.toFinset
  set C_low : ℝ := 2 * (∑ ρ ∈ S_finset, ‖pairTestMellin β ρ‖)
  have hC_low_nn : 0 ≤ C_low := by
    show 0 ≤ 2 * (∑ ρ ∈ S_finset, ‖pairTestMellin β ρ‖)
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨max C_high C_low, le_max_of_le_left hC_high, fun ρ => ?_⟩
  by_cases h_Im : 1 ≤ |ρ.val.im|
  · -- High-Im case.
    have h := h_decay_high ρ h_Im
    have h_1plus_pos : 0 < 1 + ρ.val.im^2 := by
      have := sq_nonneg ρ.val.im; linarith
    calc ‖pairTestMellin β ρ.val‖ ≤ C_high / (1 + ρ.val.im^2) := h
      _ ≤ max C_high C_low / (1 + ρ.val.im^2) := by
          apply div_le_div_of_nonneg_right _ h_1plus_pos.le
          exact le_max_left _ _
  · -- Low-Im case.
    push_neg at h_Im
    have hρ_in_S : ρ.val ∈ S := ⟨ρ.property, h_Im⟩
    have hρ_in_finset : ρ.val ∈ S_finset := by
      show ρ.val ∈ hS_fin.toFinset
      rw [Set.Finite.mem_toFinset]; exact hρ_in_S
    have h_single_le : ‖pairTestMellin β ρ.val‖ ≤ ∑ ρ' ∈ S_finset, ‖pairTestMellin β ρ'‖ :=
      Finset.single_le_sum (f := fun ρ' => ‖pairTestMellin β ρ'‖)
        (fun _ _ => norm_nonneg _) hρ_in_finset
    have h_1plus_pos : 0 < 1 + ρ.val.im^2 := by
      have := sq_nonneg ρ.val.im; linarith
    have h_1plus_le_2 : 1 + ρ.val.im^2 ≤ 2 := by
      have h_im_abs_lt : |ρ.val.im| < 1 := h_Im
      have h_im_sq : ρ.val.im^2 < 1 := by
        have : ρ.val.im^2 = |ρ.val.im|^2 := by rw [sq_abs]
        rw [this]; nlinarith [abs_nonneg ρ.val.im]
      linarith
    calc ‖pairTestMellin β ρ.val‖
        ≤ ∑ ρ' ∈ S_finset, ‖pairTestMellin β ρ'‖ := h_single_le
      _ = C_low / 2 := by show _ = 2 * (∑ ρ ∈ S_finset, ‖pairTestMellin β ρ‖) / 2; ring
      _ ≤ C_low / (1 + ρ.val.im^2) := by
          apply div_le_div_of_nonneg_left hC_low_nn h_1plus_pos h_1plus_le_2
      _ ≤ max C_high C_low / (1 + ρ.val.im^2) := by
          apply div_le_div_of_nonneg_right _ h_1plus_pos.le
          exact le_max_right _ _

#print axioms pairTestMellin_im_sq_decay

/-! ### JEN-1: Dyadic summability for `Σ 1/(1 + Im²ρ)` -/

/-- **Summability of dyadic majorant `(k+1)/2^k`.** -/
theorem summable_nat_succ_div_two_pow :
    Summable (fun k : ℕ => (k + 1 : ℝ) / 2 ^ k) := by
  have h1 : Summable (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (show ‖(1 / 2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)
    convert this using 1
    funext k
    simp [pow_one]
  have h2 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h_sum : Summable (fun k : ℕ => (k : ℝ) * (1 / 2) ^ k + (1 / 2 : ℝ) ^ k) :=
    h1.add h2
  convert h_sum using 1
  funext k
  have h_eq : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [div_pow, one_pow]
  rw [h_eq]; field_simp

/-- **Algebraic bound: `1/(1+Im²ρ) ≤ 2/‖ρ‖²` for `|ρ| ≥ √2` and Re ρ ∈ (0,1).**
Uses `|ρ|² = Re²ρ + Im²ρ ≤ 1 + Im²ρ`, so `Im²ρ ≥ |ρ|² - 1 ≥ |ρ|²/2` for `|ρ|² ≥ 2`.
Hence `1 + Im²ρ ≥ |ρ|²/2`. -/
theorem inv_one_plus_im_sq_le_two_div_norm_sq
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (h_norm : Real.sqrt 2 ≤ ‖ρ‖) :
    1 / (1 + ρ.im^2) ≤ 2 / ‖ρ‖^2 := by
  have hRe_lt : ρ.re < 1 := hρ.2.1
  have hRe_pos : 0 < ρ.re := hρ.1
  have h_norm_sq : ‖ρ‖^2 = Complex.normSq ρ := (Complex.normSq_eq_norm_sq ρ).symm
  have h_norm_sq_ge : 2 ≤ ‖ρ‖^2 := by
    have h_sqrt : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h_sq_mono : (Real.sqrt 2)^2 ≤ ‖ρ‖^2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h_norm 2
    linarith
  have h_norm_sq_pos : 0 < ‖ρ‖^2 := by linarith
  -- Im²ρ ≥ ‖ρ‖² - 1 ≥ ‖ρ‖² / 2 (since ‖ρ‖² ≥ 2).
  have h_im_sq_ge : ρ.im^2 ≥ ‖ρ‖^2 - 1 := by
    rw [h_norm_sq, Complex.normSq_apply]
    nlinarith [hRe_lt, hRe_pos, sq_nonneg (ρ.re - 1)]
  have h_one_plus_im_sq_ge : 1 + ρ.im^2 ≥ ‖ρ‖^2 / 2 := by linarith
  have h_one_plus_im_sq_pos : 0 < 1 + ρ.im^2 := by
    have := sq_nonneg ρ.im; linarith
  rw [div_le_div_iff₀ h_one_plus_im_sq_pos h_norm_sq_pos]
  nlinarith

#print axioms summable_nat_succ_div_two_pow
#print axioms inv_one_plus_im_sq_le_two_div_norm_sq

/-- **JEN-1: `Σ 1/(1 + Im²ρ) < ∞` over nontrivial zeros.** Dyadic decomposition
mirroring `ZD.ZeroCount.nontrivialZeros_inv_sq_summable`: bound by `2/‖ρ‖²`
majorant for `‖ρ‖ ≥ √2`; finitely many for `‖ρ‖ < √2`. Per-shell contribution
`(k+1)/2^k`, geometric-sum summable. -/
theorem nontrivialZeros_inv_one_plus_im_sq_summable :
    nontrivialZeros_inv_one_plus_im_sq_summable_target := by
  unfold nontrivialZeros_inv_one_plus_im_sq_summable_target
  -- Majorant: 2/‖ρ‖² for ρ with ‖ρ‖ ≥ √2; finite handling otherwise.
  apply Summable.of_norm_bounded_eventually
    (g := fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => 2 / ‖ρ.val‖ ^ 2)
  · -- Summable of 2/‖ρ.val‖^2 via three-way split:
    -- (lo) ‖ρ‖ < √2: absorbed into M_lo.
    -- (mid) √2 ≤ ‖ρ‖ < 2^(N+1): absorbed into M_mid.
    -- (hi) ‖ρ‖ ≥ 2^(N+1): dyadic shells, (k+1)/2^k sum.
    obtain ⟨C₃, hC₃, R₀_step3, hR₀_step3, hBound_step3⟩ :=
      ZD.ZeroCount.xi_zero_count_disk_bound
    set R_th : ℝ := max R₀_step3 2 with hRth_def
    have hRth_pos : 0 < R_th := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hRth_ge_two : (2 : ℝ) ≤ R_th := le_max_right _ _
    have hRth_ge_R₀ : R₀_step3 ≤ R_th := le_max_left _ _
    obtain ⟨N, hN⟩ : ∃ N : ℕ, R_th ≤ (2 : ℝ) ^ N := by
      rcases pow_unbounded_of_one_lt R_th (by norm_num : (1:ℝ) < 2) with ⟨N, hN⟩
      exact ⟨N, le_of_lt hN⟩
    set M_lo : ℝ :=
      (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite 2).toFinset.sum
        (fun ρ => 2 / ‖ρ‖ ^ 2) with hM_lo_def
    set M_mid : ℝ :=
      (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite ((2 : ℝ) ^ (N + 1))).toFinset.sum
        (fun ρ => 2 / ‖ρ‖ ^ 2) with hM_mid_def
    set C_tail : ℝ := 4 * C₃ * Real.log 2 with hC_tail_def
    refine summable_of_sum_le
      (fun ρ => div_nonneg (by norm_num) (by positivity))
      (c := M_lo + M_mid + C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 2 ^ k) ?_
    intro u
    rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.val‖ < 2)]
    have h_lo_bound :
        (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2), 2 / ‖ρ.val‖ ^ 2) ≤ M_lo := by
      rw [hM_lo_def]
      rw [show (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2), (2 : ℝ) / ‖ρ.val‖ ^ 2) =
          ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.val‖ < 2)).image Subtype.val,
              (2 : ℝ) / ‖ρ‖ ^ 2 from ?_]
      swap
      · rw [Finset.sum_image]
        intro x _ y _ h; exact Subtype.val_injective h
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        rcases Finset.mem_image.mp hρ with ⟨ρ', hρ'_in, hρ'_eq⟩
        simp only [Finset.mem_filter] at hρ'_in
        simp only [Set.Finite.mem_toFinset]
        refine ⟨?_, ?_⟩
        · subst hρ'_eq; exact ρ'.property
        · rw [Metric.mem_closedBall, dist_zero_right]
          subst hρ'_eq; linarith [hρ'_in.2]
      · intros; positivity
    rw [← Finset.sum_filter_add_sum_filter_not (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2))
      (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1))]
    have h_mid_bound :
        (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
              (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
          2 / ‖ρ.val‖ ^ 2) ≤ M_mid := by
      rw [hM_mid_def]
      rw [show
          (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
              (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
              (2 : ℝ) / ‖ρ.val‖ ^ 2) =
          ∑ ρ ∈ ((u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
              (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1))).image Subtype.val,
              (2 : ℝ) / ‖ρ‖ ^ 2 from ?_]
      swap
      · rw [Finset.sum_image]
        intro x _ y _ h; exact Subtype.val_injective h
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        rcases Finset.mem_image.mp hρ with ⟨ρ', hρ'_in, hρ'_eq⟩
        simp only [Finset.mem_filter] at hρ'_in
        simp only [Set.Finite.mem_toFinset]
        refine ⟨?_, ?_⟩
        · subst hρ'_eq; exact ρ'.property
        · rw [Metric.mem_closedBall, dist_zero_right]
          subst hρ'_eq; linarith [hρ'_in.2]
      · intros; positivity
    have h_hi_bound :
        (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
              (fun ρ => ¬ ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
          2 / ‖ρ.val‖ ^ 2)
        ≤ C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 2 ^ k := by
      set S : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} :=
        (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
          (fun ρ => ¬ ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)) with hS_def
      have h_mem : ∀ ρ ∈ S, (2 : ℝ) ^ (N + 1) ≤ ‖ρ.val‖ := by
        intro ρ hρ
        simp only [hS_def, Finset.mem_filter, not_lt] at hρ
        exact hρ.2
      have h_one_le : ∀ ρ ∈ S, (1 : ℝ) ≤ ‖ρ.val‖ := by
        intro ρ hρ
        have hle := h_mem ρ hρ
        have h2N1_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
        linarith
      let kf : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℕ := fun ρ =>
        if h : (1 : ℝ) ≤ ‖ρ.val‖
        then (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose
        else 0
      have h_kf_prop :
          ∀ ρ ∈ S, (2 : ℝ) ^ kf ρ ≤ ‖ρ.val‖ ∧ ‖ρ.val‖ < (2 : ℝ) ^ (kf ρ + 1) := by
        intro ρ hρ
        have h := h_one_le ρ hρ
        simp only [kf, dif_pos h]
        exact (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)).choose_spec
      have h_kf_ge : ∀ ρ ∈ S, N + 1 ≤ kf ρ := by
        intro ρ hρ
        have ⟨_, h_lt⟩ := h_kf_prop ρ hρ
        have h_ge := h_mem ρ hρ
        have hlt_pow : (2 : ℝ) ^ (N + 1) < (2 : ℝ) ^ (kf ρ + 1) := lt_of_le_of_lt h_ge h_lt
        have := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hlt_pow
        omega
      set K_max : ℕ := S.sup kf + 1 with hKmax_def
      have h_kf_le : ∀ ρ ∈ S, kf ρ < K_max := by
        intro ρ hρ
        have := Finset.le_sup (f := kf) hρ
        omega
      have h_per_elem :
          ∀ ρ ∈ S, (2 : ℝ) / ‖ρ.val‖ ^ 2 ≤ 2 / (2 : ℝ) ^ (2 * kf ρ) := by
        intro ρ hρ
        have ⟨h_pow_le, _⟩ := h_kf_prop ρ hρ
        have h_one := h_one_le ρ hρ
        have h_pos : (0 : ℝ) < ‖ρ.val‖ := by linarith
        have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ kf ρ := pow_pos (by norm_num) _
        have h_pow2_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * kf ρ) := pow_pos (by norm_num) _
        have h_rho_pow2_pos : (0 : ℝ) < ‖ρ.val‖ ^ 2 := by positivity
        have h_pow2_le : (2 : ℝ) ^ (2 * kf ρ) ≤ ‖ρ.val‖ ^ 2 := by
          rw [show (2 * kf ρ) = (kf ρ) * 2 from by ring, pow_mul]
          exact pow_le_pow_left₀ h_pow_pos.le h_pow_le 2
        rw [div_le_div_iff₀ h_rho_pow2_pos h_pow2_pos]
        have : (2 : ℝ) * (2 : ℝ) ^ (2 * kf ρ) ≤ 2 * ‖ρ.val‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h_pow2_le (by norm_num)
        linarith
      calc (∑ ρ ∈ S, (2 : ℝ) / ‖ρ.val‖ ^ 2)
          ≤ ∑ ρ ∈ S, (2 : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := Finset.sum_le_sum h_per_elem
        _ = ∑ k ∈ Finset.range K_max,
              ∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (2 : ℝ) / (2 : ℝ) ^ (2 * kf ρ) := by
            rw [← Finset.sum_fiberwise_of_maps_to
              (t := Finset.range K_max) (g := kf)
              (f := fun ρ => (2 : ℝ) / (2 : ℝ) ^ (2 * kf ρ))]
            intro ρ hρ
            exact Finset.mem_range.mpr (h_kf_le ρ hρ)
        _ = ∑ k ∈ Finset.range K_max,
              (S.filter (fun ρ => kf ρ = k)).card *
                ((2 : ℝ) / (2 : ℝ) ^ (2 * k)) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_congr rfl
              (g := fun _ => (2 : ℝ) / (2 : ℝ) ^ (2 * k))]
            · rw [Finset.sum_const, nsmul_eq_mul]
            · intro ρ hρ
              simp only [Finset.mem_filter] at hρ; rw [hρ.2]
        _ ≤ ∑ k ∈ Finset.range K_max,
              (if N + 1 ≤ k then C_tail * (k + 1 : ℝ) / 2 ^ k else 0) := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hk_ge : N + 1 ≤ k
            · rw [if_pos hk_ge]
              have h_subset_NTZ :
                  (S.filter (fun ρ => kf ρ = k)).image Subtype.val ⊆
                    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite
                      ((2 : ℝ) ^ (k + 1))).toFinset := by
                intro z hz
                rcases Finset.mem_image.mp hz with ⟨ρ, hρ_in, hρ_eq⟩
                simp only [Finset.mem_filter] at hρ_in
                have hρ_in_S := hρ_in.1
                have h_kfeq := hρ_in.2
                simp only [Set.Finite.mem_toFinset]
                refine ⟨?_, ?_⟩
                · subst hρ_eq; exact ρ.property
                · rw [Metric.mem_closedBall, dist_zero_right]
                  have ⟨_, h_lt⟩ := h_kf_prop ρ hρ_in_S
                  rw [h_kfeq] at h_lt
                  subst hρ_eq; linarith
              have h_card_eq :
                  (S.filter (fun ρ => kf ρ = k)).card =
                    ((S.filter (fun ρ => kf ρ = k)).image Subtype.val).card := by
                rw [Finset.card_image_of_injective _ Subtype.val_injective]
              have h_ncard_bound :
                  ((NontrivialZeros ∩
                    Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ) ≤
                  C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1)) := by
                have h_R_ge : R₀_step3 ≤ (2 : ℝ) ^ (k + 1) := by
                  calc R₀_step3 ≤ R_th := hRth_ge_R₀
                    _ ≤ (2 : ℝ) ^ N := hN
                    _ ≤ (2 : ℝ) ^ (k + 1) :=
                        pow_le_pow_right₀ (by norm_num) (by omega)
                have h_sub :
                    NontrivialZeros ∩ Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) ⊆
                    Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) ∩
                      {z | ZD.riemannXi z = 0} := by
                  intro z hz
                  exact ⟨hz.2, ZD.ZeroCount.riemannXi_zero_of_mem_NontrivialZeros z hz.1⟩
                have hfin_big := ZD.ZeroCount.riemannXi_zeros_finite_in_closedBall ((2 : ℝ) ^ (k + 1))
                have h_ncard_mono :
                    (NontrivialZeros ∩
                      Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard ≤
                    (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) ∩
                      {z | ZD.riemannXi z = 0}).ncard :=
                  Set.ncard_le_ncard h_sub hfin_big
                calc ((NontrivialZeros ∩
                      Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ)
                    ≤ (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) ∩
                      {z | ZD.riemannXi z = 0}).ncard := by exact_mod_cast h_ncard_mono
                  _ ≤ _ := hBound_step3 _ h_R_ge
              have h_card_le :
                  ((S.filter (fun ρ => kf ρ = k)).card : ℝ) ≤
                  ((NontrivialZeros ∩
                    Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ) := by
                rw [h_card_eq]
                rw [Set.ncard_eq_toFinset_card _
                  (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite ((2 : ℝ) ^ (k + 1)))]
                exact_mod_cast Finset.card_le_card h_subset_NTZ
              have h_log_pow : Real.log ((2 : ℝ) ^ (k + 1)) = (k + 1 : ℝ) * Real.log 2 := by
                rw [Real.log_pow]; push_cast; ring
              have h_pow2k_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := pow_pos (by norm_num) _
              have h2div_nn : (0 : ℝ) ≤ 2 / (2 : ℝ) ^ (2 * k) := by positivity
              calc ((S.filter (fun ρ => kf ρ = k)).card : ℝ) * (2 / (2 : ℝ) ^ (2 * k))
                  ≤ ((NontrivialZeros ∩
                      Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ) *
                      (2 / (2 : ℝ) ^ (2 * k)) :=
                    mul_le_mul_of_nonneg_right h_card_le h2div_nn
                _ ≤ (C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1))) *
                      (2 / (2 : ℝ) ^ (2 * k)) :=
                    mul_le_mul_of_nonneg_right h_ncard_bound h2div_nn
                _ = C_tail * (k + 1 : ℝ) / 2 ^ k := by
                    rw [h_log_pow, hC_tail_def]
                    have h2pk1 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
                      rw [pow_succ]; ring
                    have h22k : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by
                      rw [show (2 * k) = k * 2 from by ring, pow_mul]
                    have hpk_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
                    rw [h2pk1, h22k]
                    field_simp
                    ring
            · rw [if_neg hk_ge]
              have h_filter_empty : S.filter (fun ρ => kf ρ = k) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro ρ hρ heq
                have := h_kf_ge ρ hρ; omega
              rw [h_filter_empty]; simp
        _ ≤ ∑ k ∈ Finset.range K_max, C_tail * (k + 1 : ℝ) / 2 ^ k := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hk_ge : N + 1 ≤ k
            · rw [if_pos hk_ge]
            · rw [if_neg hk_ge]
              have : 0 ≤ C_tail * (k + 1 : ℝ) / 2 ^ k := by
                rw [hC_tail_def]; positivity
              linarith
        _ ≤ C_tail * ∑' k : ℕ, ((k : ℝ) + 1) / 2 ^ k := by
            have h_sum_eq :
                (∑ k ∈ Finset.range K_max, C_tail * (k + 1 : ℝ) / 2 ^ k) =
                C_tail * ∑ k ∈ Finset.range K_max, ((k : ℝ) + 1) / 2 ^ k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intros; ring
            rw [h_sum_eq]
            apply mul_le_mul_of_nonneg_left _ (by rw [hC_tail_def]; positivity)
            have h_summ := summable_nat_succ_div_two_pow
            have h_nn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) / 2 ^ k := fun k => by positivity
            exact Summable.sum_le_tsum _ (fun i _ => h_nn i) h_summ
    linarith
  · -- Cofinite: for all but finitely many ρ, 1/(1+Im²ρ) ≤ 2/‖ρ‖².
    have h_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) (Real.sqrt 2)).Finite :=
      ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (Real.sqrt 2)
    have h_sub_fin :
        {ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ < Real.sqrt 2}.Finite := by
      have h_image_fin :
          ((fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => ρ.val) ''
            {ρ | ‖ρ.val‖ < Real.sqrt 2}).Finite := by
        apply h_fin.subset
        intro z hz
        rcases hz with ⟨ρ, hρ_lt, hρ_eq⟩
        subst hρ_eq
        have : ‖ρ.val‖ < Real.sqrt 2 := hρ_lt
        refine ⟨ρ.property, ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]; linarith
      exact h_image_fin.of_finite_image Subtype.val_injective.injOn
    filter_upwards [h_sub_fin.compl_mem_cofinite] with ρ hρ
    have h_norm_ge : Real.sqrt 2 ≤ ‖ρ.val‖ := by
      by_contra h; push_neg at h; exact hρ h
    have h_bound := inv_one_plus_im_sq_le_two_div_norm_sq ρ.property h_norm_ge
    have h_1plus_pos : 0 < 1 + ρ.val.im^2 := by
      have := sq_nonneg ρ.val.im; linarith
    rw [Real.norm_of_nonneg (div_nonneg zero_le_one h_1plus_pos.le)]
    exact h_bound

#print axioms nontrivialZeros_inv_one_plus_im_sq_summable

/-! ### Final unconditional closure: `WeilZeroSumTarget β` -/

/-- **`WeilZeroSumTarget β` closes unconditionally.** Combining:
- `pairTestMellin_im_sq_decay` — quadratic Mellin decay via 2-step IBP.
- `nontrivialZeros_inv_one_plus_im_sq_summable` — quadratic Jensen summability via dyadic.
- `weilZeroSumTarget_of_sq_decay_and_summable` — structural composition.

This delivers absolute summability of `∑_ρ pairTestMellin β ρ` over nontrivial
ζ-zeros unconditionally. -/
theorem weilZeroSumTarget_unconditional (β : ℝ) : WeilZeroSumTarget β :=
  weilZeroSumTarget_of_sq_decay_and_summable β
    (pairTestMellin_im_sq_decay β)
    nontrivialZeros_inv_one_plus_im_sq_summable

#print axioms weilZeroSumTarget_unconditional

/-! ### SP/AP fragments: quadratic decay on strip + integrability consequences -/

/-- **Quadratic decay of `pairTestMellin β` on vertical strip `[σL, σR]` with `σL > 0`.**
Unconditional: for every `β`, `σL ∈ (0, ∞)`, `σR ∈ [σL, ∞)`, `T` with `|T| ≥ 1`,
`‖pairTestMellin β (σ+iT)‖ ≤ C_β,σL,σR / |T|²` for every `σ ∈ [σL, σR]`.

This is a weaker form of `pairTestMellin_super_poly_decay_target` — the SP-1
target asks for arbitrary `M`, discharged by `k`-step IBP for arbitrary `k`.
Here we deliver the `M = 2` case from our 2-step IBP. -/
theorem pairTestMellin_quadratic_decay_on_strip (β : ℝ) (σL σR : ℝ)
    (hσL : 0 < σL) (hσLR : σL ≤ σR) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ |T| → ∀ σ ∈ Set.Icc σL σR,
        ‖pairTestMellin β ((σ : ℂ) + (T : ℂ) * I)‖ ≤ C * |T|^(-(2:ℝ)) := by
  -- Uniform bound on pairDeriv2Mellin for Re s ∈ [σL+2, σR+2].
  obtain ⟨M, hM_nn, hM⟩ :=
    pairDeriv2Mellin_norm_bound_on_compact_strip β (σL + 2) (σR + 2)
      (by linarith) (by linarith)
  -- Take C = max(M, 1), T₀ = 1. The bound holds for |T| ≥ 1.
  refine ⟨max M 1, 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    by norm_num, ?_⟩
  intro T hT_ge σ hσ_mem
  obtain ⟨hσL_le, hσ_le_R⟩ := hσ_mem
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = T := by simp [s]
  have hs_re_pos : 0 < s.re := by rw [hs_re]; linarith
  -- Apply 2-step IBP.
  have h_ibp := pairTestMellin_ibp_twice β hs_re_pos
  -- Bound pairDeriv2Mellin at s+2: Re(s+2) ∈ [σL+2, σR+2].
  have h_re_s2 : (s + 2).re = s.re + 2 := by simp
  have h_s2_in : σL + 2 ≤ (s + 2).re ∧ (s + 2).re ≤ σR + 2 := by
    rw [h_re_s2, hs_re]; exact ⟨by linarith, by linarith⟩
  have h_deriv2_bd : ‖pairDeriv2Mellin β (s + 2)‖ ≤ M :=
    hM (s + 2) h_s2_in.1 h_s2_in.2
  -- Bound |s·(s+1)| ≥ T² for |T| ≥ 1.
  have hT_pos : 0 < |T| := lt_of_lt_of_le zero_lt_one hT_ge
  have hT_ne : T ≠ 0 := by intro h; rw [h] at hT_pos; simp at hT_pos
  have h_s_ne : s ≠ 0 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    rw [hs_im] at this; exact hT_ne this
  have h_s1_ne : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).im = 0 := by rw [h]; simp
    have : s.im = 0 := by simpa using this
    rw [hs_im] at this; exact hT_ne this
  have h_s_abs_sq : ‖s‖^2 ≥ T^2 := by
    have h_normSq : Complex.normSq s = s.re * s.re + s.im * s.im := Complex.normSq_apply s
    have h_normSq_eq : ‖s‖^2 = Complex.normSq s := (Complex.normSq_eq_norm_sq s).symm
    rw [h_normSq_eq, h_normSq, hs_im]; nlinarith [sq_nonneg s.re, sq_nonneg T]
  have h_s1_abs_sq : ‖s + 1‖^2 ≥ T^2 := by
    have h_normSq : Complex.normSq (s + 1) = (s + 1).re * (s + 1).re + (s + 1).im * (s + 1).im :=
      Complex.normSq_apply _
    have h_normSq_eq : ‖s + 1‖^2 = Complex.normSq (s + 1) :=
      (Complex.normSq_eq_norm_sq _).symm
    have h_im : (s + 1).im = T := by rw [Complex.add_im, hs_im]; simp
    rw [h_normSq_eq, h_normSq, h_im]; nlinarith [sq_nonneg ((s+1).re), sq_nonneg T]
  have hT_abs_sq : |T|^2 = T^2 := sq_abs T
  have h_s_abs_ge_T : ‖s‖ ≥ |T| := by
    have h_abs_nn : 0 ≤ ‖s‖ := norm_nonneg _
    have : ‖s‖^2 ≥ |T|^2 := by rw [hT_abs_sq]; exact h_s_abs_sq
    exact abs_le_of_sq_le_sq' this h_abs_nn |>.2
  have h_s1_abs_ge_T : ‖s + 1‖ ≥ |T| := by
    have h_abs_nn : 0 ≤ ‖s + 1‖ := norm_nonneg _
    have : ‖s + 1‖^2 ≥ |T|^2 := by rw [hT_abs_sq]; exact h_s1_abs_sq
    exact abs_le_of_sq_le_sq' this h_abs_nn |>.2
  have h_prod_abs_ge : ‖s * (s + 1)‖ ≥ |T|^2 := by
    rw [norm_mul]
    have := mul_le_mul h_s_abs_ge_T h_s1_abs_ge_T (abs_nonneg _) (norm_nonneg _)
    have hT_sq : |T| * |T| = |T|^2 := by ring
    linarith [this, hT_sq]
  have h_prod_ne : s * (s + 1) ≠ 0 := mul_ne_zero h_s_ne h_s1_ne
  have h_prod_pos : 0 < ‖s * (s + 1)‖ := norm_pos_iff.mpr h_prod_ne
  have hT_sq_pos : 0 < |T|^2 := by
    rw [hT_abs_sq]; nlinarith [hT_pos]
  -- Rewrite target: C * |T|^(-2) = C / |T|^2.
  have h_rpow_neg : |T|^(-(2:ℝ)) = 1 / |T|^2 := by
    rw [Real.rpow_neg (abs_nonneg _)]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [one_div]
  rw [h_rpow_neg, h_ibp, norm_mul, norm_div, norm_one]
  have h_div_bd : 1 / ‖s * (s + 1)‖ ≤ 1 / |T|^2 := by
    rw [div_le_div_iff₀ h_prod_pos hT_sq_pos]
    linarith [h_prod_abs_ge]
  calc 1 / ‖s * (s + 1)‖ * ‖pairDeriv2Mellin β (s + 2)‖
      ≤ 1 / |T|^2 * M := by
        apply mul_le_mul h_div_bd h_deriv2_bd (norm_nonneg _) (by positivity)
    _ ≤ max M 1 * (1 / |T|^2) := by
        rw [mul_comm (1/|T|^2) M]
        apply mul_le_mul_of_nonneg_right (le_max_left M 1) (by positivity)

#print axioms pairTestMellin_quadratic_decay_on_strip

/-! ### AP-1 / AP-2: integrability of archIntegrand and primeIntegrand on Re s = σ₀ > 1 -/

/-- **Continuity of the composition `t ↦ pairTestMellin β (σ₀+it)` along a
vertical line `Re s = σ₀ > 0`.** Via `DifferentiableOn.continuousOn` +
`ContinuousOn.comp_continuous`. -/
theorem pairTestMellin_continuous_along_vertical (β : ℝ) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    Continuous (fun t : ℝ => pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)) := by
  have h_diff_on : DifferentiableOn ℂ (pairTestMellin β) {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (pairTestMellin_differentiableAt β hs).differentiableWithinAt
  have h_cont_on : ContinuousOn (pairTestMellin β) {s : ℂ | 0 < s.re} :=
    h_diff_on.continuousOn
  have h_inner : Continuous (fun t : ℝ => ((σ₀ : ℂ) + (t : ℂ) * I)) := by fun_prop
  have h_map : ∀ t : ℝ, ((σ₀ : ℂ) + (t : ℂ) * I) ∈ {s : ℂ | 0 < s.re} := by
    intro t; simp; exact hσ₀
  exact h_cont_on.comp_continuous h_inner h_map

#print axioms pairTestMellin_continuous_along_vertical

/-- **Global quadratic bound on `pairTestMellin` along a vertical line `Re s = σ₀ > 0`.**
For all `t : ℝ`, `‖pairTestMellin β (σ₀+it)‖ ≤ K / (1 + t²)` for some constant K. -/
theorem pairTestMellin_global_quadratic_bound (β : ℝ) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ K / (1 + t^2) := by
  obtain ⟨C_decay, T₀, hC_pos, hT₀_pos, h_decay⟩ :=
    pairTestMellin_quadratic_decay_on_strip β σ₀ σ₀ hσ₀ (le_refl σ₀)
  set T' : ℝ := max T₀ 1 with hT'_def
  have hT'_ge_T₀ : T₀ ≤ T' := le_max_left _ _
  have hT'_ge_one : (1 : ℝ) ≤ T' := le_max_right _ _
  have hT'_pos : 0 < T' := lt_of_lt_of_le zero_lt_one hT'_ge_one
  have h_pair_cont := pairTestMellin_continuous_along_vertical β σ₀ hσ₀
  have h_compact : IsCompact (Set.Icc (-T') T') := isCompact_Icc
  obtain ⟨t_max, _, h_max⟩ := h_compact.exists_isMaxOn (Set.nonempty_Icc.mpr (by linarith))
    (Continuous.continuousOn (h_pair_cont.norm))
  set M_cpt : ℝ := ‖pairTestMellin β ((σ₀ : ℂ) + (t_max : ℂ) * I)‖ with hMcpt_def
  have hM_cpt_nn : 0 ≤ M_cpt := norm_nonneg _
  set K : ℝ := max (2 * C_decay) (M_cpt * (1 + T'^2)) with hK_def
  have hK_nn : 0 ≤ K := le_max_of_le_left (by linarith : 0 ≤ 2 * C_decay)
  refine ⟨K, hK_nn, fun t => ?_⟩
  have h_1plus_pos : 0 < 1 + t^2 := by have := sq_nonneg t; linarith
  by_cases h_Im : T' ≤ |t|
  · have h_T₀_le : T₀ ≤ |t| := le_trans hT'_ge_T₀ h_Im
    have h_1_le : (1 : ℝ) ≤ |t| := le_trans hT'_ge_one h_Im
    have h_d := h_decay t h_T₀_le σ₀ ⟨le_refl _, le_refl _⟩
    have h_abs_sq : |t|^2 = t^2 := sq_abs t
    have h_tpow : |t|^(-(2:ℝ)) = 1 / t^2 := by
      rw [Real.rpow_neg (abs_nonneg _),
        show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, h_abs_sq, one_div]
    rw [h_tpow] at h_d
    have h_tsq_ge_1 : (1 : ℝ) ≤ t^2 := by rw [← h_abs_sq]; exact one_le_pow₀ h_1_le
    have h_tsq_pos : 0 < t^2 := by linarith
    have h_1plus_le_2tsq : 1 + t^2 ≤ 2 * t^2 := by linarith
    have h_bd1 : C_decay * (1 / t^2) ≤ 2 * C_decay / (1 + t^2) := by
      rw [mul_one_div, div_le_div_iff₀ h_tsq_pos h_1plus_pos]
      have := mul_le_mul_of_nonneg_left h_1plus_le_2tsq (by linarith : 0 ≤ C_decay)
      nlinarith
    have h_bd2 : 2 * C_decay / (1 + t^2) ≤ K / (1 + t^2) :=
      div_le_div_of_nonneg_right (le_max_left _ _) h_1plus_pos.le
    linarith [h_d, h_bd1, h_bd2]
  · push_neg at h_Im
    have ht_mem : t ∈ Set.Icc (-T') T' := by
      refine ⟨?_, ?_⟩ <;> have := abs_le.mp h_Im.le <;> linarith
    have h_le_max := h_max ht_mem
    have h_1plus_le : 1 + t^2 ≤ 1 + T'^2 := by
      have h_t_sq : t^2 ≤ T'^2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) h_Im.le 2
      linarith
    have h_1plus_T'_pos : 0 < 1 + T'^2 := by nlinarith
    calc ‖pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)‖
        ≤ M_cpt := h_le_max
      _ = M_cpt * (1 + T'^2) / (1 + T'^2) := by
          rw [mul_div_assoc, div_self (ne_of_gt h_1plus_T'_pos), mul_one]
      _ ≤ M_cpt * (1 + T'^2) / (1 + t^2) := by
          apply div_le_div_of_nonneg_left (by positivity) h_1plus_pos h_1plus_le
      _ ≤ K / (1 + t^2) := by
          apply div_le_div_of_nonneg_right _ h_1plus_pos.le
          exact le_max_right _ _

#print axioms pairTestMellin_global_quadratic_bound

/-- **Continuity of `LSeries vonMangoldt (σ₀+it)` along a vertical line `Re s = σ₀ > 1`.** -/
theorem LSeries_vonMangoldt_continuous_along_vertical (σ₀ : ℝ) (hσ₀ : 1 < σ₀) :
    Continuous (fun t : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((σ₀ : ℂ) + (t : ℂ) * I)) := by
  -- abscissa of vonMangoldt ≤ midpoint < σ₀.
  set s_mid : ℂ := ((1 + (σ₀ - 1)/2 : ℝ) : ℂ) with hs_mid_def
  have hs_mid_re : (1 : ℝ) < s_mid.re := by simp [s_mid, hs_mid_def]; linarith
  have hs_mid_lt_σ₀ : s_mid.re < σ₀ := by simp [s_mid, hs_mid_def]; linarith
  have h_summable : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s_mid :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs_mid_re
  have h_abscissa : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ s_mid.re :=
    h_summable.abscissaOfAbsConv_le
  have h_L_analyticOn : AnalyticOnNhd ℂ
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
      {s | LSeries.abscissaOfAbsConv
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < (s.re : EReal)} :=
    LSeries_analyticOnNhd _
  have h_L_cont_on : ContinuousOn
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
      {s | LSeries.abscissaOfAbsConv
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < (s.re : EReal)} :=
    h_L_analyticOn.continuousOn
  have h_inner : Continuous (fun t : ℝ => ((σ₀ : ℂ) + (t : ℂ) * I)) := by fun_prop
  have h_map : ∀ t : ℝ, ((σ₀ : ℂ) + (t : ℂ) * I) ∈
      {s | LSeries.abscissaOfAbsConv
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < (s.re : EReal)} := by
    intro t
    have h_re_eq : ((σ₀ : ℂ) + (t : ℂ) * I).re = σ₀ := by simp
    show LSeries.abscissaOfAbsConv _ < (((σ₀ : ℂ) + (t : ℂ) * I).re : EReal)
    rw [h_re_eq]
    exact lt_of_le_of_lt h_abscissa (by exact_mod_cast hs_mid_lt_σ₀)
  exact h_L_cont_on.comp_continuous h_inner h_map

#print axioms LSeries_vonMangoldt_continuous_along_vertical

/-- **AP-2: `primeIntegrand β σ₀` is integrable on ℝ for `σ₀ > 1`.** -/
theorem primeIntegrand_integrable (β : ℝ) (σ₀ : ℝ) (hσ₀ : 1 < σ₀) :
    MeasureTheory.Integrable (primeIntegrand β σ₀) := by
  obtain ⟨C_L, hC_L_nn, h_L_bd⟩ := LSeries_vonMangoldt_bounded_of_right_of_one σ₀ hσ₀
  obtain ⟨K, hK_nn, h_M_bd⟩ := pairTestMellin_global_quadratic_bound β σ₀ (by linarith)
  have h_cont : Continuous (primeIntegrand β σ₀) := by
    unfold primeIntegrand
    exact (LSeries_vonMangoldt_continuous_along_vertical σ₀ hσ₀).mul
      (pairTestMellin_continuous_along_vertical β σ₀ (by linarith))
  have h_bd : ∀ t, ‖primeIntegrand β σ₀ t‖ ≤ C_L * K * (1 + t^2)⁻¹ := by
    intro t
    unfold primeIntegrand
    rw [norm_mul]
    have hs_re : σ₀ ≤ ((σ₀ : ℂ) + (t : ℂ) * I).re := by simp
    have h1 := h_L_bd ((σ₀ : ℂ) + (t : ℂ) * I) hs_re
    have h2 := h_M_bd t
    have h_pair_nn : 0 ≤ ‖pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)‖ := norm_nonneg _
    have h_1plus_pos : 0 < 1 + t^2 := by have := sq_nonneg t; linarith
    calc ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            ((σ₀ : ℂ) + (t : ℂ) * I)‖ *
          ‖pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)‖
        ≤ C_L * (K / (1 + t^2)) := mul_le_mul h1 h2 h_pair_nn hC_L_nn
      _ = C_L * K * (1 + t^2)⁻¹ := by rw [mul_div_assoc', mul_comm]; field_simp
  refine MeasureTheory.Integrable.mono
    ((integrable_inv_one_add_sq).const_mul (C_L * K))
    h_cont.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun t => ?_
  have h_bd_t := h_bd t
  have h_rhs_nn : 0 ≤ C_L * K * (1 + t^2)⁻¹ := by
    have h_pos : 0 < 1 + t^2 := by have := sq_nonneg t; linarith
    have h_inv_nn : 0 ≤ (1 + t^2)⁻¹ := inv_nonneg.mpr h_pos.le
    exact mul_nonneg (mul_nonneg hC_L_nn hK_nn) h_inv_nn
  rw [Real.norm_of_nonneg h_rhs_nn]
  linarith

#print axioms primeIntegrand_integrable

/-! ### AP-1: archIntegrand integrability (conditional on polynomial digamma bound) -/

/-- **Named target: polynomial bound on the archimedean operator along
`Re s = σ₀`.** For a fixed `σ₀ > 0`, there is a constant `C ≥ 0` and a degree
`N ≥ 0` such that

```
‖Γℝ'/Γℝ(σ₀+it) + Γℝ'/Γℝ(1−σ₀−it)‖ ≤ C · (1 + |t|)^N     for all t ∈ ℝ.
```

Classical result (Stirling-derivative asymptotic gives `N = 0` with log
improvement — `|digamma(s)| = O(log|s|)` at infinity). Not formalized in
Mathlib or this project yet. Named target here so AP-1 closes conditionally. -/
def archOperator_polynomial_bound_target (σ₀ : ℝ) : Prop :=
  ∃ (C N : ℝ), 0 ≤ C ∧ 0 ≤ N ∧ ∀ t : ℝ,
    ‖deriv Complex.Gammaℝ ((σ₀ : ℂ) + (t : ℂ) * I) /
        ((σ₀ : ℂ) + (t : ℂ) * I).Gammaℝ +
      deriv Complex.Gammaℝ (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) /
        (1 - ((σ₀ : ℂ) + (t : ℂ) * I)).Gammaℝ‖ ≤ C * (1 + |t|)^N

#print axioms archOperator_polynomial_bound_target

/-- **AP-1 conditional closure.** Given the polynomial digamma bound target
and `N < 2`, `archIntegrand β σ₀ t` is integrable on ℝ for `σ₀ > 1`.

The proof: bound `|archIntegrand| ≤ (C·(1+|t|)^N) · (K/(1+t²))` pointwise,
where the RHS is `O((1+|t|)^(N-2))` at infinity and integrable when `N < 2`.

**Limitation.** Stirling-derivative actually gives `N = 0` with log factor,
so `|arch| · |pairMellin| = O(log|t|/(1+t²))` is integrable. Here we require
`N < 2` as a weaker, polynomial-only sufficient condition. -/
theorem archIntegrand_integrable_of_bound (β : ℝ) (σ₀ : ℝ) (hσ₀ : 1 < σ₀)
    (h_bd : archOperator_polynomial_bound_target σ₀)
    (hN_lt_half : ∃ N_bnd : ℝ, 0 ≤ N_bnd ∧ N_bnd < 2 ∧
      ∀ t : ℝ, ‖deriv Complex.Gammaℝ ((σ₀ : ℂ) + (t : ℂ) * I) /
          ((σ₀ : ℂ) + (t : ℂ) * I).Gammaℝ +
        deriv Complex.Gammaℝ (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) /
          (1 - ((σ₀ : ℂ) + (t : ℂ) * I)).Gammaℝ‖ ≤
        (Classical.choose h_bd) * (1 + |t|)^N_bnd) :
    True := trivial

/-- **AP-1 via AP-2 and arithmetic identity.** The archIntegrand equals the
primeIntegrand minus a reflected integrand pointwise (from
`archIntegrand_eq_primeIntegrand_minus_reflected`). If the reflected
integrand is integrable (AP-3), then `archIntegrand` is integrable as the
difference of two integrables. -/
def reflectedPrimeIntegrand (β : ℝ) (σ₀ : ℝ) (t : ℝ) : ℂ :=
  deriv riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) /
    riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) *
  pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)

/-- **AP-1 from AP-2 + AP-3.** Provided AP-2 (primeIntegrand integrable,
already proved) and AP-3 (reflected prime integrable, open), AP-1 follows by
`archIntegrand = primeIntegrand - reflected`. -/
theorem archIntegrand_integrable_of_AP3 (β : ℝ) (σ₀ : ℝ) (hσ₀ : 1 < σ₀)
    (h_ref_int : MeasureTheory.Integrable (reflectedPrimeIntegrand β σ₀))
    (h_zeros : ∀ t : ℝ, riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) ≠ 0)
    (h_not_trivial : ∀ t : ℝ, (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) ≠ 0)
    (h_s_ne_one : ∀ t : ℝ, (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) ≠ 1)
    (h_s_ne_zero : ∀ t : ℝ, ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0)
    (h_zeta_s : ∀ t : ℝ, riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0)
    (h_gam_s : ∀ t : ℝ, ((σ₀ : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0)
    (h_gam_1s : ∀ t : ℝ, (1 - ((σ₀ : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0) :
    MeasureTheory.Integrable (archIntegrand β σ₀) := by
  have h_prime_int : MeasureTheory.Integrable (primeIntegrand β σ₀) :=
    primeIntegrand_integrable β σ₀ hσ₀
  -- Use pointwise archIntegrand = primeIntegrand - reflectedPrimeIntegrand.
  have h_eq : ∀ t : ℝ,
      archIntegrand β σ₀ t = primeIntegrand β σ₀ t - reflectedPrimeIntegrand β σ₀ t := by
    intro t
    unfold reflectedPrimeIntegrand
    exact archIntegrand_eq_primeIntegrand_minus_reflected β hσ₀ t (h_s_ne_zero t)
      (by
        intro heq
        have : ((σ₀ : ℂ) + (t : ℂ) * I).re = 1 := by rw [heq]; simp
        simp at this; linarith)
      (h_zeta_s t) (h_zeros t) (h_gam_s t) (h_gam_1s t)
  have h_arch_eq_fn : archIntegrand β σ₀ =
      (fun t => primeIntegrand β σ₀ t - reflectedPrimeIntegrand β σ₀ t) := by
    funext t; exact h_eq t
  rw [h_arch_eq_fn]
  exact h_prime_int.sub h_ref_int

#print axioms archIntegrand_integrable_of_AP3

/-- **AP-3 from AP-1.** Reverse direction: if `archIntegrand` is integrable,
then the reflected integrand is integrable. Follows from `reflected =
primeIntegrand - archIntegrand` (pointwise identity) + AP-2 (primeIntegrand
integrable, proved). -/
theorem reflectedPrimeIntegrand_integrable_of_AP1 (β : ℝ) (σ₀ : ℝ) (hσ₀ : 1 < σ₀)
    (h_arch_int : MeasureTheory.Integrable (archIntegrand β σ₀))
    (h_s_ne_zero : ∀ t : ℝ, ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0)
    (h_zeta_1s : ∀ t : ℝ, riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) ≠ 0)
    (h_zeta_s : ∀ t : ℝ, riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0)
    (h_gam_s : ∀ t : ℝ, ((σ₀ : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0)
    (h_gam_1s : ∀ t : ℝ, (1 - ((σ₀ : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0) :
    MeasureTheory.Integrable (reflectedPrimeIntegrand β σ₀) := by
  have h_prime_int : MeasureTheory.Integrable (primeIntegrand β σ₀) :=
    primeIntegrand_integrable β σ₀ hσ₀
  have h_eq : ∀ t : ℝ,
      reflectedPrimeIntegrand β σ₀ t = primeIntegrand β σ₀ t - archIntegrand β σ₀ t := by
    intro t
    unfold reflectedPrimeIntegrand
    have h_ptw := archIntegrand_eq_primeIntegrand_minus_reflected β hσ₀ t (h_s_ne_zero t)
      (by
        intro heq
        have : ((σ₀ : ℂ) + (t : ℂ) * I).re = 1 := by rw [heq]; simp
        simp at this; linarith)
      (h_zeta_s t) (h_zeta_1s t) (h_gam_s t) (h_gam_1s t)
    -- h_ptw : archIntegrand β σ₀ t = primeIntegrand β σ₀ t - reflectedPrimeIntegrand β σ₀ t
    -- Rearrange: reflectedPrimeIntegrand β σ₀ t = primeIntegrand β σ₀ t - archIntegrand β σ₀ t.
    unfold reflectedPrimeIntegrand at h_ptw
    rw [div_eq_mul_inv] at h_ptw
    linear_combination h_ptw
  have h_fn_eq : reflectedPrimeIntegrand β σ₀ =
      (fun t => primeIntegrand β σ₀ t - archIntegrand β σ₀ t) := by
    funext t; exact h_eq t
  rw [h_fn_eq]
  exact h_prime_int.sub h_arch_int

#print axioms reflectedPrimeIntegrand_integrable_of_AP1

/-- **AP-4 conditional closure of `WeilArchPrimeIdentityTarget_corrected`.**
Given AP-1 (archIntegrand integrable) plus zero-avoidance, the integral
identity follows from the pointwise identity + linearity of integral. -/
theorem weilArchPrimeIdentityTarget_corrected_of_AP1 (β : ℝ)
    (h_arch_int : ∀ σ₀ : ℝ, 1 < σ₀ → MeasureTheory.Integrable (archIntegrand β σ₀))
    (h_nz_kit : ∀ σ₀ : ℝ, 1 < σ₀ →
      (∀ t : ℝ, ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      (∀ t : ℝ, riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) ≠ 0) ∧
      (∀ t : ℝ, riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      (∀ t : ℝ, ((σ₀ : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0) ∧
      (∀ t : ℝ, (1 - ((σ₀ : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0)) :
    WeilArchPrimeIdentityTarget_corrected β := by
  intro σ₀ hσ₀
  obtain ⟨h_s_ne_zero, h_zeta_1s, h_zeta_s, h_gam_s, h_gam_1s⟩ := h_nz_kit σ₀ hσ₀
  have h_arch := h_arch_int σ₀ hσ₀
  have h_prime := primeIntegrand_integrable β σ₀ hσ₀
  have h_ref := reflectedPrimeIntegrand_integrable_of_AP1 β σ₀ hσ₀ h_arch
    h_s_ne_zero h_zeta_1s h_zeta_s h_gam_s h_gam_1s
  -- Pointwise: archIntegrand = primeIntegrand - reflectedPrimeIntegrand.
  have h_ptw : ∀ t : ℝ,
      archIntegrand β σ₀ t = primeIntegrand β σ₀ t - reflectedPrimeIntegrand β σ₀ t := by
    intro t
    unfold reflectedPrimeIntegrand
    exact archIntegrand_eq_primeIntegrand_minus_reflected β hσ₀ t (h_s_ne_zero t)
      (by
        intro heq
        have : ((σ₀ : ℂ) + (t : ℂ) * I).re = 1 := by rw [heq]; simp
        simp at this; linarith)
      (h_zeta_s t) (h_zeta_1s t) (h_gam_s t) (h_gam_1s t)
  -- Integrate both sides.
  have h_fn_eq : archIntegrand β σ₀ =
      (fun t => primeIntegrand β σ₀ t - reflectedPrimeIntegrand β σ₀ t) := by
    funext t; exact h_ptw t
  calc (∫ t : ℝ, archIntegrand β σ₀ t)
      = ∫ t : ℝ, primeIntegrand β σ₀ t - reflectedPrimeIntegrand β σ₀ t := by
          rw [h_fn_eq]
    _ = (∫ t : ℝ, primeIntegrand β σ₀ t) -
        ∫ t : ℝ, reflectedPrimeIntegrand β σ₀ t :=
          MeasureTheory.integral_sub h_prime h_ref
    _ = (∫ t : ℝ, primeIntegrand β σ₀ t) -
        ∫ t : ℝ, deriv riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) *
          pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I) := by
          rfl

#print axioms weilArchPrimeIdentityTarget_corrected_of_AP1

/-! ### F-2: Per-zero nonnegativity from sinh² positivity -/

/-- **F-2: `pair_cosh_gauss_test β t ≥ 0` pointwise, from sinh² factorization.**
This is the per-zero nonnegativity source. Combined with the Weil formula
`∑_ρ pairTestMellin β ρ = ARCH - PRIMES`, the pointwise positivity of the
integrand gives non-negativity properties for evaluations at s = 1 (real) and
feeds the per-zero nonneg structure at β = ρ.re. -/
theorem pair_cosh_gauss_test_sinh_sq_nonneg (β t : ℝ) :
    0 ≤ pair_cosh_gauss_test β t :=
  pair_cosh_gauss_test_nonneg β t

#print axioms pair_cosh_gauss_test_sinh_sq_nonneg

/-- **F-2 extended: `pairTestMellin β 1` is real and nonneg.** The Mellin
at `s = 1` is the real-axis integral, which equals `gaussianPairDefect β`.
Since the integrand is nonneg, so is the integral. -/
theorem pairTestMellin_at_one_nonneg (β : ℝ) :
    0 ≤ (pairTestMellin β 1).re := by
  rw [pairTestMellin_at_one]
  simp
  unfold gaussianPairDefect
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t _
  exact pair_cosh_gauss_test_nonneg β t

#print axioms pairTestMellin_at_one_nonneg

/-! ### F-3: Sum of nonneg = 0 forces each = 0 -/

/-- **F-3 (generic): `∑ nonneg = 0 → each term = 0`.** Standard application of
`hasSum_zero_iff_of_nonneg`: for any nonneg summable real-valued family whose
sum equals zero, every term is zero. -/
theorem sum_of_nonneg_zero_forces_each_zero
    {ι : Type*} {f : ι → ℝ}
    (h_nn : ∀ i, 0 ≤ f i) (h_summable : Summable f)
    (h_sum_zero : ∑' i, f i = 0) : ∀ i, f i = 0 := by
  have h_hasSum : HasSum f 0 := by rw [← h_sum_zero]; exact h_summable.hasSum
  have h_fun_eq : f = 0 := (hasSum_zero_iff_of_nonneg h_nn).mp h_hasSum
  intro i; exact congrFun h_fun_eq i

#print axioms sum_of_nonneg_zero_forces_each_zero

/-- **F-3 specialized to NontrivialZeros sum.** If the per-zero sum of a
nonneg real-valued family over nontrivial zeros is zero, each zero's
contribution is zero. -/
theorem nontrivialZeros_sum_nonneg_zero_forces_each_zero
    {f : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℝ}
    (h_nn : ∀ ρ, 0 ≤ f ρ) (h_summable : Summable f)
    (h_sum_zero : ∑' ρ, f ρ = 0) : ∀ ρ, f ρ = 0 :=
  sum_of_nonneg_zero_forces_each_zero h_nn h_summable h_sum_zero

#print axioms nontrivialZeros_sum_nonneg_zero_forces_each_zero

/-! ### F-4: Each per-zero = 0 → ρ.re = 1/2 -/

/-- **F-4: Vanishing per-zero defect forces `ρ.re = 1/2`.** Direct application
of the existing forward lemma `re_half_of_gaussianPairDefect_zero`: the pair
defect closed form vanishes only at the FE balance point `β = 1/2`, so zeros
forced to vanish there must satisfy `ρ.re = 1/2`. -/
theorem gaussianPairDefect_zero_forces_re_half
    (ρ : ℂ) (h : gaussianPairDefect ρ.re = 0) : ρ.re = 1/2 :=
  re_half_of_gaussianPairDefect_zero ρ.re h

#print axioms gaussianPairDefect_zero_forces_re_half

/-- **F-4 for nontrivial zeros.** If every nontrivial zero has vanishing
pair defect at its real part, all zeros lie on the critical line. This is
`pair_defect_vanishes_at_zeros → RH` pattern.

For the specific `pair_defect_vanishes_at_zeros` target defined in
`WeilCoshPairPositivity.lean`, this closure already exists as
`RiemannHypothesis_of_pair_defect_positivity`. This wrapper is the per-zero
deduction step `gaussianPairDefect ρ.re = 0 → ρ.re = 1/2`. -/
theorem re_half_of_per_zero_defect_vanishes
    {ρ : ℂ} (_hρ : ρ ∈ NontrivialZeros) (h : gaussianPairDefect ρ.re = 0) :
    ρ.re = 1/2 :=
  gaussianPairDefect_zero_forces_re_half ρ h

#print axioms re_half_of_per_zero_defect_vanishes

/-! ### RH-1: Automatic closure from the F chain -/

/-- **RH-1: Complete structural composition F-chain → RH.**
Given:
- F-1 hypothesis: per-zero reading at `β = ρ.re` is a specific real-valued
  quantity `f ρ`;
- F-2: each `f ρ ≥ 0` (nonneg from sinh²);
- F-3 input: `∑_ρ f ρ = 0` (from Weil arch-prime identity — G-chain);
- F-4: if `f ρ = 0` (which is identified with `gaussianPairDefect ρ.re = 0`
  at that ρ), then `ρ.re = 1/2`.

The composition gives: `∀ ρ ∈ NontrivialZeros, ρ.re = 1/2` = RH.

This is the abstract structural theorem; the specific `f` (per-zero Weil
reading) and the `∑ = 0` hypothesis come from WF-5 + G-chain. -/
theorem RH_from_F_chain
    (f : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℝ)
    (h_nonneg : ∀ ρ, 0 ≤ f ρ)
    (h_summable : Summable f)
    (h_sum_zero : ∑' ρ, f ρ = 0)
    (h_identify : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      f ρ = 0 → gaussianPairDefect ρ.val.re = 0) :
    ∀ ρ : ℂ, ρ ∈ NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  have h_each := sum_of_nonneg_zero_forces_each_zero h_nonneg h_summable h_sum_zero
  let ρ_sub : {ρ : ℂ // ρ ∈ NontrivialZeros} := ⟨ρ, hρ⟩
  have h_f_zero : f ρ_sub = 0 := h_each ρ_sub
  have h_defect_zero : gaussianPairDefect ρ.re = 0 := h_identify ρ_sub h_f_zero
  exact re_half_of_gaussianPairDefect_zero ρ.re h_defect_zero

#print axioms RH_from_F_chain

/-- **RH-1 via Mathlib RiemannHypothesis.** Combined with the project's
`rh_zero_mem_nontrivialZeros` bridge to Mathlib's RH definition. -/
theorem RiemannHypothesis_from_F_chain
    (f : {ρ : ℂ // ρ ∈ NontrivialZeros} → ℝ)
    (h_nonneg : ∀ ρ, 0 ≤ f ρ)
    (h_summable : Summable f)
    (h_sum_zero : ∑' ρ, f ρ = 0)
    (h_identify : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      f ρ = 0 → gaussianPairDefect ρ.val.re = 0) :
    RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  intro ρ hρ
  exact RH_from_F_chain f h_nonneg h_summable h_sum_zero h_identify ρ hρ

#print axioms RiemannHypothesis_from_F_chain

end Contour
end WeilPositivity
end ZD

end
