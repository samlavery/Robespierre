import Mathlib
import RequestProject.RiemannXiDecay
import RequestProject.ZetaStripBound
import RequestProject.MellinPathToXi

/-!
# Zero-count bound for Riemann ξ via Jensen + Stirling + PL

Replaces the classical Riemann–von Mangoldt zero-count asymptotic
(not in Mathlib) with a Jensen + Stirling + polynomial-strip-bound
derivation that closes `nontrivialZeros_inv_sq_summable_target` from
`RiemannXiDecay.lean` unconditionally, given the direct Euler–Maclaurin
proof of `zetaPolynomialBoundInStrip` (no PL needed in this chain once
that lands unconditionally).

## Chain

1. **ξ order-1 bound** on `‖s‖ ≤ R`: combines `Gammaℝ_vertical_decay`
   (Stirling, landed) + `zetaPolynomialBoundInStrip` (Euler–Maclaurin, gate)
   to give `log ‖ξ(s)‖ ≤ C · R · log R` on large disks.
2. **Jensen's formula** applied to ξ at 0: Mathlib 2025
   `MeromorphicOn.circleAverage_log_norm`. ξ is entire, `ξ(0) = 1/2 ≠ 0`,
   so the formula gives
     `circleAverage (log ‖ξ·‖) 0 R = ∑_{ρ ∈ B_R, ξ(ρ)=0} log(R/‖ρ‖) + log‖ξ(0)‖`.
3. **Zero count in disk**: zeros in the annulus `R/2 ≤ ‖ρ‖ ≤ R` each
   contribute ≥ `log 2` to the sum in (2), so
     `#{zeros : ‖ρ‖ ≤ R} ≤ C · R · log R / log 2 = O(R log R)`.
4. **Summability via dyadic partition**:
   `∑_ρ 1/‖ρ‖² ≤ ∑_{k≥0} #{zeros in [2^k, 2^{k+1}]} / 2^{2k}
               ≤ ∑_k C · 2^{k+1}·(k+1) / 2^{2k}
               = C · ∑_k (k+1) / 2^{k−1} < ∞`.

## Status

Scaffold — each step is a named theorem with a targeted `sorry`
explaining what closes it. Intended as a drop-in replacement for a
Mathlib `N(T)` (which doesn't exist).

The remaining analytic gaps are statements about entire-function growth
and zero density.
-/

open Real Complex MeasureTheory Filter Topology Set
open scoped Real

namespace ZD
namespace ZeroCount

/-- `riemannXi 0 = 1/2` — the constant term in the definition
`ξ(s) = (s(s−1)/2)·completedRiemannZeta₀ s + 1/2`. -/
theorem riemannXi_zero : ZD.riemannXi 0 = 1 / 2 := by
  unfold ZD.riemannXi
  simp

/-- `riemannXi 0 ≠ 0`. -/
theorem riemannXi_zero_ne_zero : ZD.riemannXi 0 ≠ 0 := by
  rw [riemannXi_zero]; norm_num

/-- ξ is `AnalyticOnNhd` on all of ℂ (entire). -/
theorem riemannXi_analyticOnNhd_univ :
    AnalyticOnNhd ℂ ZD.riemannXi Set.univ :=
  ZD.riemannXi_differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-- **Functional equation for ξ**: `ξ(1 - s) = ξ(s)`. Clean because ξ is
defined via `completedRiemannZeta₀` (entire part), which satisfies the
symmetric FE `Λ₀(1-s) = Λ₀(s)`. The polynomial prefactor `(s(s-1)/2)`
is invariant under `s ↦ 1-s` since `(1-s)(-s) = s(s-1)`. -/
theorem riemannXi_one_sub (s : ℂ) :
    ZD.riemannXi (1 - s) = ZD.riemannXi s := by
  unfold ZD.riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- ξ continuous on ℂ. -/
theorem riemannXi_continuous : Continuous ZD.riemannXi :=
  ZD.riemannXi_differentiable.continuous

/-- **Compact bound on ξ** — ξ is bounded on any closed disk. Clean
consequence of continuity on compact. Used to handle the small-`‖s‖`
region in step 1 assembly. -/
theorem riemannXi_bounded_on_closedBall (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ s ∈ Metric.closedBall (0 : ℂ) R, ‖ZD.riemannXi s‖ ≤ M := by
  rcases (isCompact_closedBall (0 : ℂ) R).bddAbove_image
    riemannXi_continuous.norm.continuousOn with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, fun s hs => ?_⟩
  exact le_trans (hM (Set.mem_image_of_mem _ hs)) (le_max_left _ _)

/-- **Every nontrivial zero of ζ is a zero of ξ.** Used for step 4 to
transfer the `ξ`-zero-count bound to `NontrivialZeros`. -/
theorem riemannXi_zero_of_mem_NontrivialZeros
    (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) :
    ZD.riemannXi ρ = 0 :=
  ZD.riemannXi_eq_zero_of_mem_NontrivialZeros ρ hρ

/-- Subset inclusion: `NontrivialZeros ⊆ {z | ξ(z) = 0}`. -/
theorem NontrivialZeros_subset_riemannXi_zeros :
    NontrivialZeros ⊆ {z | ZD.riemannXi z = 0} := by
  intro ρ hρ
  exact riemannXi_zero_of_mem_NontrivialZeros ρ hρ

/-- **ξ is not identically zero on any neighborhood.** Since `ξ(0) = 1/2 ≠ 0`
and ξ is entire on the (preconnected) ℂ, the identity theorem rules out
local vanishing: if ξ were ≡ 0 near any point, the identity theorem would
force ξ ≡ 0 on ℂ, contradicting `ξ(0) ≠ 0`. -/
theorem riemannXi_analyticOrderAt_ne_top (z : ℂ) :
    analyticOrderAt ZD.riemannXi z ≠ ⊤ := by
  intro h_top
  rw [analyticOrderAt_eq_top] at h_top
  -- h_top : ∀ᶠ w in 𝓝 z, ξ w = 0
  have h_fre : ∃ᶠ w in 𝓝[≠] z, ZD.riemannXi w = 0 := by
    have : ∀ᶠ w in 𝓝[≠] z, ZD.riemannXi w = 0 :=
      h_top.filter_mono nhdsWithin_le_nhds
    exact this.frequently
  have hEq := (riemannXi_analyticOnNhd_univ).eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ z) h_fre
  have h0 := hEq (Set.mem_univ 0)
  simp at h0
  exact riemannXi_zero_ne_zero h0

/-- **Finiteness of ξ-zeros on any closed ball.** Uses
`MeromorphicOn.divisor.finiteSupport` on the compact ball + the fact
that ξ is not identically zero (via `riemannXi_analyticOrderAt_ne_top`).

The remaining gap is the WithTop/untop₀ case analysis translating
"divisor support" ↔ "analytic zero set with ξ ≢ 0 near z". Clean Mathlib
API hunting task for next session. -/
theorem riemannXi_zeros_finite_in_closedBall (R : ℝ) :
    (Metric.closedBall (0 : ℂ) R ∩ {z | ZD.riemannXi z = 0}).Finite := by
  have hMero : MeromorphicOn ZD.riemannXi (Metric.closedBall (0 : ℂ) R) :=
    (riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)).meromorphicOn
  have hCpt : IsCompact (Metric.closedBall (0 : ℂ) R) :=
    isCompact_closedBall 0 R
  have hDiv_fin := (MeromorphicOn.divisor ZD.riemannXi
    (Metric.closedBall (0 : ℂ) R)).finiteSupport hCpt
  apply hDiv_fin.subset
  intro z hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := hz.1
  have hz_zero : ZD.riemannXi z = 0 := hz.2
  have hAnal : AnalyticAt ℂ ZD.riemannXi z :=
    riemannXi_analyticOnNhd_univ z (Set.mem_univ _)
  have hAnalOrd_ne_zero : analyticOrderAt ZD.riemannXi z ≠ 0 := by
    rw [analyticOrderAt_ne_zero]
    exact ⟨hAnal, hz_zero⟩
  have hAnalOrd_ne_top := riemannXi_analyticOrderAt_ne_top z
  -- Extract the natural order: analyticOrderAt = ↑n for some n : ℕ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt ZD.riemannXi z :=
    ENat.ne_top_iff_exists.mp hAnalOrd_ne_top
  -- n ≠ 0 (since analyticOrderAt ≠ 0)
  have hn_ne : n ≠ 0 := by
    intro h; apply hAnalOrd_ne_zero; rw [← hn, h]; rfl
  -- Now: divisor ξ U z = (meromorphicOrderAt ξ z).untop₀ = (↑↑n : ℤ∞).untop₀ = n
  simp only [Function.mem_support]
  rw [MeromorphicOn.divisor_apply hMero hz_ball,
      hAnal.meromorphicOrderAt_eq, ← hn]
  -- Goal: ((↑n : ℕ∞).map (↑) : ℤ∞).untop₀ ≠ 0
  simp
  exact hn_ne

/-- `NontrivialZeros ∩ closedBall 0 R` is finite (subset of ξ-zeros). -/
theorem NontrivialZeros_inter_closedBall_finite (R : ℝ) :
    (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) R).Finite := by
  apply Set.Finite.subset (riemannXi_zeros_finite_in_closedBall R)
  intro ρ hρ
  exact ⟨hρ.2, riemannXi_zero_of_mem_NontrivialZeros ρ hρ.1⟩

/-- **Summability of the dyadic series `(k+1)/8^k`.** Used as the
ℕ-indexed majorant in step 4's dyadic proof. -/
theorem summable_nat_succ_div_eight_pow :
    Summable (fun k : ℕ => (k + 1 : ℝ) / 8 ^ k) := by
  have h1 : Summable (fun k : ℕ => (k : ℝ) * (1 / 8 : ℝ) ^ k) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (show ‖(1 / 8 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)
    convert this using 1
    funext k
    simp [pow_one]
  have h2 : Summable (fun k : ℕ => (1 / 8 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h_sum : Summable (fun k : ℕ => (k : ℝ) * (1 / 8) ^ k + (1 / 8 : ℝ) ^ k) :=
    h1.add h2
  convert h_sum using 1
  funext k
  have h8_pow_ne : (8 : ℝ) ^ k ≠ 0 := by positivity
  have h_eq : (1 / 8 : ℝ) ^ k = 1 / 8 ^ k := by
    rw [div_pow, one_pow]
  rw [h_eq]
  field_simp

/-- **Lower bound on `‖ρ(ρ-1)‖² ≥ ‖ρ‖⁴/4` for `‖ρ‖ ≥ 2`.**
Used for step 4: converts `1/normSq(ρ(ρ-1))` summability into
`1/‖ρ‖⁴` summability via a term-by-term bound. -/
theorem normSq_rho_times_rho_sub_one_ge (ρ : ℂ) (h : 2 ≤ ‖ρ‖) :
    ‖ρ‖ ^ 4 / 4 ≤ Complex.normSq (ρ * (ρ - 1)) := by
  have hρ_ge_one : (1 : ℝ) ≤ ‖ρ‖ := le_trans (by norm_num) h
  have hρ_sub_one : ‖ρ‖ / 2 ≤ ‖ρ - 1‖ := by
    have : ‖ρ‖ - 1 ≤ ‖ρ - 1‖ := by
      have := norm_sub_norm_le ρ 1
      simpa using this
    linarith
  have hρ_sub_one_nn : (0 : ℝ) ≤ ‖ρ - 1‖ := norm_nonneg _
  have h_half_nn : (0 : ℝ) ≤ ‖ρ‖ / 2 := by linarith
  have hρ_nn : (0 : ℝ) ≤ ‖ρ‖ := norm_nonneg _
  have h_sq : (‖ρ‖ / 2) ^ 2 ≤ ‖ρ - 1‖ ^ 2 :=
    pow_le_pow_left₀ h_half_nn hρ_sub_one 2
  have h_mul : ‖ρ‖ ^ 2 * (‖ρ‖ / 2) ^ 2 ≤ ‖ρ‖ ^ 2 * ‖ρ - 1‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
  have h_normSq_eq : Complex.normSq (ρ * (ρ - 1)) = ‖ρ * (ρ - 1)‖ ^ 2 :=
    Complex.normSq_eq_norm_sq _
  rw [h_normSq_eq, norm_mul]
  calc ‖ρ‖ ^ 4 / 4
      = ‖ρ‖ ^ 2 * (‖ρ‖ / 2) ^ 2 := by ring
    _ ≤ ‖ρ‖ ^ 2 * ‖ρ - 1‖ ^ 2 := h_mul
    _ = (‖ρ‖ * ‖ρ - 1‖) ^ 2 := by ring

/-! ### Step 1 decomposition: strip / right half / FE

ξ is entire of order ≤ 1 (Hadamard product fact). To prove the uniform
`log ‖ξ(s)‖ ≤ C · R · log R` bound on `‖s‖ ≤ R`, we split by `Re s`:

* `xi_bound_in_strip`: `0 ≤ Re s ≤ 1` — from PL polynomial bound on ζ ×
  Stirling on Γℝ (via `riemannXi_vertical_decay_of_zetaBound`).
* `xi_bound_right_halfplane`: `Re s ≥ 1` — from absolute convergence of
  `ζ(s) = ∑ 1/n^s` on `Re s ≥ 1+ε` (bounded by `ζ(1+ε)`), Stirling on Γℝ.
* `xi_bound_left_halfplane`: `Re s ≤ 0` — from functional equation
  `ξ(s) = ξ(1-s)` (Mathlib: `completedRiemannZeta_one_sub`) + right-half bound.

These three assemble in `xi_order_one_log_bound`.
-/

/-! ### Mellin-route helpers for the strip polynomial bound

The strip polynomial bound on `ξ` is obtained here via the Mellin identity
`I_theta_of ψ_mellin s = completedRiemannZeta₀ s` from `MellinPathToXi.lean`,
rather than via Phragmén–Lindelöf (which would require the missing
order-1 subexponential hypothesis).

* `integrable_cosh_half_abs_ψ_mellin` — integrability of the
  dominator `2·cosh(t/2)·|ψ_mellin(t)|` on `Ioi 0`, obtained by
  specializing the existing `ZD.integrable_I_theta_integrand 1` and
  identifying its norm with the dominator pointwise.
* `complex_cosh_norm_le_cosh_re` — pointwise bound
  `‖Complex.cosh z‖ ≤ Real.cosh (Re z)` by the triangle inequality on `exp`.
* `ptwise_bound_cosh_kernel_strip` — the per-`t` bound
  `‖2·cosh((s−1/2)t)·ψ_mellin t‖ ≤ 2·cosh(t/2)·|ψ_mellin t|`, uniform for
  `s` in the closed strip `[0, 1]` (since `|Re(s − 1/2)| ≤ 1/2`).
* `completedRiemannZeta₀_bounded_on_strip` — `‖Λ₀(s)‖ ≤ M` for `s` in
  the closed strip, via `norm_integral_le_integral_norm` composed with
  `setIntegral_mono_ae` against the dominator.
-/

/-- **Dominator integrability**: `2·cosh(t/2)·|ψ_mellin(t)|` is integrable on `Ioi 0`.
Obtained by specializing `ZD.integrable_I_theta_integrand 1` to `s = 1` and
identifying its norm with the dominator (using `Complex.ofReal_cosh` and
positivity of `Real.cosh`). -/
theorem integrable_cosh_half_abs_ψ_mellin :
    IntegrableOn (fun t : ℝ => 2 * Real.cosh (t/2) * |ZD.ψ_mellin t|) (Set.Ioi 0) := by
  have h := (ZD.integrable_I_theta_integrand 1).norm
  have h_eq :
      (fun t : ℝ => ‖(2 : ℂ) * Complex.cosh ((1 - 1/2) * (t : ℂ)) *
          ((ZD.ψ_mellin t : ℝ) : ℂ)‖) =
      (fun t : ℝ => 2 * Real.cosh (t/2) * |ZD.ψ_mellin t|) := by
    funext t
    rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
    have hstep : (1 - 1/2 : ℂ) * (t : ℂ) = ((t/2 : ℝ) : ℂ) := by push_cast; ring
    rw [hstep, show Complex.cosh ((t/2 : ℝ) : ℂ) = ((Real.cosh (t/2) : ℝ) : ℂ) from
      (Complex.ofReal_cosh (t/2)).symm]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  rw [← h_eq]; exact h

/-- **Pointwise norm bound on Complex.cosh**: `‖cosh z‖ ≤ cosh(Re z)`. Proved
by triangle inequality on `(exp z + exp(-z))/2` combined with
`‖exp z‖ = exp(Re z)`. -/
theorem complex_cosh_norm_le_cosh_re : ∀ z : ℂ, ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  intro z
  rw [Complex.cosh, show (Complex.exp z + Complex.exp (-z)) / 2 =
        (1/2 : ℂ) * (Complex.exp z + Complex.exp (-z)) from by ring]
  rw [norm_mul]
  have hnz : ‖(1/2 : ℂ)‖ = 1/2 := by simp
  rw [hnz]
  have h_add : ‖Complex.exp z + Complex.exp (-z)‖ ≤
      Real.exp z.re + Real.exp (-z.re) := by
    calc ‖Complex.exp z + Complex.exp (-z)‖
        ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_add_le _ _
      _ = Real.exp z.re + Real.exp (-z).re := by rw [Complex.norm_exp, Complex.norm_exp]
      _ = Real.exp z.re + Real.exp (-z.re) := by rw [Complex.neg_re]
  have h_cosh_eq : Real.cosh z.re = (Real.exp z.re + Real.exp (-z.re)) / 2 := Real.cosh_eq _
  linarith [h_add]

/-- **Pointwise dominator bound on the strip**: for any `s` with `0 ≤ Re s ≤ 1`
and any real `t`, `‖2·cosh((s − 1/2)·t)·ψ_mellin(t)‖ ≤ 2·cosh(t/2)·|ψ_mellin t|`.
Uses `complex_cosh_norm_le_cosh_re` + `|Re(s − 1/2)| ≤ 1/2` + `Real.cosh_le_cosh`. -/
lemma ptwise_bound_cosh_kernel_strip (s : ℂ) (hs_nn : 0 ≤ s.re) (hs_le : s.re ≤ 1) (t : ℝ) :
    ‖(2 : ℂ) * Complex.cosh ((s - (1 / 2 : ℂ)) * (t : ℂ)) * ((ZD.ψ_mellin t : ℝ) : ℂ)‖ ≤
    2 * Real.cosh (t/2) * |ZD.ψ_mellin t| := by
  rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
  have h_cosh := complex_cosh_norm_le_cosh_re ((s - 1/2) * (t : ℂ))
  have h_re : ((s - 1/2) * (t : ℂ)).re = (s.re - 1/2) * t := by
    simp [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_im]
  rw [h_re] at h_cosh
  have h_abs_bound : |(s.re - 1/2) * t| ≤ |t/2| := by
    rw [abs_mul]
    have h1 : |s.re - 1/2| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
    have h_t2 : |t/2| = (1/2) * |t| := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; ring
    rw [h_t2]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg t)
  have h_cosh_mono : Real.cosh ((s.re - 1/2) * t) ≤ Real.cosh (t/2) := by
    rw [Real.cosh_le_cosh]; exact h_abs_bound
  have h_cosh_final := le_trans h_cosh h_cosh_mono
  have h_abs_ψ_nn : 0 ≤ |ZD.ψ_mellin t| := abs_nonneg _
  have h_step : 2 * ‖Complex.cosh ((s - 1/2) * (t : ℂ))‖ ≤ 2 * Real.cosh (t/2) :=
    mul_le_mul_of_nonneg_left h_cosh_final (by norm_num : (0:ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_right h_step h_abs_ψ_nn

/-- **Bound on Λ₀ on the closed critical strip**. Via the Mellin identity
`I_theta_of ψ_mellin = completedRiemannZeta₀` and the pointwise dominator
`2·cosh(t/2)·|ψ_mellin t|` (integrable by `integrable_cosh_half_abs_ψ_mellin`),
we get `‖completedRiemannZeta₀ s‖ ≤ M` for all `s` in the closed strip
`[0, 1]`, where `M` is the integral of the dominator (plus a `+1` slack for
positivity). -/
theorem completedRiemannZeta₀_bounded_on_strip :
    ∃ M : ℝ, 0 < M ∧
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
        ‖completedRiemannZeta₀ s‖ ≤ M := by
  set M₀ : ℝ := ∫ t in Set.Ioi (0:ℝ), 2 * Real.cosh (t/2) * |ZD.ψ_mellin t| with hM0def
  have h_int := integrable_cosh_half_abs_ψ_mellin
  have hM0_nn : 0 ≤ M₀ := by
    apply MeasureTheory.integral_nonneg; intro t; positivity
  refine ⟨M₀ + 1, by linarith, ?_⟩
  intro s hs_nn hs_le
  rw [← ZD.I_theta_of_ψ_mellin_eq_completedRiemannZeta₀ s]
  have h_integrable_norm :
      IntegrableOn (fun t : ℝ =>
          ‖(2 : ℂ) * Complex.cosh ((s - (1 / 2 : ℂ)) * (t : ℂ)) *
            ((ZD.ψ_mellin t : ℝ) : ℂ)‖) (Set.Ioi 0) :=
    (ZD.integrable_I_theta_integrand s).norm
  have h_ptwise :
      (fun t : ℝ => ‖(2 : ℂ) * Complex.cosh ((s - (1 / 2 : ℂ)) * (t : ℂ)) *
          ((ZD.ψ_mellin t : ℝ) : ℂ)‖) ≤ᵐ[volume]
      (fun t : ℝ => 2 * Real.cosh (t/2) * |ZD.ψ_mellin t|) :=
    Filter.Eventually.of_forall (ptwise_bound_cosh_kernel_strip s hs_nn hs_le)
  have h2 :
      ∫ (x : ℝ) in Ioi 0,
          ‖(2 : ℂ) * Complex.cosh ((s - 1 / 2) * (x : ℂ)) * ((ZD.ψ_mellin x : ℝ) : ℂ)‖ ≤
      ∫ (x : ℝ) in Ioi 0, 2 * Real.cosh (x / 2) * |ZD.ψ_mellin x| :=
    MeasureTheory.setIntegral_mono_ae h_integrable_norm h_int h_ptwise
  have h1 :
      ‖∫ (a : ℝ) in Ioi 0,
          (2 : ℂ) * Complex.cosh ((s - 1 / 2) * (a : ℂ)) * ((ZD.ψ_mellin a : ℝ) : ℂ)‖ ≤
      ∫ (a : ℝ) in Ioi 0,
          ‖(2 : ℂ) * Complex.cosh ((s - 1 / 2) * (a : ℂ)) * ((ZD.ψ_mellin a : ℝ) : ℂ)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  show ‖ZD.I_theta_of ZD.ψ_mellin s‖ ≤ M₀ + 1
  unfold ZD.I_theta_of
  linarith

/-- **Step 1a** — polynomial-order bound on ξ inside the critical strip.
Unconditional now that `zetaPolynomialBoundInStrip_from_euler_maclaurin`
(in `ZetaStripBound.lean`) provides the ζ bound directly. Routes through
`riemannXi_vertical_decay_of_zetaBound`. -/
theorem xi_bound_in_strip :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ →
      0 ≤ s.re → s.re ≤ 1 →
        Real.log (‖ZD.riemannXi s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖ := by
  -- Reduction to a polynomial bound on ξ in the closed strip, then use
  -- log(x+1) ≤ x slack to convert a polynomial bound to the target.
  -- Claim: ∃ A K R_poly, ∀ s in strip with ‖s‖ ≥ R_poly, ‖ξ(s)‖ ≤ A · ‖s‖^K.
  -- With that, log(‖ξ‖+1) ≤ log(A·‖s‖^K + 1) ≤ log(A+1) + K·log‖s‖
  -- ≤ (K+1+log(A+1)) · ‖s‖ · log‖s‖ for ‖s‖ ≥ max(A+2, e).
  -- The polynomial bound is the σ-uniform Phragmén–Lindelöf consequence of
  -- `zetaPolynomialBoundInStrip_from_euler_maclaurin` + `Gammaℝ_vertical_decay`
  -- applied to `ξ/(s+2)^N`, analogous to `zetaRegularizer_bound_in_strip`
  -- in `ZetaStripBound.lean` — scoped as a single `have` sorry below.
  have h_poly : ∃ (A K R_poly : ℝ), 0 < A ∧ 0 < K ∧ 0 < R_poly ∧
      ∀ s : ℂ, R_poly ≤ ‖s‖ → 0 ≤ s.re → s.re ≤ 1 →
        ‖ZD.riemannXi s‖ ≤ A * ‖s‖ ^ K := by
    -- CLOSED via the Mellin route (rather than Phragmén–Lindelöf).
    --
    -- Strategy: use the Mellin identity
    --   `I_theta_of ψ_mellin s = completedRiemannZeta₀ s`
    -- from `MellinPathToXi.lean` and bound the cosh-kernel integral directly
    -- on the strip, using `|cosh(a+ib)| ≤ cosh(a)` and `|Re s − 1/2| ≤ 1/2`
    -- on the strip. This avoids the order-1 subexponential hypothesis needed
    -- for PL. The bound on `Λ₀` is packaged as
    -- `completedRiemannZeta₀_bounded_on_strip` above.
    obtain ⟨M, hM_pos, hM_bnd⟩ := completedRiemannZeta₀_bounded_on_strip
    refine ⟨M + 1, 2, 2, by linarith, by norm_num, by norm_num, ?_⟩
    intro s hR hs_nn hs_le
    have hs_pos : 0 < ‖s‖ := by linarith
    have hs_ge_one : 1 ≤ ‖s‖ := by linarith
    -- Unfold ξ(s) = (s(s-1)/2)·Λ₀(s) + 1/2
    have hxi_eq : ZD.riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2 := rfl
    rw [hxi_eq]
    -- ‖(s(s-1)/2)·Λ₀(s) + 1/2‖ ≤ ‖(s(s-1)/2)·Λ₀(s)‖ + 1/2
    have h_tri : ‖(s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2‖ ≤
        ‖(s * (s - 1) / 2) * completedRiemannZeta₀ s‖ + ‖(1/2 : ℂ)‖ := norm_add_le _ _
    have h_norm_half : ‖(1/2 : ℂ)‖ = 1/2 := by simp
    rw [h_norm_half] at h_tri
    -- Split the norm of the product.
    have h_prod : ‖(s * (s - 1) / 2) * completedRiemannZeta₀ s‖ =
        ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖ := norm_mul _ _
    rw [h_prod] at h_tri
    -- Bound ‖s(s-1)/2‖ ≤ ‖s‖·(‖s‖+1)/2 ≤ ‖s‖² (for ‖s‖ ≥ 1, actually ≥ 2 here).
    have h_s1 : ‖s - 1‖ ≤ ‖s‖ + 1 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by rw [norm_one]
    have h_sub_le : ‖s - 1‖ ≤ 2 * ‖s‖ := by linarith
    have h_ss1 : ‖s * (s - 1) / 2‖ ≤ ‖s‖ * ‖s‖ := by
      rw [norm_div, norm_mul, show ‖(2:ℂ)‖ = 2 from Complex.norm_two]
      have h_num : ‖s‖ * ‖s - 1‖ ≤ ‖s‖ * (2 * ‖s‖) :=
        mul_le_mul_of_nonneg_left h_sub_le (norm_nonneg _)
      calc ‖s‖ * ‖s - 1‖ / 2
          ≤ (‖s‖ * (2 * ‖s‖)) / 2 :=
            div_le_div_of_nonneg_right h_num (by norm_num : (0:ℝ) ≤ 2)
        _ = ‖s‖ * ‖s‖ := by ring
    -- Plug in the Λ₀ bound.
    have h_Lam : ‖completedRiemannZeta₀ s‖ ≤ M := hM_bnd s hs_nn hs_le
    have h_Lam_nn : 0 ≤ ‖completedRiemannZeta₀ s‖ := norm_nonneg _
    have h_s2_nn : 0 ≤ ‖s‖ * ‖s‖ := by positivity
    have h_main : ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖ ≤ (‖s‖ * ‖s‖) * M := by
      calc ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖
          ≤ (‖s‖ * ‖s‖) * ‖completedRiemannZeta₀ s‖ :=
            mul_le_mul_of_nonneg_right h_ss1 h_Lam_nn
        _ ≤ (‖s‖ * ‖s‖) * M := mul_le_mul_of_nonneg_left h_Lam h_s2_nn
    -- ‖s‖ ≥ 2 ⇒ ‖s‖² ≥ 4 ⇒ (1/2) ≤ ‖s‖², so the `+1/2` fits in the `+1` slack.
    have hs_sq_ge_4 : (4:ℝ) ≤ ‖s‖ * ‖s‖ := by
      have h := mul_le_mul hR hR (by norm_num : (0:ℝ) ≤ 2) (by linarith)
      linarith
    have h_half : (1:ℝ)/2 ≤ ‖s‖ * ‖s‖ := by linarith
    -- Convert ‖s‖² to ‖s‖ ^ (2 : ℝ).
    have h_rpow : ‖s‖ ^ (2 : ℝ) = ‖s‖ * ‖s‖ := by
      rw [show (2:ℝ) = ((2:ℕ) : ℝ) from by norm_num, Real.rpow_natCast, pow_two]
    rw [h_rpow]
    linarith
  obtain ⟨A, K, R_poly, hA, hK, hR_poly, h_poly_bound⟩ := h_poly
  -- Arithmetic: log-of-poly ≤ C · ‖s‖ · log ‖s‖.
  set C : ℝ := K + 1 + Real.log (A + 1) with hC_def
  have hlogA_nn : 0 ≤ Real.log (A + 1) := Real.log_nonneg (by linarith)
  have hC_pos : 0 < C := by show 0 < K + 1 + Real.log (A + 1); linarith
  -- R₀ = max(R_poly, e, A+2): ensures ‖s‖ ≥ 1, log ‖s‖ ≥ 1, A+1 ≤ ‖s‖.
  set R₀ : ℝ := max (max R_poly (Real.exp 1)) (A + 2) with hR₀_def
  have hR₀_pos : 0 < R₀ := by
    apply lt_max_of_lt_left
    apply lt_max_of_lt_right
    exact Real.exp_pos _
  refine ⟨C, hC_pos, R₀, hR₀_pos, ?_⟩
  intro s hs_R hs_re_nn hs_re_le
  have hs_R_poly : R_poly ≤ ‖s‖ :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs_R
  have hs_exp : Real.exp 1 ≤ ‖s‖ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs_R
  have hs_Aplus : A + 2 ≤ ‖s‖ := le_trans (le_max_right _ _) hs_R
  have hs_pos : 0 < ‖s‖ := lt_of_lt_of_le (Real.exp_pos _) hs_exp
  have hs_one : (1 : ℝ) ≤ ‖s‖ := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      have h1 := Real.exp_one_gt_d9
      linarith
    linarith
  have hs_log_nn : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hs_one
  have hs_log_ge_one : 1 ≤ Real.log ‖s‖ := by
    have h := Real.log_le_log (Real.exp_pos 1) hs_exp
    rw [Real.log_exp] at h; exact h
  have h_xi_poly : ‖ZD.riemannXi s‖ ≤ A * ‖s‖ ^ K :=
    h_poly_bound s hs_R_poly hs_re_nn hs_re_le
  have hs_pow_pos : 0 < ‖s‖ ^ K := Real.rpow_pos_of_pos hs_pos _
  have hs_pow_ge_one : 1 ≤ ‖s‖ ^ K := Real.one_le_rpow hs_one hK.le
  -- log(‖ξ‖ + 1) ≤ log(A·‖s‖^K + 1)
  have hlog_mono : Real.log (‖ZD.riemannXi s‖ + 1) ≤
      Real.log (A * ‖s‖ ^ K + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  -- log(A·‖s‖^K + 1) ≤ log((A+1) · ‖s‖^K) = log(A+1) + K · log ‖s‖
  have h_sum_le : A * ‖s‖ ^ K + 1 ≤ (A + 1) * ‖s‖ ^ K := by
    have hexpand : (A + 1) * ‖s‖ ^ K = A * ‖s‖ ^ K + ‖s‖ ^ K := by ring
    rw [hexpand]; linarith
  have hlog_split : Real.log (A * ‖s‖ ^ K + 1) ≤
      Real.log (A + 1) + K * Real.log ‖s‖ := by
    calc Real.log (A * ‖s‖ ^ K + 1)
        ≤ Real.log ((A + 1) * ‖s‖ ^ K) :=
          Real.log_le_log (by positivity) h_sum_le
      _ = Real.log (A + 1) + Real.log (‖s‖ ^ K) :=
          Real.log_mul (by linarith) (ne_of_gt hs_pow_pos)
      _ = Real.log (A + 1) + K * Real.log ‖s‖ := by
          rw [Real.log_rpow hs_pos]
  have hlog_total : Real.log (‖ZD.riemannXi s‖ + 1) ≤
      Real.log (A + 1) + K * Real.log ‖s‖ := le_trans hlog_mono hlog_split
  -- Finish: log(A+1) + K·log‖s‖ ≤ C·‖s‖·log‖s‖.
  have h_s_log_nn : 0 ≤ ‖s‖ * Real.log ‖s‖ := by positivity
  have hlogA_le_s : Real.log (A + 1) ≤ ‖s‖ * Real.log ‖s‖ := by
    have h1 : Real.log (A + 1) ≤ Real.log ‖s‖ :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
      calc Real.log ‖s‖ = 1 * Real.log ‖s‖ := by ring
        _ ≤ ‖s‖ * Real.log ‖s‖ :=
            mul_le_mul_of_nonneg_right hs_one hs_log_nn
    linarith
  have h_K_log_s : K * Real.log ‖s‖ ≤ K * (‖s‖ * Real.log ‖s‖) := by
    apply mul_le_mul_of_nonneg_left _ hK.le
    calc Real.log ‖s‖ = 1 * Real.log ‖s‖ := by ring
      _ ≤ ‖s‖ * Real.log ‖s‖ := mul_le_mul_of_nonneg_right hs_one hs_log_nn
  have h_combined : Real.log (A + 1) + K * Real.log ‖s‖ ≤
      (1 + K) * (‖s‖ * Real.log ‖s‖) := by
    have h_expand : (1 + K) * (‖s‖ * Real.log ‖s‖) =
        ‖s‖ * Real.log ‖s‖ + K * (‖s‖ * Real.log ‖s‖) := by ring
    linarith
  have h_C_ge : (1 + K : ℝ) ≤ C := by show 1 + K ≤ K + 1 + Real.log (A + 1); linarith
  have h_final_step : (1 + K) * (‖s‖ * Real.log ‖s‖) ≤ C * ‖s‖ * Real.log ‖s‖ := by
    have h := mul_le_mul_of_nonneg_right h_C_ge h_s_log_nn
    calc (1 + K) * (‖s‖ * Real.log ‖s‖)
        ≤ C * (‖s‖ * Real.log ‖s‖) := h
      _ = C * ‖s‖ * Real.log ‖s‖ := by ring
  linarith

/-! ### Helpers for `xi_bound_right_halfplane`

Strategy: use the Mellin identity `I_theta_of ψ_mellin s = Λ₀(s)` together
with the non-negativity `ψ_mellin t ≥ 0` (from `evenKernel 0 u ≥ 1`) to
reduce `‖Λ₀(s)‖` to the real value `Λ₀(Re s)` for `Re s ≥ 1/2`, and then
bound the real-σ completed-zeta via the classical identity
`Λ(σ) = π^{-σ/2}·Γ(σ/2)·ζ(σ)` + `ζ(σ) ≤ ζ(2)` + `Γ(σ/2) ≤ ⌈σ/2⌉^⌈σ/2⌉`.
-/

/-- **`evenKernel 0 u ≥ 1` for `u > 0`.** From `hasSum_int_evenKernel` +
single-term bound (n = 0 contributes `exp(0) = 1`). -/
theorem one_le_evenKernel_zero {u : ℝ} (hu : 0 < u) :
    1 ≤ HurwitzZeta.evenKernel 0 u := by
  have h := HurwitzZeta.hasSum_int_evenKernel (0 : ℝ) hu
  simp only [add_zero] at h
  have h_summable : Summable (fun n : ℤ ↦ Real.exp (-π * (n : ℝ) ^ 2 * u)) := h.summable
  have h_eq : HurwitzZeta.evenKernel ((0 : ℝ) : UnitAddCircle) u =
      ∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * u) := h.tsum_eq.symm
  have h_zero : HurwitzZeta.evenKernel ((0 : ℝ) : UnitAddCircle) u =
      HurwitzZeta.evenKernel 0 u := by norm_cast
  rw [h_zero] at h_eq
  have h_single : (fun n : ℤ ↦ Real.exp (-π * (n : ℝ) ^ 2 * u)) (0 : ℤ) ≤
      ∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * u) := by
    apply Summable.le_tsum h_summable (i := (0 : ℤ))
    intro j _; exact (Real.exp_pos _).le
  have hs1 : (fun n : ℤ ↦ Real.exp (-π * (n : ℝ) ^ 2 * u)) (0 : ℤ) = 1 := by
    simp [Real.exp_zero]
  rw [hs1] at h_single
  linarith [h_eq ▸ h_single]

/-- **`ψ_mellin t ≥ 0` for all `t`.** Since `ψ_mellin t = (θ(e^(2t)) − 1)·e^(t/2)`,
with `θ ≥ 1` and `e^(t/2) ≥ 0`. -/
theorem ψ_mellin_nonneg (t : ℝ) : 0 ≤ ZD.ψ_mellin t := by
  unfold ZD.ψ_mellin
  have hexp2t : 0 < Real.exp (2 * t) := Real.exp_pos _
  have h1 : 1 ≤ HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) :=
    one_le_evenKernel_zero hexp2t
  have h_sub : 0 ≤ HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1 := by linarith
  have h_exp : 0 ≤ Real.exp (t / 2) := (Real.exp_pos _).le
  exact mul_nonneg h_sub h_exp

/-- **`I_theta_of ψ_mellin σ` for real `σ` is a real-valued complex number**
(imaginary part zero), equal to the real integral of the real integrand. -/
theorem I_theta_of_ψ_mellin_real (σ : ℝ) :
    ZD.I_theta_of ZD.ψ_mellin (σ : ℂ) =
    ((∫ t in Set.Ioi (0 : ℝ), 2 * Real.cosh ((σ - 1/2) * t) * ZD.ψ_mellin t : ℝ) : ℂ) := by
  unfold ZD.I_theta_of
  rw [show (((∫ t in Set.Ioi (0 : ℝ), 2 * Real.cosh ((σ - 1/2) * t) * ZD.ψ_mellin t : ℝ) : ℂ)) =
      ∫ t in Set.Ioi (0 : ℝ),
        ((2 * Real.cosh ((σ - 1/2) * t) * ZD.ψ_mellin t : ℝ) : ℂ) from
    (integral_ofReal (f := fun t => 2 * Real.cosh ((σ - 1/2) * t) * ZD.ψ_mellin t)).symm]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only
  have h1 : ((σ : ℂ) - 1/2) * (t : ℂ) = (((σ - 1/2) * t : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, show Complex.cosh (((σ - 1/2) * t : ℝ) : ℂ) =
    ((Real.cosh ((σ - 1/2) * t) : ℝ) : ℂ) from (Complex.ofReal_cosh _).symm]
  push_cast; ring

/-- **`completedRiemannZeta₀ σ` is real-valued** (imaginary part zero)
for real `σ`, via `I_theta_of_ψ_mellin_real`. -/
theorem completedRiemannZeta₀_real_re (σ : ℝ) :
    completedRiemannZeta₀ (σ : ℂ) =
      ((∫ t in Set.Ioi (0 : ℝ), 2 * Real.cosh ((σ - 1/2) * t) * ZD.ψ_mellin t : ℝ) : ℂ) := by
  rw [← ZD.I_theta_of_ψ_mellin_eq_completedRiemannZeta₀]
  exact I_theta_of_ψ_mellin_real σ

/-- **Real-valued `Λ₀(σ)` for real `σ`**: the integral formula gives a
real number. Denote this real value `Λ₀_real σ`. -/
noncomputable def Λ₀_real (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), 2 * Real.cosh ((σ - 1/2) * t) * ZD.ψ_mellin t

theorem Λ₀_real_nonneg (σ : ℝ) (hσ : 1/2 ≤ σ) : 0 ≤ Λ₀_real σ := by
  unfold Λ₀_real
  apply MeasureTheory.integral_nonneg
  intro t
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · have h_cosh_nn : 0 ≤ Real.cosh ((σ - 1/2) * t) := (Real.cosh_pos _).le
    have h_two_nn : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_nonneg (mul_nonneg h_two_nn h_cosh_nn) (ψ_mellin_nonneg t)
  · -- Wait, integrand over ℝ — but we're using `Ioi 0`, so this is the Ioi 0 integral.
    -- `integral_nonneg` on measure restricted to Ioi 0 — we need to show the integrand is ≥ 0
    -- on Ioi 0. Let me adjust.
    have h_cosh_nn : 0 ≤ Real.cosh ((σ - 1/2) * t) := (Real.cosh_pos _).le
    exact mul_nonneg (mul_nonneg (by norm_num) h_cosh_nn) (ψ_mellin_nonneg t)

/-- **Completed-zeta equals the real integral**: for real σ, `Λ₀(σ) = Λ₀_real σ` (as ℂ). -/
theorem completedRiemannZeta₀_real_eq (σ : ℝ) :
    completedRiemannZeta₀ (σ : ℂ) = ((Λ₀_real σ : ℝ) : ℂ) := by
  rw [completedRiemannZeta₀_real_re σ]
  rfl

/-- **Key bound**: `‖Λ₀(s)‖ ≤ Λ₀_real(Re s)` for `Re s ≥ 1/2`.
Key ingredients: (1) `ψ_mellin ≥ 0`; (2) `‖cosh z‖ ≤ cosh (Re z)`; (3) Mellin identity. -/
theorem norm_completedRiemannZeta₀_le_Λ₀_real (s : ℂ) (hs : 1/2 ≤ s.re) :
    ‖completedRiemannZeta₀ s‖ ≤ Λ₀_real s.re := by
  rw [← ZD.I_theta_of_ψ_mellin_eq_completedRiemannZeta₀ s]
  unfold ZD.I_theta_of Λ₀_real
  -- Step 1: norm of integral ≤ integral of norm
  have h_norm_le :
      ‖∫ t in Set.Ioi (0 : ℝ),
          (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * (ZD.ψ_mellin t : ℂ)‖ ≤
      ∫ t in Set.Ioi (0 : ℝ),
          ‖(2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * (ZD.ψ_mellin t : ℂ)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  -- Step 2: pointwise bound on integrand
  have h_ptwise : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖(2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * (ZD.ψ_mellin t : ℂ)‖ ≤
      2 * Real.cosh ((s.re - 1/2) * t) * ZD.ψ_mellin t := by
    intro t ht
    have ht_pos : 0 < t := ht
    have ht_nn : 0 ≤ t := ht_pos.le
    have h_psi_nn : 0 ≤ ZD.ψ_mellin t := ψ_mellin_nonneg t
    -- ‖2‖ = 2, ‖(ψ_mellin t : ℂ)‖ = |ψ_mellin t| = ψ_mellin t (since ≥ 0)
    rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg h_psi_nn]
    -- Bound ‖Complex.cosh ((s - 1/2) * t)‖ ≤ Real.cosh (Re((s-1/2)*t))
    have h_cosh := complex_cosh_norm_le_cosh_re ((s - 1/2) * (t : ℂ))
    have h_re : ((s - 1/2) * (t : ℂ)).re = (s.re - 1/2) * t := by
      simp [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.sub_im]
    rw [h_re] at h_cosh
    have h_step : 2 * ‖Complex.cosh ((s - 1/2) * (t : ℂ))‖ ≤
        2 * Real.cosh ((s.re - 1/2) * t) :=
      mul_le_mul_of_nonneg_left h_cosh (by norm_num : (0:ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_right h_step h_psi_nn
  -- Step 3: integral of norm ≤ integral of dominator
  have h_integrable_norm :
      IntegrableOn (fun t : ℝ =>
          ‖(2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * (ZD.ψ_mellin t : ℂ)‖)
        (Set.Ioi 0) :=
    (ZD.integrable_I_theta_integrand s).norm
  -- Need: integrability of 2·cosh((Re s - 1/2)·t)·ψ_mellin(t). Use integrable_I_theta_integrand
  -- at s' = (s.re : ℂ), noting that its norm equals this since the integrand is real ≥ 0.
  have h_integrable_dom :
      IntegrableOn (fun t : ℝ => 2 * Real.cosh ((s.re - 1/2) * t) * ZD.ψ_mellin t)
        (Set.Ioi 0) := by
    have h_base := (ZD.integrable_I_theta_integrand (s.re : ℂ)).norm
    -- ‖integrand (s.re)‖ pointwise equals 2·cosh((s.re - 1/2)·t)·ψ_mellin(t) (since ≥ 0)
    have h_eq :
        (fun t : ℝ => ‖(2 : ℂ) * Complex.cosh (((s.re : ℂ) - 1/2) * (t : ℂ)) *
            (ZD.ψ_mellin t : ℂ)‖) =
        (fun t : ℝ => 2 * Real.cosh ((s.re - 1/2) * t) * ZD.ψ_mellin t) := by
      funext t
      rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (ψ_mellin_nonneg t)]
      have h1 : ((s.re : ℂ) - 1/2) * (t : ℂ) = (((s.re - 1/2) * t : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1, show Complex.cosh (((s.re - 1/2) * t : ℝ) : ℂ) =
        ((Real.cosh ((s.re - 1/2) * t) : ℝ) : ℂ) from (Complex.ofReal_cosh _).symm,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    rw [← h_eq]; exact h_base
  have h_int_mono :
      ∫ t in Set.Ioi (0 : ℝ),
          ‖(2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * (ZD.ψ_mellin t : ℂ)‖ ≤
      ∫ t in Set.Ioi (0 : ℝ), 2 * Real.cosh ((s.re - 1/2) * t) * ZD.ψ_mellin t :=
    MeasureTheory.setIntegral_mono_on h_integrable_norm h_integrable_dom
      measurableSet_Ioi h_ptwise
  linarith

/-! ### Bound on `Λ₀_real σ` for σ ≥ 1

For σ ∈ [1, 2]: by continuity of `completedRiemannZeta₀` on the compact
interval `[1, 2]`, `|Λ₀_real σ|` is bounded by some constant.

For σ ≥ 2: use `Λ(σ) = π^{-σ/2}·Γ(σ/2)·ζ(σ)` with `ζ(σ) ≤ ζ(2)`,
`π^{-σ/2} ≤ 1`, and `Γ(σ/2) ≤ ⌈σ/2⌉^⌈σ/2⌉ ≤ σ^σ`.
-/

/-- **Bound on `Λ₀_real` on `[1, 4]`**: by continuity of `completedRiemannZeta₀`. -/
theorem Λ₀_real_bounded_one_four :
    ∃ M₁ : ℝ, 0 < M₁ ∧ ∀ σ : ℝ, 1 ≤ σ → σ ≤ 4 → Λ₀_real σ ≤ M₁ := by
  have h_cont : ContinuousOn (fun σ : ℝ => Λ₀_real σ) (Set.Icc (1:ℝ) 4) := by
    have h_cont_Λ : Continuous (fun σ : ℝ => completedRiemannZeta₀ (σ : ℂ)) :=
      differentiable_completedZeta₀.continuous.comp Complex.continuous_ofReal
    have h_eq : ∀ σ : ℝ, ((Λ₀_real σ : ℝ) : ℂ) = completedRiemannZeta₀ (σ : ℂ) :=
      fun σ => (completedRiemannZeta₀_real_eq σ).symm
    have h_re_cont : Continuous (fun σ : ℝ => (completedRiemannZeta₀ (σ : ℂ)).re) :=
      Complex.continuous_re.comp h_cont_Λ
    have h_eq_re : ∀ σ : ℝ, Λ₀_real σ = (completedRiemannZeta₀ (σ : ℂ)).re := by
      intro σ
      have := h_eq σ
      have : ((Λ₀_real σ : ℝ) : ℂ).re = (completedRiemannZeta₀ (σ : ℂ)).re :=
        congrArg Complex.re this
      simp at this
      exact this
    have : (fun σ : ℝ => Λ₀_real σ) = (fun σ : ℝ => (completedRiemannZeta₀ (σ : ℂ)).re) := by
      funext σ; exact h_eq_re σ
    rw [this]
    exact h_re_cont.continuousOn
  have h_cpt : IsCompact (Set.Icc (1:ℝ) 4) := isCompact_Icc
  obtain ⟨M, hM⟩ := h_cpt.bddAbove_image h_cont
  refine ⟨max M 1, lt_max_of_lt_right one_pos, ?_⟩
  intro σ hσ1 hσ2
  have hσ_mem : σ ∈ Set.Icc (1:ℝ) 4 := ⟨hσ1, hσ2⟩
  have h_in_image : Λ₀_real σ ∈ (fun σ : ℝ => Λ₀_real σ) '' (Set.Icc (1:ℝ) 4) :=
    ⟨σ, hσ_mem, rfl⟩
  exact le_trans (hM h_in_image) (le_max_left _ _)

/-- **Key consequence**: for real `σ ≥ 1/2`, `Λ₀_real σ = ‖completedRiemannZeta₀ σ‖`
(since `Λ₀_real σ ≥ 0`). -/
theorem Λ₀_real_eq_norm (σ : ℝ) (hσ : 1/2 ≤ σ) :
    Λ₀_real σ = ‖completedRiemannZeta₀ (σ : ℂ)‖ := by
  rw [completedRiemannZeta₀_real_eq]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Λ₀_real_nonneg σ hσ)]

/-- **Norm bound on `completedRiemannZeta₀ σ` for real σ ≥ 4**. Via the classical
identity `Λ(s) = π^{-s/2}·Γ(s/2)·ζ(s)` + `‖ζ(σ)‖ ≤ ζ(2)` + `π^{-σ/2} ≤ 1` + Γ-bound.
Threshold σ ≥ 4 ensures σ/2 ≥ 2 so we can use `Real.Gamma_strictMonoOn_Ici` on σ/2. -/
theorem norm_completedRiemannZeta₀_real_le_of_four_le (σ : ℝ) (hσ : 4 ≤ σ) :
    ‖completedRiemannZeta₀ (σ : ℂ)‖ ≤
      Real.Gamma (σ/2) * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) + 2 := by
  have hσ_pos : 0 < σ := by linarith
  have hσ_gt_one : 1 < σ := by linarith
  have hσ_re_gt_one : (1 : ℝ) < (σ : ℂ).re := by simp; linarith
  have hσ_re_two_le : (2 : ℝ) ≤ (σ : ℂ).re := by simp; linarith
  -- completedRiemannZeta s = π^(-s/2)·Γ(s/2)·ζ(s) for Re s > 1.
  have h_classical := completedZeta_eq_tsum_of_one_lt_re hσ_re_gt_one
  -- Λ = Λ₀ - 1/s - 1/(1-s), so Λ₀ = Λ + 1/s + 1/(1-s).
  have h_Λ_Λ₀ := completedRiemannZeta_eq (σ : ℂ)
  -- Rearrange: completedRiemannZeta₀ σ = completedRiemannZeta σ + 1/σ + 1/(1-σ).
  have h_Λ₀ : completedRiemannZeta₀ (σ : ℂ) =
      completedRiemannZeta (σ : ℂ) + 1/(σ : ℂ) + 1/(1 - (σ : ℂ)) := by
    rw [h_Λ_Λ₀]; ring
  -- Bound ‖Λ₀(σ)‖ ≤ ‖Λ(σ)‖ + 1/σ + 1/(σ-1).
  have h_norm_triangle : ‖completedRiemannZeta₀ (σ : ℂ)‖ ≤
      ‖completedRiemannZeta (σ : ℂ)‖ + ‖(1 : ℂ)/(σ : ℂ)‖ + ‖(1 : ℂ)/(1 - (σ : ℂ))‖ := by
    rw [h_Λ₀]
    calc ‖completedRiemannZeta (σ : ℂ) + 1/(σ : ℂ) + 1/(1 - (σ : ℂ))‖
        ≤ ‖completedRiemannZeta (σ : ℂ) + 1/(σ : ℂ)‖ + ‖(1:ℂ)/(1 - (σ : ℂ))‖ := norm_add_le _ _
      _ ≤ ‖completedRiemannZeta (σ : ℂ)‖ + ‖(1:ℂ)/(σ : ℂ)‖ + ‖(1:ℂ)/(1 - (σ : ℂ))‖ := by
          have := norm_add_le (completedRiemannZeta (σ : ℂ)) ((1:ℂ)/(σ : ℂ))
          linarith
  -- Bound ‖Λ(σ)‖ ≤ Γ(σ/2) · ζ(2).
  have h_norm_pi : ‖((π : ℂ) ^ (-(σ : ℂ) / 2))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    rw [show (-(σ : ℂ) / 2).re = -σ/2 from by simp [Complex.neg_re]]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · linarith [Real.pi_gt_three]
    · linarith
  -- ‖Γ(σ/2 : ℂ)‖ = Γ(σ/2) since σ/2 > 0 is real (> 0) and Complex.Gamma of real = Real.Gamma.
  have h_norm_Gamma : ‖Complex.Gamma ((σ : ℂ) / 2)‖ = Real.Gamma (σ/2) := by
    have h1 : ((σ : ℂ) / 2) = ((σ/2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.Gamma_nonneg_of_nonneg (by linarith))]
  -- ‖ζ(σ)‖ ≤ ζ(2).
  have h_norm_zeta : ‖riemannZeta (σ : ℂ)‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) :=
    ZD.StripBound.norm_zeta_le_zeta_two_of_two_le_re hσ_re_two_le
  -- Combine: ‖Λ(σ)‖ ≤ 1 · Γ(σ/2) · ζ(2) = Γ(σ/2) · ζ(2).
  have h_Λ_norm : ‖completedRiemannZeta (σ : ℂ)‖ ≤
      Real.Gamma (σ/2) * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) := by
    -- Express the tsum in h_classical as a regular sum.
    have h_tsum_cpx : (∑' n : ℕ, 1 / ((n : ℂ) ^ (σ : ℂ))) = riemannZeta (σ : ℂ) :=
      (zeta_eq_tsum_one_div_nat_cpow (by linarith)).symm
    rw [h_classical, h_tsum_cpx, norm_mul, norm_mul, h_norm_Gamma]
    have h_two_nn : 0 ≤ Real.Gamma (σ/2) := Real.Gamma_nonneg_of_nonneg (by linarith)
    have h_ζ_nn : 0 ≤ ‖riemannZeta (σ : ℂ)‖ := norm_nonneg _
    calc ‖((π : ℂ) ^ (-(σ : ℂ) / 2))‖ * Real.Gamma (σ / 2) * ‖riemannZeta (σ : ℂ)‖
        ≤ 1 * Real.Gamma (σ / 2) * ‖riemannZeta (σ : ℂ)‖ := by
          apply mul_le_mul_of_nonneg_right
          apply mul_le_mul_of_nonneg_right h_norm_pi h_two_nn
          exact h_ζ_nn
      _ = Real.Gamma (σ/2) * ‖riemannZeta (σ : ℂ)‖ := by ring
      _ ≤ Real.Gamma (σ/2) * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h_norm_zeta h_two_nn
  -- Bound 1/σ + 1/(σ-1) ≤ 1 for σ ≥ 2.
  have h_norm_1σ : ‖(1 : ℂ)/(σ : ℂ)‖ ≤ 1/2 := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ_pos]
    rw [div_le_div_iff₀ hσ_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have h_norm_11σ : ‖(1 : ℂ)/(1 - (σ : ℂ))‖ ≤ 1/1 := by
    rw [norm_div, norm_one]
    have h_denom : ‖(1 : ℂ) - (σ : ℂ)‖ = σ - 1 := by
      rw [show (1 : ℂ) - (σ : ℂ) = -((σ : ℂ) - 1) from by ring, norm_neg]
      rw [show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [h_denom]
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 1)]
    linarith
  have h_Γ_nn : 0 ≤ Real.Gamma (σ/2) := Real.Gamma_nonneg_of_nonneg (by linarith)
  have h_tsum_nn : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) := by
    apply tsum_nonneg
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0)]
    · have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
  linarith

/-- **Γ bound**: for `x ≥ 2`, `Real.Gamma x ≤ Nat.factorial (⌈x⌉₊ + 1)`. Combined
with `Nat.factorial n ≤ n ^ n`, this gives `Γ(x) ≤ (⌈x⌉₊ + 1)^(⌈x⌉₊ + 1)`. -/
theorem gamma_le_factorial_of_two_le (x : ℝ) (hx : 2 ≤ x) :
    Real.Gamma x ≤ (⌈x⌉₊ + 1).factorial := by
  have h_gamma_nat : Real.Gamma (((⌈x⌉₊ + 1 : ℕ) : ℝ) + 1) = (⌈x⌉₊ + 1).factorial :=
    Real.Gamma_nat_eq_factorial _
  have hx_nat : (⌈x⌉₊ : ℝ) ≥ x := Nat.le_ceil _
  have h_x_le : x ≤ ((⌈x⌉₊ + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  have h_ge2_ceil : (2 : ℝ) ≤ ((⌈x⌉₊ + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    have : (0 : ℝ) ≤ (⌈x⌉₊ : ℝ) := by positivity
    linarith
  have h_mono := Real.Gamma_strictMonoOn_Ici
  have : Real.Gamma x ≤ Real.Gamma (((⌈x⌉₊ + 1 : ℕ) : ℝ) + 1) :=
    h_mono.monotoneOn hx h_ge2_ceil h_x_le
  rw [← h_gamma_nat]; exact this

/-- **Log bound on `Real.Gamma (σ/2)` for σ ≥ 4**: `log Γ(σ/2) ≤ (σ + 2) · log(σ + 2)`. -/
theorem log_gamma_half_le (σ : ℝ) (hσ : 4 ≤ σ) :
    Real.log (Real.Gamma (σ/2)) ≤ (σ + 2) * Real.log (σ + 2) := by
  have hσ_half : 2 ≤ σ/2 := by linarith
  have h_gam_le : Real.Gamma (σ/2) ≤ (⌈σ/2⌉₊ + 1).factorial :=
    gamma_le_factorial_of_two_le (σ/2) hσ_half
  -- (⌈σ/2⌉₊ + 1).factorial ≤ (⌈σ/2⌉₊ + 1)^(⌈σ/2⌉₊ + 1)
  have h_fac_pow : ((⌈σ/2⌉₊ + 1).factorial : ℝ) ≤ ((⌈σ/2⌉₊ + 1 : ℕ) : ℝ) ^ (⌈σ/2⌉₊ + 1) := by
    exact_mod_cast Nat.factorial_le_pow (⌈σ/2⌉₊ + 1)
  have h_ceil_le : (⌈σ/2⌉₊ : ℝ) + 1 ≤ σ/2 + 2 := by
    have : (⌈σ/2⌉₊ : ℝ) ≤ σ/2 + 1 := by
      have hc := Nat.ceil_lt_add_one (a := σ/2) (by linarith : 0 ≤ σ/2)
      linarith
    linarith
  have h_ceil_pos : 0 < (⌈σ/2⌉₊ : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (⌈σ/2⌉₊ : ℝ) := by positivity
    linarith
  have h_ceil_nn : 0 ≤ ((⌈σ/2⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h_ceil1_le_2 : ((⌈σ/2⌉₊ + 1 : ℕ) : ℝ) ≤ σ/2 + 2 := by push_cast; linarith
  have h_pow_le : ((⌈σ/2⌉₊ + 1 : ℕ) : ℝ) ^ (⌈σ/2⌉₊ + 1) ≤ (σ/2 + 2) ^ (⌈σ/2⌉₊ + 1) :=
    pow_le_pow_left₀ h_ceil_nn h_ceil1_le_2 _
  have h_Γ_pos : 0 < Real.Gamma (σ/2) := Real.Gamma_pos_of_pos (by linarith)
  have h_s2p2_pos : 0 < σ/2 + 2 := by linarith
  have h_Γ_le_pow : Real.Gamma (σ/2) ≤ (σ/2 + 2) ^ (⌈σ/2⌉₊ + 1) := by
    calc Real.Gamma (σ/2) ≤ ((⌈σ/2⌉₊ + 1).factorial : ℝ) := h_gam_le
      _ ≤ ((⌈σ/2⌉₊ + 1 : ℕ) : ℝ) ^ (⌈σ/2⌉₊ + 1) := h_fac_pow
      _ ≤ (σ/2 + 2) ^ (⌈σ/2⌉₊ + 1) := h_pow_le
  have h_Γ_le_pow_pos : 0 < (σ/2 + 2) ^ (⌈σ/2⌉₊ + 1) := pow_pos h_s2p2_pos _
  -- Take log:
  have h_log_Γ : Real.log (Real.Gamma (σ/2)) ≤ Real.log ((σ/2 + 2) ^ (⌈σ/2⌉₊ + 1)) :=
    Real.log_le_log h_Γ_pos h_Γ_le_pow
  -- log(x^n) = n · log x
  have h_log_pow : Real.log ((σ/2 + 2) ^ (⌈σ/2⌉₊ + 1)) =
      (⌈σ/2⌉₊ + 1 : ℕ) * Real.log (σ/2 + 2) := by
    rw [Real.log_pow]
  rw [h_log_pow] at h_log_Γ
  -- Bound (⌈σ/2⌉₊ + 1) ≤ σ/2 + 2 ≤ σ/2 + 2.
  have h_ceil1_le : ((⌈σ/2⌉₊ + 1 : ℕ) : ℝ) ≤ σ/2 + 2 := by
    push_cast
    linarith
  -- log(σ/2 + 2) ≤ log(σ + 2) for σ ≥ 4 (since σ/2 + 2 ≤ σ + 2 for σ ≥ 0).
  have h_log_mono : Real.log (σ/2 + 2) ≤ Real.log (σ + 2) :=
    Real.log_le_log h_s2p2_pos (by linarith)
  have h_log_nn : 0 ≤ Real.log (σ/2 + 2) := by
    apply Real.log_nonneg; linarith
  -- Combine: (⌈σ/2⌉₊ + 1) · log(σ/2 + 2) ≤ (σ/2 + 2) · log(σ + 2) ≤ (σ + 2) · log(σ + 2).
  calc Real.log (Real.Gamma (σ/2))
      ≤ (⌈σ/2⌉₊ + 1 : ℕ) * Real.log (σ/2 + 2) := h_log_Γ
    _ ≤ (σ/2 + 2) * Real.log (σ/2 + 2) :=
        mul_le_mul_of_nonneg_right h_ceil1_le h_log_nn
    _ ≤ (σ + 2) * Real.log (σ/2 + 2) := by
        apply mul_le_mul_of_nonneg_right _ h_log_nn
        linarith
    _ ≤ (σ + 2) * Real.log (σ + 2) := by
        apply mul_le_mul_of_nonneg_left h_log_mono
        linarith

set_option maxHeartbeats 1000000 in
/-- **Step 1b** — bound on ξ in the right half-plane `Re s ≥ 1`.

Strategy: use `‖Λ₀(s)‖ ≤ Λ₀_real(Re s)` + bound on `Λ₀_real σ` for σ ∈ [1, 4]
(continuity) and σ ≥ 4 (classical identity + Γ ≤ σ^σ bound). -/
theorem xi_bound_right_halfplane :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → 1 ≤ s.re →
      Real.log (‖ZD.riemannXi s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖ := by
  -- Key: prove polynomial-exp bound on ξ, then take log.
  -- `‖ξ(s)‖ ≤ ‖s(s-1)/2‖·‖Λ₀(s)‖ + 1/2 ≤ ‖s‖²·‖Λ₀(s)‖ + 1/2`
  -- For `Re s ∈ [1, 4]`: `‖Λ₀(s)‖ ≤ M₁` (uniform bound) ⇒ `‖ξ(s)‖ ≤ ‖s‖²·M₁ + 1/2`
  -- For `Re s ≥ 4`: `‖Λ₀(s)‖ ≤ Λ₀_real(Re s) ≤ Γ(Re s/2)·ζ(2) + 2`
  --   ⇒ `log(‖ξ‖+1) ≤ C·‖s‖·log‖s‖` via log bound on Γ.
  obtain ⟨M₁, hM₁_pos, hM₁_bnd⟩ := Λ₀_real_bounded_one_four
  set ζ2 : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) with hζ2_def
  have hζ2_nn : 0 ≤ ζ2 := by
    apply tsum_nonneg
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0)]
    · have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
  -- Choose constants
  set C : ℝ := 10 + Real.log (M₁ + ζ2 + 3) with hC_def
  have hlogM_nn : 0 ≤ Real.log (M₁ + ζ2 + 3) := by
    apply Real.log_nonneg; linarith
  have hC_pos : 0 < C := by show 0 < 10 + Real.log (M₁ + ζ2 + 3); linarith
  -- Choose R₀ large enough: ‖s‖ ≥ max(10, e, M₁+ζ2+3)
  set R₀ : ℝ := max (max 10 (Real.exp 1)) (M₁ + ζ2 + 3) with hR₀_def
  have hR₀_pos : 0 < R₀ := by
    apply lt_max_of_lt_left
    apply lt_max_of_lt_left
    norm_num
  refine ⟨C, hC_pos, R₀, hR₀_pos, ?_⟩
  intro s hs_R hs_re
  have hs_ten : (10 : ℝ) ≤ ‖s‖ :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs_R
  have hs_exp : Real.exp 1 ≤ ‖s‖ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs_R
  have hs_M₁ : M₁ + ζ2 + 3 ≤ ‖s‖ := le_trans (le_max_right _ _) hs_R
  have hs_pos : 0 < ‖s‖ := by linarith
  have hs_one : (1 : ℝ) ≤ ‖s‖ := by linarith
  have hs_log_nn : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hs_one
  have hs_log_ge_one : 1 ≤ Real.log ‖s‖ := by
    have h := Real.log_le_log (Real.exp_pos 1) hs_exp
    rw [Real.log_exp] at h; exact h
  have h_s_log_nn : 0 ≤ ‖s‖ * Real.log ‖s‖ := by positivity
  -- `Re s ≤ ‖s‖`
  have hs_re_le : s.re ≤ ‖s‖ := Complex.re_le_norm s
  -- `Re s ≥ 1/2` for the norm-Λ₀ bound
  have hs_re_half : (1:ℝ)/2 ≤ s.re := by linarith
  -- ‖ξ(s)‖ ≤ ‖s(s-1)/2‖·‖Λ₀(s)‖ + 1/2 ≤ ‖s‖²·‖Λ₀(s)‖ + 1/2
  have hxi_eq : ZD.riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1/2 := rfl
  have h_ss1_norm : ‖s * (s - 1) / 2‖ ≤ ‖s‖ * ‖s‖ := by
    rw [norm_div, norm_mul, show ‖(2:ℂ)‖ = 2 from Complex.norm_two]
    have h_sub_le : ‖s - 1‖ ≤ 2 * ‖s‖ := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by rw [norm_one]
        _ ≤ 2 * ‖s‖ := by linarith
    have h_num : ‖s‖ * ‖s - 1‖ ≤ ‖s‖ * (2 * ‖s‖) :=
      mul_le_mul_of_nonneg_left h_sub_le (norm_nonneg _)
    calc ‖s‖ * ‖s - 1‖ / 2
        ≤ (‖s‖ * (2 * ‖s‖)) / 2 :=
          div_le_div_of_nonneg_right h_num (by norm_num : (0:ℝ) ≤ 2)
      _ = ‖s‖ * ‖s‖ := by ring
  have h_xi_bound : ‖ZD.riemannXi s‖ ≤ ‖s‖ * ‖s‖ * ‖completedRiemannZeta₀ s‖ + 1/2 := by
    rw [hxi_eq]
    calc ‖(s * (s - 1) / 2) * completedRiemannZeta₀ s + 1/2‖
        ≤ ‖(s * (s - 1) / 2) * completedRiemannZeta₀ s‖ + ‖((1:ℂ)/2)‖ := norm_add_le _ _
      _ = ‖s * (s - 1) / 2‖ * ‖completedRiemannZeta₀ s‖ + 1/2 := by
          rw [norm_mul]; congr 1; simp [norm_div, Complex.norm_two]
      _ ≤ ‖s‖ * ‖s‖ * ‖completedRiemannZeta₀ s‖ + 1/2 := by
          have h := mul_le_mul_of_nonneg_right h_ss1_norm
            (norm_nonneg (completedRiemannZeta₀ s))
          linarith
  -- Split on Re s:
  by_cases h_re_four : s.re ≤ 4
  · -- Case 1: Re s ∈ [1, 4]. Use Λ₀_real_bounded_one_four.
    have hΛ₀_norm : ‖completedRiemannZeta₀ s‖ ≤ M₁ := by
      have h1 : ‖completedRiemannZeta₀ s‖ ≤ Λ₀_real s.re :=
        norm_completedRiemannZeta₀_le_Λ₀_real s hs_re_half
      have h2 : Λ₀_real s.re ≤ M₁ := hM₁_bnd s.re hs_re h_re_four
      linarith
    -- ‖ξ(s)‖ ≤ ‖s‖²·M₁ + 1/2
    have h_xi_le : ‖ZD.riemannXi s‖ ≤ ‖s‖ * ‖s‖ * M₁ + 1/2 := by
      have := mul_le_mul_of_nonneg_left hΛ₀_norm
        (by positivity : (0:ℝ) ≤ ‖s‖ * ‖s‖)
      linarith
    -- log(‖ξ‖ + 1) ≤ log(‖s‖²·M₁ + 3/2) ≤ log((M₁+2)·‖s‖²) = log(M₁+2) + 2·log‖s‖
    have h_xi_plus_one : ‖ZD.riemannXi s‖ + 1 ≤ (M₁ + 2) * (‖s‖ * ‖s‖) := by
      have : (M₁ + 2) * (‖s‖ * ‖s‖) = M₁ * (‖s‖ * ‖s‖) + 2 * (‖s‖ * ‖s‖) := by ring
      have h_sq_ge : (2 : ℝ) ≤ ‖s‖ * ‖s‖ := by nlinarith
      have h_Λ_nn : 0 ≤ M₁ := hM₁_pos.le
      rw [this]
      have h_nn : 0 ≤ ‖s‖ * ‖s‖ := by positivity
      nlinarith [mul_nonneg h_Λ_nn h_nn]
    have h_xi_pos : 0 < ‖ZD.riemannXi s‖ + 1 := by
      have := norm_nonneg (ZD.riemannXi s); linarith
    have h_s_sq_pos : 0 < ‖s‖ * ‖s‖ := by positivity
    have h_M₁2_pos : 0 < M₁ + 2 := by linarith
    have h_log : Real.log (‖ZD.riemannXi s‖ + 1) ≤ Real.log ((M₁ + 2) * (‖s‖ * ‖s‖)) :=
      Real.log_le_log h_xi_pos h_xi_plus_one
    have h_log_prod : Real.log ((M₁ + 2) * (‖s‖ * ‖s‖)) = Real.log (M₁ + 2) + 2 * Real.log ‖s‖ := by
      rw [Real.log_mul h_M₁2_pos.ne' (by positivity : ‖s‖ * ‖s‖ ≠ 0)]
      rw [show ‖s‖ * ‖s‖ = ‖s‖ ^ 2 from by ring, Real.log_pow]
      push_cast; ring
    rw [h_log_prod] at h_log
    -- log(M₁+2) ≤ log(M₁+ζ2+3) (since ζ2 ≥ 1).
    have h_logM2 : Real.log (M₁ + 2) ≤ Real.log (M₁ + ζ2 + 3) := by
      apply Real.log_le_log (by linarith : (0:ℝ) < M₁ + 2)
      -- Need ζ2 ≥ 0 and +3 ≥ +2, so M₁ + ζ2 + 3 ≥ M₁ + 2.
      linarith
    -- Want: log(M₁+2) + 2·log‖s‖ ≤ C·‖s‖·log‖s‖.
    -- Use: log(M₁+ζ2+3) ≤ ‖s‖·log‖s‖ (since M₁+ζ2+3 ≤ ‖s‖ and log is monotone).
    -- And: 2·log‖s‖ ≤ ‖s‖·log‖s‖ (since ‖s‖ ≥ 2).
    have h_logM_le : Real.log (M₁ + ζ2 + 3) ≤ Real.log ‖s‖ :=
      Real.log_le_log (by linarith) hs_M₁
    have h_logM2_le : Real.log (M₁ + 2) ≤ Real.log ‖s‖ := le_trans h_logM2 h_logM_le
    have h_logM2_le_sl : Real.log (M₁ + 2) ≤ ‖s‖ * Real.log ‖s‖ := by
      calc Real.log (M₁ + 2) ≤ Real.log ‖s‖ := h_logM2_le
        _ = 1 * Real.log ‖s‖ := by ring
        _ ≤ ‖s‖ * Real.log ‖s‖ := mul_le_mul_of_nonneg_right hs_one hs_log_nn
    have h_2log : 2 * Real.log ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
      have h_s_two : (2 : ℝ) ≤ ‖s‖ := by linarith
      exact mul_le_mul_of_nonneg_right h_s_two hs_log_nn
    have h_sum : Real.log (M₁ + 2) + 2 * Real.log ‖s‖ ≤ 2 * (‖s‖ * Real.log ‖s‖) := by
      linarith
    have h_two_le_C : (2 : ℝ) ≤ C := by show 2 ≤ 10 + Real.log (M₁ + ζ2 + 3); linarith
    have h_final : 2 * (‖s‖ * Real.log ‖s‖) ≤ C * ‖s‖ * Real.log ‖s‖ := by
      have h_step := mul_le_mul_of_nonneg_right h_two_le_C h_s_log_nn
      nlinarith [h_step]
    linarith
  · -- Case 2: Re s ≥ 4. Use classical formula bound.
    push_neg at h_re_four
    have hs_re_ge_4 : 4 ≤ s.re := h_re_four.le
    have hΛ₀_norm : ‖completedRiemannZeta₀ s‖ ≤
        Real.Gamma (s.re/2) * ζ2 + 2 := by
      have h1 : ‖completedRiemannZeta₀ s‖ ≤ Λ₀_real s.re :=
        norm_completedRiemannZeta₀_le_Λ₀_real s hs_re_half
      have h2 : Λ₀_real s.re = ‖completedRiemannZeta₀ (s.re : ℂ)‖ :=
        Λ₀_real_eq_norm s.re hs_re_half
      have h3 : ‖completedRiemannZeta₀ (s.re : ℂ)‖ ≤ Real.Gamma (s.re/2) * ζ2 + 2 :=
        norm_completedRiemannZeta₀_real_le_of_four_le s.re hs_re_ge_4
      linarith
    -- ‖ξ(s)‖ ≤ ‖s‖² · (Γ(Re s/2)·ζ2 + 2) + 1/2
    have h_Γ_pos : 0 < Real.Gamma (s.re/2) := Real.Gamma_pos_of_pos (by linarith)
    have h_bound_pos : 0 < Real.Gamma (s.re/2) * ζ2 + 2 := by
      have : 0 ≤ Real.Gamma (s.re/2) * ζ2 := mul_nonneg h_Γ_pos.le hζ2_nn
      linarith
    have h_xi_le : ‖ZD.riemannXi s‖ ≤
        ‖s‖ * ‖s‖ * (Real.Gamma (s.re/2) * ζ2 + 2) + 1/2 := by
      have := mul_le_mul_of_nonneg_left hΛ₀_norm
        (by positivity : (0:ℝ) ≤ ‖s‖ * ‖s‖)
      linarith
    -- ‖ξ(s)‖ + 1 ≤ ‖s‖² · (Γ(Re s/2)·ζ2 + 3)
    have h_xi_plus_one :
        ‖ZD.riemannXi s‖ + 1 ≤ ‖s‖ * ‖s‖ * (Real.Gamma (s.re/2) * ζ2 + 3) := by
      have h_nn : 0 ≤ ‖s‖ * ‖s‖ := by positivity
      have h_sq_ge : (2 : ℝ) ≤ ‖s‖ * ‖s‖ := by nlinarith
      have h_prod_nn : 0 ≤ Real.Gamma (s.re/2) * ζ2 := mul_nonneg h_Γ_pos.le hζ2_nn
      nlinarith
    have h_ex : 0 < Real.Gamma (s.re/2) * ζ2 + 3 := by linarith
    have h_xi_pos : 0 < ‖ZD.riemannXi s‖ + 1 := by
      have := norm_nonneg (ZD.riemannXi s); linarith
    have h_s_sq_pos : 0 < ‖s‖ * ‖s‖ := by positivity
    have h_log : Real.log (‖ZD.riemannXi s‖ + 1) ≤
        Real.log (‖s‖ * ‖s‖ * (Real.Gamma (s.re/2) * ζ2 + 3)) :=
      Real.log_le_log h_xi_pos h_xi_plus_one
    -- Decompose the log of the product.
    have h_log_prod : Real.log (‖s‖ * ‖s‖ * (Real.Gamma (s.re/2) * ζ2 + 3)) =
        2 * Real.log ‖s‖ + Real.log (Real.Gamma (s.re/2) * ζ2 + 3) := by
      rw [Real.log_mul (by positivity : ‖s‖ * ‖s‖ ≠ 0) h_ex.ne']
      rw [show ‖s‖ * ‖s‖ = ‖s‖ ^ 2 from by ring, Real.log_pow]
      push_cast; ring
    rw [h_log_prod] at h_log
    -- Bound log(Γ(Re s/2)·ζ2 + 3).
    -- Γ(Re s/2)·ζ2 + 3 ≤ Γ(Re s/2)·(ζ2 + 3) when Γ(Re s/2) ≥ 1.
    -- For Re s ≥ 4, Γ(Re s/2) ≥ Γ(2) = 1.
    have h_Γ_ge_one : 1 ≤ Real.Gamma (s.re/2) := by
      have h1 : Real.Gamma 2 = 1 := by
        have : Real.Gamma ((1 : ℕ) + 1) = (1 : ℕ).factorial := Real.Gamma_nat_eq_factorial _
        simp at this
        convert this using 2; norm_num
      have h2 : (2 : ℝ) ≤ s.re/2 := by linarith
      by_cases h_eq : s.re/2 = 2
      · rw [h_eq, h1]
      · have h_mono := Real.Gamma_strictMonoOn_Ici
        have : Real.Gamma 2 ≤ Real.Gamma (s.re/2) :=
          h_mono.monotoneOn (by norm_num : (2:ℝ) ∈ Set.Ici (2:ℝ)) h2 h2
        rw [h1] at this; exact this
    have h_prod_ge_one : 1 ≤ Real.Gamma (s.re/2) * ζ2 + 3 := by
      have : 0 ≤ Real.Gamma (s.re/2) * ζ2 := mul_nonneg h_Γ_pos.le hζ2_nn
      linarith
    -- log(Γ·ζ2 + 3) ≤ log(Γ · (ζ2 + 3)) = log Γ + log(ζ2 + 3).
    have h_sum_le_prod : Real.Gamma (s.re/2) * ζ2 + 3 ≤ Real.Gamma (s.re/2) * (ζ2 + 3) := by
      have h_Γ_ge_1 : 1 ≤ Real.Gamma (s.re/2) := h_Γ_ge_one
      have hΓζ_nn : 0 ≤ Real.Gamma (s.re/2) * ζ2 := mul_nonneg h_Γ_pos.le hζ2_nn
      have h_expand : Real.Gamma (s.re/2) * (ζ2 + 3) =
          Real.Gamma (s.re/2) * ζ2 + 3 * Real.Gamma (s.re/2) := by ring
      have h_3Γ_ge_3 : 3 ≤ 3 * Real.Gamma (s.re/2) := by
        have := mul_le_mul_of_nonneg_left h_Γ_ge_1 (by norm_num : (0:ℝ) ≤ 3)
        linarith
      rw [h_expand]; linarith
    have h_log_split : Real.log (Real.Gamma (s.re/2) * ζ2 + 3) ≤
        Real.log (Real.Gamma (s.re/2)) + Real.log (ζ2 + 3) := by
      have h_lhs_pos : 0 < Real.Gamma (s.re/2) * ζ2 + 3 := h_ex
      have h_lhs_le := Real.log_le_log h_lhs_pos h_sum_le_prod
      rw [Real.log_mul h_Γ_pos.ne' (by linarith : ζ2 + 3 ≠ 0)] at h_lhs_le
      exact h_lhs_le
    -- Bound log Γ(Re s/2) ≤ (Re s + 2) · log(Re s + 2).
    have h_logΓ : Real.log (Real.Gamma (s.re/2)) ≤ (s.re + 2) * Real.log (s.re + 2) :=
      log_gamma_half_le s.re hs_re_ge_4
    -- (Re s + 2) ≤ 2‖s‖ (since Re s ≤ ‖s‖ and ‖s‖ ≥ 10 > 2).
    have h_s_p2_le : s.re + 2 ≤ 2 * ‖s‖ := by linarith
    have h_s_p2_pos : 0 < s.re + 2 := by linarith
    -- log(Re s + 2) ≤ log(2‖s‖) = log 2 + log ‖s‖ ≤ 2 · log ‖s‖ (for ‖s‖ ≥ 2).
    have h_log_sp2 : Real.log (s.re + 2) ≤ 2 * Real.log ‖s‖ := by
      have h1 : Real.log (s.re + 2) ≤ Real.log (2 * ‖s‖) :=
        Real.log_le_log h_s_p2_pos h_s_p2_le
      have h2 : Real.log (2 * ‖s‖) = Real.log 2 + Real.log ‖s‖ :=
        Real.log_mul (by norm_num) (by positivity)
      have h3 : Real.log 2 ≤ Real.log ‖s‖ :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
    have h_sp2_nn : 0 ≤ s.re + 2 := h_s_p2_pos.le
    have h_log_sp2_nn : 0 ≤ Real.log (s.re + 2) := by
      apply Real.log_nonneg; linarith
    have h_logΓ_bnd : Real.log (Real.Gamma (s.re/2)) ≤ 4 * (‖s‖ * Real.log ‖s‖) := by
      calc Real.log (Real.Gamma (s.re/2))
          ≤ (s.re + 2) * Real.log (s.re + 2) := h_logΓ
        _ ≤ (2 * ‖s‖) * Real.log (s.re + 2) :=
            mul_le_mul_of_nonneg_right h_s_p2_le h_log_sp2_nn
        _ ≤ (2 * ‖s‖) * (2 * Real.log ‖s‖) :=
            mul_le_mul_of_nonneg_left h_log_sp2 (by linarith)
        _ = 4 * (‖s‖ * Real.log ‖s‖) := by ring
    -- log(ζ2 + 3) ≤ log(M₁+ζ2+3) ≤ log‖s‖ ≤ ‖s‖·log‖s‖.
    have h_ζ2p3 : Real.log (ζ2 + 3) ≤ Real.log (M₁ + ζ2 + 3) := by
      apply Real.log_le_log (by linarith : (0:ℝ) < ζ2 + 3)
      linarith
    have h_logM_le : Real.log (M₁ + ζ2 + 3) ≤ Real.log ‖s‖ :=
      Real.log_le_log (by linarith) hs_M₁
    have h_ζ2_log_le : Real.log (ζ2 + 3) ≤ ‖s‖ * Real.log ‖s‖ := by
      calc Real.log (ζ2 + 3) ≤ Real.log (M₁ + ζ2 + 3) := h_ζ2p3
        _ ≤ Real.log ‖s‖ := h_logM_le
        _ = 1 * Real.log ‖s‖ := by ring
        _ ≤ ‖s‖ * Real.log ‖s‖ := mul_le_mul_of_nonneg_right hs_one hs_log_nn
    -- 2·log‖s‖ ≤ ‖s‖·log‖s‖.
    have h_2log : 2 * Real.log ‖s‖ ≤ ‖s‖ * Real.log ‖s‖ := by
      have : (2 : ℝ) ≤ ‖s‖ := by linarith
      exact mul_le_mul_of_nonneg_right this hs_log_nn
    -- Combine:
    -- 2·log‖s‖ + log(Γ·ζ2+3) ≤ 2·log‖s‖ + log Γ + log(ζ2+3)
    --                          ≤ ‖s‖·log‖s‖ + 4·‖s‖·log‖s‖ + ‖s‖·log‖s‖
    --                          = 6·‖s‖·log‖s‖ ≤ C·‖s‖·log‖s‖
    have h_combined : 2 * Real.log ‖s‖ + Real.log (Real.Gamma (s.re/2) * ζ2 + 3) ≤
        6 * (‖s‖ * Real.log ‖s‖) := by
      have := h_log_split
      linarith
    have h_six_le_C : (6 : ℝ) ≤ C := by show 6 ≤ 10 + Real.log (M₁ + ζ2 + 3); linarith
    have h_final : 6 * (‖s‖ * Real.log ‖s‖) ≤ C * ‖s‖ * Real.log ‖s‖ := by
      have := mul_le_mul_of_nonneg_right h_six_le_C h_s_log_nn
      calc 6 * (‖s‖ * Real.log ‖s‖)
          ≤ C * (‖s‖ * Real.log ‖s‖) := this
        _ = C * ‖s‖ * Real.log ‖s‖ := by ring
    linarith

/-- **Step 1c** — bound on ξ in the left half-plane `Re s ≤ 0` via FE.
Uses `riemannXi_one_sub` and routes through 1b. Proved from 1b. -/
theorem xi_bound_left_halfplane :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ s : ℂ, R₀ ≤ ‖s‖ → s.re ≤ 0 →
      Real.log (‖ZD.riemannXi s‖ + 1) ≤ C * ‖s‖ * Real.log ‖s‖ := by
  obtain ⟨C₂, hC₂, R₂, hR₂, hBound₂⟩ := xi_bound_right_halfplane
  -- Take C = 4·C₂, R₀ = max (R₂ + 1) 2 so ‖1-s‖ ≥ R₂ and log ‖s‖ ≥ log 2
  refine ⟨4 * C₂, by positivity, max (R₂ + 1) 2, by positivity, ?_⟩
  intro s hs hs_re
  have hs_R₂ : R₂ + 1 ≤ ‖s‖ := le_trans (le_max_left _ _) hs
  have hs_two : (2 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) hs
  have hs_pos : (0 : ℝ) < ‖s‖ := lt_of_lt_of_le (by norm_num) hs_two
  have hs_one : (1 : ℝ) ≤ ‖s‖ := le_trans (by norm_num) hs_two
  -- Let s' := 1 - s, route through step 1b
  have hFE : ZD.riemannXi s = ZD.riemannXi (1 - s) := (riemannXi_one_sub s).symm
  have hs'_re : 1 ≤ (1 - s).re := by simp; linarith
  have hs'_norm_upper : ‖1 - s‖ ≤ 2 * ‖s‖ := by
    calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
      _ ≤ 1 + ‖s‖ := by simp
      _ ≤ ‖s‖ + ‖s‖ := by linarith
      _ = 2 * ‖s‖ := by ring
  have hs'_norm_lower : R₂ ≤ ‖1 - s‖ := by
    have := norm_sub_norm_le (1 : ℂ) s
    simp at this
    -- |‖1‖ - ‖s‖| ≤ ‖1 - s‖ ⇒ ‖s‖ - 1 ≤ ‖1 - s‖
    have hRev : ‖s‖ - 1 ≤ ‖1 - s‖ := by
      have h := norm_sub_norm_le s 1
      rw [show s - 1 = -(1 - s) by ring, norm_neg] at h
      simpa using h
    linarith
  have hs'_one : (1 : ℝ) ≤ ‖1 - s‖ := by
    have hRev : ‖s‖ - 1 ≤ ‖1 - s‖ := by
      have h := norm_sub_norm_le s 1
      rw [show s - 1 = -(1 - s) by ring, norm_neg] at h
      simpa using h
    linarith
  have hs'_pos : (0 : ℝ) < ‖1 - s‖ := lt_of_lt_of_le one_pos hs'_one
  have hs'_log_upper : Real.log ‖1 - s‖ ≤ 2 * Real.log ‖s‖ := by
    have h1 : Real.log ‖1 - s‖ ≤ Real.log (2 * ‖s‖) :=
      Real.log_le_log hs'_pos hs'_norm_upper
    have h2 : Real.log (2 * ‖s‖) = Real.log 2 + Real.log ‖s‖ :=
      Real.log_mul (by norm_num) hs_pos.ne'
    have h3 : Real.log 2 ≤ Real.log ‖s‖ :=
      Real.log_le_log (by norm_num) hs_two
    linarith
  have hs'_log_nn : 0 ≤ Real.log ‖1 - s‖ := Real.log_nonneg hs'_one
  have hs_log_nn : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hs_one
  have hBound' := hBound₂ (1 - s) hs'_norm_lower hs'_re
  rw [hFE]
  calc Real.log (‖ZD.riemannXi (1 - s)‖ + 1)
      ≤ C₂ * ‖1 - s‖ * Real.log ‖1 - s‖ := hBound'
    _ ≤ C₂ * (2 * ‖s‖) * (2 * Real.log ‖s‖) := by
        apply mul_le_mul _ hs'_log_upper hs'_log_nn (by positivity)
        exact mul_le_mul_of_nonneg_left hs'_norm_upper hC₂.le
    _ = 4 * C₂ * ‖s‖ * Real.log ‖s‖ := by ring

/-- **Step 1 — Order-1 upper bound for ξ on large disks.** On `‖s‖ ≤ R`
for `R` large, `log‖ξ(s)‖ ≤ C · R · log R`, assuming ζ has subexponential
growth in the critical strip (the PL output).

Assembly: case split on `s.re` using steps 1a, 1b, 1c. Each sub-bound
is of the form `C · ‖s‖ · log ‖s‖`, which is `≤ C · R · log R` on the
disk `‖s‖ ≤ R` (log monotone for `‖s‖ ≥ 1`). -/
theorem xi_order_one_log_bound :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R, R₀ ≤ R →
      ∀ s : ℂ, ‖s‖ ≤ R →
        Real.log (‖ZD.riemannXi s‖ + 1) ≤ C * R * Real.log R := by
  obtain ⟨C1, hC1, R1, hR1, hBound1⟩ := xi_bound_in_strip
  obtain ⟨C2, hC2, R2, hR2, hBound2⟩ := xi_bound_right_halfplane
  obtain ⟨C3, hC3, R3, hR3, hBound3⟩ := xi_bound_left_halfplane
  -- Threshold R_max ≥ max(R1, R2, R3, e) so sub-bounds apply for ‖s‖ ≥ R_max
  -- and R · log R ≥ 1 for R ≥ R_max.
  set R_max := max (max R1 R2) (max R3 (Real.exp 1)) with hR_max_def
  have hR_max_pos : 0 < R_max := by
    apply lt_max_of_lt_right
    exact lt_max_of_lt_right (Real.exp_pos 1)
  obtain ⟨M, hM_nn, hM⟩ := riemannXi_bounded_on_closedBall R_max
  have hlogM_nn : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith)
  -- C = max of sub-constants and log(M+1) + 1 (so C ≥ log(M+1) and C > 0).
  set C := max (max (max C1 C2) C3) (Real.log (M + 1) + 1) with hC_def
  have hC_ge_C1 : C1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC_ge_C2 : C2 ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC_ge_C3 : C3 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC_ge_logM : Real.log (M + 1) + 1 ≤ C := le_max_right _ _
  have hC_pos : 0 < C := lt_of_lt_of_le (by linarith) hC_ge_C1
  refine ⟨C, hC_pos, R_max, hR_max_pos, ?_⟩
  intro R hR s hs
  -- R ≥ R_max ≥ e, so log R ≥ 1 and R ≥ e ≥ 1
  have hR_exp : Real.exp 1 ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hR_one : (1 : ℝ) ≤ R := le_trans (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1) hR_exp
  have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR_one
  have hR_log_ge_1 : (1 : ℝ) ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 1) hR_exp
    rwa [Real.log_exp] at this
  have hR_log_nn : 0 ≤ Real.log R := le_trans zero_le_one hR_log_ge_1
  -- `C * R * log R ≥ log(M + 1)` since C ≥ log(M+1)+1 ≥ log(M+1), R≥1, logR≥1
  have hC_bound_M : Real.log (M + 1) ≤ C * R * Real.log R := by
    calc Real.log (M + 1)
        ≤ Real.log (M + 1) + 1 := by linarith
      _ ≤ C := hC_ge_logM
      _ = C * 1 * 1 := by ring
      _ ≤ C * R * Real.log R := by
          apply mul_le_mul _ hR_log_ge_1 zero_le_one (by positivity)
          exact mul_le_mul_of_nonneg_left hR_one hC_pos.le
  -- Case: ‖s‖ ≤ R_max (compact region)
  by_cases h_small : ‖s‖ ≤ R_max
  · have hs_in : s ∈ Metric.closedBall (0 : ℂ) R_max := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact h_small
    have hξ_bound : ‖ZD.riemannXi s‖ ≤ M := hM s hs_in
    have h1 : Real.log (‖ZD.riemannXi s‖ + 1) ≤ Real.log (M + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    exact le_trans h1 hC_bound_M
  -- Case: ‖s‖ > R_max (tail region) — use sub-bounds by Re s
  · push_neg at h_small
    have hs_nn : 0 < ‖s‖ := lt_trans hR_max_pos h_small
    have hs_one : (1 : ℝ) ≤ ‖s‖ := by
      have : Real.exp 1 ≤ ‖s‖ :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h_small.le
      exact le_trans (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1) this
    have hs_log_nn : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hs_one
    -- `‖s‖ * log ‖s‖ ≤ R * log R` from monotonicity
    have hmono : ‖s‖ * Real.log ‖s‖ ≤ R * Real.log R := by
      have hlog_le : Real.log ‖s‖ ≤ Real.log R :=
        Real.log_le_log hs_nn hs
      calc ‖s‖ * Real.log ‖s‖
          ≤ ‖s‖ * Real.log R := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hs_nn)
        _ ≤ R * Real.log R := mul_le_mul_of_nonneg_right hs hR_log_nn
    -- Sub-bound thresholds
    have hs_R1 : R1 ≤ ‖s‖ :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h_small.le
    have hs_R2 : R2 ≤ ‖s‖ :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h_small.le
    have hs_R3 : R3 ≤ ‖s‖ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h_small.le
    -- Case split on Re s
    rcases le_or_gt s.re 0 with hre_neg | hre_pos
    · -- Re s ≤ 0 : step 1c
      have hb := hBound3 s hs_R3 hre_neg
      calc Real.log (‖ZD.riemannXi s‖ + 1)
          ≤ C3 * ‖s‖ * Real.log ‖s‖ := hb
        _ ≤ C * ‖s‖ * Real.log ‖s‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC_ge_C3 (le_of_lt hs_nn)) hs_log_nn
        _ ≤ C * (R * Real.log R) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hmono hC_pos.le
        _ = C * R * Real.log R := by ring
    · rcases le_or_gt s.re 1 with hre_le1 | hre_gt1
      · -- 0 < Re s ≤ 1 : step 1a
        have hb := hBound1 s hs_R1 (le_of_lt hre_pos) hre_le1
        calc Real.log (‖ZD.riemannXi s‖ + 1)
            ≤ C1 * ‖s‖ * Real.log ‖s‖ := hb
          _ ≤ C * ‖s‖ * Real.log ‖s‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hC_ge_C1 (le_of_lt hs_nn)) hs_log_nn
          _ ≤ C * (R * Real.log R) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left hmono hC_pos.le
          _ = C * R * Real.log R := by ring
      · -- Re s > 1 : step 1b
        have hb := hBound2 s hs_R2 (le_of_lt hre_gt1)
        calc Real.log (‖ZD.riemannXi s‖ + 1)
            ≤ C2 * ‖s‖ * Real.log ‖s‖ := hb
          _ ≤ C * ‖s‖ * Real.log ‖s‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hC_ge_C2 (le_of_lt hs_nn)) hs_log_nn
          _ ≤ C * (R * Real.log R) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left hmono hC_pos.le
          _ = C * R * Real.log R := by ring

/-- **Step 2 — Jensen's formula at ξ.** For `R > 0`, ξ entire, `ξ(0) ≠ 0`.
Direct specialisation of Mathlib's `MeromorphicOn.circleAverage_log_norm`
(2025). The `divisor · log R + log ‖meromorphicTrailingCoeffAt‖` term
simplifies because `ξ(0) = 1/2 ≠ 0`, so the divisor at 0 is 0 and the
trailing coefficient is `ξ(0)`. -/
theorem xi_jensen_at_zero (R : ℝ) (hR : 0 < R) :
    circleAverage (fun s => Real.log ‖ZD.riemannXi s‖) 0 R
      = ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi
                (Metric.closedBall (0 : ℂ) |R|)) u *
              Real.log (R * ‖u‖⁻¹)
        + Real.log ‖ZD.riemannXi 0‖ := by
  have hR' : R ≠ 0 := hR.ne'
  have hAnal : AnalyticOnNhd ℂ ZD.riemannXi (Metric.closedBall (0 : ℂ) |R|) :=
    riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hMero : MeromorphicOn ZD.riemannXi (Metric.closedBall (0 : ℂ) |R|) :=
    hAnal.meromorphicOn
  have hJensen := MeromorphicOn.circleAverage_log_norm hR' hMero
  have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) |R| := by
    simp [Metric.closedBall, abs_of_pos hR, hR.le]
  have hξ0_analytic : AnalyticAt ℂ ZD.riemannXi 0 :=
    riemannXi_analyticOnNhd_univ 0 (Set.mem_univ _)
  have hDiv0 : (MeromorphicOn.divisor ZD.riemannXi
      (Metric.closedBall (0 : ℂ) |R|)) 0 = 0 := by
    rw [MeromorphicOn.divisor_apply hMero h0_mem]
    have hAnalOrd : analyticOrderAt ZD.riemannXi 0 = 0 := by
      rw [analyticOrderAt_eq_zero]; right; exact riemannXi_zero_ne_zero
    rw [hξ0_analytic.meromorphicOrderAt_eq, hAnalOrd]
    rfl
  have hTrail : meromorphicTrailingCoeffAt ZD.riemannXi 0 = ZD.riemannXi 0 :=
    hξ0_analytic.meromorphicTrailingCoeffAt_of_ne_zero riemannXi_zero_ne_zero
  rw [hJensen, hDiv0, hTrail]
  push_cast
  simp only [zero_sub, norm_neg]
  ring_nf

/-- **Helper — divisor ≥ 1 at ξ-zeros.** On any closed ball `CB`, if ξ(ρ) = 0 and
ρ ∈ CB, then `divisor ξ CB ρ ≥ 1`. Combines `analyticOrderAt ≠ 0` (from ξ(ρ) = 0 and
ξ analytic) with `analyticOrderAt ≠ ⊤` (from the identity theorem, via
`riemannXi_analyticOrderAt_ne_top`). -/
theorem xi_divisor_ge_one_of_zero {CB : Set ℂ} (hMero : MeromorphicOn ZD.riemannXi CB)
    (ρ : ℂ) (hρ : ρ ∈ CB) (hρ_zero : ZD.riemannXi ρ = 0) :
    (1 : ℤ) ≤ MeromorphicOn.divisor ZD.riemannXi CB ρ := by
  have hAnalρ : AnalyticAt ℂ ZD.riemannXi ρ :=
    riemannXi_analyticOnNhd_univ ρ (Set.mem_univ _)
  have hAnalOrd_ne_zero : analyticOrderAt ZD.riemannXi ρ ≠ 0 := by
    rw [analyticOrderAt_ne_zero]; exact ⟨hAnalρ, hρ_zero⟩
  have hAnalOrd_ne_top := riemannXi_analyticOrderAt_ne_top ρ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt ZD.riemannXi ρ :=
    ENat.ne_top_iff_exists.mp hAnalOrd_ne_top
  have hn_ne : n ≠ 0 := fun h => hAnalOrd_ne_zero (by rw [← hn, h]; rfl)
  have hn_ge : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_ne
  rw [MeromorphicOn.divisor_apply hMero hρ, hAnalρ.meromorphicOrderAt_eq, ← hn]
  simp
  exact hn_ge

/-- **Step 3 — Zero count in a disk.** `#{ρ : ξ(ρ) = 0, ‖ρ‖ ≤ R} ≤ C·R·log R`
for large R. Obtained from Jensen at radius `2R` + step 1:

* `xi_order_one_log_bound` gives `log(‖ξ(s)‖+1) ≤ C₁·(2R)·log(2R)` on `‖s‖ ≤ 2R`.
* Apply `circleAverage_mono_on_of_le_circle` → circleAvg bound.
* `xi_jensen_at_zero (2R)` converts to a finsum over zeros (with multiplicity).
* Each zero ρ in `B_R` has `‖ρ‖ ≤ R < 2R`, so `log(2R/‖ρ‖) ≥ log 2`.
* With `divisor ρ ≥ 1` at zeros (ξ analytic, non-vanishing at 0 ⇒ not identically 0),
  finsum over zeros in `B_R` is `≥ ncard · log 2`.
* `log(2R) ≤ 2 log R` for `R ≥ 2`.

Total: `ncard ≤ (4·C₁·R·log R + log 2) / log 2 ≤ C·R·log R`. -/
theorem xi_zero_count_disk_bound :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R, R₀ ≤ R →
      ((Metric.closedBall (0 : ℂ) R ∩ {z | ZD.riemannXi z = 0}).ncard : ℝ)
        ≤ C * R * Real.log R := by
  -- Extract step 1's pointwise bound
  obtain ⟨C₁, hC₁, R₁, hR₁, hBound⟩ := xi_order_one_log_bound
  -- Take R₀ = max R₁ 2 (so 2R ≥ 2·max(R₁, 2) ≥ R₁ and ≥ 4 for log 2 bounds)
  -- Constants: for each zero ρ in B_R with ‖ρ‖ ≤ R = 2R/2, log(2R/‖ρ‖) ≥ log 2
  -- C := something like (4·C₁ + 1) / log 2
  refine ⟨(8 * C₁ + 4) / Real.log 2, by positivity, max (max R₁ 2) (Real.exp 1),
    by positivity, ?_⟩
  intro R hR
  -- Boilerplate: R ≥ R₁, R ≥ 2, R ≥ e
  have hR_R₁ : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR_two : (2 : ℝ) ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR_e : Real.exp 1 ≤ R := le_trans (le_max_right _ _) hR
  have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR_two
  have hR_one : (1 : ℝ) ≤ R := le_trans (by norm_num) hR_two
  have hR_log_ge_1 : (1 : ℝ) ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 1) hR_e
    rwa [Real.log_exp] at this
  have hR_log_nn : 0 ≤ Real.log R := le_trans zero_le_one hR_log_ge_1
  -- Jensen + circleAverage bound + pigeonhole
  set CB : Set ℂ := Metric.closedBall (0 : ℂ) |2 * R| with hCB_def
  have h2R_pos : (0 : ℝ) < 2 * R := by linarith
  have h2R_R₁ : R₁ ≤ 2 * R := by linarith
  have habs2R : |2 * R| = 2 * R := abs_of_pos h2R_pos
  have hAnal : AnalyticOnNhd ℂ ZD.riemannXi CB :=
    riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hMero : MeromorphicOn ZD.riemannXi CB := hAnal.meromorphicOn
  -- Jensen identity at 2R
  have hJensen :
      circleAverage (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R)
        = ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                  Real.log (2 * R * ‖u‖⁻¹)
          + Real.log ‖ZD.riemannXi 0‖ :=
    xi_jensen_at_zero (2 * R) h2R_pos
  -- log ‖ξ(0)‖ = log(1/2) = -log 2
  have hlog_xi0 : Real.log ‖ZD.riemannXi 0‖ = -Real.log 2 := by
    rw [riemannXi_zero]; simp
  -- CircleAverage bound via `circleAverage_mono_on_of_le_circle` + step 1
  have hAnalSph : AnalyticOnNhd ℂ ZD.riemannXi (Metric.sphere (0 : ℂ) |2 * R|) :=
    riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hCI : CircleIntegrable (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R) :=
    circleIntegrable_log_norm_meromorphicOn hAnalSph.meromorphicOn
  have hCircAvg_le :
      circleAverage (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R) ≤
        C₁ * (2 * R) * Real.log (2 * R) := by
    apply circleAverage_mono_on_of_le_circle hCI
    intro s hs
    rw [Metric.mem_sphere, dist_zero_right, habs2R] at hs
    have h_log_le : Real.log ‖ZD.riemannXi s‖ ≤ Real.log (‖ZD.riemannXi s‖ + 1) := by
      rcases eq_or_lt_of_le (norm_nonneg (ZD.riemannXi s)) with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact Real.log_nonneg (by linarith [norm_nonneg (ZD.riemannXi s)])
      · exact Real.log_le_log hpos (by linarith)
    have h_bound_s := hBound (2 * R) h2R_R₁ s (le_of_eq hs)
    linarith
  -- Every term of the finsum is ≥ 0 (divisor ≥ 0 analytic; log(2R/‖u‖) ≥ 0 on ball)
  have hD_nn : ∀ u, 0 ≤ MeromorphicOn.divisor ZD.riemannXi CB u := by
    intro u; exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnal u
  have h_term_nn :
      ∀ u, 0 ≤ (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                Real.log (2 * R * ‖u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ CB
    · rw [hCB_def, Metric.mem_closedBall, dist_zero_right, habs2R] at hu
      by_cases hu0 : u = 0
      · simp [hu0, Real.log_zero]
      · have h_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have hlog_nn : 0 ≤ Real.log (2 * R * ‖u‖⁻¹) := by
          apply Real.log_nonneg
          rw [show (2 * R * ‖u‖⁻¹) = (2 * R) / ‖u‖ from by ring, le_div_iff₀ h_norm_pos]
          linarith
        exact mul_nonneg (by exact_mod_cast hD_nn u) hlog_nn
    · have hD0 := (MeromorphicOn.divisor ZD.riemannXi CB).apply_eq_zero_of_notMem hu
      simp [hD0]
  -- The set of zeros in closedBall 0 R is finite
  have hS_fin : (Metric.closedBall (0 : ℂ) R ∩ {z | ZD.riemannXi z = 0}).Finite :=
    riemannXi_zeros_finite_in_closedBall R
  set S : Set ℂ := Metric.closedBall (0 : ℂ) R ∩ {z | ZD.riemannXi z = 0} with hS_def
  -- S ⊆ closedBall 0 (2R) = CB
  have hS_sub_CB : S ⊆ CB := by
    intro u ⟨hu_ball, _⟩
    rw [hCB_def, Metric.mem_closedBall, dist_zero_right, habs2R]
    rw [Metric.mem_closedBall, dist_zero_right] at hu_ball
    linarith
  -- Per-element lower bound: for ρ ∈ S, (D ρ : ℝ) * log(2R/‖ρ‖) ≥ log 2
  have hS_each :
      ∀ ρ ∈ S,
        Real.log 2 ≤
          (MeromorphicOn.divisor ZD.riemannXi CB ρ : ℝ) * Real.log (2 * R * ‖ρ‖⁻¹) := by
    intro ρ hρ
    rcases hρ with ⟨hρ_ball, hρ_zero⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball
    -- ρ ≠ 0: since ξ(0) ≠ 0 and ξ(ρ) = 0
    have hρ_zero' : ZD.riemannXi ρ = 0 := hρ_zero
    have hρ_ne_zero : ρ ≠ 0 := fun h0 =>
      riemannXi_zero_ne_zero (h0 ▸ hρ_zero')
    have h_norm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne_zero
    have hρ_mem_CB : ρ ∈ CB := hS_sub_CB ⟨by rwa [Metric.mem_closedBall, dist_zero_right], hρ_zero⟩
    have hD_ge_one :
        (1 : ℤ) ≤ MeromorphicOn.divisor ZD.riemannXi CB ρ :=
      xi_divisor_ge_one_of_zero hMero ρ hρ_mem_CB hρ_zero
    -- log(2R/‖ρ‖) ≥ log 2 since ‖ρ‖ ≤ R so 2R/‖ρ‖ ≥ 2
    have h_ratio_ge_two : (2 : ℝ) ≤ 2 * R * ‖ρ‖⁻¹ := by
      rw [show (2 * R * ‖ρ‖⁻¹) = (2 * R) / ‖ρ‖ from by ring, le_div_iff₀ h_norm_pos]
      linarith
    have hlog_ge : Real.log 2 ≤ Real.log (2 * R * ‖ρ‖⁻¹) :=
      Real.log_le_log (by norm_num) h_ratio_ge_two
    -- (D ρ : ℝ) ≥ 1 so product ≥ log 2 (which is ≥ 0 so monotone mul works)
    have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hD_ge_one_R : (1 : ℝ) ≤ (MeromorphicOn.divisor ZD.riemannXi CB ρ : ℝ) := by
      exact_mod_cast hD_ge_one
    calc Real.log 2
        = 1 * Real.log 2 := by ring
      _ ≤ (MeromorphicOn.divisor ZD.riemannXi CB ρ : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hD_ge_one_R hlog2_nn
      _ ≤ (MeromorphicOn.divisor ZD.riemannXi CB ρ : ℝ) * Real.log (2 * R * ‖ρ‖⁻¹) := by
          apply mul_le_mul_of_nonneg_left hlog_ge
          linarith
  -- D.support is finite
  have h_D_fs : (MeromorphicOn.divisor ZD.riemannXi CB).support.Finite :=
    (MeromorphicOn.divisor ZD.riemannXi CB).finiteSupport (isCompact_closedBall 0 _)
  -- S ⊆ D.support (since D ρ ≥ 1 > 0 for ρ ∈ S)
  have hS_sub_Dsupp : S ⊆ (MeromorphicOn.divisor ZD.riemannXi CB).support := by
    intro ρ hρ
    rcases hρ with ⟨hρ_ball, hρ_zero⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball
    have hρ_mem_CB : ρ ∈ CB := hS_sub_CB ⟨by rwa [Metric.mem_closedBall, dist_zero_right], hρ_zero⟩
    have hD_ge_one :
        (1 : ℤ) ≤ MeromorphicOn.divisor ZD.riemannXi CB ρ :=
      xi_divisor_ge_one_of_zero hMero ρ hρ_mem_CB hρ_zero
    simp only [Function.mem_support]
    intro hD0
    rw [hD0] at hD_ge_one
    exact absurd hD_ge_one (by norm_num)
  -- Express finsum as sum over D.support
  have h_finsum_eq :
      (∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                Real.log (2 * R * ‖u‖⁻¹)) =
        ∑ u ∈ h_D_fs.toFinset,
          (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) * Real.log (2 * R * ‖u‖⁻¹) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro hD0
    apply hu
    rw [hD0]; simp
  -- S.toFinset ⊆ D.support.toFinset
  have h_sub_fs : hS_fin.toFinset ⊆ h_D_fs.toFinset := by
    intro u hu
    simp only [Set.Finite.mem_toFinset] at hu ⊢
    exact hS_sub_Dsupp hu
  -- ncard(S) · log 2 ≤ finsum
  have h_lower :
      (S.ncard : ℝ) * Real.log 2 ≤
        ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                Real.log (2 * R * ‖u‖⁻¹) := by
    rw [Set.ncard_eq_toFinset_card S hS_fin, h_finsum_eq]
    calc (hS_fin.toFinset.card : ℝ) * Real.log 2
        = ∑ u ∈ hS_fin.toFinset, Real.log 2 := by rw [Finset.sum_const]; ring
      _ ≤ ∑ u ∈ hS_fin.toFinset,
            (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
              Real.log (2 * R * ‖u‖⁻¹) := by
          apply Finset.sum_le_sum
          intro u hu
          simp only [Set.Finite.mem_toFinset] at hu
          exact hS_each u hu
      _ ≤ ∑ u ∈ h_D_fs.toFinset,
            (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
              Real.log (2 * R * ‖u‖⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_sub_fs
          intros u _ _; exact h_term_nn _
  -- Combine: ncard · log 2 ≤ finsum = circleAverage - log‖ξ(0)‖ = circleAverage + log 2
  --   ≤ C₁ · 2R · log(2R) + log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_upper_finsum :
      ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
              Real.log (2 * R * ‖u‖⁻¹)
        ≤ C₁ * (2 * R) * Real.log (2 * R) + Real.log 2 := by
    have h_eq_rearrange :
        ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                Real.log (2 * R * ‖u‖⁻¹)
          = circleAverage (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R)
              - Real.log ‖ZD.riemannXi 0‖ := by
      rw [hJensen]; ring
    rw [h_eq_rearrange, hlog_xi0]
    linarith
  have h_main_ineq : (S.ncard : ℝ) * Real.log 2 ≤
      C₁ * (2 * R) * Real.log (2 * R) + Real.log 2 := le_trans h_lower h_upper_finsum
  -- Divide by log 2 and bound log(2R) ≤ 2 log R for R ≥ 2
  have h_log2R_le : Real.log (2 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR_pos.ne']
    -- log 2 ≤ log R (since 2 ≤ R)
    have : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR_two
    linarith
  -- C₁ · 2R · log(2R) ≤ C₁ · 2R · 2 log R = 4 C₁ R log R
  have hC12R_nn : 0 ≤ C₁ * (2 * R) := by positivity
  have h_bound_2 : C₁ * (2 * R) * Real.log (2 * R) ≤ 4 * C₁ * R * Real.log R := by
    calc C₁ * (2 * R) * Real.log (2 * R)
        ≤ C₁ * (2 * R) * (2 * Real.log R) := by
          apply mul_le_mul_of_nonneg_left h_log2R_le hC12R_nn
      _ = 4 * C₁ * R * Real.log R := by ring
  -- ncard ≤ (4 C₁ R log R + log 2) / log 2
  have h_divide : (S.ncard : ℝ) ≤ (4 * C₁ * R * Real.log R + Real.log 2) / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    linarith
  -- Final arithmetic: (4 C₁ R log R + log 2) / log 2 ≤ (8 C₁ + 4) / log 2 · R · log R
  -- since log 2 ≤ 4 · R · log R (because R · log R ≥ e ≥ 2 > log 2 / 4).
  have hR_logR : (1 : ℝ) ≤ R * Real.log R := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ R * Real.log R := mul_le_mul hR_one hR_log_ge_1 zero_le_one (by linarith)
  have hlog2_le_4RlogR : Real.log 2 ≤ 4 * R * Real.log R := by
    have h : Real.log 2 ≤ 1 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2) |>.trans (by norm_num)
    linarith
  -- (4 C₁ R log R + log 2) / log 2 ≤ ((4 C₁ + 4) R log R) / log 2 + (wait, we need ≤)
  -- Better: (4 C₁ R log R + log 2) ≤ (4 C₁ + 4) R log R ≤ (8 C₁ + 4) R log R
  -- From hlog2_le_4RlogR: log 2 ≤ 4 R log R so 4 C₁ R log R + log 2 ≤ (4 C₁ + 4) R log R.
  -- Then (4 C₁ + 4) ≤ (8 C₁ + 4) since C₁ > 0.
  have h_num_le :
      4 * C₁ * R * Real.log R + Real.log 2 ≤ (8 * C₁ + 4) * R * Real.log R := by
    have h1 : 4 * C₁ * R * Real.log R + Real.log 2 ≤
        4 * C₁ * R * Real.log R + 4 * R * Real.log R := by linarith
    have h2 : 4 * C₁ * R * Real.log R + 4 * R * Real.log R =
        (4 * C₁ + 4) * R * Real.log R := by ring
    have h3 : (4 * C₁ + 4) * R * Real.log R ≤ (8 * C₁ + 4) * R * Real.log R := by
      apply mul_le_mul_of_nonneg_right _ hR_log_nn
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hR_pos)
      linarith
    linarith
  -- Divide: (8 C₁ + 4) R log R / log 2 = (8 C₁ + 4) / log 2 · R · log R
  have h_final :
      (4 * C₁ * R * Real.log R + Real.log 2) / Real.log 2 ≤
        (8 * C₁ + 4) / Real.log 2 * R * Real.log R := by
    rw [div_le_iff₀ hlog2_pos]
    have : (8 * C₁ + 4) / Real.log 2 * R * Real.log R * Real.log 2 =
        (8 * C₁ + 4) * R * Real.log R := by
      field_simp
    rw [this]
    exact h_num_le
  exact le_trans h_divide h_final

/-- **Step 4 — Target: `∑ 1/|ρ|² < ∞` over nontrivial zeros.** Dyadic
partition of the disk: at each shell `2^k ≤ ‖ρ‖ ≤ 2^{k+1}`, count is
`O(2^{k+1} · (k+1))` by Step 3, and `1/‖ρ‖² ≤ 4^{-k}`. Geometric series
closes. -/
theorem nontrivialZeros_inv_sq_summable :
    nontrivialZeros_inv_sq_summable_target := by
  unfold nontrivialZeros_inv_sq_summable_target
  -- Majorant: for ρ with ‖ρ‖ ≥ 2, f ρ ≤ 4/‖ρ‖^4 via normSq_rho_times_rho_sub_one_ge.
  -- For ρ with ‖ρ‖ < 2, finite (from NontrivialZeros_inter_closedBall_finite 2).
  apply Summable.of_norm_bounded_eventually
    (g := fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => 4 / ‖ρ.val‖ ^ 4)
  · -- Summable of 4/‖ρ.val‖^4 over NTZ_sub via three-way split:
    -- (lo) ‖ρ‖ < 2: absorbed into M_lo.
    -- (mid) 2 ≤ ‖ρ‖ < 2^(N+1): absorbed into M_mid, where N = ⌈log₂ R₀⌉
    --   with R₀ from step 3.
    -- (hi) ‖ρ‖ ≥ 2^(N+1): dyadic shells k ≥ N, shell contribution ≤
    --   (8·C·log 2) · (k+1)/8^k; geometric series converges.
    obtain ⟨C₃, hC₃, R₀_step3, hR₀_step3, hBound_step3⟩ := xi_zero_count_disk_bound
    -- Choose N : ℕ with 2^N ≥ max R₀_step3 2.
    -- Use Nat.ceil: N_ceil := ⌈log₂ (max R₀_step3 2)⌉.toNat, then 2^N_ceil ≥ max R₀_step3 2.
    set R_th : ℝ := max R₀_step3 2 with hRth_def
    have hRth_pos : 0 < R_th := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hRth_ge_two : (2 : ℝ) ≤ R_th := le_max_right _ _
    have hRth_ge_R₀ : R₀_step3 ≤ R_th := le_max_left _ _
    -- N such that 2^N ≥ R_th.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, R_th ≤ (2 : ℝ) ^ N := by
      rcases pow_unbounded_of_one_lt R_th (by norm_num : (1:ℝ) < 2) with ⟨N, hN⟩
      exact ⟨N, le_of_lt hN⟩
    set M_lo : ℝ :=
      (NontrivialZeros_inter_closedBall_finite 2).toFinset.sum
        (fun ρ => 4 / ‖ρ‖ ^ 4) with hM_lo_def
    -- Middle: sum over zeros with 2 ≤ ‖ρ‖ < 2^(N+1). Absorb into M_mid.
    set M_mid : ℝ :=
      (NontrivialZeros_inter_closedBall_finite ((2 : ℝ) ^ (N + 1))).toFinset.sum
        (fun ρ => 4 / ‖ρ‖ ^ 4) with hM_mid_def
    -- Tail constant
    set C_tail : ℝ := 8 * C₃ * Real.log 2 with hC_tail_def
    refine summable_of_sum_le
      (fun ρ => div_nonneg (by norm_num) (by positivity))
      (c := M_lo + M_mid + C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 8 ^ k) ?_
    intro u
    -- Split u into: ‖ρ‖ < 2, 2 ≤ ‖ρ‖ < 2^(N+1), ‖ρ‖ ≥ 2^(N+1).
    rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.val‖ < 2)]
    have h_lo_bound :
        (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2), 4 / ‖ρ.val‖ ^ 4) ≤ M_lo := by
      rw [hM_lo_def]
      -- Sum over u.filter (subtype) equals sum over its image under Subtype.val
      -- (injective), which is a subset of NTZ_inter_B_2's toFinset.
      rw [show (∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2), (4 : ℝ) / ‖ρ.val‖ ^ 4) =
          ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.val‖ < 2)).image Subtype.val,
              (4 : ℝ) / ‖ρ‖ ^ 4 from ?_]
      swap
      · rw [Finset.sum_image]
        intro x _ y _ h
        exact Subtype.val_injective h
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
    -- Split the ‖ρ‖ ≥ 2 part further by 2^(N+1).
    rw [← Finset.sum_filter_add_sum_filter_not (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2))
      (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1))]
    have h_mid_bound :
        (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
              (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
          4 / ‖ρ.val‖ ^ 4) ≤ M_mid := by
      rw [hM_mid_def]
      rw [show
          (∑ ρ ∈ (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
              (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)),
              (4 : ℝ) / ‖ρ.val‖ ^ 4) =
          ∑ ρ ∈ ((u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
              (fun ρ => ‖ρ.val‖ < (2 : ℝ) ^ (N + 1))).image Subtype.val,
              (4 : ℝ) / ‖ρ‖ ^ 4 from ?_]
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
          4 / ‖ρ.val‖ ^ 4)
        ≤ C_tail * ∑' k : ℕ, (↑k + 1 : ℝ) / 8 ^ k := by
      -- Dyadic partition by shell k : ρ.val is in the shell [2^k, 2^(k+1)) for
      -- k := ⌊log₂ ‖ρ.val‖⌋, necessarily k ≥ N+1. Per-element 4/‖ρ.val‖^4 ≤ 4/2^(4k).
      -- The total number in the k-th shell is ≤ ncard(B_{2^(k+1)} ∩ {ξ=0}) ≤
      -- C₃ · 2^(k+1) · log(2^(k+1)) = 2·C₃·2^k·(k+1)·log 2.
      -- Shell contribution ≤ 2·C₃·2^k·(k+1)·log 2 · 4/2^(4k) = 8·C₃·log 2 · (k+1)/8^k.
      -- Sum is ≤ 8·C₃·log 2 · ∑' k, (k+1)/8^k = C_tail · ∑'.
      set S : Finset {ρ : ℂ // ρ ∈ NontrivialZeros} :=
        (u.filter (fun ρ => ¬ ‖ρ.val‖ < 2)).filter
          (fun ρ => ¬ ‖ρ.val‖ < (2 : ℝ) ^ (N + 1)) with hS_def
      -- Each ρ ∈ S has ‖ρ.val‖ ≥ 2^(N+1) ≥ 2 ≥ 1, so k(ρ) defined.
      have h_mem : ∀ ρ ∈ S, (2 : ℝ) ^ (N + 1) ≤ ‖ρ.val‖ := by
        intro ρ hρ
        simp only [hS_def, Finset.mem_filter, not_lt] at hρ
        exact hρ.2
      have h_one_le : ∀ ρ ∈ S, (1 : ℝ) ≤ ‖ρ.val‖ := by
        intro ρ hρ
        have hle := h_mem ρ hρ
        have h2N1_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
        linarith
      -- k(ρ) via exists_nat_pow_near
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
      -- Per-element bound
      have h_per_elem :
          ∀ ρ ∈ S, (4 : ℝ) / ‖ρ.val‖ ^ 4 ≤ 4 / (2 : ℝ) ^ (4 * kf ρ) := by
        intro ρ hρ
        have ⟨h_pow_le, _⟩ := h_kf_prop ρ hρ
        have h_one := h_one_le ρ hρ
        have h_pos : (0 : ℝ) < ‖ρ.val‖ := by linarith
        have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ kf ρ := pow_pos (by norm_num) _
        have h_pow4_pos : (0 : ℝ) < (2 : ℝ) ^ (4 * kf ρ) := pow_pos (by norm_num) _
        have h_rho_pow4_pos : (0 : ℝ) < ‖ρ.val‖ ^ 4 := by positivity
        have h_pow4_le : (2 : ℝ) ^ (4 * kf ρ) ≤ ‖ρ.val‖ ^ 4 := by
          rw [show (4 * kf ρ) = (kf ρ) * 4 from by ring, pow_mul]
          exact pow_le_pow_left₀ h_pow_pos.le h_pow_le 4
        rw [div_le_div_iff₀ h_rho_pow4_pos h_pow4_pos]
        have : (4 : ℝ) * (2 : ℝ) ^ (4 * kf ρ) ≤ 4 * ‖ρ.val‖ ^ 4 :=
          mul_le_mul_of_nonneg_left h_pow4_le (by norm_num)
        linarith
      calc (∑ ρ ∈ S, (4 : ℝ) / ‖ρ.val‖ ^ 4)
          ≤ ∑ ρ ∈ S, (4 : ℝ) / (2 : ℝ) ^ (4 * kf ρ) := by
            apply Finset.sum_le_sum h_per_elem
        _ = ∑ k ∈ Finset.range K_max,
              ∑ ρ ∈ S.filter (fun ρ => kf ρ = k), (4 : ℝ) / (2 : ℝ) ^ (4 * kf ρ) := by
            rw [← Finset.sum_fiberwise_of_maps_to
              (t := Finset.range K_max) (g := kf)
              (f := fun ρ => (4 : ℝ) / (2 : ℝ) ^ (4 * kf ρ))]
            intro ρ hρ
            exact Finset.mem_range.mpr (h_kf_le ρ hρ)
        _ = ∑ k ∈ Finset.range K_max,
              (S.filter (fun ρ => kf ρ = k)).card *
                ((4 : ℝ) / (2 : ℝ) ^ (4 * k)) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_congr rfl
              (g := fun _ => (4 : ℝ) / (2 : ℝ) ^ (4 * k))]
            · rw [Finset.sum_const, nsmul_eq_mul]
            · intro ρ hρ
              simp only [Finset.mem_filter] at hρ
              rw [hρ.2]
        _ ≤ ∑ k ∈ Finset.range K_max,
              (if N + 1 ≤ k then C_tail * (k + 1 : ℝ) / 8 ^ k else 0) := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hk_ge : N + 1 ≤ k
            · rw [if_pos hk_ge]
              -- card bound via step 3
              have h_subset_NTZ :
                  (S.filter (fun ρ => kf ρ = k)).image Subtype.val ⊆
                    (NontrivialZeros_inter_closedBall_finite
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
                  subst hρ_eq
                  linarith
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
                  exact ⟨hz.2, riemannXi_zero_of_mem_NontrivialZeros z hz.1⟩
                have hfin_big := riemannXi_zeros_finite_in_closedBall ((2 : ℝ) ^ (k + 1))
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
                  (NontrivialZeros_inter_closedBall_finite ((2 : ℝ) ^ (k + 1)))]
                exact_mod_cast Finset.card_le_card h_subset_NTZ
              have h_log_pow : Real.log ((2 : ℝ) ^ (k + 1)) = (k + 1 : ℝ) * Real.log 2 := by
                rw [Real.log_pow]; push_cast; ring
              have h_pow4k_pos : (0 : ℝ) < (2 : ℝ) ^ (4 * k) := pow_pos (by norm_num) _
              have h4div_nn : (0 : ℝ) ≤ 4 / (2 : ℝ) ^ (4 * k) := by positivity
              calc ((S.filter (fun ρ => kf ρ = k)).card : ℝ) * (4 / (2 : ℝ) ^ (4 * k))
                  ≤ ((NontrivialZeros ∩
                      Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))).ncard : ℝ) *
                      (4 / (2 : ℝ) ^ (4 * k)) :=
                    mul_le_mul_of_nonneg_right h_card_le h4div_nn
                _ ≤ (C₃ * (2 : ℝ) ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1))) *
                      (4 / (2 : ℝ) ^ (4 * k)) :=
                    mul_le_mul_of_nonneg_right h_ncard_bound h4div_nn
                _ = C_tail * (k + 1 : ℝ) / 8 ^ k := by
                    rw [h_log_pow, hC_tail_def]
                    have h2pk1 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
                      rw [pow_succ]; ring
                    have h24k : (2 : ℝ) ^ (4 * k) = ((2 : ℝ) ^ k) ^ 4 := by
                      rw [show (4 * k) = k * 4 from by ring, pow_mul]
                    have h8k : (8 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 3 := by
                      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 from by norm_num,
                          show ((2:ℝ)^3)^k = ((2:ℝ)^k)^3 from by
                            rw [← pow_mul, ← pow_mul, mul_comm]]
                    have hpk_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
                    rw [h2pk1, h24k, h8k]
                    field_simp
                    ring
            · rw [if_neg hk_ge]
              have h_filter_empty : S.filter (fun ρ => kf ρ = k) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro ρ hρ heq
                have := h_kf_ge ρ hρ
                omega
              rw [h_filter_empty]
              simp
        _ ≤ ∑ k ∈ Finset.range K_max, C_tail * (k + 1 : ℝ) / 8 ^ k := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hk_ge : N + 1 ≤ k
            · rw [if_pos hk_ge]
            · rw [if_neg hk_ge]
              have : 0 ≤ C_tail * (k + 1 : ℝ) / 8 ^ k := by
                rw [hC_tail_def]; positivity
              linarith
        _ ≤ C_tail * ∑' k : ℕ, ((k : ℝ) + 1) / 8 ^ k := by
            have h_sum_eq :
                (∑ k ∈ Finset.range K_max, C_tail * (k + 1 : ℝ) / 8 ^ k) =
                C_tail * ∑ k ∈ Finset.range K_max, ((k : ℝ) + 1) / 8 ^ k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intros; ring
            rw [h_sum_eq]
            apply mul_le_mul_of_nonneg_left _ (by rw [hC_tail_def]; positivity)
            have h_summ := summable_nat_succ_div_eight_pow
            have h_nn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) / 8 ^ k := fun k => by positivity
            exact Summable.sum_le_tsum _ (fun i _ => h_nn i) h_summ
    linarith
  · -- Cofinite bound: for all but finitely many ρ, f ρ ≤ 4/‖ρ‖^4.
    -- The exceptions are ρ with ‖ρ‖ < 2, a finite set by
    -- NontrivialZeros_inter_closedBall_finite.
    have h_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) 2).Finite :=
      NontrivialZeros_inter_closedBall_finite 2
    have h_sub_fin :
        {ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ < 2}.Finite := by
      have h_image_fin :
          ((fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => ρ.val) ''
            {ρ | ‖ρ.val‖ < 2}).Finite := by
        apply h_fin.subset
        intro z hz
        rcases hz with ⟨ρ, hρ_lt, hρ_eq⟩
        subst hρ_eq
        have : ‖ρ.val‖ < 2 := hρ_lt
        refine ⟨ρ.property, ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        linarith
      exact h_image_fin.of_finite_image Subtype.val_injective.injOn
    filter_upwards [h_sub_fin.compl_mem_cofinite] with ρ hρ
    -- hρ : ρ ∉ {ρ | ‖ρ.val‖ < 2}, i.e., ‖ρ.val‖ ≥ 2
    have h_norm_ge : (2 : ℝ) ≤ ‖ρ.val‖ := by
      by_contra h
      push_neg at h
      exact hρ h
    -- Now apply normSq_rho_times_rho_sub_one_ge
    have h_bound := normSq_rho_times_rho_sub_one_ge ρ.val h_norm_ge
    have h_normSq_pos : 0 < Complex.normSq (ρ.val * (ρ.val - 1)) := by
      apply lt_of_lt_of_le _ h_bound
      positivity
    rw [Real.norm_of_nonneg (div_nonneg zero_le_one (Complex.normSq_nonneg _))]
    rw [div_le_div_iff₀ h_normSq_pos (by positivity : (0 : ℝ) < ‖ρ.val‖ ^ 4)]
    linarith

#print axioms xi_bound_right_halfplane
#print axioms xi_bound_in_strip
#print axioms completedRiemannZeta₀_bounded_on_strip
#print axioms integrable_cosh_half_abs_ψ_mellin
#print axioms complex_cosh_norm_le_cosh_re
#print axioms ptwise_bound_cosh_kernel_strip
#print axioms xi_order_one_log_bound
#print axioms xi_jensen_at_zero
#print axioms xi_zero_count_disk_bound
#print axioms nontrivialZeros_inv_sq_summable

end ZeroCount
end ZD
