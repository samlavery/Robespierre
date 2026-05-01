import Mathlib
import RequestProject.EnergyDefect
import RequestProject.ZetaZeroDefs
import RequestProject.ThetaCenteredExcess
import RequestProject.StirlingBound

/-!
# Theta-transported density and the Mellin bridge to ξ

This file defines the theta-transported density `ψ_theta` and basic
complex-analytic tools used by downstream bridges. The `ξ`-identity
(`I_theta_of ψ_theta = riemannXi`) is developed in `MellinPathToXi.lean`.

## Structure of the file

* `riemannXi` — the entire `ξ(s) := (s(s−1)/2)·completedRiemannZeta₀ s + 1/2`.
* `ψ_theta` — inverse cosine transform of `ω ↦ ξ(1/2 + iω)` on `Ioi 0`.
* `I_theta_of` — the project's cosh-kernel integral as a `ℂ → ℂ` function.
* `riemannXi_eq_zero_of_mem_NontrivialZeros` — `ξ` vanishes at every
  nontrivial zero of `ζ` (used by `MellinPathToXi`).
-/

open Real Complex MeasureTheory BigOperators HurwitzZeta
  Set Filter Topology

noncomputable section

namespace ZD

/-- **The entire Riemann ξ**: `ξ(s) := (s(s−1)/2)·completedRiemannZeta₀ s + 1/2`.

This is the explicit entire form (avoiding Mathlib's `1/0 = 0` convention
issue at `s = 0, 1`). For `s ≠ 0, 1`, it agrees with the classical form
`(s(s−1)/2)·completedRiemannZeta s` via `completedRiemannZeta_eq`; the
value at `0, 1` is `1/2` (the removable-singularity value). Zeros of `ξ`
in the critical strip coincide with nontrivial zeros of `ζ`. -/
def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2

/-- **Theta-transported density**: the inverse cosine transform of
`ω ↦ ξ(1/2 + iω)` on `Ioi 0`.

Since `ξ(1/2 + iω)` is real-valued (by `ξ(s̄) = conj(ξ(s))` + FE
`ξ(s) = ξ(1−s)`), taking `.re` recovers the full value. The inverse
cosine transform is chosen so that the project's cosh-kernel integral
`I_theta_of ψ_theta s = ξ(s)` by Fourier inversion. -/
def ψ_theta : ℝ → ℝ := fun t =>
  (1 / Real.pi) *
    ∫ ω in Set.Ioi (0 : ℝ),
      (riemannXi ((1 / 2 : ℂ) + (ω : ℂ) * Complex.I)).re * Real.cos (ω * t)

/-- **Project-level theta observable**: `I(s) = ∫₀^∞ 2·cosh((s−1/2)t)·ψ(t) dt`. -/
def I_theta_of (ψ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    ((2 : ℂ) * Complex.cosh ((s - (1 / 2 : ℂ)) * (t : ℂ)) * (ψ t : ℂ))

/-- The `I_theta_of ψ` construction satisfies the project's `ThetaKernelRep`
predicate by definition. -/
theorem I_theta_of_ThetaKernelRep (ψ : ℝ → ℝ) :
    ThetaKernelRep (I_theta_of ψ) ψ := by
  intro s; rfl

/-! ### Fourier-inversion identity: proof scaffolding

The identity `I_theta_of ψ_theta s = riemannXi s` for all `s ∈ ℂ` is proved
by reducing to two sub-lemmas:

* `I_theta_eq_riemannXi_on_critical_line` — the identity holds for
  `s = 1/2 + iω`, by Fourier cosine inversion applied to the definition
  of `ψ_theta`.
* `I_theta_entire`, `riemannXi_entire` — both sides are entire.
* Identity theorem: entire functions agreeing on a line with
  accumulation points agree everywhere.

The critical-line sub-lemma is itself decomposed:

1. `I_theta_of ψ_theta (1/2 + iω) = 2·∫₀^∞ ψ_theta(t)·cos(ωt) dt`
   (unfold `Complex.cosh (iωt) = cos(ωt)` for real ω, t).
2. `2·∫₀^∞ ψ_theta(t)·cos(ωt) dt = riemannXi (1/2 + iω)`
   (cosine inversion: since `ψ_theta(t) = (1/π)·∫₀^∞ F(ω')·cos(ω't) dω'`
   with `F(ω) := (riemannXi (1/2+iω)).re`, the inverse-transform
   relation gives the result).
-/

/-- For `s ≠ 0, 1`, `riemannXi s = (s(s-1)/2) · completedRiemannZeta s`
(the classical expression). At `s = 0, 1` the Mathlib convention differs
from the entire-function value; `riemannXi` uses the entire form. -/
theorem riemannXi_eq_classical_of_ne_zero_of_ne_one
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  unfold riemannXi
  rw [completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- `riemannXi` is entire (by construction, as `polynomial · completedRiemannZeta₀ + const`). -/
theorem riemannXi_differentiable : Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact (((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).div_const
    2).mul differentiable_completedZeta₀).add (differentiable_const _)

/-! ### Stirling-derived decay on the critical line

These lemmas wire `ZD.StirlingBound.gamma_stirling_bound` into the project,
giving exponential decay of `Complex.Gamma` and `Gammaℝ` on vertical lines.
They are the analytic foundation for the missing `ψ_theta` decay needed by
the FT-inversion route. -/

/-- **Direct Stirling at σ = 1/4.** For large `|t|`,
`‖Γ(1/4 + it)‖ ≤ C · |t|^(-1/4) · exp(-π|t|/2)`. -/
theorem norm_Gamma_quarter_decay :
    ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ (t : ℝ), T₀ ≤ |t| →
        ‖Complex.Gamma (⟨(1 : ℝ)/4, t⟩ : ℂ)‖ ≤
          C * |t| ^ ((1 : ℝ)/4 - 1/2) * Real.exp (-π * |t| / 2) := by
  obtain ⟨_C_lo, C_hi, T₀, _hClo, hChi, hT0, hbnd⟩ :=
    ZD.StirlingBound.gamma_stirling_bound
      (hUpper := ZD.StirlingBound.gammaRatioUpperHalf_proved) (1/4 : ℝ) (by norm_num)
  exact ⟨C_hi, T₀, hChi, hT0, fun t ht => (hbnd t ht).2⟩

/-- Algebraic identification: `(⟨1/2, t⟩ : ℂ) / 2 = ⟨1/4, t/2⟩`. -/
private lemma half_critical_div_two (t : ℝ) :
    (⟨(1 : ℝ)/2, t⟩ : ℂ) / 2 = ⟨(1 : ℝ)/4, t/2⟩ := by
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq] <;> ring

/-- **Gammaℝ decay on the critical line.** For large `|t|`,
`‖Gammaℝ(1/2 + it)‖ ≤ C · |t|^(-1/4) · exp(-π|t|/4)`. Derived from
`norm_Gamma_quarter_decay` via `Gammaℝ s = π^(-s/2) · Γ(s/2)`. -/
theorem norm_Gammaℝ_critical_decay :
    ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ (t : ℝ), T₀ ≤ |t| →
        ‖Gammaℝ (⟨(1 : ℝ)/2, t⟩ : ℂ)‖ ≤
          C * |t| ^ (-(1 : ℝ)/4) * Real.exp (-π * |t| / 4) := by
  obtain ⟨C, T₀, hC, hT0, hbnd⟩ := norm_Gamma_quarter_decay
  refine ⟨Real.pi ^ (-(1 : ℝ)/4) * C * (2 : ℝ) ^ ((1 : ℝ)/4),
    2 * T₀, by positivity, by linarith, ?_⟩
  intro t ht
  -- |t/2| ≥ T₀
  have ht2 : T₀ ≤ |t/2| := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  -- Apply Stirling at the half point
  have hG := hbnd (t/2) ht2
  -- Algebraic decomposition of Gammaℝ
  have h_def : Gammaℝ (⟨(1 : ℝ)/2, t⟩ : ℂ) =
      (Real.pi : ℂ) ^ (-(⟨(1 : ℝ)/2, t⟩ : ℂ) / 2) *
        Complex.Gamma (⟨(1 : ℝ)/4, t/2⟩ : ℂ) := by
    rw [Gammaℝ_def, half_critical_div_two]
  rw [h_def]
  -- Norm of product
  rw [norm_mul]
  -- ‖π^z‖ = π^(Re z) for π > 0
  have h_re : (-(⟨(1 : ℝ)/2, t⟩ : ℂ) / 2).re = -(1 : ℝ)/4 := by
    simp [Complex.div_re, Complex.neg_re, Complex.normSq]; ring
  have h_pi : ‖(Real.pi : ℂ) ^ (-(⟨(1 : ℝ)/2, t⟩ : ℂ) / 2)‖ =
      Real.pi ^ (-(1 : ℝ)/4) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, h_re]
  rw [h_pi]
  -- Now: π^(-1/4) * ‖Γ⟨1/4, t/2⟩‖ ≤ π^(-1/4) * 2^(1/4) * C * |t|^(-1/4) · exp(...)
  have h_t2_pos : 0 < |t/2| := lt_of_lt_of_le hT0 ht2
  have h_t_pos : 0 < |t| := by
    have : (0:ℝ) < |t|/2 := by rw [← abs_of_pos (by norm_num : (0:ℝ) < 2)]; rwa [← abs_div]
    linarith
  have h_rewrite : |t/2| ^ ((1 : ℝ)/4 - 1/2) = (2 : ℝ) ^ ((1 : ℝ)/4) * |t| ^ (-(1:ℝ)/4) := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [Real.div_rpow (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 2)]
    have h_exp_eq : ((1:ℝ)/4 - 1/2) = -(1/4 : ℝ) := by norm_num
    rw [h_exp_eq, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (-(1:ℝ)/4) = -(1/4 : ℝ) from by norm_num]
    field_simp
  have h_exp : Real.exp (-π * |t/2| / 2) = Real.exp (-π * |t| / 4) := by
    congr 1
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  -- Combine
  calc Real.pi ^ (-(1 : ℝ)/4) * ‖Complex.Gamma (⟨(1 : ℝ)/4, t/2⟩ : ℂ)‖
      ≤ Real.pi ^ (-(1 : ℝ)/4) *
          (C * |t/2| ^ ((1 : ℝ)/4 - 1/2) * Real.exp (-π * |t/2| / 2)) := by
        apply mul_le_mul_of_nonneg_left hG (by positivity)
    _ = Real.pi ^ (-(1 : ℝ)/4) * C *
          ((2 : ℝ) ^ ((1 : ℝ)/4) * |t| ^ (-(1 : ℝ)/4)) *
          Real.exp (-π * |t| / 4) := by
        rw [h_rewrite, h_exp]; ring
    _ = Real.pi ^ (-(1 : ℝ)/4) * C * (2 : ℝ) ^ ((1 : ℝ)/4) *
          |t| ^ (-(1 : ℝ)/4) * Real.exp (-π * |t| / 4) := by ring

/-! ### Exponential decay of `evenKernel 0` — foundation for Mellin bounds

These lemmas provide the pointwise exponential decay of `evenKernel 0`
(equivalently, the Jacobi theta function `θ(ix)`) at both `x → ∞` and `x → 0`.
Both are needed for the Mellin-integral absolute bound that controls
`completedRiemannZeta₀` on the critical line.

Source: Mathlib's `norm_jacobiTheta_sub_one_le` + `evenKernel_functional_equation`.
-/

/-- **Pointwise bound on `evenKernel 0 x - 1` for `x > 0`.** Via
`norm_jacobiTheta_sub_one_le` composed with
`evenKernel 0 x = jacobiTheta(I·x)` (`evenKernel_eq_cosKernel_of_zero` +
`cosKernel_def` + `jacobiTheta_eq_jacobiTheta₂`). -/
theorem norm_evenKernel_zero_sub_one_le (x : ℝ) (hx : 0 < x) :
    |evenKernel 0 x - 1| ≤
      2 * Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x)) := by
  have hpos : 0 < (Complex.I * (x : ℂ)).im := by simpa using hx
  have hbnd := norm_jacobiTheta_sub_one_le hpos
  have hτim : (Complex.I * (x : ℂ)).im = x := by simp
  rw [hτim] at hbnd
  have hek : (evenKernel 0 x : ℂ) = jacobiTheta (Complex.I * (x : ℂ)) := by
    rw [evenKernel_eq_cosKernel_of_zero]
    rw [show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) from rfl]
    rw [cosKernel_def]
    simp [← jacobiTheta_eq_jacobiTheta₂]
  have hnorm_eq : ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ = |evenKernel 0 x - 1| := by
    rw [← hek]
    have hcast : (evenKernel 0 x : ℂ) - 1 = (((evenKernel 0 x - 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  calc |evenKernel 0 x - 1|
      = ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ := hnorm_eq.symm
    _ ≤ 2 / (1 - Real.exp (-Real.pi * x)) * Real.exp (-Real.pi * x) := hbnd
    _ = 2 * Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x)) := by ring

/-- `‖cosh z‖ ≤ exp(‖z‖)` for any complex z. -/
theorem norm_cosh_le_exp_norm (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  have h2 := Complex.two_cosh z
  have hcosh : Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 := by
    have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
    field_simp
    linear_combination h2
  rw [hcosh]
  calc ‖(Complex.exp z + Complex.exp (-z)) / 2‖
      ≤ (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 := by
        rw [norm_div]
        have : ‖(2 : ℂ)‖ = 2 := by simp
        rw [this]
        apply div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ = (Real.exp z.re + Real.exp (-z.re)) / 2 := by
        rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
    _ ≤ Real.exp |z.re| := by
        rcases le_total 0 z.re with h | h
        · rw [abs_of_nonneg h]
          have h1 : Real.exp (-z.re) ≤ Real.exp z.re :=
            Real.exp_le_exp.mpr (by linarith)
          linarith
        · rw [abs_of_nonpos h]
          have h1 : Real.exp z.re ≤ Real.exp (-z.re) :=
            Real.exp_le_exp.mpr (by linarith)
          linarith
    _ ≤ Real.exp ‖z‖ :=
        Real.exp_le_exp.mpr (Complex.abs_re_le_norm z)

/-- `‖cosh((s-1/2)t)‖ ≤ exp(‖s-1/2‖·|t|)` for all complex s, real t. -/
theorem norm_cosh_le_exp_abs (s : ℂ) (t : ℝ) :
    ‖Complex.cosh ((s - (1 / 2 : ℂ)) * (t : ℂ))‖ ≤
      Real.exp (‖s - (1 / 2 : ℂ)‖ * |t|) := by
  have h := norm_cosh_le_exp_norm ((s - (1 / 2 : ℂ)) * (t : ℂ))
  rw [norm_mul, Complex.norm_real] at h
  exact h

/-- `‖sinh z‖ ≤ exp(‖z‖)` for any complex z. -/
theorem norm_sinh_le_exp_norm (z : ℂ) :
    ‖Complex.sinh z‖ ≤ Real.exp ‖z‖ := by
  have h2 := Complex.two_sinh z
  have hsinh : Complex.sinh z = (Complex.exp z - Complex.exp (-z)) / 2 := by
    have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
    field_simp
    linear_combination h2
  rw [hsinh]
  calc ‖(Complex.exp z - Complex.exp (-z)) / 2‖
      ≤ (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 := by
        rw [norm_div]
        have : ‖(2 : ℂ)‖ = 2 := by simp
        rw [this]
        apply div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ = (Real.exp z.re + Real.exp (-z.re)) / 2 := by
        rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
    _ ≤ Real.exp |z.re| := by
        rcases le_total 0 z.re with h | h
        · rw [abs_of_nonneg h]
          have h1 : Real.exp (-z.re) ≤ Real.exp z.re :=
            Real.exp_le_exp.mpr (by linarith)
          linarith
        · rw [abs_of_nonpos h]
          have h1 : Real.exp z.re ≤ Real.exp (-z.re) :=
            Real.exp_le_exp.mpr (by linarith)
          linarith
    _ ≤ Real.exp ‖z‖ :=
        Real.exp_le_exp.mpr (Complex.abs_re_le_norm z)

/-- `‖t·sinh((s-1/2)t)‖ ≤ |t|·exp(‖s-1/2‖·|t|)`. -/
theorem norm_t_sinh_le_t_exp_abs (s : ℂ) (t : ℝ) :
    ‖((t : ℂ)) * Complex.sinh ((s - (1 / 2 : ℂ)) * (t : ℂ))‖ ≤
      |t| * Real.exp (‖s - (1 / 2 : ℂ)‖ * |t|) := by
  rw [norm_mul, Complex.norm_real]
  have h := norm_sinh_le_exp_norm ((s - (1 / 2 : ℂ)) * (t : ℂ))
  rw [norm_mul, Complex.norm_real] at h
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The sequence `1/2 + i/(n+1)` tends to `1/2` avoiding `1/2`. -/
theorem tendsto_critical_seq :
    Filter.Tendsto
      (fun n : ℕ => ((1 / 2 : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝[≠] ((1 / 2 : ℂ))) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · -- Tendsto to 1/2 in 𝓝
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        Filter.atTop (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    have h3 : Filter.Tendsto
        (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
        Filter.atTop (𝓝 (0 : ℂ)) := by
      have hmul := h2.mul_const Complex.I
      simpa using hmul
    have h4 : Filter.Tendsto
        (fun n : ℕ => (1 / 2 : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
        Filter.atTop (𝓝 ((1/2 : ℂ) + 0)) :=
      (tendsto_const_nhds (x := (1 / 2 : ℂ))).add h3
    simpa using h4
  · -- Each term ≠ 1/2
    filter_upwards with n
    intro h
    have hsub : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I = 0 := by
      have := sub_eq_zero.mpr h.symm
      -- h : 1/2 + (...)·I = 1/2 ⟹ (...)·I = 0
      have hre := congrArg Complex.re this
      have him := congrArg Complex.im this
      simp at hre him
      exact Complex.ext (by simpa using hre) (by simpa using him)
    have hI_ne : Complex.I ≠ 0 := Complex.I_ne_zero
    have hR : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hsub).resolve_right hI_ne
    have hRreal : (1 / ((n : ℝ) + 1) : ℝ) = 0 := by exact_mod_cast hR
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- **ξ vanishes at nontrivial zeros of ζ.** Proved unconditionally via
`riemannZeta_def_of_ne_zero` + `Gammaℝ_ne_zero_of_re_pos`, giving
`completedRiemannZeta ρ = 0`, then using `riemannXi_eq_classical_of_ne_zero_of_ne_one`. -/
theorem riemannXi_eq_zero_of_mem_NontrivialZeros
    (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) :
    riemannXi ρ = 0 := by
  have hρ_re_pos : 0 < ρ.re := hρ.1
  have hρ_re_lt_one : ρ.re < 1 := hρ.2.1
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ_re_pos; linarith
  have hρ_ne_one : ρ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hρ_re_lt_one; linarith
  rw [riemannXi_eq_classical_of_ne_zero_of_ne_one ρ hρ_ne_zero hρ_ne_one]
  have hGammaℝ_ne : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos hρ_re_pos
  have hzeta_zero : riemannZeta ρ = 0 := hρ.2.2
  have hdiv : completedRiemannZeta ρ / Gammaℝ ρ = 0 := by
    rw [← riemannZeta_def_of_ne_zero hρ_ne_zero]; exact hzeta_zero
  have hC : completedRiemannZeta ρ = 0 :=
    (div_eq_zero_iff.mp hdiv).resolve_right hGammaℝ_ne
  rw [hC]; ring

end ZD
