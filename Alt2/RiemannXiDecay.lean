import Mathlib
import RequestProject.StirlingBound
import RequestProject.ThetaTransport

/-!
# Exponential Decay of Riemann Xi on Vertical Lines

Using `StirlingBound.gamma_stirling_bound` (proved unconditionally via
`GammaSeq` ratio analysis), we derive exponential decay of the `Γ(s/2)`
factor on vertical lines. This feeds into the full ξ decay once combined
with a polynomial bound on ζ in the critical strip.

## Content

* `gamma_half_vertical_decay` — direct Stirling application at σ/2, gives
  `‖Γ(σ/2 + iγ/2)‖ ≤ C · |γ|^{(σ-1)/2} · exp(−π|γ|/4)` for large γ.
  Unconditional via `gamma_stirling_bound`.
* `gammaℝ_vertical_decay` — `Gammaℝ(σ+iγ) = π^{-s/2}·Γ(s/2)` factor's
  exponential decay, follows from the previous + π-factor algebra.

## Not yet addressed

* `riemannXi_vertical_decay` — requires a polynomial bound on `|ζ(σ+iγ)|`
  in the critical strip, which is classical analytic number theory
  (convexity theorem / Phragmén-Lindelöf) not currently packaged in
  Mathlib. Stated as a named `Prop` target.
-/

open Real Complex MeasureTheory

noncomputable section

namespace ZD

/-- **Γ-factor exponential decay at σ/2 on vertical lines.** Direct
Stirling: for each `σ > 0`, there exist constants `C, T₀` such that for
`|γ| ≥ 2·T₀`, `‖Γ(σ/2 + iγ/2)‖ ≤ C · |γ|^{(σ-1)/2} · exp(-π|γ|/4)`.
Unconditional via `StirlingBound.gamma_stirling_bound` applied at `σ/2`. -/
theorem gamma_half_vertical_decay (σ : ℝ) (hσ : 0 < σ) :
    ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ (γ : ℝ), T₀ ≤ |γ| →
        ‖Complex.Gamma (⟨σ/2, γ/2⟩ : ℂ)‖ ≤
          C * |γ| ^ ((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4) := by
  -- Apply Stirling at σ' = σ/2, t = γ/2.
  obtain ⟨_C_lo, C_hi, T₀, _hClo, hChi, hT0, hbnd⟩ :=
    ZD.StirlingBound.gamma_stirling_bound
      (hUpper := ZD.StirlingBound.gammaRatioUpperHalf_proved) (σ/2 : ℝ)
      (by linarith)
  -- Rescale: |γ/2| ≥ T₀ ⟺ |γ| ≥ 2·T₀
  refine ⟨C_hi * (2 : ℝ)^((1 - σ)/2), 2 * T₀, by positivity, by linarith, ?_⟩
  intro γ hγ
  have hγ2 : T₀ ≤ |γ/2| := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  -- Stirling at (σ/2, γ/2) gives the upper bound
  have hG := (hbnd (γ/2) hγ2).2
  -- |γ/2|^((σ/2) - 1/2) = |γ|^((σ-1)/2) · 2^((1-σ)/2)
  have hγ_pos : 0 < |γ| := by
    have : (0:ℝ) < 2 * T₀ := by linarith
    linarith
  have h_pow_eq : |γ/2| ^ ((σ/2 : ℝ) - 1/2) =
      (2 : ℝ)^(-((σ - 1)/2)) * |γ| ^ ((σ - 1)/2) := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [show ((σ/2 : ℝ) - 1/2) = (σ - 1)/2 from by ring]
    rw [Real.div_rpow (abs_nonneg γ) (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (2 : ℝ)^((σ - 1)/2) = ((2 : ℝ)^(-((σ-1)/2)))⁻¹ from by
      rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]; ring_nf]
    field_simp
  have h_exp_eq : Real.exp (-Real.pi * |γ/2| / 2) =
      Real.exp (-Real.pi * |γ| / 4) := by
    congr 1
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    field_simp
    ring
  have h_argument : (⟨σ/2, γ/2⟩ : ℂ) = (σ/2 : ℂ) + (γ/2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  -- Combine
  calc ‖Complex.Gamma (⟨σ/2, γ/2⟩ : ℂ)‖
      ≤ C_hi * |γ/2| ^ ((σ/2 : ℝ) - 1/2) * Real.exp (-Real.pi * |γ/2| / 2) := hG
    _ = C_hi * ((2 : ℝ)^(-((σ - 1)/2)) * |γ| ^ ((σ - 1)/2)) *
          Real.exp (-Real.pi * |γ| / 4) := by rw [h_pow_eq, h_exp_eq]
    _ = C_hi * (2 : ℝ)^(-((σ - 1)/2)) * |γ| ^ ((σ - 1)/2) *
          Real.exp (-Real.pi * |γ| / 4) := by ring
    _ = C_hi * (2 : ℝ)^((1 - σ)/2) * |γ| ^ ((σ - 1)/2) *
          Real.exp (-Real.pi * |γ| / 4) := by
        rw [show -((σ - 1)/2) = (1 - σ)/2 from by ring]
    _ = C_hi * (2 : ℝ) ^ ((1 - σ)/2) * |γ| ^ ((σ - 1)/2) *
          Real.exp (-Real.pi * |γ| / 4) := by ring

/-- **ζ polynomial growth bound in the critical strip (named target).**
For each `σ ∈ (0, 1)`, there exist `C, N, T₀` such that for `|γ| ≥ T₀`,
`|ζ(σ + iγ)| ≤ C · |γ|^N`. Classical result (convexity theorem +
Phragmén-Lindelöf); not currently in Mathlib. Stated here as a named
Prop to be discharged; every theorem that depends on it explicitly takes
it as a hypothesis. -/
def zetaPolynomialBoundInStrip : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 →
    ∃ (C : ℝ) (N : ℝ) (T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ (γ : ℝ), T₀ ≤ |γ| →
        ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ C * |γ|^N

/-- **riemannXi vertical decay (conditional on ζ polynomial bound).** For
each `σ ∈ (0, 1)`, `‖ξ(σ + iγ)‖ ≤ C · |γ|^M · exp(-π|γ|/4)` for large `|γ|`,
where `M` depends on the ζ polynomial exponent. Proof is
`ξ = (s(s-1)/2)·π^{-s/2}·Γ(s/2)·ζ(s)`: (s(s-1)/2) is polynomial; π^{-s/2}
is constant in γ; Γ(s/2) decays via `gamma_half_vertical_decay`; ζ is
bounded polynomially by hypothesis. Product: polynomial × exp decay. -/
def riemannXi_vertical_decay_target : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 →
    ∃ (C : ℝ) (M : ℝ) (T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ (γ : ℝ), T₀ ≤ |γ| →
        ‖ZD.riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤
          C * |γ|^M * Real.exp (-Real.pi * |γ| / 4)

/-- **Integrability of `|ξ|²` on vertical lines (conditional target).** If
ξ decays exponentially on vertical lines, `|ξ(σ+iγ)|²` is integrable on
`Ioi 0` for each σ ∈ (0,1). This is an `Integrable`/`IntegrableOn`
conclusion downstream of `riemannXi_vertical_decay_target`. -/
def riemannXi_L2_integrable_target (σ : ℝ) : Prop :=
  IntegrableOn
    (fun γ : ℝ =>
      Complex.normSq (ZD.riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)))
    (Set.Ioi (0:ℝ))

/-- **Pointwise squared-norm bound from ξ vertical decay.** If
`riemannXi_vertical_decay_target` holds at σ, then `|ξ(σ+iγ)|²` is bounded
by `C²·|γ|^{2M}·exp(-π|γ|/2)` for `|γ| ≥ T₀`. Forward-only; no
integrability claim. This is the clean ingredient that feeds into any
standard Mathlib `Integrable.mono'` assembly for the full L² integrability
target. -/
theorem riemannXi_normSq_tail_bound_of_decay
    (hdecay : riemannXi_vertical_decay_target)
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ_lt : σ < 1) :
    ∃ (K : ℝ) (M : ℝ) (T₀ : ℝ), 0 < K ∧ 0 < T₀ ∧
      ∀ (γ : ℝ), T₀ ≤ |γ| →
        Complex.normSq (ZD.riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)) ≤
          K * |γ|^(2*M) * Real.exp (-Real.pi * |γ| / 2) := by
  obtain ⟨C, M, T₀, hC, hT0, hbnd⟩ := hdecay σ hσ_pos hσ_lt
  refine ⟨C^2, M, T₀, by positivity, hT0, ?_⟩
  intro γ hγ
  have h := hbnd γ hγ
  have h_pos : 0 ≤ ‖ZD.riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ := norm_nonneg _
  have h_dom : 0 ≤ C * |γ|^M * Real.exp (-Real.pi * |γ| / 4) := by positivity
  have h_sq : ‖ZD.riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)‖^2 ≤
      (C * |γ|^M * Real.exp (-Real.pi * |γ| / 4))^2 := by
    exact sq_le_sq' (by linarith [h_pos]) h
  have h_normSq : Complex.normSq (ZD.riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)) =
      ‖ZD.riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)‖^2 :=
    Complex.normSq_eq_norm_sq _
  rw [h_normSq]
  calc ‖ZD.riemannXi ((σ : ℂ) + (γ : ℂ) * Complex.I)‖^2
      ≤ (C * |γ|^M * Real.exp (-Real.pi * |γ| / 4))^2 := h_sq
    _ = C^2 * (|γ|^M)^2 * (Real.exp (-Real.pi * |γ| / 4))^2 := by ring
    _ = C^2 * |γ|^(2*M) * Real.exp (-Real.pi * |γ| / 2) := by
        have hγ_pos : 0 < |γ| := lt_of_lt_of_le hT0 hγ
        have h1 : (|γ|^M)^2 = |γ|^(2*M) := by
          rw [sq, ← Real.rpow_add hγ_pos]
          congr 1; ring
        have h2 : Real.exp (-Real.pi * |γ| / 4)^2 =
            Real.exp (-Real.pi * |γ| / 2) := by
          rw [sq, ← Real.exp_add]
          congr 1; ring
        rw [h1, h2]

/-- **Norm of `s(s-1)/2` on vertical lines, strip case.** For `σ ∈ (0,1)` and
`|γ| ≥ 1`, `|s(s-1)/2| ≤ |γ|²` where `s = σ + iγ`. -/
lemma abs_s_sub_one_half_le_sq (σ : ℝ) (hσ_pos : 0 < σ) (hσ_lt : σ < 1)
    (γ : ℝ) (hγ : 1 ≤ |γ|) :
    ‖((σ : ℂ) + (γ : ℂ) * Complex.I) *
        (((σ : ℂ) + (γ : ℂ) * Complex.I) - 1) / 2‖ ≤ |γ|^2 := by
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hs_def
  have h_γsq : γ^2 = |γ|^2 := (sq_abs γ).symm
  have hγsq_ge_one : 1 ≤ γ^2 := by
    rw [h_γsq]; nlinarith [abs_nonneg γ]
  have hsigma_bound : σ^2 ≤ 1 := by nlinarith
  have h1sigma_bound : (σ - 1)^2 ≤ 1 := by nlinarith
  -- ‖s‖² = σ² + γ²
  have h_normSq_s : ‖s‖^2 = σ^2 + γ^2 := by
    rw [← Complex.normSq_eq_norm_sq, hs_def, Complex.normSq_add_mul_I]
  -- ‖s - 1‖² = (σ-1)² + γ²
  have h_normSq_s1 : ‖s - 1‖^2 = (σ - 1)^2 + γ^2 := by
    have hrw : s - 1 = ((σ - 1 : ℝ) : ℂ) + (γ : ℂ) * Complex.I := by
      rw [hs_def]; push_cast; ring
    rw [← Complex.normSq_eq_norm_sq, hrw, Complex.normSq_add_mul_I]
  -- Upper bound each
  have h_norm_s_sq : ‖s‖^2 ≤ 1 + γ^2 := by rw [h_normSq_s]; linarith
  have h_norm_s1_sq : ‖s - 1‖^2 ≤ 1 + γ^2 := by rw [h_normSq_s1]; linarith
  have h_nn : 0 ≤ ‖s‖ := norm_nonneg _
  have h_nn' : 0 ≤ ‖s - 1‖ := norm_nonneg _
  -- Product bound: ‖s·(s-1)‖² = ‖s‖² · ‖s-1‖² ≤ (1+γ²)²
  have h_prod_sq : (‖s‖ * ‖s - 1‖)^2 ≤ (1 + γ^2)^2 := by
    have h1 : (‖s‖ * ‖s - 1‖)^2 = ‖s‖^2 * ‖s - 1‖^2 := by ring
    rw [h1]
    have h_nn_1γ : 0 ≤ 1 + γ^2 := by positivity
    calc ‖s‖^2 * ‖s - 1‖^2
        ≤ (1 + γ^2) * (1 + γ^2) := by
          apply mul_le_mul h_norm_s_sq h_norm_s1_sq (sq_nonneg _) h_nn_1γ
      _ = (1 + γ^2)^2 := by ring
  have h_prod_nn : 0 ≤ ‖s‖ * ‖s - 1‖ := by positivity
  have h_1γ_nn : 0 ≤ 1 + γ^2 := by positivity
  have h_prod_bound : ‖s * (s - 1)‖ ≤ 1 + γ^2 := by
    rw [norm_mul]
    exact abs_le_of_sq_le_sq' h_prod_sq h_1γ_nn |>.2
  -- 1 + γ² ≤ 2γ²
  have h_gamma_sq : 1 + γ^2 ≤ 2 * γ^2 := by linarith
  have h_div : ‖s * (s - 1) / 2‖ = ‖s * (s - 1)‖ / 2 := by
    rw [norm_div]; simp
  rw [h_div]
  have h_chain : ‖s * (s - 1)‖ / 2 ≤ γ^2 := by linarith
  rw [← h_γsq]; exact h_chain

/-- **`Gammaℝ` decay on vertical lines, strip case.** For `σ > 0` and large
`|γ|`, `‖Gammaℝ(σ + iγ)‖ ≤ C · |γ|^((σ-1)/2) · exp(-π|γ|/4)`.
Derived from `gamma_half_vertical_decay` + constant `π^(-σ/2)` factor. -/
theorem Gammaℝ_vertical_decay (σ : ℝ) (hσ : 0 < σ) :
    ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
      ∀ (γ : ℝ), T₀ ≤ |γ| →
        ‖Complex.Gammaℝ ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤
          C * |γ|^((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4) := by
  obtain ⟨C_Γ, T_Γ, hCΓ, hTΓ, hΓ⟩ := gamma_half_vertical_decay σ hσ
  refine ⟨Real.pi ^ (-σ/2) * C_Γ, T_Γ, by positivity, hTΓ, ?_⟩
  intro γ hγ
  -- s = σ + iγ, s/2 = ⟨σ/2, γ/2⟩
  have h_arg : ((σ : ℂ) + (γ : ℂ) * Complex.I) / 2 = (⟨σ/2, γ/2⟩ : ℂ) := by
    apply Complex.ext <;> simp
  -- Gammaℝ s = π^(-s/2) · Γ(s/2)
  have h_unfold : Complex.Gammaℝ ((σ : ℂ) + (γ : ℂ) * Complex.I) =
      (Real.pi : ℂ) ^ (-((σ : ℂ) + (γ : ℂ) * Complex.I) / 2) *
        Complex.Gamma (⟨σ/2, γ/2⟩ : ℂ) := by
    unfold Complex.Gammaℝ
    rw [h_arg]
  rw [h_unfold, norm_mul]
  -- Norm of π^(-s/2) = π^(-σ/2), constant in γ
  have h_pi_norm : ‖(Real.pi : ℂ) ^ (-((σ : ℂ) + (γ : ℂ) * Complex.I) / 2)‖ =
      Real.pi ^ (-σ/2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  rw [h_pi_norm]
  have hG := hΓ γ hγ
  have h_pi_nn : 0 ≤ Real.pi ^ (-σ/2) := by positivity
  calc Real.pi ^ (-σ/2) * ‖Complex.Gamma (⟨σ/2, γ/2⟩ : ℂ)‖
      ≤ Real.pi ^ (-σ/2) * (C_Γ * |γ|^((σ-1)/2) * Real.exp (-Real.pi * |γ| / 4)) :=
        mul_le_mul_of_nonneg_left hG h_pi_nn
    _ = Real.pi ^ (-σ/2) * C_Γ * |γ|^((σ-1)/2) * Real.exp (-Real.pi * |γ| / 4) := by ring

/-- **Main forward theorem.** Assuming a polynomial bound on ζ in the critical
strip, ξ decays exponentially on vertical lines with exponent `-π|γ|/4`.
Proof: for `s = σ + iγ` with `|γ| ≥ 1`:
  * `s ≠ 0, s ≠ 1`, so `ξ(s) = (s(s-1)/2) · Λ(s)` with Λ = completedRiemannZeta.
  * `Λ(s) = Gammaℝ(s) · ζ(s)` (via `riemannZeta_def_of_ne_zero` rearranged).
  * `|s(s-1)/2| ≤ |γ|²` by `abs_s_sub_one_half_le_sq`.
  * `|Gammaℝ(s)| ≤ C_Γ · |γ|^((σ-1)/2) · exp(-π|γ|/4)` by `Gammaℝ_vertical_decay`.
  * `|ζ(s)| ≤ C_ζ · |γ|^N` by hypothesis.
  * Combined: polynomial × exp decay. -/
theorem riemannXi_vertical_decay_of_zetaBound
    (hζ : zetaPolynomialBoundInStrip) :
    riemannXi_vertical_decay_target := by
  intro σ hσ_pos hσ_lt
  obtain ⟨C_Γ, T_Γ, hCΓ, hTΓ, hΓ⟩ := Gammaℝ_vertical_decay σ hσ_pos
  obtain ⟨C_ζ, N_ζ, T_ζ, hCζ, hTζ, hζb⟩ := hζ σ hσ_pos hσ_lt
  refine ⟨C_Γ * C_ζ, 2 + (σ - 1)/2 + N_ζ, max 1 (max T_Γ T_ζ),
    by positivity, lt_max_of_lt_left one_pos, ?_⟩
  intro γ hγ
  have hγ_one : 1 ≤ |γ| := le_of_max_le_left hγ
  have hγ_Γ : T_Γ ≤ |γ| := le_of_max_le_left (le_of_max_le_right hγ)
  have hγ_ζ : T_ζ ≤ |γ| := le_of_max_le_right (le_of_max_le_right hγ)
  have hγ_pos : 0 < |γ| := lt_of_lt_of_le one_pos hγ_one
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hs_def
  -- s ≠ 0 and s ≠ 1
  have hs_ne_zero : s ≠ 0 := by
    intro h
    have him : s.im = γ := by simp [hs_def]
    have : γ = 0 := by rw [← him, h]; simp
    have : |γ| = 0 := by rw [this]; simp
    linarith
  have hs_ne_one : s ≠ 1 := by
    intro h
    have him : s.im = γ := by simp [hs_def]
    have : γ = 0 := by rw [← him, h]; simp
    have : |γ| = 0 := by rw [this]; simp
    linarith
  -- ξ(s) = (s(s-1)/2) · completedRiemannZeta(s)
  have h_xi_class : ZD.riemannXi s =
      (s * (s - 1) / 2) * completedRiemannZeta s :=
    ZD.riemannXi_eq_classical_of_ne_zero_of_ne_one s hs_ne_zero hs_ne_one
  -- completedRiemannZeta s = Gammaℝ s · ζ s (rearranged from riemannZeta_def_of_ne_zero)
  have h_Lambda : completedRiemannZeta s =
      Complex.Gammaℝ s * riemannZeta s := by
    have h_Gammaℝ_ne : Complex.Gammaℝ s ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp [hs_def]; exact hσ_pos)
    have hz := riemannZeta_def_of_ne_zero hs_ne_zero
    field_simp [h_Gammaℝ_ne] at hz
    linear_combination -hz
  -- ξ(s) = (s(s-1)/2) · Gammaℝ(s) · ζ(s)
  have h_xi_full : ZD.riemannXi s =
      (s * (s - 1) / 2) * Complex.Gammaℝ s * riemannZeta s := by
    rw [h_xi_class, h_Lambda]; ring
  -- Norm bounds on each factor
  have h_norm_poly : ‖s * (s - 1) / 2‖ ≤ |γ|^2 := by
    rw [hs_def]
    exact abs_s_sub_one_half_le_sq σ hσ_pos hσ_lt γ hγ_one
  have h_norm_G : ‖Complex.Gammaℝ s‖ ≤
      C_Γ * |γ|^((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4) := by
    rw [hs_def]; exact hΓ γ hγ_Γ
  have h_norm_ζ : ‖riemannZeta s‖ ≤ C_ζ * |γ|^N_ζ := by
    rw [hs_def]; exact hζb γ hγ_ζ
  -- Combine
  have h_nn_poly : 0 ≤ ‖s * (s - 1) / 2‖ := norm_nonneg _
  have h_nn_γ_pow : ∀ (r : ℝ), 0 ≤ |γ|^r := fun r => Real.rpow_nonneg (abs_nonneg _) r
  have h_nn_G : 0 ≤ C_Γ * |γ|^((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4) := by
    have := h_nn_γ_pow ((σ-1)/2)
    have : 0 ≤ Real.exp (-Real.pi * |γ| / 4) := (Real.exp_pos _).le
    positivity
  have h_nn_ζ : 0 ≤ C_ζ * |γ|^N_ζ := by
    have := h_nn_γ_pow N_ζ; positivity
  have h_prod1 : ‖(s * (s - 1) / 2) * Complex.Gammaℝ s‖ ≤
      |γ|^2 * (C_Γ * |γ|^((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4)) := by
    rw [norm_mul]
    exact mul_le_mul h_norm_poly h_norm_G (norm_nonneg _) (sq_nonneg _)
  have h_nn_prod1 : 0 ≤ ‖(s * (s - 1) / 2) * Complex.Gammaℝ s‖ := norm_nonneg _
  have h_bound : ‖ZD.riemannXi s‖ ≤
      (|γ|^2 * (C_Γ * |γ|^((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4))) *
        (C_ζ * |γ|^N_ζ) := by
    rw [h_xi_full, norm_mul]
    exact mul_le_mul h_prod1 h_norm_ζ (norm_nonneg _)
      (by positivity)
  -- Algebra: rearrange to target form
  have h_γ_sq : |γ|^(2 : ℕ) = |γ|^(2 : ℝ) :=
    (Real.rpow_natCast _ 2).symm
  have h_eq : (|γ|^2 * (C_Γ * |γ|^((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4))) *
      (C_ζ * |γ|^N_ζ) =
      C_Γ * C_ζ * |γ|^(2 + (σ - 1)/2 + N_ζ) * Real.exp (-Real.pi * |γ| / 4) := by
    rw [h_γ_sq]
    have hrearrange : |γ|^(2:ℝ) * (C_Γ * |γ|^((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4)) *
        (C_ζ * |γ|^N_ζ) =
        C_Γ * C_ζ * (|γ|^(2:ℝ) * |γ|^((σ - 1)/2) * |γ|^N_ζ) *
          Real.exp (-Real.pi * |γ| / 4) := by ring
    rw [hrearrange, ← Real.rpow_add hγ_pos, ← Real.rpow_add hγ_pos]
  calc ‖ZD.riemannXi s‖
      ≤ (|γ|^2 * (C_Γ * |γ|^((σ - 1)/2) * Real.exp (-Real.pi * |γ| / 4))) *
          (C_ζ * |γ|^N_ζ) := h_bound
    _ = C_Γ * C_ζ * |γ|^(2 + (σ - 1)/2 + N_ζ) * Real.exp (-Real.pi * |γ| / 4) := h_eq

/-- **Zero-sum convergence (conditional target).** The classical Σ_ρ 1/|ρ|²
over nontrivial zeros converges via the zero density N(T) ~ (T/2π)·log(T).
Mathlib does not currently package N(T). This named target abstracts that
gap. -/
def nontrivialZeros_inv_sq_summable_target : Prop :=
  Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
    1 / Complex.normSq (ρ.val * (ρ.val - 1)))

#print axioms gamma_half_vertical_decay
#print axioms riemannXi_normSq_tail_bound_of_decay
#print axioms Gammaℝ_vertical_decay
#print axioms riemannXi_vertical_decay_of_zetaBound

end ZD

end
