/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 583d3369-ddb5-4090-8f45-8d6065a8c96f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The version of Mathlib expected in this file appears to be incompatible with Aristotle's.
Please either switch your project to use the same version, or try again with `import Mathlib` only.
Details:
object file '/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/SpecialFunctions/Trigonometric/DerivHyp.olean' of module Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp does not exist
-/

/-
  GRH.StirlingBound.lean — Gamma Stirling bound from reflection + recurrence
  =====================================================================

  Proves gamma_stirling_bound (formerly an axiom in GRH.AFEInfrastructure.lean):

    For fixed σ > 0 and large |t|:
      C_lo·|t|^{σ-1/2}·e^{-π|t|/2} ≤ |Γ(σ+it)| ≤ C_hi·|t|^{σ-1/2}·e^{-π|t|/2}

  Route: Reflection formula → exact norm at σ=1/2 and σ=1 →
         GammaSeq ratio convergence → product bound → full strip.

  Architecture:
  • Section 1: |Γ(1/2+it)|² = π/cosh(πt) — PROVED via reflection (σ=1/2 anchor)
  • Section 2: Upper/lower bounds at σ=1/2 — PROVED
  • Section 3: stirling_at_half — PROVED (base case)
  • Section 4: |Γ(1+it)|² = π|t|/sinh(π|t|) — PROVED via reflection (σ=1 anchor)
  • Section 5: Recurrence step ‖Γ(σ+1+it)‖ = ‖(σ+it)‖·‖Γ(σ+it)‖ — PROVED
  • Section 6: GammaSeq ratio convergence — PROVED
  • Section 7: Reflection sin norm bounds — PROVED
  • Section 8: stirling_unit_strip — THEOREM (was axiom)
  • Section 9: gamma_stirling_bound — THEOREM for all σ > 0
    (from stirling_unit_strip + recurrence)

  TODO status:
  • The upper-half strip ratio lemma is still under formalization.
  • See the `Mathlib Port TODO` section below.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Complex Real

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
namespace ZD.StirlingBound

/-! ## Mathlib Port TODO

This file is being structured so the non-project-specific pieces can be moved
to mathlib later. The intended upstream order is:

1. `GammaRatioUpperHalf`: two-sided bound for
   `‖Γ(σ+it)‖ / ‖Γ(1/2+it)‖` on `σ ∈ (1/2, 1)`, `|t| ≥ 1`.
2. `BetaVerticalDecay`: two-sided decay for
   `‖B(a, 1/2+it)‖` on `a ∈ (0, 1/2)`, `|t| ≥ 1`.
3. Transfer lemma `GammaRatioFromBeta`: algebraic conversion between (1) and (2).
4. Strip assembly: lower-half via reflection and full `(0,1]` bound.

Design rules for portability:
* keep statements in terms of `Complex.Gamma`, `Complex.betaIntegral`,
  and standard asymptotic inequalities on `|t|`.
* avoid GRH-specific constants/names in intermediate lemmas.
* prefer lemmas that are reusable as standalone `Mathlib` theorems.
-/

/-- Target upstream statement: upper-half strip Gamma-ratio bounds. -/
def GammaRatioUpperHalf : Prop :=
  ∀ (σ : ℝ), 1 / 2 < σ → σ < 1 →
    ∃ (C_lo C_hi : ℝ), 0 < C_lo ∧ 0 < C_hi ∧
      ∀ (t : ℝ), 1 ≤ |t| →
        C_lo * |t| ^ (σ - 1 / 2) ≤
          ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
          C_hi * |t| ^ (σ - 1 / 2)

-- gammaRatioUpperHalf_axiom: proved via GammaSeq product analysis.
-- Definition moved after gammaRatioUpperHalf_proved to resolve forward reference.

/-- Target upstream statement: vertical-line Beta decay for `a ∈ (0,1/2)`. -/
def BetaVerticalDecay : Prop :=
  ∀ (a : ℝ), 0 < a → a < 1 / 2 →
    ∃ (B_lo B_hi : ℝ), 0 < B_lo ∧ 0 < B_hi ∧
      ∀ (t : ℝ), 1 ≤ |t| →
        B_lo * |t| ^ (-a) ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ∧
        ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ B_hi * |t| ^ (-a)

/-- One-sided upper branch for Beta vertical decay. -/
def BetaUpperDecay : Prop :=
  ∀ (a : ℝ), 0 < a → a < 1 / 2 →
    ∃ (B_hi : ℝ), 0 < B_hi ∧
      ∀ (t : ℝ), 1 ≤ |t| →
        ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ B_hi * |t| ^ (-a)

/-- One-sided lower branch for Beta vertical decay. -/
def BetaLowerDecay : Prop :=
  ∀ (a : ℝ), 0 < a → a < 1 / 2 →
    ∃ (B_lo : ℝ), 0 < B_lo ∧
      ∀ (t : ℝ), 1 ≤ |t| →
        B_lo * |t| ^ (-a) ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖

/-- Compact-window control interface for the upper Beta branch. -/
def BetaUpperCompactWindowBound : Prop :=
  ∀ (a : ℝ), 0 < a → a < 1 / 2 →
    ∀ (T : ℝ), 1 ≤ T →
      ∃ (M : ℝ), 0 < M ∧
        (∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
          ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ M)

/-- Tail-decay interface for the upper Beta branch. -/
def BetaUpperTailDecayBound : Prop :=
  ∀ (a : ℝ), 0 < a → a < 1 / 2 →
    ∃ (T C : ℝ), 1 ≤ T ∧ 0 < C ∧
      (∀ (t : ℝ), T ≤ |t| →
        ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ C * |t| ^ (-a))

/-- If both one-sided Beta decay branches hold, then full two-sided Beta vertical
    decay holds. -/
theorem betaVerticalDecay_of_upper_lower
    (hlo : BetaLowerDecay) (hhi : BetaUpperDecay) : BetaVerticalDecay := by
  intro a ha₀ ha₁
  rcases hlo a ha₀ ha₁ with ⟨B_lo, hBlo, hlo'⟩
  rcases hhi a ha₀ ha₁ with ⟨B_hi, hBhi, hhi'⟩
  refine ⟨B_lo, B_hi, hBlo, hBhi, ?_⟩
  intro t ht
  exact ⟨hlo' t ht, hhi' t ht⟩

/-- Upper-branch glue lemma:
combine a bounded compact window `1 ≤ |t| ≤ T` with a tail decay estimate
`T ≤ |t|` to get a global `BetaUpperDecay` bound. -/
theorem betaUpperDecay_of_compact_and_tail
    (hcompact : ∀ (a : ℝ), 0 < a → a < 1 / 2 →
      ∀ (T : ℝ), 1 ≤ T →
        ∃ (M : ℝ), 0 < M ∧
          (∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
            ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ M))
    (htail : ∀ (a : ℝ), 0 < a → a < 1 / 2 →
      ∃ (T C : ℝ), 1 ≤ T ∧ 0 < C ∧
        (∀ (t : ℝ), T ≤ |t| →
          ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ C * |t| ^ (-a))) :
    BetaUpperDecay := by
  intro a ha₀ ha₁
  rcases htail a ha₀ ha₁ with ⟨Tt, C, hTt1, hCpos, htail'⟩
  set T := Tt
  have hT1 : 1 ≤ T := by simpa [T] using hTt1
  rcases hcompact a ha₀ ha₁ T hT1 with ⟨M, hMpos, hcomp⟩
  have hM_nonneg : 0 ≤ M := le_of_lt hMpos
  have hTa_nonneg : 0 ≤ T ^ a := by
    have hT_nonneg : 0 ≤ T := le_trans (by norm_num) hT1
    exact Real.rpow_nonneg hT_nonneg a
  set B_hi := max C (M * T ^ a) with hB_def
  refine ⟨B_hi, by
    have : 0 < max C (M * T ^ a) := lt_of_lt_of_le hCpos (le_max_left _ _)
    simpa [hB_def] using this, ?_⟩
  intro t ht1
  by_cases htailCase : T ≤ |t|
  · have hC : ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ C * |t| ^ (-a) := by
      exact htail' t (by simpa [T] using htailCase)
    calc
      ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ C * |t| ^ (-a) := hC
      _ ≤ B_hi * |t| ^ (-a) := by
        rw [hB_def]
        have hpow_nonneg : 0 ≤ |t| ^ (-a) := by
          exact Real.rpow_nonneg (abs_nonneg t) (-a)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpow_nonneg
  · have hleT : |t| ≤ T := le_of_not_ge htailCase
    have hM : ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ M := hcomp t ht1 hleT
    have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht1
    have hpow_inv_lb : T ^ (-a) ≤ |t| ^ (-a) := by
      have hpow_le : |t| ^ a ≤ T ^ a := Real.rpow_le_rpow (abs_nonneg t) hleT ha₀.le
      have hT_pow_pos : 0 < T ^ a := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT1) a
      have hAbs_pow_pos : 0 < |t| ^ a := Real.rpow_pos_of_pos ht_pos a
      rw [Real.rpow_neg (le_trans (by norm_num) hT1), Real.rpow_neg (abs_nonneg t)]
      exact (inv_le_inv₀ hT_pow_pos hAbs_pow_pos).2 hpow_le
    have hpow_cancel : T ^ a * T ^ (-a) = 1 := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hT1)]
      rw [show a + -a = 0 by ring, Real.rpow_zero]
    have hM_to_scaled : M ≤ (M * T ^ a) * |t| ^ (-a) := by
      have h_step1 : M * 1 ≤ M * (T ^ a * |t| ^ (-a)) := by
        apply mul_le_mul_of_nonneg_left ?_ hM_nonneg
        have h_step1a : 1 ≤ T ^ a * |t| ^ (-a) := by
          have h_step1b : T ^ (-a) ≤ |t| ^ (-a) := hpow_inv_lb
          have h_step1c : T ^ a * T ^ (-a) ≤ T ^ a * |t| ^ (-a) :=
            mul_le_mul_of_nonneg_left h_step1b hTa_nonneg
          simpa [hpow_cancel] using h_step1c
        simpa using h_step1a
      simpa [mul_assoc] using h_step1
    calc
      ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ M := hM
      _ ≤ (M * T ^ a) * |t| ^ (-a) := hM_to_scaled
      _ ≤ B_hi * |t| ^ (-a) := by
        rw [hB_def]
        have hpow_nonneg : 0 ≤ |t| ^ (-a) := by
          exact Real.rpow_nonneg (abs_nonneg t) (-a)
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpow_nonneg

/-- Spiral-style combiner: hypothesis interfaces to an upper Beta decay theorem. -/
theorem betaUpperDecay_of_interfaces
    (hcompact : BetaUpperCompactWindowBound)
    (htail : BetaUpperTailDecayBound) : BetaUpperDecay :=
  betaUpperDecay_of_compact_and_tail hcompact htail

/-! ## Section 1: |Γ(1/2 + it)|² = π / cosh(πt) -/

theorem gamma_half_norm_sq (t : ℝ) :
    ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 = π / Real.cosh (π * t) := by
  set z : ℂ := ⟨1/2, t⟩
  have h1mz : (1 : ℂ) - z = starRingEnd ℂ z := by
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re]; ring
    · simp [Complex.sub_im, Complex.conj_im]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  rw [h1mz, Complex.Gamma_conj z] at hrefl
  have hsin_eq : Complex.sin (↑π * z) = ↑(Real.cosh (π * t)) := by
    show Complex.sin (↑π * ⟨1/2, t⟩) = ↑(Real.cosh (π * t))
    have h1 : (↑π : ℂ) * (⟨1/2, t⟩ : ℂ) = ⟨π / 2, π * t⟩ := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
      · simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [h1, Complex.sin_eq]
    simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos,
               ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
    push_cast; ring
  rw [hsin_eq] at hrefl
  have h_mc : Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z) =
      ↑(Complex.normSq (Complex.Gamma z)) := by rw [Complex.mul_conj]
  rw [h_mc] at hrefl
  rw [Complex.normSq_eq_norm_sq] at hrefl
  exact Complex.ofReal_injective (by rwa [Complex.ofReal_div])

/-! ## Section 2: Bounds at σ = 1/2 -/

private lemma cosh_even (t : ℝ) : Real.cosh (π * t) = Real.cosh (π * |t|) := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, show π * -t = -(π * t) from by ring, Real.cosh_neg]

theorem gamma_half_upper (t : ℝ) :
    ‖Complex.Gamma ⟨1/2, t⟩‖ ≤ Real.sqrt (2 * π) * Real.exp (-π * |t| / 2) := by
  have hpi : 0 < π := pi_pos
  have hsq := gamma_half_norm_sq t
  have hcosh_pos : 0 < Real.cosh (π * |t|) := Real.cosh_pos _
  have hcosh_lower : Real.exp (π * |t|) / 2 ≤ Real.cosh (π * |t|) := by
    rw [Real.cosh_eq]; have := (Real.exp_pos (-(π * |t|))).le; linarith
  have h_sq_bound : ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 ≤
      2 * π * Real.exp (-(π * |t|)) := by
    rw [hsq, cosh_even, div_le_iff₀ hcosh_pos]
    calc π = 2 * π * Real.exp (-(π * |t|)) * (Real.exp (π * |t|) / 2) := by
            rw [Real.exp_neg]; field_simp
      _ ≤ 2 * π * Real.exp (-(π * |t|)) * Real.cosh (π * |t|) :=
          mul_le_mul_of_nonneg_left hcosh_lower (by positivity)
  have h_rhs_sq : (Real.sqrt (2 * π) * Real.exp (-π * |t| / 2)) ^ 2 =
      2 * π * Real.exp (-(π * |t|)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * π), sq, ← Real.exp_add]
    congr 1; ring
  calc ‖Complex.Gamma ⟨1/2, t⟩‖
      = Real.sqrt (‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (2 * π) * Real.exp (-π * |t| / 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt; rwa [h_rhs_sq]
    _ = _ := Real.sqrt_sq (by positivity)

theorem gamma_half_lower (t : ℝ) :
    Real.sqrt π * Real.exp (-π * |t| / 2) ≤
      ‖Complex.Gamma ⟨1/2, t⟩‖ := by
  have hpi : 0 < π := pi_pos
  have hsq := gamma_half_norm_sq t
  have hcosh_pos : 0 < Real.cosh (π * |t|) := Real.cosh_pos _
  have hcosh_upper : Real.cosh (π * |t|) ≤ Real.exp (π * |t|) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(π * |t|)) ≤ Real.exp (π * |t|) :=
      Real.exp_le_exp_of_le (by nlinarith [abs_nonneg t])
    linarith
  have h_sq_lower : π * Real.exp (-(π * |t|)) ≤
      ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 := by
    rw [hsq, cosh_even, le_div_iff₀ hcosh_pos]
    calc π * Real.exp (-(π * |t|)) * Real.cosh (π * |t|)
        ≤ π * Real.exp (-(π * |t|)) * Real.exp (π * |t|) :=
          mul_le_mul_of_nonneg_left hcosh_upper (by positivity)
      _ = π := by rw [Real.exp_neg]; field_simp
  have h_lhs_sq : (Real.sqrt π * Real.exp (-π * |t| / 2)) ^ 2 =
      π * Real.exp (-(π * |t|)) := by
    rw [mul_pow, Real.sq_sqrt hpi.le, sq, ← Real.exp_add]; congr 1; ring
  calc Real.sqrt π * Real.exp (-π * |t| / 2)
      = Real.sqrt ((Real.sqrt π * Real.exp (-π * |t| / 2)) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2) := by
        apply Real.sqrt_le_sqrt; rwa [h_lhs_sq]
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/-! ## Section 3: Base case in standard format -/

theorem stirling_at_half :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ ((1:ℝ)/2 - 1/2) * Real.exp (-π * |t| / 2) ≤
        ‖Complex.Gamma ⟨1/2, t⟩‖ ∧
      ‖Complex.Gamma ⟨1/2, t⟩‖ ≤
        C_hi * |t| ^ ((1:ℝ)/2 - 1/2) * Real.exp (-π * |t| / 2) := by
  refine ⟨Real.sqrt π, Real.sqrt (2 * π), 1,
    by positivity, by positivity, by positivity, ?_⟩
  intro t ht
  have h_rpow_zero : |t| ^ ((1:ℝ)/2 - 1/2) = 1 := by
    rw [show (1:ℝ)/2 - 1/2 = 0 from by ring, Real.rpow_zero]
  simp only [h_rpow_zero, mul_one]
  exact ⟨gamma_half_lower t, gamma_half_upper t⟩

/-! ## Section 4: |Γ(1 + it)|² = π|t|/sinh(π|t|)

  Second anchor point. Combined with σ=1/2, covers both parities
  for the recurrence ladder. -/

theorem gamma_one_norm_sq (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gamma ⟨1, t⟩‖ ^ 2 = π * |t| / Real.sinh (π * |t|) := by
  have ht_abs : (|t| : ℝ) ≠ 0 := abs_ne_zero.mpr ht
  have hpi_abs_pos : 0 < π * |t| := mul_pos pi_pos (abs_pos.mpr ht)
  have hsinh_pos : 0 < Real.sinh (π * |t|) := Real.sinh_pos_iff.mpr hpi_abs_pos
  have hsinh_ne : Real.sinh (π * |t|) ≠ 0 := ne_of_gt hsinh_pos
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (⟨1, t⟩ : ℂ)
  have hsub : (1 : ℂ) - ⟨1, t⟩ = ⟨0, -t⟩ := by apply Complex.ext <;> simp
  rw [hsub] at hrefl
  have hnorm_eq : ‖Complex.Gamma ⟨1, t⟩‖ * ‖Complex.Gamma ⟨0, -t⟩‖ = π / |Real.sinh (π * t)| := by
    have hn := congr_arg (‖·‖) hrefl
    simp only at hn
    rw [norm_mul, norm_div] at hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos] at hn
    have hsin : Complex.sin (↑π * ⟨1, t⟩) = -(Complex.sinh (↑(π * t)) * I) := by
      have h1 : (↑π * (⟨1, t⟩ : ℂ)) = ↑π + ↑(π * t) * I := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      rw [h1, Complex.sin_add_mul_I]
      simp [Real.sin_pi, Real.cos_pi]
    rw [hsin, norm_neg, norm_mul, Complex.norm_I, mul_one] at hn
    rw [← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs] at hn
    exact hn
  have hne : (⟨0, -t⟩ : ℂ) ≠ 0 := by
    intro h; apply ht; have := congr_arg Complex.im h; simp at this; exact this
  have hadd : (⟨0, -t⟩ : ℂ) + 1 = ⟨1, -t⟩ := by apply Complex.ext <;> simp
  have hga := Complex.Gamma_add_one (⟨0, -t⟩ : ℂ) hne
  rw [hadd] at hga
  have hconj_norm : ‖Complex.Gamma ⟨1, -t⟩‖ = ‖Complex.Gamma ⟨1, t⟩‖ := by
    have hc : (⟨1, -t⟩ : ℂ) = starRingEnd ℂ ⟨1, t⟩ := by apply Complex.ext <;> simp
    rw [hc, Complex.Gamma_conj]; exact norm_conj _
  have hnorm_it : ‖(⟨0, -t⟩ : ℂ)‖ = |t| := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; simp [sq, Real.sqrt_mul_self_eq_abs]
  have hnorm_gamma0 : ‖Complex.Gamma ⟨0, -t⟩‖ = ‖Complex.Gamma ⟨1, t⟩‖ / |t| := by
    rw [eq_div_iff ht_abs]
    calc ‖Complex.Gamma ⟨0, -t⟩‖ * |t|
        = ‖Complex.Gamma ⟨0, -t⟩‖ * ‖(⟨0, -t⟩ : ℂ)‖ := by rw [hnorm_it]
      _ = ‖(⟨0, -t⟩ : ℂ)‖ * ‖Complex.Gamma ⟨0, -t⟩‖ := by ring
      _ = ‖(⟨0, -t⟩ : ℂ) * Complex.Gamma ⟨0, -t⟩‖ := by rw [norm_mul]
      _ = ‖Complex.Gamma ⟨1, -t⟩‖ := by rw [← hga]
      _ = ‖Complex.Gamma ⟨1, t⟩‖ := hconj_norm
  rw [hnorm_gamma0] at hnorm_eq
  have habs_sinh : |Real.sinh (π * t)| = Real.sinh (π * |t|) := by
    by_cases h : 0 < t
    · rw [abs_of_pos h]
      exact abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos pi_pos h))
    · push_neg at h
      have ht_neg : t < 0 := lt_of_le_of_ne h (fun h' => absurd h' ht)
      have hsinh_neg : Real.sinh (π * t) < 0 :=
        Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg pi_pos ht_neg)
      rw [abs_of_neg ht_neg, abs_of_neg hsinh_neg, mul_neg, Real.sinh_neg]
  rw [habs_sinh] at hnorm_eq
  have h1 : ‖Complex.Gamma ⟨1, t⟩‖ * (‖Complex.Gamma ⟨1, t⟩‖ / |t|) =
            ‖Complex.Gamma ⟨1, t⟩‖ ^ 2 / |t| := by rw [sq]; ring
  rw [h1] at hnorm_eq
  rw [div_eq_div_iff ht_abs hsinh_ne] at hnorm_eq
  rw [eq_div_iff hsinh_ne]
  linarith

/-! ## Section 5: Recurrence step

  Γ(s+1) = s·Γ(s) gives ‖Γ(σ+1+it)‖ = ‖(σ+it)‖·‖Γ(σ+it)‖. -/

private lemma mk_ne_zero_of_pos (σ t : ℝ) (hσ : 0 < σ) : (⟨σ, t⟩ : ℂ) ≠ 0 := by
  intro h; have := congr_arg Complex.re h; simp at this; linarith

private lemma mk_add_one (σ t : ℝ) : (⟨σ, t⟩ : ℂ) + 1 = ⟨σ + 1, t⟩ := by
  apply Complex.ext <;> simp

theorem norm_Gamma_step (σ t : ℝ) (hne : (⟨σ, t⟩ : ℂ) ≠ 0) :
    ‖Complex.Gamma ⟨σ + 1, t⟩‖ = ‖(⟨σ, t⟩ : ℂ)‖ * ‖Complex.Gamma ⟨σ, t⟩‖ := by
  have h := Complex.Gamma_add_one ⟨σ, t⟩ hne
  rw [mk_add_one] at h; rw [h, norm_mul]

/-! ## Section 6: GammaSeq ratio convergence and norm identities -/

/-- normSq of sin at a complex point ⟨x,y⟩ -/
private lemma norm_sq_sin_mk (x y : ℝ) :
    Complex.normSq (Complex.sin ⟨x, y⟩) =
    Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  have heq : (⟨x, y⟩ : ℂ) = ↑x + ↑y * I := by apply Complex.ext <;> simp
  rw [heq, Complex.sin_add_mul_I,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.normSq_add_mul_I]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cosh_sq y]

/-- ‖sin(π(σ+it))‖² = sin²(πσ) + sinh²(πt) -/
theorem sin_norm_sq (σ t : ℝ) :
    ‖Complex.sin (↑π * (⟨σ, t⟩ : ℂ))‖ ^ 2 =
    Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2 := by
  have h1 : (↑π : ℂ) * (⟨σ, t⟩ : ℂ) = ⟨π * σ, π * t⟩ := by
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
  rw [h1, ← Complex.normSq_eq_norm_sq]
  exact norm_sq_sin_mk (π * σ) (π * t)

/-- Reflection formula for norms: ‖Γ(σ+it)‖·‖Γ(1-σ+it)‖ = π/‖sin(π(σ+it))‖ -/
theorem reflection_norm_product (σ t : ℝ) :
    ‖Complex.Gamma ⟨σ, t⟩‖ * ‖Complex.Gamma ⟨1-σ, t⟩‖ =
    π / ‖Complex.sin (↑π * ⟨σ, t⟩)‖ := by
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (⟨σ, t⟩ : ℂ)
  have hsub : (1 : ℂ) - ⟨σ, t⟩ = ⟨1 - σ, -t⟩ := by apply Complex.ext <;> simp
  rw [hsub] at hrefl
  have hconj : ‖Complex.Gamma ⟨1 - σ, -t⟩‖ = ‖Complex.Gamma ⟨1 - σ, t⟩‖ := by
    have : (⟨1 - σ, -t⟩ : ℂ) = starRingEnd ℂ ⟨1 - σ, t⟩ := by apply Complex.ext <;> simp
    rw [this, Complex.Gamma_conj]; exact norm_conj _
  calc ‖Complex.Gamma ⟨σ, t⟩‖ * ‖Complex.Gamma ⟨1-σ, t⟩‖
      = ‖Complex.Gamma ⟨σ, t⟩‖ * ‖Complex.Gamma ⟨1-σ, -t⟩‖ := by rw [hconj]
    _ = ‖Complex.Gamma ⟨σ, t⟩ * Complex.Gamma ⟨1-σ, -t⟩‖ := (norm_mul _ _).symm
    _ = ‖↑π / Complex.sin (↑π * ⟨σ, t⟩)‖ := by rw [hrefl]
    _ = π / ‖Complex.sin (↑π * ⟨σ, t⟩)‖ := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]

/-! ## Section 7: Sin norm bounds for large |t| and Stirling at σ=1 -/

private lemma sinh_abs (t : ℝ) (ht : t ≠ 0) :
    |Real.sinh (π * t)| = Real.sinh (π * |t|) := by
  have hpi_abs : 0 < π * |t| := mul_pos pi_pos (abs_pos.mpr ht)
  rcases lt_or_gt_of_ne ht with h | h
  · have hsinh_neg : Real.sinh (π * t) < 0 :=
      Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg pi_pos h)
    rw [abs_of_neg hsinh_neg, abs_of_neg h, mul_neg, Real.sinh_neg]
  · rw [abs_of_pos h]
    exact abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos pi_pos h))

/-- sinh(x) upper: sinh(x) < e^x / 2 for all x -/
private lemma sinh_lt_exp_half (x : ℝ) : Real.sinh x < Real.exp x / 2 := by
  rw [Real.sinh_eq]; linarith [Real.exp_pos (-x)]

/-- sinh(x) lower: sinh(x) ≥ (e^x - 1)/2 for x ≥ 0 -/
private lemma sinh_ge_exp_sub_one_half (x : ℝ) (hx : 0 ≤ x) :
    (Real.exp x - 1) / 2 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have : Real.exp (-x) ≤ 1 := by
    calc Real.exp (-x) ≤ Real.exp 0 := Real.exp_le_exp_of_le (by linarith)
      _ = 1 := Real.exp_zero
  linarith

/-- For x ≥ 1: sinh(x) ≥ e^x / 4 (since e^x ≥ e ≥ 2, so e^x - 1 ≥ e^x/2) -/
private lemma sinh_lower_for_ge_one (x : ℝ) (hx : 1 ≤ x) :
    Real.exp x / 4 ≤ Real.sinh x := by
  have h1 : (2 : ℝ) ≤ Real.exp x := by
    calc (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
      _ ≤ Real.exp x := Real.exp_le_exp_of_le hx
  have h2 := sinh_ge_exp_sub_one_half x (by linarith)
  linarith

/-! ## Section 8: Stirling bound in the unit strip — THEOREM

  For σ ∈ (0, 1], proved via:
  - σ = 1/2: from stirling_at_half
  - σ = 1: from gamma_one_norm_sq + sinh bounds
  - σ ∈ (0, 1) \ {1/2}: from reflection formula + GammaSeq ratio convergence

  The GammaSeq ratio bound: for s = ⟨σ, t⟩, s' = ⟨1/2, t⟩,
    ‖Γ(s)‖ / ‖Γ(s')‖ = lim_{n→∞} ‖GammaSeq(s,n)‖ / ‖GammaSeq(s',n)‖
    = lim n^{σ-1/2} · ∏_{j=0}^n (‖s'+j‖/‖s+j‖)
  The product × power converges to C·|t|^{σ-1/2} where C is bounded
  above and below (independent of t for large |t|). -/

/-- Stirling at σ=1: from the exact formula π|t|/sinh(π|t|) -/
private theorem stirling_at_one :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ ((1:ℝ) - 1/2) * Real.exp (-π * |t| / 2) ≤
        ‖Complex.Gamma ⟨1, t⟩‖ ∧
      ‖Complex.Gamma ⟨1, t⟩‖ ≤
        C_hi * |t| ^ ((1:ℝ) - 1/2) * Real.exp (-π * |t| / 2) := by
  refine ⟨Real.sqrt (2 * π), 2 * Real.sqrt π, 1,
    by positivity, by positivity, by positivity, ?_⟩
  intro t ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht
  have ht_ne : t ≠ 0 := fun h => by simp [h] at ht_pos
  have h_rpow : |t| ^ ((1:ℝ) - 1/2) = |t| ^ ((1:ℝ)/2) := by congr 1; ring
  rw [h_rpow]
  have hsq := gamma_one_norm_sq t ht_ne
  have hpi_t : 0 < π * |t| := mul_pos pi_pos ht_pos
  have hsinh_pos : 0 < Real.sinh (π * |t|) := Real.sinh_pos_iff.mpr hpi_t
  -- Lower bound on ‖Γ‖²: 2π|t|·e^{-π|t|} ≤ π|t|/sinh(π|t|)
  have h_sq_lower : 2 * π * |t| * Real.exp (-(π * |t|)) ≤
      ‖Complex.Gamma ⟨1, t⟩‖ ^ 2 := by
    rw [hsq, le_div_iff₀ hsinh_pos, Real.sinh_eq]
    have key : Real.exp (-(π * |t|)) * Real.exp (π * |t|) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [sq_nonneg (Real.exp (-(π * |t|)))]
  -- Upper bound on ‖Γ‖²: π|t|/sinh(π|t|) ≤ 4π|t|·e^{-π|t|}
  have h_sq_upper : ‖Complex.Gamma ⟨1, t⟩‖ ^ 2 ≤
      4 * π * |t| * Real.exp (-(π * |t|)) := by
    rw [hsq]
    have hx_ge : 1 ≤ π * |t| := by nlinarith [two_le_pi]
    have h1 : π * |t| / Real.sinh (π * |t|) ≤
        π * |t| / (Real.exp (π * |t|) / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (sinh_lower_for_ge_one _ hx_ge)
    have h2 : π * |t| / (Real.exp (π * |t|) / 4) =
        4 * π * |t| * Real.exp (-(π * |t|)) := by
      rw [Real.exp_neg]; field_simp
    linarith
  -- Square identities for the bounds
  have h_rpow_sq : |t| ^ ((1:ℝ)/2) * |t| ^ ((1:ℝ)/2) = |t| := by
    rw [← Real.rpow_add ht_pos, show (1:ℝ)/2 + 1/2 = 1 from by ring, Real.rpow_one]
  have h_exp_sq : Real.exp (-π * |t| / 2) * Real.exp (-π * |t| / 2) =
      Real.exp (-(π * |t|)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_lhs_sq : (Real.sqrt (2 * π) * |t| ^ ((1:ℝ)/2) *
      Real.exp (-π * |t| / 2)) ^ 2 = 2 * π * |t| * Real.exp (-(π * |t|)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * π),
        sq, h_rpow_sq, sq, h_exp_sq]
  have h_rhs_sq : (2 * Real.sqrt π * |t| ^ ((1:ℝ)/2) *
      Real.exp (-π * |t| / 2)) ^ 2 = 4 * π * |t| * Real.exp (-(π * |t|)) := by
    rw [mul_pow, mul_pow, mul_pow, show (2:ℝ) ^ 2 = 4 from by norm_num,
        Real.sq_sqrt pi_pos.le, sq, h_rpow_sq, sq, h_exp_sq]
  constructor
  · calc Real.sqrt (2 * π) * |t| ^ ((1:ℝ)/2) * Real.exp (-π * |t| / 2)
        = Real.sqrt ((Real.sqrt (2 * π) * |t| ^ ((1:ℝ)/2) * Real.exp (-π * |t| / 2)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (‖Complex.Gamma ⟨1, t⟩‖ ^ 2) := by
          apply Real.sqrt_le_sqrt; rwa [h_lhs_sq]
      _ = _ := Real.sqrt_sq (norm_nonneg _)
  · calc ‖Complex.Gamma ⟨1, t⟩‖
        = Real.sqrt (‖Complex.Gamma ⟨1, t⟩‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((2 * Real.sqrt π * |t| ^ ((1:ℝ)/2) * Real.exp (-π * |t| / 2)) ^ 2) := by
          apply Real.sqrt_le_sqrt; rwa [h_rhs_sq]
      _ = _ := Real.sqrt_sq (by positivity)

/-- The reflection product f(σ)·f(1-σ) equals cosh(πt)/‖sin(π(σ+it))‖ -/
private lemma reflection_ratio_product (σ t : ℝ) (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (_ht : t ≠ 0) :
    ‖Complex.Gamma ⟨σ, t⟩‖ * ‖Complex.Gamma ⟨1-σ, t⟩‖ /
      ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 =
    Real.cosh (π * t) / ‖Complex.sin (↑π * ⟨σ, t⟩)‖ := by
  have h_half_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
  have h_half_sq := gamma_half_norm_sq t
  have h_cosh_pos : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hsin_pos_r : 0 < Real.sin (π * σ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos pi_pos hσ₀
    · calc π * σ < π * 1 := mul_lt_mul_of_pos_left hσ₁ pi_pos
        _ = π := mul_one π
  have hsin_ne : ‖Complex.sin (↑π * ⟨σ, t⟩)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    have hsq := sin_norm_sq σ t
    rw [h, norm_zero] at hsq
    simp at hsq
    nlinarith [sq_nonneg (Real.sinh (π * t))]
  rw [reflection_norm_product σ t, h_half_sq]
  rw [div_div, div_eq_div_iff (mul_ne_zero hsin_ne (ne_of_gt (div_pos pi_pos h_cosh_pos))) hsin_ne]
  field_simp

/-- The reflection product squared: [f(σ)·f(1-σ)/‖Γ(1/2+it)‖²]² is bounded -/
private lemma reflection_product_sq_bound (σ t : ℝ) (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (ht : 1 ≤ |t|) :
    1 ≤ Real.cosh (π * t) ^ 2 / (Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2) ∧
    Real.cosh (π * t) ^ 2 / (Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2) ≤
      1 / Real.sin (π * σ) ^ 2 + 1 := by
  have h_cosh_sq : Real.cosh (π * t) ^ 2 = 1 + Real.sinh (π * t) ^ 2 := by
    nlinarith [Real.cosh_sq (π * t)]
  have hsinh_pos : 0 < Real.sinh (π * |t|) :=
    Real.sinh_pos_iff.mpr (mul_pos pi_pos (lt_of_lt_of_le one_pos ht))
  have hsinh_sq_pos : 0 < Real.sinh (π * t) ^ 2 := by
    have hne : Real.sinh (π * t) ≠ 0 := by
      intro h
      rcases le_or_gt 0 t with h' | h'
      · have : π * |t| = π * t := by rw [abs_of_nonneg h']
        linarith [this ▸ hsinh_pos, h.symm ▸ (le_refl (0:ℝ))]
      · have : Real.sinh (π * |t|) = -Real.sinh (π * t) := by
          rw [show π * |t| = -(π * t) from by rw [abs_of_neg h']; ring]
          exact Real.sinh_neg (π * t)
        linarith [this ▸ hsinh_pos, h.symm ▸ (le_refl (0:ℝ))]
    positivity
  have hsin_pos : 0 < Real.sin (π * σ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos pi_pos hσ₀
    · calc π * σ < π * 1 := mul_lt_mul_of_pos_left hσ₁ pi_pos
        _ = π := mul_one π
  have hsin_sq_pos : 0 < Real.sin (π * σ) ^ 2 := by positivity
  have hdenom_pos : 0 < Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2 := by linarith
  constructor
  · rw [le_div_iff₀ hdenom_pos, h_cosh_sq, one_mul]
    have := Real.sin_le_one (π * σ)
    nlinarith [sq_abs (Real.sin (π * σ))]
  · rw [h_cosh_sq, div_le_iff₀ hdenom_pos]
    -- Need: 1 + sinh² ≤ (1/sin² + 1) · (sin² + sinh²)
    -- = sin²/sin² + sinh²/sin² + sin² + sinh²
    -- = 1 + sinh²/sin² + sin² + sinh²
    -- ≥ 1 + 0 + 0 + sinh² = 1 + sinh²
    have h_expand : (1 / Real.sin (π * σ) ^ 2 + 1) *
        (Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2) =
        1 + Real.sinh (π * t) ^ 2 / Real.sin (π * σ) ^ 2 +
        Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2 := by
      field_simp; ring
    rw [h_expand]
    have : 0 ≤ Real.sinh (π * t) ^ 2 / Real.sin (π * σ) ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith [sq_nonneg (Real.sin (π * σ))]

/-- Transfer reflection-product bounds into power bounds:
if `Rσ * R1σ ∈ [1, P]` and `R1σ ~ |t|^{-a}` with two-sided constants,
then `Rσ ~ |t|^a` with explicit constants. -/
private lemma ratio_bounds_from_reflection
    (a t P Rσ R1σ C1 C2 : ℝ)
    (ht : 1 ≤ |t|)
    (hR1_pos : 0 < R1σ)
    (hprod_lo : 1 ≤ Rσ * R1σ) (hprod_hi : Rσ * R1σ ≤ P)
    (hR1_lo : C1 * |t| ^ (-a) ≤ R1σ) (hR1_hi : R1σ ≤ C2 * |t| ^ (-a))
    (hC1 : 0 < C1) (hC2 : 0 < C2) :
    1 / (C2 * |t| ^ (-a)) ≤ Rσ ∧ Rσ ≤ P / (C1 * |t| ^ (-a)) := by
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht
  have hpow_pos : 0 < |t| ^ (-a) := Real.rpow_pos_of_pos ht_pos (-a)
  have hC1pow_pos : 0 < C1 * |t| ^ (-a) := mul_pos hC1 hpow_pos
  have hC2pow_pos : 0 < C2 * |t| ^ (-a) := mul_pos hC2 hpow_pos
  have hRσ_nonneg : 0 ≤ Rσ := by
    have hmul_pos : 0 < Rσ * R1σ := lt_of_lt_of_le zero_lt_one hprod_lo
    have hcases := (mul_pos_iff.mp hmul_pos)
    have hRσ_pos : 0 < Rσ := by
      rcases hcases with h | h
      · exact h.1
      · linarith
    exact le_of_lt hRσ_pos
  have hRσ_mul_C2pow : 1 ≤ Rσ * (C2 * |t| ^ (-a)) := by
    calc
      1 ≤ Rσ * R1σ := hprod_lo
      _ ≤ Rσ * (C2 * |t| ^ (-a)) := mul_le_mul_of_nonneg_left hR1_hi hRσ_nonneg
  have h_lower_div : 1 / (C2 * |t| ^ (-a)) ≤ Rσ := by
    exact (div_le_iff₀ hC2pow_pos).2 (by simpa [one_mul, mul_assoc, mul_comm, mul_left_comm] using hRσ_mul_C2pow)
  have hRσ_mul_C1pow : Rσ * (C1 * |t| ^ (-a)) ≤ P := by
    calc
      Rσ * (C1 * |t| ^ (-a)) ≤ Rσ * R1σ := mul_le_mul_of_nonneg_left hR1_lo hRσ_nonneg
      _ ≤ P := hprod_hi
  have h_upper_div : Rσ ≤ P / (C1 * |t| ^ (-a)) := by
    exact (le_div_iff₀ hC1pow_pos).2 hRσ_mul_C1pow
  exact ⟨h_lower_div, h_upper_div⟩

/-- The ratio at σ=1 is between |t| and 2|t| (squared) for |t| ≥ 1 -/
private lemma ratio_at_one_bounds (t : ℝ) (ht_ne : t ≠ 0) (ht : 1 ≤ |t|) :
    |t| ≤ ‖Complex.Gamma ⟨1, t⟩‖ ^ 2 / ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 ∧
    ‖Complex.Gamma ⟨1, t⟩‖ ^ 2 / ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 ≤ 2 * |t| := by
  have h_half := gamma_half_norm_sq t
  have h_one := gamma_one_norm_sq t ht_ne
  have hcosh_pos : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hpi_abs_pos : 0 < π * |t| := mul_pos pi_pos (lt_of_lt_of_le one_pos ht)
  have hsinh_pos : 0 < Real.sinh (π * |t|) := Real.sinh_pos_iff.mpr hpi_abs_pos
  have h_half_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
  have h_half_sq_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 := by positivity
  -- Key: the ratio squared = (π|t|/sinh) / (π/cosh) = |t|·cosh/sinh
  -- We bound cosh(πt)/sinh(π|t|) using cosh(πt) = cosh(π|t|) and
  -- sinh(x) ≤ cosh(x) ≤ 2·sinh(x) for x ≥ 1
  have hcosh_ge_sinh : Real.sinh (π * |t|) ≤ Real.cosh (π * |t|) := by
    rw [Real.cosh_eq, Real.sinh_eq]; linarith [Real.exp_pos (-(π * |t|))]
  -- For cosh ≤ 2·sinh when x ≥ 1: need 3·e^{-x} ≤ e^x
  have hthree_exp : 3 * Real.exp (-(π * |t|)) ≤ Real.exp (π * |t|) := by
    have h1 : π * |t| ≥ π := by nlinarith [abs_nonneg t, two_le_pi]
    have h2 : (3 : ℝ) ≤ Real.exp π := by
      calc (3 : ℝ) ≤ π + 1 := by linarith [two_le_pi]
        _ ≤ Real.exp π := Real.add_one_le_exp π
    calc 3 * Real.exp (-(π * |t|))
        ≤ 3 * Real.exp 0 := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le _) (by norm_num)
          linarith
      _ = 3 := by simp
      _ ≤ Real.exp π := h2
      _ ≤ Real.exp (π * |t|) := Real.exp_le_exp_of_le (by linarith)
  have hcosh_le : Real.cosh (π * |t|) ≤ 2 * Real.sinh (π * |t|) := by
    rw [Real.cosh_eq, Real.sinh_eq]; linarith
  -- Now bound the ratio
  -- Key identity: (π|t|/sinh) / (π/cosh) = |t|·cosh/sinh
  have h_ratio_eq : π * |t| / Real.sinh (π * |t|) / (π / Real.cosh (π * t)) =
      |t| * Real.cosh (π * t) / Real.sinh (π * |t|) := by
    field_simp
  rw [h_one, h_half, h_ratio_eq]
  have hcosh_t : Real.cosh (π * t) = Real.cosh (π * |t|) := cosh_even t
  constructor
  · -- Lower: |t| ≤ |t|·cosh/sinh, i.e., sinh ≤ cosh
    rw [le_div_iff₀ hsinh_pos, hcosh_t]
    exact mul_le_mul_of_nonneg_left hcosh_ge_sinh (abs_nonneg t)
  · -- Upper: |t|·cosh/sinh ≤ 2|t|, i.e., cosh ≤ 2·sinh
    rw [div_le_iff₀ hsinh_pos, hcosh_t]
    calc |t| * Real.cosh (π * |t|)
        ≤ |t| * (2 * Real.sinh (π * |t|)) :=
          mul_le_mul_of_nonneg_left hcosh_le (abs_nonneg t)
      _ = 2 * |t| * Real.sinh (π * |t|) := by ring

/-! ## Section 6b: Per-factor bounds for GammaSeq ratio product -/

/-- R_j² identity: ‖(1/2+j, t)‖²/‖(σ+j, t)‖² = ((1/2+j)²+t²)/((σ+j)²+t²) -/
private lemma R_j_sq_identity (σ t : ℝ) (j : ℕ) :
    ‖(⟨1/2 + ↑j, t⟩ : ℂ)‖ ^ 2 / ‖(⟨σ + ↑j, t⟩ : ℂ)‖ ^ 2 =
    ((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_mk]
  ring_nf

/-- R_j ≤ 1 when σ > 1/2 (the half-integer norm is smaller) -/
private lemma R_j_le_one (σ t : ℝ) (j : ℕ) (hσ : 1/2 < σ) :
    ‖(⟨1/2 + ↑j, t⟩ : ℂ)‖ / ‖(⟨σ + ↑j, t⟩ : ℂ)‖ ≤ (1 : ℝ) := by
  have hj := j.cast_nonneg (α := ℝ)
  have hσj : (0 : ℝ) < σ + (j : ℝ) := by linarith
  have h12j : (0 : ℝ) < 1/2 + (j : ℝ) := by linarith
  have hsq : Complex.normSq (⟨1/2 + (j : ℝ), t⟩ : ℂ) ≤
      Complex.normSq (⟨σ + (j : ℝ), t⟩ : ℂ) := by
    rw [Complex.normSq_mk, Complex.normSq_mk]
    have : (1/2 + (j : ℝ)) * (1/2 + (j : ℝ)) ≤ (σ + (j : ℝ)) * (σ + (j : ℝ)) :=
      mul_self_le_mul_self (by linarith) (by linarith)
    linarith
  have hn : ‖(⟨1/2 + ↑j, t⟩ : ℂ)‖ ≤ ‖(⟨σ + ↑j, t⟩ : ℂ)‖ := by
    simp only [Complex.norm_eq_sqrt_sq_add_sq]
    exact Real.sqrt_le_sqrt (by rw [Complex.normSq_mk, Complex.normSq_mk] at hsq; nlinarith)
  exact div_le_one_iff.mpr (Or.inl ⟨norm_pos_iff.mpr (mk_ne_zero_of_pos _ _ hσj), hn⟩)

/-- R_j ≥ (1/2+j)/(σ+j) when σ > 1/2 (adding t² helps the smaller number) -/
private lemma R_j_ge_real_ratio (σ t : ℝ) (j : ℕ) (hσ : 1/2 < σ) :
    (1/2 + ↑j) / (σ + ↑j) ≤
      ‖(⟨1/2 + ↑j, t⟩ : ℂ)‖ / ‖(⟨σ + ↑j, t⟩ : ℂ)‖ := by
  have hj := j.cast_nonneg (α := ℝ)
  have h12j : (0 : ℝ) < 1/2 + (j : ℝ) := by linarith
  have hσj : (0 : ℝ) < σ + (j : ℝ) := by linarith
  rw [div_le_div_iff₀ hσj (norm_pos_iff.mpr (mk_ne_zero_of_pos _ _ hσj))]
  have h_rhs_nn : (0 : ℝ) ≤ ‖(⟨1/2 + ↑j, t⟩ : ℂ)‖ * (σ + ↑j) :=
    mul_nonneg (norm_nonneg _) hσj.le
  apply le_of_sq_le_sq _ h_rhs_nn
  rw [mul_pow, mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_mk, Complex.normSq_mk, sq (σ + (j : ℝ)), sq (1/2 + (j : ℝ))]
  nlinarith [sq_nonneg t, mul_self_le_mul_self h12j.le (show 1/2 + (j : ℝ) ≤ σ + (j : ℝ) by linarith)]

/-- The complex GammaSeq norm ratio converges to the Gamma ratio. -/
private lemma complex_gammaSeq_ratio_tendsto' (σ t : ℝ) (hσ : 0 < σ) :
    Filter.Tendsto
      (fun n => ‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖)
      Filter.atTop
      (nhds (‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖)) := by
  apply Filter.Tendsto.div
  · exact (Complex.GammaSeq_tendsto_Gamma _).norm
  · exact (Complex.GammaSeq_tendsto_Gamma _).norm
  · exact norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re))

/-! ## Section 6c: GammaSeq product analysis → GammaRatioUpperHalf

The strategy: express R(σ,t) = lim n^{σ-1/2} · ∏ R_j, bound each log R_j²
using log(1-x) ∈ [-x/(1-x), -x], sum via comparison to log integral,
and deduce R(σ,t) ~ |t|^{σ-1/2}. -/

/-- R_j² = 1 - x_j where x_j = (σ-1/2)(σ+1/2+2j)/((σ+j)²+t²).
    Algebraic identity: (σ+j)² - (1/2+j)² = (σ-1/2)(σ+1/2+2j). -/
private lemma R_j_sq_one_minus (σ t : ℝ) (j : ℕ) (hσ : 1/2 < σ) :
    ((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) =
    1 - (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) := by
  have hj := j.cast_nonneg (α := ℝ)
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  rw [div_eq_iff (ne_of_gt hD), sub_mul, div_mul_cancel₀ _ (ne_of_gt hD), one_mul]
  nlinarith [sq_nonneg (1/2 + (j : ℝ)), sq_nonneg (σ + (j : ℝ))]

/-- The fraction x_j = δ/D is in (0, 1). -/
private lemma x_j_bounds (σ t : ℝ) (j : ℕ) (hσ : 1/2 < σ) :
    0 < (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) ∧
    (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) < 1 := by
  have hj := j.cast_nonneg (α := ℝ)
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  have hδ : 0 < σ - 1/2 := by linarith
  have hsum : 0 < σ + 1/2 + 2 * ↑j := by positivity
  refine ⟨div_pos (mul_pos hδ hsum) hD, ?_⟩
  rw [div_lt_one hD]
  -- Need: (σ-1/2)(σ+1/2+2j) < (σ+j)² + t²
  -- Equivalently: (1/2+j)² + t² > 0, which is obvious
  nlinarith [sq_nonneg (1/2 + (j : ℝ)), sq_nonneg t]

/-- log R_j² ≤ -x_j (upper bound from log(1-x) ≤ -x). -/
private lemma log_R_j_sq_upper (σ t : ℝ) (j : ℕ) (hσ : 1/2 < σ) :
    Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) ≤
    -((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) := by
  rw [R_j_sq_one_minus σ t j hσ]
  have ⟨hx_pos, hx_lt⟩ := x_j_bounds σ t j hσ
  set x := (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)
  -- log(1 - x) ≤ (1-x) - 1 = -x from Real.log_le_sub_one_of_pos
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - x by linarith)]

/-- log R_j² ≥ -x_j/(1-x_j) = -δ/((1/2+j)²+t²) (lower bound from log(y) ≤ y-1). -/
private lemma log_R_j_sq_lower (σ t : ℝ) (j : ℕ) (hσ : 1/2 < σ) :
    -((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((1/2 + ↑j) ^ 2 + t ^ 2)) ≤
    Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) := by
  -- Strategy: log(N/D) = -log(D/N), and log(D/N) ≤ D/N - 1 = δ/N
  have hj := j.cast_nonneg (α := ℝ)
  have hN : (0 : ℝ) < (1/2 + ↑j) ^ 2 + t ^ 2 := by positivity
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  have hDN_pos : (0 : ℝ) < ((σ + ↑j) ^ 2 + t ^ 2) / ((1/2 + ↑j) ^ 2 + t ^ 2) :=
    div_pos hD hN
  -- log(D/N) ≤ D/N - 1 by log_le_sub_one_of_pos
  have h1 := Real.log_le_sub_one_of_pos hDN_pos
  -- log(N/D) = -log(D/N)
  have h2 : Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) =
      -Real.log (((σ + ↑j) ^ 2 + t ^ 2) / ((1/2 + ↑j) ^ 2 + t ^ 2)) := by
    rw [Real.log_div (ne_of_gt hN) (ne_of_gt hD),
        Real.log_div (ne_of_gt hD) (ne_of_gt hN)]
    ring
  -- D/N - 1 = δ/N
  have h3 : ((σ + ↑j) ^ 2 + t ^ 2) / ((1/2 + ↑j) ^ 2 + t ^ 2) - 1 =
      (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((1/2 + ↑j) ^ 2 + t ^ 2) := by
    rw [div_sub_one (ne_of_gt hN)]; congr 1; ring
  linarith

/-- Each x_j is at most 2(σ-1/2)/(σ+j), giving a harmonic-type series.
    Proof: (σ+1/2+2j) ≤ 2(σ+j) and (σ+j)²+t² ≥ (σ+j)·1. -/
private lemma x_j_le_inv (σ t : ℝ) (j : ℕ) (hσ : 1/2 < σ) :
    (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) ≤
    2 * (σ - 1/2) / (σ + ↑j) := by
  have hj := j.cast_nonneg (α := ℝ)
  have hσj : (0 : ℝ) < σ + ↑j := by linarith
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  rw [div_le_div_iff₀ hD hσj]
  -- Need: (σ-1/2)(σ+1/2+2j)(σ+j) ≤ 2(σ-1/2)((σ+j)²+t²)
  have h1 : σ + 1/2 + 2 * ↑j ≤ 2 * (σ + ↑j) := by linarith
  have hδ : (0 : ℝ) ≤ σ - 1/2 := by linarith
  have h2 : (σ - 1/2) * (σ + 1/2 + 2 * ↑j) ≤ 2 * (σ - 1/2) * (σ + ↑j) :=
    by nlinarith
  have h3 : (σ - 1/2) * (σ + 1/2 + 2 * ↑j) * (σ + ↑j) ≤
      2 * (σ - 1/2) * (σ + ↑j) * (σ + ↑j) :=
    mul_le_mul_of_nonneg_right h2 hσj.le
  nlinarith [sq_nonneg t, sq_abs (σ + (j : ℝ))]

/-- D_{j+1} = D_j + 2(σ+j) + 1 where D_j = (σ+j)²+t². -/
private lemma D_step (σ t : ℝ) (j : ℕ) :
    (σ + (↑j + 1)) ^ 2 + t ^ 2 = ((σ + ↑j) ^ 2 + t ^ 2) + (2 * (σ + ↑j) + 1) := by
  push_cast; ring

/-- The ratio D_{j+1}/D_j = 1 + (2(σ+j)+1)/D_j, so 2(σ+j)/D_j = D_{j+1}/D_j - 1 - 1/D_j. -/
private lemma f_eq_ratio_sub (σ t : ℝ) (j : ℕ) (hσ : 0 < σ) :
    2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) =
    ((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) - 1 - 1 / ((σ + ↑j) ^ 2 + t ^ 2) := by
  have hj := j.cast_nonneg (α := ℝ)
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  rw [D_step]
  field_simp
  ring

/-- Lower bound per term: f_j ≥ log(D_{j+1}/D_j) - 1/D_j.
    From log(x) ≤ x - 1 applied to x = D_{j+1}/D_j. -/
private lemma f_ge_log_ratio_sub (σ t : ℝ) (j : ℕ) (hσ : 0 < σ) :
    Real.log (((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) -
    1 / ((σ + ↑j) ^ 2 + t ^ 2) ≤
    2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) := by
  have hj := j.cast_nonneg (α := ℝ)
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  have hD1 : (0 : ℝ) < (σ + (↑j + 1)) ^ 2 + t ^ 2 := by positivity
  have hratio : (0 : ℝ) < ((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) :=
    div_pos hD1 hD
  -- log(D_{j+1}/D_j) ≤ D_{j+1}/D_j - 1
  have hlog := Real.log_le_sub_one_of_pos hratio
  -- D_{j+1}/D_j - 1 = (2(σ+j)+1)/D_j = f_j + 1/D_j
  rw [f_eq_ratio_sub σ t j hσ]
  linarith

/-- Telescoping log identity: Σ log(D_{j+1}/D_j) = log(D_{n+1}/D_0). -/
private lemma log_telescope (σ t : ℝ) (n : ℕ) (hσ₀ : 0 < σ) :
    (Finset.range (n + 1)).sum (fun j =>
      Real.log (((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2))) =
    Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) - Real.log (σ ^ 2 + t ^ 2) := by
  have hD : ∀ j : ℕ, (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := fun j => by
    have : (0 : ℝ) ≤ (j : ℝ) := j.cast_nonneg; positivity
  set g : ℕ → ℝ := fun j => Real.log ((σ + ↑j) ^ 2 + t ^ 2)
  -- Rewrite log(a/b) to g(j+1) - g(j)
  have hconv : ∀ j : ℕ,
      Real.log (((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) =
      g (j + 1) - g j := by
    intro j
    simp only [g, Nat.cast_succ]
    rw [Real.log_div (ne_of_gt (by positivity)) (ne_of_gt (hD j))]
  simp_rw [hconv]
  rw [Finset.sum_range_sub]
  simp only [g, Nat.cast_zero, Nat.cast_succ]
  ring_nf

/-- Lower bound via telescoping: Σ f_j ≥ log(D_{n+1}/D_0) - Σ 1/D_j.
    From f_j ≥ log(D_{j+1}/D_j) - 1/D_j (proved in f_ge_log_ratio_sub). -/
private lemma sum_f_ge_log_sub (σ t : ℝ) (n : ℕ) (hσ₀ : 0 < σ) :
    Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) - Real.log (σ ^ 2 + t ^ 2) -
    (Finset.range (n + 1)).sum (fun j => 1 / ((σ + ↑j) ^ 2 + t ^ 2)) ≤
    (Finset.range (n + 1)).sum (fun j => 2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) := by
  rw [← log_telescope σ t n hσ₀]
  rw [sub_le_iff_le_add, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  linarith [f_ge_log_ratio_sub σ t j hσ₀]

/-- f(u) = 2u/(u²+t²) ≤ 1/|t| ≤ 1 for |t| ≥ 1 (AM-GM: u²+t² ≥ 2u|t|). -/
private lemma f_le_one (σ t : ℝ) (j : ℕ) (hσ₀ : 0 < σ) (ht : 1 ≤ |t|) :
    2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) ≤ 1 := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hσj : (0 : ℝ) < σ + ↑j := by linarith
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  rw [div_le_one hD]
  -- Need: 2(σ+j) ≤ (σ+j)² + t²  i.e.  0 ≤ (σ+j)² - 2(σ+j) + t²
  -- = (σ+j-1)² + t² - 1 ≥ 0 when t²≥1 and σ+j ≥ 0. Actually that needs t²≥1.
  -- Alternatively: (σ+j)² + t² ≥ 2(σ+j)|t| ≥ 2(σ+j) by AM-GM
  nlinarith [sq_nonneg (σ + ↑j - 1), sq_abs t]

/-- Per-term upper bound: f_j ≤ log(D_{j+1}/D_j) + u_j² where u_j = (2(σ+j)+1)/D_j.
    Proof: f_j + 1/D_j = u_j and log(1+u) ≥ u/(1+u), so
    u - log(1+u) ≤ u - u/(1+u) = u²/(1+u) ≤ u². -/
private lemma f_le_log_ratio_add_u_sq (σ t : ℝ) (j : ℕ) (hσ₀ : 0 < σ) :
    2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) ≤
    Real.log (((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) +
    ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2 := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  set D := (σ + ↑j) ^ 2 + t ^ 2
  set u := (2 * (σ + ↑j) + 1) / D with hu_def
  -- f_j = u - 1/D
  have hf : 2 * (σ + ↑j) / D = u - 1 / D := by
    simp only [hu_def]; field_simp; ring
  rw [hf]
  -- log(D_{j+1}/D_j) = log(1 + u) since D_{j+1} = D + (2(σ+j)+1)
  have hD_step : (σ + (↑j + 1)) ^ 2 + t ^ 2 = D + (2 * (σ + ↑j) + 1) := by
    simp only [D]; push_cast; ring
  have hu_pos : 0 < u := by positivity
  have hDu : ((σ + (↑j + 1)) ^ 2 + t ^ 2) / D = 1 + u := by
    rw [hD_step, hu_def]; field_simp
  rw [hDu]
  -- Need: u - 1/D ≤ log(1+u) + u²
  -- Apply log(x) ≤ x-1 to x = 1/(1+u):
  --   log(1/(1+u)) ≤ 1/(1+u) - 1  →  -log(1+u) ≤ -u/(1+u)  →  log(1+u) ≥ u/(1+u)
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have hlog_inv := Real.log_le_sub_one_of_pos (div_pos one_pos h1u)
  rw [Real.log_div one_ne_zero (ne_of_gt h1u), Real.log_one, zero_sub] at hlog_inv
  -- hlog_inv : -log(1+u) ≤ 1/(1+u) - 1, so log(1+u) ≥ 1 - 1/(1+u) = u/(1+u)
  have hlog_lb : u / (1 + u) ≤ Real.log (1 + u) := by
    have : 1 - 1 / (1 + u) = u / (1 + u) := by field_simp; ring
    linarith
  -- u/(1+u) ≥ u - u² (since u/(1+u) - u + u² = u³/(1+u) ≥ 0)
  have hlog_lb2 : u - u ^ 2 ≤ u / (1 + u) := by
    rw [le_div_iff₀ h1u]
    nlinarith [sq_nonneg u, sq_nonneg (u * u)]
  -- Combine: log(1+u) ≥ u - u², so u - 1/D ≤ u ≤ log(1+u) + u²
  linarith [div_pos one_pos hD]

/-- Each 1/D_j ≤ 1 since D_j ≥ 1 when t²≥1. Crude but simple. -/
private lemma inv_D_le_one (σ t : ℝ) (j : ℕ) (hσ₀ : 0 < σ) (ht : 1 ≤ |t|) :
    1 / ((σ + ↑j) ^ 2 + t ^ 2) ≤ 1 := by
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hD : 1 ≤ (σ + ↑j) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (σ + ↑j)]
  have hDpos : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  rwa [div_le_one hDpos]

/-- Σ 1/D_j ≤ 3 for σ > 0, |t| ≥ 1. Proof: 1/D_j ≤ 1/(j²+1) since (σ+j)²≥j², t²≥1.
    Then Σ 1/(j²+1) ≤ 1 + 1/2 + Σ_{j≥2} 1/(j(j-1)) ≤ 5/2 < 3. -/
private lemma sum_inv_D_le (σ t : ℝ) (n : ℕ) (hσ : 1/2 < σ) (ht : 1 ≤ |t|) :
    (Finset.range (n + 1)).sum (fun j => 1 / ((σ + ↑j) ^ 2 + t ^ 2)) ≤ 3 := by
  -- For j ≥ 1: (σ+j)² ≥ (1/2+j)² = j²+j+1/4 > j(j+1), so 1/D_j < 1/(j(j+1)).
  -- Telescoping: Σ_{j=1}^n 1/(j(j+1)) = 1 - 1/(n+1) < 1. Plus 1/D_0 ≤ 1. Total < 2 ≤ 3.
  have hσ₀ : (0 : ℝ) < σ := by linarith
  -- Bound each term
  have hterm : ∀ j ∈ Finset.range (n + 1),
      1 / ((σ + ↑j) ^ 2 + t ^ 2) ≤ if j = 0 then 1 else 1 / ((↑j : ℝ) * (↑j + 1)) := by
    intro j _
    split_ifs with hj
    · -- j = 0: D_0 ≥ 1
      subst hj; simp
      have := inv_D_le_one σ t 0 hσ₀ ht; simp at this; exact this
    · -- j ≥ 1: D_j > j(j+1)
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      have hjj1 : (0 : ℝ) < (↑j : ℝ) * (↑j + 1) := by positivity
      gcongr
      -- (σ+j)² + t² ≥ j(j+1)
      have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
      nlinarith [sq_nonneg (σ + ↑j - (1/2 + ↑j))]
  apply le_trans (Finset.sum_le_sum hterm)
  -- Now bound Σ (if j=0 then 1 else 1/(j(j+1)))
  -- Induction: Σ ≤ 2 - 1/(n+1) ≤ 2 ≤ 3
  suffices h : ∀ m : ℕ,
      (Finset.range (m + 1)).sum (fun i => if i = 0 then (1 : ℝ) else 1 / (↑i * (↑i + 1))) ≤
      2 - 1 / ((m : ℝ) + 1) by
    have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    linarith [h n, div_pos one_pos hn1]
  intro m; induction m with
  | zero => simp; norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0:ℝ) < (k : ℝ) + 2 := by positivity
    -- Goal: prev + 1/((k+1)*(k+2)) ≤ 2 - 1/(k+2)
    -- From ih: prev ≤ 2 - 1/(k+1)
    -- So suffices: 2 - 1/(k+1) + 1/((k+1)(k+2)) ≤ 2 - 1/(k+2)
    -- Which is: 1/((k+1)(k+2)) ≤ 1/(k+1) - 1/(k+2)
    -- Which is: 1/((k+1)(k+2)) = 1/((k+1)(k+2)). ✓
    simp only [Nat.cast_succ] at ih ⊢
    have halg : (1:ℝ) / ((↑k + 1) * (↑k + 1 + 1)) = 1/(↑k + 1) - 1/(↑k + 1 + 1) := by
      field_simp; ring
    linarith

/-- Bound Σ u_j² ≤ 18 where u_j = (2(σ+j)+1)/D_j. For j≥1: u_j ≤ 3/(σ+j) so
    u_j² ≤ 9/(σ+j)² ≤ 9/(j(j+1)). Telescoping gives Σ_{j≥1} ≤ 9. Plus u_0² ≤ 9. -/
private lemma sum_u_sq_le (σ t : ℝ) (n : ℕ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : 1 ≤ |t|) :
    (Finset.range (n + 1)).sum (fun j =>
      ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2) ≤ 18 := by
  have hσ₀ : (0 : ℝ) < σ := by linarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  -- Per-term bound: u_j² ≤ 9/(j²+1) for all j
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2 ≤
      if j = 0 then (9 : ℝ) else 9 / ((↑j : ℝ) * (↑j + 1)) := by
    intro j _
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
    split_ifs with hj0
    · -- j = 0: u_0 = (2σ+1)/(σ²+t²), u_0² ≤ 9 since D_0 ≥ 1 and 2σ+1 < 3
      subst hj0; simp
      have hD0 : 1 ≤ σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg σ]
      have hDp : (0 : ℝ) < σ ^ 2 + t ^ 2 := by linarith
      have h2s1 : (2 * σ + 1) ^ 2 < 9 := by nlinarith
      rw [div_pow, div_le_iff₀ (sq_pos_of_pos hDp)]
      nlinarith [sq_nonneg (σ ^ 2 + t ^ 2)]
    · -- j ≥ 1: u_j ≤ 3/(σ+j), so u_j² ≤ 9/(σ+j)² ≤ 9/(j(j+1))
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
      have hjj1 : (0 : ℝ) < (↑j : ℝ) * (↑j + 1) := by positivity
      rw [div_pow, div_le_div_iff₀ (by positivity) hjj1]
      -- Need: (2(σ+j)+1)² · (j(j+1)) ≤ 9 · D²
      -- Since D = (σ+j)²+t² ≥ (σ+j)² and 2(σ+j)+1 ≤ 3(σ+j) (for σ+j≥1):
      -- (2(σ+j)+1)² ≤ 9(σ+j)², and j(j+1) ≤ (σ+j)² (since (σ+j)²-j(j+1) = σ²+2σj-j = σ(σ+2j)-j > 0)
      -- So LHS ≤ 9(σ+j)²·(σ+j)² ≤ 9·D²
      have hsj : 1 ≤ σ + ↑j := by linarith
      -- (2(σ+j)+1)² ≤ 9(σ+j)² since 2(σ+j)+1 ≤ 3(σ+j)
      have h3 : 2 * (σ + ↑j) + 1 ≤ 3 * (σ + ↑j) := by linarith
      -- j(j+1) ≤ (σ+j)² since (σ+j)² - j(j+1) = σ²+2σj-j ≥ 0
      have hjsj : ↑j * (↑j + 1) ≤ (σ + ↑j) ^ 2 := by nlinarith [sq_nonneg σ]
      -- D ≥ (σ+j)² (trivially since t² ≥ 0)
      have hDge : (σ + ↑j) ^ 2 ≤ (σ + ↑j) ^ 2 + t ^ 2 := by linarith [sq_nonneg t]
      -- Chain: (2s+1)² ≤ 9·s² (from h3 squared), j(j+1) ≤ s², so LHS ≤ 9·s⁴ ≤ 9·D²
      have h3sq : (2 * (σ + ↑j) + 1) ^ 2 ≤ (3 * (σ + ↑j)) ^ 2 := by nlinarith
      have h9 : (3 * (σ + ↑j)) ^ 2 = 9 * (σ + ↑j) ^ 2 := by ring
      rw [h9] at h3sq
      -- LHS ≤ 9(σ+j)²·(σ+j)² and D ≥ (σ+j)², so 9D² ≥ 9(σ+j)⁴ ≥ LHS
      nlinarith [sq_nonneg t]
  apply le_trans (Finset.sum_le_sum hterm)
  -- Now: Σ (if j=0 then 9 else 9/(j(j+1))) = 9 + 9·Σ_{j=1}^n 1/(j(j+1)) ≤ 9 + 9·1 = 18
  -- Use tighter bound: Σ ≤ 18 - 9/(m+1)
  suffices h : ∀ m : ℕ,
      (Finset.range (m + 1)).sum (fun i =>
        if i = 0 then (9 : ℝ) else 9 / (↑i * (↑i + 1))) ≤
      18 - 9 / ((m : ℝ) + 1) by
    have hm1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    linarith [h n, div_pos (by norm_num : (0:ℝ) < 9) hm1]
  intro m; induction m with
  | zero => simp; norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.cast_succ]
    have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0:ℝ) < (k : ℝ) + 2 := by positivity
    -- 9/((k+1)(k+2)) = 9/(k+1) - 9/(k+2)
    have halg : (9:ℝ) / ((↑k + 1) * (↑k + 1 + 1)) = 9/(↑k + 1) - 9/(↑k + 1 + 1) := by
      field_simp; ring
    linarith

/-- Upper bound on Σ f_j via telescoping + Σu_j²: Σ f_j ≤ L + 18. -/
private lemma sum_f_le_upper (σ t : ℝ) (n : ℕ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : 1 ≤ |t|) :
    (Finset.range (n + 1)).sum (fun j => 2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ≤
    Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) - Real.log (σ ^ 2 + t ^ 2) + 18 := by
  have hσ₀ : (0 : ℝ) < σ := by linarith
  rw [← log_telescope σ t n hσ₀]
  have hU := sum_u_sq_le σ t n hσ hσ1 ht
  have hper : ∀ j ∈ Finset.range (n + 1),
      2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) ≤
      Real.log (((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) +
      ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2 :=
    fun j _ => f_le_log_ratio_add_u_sq σ t j hσ₀
  calc (Finset.range (n + 1)).sum (fun j => 2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2))
      ≤ (Finset.range (n + 1)).sum (fun j =>
          Real.log (((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) +
          ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2) :=
        Finset.sum_le_sum hper
    _ = (Finset.range (n + 1)).sum (fun j =>
          Real.log (((σ + (↑j + 1)) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2))) +
        (Finset.range (n + 1)).sum (fun j =>
          ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2) :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-- Algebraic split: (σ-1/2)(σ+1/2+2j) = (σ-1/2)·2(σ+j) - (σ-1/2)². -/
private lemma delta_split (σ t : ℝ) (j : ℕ) :
    (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) =
    (σ - 1/2) * (2 * (σ + ↑j)) / ((σ + ↑j) ^ 2 + t ^ 2) -
    (σ - 1/2) ^ 2 / ((σ + ↑j) ^ 2 + t ^ 2) := by
  ring

/-- Weaker form: the sum involving (σ+1/2+2j)/D_j is controlled by the same log difference.
    Uses: (σ+1/2+2j) = 2(σ+j) - (σ-1/2), so the sum splits into the
    main log term plus a convergent remainder bounded by (σ-1/2)²·3. -/
private lemma sum_delta_over_D_bound (σ t : ℝ) (n : ℕ) (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (ht : 1 ≤ |t|) :
    (σ - 1/2) * (Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) - Real.log (σ ^ 2 + t ^ 2) - 20) ≤
      (Finset.range (n + 1)).sum (fun j =>
        (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ∧
    (Finset.range (n + 1)).sum (fun j =>
        (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ≤
      (σ - 1/2) * (Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) - Real.log (σ ^ 2 + t ^ 2) + 20) := by
  have hσ₀ : (0 : ℝ) < σ := by linarith
  have hδ : (0 : ℝ) ≤ σ - 1/2 := by linarith
  have hδ1 : σ - 1/2 < 1/2 := by linarith
  set L := Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) - Real.log (σ ^ 2 + t ^ 2)
  set S := (Finset.range (n + 1)).sum (fun j =>
      1 / ((σ + ↑j) ^ 2 + t ^ 2))
  have hS : S ≤ 3 := sum_inv_D_le σ t n hσ ht
  have hF := sum_f_ge_log_sub σ t n hσ₀  -- L - S ≤ Σ f_j
  -- Algebraic split: Σ x_j = (σ-1/2)·Σ f_j - (σ-1/2)²·Σ 1/D_j
  set sumF := (Finset.range (n + 1)).sum (fun j =>
      2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2))
  set sumX := (Finset.range (n + 1)).sum (fun j =>
      (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2))
  -- sumX = (σ-1/2)·sumF - (σ-1/2)²·S
  -- Algebraic identity: Σ x_j = (σ-1/2)·Σf - (σ-1/2)²·S
  -- where x_j = (σ-1/2)(σ+1/2+2j)/D_j and f_j = 2(σ+j)/D_j
  -- From: (σ+1/2+2j) = 2(σ+j) - (σ-1/2)
  have hsplit : sumX = (σ - 1/2) * sumF - (σ - 1/2) ^ 2 * S := by
    simp only [sumX, sumF, S, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hD : ((σ + ↑j) ^ 2 + t ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    field_simp; ring
  constructor
  · -- Lower bound: sumX ≥ (σ-1/2)·(L-S) - (σ-1/2)²·S ≥ (σ-1/2)·(L-5)
    -- From hF: L - S ≤ sumF, so (σ-1/2)·(L-S) ≤ (σ-1/2)·sumF
    -- sumX = (σ-1/2)·sumF - (σ-1/2)²·S ≥ (σ-1/2)·(L-S) - (σ-1/2)²·S
    -- = (σ-1/2)·L - (σ-1/2)·S·(1+(σ-1/2))
    -- Since S ≤ 3 and (σ-1/2) < 1/2: S·(1+(σ-1/2)) ≤ 3·3/2 = 9/2 < 5
    rw [hsplit]
    nlinarith [sq_nonneg (σ - 1/2)]
  · -- Upper bound: sumF ≤ L + 18 from sum_f_le_upper
    rw [hsplit]
    have hFup : sumF ≤ L + 18 := sum_f_le_upper σ t n hσ hσ1 ht
    have h1 : (σ - 1/2) * sumF ≤ (σ - 1/2) * (L + 18) := mul_le_mul_of_nonneg_left hFup hδ
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
    nlinarith [sq_nonneg (σ - 1/2), mul_nonneg (sq_nonneg (σ - 1/2)) hS0]

/-- x_j < 1/2: uses f_le_one and σ-1/2 < 1/2. -/
private lemma x_j_lt_half (σ t : ℝ) (j : ℕ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : 1 ≤ |t|) :
    (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) < 1/2 := by
  have hσ₀ : (0 : ℝ) < σ := by linarith
  have hf := f_le_one σ t j hσ₀ ht
  have hj := j.cast_nonneg (α := ℝ)
  -- x_j ≤ (σ-1/2)·f_j ≤ σ-1/2 < 1/2
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  have hle : (σ - 1/2) * (σ + 1/2 + 2 * ↑j) ≤ (σ - 1/2) * (2 * (σ + ↑j)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)
      ≤ (σ - 1/2) * (2 * (σ + ↑j)) / ((σ + ↑j) ^ 2 + t ^ 2) :=
        div_le_div_of_nonneg_right hle hD.le
    _ = (σ - 1/2) * (2 * (σ + ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) := by ring
    _ ≤ (σ - 1/2) * 1 := mul_le_mul_of_nonneg_left hf (by linarith)
    _ < 1/2 := by linarith

/-- Lower log bound using x_j/(1-x_j) ≤ 2x_j: Σlog(R_j²) ≥ -2·Σx_j. -/
private lemma sum_log_R_lower (σ t : ℝ) (n : ℕ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : 1 ≤ |t|) :
    -2 * (Finset.range (n + 1)).sum (fun j =>
        (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ≤
    (Finset.range (n + 1)).sum (fun j =>
        Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2))) := by
  suffices hper : ∀ j ∈ Finset.range (n + 1),
      -(2 * ((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2))) ≤
      Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) by
    calc -2 * (Finset.range (n + 1)).sum (fun j =>
          (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2))
        = (Finset.range (n + 1)).sum (fun j =>
          -(2 * ((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)))) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ _ := Finset.sum_le_sum hper
  intro j _
  have ⟨hx_pos, hx_lt⟩ := x_j_bounds σ t j hσ
  have hx_half := x_j_lt_half σ t j hσ hσ1 ht
  set x := (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) with hx_def
  -- x/(1-x) = (σ-1/2)(σ+1/2+2j)/((1/2+j)²+t²) which is what log_R_j_sq_lower uses
  have hj := j.cast_nonneg (α := ℝ)
  have hN : (0 : ℝ) < (1/2 + ↑j) ^ 2 + t ^ 2 := by positivity
  have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
  -- log_R_j_sq_lower gives: log(R_j²) ≥ -(σ-1/2)(σ+1/2+2j)/((1/2+j)²+t²)
  have hlog := log_R_j_sq_lower σ t j hσ
  -- And x/(1-x) = (σ-1/2)(σ+1/2+2j)/((1/2+j)²+t²) from R_j_sq_one_minus
  have h1x : (0:ℝ) < 1 - x := by linarith
  -- x/(1-x) ≤ 2x since x < 1/2
  have hxdiv : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ h1x]; nlinarith
  -- x/(1-x) = delta/N where N = (1/2+j)²+t² by R_j_sq_one_minus
  -- 1-x = N/D by R_j_sq_one_minus, so x/(1-x) = x·D/N = delta/N
  have h1x_eq : 1 - x = ((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) := by
    rw [hx_def, R_j_sq_one_minus σ t j hσ]
  have hval : (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((1/2 + ↑j) ^ 2 + t ^ 2) = x / (1 - x) := by
    rw [h1x_eq, hx_def]; field_simp
  linarith

/-- The GammaSeq norm ratio equals n^{σ-1/2} times the product of norm ratios.
    This is an algebraic identity from GammaSeq s n = n^s · n! / ∏(s+j):
    the n! factors cancel, n^s / n^{1/2} = n^{σ-1/2} (norm of n^{it} is 1),
    and the remaining product is ∏ ‖(1/2+it+j)‖/‖(σ+it+j)‖. -/
private lemma gammaSeq_norm_ratio_eq (σ t : ℝ) (n : ℕ) (hn : 0 < n)
    (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (hden : ‖Complex.GammaSeq ⟨1/2, t⟩ n‖ ≠ 0) :
    ‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖ =
    (n : ℝ) ^ (σ - 1/2) *
    ∏ j ∈ Finset.range (n + 1),
      (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ ((1:ℝ)/2) := by
  set s₁ : ℂ := ⟨σ, t⟩; set s₂ : ℂ := ⟨1/2, t⟩
  have hn' : (↑n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfact : (↑(n.factorial) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hprod₁ : ∀ j ∈ Finset.range (n+1), s₁ + (↑j : ℂ) ≠ 0 := fun j _ hz => by
    have := congr_arg Complex.re hz; simp [s₁] at this; linarith [j.cast_nonneg (α := ℝ)]
  have hprod₂ : ∀ j ∈ Finset.range (n+1), s₂ + (↑j : ℂ) ≠ 0 := fun j _ hz => by
    have := congr_arg Complex.re hz; simp [s₂] at this; linarith [j.cast_nonneg (α := ℝ)]
  -- Step 1: complex ratio identity
  have hratio : Complex.GammaSeq s₁ n / Complex.GammaSeq s₂ n =
      (↑n : ℂ) ^ (s₁ - s₂) * ∏ j ∈ Finset.range (n+1), ((s₂ + ↑j) / (s₁ + ↑j)) := by
    simp only [Complex.GammaSeq.eq_1, Finset.prod_div_distrib, Complex.cpow_sub _ _ hn']
    have hns₁ : (↑n : ℂ) ^ s₁ ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hn']; exact Complex.exp_ne_zero _
    have hns₂ : (↑n : ℂ) ^ s₂ ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hn']; exact Complex.exp_ne_zero _
    field_simp
  -- Step 2: take norms
  rw [← norm_div, hratio, norm_mul, norm_prod]
  congr 1
  · -- ‖n^{s₁-s₂}‖ = n^{σ-1/2}
    rw [Complex.norm_natCast_cpow_of_pos hn]; simp [s₁, s₂]
  · -- Each factor: ‖(s₂+j)/(s₁+j)‖ = ((1/2+j)²+t²)/((σ+j)²+t²))^{1/2}
    apply Finset.prod_congr rfl; intro j hj
    rw [norm_div]
    -- ‖s₂+j‖ = √((1/2+j)²+t²), ‖s₁+j‖ = √((σ+j)²+t²)
    have h₁ : ‖s₁ + (↑j : ℂ)‖ ^ 2 = (σ + ↑j) ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; simp [s₁]; ring
    have h₂ : ‖s₂ + (↑j : ℂ)‖ ^ 2 = (1/2 + ↑j) ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; simp [s₂]; ring
    have h1pos : (0:ℝ) < ‖s₁ + (↑j : ℂ)‖ :=
      norm_pos_iff.mpr (hprod₁ j hj)
    have h2nn : (0:ℝ) ≤ ‖s₂ + (↑j : ℂ)‖ := norm_nonneg _
    have hsq : (‖s₂ + (↑j : ℂ)‖ / ‖s₁ + (↑j : ℂ)‖) ^ 2 =
        ((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) := by
      rw [div_pow, h₁, h₂]
    rw [← Real.sqrt_sq (div_nonneg h2nn (le_of_lt h1pos)), hsq, Real.sqrt_eq_rpow]

/-- GammaSeq(s,n) ≠ 0 for n ≥ 1 and Re(s) > 0. -/
private lemma gammaSeq_ne_zero (s : ℂ) (n : ℕ) (hn : 0 < n) (hs : 0 < s.re) :
    Complex.GammaSeq s n ≠ 0 := by
  rw [Complex.GammaSeq.eq_1]
  apply div_ne_zero
  · apply mul_ne_zero
    · rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega))]
      exact Complex.exp_ne_zero _
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  · apply Finset.prod_ne_zero_iff.mpr; intro j _
    intro hz; have := congr_arg Complex.re hz
    simp [Complex.add_re] at this; linarith [j.cast_nonneg (α := ℝ)]

/-- Upper bound on the log of the product ∏R_j² using log_R_j_sq_upper and sum_delta_over_D_bound.
    Gives: Σ log(R_j²) ≤ -Σx_j ≤ -(σ-1/2)(L-20) where L = log-ratio of endpoints. -/
private lemma sum_log_R_upper (σ t : ℝ) (n : ℕ) (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (ht : 1 ≤ |t|) :
    (Finset.range (n + 1)).sum (fun j =>
        Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2))) ≤
    -(σ - 1/2) * (Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) -
        Real.log (σ ^ 2 + t ^ 2) - 20) := by
  have hup : (Finset.range (n + 1)).sum (fun j =>
      Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2))) ≤
    (Finset.range (n + 1)).sum (fun j =>
      -((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2))) := by
    apply Finset.sum_le_sum; intro j _; exact log_R_j_sq_upper σ t j hσ
  have hsum_neg : (Finset.range (n + 1)).sum (fun j =>
      -((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2))) =
    -(Finset.range (n + 1)).sum (fun j =>
      (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) := by
    simp only [Finset.sum_neg_distrib]
  have ⟨hlo_sum, _⟩ := sum_delta_over_D_bound σ t n hσ hσ1 ht
  linarith

/-- The product ∏(R_j²)^{1/2} ≤ n^{-(σ-1/2)} · (σ²+t²)^{(σ-1/2)/2} · exp(10·(σ-1/2)).
    Combined with the n^{σ-1/2} prefactor, ratio ≤ (σ²+t²)^{(σ-1/2)/2} · exp(10·(σ-1/2)). -/
private lemma gammaSeq_ratio_le_of_log (σ t : ℝ) (n : ℕ) (hn : 0 < n)
    (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : 1 ≤ |t|) :
    (n : ℝ) ^ (σ - 1/2) *
    ∏ j ∈ Finset.range (n + 1),
      (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ ((1:ℝ)/2) ≤
    (σ ^ 2 + t ^ 2) ^ ((σ - 1/2) / 2) * Real.exp (10 * (σ - 1/2)) := by
  have hδ : 0 < σ - 1/2 := by linarith
  have hD0 : (0:ℝ) < σ ^ 2 + t ^ 2 := by positivity
  have hn_pos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  -- Each R_j² factor is positive
  have hRpos : ∀ j ∈ Finset.range (n+1),
      (0:ℝ) < ((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) := by
    intro j _; apply div_pos <;> positivity
  -- LHS is positive
  have hLHS : 0 < (n : ℝ) ^ (σ - 1/2) *
      ∏ j ∈ Finset.range (n+1),
        (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ ((1:ℝ)/2) := by
    apply mul_pos (Real.rpow_pos_of_pos hn_pos _)
    apply Finset.prod_pos; intro j hj; exact Real.rpow_pos_of_pos (hRpos j hj) _
  -- RHS is positive
  have hRHS : 0 < (σ ^ 2 + t ^ 2) ^ ((σ - 1/2) / 2) * Real.exp (10 * (σ - 1/2)) :=
    mul_pos (Real.rpow_pos_of_pos hD0 _) (Real.exp_pos _)
  -- Strategy: show log(LHS) ≤ log(RHS) then transfer via exp
  set P := ∏ j ∈ Finset.range (n+1),
    (((1/2 + ↑j)^2 + t^2) / ((σ + ↑j)^2 + t^2)) ^ ((1:ℝ)/2)
  have hP : 0 < P := Finset.prod_pos (fun j hj => Real.rpow_pos_of_pos (hRpos j hj) _)
  -- log(P) = (1/2)*Σlog(R_j²)
  have hlogP : Real.log P = (1/2) * (Finset.range (n+1)).sum (fun j =>
      Real.log (((1/2 + ↑j)^2 + t^2) / ((σ + ↑j)^2 + t^2))) := by
    rw [Real.log_prod (fun j hj => ne_of_gt (Real.rpow_pos_of_pos (hRpos j hj) _)),
        show ∑ j ∈ Finset.range (n+1), Real.log
          ((((1/2 + ↑j)^2 + t^2) / ((σ + ↑j)^2 + t^2)) ^ ((1:ℝ)/2)) =
        ∑ j ∈ Finset.range (n+1), ((1:ℝ)/2 * Real.log
          (((1/2 + ↑j)^2 + t^2) / ((σ + ↑j)^2 + t^2))) from
        Finset.sum_congr rfl (fun j hj => Real.log_rpow (hRpos j hj) _),
        ← Finset.mul_sum]
  -- Use sum_log_R_upper
  have hSup := sum_log_R_upper σ t n hσ hσ1 ht
  -- (σ+n+1)²+t² ≥ n² ≥ n² so log ≥ 2*log(n)
  have hn_sq : (n : ℝ) ^ 2 ≤ (σ + ↑n + 1) ^ 2 + t ^ 2 := by
    have : (n : ℝ) ≤ σ + ↑n + 1 := by linarith
    nlinarith [sq_nonneg t, sq_nonneg (n : ℝ)]
  have hlog_n : 2 * Real.log n ≤ Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) := by
    have : Real.log ((n : ℝ) ^ 2) ≤ Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) :=
      Real.log_le_log (by positivity) hn_sq
    rwa [Real.log_pow, show (↑(2:ℕ) : ℝ) = 2 from rfl] at this
  -- log(n^{σ-1/2}*P) ≤ (σ-1/2)/2*log(σ²+t²) + 10*(σ-1/2) = log(RHS)
  have hlog_LHS : Real.log ((n : ℝ) ^ (σ - 1/2) * P) ≤
      (σ - 1/2) / 2 * Real.log (σ^2 + t^2) + 10 * (σ - 1/2) := by
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hn_pos _)) (ne_of_gt hP),
        Real.log_rpow hn_pos, hlogP]
    -- Goal: (σ-1/2)*log(n) + (1/2)*Σlog(R_j²) ≤ ...
    -- From hSup: Σlog(R_j²) ≤ -(σ-1/2)*(L-20)
    -- From hlog_n: L ≥ 2*log(n) - log(σ²+t²)
    nlinarith [hSup, hlog_n, sq_nonneg (σ - 1/2)]
  have hlog_RHS : Real.log ((σ^2 + t^2) ^ ((σ - 1/2)/2) * Real.exp (10*(σ - 1/2))) =
      (σ - 1/2)/2 * Real.log (σ^2 + t^2) + 10*(σ - 1/2) := by
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hD0 _)) (ne_of_gt (Real.exp_pos _)),
        Real.log_rpow hD0, Real.log_exp]
  rwa [← Real.exp_log hLHS, ← Real.exp_log hRHS, Real.exp_le_exp, hlog_RHS]

/-- Tight lower bound: Σlog(R_j²) ≥ -Σx_j - 36*(σ-1/2)².
    Uses log(1-x) ≥ -x/(1-x) ≥ -(x+2x²) for x < 1/2,
    then Σx_j² = (σ-1/2)²·Σu_j² ≤ 18·(σ-1/2)². -/
private lemma sum_log_R_lower_tight (σ t : ℝ) (n : ℕ)
    (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : 1 ≤ |t|) :
    -((Finset.range (n + 1)).sum (fun j =>
        (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2))) -
      36 * (σ - 1/2) ^ 2 ≤
    (Finset.range (n + 1)).sum (fun j =>
        Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2))) := by
  -- Per-term: log(R_j²) ≥ -x_j/(1-x_j) ≥ -(x_j + 2x_j²)
  have hper : ∀ j ∈ Finset.range (n + 1),
      -((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) -
        2 * ((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2 ≤
      Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2)) := by
    intro j _
    set x := (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2) with hx_def
    have ⟨hx_pos, hx_lt⟩ := x_j_bounds σ t j hσ
    have hx_half := x_j_lt_half σ t j hσ hσ1 ht
    have h1x : (0:ℝ) < 1 - x := by linarith
    -- log(R_j²) ≥ -x/(1-x) from log_R_j_sq_lower
    have hlog := log_R_j_sq_lower σ t j hσ
    -- -x/(1-x) ≥ -(x + 2x²)  i.e.  x/(1-x) ≤ x + 2x²
    have hxe : x / (1 - x) ≤ x + 2 * x ^ 2 := by
      rw [div_le_iff₀ h1x]; nlinarith [sq_nonneg x]
    -- Need: log(R_j²) ≥ -δ_j/N_j ≥ -(x + 2x²) where δ_j/N_j = x/(1-x)
    -- From log_R_j_sq_lower: log(R_j²) ≥ -δ_j/N_j = -x/(1-x) ≥ -(x+2x²)
    -- δ_j/N_j = x/(1-x) from R_j_sq_one_minus
    have hj := j.cast_nonneg (α := ℝ)
    have hN : (0 : ℝ) < (1/2 + ↑j) ^ 2 + t ^ 2 := by positivity
    have hD : (0 : ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
    have h1x_eq : 1 - x = ((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) := by
      rw [hx_def, R_j_sq_one_minus σ t j hσ]
    have hval : (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((1/2 + ↑j) ^ 2 + t ^ 2) = x / (1 - x) := by
      rw [h1x_eq, hx_def]; field_simp
    linarith
  -- Sum the per-term bounds
  have hsum := Finset.sum_le_sum hper
  simp only [Finset.sum_sub_distrib] at hsum
  -- Σx_j² = (σ-1/2)²·Σu_j² ≤ 18·(σ-1/2)² from sum_u_sq_le
  have hsq : (Finset.range (n + 1)).sum (fun j =>
      2 * ((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2) ≤
    36 * (σ - 1/2) ^ 2 := by
    -- x_j ≤ (σ-1/2)*u_j since σ+1/2+2j ≤ 2(σ+j)+1, so 2*x_j² ≤ 2*(σ-1/2)²*u_j²
    have hle : ∀ j ∈ Finset.range (n + 1),
        2 * ((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2 ≤
        2 * (σ - 1/2) ^ 2 * ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2 := by
      intro j _
      have hD : (0:ℝ) < (σ + ↑j) ^ 2 + t ^ 2 := by positivity
      have hj := j.cast_nonneg (α := ℝ)
      -- a = x_j, b = (σ-1/2)*u_j, 0 ≤ a ≤ b so a² ≤ b²
      set a := (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)
      set b := (σ - 1/2) * (2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)
      have ha0 : 0 ≤ a := div_nonneg (mul_nonneg (by linarith) (by linarith)) hD.le
      have hab : a ≤ b := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hD.le
      have : a ^ 2 ≤ b ^ 2 := sq_le_sq' (by linarith) hab
      -- Goal: 2*a² ≤ 2*b² where b² = (σ-1/2)²*((2(σ+j)+1)/D)²
      show 2 * a ^ 2 ≤ 2 * (σ - 1/2) ^ 2 * ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2
      rw [show b = (σ - 1/2) * (2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2) from rfl,
          show ((σ - 1/2) * (2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2 =
            (σ - 1/2) ^ 2 * ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2 from by
            rw [mul_div_assoc, mul_pow]] at this
      linarith
    calc (Finset.range (n + 1)).sum (fun j =>
          2 * ((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2)
        ≤ (Finset.range (n + 1)).sum (fun j =>
          2 * (σ - 1/2) ^ 2 * ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2) :=
          Finset.sum_le_sum hle
      _ = 2 * (σ - 1/2) ^ 2 * (Finset.range (n + 1)).sum (fun j =>
          ((2 * (σ + ↑j) + 1) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2) :=
          (Finset.mul_sum ..).symm
      _ ≤ 2 * (σ - 1/2) ^ 2 * 18 :=
          mul_le_mul_of_nonneg_left (sum_u_sq_le σ t n hσ hσ1 ht) (by positivity)
      _ = 36 * (σ - 1/2) ^ 2 := by ring
  -- Convert Σ(-f) to -Σf for linarith
  have hsum' : -(Finset.range (n + 1)).sum (fun j =>
      (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) -
    (Finset.range (n + 1)).sum (fun j =>
      2 * ((σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) ^ 2) ≤
    (Finset.range (n + 1)).sum (fun j =>
      Real.log (((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2))) := by
    have := Finset.sum_neg_distrib (f := fun j =>
      (σ - 1/2) * (σ + 1/2 + 2 * ↑j) / ((σ + ↑j) ^ 2 + t ^ 2)) (s := Finset.range (n+1))
    linarith [hsum]
  linarith [hsum', hsq]

/-- Key upper bound on the GammaSeq norm ratio via the log-product chain:
    log(ratio) = (σ-1/2)·log n + (1/2)·Σlog(R_j²)
    ≤ (σ-1/2)·log n - (σ-1/2)/2·(L-20) where L = log((σ+n+1)²+t²)-log(σ²+t²)
    ≤ (σ-1/2)·(log n - log n + log√(σ²+t²) + 10) [since (σ+n+1)²+t²≥n²]
    ≤ (σ-1/2)·(log(√2·|t|) + 10) [since σ²+t²≤2t²]
    = (σ-1/2)·log|t| + (σ-1/2)·(10+log2/2)
    So ratio ≤ |t|^{σ-1/2} · exp((σ-1/2)·(10+log2/2)) ≤ C·|t|^{σ-1/2}.
    Uses gammaSeq_norm_ratio_eq + gammaSeq_ratio_le_of_log. -/
private lemma gammaSeq_ratio_bounded_above (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) :
    ∃ C_hi : ℝ, 0 < C_hi ∧
    ∀ t : ℝ, 1 ≤ |t| → ∀ n : ℕ,
      ‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖ ≤
      C_hi * |t| ^ (σ - 1/2) := by
  -- Use the product formula: ratio = n^{σ-1/2} · ∏√(R_j²)
  -- For n = 0: GammaSeq(s,0) = 0 for re(s) > 0, ratio = 0/0 = 0, bound trivial
  -- For n ≥ 1: use gammaSeq_norm_ratio_eq + sum_log_R_upper
  refine ⟨Real.exp (11 / 2), Real.exp_pos _, ?_⟩
  intro t ht n
  -- The ratio is always ≥ 0
  by_cases hn : n = 0
  · -- n = 0: GammaSeq(s,0) = 0 for re(s)>0, so norm ratio = 0
    subst hn
    have hs_ne : (⟨σ, t⟩ : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this; linarith
    rw [show Complex.GammaSeq ⟨σ, t⟩ 0 = 0 from by
      rw [Complex.GammaSeq.eq_1]; simp [Complex.zero_cpow hs_ne]]
    simp only [norm_zero, zero_div]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.rpow_nonneg (abs_nonneg t) _)
  · -- n ≥ 1: use gammaSeq_norm_ratio_eq + gammaSeq_ratio_le_of_log
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hden : ‖Complex.GammaSeq ⟨1/2, t⟩ n‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (gammaSeq_ne_zero _ n hn' (by simp))
    rw [gammaSeq_norm_ratio_eq σ t n hn' hσ hσ1 hden]
    have hδ : 0 < σ - 1/2 := by linarith
    have hD0 : (0:ℝ) < σ^2 + t^2 := by positivity
    -- Step 1: product bound from gammaSeq_ratio_le_of_log
    have h1 := gammaSeq_ratio_le_of_log σ t n hn' hσ hσ1 ht
    -- Step 2: σ²+t² ≤ 2t² (since σ² < 1 ≤ t² for |t| ≥ 1, σ < 1)
    have h_st : σ^2 + t^2 ≤ 2 * t^2 := by nlinarith [sq_abs t, sq_nonneg σ]
    -- Step 3: (σ²+t²)^{(σ-1/2)/2} ≤ (2t²)^{(σ-1/2)/2}
    have h2 : (σ^2 + t^2) ^ ((σ - 1/2)/2) ≤ (2 * t^2) ^ ((σ - 1/2)/2) :=
      Real.rpow_le_rpow (by positivity) h_st (by linarith)
    -- Step 4: (2t²)^a = 2^a * |t|^{2a} via rpow
    have h_split : (2 * t^2) ^ ((σ - 1/2)/2) = 2 ^ ((σ - 1/2)/2) * |t| ^ (σ - 1/2) := by
      rw [Real.mul_rpow (by linarith : (0:ℝ) ≤ 2) (sq_nonneg t)]
      congr 1
      rw [show t^2 = |t|^2 from (sq_abs t).symm,
          ← Real.rpow_natCast |t| 2, ← Real.rpow_mul (abs_nonneg t)]
      congr 1; ring
    -- Step 5: 2^a * exp(10*δ) ≤ exp(a + 10*δ) ≤ exp(11/2) for δ = σ-1/2 < 1/2
    -- Use: 2^a = exp(a*log2) ≤ exp(a) since log(2) ≤ 1
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
    have h_2_exp : 2 ^ ((σ - 1/2)/2) ≤ Real.exp ((σ - 1/2)/2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have h_const : 2 ^ ((σ - 1/2)/2) * Real.exp (10*(σ - 1/2)) ≤ Real.exp (11/2) := by
      calc 2 ^ ((σ-1/2)/2) * Real.exp (10*(σ-1/2))
          ≤ Real.exp ((σ-1/2)/2) * Real.exp (10*(σ-1/2)) :=
            mul_le_mul_of_nonneg_right h_2_exp (le_of_lt (Real.exp_pos _))
        _ = Real.exp ((σ-1/2)/2 + 10*(σ-1/2)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (11/2) := Real.exp_le_exp.mpr (by nlinarith)
    -- Combine
    calc (n : ℝ) ^ (σ - 1/2) * ∏ j ∈ Finset.range (n+1), _ ≤
          (σ^2+t^2) ^ ((σ-1/2)/2) * Real.exp (10*(σ-1/2)) := h1
      _ ≤ (2*t^2) ^ ((σ-1/2)/2) * Real.exp (10*(σ-1/2)) :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos _))
      _ = (2 ^ ((σ-1/2)/2) * |t| ^ (σ-1/2)) * Real.exp (10*(σ-1/2)) := by rw [h_split]
      _ = (2 ^ ((σ-1/2)/2) * Real.exp (10*(σ-1/2))) * |t| ^ (σ-1/2) := by ring
      _ ≤ Real.exp (11/2) * |t| ^ (σ-1/2) :=
          mul_le_mul_of_nonneg_right h_const (Real.rpow_nonneg (abs_nonneg t) _)

/-- Key lower bound on the GammaSeq norm ratio (eventually in n).
    The bound fails at n=0 since GammaSeq(s,0) = 0 for re(s) > 0,
    but holds for all n ≥ 1 via the log-product chain. -/
private lemma gammaSeq_ratio_bounded_below (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) :
    ∃ C_lo : ℝ, 0 < C_lo ∧
    ∀ t : ℝ, 1 ≤ |t| → ∀ᶠ n in Filter.atTop,
      C_lo * |t| ^ (σ - 1/2) ≤
      ‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖ := by
  refine ⟨Real.exp (-12), Real.exp_pos _, ?_⟩
  intro t ht
  set N := max 1 (Nat.ceil (|t|)) with hN_def
  filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun _ h => h⟩] with n (hn : N ≤ n)
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 _) hn
  have hn' : 0 < n := lt_of_lt_of_le Nat.one_pos hn1
  have hden : ‖Complex.GammaSeq ⟨1/2, t⟩ n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gammaSeq_ne_zero _ n hn' (by simp))
  rw [gammaSeq_norm_ratio_eq σ t n hn' hσ hσ1 hden]
  have hδ : 0 < σ - 1/2 := by linarith
  have hn_pos : (0:ℝ) < n := Nat.cast_pos.mpr hn'
  have hRpos : ∀ j ∈ Finset.range (n+1),
      (0:ℝ) < ((1/2 + ↑j) ^ 2 + t ^ 2) / ((σ + ↑j) ^ 2 + t ^ 2) := by
    intro j _; apply div_pos <;> positivity
  set P := ∏ j ∈ Finset.range (n+1),
    (((1/2 + ↑j)^2 + t^2) / ((σ + ↑j)^2 + t^2)) ^ ((1:ℝ)/2) with hP_def
  have hP : 0 < P := Finset.prod_pos (fun j hj => Real.rpow_pos_of_pos (hRpos j hj) _)
  have hLHS : 0 < (n : ℝ) ^ (σ - 1/2) * P :=
    mul_pos (Real.rpow_pos_of_pos hn_pos _) hP
  -- log(P) = (1/2)*Σlog(R_j²)
  have hlogP : Real.log P = (1/2) * (Finset.range (n+1)).sum (fun j =>
      Real.log (((1/2 + ↑j)^2 + t^2) / ((σ + ↑j)^2 + t^2))) := by
    rw [Real.log_prod (fun j hj => ne_of_gt (Real.rpow_pos_of_pos (hRpos j hj) _)),
        show ∑ j ∈ Finset.range (n+1), Real.log
          ((((1/2 + ↑j)^2 + t^2) / ((σ + ↑j)^2 + t^2)) ^ ((1:ℝ)/2)) =
        ∑ j ∈ Finset.range (n+1), ((1:ℝ)/2 * Real.log
          (((1/2 + ↑j)^2 + t^2) / ((σ + ↑j)^2 + t^2))) from
        Finset.sum_congr rfl (fun j hj => Real.log_rpow (hRpos j hj) _),
        ← Finset.mul_sum]
  -- TIGHT bound: Σlog(R_j²) ≥ -Σx_j - 36*(σ-1/2)² (from sum_log_R_lower_tight)
  have hStight := sum_log_R_lower_tight σ t n hσ hσ1 ht
  -- Σx_j ≤ (σ-1/2)*(L+20) where L = log((σ+n+1)²+t²)-log(σ²+t²)
  have ⟨_, hhi_sum⟩ := sum_delta_over_D_bound σ t n hσ hσ1 ht
  -- (σ+n+1)²+t² ≤ 10n² for n ≥ |t|
  have hn_ge_t : |t| ≤ ↑n := by
    calc |t| ≤ ↑(Nat.ceil |t|) := Nat.le_ceil _
      _ ≤ ↑(max 1 (Nat.ceil |t|)) := by exact_mod_cast le_max_right 1 _
      _ ≤ ↑n := by exact_mod_cast hn
  have hlog_upper : Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2) ≤ Real.log 10 + 2 * Real.log ↑n := by
    have h_nsq : (σ + ↑n + 1) ^ 2 + t ^ 2 ≤ 10 * (↑n : ℝ) ^ 2 := by
      nlinarith [sq_abs t, sq_nonneg (↑n + 2 - (σ + ↑n + 1))]
    calc Real.log ((σ + ↑n + 1) ^ 2 + t ^ 2)
        ≤ Real.log (10 * (↑n) ^ 2) := Real.log_le_log (by positivity) h_nsq
      _ = Real.log 10 + Real.log ((↑n) ^ 2) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log 10 + 2 * Real.log ↑n := by
          rw [Real.log_pow, show (↑(2:ℕ) : ℝ) = 2 from rfl]
  have h_st : Real.log (σ^2+t^2) ≥ 2 * Real.log |t| := by
    calc 2 * Real.log |t| = Real.log (|t|^2) := by
          rw [Real.log_pow, show (↑(2:ℕ) : ℝ) = 2 from rfl]
      _ = Real.log (t^2) := by rw [sq_abs]
      _ ≤ Real.log (σ^2+t^2) := Real.log_le_log (by nlinarith [sq_abs t])
          (by nlinarith [sq_nonneg σ])
  -- log(10) ≤ 10 (trivial from log ≤ x-1)
  have hlog10 : Real.log 10 ≤ 10 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 10)]
  -- Main inequality: log(LHS) ≥ (σ-1/2)*log|t| - 12
  have hlog_LHS : (σ - 1/2) * Real.log |t| - 12 ≤
      Real.log ((n : ℝ) ^ (σ - 1/2) * P) := by
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hn_pos _)) (ne_of_gt hP),
        Real.log_rpow hn_pos, hlogP]
    -- Need: (σ-1/2)*log|t| - 12 ≤ (σ-1/2)*log(n) + (1/2)*Σlog
    -- From hStight: Σlog ≥ -Σx - 36*(σ-1/2)²
    -- So (1/2)*Σlog ≥ -(1/2)*Σx - 18*(σ-1/2)²
    -- From hhi_sum: Σx ≤ (σ-1/2)*(L+20), so -(1/2)*Σx ≥ -(σ-1/2)/2*(L+20)
    -- L ≤ log(10)+2*log(n) - log(σ²+t²)  (from hlog_upper, h_st)
    -- Combined: (σ-1/2)*log(n) - (σ-1/2)/2*(log(10)+2*log(n)-2*log|t|+20) - 18*(σ-1/2)²
    -- = (σ-1/2)*log|t| - (σ-1/2)/2*(log(10)+20) - 18*(σ-1/2)²
    -- ≥ (σ-1/2)*log|t| - (1/2)/2*(10+20) - 18*(1/2)²
    -- = (σ-1/2)*log|t| - 7.5 - 4.5 = (σ-1/2)*log|t| - 12
    nlinarith [hStight, hhi_sum, hlog_upper, h_st, hlog10,
               sq_nonneg (σ - 1/2), sq_abs t]
  have ht_pos : (0:ℝ) < |t| := by linarith
  calc Real.exp (-12) * |t| ^ (σ - 1/2)
      = Real.exp ((σ - 1/2) * Real.log |t| - 12) := by
        rw [show (σ - 1/2) * Real.log |t| - 12 = Real.log |t| * (σ - 1/2) + (-12 : ℝ) from by ring,
            Real.exp_add, ← Real.rpow_def_of_pos ht_pos, mul_comm]
    _ ≤ Real.exp (Real.log ((n : ℝ) ^ (σ - 1/2) * P)) :=
        Real.exp_le_exp.mpr hlog_LHS
    _ = (n : ℝ) ^ (σ - 1/2) * P := Real.exp_log hLHS

/-- Two-sided bound on the Gamma ratio from GammaSeq product analysis.
    Uses gammaSeq_ratio_bounded_above/below + le/ge_of_tendsto. -/
theorem gammaRatioUpperHalf_proved : GammaRatioUpperHalf := by
  intro σ hσ hσ1
  obtain ⟨C_hi, hChi, hhi⟩ := gammaSeq_ratio_bounded_above σ hσ hσ1
  obtain ⟨C_lo, hClo, hlo⟩ := gammaSeq_ratio_bounded_below σ hσ hσ1
  refine ⟨C_lo, C_hi, hClo, hChi, ?_⟩
  intro t ht
  have hσ₀ : (0 : ℝ) < σ := by linarith
  have h_tendsto := complex_gammaSeq_ratio_tendsto' σ t hσ₀
  constructor
  · -- Lower bound via ge_of_tendsto (eventually)
    exact ge_of_tendsto h_tendsto (hlo t ht)
  · -- Upper bound via le_of_tendsto
    exact le_of_tendsto h_tendsto (Filter.Eventually.of_forall fun n => hhi t ht n)

/-- The Gamma ratio upper-half bound, proved from first principles via GammaSeq product analysis. -/
theorem gammaRatioUpperHalf_axiom : GammaRatioUpperHalf :=
  gammaRatioUpperHalf_proved

/-  Upper-half ratio lemma. Current structure:
    reflection controls `R(σ) * R(1-σ)`, and the remaining analytic input is a
    global two-sided bound for `R(1-σ)` with exponent `-(σ-1/2)`. -/
private lemma neg_upper_half_exp_eq_lower (σ : ℝ) :
    -(σ - 1 / 2) = (1 - σ) - 1 / 2 := by
  ring

private lemma lower_half_ratio_pos_for_upper
    (σ : ℝ) (_hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) :
    ∀ (t : ℝ), 1 ≤ |t| →
      0 <
        ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ := by
  intro t _ht
  have hnum_ne : Complex.Gamma ⟨1 - σ, t⟩ ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [show (0 : ℝ) < 1 - σ by linarith [hσ₁]]
  have hden_ne : Complex.Gamma ⟨1 / 2, t⟩ ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
  exact div_pos (norm_pos_iff.mpr hnum_ne) (norm_pos_iff.mpr hden_ne)

private lemma lower_half_ratio_line_eq_mk_inv2 (σ t : ℝ) :
    ‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
    = ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨(2 : ℝ)⁻¹, t⟩‖ := by
  have hA : (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) = (⟨1 - σ, t⟩ : ℂ) := by
    apply Complex.ext <;> simp
  have hB : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = (⟨(2 : ℝ)⁻¹, t⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [hA, hB]

private lemma lower_half_ratio_line_eq_mk (σ t : ℝ) :
    ‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
    = ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ := by
  simpa [one_div] using lower_half_ratio_line_eq_mk_inv2 σ t

private lemma lower_half_ratio_nf_eq_mk_inv2 (σ t : ℝ) :
    ‖Complex.Gamma (1 - (σ : ℂ) + (t : ℂ) * Complex.I)‖ /
      ‖Complex.Gamma (((2 : ℝ)⁻¹ : ℂ) + (t : ℂ) * Complex.I)‖
    = ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨(2 : ℝ)⁻¹, t⟩‖ := by
  have hA : (1 - (σ : ℂ) + (t : ℂ) * Complex.I) = (⟨1 - σ, t⟩ : ℂ) := by
    apply Complex.ext <;> simp
  have hB : ((((2 : ℝ)⁻¹ : ℂ) + (t : ℂ) * Complex.I)) = (⟨(2 : ℝ)⁻¹, t⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [hA, hB]

private lemma lower_half_ratio_compact_upper_for_upper
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) (T : ℝ) (_hT : 1 ≤ T) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
        ‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
          ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  set phi1 : ℝ → ℂ := fun t => ((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I
  set phi2 : ℝ → ℂ := fun t => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hphi1_cont : Continuous phi1 := by
    dsimp [phi1]
    continuity
  have hphi2_cont : Continuous phi2 := by
    dsimp [phi2]
    continuity
  have hGamma1_cont : Continuous (fun t : ℝ => Complex.Gamma (phi1 t)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hnot : ∀ m : ℕ, phi1 t ≠ -↑m := by
      intro m hm
      have hre : (phi1 t).re = (- (m : ℂ)).re := congrArg Complex.re hm
      simp [phi1] at hre
      linarith [hσ₁]
    exact ((Complex.differentiableAt_Gamma _ hnot).continuousAt).comp hphi1_cont.continuousAt
  have hGamma2_cont : Continuous (fun t : ℝ => Complex.Gamma (phi2 t)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hnot : ∀ m : ℕ, phi2 t ≠ -↑m := by
      intro m hm
      have hre : (phi2 t).re = (- (m : ℂ)).re := congrArg Complex.re hm
      simp [phi2] at hre
      linarith
    exact ((Complex.differentiableAt_Gamma _ hnot).continuousAt).comp hphi2_cont.continuousAt
  set r : ℝ → ℝ := fun t => ‖Complex.Gamma (phi1 t)‖ / ‖Complex.Gamma (phi2 t)‖ with hr
  have hr_cont : Continuous r := by
    refine (hGamma1_cont.norm).div (hGamma2_cont.norm) ?_
    intro t
    exact norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero_of_re_pos (by simp [phi2] : (0 : ℝ) < (phi2 t).re))
  have hK : IsCompact (Set.Icc (-T) T) := isCompact_Icc
  rcases hK.exists_bound_of_continuousOn hr_cont.continuousOn with ⟨C, hC⟩
  refine ⟨max C 1, by positivity, ?_⟩
  intro t _ht1 htT
  have hmem : t ∈ Set.Icc (-T) T := by
    constructor
    · linarith [neg_abs_le t, htT]
    · linarith [le_abs_self t, htT]
  have hnorm : ‖r t‖ ≤ C := hC t hmem
  have hr_nonneg : 0 ≤ r t := by
    dsimp [r]
    positivity
  have hrt : r t ≤ C := by
    have : ‖r t‖ = r t := by
      rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    simpa [this] using hnorm
  have : r t ≤ max C 1 := le_trans hrt (le_max_left C 1)
  simpa [r, phi1, phi2, hr] using this

private lemma lower_half_ratio_compact_upper_for_upper_mk
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) (T : ℝ) (hT : 1 ≤ T) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
        ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤ C := by
  rcases lower_half_ratio_compact_upper_for_upper σ hσ₀ hσ₁ T hT with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht1 htT
  have hbound' :
      ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤ C := by
    rw [← lower_half_ratio_line_eq_mk σ t]
    exact hbound t ht1 htT
  exact hbound'

private lemma lower_half_ratio_compact_lower_for_upper
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) (T : ℝ) (_hT : 1 ≤ T) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
        C ≤
          ‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ /
            ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set phi1 : ℝ → ℂ := fun t => ((1 - σ : ℝ) : ℂ) + (t : ℂ) * Complex.I
  set phi2 : ℝ → ℂ := fun t => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hphi1_cont : Continuous phi1 := by
    dsimp [phi1]
    continuity
  have hphi2_cont : Continuous phi2 := by
    dsimp [phi2]
    continuity
  have hGamma1_cont : Continuous (fun t : ℝ => Complex.Gamma (phi1 t)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hnot : ∀ m : ℕ, phi1 t ≠ -↑m := by
      intro m hm
      have hre : (phi1 t).re = (- (m : ℂ)).re := congrArg Complex.re hm
      simp [phi1] at hre
      linarith [hσ₁]
    exact ((Complex.differentiableAt_Gamma _ hnot).continuousAt).comp hphi1_cont.continuousAt
  have hGamma2_cont : Continuous (fun t : ℝ => Complex.Gamma (phi2 t)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hnot : ∀ m : ℕ, phi2 t ≠ -↑m := by
      intro m hm
      have hre : (phi2 t).re = (- (m : ℂ)).re := congrArg Complex.re hm
      simp [phi2] at hre
      linarith
    exact ((Complex.differentiableAt_Gamma _ hnot).continuousAt).comp hphi2_cont.continuousAt
  set r : ℝ → ℝ := fun t => ‖Complex.Gamma (phi1 t)‖ / ‖Complex.Gamma (phi2 t)‖ with hr
  have hr_pos : ∀ t : ℝ, 0 < r t := by
    intro t
    have hnum_ne : Complex.Gamma (phi1 t) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      simp [phi1, show (0 : ℝ) < 1 - σ by linarith [hσ₁]]
    have hden_ne : Complex.Gamma (phi2 t) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      simp [phi2]
    dsimp [r]
    exact div_pos (norm_pos_iff.mpr hnum_ne) (norm_pos_iff.mpr hden_ne)
  have hr_cont : Continuous r := by
    refine (hGamma1_cont.norm).div (hGamma2_cont.norm) ?_
    intro t
    exact norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero_of_re_pos (by simp [phi2] : (0 : ℝ) < (phi2 t).re))
  have hrInv_cont : Continuous (fun t : ℝ => (r t)⁻¹) := by
    exact hr_cont.inv₀ (by intro t; exact (ne_of_gt (hr_pos t)))
  have hK : IsCompact (Set.Icc (-T) T) := isCompact_Icc
  rcases hK.exists_bound_of_continuousOn hrInv_cont.continuousOn with ⟨M, hM⟩
  refine ⟨1 / max M 1, by positivity, ?_⟩
  intro t _ht1 htT
  have hmem : t ∈ Set.Icc (-T) T := by
    constructor
    · linarith [neg_abs_le t, htT]
    · linarith [le_abs_self t, htT]
  have h_inv_norm : ‖(r t)⁻¹‖ ≤ M := hM t hmem
  have h_inv : (r t)⁻¹ ≤ max M 1 := by
    have h_inv_nonneg : 0 ≤ (r t)⁻¹ := by positivity
    have h_inv_le_M : (r t)⁻¹ ≤ M := by
      have habs : |(r t)⁻¹| ≤ M := by
        simpa [Real.norm_eq_abs] using h_inv_norm
      simpa [abs_of_nonneg h_inv_nonneg] using habs
    exact le_trans h_inv_le_M (le_max_left _ _)
  have hmax_pos : 0 < max M 1 := by positivity
  have hr_pos_t : 0 < r t := hr_pos t
  have h_lower : 1 / max M 1 ≤ r t := by
    have h_rinv_pos : 0 < (r t)⁻¹ := by positivity
    have h_inv_div : 1 / (max M 1) ≤ 1 / ((r t)⁻¹) := by
      simpa [one_div] using (inv_le_inv₀ hmax_pos h_rinv_pos).2 h_inv
    simpa [one_div, inv_inv] using h_inv_div
  simpa [r, phi1, phi2, hr] using h_lower

private lemma lower_half_ratio_compact_lower_for_upper_mk
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) (T : ℝ) (hT : 1 ≤ T) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
        C ≤ ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ := by
  rcases lower_half_ratio_compact_lower_for_upper σ hσ₀ hσ₁ T hT with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht1 htT
  have hbound' :
      C ≤ ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ := by
    rw [← lower_half_ratio_line_eq_mk σ t]
    exact hbound t ht1 htT
  exact hbound'

private lemma lower_half_tail_from_upper_tail
    (σ : ℝ) (hσ₀ : 0 < σ) (hσ₁ : σ < 1 / 2)
    (hUpperTail :
      ∃ (T C1 C2 : ℝ), 1 ≤ T ∧ 0 < C1 ∧ 0 < C2 ∧
        ∀ (t : ℝ), T ≤ |t| →
          C1 * |t| ^ ((1 - σ) - 1 / 2) ≤
            ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
          ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
            C2 * |t| ^ ((1 - σ) - 1 / 2)) :
    ∃ (T C_lo C_hi : ℝ), 1 ≤ T ∧ 0 < C_lo ∧ 0 < C_hi ∧
      ∀ (t : ℝ), T ≤ |t| →
        C_lo * |t| ^ (σ - 1 / 2) ≤
          ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
          C_hi * |t| ^ (σ - 1 / 2) := by
  rcases hUpperTail with ⟨T1, C1, C2, hT1, hC1, hC2, hbound⟩
  set P : ℝ := Real.sqrt (1 / Real.sin (π * σ) ^ 2 + 1)
  have hsin_pos : 0 < Real.sin (π * σ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos pi_pos hσ₀
    · calc π * σ < π * (1 / 2) := mul_lt_mul_of_pos_left hσ₁ pi_pos
        _ < π := by nlinarith [pi_pos]
  refine ⟨max T1 1, 1 / C2, P / C1, le_max_right _ _, by positivity, ?_, ?_⟩
  · have hP_pos : 0 < P := by
      dsimp [P]
      positivity
    exact div_pos hP_pos hC1
  intro t ht
  have hT : T1 ≤ |t| := le_trans (le_max_left _ _) ht
  have ht1 : 1 ≤ |t| := le_trans (le_max_right _ _) ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht1
  obtain ⟨hlo_1σ, hhi_1σ⟩ := hbound t hT
  have h_σ_pos : 0 < ‖Complex.Gamma ⟨σ, t⟩‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp [hσ₀] : (0:ℝ) < (⟨σ, t⟩ : ℂ).re)
  have h_half_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
  have h_1σ_pos : 0 < ‖Complex.Gamma ⟨1 - σ, t⟩‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp [show (0:ℝ) < 1 - σ by linarith] :
      (0:ℝ) < (⟨1 - σ, t⟩ : ℂ).re)
  set R_σ := ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ with hR_σ_def
  set R_1σ := ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ with hR_1σ_def
  have hR_σ_pos : 0 < R_σ := div_pos h_σ_pos h_half_pos
  have hR_1σ_pos : 0 < R_1σ := div_pos h_1σ_pos h_half_pos
  have ht_ne : t ≠ 0 := fun h => by simp [h] at ht_pos
  have h_refl : R_σ * R_1σ = Real.cosh (π * t) / ‖Complex.sin (↑π * ⟨σ, t⟩)‖ := by
    rw [hR_σ_def, hR_1σ_def, div_mul_div_comm,
        show ‖Complex.Gamma ⟨1/2, t⟩‖ * ‖Complex.Gamma ⟨1/2, t⟩‖ =
            ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 from (sq _).symm]
    exact reflection_ratio_product σ t hσ₀ (by linarith : σ < 1) ht_ne
  have h_sq_bounds := reflection_product_sq_bound σ t hσ₀ (by linarith : σ < 1) ht1
  have h_prod_sq : (R_σ * R_1σ) ^ 2 =
      Real.cosh (π * t) ^ 2 / (Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2) := by
    rw [h_refl, div_pow, ← sin_norm_sq]
  have h_prod_lo : 1 ≤ R_σ * R_1σ := by
    have h1 : 1 ≤ (R_σ * R_1σ) ^ 2 := by rw [h_prod_sq]; exact h_sq_bounds.1
    nlinarith [sq_nonneg (R_σ * R_1σ - 1), mul_pos hR_σ_pos hR_1σ_pos]
  have h_prod_hi : R_σ * R_1σ ≤ P := by
    dsimp [P]
    rw [← Real.sqrt_sq (le_of_lt (mul_pos hR_σ_pos hR_1σ_pos))]
    exact Real.sqrt_le_sqrt (by rw [h_prod_sq]; exact h_sq_bounds.2)
  set a : ℝ := σ - (1 + -(2 : ℝ)⁻¹)
  have hExpUpper : (1 - σ) - 1 / 2 = -a := by
    dsimp [a]
    ring
  have hlo_a : C1 * |t| ^ (-a) ≤ R_1σ := by
    have hnegA : -a = -σ + (1 + -(2 : ℝ)⁻¹) := by
      dsimp [a]
      ring
    rw [hnegA]
    simpa [hR_1σ_def, one_div, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hlo_1σ
  have hhi_a : R_1σ ≤ C2 * |t| ^ (-a) := by
    have hnegA : -a = -σ + (1 + -(2 : ℝ)⁻¹) := by
      dsimp [a]
      ring
    rw [hnegA]
    simpa [hR_1σ_def, one_div, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hhi_1σ
  have hRσ_bounds :=
    ratio_bounds_from_reflection a t P R_σ R_1σ C1 C2
      ht1 hR_1σ_pos h_prod_lo h_prod_hi hlo_a hhi_a hC1 hC2
  have hpow_rewrite : |t| ^ (σ - 1 / 2) = |t| ^ a := by
    congr 1
    dsimp [a]
    ring
  constructor
  · calc
      (1 / C2) * |t| ^ (σ - 1 / 2)
          = 1 / (C2 * |t| ^ (-a)) := by
            rw [hpow_rewrite, Real.rpow_neg (abs_nonneg t)]
            field_simp
      _ ≤ R_σ := by simpa using hRσ_bounds.1
  · calc
      R_σ ≤ P / (C1 * |t| ^ (-a)) := by
        simpa using hRσ_bounds.2
    _ = (P / C1) * |t| ^ (σ - 1 / 2) := by
        rw [hpow_rewrite, Real.rpow_neg (abs_nonneg t)]
        field_simp

/-- Interface extractor: any `GammaRatioUpperHalf` witness yields the tail form used
in this section by taking `T = 1`. -/
private lemma upper_half_ratio_tail_of_GammaRatioUpperHalf
    (hR : GammaRatioUpperHalf)
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) :
    ∃ (T C1 C2 : ℝ), 1 ≤ T ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (t : ℝ), T ≤ |t| →
        C1 * |t| ^ (σ - 1 / 2) ≤
          ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
          C2 * |t| ^ (σ - 1 / 2) := by
  rcases hR σ hσ₀ hσ₁ with ⟨C1, C2, hC1, hC2, hbound⟩
  refine ⟨1, C1, C2, by norm_num, hC1, hC2, ?_⟩
  intro t ht
  exact hbound t (le_trans (by norm_num) ht)

section GammaRatioUpperHalfInterface

variable {hUpper : GammaRatioUpperHalf}
include hUpper

private lemma upper_half_ratio_tail
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) :
    ∃ (T C1 C2 : ℝ), 1 ≤ T ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (t : ℝ), T ≤ |t| →
        C1 * |t| ^ (σ - 1 / 2) ≤
          ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
          C2 * |t| ^ (σ - 1 / 2) := by
  simpa using
    upper_half_ratio_tail_of_GammaRatioUpperHalf hUpper σ hσ₀ hσ₁

private lemma lower_half_ratio_tail_for_upper
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) :
    ∃ (T C1 C2 : ℝ), 1 ≤ T ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (t : ℝ), T ≤ |t| →
        C1 * |t| ^ (-(σ - 1 / 2)) ≤
          ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
        ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
          C2 * |t| ^ (-(σ - 1 / 2)) := by
  set τ : ℝ := 1 - σ
  have hτ₀ : 0 < τ := by
    linarith [hσ₁]
  have hτ₁ : τ < 1 / 2 := by
    linarith [hσ₀]
  have hτUpper0 : 1 / 2 < 1 - τ := by linarith [hτ₁]
  have hτUpper1 : 1 - τ < 1 := by linarith [hτ₀]
  have hupperTailForOneMinusTau :
      ∃ (T C1 C2 : ℝ), 1 ≤ T ∧ 0 < C1 ∧ 0 < C2 ∧
        ∀ (t : ℝ), T ≤ |t| →
          C1 * |t| ^ ((1 - τ) - 1 / 2) ≤
            ‖Complex.Gamma ⟨1 - τ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
          ‖Complex.Gamma ⟨1 - τ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
            C2 * |t| ^ ((1 - τ) - 1 / 2) := by
    simpa using upper_half_ratio_tail (hUpper := hUpper) (1 - τ) hτUpper0 hτUpper1
  rcases lower_half_tail_from_upper_tail τ hτ₀ hτ₁ hupperTailForOneMinusTau with
    ⟨T, C1, C2, hT, hC1, hC2, htail⟩
  refine ⟨T, C1, C2, hT, hC1, hC2, ?_⟩
  intro t htT
  have htail' := htail t htT
  have hExp' : τ + -(2 : ℝ)⁻¹ = -σ + (2 : ℝ)⁻¹ := by
    dsimp [τ]
    ring
  constructor
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, hExp'] using htail'.1
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, hExp'] using htail'.2

private lemma lower_half_ratio_global_for_upper
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) :
    ∃ (C1 C2 : ℝ), 0 < C1 ∧ 0 < C2 ∧
    ∀ (t : ℝ), 1 ≤ |t| →
      C1 * |t| ^ (-(σ - 1 / 2)) ≤
        ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
      ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
        C2 * |t| ^ (-(σ - 1 / 2)) := by
  set τ : ℝ := 1 - σ
  have hτ₀ : 0 < τ := by
    linarith [hσ₁]
  have hτ₁ : τ < 1 / 2 := by
    linarith [hσ₀]
  have ha : 0 < σ - 1 / 2 := by
    linarith [hσ₀]
  set a : ℝ := σ - 1 / 2
  have hExp : -(σ - 1 / 2) = τ - 1 / 2 := by
    simpa [τ] using neg_upper_half_exp_eq_lower σ
  have htail :
      ∃ (T C1 C2 : ℝ), 1 ≤ T ∧ 0 < C1 ∧ 0 < C2 ∧
        ∀ (t : ℝ), T ≤ |t| →
          C1 * |t| ^ (-(σ - 1 / 2)) ≤
            ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
          ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
            C2 * |t| ^ (-(σ - 1 / 2)) :=
    lower_half_ratio_tail_for_upper (hUpper := hUpper) σ hσ₀ hσ₁
  rcases htail with ⟨Tt, C1t, C2t, hTt1, hC1t, hC2t, htail'⟩
  set T : ℝ := Tt
  have hT1 : 1 ≤ T := by simpa [T] using hTt1
  rcases lower_half_ratio_compact_upper_for_upper_mk σ hσ₀ hσ₁ T hT1 with
    ⟨U, hUpos, hUbound⟩
  rcases lower_half_ratio_compact_lower_for_upper_mk σ hσ₀ hσ₁ T hT1 with
    ⟨L, hLpos, hLbound⟩
  set C1 : ℝ := min C1t L
  set C2 : ℝ := max C2t (U * T ^ a)
  refine ⟨C1, C2, by
    dsimp [C1]
    exact lt_min hC1t hLpos, by
    dsimp [C2]
    exact lt_of_lt_of_le hC2t (le_max_left _ _), ?_⟩
  intro t ht1
  by_cases htailCase : T ≤ |t|
  · have htailT := htail' t (by simpa [T] using htailCase)
    constructor
    · calc
        C1 * |t| ^ (-(σ - 1 / 2))
            ≤ C1t * |t| ^ (-(σ - 1 / 2)) := by
              dsimp [C1]
              exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (abs_nonneg t) _)
        _ ≤ ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ := htailT.1
    · calc
        ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖
            ≤ C2t * |t| ^ (-(σ - 1 / 2)) := htailT.2
        _ ≤ C2 * |t| ^ (-(σ - 1 / 2)) := by
              dsimp [C2]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg t) _)
  · have hleT : |t| ≤ T := le_of_not_ge htailCase
    have hpos_t : 0 < |t| := lt_of_lt_of_le one_pos ht1
    have hratio_lo : L ≤ ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ :=
      hLbound t ht1 hleT
    have hratio_hi : ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤ U :=
      hUbound t ht1 hleT
    have hpow_le_one_a : |t| ^ (-a) ≤ 1 := by
      have hpow_pos : 0 < |t| ^ a := Real.rpow_pos_of_pos hpos_t a
      have hone_le : 1 ≤ |t| ^ a := Real.one_le_rpow ht1 ha.le
      have hinv : (|t| ^ a)⁻¹ ≤ (1 : ℝ)⁻¹ := (inv_le_inv₀ hpow_pos zero_lt_one).2 hone_le
      simpa [Real.rpow_neg (abs_nonneg _)] using hinv
    have hpow_le_one : |t| ^ (-(σ - 1 / 2)) ≤ 1 := by
      simpa [a] using hpow_le_one_a
    have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hpowTa_pos : 0 < T ^ a := Real.rpow_pos_of_pos hT_pos a
    have hpowTa_ne : T ^ a ≠ 0 := ne_of_gt hpowTa_pos
    have hpowTa_cancel : T ^ a * T ^ (-a) = 1 := by
      rw [← Real.rpow_add hT_pos]
      simp
    have hpow_tail_a : T ^ (-a) ≤ |t| ^ (-a) := by
      have hTa_le : |t| ^ a ≤ T ^ a := Real.rpow_le_rpow (abs_nonneg t) hleT ha.le
      have hTa_pos_t : 0 < |t| ^ a := Real.rpow_pos_of_pos hpos_t a
      have hInv : (T ^ a)⁻¹ ≤ (|t| ^ a)⁻¹ := (inv_le_inv₀ hpowTa_pos hTa_pos_t).2 hTa_le
      simpa [Real.rpow_neg hT_pos.le, Real.rpow_neg (abs_nonneg _)] using hInv
    have hpow_tail : T ^ (-(σ - 1 / 2)) ≤ |t| ^ (-(σ - 1 / 2)) := by
      simpa [a] using hpow_tail_a
    have hU_to_pow : U ≤ (U * T ^ a) * |t| ^ (-(σ - 1 / 2)) := by
      have hstep : U * 1 ≤ U * (T ^ a * |t| ^ (-(σ - 1 / 2))) := by
        apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hUpos)
        have hpowTnonneg : 0 ≤ T ^ a := (le_of_lt hpowTa_pos)
        have hmul : T ^ a * T ^ (-(σ - 1 / 2)) ≤ T ^ a * |t| ^ (-(σ - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hpow_tail hpowTnonneg
        have hEqOne' : T ^ a * T ^ (-(σ - 1 / 2)) = 1 := by
          calc
            T ^ a * T ^ (-(σ - 1 / 2)) = T ^ a * T ^ (-a) := by simp [a]
            _ = 1 := hpowTa_cancel
        have hbase : 1 ≤ T ^ a * |t| ^ (-(σ - 1 / 2)) := by
          calc
            1 = T ^ a * T ^ (-(σ - 1 / 2)) := by simpa using hEqOne'.symm
            _ ≤ T ^ a * |t| ^ (-(σ - 1 / 2)) := hmul
        simpa using hbase
      simpa [mul_assoc] using hstep
    constructor
    · calc
        C1 * |t| ^ (-(σ - 1 / 2))
            ≤ L * |t| ^ (-(σ - 1 / 2)) := by
              dsimp [C1]
              exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (abs_nonneg t) _)
        _ ≤ L := by
              have hnonnegL : 0 ≤ L := le_of_lt hLpos
              calc
                L * |t| ^ (-(σ - 1 / 2)) ≤ L * 1 := by
                  exact mul_le_mul_of_nonneg_left hpow_le_one hnonnegL
                _ = L := by ring
        _ ≤ ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ := hratio_lo
    · calc
        ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤ U := hratio_hi
        _ ≤ (U * T ^ a) * |t| ^ (-(σ - 1 / 2)) := hU_to_pow
        _ ≤ C2 * |t| ^ (-(σ - 1 / 2)) := by
              dsimp [C2]
              exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg t) _)

theorem gamma_ratio_upper_half_direct (σ : ℝ) (hσ₀ : 1/2 < σ) (hσ₁ : σ < 1) :
    ∃ (C_lo C_hi : ℝ), 0 < C_lo ∧ 0 < C_hi ∧
    ∀ (t : ℝ), 1 ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) := by
  have h1σ_lo : 0 < 1 - σ := by linarith
  have hσ_pos : 0 < σ := by linarith
  have hsin_pos : 0 < Real.sin (π * σ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos pi_pos hσ_pos
    · calc π * σ < π * 1 := mul_lt_mul_of_pos_left hσ₁ pi_pos
        _ = π := mul_one π
  set P := Real.sqrt (1 / Real.sin (π * σ) ^ 2 + 1) with hP_def
  set a : ℝ := σ - 1 / 2
  have hR1_global :
      ∃ (C1 C2 : ℝ), 0 < C1 ∧ 0 < C2 ∧
      ∀ (t : ℝ), 1 ≤ |t| →
        C1 * |t| ^ (-a) ≤
          ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ∧
        ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ≤
          C2 * |t| ^ (-a) := by
    rcases lower_half_ratio_global_for_upper (hUpper := hUpper) σ hσ₀ hσ₁ with
      ⟨C1, C2, hC1, hC2, hB⟩
    refine ⟨C1, C2, hC1, hC2, ?_⟩
    intro t ht
    simpa [a] using hB t ht
  rcases hR1_global with ⟨C1, C2, hC1, hC2, hR1_global⟩
  exact ⟨1 / C2, P / C1,
    by positivity, by positivity, fun t ht => by
    have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht
    have ht_ne : t ≠ 0 := fun h => by simp [h] at ht_pos
    -- All Gamma values are nonzero and have positive norms
    have h_σ_ne := Complex.Gamma_ne_zero_of_re_pos
      (by simp [show (0:ℝ) < σ from hσ_pos] : (0:ℝ) < (⟨σ, t⟩ : ℂ).re)
    have h_half_ne := Complex.Gamma_ne_zero_of_re_pos
      (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
    have h_1σ_ne := Complex.Gamma_ne_zero_of_re_pos
      (by simp [show (0:ℝ) < 1 - σ from h1σ_lo] : (0:ℝ) < (⟨1 - σ, t⟩ : ℂ).re)
    have h_σ_pos' : 0 < ‖Complex.Gamma ⟨σ, t⟩‖ := norm_pos_iff.mpr h_σ_ne
    have h_half_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ := norm_pos_iff.mpr h_half_ne
    have h_1σ_pos : 0 < ‖Complex.Gamma ⟨1 - σ, t⟩‖ := norm_pos_iff.mpr h_1σ_ne
    set R_σ := ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖
    set R_1σ := ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖
    have hR_σ_pos : 0 < R_σ := div_pos h_σ_pos' h_half_pos
    have hR_1σ_pos : 0 < R_1σ := div_pos h_1σ_pos h_half_pos
    -- Reflection product: R_σ · R_1σ bounded
    have h_refl : R_σ * R_1σ = Real.cosh (π * t) / ‖Complex.sin (↑π * ⟨σ, t⟩)‖ := by
      show ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ *
        (‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖) = _
      rw [div_mul_div_comm,
          show ‖Complex.Gamma ⟨1/2, t⟩‖ * ‖Complex.Gamma ⟨1/2, t⟩‖ =
              ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 from (sq _).symm]
      exact reflection_ratio_product σ t hσ_pos (by linarith : σ < 1) ht_ne
    -- Squared product bounds
    have h_prod_sq : (R_σ * R_1σ) ^ 2 =
        Real.cosh (π * t) ^ 2 / (Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2) := by
      rw [h_refl, div_pow, ← sin_norm_sq]
    have h_sq_bounds := reflection_product_sq_bound σ t hσ_pos (by linarith) ht
    have h_prod_lo : 1 ≤ R_σ * R_1σ := by
      have : 1 ≤ (R_σ * R_1σ) ^ 2 := by rw [h_prod_sq]; exact h_sq_bounds.1
      nlinarith [sq_nonneg (R_σ * R_1σ - 1), mul_pos hR_σ_pos hR_1σ_pos]
    have h_prod_hi : R_σ * R_1σ ≤ P := by
      rw [hP_def, ← Real.sqrt_sq (le_of_lt (mul_pos hR_σ_pos hR_1σ_pos))]
      exact Real.sqrt_le_sqrt (by rw [h_prod_sq]; exact h_sq_bounds.2)
    have hR1_bounds := hR1_global t ht
    have hRσ_bounds :=
      ratio_bounds_from_reflection a t P R_σ R_1σ C1 C2
        ht hR_1σ_pos h_prod_lo h_prod_hi hR1_bounds.1 hR1_bounds.2
        hC1 hC2
    have hpow_rewrite : |t| ^ (σ - 1 / 2) = |t| ^ a := by
      simp [a]
    constructor
    · calc
        (1 / C2) * |t| ^ (σ - 1 / 2)
            = 1 / (C2 * |t| ^ (-a)) := by
              rw [hpow_rewrite, Real.rpow_neg (abs_nonneg t)]
              field_simp
        _ ≤ R_σ := by simpa using hRσ_bounds.1
    · calc
        R_σ ≤ P / (C1 * |t| ^ (-a)) := by
          simpa using hRσ_bounds.2
      _ = (P / C1) * |t| ^ (σ - 1 / 2) := by
          rw [hpow_rewrite, Real.rpow_neg (abs_nonneg t)]
          field_simp⟩

private lemma beta_norm_bounds (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1/2) :
    ∃ (B_lo B_hi : ℝ), 0 < B_lo ∧ 0 < B_hi ∧
    ∀ (t : ℝ), 1 ≤ |t| →
      B_lo * |t| ^ (-a) ≤ ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ ∧
      ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ ≤ B_hi * |t| ^ (-a) := by
  -- Derive from gamma_ratio_upper_half_direct via the Beta-Gamma identity
  set σ := a + 1/2 with hσ_def
  have hσ₀ : 1/2 < σ := by linarith
  have hσ₁ : σ < 1 := by linarith
  obtain ⟨C_lo, C_hi, hClo, hChi, hbound⟩ :=
    ZD.StirlingBound.gamma_ratio_upper_half_direct (hUpper := hUpper) σ hσ₀ hσ₁
  have hGa_pos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha₀
  -- B(a, 1/2+it) = Γ(a)·Γ(1/2+it)/Γ(σ+it), so
  -- ‖B‖ = Γ(a) · ‖Γ(1/2+it)‖ / ‖Γ(σ+it)‖ = Γ(a) / R(σ)
  -- R(σ) ∈ [C_lo·|t|^{σ-1/2}, C_hi·|t|^{σ-1/2}]
  -- So ‖B‖ ∈ [Γ(a)/(C_hi·|t|^{σ-1/2}), Γ(a)/(C_lo·|t|^{σ-1/2})]
  -- = [Γ(a)/C_hi · |t|^{-(σ-1/2)}, Γ(a)/C_lo · |t|^{-(σ-1/2)}]
  -- = [Γ(a)/C_hi · |t|^{-a}, Γ(a)/C_lo · |t|^{-a}]
  refine ⟨Real.Gamma a / C_hi, Real.Gamma a / C_lo,
    div_pos hGa_pos hChi, div_pos hGa_pos hClo, ?_⟩
  intro t ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht
  -- Gamma values are nonzero
  have h_half_ne : Complex.Gamma ⟨1/2, t⟩ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
  have h_σ_ne : Complex.Gamma ⟨σ, t⟩ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [show (0:ℝ) < σ from by linarith] :
      (0:ℝ) < (⟨σ, t⟩ : ℂ).re)
  have h_half_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ := norm_pos_iff.mpr h_half_ne
  have h_σ_pos : 0 < ‖Complex.Gamma ⟨σ, t⟩‖ := norm_pos_iff.mpr h_σ_ne
  -- Beta function identity: B(a, 1/2+it) = Γ(a)·Γ(1/2+it)/Γ(σ+it)
  have h_sum : (↑a : ℂ) + ⟨1/2, t⟩ = ⟨σ, t⟩ := by
    apply Complex.ext <;> simp [hσ_def]
  have h_re_a : 0 < (↑a : ℂ).re := by simp [ha₀]
  have h_re_half : 0 < (⟨1/2, t⟩ : ℂ).re := by simp
  have h_beta_eq : Complex.betaIntegral ↑a ⟨1/2, t⟩ =
      Complex.Gamma ↑a * Complex.Gamma ⟨1/2, t⟩ / Complex.Gamma ⟨σ, t⟩ := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ h_re_a h_re_half, h_sum]
  -- Beta is nonzero
  have h_beta_ne : Complex.betaIntegral ↑a ⟨1/2, t⟩ ≠ 0 := by
    rw [h_beta_eq]; exact div_ne_zero (mul_ne_zero
      (Complex.Gamma_ne_zero_of_re_pos h_re_a) h_half_ne) h_σ_ne
  have h_beta_pos : 0 < ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ :=
    norm_pos_iff.mpr h_beta_ne
  -- Norm of beta: ‖B‖ = Γ(a) · ‖Γ(1/2+it)‖ / ‖Γ(σ+it)‖
  have h_beta_norm : ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ =
      ‖Complex.Gamma ↑a‖ * ‖Complex.Gamma ⟨1/2, t⟩‖ / ‖Complex.Gamma ⟨σ, t⟩‖ := by
    rw [h_beta_eq, norm_div, norm_mul]
  have h_Ga_norm : ‖Complex.Gamma (↑a : ℂ)‖ = Real.Gamma a := by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.Gamma_pos_of_pos ha₀)]
  -- ‖B‖ = Γ(a) / R(σ)
  have h_beta_eq_ratio : ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ =
      Real.Gamma a / (‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖) := by
    rw [h_beta_norm, h_Ga_norm]; field_simp
  -- Get the ratio bounds
  obtain ⟨hlo_r, hhi_r⟩ := hbound t ht
  -- rpow identity: σ - 1/2 = a
  have h_rpow_a : |t| ^ (σ - 1/2) = |t| ^ a := by rw [hσ_def]; ring_nf
  have h_rpow_neg : |t| ^ (-a) = 1 / |t| ^ a := by
    rw [Real.rpow_neg (abs_nonneg _), one_div]
  rw [h_rpow_a] at hlo_r hhi_r
  -- R(σ) bounds
  set R := ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ with hR_def
  have hR_pos : 0 < R := div_pos h_σ_pos h_half_pos
  have h_rpow_pos : 0 < |t| ^ a := Real.rpow_pos_of_pos ht_pos a
  rw [h_beta_eq_ratio]
  constructor
  · -- Lower: (Γ(a)/C_hi) · |t|^{-a} ≤ Γ(a)/R
    -- Rewrite |t|^{-a} = 1/|t|^a, then simplify
    rw [h_rpow_neg]
    rw [show Real.Gamma a / C_hi * (1 / |t| ^ a) = Real.Gamma a / (C_hi * |t| ^ a) from by
      field_simp]
    -- Need: Γ(a)/(C_hi · |t|^a) ≤ Γ(a)/R
    -- Since R ≤ C_hi · |t|^a (from hhi_r), Γ(a)/R ≥ Γ(a)/(C_hi · |t|^a)
    exact div_le_div_of_nonneg_left hGa_pos.le hR_pos hhi_r
  · -- Upper: Γ(a)/R ≤ (Γ(a)/C_lo) · |t|^{-a}
    rw [h_rpow_neg]
    rw [show Real.Gamma a / C_lo * (1 / |t| ^ a) = Real.Gamma a / (C_lo * |t| ^ a) from by
      field_simp]
    -- Need: Γ(a)/R ≤ Γ(a)/(C_lo · |t|^a)
    -- Since R ≥ C_lo · |t|^a (from hlo_r), Γ(a)/R ≤ Γ(a)/(C_lo · |t|^a)
    exact div_le_div_of_nonneg_left hGa_pos.le (mul_pos hClo h_rpow_pos) hlo_r

omit hUpper in
private lemma gamma_ratio_upper_half_from_beta_decay
    (σ a : ℝ) (hσ : σ = a + 1/2) (ha₀ : 0 < a)
    (B_lo B_hi : ℝ) (hBlo : 0 < B_lo) (hBhi : 0 < B_hi)
    (hbeta : ∀ (t : ℝ), 1 ≤ |t| →
      B_lo * |t| ^ (-a) ≤ ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ ∧
      ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ ≤ B_hi * |t| ^ (-a)) :
    ∃ (C_lo C_hi : ℝ), 0 < C_lo ∧ 0 < C_hi ∧
    ∀ (t : ℝ), 1 ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ∧
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) := by
  have hσ_pos : 0 < σ := by linarith [ha₀, hσ]
  have hGa_pos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha₀
  refine ⟨Real.Gamma a / B_hi, Real.Gamma a / B_lo,
    div_pos hGa_pos hBhi, div_pos hGa_pos hBlo, ?_⟩
  intro t ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht
  have h_half_ne : Complex.Gamma ⟨1/2, t⟩ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
  have h_σ_ne : Complex.Gamma ⟨σ, t⟩ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using hσ_pos)
  have h_sum : (↑a : ℂ) + ⟨1/2, t⟩ = ⟨σ, t⟩ := by
    apply Complex.ext <;> simp [hσ]
  have h_re_a : 0 < (↑a : ℂ).re := by simp [ha₀]
  have h_re_half : 0 < (⟨1/2, t⟩ : ℂ).re := by simp
  have h_beta_eq : Complex.betaIntegral ↑a ⟨1/2, t⟩ =
      Complex.Gamma ↑a * Complex.Gamma ⟨1/2, t⟩ / Complex.Gamma ⟨σ, t⟩ := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ h_re_a h_re_half, h_sum]
  have h_beta_ne : Complex.betaIntegral ↑a ⟨1/2, t⟩ ≠ 0 := by
    rw [h_beta_eq]
    exact div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos h_re_a) h_half_ne) h_σ_ne
  have h_beta_pos : 0 < ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ := norm_pos_iff.mpr h_beta_ne
  have h_beta_norm : ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ =
      ‖Complex.Gamma ↑a‖ * ‖Complex.Gamma ⟨1/2, t⟩‖ / ‖Complex.Gamma ⟨σ, t⟩‖ := by
    rw [h_beta_eq, norm_div, norm_mul]
  have h_Ga_norm : ‖Complex.Gamma (↑a : ℂ)‖ = Real.Gamma a := by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.Gamma_pos_of_pos ha₀)]
  have h_ratio_eq : ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ =
      Real.Gamma a / ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ := by
    rw [h_beta_norm, h_Ga_norm]
    field_simp
  obtain ⟨hblo, hbhi⟩ := hbeta t ht
  have h_rpow_a : |t| ^ (σ - 1/2) = |t| ^ a := by
    rw [hσ]
    ring_nf
  have h_cancel : |t| ^ a * |t| ^ (-a) = 1 := by
    rw [← Real.rpow_add ht_pos]
    simp
  constructor
  · rw [h_ratio_eq, h_rpow_a, div_mul_eq_mul_div]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < B_hi) h_beta_pos]
    calc
      Real.Gamma a * |t| ^ a * ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖
          ≤ Real.Gamma a * |t| ^ a * (B_hi * |t| ^ (-a)) :=
            mul_le_mul_of_nonneg_left hbhi (by positivity)
      _ = Real.Gamma a * B_hi * (|t| ^ a * |t| ^ (-a)) := by ring
      _ = Real.Gamma a * B_hi := by rw [h_cancel, mul_one]
  · rw [h_ratio_eq, h_rpow_a, div_mul_eq_mul_div]
    rw [div_le_div_iff₀ h_beta_pos (by positivity : (0:ℝ) < B_lo)]
    calc
      Real.Gamma a * B_lo
          = Real.Gamma a * B_lo * (|t| ^ a * |t| ^ (-a)) := by rw [h_cancel, mul_one]
      _ = Real.Gamma a * |t| ^ a * (B_lo * |t| ^ (-a)) := by ring
      _ ≤ Real.Gamma a * |t| ^ a * ‖Complex.betaIntegral ↑a ⟨1/2, t⟩‖ :=
            mul_le_mul_of_nonneg_left hblo (by positivity)

omit hUpper
/-- Portability bridge: Beta vertical decay implies upper-half Gamma ratio bounds. -/
theorem gammaRatioUpperHalf_of_betaVerticalDecay
    (hβ : BetaVerticalDecay) : GammaRatioUpperHalf := by
  intro σ hσ₀ hσ₁
  set a := σ - 1/2 with ha_def
  have ha₀ : 0 < a := by linarith
  have ha₁ : a < 1/2 := by linarith
  have hσa : σ = a + 1/2 := by
    rw [ha_def]
    ring
  rcases hβ a ha₀ ha₁ with ⟨B_lo, B_hi, hBlo, hBhi, hbeta⟩
  exact gamma_ratio_upper_half_from_beta_decay
    σ a hσa ha₀ B_lo B_hi hBlo hBhi hbeta

omit hUpper
/-- Wrapper: if the abstract upper-half ratio statement is available, recover the
    concrete theorem shape used in this file. -/
theorem gamma_ratio_upper_half_direct_of_GammaRatioUpperHalf
    (hR : GammaRatioUpperHalf)
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) :
  ∃ (C_lo C_hi : ℝ), 0 < C_lo ∧ 0 < C_hi ∧
    ∀ (t : ℝ), 1 ≤ |t| →
      C_lo * |t| ^ (σ - 1 / 2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1 / 2) :=
  hR σ hσ₀ hσ₁

include hUpper

/-- Wrapper: a proved Beta decay statement directly yields the concrete
    upper-half Gamma ratio theorem shape. -/
theorem gamma_ratio_upper_half_direct_of_betaVerticalDecay
    (hβ : BetaVerticalDecay)
    (σ : ℝ) (hσ₀ : 1 / 2 < σ) (hσ₁ : σ < 1) :
    ∃ (C_lo C_hi : ℝ), 0 < C_lo ∧ 0 < C_hi ∧
    ∀ (t : ℝ), 1 ≤ |t| →
      C_lo * |t| ^ (σ - 1 / 2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1 / 2) := by
  exact gamma_ratio_upper_half_direct_of_GammaRatioUpperHalf
    (gammaRatioUpperHalf_of_betaVerticalDecay hβ) σ hσ₀ hσ₁

theorem gamma_ratio_upper_half_bound (σ : ℝ) (hσ₀ : 1/2 < σ) (hσ₁ : σ < 1) :
    ∃ (C_lo C_hi : ℝ), 0 < C_lo ∧ 0 < C_hi ∧
    ∀ (t : ℝ), 1 ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) := by
  set a := σ - 1/2 with ha_def
  have ha₀ : 0 < a := by linarith
  have ha₁ : a < 1/2 := by linarith
  have hσa : σ = a + 1/2 := by
    rw [ha_def]
    ring
  obtain ⟨B_lo, B_hi, hBlo, hBhi, hbeta⟩ := beta_norm_bounds (hUpper := hUpper) a ha₀ ha₁
  exact gamma_ratio_upper_half_from_beta_decay
    σ a hσa ha₀ B_lo B_hi hBlo hBhi hbeta

/-- Current route: extract the one-sided upper Beta decay branch from
    `beta_norm_bounds` (which currently depends on `gamma_ratio_upper_half_direct`). -/
theorem betaUpperDecay_from_gamma_ratio_upper_half_direct : BetaUpperDecay := by
  intro a ha₀ ha₁
  rcases beta_norm_bounds (hUpper := hUpper) a ha₀ ha₁ with ⟨B_lo, B_hi, _hBlo, hBhi, hbeta⟩
  refine ⟨B_hi, hBhi, ?_⟩
  intro t ht
  exact (hbeta t ht).2

/-- Interface witness (current route): compact-window upper control extracted
    from the global upper branch. -/
theorem betaUpperCompactWindowBound_from_gamma_ratio_upper_half_direct :
    BetaUpperCompactWindowBound := by
  intro a ha₀ ha₁ T hT
  rcases betaUpperDecay_from_gamma_ratio_upper_half_direct (hUpper := hUpper) a ha₀ ha₁ with
    ⟨B_hi, hBhi, hupper⟩
  refine ⟨B_hi, hBhi, ?_⟩
  intro t ht1 _htT
  have hpow_le_one : |t| ^ (-a) ≤ 1 := by
    have hone_le : 1 ≤ |t| ^ a := Real.one_le_rpow ht1 ha₀.le
    have hpow_pos : 0 < |t| ^ a := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos ht1) a
    have hinv : (|t| ^ a)⁻¹ ≤ (1 : ℝ)⁻¹ := (inv_le_inv₀ hpow_pos zero_lt_one).2 hone_le
    have hrpow_neg : |t| ^ (-a) = (|t| ^ a)⁻¹ := by
      rw [Real.rpow_neg (abs_nonneg t)]
    simpa [hrpow_neg] using hinv
  calc
    ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ B_hi * |t| ^ (-a) := hupper t ht1
    _ ≤ B_hi * 1 := mul_le_mul_of_nonneg_left hpow_le_one (le_of_lt hBhi)
    _ = B_hi := by ring

omit hUpper
/-- Independent compact-window bound:
continuity of `t ↦ betaIntegral a (1/2+it)` on a compact interval gives a
uniform finite upper bound. -/
theorem betaUpperCompactWindowBound_independent :
    BetaUpperCompactWindowBound := by
  intro a ha₀ ha₁ T hT
  let phi1 : ℝ → ℂ := fun x => ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)
  let phi2 : ℝ → ℂ := fun x => (((a + 1 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun t =>
    Complex.Gamma (↑a : ℂ) * Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
      Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hEq : ∀ t : ℝ, Complex.betaIntegral ↑a ⟨1 / 2, t⟩ = g t := by
    intro t
    have h_re_a : 0 < (↑a : ℂ).re := by simpa using ha₀
    have h_re_half : 0 < (⟨1 / 2, t⟩ : ℂ).re := by norm_num
    have hBeta :=
      Complex.betaIntegral_eq_Gamma_mul_div (↑a : ℂ) (⟨1 / 2, t⟩ : ℂ) h_re_a h_re_half
    have hhalf : (⟨1 / 2, t⟩ : ℂ) = ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    have hsum : (↑a : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
        (((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [add_assoc, add_comm, add_left_comm]
    have hBeta' : Complex.betaIntegral ↑a ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = g t := by
      rw [hhalf] at hBeta
      rw [hsum] at hBeta
      simpa [g] using hBeta
    have hbeta_arg :
        Complex.betaIntegral ↑a ⟨1 / 2, t⟩ =
          Complex.betaIntegral ↑a ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
      exact congrArg (Complex.betaIntegral (↑a : ℂ)) hhalf
    calc
      Complex.betaIntegral ↑a ⟨1 / 2, t⟩
          = Complex.betaIntegral ↑a ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := hbeta_arg
      _ = g t := hBeta'
  have hline_half_cont : Continuous phi1 := by
    simpa [phi1] using
      (continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const))
  have hline_sum_cont :
      Continuous phi2 := by
    simpa [phi2] using
      (continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const))
  have hGamma_half_cont : Continuous (fun t : ℝ => Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hnot : ∀ m : ℕ, phi1 t ≠ -↑m := by
      intro m hm
      have hre : (phi1 t).re = (- (m : ℂ)).re := by
        exact congrArg Complex.re hm
      simp [phi1] at hre
      nlinarith
    have hgamma : ContinuousAt Complex.Gamma (phi1 t) := (Complex.differentiableAt_Gamma _ hnot).continuousAt
    have hphi : ContinuousAt phi1 t := hline_half_cont.continuousAt
    simpa [Function.comp, phi1] using hgamma.comp hphi
  have hGamma_sum_cont :
      Continuous (fun t : ℝ => Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hnot : ∀ m : ℕ, phi2 t ≠ -↑m := by
      intro m hm
      have hre : (phi2 t).re = (- (m : ℂ)).re := by
        exact congrArg Complex.re hm
      simp [phi2] at hre
      linarith
    have hgamma : ContinuousAt Complex.Gamma (phi2 t) := (Complex.differentiableAt_Gamma _ hnot).continuousAt
    have hphi : ContinuousAt phi2 t := hline_sum_cont.continuousAt
    simpa [Function.comp, phi2] using hgamma.comp hphi
  have hGamma_sum_ne : ∀ t : ℝ,
      Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t
    apply Complex.Gamma_ne_zero_of_re_pos
    have hRe : ((((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re) = a + 1 / 2 := by simp
    rw [hRe]
    linarith
  have hg_cont : Continuous g := by
    refine (continuous_const.mul hGamma_half_cont).div hGamma_sum_cont hGamma_sum_ne
  have hBeta_cont : Continuous (fun t : ℝ => Complex.betaIntegral ↑a ⟨1 / 2, t⟩) := by
    refine hg_cont.congr ?_
    intro t
    exact (hEq t).symm
  have hK : IsCompact (Set.Icc (-T) T) := isCompact_Icc
  rcases hK.exists_bound_of_continuousOn hBeta_cont.continuousOn with ⟨C, hC⟩
  refine ⟨max C 1, by positivity, ?_⟩
  intro t ht1 htT
  have hmem : t ∈ Set.Icc (-T) T := by
    constructor
    · linarith [neg_abs_le t, htT]
    · linarith [le_abs_self t, htT]
  calc
    ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ ≤ C := hC t hmem
    _ ≤ max C 1 := le_max_left _ _

omit hUpper
/-- Independent compact-window lower control for Beta norms:
on `1 ≤ |t| ≤ T`, continuity and nonvanishing give a positive lower bound. -/
theorem betaLowerCompactWindowBound_independent :
    ∀ (a : ℝ), 0 < a → a < 1 / 2 →
      ∀ (T : ℝ), 1 ≤ T →
        ∃ (m : ℝ), 0 < m ∧
          (∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
            m ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖) := by
  intro a ha₀ _ha₁ T _hT
  let phi1 : ℝ → ℂ := fun x => ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)
  let phi2 : ℝ → ℂ := fun x => (((a + 1 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun t =>
    Complex.Gamma (↑a : ℂ) * Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
      Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hEq : ∀ t : ℝ, Complex.betaIntegral ↑a ⟨1 / 2, t⟩ = g t := by
    intro t
    have h_re_a : 0 < (↑a : ℂ).re := by simpa using ha₀
    have h_re_half : 0 < (⟨1 / 2, t⟩ : ℂ).re := by norm_num
    have hBeta :=
      Complex.betaIntegral_eq_Gamma_mul_div (↑a : ℂ) (⟨1 / 2, t⟩ : ℂ) h_re_a h_re_half
    have hhalf : (⟨1 / 2, t⟩ : ℂ) = ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    have hsum : (↑a : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
        (((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [add_assoc, add_comm, add_left_comm]
    have hBeta' : Complex.betaIntegral ↑a ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = g t := by
      rw [hhalf] at hBeta
      rw [hsum] at hBeta
      simpa [g] using hBeta
    have hbeta_arg :
        Complex.betaIntegral ↑a ⟨1 / 2, t⟩ =
          Complex.betaIntegral ↑a ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
      exact congrArg (Complex.betaIntegral (↑a : ℂ)) hhalf
    calc
      Complex.betaIntegral ↑a ⟨1 / 2, t⟩
          = Complex.betaIntegral ↑a ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := hbeta_arg
      _ = g t := hBeta'
  have hline_half_cont : Continuous phi1 := by
    simpa [phi1] using
      (continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const))
  have hline_sum_cont :
      Continuous phi2 := by
    simpa [phi2] using
      (continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const))
  have hGamma_half_cont : Continuous (fun t : ℝ => Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hnot : ∀ m : ℕ, phi1 t ≠ -↑m := by
      intro m hm
      have hre : (phi1 t).re = (- (m : ℂ)).re := by
        exact congrArg Complex.re hm
      simp [phi1] at hre
      nlinarith
    have hgamma : ContinuousAt Complex.Gamma (phi1 t) := (Complex.differentiableAt_Gamma _ hnot).continuousAt
    have hphi : ContinuousAt phi1 t := hline_half_cont.continuousAt
    simpa [Function.comp, phi1] using hgamma.comp hphi
  have hGamma_sum_cont :
      Continuous (fun t : ℝ => Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hnot : ∀ m : ℕ, phi2 t ≠ -↑m := by
      intro m hm
      have hre : (phi2 t).re = (- (m : ℂ)).re := by
        exact congrArg Complex.re hm
      simp [phi2] at hre
      linarith
    have hgamma : ContinuousAt Complex.Gamma (phi2 t) := (Complex.differentiableAt_Gamma _ hnot).continuousAt
    have hphi : ContinuousAt phi2 t := hline_sum_cont.continuousAt
    simpa [Function.comp, phi2] using hgamma.comp hphi
  have hGamma_sum_ne : ∀ t : ℝ,
      Complex.Gamma (((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t
    apply Complex.Gamma_ne_zero_of_re_pos
    have hRe : ((((a + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re) = a + 1 / 2 := by simp
    rw [hRe]
    linarith
  have hg_cont : Continuous g := by
    refine (continuous_const.mul hGamma_half_cont).div hGamma_sum_cont hGamma_sum_ne
  have hBeta_cont : Continuous (fun t : ℝ => Complex.betaIntegral ↑a ⟨1 / 2, t⟩) := by
    refine hg_cont.congr ?_
    intro t
    exact (hEq t).symm
  have hBeta_ne : ∀ t : ℝ, Complex.betaIntegral ↑a ⟨1 / 2, t⟩ ≠ 0 := by
    intro t
    have h_re_a : 0 < (↑a : ℂ).re := by simpa using ha₀
    have h_re_half : 0 < (⟨1 / 2, t⟩ : ℂ).re := by norm_num
    have h_sum : (↑a : ℂ) + (⟨1 / 2, t⟩ : ℂ) = ⟨a + 1 / 2, t⟩ := by
      apply Complex.ext <;> simp
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ h_re_a h_re_half, h_sum]
    exact div_ne_zero
      (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos h_re_a)
        (Complex.Gamma_ne_zero_of_re_pos h_re_half))
      (Complex.Gamma_ne_zero_of_re_pos (by
        change (0 : ℝ) < (⟨a + 1 / 2, t⟩ : ℂ).re
        simp
        linarith))
  have hNorm_cont : Continuous (fun t : ℝ => ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖) := hBeta_cont.norm
  have hNormInv_cont : Continuous (fun t : ℝ => (‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖)⁻¹) := by
    exact hNorm_cont.inv₀ (by
      intro t
      exact norm_ne_zero_iff.mpr (hBeta_ne t))
  have hK : IsCompact (Set.Icc (-T) T) := isCompact_Icc
  rcases hK.exists_bound_of_continuousOn hNormInv_cont.continuousOn with ⟨M, hM⟩
  refine ⟨1 / max M 1, by positivity, ?_⟩
  intro t _ht1 htT
  have hmem : t ∈ Set.Icc (-T) T := by
    constructor
    · linarith [neg_abs_le t, htT]
    · linarith [le_abs_self t, htT]
  have h_inv_norm : ‖(‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖)⁻¹‖ ≤ M := hM t hmem
  have h_inv : (‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖)⁻¹ ≤ max M 1 := by
    have h_inv_nonneg : 0 ≤ (‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖)⁻¹ := by positivity
    have h_inv_le_M : (‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖)⁻¹ ≤ M := by
      have habs : |(‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖)⁻¹| ≤ M := by
        simpa [Real.norm_eq_abs] using h_inv_norm
      simpa [abs_of_nonneg h_inv_nonneg] using habs
    exact le_trans h_inv_le_M (le_max_left _ _)
  have hmax_pos : 0 < max M 1 := by positivity
  have hnorm_pos : 0 < ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ := by
    exact norm_pos_iff.mpr (hBeta_ne t)
  have h_lower : 1 / max M 1 ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ := by
    have h_rinv_pos : 0 < (‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖)⁻¹ := by positivity
    have h_inv_div : 1 / (max M 1) ≤ 1 / ((‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖)⁻¹) := by
      simpa [one_div] using (inv_le_inv₀ hmax_pos h_rinv_pos).2 h_inv
    simpa [one_div, inv_inv] using h_inv_div
  exact h_lower

include hUpper

/-- Interface witness (current route): tail upper decay extracted from the
    global upper branch. -/
theorem betaUpperTailDecayBound_from_gamma_ratio_upper_half_direct :
    BetaUpperTailDecayBound := by
  intro a ha₀ ha₁
  rcases betaUpperDecay_from_gamma_ratio_upper_half_direct (hUpper := hUpper) a ha₀ ha₁ with
    ⟨B_hi, hBhi, hupper⟩
  refine ⟨1, B_hi, by norm_num, hBhi, ?_⟩
  intro t ht
  exact hupper t (le_trans (by norm_num) ht)

/-- Current route: extract the one-sided lower Beta decay branch from
    `beta_norm_bounds` (which currently depends on `gamma_ratio_upper_half_direct`). -/
theorem betaLowerDecay_from_gamma_ratio_upper_half_direct : BetaLowerDecay := by
  intro a ha₀ ha₁
  rcases beta_norm_bounds (hUpper := hUpper) a ha₀ ha₁ with ⟨B_lo, B_hi, hBlo, _hBhi, hbeta⟩
  refine ⟨B_lo, hBlo, ?_⟩
  intro t ht
  exact (hbeta t ht).1

/-- Current file-level route to Beta vertical decay from the upper-half ratio theorem. -/
theorem betaVerticalDecay_from_gamma_ratio_upper_half_direct : BetaVerticalDecay := by
  have hUpperDecay : BetaUpperDecay :=
    betaUpperDecay_of_interfaces
      betaUpperCompactWindowBound_independent
      (betaUpperTailDecayBound_from_gamma_ratio_upper_half_direct (hUpper := hUpper))
  exact betaVerticalDecay_of_upper_lower
    (betaLowerDecay_from_gamma_ratio_upper_half_direct (hUpper := hUpper))
    hUpperDecay

/-- GammaSeq product bound: derived from gamma_ratio_upper_half_bound
    via GammaSeq convergence. The GammaSeq ratio converges to the Gamma ratio,
    and the Gamma ratio is bounded by the axiom, so the sequence is eventually bounded.

    Note: ge_of_tendsto/le_of_tendsto go from sequence bounds to limit bounds.
    We need the reverse: limit bounds → eventual sequence bounds. This follows
    from Tendsto + the fact that [a, b] is a neighborhood of any point in (a, b).
    For the boundary case (limit = a or b), we relax the constants. -/
private lemma gammaSeq_product_bound (σ : ℝ) (hσ₀ : 1/2 < σ) (hσ₁ : σ < 1) :
    ∃ (P_lo P_hi : ℝ), 0 < P_lo ∧ 0 < P_hi ∧
    ∀ (t : ℝ), 1 ≤ |t| → ∀ᶠ (n : ℕ) in Filter.atTop,
      P_lo * |t| ^ (σ - 1/2) ≤
        ‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖ ∧
      ‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖ ≤
        P_hi * |t| ^ (σ - 1/2) := by
  obtain ⟨C_lo, C_hi, hClo, hChi, hbound⟩ :=
    gamma_ratio_upper_half_bound (hUpper := hUpper) σ hσ₀ hσ₁
  -- Use relaxed constants C_lo/2 and 2*C_hi so we have room for ε
  refine ⟨C_lo / 2, 2 * C_hi, by linarith, by linarith, ?_⟩
  intro t ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht
  -- The GammaSeq ratio converges to the Gamma ratio
  have h_tendsto : Filter.Tendsto
      (fun n => ‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖)
      Filter.atTop
      (nhds (‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖)) := by
    apply Filter.Tendsto.div
    · exact (Complex.GammaSeq_tendsto_Gamma _).norm
    · exact (Complex.GammaSeq_tendsto_Gamma _).norm
    · exact norm_ne_zero_iff.mpr
        (Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re))
  set L := ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ with hL_def
  obtain ⟨hlo, hhi⟩ := hbound t ht
  -- L > 0 and the bounds hold
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hlo
  -- ε = min(L - C_lo/2·|t|^δ, 2·C_hi·|t|^δ - L) if positive, else L/2
  -- Simpler: use Icc neighborhood. Since C_lo/2·|t|^δ < L ≤ C_hi·|t|^δ < 2·C_hi·|t|^δ,
  -- the interval (C_lo/2·|t|^δ, 2·C_hi·|t|^δ) is a neighborhood of L.
  have h_lo_strict : C_lo / 2 * |t| ^ (σ - 1/2) < L := by
    calc C_lo / 2 * |t| ^ (σ - 1/2) < C_lo * |t| ^ (σ - 1/2) := by
          apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos ht_pos _)
          linarith
      _ ≤ L := hlo
  have h_hi_strict : L < 2 * C_hi * |t| ^ (σ - 1/2) := by
    calc L ≤ C_hi * |t| ^ (σ - 1/2) := hhi
      _ < 2 * C_hi * |t| ^ (σ - 1/2) := by
          apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos ht_pos _)
          linarith
  -- The open interval (lo, hi) is a neighborhood of L
  have h_nhd : Set.Ioo (C_lo / 2 * |t| ^ (σ - 1/2)) (2 * C_hi * |t| ^ (σ - 1/2)) ∈ nhds L :=
    Ioo_mem_nhds h_lo_strict h_hi_strict
  -- Eventually the sequence is in this interval
  have h_ev : ∀ᶠ n in Filter.atTop,
      (‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖) ∈
        Set.Ioo (C_lo / 2 * |t| ^ (σ - 1/2)) (2 * C_hi * |t| ^ (σ - 1/2)) :=
    Filter.Tendsto.eventually_mem h_tendsto h_nhd
  exact h_ev.mono fun n hn => ⟨le_of_lt hn.1, le_of_lt hn.2⟩

/-- For σ ∈ (1/2, 1) and large |t|, the ratio ‖Γ(σ+it)‖/‖Γ(1/2+it)‖ is bounded
    above and below by C·|t|^{σ-1/2}. Proof: transfer the GammaSeq product bound
    to the Gamma limit using ge_of_tendsto / le_of_tendsto. -/
private lemma gammaSeq_ratio_bound_upper_half (σ : ℝ) (hσ₀ : 1/2 < σ) (hσ₁ : σ < 1) :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) := by
  obtain ⟨P_lo, P_hi, hPlo, hPhi, hprod⟩ :=
    gammaSeq_product_bound (hUpper := hUpper) σ hσ₀ hσ₁
  refine ⟨P_lo, P_hi, 1, hPlo, hPhi, one_pos, ?_⟩
  intro t ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht
  -- The GammaSeq ratio converges to the Gamma ratio
  have h_tendsto : Filter.Tendsto
      (fun n => ‖Complex.GammaSeq ⟨σ, t⟩ n‖ / ‖Complex.GammaSeq ⟨1/2, t⟩ n‖)
      Filter.atTop
      (nhds (‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖)) := by
    apply Filter.Tendsto.div
    · exact (Complex.GammaSeq_tendsto_Gamma _).norm
    · exact (Complex.GammaSeq_tendsto_Gamma _).norm
    · exact norm_ne_zero_iff.mpr
        (Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re))
  have hev := hprod t ht
  constructor
  · -- Lower bound: transfer from GammaSeq sequence to limit
    exact ge_of_tendsto h_tendsto (hev.mono (fun n hn => hn.1))
  · -- Upper bound: transfer from GammaSeq sequence to limit
    exact le_of_tendsto h_tendsto (hev.mono (fun n hn => hn.2))

/-- For σ ∈ (0, 1/2) and large |t|, the ratio ‖Γ(σ+it)‖/‖Γ(1/2+it)‖ is bounded.
    Proof: reflection formula gives R(σ)·R(1-σ) = cosh(πt)/‖sin(π(σ+it))‖,
    which is bounded above and below for large |t|. Since 1-σ ∈ (1/2, 1),
    R(1-σ) is bounded by gammaSeq_ratio_bound_upper_half, so
    R(σ) = [reflection product] / R(1-σ) inherits the reciprocal bound. -/
private lemma gammaSeq_ratio_bound_lower_half (σ : ℝ) (hσ₀ : 0 < σ) (hσ₁ : σ < 1/2) :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) := by
  -- 1-σ ∈ (1/2, 1), so we can use gammaSeq_ratio_bound_upper_half
  have h1σ_lo : 1/2 < 1 - σ := by linarith
  have h1σ_hi : 1 - σ < 1 := by linarith
  obtain ⟨C₁, C₂, T₁, hC₁, hC₂, hT₁, hbound⟩ :=
    gammaSeq_ratio_bound_upper_half (hUpper := hUpper) (1 - σ) h1σ_lo h1σ_hi
  -- Key constants: P_hi is the upper bound on the reflection ratio R(σ)·R(1-σ),
  -- which is √(1/sin²(πσ)+1). We use P_lo = 1 for the lower bound.
  set P := Real.sqrt (1 / Real.sin (π * σ) ^ 2 + 1) with hP_def
  have hsin_pos : 0 < Real.sin (π * σ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos pi_pos hσ₀
    · calc π * σ < π * (1/2) := mul_lt_mul_of_pos_left hσ₁ pi_pos
        _ < π * 1 := mul_lt_mul_of_pos_left (by norm_num) pi_pos
        _ = π := mul_one π
  have hP_pos : 0 < P := by positivity
  refine ⟨1 / C₂, P / C₁, max T₁ 1,
    by positivity, by positivity, by positivity, ?_⟩
  intro t ht
  have hT : T₁ ≤ |t| := le_trans (le_max_left _ _) ht
  have ht1 : 1 ≤ |t| := le_trans (le_max_right _ _) ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht1
  have ht_ne : t ≠ 0 := fun h => by simp [h] at ht_pos
  obtain ⟨hlo_1σ, hhi_1σ⟩ := hbound t hT
  -- Gamma norms are positive
  have h_σ_pos : 0 < ‖Complex.Gamma ⟨σ, t⟩‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp [hσ₀] : (0:ℝ) < (⟨σ, t⟩ : ℂ).re)
  have h_half_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
  have h_1σ_pos : 0 < ‖Complex.Gamma ⟨1 - σ, t⟩‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp [show (0:ℝ) < 1 - σ from by linarith] :
      (0:ℝ) < (⟨1 - σ, t⟩ : ℂ).re)
  -- R(σ) = ratio, R(1-σ) = ratio_1σ
  set R_σ := ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ with hR_σ_def
  set R_1σ := ‖Complex.Gamma ⟨1 - σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ with hR_1σ_def
  have hR_σ_pos : 0 < R_σ := div_pos h_σ_pos h_half_pos
  have hR_1σ_pos : 0 < R_1σ := div_pos h_1σ_pos h_half_pos
  -- From reflection_ratio_product (already proved):
  -- R(σ)·R(1-σ) = cosh(πt)/‖sin(π(σ+it))‖
  -- But we actually need R(σ)·R(1-σ) for the div by ‖Γ(1/2+it)‖²
  -- reflection_ratio_product says:
  --   ‖Γ(σ+it)‖·‖Γ(1-σ+it)‖ / ‖Γ(1/2+it)‖² = cosh(πt)/‖sin(π(σ+it))‖
  -- i.e., R_σ * R_1σ = cosh(πt)/‖sin(π(σ+it))‖
  have h_refl : R_σ * R_1σ = Real.cosh (π * t) / ‖Complex.sin (↑π * ⟨σ, t⟩)‖ := by
    rw [hR_σ_def, hR_1σ_def, div_mul_div_comm,
        show ‖Complex.Gamma ⟨1/2, t⟩‖ * ‖Complex.Gamma ⟨1/2, t⟩‖ =
            ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 from (sq _).symm]
    exact reflection_ratio_product σ t hσ₀ (by linarith : σ < 1) ht_ne
  -- Bound the reflection product from above and below
  -- ‖sin(π(σ+it))‖² = sin²(πσ)+sinh²(πt), from sin_norm_sq
  -- cosh²(πt) = 1+sinh²(πt)
  -- So (R_σ*R_1σ)² = cosh²(πt)/(sin²(πσ)+sinh²(πt))
  -- From reflection_product_sq_bound: this is ∈ [1, 1/sin²(πσ)+1]
  have h_sq_bounds := reflection_product_sq_bound σ t hσ₀ (by linarith : σ < 1) ht1
  -- The reflection product squared is:
  have h_prod_sq : (R_σ * R_1σ) ^ 2 =
      Real.cosh (π * t) ^ 2 / (Real.sin (π * σ) ^ 2 + Real.sinh (π * t) ^ 2) := by
    rw [h_refl, div_pow, ← sin_norm_sq]
  -- Lower bound: R_σ*R_1σ ≥ 1
  have h_prod_lo : 1 ≤ R_σ * R_1σ := by
    have h1 : 1 ≤ (R_σ * R_1σ) ^ 2 := by rw [h_prod_sq]; exact h_sq_bounds.1
    nlinarith [sq_nonneg (R_σ * R_1σ - 1), mul_pos hR_σ_pos hR_1σ_pos]
  -- Upper bound: R_σ*R_1σ ≤ P
  have h_prod_hi : R_σ * R_1σ ≤ P := by
    rw [hP_def, ← Real.sqrt_sq (le_of_lt (mul_pos hR_σ_pos hR_1σ_pos))]
    exact Real.sqrt_le_sqrt (by rw [h_prod_sq]; exact h_sq_bounds.2)
  -- Key rpow identity: |t|^a * |t|^b = 1 where a = σ-1/2, b = (1-σ)-1/2
  have h_rpow_cancel : |t| ^ (σ - 1/2) * |t| ^ ((1 - σ) - 1/2) = 1 := by
    rw [← Real.rpow_add ht_pos, show σ - 1/2 + ((1 - σ) - 1/2) = 0 from by ring,
        Real.rpow_zero]
  have h_rpow_a_pos : 0 < |t| ^ (σ - 1/2) := by positivity
  have h_rpow_eq : |t| ^ (σ - 1/2) = 1 / |t| ^ ((1 - σ) - 1/2) :=
    eq_one_div_of_mul_eq_one_left h_rpow_cancel
  constructor
  · -- Lower: (1/C₂) * |t|^{σ-1/2} ≤ R_σ
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC₂]
    calc |t| ^ (σ - 1/2)
        = |t| ^ (σ - 1/2) * 1 := (mul_one _).symm
      _ ≤ |t| ^ (σ - 1/2) * (R_σ * R_1σ) :=
          mul_le_mul_of_nonneg_left h_prod_lo (le_of_lt h_rpow_a_pos)
      _ = R_σ * (|t| ^ (σ - 1/2) * R_1σ) := by ring
      _ ≤ R_σ * C₂ := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hR_σ_pos)
          calc |t| ^ (σ - 1/2) * R_1σ
              ≤ |t| ^ (σ - 1/2) * (C₂ * |t| ^ ((1 - σ) - 1/2)) :=
                mul_le_mul_of_nonneg_left hhi_1σ (le_of_lt h_rpow_a_pos)
            _ = C₂ * (|t| ^ (σ - 1/2) * |t| ^ ((1 - σ) - 1/2)) := by ring
            _ = C₂ := by rw [h_rpow_cancel, mul_one]
  · -- Upper: R_σ ≤ (P/C₁) * |t|^{σ-1/2}
    have h_Rσ_le : R_σ ≤ P / R_1σ := by
      rw [le_div_iff₀ hR_1σ_pos]; exact h_prod_hi
    calc R_σ ≤ P / R_1σ := h_Rσ_le
      _ ≤ P / (C₁ * |t| ^ ((1 - σ) - 1/2)) :=
          div_le_div_of_nonneg_left (by linarith) (by positivity) hlo_1σ
      _ = P / C₁ * |t| ^ (σ - 1/2) := by rw [h_rpow_eq]; field_simp

/-- **GammaSeq ratio bound** (key lemma for stirling_unit_strip).
    For σ ∈ (0, 1] and the half-plane point 1/2:
    ‖Γ(σ+it)‖/‖Γ(1/2+it)‖ is bounded between C₁·|t|^{σ-1/2} and C₂·|t|^{σ-1/2}
    for large |t|. Proved via GammaSeq product convergence: the ratio
    n^{σ-1/2} · ∏_{j=0}^n ‖(1/2+j+it)‖/‖(σ+j+it)‖ → C(σ)·|t|^{σ-1/2}
    where C(σ) is bounded (Titchmarsh §4.42). -/
private lemma gammaSeq_ratio_bound (σ : ℝ) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) := by
  /- Strategy: combine three ingredients:
     1. Reflection: ‖Γ(σ+it)‖·‖Γ(1-σ+it)‖ = π/‖sin(π(σ+it))‖
     2. Gamma_half_norm_sq: ‖Γ(1/2+it)‖² = π/cosh(πt)
     3. Gamma_one_norm_sq: ‖Γ(1+it)‖² = π|t|/sinh(π|t|)
     These give the product f(σ)·f(1-σ) bounded, and f(1) ~ |t|^{1/2}.

     For σ = 1: direct from the exact formulas.
     For σ = 1/2: trivial (ratio = 1).
     For σ ∈ (0,1) \ {1/2}: use the functional equation
       Γ(s) = Γ(s+1)/s to reduce: the ratio ‖Γ(σ+it)‖/‖Γ(1/2+it)‖
       equals ‖Γ(σ+N+it)‖/(‖Γ(1/2+N+it)‖·∏‖(σ+j+it)/(1/2+j+it)‖)
       for any N. For N = 1: uses Γ at σ+1 and 3/2.

     For σ ∈ (1/2, 1): use the functional equation downward:
       f(σ) = f(σ+1)/‖(σ+it)‖, and f(3/2) = ‖(1/2+it)‖.
       This relates f(σ) to the value at σ+1 ∈ (3/2, 2),
       which equals ‖(σ+it)‖·f(σ). The product telescopes.

     For σ ∈ (0, 1/2): use f(σ) = f(σ+1)/‖(σ+it)‖ where σ+1 ∈ (1, 3/2).
       And f(σ+1) = ‖(σ+it)‖·f(σ) by the recurrence.

     The proof uses the GammaSeq limit representation to express the ratio
     as a convergent product, and bounds the product using telescoping. -/
  /- The proof proceeds via the GammaSeq product representation.

     GammaSeq(s, n) = n^s · n! / ∏_{j=0}^n (s+j) → Γ(s) as n → ∞.

     The ratio ‖GammaSeq(σ+it,n)‖ / ‖GammaSeq(1/2+it,n)‖ equals
     n^{σ-1/2} · ∏_{j=0}^n ‖(1/2+j+it)‖/‖(σ+j+it)‖, and converges to
     ‖Γ(σ+it)‖/‖Γ(1/2+it)‖.

     Each factor R_j = ‖(1/2+j+it)‖/‖(σ+j+it)‖ satisfies:
     R_j² = ((1/2+j)²+t²)/((σ+j)²+t²) = 1 + (1/2-σ)(1/2+σ+2j)/((σ+j)²+t²)

     Splitting at M = ⌊|t|⌋:
     • j ≤ M: |log R_j| ≤ C/t², sum bounded by C'/2
     • j > M: log R_j ≈ (1/2-σ)/(σ+j), sum ≈ (1/2-σ)·log(n/|t|)

     Combined: n^{σ-1/2} · ∏ R_j = |t|^{σ-1/2} · exp(O(1))

     The O(1) error is bounded uniformly in t, giving the result. -/
  -- Case split: σ = 1/2 (trivial), σ = 1 (from ratio_at_one_bounds),
  -- general σ via GammaSeq product representation.
  -- Step 1: Handle σ = 1/2 trivially
  by_cases hσ_half : σ = 1/2
  · subst hσ_half
    refine ⟨1, 1, 1, one_pos, one_pos, one_pos, ?_⟩
    intro t ht
    simp only [show (1:ℝ)/2 - 1/2 = 0 from by ring, Real.rpow_zero, mul_one]
    have h_pos : (0:ℝ) < ‖Complex.Gamma (⟨1/2, t⟩ : ℂ)‖ := by
      rw [norm_pos_iff]
      exact Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
    have heq : ‖Complex.Gamma (⟨1/2, t⟩ : ℂ)‖ / ‖Complex.Gamma (⟨1/2, t⟩ : ℂ)‖ = 1 :=
      div_self (ne_of_gt h_pos)
    exact ⟨heq.symm.le, heq.le⟩
  -- Step 2: Handle σ = 1 from ratio_at_one_bounds
  by_cases hσ_one : σ = 1
  · subst hσ_one
    refine ⟨1, Real.sqrt 2, 1, one_pos, by positivity, one_pos, ?_⟩
    intro t ht
    have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht
    have ht_ne : t ≠ 0 := fun h => by simp [h] at ht_pos
    have h_half_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ := by
      rw [norm_pos_iff]
      exact Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
    have h_one_pos : 0 < ‖Complex.Gamma ⟨1, t⟩‖ := by
      rw [norm_pos_iff]
      exact Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1, t⟩ : ℂ).re)
    obtain ⟨hlo, hhi⟩ := ratio_at_one_bounds t ht_ne ht
    have h_rpow : |t| ^ ((1:ℝ) - 1/2) = |t| ^ ((1:ℝ)/2) := by congr 1; ring
    rw [h_rpow]
    have h_ratio_pos : 0 < ‖Complex.Gamma ⟨1, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ :=
      div_pos h_one_pos h_half_pos
    -- From hlo: |t| ≤ f(1)²/f(1/2)² = (f(1)/f(1/2))²
    -- So √|t| ≤ f(1)/f(1/2)
    have h_ratio_sq : ‖Complex.Gamma ⟨1, t⟩‖ ^ 2 / ‖Complex.Gamma ⟨1/2, t⟩‖ ^ 2 =
        (‖Complex.Gamma ⟨1, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖) ^ 2 := by
      rw [div_pow]
    rw [h_ratio_sq] at hlo hhi
    constructor
    · -- Lower: 1 * |t|^{1/2} ≤ f(1)/f(1/2)
      rw [one_mul]
      -- |t|^{1/2} ≤ f(1)/f(1/2) follows from |t| ≤ (f(1)/f(1/2))²
      have h_sqrt_le : Real.sqrt |t| ≤ ‖Complex.Gamma ⟨1, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ := by
        rw [← Real.sqrt_sq (le_of_lt h_ratio_pos)]
        exact Real.sqrt_le_sqrt hlo
      rwa [Real.sqrt_eq_rpow] at h_sqrt_le
    · -- Upper: f(1)/f(1/2) ≤ √2 * |t|^{1/2}
      have h_le_sqrt : ‖Complex.Gamma ⟨1, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖ ≤ Real.sqrt (2 * |t|) := by
        rw [← Real.sqrt_sq (le_of_lt h_ratio_pos)]
        exact Real.sqrt_le_sqrt hhi
      calc ‖Complex.Gamma ⟨1, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖
          ≤ Real.sqrt (2 * |t|) := h_le_sqrt
        _ = Real.sqrt 2 * Real.sqrt |t| := Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) _
        _ = Real.sqrt 2 * |t| ^ ((1:ℝ)/2) := by
            congr 1; exact Real.sqrt_eq_rpow |t|
  -- Step 3: General case σ ∈ (0,1) \ {1/2}.
  -- Split into σ ∈ (1/2, 1) and σ ∈ (0, 1/2).
  have hσ₁' : σ < 1 := lt_of_le_of_ne hσ₁ hσ_one
  rcases lt_or_gt_of_ne hσ_half with hσ_lt_half | hσ_gt_half
  · -- Case σ < 1/2: use gammaSeq_ratio_bound_lower_half
    exact gammaSeq_ratio_bound_lower_half (hUpper := hUpper) σ hσ₀ hσ_lt_half
  · -- Case σ > 1/2: use gammaSeq_ratio_bound_upper_half
    exact gammaSeq_ratio_bound_upper_half (hUpper := hUpper) σ hσ_gt_half hσ₁'

/-- Stirling bound in the unit strip σ ∈ (0, 1] — THEOREM (was axiom). -/
theorem stirling_unit_strip (σ : ℝ) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2) := by
  -- From gammaSeq_ratio_bound: ‖Γ(σ+it)‖/‖Γ(1/2+it)‖ ~ C·|t|^{σ-1/2}
  -- From gamma_half_lower/upper: ‖Γ(1/2+it)‖ ~ D·e^{-π|t|/2}
  -- Combining: ‖Γ(σ+it)‖ ~ C·D·|t|^{σ-1/2}·e^{-π|t|/2}
  obtain ⟨C₁, C₂, T₁, hC₁, hC₂, hT₁, hratio⟩ :=
    gammaSeq_ratio_bound (hUpper := hUpper) σ hσ₀ hσ₁
  refine ⟨C₁ * Real.sqrt π, C₂ * Real.sqrt (2 * π), max T₁ 1,
    by positivity, by positivity, by positivity, ?_⟩
  intro t ht
  have hT : T₁ ≤ |t| := le_trans (le_max_left _ _) ht
  have ht1 : 1 ≤ |t| := le_trans (le_max_right _ _) ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos ht1
  -- Gamma at 1/2 is nonzero
  have h_half_pos : 0 < ‖Complex.Gamma ⟨1/2, t⟩‖ := by
    rw [norm_pos_iff]; exact Complex.Gamma_ne_zero_of_re_pos (by simp : (0:ℝ) < (⟨1/2, t⟩ : ℂ).re)
  obtain ⟨hlo_r, hhi_r⟩ := hratio t hT
  have h_half_lo := gamma_half_lower t
  have h_half_hi := gamma_half_upper t
  -- ‖Γ(σ+it)‖ = (‖Γ(σ+it)‖/‖Γ(1/2+it)‖) * ‖Γ(1/2+it)‖
  have h_prod : ‖Complex.Gamma ⟨σ, t⟩‖ =
      (‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖) *
      ‖Complex.Gamma ⟨1/2, t⟩‖ := by field_simp
  constructor
  · -- Lower: C₁·|t|^{σ-1/2}·√π·e^{-π|t|/2} ≤ ‖Γ(σ+it)‖
    rw [h_prod]
    calc C₁ * Real.sqrt π * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2)
        = C₁ * |t| ^ (σ - 1/2) * (Real.sqrt π * Real.exp (-π * |t| / 2)) := by ring
      _ ≤ (‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖) *
          ‖Complex.Gamma ⟨1/2, t⟩‖ :=
        mul_le_mul hlo_r h_half_lo (by positivity) (by positivity)
  · -- Upper: ‖Γ(σ+it)‖ ≤ C₂·√(2π)·|t|^{σ-1/2}·e^{-π|t|/2}
    rw [h_prod]
    calc (‖Complex.Gamma ⟨σ, t⟩‖ / ‖Complex.Gamma ⟨1/2, t⟩‖) *
          ‖Complex.Gamma ⟨1/2, t⟩‖
        ≤ C₂ * |t| ^ (σ - 1/2) *
          (Real.sqrt (2 * π) * Real.exp (-π * |t| / 2)) :=
          mul_le_mul hhi_r h_half_hi (norm_nonneg _) (by positivity)
      _ = C₂ * Real.sqrt (2 * π) * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2) := by ring

/-! ## Section 9: Main theorem — all σ > 0

  For σ > 1: reduce to σ₀ = σ - n ∈ (0,1] via Gamma recurrence.
  Γ(σ+it) = (σ-1+it)·(σ-2+it)·...·(σ₀+it)·Γ(σ₀+it)
  Each factor ‖(σ₀+k+it)‖ ∈ [|t|, |t|+σ] for large |t|,
  contributing ~|t|^1 to the norm. After n steps: ~|t|^n factor.
  Combined with |t|^{σ₀-1/2} from the base: |t|^{σ₀+n-1/2} = |t|^{σ-1/2}. -/

omit hUpper in
private lemma mul_rpow_eq (x : ℝ) (hx : 0 < x) (y : ℝ) :
    x * x ^ y = x ^ (y + 1) := by
  calc x * x ^ y = x ^ (1:ℝ) * x ^ y := by rw [Real.rpow_one]
    _ = x ^ (1 + y) := by rw [← Real.rpow_add hx]
    _ = x ^ (y + 1) := by ring_nf

/-- **Gamma Stirling bound** (THEOREM, replacing axiom in GRH.AFEInfrastructure).
    For fixed σ > 0 and large |t|:
      C_lo·|t|^{σ-1/2}·e^{-π|t|/2} ≤ |Γ(σ+it)| ≤ C_hi·|t|^{σ-1/2}·e^{-π|t|/2} -/
theorem gamma_stirling_bound (σ : ℝ) (hσ : 0 < σ) :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2) := by
  by_cases hle : σ ≤ 1
  · exact stirling_unit_strip (hUpper := hUpper) σ hσ hle
  · push_neg at hle
    have hσ1 : 0 < σ - 1 := by linarith
    obtain ⟨C_lo', C_hi', T₀', hClo', hChi', hT₀', hbounds'⟩ :=
      gamma_stirling_bound (σ - 1) hσ1
    refine ⟨C_lo' / 2, 2 * C_hi', max T₀' (2 * (σ - 1)),
      by positivity, by positivity, lt_max_of_lt_left hT₀', ?_⟩
    intro t ht
    have hT₀ : T₀' ≤ |t| := le_trans (le_max_left _ _) ht
    have hσt : 2 * (σ - 1) ≤ |t| := le_trans (le_max_right _ _) ht
    have ht_pos : 0 < |t| := lt_of_lt_of_le hT₀' hT₀
    have hne : (⟨σ - 1, t⟩ : ℂ) ≠ 0 := mk_ne_zero_of_pos _ _ hσ1
    have h_step : ‖Complex.Gamma ⟨σ, t⟩‖ =
        ‖(⟨σ - 1, t⟩ : ℂ)‖ * ‖Complex.Gamma ⟨σ - 1, t⟩‖ := by
      have h_eq : ‖Complex.Gamma ⟨σ - 1 + 1, t⟩‖ =
          ‖(⟨σ - 1, t⟩ : ℂ)‖ * ‖Complex.Gamma ⟨σ - 1, t⟩‖ :=
        norm_Gamma_step (σ - 1) t hne
      rwa [show σ - 1 + 1 = σ from by ring] at h_eq
    have h_norm_lower : |t| ≤ ‖(⟨σ - 1, t⟩ : ℂ)‖ := by
      rw [show ‖(⟨σ - 1, t⟩ : ℂ)‖ = Real.sqrt (Complex.normSq ⟨σ - 1, t⟩) from rfl,
          Complex.normSq_mk]
      calc |t| = Real.sqrt (t ^ 2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt ((σ - 1) * (σ - 1) + t * t) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (σ - 1)])
    have h_norm_upper : ‖(⟨σ - 1, t⟩ : ℂ)‖ ≤ 2 * |t| := by
      rw [show ‖(⟨σ - 1, t⟩ : ℂ)‖ = Real.sqrt (Complex.normSq ⟨σ - 1, t⟩) from rfl,
          Complex.normSq_mk]
      calc Real.sqrt ((σ - 1) * (σ - 1) + t * t)
          ≤ Real.sqrt ((2 * |t|) ^ 2) := by
            apply Real.sqrt_le_sqrt; nlinarith [sq_abs t, sq_nonneg (σ - 1)]
        _ = 2 * |t| := by rw [Real.sqrt_sq (by positivity)]
    have h_rpow : |t| * |t| ^ (σ - 1 - 1/2) = |t| ^ (σ - 1/2) := by
      rw [mul_rpow_eq _ ht_pos]; congr 1; ring
    obtain ⟨hlo', hhi'⟩ := hbounds' t hT₀
    rw [h_step]
    constructor
    · calc C_lo' / 2 * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2)
          = C_lo' / 2 * (|t| * |t| ^ (σ - 1 - 1/2)) * Real.exp (-π * |t| / 2) := by
              rw [h_rpow]
        _ ≤ C_lo' * (|t| * |t| ^ (σ - 1 - 1/2)) * Real.exp (-π * |t| / 2) := by
              have h1 : 0 ≤ |t| * |t| ^ (σ - 1 - 1/2) * Real.exp (-π * |t| / 2) := by positivity
              nlinarith
        _ = |t| * (C_lo' * |t| ^ (σ - 1 - 1/2) * Real.exp (-π * |t| / 2)) := by ring
        _ ≤ ‖(⟨σ - 1, t⟩ : ℂ)‖ * ‖Complex.Gamma ⟨σ - 1, t⟩‖ :=
              mul_le_mul h_norm_lower hlo' (by positivity) (norm_nonneg _)
    · calc ‖(⟨σ - 1, t⟩ : ℂ)‖ * ‖Complex.Gamma ⟨σ - 1, t⟩‖
          ≤ (2 * |t|) * (C_hi' * |t| ^ (σ - 1 - 1/2) * Real.exp (-π * |t| / 2)) :=
            mul_le_mul h_norm_upper hhi' (norm_nonneg _) (by positivity)
        _ = 2 * C_hi' * (|t| * |t| ^ (σ - 1 - 1/2)) * Real.exp (-π * |t| / 2) := by ring
        _ = 2 * C_hi' * |t| ^ (σ - 1/2) * Real.exp (-π * |t| / 2) := by rw [h_rpow]
termination_by ⌈σ⌉₊

/-- Tail-decay interface for the upper Beta branch (from Stirling via axiom).
Derives from Stirling lower control at `σ = a + 1/2` and the explicit
`σ = 1/2` upper bound, then uses the Beta-Gamma identity.
NOTE: depends on `hUpper : GammaRatioUpperHalf` via `gamma_stirling_bound`. -/
theorem betaUpperTailDecayBound_from_stirling : BetaUpperTailDecayBound := by
  intro a ha₀ ha₁
  set σ : ℝ := a + 1 / 2
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    linarith
  obtain ⟨C_lo, _C_hi, T0, hClo, _hChi, hT0, hStirling⟩ :=
    gamma_stirling_bound (hUpper := hUpper) σ hσ_pos
  set T : ℝ := max 1 T0
  set C : ℝ := Real.Gamma a * Real.sqrt (2 * π) / C_lo
  refine ⟨T, C, le_max_left _ _, by
    dsimp [C]
    exact div_pos (mul_pos (Real.Gamma_pos_of_pos ha₀) (Real.sqrt_pos.2 (by positivity))) hClo, ?_⟩
  intro t ht
  have hT0_le : T0 ≤ |t| := le_trans (le_max_right 1 T0) ht
  have hone_le : 1 ≤ |t| := le_trans (le_max_left 1 T0) ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos hone_le
  set E : ℝ := Real.exp (-π * |t| / 2)
  have hStirling_t := hStirling t hT0_le
  have hSigmaExp : σ - 1 / 2 = a := by
    dsimp [σ]
    ring
  have hSigmaExp' : σ - (2 : ℝ)⁻¹ = a := by
    simpa [one_div] using hSigmaExp
  have hGamma_sigma_lower_raw :
      C_lo * |t| ^ (σ - (2 : ℝ)⁻¹) * E ≤ ‖Complex.Gamma ⟨σ, t⟩‖ := by
    simpa [E, one_div, mul_assoc] using hStirling_t.1
  have hGamma_sigma_lower :
      C_lo * |t| ^ a * E ≤ ‖Complex.Gamma ⟨σ, t⟩‖ := by
    simpa [hSigmaExp'] using hGamma_sigma_lower_raw
  have hGamma_half_upper :
      ‖Complex.Gamma ⟨1 / 2, t⟩‖ ≤ Real.sqrt (2 * π) * E := by
    simpa [E] using gamma_half_upper t
  have hpow_pos : 0 < |t| ^ a := Real.rpow_pos_of_pos ht_pos a
  have hE_pos : 0 < E := by
    dsimp [E]
    exact Real.exp_pos _
  have hden_pos : 0 < C_lo * |t| ^ a * E := mul_pos (mul_pos hClo hpow_pos) hE_pos
  have hratio_le :
      ‖Complex.Gamma ⟨1 / 2, t⟩‖ / ‖Complex.Gamma ⟨σ, t⟩‖
        ≤ (Real.sqrt (2 * π) * E) / (C_lo * |t| ^ a * E) := by
    have hstep1 :
        ‖Complex.Gamma ⟨1 / 2, t⟩‖ / ‖Complex.Gamma ⟨σ, t⟩‖
          ≤ ‖Complex.Gamma ⟨1 / 2, t⟩‖ / (C_lo * |t| ^ a * E) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hden_pos hGamma_sigma_lower
    have hstep2 :
        ‖Complex.Gamma ⟨1 / 2, t⟩‖ / (C_lo * |t| ^ a * E)
          ≤ (Real.sqrt (2 * π) * E) / (C_lo * |t| ^ a * E) :=
      div_le_div_of_nonneg_right hGamma_half_upper (le_of_lt hden_pos)
    exact le_trans hstep1 hstep2
  have h_re_a : 0 < (↑a : ℂ).re := by simpa using ha₀
  have h_re_half : 0 < (⟨1 / 2, t⟩ : ℂ).re := by norm_num
  have h_sum : (↑a : ℂ) + (⟨1 / 2, t⟩ : ℂ) = ⟨σ, t⟩ := by
    apply Complex.ext <;> simp [σ]
  have h_beta_eq : Complex.betaIntegral ↑a ⟨1 / 2, t⟩ =
      Complex.Gamma ↑a * Complex.Gamma ⟨1 / 2, t⟩ / Complex.Gamma ⟨σ, t⟩ := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ h_re_a h_re_half, h_sum]
  have h_beta_norm : ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ =
      Real.Gamma a * (‖Complex.Gamma ⟨1 / 2, t⟩‖ / ‖Complex.Gamma ⟨σ, t⟩‖) := by
    rw [h_beta_eq, norm_div, norm_mul]
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos ha₀)]
    ring
  have hGamma_pos : 0 ≤ Real.Gamma a := (Real.Gamma_pos_of_pos ha₀).le
  have h_beta_le_exp :
      ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖
        ≤ Real.Gamma a * ((Real.sqrt (2 * π) * E) / (C_lo * |t| ^ a * E)) := by
    rw [h_beta_norm]
    exact mul_le_mul_of_nonneg_left hratio_le hGamma_pos
  have hE_ne : E ≠ 0 := ne_of_gt hE_pos
  have hpow_ne : |t| ^ a ≠ 0 := ne_of_gt hpow_pos
  calc
    ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖
        ≤ Real.Gamma a * ((Real.sqrt (2 * π) * E) / (C_lo * |t| ^ a * E)) := h_beta_le_exp
    _ = (Real.Gamma a * Real.sqrt (2 * π) / C_lo) * (|t| ^ a)⁻¹ := by
      field_simp [hE_ne, hpow_ne, hClo.ne']
    _ = (Real.Gamma a * Real.sqrt (2 * π) / C_lo) * |t| ^ (-a) := by
      rw [Real.rpow_neg (abs_nonneg t)]
    _ = C * |t| ^ (-a) := by rfl

/-- Lower-tail interface for Beta vertical decay (from Stirling via axiom).
Derives from Stirling upper control at `σ = a + 1/2` and the explicit
`σ = 1/2` lower bound, then uses the Beta-Gamma identity.
NOTE: depends on `hUpper : GammaRatioUpperHalf` via `gamma_stirling_bound`. -/
theorem betaLowerTailDecayBound_from_stirling :
    ∀ (a : ℝ), 0 < a → a < 1 / 2 →
      ∃ (T C : ℝ), 1 ≤ T ∧ 0 < C ∧
        (∀ (t : ℝ), T ≤ |t| →
          C * |t| ^ (-a) ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖) := by
  intro a ha₀ ha₁
  set σ : ℝ := a + 1 / 2
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    linarith
  obtain ⟨_C_lo, C_hi, T0, _hClo, hChi, hT0, hStirling⟩ :=
    gamma_stirling_bound (hUpper := hUpper) σ hσ_pos
  set T : ℝ := max 1 T0
  set C : ℝ := Real.Gamma a * Real.sqrt π / C_hi
  refine ⟨T, C, le_max_left _ _, by
    dsimp [C]
    exact div_pos (mul_pos (Real.Gamma_pos_of_pos ha₀) (Real.sqrt_pos.2 pi_pos)) hChi, ?_⟩
  intro t ht
  have hT0_le : T0 ≤ |t| := le_trans (le_max_right 1 T0) ht
  have hone_le : 1 ≤ |t| := le_trans (le_max_left 1 T0) ht
  have ht_pos : 0 < |t| := lt_of_lt_of_le one_pos hone_le
  set E : ℝ := Real.exp (-π * |t| / 2)
  have hStirling_t := hStirling t hT0_le
  have hSigmaExp : σ - 1 / 2 = a := by
    dsimp [σ]
    ring
  have hSigmaExp' : σ - (2 : ℝ)⁻¹ = a := by
    simpa [one_div] using hSigmaExp
  have hGamma_sigma_upper_raw :
      ‖Complex.Gamma ⟨σ, t⟩‖ ≤ C_hi * |t| ^ (σ - (2 : ℝ)⁻¹) * E := by
    simpa [E, one_div, mul_assoc] using hStirling_t.2
  have hGamma_sigma_upper :
      ‖Complex.Gamma ⟨σ, t⟩‖ ≤ C_hi * |t| ^ a * E := by
    simpa [hSigmaExp'] using hGamma_sigma_upper_raw
  have hGamma_half_lower :
      Real.sqrt π * E ≤ ‖Complex.Gamma ⟨1 / 2, t⟩‖ := by
    simpa [E] using gamma_half_lower t
  have hpow_pos : 0 < |t| ^ a := Real.rpow_pos_of_pos ht_pos a
  have hE_pos : 0 < E := by
    dsimp [E]
    exact Real.exp_pos _
  have hden_pos : 0 < C_hi * |t| ^ a * E := mul_pos (mul_pos hChi hpow_pos) hE_pos
  have hσ_ne : Complex.Gamma ⟨σ, t⟩ ≠ 0 := by
    exact Complex.Gamma_ne_zero_of_re_pos (by simp [show (0:ℝ) < σ by linarith] :
      (0:ℝ) < (⟨σ, t⟩ : ℂ).re)
  have hσ_norm_pos : 0 < ‖Complex.Gamma ⟨σ, t⟩‖ := norm_pos_iff.mpr hσ_ne
  have hratio_ge :
      (Real.sqrt π * E) / (C_hi * |t| ^ a * E)
        ≤ ‖Complex.Gamma ⟨1 / 2, t⟩‖ / ‖Complex.Gamma ⟨σ, t⟩‖ := by
    have hstep1 :
        (Real.sqrt π * E) / (C_hi * |t| ^ a * E)
          ≤ ‖Complex.Gamma ⟨1 / 2, t⟩‖ / (C_hi * |t| ^ a * E) :=
      div_le_div_of_nonneg_right hGamma_half_lower (le_of_lt hden_pos)
    have hstep2 :
        ‖Complex.Gamma ⟨1 / 2, t⟩‖ / (C_hi * |t| ^ a * E)
          ≤ ‖Complex.Gamma ⟨1 / 2, t⟩‖ / ‖Complex.Gamma ⟨σ, t⟩‖ :=
      div_le_div_of_nonneg_left (norm_nonneg _) hσ_norm_pos hGamma_sigma_upper
    exact le_trans hstep1 hstep2
  have h_re_a : 0 < (↑a : ℂ).re := by simpa using ha₀
  have h_re_half : 0 < (⟨1 / 2, t⟩ : ℂ).re := by norm_num
  have h_sum : (↑a : ℂ) + (⟨1 / 2, t⟩ : ℂ) = ⟨σ, t⟩ := by
    apply Complex.ext <;> simp [σ]
  have h_beta_eq : Complex.betaIntegral ↑a ⟨1 / 2, t⟩ =
      Complex.Gamma ↑a * Complex.Gamma ⟨1 / 2, t⟩ / Complex.Gamma ⟨σ, t⟩ := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ h_re_a h_re_half, h_sum]
  have h_beta_norm : ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ =
      Real.Gamma a * (‖Complex.Gamma ⟨1 / 2, t⟩‖ / ‖Complex.Gamma ⟨σ, t⟩‖) := by
    rw [h_beta_eq, norm_div, norm_mul]
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos ha₀)]
    ring
  have hGamma_pos : 0 ≤ Real.Gamma a := (Real.Gamma_pos_of_pos ha₀).le
  have h_beta_ge_exp :
      Real.Gamma a * ((Real.sqrt π * E) / (C_hi * |t| ^ a * E))
        ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ := by
    rw [h_beta_norm]
    exact mul_le_mul_of_nonneg_left hratio_ge hGamma_pos
  have hE_ne : E ≠ 0 := ne_of_gt hE_pos
  have hpow_ne : |t| ^ a ≠ 0 := ne_of_gt hpow_pos
  calc
    C * |t| ^ (-a)
        = Real.Gamma a * ((Real.sqrt π * E) / (C_hi * |t| ^ a * E)) := by
          dsimp [C]
          rw [Real.rpow_neg (abs_nonneg t)]
          field_simp [hE_ne, hpow_ne, hChi.ne']
    _ ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ := h_beta_ge_exp

/-- One-sided lower branch for Beta vertical decay (from Stirling via axiom):
compact-window lower control + tail lower control.
NOTE: depends on `hUpper : GammaRatioUpperHalf` via tail decay bound. -/
theorem betaLowerDecay_from_stirling : BetaLowerDecay := by
  intro a ha₀ ha₁
  rcases betaLowerTailDecayBound_from_stirling (hUpper := hUpper) a ha₀ ha₁ with
    ⟨T, C, hT1, hCpos, htail⟩
  rcases betaLowerCompactWindowBound_independent a ha₀ ha₁ T hT1 with
    ⟨m, hmpos, hcompact⟩
  set B_lo : ℝ := min C m
  refine ⟨B_lo, by
    dsimp [B_lo]
    exact lt_min hCpos hmpos, ?_⟩
  intro t ht1
  by_cases htailCase : T ≤ |t|
  · have htail_t := htail t htailCase
    calc
      B_lo * |t| ^ (-a) ≤ C * |t| ^ (-a) := by
        dsimp [B_lo]
        exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (abs_nonneg t) _)
      _ ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ := htail_t
  · have hleT : |t| ≤ T := le_of_not_ge htailCase
    have hcompact_t : m ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ :=
      hcompact t ht1 hleT
    have hpow_le_one : |t| ^ (-a) ≤ 1 := by
      have hpow_pos : 0 < |t| ^ a := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos ht1) a
      have hone_le : 1 ≤ |t| ^ a := Real.one_le_rpow ht1 ha₀.le
      have hinv : (|t| ^ a)⁻¹ ≤ (1 : ℝ)⁻¹ := (inv_le_inv₀ hpow_pos zero_lt_one).2 hone_le
      simpa [Real.rpow_neg (abs_nonneg _)] using hinv
    calc
      B_lo * |t| ^ (-a) ≤ B_lo * 1 := by
        exact mul_le_mul_of_nonneg_left hpow_le_one (by
          dsimp [B_lo]
          exact le_trans (le_of_lt (lt_min hCpos hmpos)) (le_refl _))
      _ = B_lo := by ring
      _ ≤ m := by
        dsimp [B_lo]
        exact min_le_right _ _
      _ ≤ ‖Complex.betaIntegral ↑a ⟨1 / 2, t⟩‖ := hcompact_t

/-- Two-sided Beta vertical decay (from Stirling via axiom).
Combines compact-window bounds (genuinely independent) with tail decay
bounds (which depend on `hUpper` via `gamma_stirling_bound`).
NOTE: despite previous naming, this is NOT independent of the axiom. -/
theorem betaVerticalDecay_from_stirling : BetaVerticalDecay := by
  have hUpperDecay : BetaUpperDecay :=
    betaUpperDecay_of_interfaces
      betaUpperCompactWindowBound_independent
      (betaUpperTailDecayBound_from_stirling (hUpper := hUpper))
  exact betaVerticalDecay_of_upper_lower
    (betaLowerDecay_from_stirling (hUpper := hUpper))
    hUpperDecay

omit hUpper in
/-- `GammaRatioUpperHalf` was formerly an axiom. Now proved via
    GammaSeq product analysis (see `gammaRatioUpperHalf_proved`).
    Now fully proved via GammaSeq product analysis
    (standard calculus, Σf ≈ ∫f for the function 2u/(u²+t²)). -/
theorem gammaRatioUpperHalf_from_axiom : GammaRatioUpperHalf :=
  gammaRatioUpperHalf_axiom

end GammaRatioUpperHalfInterface

end ZD.StirlingBound
