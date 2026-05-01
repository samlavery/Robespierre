import RequestProject.HarmonicDiagnostics

/-!
# Double-Cosh Residue: Balanced vs. Unbalanced Harmonic Classification

This file states and proves the structural theorems that make the reflected
cosh-kernel pair a **classifier** between balanced (β = 1/2) and unbalanced
(β ≠ 1/2) harmonic configurations. The residue is the
`pairAgreementDefect r β = (K_L β (log r) − K_R β (log r))²` introduced in
§11.5 of `OfflineAmplitudeMethods.lean`.

## Main identity

The **closed-form factorization** is the workhorse — everything else is a
corollary:

  R_double(β, r) := pairAgreementDefect r β
                  = 4 · sinh²((β − 1/2)·log r) · sinh²((1/2 − π/6)·log r)

The β-dependence is isolated in the first sinh² factor; the second is a
β-independent calibration that vanishes only at `log r = 0`.

## Classification signatures (proved below)

* **(S1)** `R_double(1/2, r) = 0` at every scale — balanced class pinned.
* **(S2)** `R_double(β, r) > 0` for β ≠ 1/2, r > 0, r ≠ 1 — unbalanced class lifted.
* **(S3)** `R_double(β, r) = R_double(1 − β, r)` — the residue measures |δ|, not sign.
* **(S4)** `|β₁ − 1/2| < |β₂ − 1/2| ⟹ R_double(β₁, r) < R_double(β₂, r)` at r > 1.
* **(S5)** For β ≠ 1/2, `1 < r₁ < r₂ ⟹ R_double(β, r₁) < R_double(β, r₂)`.

Combining (S1) + (S5): the separation μ_U(r) − μ_B(r) = R_double(β, r) − 0
strictly increases in r whenever the input class is unbalanced. The
balanced-class residue stays pinned at 0; the unbalanced class lifts away
and the gap widens monotonically with scale.
-/

open Real ZetaDefs

noncomputable section

namespace DoubleCoshResidue

/-! ### §0. Local helpers for `Real.sinh` -/

private lemma sinh_lt_sinh {a b : ℝ} (h : a < b) : Real.sinh a < Real.sinh b := by
  have h1 : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr h
  have h2 : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith)
  have ea := Real.sinh_eq a
  have eb := Real.sinh_eq b
  linarith

private lemma sinh_eq_zero_iff (x : ℝ) : Real.sinh x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, Real.sinh_zero]⟩
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · have := sinh_lt_sinh hlt
    rw [Real.sinh_zero] at this; linarith
  · exact heq
  · have := sinh_lt_sinh hgt
    rw [Real.sinh_zero] at this; linarith

private lemma sinh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.sinh x := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0, Real.sinh_zero]
  · have := sinh_lt_sinh h0
    rw [Real.sinh_zero] at this; linarith

private lemma sq_sinh_abs (x : ℝ) : Real.sinh x ^ 2 = Real.sinh |x| ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · push_neg at hx
    rw [abs_of_neg hx, Real.sinh_neg, neg_sq]

private lemma sinh_sq_strict_mono_of_abs_lt {a b : ℝ} (h : |a| < |b|) :
    Real.sinh a ^ 2 < Real.sinh b ^ 2 := by
  rw [sq_sinh_abs a, sq_sinh_abs b]
  have hna : 0 ≤ Real.sinh |a| := sinh_nonneg_of_nonneg (abs_nonneg _)
  have hmono : Real.sinh |a| < Real.sinh |b| := sinh_lt_sinh h
  exact sq_lt_sq' (by linarith) hmono

/-! ### §1. Closed-form factorization -/

/-- **Closed-form factorization of the pair-agreement defect.**
  The β-dependence is isolated in the first factor. The second factor is a
  β-independent calibration that vanishes only when `log r = 0`, i.e. `r = 1`. -/
theorem pairAgreementDefect_sinh_factor (r β : ℝ) :
    pairAgreementDefect r β =
      4 * Real.sinh ((β - 1/2) * Real.log r) ^ 2 *
          Real.sinh ((1/2 - Real.pi/6) * Real.log r) ^ 2 := by
  unfold pairAgreementDefect coshDetectorLeft coshDetectorRight
  have hL : (β - Real.pi / 6) * Real.log r =
            (β - 1/2) * Real.log r + (1/2 - Real.pi / 6) * Real.log r := by ring
  have hR : (β - (1 - Real.pi / 6)) * Real.log r =
            (β - 1/2) * Real.log r - (1/2 - Real.pi / 6) * Real.log r := by ring
  rw [hL, hR, Real.cosh_add, Real.cosh_sub]
  ring

/-! ### §2. Classification signatures (S1)–(S5) -/

/-- **(S1) Balanced class pinned at zero.** At β = 1/2 the residue vanishes
unconditionally, at every scale r. -/
theorem residue_balanced (r : ℝ) : pairAgreementDefect r (1/2) = 0 := by
  rw [pairAgreementDefect_sinh_factor]
  have h : ((1:ℝ)/2 - 1/2) * Real.log r = 0 := by ring
  rw [h, Real.sinh_zero]; ring

/-- **(S2) Unbalanced class strictly positive.** For β ≠ 1/2 at any scale
r > 0, r ≠ 1, the residue is strictly positive. -/
theorem residue_unbalanced {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {β : ℝ} (hβ : β ≠ 1/2) :
    0 < pairAgreementDefect r β :=
  pairAgreementDefect_pos hr hr1 hβ

/-- **(S3) Reflection invariance.** The residue measures |β − 1/2|, not its
sign: β and its FE-reflection 1 − β give identical residues at every scale. -/
theorem residue_reflect (r β : ℝ) :
    pairAgreementDefect r β = pairAgreementDefect r (1 - β) := by
  rw [pairAgreementDefect_sinh_factor, pairAgreementDefect_sinh_factor]
  have h : (1 - β - 1/2) * Real.log r = -((β - 1/2) * Real.log r) := by ring
  rw [h, Real.sinh_neg, neg_sq]

/-- **(S4) Residue grows with offset magnitude.** At any scale r > 1, a larger
offset |β − 1/2| produces a strictly larger residue. -/
theorem residue_mono_offset {r : ℝ} (hr : 1 < r) {β₁ β₂ : ℝ}
    (h : |β₁ - 1/2| < |β₂ - 1/2|) :
    pairAgreementDefect r β₁ < pairAgreementDefect r β₂ := by
  rw [pairAgreementDefect_sinh_factor, pairAgreementDefect_sinh_factor]
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hπ : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hc_ne : (1/2 : ℝ) - Real.pi/6 ≠ 0 := by intro h'; linarith
  have hc_log_ne : ((1/2 : ℝ) - Real.pi/6) * Real.log r ≠ 0 :=
    mul_ne_zero hc_ne hlog.ne'
  have hsinh_c_ne : Real.sinh (((1/2 : ℝ) - Real.pi/6) * Real.log r) ≠ 0 :=
    fun hh => hc_log_ne ((sinh_eq_zero_iff _).mp hh)
  have hc_sq_pos : 0 < Real.sinh (((1/2 : ℝ) - Real.pi/6) * Real.log r) ^ 2 := by
    positivity
  have habs : |(β₁ - 1/2) * Real.log r| < |(β₂ - 1/2) * Real.log r| := by
    rw [abs_mul, abs_mul, abs_of_pos hlog]
    exact mul_lt_mul_of_pos_right h hlog
  have hsinh_lt : Real.sinh ((β₁ - 1/2) * Real.log r) ^ 2 <
                   Real.sinh ((β₂ - 1/2) * Real.log r) ^ 2 :=
    sinh_sq_strict_mono_of_abs_lt habs
  nlinarith [hc_sq_pos, hsinh_lt, sq_nonneg (Real.sinh ((β₁ - 1/2) * Real.log r))]

/-- **(S5) Separation widens with scale.** For fixed unbalanced β ≠ 1/2, the
residue strictly increases as r grows (for r > 1). -/
theorem residue_mono_scale {β : ℝ} (hβ : β ≠ 1/2)
    {r₁ r₂ : ℝ} (hr₁ : 1 < r₁) (hr₁₂ : r₁ < r₂) :
    pairAgreementDefect r₁ β < pairAgreementDefect r₂ β := by
  rw [pairAgreementDefect_sinh_factor, pairAgreementDefect_sinh_factor]
  have hr₁_pos : 0 < r₁ := by linarith
  have hlog₁ : 0 < Real.log r₁ := Real.log_pos hr₁
  have hlog₂ : 0 < Real.log r₂ := Real.log_pos (by linarith)
  have hloglt : Real.log r₁ < Real.log r₂ := Real.log_lt_log hr₁_pos hr₁₂
  have hπ : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hc_ne : ((1/2 : ℝ) - Real.pi/6) ≠ 0 := by intro h; linarith
  have hδ_ne : (β - 1/2) ≠ 0 := sub_ne_zero.mpr hβ
  have habs_δ : |(β - 1/2) * Real.log r₁| < |(β - 1/2) * Real.log r₂| := by
    rw [abs_mul, abs_mul, abs_of_pos hlog₁, abs_of_pos hlog₂]
    exact mul_lt_mul_of_pos_left hloglt (abs_pos.mpr hδ_ne)
  have habs_c : |((1/2 : ℝ) - Real.pi/6) * Real.log r₁| <
                 |((1/2 : ℝ) - Real.pi/6) * Real.log r₂| := by
    rw [abs_mul, abs_mul, abs_of_pos hlog₁, abs_of_pos hlog₂]
    exact mul_lt_mul_of_pos_left hloglt (abs_pos.mpr hc_ne)
  have h_δ_sq := sinh_sq_strict_mono_of_abs_lt habs_δ
  have h_c_sq := sinh_sq_strict_mono_of_abs_lt habs_c
  have hδ_log₁_ne : (β - 1/2) * Real.log r₁ ≠ 0 := mul_ne_zero hδ_ne hlog₁.ne'
  have hc_log₁_ne : ((1/2 : ℝ) - Real.pi/6) * Real.log r₁ ≠ 0 :=
    mul_ne_zero hc_ne hlog₁.ne'
  have hsinh_δ₁_ne : Real.sinh ((β - 1/2) * Real.log r₁) ≠ 0 :=
    fun h => hδ_log₁_ne ((sinh_eq_zero_iff _).mp h)
  have hsinh_c₁_ne : Real.sinh (((1/2 : ℝ) - Real.pi/6) * Real.log r₁) ≠ 0 :=
    fun h => hc_log₁_ne ((sinh_eq_zero_iff _).mp h)
  have hδ₁_pos : 0 < Real.sinh ((β - 1/2) * Real.log r₁) ^ 2 := by positivity
  have hc₁_pos : 0 < Real.sinh (((1/2 : ℝ) - Real.pi/6) * Real.log r₁) ^ 2 := by
    positivity
  nlinarith [h_δ_sq, h_c_sq, hδ₁_pos, hc₁_pos,
             sq_nonneg (Real.sinh ((β - 1/2) * Real.log r₂)),
             sq_nonneg (Real.sinh (((1/2 : ℝ) - Real.pi/6) * Real.log r₂))]

/-! ### §3. Classification summary -/

/-- **Class separation at any scale r > 1.** The balanced class reads 0;
every unbalanced input reads strictly positive; the balanced reading is
strictly less than any unbalanced reading. -/
theorem classify_at_scale {r : ℝ} (hr : 1 < r) {β : ℝ} (hβ : β ≠ 1/2) :
    pairAgreementDefect r (1/2) = 0 ∧
    0 < pairAgreementDefect r β ∧
    pairAgreementDefect r (1/2) < pairAgreementDefect r β := by
  refine ⟨residue_balanced r, ?_, ?_⟩
  · exact residue_unbalanced (by linarith) (by linarith) hβ
  · rw [residue_balanced]
    exact residue_unbalanced (by linarith) (by linarith) hβ

/-- **Widening-gap signature.** The balanced residue stays pinned at 0 as r
grows, while any unbalanced residue strictly increases. The classification
margin `μ_U(r) − μ_B(r)` therefore strictly widens with r. -/
theorem widening_gap {β : ℝ} (hβ : β ≠ 1/2) {r₁ r₂ : ℝ}
    (hr₁ : 1 < r₁) (hr₁₂ : r₁ < r₂) :
    pairAgreementDefect r₁ (1/2) = pairAgreementDefect r₂ (1/2) ∧
    pairAgreementDefect r₁ β < pairAgreementDefect r₂ β ∧
    (pairAgreementDefect r₁ β - pairAgreementDefect r₁ (1/2)) <
      (pairAgreementDefect r₂ β - pairAgreementDefect r₂ (1/2)) := by
  have hbal_eq : pairAgreementDefect r₁ (1/2) = pairAgreementDefect r₂ (1/2) := by
    rw [residue_balanced, residue_balanced]
  refine ⟨hbal_eq, residue_mono_scale hβ hr₁ hr₁₂, ?_⟩
  rw [residue_balanced, residue_balanced]
  simpa using residue_mono_scale hβ hr₁ hr₁₂

/-! ### §4. Applied to actual zeta zeros -/

/-- **Applied to an on-line zeta zero.** An `ρ ∈ OnLineZeros` reads
residue = 0 at every scale: the balanced class on a real observable. -/
theorem online_zero_residue_zero (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) (r : ℝ) :
    pairAgreementDefect r ρ.re = 0 := by
  rw [hρ.2]; exact residue_balanced r

/-- **Applied to an off-line zeta zero.** An `ρ ∈ OffLineZeros` reads strictly
positive residue at every scale r > 1, and the residue grows strictly with r.
This is the classifier firing on a real observable. -/
theorem offline_zero_residue_grows (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {r₁ r₂ : ℝ} (hr₁ : 1 < r₁) (hr₁₂ : r₁ < r₂) :
    0 < pairAgreementDefect r₁ ρ.re ∧
    pairAgreementDefect r₁ ρ.re < pairAgreementDefect r₂ ρ.re :=
  ⟨residue_unbalanced (by linarith) (by linarith) hρ.2,
   residue_mono_scale hρ.2 hr₁ hr₁₂⟩

/-- **Classifier biconditional on an actual zeta zero.** For any nontrivial
zeta zero ρ and any scale r > 1, the residue is zero iff ρ is on the
critical line. This is the double-cosh discriminant in its cleanest form. -/
theorem classifier_iff_online (ρ : ℂ) (_hρ : ρ ∈ ZD.NontrivialZeros)
    {r : ℝ} (hr : 1 < r) :
    pairAgreementDefect r ρ.re = 0 ↔ ρ.re = 1/2 :=
  pairAgreementDefect_eq_zero_iff (by linarith) (by linarith)

end DoubleCoshResidue

end
