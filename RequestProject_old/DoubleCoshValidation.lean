import RequestProject.DoubleCoshResidue

/-!
# Double-Cosh Classifier: Validation Against Mathlib's `riemannZeta` Zeros

This file validates the `DoubleCoshResidue` classifier against
`ZD.NontrivialZeros` (defined via Mathlib's `riemannZeta`). It proves that
the classifier is **sound** (its verdicts are correct labels) and
**complete** (every zero gets the correct verdict at every admissible scale),
and checks the classifier's coherence under the functional-equation
reflection `ρ ↔ 1 − ρ`.

## Results

* **(V1) Soundness — balanced verdict ⇒ on-line**: if `R_double(ρ.re, r) = 0`
  at any scale `r > 1` for a nontrivial zero `ρ`, then `ρ ∈ OnLineZeros`.
* **(V2) Soundness — unbalanced verdict ⇒ off-line**: if `0 < R_double(ρ.re, r)`
  at any `r > 0`, `r ≠ 1`, then `ρ ∈ OffLineZeros`.
* **(V3) Completeness — on-line zeros always read zero**: every
  `ρ ∈ OnLineZeros` has `R_double(ρ.re, r) = 0` for **every** `r`.
* **(V4) Completeness — off-line zeros always read positive**: every
  `ρ ∈ OffLineZeros` has `0 < R_double(ρ.re, r)` for every `r > 0, r ≠ 1`.
* **(V5) Dichotomy on the entire zero set**: every `ρ ∈ NontrivialZeros`
  falls into exactly one of the two classifier classes.
* **(V6) FE coherence**: the verdict on `ρ` equals the verdict on `1 − ρ`
  (whose real parts are `β` and `1 − β`, same `|δ|`).
* **(V7) Single-scale capstone**: RH is equivalent to `R_double(ρ.re, r) = 0`
  holding for every nontrivial zero at **any single fixed scale** `r > 1`.

Together these show the classifier is a lossless observable: its verdict
at any single admissible scale `r > 1` determines the critical-line status
of every nontrivial zeta zero.
-/

open Real ZetaDefs

noncomputable section

namespace DoubleCoshValidation

open DoubleCoshResidue

/-! ### §1. Soundness — classifier verdicts are correct labels -/

/-- **(V1) Soundness, balanced**: if the classifier reports balance
(`R_double = 0`) at any scale `r > 1` on a nontrivial zero, the zero lies
on the critical line. No false positives. -/
theorem classifier_balanced_implies_online
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    {r : ℝ} (hr : 1 < r)
    (hbal : pairAgreementDefect r ρ.re = 0) :
    ρ ∈ ZD.OnLineZeros :=
  ⟨hρ, (classifier_iff_online ρ hρ hr).mp hbal⟩

/-- **(V2) Soundness, unbalanced**: if the classifier reports positive
residue at any scale `r > 0, r ≠ 1` on a nontrivial zero, the zero lies
off the critical line. No false positives on the off-line side. -/
theorem classifier_unbalanced_implies_offline
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    (hunbal : 0 < pairAgreementDefect r ρ.re) :
    ρ ∈ ZD.OffLineZeros := by
  refine ⟨hρ, ?_⟩
  intro hhalf
  rw [hhalf] at hunbal
  exact absurd (residue_balanced r) (ne_of_gt hunbal)

/-! ### §2. Completeness — every zero reads its correct class at every scale -/

/-- **(V3) Completeness, on-line**: every on-line zero reads residue `0`
at **every** scale `r` — no false negatives. -/
theorem online_zeros_read_balanced
    (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) (r : ℝ) :
    pairAgreementDefect r ρ.re = 0 :=
  online_zero_residue_zero ρ hρ r

/-- **(V4) Completeness, off-line**: every off-line zero reads strictly
positive residue at every `r > 0, r ≠ 1` — no false negatives. -/
theorem offline_zeros_read_unbalanced
    (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < pairAgreementDefect r ρ.re :=
  residue_unbalanced hr hr1 hρ.2

/-! ### §3. Dichotomy on the entire zero set -/

/-- **(V5) Exhaustive classification**: every nontrivial zeta zero falls
into exactly one class — either on-line (classifier zero at every scale)
or off-line (classifier strictly positive at every `r > 0, r ≠ 1`, and
strictly monotone in `r` for `r > 1`). -/
theorem zeta_zero_classifier_dichotomy
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    (∀ r : ℝ, pairAgreementDefect r ρ.re = 0) ∨
    ((∀ r : ℝ, 0 < r → r ≠ 1 → 0 < pairAgreementDefect r ρ.re) ∧
     (∀ r₁ r₂ : ℝ, 1 < r₁ → r₁ < r₂ →
        pairAgreementDefect r₁ ρ.re < pairAgreementDefect r₂ ρ.re)) := by
  rcases Classical.em (ρ.re = 1/2) with hon | hoff
  · left
    intro r; rw [hon]; exact residue_balanced r
  · right
    refine ⟨?_, ?_⟩
    · intro r hr hr1
      exact residue_unbalanced hr hr1 hoff
    · intro r₁ r₂ hr₁ hr₁₂
      exact residue_mono_scale hoff hr₁ hr₁₂

/-! ### §4. FE coherence — ρ and 1 − ρ give identical verdicts -/

/-- **(V6) FE coherence**: the classifier is invariant under the functional
equation reflection. `ρ` and `1 − ρ` (whose real parts are `β` and `1 − β`)
produce identical residues at every scale. -/
theorem classifier_fe_invariant (ρ : ℂ) (r : ℝ) :
    pairAgreementDefect r ρ.re = pairAgreementDefect r (1 - ρ).re := by
  have h : (1 - ρ).re = 1 - ρ.re := by simp
  rw [h]
  exact residue_reflect r ρ.re

/-- **(V6′) FE consistency with zeros**: the reflected point `1 − ρ` is also
a zero of `riemannZeta` (by Mathlib's functional equation), so the
classifier's FE-invariant verdict is coherent with the zero set being
FE-closed. -/
theorem classifier_fe_zero_pair
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) (r : ℝ) :
    riemannZeta ρ = 0 ∧
    riemannZeta (1 - ρ) = 0 ∧
    pairAgreementDefect r ρ.re = pairAgreementDefect r (1 - ρ).re := by
  have hz : riemannZeta ρ = 0 := hρ.2.2
  have hne_neg : ∀ n : ℕ, ρ ≠ -(↑n : ℂ) := by
    intro n hn
    have := congr_arg Complex.re hn
    simp at this; linarith [hρ.1]
  have hne_one : ρ ≠ 1 := by
    intro h
    have h1 := hρ.2.1
    rw [h, Complex.one_re] at h1
    linarith
  have hfe : riemannZeta (1 - ρ) = 0 := by
    rw [riemannZeta_one_sub hne_neg hne_one, hz, mul_zero]
  exact ⟨hz, hfe, classifier_fe_invariant ρ r⟩

/-! ### §5. Program-level compressed statement

The entire on-line/off-line classification program reduces to a single
biconditional: for any nontrivial zero and any admissible scale `r > 1`,
on-line membership is equivalent to classifier balance. -/

/-- **Compressed program statement**: for every nontrivial zeta zero `ρ` and
every admissible scale `r > 1`,

    ρ ∈ OnLineZeros  ↔  R_double(ρ.re, r) = 0.

One biconditional captures soundness, completeness, and the classifier's
characterization of the critical line in one breath. -/
theorem rho_online_iff_residue_zero
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    {r : ℝ} (hr : 1 < r) :
    ρ ∈ ZD.OnLineZeros ↔ pairAgreementDefect r ρ.re = 0 := by
  constructor
  · intro hon
    exact online_zero_residue_zero ρ hon r
  · intro hres
    exact ⟨hρ, (classifier_iff_online ρ hρ hr).mp hres⟩

/-- **Off-line mirror**: for every nontrivial zeta zero `ρ` and every
admissible scale `r > 1`,

    ρ ∈ OffLineZeros  ↔  0 < R_double(ρ.re, r). -/
theorem rho_offline_iff_residue_pos
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    {r : ℝ} (hr : 1 < r) :
    ρ ∈ ZD.OffLineZeros ↔ 0 < pairAgreementDefect r ρ.re := by
  constructor
  · intro hoff
    exact residue_unbalanced (by linarith) (by linarith) hoff.2
  · intro hres
    refine ⟨hρ, ?_⟩
    intro hhalf
    rw [hhalf] at hres
    exact absurd (residue_balanced r) (ne_of_gt hres)

/-! ### §6. Single-scale capstone -/

/-- **(V7) Single-scale RH equivalence**: RH is equivalent to the classifier
reading zero on every nontrivial zero at **any single fixed scale** `r > 1`.
Checking at one scale suffices — the classifier is lossless. -/
theorem rh_iff_classifier_at_scale {r : ℝ} (hr : 1 < r) :
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → pairAgreementDefect r ρ.re = 0) ↔
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2) := by
  constructor
  · intro h ρ hρ
    exact (classifier_iff_online ρ hρ hr).mp (h ρ hρ)
  · intro h ρ hρ
    rw [h ρ hρ]; exact residue_balanced r

/-- **(V7′) Multi-scale equivalent**: reading zero at **every** `r > 1` is
equivalent to RH — identical to V7 by pointwise application. -/
theorem rh_iff_classifier_all_scales :
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ r : ℝ, 1 < r → pairAgreementDefect r ρ.re = 0) ↔
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2) := by
  constructor
  · intro h ρ hρ
    have : pairAgreementDefect 2 ρ.re = 0 := h ρ hρ 2 (by norm_num)
    exact (classifier_iff_online ρ hρ (by norm_num : (1:ℝ) < 2)).mp this
  · intro h ρ hρ r hr
    rw [h ρ hρ]; exact residue_balanced r

/-! ### §7. Classification bundles applied to the zero set -/

/-- For any nontrivial zero, the applied classifier outputs a complete
verdict record: class label, residue reading at the unit basis `r = π/3`,
readings at every prime, FE invariance, and scale growth (if off-line). -/
structure ZetaZeroClassifierReport (ρ : ℂ) : Prop where
  is_nontrivial : ρ ∈ ZD.NontrivialZeros
  zeta_eq_zero : riemannZeta ρ = 0
  /-- At the natural unit basis `r = π/3`, the residue classifies. -/
  residue_at_pi_third_zero_iff_online :
    pairAgreementDefect (Real.pi / 3) ρ.re = 0 ↔ ρ.re = 1/2
  /-- At any admissible scale, the classifier's verdict equals the label. -/
  classifier_verdict_iff_online :
    ∀ {r : ℝ}, 1 < r →
      (pairAgreementDefect r ρ.re = 0 ↔ ρ.re = 1/2)
  /-- FE-invariance: the verdict on the reflected zero matches. -/
  fe_invariant :
    ∀ r : ℝ, pairAgreementDefect r ρ.re = pairAgreementDefect r (1 - ρ).re
  /-- On-line branch: residue vanishes at every scale. -/
  on_line_residue_zero :
    ρ.re = 1/2 → ∀ r : ℝ, pairAgreementDefect r ρ.re = 0
  /-- Off-line branch: residue strictly positive at every admissible scale. -/
  off_line_residue_pos :
    ρ.re ≠ 1/2 → ∀ {r : ℝ}, 0 < r → r ≠ 1 →
      0 < pairAgreementDefect r ρ.re
  /-- Off-line branch: residue strictly grows with scale for `r > 1`. -/
  off_line_residue_mono :
    ρ.re ≠ 1/2 → ∀ {r₁ r₂ : ℝ}, 1 < r₁ → r₁ < r₂ →
      pairAgreementDefect r₁ ρ.re < pairAgreementDefect r₂ ρ.re

/-- Constructor: every nontrivial zero yields a classifier report. -/
def classifierReport (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    ZetaZeroClassifierReport ρ where
  is_nontrivial := hρ
  zeta_eq_zero := hρ.2.2
  residue_at_pi_third_zero_iff_online :=
    classifier_iff_online ρ hρ
      (by have := Real.pi_gt_three; linarith : (1:ℝ) < Real.pi / 3)
  classifier_verdict_iff_online := fun {_} hr => classifier_iff_online ρ hρ hr
  fe_invariant := classifier_fe_invariant ρ
  on_line_residue_zero := fun h r => by
    rw [h]; exact residue_balanced r
  off_line_residue_pos := fun h {_} hr hr1 => residue_unbalanced hr hr1 h
  off_line_residue_mono := fun h {_ _} hr₁ hr₁₂ => residue_mono_scale h hr₁ hr₁₂

/-! ### §8. Smoke tests — exercising the validation on the real zero set -/

/-- Every nontrivial zero gets a classifier report. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) : ZetaZeroClassifierReport ρ :=
  classifierReport ρ hρ

/-- On-line zeros read balanced at the unit basis `r = π/3`. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    pairAgreementDefect (Real.pi / 3) ρ.re = 0 :=
  online_zeros_read_balanced ρ hρ _

/-- Off-line zeros read unbalanced at the unit basis `r = π/3`. -/
example (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    0 < pairAgreementDefect (Real.pi / 3) ρ.re :=
  offline_zeros_read_unbalanced ρ hρ
    (by have := Real.pi_gt_three; positivity)
    (by have := Real.pi_gt_three
        intro h
        have : Real.pi = 3 := by linarith [(show Real.pi / 3 = 1 from h)]
        linarith)

/-- RH is equivalent to classifier balance at r = π/3. -/
example :
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      pairAgreementDefect (Real.pi / 3) ρ.re = 0) ↔
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2) :=
  rh_iff_classifier_at_scale
    (by have := Real.pi_gt_three; linarith : (1:ℝ) < Real.pi / 3)

/-! ### §9. Axiom hygiene

Expected footprint: `[propext, Classical.choice, Quot.sound]` only.
Any leak indicates an upstream issue. -/

#print axioms classifier_balanced_implies_online
#print axioms classifier_unbalanced_implies_offline
#print axioms online_zeros_read_balanced
#print axioms offline_zeros_read_unbalanced
#print axioms zeta_zero_classifier_dichotomy
#print axioms classifier_fe_invariant
#print axioms classifier_fe_zero_pair
#print axioms rh_iff_classifier_at_scale
#print axioms rh_iff_classifier_all_scales
#print axioms rho_online_iff_residue_zero
#print axioms rho_offline_iff_residue_pos
#print axioms classifierReport

end DoubleCoshValidation

end
