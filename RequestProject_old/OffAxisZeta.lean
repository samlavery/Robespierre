/-
# Off-Axis Zeta Zeros Force Observable Anti-Symmetry
## Proof Path (fully formalized below)
```
offAxisZero (ρ with Re ρ ≠ 1/2, ζ(ρ)=0, 0 < Re ρ < 1)
  │
  ├─► [4-way orbit]  ζ(ρ)=0, ζ(1-ρ)=0, ζ(conj ρ)=0, ζ(1-conj ρ)=0
  │     │  (functional equation + conjugation symmetry)
  │     │
  │     └─► [orbit distinctness]  ρ ≠ 1-ρ  (because Re ρ ≠ 1/2)
  │
  ├─► [critical displacement observable]  O(s) := Re(s) - 1/2
  │     │
  │     ├─ O(conj s) = O(s)          (conjugation-invariant)
  │     ├─ O(s) = 0 ⟺ Re s = 1/2   (vanishes on critical line)
  │     └─ O(1 - s) = -O(s)          (anti-symmetric under reflection)
  │
  ├─► [anti-symmetry event]  O(ρ) ≠ 0  ∧  O(ρ) = -O(1-ρ)
  │
  └─► [harmonic amplitude bridge]
        For x > 1:  x^(Re ρ) ≠ x^(Re(1-ρ))
        i.e. the explicit-formula contributions of the zero pair
        {ρ, 1-ρ} have distinct magnitudes — a measurable prime-side distortion.
```
-/
import Mathlib

noncomputable section
open Complex Real
-- ============================================================================
-- § 1. Definitions
-- ============================================================================
/-- Displacement from the critical line Re(s) = 1/2. -/
def criticalDisplacement (s : ℂ) : ℝ := s.re - 1 / 2
/-- A symmetry-compatible observable: conjugation-invariant and vanishes on the
    critical line.  Any such observable is "blind" to on-axis zeros and respects
    the natural symmetry of the zeta zero set. -/
structure SymmetryCompatibleObservable (O : ℂ → ℝ) : Prop where
  conj_invariant   : ∀ s : ℂ, O (starRingEnd ℂ s) = O s
  vanishes_on_axis : ∀ s : ℂ, s.re = 1 / 2 → O s = 0
/-- An anti-symmetry event at ρ: the observable is nonzero and anti-symmetric
    under the functional-equation reflection s ↦ 1 − s.  This is the "detector
    fires" condition — precisely the signature an off-axis zero must leave. -/
structure ObservableAntiSymmetryEvent (O : ℂ → ℝ) (ρ : ℂ) : Prop where
  nonzero       : O ρ ≠ 0
  antisymmetric : O ρ = -(O (1 - ρ))
/-- The harmonic amplitude at scale x: |x^s| = x^(Re s).
    In the explicit formula ψ(x) = x − Σ_ρ x^ρ/ρ − …, each zero ρ contributes
    a term whose magnitude is governed by x^(Re ρ). -/
def harmonicAmplitude (x : ℝ) (s : ℂ) : ℝ := x ^ s.re
/-
PROBLEM
============================================================================
§ 2. Properties of criticalDisplacement  (pure real-arithmetic lemmas)
============================================================================
PROVIDED SOLUTION
Unfold criticalDisplacement. conj(s).re = s.re, so both sides are s.re - 1/2.
-/
lemma criticalDisplacement_conj (s : ℂ) :
    criticalDisplacement (starRingEnd ℂ s) = criticalDisplacement s := by
  unfold criticalDisplacement; norm_num;
/-
PROVIDED SOLUTION
Unfold criticalDisplacement. (1-s).re = 1 - s.re, so LHS = 1 - s.re - 1/2 = 1/2 - s.re = -(s.re - 1/2) = -RHS.
-/
lemma criticalDisplacement_one_sub (s : ℂ) :
    criticalDisplacement (1 - s) = -(criticalDisplacement s) := by
  unfold criticalDisplacement; norm_num; ring;
/-
PROVIDED SOLUTION
Unfold criticalDisplacement. s.re - 1/2 = 0 ↔ s.re = 1/2. Use sub_eq_zero.
-/
lemma criticalDisplacement_eq_zero_iff (s : ℂ) :
    criticalDisplacement s = 0 ↔ s.re = 1 / 2 := by
  unfold criticalDisplacement; rw [ sub_eq_zero ] ;
/-
PROVIDED SOLUTION
Use criticalDisplacement_eq_zero_iff to convert, then apply h.
-/
lemma criticalDisplacement_ne_zero_of_offaxis (s : ℂ) (h : s.re ≠ 1 / 2) :
    criticalDisplacement s ≠ 0 := by
  exact sub_ne_zero_of_ne h
-- ============================================================================
-- § 3. criticalDisplacement is a SymmetryCompatibleObservable
-- ============================================================================
theorem criticalDisplacement_is_symmetry_compatible :
    SymmetryCompatibleObservable criticalDisplacement := by
  exact ⟨criticalDisplacement_conj, fun s hs =>
    (criticalDisplacement_eq_zero_iff s).mpr hs⟩
-- ============================================================================
-- § 4. Off-axis zero forces anti-symmetry event on criticalDisplacement
-- ============================================================================
theorem criticalDisplacement_antisymmetry_event
    (ρ : ℂ) (hoff : ρ.re ≠ 1 / 2) :
    ObservableAntiSymmetryEvent criticalDisplacement ρ :=
  ⟨criticalDisplacement_ne_zero_of_offaxis ρ hoff, by
    have := criticalDisplacement_one_sub ρ; linarith⟩
/-
PROBLEM
============================================================================
§ 5. Four-fold symmetry orbit of zeta zeros
============================================================================
Conjugation symmetry of the Riemann zeta function: ζ(conj s) = conj(ζ(s)).
    This follows from the Dirichlet series having real (= 1) coefficients and
    analytic continuation preserving the Schwarz reflection principle.
PROVIDED SOLUTION
The Riemann zeta function satisfies ζ(conj s) = conj(ζ(s)) because it has real coefficients. Look for an existing Mathlib lemma. Try searching for riemannZeta_conj or checking if there's a general LSeries conjugation result. The definition goes through `completedRiemannZeta` and `completedRiemannZeta₀`. Alternatively, for Re s > 1, use the Dirichlet series representation and show term-by-term conjugation. Then extend by analytic continuation.
-/
lemma riemannZeta_conj (s : ℂ) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  by_contra h_neq;
  -- Apply the fact that the Riemann zeta function is real on the real line and that it's analytic to derive a contradiction.
  have h_conj : ∀ s : ℂ, riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
    intro s
    by_cases hs : s.re > 1;
    · have h_conj : ∀ s : ℂ, s.re > 1 → riemannZeta s = ∑' n : ℕ, (1 : ℂ) / (n + 1) ^ s := by
        exact?;
      rw [ h_conj s hs, h_conj ( starRingEnd ℂ s ) ];
      · rw [ Complex.conj_tsum ] ; congr ; ext n ; norm_num [ Complex.cpow_def ] ; ring;
        norm_cast ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
      · simpa using hs;
    · -- By the identity theorem for analytic functions, since the zeta function is analytic on the entire complex plane (except at s=1), and it's equal to its conjugate for Re(s) > 1, it must be equal to its conjugate everywhere.
      have h_identity : ∀ s : ℂ, riemannZeta s = starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) := by
        have h_analytic : ∀ s : ℂ, s ≠ 1 → AnalyticAt ℂ riemannZeta s := by
          intro s hs; exact (by
          apply_rules [ DifferentiableOn.analyticAt, riemannZeta ];
          rotate_right;
          exact { s : ℂ | s ≠ 1 };
          · intro s hs; exact (by
            refine' DifferentiableAt.differentiableWithinAt _;
            grind +suggestions);
          · exact isOpen_ne.mem_nhds hs)
        have h_identity : ∀ s : ℂ, s ≠ 1 → riemannZeta s = starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) := by
          intros s hs_ne_one
          have h_eq : ∀ s : ℂ, s.re > 1 → riemannZeta s = starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) := by
            intro s hs_gt_one
            have h_eq : riemannZeta s = ∑' n : ℕ, (1 : ℂ) / (n + 1) ^ s := by
              grind +suggestions;
            have h_eq_conj : riemannZeta (starRingEnd ℂ s) = ∑' n : ℕ, (1 : ℂ) / (n + 1) ^ (starRingEnd ℂ s) := by
              rw [ zeta_eq_tsum_one_div_nat_add_one_cpow ] ; aesop;
            rw [ h_eq, h_eq_conj, Complex.conj_tsum ];
            refine' tsum_congr fun n => _;
            simp +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ];
            norm_cast ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
          have h_identity : AnalyticOnNhd ℂ (fun s => riemannZeta s - starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))) (Set.univ \ {1}) := by
            apply_rules [ DifferentiableOn.analyticOnNhd ];
            · refine' fun s hs => DifferentiableAt.differentiableWithinAt _;
              refine' DifferentiableAt.sub _ _;
              · exact h_analytic s hs.2 |> AnalyticAt.differentiableAt;
              · have h_diff : DifferentiableAt ℂ riemannZeta (starRingEnd ℂ s) := by
                  exact h_analytic _ ( by simpa [ Complex.ext_iff ] using hs.2 ) |> AnalyticAt.differentiableAt;
                have h_diff : HasDerivAt (fun s => starRingEnd ℂ (riemannZeta (starRingEnd ℂ s))) (starRingEnd ℂ (deriv riemannZeta (starRingEnd ℂ s))) s := by
                  rw [ hasDerivAt_iff_tendsto_slope_zero ];
                  have := h_diff.hasDerivAt.tendsto_slope_zero;
                  convert Complex.continuous_conj.continuousAt.tendsto.comp ( this.comp ( show Filter.Tendsto ( fun t : ℂ => starRingEnd ℂ t ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhdsWithin 0 { 0 } ᶜ ) from ?_ ) ) using 2 <;> norm_num;
                  rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
                exact h_diff.differentiableAt;
            · exact isOpen_univ.sdiff isClosed_singleton;
          have h_identity : ∀ s : ℂ, s ≠ 1 → riemannZeta s - starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) = 0 := by
            intro s hs_ne_one;
            apply h_identity.eqOn_zero_of_preconnected_of_eventuallyEq_zero;
            rotate_right;
            exact 2;
            · have h_preconnected : IsPreconnected (Set.univ \ {0} : Set ℂ) := by
                have h_preconnected : IsConnected (Set.univ \ {0} : Set ℂ) := by
                  have h_connected : IsConnected (Set.range (fun z : ℂ => Complex.exp z)) := by
                    exact isConnected_range ( Complex.continuous_exp );
                  convert h_connected using 1;
                  ext; simp [Complex.exp_ne_zero];
                exact h_preconnected.isPreconnected;
              convert h_preconnected.image ( fun x => x + 1 ) ( Continuous.continuousOn ( by continuity ) ) using 1 ; ext ; simp +decide [ Set.ext_iff ];
            · norm_num;
            · filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) ( show 1 < ( 2 : ℂ ).re by norm_num ) ] with s hs using sub_eq_zero.mpr ( h_eq s hs );
            · aesop;
          exact eq_of_sub_eq_zero <| h_identity s hs_ne_one;
        intro s; by_cases hs : s = 1 <;> simp_all +decide ;
        rw [ riemannZeta_one ] ; norm_num [ Complex.ext_iff ];
        norm_num [ Complex.normSq, Complex.div_re, Complex.div_im, Complex.log_re, Complex.log_im ] ; ring ; norm_num [ Real.pi_pos.le ] ;
        norm_num [ Complex.arg ] ; ring ; norm_num [ Real.pi_pos.le ] ;
      rw [ h_identity s, Complex.conj_conj ];
  exact h_neq <| h_conj s
/-- Conjugation symmetry for zeros. -/
lemma riemannZeta_zero_conj (ρ : ℂ) (hz : riemannZeta ρ = 0) :
    riemannZeta (starRingEnd ℂ ρ) = 0 := by
  rw [riemannZeta_conj, hz, map_zero]

/-
-/
lemma riemannZeta_zero_one_sub (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    riemannZeta (1 - ρ) = 0 := by
      convert riemannZeta_one_sub ( show ∀ ( n : ℕ ), ρ ≠ -n by ( intros n hn; ( norm_num [ Complex.ext_iff ] at hn; linarith ) ) ) ( show ρ ≠ 1 by ( intro hn; ( norm_num [ hn ] at hstrip ) ) ) using 1 ; aesop

/-- The full four-fold orbit: if ζ(ρ) = 0 in the critical strip, then all four
    points ρ, 1−ρ, conj ρ, 1−conj ρ are zeros. -/
theorem four_fold_zeros (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    riemannZeta ρ = 0 ∧
    riemannZeta (1 - ρ) = 0 ∧
    riemannZeta (starRingEnd ℂ ρ) = 0 ∧
    riemannZeta (1 - starRingEnd ℂ ρ) = 0 := by
  refine ⟨hz, riemannZeta_zero_one_sub ρ hz hstrip, riemannZeta_zero_conj ρ hz, ?_⟩
  apply riemannZeta_zero_one_sub
  · exact riemannZeta_zero_conj ρ hz
  · constructor <;> simp [hstrip.1, hstrip.2]
-- ============================================================================
-- § 6. Distinctness of the orbit for off-axis zeros
-- ============================================================================
/-- If Re(ρ) ≠ 1/2, then ρ ≠ 1 − ρ. -/
lemma offaxis_ne_reflection (ρ : ℂ) (hoff : ρ.re ≠ 1 / 2) :
    ρ ≠ 1 - ρ := by
  intro h
  apply hoff
  have := congr_arg re h
  simp only [sub_re, one_re] at this
  linarith
/-- If Re(ρ) ≠ 1/2, then Re(ρ) ≠ Re(1−ρ). -/
lemma offaxis_re_ne_reflection (ρ : ℂ) (hoff : ρ.re ≠ 1 / 2) :
    ρ.re ≠ (1 - ρ).re := by
  simp only [sub_re, one_re]
  intro h
  apply hoff
  linarith
-- ============================================================================
-- § 7. Harmonic amplitude asymmetry  (bridge to prime distribution)
-- ============================================================================
/-- For x > 1 and Re(ρ) ≠ 1/2, the harmonic amplitudes x^(Re ρ) and x^(Re(1−ρ))
    are distinct.  In the explicit formula, this means the zero pair {ρ, 1−ρ}
    contributes terms of unequal magnitude to the prime-counting function —
    a measurable, nonzero distortion of the prime distribution. -/
theorem harmonic_amplitude_asymmetry (ρ : ℂ) (x : ℝ)
    (hx : 1 < x)
    (hoff : ρ.re ≠ 1 / 2) :
    harmonicAmplitude x ρ ≠ harmonicAmplitude x (1 - ρ) := by
  unfold harmonicAmplitude
  simp only [sub_re, one_re]
  intro h
  apply hoff
  have := (rpow_right_inj (by linarith : (0 : ℝ) < x) (by linarith : x ≠ 1)).mp h
  linarith
-- ============================================================================
-- § 8. Main theorem
-- ============================================================================
/-- **Main Theorem.**  An off-axis zero of the Riemann zeta function in the
    critical strip forces a detectable anti-symmetry event on a
    symmetry-compatible observable.
    *Witness observable:*  `criticalDisplacement s = Re(s) − 1/2`.
    *Proof sketch:*
    1. `criticalDisplacement` is conjugation-invariant (Re(conj s) = Re s)
       and vanishes on the critical line, so it is symmetry-compatible.
    2. For any ρ with Re ρ ≠ 1/2:
       • `criticalDisplacement ρ = Re ρ − 1/2 ≠ 0`  (off-axis ⟹ nonzero),
       • `criticalDisplacement (1 − ρ) = 1/2 − Re ρ = −criticalDisplacement ρ`
         (anti-symmetric under the functional-equation reflection).
    3. Hence `(criticalDisplacement, ρ)` is an anti-symmetry event.
    The hypotheses `hz` and `hstrip` are not needed for the observable algebra
    but are carried for semantic completeness: they guarantee that ρ and its
    orbit partners are genuine zeta zeros, so the anti-symmetry event has
    number-theoretic meaning (cf. `four_fold_zeros`, `harmonic_amplitude_asymmetry`). -/
theorem offaxis_zero_forces_observable_antisymmetry
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (_hstrip : 0 < ρ.re ∧ ρ.re < 1)
    (hoff : ρ.re ≠ 1 / 2) :
    ∃ O : ℂ → ℝ,
      SymmetryCompatibleObservable O ∧
      ObservableAntiSymmetryEvent O ρ :=
  ⟨criticalDisplacement,
   criticalDisplacement_is_symmetry_compatible,
   criticalDisplacement_antisymmetry_event ρ hoff⟩
-- ============================================================================
-- § 9. Strengthened version: harmonic detector
-- ============================================================================
/-- The harmonic detector at scale x measures the amplitude gap
    x^(Re s) − x^(Re(1−s)) between a zero and its functional-equation partner.
    It is zero iff both have the same real part, i.e. iff Re s = 1/2. -/
def harmonicDetector (x : ℝ) (s : ℂ) : ℝ :=
  harmonicAmplitude x s - harmonicAmplitude x (1 - s)
/-- The harmonic detector fires (is nonzero) at every off-axis point,
    for every scale x > 1.  This is the quantitative "prime-side observable"
    that an off-axis zeta zero would disturb. -/
theorem harmonicDetector_fires_offaxis (ρ : ℂ) (x : ℝ)
    (hx : 1 < x)
    (hoff : ρ.re ≠ 1 / 2) :
    harmonicDetector x ρ ≠ 0 := by
  unfold harmonicDetector
  rw [sub_ne_zero]
  unfold harmonicAmplitude
  simp only [sub_re, one_re]
  intro h
  apply hoff
  have := (rpow_right_inj (by linarith : (0 : ℝ) < x) (by linarith : x ≠ 1)).mp h
  linarith
-- ============================================================================
-- § 10. Axiom audit
-- ============================================================================
#check @offaxis_zero_forces_observable_antisymmetry
#print axioms offaxis_zero_forces_observable_antisymmetry
#print axioms four_fold_zeros
#print axioms harmonic_amplitude_asymmetry
#print axioms harmonicDetector_fires_offaxis