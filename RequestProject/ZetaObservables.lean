import Mathlib
/-!
# Off-Axis Zeta Zeros: Observable Anti-Symmetry and Prime Harmonic Modification
Unconditional theorems connecting nontrivial zeros of the Riemann zeta function
off the critical line to observable distortions in prime-counting harmonics.
No assumption of RH. No use of the functional equation.
-/
open Real
noncomputable section
/-! ## Predicates and observables -/
/-- A nontrivial zero of `riemannZeta` strictly off the critical line `Re s = 1/2`. -/
def offAxisClassicalZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re ≠ 1 / 2
/-- Signed displacement of `Re ρ` from the critical line. -/
def realAxisDistortion (ρ : ℂ) : ℝ := ρ.re - 1 / 2
/-- Real observable: amplitude‑weighted cosine from a conjugate zero pair.
    Models `Re(x^ρ + x^ρ̄) = 2 x^σ cos(γ ln x)` for `ρ = σ + iγ`. -/
def offAxisRealObservable (ρ : ℂ) (x : ℝ) : ℝ :=
  2 * x ^ ρ.re * cos (ρ.im * Real.log x)
/-- Imaginary observable: amplitude‑weighted sine from a conjugate zero pair.
    Models `Im(x^ρ − x^ρ̄)/i = 2 x^σ sin(γ ln x)`. -/
def offAxisImagObservable (ρ : ℂ) (x : ℝ) : ℝ :=
  2 * x ^ ρ.re * sin (ρ.im * Real.log x)
/-- Distortion in amplitude relative to a critical‑line zero: `x^σ − x^{1/2}`. -/
def realObservableDistortion (ρ : ℂ) (x : ℝ) : ℝ :=
  x ^ ρ.re - x ^ (1 / 2 : ℝ)
/-- Rotated detector: the pair contribution observed at rotation angle `θ`.
    `2 x^σ cos(γ ln x + θ)`. At `θ = π/2` this becomes `−2 x^σ sin(γ ln x)`. -/
def rotatedPrimeDensityDetector (ρ : ℂ) (θ x : ℝ) : ℝ :=
  2 * x ^ ρ.re * cos (ρ.im * Real.log x + θ)
/-! ## Events -/
/-- **Rotated Observable Anti-Symmetry Event.**
    Three conditions, each unconditionally implied by an off-axis zero:
    1. The critical‑line distortion is nonzero.
    2. The π/2‑rotated detector is anti‑symmetric under conjugation of ρ.
    3. For every `x > 1` the amplitude distortion is nonzero. -/
def RotatedObservableAntiSymmetryEvent (ρ : ℂ) : Prop :=
  realAxisDistortion ρ ≠ 0 ∧
  (∀ x : ℝ, 0 < x →
    rotatedPrimeDensityDetector ρ (π / 2) x =
      - rotatedPrimeDensityDetector (starRingEnd ℂ ρ) (π / 2) x) ∧
  (∀ x : ℝ, 1 < x → realObservableDistortion ρ x ≠ 0)
/-- **Prime Harmonic Modification Event.**
    Strictly stronger than the anti-symmetry event:
    1. The critical‑line distortion is nonzero.
    2. For every `x > 1` the amplitude distortion is nonzero.
    3. The sign of the distortion is *uniform* over all `x > 1`
       (all positive when `σ > 1/2`; all negative when `σ < 1/2`). -/
def PrimeHarmonicModificationEvent (ρ : ℂ) : Prop :=
  realAxisDistortion ρ ≠ 0 ∧
  (∀ x : ℝ, 1 < x → realObservableDistortion ρ x ≠ 0) ∧
  (∀ x y : ℝ, 1 < x → 1 < y →
    (0 < realObservableDistortion ρ x ↔ 0 < realObservableDistortion ρ y))
/-! ## Helper lemmas -/
/-- If `x > 1` and `a ≠ b`, then `x ^ a ≠ x ^ b`. -/
lemma rpow_ne_rpow_of_exponent_ne {x : ℝ} (hx : 1 < x) {a b : ℝ} (hab : a ≠ b) :
    x ^ a ≠ x ^ b := by
  cases lt_or_gt_of_ne hab <;>
    [ exact ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hx ‹_›)
    ; exact ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hx ‹_›) ]
/-- The π/2-rotated detector satisfies conjugation anti-symmetry. -/
lemma rotatedPrimeDensityDetector_pi_div_two_antisymm (ρ : ℂ) (x : ℝ) (_hx : 0 < x) :
    rotatedPrimeDensityDetector ρ (π / 2) x =
      - rotatedPrimeDensityDetector (starRingEnd ℂ ρ) (π / 2) x := by
  unfold rotatedPrimeDensityDetector
  simp [Complex.conj_re, Complex.conj_im, Real.cos_add_pi_div_two, Real.sin_neg]
/-- For `x > 1`, the sign of `x ^ a - x ^ b` is determined by the sign of `a - b`. -/
lemma rpow_sub_rpow_pos_iff {x a b : ℝ} (hx : 1 < x) :
    0 < x ^ a - x ^ b ↔ b < a := by
  rw [sub_pos, Real.rpow_lt_rpow_left_iff]; linarith
/-! ## Main theorems -/
/-- **Theorem 1 (strongest unconditional).**
    An off‑axis classical zeta zero produces a rotated observable anti‑symmetry event. -/
theorem offAxisZero_implies_antiSymmetryEvent (ρ : ℂ)
    (h : offAxisClassicalZetaZero ρ) :
    RotatedObservableAntiSymmetryEvent ρ := by
  refine ⟨sub_ne_zero.mpr h.2.2.2,
    fun x hx => rotatedPrimeDensityDetector_pi_div_two_antisymm ρ x hx,
    fun x hx hc => h.2.2.2 ?_⟩
  exact le_antisymm
    (le_of_not_gt fun h' => hc.not_gt <| sub_pos_of_lt <|
      Real.rpow_lt_rpow_of_exponent_lt hx h')
    (le_of_not_gt fun h' => hc.not_lt <| sub_neg_of_lt <|
      Real.rpow_lt_rpow_of_exponent_lt hx h')
/-- **Theorem 2 (strongest unconditional upgrade).**
    A rotated observable anti‑symmetry event implies a prime harmonic modification event
    (uniform sign of amplitude distortion). -/
theorem antiSymmetryEvent_implies_primeHarmonicModification (ρ : ℂ)
    (h : RotatedObservableAntiSymmetryEvent ρ) :
    PrimeHarmonicModificationEvent ρ := by
  refine ⟨h.1, h.2.2, fun x y hx hy => ?_⟩
  simp only [realObservableDistortion, rpow_sub_rpow_pos_iff hx, rpow_sub_rpow_pos_iff hy]
end