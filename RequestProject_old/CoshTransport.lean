/-
  CoshTransport.lean

  Proves the transport/intertwining theorem.
-/

import Mathlib

open Complex Function

noncomputable section

/-! ### 1. Cosh-domain operators -/

def coshReflection (s : ℂ) : ℂ := ⟨Real.pi / 3 - s.re, s.im⟩
def coshFolding (s : ℂ) : ℂ := starRingEnd ℂ s

/-! ### 2. ζ-domain operators -/

def zetaConj (w : ℂ) : ℂ := starRingEnd ℂ w
def zetaFuncEq (w : ℂ) : ℂ := 1 - w

/-! ### 3. The critical-line identity: conj w = 1 - w when Re w = 1/2 -/

theorem conj_eq_one_sub_on_critical_line (w : ℂ) (hw : w.re = 1 / 2) :
    zetaConj w = zetaFuncEq w := by
  apply Complex.ext
  · simp [zetaConj, zetaFuncEq, hw]; linarith
  · simp [zetaConj, zetaFuncEq]

/-! ### 4. Intertwiner structure -/

structure CoshZetaIntertwiner (Φ : ℂ → ℂ) : Prop where
  injective : Injective Φ
  equivar_R : ∀ s, Φ (coshReflection s) = zetaConj (Φ s)
  equivar_F : ∀ s, Φ (coshFolding s) = zetaFuncEq (Φ s)

/-! ### 5. Main theorem: R(s) = F(s) on the critical-line preimage -/

theorem intertwiner_forces_R_eq_F
    {Φ : ℂ → ℂ} (hΦ : CoshZetaIntertwiner Φ)
    (s : ℂ) (hs : (Φ s).re = 1 / 2) :
    coshReflection s = coshFolding s := by
  apply hΦ.injective
  rw [hΦ.equivar_R, conj_eq_one_sub_on_critical_line _ hs, ← hΦ.equivar_F]

/-! ### 6. Coordinate extraction: R(s) = F(s) forces s = π/6 -/

theorem R_eq_F_forces_coordinates (s : ℂ)
    (h : coshReflection s = coshFolding s) :
    s.re = Real.pi / 6 ∧ s.im = 0 := by
  have hre := congr_arg re h
  have him := congr_arg im h
  simp [coshReflection, coshFolding] at hre him
  constructor
  · linarith
  · linarith

/-! ### 7. The full transport theorem -/

theorem transport_to_critical_line
    {Φ : ℂ → ℂ} (hΦ : CoshZetaIntertwiner Φ)
    (s : ℂ) (hs : (Φ s).re = 1 / 2) :
    coshReflection s = s ∧ coshFolding s = s := by
  have hRF := intertwiner_forces_R_eq_F hΦ s hs
  obtain ⟨hx, hy⟩ := R_eq_F_forces_coordinates s hRF
  constructor
  · apply Complex.ext
    · simp [coshReflection, hx]; ring
    · simp [coshReflection]
  · apply Complex.ext
    · simp [coshFolding]
    · simp [coshFolding, hy]

theorem critical_line_preimage_is_singleton
    {Φ : ℂ → ℂ} (hΦ : CoshZetaIntertwiner Φ)
    (s : ℂ) (hs : (Φ s).re = 1 / 2) :
    s = ↑(Real.pi / 6 : ℝ) := by
  obtain ⟨hx, hy⟩ := R_eq_F_forces_coordinates s (intertwiner_forces_R_eq_F hΦ s hs)
  apply Complex.ext
  · simp [hx]
  · simp [hy]

theorem transport_to_critical_line_disjunction
    {Φ : ℂ → ℂ} (hΦ : CoshZetaIntertwiner Φ)
    (s : ℂ) (hs : (Φ s).re = 1 / 2) :
    coshReflection s = s ∨ coshFolding s = s := by
  exact Or.inl (transport_to_critical_line hΦ s hs).1

/-! ### 8. Euler product harmonics and spectral inheritance

The Euler product for ζ(s) is  ζ(s) = ∏_p (1 − p^{−s})^{−1}.
Taking the logarithm yields  log ζ(s) = −∑_p log(1 − p^{−s}) = ∑_p ∑_{k≥1} p^{−ks}/k,
a sum of "harmonics" of the form r^{−s} with r a positive real (prime power).

Each such harmonic satisfies  conj(r^{−s}) = r^{−conj(s)},
and on the critical line Re(s) = 1/2 we have conj(s) = 1 − s, so
  conj(r^{−s}) = r^{−(1−s)}.

This means the conjugation symmetry (`zetaConj`) and the functional-equation
symmetry (`zetaFuncEq`) coincide *at the level of individual harmonics*
when evaluated on the critical line.  We call this **spectral 1/2 inheritance**:
the harmonics inherit the intertwining property from the spectral axis Re = 1/2.
-/

/-- An Euler harmonic: the map s ↦ r^(−s) for a positive real base r. -/
def eulerHarmonic (r : ℝ) (s : ℂ) : ℂ := (↑r : ℂ) ^ (-s)

/-
Conjugation commutes with positive-real-base complex exponentiation:
    conj(r^s) = r^(conj s)  for  r > 0.
-/
theorem conj_cpow_ofReal (r : ℝ) (hr : 0 < r) (s : ℂ) :
    starRingEnd ℂ ((↑r : ℂ) ^ s) = (↑r : ℂ) ^ (starRingEnd ℂ s) := by
  rw [ Complex.cpow_def_of_ne_zero ( Complex.ofReal_ne_zero.mpr hr.ne' ), Complex.cpow_def_of_ne_zero ( Complex.ofReal_ne_zero.mpr hr.ne' ) ];
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
  norm_num [ Complex.arg_ofReal_of_nonneg hr.le ]

/-
The conjugate of an Euler harmonic equals the harmonic at the conjugate point:
    conj(r^(−s)) = r^(−conj s).
-/
theorem eulerHarmonic_conj (r : ℝ) (hr : 0 < r) (s : ℂ) :
    starRingEnd ℂ (eulerHarmonic r s) = eulerHarmonic r (starRingEnd ℂ s) := by
  unfold eulerHarmonic;
  simp [conj_cpow_ofReal _ hr, map_neg]

/-
**Spectral 1/2 inheritance.**  On the critical line Re(s) = 1/2,
    the conjugation of each Euler harmonic equals the harmonic at 1 − s:
      conj(r^(−s)) = r^(−(1−s)).
    Each term in log Euler's product individually inherits the intertwining
    of `zetaConj` with `zetaFuncEq` from the spectral axis.
-/
theorem spectral_half_inheritance (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : s.re = 1 / 2) :
    starRingEnd ℂ (eulerHarmonic r s) = eulerHarmonic r (1 - s) := by
  convert eulerHarmonic_conj r hr s using 1;
  congr ; norm_num [ Complex.ext_iff, hs ]

/-! ### 9. Spectral inheritance for Dirichlet sums

The intertwining extends by linearity to finite Dirichlet sums
  F(s) = ∑ aᵢ · rᵢ^(−s)
with real coefficients aᵢ and positive real bases rᵢ.
-/

/-- A finite Dirichlet sum with real coefficients and positive real bases. -/
def dirichletSum (coeffs : Fin n → ℝ) (bases : Fin n → ℝ) (s : ℂ) : ℂ :=
  ∑ i, (↑(coeffs i) : ℂ) * eulerHarmonic (bases i) s

/-
The spectral inheritance extends to finite Dirichlet sums:
    conj(F(s)) = F(1−s) on the critical line.
-/
theorem dirichletSum_spectral_inheritance
    (coeffs : Fin n → ℝ) (bases : Fin n → ℝ)
    (hbases : ∀ i, 0 < bases i)
    (s : ℂ) (hs : s.re = 1 / 2) :
    starRingEnd ℂ (dirichletSum coeffs bases s) = dirichletSum coeffs bases (1 - s) := by
  unfold dirichletSum;
  rw [ map_sum ];
  refine' Finset.sum_congr rfl fun i _ => _;
  -- Apply the spectral inheritance result to each term in the sum.
  have h_term : starRingEnd ℂ (eulerHarmonic (bases i) s) = eulerHarmonic (bases i) (1 - s) := by
    exact spectral_half_inheritance (bases i) (hbases i) s hs;
  convert congr_arg ( fun x : ℂ => coeffs i * x ) h_term using 1 ; norm_num [ eulerHarmonic ]

/-! ### 10. Euler harmonics intertwine `zetaConj` and `zetaFuncEq` -/

/-
On the critical line, applying `zetaConj` to an Euler harmonic is the
    same as evaluating the harmonic at `zetaFuncEq s`.  This says precisely
    that each harmonic from log Euler's product is an intertwiner between
    the two symmetries, inheriting the spectral 1/2 from its source.
-/
theorem euler_harmonic_intertwines_on_critical_line
    (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : s.re = 1 / 2) :
    zetaConj (eulerHarmonic r s) = eulerHarmonic r (zetaFuncEq s) := by
  convert spectral_half_inheritance r hr s hs using 1

/-
Intertwining for finite Dirichlet sums: `zetaConj(F(s)) = F(zetaFuncEq(s))`
    on the critical line.
-/
theorem dirichletSum_intertwines_on_critical_line
    (coeffs : Fin n → ℝ) (bases : Fin n → ℝ)
    (hbases : ∀ i, 0 < bases i)
    (s : ℂ) (hs : s.re = 1 / 2) :
    zetaConj (dirichletSum coeffs bases s) =
      dirichletSum coeffs bases (zetaFuncEq s) := by
  convert dirichletSum_spectral_inheritance coeffs bases hbases s hs using 1

end