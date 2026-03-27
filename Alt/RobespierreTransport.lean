import Mathlib
open Complex
/-- The Robespierre transport function: maps s to riemannZeta at the transported point
    T(s) = (s.re / (2θ)) + s.im * I, where θ = arcsin(1/2). -/


noncomputable def RobespierreZetaO (θ : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (↑(s.re / (2 * θ)) + ↑s.im * I)

/-- An off-axis zero of RobespierreZetaO gives an off-axis classical zeta zero
    at the transported point. This is purely algebraic transport — no RH or
    functional equation is used. -/

theorem offaxis_robespierre_zero_gives_offaxis_classical_zero
  (θ : ℝ) (hθ : θ = Real.arcsin (1/2))
  (s : ℂ)
  (hz : RobespierreZetaO θ s = 0)
  (hoff : s.re ≠ θ) :
  ∃ w : ℂ,
    riemannZeta w = 0 ∧
    w = ↑(s.re / (2 * θ)) + ↑s.im * I ∧
    w.re ≠ (1 / 2 : ℝ) ∧
    w.im = s.im := by
  refine ⟨↑(s.re / (2 * θ)) + ↑s.im * I, ?_, rfl, ?_, ?_⟩
  · -- riemannZeta w = 0 from hz
    exact hz
  · -- w.re ≠ 1/2
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
    ring_nf
    intro h
    apply hoff
    subst hθ
    have hθ_pos : (0 : ℝ) < Real.arcsin (1/2) := Real.arcsin_pos.mpr (by norm_num)
    have hθ_ne : Real.arcsin (1/2) ≠ 0 := ne_of_gt hθ_pos
    field_simp at h
    linarith
  · -- w.im = s.im
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
    ring