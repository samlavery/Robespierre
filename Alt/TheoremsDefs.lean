/-
  Definitions for the Robespierre transport framework.
  Defines θ, the transport map T, RobespierreZetaO, NativeZero,
  reflection operations, and test predicates.
-/
import Mathlib
open Complex
noncomputable section
/-- θ = arcsin(1/2) = π/6. -/
def theta : ℝ := Real.arcsin (1 / 2)
/-- θ = π/6. -/
theorem theta_eq : theta = Real.pi / 6 := by
  unfold theta
  have h1 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  have h2 : -(Real.pi / 2) ≤ Real.pi / 6 := by linarith [Real.pi_pos]
  have h3 : Real.pi / 6 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [← h1, Real.arcsin_sin h2 h3]
/-- θ ≠ 0. -/
theorem theta_ne_zero : theta ≠ 0 := by
  rw [theta_eq]
  positivity
/-- θ > 0. -/
theorem theta_pos : 0 < theta := by
  rw [theta_eq]
  positivity
/-- The transport map T : ℂ → ℂ sending the native axis Re = θ
    to the classical critical line Re = 1/2.
    T(s) = ⟨s.re / (2 * θ), s.im⟩. -/
def T (s : ℂ) : ℂ := ⟨s.re / (2 * theta), s.im⟩
@[simp] theorem T_re (s : ℂ) : (T s).re = s.re / (2 * theta) := rfl
@[simp] theorem T_im (s : ℂ) : (T s).im = s.im := rfl
/-- RobespierreZetaO is the transported zeta: RobespierreZetaO(s) = ζ(T(s)). -/
def RobespierreZetaO (s : ℂ) : ℂ := riemannZeta (T s)
/-- A native zero is a point s where RobespierreZetaO(s) = 0,
    equivalently ζ(T(s)) = 0. -/
def NativeZero (s : ℂ) : Prop := RobespierreZetaO s = 0
/-- On the native axis: Re(s) = θ. -/
def OnNativeAxis (s : ℂ) : Prop := s.re = theta
/-- On the classical critical line: Re(w) = 1/2. -/
def OnClassicalAxis (w : ℂ) : Prop := w.re = (1 : ℝ) / 2
/-- The π/6 reflection: s ↦ ⟨2θ - Re(s), Im(s)⟩. -/
def piDivSixReflect (s : ℂ) : ℂ := ⟨2 * theta - s.re, s.im⟩
@[simp] theorem piDivSixReflect_re (s : ℂ) :
    (piDivSixReflect s).re = 2 * theta - s.re := rfl
@[simp] theorem piDivSixReflect_im (s : ℂ) :
    (piDivSixReflect s).im = s.im := rfl
/-- The classical reflection: w ↦ ⟨1 - Re(w), Im(w)⟩. -/
def classicalReflect (w : ℂ) : ℂ := ⟨1 - w.re, w.im⟩
@[simp] theorem classicalReflect_re (w : ℂ) :
    (classicalReflect w).re = 1 - w.re := rfl
@[simp] theorem classicalReflect_im (w : ℂ) :
    (classicalReflect w).im = w.im := rfl
/-- A zero passes the π/6 reflection test if it lies on the native axis. -/
def PassesPiDivSixReflectionTest (s : ℂ) : Prop := OnNativeAxis s
/-- A zero passes the classical critical-line test if it lies on Re = 1/2. -/
def PassesClassicalCriticalLineTest (w : ℂ) : Prop := OnClassicalAxis w
/-- The two-plane test: a native zero passes both the π/6 reflection test
    AND its transport passes the classical critical-line test. -/
def TwoPlaneTestPasses (s : ℂ) : Prop :=
  PassesPiDivSixReflectionTest s ∧ PassesClassicalCriticalLineTest (T s)
/-- A reflected native zero pair: both s and its π/6 reflection are native zeros. -/
def ReflectedNativeZeroPair (s : ℂ) : Prop :=
  NativeZero s ∧ NativeZero (piDivSixReflect s)
/-- A reflected classical zero pair: both w and its classical reflection are ζ-zeros. -/
def ReflectedClassicalZeroPair (w : ℂ) : Prop :=
  riemannZeta w = 0 ∧ riemannZeta (classicalReflect w) = 0
/-- Off-axis in native coordinates. -/
def OffNativeAxis (s : ℂ) : Prop := s.re ≠ theta
/-- Off-axis in classical coordinates. -/
def OffClassicalAxis (w : ℂ) : Prop := w.re ≠ (1 : ℝ) / 2
end