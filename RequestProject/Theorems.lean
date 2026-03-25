/-
  Implication chain: off-axis native zero → off-axis classical zero
  → π/6 reflection failure → rotated symmetry failure → only on-axis zeros pass both tests.
  All theorems are unconditional. No use of RH or functional equation.
-/
import Mathlib
import RequestProject.TheoremsDefs
open Complex
noncomputable section

/-! ## Structural lemmas about the transport map -/
/-
PROBLEM
Core intertwining: T commutes with the two reflections.
    T(piDivSixReflect(s)) = classicalReflect(T(s)).
PROVIDED SOLUTION
Unfold T, piDivSixReflect, classicalReflect. Both sides are Complex.mk with re = (2*theta - s.re)/(2*theta) and im = s.im. The re component: LHS = (2*theta - s.re)/(2*theta), RHS = 1 - s.re/(2*theta) = (2*theta - s.re)/(2*theta). Use Complex.ext, simp with the @[simp] lemmas, then field_simp and ring.
-/


theorem transport_intertwines_reflections (s : ℂ) :
    T (piDivSixReflect s) = classicalReflect (T s) := by
  unfold piDivSixReflect T classicalReflect ; ring;
  norm_num [ theta_ne_zero ]
/-
PROBLEM
T maps the native axis Re = θ to the classical line Re = 1/2.
PROVIDED SOLUTION
Unfold OnNativeAxis and OnClassicalAxis. s.re = theta ↔ s.re/(2*theta) = 1/2. Use constructor, intro, field_simp at *, linarith or similar. Key fact: theta ≠ 0 from theta_ne_zero.
-/
theorem transport_onaxis_iff (s : ℂ) :
    OnNativeAxis s ↔ OnClassicalAxis (T s) := by
  unfold OnNativeAxis OnClassicalAxis T; norm_num [ theta_eq ] ; ring_nf ; norm_num [ theta_ne_zero, theta_pos ] ;
  constructor <;> intro h <;> nlinarith [ Real.pi_pos, mul_inv_cancel₀ Real.pi_ne_zero ] ;
/-
PROBLEM
T maps off-native-axis to off-classical-axis.
PROVIDED SOLUTION
This is the negation of transport_onaxis_iff. Use simp [OffNativeAxis, OffClassicalAxis, ← transport_onaxis_iff].
-/
theorem transport_offaxis_iff (s : ℂ) :
    OffNativeAxis s ↔ OffClassicalAxis (T s) := by
  simp +decide [ OffNativeAxis, OffClassicalAxis, transport_onaxis_iff ];
  field_simp [theta_ne_zero]
/-
PROBLEM
T preserves the imaginary part.
PROVIDED SOLUTION
By definition, (T s).im = s.im. Just rfl or simp [T].
-/
theorem transport_preserves_im (s : ℂ) : (T s).im = s.im := by
  rfl
/-! ## Step 0: NativeZero is equivalent to ζ(T(s)) = 0 -/
/-
PROBLEM
Bridge lemma: a native zero is exactly a zero of ζ at the transported point.
PROVIDED SOLUTION
Unfold NativeZero and RobespierreZetaO. Both sides are riemannZeta (T s) = 0. It's Iff.rfl.
-/
theorem native_zero_iff_zeta_zero (s : ℂ) :
    NativeZero s ↔ riemannZeta (T s) = 0 := by
  rfl
/-! ## Step 1: Off-axis native zero gives off-axis classical zero -/
/-
PROBLEM
Step 1: An off-axis native zero transports to an off-axis classical ζ-zero.
    This is unconditional and uses only the definition of T.
PROVIDED SOLUTION
Use w = T s. Then riemannZeta w = 0 from native_zero_iff_zeta_zero. w = T s by rfl. w.re ≠ 1/2 from transport_offaxis_iff (since hoff : s.re ≠ theta means OffNativeAxis s, hence OffClassicalAxis (T s)). w.im = s.im from transport_preserves_im. Use exact ⟨T s, ..., rfl, ..., ...⟩.
-/
theorem offaxis_native_zero_gives_offaxis_classical_zero
    (s : ℂ)
    (hz : NativeZero s)
    (hoff : s.re ≠ theta) :
    ∃ w : ℂ,
      riemannZeta w = 0 ∧
      w = T s ∧
      w.re ≠ (1 / 2 : ℝ) ∧
      w.im = s.im := by
  grind +suggestions
/-! ## Step 2: Off-axis native zero forces π/6 reflection-test failure -/
/-
PROBLEM
Step 2: An off-axis native zero cannot pass the π/6 reflection test,
    i.e., it does not lie on the native axis.
PROVIDED SOLUTION
PassesPiDivSixReflectionTest s = OnNativeAxis s = (s.re = theta). We have hoff : s.re ≠ theta. So ¬PassesPiDivSixReflectionTest s follows directly. Unfold PassesPiDivSixReflectionTest, OnNativeAxis, exact hoff.
-/
theorem offaxis_native_zero_forces_pi_div_six_reflection_failure
    (s : ℂ)
    (hz : NativeZero s)
    (hoff : s.re ≠ theta) :
    ¬ PassesPiDivSixReflectionTest s := by
  exact hoff
/-! ## Step 3: Off-axis classical zero forces rotated critical-strip symmetry failure -/
/-
PROBLEM
Step 3: An off-axis ζ-zero cannot pass the classical critical-line test.
PROVIDED SOLUTION
PassesClassicalCriticalLineTest w = OnClassicalAxis w = (w.re = 1/2). We have hoff : w.re ≠ 1/2. So ¬PassesClassicalCriticalLineTest w follows directly. Unfold PassesClassicalCriticalLineTest, OnClassicalAxis, exact hoff.
-/
theorem offaxis_classical_zero_forces_rotated_symmetry_failure
    (w : ℂ)
    (hz : riemannZeta w = 0)
    (hoff : w.re ≠ (1 / 2 : ℝ)) :
    ¬ PassesClassicalCriticalLineTest w := by
  exact hoff
/-! ## Intertwining consequence: reflected native pairs map to reflected classical pairs -/
/-
PROBLEM
If both s and piDivSixReflect(s) are native zeros,
    then T(s) and classicalReflect(T(s)) are both ζ-zeros.
PROVIDED SOLUTION
hp gives NativeZero s and NativeZero (piDivSixReflect s). By native_zero_iff_zeta_zero, riemannZeta (T s) = 0 and riemannZeta (T (piDivSixReflect s)) = 0. By transport_intertwines_reflections, T (piDivSixReflect s) = classicalReflect (T s). Rewrite to get riemannZeta (classicalReflect (T s)) = 0. So ReflectedClassicalZeroPair (T s) holds.
-/
theorem reflected_native_pair_gives_reflected_classical_pair
    (s : ℂ)
    (hp : ReflectedNativeZeroPair s) :
    ReflectedClassicalZeroPair (T s) := by
  exact ⟨ native_zero_iff_zeta_zero s |>.1 hp.1, native_zero_iff_zeta_zero ( piDivSixReflect s ) |>.1 hp.2 ▸ transport_intertwines_reflections s ▸ rfl ⟩
/-! ## Step 4: Only on-axis zeros pass both tests -/
/-
PROBLEM
Step 4 (zero-level corollary): If a native zero passes both the π/6 reflection
    test AND its transport passes the classical critical-line test, then it lies
    on the native axis (equivalently, its transport lies on the critical line).
PROVIDED SOLUTION
hpass : TwoPlaneTestPasses s = PassesPiDivSixReflectionTest s ∧ PassesClassicalCriticalLineTest (T s). The first component is OnNativeAxis s, the second is OnClassicalAxis (T s). Extract both from hpass.
-/
theorem passes_both_tests_implies_on_axis
    (s : ℂ)
    (hz : NativeZero s)
    (hpass : TwoPlaneTestPasses s) :
    OnNativeAxis s ∧ OnClassicalAxis (T s) := by
  finiteness
/-
PROBLEM
The two-plane test is equivalent to being on the native axis.
PROVIDED SOLUTION
TwoPlaneTestPasses s ↔ OnNativeAxis s ∧ OnClassicalAxis (T s). By transport_onaxis_iff, these two conditions are equivalent. So TwoPlaneTestPasses s ↔ OnNativeAxis s. Use constructor: forward direction takes the first component, backward direction uses transport_onaxis_iff to get the second.
-/
theorem two_plane_test_iff_on_native_axis (s : ℂ) :
    TwoPlaneTestPasses s ↔ OnNativeAxis s := by
  exact ⟨ fun h => h.1, fun h => ⟨ h, transport_onaxis_iff s |>.1 h ⟩ ⟩
/-
PROBLEM
Contrapositive of Step 4: any off-axis native zero fails at least one test.
PROVIDED SOLUTION
By two_plane_test_iff_on_native_axis, TwoPlaneTestPasses s ↔ OnNativeAxis s. OffNativeAxis s means ¬OnNativeAxis s. So ¬TwoPlaneTestPasses s.
-/
theorem offaxis_native_zero_fails_two_plane_test
    (s : ℂ)
    (hz : NativeZero s)
    (hoff : OffNativeAxis s) :
    ¬ TwoPlaneTestPasses s := by
  -- By the equivalence between TwoPlaneTestPasses and OnNativeAxis, we have ¬TwoPlaneTestPasses s ↔ ¬OnNativeAxis s.
  apply two_plane_test_iff_on_native_axis s |>.not.mpr hoff
/-! ## Combined chain -/
/-
PROBLEM
The full implication chain: an off-axis native zero simultaneously
    (1) produces an off-critical-line ζ-zero,
    (2) fails the π/6 reflection test,
    (3) fails the classical critical-line test,
    and therefore fails the two-plane test.
PROVIDED SOLUTION
Combine the previous results. (1) From offaxis_native_zero_gives_offaxis_classical_zero, get the ζ-zero w with w.re ≠ 1/2. (2) From offaxis_native_zero_forces_pi_div_six_reflection_failure. (3) From offaxis_classical_zero_forces_rotated_symmetry_failure applied to T s. (4) From offaxis_native_zero_fails_two_plane_test. Use exact ⟨..., ..., ..., ...⟩ combining all four.
-/
theorem offaxis_native_zero_full_chain
    (s : ℂ)
    (hz : NativeZero s)
    (hoff : s.re ≠ theta) :
    (∃ w : ℂ, riemannZeta w = 0 ∧ w.re ≠ (1 / 2 : ℝ)) ∧
    ¬ PassesPiDivSixReflectionTest s ∧
    ¬ PassesClassicalCriticalLineTest (T s) ∧
    ¬ TwoPlaneTestPasses s := by
  refine' ⟨ _, _, _, _ ⟩;
  · obtain ⟨ w, hw ⟩ := offaxis_native_zero_gives_offaxis_classical_zero s hz hoff;
    exact ⟨ w, hw.1, hw.2.2.1 ⟩;
  · grind +suggestions;
  · convert transport_offaxis_iff s |>.1 hoff using 1;
  · exact offaxis_native_zero_fails_two_plane_test s hz hoff
end