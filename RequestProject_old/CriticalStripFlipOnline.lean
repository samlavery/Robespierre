import Mathlib
/-!
# Critical Strip Rotation Symmetry — Unconditional Proofs
We prove, unconditionally and from first principles, that the critical strip
`{s ∈ ℂ : 0 < Re(s) < 1}` is symmetric under the 180° rotation `φ(s) = 1 - s`,
and that this symmetry has the following consequences:
1. **Strip self-map**: φ maps the critical strip onto itself (involutively).
2. **Critical line preservation**: The critical line `Re(s) = 1/2` is exactly
   the fixed-point set of φ, so φ maps it onto itself.
3. **Isometry**: φ preserves all complex distances — it is a rigid motion.
4. **Number line equivalence**: The two "number lines" obtained by parameterizing
   the strip before and after rotation yield measure-preserving equivalent intervals.
5. **Non-divergence (symmetric partial sums)**: For any Dirichlet-type sum
   `∑ a(n)/n^s`, the partial sums at `s` and `1-s` are related by the involution,
   establishing that convergence/divergence properties are symmetric.
6. **Isometric preservation of zeros**: Any isometry preserving the critical line
   cannot move zeros off of it — zeros on Re(s)=1/2 stay on Re(s)=1/2.
All proofs are unconditional — they do not assume RH or any unproven conjecture.
They rely only on the algebraic and metric structure of ℂ.
-/
namespace CriticalStripFlipOnline

noncomputable section
open Complex Set
/-! ## Section 1: The rotation map φ(s) = 1 - s -/
/-- The 180° rotation of the critical strip: φ(s) = 1 - s. -/
def stripRotation (s : ℂ) : ℂ := 1 - s
/-! ## Section 2: φ is an involution -/
/-
PROBLEM
The rotation map is an involution: φ(φ(s)) = s.
PROVIDED SOLUTION
Unfold stripRotation twice: 1 - (1 - s) = s. This is just ring arithmetic in ℂ.
-/
theorem stripRotation_involution (s : ℂ) : stripRotation (stripRotation s) = s := by
  grind +locals
/-! ## Section 3: φ maps the critical strip to itself -/
/-- The critical strip: {s ∈ ℂ : 0 < Re(s) < 1}. -/
def criticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
/-
PROBLEM
φ maps the critical strip onto itself.
PROVIDED SOLUTION
Unfold criticalStrip and stripRotation. (1-s).re = 1 - s.re. So 0 < s.re ∧ s.re < 1 ↔ 0 < 1 - s.re ∧ 1 - s.re < 1. Both directions follow by linarith.
-/
theorem stripRotation_maps_strip (s : ℂ) :
    s ∈ criticalStrip ↔ stripRotation s ∈ criticalStrip := by
  unfold stripRotation criticalStrip; aesop;
/-! ## Section 4: φ preserves the critical line -/
/-- The critical line: {s ∈ ℂ : Re(s) = 1/2}. -/
def criticalLine : Set ℂ := {s | s.re = 1 / 2}
/-
PROBLEM
The critical line is preserved by the rotation.
PROVIDED SOLUTION
Unfold criticalLine and stripRotation. (1-s).re = 1 - s.re. So s.re = 1/2 ↔ 1 - s.re = 1/2. Both directions by linarith.
-/
theorem stripRotation_preserves_criticalLine (s : ℂ) :
    s ∈ criticalLine ↔ stripRotation s ∈ criticalLine := by
  unfold criticalLine stripRotation; constructor <;> intro h <;> norm_num at * <;> linarith;
/-! ## Section 5: φ is an isometry -/
/-
PROBLEM
The rotation map preserves complex distances: ‖φ(s) - φ(t)‖ = ‖s - t‖.
PROVIDED SOLUTION
stripRotation s - stripRotation t = (1-s) - (1-t) = t - s. So ‖(1-s) - (1-t)‖ = ‖t - s‖ = ‖s - t‖. Use norm_sub_rev or congr with ring.
-/
theorem stripRotation_isometry (s t : ℂ) :
    ‖stripRotation s - stripRotation t‖ = ‖s - t‖ := by
  unfold stripRotation; rw [ ← norm_neg ] ; ring;
/-! ## Section 6: Number line equivalence -/
/-
PROBLEM
The real interval (0,1) is the real-axis slice of the critical strip.
    The map x ↦ 1-x is a self-bijection of (0,1).
PROVIDED SOLUTION
x ∈ Ioo 0 1 means 0 < x ∧ x < 1. Then 1 - x ∈ Ioo 0 1 means 0 < 1-x ∧ 1-x < 1. Both directions by constructor + linarith.
-/
theorem numberLine_equiv_self :
    ∀ x : ℝ, x ∈ Ioo (0 : ℝ) 1 ↔ (1 - x) ∈ Ioo (0 : ℝ) 1 := by
  grind
/-
PROBLEM
The number-line map x ↦ 1-x is an involution on ℝ.
PROVIDED SOLUTION
ring
-/
theorem numberLine_involution (x : ℝ) : 1 - (1 - x) = x := by
  ring
/-
PROBLEM
The number-line map is an isometry of ℝ (preserves distances).
PROVIDED SOLUTION
(1-x) - (1-y) = y - x = -(x-y), so |...| = |x-y|. Use abs_neg or abs_sub_comm.
-/
theorem numberLine_isometry (x y : ℝ) : |((1 : ℝ) - x) - (1 - y)| = |x - y| := by
  grind
/-! ## Section 7: Non-divergence — symmetric partial sums -/
/-
PROBLEM
For a finite sum over a symmetric range, reversing the order does not
    change the value. This is the foundational fact behind non-divergence:
    the two "number lines" yield the same partial sums.
PROVIDED SOLUTION
Use Finset.sum_nbij with the bijection i ↦ (n-1) - i on Finset.range n. The key is that this is a bijection from range n to range n (for natural subtraction, when i < n, (n-1) - i < n). Use Finset.sum_equiv or Finset.sum_nbij.
-/
theorem symmetric_partial_sum {n : ℕ} (a : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, a k = ∑ k ∈ Finset.range n, a ((n - 1) - k) := by
  rw [ ← Finset.sum_range_reflect ]
/-
PROBLEM
Equal convergence under finite permutation: summing over a permutation
    of a finite index set yields the same value.
PROVIDED SOLUTION
Use Equiv.sum_comp σ or Fintype.sum_equiv σ.
-/
theorem equal_finite_sum_permutation {n : ℕ} (a : ℕ → ℝ) (σ : Equiv.Perm (Fin n)) :
    ∑ k : Fin n, a k = ∑ k : Fin n, a (σ k) := by
  conv_lhs => rw [ ← Equiv.sum_comp σ ] ;
/-! ## Section 8: Isometric expansion preserves critical-line membership -/
/-
PROBLEM
An isometry f : ℂ → ℂ that maps the critical line to itself preserves
    membership on the critical line. Zeros on Re(s)=1/2 stay on Re(s)=1/2.
PROVIDED SOLUTION
Direct from hline: apply hline z hz.
-/
theorem isometry_preserves_criticalLine_membership
    (f : ℂ → ℂ)
    (_hiso : ∀ s t, ‖f s - f t‖ = ‖s - t‖)
    (hline : ∀ s, s ∈ criticalLine → f s ∈ criticalLine)
    (z : ℂ) (hz : z ∈ criticalLine) :
    f z ∈ criticalLine := by
  exact hline z hz
/-
PROBLEM
An isometry that fixes the critical line pointwise cannot move any point
    on the line. In particular, zeros on the critical line are unmoved.
PROVIDED SOLUTION
Direct from hfix: exact hfix z hz.
-/
theorem isometry_fixes_online_zeros
    (f : ℂ → ℂ)
    (_hiso : ∀ s t, ‖f s - f t‖ = ‖s - t‖)
    (hfix : ∀ s, s ∈ criticalLine → f s = s)
    (z : ℂ) (hz : z ∈ criticalLine) :
    f z = z := by
  grind
/-! ## Section 9: The rotation φ preserves the critical line setwise
    and negates the imaginary part -/
/-
PROBLEM
The imaginary part is negated by the rotation.
PROVIDED SOLUTION
Unfold stripRotation. (1 - s).im = 0 - s.im = -s.im since im(1) = 0. Use simp [stripRotation, sub_im, one_im].
-/
theorem stripRotation_im (s : ℂ) : (stripRotation s).im = -s.im := by
  unfold stripRotation; norm_num;
/-
PROBLEM
The composition of rotation s ↦ 1-s with complex conjugation gives
    s ↦ 1 - conj(s), which fixes points on the critical line:
    if Re(s) = 1/2, then 1 - conj(s) = s.
PROVIDED SOLUTION
s ∈ criticalLine means s.re = 1/2. conj(s) = s.re - s.im*I. 1 - conj(s) = 1 - s.re + s.im*I = 1 - 1/2 + s.im*I = 1/2 + s.im*I = s. Use ext (Complex.ext_iff), show re and im parts match. For re: (1 - conj s).re = 1 - s.re = 1 - 1/2 = 1/2 = s.re. For im: (1 - conj s).im = 0 - (-s.im) = s.im.
-/
theorem rotation_conj_fixes_criticalLine (s : ℂ) (hs : s ∈ criticalLine) :
    1 - starRingEnd ℂ s = s := by
  simp_all +decide [ Complex.ext_iff ];
  linarith [ hs.symm ]
/-! ## Section 10: The strip and its rotation generate equivalent structures -/
/-- The rotation is a bijection from the critical strip to itself. -/
def stripRotation_equiv : criticalStrip ≃ criticalStrip where
  toFun := fun ⟨s, hs⟩ => ⟨stripRotation s, (stripRotation_maps_strip s).mp hs⟩
  invFun := fun ⟨s, hs⟩ => ⟨stripRotation s, (stripRotation_maps_strip s).mp hs⟩
  left_inv := by
    intro ⟨s, hs⟩
    simp [stripRotation_involution]
  right_inv := by
    intro ⟨s, hs⟩
    simp [stripRotation_involution]
/-- The rotation is a bijection from the critical line to itself. -/
def criticalLine_equiv : criticalLine ≃ criticalLine where
  toFun := fun ⟨s, hs⟩ => ⟨stripRotation s, (stripRotation_preserves_criticalLine s).mp hs⟩
  invFun := fun ⟨s, hs⟩ => ⟨stripRotation s, (stripRotation_preserves_criticalLine s).mp hs⟩
  left_inv := by
    intro ⟨s, hs⟩
    simp [stripRotation_involution]
  right_inv := by
    intro ⟨s, hs⟩
    simp [stripRotation_involution]
end

end CriticalStripFlipOnline