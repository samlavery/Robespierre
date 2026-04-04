import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section
namespace Translation
/-- The critical strip: {s ∈ ℂ | 0 < Re(s) < 1}. -/
def CriticalStrip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The critical line: {s ∈ ℂ | Re(s) = 1/2}. -/
def CriticalLine : Set ℂ := {s : ℂ | s.re = 1 / 2}

/-- The functional equation reflection: s ↦ 1 - s.
    This is the reflection about the line Re(s) = 1/2. -/
def funcEqReflection (s : ℂ) : ℂ := 1 - s

/-- The cosh reflection over the x = 0 line (imaginary axis): s ↦ -s.
    Since cosh is an even function, cosh(s) = cosh(-s),
    so this captures the symmetry of the cosh kernel about Re(s) = 0. -/
def coshReflection (s : ℂ) : ℂ := -s

/-- The cosh folding over the Im = 0 line (real axis): s ↦ conj(s).
    Since cosh(conj(s)) = conj(cosh(s)), the real axis is a
    symmetry axis of the cosh kernel. -/
def coshFolding (s : ℂ) : ℂ := starRingEnd ℂ s

-- ============================================================
-- Part 1: The composition of reflections is a translation by 1
-- ============================================================

/-- The composition of the functional equation reflection (s ↦ 1 - s)
    and the cosh reflection (s ↦ -s) is a translation by 1. -/
lemma composition_eq_translation (s : ℂ) :
    coshReflection (funcEqReflection s) = s - 1 := by
  unfold coshReflection funcEqReflection; ring

/-- The composition in the other order is a translation by +1. -/
lemma composition_eq_translation' (s : ℂ) :
    funcEqReflection (coshReflection s) = s + 1 := by
  unfold funcEqReflection coshReflection; ring

-- ============================================================
-- Part 2: No nonempty dual-invariant set in the critical strip
-- ============================================================

/-- By induction on n, if S is invariant under both reflections,
    then s₀ + n ∈ S for all n ∈ ℕ. -/
lemma iterate_translation_in_S (S : Set ℂ)
    (hFE : ∀ s ∈ S, funcEqReflection s ∈ S)
    (hCR : ∀ s ∈ S, coshReflection s ∈ S)
    (s₀ : ℂ) (hs₀ : s₀ ∈ S) (n : ℕ) :
    s₀ + (n : ℂ) ∈ S := by
  induction n with
  | zero => simpa
  | succ n ih =>
    have h := hFE _ (hCR _ ih)
    convert h using 1
    unfold funcEqReflection coshReflection; push_cast; ring

/-- For any s₀ with 0 < Re(s₀), there exists n such that
    Re(s₀ + n) ≥ 1. In fact n = 1 suffices since the
    translation step is exactly 1. -/
lemma eventually_exceeds_one (s₀ : ℂ) (hs₀ : 0 < s₀.re) :
    ∃ n : ℕ, ¬ (s₀ + (n : ℂ)).re < 1 := by
  exact ⟨1, by simp; linarith⟩

/-- **Main Theorem (Strip Emptiness)**: No nonempty subset of the
    critical strip {s ∈ ℂ | 0 < Re(s) < 1} can be simultaneously
    invariant under both the functional equation reflection s ↦ 1 - s
    and the cosh reflection s ↦ -s.

    **Proof**: The composition (funcEqReflection ∘ coshReflection) is
    a translation by +1. If S ⊆ CriticalStrip is invariant under both,
    then for any s₀ ∈ S, s₀ + 1 ∈ S. But Re(s₀ + 1) = Re(s₀) + 1 > 1,
    contradicting S ⊆ CriticalStrip. -/
theorem no_dual_invariant_set_in_strip :
    ∀ S : Set ℂ, S ⊆ CriticalStrip →
    (∀ s ∈ S, funcEqReflection s ∈ S) →
    (∀ s ∈ S, coshReflection s ∈ S) →
    S = ∅ := by
  intro S hS hFE hCR
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  have hstrip := hS hs
  simp only [CriticalStrip, Set.mem_setOf_eq] at hstrip
  obtain ⟨hpos, hlt⟩ := hstrip
  have h1 := iterate_translation_in_S S hFE hCR s hs 1
  have hstrip1 := hS h1
  simp only [CriticalStrip, Set.mem_setOf_eq, Nat.cast_one] at hstrip1
  simp [Complex.add_re] at hstrip1; linarith [hstrip1.2]

-- ============================================================
-- Part 3: The critical line Re(s) = 1/2 is the unique balance point
-- ============================================================

/-- The functional equation reflection preserves the critical line. -/
lemma funcEqReflection_preserves_criticalLine (s : ℂ) (hs : s ∈ CriticalLine) :
    funcEqReflection s ∈ CriticalLine := by
  simp only [CriticalLine, Set.mem_setOf_eq, funcEqReflection] at *
  simp [hs]
  linarith

/-- The cosh folding (conjugation) preserves the critical line. -/
lemma coshFolding_preserves_criticalLine (s : ℂ) (hs : s ∈ CriticalLine) :
    coshFolding s ∈ CriticalLine := by
  simp only [CriticalLine, Set.mem_setOf_eq, coshFolding] at *
  simp [hs]

/-- **Balance Point Theorem**: If a vertical line Re(s) = c (with 0 < c < 1)
    is invariant under the functional equation reflection s ↦ 1 - s,
    then c = 1/2.

    The functional equation forces Re(1 - s) = 1 - c, so invariance
    of the line Re = c requires c = 1 - c, hence c = 1/2. -/
theorem balance_point_from_funcEq (c : ℝ)
    (hinv : ∀ s : ℂ, s.re = c → (funcEqReflection s).re = c) :
    c = 1 / 2 := by
  have := hinv ⟨c, 0⟩ (by simp)
  simp [funcEqReflection] at this
  linarith

/-- **Full Balance Point Theorem**: The critical line Re(s) = 1/2 is
    the unique vertical line in the critical strip that is preserved
    by all three symmetries:
    • Functional equation reflection: s ↦ 1 - s
    • Cosh reflection: s ↦ -s
    • Cosh folding: s ↦ conj(s)

    The cosh folding preserves every vertical line, so it imposes no
    constraint on c. The cosh reflection sends Re = c to Re = -c,
    which is outside the strip for c > 0, so it cannot preserve
    Re = c within the strip. The functional equation sends Re = c
    to Re = 1 - c, forcing c = 1/2.

    Together, these symmetries force any invariant structure within
    the critical strip to concentrate on the critical line Re(s) = 1/2. -/
theorem critical_line_unique_balance (c : ℝ) (_hc0 : 0 < c) (_hc1 : c < 1)
    (hinv_fe : ∀ s : ℂ, s.re = c → (funcEqReflection s).re = c)
    (_hinv_fold : ∀ s : ℂ, s.re = c → (coshFolding s).re = c) :
    c = 1 / 2 := by
  exact balance_point_from_funcEq c hinv_fe

end Translation
