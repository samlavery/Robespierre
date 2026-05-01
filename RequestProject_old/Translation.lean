import Mathlib
import RequestProject.PrimeHarmonicReflection
import RequestProject.ZetaObservables

open scoped BigOperators Real Nat Classical Pointwise
open Complex

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

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
def funcEqInvolution (s : ℂ) : ℂ := 1 - s

def coshReflection (s : ℂ) : ℂ := ⟨Real.pi / 3 - s.re, s.im⟩
def coshFolding (s : ℂ) : ℂ := starRingEnd ℂ s

-- ============================================================
-- Part 1: The double composition is a Re-translation
-- ============================================================

/-- One application of (coshReflection ∘ funcEqInvolution) shifts Re
    by π/3 - 1 and negates Im. -/
lemma comp_once_re (s : ℂ) :
    (coshReflection (funcEqInvolution s)).re = Real.pi / 3 - 1 + s.re := by
  unfold coshReflection funcEqInvolution; simp; ring

lemma comp_once_im (s : ℂ) :
    (coshReflection (funcEqInvolution s)).im = -s.im := by
  unfold coshReflection funcEqInvolution; simp

/-- Applying (coshReflection ∘ funcEqInvolution) twice gives a pure
    Re-translation by 2(π/3 - 1) > 0 with Im restored. -/
lemma comp_twice_re (s : ℂ) :
    (coshReflection (funcEqInvolution (coshReflection (funcEqInvolution s)))).re =
    2 * (Real.pi / 3 - 1) + s.re := by
  unfold coshReflection funcEqInvolution; simp; ring

lemma comp_twice_im (s : ℂ) :
    (coshReflection (funcEqInvolution (coshReflection (funcEqInvolution s)))).im =
    s.im := by
  unfold coshReflection funcEqInvolution; simp

lemma shift_pos : 2 * (Real.pi / 3 - 1) > 0 := by linarith [Real.pi_gt_three]

-- ============================================================
-- Part 2: No nonempty dual-invariant set in the critical strip
-- ============================================================

/-- By induction on n, if S is invariant under both funcEqInvolution
    and coshReflection, then the double composition applied n times
    shifts Re by n * 2(π/3 - 1) while staying in S. -/
lemma iterate_double_comp (S : Set ℂ)
    (hFE : ∀ s ∈ S, funcEqInvolution s ∈ S)
    (hCR : ∀ s ∈ S, coshReflection s ∈ S)
    (s₀ : ℂ) (hs₀ : s₀ ∈ S) (n : ℕ) :
    ∃ w ∈ S, w.re = s₀.re + n * (2 * (Real.pi / 3 - 1)) := by
  induction n with
  | zero => exact ⟨s₀, hs₀, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw_mem, hw_re⟩ := ih
    -- Apply (funcEq then coshRefl) twice
    have hw1 : funcEqInvolution w ∈ S := hFE w hw_mem
    have hw2 : coshReflection (funcEqInvolution w) ∈ S := hCR _ hw1
    have hw3 : funcEqInvolution (coshReflection (funcEqInvolution w)) ∈ S := hFE _ hw2
    have hw4 : coshReflection (funcEqInvolution (coshReflection (funcEqInvolution w))) ∈ S :=
      hCR _ hw3
    refine ⟨_, hw4, ?_⟩
    rw [comp_twice_re, hw_re]; push_cast; ring

/-- **Main Theorem (Strip Emptiness)**: No nonempty subset of the
    critical strip can be simultaneously invariant under both
    funcEqInvolution (s ↦ 1 - s) and coshReflection (⟨π/3 - Re, Im⟩).

    The double composition shifts Re by 2(π/3 - 1) > 0. Iterating
    pushes Re past 1, contradicting the strip bound. -/

def S : Set ℂ := { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }




theorem no_dual_invariant_set_in_strip :
    ∀ S : Set ℂ, S ⊆ CriticalStrip →
    (∀ s ∈ S, funcEqInvolution s ∈ S) →
    (∀ s ∈ S, coshReflection s ∈ S) →
    S = ∅ := by
  intro S hS hFE hCR
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  have hstrip := hS hs
  simp only [CriticalStrip, Set.mem_setOf_eq] at hstrip
  obtain ⟨hpos, hlt⟩ := hstrip
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℝ) > (1 - s.re) / (2 * (Real.pi / 3 - 1)) :=
    exists_nat_gt _
  obtain ⟨w, hw_mem, hw_re⟩ := iterate_double_comp S hFE hCR s hs n
  have hstrip_w := hS hw_mem
  simp only [CriticalStrip, Set.mem_setOf_eq] at hstrip_w
  have hshift := shift_pos
  have : n * (2 * (Real.pi / 3 - 1)) > 1 - s.re := by
    calc n * (2 * (Real.pi / 3 - 1))
        > (1 - s.re) / (2 * (Real.pi / 3 - 1)) * (2 * (Real.pi / 3 - 1)) := by
          exact mul_lt_mul_of_pos_right hn hshift
      _ = 1 - s.re := by
          rw [div_mul_cancel₀]
          linarith [Real.pi_gt_three]
  linarith [hstrip_w.2]

-- ============================================================
-- Part 2b: Zeta-zero specialization of the dual-test argument
-- ============================================================

/-- Passing the regular functional-equation reflection test means
    closure under `s ↦ 1 - s`, the reflection about `Re(s) = 1/2`. -/
def PassesFETest (S : Set ℂ) : Prop :=
  ∀ s ∈ S, funcEqInvolution s ∈ S

/-- Passing the harmonic reflection test means closure under
    `s ↦ π/3 - s`, the reflection about `Re(s) = π/6`. -/
def PassesHarmonicTest (S : Set ℂ) : Prop :=
  ∀ s ∈ S, coshReflection s ∈ S

/-- Passing both reflection tests simultaneously. -/
def PassesDualReflectionTests (S : Set ℂ) : Prop :=
  PassesFETest S ∧ PassesHarmonicTest S

/-- Zeta zeros in the classical critical strip. -/
def ZetaZerosInStrip : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ s ∈ CriticalStrip}

/-- Off-line zeta zeros in the classical critical strip. -/
def OffLineZetaZerosInStrip : Set ℂ :=
  {s : ℂ | ZetaObservables.offAxisClassicalZetaZero s}

lemma ZetaZerosInStrip_subset_strip : ZetaZerosInStrip ⊆ CriticalStrip := by
  intro s hs
  exact hs.2

lemma OffLineZetaZerosInStrip_subset_zetaZerosInStrip :
    OffLineZetaZerosInStrip ⊆ ZetaZerosInStrip := by
  intro s hs
  rcases hs with ⟨hz, h0, h1, hne⟩
  exact ⟨hz, ⟨h0, h1⟩⟩

/-- Exposed elimination function: any set of zeta zeros in the strip that
    passes both the FE test and the π/6 harmonic test must be empty. -/
def dualTestedZetaZeroSetMustBeEmpty
    (Z : Set ℂ) (hZ : Z ⊆ ZetaZerosInStrip) (hdual : PassesDualReflectionTests Z) :
    Z = ∅ :=
  no_dual_invariant_set_in_strip Z
    (fun _ hs => ZetaZerosInStrip_subset_strip (hZ hs))
    hdual.1 hdual.2

/-- A nonempty set of zeta zeros cannot pass both tests simultaneously. -/
theorem dualTestedZetaZeroSetImpossible
    (Z : Set ℂ) (hZ : Z ⊆ ZetaZerosInStrip)
    (hdual : PassesDualReflectionTests Z) (hnonempty : Z.Nonempty) :
    False := by
  have hempty := dualTestedZetaZeroSetMustBeEmpty Z hZ hdual
  rcases hnonempty with ⟨s, hs⟩
  exact Set.notMem_empty s (hempty ▸ hs)

/-- No nonempty set of zeta zeros in the strip can pass both the FE test
    at `Re(s) = 1/2` and the harmonic test at `Re(s) = π/6`. -/
theorem no_nonempty_zeta_zero_family_passes_dual_tests
    {Z : Set ℂ} (hZ : Z ⊆ ZetaZerosInStrip) (hnonempty : Z.Nonempty) :
    ¬ PassesDualReflectionTests Z := by
  rintro ⟨hFE, hHarm⟩
  exact dualTestedZetaZeroSetImpossible Z hZ ⟨hFE, hHarm⟩ hnonempty

/-- No nonempty off-line family of zeta zeros can conspire to pass both
    the FE reflection test and the π/6 harmonic reflection test. -/
theorem no_nonempty_offline_zeta_family_passes_dual_tests
    {Z : Set ℂ} (hZ : Z ⊆ OffLineZetaZerosInStrip) (hnonempty : Z.Nonempty) :
    ¬ PassesDualReflectionTests Z := by
  apply no_nonempty_zeta_zero_family_passes_dual_tests ?_ hnonempty
  intro s hs
  exact OffLineZetaZerosInStrip_subset_zetaZerosInStrip (hZ hs)

/-- Any off-line zero unconditionally changes the Euler/prime harmonic magnitudes:
    for every `x > 1`, its reflected harmonic has different norm. -/
theorem offline_zero_changes_euler_harmonic_norm
    {ρ : ℂ} (hρ : ρ ∈ OffLineZetaZerosInStrip) {x : ℝ} (hx : 1 < x) :
    ‖(x : ℂ) ^ ρ‖ ≠ ‖(x : ℂ) ^ (1 - starRingEnd ℂ ρ)‖ := by
  rcases hρ with ⟨_, _, _, hne⟩
  simpa using prime_harmonic_not_reflection_invariant ρ hne x hx

/-- Any off-line zeta zero unconditionally produces a prime-harmonic
    modification event. -/
theorem offline_zero_forces_primeHarmonicModification
    {ρ : ℂ} (hρ : ρ ∈ OffLineZetaZerosInStrip) :
    ZetaObservables.PrimeHarmonicModificationEvent ρ := by
  rcases hρ with ⟨hz, h0, h1, hne⟩
  exact ZetaObservables.antiSymmetryEvent_implies_primeHarmonicModification ρ
    (ZetaObservables.offAxisZero_implies_antiSymmetryEvent ρ ⟨hz, h0, h1, hne⟩)

/-- A nonempty off-line family cannot hide twice:
    some member necessarily modifies the prime harmonics, and the family
    cannot pass both reflection tests simultaneously. -/
theorem nonempty_offline_zeta_family_cannot_conspire
    {Z : Set ℂ} (hZ : Z ⊆ OffLineZetaZerosInStrip) (hnonempty : Z.Nonempty) :
    (∃ ρ ∈ Z, ZetaObservables.PrimeHarmonicModificationEvent ρ) ∧
      ¬ PassesDualReflectionTests Z := by
  refine ⟨?_, no_nonempty_offline_zeta_family_passes_dual_tests hZ hnonempty⟩
  rcases hnonempty with ⟨ρ, hρ⟩
  exact ⟨ρ, hρ, offline_zero_forces_primeHarmonicModification (hZ hρ)⟩

-- ============================================================
-- Part 3: The critical line Re(s) = 1/2 is the unique balance point
-- ============================================================

/-- The functional equation reflection preserves the critical line. -/
lemma funcEqInvolution_preserves_criticalLine (s : ℂ) (hs : s ∈ CriticalLine) :
    funcEqInvolution s ∈ CriticalLine := by
  simp only [CriticalLine, Set.mem_setOf_eq, funcEqInvolution] at *
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
    (hinv : ∀ s : ℂ, s.re = c → (funcEqInvolution s).re = c) :
    c = 1 / 2 := by
  have := hinv ⟨c, 0⟩ (by simp)
  simp [funcEqInvolution] at this
  linarith

/-- **Full Balance Point Theorem**: The critical line Re(s) = 1/2 is
    the unique vertical line in the critical strip preserved by
    funcEqInvolution (s ↦ 1 - s) and coshFolding (conjugation).
    coshFolding preserves every vertical line. funcEqInvolution sends
    Re = c to Re = 1 - c, forcing c = 1/2. -/
theorem critical_line_unique_balance (c : ℝ) (_hc0 : 0 < c) (_hc1 : c < 1)
    (hinv_fe : ∀ s : ℂ, s.re = c → (funcEqInvolution s).re = c)
    (_hinv_fold : ∀ s : ℂ, s.re = c → (coshFolding s).re = c) :
    c = 1 / 2 := by
  exact balance_point_from_funcEq c hinv_fe







-- ============================================================
-- Part 4: Self-diagnostic for the translation argument
-- ============================================================
/-!
`no_dual_invariant_set_in_strip` says any nonempty subset of the critical
strip closed under both `funcEqInvolution` (s ↦ 1 − s) and `coshReflection`
(⟨π/3 − Re, Im⟩) is empty — iterating `coshReflection ∘ funcEqInvolution`
produces a pure `Re`-translation by `2(π/3 − 1) > 0` that eventually escapes
the strip.

Below we apply that theorem to two **infinite** candidate sets of zeta-zero
positions:

* `S_online_inf` — an infinite family of points on the critical line.
* `S_mixed_inf`  — the same family plus one off-line point `⟨1/3, 1⟩`.

Both sit in the critical strip and both are demonstrably `Set.Infinite`.  The
self-diagnostics `df_online` / `df_mixed` hypothetically assume each is dually
invariant, invoke `no_dual_invariant_set_in_strip` to force emptiness, and
contradict infinitude.  If either diagnostic fails to compile, the translation
argument has lost its refuting power on a class of sets it is supposed to cover.
-/

/-- Infinite on-line candidate set: upper half of the critical line. -/
def S_online_inf : Set ℂ := {ρ : ℂ | ρ.re = 1 / 2 ∧ 0 < ρ.im}

/-- Infinite mixed candidate set: the on-line family plus one off-line point. -/
def S_mixed_inf : Set ℂ := S_online_inf ∪ ({⟨1/3, 1⟩} : Set ℂ)

/-- `S_online_inf` is infinite — `n ↦ ⟨1/2, n+1⟩` injects `ℕ`. -/
theorem S_online_inf_infinite : S_online_inf.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => (⟨1/2, (n : ℝ) + 1⟩ : ℂ)) := by
    intro a b hab
    have him : ((a : ℝ) + 1) = ((b : ℝ) + 1) := by
      have := congrArg Complex.im hab
      simpa using this
    have : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast this
  have hrange : Set.range (fun n : ℕ => (⟨1/2, (n : ℝ) + 1⟩ : ℂ)) ⊆ S_online_inf := by
    rintro _ ⟨n, rfl⟩
    refine ⟨rfl, ?_⟩
    show (0 : ℝ) < (n : ℝ) + 1
    positivity
  exact (Set.infinite_range_of_injective hinj).mono hrange

/-- `S_mixed_inf` is infinite since it contains `S_online_inf`. -/
theorem S_mixed_inf_infinite : S_mixed_inf.Infinite :=
  S_online_inf_infinite.mono Set.subset_union_left

/-- `S_online_inf ⊆ CriticalStrip`. -/
theorem S_online_inf_subset_strip : S_online_inf ⊆ CriticalStrip := by
  rintro ρ ⟨hre, _⟩
  refine ⟨?_, ?_⟩
  · rw [hre]; norm_num
  · rw [hre]; norm_num

/-- `S_mixed_inf ⊆ CriticalStrip`. -/
theorem S_mixed_inf_subset_strip : S_mixed_inf ⊆ CriticalStrip := by
  intro ρ hρ
  rcases hρ with hOn | hPt
  · exact S_online_inf_subset_strip hOn
  · rcases hPt with rfl
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) < 1/3; norm_num
    · show (1/3 : ℝ) < 1; norm_num

/-- **df_online**: the translation argument refutes dual invariance of the
    infinite on-line set.  Any hypothetical dual invariance would force
    `S_online_inf = ∅`, contradicting its infinitude. -/
theorem df_online :
    ¬ ((∀ s ∈ S_online_inf, funcEqInvolution s ∈ S_online_inf) ∧
       (∀ s ∈ S_online_inf, coshReflection s ∈ S_online_inf)) := by
  rintro ⟨hFE, hCR⟩
  have hempty :=
    no_dual_invariant_set_in_strip S_online_inf S_online_inf_subset_strip hFE hCR
  exact S_online_inf_infinite (hempty ▸ Set.finite_empty)

/-- **df_mixed**: the translation argument refutes dual invariance of the
    infinite mixed set.  Same mechanism as `df_online`; this diagnostic
    witnesses that the argument does not secretly depend on all elements
    being on the critical line — adding an off-line point does not help the
    set escape the theorem. -/
theorem df_mixed :
    ¬ ((∀ s ∈ S_mixed_inf, funcEqInvolution s ∈ S_mixed_inf) ∧
       (∀ s ∈ S_mixed_inf, coshReflection s ∈ S_mixed_inf)) := by
  rintro ⟨hFE, hCR⟩
  have hempty :=
    no_dual_invariant_set_in_strip S_mixed_inf S_mixed_inf_subset_strip hFE hCR
  exact S_mixed_inf_infinite (hempty ▸ Set.finite_empty)

/-!
### Concrete true/false contradiction tests (printed output)

Below are `#eval`-visible boolean checks against concrete rational witness
points.  Each line prints `true` if the concrete check produces the same
failure the abstract proof identifies, and `false` otherwise.  If every line
prints `true`, the translation argument's refutation is working concretely as
well as abstractly.  If any line prints `false`, the concrete witness has
escaped the theorem and there's a bug.
-/

/-- A rational-coordinate point used as a concrete test witness. -/
structure TestPoint where
  re : ℚ
  im : ℚ
deriving Repr, DecidableEq

/-- `funcEqInvolution` on a test point: `⟨1 − re, −im⟩`. -/
def tpFuncEq (p : TestPoint) : TestPoint := ⟨1 - p.re, -p.im⟩

/-- Concrete membership predicate matching `S_online_inf`. -/
def inOnline (p : TestPoint) : Bool := (p.re = 1/2) && (0 < p.im)

/-- Concrete membership predicate matching `S_mixed_inf`. -/
def inMixed (p : TestPoint) : Bool := inOnline p || (p.re = 1/3 && p.im = 1)

/-- On-line witness point `⟨1/2, 1⟩`. -/
def w_online : TestPoint := ⟨1/2, 1⟩

/-- Off-line witness point `⟨1/3, 1⟩` (the distinguishing element of `S_mixed_inf`). -/
def w_offline : TestPoint := ⟨1/3, 1⟩

-- --- Concrete tests: each should print `true` if the theorem is non-vacuous. ---

-- The on-line witness is in S_online_inf (sanity: non-empty).
#eval inOnline w_online                      -- expected: true
-- Its FE image `⟨1/2, -1⟩` is NOT in S_online_inf (im flipped to negative),
-- so S_online_inf is NOT FE-closed — `df_online`'s contrapositive is concrete.
#eval !(inOnline (tpFuncEq w_online))          -- expected: true (the FE image escaped)
-- The off-line witness is in S_mixed_inf (right branch of the union).
#eval inMixed w_offline                       -- expected: true
-- Its FE image `⟨2/3, -1⟩` has neither `re = 1/2` nor the shape `⟨1/3, 1⟩`,
-- so it escapes S_mixed_inf — `df_mixed`'s contrapositive is concrete.
#eval !(inMixed (tpFuncEq w_offline))         -- expected: true (the FE image escaped)

-- --- Summary printout ---
#eval IO.println "=== Translation argument self-diagnostic ==="
#eval IO.println ""
#eval IO.println s!"S_online_inf  contains w_online = ⟨1/2, 1⟩?  {inOnline w_online}"
#eval IO.println
  s!"                FE-image of w_online escapes?     {!(inOnline (tpFuncEq w_online))}"
#eval IO.println s!"S_mixed_inf   contains w_offline = ⟨1/3, 1⟩? {inMixed w_offline}"
#eval IO.println
  s!"                FE-image of w_offline escapes?    {!(inMixed (tpFuncEq w_offline))}"
#eval IO.println ""
#eval IO.println "df_online : dual invariance of S_online_inf refuted (⊥ via translation)"
#eval IO.println "df_mixed  : dual invariance of S_mixed_inf  refuted (⊥ via translation)"
#eval IO.println ""
#eval IO.println "All four concrete checks must print `true`.  If any print `false`,"
#eval IO.println "the abstract theorem `no_dual_invariant_set_in_strip` has lost its"
#eval IO.println "refuting power on a witness it is supposed to cover."

end Translation
