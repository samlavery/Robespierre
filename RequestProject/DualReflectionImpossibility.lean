import Mathlib

/-!
# Dual Reflection Impossibility Theorem

We prove unconditionally that no infinite set of off-critical-line points in the
classical critical strip {s ∈ ℂ : 0 < Re(s) < 1} can be simultaneously invariant under:

1. **Classical 180° rotation** around Re(s) = 1/2: the map s ↦ 1 - s.
   This is the symmetry from the functional equation ξ(s) = ξ(1 - s), so zeros of ζ
   come in pairs {s, 1 - s}. The classical critical strip goes from 1/2 to -1/2
   under Schwarz reflection.

2. **Cosh reflection** at arcsin(1/2) = π/6: the map s ↦ π/3 - s.
   The cosh critical strip goes from π/6 to -π/6 under Schwarz reflection.
   The offset coverage extends from 0 to π/3, which exceeds 1.

## Key Argument

The composition of these two involutions is translation by π/3 - 1 > 0
(since π > 3). Any point in the critical strip, when repeatedly translated by
this positive amount, eventually exceeds Re(s) = 1, leaving the strip.
Therefore no nonempty subset of the strip can be invariant under both maps.

In particular, no infinite set of off-line zeros can simultaneously:
- survive the classical 180° rotation symmetry test (Euler product / functional equation), AND
- satisfy the cosh reflection symmetry test at arcsin(1/2) based on prime harmonic decomposition.

This is proved unconditionally — no assumption about RH is needed.

## Closure

We further show that both maps are continuous (affine) involutions, so invariance
passes to topological closure. Since the main theorem forces S = ∅, we conclude
closure S = ∅ as well. This gives the strongest form of the impossibility result.
-/

open Complex Real Set

noncomputable section

/-- Classical 180° rotation around s = 1/2: s ↦ 1 - s.
    This is the symmetry of the Riemann xi function: ξ(s) = ξ(1 - s). -/
def classicalRotation (s : ℂ) : ℂ := 1 - s

/-- Cosh reflection around arcsin(1/2) = π/6: s ↦ π/3 - s.
    Based on prime harmonic decomposition with cosh kernel at arcsin(1/2),
    the cosh critical strip runs from π/6 to -π/6 under Schwarz reflection,
    giving coverage from 0 to π/3 (which extends past 1). -/
def coshRotation (s : ℂ) : ℂ := ↑(Real.pi / 3) - s

/-- The composition of cosh rotation after classical rotation is a real translation
    by π/3 - 1, the key offset between the two symmetry axes. -/
lemma composition_is_translation (s : ℂ) :
    coshRotation (classicalRotation s) = s + ↑(Real.pi / 3 - 1) := by
  simp [classicalRotation, coshRotation]
  ring

/-- π/3 - 1 > 0, since π > 3. This is what makes the cosh strip "extend past one." -/
lemma shift_pos : Real.pi / 3 - 1 > 0 := by
  linarith [Real.pi_gt_three]

/-- If S is invariant under both rotations, any element can be translated by π/3 - 1. -/
lemma translate_step (S : Set ℂ)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotation s ∈ S)
    {s : ℂ} (hs : s ∈ S) :
    s + ↑(Real.pi / 3 - 1) ∈ S := by
  simpa [composition_is_translation] using h2 _ (h1 _ hs)

/-- Iterating: s + n * (π/3 - 1) ∈ S for all n ∈ ℕ. -/
lemma iterate_translate (S : Set ℂ)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotation s ∈ S)
    {s : ℂ} (hs : s ∈ S) (n : ℕ) :
    s + ↑(↑n * (Real.pi / 3 - 1)) ∈ S := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    convert translate_step S h1 h2 ih using 1
    push_cast; ring

/-- **Main Theorem**: No nonempty subset of the critical strip {0 < Re(s) < 1}
    can be simultaneously invariant under the classical rotation at 1/2
    and the cosh rotation at arcsin(1/2) = π/6.

    The proof shows that dual invariance implies invariance under translation
    by π/3 - 1 > 0. By the Archimedean property, iterating this translation
    pushes any point's real part past 1, contradicting membership in the strip. -/
theorem no_dual_symmetric_set (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotation s ∈ S) :
    S = ∅ := by
  by_contra h_nonempty
  obtain ⟨s, hs⟩ : ∃ s ∈ S, 0 < s.re ∧ s.re < 1 :=
    (Set.nonempty_iff_ne_empty.mpr h_nonempty).elim fun s hs => ⟨s, hs, hstrip s hs⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℝ) > (1 - s.re) / (Real.pi / 3 - 1) := exists_nat_gt _
  have hmem := iterate_translate S h1 h2 hs.1 n
  have hbound := hstrip _ hmem
  norm_num at *
  nlinarith [Real.pi_gt_three,
    mul_div_cancel₀ (1 - s.re) (show (Real.pi / 3 - 1) ≠ 0 by linarith [Real.pi_gt_three])]

/-- **Corollary (The Impossibility Result)**:
    No infinite set of off-critical-line zeros can pass both symmetry tests.

    Given prime harmonic decomposition and cancellation at arcsin(1/2),
    no infinite collection of off-line classical zeros can simultaneously:
    (a) survive a classical 180° rotation around 1/2 (functional equation / Euler product), AND
    (b) satisfy a cosh reflection symmetry test at arcsin(1/2).

    This is proved unconditionally — it assumes nothing about RH. -/
theorem no_infinite_offline_zeros_pass_both_tests (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (hoffline : ∀ s ∈ S, s.re ≠ 1/2)
    (hinf : S.Infinite)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotation s ∈ S) :
    False := by
  have hempty := no_dual_symmetric_set S hstrip h1 h2
  subst hempty
  exact hinf Set.finite_empty

/-! ## Closure invariance

The maps `classicalRotation` and `coshRotation` are continuous (in fact, affine).
Therefore, if a set `S` is invariant under both maps, so is its topological closure `closure S`.
Combined with the main theorem, this shows `closure S = ∅`, hence `S = ∅`.

This is the natural setting for zero sets of analytic or continuous functions,
which are automatically closed. -/

/-- Classical rotation is continuous. -/
lemma continuous_classicalRotation : Continuous classicalRotation :=
  continuous_const.sub continuous_id

/-- Cosh rotation is continuous. -/
lemma continuous_coshRotation : Continuous coshRotation :=
  continuous_const.sub continuous_id

/-- Classical rotation is an involution: applying it twice yields the identity. -/
lemma classicalRotation_involutive : Function.Involutive classicalRotation := by
  intro s; simp [classicalRotation, sub_sub_cancel]

/-- Cosh rotation is an involution: applying it twice yields the identity. -/
lemma coshRotation_involutive : Function.Involutive coshRotation := by
  intro s; simp [coshRotation, sub_sub_cancel]

/-
PROBLEM
If S is invariant under classical rotation, so is closure S.
    Since classicalRotation is a continuous involution, it maps S into S
    iff it maps closure S into closure S.

PROVIDED SOLUTION
classicalRotation is continuous (continuous_classicalRotation). The hypothesis says classicalRotation maps S into S, i.e. classicalRotation '' S ⊆ S. By continuity, classicalRotation maps closure S into closure (classicalRotation '' S) ⊆ closure S. Concretely: use Continuous.closure_preimage_subset or the fact that the preimage of closure S under a continuous map contains closure of the preimage. Since classicalRotation is its own inverse (involutive), s ∈ closure S implies classicalRotation s ∈ closure S.
-/
lemma closure_invariant_classicalRotation (S : Set ℂ)
    (h : ∀ s ∈ S, classicalRotation s ∈ S) :
    ∀ s ∈ closure S, classicalRotation s ∈ closure S := by
  intro s hs;
  rw [ mem_closure_iff_seq_limit ] at *;
  obtain ⟨ x, hx₁, hx₂ ⟩ := hs; exact ⟨ fun n => classicalRotation ( x n ), fun n => h _ ( hx₁ n ), by simpa [ classicalRotation ] using Filter.Tendsto.const_sub 1 hx₂ ⟩ ;

/-
PROBLEM
If S is invariant under cosh rotation, so is closure S.

PROVIDED SOLUTION
Same approach as closure_invariant_classicalRotation: coshRotation is continuous, and maps S into S by hypothesis. Use sequential characterization of closure: if s_n → s with s_n ∈ S, then coshRotation(s_n) → coshRotation(s) by continuity, and coshRotation(s_n) ∈ S by hypothesis.
-/
lemma closure_invariant_coshRotation (S : Set ℂ)
    (h : ∀ s ∈ S, coshRotation s ∈ S) :
    ∀ s ∈ closure S, coshRotation s ∈ closure S := by
  intro s hs
  rw [mem_closure_iff_seq_limit] at *;
  exact ⟨ _, fun n => h _ ( hs.choose_spec.1 n ), Filter.Tendsto.sub tendsto_const_nhds hs.choose_spec.2 ⟩

/-- The closure of a dual-invariant subset of the critical strip is empty.
    Since S = ∅ by the main theorem, closure ∅ = ∅ follows immediately. -/
theorem closure_dual_invariant_empty (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotation s ∈ S) :
    closure S = ∅ := by
  have hempty := no_dual_symmetric_set S hstrip h1 h2
  rw [hempty, closure_empty]

/-- **Final Conclusion**: Even after taking closure, a dual-invariant subset
    of the critical strip must be empty. This gives the strongest form of the
    impossibility result: no set (open, closed, or otherwise) in the critical strip
    can be simultaneously invariant under both reflections. -/
theorem dual_invariance_forces_empty (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (h1 : ∀ s ∈ S, classicalRotation s ∈ S)
    (h2 : ∀ s ∈ S, coshRotation s ∈ S) :
    S = ∅ ∧ closure S = ∅ :=
  ⟨no_dual_symmetric_set S hstrip h1 h2,
   closure_dual_invariant_empty S hstrip h1 h2⟩

end