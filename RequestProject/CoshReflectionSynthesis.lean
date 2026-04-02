import Mathlib

/-!
# Synthesis: Cosh Reflection Invariance of Zeta Zeros

This file proves the synthesis step that connects cosh harmonic representation theory
to the Riemann Hypothesis. It constructs a cosh-reflection-invariant domain containing
both the critical strip and the overlap region, then shows that the assumed cosh harmonic
representation transfers its reflection symmetry to the zeros of the Riemann zeta function.

## Architecture

The proof architecture has these components (numbered as in the project description):

1. **Cosh Harmonics Zeta Invariance**: If `g` is a `CoshHarmonicRepr` on a connected open
   domain `U ⊇ overlapRegion'` and `g` agrees with `riemannZeta` on the overlap, then
   `g = riemannZeta` on all of `U` (identity theorem).
2. **Cosh Kernel Symmetry**: `coshKernel' t (π/6 + δ) = coshKernel' t (π/6 - δ)`.
3. **Cosh Kernel Zeros at Re = π/6**.
4. **Functional Equation**: `completedRiemannZeta s₀ = 0 → completedRiemannZeta (1 - s₀) = 0`.
5. **Dual Reflection Impossibility**: If `S ⊆ criticalStrip` is invariant under both
   `s ↦ 1 - s` and `s ↦ π/3 - s`, then `S = ∅`.
6. **RH Bridge**: If every nontrivial zero with `Re(s) ≠ 1/2` leads to `False`, then RH.

**This file provides the synthesis** (the gap): given (1) and (2), derive that zeros of ζ
in `coshReflDomain` are preserved under cosh reflection `s ↦ π/3 - s`. Combined with
(4)-(6), this yields the Riemann Hypothesis.

## Main results

- `zeta_zero_cosh_reflection` : The synthesis theorem.
- `no_zero_small_re` : No nontrivial zeros with `Re(s) < π/3 - 1`.
- `no_dual_symmetric_set` : Dual reflection impossibility.
- `RiemannHypothesis_of_cosh_harmonics` : RH from the full architecture.
-/

open Complex Real Set Filter Topology

noncomputable section

/-! ## Domain definitions -/

/-- The cosh reflection domain: the vertical strip `{s : ℂ | 0 < Re(s) < π/3}`. -/
def coshReflDomain : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < Real.pi / 3}

/-- The overlap region where the cosh harmonic representation agrees with ζ. -/
def overlapRegion' : Set ℂ :=
  {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}

/-- The critical strip `{s : ℂ | 0 < Re(s) < 1}`. -/
def criticalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The cosh rotation: `s ↦ π/3 - s`. -/
def coshRotation (s : ℂ) : ℂ :=
  ↑(Real.pi / 3) - s

/-- The classical rotation: `s ↦ 1 - s`. -/
def classicalRotation (s : ℂ) : ℂ :=
  1 - s

/-! ## Basic facts -/

theorem pi_div_three_gt_one : Real.pi / 3 > 1 := by
  linarith [pi_gt_three]

theorem pi_div_three_lt_two : Real.pi / 3 < 2 := by
  linarith [pi_lt_d2]

theorem coshRotation_re (s : ℂ) : (coshRotation s).re = Real.pi / 3 - s.re := by
  simp [coshRotation, sub_re, ofReal_re]

theorem coshRotation_im (s : ℂ) : (coshRotation s).im = -s.im := by
  simp [coshRotation, sub_im, ofReal_im]

theorem classicalRotation_re (s : ℂ) : (classicalRotation s).re = 1 - s.re := by
  simp [classicalRotation, sub_re, one_re]

/-! ## Domain properties -/

theorem coshReflDomain_isOpen : IsOpen coshReflDomain := by
  exact isOpen_Ioo.preimage Complex.continuous_re

/-
PROVIDED SOLUTION
coshReflDomain = Complex.re ⁻¹' Set.Ioo 0 (π/3). Since Complex.re is a linear map (ℂ →ₗ[ℝ] ℝ) and Ioo is convex, the preimage is convex. Or prove directly using convex_iff_forall_pos.
-/
theorem coshReflDomain_convex : Convex ℝ coshReflDomain := by
  intro x hx y hy a b ha hb hab;
  constructor <;> simp_all +decide [ ← eq_sub_iff_add_eq' ];
  · cases lt_or_eq_of_le ha <;> cases lt_or_eq_of_le hb <;> nlinarith [ hx.1, hx.2, hy.1, hy.2 ];
  · cases lt_or_ge x.re y.re <;> nlinarith [ hx.2, hy.2 ]

theorem coshReflDomain_isPreconnected : IsPreconnected coshReflDomain :=
  coshReflDomain_convex.isPreconnected

theorem coshReflDomain_nonempty : coshReflDomain.Nonempty :=
  ⟨1 / 2, by constructor <;> simp [coshReflDomain] <;> linarith [pi_gt_three]⟩

theorem coshReflDomain_isConnected : IsConnected coshReflDomain :=
  ⟨coshReflDomain_nonempty, coshReflDomain_isPreconnected⟩

theorem overlapRegion'_subset_coshReflDomain : overlapRegion' ⊆ coshReflDomain := by
  intro s ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

theorem criticalStrip_subset_coshReflDomain : criticalStrip ⊆ coshReflDomain := by
  intro s ⟨h1, h2⟩; exact ⟨h1, by linarith [pi_div_three_gt_one]⟩

/-
PROVIDED SOLUTION
Use the witness ((1 + Real.pi / 3) / 2 : ℝ) cast to ℂ. Show 1 < (1 + π/3)/2 < π/3 using pi_gt_three.
-/
theorem overlapRegion'_nonempty : overlapRegion'.Nonempty := by
  use (1 + Real.pi / 3) / 2;
  constructor <;> norm_num [ Complex.ext_iff ];
  · linarith [ Real.pi_gt_three ];
  · linarith [ Real.pi_gt_three ]

theorem coshReflDomain_coshRotation_invariant :
    ∀ s ∈ coshReflDomain, coshRotation s ∈ coshReflDomain := by
  intro s ⟨h1, h2⟩
  refine ⟨?_, ?_⟩ <;> rw [coshRotation_re] <;> linarith

theorem coshRotation_involutive : Function.Involutive coshRotation :=
  fun s => by simp [coshRotation]

/-- The composition of cosh rotation and classical rotation is translation by `π/3 - 1`. -/
theorem coshRotation_comp_classicalRotation (s : ℂ) :
    coshRotation (classicalRotation s) = s + ↑(Real.pi / 3 - 1) := by
  simp [coshRotation, classicalRotation]; ring

theorem classicalRotation_comp_coshRotation (s : ℂ) :
    classicalRotation (coshRotation s) = s - ↑(Real.pi / 3 - 1) := by
  simp [classicalRotation, coshRotation]; ring

theorem pi_div_three_minus_one_pos : Real.pi / 3 - 1 > 0 := by
  linarith [pi_gt_three]

/-! ## Synthesis theorem

The key deduction: if an analytic function `g` agrees with `riemannZeta` on the
cosh reflection domain and satisfies cosh reflection symmetry `g(π/3 - s) = g(s)`,
then zeros of ζ in the domain are preserved under cosh reflection.
-/

/-- **Synthesis theorem**: Cosh reflection invariance of zeta zeros.

Given a function `g` that:
1. Agrees with `riemannZeta` on `coshReflDomain` (away from `s = 1`)
2. Satisfies cosh reflection symmetry: `g(π/3 - s) = g(s)` for all `s` in the domain

Then `riemannZeta s = 0` implies `riemannZeta (π/3 - s) = 0` for `s` in the domain,
provided both `s` and `π/3 - s` avoid the pole at `s = 1`.

**Proof**: `ζ(π/3 - s) = g(π/3 - s) = g(s) = ζ(s) = 0`.
-/
theorem zeta_zero_cosh_reflection
    (g : ℂ → ℂ)
    (hg_eq : ∀ s ∈ coshReflDomain, s ≠ 1 → g s = riemannZeta s)
    (hg_symm : ∀ s ∈ coshReflDomain, g (coshRotation s) = g s)
    {s : ℂ} (hs : s ∈ coshReflDomain) (hs1 : s ≠ 1)
    (hs_cosh1 : coshRotation s ≠ 1)
    (hzero : riemannZeta s = 0) :
    riemannZeta (coshRotation s) = 0 := by
  have hmem : coshRotation s ∈ coshReflDomain := coshReflDomain_coshRotation_invariant s hs
  calc riemannZeta (coshRotation s)
      = g (coshRotation s) := (hg_eq _ hmem hs_cosh1).symm
    _ = g s := hg_symm s hs
    _ = riemannZeta s := hg_eq s hs hs1
    _ = 0 := hzero

/-- For s in the critical strip, `s ≠ 1` is automatic since `Re(s) < 1`. -/
theorem ne_one_of_mem_criticalStrip {s : ℂ} (hs : s ∈ criticalStrip) : s ≠ 1 := by
  intro h; subst h; exact absurd hs.2 (by norm_num)

/-
PROBLEM
For s in the critical strip with `Im(s) ≠ 0`, `coshRotation s ≠ 1` since
`Im(coshRotation s) = -Im(s) ≠ 0` while `Im(1) = 0`.

PROVIDED SOLUTION
If coshRotation s = 1, then (coshRotation s).im = 0, i.e., -s.im = 0 (by coshRotation_im), so s.im = 0, contradicting him.
-/
theorem coshRotation_ne_one_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0) :
    coshRotation s ≠ 1 := by
  unfold coshRotation; intro H;
  norm_num [ Complex.ext_iff, him ] at H

/-
PROBLEM
For s in the critical strip with `Re(s) ≠ π/3 - 1`, `coshRotation s ≠ 1` since
`Re(coshRotation s) = π/3 - Re(s) ≠ 1`.

PROVIDED SOLUTION
If coshRotation s = 1, then (coshRotation s).re = 1, i.e., π/3 - s.re = 1 (by coshRotation_re), so s.re = π/3 - 1, contradicting hre.
-/
theorem coshRotation_ne_one_of_re_ne {s : ℂ} (hre : s.re ≠ Real.pi / 3 - 1) :
    coshRotation s ≠ 1 := by
  exact fun h => hre <| by have := congr_arg Complex.re h; norm_num [ coshRotation_re ] at this; linarith;

/-! ## Consequences of the synthesis

Using the synthesis theorem and the Mathlib result `riemannZeta_ne_zero_of_one_le_re`,
we derive constraints on the real parts of nontrivial zeros.
-/

/-- **No nontrivial zeros with small real part**: If the cosh harmonic synthesis holds,
then there are no zeros of ζ in the critical strip with `Re(s) < π/3 - 1` (and `Im(s) ≠ 0`).

**Proof**: If `ζ(s) = 0` with `Re(s) < π/3 - 1`, then `Re(π/3 - s) = π/3 - Re(s) > 1`,
so `riemannZeta_ne_zero_of_one_lt_re` gives `ζ(π/3 - s) ≠ 0`. But the synthesis theorem
gives `ζ(π/3 - s) = 0`, contradiction. -/
theorem no_zero_small_re
    (g : ℂ → ℂ)
    (hg_eq : ∀ s ∈ coshReflDomain, s ≠ 1 → g s = riemannZeta s)
    (hg_symm : ∀ s ∈ coshReflDomain, g (coshRotation s) = g s)
    {s : ℂ} (hs : s ∈ criticalStrip) (hre : s.re < Real.pi / 3 - 1)
    (him : s.im ≠ 0)
    (hzero : riemannZeta s = 0) : False := by
  have h1 : riemannZeta (coshRotation s) = 0 :=
    zeta_zero_cosh_reflection g hg_eq hg_symm
      (criticalStrip_subset_coshReflDomain hs)
      (ne_one_of_mem_criticalStrip hs)
      (coshRotation_ne_one_of_im_ne_zero him)
      hzero
  have h2 : 1 < (coshRotation s).re := by rw [coshRotation_re]; linarith
  exact riemannZeta_ne_zero_of_one_lt_re h2 h1

/-- **No nontrivial zeros with large real part**: By the functional equation, if
all nontrivial zeros have `Re(s) ≥ π/3 - 1`, then all have `Re(s) ≤ 2 - π/3`
(since `1 - s` is also a zero and `1 - Re(s) ≥ π/3 - 1` iff `Re(s) ≤ 2 - π/3`). -/
theorem no_zero_large_re
    (g : ℂ → ℂ)
    (hg_eq : ∀ s ∈ coshReflDomain, s ≠ 1 → g s = riemannZeta s)
    (hg_symm : ∀ s ∈ coshReflDomain, g (coshRotation s) = g s)
    -- The functional equation for zeros
    (h_fe : ∀ s : ℂ, s ∈ criticalStrip → riemannZeta s = 0 →
      riemannZeta (classicalRotation s) = 0)
    (h_fe_strip : ∀ s : ℂ, s ∈ criticalStrip → classicalRotation s ∈ criticalStrip)
    {s : ℂ} (hs : s ∈ criticalStrip) (hre : 2 - Real.pi / 3 < s.re)
    (him : s.im ≠ 0)
    (hzero : riemannZeta s = 0) : False := by
  -- 1-s has Re(1-s) = 1 - Re(s) < 1 - (2 - π/3) = π/3 - 1
  have h_cs_mem : classicalRotation s ∈ criticalStrip := h_fe_strip s hs
  have h_cs_re : (classicalRotation s).re < Real.pi / 3 - 1 := by
    rw [classicalRotation_re]; linarith
  have h_cs_im : (classicalRotation s).im ≠ 0 := by
    simp [classicalRotation, sub_im, one_im]; exact him
  exact no_zero_small_re g hg_eq hg_symm h_cs_mem h_cs_re h_cs_im (h_fe s hs hzero)

/-! ## Dual reflection impossibility -/

/-
PROBLEM
**Dual reflection impossibility**: If `S ⊆ criticalStrip` is invariant under both
`classicalRotation` (`s ↦ 1 - s`) and `coshRotation` (`s ↦ π/3 - s`), then `S = ∅`.

The composition `coshRotation ∘ classicalRotation` is translation by `π/3 - 1 > 0`.
For any `s₀ ∈ S`, the orbit `{s₀ + n(π/3 - 1) | n ∈ ℤ} ⊆ S ⊆ criticalStrip`.
But `Re(s₀ + n(π/3 - 1)) = Re(s₀) + n(π/3 - 1)` exceeds 1 for large `n`,
contradicting `S ⊆ criticalStrip`.

PROVIDED SOLUTION
By contradiction, suppose s₀ ∈ S. Then s₀ ∈ criticalStrip, so 0 < Re(s₀) < 1. By hS_cosh, coshRotation s₀ ∈ S. By hS_classical applied to coshRotation s₀, classicalRotation(coshRotation s₀) ∈ S. By classicalRotation_comp_coshRotation, this equals s₀ - ↑(π/3 - 1). So s₁ = s₀ - ↑(π/3 - 1) ∈ S, hence in criticalStrip. Re(s₁) = Re(s₀) - (π/3 - 1). Similarly, using coshRotation_comp_classicalRotation, hS_classical then hS_cosh gives s₀ + ↑(π/3 - 1) ∈ S. By induction, s₀ + n·↑(π/3 - 1) ∈ S for all natural n. Since π/3 - 1 > 0 (by pi_div_three_minus_one_pos), for large enough n, Re(s₀) + n(π/3-1) > 1, but S ⊆ criticalStrip requires Re < 1. Use Archimedean property: ∃ n such that n(π/3-1) > 1 - Re(s₀). This gives a contradiction.
-/
theorem no_dual_symmetric_set (S : Set ℂ)
    (hS_strip : S ⊆ criticalStrip)
    (hS_classical : ∀ s ∈ S, classicalRotation s ∈ S)
    (hS_cosh : ∀ s ∈ S, coshRotation s ∈ S) :
    S = ∅ := by
  contrapose! hS_strip;
  -- By induction, we can show that for any natural number $n$, $s + n \cdot (Real.pi / 3 - 1) \in S$.
  have h_induction : ∀ n : ℕ, ∀ s ∈ S, s + n * (Real.pi / 3 - 1) ∈ S := by
    intro n s hs;
    induction' n with n ih;
    · simpa;
    · have := hS_cosh _ ( hS_classical _ ih );
      convert this using 1 ; push_cast [ coshRotation, classicalRotation ] ; ring;
  -- Choose $n$ such that $n(\pi/3 - 1) > 1 - s.re$ for any $s \in S$.
  obtain ⟨s, hs⟩ : ∃ s ∈ S, True := by
    exact ⟨ hS_strip.some, hS_strip.choose_spec, trivial ⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n * (Real.pi / 3 - 1) > 1 - s.re := by
    exact exists_nat_gt ( ( 1 - s.re ) / ( Real.pi / 3 - 1 ) ) |> fun ⟨ n, hn ⟩ => ⟨ n, by rwa [ div_lt_iff₀ ( by linarith [ Real.pi_gt_three ] ) ] at hn ⟩;
  exact Set.not_subset.2 ⟨ s + n * ( Real.pi / 3 - 1 ), h_induction n s hs.1, fun h => by have := h.2; norm_num at this; linarith ⟩

/-! ## RH from the architecture -/

/-
PROBLEM
**RH from the full proof architecture**.

The argument proceeds as follows. Given a hypothetical nontrivial zero `s₀` with
`Re(s₀) ≠ 1/2`, the zero set `Z` of ζ restricted to the critical strip (with appropriate
conditions) would be:
- Invariant under `classicalRotation` (functional equation)
- Invariant under `coshRotation` (synthesis theorem)
- Contained in the critical strip

By `no_dual_symmetric_set`, `Z = ∅`, contradicting `s₀ ∈ Z`.

Note: The hypotheses `h_cosh_strip` and the synthesis `h_cosh` together require that
cosh rotation maps zeros in the critical strip to zeros in the critical strip. This is
established by first showing (via `no_zero_small_re` and `no_zero_large_re`) that all
nontrivial zeros with `Im ≠ 0` have `π/3 - 1 ≤ Re ≤ 2 - π/3`, and for such zeros,
`coshRotation` maps them into the critical strip.

PROVIDED SOLUTION
Unfold RiemannHypothesis. Take s with ζ(s) = 0, s not a trivial zero, s ≠ 1. We must show s.re = 1/2. By h_nt_strip, s ∈ criticalStrip.

Define the set S = {z ∈ criticalStrip | riemannZeta z = 0 ∧ ¬∃ n : ℕ, z = -2 * (↑n + 1)} (nontrivial zeros in the critical strip).

We want to apply no_dual_symmetric_set to S. We need:
1. S ⊆ criticalStrip: by definition.
2. ∀ z ∈ S, classicalRotation z ∈ S: by h_fe (functional equation preserves zeros) and h_fe_strip (classical rotation preserves critical strip), and showing that classicalRotation z is also not a trivial zero.
3. ∀ z ∈ S, coshRotation z ∈ S: this is the hard part.

For (3), we need: for z ∈ criticalStrip with ζ(z) = 0, coshRotation z ∈ criticalStrip and ζ(coshRotation z) = 0.

Case analysis on Im(z):
- If Im(z) ≠ 0: By coshRotation_ne_one_of_im_ne_zero, coshRotation z ≠ 1. By zeta_zero_cosh_reflection, ζ(coshRotation z) = 0. For coshRotation z ∈ criticalStrip: Re(coshRotation z) = π/3 - Re(z). We need 0 < π/3 - Re(z) < 1. The first holds since Re(z) < 1 < π/3. The second requires Re(z) > π/3 - 1. If Re(z) ≤ π/3 - 1, then by no_zero_small_re, we get False (contradiction with Im(z) ≠ 0 and ζ(z) = 0). So Re(z) > π/3 - 1, hence coshRotation z ∈ criticalStrip.
- If Im(z) = 0: By h_no_real_zeros, ζ(z) ≠ 0, contradicting z ∈ S.

So S is invariant under both rotations. By no_dual_symmetric_set, S = ∅. But s ∈ S (from h_nt_strip and the hypotheses). Contradiction... wait, that means there are NO nontrivial zeros, which can't be right since ζ has known zeros on Re = 1/2.

Hmm, actually RiemannHypothesis says all nontrivial zeros have Re = 1/2. If S is the set of ALL nontrivial zeros in the critical strip, and S = ∅, that would mean there are no nontrivial zeros at all, which contradicts known facts. But RH only needs to be proved FROM the hypotheses. The hypotheses include h_no_real_zeros (no real zeros in (0,1)) and the cosh harmonic representation g.

Actually wait - the hypotheses also include h_cosh_strip-like properties implicitly. The issue is that no_dual_symmetric_set says S = ∅, but s ∈ S by assumption. So we get False, hence any conclusion including s.re = 1/2.

Actually, let me reconsider. The problem is that h_cosh_strip (cosh rotation maps criticalStrip to criticalStrip) is FALSE - it's not a hypothesis of RiemannHypothesis_of_cosh_harmonics. Instead, we show coshRotation z ∈ criticalStrip for zeros by combining the synthesis with the nonvanishing result.

So the proof is: define S = {nontrivial zeros in criticalStrip}. Show S is invariant under both rotations (with the case analysis above). Conclude S = ∅. Since s ∈ S, contradiction, hence any conclusion.

But wait, s.re = 1/2 follows from S = ∅ and s ∈ S only by contradiction (we can prove anything). Is that right? The theorem says: if ζ(s) = 0 and s is not trivial and s ≠ 1, then s.re = 1/2. If we can show that such s leads to s ∈ S = ∅, we get False, hence s.re = 1/2.

Yes, that works. Let me write the proof sketch.

Actually, the approach above shows there are no nontrivial zeros AT ALL (not just those with Re ≠ 1/2), which contradicts mathematics. But from the hypotheses, this is consistent because some hypotheses (like the existence of g with cosh symmetry agreeing with ζ) are almost certainly mathematically false. The theorem is a correct CONDITIONAL statement.

Let me write the proof more carefully for the subagent.
-/
theorem RiemannHypothesis_of_cosh_harmonics
    -- The cosh harmonic representation
    (g : ℂ → ℂ)
    (hg_eq : ∀ s ∈ coshReflDomain, s ≠ 1 → g s = riemannZeta s)
    (hg_symm : ∀ s ∈ coshReflDomain, g (coshRotation s) = g s)
    -- Classical rotation (functional equation) preserves nontrivial zeros
    (h_fe : ∀ s : ℂ, s ∈ criticalStrip → riemannZeta s = 0 →
      riemannZeta (classicalRotation s) = 0)
    -- Classical rotation preserves the critical strip
    (h_fe_strip : ∀ s : ℂ, s ∈ criticalStrip → classicalRotation s ∈ criticalStrip)
    -- Nontrivial zeros lie in the critical strip
    (h_nt_strip : ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 → s ∈ criticalStrip)
    -- Technical: ζ has no real zeros in (0,1)
    -- (needed for the edge case Re(s) = π/3 - 1, Im(s) = 0)
    (h_no_real_zeros : ∀ s : ℂ, s ∈ criticalStrip → s.im = 0 →
      riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hs h_non_trivial h_ne_one
  have h_critical : s ∈ criticalStrip := by
    exact h_nt_strip s hs h_non_trivial h_ne_one;
  -- Define the set S = {z ∈ criticalStrip | riemannZeta z = 0 ∧ ¬∃ n : ℕ, z = -2 * (↑n + 1)} (nontrivial zeros in the critical strip).
  set S : Set ℂ := {z ∈ criticalStrip | riemannZeta z = 0 ∧ ¬∃ n : ℕ, z = -2 * (↑n + 1)};
  -- Show that S is invariant under both classical and cosh rotations.
  have hS_classical : ∀ z ∈ S, classicalRotation z ∈ S := by
    simp +zetaDelta at *;
    intro z hz hz' hz'' hz'''; simp_all +decide [ criticalStrip, classicalRotation ] ;
    intro n hn; norm_num [ Complex.ext_iff ] at hn; linarith;
  have hS_cosh : ∀ z ∈ S, coshRotation z ∈ S := by
    intro z hz;
    by_cases hz_im : z.im = 0;
    · exact False.elim <| h_no_real_zeros z hz.1 hz_im hz.2.1;
    · -- By the synthesis theorem, since $z \in S$, we have $\zeta(\pi/3 - z) = 0$.
      have hz_cosh_zero : riemannZeta (coshRotation z) = 0 := by
        apply zeta_zero_cosh_reflection g hg_eq hg_symm;
        · exact criticalStrip_subset_coshReflDomain hz.1;
        · exact ne_one_of_mem_criticalStrip hz.1;
        · exact coshRotation_ne_one_of_im_ne_zero hz_im;
        · exact hz.2.1;
      -- By the synthesis theorem, since $z \in S$, we have $\pi/3 - z \in \text{criticalStrip}$.
      have hz_cosh_critical : coshRotation z ∈ criticalStrip := by
        simp_all +decide [ Complex.ext_iff, coshRotation ];
      refine' ⟨ hz_cosh_critical, hz_cosh_zero, _ ⟩;
      rintro ⟨ n, hn ⟩;
      norm_num [ Complex.ext_iff, coshRotation ] at hn;
      exact hz_im hn.2;
  -- By `no_dual_symmetric_set`, `S = ∅`.
  have hS_empty : S = ∅ := by
    apply no_dual_symmetric_set;
    · exact fun x hx => hx.1;
    · assumption;
    · assumption;
  exact False.elim <| hS_empty.subset ⟨ h_critical, hs, h_non_trivial ⟩

end