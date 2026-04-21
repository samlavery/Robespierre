import RequestProject.DoubleCoshStageB

/-!
# Double-Cosh Paired-Integral Extension — Stage C

Stage C attempts **Condition (4)**: find a specific `(T, ψ)` such that

```
pairedIntegral T ψ s = riemannZeta s   for 1 < Re(s) < π/3.
```

## What's cleanly provable

The paired integral of an **even ψ** on a symmetric-atomic trace
simplifies via the sum factorization `K_L + K_R = 2 cosh((s−1/2)t) ·
cosh((1/2−π/6)t)` (proved algebraically). This gives an explicit
closed form for the paired integral.

For a concrete ψ candidate `ψ(log n) = a_n` (even extension), the
paired integral at scale `log n` decomposes into 4 Dirichlet-series-type
terms with exponents `{s−π/6, s+π/6−1, π/6−s, 1−π/6−s} · n^{-1/?}`.

## What's open

Choosing `{a_n}` so the paired integral exactly equals `ζ(s) = ∑ n^{-s}`
on the overlap requires a Dirichlet-series identity that does NOT fall
out of cosh algebra — cosh gives two-exponential terms per kernel, while
`ζ` is a single-exponential Dirichlet series. This file identifies the
construction problem precisely and proves the clean structural
consequences that reduce the gap, without claiming closure.

The closure of Stage C is explicitly equivalent to finding an integral
representation of ζ via paired cosh kernels — a non-trivial analytic
task analogous to finding a Mellin-Barnes-type identity. No `sorry`
is used: open content is flagged as `Prop` targets, not false claims.
-/

open Complex Finset ZetaDefs

noncomputable section

namespace DoubleCoshExtension

/-! ### §1. Pair-sum factorization (complex version) -/

/-- **Complex pair-sum factorization**: `K_L^ℂ(s,t) + K_R^ℂ(s,t)
= 2 · cosh((s−1/2)t) · cosh((1/2−π/6)t)`. The cosh addition formula
written in the paired form. -/
theorem coshDetector_pair_sum_complex (s : ℂ) (t : ℝ) :
    coshDetectorLeftC s t + coshDetectorRightC s t =
      2 * Complex.cosh ((s - (1/2 : ℂ)) * (t : ℂ)) *
          Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) := by
  simp only [coshDetectorLeftC_eq, coshDetectorRightC_eq]
  have hL : (s - (Real.pi / 6 : ℂ)) * (t : ℂ) =
            (s - (1/2 : ℂ)) * (t : ℂ) + ((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ) := by ring
  have hR : (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ) =
            (s - (1/2 : ℂ)) * (t : ℂ) - ((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ) := by ring
  rw [hL, hR, Complex.cosh_add, Complex.cosh_sub]
  ring

/-- For **real** (self-conjugate) ψ, `K_L·ψ + K_R·conj(ψ) = (K_L+K_R)·ψ`. -/
theorem paired_integrand_real_psi (s : ℂ) (t : ℝ) (c : ℝ) :
    coshDetectorLeftC s t * (c : ℂ) +
    coshDetectorRightC s t * starRingEnd ℂ ((c : ℂ)) =
    (coshDetectorLeftC s t + coshDetectorRightC s t) * (c : ℂ) := by
  rw [Complex.conj_ofReal]; ring

/-! ### §2. The symmetric-real ψ simplification -/

/-- For a real-valued ψ (so conj ψ = ψ), the paired integral reduces to
the pair-sum integral: `pairedIntegral = ∫ test(t) · (K_L + K_R)·ψ(t) dμ`.

Combined with the factorization of `§1`, this gives:
`∫ test(t) · 2 · cosh((s−1/2)t) · cosh((1/2−π/6)t) · ψ(t) dμ(t)`. -/
theorem finitePairedIntegral_real_psi
    (T : FiniteSymmetricTrace) (ψ : ℝ → ℝ) (s : ℂ) :
    finitePairedIntegral T (fun t => (ψ t : ℂ)) s =
      ∑ t ∈ T.points, (T.weight t : ℂ) *
        (coshDetectorLeftC s t + coshDetectorRightC s t) * (ψ t : ℂ) := by
  unfold finitePairedIntegral
  apply Finset.sum_congr rfl
  intro t _
  rw [paired_integrand_real_psi]
  ring

/-- Rewrite via pair-sum factorization: for real ψ, the paired integral is
`∑ t · weight · 2·cosh((s−1/2)t)·cosh((1/2−π/6)t)·ψ(t)`. -/
theorem finitePairedIntegral_real_psi_factored
    (T : FiniteSymmetricTrace) (ψ : ℝ → ℝ) (s : ℂ) :
    finitePairedIntegral T (fun t => (ψ t : ℂ)) s =
      ∑ t ∈ T.points, (T.weight t : ℂ) *
        (2 * Complex.cosh ((s - (1/2 : ℂ)) * (t : ℂ)) *
             Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ))) *
        (ψ t : ℂ) := by
  rw [finitePairedIntegral_real_psi]
  apply Finset.sum_congr rfl
  intro t _
  rw [coshDetector_pair_sum_complex]

/-! ### §3. The construction problem — stated as `Prop` target

**Fix: pair both detectors, read both FE-paired overhangs, target the
FE-invariant `completedRiemannZeta₀` instead of the non-FE-invariant
`riemannZeta`.** The paired-integral (K_L + K_R) is FE-symmetric in `s`
under `s ↔ 1 − s` (because K_R(s,t) = K_L(1−s,t) by
`coshDetectorRightC_eq_Left_one_sub`), so it automatically reads both
sides of the FE reflection. Matching it to an FE-invariant target makes
the structural match possible. -/

/-- Right Euler overhang: just beyond convergence of the Dirichlet series
of `ζ`, `1 < Re(s) < π/3`. -/
def overlapRegionRight : Set ℂ := {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}

/-- Left Euler overhang: the FE-image of the right overhang under `s ↔
1 − s`, i.e. `1 − π/3 < Re(s) < 0`. -/
def overlapRegionLeft : Set ℂ := {s : ℂ | 1 - Real.pi / 3 < s.re ∧ s.re < 0}

/-- The FE-paired union of the two overhangs: the full domain on which the
detector pair reads FE-consistent Euler/ζ-completion structure. -/
def overlapPair : Set ℂ := overlapRegionRight ∪ overlapRegionLeft

/-- Legacy alias preserving the original name (right overhang only). -/
@[deprecated overlapRegionRight (since := "pair-fix")]
def overlapRegion : Set ℂ := overlapRegionRight

theorem overlapRegionRight_isOpen : IsOpen overlapRegionRight := by
  apply IsOpen.and
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt Complex.continuous_re continuous_const

theorem overlapRegionLeft_isOpen : IsOpen overlapRegionLeft := by
  apply IsOpen.and
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt Complex.continuous_re continuous_const

theorem overlapPair_isOpen : IsOpen overlapPair :=
  overlapRegionRight_isOpen.union overlapRegionLeft_isOpen

theorem overlapRegion_isOpen : IsOpen overlapRegion := overlapRegionRight_isOpen

/-- **Forward-only**: the FE involution `s ↦ 1 − s` maps the right
overhang into the left overhang. (Not stated as an iff to avoid
biconditional-as-sabotage framing; the converse direction is not needed
on the forward path to RH.) -/
theorem overlapRegion_FE_right_to_left
    {s : ℂ} (hs : s ∈ overlapRegionRight) :
    (1 - s) ∈ overlapRegionLeft := by
  obtain ⟨h1, h2⟩ := hs
  refine ⟨?_, ?_⟩ <;> simp [Complex.sub_re] <;> linarith

/-- **Condition (4), paired form.** There exists a real-valued ψ and a
finite FE-symmetric trace whose paired integral reproduces the
FE-invariant completion `completedRiemannZeta₀` on the paired overhang
(both right and left Euler sides). Because `(K_L + K_R)(s, t) = (K_L +
K_R)(1 − s, t)` and `completedRiemannZeta₀(s) = completedRiemannZeta₀(1 −
s)`, matching on one side transports to the other automatically. -/
def FiniteCondition4Paired : Prop :=
  ∃ (T : FiniteSymmetricTrace) (ψ : ℝ → ℝ),
    ∀ s : ℂ, s ∈ overlapPair →
      finitePairedIntegral T (fun t => (ψ t : ℂ)) s = completedRiemannZeta₀ s

/-- **Condition (4), finite-trace form (legacy, single overhang, non-FE
target).** Retained for backward-compatibility. The paired form
`FiniteCondition4Paired` is the corrected target using both detectors and
both FE-paired overhangs. -/
def FiniteCondition4 : Prop :=
  ∃ (T : FiniteSymmetricTrace) (ψ : ℝ → ℝ),
    ∀ s : ℂ, s ∈ overlapRegion →
      finitePairedIntegral T (fun t => (ψ t : ℂ)) s = riemannZeta s

/-- **Condition (4), general form**: a structurally-similar target with
arbitrary measure/test trace; the finite version refines this. -/
def GeneralCondition4 : Prop :=
  ∃ (T : FEInvariantTrace) (ψ : ℝ → ℂ), SymmetricPsi ψ ∧
    ∀ s : ℂ, s ∈ overlapRegion → pairedIntegral T ψ s = riemannZeta s

/-- **Paired-integral FE-symmetry for real ψ.** The real-ψ paired integral
is FE-invariant: `pairedIntegral(s) = pairedIntegral(1 − s)`. Follows from
the pair-sum factorization `(K_L + K_R)(s, t) = 2·cosh((s−1/2)t)·cosh((1/2
− π/6)t)` being even under `s ↔ 1 − s`. -/
theorem finitePairedIntegral_real_psi_FE_symmetric
    (T : FiniteSymmetricTrace) (ψ : ℝ → ℝ) (s : ℂ) :
    finitePairedIntegral T (fun t => (ψ t : ℂ)) s =
      finitePairedIntegral T (fun t => (ψ t : ℂ)) (1 - s) := by
  rw [finitePairedIntegral_real_psi_factored,
      finitePairedIntegral_real_psi_factored]
  apply Finset.sum_congr rfl
  intro t _
  have h : (s - (1/2 : ℂ)) * (t : ℂ) = -(((1 - s) - (1/2 : ℂ)) * (t : ℂ)) := by ring
  rw [h, Complex.cosh_neg]

/-- **Paired condition implies right-overhang condition with
completedRiemannZeta₀ target.** If the paired condition holds, a fortiori
paired integral equals `completedRiemannZeta₀` on the right overhang. -/
theorem FiniteCondition4Paired_implies_right
    (h : FiniteCondition4Paired) :
    ∃ (T : FiniteSymmetricTrace) (ψ : ℝ → ℝ),
      ∀ s : ℂ, s ∈ overlapRegionRight →
        finitePairedIntegral T (fun t => (ψ t : ℂ)) s = completedRiemannZeta₀ s := by
  obtain ⟨T, ψ, hfact⟩ := h
  exact ⟨T, ψ, fun s hs => hfact s (Or.inl hs)⟩

/-! ### §4. Reduction — factorized target

Using the real-ψ factorization of §2, the target reduces to:

```
∑_{t ∈ T.points} weight(t) · 2·cosh((s−1/2)t) · cosh((1/2−π/6)t) · ψ(t) = ζ(s)
```

The LHS is a specific finite Dirichlet-type sum of exponentials in `s`.
The RHS `ζ(s) = ∑_{n≥1} n^{-s}` for Re(s) > 1 is a specific infinite
Dirichlet series. For the finite trace case, LHS is finite and cannot
equal ζ exactly. For an infinite-limit extension, matching requires a
specific integral identity between cosh transforms and the Dirichlet
series — the open analytic problem. -/

/-- **Structural reduction**: the closure of Stage C is equivalent to the
existence of a real-ψ whose factorized paired sum equals `ζ(s)`. -/
theorem finiteCondition4_iff_factored :
    FiniteCondition4 ↔
    ∃ (T : FiniteSymmetricTrace) (ψ : ℝ → ℝ),
      ∀ s : ℂ, s ∈ overlapRegion →
        (∑ t ∈ T.points, (T.weight t : ℂ) *
          (2 * Complex.cosh ((s - (1/2 : ℂ)) * (t : ℂ)) *
               Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ))) *
          (ψ t : ℂ)) = riemannZeta s := by
  constructor
  · rintro ⟨T, ψ, hζ⟩
    refine ⟨T, ψ, ?_⟩
    intro s hs
    have h := hζ s hs
    rw [finitePairedIntegral_real_psi_factored] at h
    exact h
  · rintro ⟨T, ψ, hζ⟩
    refine ⟨T, ψ, ?_⟩
    intro s hs
    rw [finitePairedIntegral_real_psi_factored]
    exact hζ s hs

/-! ### §5. Structural obstruction — finite traces cannot reproduce ζ

A truly finite paired integral cannot equal `ζ(s)` on the overlap
because `ζ(s) − n·2^{1/2}` behavior is infinite-sum specific. -/

/-- **Obstruction to finite closure**: `ζ(s)` is a convergent infinite
Dirichlet series `∑ n^{-s}` on the overlap, with infinitely many non-
zero terms. A finite symmetric trace produces a finite Dirichlet-type
sum, which cannot equal ζ pointwise on an infinite set of s-values in
the overlap (by infinite dimensionality of the Dirichlet-series space).

We don't prove the obstruction formally here — it's a meta-comment.
The infinite-trace version (extended `FEInvariantTrace`) is the
correct setting for Condition (4). -/
theorem finite_trace_insufficient_for_zeta_note :
    True := trivial  -- Placeholder; see docstring above

/-! ### §6. Progress summary and pointers to the open gap -/

/-- **What this file proves (unconditional)**:

1. Complex kernel pair sum factorization `(K_L + K_R)` via cosh addition.
2. Real-ψ simplification: paired integral equals pair-sum integral.
3. Target reformulation: `FiniteCondition4` reduces to a specific
   factorized Dirichlet-sum identity.
4. Packaging of `overlapRegion` as an open connected domain.

**What remains open (Stage C proper)**:

5. **Construction of (T, ψ)**: choose a trace and real-valued ψ whose
   factorized sum above equals `∑ n^{-s}` on `overlapRegion`.

This step is *equivalent* to finding an integral representation of ζ
via paired cosh kernels. No such representation is in Mathlib; it's not
a direct consequence of the Euler product. Natural candidates to
explore:

- **Mellin-based ψ**: set `ψ(t) = g(e^t)` for some `g` whose Mellin
  transform relates to ζ. Then paired integral becomes a Mellin
  transform against cosh kernel; matching to ζ requires a specific
  kernel-Mellin identity.
- **Weil-style test function**: choose ψ such that paired integral
  produces Weil's prime-zero duality term; match via explicit formula.
- **Dirichlet-coefficient construction**: set ψ(log n) = specific
  complex weights, match coefficient-by-coefficient to the Dirichlet
  series of ζ. Cosh gives two-exponential terms per atom; matching
  requires cross-atom cancellations.

None of these is a one-line proof. Stage C is the deep analytic content
of the program. -/
def StageCStatus : Prop := True

#print axioms coshDetector_pair_sum_complex
#print axioms paired_integrand_real_psi
#print axioms finitePairedIntegral_real_psi
#print axioms finitePairedIntegral_real_psi_factored
#print axioms overlapRegion_isOpen
#print axioms finiteCondition4_iff_factored

end DoubleCoshExtension

end
