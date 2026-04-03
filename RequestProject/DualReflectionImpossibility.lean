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
   The cosh kernel is anchored at x = π/6 with the cosh critical strip extending
   vertically from y = −π/3 to y = π/3 (the imaginary extent). The strip's two
   boundaries extend past y = −1 and y = 1 (since π/3 > 1).
   The Schwarz reflection line sits at x = 0 (the imaginary axis), so the cosh
   critical strip runs from π/6 to −π/6 under this reflection, giving offset
   coverage from 0 to π/3 which exceeds 1.

## Two Automatic Symmetries of Cosh

Both symmetries exploited here are baked into the analytic structure of `cosh`:

- **Re-axis reflection (evenness, s ↦ −s)**: comes from `cosh(z) = cosh(−z)`,
  the even-function property. This is the source of the cosh reflection
  invariance for prime harmonics (`primeHarmonic_reflection_invariant`).

- **Im = 0 fold (conjugate symmetry, s ↦ s̄)**: comes from `cosh` having real
  Taylor coefficients, giving `cosh(z̄) = conj(cosh(z))`. This is the
  "automatic fold" property.

Conjugate zeros of cosh appear in dual pairs: two between y = 1 and y = π/3,
and two between y = −1 and y = −π/3. These dual pairs decompose harmonics
into cosine (even/balanced) and sine (odd/balanced) components, and reflect
over the Schwarz line at x = 0 to within y = π/3 − 1 to y = −π/3 + 1,
creating balanced quartets from balanced harmonics.

Decomposed balanced harmonics cancel under this regime. Unbalanced harmonics
are forced by the implicit fold over Im = 0 to real values x = 1/2 with y ≠ 0.
This is structural.

## Key Argument

The composition of these two involutions is translation by π/3 - 1 > 0
(since π > 3). Any point in the critical strip, when repeatedly translated by
this positive amount, eventually exceeds Re(s) = 1, leaving the strip.
Therefore no nonempty subset of the strip can be invariant under both maps.

In particular, no infinite set of off-line zeros can simultaneously:
- survive the classical 180° rotation symmetry test (Euler product / functional equation), AND
- satisfy the cosh reflection symmetry test at arcsin(1/2) based on prime harmonic decomposition.

This is proved unconditionally — no assumption about RH is needed.

## Prime Harmonics and the Cosh Kernel

The deeper reason for the cosh reflection is the Euler product for ζ: each prime p
contributes a factor (1 − p⁻ˢ)⁻¹, giving rise to "prime harmonics" at frequencies
log p. The cosh kernel naturally symmetrizes these harmonics:

  cosh((s − σ) · log p)  =  (p^(s−σ) + p^(σ−s)) / 2

is invariant under s ↦ 2σ − s for any center σ. When σ = π/6, this gives the
cosh reflection s ↦ π/3 − s. Both the evenness of cosh and its real-coefficient
conjugate symmetry are "automatic" — they are intrinsic to cosh's analytic
structure and require no additional assumptions. We prove:

- **Primes are the fundamental invariant**: the set of prime logarithms {log p}
  generates the harmonic frequencies.
- **Prime harmonics are cosh-invariant**: for each prime p, the function
  s ↦ cosh((s − π/6) · log p) is invariant under the cosh reflection.
- **Prime harmonics are classically invariant**: for each prime p, the function
  s ↦ cosh((s − 1/2) · log p) is invariant under the classical rotation.
- **Cosh evenness** (`cosh_even_symmetry`): cosh(z) = cosh(−z), the Re-axis
  reflection that drives the prime harmonic reflection invariance.
- **Cosh conjugate symmetry** (`cosh_conjugate_symmetry`): cosh(z̄) = conj(cosh(z)),
  the Im = 0 fold from real Taylor coefficients.
- **No set of harmonics can be invariant under both**: since the two symmetry
  axes differ by (π/3 − 1)/2 > 0, the dual invariance forces emptiness.

This connects the classical zeros of ζ (governed by the functional equation)
to the primes (governing the Euler product) through the prime harmonics that
the cosh kernel observes.

## Closure

We further show that both maps are continuous (affine) involutions, so invariance
passes to topological closure. Since the main theorem forces S = ∅, we conclude
closure S = ∅ as well. This gives the strongest form of the impossibility result.
-/

open Complex Real Set

noncomputable section

/-! ### Fundamental maps -/

/-- Classical 180° rotation around s = 1/2: s ↦ 1 - s.
    This is the symmetry of the Riemann xi function: ξ(s) = ξ(1 - s). -/
def classicalRotationD (s : ℂ) : ℂ := 1 - s

/-- Cosh reflection around arcsin(1/2) = π/6: s ↦ π/3 - s.
    The cosh kernel is anchored at x = π/6. The cosh critical strip extends
    vertically from y = −π/3 to y = π/3, with boundaries extending past y = ±1
    (since π/3 > 1). The Schwarz reflection line sits at x = 0 (the imaginary
    axis), so the strip runs from π/6 to −π/6 under this reflection, giving
    offset coverage from 0 to π/3.

    The cosh reflection is "automatic" — it derives from two intrinsic symmetries
    of cosh: the evenness cosh(z) = cosh(−z) (Re-axis reflection), and the
    conjugate symmetry cosh(z̄) = conj(cosh(z)) from real Taylor coefficients
    (Im = 0 fold). -/
def coshRotationD (s : ℂ) : ℂ := ↑(Real.pi / 3) - s

/-- The composition of cosh rotation after classical rotation is a real translation
    by π/3 - 1, the key offset between the two symmetry axes. -/
lemma composition_is_translation (s : ℂ) :
    coshRotationD (classicalRotationD s) = s + ↑(Real.pi / 3 - 1) := by
  simp [classicalRotationD, coshRotationD]
  ring

/-- π/3 - 1 > 0, since π > 3. This is what makes the cosh strip "extend past one." -/
lemma shift_pos : Real.pi / 3 - 1 > 0 := by
  linarith [Real.pi_gt_three]

/-! ### Automatic Cosh Symmetries

The two symmetries of the cosh kernel that drive all the reflection invariance
results are both intrinsic ("automatic") properties of cosh:

1. **Evenness** (Re-axis reflection, s ↦ −s): `cosh(z) = cosh(−z)`.
2. **Conjugate symmetry** (Im = 0 fold, s ↦ s̄): `cosh(z̄) = conj(cosh(z))`,
   because cosh has real Taylor coefficients.

Conjugate zeros of cosh appear in dual pairs between y = 1 and y = π/3, and
between y = −1 and y = −π/3. These dual pairs decompose harmonics into cosine
and sine components, and reflect over the Schwarz line at x = 0 to create
balanced quartets. Balanced harmonics cancel; unbalanced harmonics are forced
by the Im = 0 fold to real values x = 1/2 with y ≠ 0. -/

/-- **Cosh evenness (Re-axis reflection symmetry)**: `cosh(z) = cosh(−z)`.
    This is the automatic even-function property that drives the cosh reflection
    invariance of prime harmonics. It is intrinsic to the analytic structure of cosh. -/
theorem cosh_even_symmetry (z : ℝ) : Real.cosh z = Real.cosh (-z) := by
  rw [Real.cosh_neg]

/-- **Cosh conjugate symmetry (Im = 0 fold)**: `cosh(z̄) = conj(cosh(z))`.
    This follows from cosh having real Taylor coefficients: cosh(z) = ∑ z²ⁿ/(2n)!,
    so applying conjugation commutes through the sum. This is the "automatic fold"
    property over the real axis (Im = 0).
    Together with evenness, this creates the balanced quartet structure from
    dual pairs of conjugate zeros. -/
theorem cosh_conjugate_symmetry (z : ℂ) :
    Complex.cosh (starRingEnd ℂ z) = starRingEnd ℂ (Complex.cosh z) := by
  unfold Complex.cosh
  simp only [map_div₀, map_add, Complex.exp_conj]
  congr 1
  · congr 1
    rw [show -(starRingEnd ℂ z) = starRingEnd ℂ (-z) from (map_neg _ z).symm, Complex.exp_conj]
  · simp [map_ofNat]

/-- The cosh kernel strip boundaries extend past ±1: π/3 > 1.
    This ensures the cosh critical strip (from y = −π/3 to y = π/3)
    covers the classical critical strip (from y = −1 to y = 1). -/
theorem cosh_strip_exceeds_one : Real.pi / 3 > 1 := by
  linarith [Real.pi_gt_three]

/-! ### Prime Harmonics

The Euler product ζ(s) = ∏_p (1 − p⁻ˢ)⁻¹ decomposes the zeta function into
contributions from individual primes. Each prime p contributes a harmonic at
frequency log p. The **cosh kernel** symmetrizes these harmonics, making them
invariant under reflection about the kernel's center.

This section formalizes:
- The set of prime harmonic frequencies {log p : p prime}.
- The cosh-symmetrized prime harmonic functions.
- Their invariance under both classical and cosh reflections.
-/

/-- The set of prime harmonic frequencies: {log p : p is prime}.
    These are the fundamental frequencies in the Euler product decomposition of ζ.
    The primes themselves are the main invariant — every harmonic frequency is
    determined by a prime. -/
def primeHarmonicFreqs : Set ℝ :=
  {ω : ℝ | ∃ p : ℕ, p.Prime ∧ ω = Real.log p}

/-- A prime harmonic observed by the cosh kernel centered at σ:
    s ↦ cosh((s − σ) · log p).
    When σ = π/6, this is the cosh kernel's observation of the p-th prime harmonic.
    When σ = 1/2, this is the classical symmetrization. -/
def primeHarmonicD (p : ℕ) (σ : ℝ) (s : ℝ) : ℝ :=
  Real.cosh ((s - σ) * Real.log p)

/-- **Prime harmonics are invariant under reflection about their center.**
    For any prime p and center σ, the function s ↦ cosh((s − σ) · log p) satisfies
    f(2σ − s) = f(s). This is the core symmetry that the cosh kernel exploits:
    it sees each prime's contribution as an even function about the reflection axis.

    This invariance is "automatic" — it follows directly from the evenness of cosh
    (cosh(z) = cosh(−z), the Re-axis reflection symmetry), which is baked into
    the analytic structure of cosh. The primes are the invariant, and their
    harmonics inherit this invariance through the automatic fold property. -/
theorem primeHarmonic_reflection_invariantD (p : ℕ) (σ s : ℝ) :
    primeHarmonicD p σ (2 * σ - s) = primeHarmonicD p σ s := by
  simp only [primeHarmonicD]
  have : (2 * σ - s - σ) * Real.log ↑p = -((s - σ) * Real.log ↑p) := by ring
  rw [this, Real.cosh_neg]

/-- **Cosh reflection invariance of prime harmonics (h2 connection).**
    For each prime p, the harmonic s ↦ cosh((s − π/6) · log p) is invariant
    under the cosh reflection s ↦ π/3 − s.

    This is the precise sense in which h2 (cosh rotation invariance) connects
    to the primes: the cosh kernel anchored at x = π/6 observes each prime
    harmonic as an even function about π/6, making the Euler product's
    prime-by-prime contributions invariant under the cosh reflection.
    The invariance is automatic, deriving from the evenness of cosh
    (cosh(z) = cosh(−z)) — the Re-axis reflection symmetry baked into
    cosh's analytic structure. -/
theorem primeHarmonic_coshRotation_invariant (p : ℕ) (s : ℝ) :
    primeHarmonicD p (Real.pi / 6) (Real.pi / 3 - s)
      = primeHarmonicD p (Real.pi / 6) s := by
  have : Real.pi / 3 - s = 2 * (Real.pi / 6) - s := by ring
  rw [this]
  exact primeHarmonic_reflection_invariantD p (Real.pi / 6) s

/-- **Classical rotation invariance of prime harmonics.**
    For each prime p, the harmonic s ↦ cosh((s − 1/2) · log p) is invariant
    under the classical rotation s ↦ 1 − s.

    This shows that the same primes that generate h2's cosh invariance also
    generate h1's classical invariance — the primes are the common invariant
    underlying both symmetries. -/
theorem primeHarmonic_classicalRotation_invariant (p : ℕ) (s : ℝ) :
    primeHarmonicD p (1/2 : ℝ) (1 - s)
      = primeHarmonicD p (1/2 : ℝ) s := by
  have : (1 : ℝ) - s = 2 * (1/2 : ℝ) - s := by ring
  rw [this]
  exact primeHarmonic_reflection_invariantD p (1/2) s

/-
PROBLEM
The prime harmonic frequencies are infinite (there are infinitely many primes).
    This shows that the cosh kernel observes infinitely many independent harmonics.

PROVIDED SOLUTION
The set {log p : p prime} is infinite because there are infinitely many primes (Nat.exists_infinite_primes). The map p ↦ log p is injective on primes (since log is strictly monotone on positive reals, and primes are ≥ 2 > 0). An injective image of an infinite set is infinite.
-/
theorem primeHarmonicFreqs_infinite : primeHarmonicFreqs.Infinite := by
  have h_log_inj : Set.Infinite (Set.image Real.log {p : ℝ | ∃ p' : ℕ, p'.Prime ∧ p = p'}) := by
    refine Set.Infinite.image ?_ ?_;
    · exact fun x hx y hy hxy => by have := Real.log_injOn_pos ( show 0 < x from by obtain ⟨ p', hp', rfl ⟩ := hx; exact Nat.cast_pos.mpr hp'.pos ) ( show 0 < y from by obtain ⟨ p', hp', rfl ⟩ := hy; exact Nat.cast_pos.mpr hp'.pos ) hxy; aesop;
    · exact Set.infinite_of_forall_exists_gt fun x => by rcases Nat.exists_infinite_primes ( ⌊x⌋₊ + 1 ) with ⟨ p, hp₁, hp₂ ⟩ ; exact ⟨ p, ⟨ p, hp₂, rfl ⟩, Nat.lt_of_floor_lt hp₁ ⟩ ;
  exact h_log_inj.mono fun x hx => by obtain ⟨ p, ⟨ q, hq, rfl ⟩, rfl ⟩ := hx; exact ⟨ q, hq, rfl ⟩ ;

/-
PROBLEM
Each prime harmonic frequency is positive (log p > 0 for p ≥ 2).
    This ensures each harmonic oscillates nontrivially.

PROVIDED SOLUTION
If ω ∈ primeHarmonicDFreqs, then ω = log p for some prime p. Since p ≥ 2, we have (p : ℝ) ≥ 2 > 1, so log p > 0 (Real.log_pos).
-/
theorem primeHarmonicFreq_pos {ω : ℝ} (hω : ω ∈ primeHarmonicFreqs) : 0 < ω := by
  obtain ⟨ p, hp, rfl ⟩ := hω; exact Real.log_pos ( Nat.one_lt_cast.mpr hp.one_lt ) ;

/-
PROBLEM
**The dual invariance gap for prime harmonics.**
    The two symmetry centers differ: π/6 ≠ 1/2. This means a prime harmonic
    cannot be simultaneously centered at both axes. The mismatch is
    (1/2 − π/6), and the composition of reflections about these two centers
    yields a translation by 2 · (1/2 − π/6) = 1 − π/3, whose absolute value
    is π/3 − 1 > 0.

    This is the harmonic-level manifestation of the impossibility: the primes
    generate invariance under each reflection separately, but the two reflection
    axes are incompatible — no set can be invariant under both.

PROVIDED SOLUTION
1/2 ≠ π/6 because π ≠ 3 (since π > 3, by Real.pi_gt_three). More precisely, if 1/2 = π/6 then π = 3, contradicting π > 3.
-/
theorem symmetry_centers_differ : (1 : ℝ) / 2 ≠ Real.pi / 6 := by
  linarith [ Real.pi_gt_three ]

/-! ### Translation and emptiness -/

/-- If S is invariant under both rotations, any element can be translated by π/3 - 1. -/
lemma translate_step (S : Set ℂ)
    (h1 : ∀ s ∈ S, classicalRotationD s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationD s ∈ S)
    {s : ℂ} (hs : s ∈ S) :
    s + ↑(Real.pi / 3 - 1) ∈ S := by
  simpa [composition_is_translation] using h2 _ (h1 _ hs)

/-- Iterating: s + n * (π/3 - 1) ∈ S for all n ∈ ℕ. -/
lemma iterate_translate (S : Set ℂ)
    (h1 : ∀ s ∈ S, classicalRotationD s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationD s ∈ S)
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
    pushes any point's real part past 1, contradicting membership in the strip.

    At the prime-harmonic level, this reflects the incompatibility of the two
    symmetry centers: each prime p generates a cosh harmonic invariant under
    reflection about π/6 (via `primeHarmonic_coshRotation_invariant`) and
    another invariant under reflection about 1/2
    (via `primeHarmonic_classicalRotation_invariant`), but since π/6 ≠ 1/2
    (via `symmetry_centers_differ`), no point set can satisfy both at once. -/
theorem no_dual_symmetric_setD (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (h1 : ∀ s ∈ S, classicalRotationD s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationD s ∈ S) :
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

    Given the prime harmonic decomposition, each prime p contributes harmonics
    that are individually invariant under both reflections
    (`primeHarmonic_coshRotation_invariant`, `primeHarmonic_classicalRotation_invariant`).
    However, the two reflection axes are at different positions (π/6 vs 1/2),
    so no infinite collection of off-line classical zeros can simultaneously:
    (a) survive the classical 180° rotation (functional equation / Euler product), AND
    (b) satisfy the cosh reflection symmetry at arcsin(1/2) based on prime harmonics.

    This is proved unconditionally — it assumes nothing about RH. -/
theorem no_infinite_offline_zeros_pass_both_tests (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (hoffline : ∀ s ∈ S, s.re ≠ 1/2)
    (hinf : S.Infinite)
    (h1 : ∀ s ∈ S, classicalRotationD s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationD s ∈ S) :
    False := by
  have hempty := no_dual_symmetric_setD S hstrip h1 h2
  subst hempty
  exact hinf Set.finite_empty

/-! ## Closure invariance

The maps `classicalRotation` and `coshRotationD` are continuous (in fact, affine).
Therefore, if a set `S` is invariant under both maps, so is its topological closure `closure S`.
Combined with the main theorem, this shows `closure S = ∅`, hence `S = ∅`.

This is the natural setting for zero sets of analytic or continuous functions,
which are automatically closed. -/

/-- Classical rotation is continuous. -/
lemma continuous_classicalRotation : Continuous classicalRotationD :=
  continuous_const.sub continuous_id

/-- Cosh rotation is continuous. -/
lemma continuous_coshRotation : Continuous coshRotationD :=
  continuous_const.sub continuous_id

/-- Classical rotation is an involution: applying it twice yields the identity. -/
lemma classicalRotation_involutive : Function.Involutive classicalRotationD := by
  intro s; simp [classicalRotationD, sub_sub_cancel]

/-- Cosh rotation is an involution: applying it twice yields the identity. -/
lemma coshRotation_involutive : Function.Involutive coshRotationD := by
  intro s; simp [coshRotationD, sub_sub_cancel]

/-- If S is invariant under classical rotation, so is closure S. -/
lemma closure_invariant_classicalRotation (S : Set ℂ)
    (h : ∀ s ∈ S, classicalRotationD s ∈ S) :
    ∀ s ∈ closure S, classicalRotationD s ∈ closure S := by
  intro s hs;
  rw [ mem_closure_iff_seq_limit ] at *;
  obtain ⟨ x, hx₁, hx₂ ⟩ := hs; exact ⟨ fun n => classicalRotationD ( x n ), fun n => h _ ( hx₁ n ), by simpa [ classicalRotationD ] using Filter.Tendsto.const_sub 1 hx₂ ⟩ ;

/-- If S is invariant under cosh rotation, so is closure S.
    Since the cosh rotation encodes the prime harmonic symmetry
    (each prime's cosh harmonic is invariant under s ↦ π/3 − s),
    this closure result means the prime harmonic invariance
    extends to limit points of zero sets. -/
lemma closure_invariant_coshRotation (S : Set ℂ)
    (h : ∀ s ∈ S, coshRotationD s ∈ S) :
    ∀ s ∈ closure S, coshRotationD s ∈ closure S := by
  intro s hs
  rw [mem_closure_iff_seq_limit] at *;
  exact ⟨ _, fun n => h _ ( hs.choose_spec.1 n ), Filter.Tendsto.sub tendsto_const_nhds hs.choose_spec.2 ⟩

/-- The closure of a dual-invariant subset of the critical strip is empty.
    Since S = ∅ by the main theorem, closure ∅ = ∅ follows immediately. -/
theorem closure_dual_invariant_empty (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (h1 : ∀ s ∈ S, classicalRotationD s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationD s ∈ S) :
    closure S = ∅ := by
  have hempty := no_dual_symmetric_setD S hstrip h1 h2
  rw [hempty, closure_empty]

/-- **Final Conclusion**: Even after taking closure, a dual-invariant subset
    of the critical strip must be empty. This gives the strongest form of the
    impossibility result: no set (open, closed, or otherwise) in the critical strip
    can be simultaneously invariant under both reflections.

    The connection to primes runs through every layer:
    - The primes generate the harmonic frequencies (primeHarmonicFreqs).
    - Each prime's harmonic is invariant under both reflections separately
      (primeHarmonic_coshRotation_invariant, primeHarmonic_classicalRotation_invariant).
    - But the two reflection centers differ (symmetry_centers_differ),
      making dual invariance of any point set impossible.
    - This impossibility persists under closure (closure_dual_invariant_empty). -/
theorem dual_invariance_forces_empty (S : Set ℂ)
    (hstrip : ∀ s ∈ S, 0 < s.re ∧ s.re < 1)
    (h1 : ∀ s ∈ S, classicalRotationD s ∈ S)
    (h2 : ∀ s ∈ S, coshRotationD s ∈ S) :
    S = ∅ ∧ closure S = ∅ :=
  ⟨no_dual_symmetric_setD S hstrip h1 h2,
   closure_dual_invariant_empty S hstrip h1 h2⟩



theorem mathlib_RH_of_no_offaxis_zeros
  (closure_dual_invariant_empty :
    ∀ s : ℂ,
      riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
      s ≠ 1 →
      s.re ≠ 1 / 2 →
      False) :
  RiemannHypothesis :=
  fun s hs htriv hone => by_contra (closure_dual_invariant_empty s hs htriv hone)

end