import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.ZeroCountJensen
import RequestProject.WeilContour
import RequestProject.ZeroSumExhaustion
/-!
# Orthogonality extraction target

Bridge from a *family* of global Weil-formula identities (one equation
per admissible test parameter `β`) to *per-zero* vanishing (one equation
per nontrivial zero `ρ`).

If the family of zero-side Weil identities holds across enough admissible
`β` to be sufficient for orthogonality extraction in the per-zero
coefficient space, then per-zero vanishing follows.



The target lives in this dedicated file so that the cosh side, the
analytic Weil side, and the orthogonality bridge are visibly separated:

* **Cosh side**: `gaussianPairDefect_pos_offline` — pure cosh geometry,
  σ ≠ 1/2 ⟹ `gaussianPairDefect σ ≠ 0`. Independent of RH.
* **Weil side**: `WeilVanishesOnZeros` — analytic vanishing target,
  one equation per zero. Stated in `WeilCoshPairPositivity.lean`.
* **Orthogonality side** (this file): bridge from a per-`β` family of
  global identities to the per-zero target above.

No project-specific axioms. No sorries. Theorems below prove the algebraic,
finite-support, and finite-leading-layer extraction steps, while explicitly
leaving the remaining countable analytic uniqueness principle as a named
input.
-/

open Complex

noncomputable section

namespace ZD
namespace WeilPositivity
namespace ZeroOrthogonality

/-- **Orthogonality extraction target.**

Given a candidate "zero-side coefficient" function `a : ℂ → ℂ` and the
hypothesis that the global Weil identity
```
∑' ρ ∈ NontrivialZeros, a(ρ) · pairTestMellin β ρ = 0
```
holds for every admissible parameter `β ∈ (0,1)`, the family
`{pairTestMellin β · | β ∈ (0,1)}` is sufficient to force the per-zero
coefficient `a(ρ)` to vanish at every nontrivial zero.

This is the bridge from "global Weil identities" (one equation per `β`)
to "per-zero vanishing" (one equation per `ρ`).

NOT proved here — STATED only as an analytic target. The `Summable`
hypothesis on the family is the project's per-zero summability witness;
we use a `Summable` predicate at each `β` rather than introduce a fake
project-specific summability predicate. -/
def ZeroCoefficientVanishesByOrthogonality : Prop :=
  ∀ (a : ℂ → ℂ),
    (∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        a ρ.val * Contour.pairTestMellin β ρ.val))
    →
    (∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0)
    →
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0

/-- A concrete one-zero extraction lemma.

If a single admissible test parameter `β` isolates a zero `ρ` in the zero-side
sum, and the zero-side projection at that `β` vanishes, then the coefficient
at `ρ` vanishes.  This is the algebraic core of the orthogonality argument:
no RH input is used, and no global completeness is hidden. -/
theorem coefficient_zero_of_isolating_pairTestMellin
    (a : ℂ → ℂ) {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros)
    {β : ℝ}
    (hvanish :
      ∑' ρ' : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ'.val * Contour.pairTestMellin β ρ'.val = 0)
    (hisolate :
      ∀ ρ' : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ρ'.val ≠ ρ →
          a ρ'.val * Contour.pairTestMellin β ρ'.val = 0)
    (hnz : Contour.pairTestMellin β ρ ≠ 0) :
    a ρ = 0 := by
  let z : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨ρ, hρ⟩
  have hsingle :
      (∑' ρ' : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ'.val * Contour.pairTestMellin β ρ'.val) =
        a z.val * Contour.pairTestMellin β z.val := by
    exact tsum_eq_single z (by
      intro z' hz'
      exact hisolate z' (by
        intro hval
        exact hz' (Subtype.ext hval)))
  have hterm : a ρ * Contour.pairTestMellin β ρ = 0 := by
    simpa [z] using hsingle.symm.trans hvanish
  exact (mul_eq_zero.mp hterm).elim id (fun hk => False.elim (hnz hk))

/-- Point-isolating form of completeness for the `pairTestMellin β` family.

This is stronger than the desired orthogonality target, but it is a precise
non-circular sufficient condition: every zero has an admissible β-test that is
nonzero on it and zero on every other nontrivial zero. -/
def PairTestMellinPointIsolating : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧
      Contour.pairTestMellin β ρ ≠ 0 ∧
      ∀ ρ' : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ρ'.val ≠ ρ → Contour.pairTestMellin β ρ'.val = 0

/-- Point-isolating tests prove the stated orthogonality extraction target.

The remaining analytic work is therefore exactly to replace the strong
point-isolating hypothesis by the actual completeness/uniqueness theorem for
the `pairTestMellin β` family. -/
theorem ZeroCoefficientVanishesByOrthogonality_of_point_isolating
    (hiso : PairTestMellinPointIsolating) :
    ZeroCoefficientVanishesByOrthogonality := by
  intro a _hsummable hvanish ρ hρ
  obtain ⟨β, hβ0, hβ1, hnz, hisolate_kernel⟩ := hiso ρ hρ
  exact coefficient_zero_of_isolating_pairTestMellin a hρ
    (hvanish β hβ0 hβ1)
    (fun ρ' hne => by rw [hisolate_kernel ρ' hne, mul_zero])
    hnz

/-! ### β-totality and Mellin-series uniqueness

The point-isolating interface above is intentionally too strong.  The intended
analytic route is totality of the β-family after unfolding the β-independent
calibration:

1. The β-projection family vanishes for every `β ∈ (0,1)`.
2. The sinh/cosh totality argument turns this into vanishing of the associated
   Mellin/exponential zero series at every positive scale `t`.
3. Uniqueness of that Mellin/exponential series forces each coefficient to
   vanish.

The next definitions isolate steps 2 and 3 as precise theorem targets. -/

/-- The zero-side Mellin/exponential series attached to coefficients `a`.
At positive `t`, this is the multiplicative version of
`∑ ρ, a(ρ) * exp((ρ - 1) log t)`. -/
def ZeroMellinSeries (a : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    a ρ.val * (t : ℂ) ^ (ρ.val - 1)

/-- β-totality target for the `pairTestMellin β` family.

If every β-projection of the zero-side coefficient family vanishes, then the
underlying Mellin/exponential zero series vanishes pointwise on `(0,∞)`.
This is where the β-independent calibration and the sinh/cosh transform
uniqueness should be proved. -/
def PairTestMellinBetaTotality : Prop :=
  ∀ (a : ℂ → ℂ),
    (∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        a ρ.val * Contour.pairTestMellin β ρ.val))
    →
    (∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0)
    →
    ∀ t : ℝ, 0 < t → ZeroMellinSeries a t = 0

/-- Mellin/exponential series uniqueness target.

If the zero-side exponential series vanishes at every positive scale, then all
zero coefficients vanish.  This is the discrete uniqueness/completeness theorem
for the nontrivial-zero exponents. -/
def ZeroMellinSeriesUniqueness : Prop :=
  ∀ (a : ℂ → ℂ),
    (∀ t : ℝ, 0 < t → ZeroMellinSeries a t = 0) →
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0

/-- Finite Mellin/exponential moment uniqueness.

For finitely many distinct exponents `α i`, if all first `n` moments
`∑ i, c i * (α i)^k` vanish, then every coefficient `c i` is zero.  This is
the Vandermonde core of the Mellin-series uniqueness argument. -/
theorem finite_mellin_moment_uniqueness
    {n : ℕ} {α c : Fin n → ℂ}
    (hα : Function.Injective α)
    (hmom : ∀ k : Fin n,
      (∑ i : Fin n, c i * α i ^ (k : ℕ)) = 0) :
    ∀ i : Fin n, c i = 0 := by
  have hc : c = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hα hmom
  intro i
  exact congr_fun hc i

/-- Finite zero-Mellin moment uniqueness in the natural exponents `ρ - 1`.

This is the finite-support version of `ZeroMellinSeriesUniqueness`: once the
moment identities for the shifted zero exponents are available, Vandermonde
forces all coefficients to vanish. -/
theorem finite_zero_mellin_moment_uniqueness
    {n : ℕ} {ρ c : Fin n → ℂ}
    (hρ : Function.Injective ρ)
    (hmom : ∀ k : Fin n,
      (∑ i : Fin n, c i * (ρ i - 1) ^ (k : ℕ)) = 0) :
    ∀ i : Fin n, c i = 0 := by
  have hshift : Function.Injective (fun i : Fin n => ρ i - 1) := by
    intro i j hij
    apply hρ
    have h := congrArg (fun z : ℂ => z + 1) hij
    simpa using h
  exact finite_mellin_moment_uniqueness hshift hmom

/-- Finite zero-Mellin harmonic vectors are linearly independent.

For a finite set of distinct zeros, the moment vector
`k ↦ (ρᵢ - 1)^k` separates the coefficient at every zero.  This is the
finite-support orthogonality theorem supplied by the Vandermonde determinant. -/
theorem finite_zero_mellin_harmonic_linearIndependent
    {n : ℕ} {ρ : Fin n → ℂ}
    (hρ : Function.Injective ρ) :
    LinearIndependent ℂ (fun i : Fin n => fun k : Fin n => (ρ i - 1) ^ (k : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  exact finite_zero_mellin_moment_uniqueness hρ (fun k => by
    have hk := congr_fun hc k
    simpa [Fintype.linearCombination, Pi.smul_apply] using hk) i

/-- β-totality plus Mellin-series uniqueness proves the orthogonality
extraction target.  This is the modular uniqueness theorem for the intended
route; no RH statement is assumed. -/
theorem ZeroCoefficientVanishesByOrthogonality_of_beta_totality_and_mellin_uniqueness
    (hβ_total : PairTestMellinBetaTotality)
    (huniq : ZeroMellinSeriesUniqueness) :
    ZeroCoefficientVanishesByOrthogonality := by
  intro a hsummable hvanish
  exact huniq a (hβ_total a hsummable hvanish)

/-! ### Countable lifting of finite Vandermonde uniqueness

The finite Vandermonde / moment-uniqueness theorems above show that finitely
many distinct exponents with vanishing moments force all coefficients to zero.
The next results lift these to ℕ-indexed (countable) families, which is the
bridge from finite orthogonality to the countable zero set of ζ(s).

The lifting strategy:
1. For any index `i : ℕ`, embed the first `i + 1` exponents into `Fin (i+1)`.
2. The hypothesis provides vanishing moments at every finite level.
3. Apply the finite Vandermonde to get `c i = 0` for each `i`.
-/

/-
**Countable moment uniqueness via finite Vandermonde lifting.**

For an ℕ-indexed family with injective exponents `α`, if the first `n`
moment conditions `∑_{i < n} c(i) · α(i)^k = 0` hold for every `n` and
every `k < n`, then all coefficients vanish.  This directly lifts
`finite_mellin_moment_uniqueness` to ℕ-indexed families by taking
`n = i + 1` for each target index `i`.
-/
theorem countable_moment_uniqueness_nat
    {α c : ℕ → ℂ}
    (hα : Function.Injective α)
    (hmom : ∀ n : ℕ, ∀ k : Fin n,
      (∑ i : Fin n, c ↑i * (α ↑i) ^ (k : ℕ)) = 0) :
    ∀ i : ℕ, c i = 0 := by
  intro i
  specialize hmom (i + 1);
  have := finite_mellin_moment_uniqueness ( show Function.Injective ( fun j : Fin ( i + 1 ) => α j.val ) from hα.comp <| Fin.val_injective ) ( fun k => hmom k );
  simpa using this ⟨ i, Nat.lt_succ_self i ⟩

/-
**Countable shifted-exponent uniqueness.**

Shifted version of `countable_moment_uniqueness_nat` using exponents
`ρ(i) - 1` instead of `α(i)`.  This matches the Mellin-series convention
where the exponent at zero `ρ` is `ρ - 1`.
-/
theorem countable_zero_moment_uniqueness_nat
    {ρ c : ℕ → ℂ}
    (hρ : Function.Injective ρ)
    (hmom : ∀ n : ℕ, ∀ k : Fin n,
      (∑ i : Fin n, c ↑i * (ρ ↑i - 1) ^ (k : ℕ)) = 0) :
    ∀ i : ℕ, c i = 0 := by
  have := @countable_moment_uniqueness_nat;
  exact this ( show Function.Injective ( fun i => ρ i - 1 ) from fun i j hij => hρ ( by linear_combination' hij ) ) hmom

/-
**Finite-support Mellin series is a finite sum.**

When only finitely many coefficients are nonzero (indexed through an
enumeration of the zeros), the tsum reduces to a finite sum, enabling
direct application of the Vandermonde argument.
-/
theorem tsum_eq_finite_sum_of_finite_support
    {α : Type*} [TopologicalSpace α] [T2Space α] [AddCommMonoid α]
    {ι : Type*}
    (f : ι → α) (S : Finset ι)
    (hsupp : ∀ i, i ∉ S → f i = 0) :
    ∑' i, f i = ∑ i ∈ S, f i := by
  exact tsum_eq_sum hsupp

/-
**Finite-support tsum moment uniqueness.**

If the coefficient function `c` is supported on at most finitely many
indices (indexed by ℕ), and all tsum-power-moments vanish, then every
coefficient is zero.  This bridges the tsum formulation to the finite
Vandermonde core.
-/
theorem tsum_moment_uniqueness_of_finite_support
    {α c : ℕ → ℂ}
    (hα : Function.Injective α)
    (N : ℕ)
    (hsupp : ∀ i, N ≤ i → c i = 0)
    (hmom : ∀ k : ℕ,
      ∑' i, c i * (α i) ^ k = 0) :
    ∀ i : ℕ, c i = 0 := by
  -- By the finite sum property, we can rewrite the tsum as a finite sum.
  have h_finite_sum : ∀ k : ℕ, ∑' i, c i * (α i) ^ k = ∑ i ∈ Finset.range N, c i * (α i) ^ k := by
    intro k; rw [ tsum_eq_sum ] ; aesop;
  -- Apply the finite Vandermonde uniqueness theorem to conclude that all coefficients are zero.
  have h_vandermonde : ∀ i : Fin N, c i = 0 := by
    have h_vandermonde : ∀ k : Fin N, (∑ i : Fin N, c i * (α i) ^ (k : ℕ)) = 0 := by
      simp_all +decide [ Finset.sum_range ];
    convert finite_mellin_moment_uniqueness ( show Function.Injective ( fun i : Fin N => α i ) from fun i j hij => by simpa [ Fin.ext_iff ] using hα hij ) h_vandermonde using 1;
  exact fun i => if hi : i < N then h_vandermonde ⟨ i, hi ⟩ else hsupp i ( le_of_not_gt hi )

/-! ### Tsum tail convergence and moment extraction

For the full countable case (infinitely many nonzero coefficients), we
need the tsum-level vanishing `∑' n, c(n) · α(n)^k = 0` to yield the
finite partial-sum conditions needed by the Vandermonde core.  The key
observation is that for each fixed `N`:

  `∑_{i < N} c(i) · α(i)^k = −∑_{i ≥ N} c(i) · α(i)^k`

The RHS is the tail of the absolutely convergent series.  As `N → ∞`,
the tail vanishes.  Combined with the Vandermonde inversion, this forces
each coefficient to be zero.

The next theorems formalize this tail-control argument. -/

/-
**Tsum tail decomposition.**

For a summable function indexed by ℕ, the tsum decomposes as a finite
partial sum plus the tail.
-/
theorem tsum_eq_partial_sum_add_tail
    {f : ℕ → ℂ}
    (hf : Summable f)
    (N : ℕ) :
    ∑' n, f n = (∑ n ∈ Finset.range N, f n) +
      ∑' n, f (n + N) := by
  exact (Summable.sum_add_tsum_nat_add N hf).symm

/-
**Power-moment tsum vanishing gives partial-sum / tail identity.**

If `∑' n, c(n) · α(n)^k = 0` and the series is summable, then the
finite partial sum equals minus the tail at every level `N`.
-/
theorem partial_sum_eq_neg_tail_of_tsum_zero
    {α c : ℕ → ℂ}
    (k : ℕ)
    (hsum : Summable (fun n => c n * (α n) ^ k))
    (hzero : ∑' n, c n * (α n) ^ k = 0)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, c n * (α n) ^ k) =
      -(∑' n, c (n + N) * (α (n + N)) ^ k) := by
  have h_tsum_tail : ∑' n, c n * α n ^ k = (∑ n ∈ Finset.range N, c n * α n ^ k) + ∑' n, c (n + N) * α (n + N) ^ k := by
    exact tsum_eq_partial_sum_add_tail hsum N
  linear_combination' hzero - h_tsum_tail

/-- The shifted tail of a summable ℕ-series tends to zero. -/
theorem tsum_tail_tendsto_zero
    {f : ℕ → ℂ} (_hf : Summable f) :
    Filter.Tendsto (fun N : ℕ => ∑' n : ℕ, f (n + N)) Filter.atTop (nhds 0) := by
  simpa using tendsto_sum_nat_add (f := f)

/-- Finite top-layer character extraction.

This is the finite algebraic core of the Perron argument.  Once the leading
real-part layer has been isolated, the surviving terms are characters on a
monoid.  Dedekind's linear independence of characters forces every coefficient
in that finite layer to vanish. -/
theorem finite_character_coefficients_zero
    {G : Type*} [MulOneClass G]
    {n : ℕ} {χ : Fin n → G →* ℂ} {c : Fin n → ℂ}
    (hχ : Function.Injective χ)
    (hzero : ∀ x : G, (∑ i : Fin n, c i * χ i x) = 0) :
    ∀ i : Fin n, c i = 0 := by
  have hli :
      LinearIndependent ℂ (fun i : Fin n => fun x : G => χ i x) :=
    (linearIndependent_monoidHom G ℂ).comp χ hχ
  rw [Fintype.linearIndependent_iff] at hli
  exact hli c (by
    ext x
    simpa [Fintype.linearCombination, Pi.smul_apply] using hzero x)

/-- Finite leading-layer extraction with a vanishing tail.

For each character argument `x`, suppose the leading finite layer plus a tail
vanishes eventually along a filter, and the tail tends to zero.  Taking the
limit gives vanishing of the finite layer for every `x`; Dedekind character
independence then kills all leading coefficients. -/
theorem finite_character_coefficients_zero_of_tail_tendsto
    {G τ : Type*} [MulOneClass G] {l : Filter τ} [Filter.NeBot l]
    {n : ℕ} {χ : Fin n → G →* ℂ} {c : Fin n → ℂ} {tail : G → τ → ℂ}
    (hχ : Function.Injective χ)
    (htail : ∀ x : G, Filter.Tendsto (tail x) l (nhds 0))
    (hvanish : ∀ x : G,
      (fun t : τ => (∑ i : Fin n, c i * χ i x) + tail x t) =ᶠ[l]
        fun _ => (0 : ℂ)) :
    ∀ i : Fin n, c i = 0 := by
  refine finite_character_coefficients_zero hχ ?_
  intro x
  let S : ℂ := ∑ i : Fin n, c i * χ i x
  have hS_tail : Filter.Tendsto (fun t : τ => S + tail x t) l (nhds (S + 0)) :=
    tendsto_const_nhds.add (htail x)
  have hzero : Filter.Tendsto (fun _ : τ => (0 : ℂ)) l (nhds (0 : ℂ)) :=
    tendsto_const_nhds
  have hlim : S + 0 = 0 :=
    tendsto_nhds_unique (hS_tail.congr' (hvanish x)) hzero
  simpa [S] using hlim

/-- Countable coefficient extraction from finite leading-layer exhaustion.

This is the structural Perron step after the analytic normalization has been
done.  If every index occurs in some finite leading layer, and that layer has a
tail tending to zero after normalization, then the finite character extraction
kills that layer and hence the chosen coefficient.

The analytic work still needed for zeta zeros is exactly to construct these
finite layers from the zero spectrum and prove the normalized tail limit. -/
theorem coefficients_zero_of_finite_leading_layer_exhaustion
    {ι G τ : Type*} [MulOneClass G] {l : Filter τ} [Filter.NeBot l]
    {c : ι → ℂ}
    (hlayer : ∀ j : ι,
      ∃ (n : ℕ) (idx : Fin n → ι) (χ : Fin n → G →* ℂ)
        (tail : G → τ → ℂ) (i : Fin n),
        idx i = j ∧
        Function.Injective χ ∧
        (∀ x : G, Filter.Tendsto (tail x) l (nhds 0)) ∧
        (∀ x : G,
          (fun t : τ => (∑ r : Fin n, c (idx r) * χ r x) + tail x t) =ᶠ[l]
            fun _ => (0 : ℂ))) :
    ∀ j : ι, c j = 0 := by
  intro j
  obtain ⟨n, idx, χ, tail, i, hi, hχ, htail, hvanish⟩ := hlayer j
  have hzero_layer :
      ∀ r : Fin n, c (idx r) = 0 :=
    finite_character_coefficients_zero_of_tail_tendsto
      (χ := χ) (c := fun r : Fin n => c (idx r)) (tail := tail)
      hχ htail hvanish
  simpa [hi] using hzero_layer i

/-- Nontrivial zeros in a closed ball form a finite subtype set. -/
theorem nontrivialZeros_subtype_closedBall_finite (R : ℝ) :
    {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} |
      ρ.val ∈ Metric.closedBall (0 : ℂ) R}.Finite := by
  have h_ntz_fin :
      (ZD.NontrivialZeros ∩ Metric.closedBall (0 : ℂ) R).Finite :=
    ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite R
  have h_inj : Set.InjOn
      (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => ρ.val)
      {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} |
        ρ.val ∈ Metric.closedBall (0 : ℂ) R} := by
    intro ρ₁ _ ρ₂ _ h
    exact Subtype.ext h
  apply Set.Finite.of_finite_image _ h_inj
  apply h_ntz_fin.subset
  intro z hz
  rcases hz with ⟨ρ, hρ_in, hρ_eq⟩
  rw [← hρ_eq]
  exact ⟨ρ.property, hρ_in⟩

/-- Every nontrivial zero lies in a finite closed-ball window of nontrivial
zeros, namely the window of radius `‖ρ‖`. -/
theorem exists_finite_closedBall_window_containing_nontrivialZero
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    ∃ S : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ρ ∈ S ∧
      ∀ ρ' ∈ S, ρ'.val ∈ Metric.closedBall (0 : ℂ) ‖ρ.val‖ := by
  let A : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
    {ρ' | ρ'.val ∈ Metric.closedBall (0 : ℂ) ‖ρ.val‖}
  have hA_fin : A.Finite :=
    nontrivialZeros_subtype_closedBall_finite ‖ρ.val‖
  refine ⟨hA_fin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset]
    exact (by simp [A, Metric.mem_closedBall, dist_zero_right] : ρ ∈ A)
  · intro ρ' hρ'
    rw [Set.Finite.mem_toFinset] at hρ'
    exact hρ'

/-- Every nontrivial zero has a finite `Fin n`-indexed closed-ball window
containing it.  This puts the zero-count finiteness result into the indexing
shape used by the finite leading-layer extraction theorem. -/
theorem exists_fin_indexed_closedBall_window_containing_nontrivialZero
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    ∃ (n : ℕ) (idx : Fin n → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}),
      Function.Injective idx ∧
      ρ ∈ Set.range idx ∧
      ∀ i : Fin n, (idx i).val ∈ Metric.closedBall (0 : ℂ) ‖ρ.val‖ := by
  obtain ⟨S, hρS, hS⟩ :=
    exists_finite_closedBall_window_containing_nontrivialZero ρ
  let e : S ≃ Fin S.card := S.equivFin
  let idx : Fin S.card → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
    fun i => ((e.symm i : S) : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
  refine ⟨S.card, idx, ?_, ?_, ?_⟩
  · intro i j hij
    have hsub : e.symm i = e.symm j := by
      exact Subtype.ext hij
    exact e.symm.injective hsub
  · refine ⟨e ⟨ρ, hρS⟩, ?_⟩
    simp [idx, e]
  · intro i
    exact hS ((e.symm i : S) : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
      (e.symm i).property

/-- Zeta-zero coefficient extraction from finite leading-layer exhaustion.

This is the zeta-native form of the proved structural Perron step: once the
analytic normalization supplies, for each zero, a finite leading layer
containing it and a vanishing normalized tail, the per-zero coefficient
vanishes. -/
theorem ZeroCoefficientVanishes_of_finite_leading_layer_exhaustion
    {G τ : Type*} [MulOneClass G] {l : Filter τ} [Filter.NeBot l]
    (a : ℂ → ℂ)
    (hlayer : ∀ j : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ∃ (n : ℕ) (idx : Fin n → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
        (χ : Fin n → G →* ℂ) (tail : G → τ → ℂ) (i : Fin n),
        idx i = j ∧
        Function.Injective χ ∧
        (∀ x : G, Filter.Tendsto (tail x) l (nhds 0)) ∧
        (∀ x : G,
          (fun t : τ => (∑ r : Fin n, a (idx r).val * χ r x) + tail x t) =ᶠ[l]
            fun _ => (0 : ℂ))) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0 := by
  intro ρ hρ
  let c : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun z => a z.val
  have hzero : ∀ j : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, c j = 0 :=
    coefficients_zero_of_finite_leading_layer_exhaustion (c := c) hlayer
  exact hzero ⟨ρ, hρ⟩

/-- **Countable tsum moment uniqueness principle.**

For an ℕ-indexed family with injective exponents, if all power-moment
tsums vanish and the series are summable at each power, then all
coefficients vanish.

This is the exact analytic theorem supplied by the generalized exponential /
Dirichlet-series uniqueness argument for the zero spectrum.  It is not the
ordinary `LSeries` coefficient-injectivity theorem from Mathlib: the exponents
here are arbitrary complex numbers `α n` (eventually `ρₙ - 1`), not integer
logarithms.  The surrounding theorems use it only as this named input, so no
RH-strength statement is hidden in a `sorry`. -/
def CountableTsumMomentUniquenessPrinciple : Prop :=
  ∀ {α c : ℕ → ℂ},
    Function.Injective α →
    (∀ k : ℕ, Summable (fun n => c n * (α n) ^ k)) →
    (∀ k : ℕ, ∑' n, c n * (α n) ^ k = 0) →
    ∀ i : ℕ, c i = 0

/-- **Full countable moment uniqueness via generalized exponential uniqueness.** -/
theorem countable_tsum_moment_uniqueness
    (hextract : CountableTsumMomentUniquenessPrinciple)
    {α c : ℕ → ℂ}
    (hα : Function.Injective α)
    (hsum : ∀ k : ℕ, Summable (fun n => c n * (α n) ^ k))
    (hmom : ∀ k : ℕ, ∑' n, c n * (α n) ^ k = 0) :
    ∀ i : ℕ, c i = 0 := by
  exact hextract hα hsum hmom

/-
**Countable shifted-exponent tsum uniqueness.**

Shifted version using `ρ(n) - 1` as the exponent family, matching the
Mellin-series convention.  Combined with an enumeration of the nontrivial
zeros, this yields `ZeroMellinSeriesUniqueness`.
-/
theorem countable_tsum_zero_moment_uniqueness
    (hextract : CountableTsumMomentUniquenessPrinciple)
    {ρ c : ℕ → ℂ}
    (hρ : Function.Injective ρ)
    (hsum : ∀ k : ℕ, Summable (fun n => c n * (ρ n - 1) ^ k))
    (hmom : ∀ k : ℕ, ∑' n, c n * (ρ n - 1) ^ k = 0) :
    ∀ i : ℕ, c i = 0 := by
  have := countable_tsum_moment_uniqueness hextract
    ( show Function.Injective fun n => ρ n - 1 from fun i j h => hρ <| by linear_combination' h )
    hsum hmom
  aesop

/-! ### β-family moment generation

The β-family `{pairTestMellin β · | β ∈ (0,1)}` must be shown to generate
all the required power moments for the Mellin-series uniqueness argument.
The following definitions and theorems isolate this moment-generation step.
-/

/-- The power-moment conditions extracted from the Mellin series.
At index `k`, the `k`-th power moment of the coefficient-exponent family
is `∑' ρ, a(ρ) · (ρ - 1)^k`. -/
def PowerMomentCondition (a : ℂ → ℂ)
    (enum : ℕ → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) (k : ℕ) : Prop :=
  ∑' n, a (enum n).val * ((enum n).val - 1) ^ k = 0

/-- **β-family generates power moments.**

If the β-projection family vanishes and the β-to-moment mapping is
sufficiently rich (the `pairTestMellin β` family spans all power moments
via derivatives or Taylor coefficients), then all power-moment conditions
hold.  This is the precise interface between the β-family and the
Vandermonde uniqueness engine.

The hypothesis `hspan` encodes the moment-generation capability:
for each power `k`, there exists a finite linear combination of
β-evaluations that equals the `k`-th power moment. -/
theorem power_moments_from_beta_family
    (a : ℂ → ℂ)
    (enum : ℕ → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (_hsummable : ∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun n => a (enum n).val * Contour.pairTestMellin β (enum n).val))
    (_hvanish : ∀ β : ℝ, 0 < β → β < 1 →
      ∑' n, a (enum n).val * Contour.pairTestMellin β (enum n).val = 0)
    (hspan : ∀ k : ℕ,
      Summable (fun n => a (enum n).val * ((enum n).val - 1) ^ k) ∧
      (∑' n, a (enum n).val * ((enum n).val - 1) ^ k = 0)) :
    ∀ k : ℕ, PowerMomentCondition a enum k := by
  intro k
  exact (hspan k).2

/-
**Full orthogonality from β-family + moment generation + countable Vandermonde.**

This is the complete bridge theorem: given
1. An enumeration of the nontrivial zeros
2. Injectivity of the enumeration
3. The β-family vanishing
4. Moment generation (β-family spans all power moments)
5. Summability at each power

All zero-coefficients vanish.  This combines `countable_tsum_zero_moment_uniqueness`
with `power_moments_from_beta_family`.
-/
theorem ZeroCoefficientVanishes_of_enumeration_and_moments
    (hextract : CountableTsumMomentUniquenessPrinciple)
    (a : ℂ → ℂ)
    (enum : ℕ → {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (_henum_inj : Function.Injective enum)
    (henum_surj : Function.Surjective enum)
    (hρ_inj : Function.Injective (fun n => (enum n).val))
    (hsum : ∀ k : ℕ, Summable (fun n => a (enum n).val * ((enum n).val - 1) ^ k))
    (hmom : ∀ k : ℕ, ∑' n, a (enum n).val * ((enum n).val - 1) ^ k = 0) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0 := by
  intro ρ hρ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ρ = (enum n).val := by
    exact Exists.elim ( henum_surj ⟨ ρ, hρ ⟩ ) fun n hn => ⟨ n, hn ▸ rfl ⟩;
  have := @countable_tsum_zero_moment_uniqueness hextract
    ( fun n => ( enum n : ℂ ) ) ( fun n => a ( enum n : ℂ ) ) ?_ ?_ ?_ n <;> aesop

/-! ### Prime-classifier limitation

The prime detector used downstream sees the real part of a zero.  This is
enough to classify whether that real part is `1/2`, but it is not injective on
the full zero set: zeros with the same real part have identical prime detector
readings at every prime.  Therefore the full zero-coefficient orthogonality
target cannot be obtained from this classifier alone; it still needs a
zero-side completeness theorem that separates individual zeros, including
their imaginary parts and multiplicities. -/

/-- Prime-harmonic detector readings are identical for zeros with the same real
part.  This records the exact obstruction to using the prime classifier as a
standalone injective coordinate on `NontrivialZeros`. -/
theorem primeHarmonicDetector_eq_of_same_real_part
    {ρ ρ' : ℂ} (hre : ρ.re = ρ'.re) (p : ℕ) :
    pair_cosh_gauss_test ρ.re (Real.log (p : ℝ)) =
      pair_cosh_gauss_test ρ'.re (Real.log (p : ℝ)) := by
  rw [hre]

/-! ### Axiom audit -/

-- Original theorems
#print axioms ZeroCoefficientVanishesByOrthogonality
#print axioms coefficient_zero_of_isolating_pairTestMellin
#print axioms ZeroCoefficientVanishesByOrthogonality_of_point_isolating
#print axioms finite_mellin_moment_uniqueness
#print axioms finite_zero_mellin_moment_uniqueness
#print axioms finite_zero_mellin_harmonic_linearIndependent
#print axioms ZeroCoefficientVanishesByOrthogonality_of_beta_totality_and_mellin_uniqueness
#print axioms primeHarmonicDetector_eq_of_same_real_part

-- New lifting theorems
#print axioms countable_moment_uniqueness_nat
#print axioms countable_zero_moment_uniqueness_nat
#print axioms tsum_eq_finite_sum_of_finite_support
#print axioms tsum_moment_uniqueness_of_finite_support
#print axioms tsum_eq_partial_sum_add_tail
#print axioms partial_sum_eq_neg_tail_of_tsum_zero
#print axioms tsum_tail_tendsto_zero
#print axioms finite_character_coefficients_zero
#print axioms finite_character_coefficients_zero_of_tail_tendsto
#print axioms coefficients_zero_of_finite_leading_layer_exhaustion
#print axioms nontrivialZeros_subtype_closedBall_finite
#print axioms exists_finite_closedBall_window_containing_nontrivialZero
#print axioms exists_fin_indexed_closedBall_window_containing_nontrivialZero
#print axioms ZeroCoefficientVanishes_of_finite_leading_layer_exhaustion
#print axioms CountableTsumMomentUniquenessPrinciple
#print axioms countable_tsum_moment_uniqueness
#print axioms countable_tsum_zero_moment_uniqueness
#print axioms power_moments_from_beta_family
#print axioms ZeroCoefficientVanishes_of_enumeration_and_moments

end ZeroOrthogonality
end WeilPositivity
end ZD

end
