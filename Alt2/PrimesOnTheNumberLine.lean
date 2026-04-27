/-
# Unconditional Truths: Primes, Harmonics, and the Zeros of Zeta
This file formalizes a chain of unconditional results establishing:
1. **The number line exists unconditionally** — ℝ is a complete linearly ordered field.
2. **Prime placement is canonical and unconditional** — the primes embed into ℝ via
   the unique ordered-field embedding ℕ ↪ ℝ, and there are infinitely many of them.
3. **Primes generate unconditional harmonics** — the prime harmonic series ∑ 1/p diverges,
   while the Euler product ζ(s) = ∏_p (1 - p^{-s})⁻¹ converges for Re(s) > 1,
   revealing the harmonic structure primes impose on the zeta function.
4. **Classical zeros control prime placement** — the von Mangoldt function Λ encodes
   prime locations, the identity Λ * ζ = log ties prime placement to the analytic
   structure of ζ, and the non-vanishing ζ(s) ≠ 0 for Re(s) ≥ 1 (the classical
   zero-free region) is the key unconditional fact that controls prime distribution.
All results here are unconditional — no unproven conjectures are assumed.
-/
import Mathlib
open Nat ArithmeticFunction Complex Filter
/-! ## Part I: The Number Line Exists Unconditionally
The real numbers ℝ form a complete linearly ordered field. This is not assumed —
it is constructed (via Cauchy sequences or Dedekind cuts) and proven in Mathlib.
-/
/-- ℝ is a linearly ordered field — the number line has unconditional algebraic structure. -/
noncomputable example : LinearOrder ℝ := inferInstance
/-- ℝ is a field. -/
noncomputable example : Field ℝ := inferInstance
/-- ℝ is order-complete — every nonempty bounded-above set has a supremum.
This is the completeness axiom that distinguishes ℝ from ℚ. -/
noncomputable example : ConditionallyCompleteLinearOrder ℝ := inferInstance
/-- The reals are Archimedean — there is no infinitely large or infinitely small element. -/
theorem number_line_is_archimedean : Archimedean ℝ := inferInstance
/-! ## Part II: Prime Placement on the Number Line is Canonical and Unconditional
The natural numbers — and hence the primes — embed canonically into ℝ via the
unique ring homomorphism ℕ → ℝ. The placement is forced by the ordered field
axioms: there is no choice involved.
-/
/-- The canonical embedding ℕ ↪ ℝ preserves order — prime placement is forced. -/
theorem canonical_embedding_preserves_order : StrictMono (Nat.cast : ℕ → ℝ) :=
  Nat.strictMono_cast
/-- There are infinitely many primes — Euclid's theorem, unconditional. -/
theorem infinitely_many_primes : ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes
/-
PROBLEM
The set of primes, viewed in ℝ, is infinite — primes populate the number line
without bound.
PROVIDED SOLUTION
Use Set.infinite_of_injective_forall_mem with the function (fun p => (Nat.Primes.val p : ℝ)). The injection follows from Nat.cast_injective on ℝ, and the membership from the definition. Alternatively, show this is the image of an infinite set under an injective map. The set of primes in ℕ is infinite by Nat.exists_infinite_primes, and Nat.cast : ℕ → ℝ is injective.
-/
theorem primes_infinite_on_number_line :
    Set.Infinite {x : ℝ | ∃ p : ℕ, Nat.Prime p ∧ (p : ℝ) = x} := by
  exact Set.Infinite.image ( fun p => by aesop ) ( Nat.infinite_setOf_prime )
/-
PROBLEM
Every prime is at a unique, canonical position on the number line.
The embedding is injective — distinct primes land at distinct points.
PROVIDED SOLUTION
Two Nat.Primes with the same cast to ℝ must have the same ℕ value by Nat.cast_injective, hence are equal as subtypes. Use Subtype.val_injective composed with Nat.cast_injective.
-/
theorem prime_placement_injective :
    Function.Injective (fun p : Nat.Primes => (p.val : ℝ)) := by
  intro p q h; cases p; cases q; aesop;
/-! ## Part III: Primes Generate Unconditional Harmonics
The prime harmonic series ∑ 1/p diverges — primes are "dense enough" to generate
an infinite harmonic signal. Meanwhile, the Euler product shows that the Riemann
zeta function ζ(s) for Re(s) > 1 is entirely determined by primes, each prime
contributing a "harmonic factor" (1 - p^{-s})⁻¹.
-/
/-- The prime harmonic series ∑ 1/p diverges — primes generate an unconditionally
divergent harmonic signal on the number line. This is Euler's theorem (1737). -/
theorem prime_harmonics_diverge :
    ¬Summable (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ)) :=
  Nat.Primes.not_summable_one_div
/-- The prime reciprocal power series ∑ p^r converges if and only if r < -1.
This characterizes precisely when the prime harmonics are tamed. -/
theorem prime_harmonics_summability {r : ℝ} :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ r) ↔ r < -1 :=
  Nat.Primes.summable_rpow
/-- The Euler product: ζ(s) = ∏_p (1 - p^{-s})⁻¹ for Re(s) > 1.
Each prime contributes a single harmonic factor to the zeta function.
This is the canonical factorization showing primes generate ζ. -/
theorem primes_generate_zeta_harmonics {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  riemannZeta_eulerProduct_hasProd hs
/-! ## Part IV: Classical Zeros Control Prime Placement
The von Mangoldt function Λ(n) is the analytic encoding of prime placement:
Λ(p^k) = log p and Λ(n) = 0 otherwise. The fundamental identity Λ * ζ = log
ties the prime-locating function to the analytic structure of ζ. The
non-vanishing of ζ on Re(s) ≥ 1 — the classical zero-free region — is the
unconditional fact from which the Prime Number Theorem follows.
-/
/-- The von Mangoldt function detects primes: Λ(p) = log p for every prime p.
This is how prime placement is encoded analytically. -/
theorem vonMangoldt_detects_primes (p : ℕ) (hp : Nat.Prime p) :
    ArithmeticFunction.vonMangoldt p = Real.log p :=
  vonMangoldt_apply_prime hp

/-- A prime is the same arithmetic datum viewed in two compatible ways:
as a canonical point `(p : ℝ)` on the number line, and as a harmonic weight
`log p` recorded by the von Mangoldt function. In this sense, primes are
numbers viewed harmonically. -/
theorem prime_is_number_viewed_as_harmonic (p : ℕ) (hp : Nat.Prime p) :
    ∃ x ω : ℝ,
      x = (p : ℝ) ∧
      ω = Real.log x ∧
      ArithmeticFunction.vonMangoldt p = ω := by
  refine ⟨(p : ℝ), Real.log (p : ℝ), rfl, rfl, ?_⟩
  simpa using vonMangoldt_apply_prime hp
/-- The fundamental identity: Λ * ζ = log.
This says that summing the von Mangoldt function over divisors recovers log:
  ∑_{d | n} Λ(d) = log n.
The zeros of ζ therefore directly control the behavior of Λ — and hence
control where the primes are placed on the number line. -/
theorem vonMangoldt_times_zeta_eq_log :
    ArithmeticFunction.vonMangoldt * ↑ArithmeticFunction.zeta =
      ArithmeticFunction.log :=
  vonMangoldt_mul_zeta
/-- The classical zero-free region: ζ(s) ≠ 0 for Re(s) ≥ 1.
This is the deepest unconditional result here. It means that the zeros of ζ
are confined to the critical strip 0 < Re(s) < 1 (apart from trivial zeros).
This confinement of zeros is what controls prime placement — it is equivalent
to the Prime Number Theorem: π(x) ~ x/log(x).
This is unconditional — no hypothesis on the Riemann Hypothesis is needed. -/
theorem classical_zeros_control_prime_placement (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs
/-- The divisor sum form: ∑_{d | n} Λ(d) = log n.
This is the pointwise form of Λ * ζ = log, making explicit that the
von Mangoldt function — the prime-placement detector — when summed over
divisors, recovers the logarithm unconditionally. -/
theorem prime_placement_divisor_sum (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d = Real.log n :=
  vonMangoldt_sum
/-- The von Mangoldt function is nonneg — prime placement carries positive weight. -/
theorem vonMangoldt_nonneg_everywhere (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n :=
  vonMangoldt_nonneg
/-! ## Summary
We have established an unconditional chain:
1. **ℝ exists** as a complete linearly ordered field (Part I).
2. **Primes embed canonically** into ℝ, with infinitely many at unique positions (Part II).
3. **Primes generate harmonics**: the series ∑ 1/p diverges, and the Euler product
   ζ(s) = ∏_p (1 - p^{-s})⁻¹ converges for Re(s) > 1 (Part III).
4. **Classical zeros control prime placement**: the von Mangoldt function Λ encodes
   primes, the identity Λ * ζ = log ties Λ to ζ, and the non-vanishing
   ζ(s) ≠ 0 for Re(s) ≥ 1 confines all nontrivial zeros to the critical strip,
   unconditionally controlling prime distribution (Part IV).
Every result here is machine-verified, unconditional, and requires no unproven conjectures.
-/
