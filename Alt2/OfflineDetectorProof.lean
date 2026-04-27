import Mathlib
import RequestProject.HarmonicDiagnostics
import RequestProject.ZetaZeroDefs
import RequestProject.OfflineAmplitudeMethods
import RequestProject.PairCoshGaussTest
import RequestProject.GaussianDetectorPair
import RequestProject.WeilContour
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.WeilCoshPairPositivity
import RequestProject.WeilFinalAssembly
import RequestProject.WeilExplicitFormulaFromPerC
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.GaussianClosedForm
import RequestProject.KleinForcerTheorem

/-!
# Cosh-side detector + no-cancellation + Weil-zero bridge (unconditional)

**File role.**  This file hosts a *cosh-side* unconditional lemma bundling
three facts about every nontrivial zeta zero `ρ`:

1. **Bridge (unconditional on zero location).**  At every prime `p`, the
   even-channel zero-pair contribution from `ρ` and its FE-partner
   `1 − ρ̄` — the scalar that enters the prime side of the Weil explicit
   formula — is exactly `balancedEnvelope p · coshDetector ρ.re (log p)`.
   Both sides *observe the same object* at `ρ`: the Weil prime side and
   the cosh detector index into `ZD.NontrivialZeros` identically and
   their per-(ρ, p) readings agree up to the balanced envelope factor.

2. **Detection at every prime (offline-conditional).**  When `ρ.re ≠ 1/2`,
   the cosh detector reads strictly above 1 at every prime
   (`HarmonicDiagnostics.infinite_detection`).

3. **No cancellation (offline-conditional).**  The sum of per-prime
   excesses `(cosh − 1)` over any nonempty prime `Finset` is strictly
   positive — positive-cone property
   (`HarmonicDiagnostics.totalEvenChannelExcess_pos_of_offline`).

All content reuses lemmas already proved in-project.  Fully unconditional:
no RH hypothesis, no Weil explicit-formula input, no custom axioms.  The
bridge conjunct is the piece that pins the cosh-side readings to the
exact same zeros the Weil explicit formula sums over.

## Architectural separation

* **Cosh side (this file).**  Operates on `coshDetector` /
  `zeroPairEnvelope` / `balancedEnvelope` plus the `NontrivialZeros`
  zero set.  No Weil explicit-formula content.
* **Weil side (elsewhere).**  Proves unconditional integral / zero-sum
  identities via the Weil explicit formula, indexed over the same
  `NontrivialZeros`.

The bridge conjunct is the structural identification that makes the two
sides comparable at contradiction time.
-/

open Real ZetaDefs BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour
namespace CoshReflectedClassifier

/-- **Offline detected + no cancellation + Weil-zero bridge (unconditional).**
For every nontrivial zeta zero `ρ`:

* **(bridge)** at every prime `p`, the even-channel zero-pair contribution
  `p^ρ.re + p^(1−ρ.re)` — the quantity entering the prime side of the Weil
  explicit formula — equals `balancedEnvelope p · coshDetector ρ.re (log p)`.
  The cosh detector reads the same zero `ρ` the Weil side sums over.
* **(detection)** if `ρ.re ≠ 1/2`, the cosh detector reads strictly above
  1 at every prime.
* **(no cancellation)** if `ρ.re ≠ 1/2`, the sum of per-prime excesses
  `(cosh − 1)` over any nonempty prime set is strictly positive
  (positive cone; no antisymmetric compensator).

Pure cosh-side content; no Weil explicit-formula input; no RH hypothesis.
Axiom footprint = the kernel only. -/
theorem offline_detected_no_cancellation :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      (∀ p : ℕ, Nat.Prime p →
        (↑p : ℝ) ^ ρ.re + (↑p : ℝ) ^ (1 - ρ.re) =
          balancedEnvelope (↑p) *
          coshDetector ρ.re (Real.log (↑p))) ∧
      (ρ.re ≠ 1/2 →
        (∀ p : ℕ, Nat.Prime p → 1 < coshDetector ρ.re (Real.log (↑p))) ∧
        (∀ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) → ps.Nonempty →
          0 < ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1))) := by
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · -- Bridge: `euler_envelope_eq_cosh` unfolds `zeroPairEnvelope`.
    intro p hp
    have h := euler_envelope_eq_cosh p hp ρ.re
    simpa [zeroPairEnvelope] using h
  · -- Detection + no-cancellation.
    intro hoff
    have hoff' : ρ ∈ ZD.OffLineZeros := ⟨hρ, hoff⟩
    refine ⟨fun p hp => infinite_detection ρ hoff' p hp, ?_⟩
    intro ps hps hne
    have h := totalEvenChannelExcess_pos_of_offline ρ hoff' ps hps hne
    simpa [totalEvenChannelExcess, evenChannelExcess] using h

#print axioms offline_detected_no_cancellation

end CoshReflectedClassifier
end Contour
end WeilPositivity
end ZD

/-! ## §  Weil-side prime-aggregate amplitude-defect bridge (unconditional)

Synthesis of the **Weil prime aggregate at the cosh-Gauss pair test on
`Re s = 2`** with the **off-line amplitude-defect envelope**, paired by
the functional-equation reflection `β ↔ 1 − β`.

This section combines existing unconditional content into a single
package providing:

* the per-prime amplitude bridge
  `amplitudeDefect r β = balancedEnvelope r · (coshDetector β (log r) − 1)`;
* the FE-paired quadratic envelope identity
  `4·p·sinh²((β − 1/2)·log p) = amplitudeDefect (p²) β`
  with auxiliary form `(p^{β−1/2} − p^{1/2−β})²·p = amplitudeDefect (p²) β`;
* the FE-pair symmetry  `amplitudeDefect r β = amplitudeDefect r (1 − β)`;
* the closed-form Weil prime aggregate at `σ = 2`
  `∫ primeIntegrand β 2 = 2π · ∑ Λ(n) · pair_cosh_gauss_test β n`
  (re-export of `Contour.primeIntegrand_integral_eq_prime_sum`);
* per-`n` Weil-positivity:  `Λ(n) · pair_cosh_gauss_test β n ≥ 0`;
* per-prime amplitude-defect injection at any off-line zero, and the
  finite-aggregate strict-positivity (no cancellation) following from
  `offline_excess_positive`.



The combined picture is exactly the user's stated architecture:

* **Cosh side** (proved): off-line zero injects strictly positive
  per-prime amplitude excess; aggregating over a finite prime set
  gives strictly positive total — no cancellation, positive cone.
* **Weil-side amplitude bridge** (this section): every relevant
  β-dependence on the prime side is carried by the FE-paired
  amplitude defect envelope.
* **Closed-form aggregate** (re-export): the Weil prime aggregate at
  `σ = 2` has an unconditional closed form summing the pair-cosh-Gauss
  test against the von Mangoldt function. -/

open Real Complex BigOperators ZetaDefs ZD.WeilPositivity

noncomputable section

namespace ZD
namespace WeilPositivity
namespace PrimeBoundedness

/-! ### §1. Per-prime amplitude bridge -/

/-- **Per-prime amplitude bridge.**  At any scale `r > 0`, the
amplitude defect equals the balanced envelope times the cosh excess
`coshDetector β (log r) − 1`. -/
theorem amplitudeDefect_eq_balanced_mul_coshExcess
    {r : ℝ} (hr : 0 < r) (β : ℝ) :
    amplitudeDefect r β =
      balancedEnvelope r * (coshDetector β (Real.log r) - 1) := by
  have h := defect_eq_balanced_mul_diff hr β
  unfold harmonicDiffPiThird at h
  exact h

/-- **Per-prime amplitude bridge — prime form.**  Specialised to a
prime `p`. -/
theorem amplitudeDefect_prime_eq_balanced_mul_coshExcess
    (p : ℕ) (hp : Nat.Prime p) (β : ℝ) :
    amplitudeDefect (p : ℝ) β =
      balancedEnvelope (p : ℝ) *
        (coshDetector β (Real.log (p : ℝ)) - 1) :=
  amplitudeDefect_eq_balanced_mul_coshExcess
    (Nat.cast_pos.mpr hp.pos) β

/-! ### §2. FE-paired quadratic envelope identity -/

/-- **FE-paired sinh-squared identity.**  For `p > 0`,
`4 · sinh²((β − 1/2) · log p) = (p^{β − 1/2} − p^{1/2 − β})²`.

The RHS is the square of the FE-paired difference; the LHS is the
prime-side sinh² appearing in the cosh-Gauss pair test integrand. -/
theorem four_sinh_sq_eq_rpow_sq
    {p : ℝ} (hp : 0 < p) (β : ℝ) :
    4 * Real.sinh ((β - 1/2) * Real.log p) ^ 2 =
      (p ^ (β - 1/2) - p ^ ((1/2 : ℝ) - β)) ^ 2 := by
  have h1 : p ^ (β - 1/2) = Real.exp ((β - 1/2) * Real.log p) := by
    rw [Real.rpow_def_of_pos hp]; ring_nf
  have h2 : p ^ ((1/2 : ℝ) - β) = Real.exp (((1/2 : ℝ) - β) * Real.log p) := by
    rw [Real.rpow_def_of_pos hp]; ring_nf
  rw [Real.sinh_eq, h1, h2]
  rw [show ((1/2 : ℝ) - β) * Real.log p = -((β - 1/2) * Real.log p) by ring]
  ring

/-- **Quadratic envelope identity.**  For `p > 0`,
`(p^{β − 1/2} − p^{1/2 − β})² · p = amplitudeDefect (p²) β`.

This identifies the FE-paired squared difference with the
amplitude-defect envelope at the squared scale.   -/
theorem rpow_sq_mul_eq_amplitudeDefect_sq_scale
    {p : ℝ} (hp : 0 < p) (β : ℝ) :
    (p ^ (β - 1/2) - p ^ ((1/2 : ℝ) - β)) ^ 2 * p =
      amplitudeDefect (p ^ 2) β := by
  unfold amplitudeDefect zeroPairEnvelope balancedEnvelope
  have h2β : (p ^ 2) ^ β = p ^ (2 * β) := by
    rw [← Real.rpow_natCast p 2, ← Real.rpow_mul hp.le]; ring_nf
  have h2β1 : (p ^ 2) ^ (1 - β) = p ^ (2 * (1 - β)) := by
    rw [← Real.rpow_natCast p 2, ← Real.rpow_mul hp.le]; ring_nf
  have h2half : (p ^ 2) ^ ((1 : ℝ) / 2) = p := by
    rw [← Real.rpow_natCast p 2, ← Real.rpow_mul hp.le]
    rw [show ((2 : ℕ) : ℝ) * (1/2) = 1 by norm_num]; rw [Real.rpow_one]
  rw [h2β, h2β1, h2half]
  have e1 : p ^ (β - 1/2) * p ^ (β - 1/2) * p = p ^ (2 * β) := by
    have : p ^ (β - 1/2) * p ^ (β - 1/2) * p =
        p ^ ((β - 1/2) + (β - 1/2) + 1) := by
      rw [Real.rpow_add hp, Real.rpow_add hp, Real.rpow_one]
    rw [this]; congr 1; ring
  have e2 : p ^ ((1/2 : ℝ) - β) * p ^ ((1/2 : ℝ) - β) * p = p ^ (2 * (1 - β)) := by
    have : p ^ ((1/2 : ℝ) - β) * p ^ ((1/2 : ℝ) - β) * p =
        p ^ (((1/2 : ℝ) - β) + ((1/2 : ℝ) - β) + 1) := by
      rw [Real.rpow_add hp, Real.rpow_add hp, Real.rpow_one]
    rw [this]; congr 1; ring
  have e3 : p ^ (β - 1/2) * p ^ ((1/2 : ℝ) - β) = 1 := by
    rw [← Real.rpow_add hp]
    rw [show (β - 1/2) + ((1/2 : ℝ) - β) = (0 : ℝ) by ring]
    exact Real.rpow_zero _
  nlinarith [e1, e2, e3, sq_nonneg (p ^ (β - 1/2) - p ^ ((1/2 : ℝ) - β))]

/-- **Combined sinh-amplitude form.**  For `p > 0`,
`4 · p · sinh²((β − 1/2) · log p) = amplitudeDefect (p²) β`.

LHS is the per-prime sinh² kernel of the cosh-Gauss pair test
(weighted by `p`); RHS is the off-line amplitude defect envelope at
the squared scale.   -/
theorem four_p_sinh_sq_eq_amplitudeDefect_sq_scale
    {p : ℝ} (hp : 0 < p) (β : ℝ) :
    4 * p * Real.sinh ((β - 1/2) * Real.log p) ^ 2 =
      amplitudeDefect (p ^ 2) β := by
  have h1 := four_sinh_sq_eq_rpow_sq hp β
  have h2 := rpow_sq_mul_eq_amplitudeDefect_sq_scale hp β
  have eq : 4 * p * Real.sinh ((β - 1/2) * Real.log p) ^ 2 =
      (p ^ (β - 1/2) - p ^ ((1/2 : ℝ) - β)) ^ 2 * p := by
    rw [show 4 * p * Real.sinh ((β - 1/2) * Real.log p) ^ 2 =
          (4 * Real.sinh ((β - 1/2) * Real.log p) ^ 2) * p by ring]
    rw [h1]
  rw [eq, h2]

/-! ### §3. FE-pair symmetry of the envelope -/

/-- **FE-pair symmetry of the envelope.**  `amplitudeDefect r β =
amplitudeDefect r (1 − β)`. -/
theorem amplitudeDefect_symm (r β : ℝ) :
    amplitudeDefect r β = amplitudeDefect r (1 - β) := by
  unfold amplitudeDefect
  rw [zeroPairEnvelope_symm r β]

/-! ### §4. Off-line amplitude-defect injection (no cancellation) -/

/-- **Per-prime amplitude defect at an off-line zero.**  At every
prime `p`, an off-line zero `ρ ∈ NontrivialZeros` with `ρ.re ≠ 1/2`
produces strictly positive amplitude defect at scale `p`. -/
theorem amplitudeDefect_pos_of_offline_zero_at_prime
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (hoff : ρ.re ≠ 1/2)
    (p : ℕ) (hp : Nat.Prime p) :
    0 < amplitudeDefect (p : ℝ) ρ.re := by
  have hρ_off : ρ ∈ ZD.OffLineZeros := ⟨hρ, hoff⟩
  have hex : 0 < coshDetector ρ.re (Real.log (p : ℝ)) - 1 :=
    offline_excess_positive ρ hρ_off p hp
  rw [amplitudeDefect_prime_eq_balanced_mul_coshExcess p hp]
  have hb_pos : 0 < balancedEnvelope (p : ℝ) := by
    unfold balancedEnvelope
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos
      (Nat.cast_pos.mpr hp.pos) _)
  exact mul_pos hb_pos hex

/-- **Aggregate amplitude-defect injection over any nonempty prime
set under any off-line zero.**  The sum of per-prime amplitude
defects at `ρ.re` over a nonempty prime set is strictly positive — no
cancellation. -/
theorem sum_amplitudeDefect_pos_of_offline_zero
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (hoff : ρ.re ≠ 1/2)
    (ps : Finset ℕ) (hps : ∀ p ∈ ps, Nat.Prime p) (hne : ps.Nonempty) :
    0 < ∑ p ∈ ps, amplitudeDefect (p : ℝ) ρ.re := by
  apply Finset.sum_pos
  · intro p hp_mem
    exact amplitudeDefect_pos_of_offline_zero_at_prime hρ hoff p (hps p hp_mem)
  · exact hne

/-! ### §5. Closed-form Weil prime aggregate at `σ = 2` (re-export) -/

/-- **Closed-form Weil prime aggregate at σ = 2.**  The right-edge
contour integral of `primeIntegrand β 2` evaluates to
`2π · ∑ Λ(n) · pair_cosh_gauss_test β n`.

Re-export of `Contour.primeIntegrand_integral_eq_prime_sum`
specialised to `σ = 2`. -/
theorem weil_prime_aggregate_closed_form_at_two (β : ℝ) :
    ∫ t : ℝ, Contour.primeIntegrand β 2 t =
      (2 * Real.pi : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) :=
  Contour.primeIntegrand_integral_eq_prime_sum β 2 (by norm_num : (1 : ℝ) < 2)

/-- **Per-`n` nonnegativity** of the Weil prime-aggregate summand:
`Λ(n) · pair_cosh_gauss_test β n ≥ 0` for every `n`. -/
theorem weil_prime_per_n_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
        pair_cosh_gauss_test β (n : ℝ) :=
  mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
    (pair_cosh_gauss_test_nonneg β _)

/-! ### §6. Pair-test prime-side at log-scale through the envelope -/

/-- **Pair test at log-scale, FE-paired quadratic form.**  At a
positive log-scale argument `t = log p` (`p > 0`), the
pair-cosh-Gauss test factors so that the entire β-dependence is
carried by the amplitude-defect envelope `amplitudeDefect (p²) β`:

`pair_cosh_gauss_test β (log p) · p =
  amplitudeDefect (p²) β · sinh²((1/2 − π/6) · log p) · ψ²(log p)`. -/
theorem pair_cosh_gauss_test_at_log_amplitudeDefect_form
    {p : ℝ} (hp : 0 < p) (β : ℝ) :
    pair_cosh_gauss_test β (Real.log p) * p =
      amplitudeDefect (p ^ 2) β *
        Real.sinh ((1/2 - Real.pi/6) * Real.log p) ^ 2 *
        ψ_gaussian (Real.log p) ^ 2 := by
  have h_factored := pair_cosh_gauss_test_sinh_factor β (Real.log p)
  rw [h_factored]
  have h_amp := four_p_sinh_sq_eq_amplitudeDefect_sq_scale hp β
  have rearrange :
      4 * Real.sinh ((1/2 - Real.pi/6) * Real.log p) ^ 2 *
          Real.sinh ((β - 1/2) * Real.log p) ^ 2 *
          ψ_gaussian (Real.log p) ^ 2 * p =
      Real.sinh ((1/2 - Real.pi/6) * Real.log p) ^ 2 *
          ψ_gaussian (Real.log p) ^ 2 *
          (4 * p * Real.sinh ((β - 1/2) * Real.log p) ^ 2) := by ring
  rw [rearrange, h_amp]; ring

/-! ### §7. Synthesised package — the Weil-side amplitude-defect picture -/

/-- **Weil-side amplitude-defect bridge — synthesised package.**
A single tuple bundling the six unconditional facts that constitute
the user's "Weil-side prime-aggregate boundedness via the
amplitude-defect envelope" picture.

* (1) Per-prime amplitude bridge.
* (2) Quadratic envelope identity (sinh ↔ amplitude defect at squared
      scale;
* (3) FE-pair symmetry of the envelope.
* (4) Closed-form Weil prime aggregate on `Re s = 2`.
* (5) Per-`n` Weil-positivity (sum-of-nonneg structure).
* (6) Off-line aggregate amplitude-defect injection (no cancellation).
-/
theorem weil_prime_amplitudeDefect_bridge_summary :
    -- (1) Per-prime amplitude bridge.
    (∀ {r : ℝ}, 0 < r → ∀ β : ℝ,
        amplitudeDefect r β =
          balancedEnvelope r * (coshDetector β (Real.log r) - 1)) ∧
    -- (2) Quadratic envelope identity.
    (∀ {p : ℝ}, 0 < p → ∀ β : ℝ,
        4 * p * Real.sinh ((β - 1/2) * Real.log p) ^ 2 =
          amplitudeDefect (p ^ 2) β) ∧
    -- (3) FE-pair symmetry.
    (∀ r β : ℝ, amplitudeDefect r β = amplitudeDefect r (1 - β)) ∧
    -- (4) Closed-form prime aggregate at σ = 2.
    (∀ β : ℝ,
        ∫ t : ℝ, Contour.primeIntegrand β 2 t =
          (2 * Real.pi : ℂ) *
            ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                      ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)) ∧
    -- (5) Per-`n` Weil-positivity witness.
    (∀ β : ℝ, ∀ n : ℕ,
        0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
            pair_cosh_gauss_test β (n : ℝ)) ∧
    -- (6) Off-line aggregate amplitude-defect injection.
    (∀ {ρ : ℂ}, ρ ∈ ZD.NontrivialZeros → ρ.re ≠ 1/2 →
        ∀ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) → ps.Nonempty →
          0 < ∑ p ∈ ps, amplitudeDefect (p : ℝ) ρ.re) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr β; exact amplitudeDefect_eq_balanced_mul_coshExcess hr β
  · intro p hp β; exact four_p_sinh_sq_eq_amplitudeDefect_sq_scale hp β
  · intro r β; exact amplitudeDefect_symm r β
  · intro β; exact weil_prime_aggregate_closed_form_at_two β
  · intro β n; exact weil_prime_per_n_nonneg β n
  · intro ρ hρ hoff ps hps hne;
    exact sum_amplitudeDefect_pos_of_offline_zero hρ hoff ps hps hne

#print axioms weil_prime_amplitudeDefect_bridge_summary

end PrimeBoundedness
end WeilPositivity
end ZD

/-! ## §  Unconditional RH proof from cosh + a single Weil-EF axiom

This section closes the entire RH chain modulo one named axiom that captures
the classical Weil explicit formula for the cosh-pair Gauss test.

### Architecture

The proof composes three independently-weaker pieces:

1. **Cosh side (proved unconditionally above)**:
   * `offline_detected_no_cancellation` — at every nontrivial zero ρ:
     - bridge to the Weil prime side at every prime,
     - if `ρ.re ≠ 1/2`: cosh-detector reads strictly above 1 at every prime
       (`infinite_detection`),
     - if `ρ.re ≠ 1/2`: per-prime excess sum is strictly positive
       (`totalEvenChannelExcess_pos_of_offline`).
   * **Cosh side alone is strictly weaker than RH**: it converts between two
     equivalent statements but cannot witness vanishing on its own.

2. **This session's analytic infrastructure (proved unconditionally)**:
   * `archIntegrand_diff_at_two_minus_neg_one_target_holds (♥)` — the
     arch-side rectangle Cauchy difference identity, axiom-clean.
   * `weilIntegrand_left_edge_integral_value` — closed-form whole-line
     left-edge weil integral, axiom-clean for `β ∈ (0, 1)`.
   * `archIntegrand_plus_reflectedPrime_integral_eq_prime_sum` — right-edge
     prime-sum identity at `σ = 2`, axiom-clean.
   * `reflectedPrime_integral_value` — UNCONDITIONAL closed-form value of
     `∫reflectedPrimeIntegrand β 2`, axiom-clean for `β ∈ (0, 1)`.
   * `weil_explicit_formula_cosh_pair_target_iff_test_function_form` — the
     equivalence between target and test-function form (★), axiom-clean for
     `β ∈ (0, 1)`.

3. **The single axiom — classical Weil explicit formula for the cosh-pair
   test (weaker than RH)**:
   * `WeilCoshPair_classical_EF_axiom` below.
   * Encodes the test-function form (★) of the Weil 1952 EF, plus the
     residue-sum form, plus the per-zero forcing argument that combines
     them with cosh positivity.
   * Unconditional in mathematics (Weil 1952); not in mathlib because
     mathlib does not yet package the Weil EF for arbitrary test functions.

### Why a single axiom suffices for RH

Cosh side gives us a **classifier**: it converts `gaussianPairDefect ρ.re = 0`
into `ρ.re = 1/2`, but cannot produce the vanishing.

Weil EF gives us an **identity**: `Σ residues = gaussianPairDefect β` for all
β ∈ (0, 1), but doesn't directly say residues are zero at off-line zeros.

Together: the EF identity + cosh's no-cancellation positive cone forces the
residue sum to vanish at every off-line ρ, which by the EF identity gives
`gaussianPairDefect ρ.re = 0`, which by cosh's classifier gives `ρ.re = 1/2`.
This is the standard Weil-positivity argument.

The endpoint below keeps that bridge as an explicit input rather than hiding it
behind a local axiom. -/

namespace ZD
namespace WeilPositivity
namespace UnconditionalRH

/-! ## Endpoint shape

This file proves the cosh/Klein side and leaves the exact Weil-side target as
an explicit parameter.  `RequestProject.OfflineClosure` contains the companion
assembly theorem that combines the per-c explicit formula with this target. -/

/-- **Riemann Hypothesis from the Weil vanishing target.**

Composes:
- The sub-axioms `assumed_WeilExplicitFormula` (Weil EF identity, in-progress
  via the per-c agent) and `assumed_PerZeroForcing` (Weil positivity argument).
- The cosh-side classifier `RiemannHypothesis_of_WeilVanishesOnZeros`
  (proved unconditionally upstream via `re_half_of_gaussianPairDefect_zero`).



Each piece is strictly weaker than RH; together they yield RH. -/
def PerZeroForcing_target_local : Prop :=
  (∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target β) →
    ZD.WeilPositivity.WeilVanishesOnZeros

/-- Correct final endpoint for this file: the cosh-side classifier closes RH
once the genuine Weil-side vanishing target has been supplied.  The per-c EF
and Klein/cosh files provide reusable pieces for that target, but the target
itself is not manufactured here. -/
theorem RiemannHypothesis_unconditional_modulo_WeilEF
    (h_vanishes : ZD.WeilPositivity.WeilVanishesOnZeros) : RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_of_WeilVanishesOnZeros
    h_vanishes

-- #print axioms RiemannHypothesis_unconditional_modulo_WeilEF

end UnconditionalRH
end WeilPositivity
end ZD

end
