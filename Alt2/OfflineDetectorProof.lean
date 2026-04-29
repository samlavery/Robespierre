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
import RequestProject.WeilZeroOrthogonality
import RequestProject.GaussianClosedForm
import RequestProject.KleinForcerTheorem
import RequestProject.RequestProject_PrimeHarmonicAmplitude

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
* **Weil side (WeilExplicitFormulaFromPerC.lean).**  Proves unconditional integral / zero-sum
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

/-- **Per-prime amplitude bridge.**  At any scale `r > 1`, the
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

/-! ## §  Endpoint: Weil identity + cosh/no-cancellation + forcing

This section records the intended dependency boundary in `RequestProject`.
Nothing here proves RH by itself, and nothing here hides RH in a renamed local
axiom.

The route has three separate pieces:

1. **Weil identity.**  The full family
   `WeilExplicitFormula_pair_cosh_gauss_target β` is an aggregate explicit
   formula.  By itself it is weaker than RH: aggregate identities can hide
   per-zero information through cancellation.

2. **Cosh/no-cancellation.**  `offline_detected_no_cancellation` is the
   cosh-side package proved above.  It says off-line zeros are detected by the
   cosh excess and that finite prime-side excess has no cancellation.  By
   itself it is weaker than RH: it does not prove that zeros are on-line or
   that online zeros exist.

3. **Prime-harmonic bridge + existing forcer.**  The bridge should not prove
   `ρ.re = 1/2` directly.  The primes are the shared observation channel: an
   off-line zero creates positive even-channel prime excess, and the
   cosh/no-cancellation package says that excess cannot be cancelled on finite
   prime sets.  The missing bridge must use that prime-harmonic balance to
   produce the per-zero Klein detector condition.  Then the existing theorem
   `ZD.KleinForcer.klein_forcer_per_zero_real` consumes that condition and
   forces `ρ.re = 1/2`. -/

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint

/-- The uncancelled Weil prime-side link.  The prime sum `S` and zero residue
sum `Sres` are still present in the same equation:

`S = S - M(1) + Sres`.

This is exactly the PerC/Weil identity before cancelling the prime side down to
the zero-only formula `Sres = M(1)`.  The prime-harmonic bridge should consume
this form, not the collapsed aggregate identity. -/
def WeilPrimeSideLink_target_local : Prop :=
  ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)) =
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)) -
        Contour.pairTestMellin β 1 +
        ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (((Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat
              ρ.property) : ℕ) : ℂ)) *
          Contour.pairTestMellin β ρ.val

/-- The PerC/Weil hypotheses provide the uncancelled prime-side link.  This is
the same algebra as `WeilExplicitFormula_pair_cosh_gauss_target_of_star`, but
we stop one line earlier, while the prime sum is still visible. -/
theorem WeilPrimeSideLink_of_star_and_archPrimeRotation
    (h_star : ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.FinalAssembly.weil_explicit_formula_cosh_pair_target β)
    (h_arch : ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β) :
    WeilPrimeSideLink_target_local := by
  intro β hβ
  have h_refl_zero :=
    (ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_iff_reflectedPrime_vanishes
      β).mp (h_arch β hβ)
  have h_arch_prime :=
    ZD.WeilPositivity.FinalAssembly.archIntegrand_plus_reflectedPrime_integral_eq_prime_sum β
  have h_left := ZD.WeilPositivity.FinalAssembly.weilIntegrand_left_edge_integral_value β hβ
  set A : ℂ := ∫ y : ℝ, Contour.archIntegrand β 2 y
  set W : ℂ := ∫ y : ℝ, Contour.weilIntegrand
      (Contour.pairTestMellin β)
      ((((-1 : ℝ) : ℂ)) + (y : ℂ) * I)
  set S : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ)
  set Sres : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat
          ρ.property) : ℕ) : ℂ)) *
      Contour.pairTestMellin β ρ.val
  have hA : A = 2 * (Real.pi : ℂ) * S := by
    have h := h_arch_prime
    rw [h_refl_zero, add_zero] at h
    exact h
  have hAW : A = W := h_star β hβ
  rw [hA, h_left] at hAW
  have h2π_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  exact mul_left_cancel₀ h2π_ne hAW

/-- The same PerC hypotheses also still provide the collapsed aggregate Weil
identity; this wrapper records the relation between the honest prime-side link
and the existing final target. -/
theorem WeilIdentity_of_star_and_archPrimeRotation
    (h_star : ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.FinalAssembly.weil_explicit_formula_cosh_pair_target β)
    (h_arch : ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.Contour.ReflectedPrimeVanishing.archPair_eq_primePair_at_two_target β) :
    ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target β := by
  intro β hβ
  exact ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target_of_star
    β hβ (h_star β hβ) (h_arch β hβ)

/-- The uncancelled prime-side link entails the collapsed aggregate Weil
identity by cancelling the visible prime sum.  This is algebraic and does not
perform any per-zero extraction. -/
theorem WeilIdentity_of_prime_side_link
    (h_link : WeilPrimeSideLink_target_local) :
    ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target β := by
  intro β hβ
  unfold ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target
  have h := h_link β hβ
  set S : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      ((pair_cosh_gauss_test β (n : ℝ) : ℝ) : ℂ) with hS
  set M : ℂ := Contour.pairTestMellin β 1 with hM
  set Sres : ℂ := ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (((Classical.choose
        (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat
          ρ.property) : ℕ) : ℂ)) *
      Contour.pairTestMellin β ρ.val with hSres
  have hS_eq : S = S - M + Sres := by
    simpa [hS, hM, hSres] using h
  have hSres : Sres = M := by
    linear_combination -hS_eq
  rw [hSres, hM]
  exact Contour.pairTestMellin_at_one β

/-- Conversely, the collapsed aggregate Weil identity implies the current
uncancelled-link formulation by adding the same prime sum to both sides.  Thus
`WeilPrimeSideLink_target_local`, as currently stated, is algebraically
equivalent to the collapsed identity; it does not by itself contain a localized
finite-prime extraction principle. -/
theorem WeilPrimeSideLink_of_WeilIdentity
    (h_weil : ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
      ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target β) :
    WeilPrimeSideLink_target_local := by
  intro β hβ
  have hβ_weil := h_weil β hβ
  unfold ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target at hβ_weil
  have hSres : (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (((Classical.choose
            (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat
              ρ.property) : ℕ) : ℂ)) *
          Contour.pairTestMellin β ρ.val) =
        Contour.pairTestMellin β 1 := by
    rw [hβ_weil]
    exact (Contour.pairTestMellin_at_one β).symm
  rw [hSres]
  ring

/-- The current prime-side-link target is exactly the collapsed Weil identity,
not yet a stronger extraction statement. -/
theorem WeilPrimeSideLink_iff_WeilIdentity :
    WeilPrimeSideLink_target_local ↔
      (∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 →
        ZD.WeilPositivity.FinalAssembly.WeilExplicitFormula_pair_cosh_gauss_target β) :=
  ⟨WeilIdentity_of_prime_side_link, WeilPrimeSideLink_of_WeilIdentity⟩

/-- Specializing the uncancelled prime-side link at a putative off-line zero
recovers the positive aggregate Weil identity at `β = ρ.re`.  This still does
not isolate a finite prime packet; it is the strongest aggregate consequence of
the current link alone. -/
theorem offline_zero_prime_side_link_has_positive_rhs
    (h_link : WeilPrimeSideLink_target_local)
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (h_off : ρ.re ≠ 1/2) :
    (∑' ρ' : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (((Classical.choose
          (Contour.analyticOrderAt_riemannZeta_nontrivialZero_pos_nat ρ'.property) :
            ℕ) : ℂ)) *
        Contour.pairTestMellin ρ.re ρ'.val)
      = ((gaussianPairDefect ρ.re : ℝ) : ℂ)
    ∧ 0 < gaussianPairDefect ρ.re := by
  exact ZD.WeilPositivity.FinalAssembly.offline_zero_weil_identity_has_positive_rhs
    (WeilIdentity_of_prime_side_link h_link) hρ h_off

/-- The cosh/no-cancellation input proved in this file. -/
def CoshNoCancellation_target_local : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    (∀ p : ℕ, Nat.Prime p →
      (↑p : ℝ) ^ ρ.re + (↑p : ℝ) ^ (1 - ρ.re) =
        balancedEnvelope (↑p) *
        coshDetector ρ.re (Real.log (↑p))) ∧
    (ρ.re ≠ 1/2 →
      (∀ p : ℕ, Nat.Prime p → 1 < coshDetector ρ.re (Real.log (↑p))) ∧
      (∀ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) → ps.Nonempty →
        0 < ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1)))

/-- The local theorem above supplies the cosh/no-cancellation input. -/
theorem CoshNoCancellation_target_local_holds :
    CoshNoCancellation_target_local :=
  Contour.CoshReflectedClassifier.offline_detected_no_cancellation

/-- If an off-line zero existed, its cosh defect would be broadcast through
every prime and could not cancel over any nonempty finite prime packet.  This is
the precise "defects flow through every prime" statement supplied by the cosh
geometry, independent of Weil/RH. -/
theorem offline_defect_flows_through_every_prime
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (h_off : ρ.re ≠ 1/2) :
    (∀ p : ℕ, Nat.Prime p →
      0 < coshDetector ρ.re (Real.log (↑p)) - 1) ∧
    (∀ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) → ps.Nonempty →
      0 < ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1)) := by
  obtain ⟨_, h_no_cancel⟩ := CoshNoCancellation_target_local_holds ρ hρ
  obtain ⟨h_prime_gt_one, h_packet_pos⟩ := h_no_cancel h_off
  refine ⟨?_, h_packet_pos⟩
  intro p hp
  linarith [h_prime_gt_one p hp]

/-- The same off-line defect is visible on the prime-side zero-pair envelope:
at every prime, the reflected zero-pair contribution is strictly larger than
the balanced on-line envelope. -/
theorem offline_zero_pair_envelope_exceeds_balanced_at_every_prime
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (h_off : ρ.re ≠ 1/2) :
    ∀ p : ℕ, Nat.Prime p →
      balancedEnvelope (↑p) <
        (↑p : ℝ) ^ ρ.re + (↑p : ℝ) ^ (1 - ρ.re) := by
  intro p hp
  obtain ⟨h_prime_bridge, h_no_cancel⟩ := CoshNoCancellation_target_local_holds ρ hρ
  obtain ⟨h_prime_gt_one, _⟩ := h_no_cancel h_off
  have hb_pos : 0 < balancedEnvelope (↑p) := by
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    unfold balancedEnvelope
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hp_pos _)
  rw [h_prime_bridge p hp]
  calc balancedEnvelope (↑p)
      = balancedEnvelope (↑p) * 1 := by ring
    _ < balancedEnvelope (↑p) * coshDetector ρ.re (Real.log (↑p)) :=
        mul_lt_mul_of_pos_left (h_prime_gt_one p hp) hb_pos

/-- Online zeros have no cosh-excess packet: every prime reads the balanced
amplitude, and every finite prime packet has zero total excess. -/
theorem online_zero_has_no_defect_packet
    {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros) (h_online : ρ.re = 1/2) :
    (∀ p : ℕ, Nat.Prime p →
      coshDetector ρ.re (Real.log (↑p)) - 1 = 0) ∧
    (∀ ps : Finset ℕ,
      ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1) = 0) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [h_online]
    simp [coshDetector, Real.cosh_zero]
  · intro ps
    apply Finset.sum_eq_zero
    intro p hp
    rw [h_online]
    simp [coshDetector, Real.cosh_zero]

/-- Online zeros have exactly the balanced prime-side zero-pair envelope at
every prime: no amplitude excess flows through the prime channel. -/
theorem online_zero_pair_envelope_balanced_at_every_prime
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (h_online : ρ.re = 1/2) :
    ∀ p : ℕ, Nat.Prime p →
      (↑p : ℝ) ^ ρ.re + (↑p : ℝ) ^ (1 - ρ.re) =
        balancedEnvelope (↑p) := by
  intro p hp
  obtain ⟨h_prime_bridge, _⟩ := CoshNoCancellation_target_local_holds ρ hρ
  rw [h_prime_bridge p hp, h_online]
  simp [coshDetector, Real.cosh_zero]

/-- The per-zero Klein condition consumed by the existing forcing theorem. -/
def PerZeroKleinCondition_local : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    ∃ p : ℕ, Nat.Prime p ∧
      coshDetectorLeft ρ.re (Real.log p) =
        coshDetectorLeft (1 - ρ.re) (Real.log p)

/-- The two-cosh-detector bridge in the form suggested by the left/right
geometry: Weil/prime invariance should produce a prime where the left and right
cosh kernels agree for each zero.  Via the reflection swap
`Left(1-β)=Right(β)`, this is exactly the input consumed by the Klein forcer. -/
def WeilTwoCoshDetectorBridge_target_local : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    ∃ p : ℕ, Nat.Prime p ∧
      coshDetectorLeft ρ.re (Real.log (↑p)) =
        coshDetectorRight ρ.re (Real.log (↑p))

/-- The left/right bridge is exactly vanishing of the existing double-cosh
agreement residue at a prime.  This is the algebraic extraction point: no RH
statement is used, only that a square vanishes iff its base vanishes. -/
theorem two_cosh_detector_bridge_iff_pairAgreementDefect_zero_at_prime
    {ρ : ℂ} {p : ℕ} (_hp : Nat.Prime p) :
    coshDetectorLeft ρ.re (Real.log (↑p)) =
        coshDetectorRight ρ.re (Real.log (↑p)) ↔
  pairAgreementDefect (↑p) ρ.re = 0 := by
  unfold pairAgreementDefect
  rw [sq_eq_zero_iff, sub_eq_zero]

/-- Per-zero prime residue vanishing is the same bridge, phrased in the
residue language used by the double-cosh detector. -/
theorem WeilTwoCoshDetectorBridge_of_pairAgreementDefect_zero_at_prime
    (h_residue : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧ pairAgreementDefect (↑p) ρ.re = 0) :
    WeilTwoCoshDetectorBridge_target_local := by
  intro ρ hρ
  obtain ⟨p, hp, hzero⟩ := h_residue ρ hρ
  exact ⟨p, hp,
    (two_cosh_detector_bridge_iff_pairAgreementDefect_zero_at_prime
      (ρ := ρ) hp).mpr hzero⟩

/-- Left/right agreement at a prime is the same as the Klein-forcer input:
`Left β = Left (1-β)`, because reflection swaps the right detector at `β`
with the left detector at `1-β`. -/
theorem PerZeroKleinCondition_of_two_cosh_detector_bridge
    (h_bridge : WeilTwoCoshDetectorBridge_target_local) :
    PerZeroKleinCondition_local := by
  intro ρ hρ
  obtain ⟨p, hp, hLR⟩ := h_bridge ρ hρ
  refine ⟨p, hp, ?_⟩
  calc
    coshDetectorLeft ρ.re (Real.log (↑p))
        = coshDetectorRight ρ.re (Real.log (↑p)) := hLR
    _ = coshDetectorLeft (1 - ρ.re) (Real.log (↑p)) :=
        (coshDetector_reflect_swap ρ.re (Real.log (↑p))).symm

/-- The two-cosh-detector bridge closes the per-zero real-part statement by
feeding the existing Klein forcer. -/
theorem no_offline_zeros_of_two_cosh_detector_bridge
    (h_bridge : WeilTwoCoshDetectorBridge_target_local) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  ZD.KleinForcer.klein_forcer_per_zero_real
    (PerZeroKleinCondition_of_two_cosh_detector_bridge h_bridge)

/-- Closing form in residue language: if the Weil/cosh extraction gives
zero double-cosh agreement residue at one prime for each nontrivial zero, the
existing Klein forcer proves every such zero is on the critical line. -/
theorem no_offline_zeros_of_pairAgreementDefect_zero_at_prime
    (h_residue : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧ pairAgreementDefect (↑p) ρ.re = 0) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  no_offline_zeros_of_two_cosh_detector_bridge
    (WeilTwoCoshDetectorBridge_of_pairAgreementDefect_zero_at_prime h_residue)

/-- **Pointwise double-cosh rigidity.**  At a prime scale, vanishing of the
double-cosh agreement residue forces the real part to be `1/2`.

Proof chain:
`pairAgreementDefect = 0` gives `Left = Right`; reflection rewrites
`Right β` as `Left (1-β)`; the existing two-kernel Klein forcer then gives
`β = 1/2`. -/
theorem critical_line_of_pairAgreementDefect_zero_at_prime
    {ρ : ℂ} {p : ℕ} (hp : Nat.Prime p)
    (h_residue : pairAgreementDefect (↑p) ρ.re = 0) :
    ρ.re = 1/2 := by
  have h_agree :
      coshDetectorLeft ρ.re (Real.log (↑p)) =
        coshDetectorRight ρ.re (Real.log (↑p)) :=
    (two_cosh_detector_bridge_iff_pairAgreementDefect_zero_at_prime
      (ρ := ρ) hp).mpr h_residue
  have h_klein :
      coshDetectorLeft ρ.re (Real.log (↑p)) =
        coshDetectorLeft (1 - ρ.re) (Real.log (↑p)) := by
    calc
      coshDetectorLeft ρ.re (Real.log (↑p))
          = coshDetectorRight ρ.re (Real.log (↑p)) := h_agree
      _ = coshDetectorLeft (1 - ρ.re) (Real.log (↑p)) :=
          (coshDetector_reflect_swap ρ.re (Real.log (↑p))).symm
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast hp.one_lt.ne'
  have hlog_ne_zero : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp_pos hp_ne_one
  exact ZD.KleinForcer.klein_forcer_two_kernel hlog_ne_zero h_klein

/-- Global rigidity form: if the Weil/Cauchy residue extraction supplies one
prime-scale zero agreement residue for every nontrivial zero, then all
nontrivial zeros lie on the critical line. -/
theorem no_offline_zeros_of_residue_rigidity
    (h_residue : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧ pairAgreementDefect (↑p) ρ.re = 0) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  obtain ⟨p, hp, hzero⟩ := h_residue ρ hρ
  exact critical_line_of_pairAgreementDefect_zero_at_prime hp hzero

/-- The one-prime residue-rigidity extraction is exactly as strong as the
no-offline-zero conclusion.  The forward direction is the Klein/cosh rigidity
proved above; the reverse direction is pure on-line geometry, witnessed at the
fixed prime `2`.

This is the key non-smuggling checkpoint: making `no_offline_zeros_final`
unconditional is equivalent to proving this residue extraction
unconditionally. -/
theorem residue_rigidity_iff_no_offline_zeros :
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧ pairAgreementDefect (↑p) ρ.re = 0) ↔
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2) := by
  constructor
  · exact no_offline_zeros_of_residue_rigidity
  · intro hline ρ hρ
    exact ⟨2, Nat.prime_two,
      by
        rw [hline ρ hρ]
        exact (pairAgreementDefect_eq_zero_iff
          (by norm_num : (0 : ℝ) < (2 : ℝ))
          (by norm_num : (2 : ℝ) ≠ 1)).mpr rfl⟩

/-- **Minimum-amplitude rigidity.**  If the observed prime harmonic amplitude
of a zero is exactly the balanced/minimum amplitude at one prime, then the zero
is on the critical line.

This is the AM-GM/equality-condition route: the observed reduced amplitude is
the cosh detector reading, the balanced observable is `1`, and equality in the
prime detector occurs only at `β = 1/2`. -/
theorem critical_line_of_observed_prime_amplitude_minimum
    {ρ : ℂ} {p : ℕ} (hp : Nat.Prime p)
    (h_min :
      actualReducedObservable ρ.re p = balancedPrimeObservable p) :
    ρ.re = 1/2 := by
  have hdet : coshDetector ρ.re (Real.log (↑p)) = 1 := by
    simpa [actualReducedObservable, balancedPrimeObservable] using h_min
  exact (prime_detector_iff p hp).mp hdet

/-- Minimum observed amplitude at a prime gives the double-cosh residue
vanishing needed by the rigidity close. -/
theorem pairAgreementDefect_zero_of_observed_prime_amplitude_minimum
    {ρ : ℂ} {p : ℕ} (hp : Nat.Prime p)
    (h_min :
      actualReducedObservable ρ.re p = balancedPrimeObservable p) :
    pairAgreementDefect (↑p) ρ.re = 0 := by
  have hline : ρ.re = 1/2 :=
    critical_line_of_observed_prime_amplitude_minimum hp h_min
  rw [hline]
  exact (pairAgreementDefect_eq_zero_iff
    (Nat.cast_pos.mpr hp.pos)
    (by exact_mod_cast hp.one_lt.ne')).mpr rfl

/-- Global minimum-amplitude close: if each nontrivial zero has one prime where
the observed prime harmonic amplitude attains the balanced minimum, then all
nontrivial zeros are on the critical line. -/
theorem no_offline_zeros_of_observed_prime_amplitude_minimum
    (h_min : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧
        actualReducedObservable ρ.re p = balancedPrimeObservable p) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  obtain ⟨p, hp, hobs⟩ := h_min ρ hρ
  exact critical_line_of_observed_prime_amplitude_minimum hp hobs

/-- The minimum-amplitude extraction implies the residue-rigidity extraction:
measuring the observed prime harmonic at its balanced minimum gives vanishing of
the two-kernel agreement residue. -/
theorem residue_rigidity_of_observed_prime_amplitude_minimum
    (h_min : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧
        actualReducedObservable ρ.re p = balancedPrimeObservable p) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧ pairAgreementDefect (↑p) ρ.re = 0 := by
  intro ρ hρ
  obtain ⟨p, hp, hobs⟩ := h_min ρ hρ
  exact ⟨p, hp,
    pairAgreementDefect_zero_of_observed_prime_amplitude_minimum hp hobs⟩

/-- **Minimum prime harmonic amplitude.**  For every prime `p`, the reflected
Euler harmonic amplitude
`p^(-β) + p^(-(1-β))` has minimum value `2 / sqrt p`, uniquely at
`β = 1/2`. -/
theorem minimum_prime_harmonic_amplitude
    (p : ℕ) (hp : Nat.Prime p) :
    (∀ β : ℝ,
      2 / Real.sqrt (p : ℝ) ≤ ZD.KleinForcer.amplitude (p : ℝ) β) ∧
    ZD.KleinForcer.amplitude (p : ℝ) (1/2 : ℝ) =
      2 / Real.sqrt (p : ℝ) ∧
    (∀ β : ℝ,
      ZD.KleinForcer.amplitude (p : ℝ) β =
          2 / Real.sqrt (p : ℝ) ↔ β = 1/2) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsingle_pow :
      ‖((p : ℂ) ^ (-eulerPhase))‖ = (p : ℝ) ^ (-(1/2 : ℝ)) :=
    min_amplitude_prime_harmonic hp
  have hsingle_sqrt :
      ‖((p : ℂ) ^ (-eulerPhase))‖ = 1 / Real.sqrt (p : ℝ) :=
    min_amplitude_eq_inv_sqrt hp
  have hmin :
      2 / Real.sqrt (p : ℝ) = 2 * (p : ℝ) ^ (-(1/2 : ℝ)) := by
    calc
      2 / Real.sqrt (p : ℝ)
          = 2 * ‖((p : ℂ) ^ (-eulerPhase))‖ := by
              rw [hsingle_sqrt]
              ring
      _ = 2 * (p : ℝ) ^ (-(1/2 : ℝ)) := by rw [hsingle_pow]
  refine ⟨?_, ?_, ?_⟩
  · intro β
    rw [hmin]
    exact ZD.KleinForcer.amplitude_ge_min hp_pos β
  · rw [hmin]
    exact (ZD.KleinForcer.amplitude_eq_min_iff hp_gt_one (1/2 : ℝ)).mpr rfl
  · intro β
    rw [hmin]
    exact ZD.KleinForcer.amplitude_eq_min_iff hp_gt_one β

/-- Prime-harmonic minimum extraction, in the inverse Euler-log-product
normalization.  If the inverse reflected prime harmonic
`p^(-β) + p^(-(1-β))` attains the minimum `2 / sqrt p`, then the central
reduced detector reads its balanced value `1`. -/
theorem actualReducedObservable_eq_balanced_of_inverse_prime_harmonic_minimum
    {β : ℝ} {p : ℕ} (hp : Nat.Prime p)
    (h_min :
      ZD.KleinForcer.amplitude (p : ℝ) β = 2 / Real.sqrt (p : ℝ)) :
    actualReducedObservable β p = balancedPrimeObservable p := by
  have hline : β = 1/2 :=
    ((minimum_prime_harmonic_amplitude p hp).2.2 β).mp h_min
  rw [hline]
  exact actualReducedObservable_online p

/-- If the inverse prime harmonic is at its minimum, then the two anchored
detectors agree at that prime.  This is the left/right detector version of the
same Euler-log-product minimum-amplitude rigidity. -/
theorem left_right_detectors_agree_of_inverse_prime_harmonic_minimum
    {β : ℝ} {p : ℕ} (hp : Nat.Prime p)
    (h_min :
      ZD.KleinForcer.amplitude (p : ℝ) β = 2 / Real.sqrt (p : ℝ)) :
    coshDetectorLeft β (Real.log (↑p)) =
      coshDetectorRight β (Real.log (↑p)) := by
  have hline : β = 1/2 :=
    ((minimum_prime_harmonic_amplitude p hp).2.2 β).mp h_min
  rw [hline]
  exact coshDetectors_equal_on_critical_line (Real.log (↑p))

/-- Every-prime version: if every nontrivial zero registers the inverse
prime-harmonic minimum at every prime, then the left and right detectors agree
at every prime for every zero. -/
theorem left_right_detectors_agree_every_prime_of_inverse_prime_harmonic_minimum
    (h_min : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        ZD.KleinForcer.amplitude (p : ℝ) ρ.re =
          2 / Real.sqrt (p : ℝ)) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        coshDetectorLeft ρ.re (Real.log (↑p)) =
          coshDetectorRight ρ.re (Real.log (↑p)) := by
  intro ρ hρ p hp
  exact left_right_detectors_agree_of_inverse_prime_harmonic_minimum hp
    (h_min ρ hρ p hp)

/-- Every-prime detector agreement gives every-prime double-cosh residue
vanishing.  Thus the left/right detectors registering the same minimum
prime-harmonic amplitude covers the zero-balancing condition at every prime. -/
theorem pairAgreementDefect_zero_every_prime_of_inverse_prime_harmonic_minimum
    (h_min : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        ZD.KleinForcer.amplitude (p : ℝ) ρ.re =
          2 / Real.sqrt (p : ℝ)) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        pairAgreementDefect (↑p) ρ.re = 0 := by
  intro ρ hρ p hp
  exact (two_cosh_detector_bridge_iff_pairAgreementDefect_zero_at_prime
    (ρ := ρ) hp).mp
      (left_right_detectors_agree_every_prime_of_inverse_prime_harmonic_minimum
        h_min ρ hρ p hp)

/-- Final close from the every-prime inverse harmonic minimum: since every
prime harmonic is observed at the AM-GM minimum on both detector sides, every
zero has a vanishing agreement residue at every prime, hence in particular at
one prime, and the rigidity theorem forces the critical line. -/
theorem no_offline_zeros_final_of_inverse_prime_harmonic_minimum_every_prime
    (h_min : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        ZD.KleinForcer.amplitude (p : ℝ) ρ.re =
          2 / Real.sqrt (p : ℝ)) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  exact critical_line_of_pairAgreementDefect_zero_at_prime Nat.prime_two
    (pairAgreementDefect_zero_every_prime_of_inverse_prime_harmonic_minimum
      h_min ρ hρ 2 Nat.prime_two)

/-- Online zeros have vanishing double-cosh agreement residue at every prime. -/
theorem pairAgreementDefect_zero_every_prime_of_online_zero
    {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros) (hline : ρ.re = 1/2) :
    ∀ p : ℕ, Nat.Prime p → pairAgreementDefect (↑p) ρ.re = 0 := by
  intro p hp
  rw [hline]
  exact (pairAgreementDefect_eq_zero_iff
    (Nat.cast_pos.mpr hp.pos)
    (by exact_mod_cast hp.one_lt.ne')).mpr rfl

/-- Offline zeros have strictly positive double-cosh agreement residue at every
prime, hence no prime-harmonic residue vanishing is possible for them. -/
theorem pairAgreementDefect_pos_every_prime_of_offline_zero
    {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros) (hoff : ρ.re ≠ 1/2) :
    ∀ p : ℕ, Nat.Prime p → 0 < pairAgreementDefect (↑p) ρ.re := by
  intro p hp
  exact pairAgreementDefect_pos
    (Nat.cast_pos.mpr hp.pos)
    (by exact_mod_cast hp.one_lt.ne') hoff

/-- Pointwise zero dichotomy: at each nontrivial zero, either every prime
agreement residue vanishes, or every prime agreement residue is strictly
positive.  Thus vanishing holds at every zero exactly unless that zero is
off-line. -/
theorem pairAgreementDefect_zero_or_positive_every_prime_at_zero
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    (ρ.re = 1/2 ∧
      ∀ p : ℕ, Nat.Prime p → pairAgreementDefect (↑p) ρ.re = 0) ∨
    (ρ.re ≠ 1/2 ∧
      ∀ p : ℕ, Nat.Prime p → 0 < pairAgreementDefect (↑p) ρ.re) := by
  by_cases hline : ρ.re = 1/2
  · left
    exact ⟨hline, pairAgreementDefect_zero_every_prime_of_online_zero hρ hline⟩
  · right
    exact ⟨hline, pairAgreementDefect_pos_every_prime_of_offline_zero hρ hline⟩

/-- Global equivalence: every nontrivial zero has vanishing agreement residue
at every prime iff there are no off-line zeros. -/
theorem pairAgreementDefect_zero_every_prime_iff_no_offline_zeros :
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p → pairAgreementDefect (↑p) ρ.re = 0) ↔
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2) := by
  constructor
  · intro hzero ρ hρ
    exact critical_line_of_pairAgreementDefect_zero_at_prime Nat.prime_two
      (hzero ρ hρ 2 Nat.prime_two)
  · intro hline ρ hρ
    exact pairAgreementDefect_zero_every_prime_of_online_zero hρ (hline ρ hρ)

/-- Endpoint fed directly by the forked PerC prime observable: if the fork
proves the pointwise prime term `pair_cosh_gauss_test ρ.re (log p)` vanishes
for every zero and every prime before aggregate cancellation, then every
nontrivial zero lies on the critical line. -/
theorem no_offline_zeros_final_of_pair_cosh_gauss_test_log_prime_zero
    (hzero : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        pair_cosh_gauss_test ρ.re (Real.log (↑p)) = 0) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  pairAgreementDefect_zero_every_prime_iff_no_offline_zeros.mp
    (ZD.WeilPositivity.FinalAssembly.pairAgreementDefect_zero_every_prime_of_pair_cosh_gauss_test_log_prime_zero
      hzero)

/-- Endpoint in the detector-harmonic names exported by the unconditional
forked PerC code.  Once the fork supplies localized harmonic vanishing for
every actual zero and every prime, the existing two-cosh rigidity closes the
no-offline-zero statement. -/
theorem no_offline_zeros_final_of_detectorPrimeHarmonicObservable_zero
    (hzero : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        ZD.WeilPositivity.FinalAssembly.detectorPrimeHarmonicObservable
          ρ.re p = 0) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  pairAgreementDefect_zero_every_prime_iff_no_offline_zeros.mp
    (ZD.WeilPositivity.FinalAssembly.pairAgreementDefect_zero_every_prime_of_detectorPrimeHarmonicObservable_zero
      hzero)

/-- RH endpoint in the detector-harmonic names exported by the unconditional
forked PerC code.  The only remaining input is localized detector-harmonic
vanishing for every actual zero and every prime. -/
theorem rh_final_of_detectorPrimeHarmonicObservable_zero
    (hzero : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        ZD.WeilPositivity.FinalAssembly.detectorPrimeHarmonicObservable
          ρ.re p = 0) :
    RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_of_WeilVanishesOnZeros
    (fun ρ hρ =>
      ZD.KleinForcer.gaussianPairDefect_zero_of_online hρ
        (no_offline_zeros_final_of_detectorPrimeHarmonicObservable_zero
          hzero ρ hρ))

/-- Cosh geometry supplies the obstruction: an off-line zero cannot satisfy
left/right detector agreement at any prime. -/
theorem offline_zero_two_cosh_detectors_disagree_at_every_prime
    {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros) (h_off : ρ.re ≠ 1/2) :
    ∀ p : ℕ, Nat.Prime p →
      coshDetectorLeft ρ.re (Real.log (↑p)) ≠
        coshDetectorRight ρ.re (Real.log (↑p)) := by
  intro p hp h_agree
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast hp.one_lt.ne'
  have hlog_ne_zero : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp_pos hp_ne_one
  exact h_off ((coshDetectors_agree_iff hlog_ne_zero).mp h_agree)

/-- Prime-harmonic zero balance at a putative off-line zero: if `ρ.re ≠ 1/2`,
the Weil/prime side should supply a finite nonempty prime packet whose total
cosh excess vanishes.  This statement does not include no-cancellation; the
cosh package below is what makes such a packet impossible off the line. -/
def PrimeHarmonicZeroBalance_local : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re ≠ 1/2 →
    ∃ ps : Finset ℕ,
      ps.Nonempty ∧
      (∀ p ∈ ps, Nat.Prime p) ∧
      ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1) = 0

/-- The cleaner prime-channel balance target: at every nontrivial zero, the
prime channel is already balanced at every prime.  There is no defect packet;
the cosh excess is identically zero on the prime observations. -/
def PrimeChannelBalanced_local : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    ∀ p : ℕ, Nat.Prime p →
      coshDetector ρ.re (Real.log (↑p)) - 1 = 0

/-- The corrected extraction target: Weil's prime side should produce balanced
prime-channel readings, not a hidden defect packet. -/
def WeilPrimeChannelBalanceExtraction_target_local : Prop :=
  WeilPrimeSideLink_target_local →
    PrimeChannelBalanced_local

/-- The Cauchy/Weil zero-defect-energy target that fits the AM-GM route:
actual nontrivial zeta zeros have zero averaged Gaussian defect energy.  The
AM-GM/positivity side is already proved; this is the analytic extraction that
should come from the localized Cauchy/rectangle/residue infrastructure. -/
def WeilCauchyZeroDefectEnergy_target_local : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    ZD.averageEnergyDefect ZD.gaussianKernel ρ.re = 0

/-- The zero-side coefficient whose pointwise vanishing is exactly zero
Gaussian defect energy at each zeta zero.  This is the coefficient the Cauchy
and Weil orthogonality extraction must isolate; no RH statement is built in. -/
def GaussianDefectCoefficient_local (ρ : ℂ) : ℂ :=
  (ZD.averageEnergyDefect ZD.gaussianKernel ρ.re : ℂ)

/-- Entire Gaussian defect kernel before restriction to the real axis.  On
real inputs this is exactly the closed-form averaged Gaussian energy defect;
off the real axis it is the holomorphic object that can be inserted into a
residue computation. -/
def gaussianDefectEntireKernel_local (s : ℂ) : ℂ :=
  ((Real.pi * Real.sqrt (Real.pi / 2) : ℝ) : ℂ) *
    (Complex.exp ((s - (1 / 2 : ℂ)) ^ 2 / 2) -
      2 * Complex.exp ((s - (1 / 2 : ℂ)) ^ 2 / 8) + 1)

/-- Folding a complex point across `Im(s)=0`: average with its conjugate. -/
def realAxisFold_local (s : ℂ) : ℂ :=
  (s + star s) / 2

/-- The reflection fold lands on the real axis at `Re(s)`. -/
theorem realAxisFold_eq_ofReal_re (s : ℂ) :
    realAxisFold_local s = (s.re : ℂ) := by
  apply Complex.ext
  · simp [realAxisFold_local]
  · simp [realAxisFold_local]

/-- The entire Gaussian defect kernel restricts on the real axis to the
averaged Gaussian energy defect already proved in `GaussianClosedForm`. -/
theorem gaussianDefectEntireKernel_ofReal (β : ℝ) :
    gaussianDefectEntireKernel_local (β : ℂ) =
      (ZD.averageEnergyDefect ZD.gaussianKernel β : ℂ) := by
  change gaussianDefectEntireKernel_local (β : ℂ) =
    (ZD.averageEnergyDefect ZD.ψ_gaussian β : ℂ)
  rw [ZD.averageEnergyDefect_gaussian_closed_form β]
  unfold gaussianDefectEntireKernel_local
  simp [Complex.ofReal_exp]

/-- The old real-part coefficient is the real-axis fold of the holomorphic
Gaussian defect kernel.  This is the residue-compatible form of the coefficient:
the non-holomorphic `ρ.re` enters only through the explicit reflection fold
`(ρ + ρ̄)/2`. -/
theorem GaussianDefectCoefficient_eq_folded_entire (ρ : ℂ) :
    GaussianDefectCoefficient_local ρ =
      gaussianDefectEntireKernel_local (realAxisFold_local ρ) := by
  rw [realAxisFold_eq_ofReal_re, gaussianDefectEntireKernel_ofReal]
  rfl

/-- The channel-balance form of the Weil/Cauchy residue output: at every
nontrivial zero, the folded cosh kernel balances the cosine and sine defect
channels at every height.  This is the residue-compatible vanishing statement:
not "RH", but balance of the two transported energy channels. -/
def WeilEnergyChannelBalance_target_local : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
    ∀ γ : ℝ, ZD.EnergyChannelsBalanced ZD.gaussianKernel ρ.re γ

/-- Balanced cosine and sine channels give pointwise zero energy defect. -/
theorem energyDefect_zero_of_channels_balanced
    {ρ : ℂ} {γ : ℝ}
    (h_bal : ZD.EnergyChannelsBalanced ZD.gaussianKernel ρ.re γ) :
    ZD.energyDefect ZD.gaussianKernel ρ.re γ = 0 :=
  (ZD.energyDefect_eq_zero_iff_channels_balanced ZD.gaussianKernel ρ.re γ).mpr h_bal

/-- If the cosine and sine channels are balanced at every height, then the
averaged Gaussian energy defect vanishes. -/
theorem averageEnergyDefect_zero_of_channels_balanced
    {ρ : ℂ}
    (h_bal : ∀ γ : ℝ,
      ZD.EnergyChannelsBalanced ZD.gaussianKernel ρ.re γ) :
    ZD.averageEnergyDefect ZD.gaussianKernel ρ.re = 0 := by
  unfold ZD.averageEnergyDefect
  simp_rw [fun γ => energyDefect_zero_of_channels_balanced (ρ := ρ) (γ := γ) (h_bal γ)]
  simp

/-- The channel-balance form of the Weil/Cauchy residue theorem supplies the
zero-defect-energy extraction target used by the AM-GM/positivity route. -/
theorem WeilCauchyZeroDefectEnergy_of_energy_channel_balance
    (h_bal : WeilEnergyChannelBalance_target_local) :
    WeilCauchyZeroDefectEnergy_target_local := by
  intro ρ hρ
  exact averageEnergyDefect_zero_of_channels_balanced (h_bal ρ hρ)

/-- Consequently, channel balance at actual zeta zeros rules out off-line zeros
by the already-proved Gaussian positivity theorem. -/
theorem no_offline_zeros_of_energy_channel_balance
    (h_bal : WeilEnergyChannelBalance_target_local) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  by_contra h_off
  have hzero : ZD.averageEnergyDefect ZD.gaussianKernel ρ.re = 0 :=
    WeilCauchyZeroDefectEnergy_of_energy_channel_balance h_bal ρ hρ
  have hpos : 0 < ZD.averageEnergyDefect ZD.gaussianKernel ρ.re :=
    ZD.gaussianKernel_averageEnergyDefect_pos_offline ρ.re h_off
  linarith

/-- Conversely, if all nontrivial zeros are already on the line, the channel
balance target follows from the pure geometry of the cosh/sinh channels. -/
theorem WeilEnergyChannelBalance_of_no_offline_zeros
    (hline : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2) :
    WeilEnergyChannelBalance_target_local := by
  intro ρ hρ γ
  have hzero : ZD.energyDefect ZD.gaussianKernel ρ.re γ = 0 := by
    rw [hline ρ hρ]
    exact ZD.energyDefect_zero_on_line ZD.gaussianKernel γ
  exact (ZD.energyDefect_eq_zero_iff_channels_balanced
    ZD.gaussianKernel ρ.re γ).mp hzero

/-- Therefore the all-zero channel-balance target is exactly as strong as
placing all nontrivial zeros on the critical line.  It is a good endpoint for
the Weil residue/fold argument, but it cannot be proved from cosh geometry alone
without already closing the RH-level statement. -/
theorem WeilEnergyChannelBalance_iff_no_offline_zeros :
    WeilEnergyChannelBalance_target_local ↔
      ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  ⟨no_offline_zeros_of_energy_channel_balance,
    WeilEnergyChannelBalance_of_no_offline_zeros⟩

/-- Summability side of the real Cauchy/Weil extraction: the Gaussian defect
coefficient may be paired with the `pairTestMellin β` zero kernel and summed
over the nontrivial zeros for every admissible `β`. -/
def CauchyWeilGaussianDefectSummable_target_local : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 →
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      GaussianDefectCoefficient_local ρ.val *
        Contour.pairTestMellin β ρ.val)

/-- Vanishing side of the real Cauchy/Weil extraction: the rectangle/residue
calculation must show that the Gaussian defect coefficient has zero projection
against every `pairTestMellin β` zero kernel.  This is the identity that cannot
be obtained by merely cancelling the existing aggregate Weil formula, because
the coefficient here is the defect energy, not the zero multiplicity. -/
def CauchyWeilGaussianDefectVanishing_target_local : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 →
    ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      GaussianDefectCoefficient_local ρ.val *
        Contour.pairTestMellin β ρ.val = 0

/-- The exact Cauchy/Weil package needed for extraction.  The first component
is convergence of the defect-weighted zero side; the second is the β-family
vanishing identity supplied by the rectangle/residue computation. -/
def CauchyWeilGaussianDefectExtraction_target_local : Prop :=
  CauchyWeilGaussianDefectSummable_target_local ∧
    CauchyWeilGaussianDefectVanishing_target_local

/-- The real extraction theorem in the form needed here: if the
`pairTestMellin β` family is an orthogonality basis for zero coefficients, and
the Cauchy/Weil rectangle supplies vanishing of the Gaussian defect coefficient
against that family for every `β ∈ (0,1)`, then every actual zeta zero has zero
Gaussian defect energy.

The analytic work is exactly in the three hypotheses:
* `h_orth`: completeness/orthogonality of the Mellin test family;
* `h_summable`: legitimate zero-side summation for this coefficient;
* `h_vanish`: the β-family of Cauchy/Weil zero-side identities.

The conclusion is then pure extraction, not an RH assumption. -/
theorem WeilCauchyZeroDefectEnergy_of_zero_orthogonality
    (h_orth :
      ZeroOrthogonality.ZeroCoefficientVanishesByOrthogonality)
    (h_summable : CauchyWeilGaussianDefectSummable_target_local)
    (h_vanish : CauchyWeilGaussianDefectVanishing_target_local) :
    WeilCauchyZeroDefectEnergy_target_local := by
  intro ρ hρ
  have hcoef :
      GaussianDefectCoefficient_local ρ = 0 :=
    h_orth GaussianDefectCoefficient_local h_summable h_vanish ρ hρ
  simpa [GaussianDefectCoefficient_local] using
    (Complex.ofReal_eq_zero.mp hcoef)

/-- Cauchy/Weil defect extraction plus orthogonality gives the per-zero zero
defect-energy target. -/
theorem WeilCauchyZeroDefectEnergy_of_cauchy_weil_extraction
    (h_orth :
      ZeroOrthogonality.ZeroCoefficientVanishesByOrthogonality)
    (h_cw : CauchyWeilGaussianDefectExtraction_target_local) :
    WeilCauchyZeroDefectEnergy_target_local :=
  WeilCauchyZeroDefectEnergy_of_zero_orthogonality
    h_orth h_cw.1 h_cw.2

/-- The existing narrow Weil-Gaussian bridge is exactly the Cauchy/Weil
zero-defect-energy extraction target in this file. -/
theorem WeilCauchyZeroDefectEnergy_of_weil_gaussian_bridge
    (h_bridge : ZD.WeilGaussianBridge) :
    WeilCauchyZeroDefectEnergy_target_local := by
  intro ρ hρ
  exact h_bridge ρ hρ

/-- Conversely, the local zero-defect-energy target supplies the existing
`WeilGaussianBridge` interface. -/
theorem weil_gaussian_bridge_of_WeilCauchyZeroDefectEnergy
    (h_energy : WeilCauchyZeroDefectEnergy_target_local) :
    ZD.WeilGaussianBridge := by
  intro ρ hρ
  exact h_energy ρ hρ

/-- The local Cauchy zero-defect target and the existing narrow Weil-Gaussian
bridge are definitionally the same extraction obligation. -/
theorem WeilCauchyZeroDefectEnergy_iff_weil_gaussian_bridge :
    WeilCauchyZeroDefectEnergy_target_local ↔ ZD.WeilGaussianBridge :=
  ⟨weil_gaussian_bridge_of_WeilCauchyZeroDefectEnergy,
    WeilCauchyZeroDefectEnergy_of_weil_gaussian_bridge⟩

/-- Zero defect energy for actual zeta zeros rules out off-line zeros by the
existing Gaussian AM-GM positivity theorem. -/
theorem no_offline_zeros_of_weil_cauchy_zero_defect_energy
    (h_energy : WeilCauchyZeroDefectEnergy_target_local) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  by_contra h_off
  have hzero : ZD.averageEnergyDefect ZD.gaussianKernel ρ.re = 0 :=
    h_energy ρ hρ
  have hpos : 0 < ZD.averageEnergyDefect ZD.gaussianKernel ρ.re :=
    ZD.gaussianKernel_averageEnergyDefect_pos_offline ρ.re h_off
  linarith

/-- Zero defect energy also gives the balanced prime-channel formulation:
once off-line zeros are excluded, every prime detector reads the balanced value
and hence has zero excess. -/
theorem PrimeChannelBalanced_of_weil_cauchy_zero_defect_energy
    (h_energy : WeilCauchyZeroDefectEnergy_target_local) :
    PrimeChannelBalanced_local := by
  intro ρ hρ p hp
  have hline : ρ.re = 1/2 :=
    no_offline_zeros_of_weil_cauchy_zero_defect_energy h_energy ρ hρ
  have hdet : coshDetector ρ.re (Real.log (↑p)) = 1 :=
    (prime_detector_iff p hp).mpr hline
  exact sub_eq_zero.mpr hdet

/-- The Cauchy zero-defect-energy target supplies the corrected prime-channel
balance extraction, independently of the already-collapsed prime-side link. -/
theorem WeilPrimeChannelBalanceExtraction_of_cauchy_zero_defect_energy
    (h_energy : WeilCauchyZeroDefectEnergy_target_local) :
    WeilPrimeChannelBalanceExtraction_target_local := by
  intro _h_link
  exact PrimeChannelBalanced_of_weil_cauchy_zero_defect_energy h_energy

/-- Prime-channel balance immediately supplies the older finite packet target:
under any putative off-line zero, choose the prime `2`; the singleton packet
has zero total excess because the channel is balanced. -/
theorem PrimeHarmonicZeroBalance_of_prime_channel_balanced
    (h_balanced : PrimeChannelBalanced_local) :
    PrimeHarmonicZeroBalance_local := by
  intro ρ hρ _h_off
  refine ⟨{2}, ?_, ?_, ?_⟩
  · exact Finset.singleton_nonempty 2
  · intro p hp
    rw [Finset.mem_singleton] at hp
    rw [hp]
    exact Nat.prime_two
  · simpa using h_balanced ρ hρ 2 Nat.prime_two

/-- A balanced prime channel rules out off-line zeros by the cosh positive cone:
an off-line zero would have strictly positive excess at every prime, while
balance says the excess is zero. -/
theorem no_offline_zeros_of_prime_channel_balanced
    (h_cosh : CoshNoCancellation_target_local)
    (h_balanced : PrimeChannelBalanced_local) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  by_contra h_off
  obtain ⟨_, h_no_cancel⟩ := h_cosh ρ hρ
  obtain ⟨h_prime_gt_one, _⟩ := h_no_cancel h_off
  have h_pos : 0 < coshDetector ρ.re (Real.log (↑2)) - 1 := by
    exact sub_pos.mpr (h_prime_gt_one 2 Nat.prime_two)
  have h_zero : coshDetector ρ.re (Real.log (↑2)) - 1 = 0 :=
    h_balanced ρ hρ 2 Nat.prime_two
  linarith

/-- Same close with the cosh/no-cancellation input discharged by the theorem
proved in this file.  The only remaining input is prime-channel balance. -/
theorem no_offline_zeros_of_prime_channel_balanced_unconditional_cosh
    (h_balanced : PrimeChannelBalanced_local) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  no_offline_zeros_of_prime_channel_balanced
    CoshNoCancellation_target_local_holds h_balanced

/-- The actual extraction bridge to be proved from Weil's uncancelled prime
identity: the visible prime side must produce a finite zero-balance packet for
any putative off-line zero. -/
def WeilExtractionBridge_target_local : Prop :=
  WeilPrimeSideLink_target_local →
    PrimeHarmonicZeroBalance_local

/-- The corrected balance extraction implies the older packet-shaped extraction
target used by the existing endpoint wrappers. -/
theorem WeilExtractionBridge_of_prime_channel_balance_extraction
    (h_extract : WeilPrimeChannelBalanceExtraction_target_local) :
    WeilExtractionBridge_target_local := by
  intro h_link
  exact PrimeHarmonicZeroBalance_of_prime_channel_balanced (h_extract h_link)

/-- If the extraction bridge is supplied, the already-proved cosh positive cone
rules out every off-line zero.  This is the direct contradiction form of the
route, before invoking the Klein forcer wrapper. -/
theorem no_offline_zeros_of_weil_extraction_bridge
    (h_cosh : CoshNoCancellation_target_local)
    (h_link : WeilPrimeSideLink_target_local)
    (h_extract : WeilExtractionBridge_target_local) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 := by
  intro ρ hρ
  by_contra h_off
  obtain ⟨ps, hne, hps_prime, hsum_zero⟩ := h_extract h_link ρ hρ h_off
  obtain ⟨_, h_no_cancel⟩ := h_cosh ρ hρ
  obtain ⟨_, h_packet_pos⟩ := h_no_cancel h_off
  have hpos : 0 < ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1) :=
    h_packet_pos ps hps_prime hne
  linarith

/-- Weil-extraction close with the local cosh/no-cancellation theorem already
discharged.  The remaining inputs are exactly the prime-side link and the
finite-packet extraction bridge. -/
theorem no_offline_zeros_of_weil_extraction_bridge_unconditional_cosh
    (h_link : WeilPrimeSideLink_target_local)
    (h_extract : WeilExtractionBridge_target_local) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  no_offline_zeros_of_weil_extraction_bridge
    CoshNoCancellation_target_local_holds h_link h_extract

/-- Conversely, if the uncancelled prime-side link is already known to rule out
off-line zeros, then the extraction bridge is vacuous: the off-line hypothesis
needed to request a finite zero-balance packet is impossible.  Together with
`no_offline_zeros_of_weil_extraction_bridge`, this pins down the remaining
substance as exactly the no-offline consequence of Weil's prime side. -/
theorem WeilExtractionBridge_of_no_offline_zeros_from_prime_side
    (h_no_off :
      WeilPrimeSideLink_target_local →
        ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2) :
    WeilExtractionBridge_target_local := by
  intro h_link ρ hρ h_off
  exact False.elim (h_off (h_no_off h_link ρ hρ))

/-- Finite prime-harmonic zero balance plus the cosh no-cancellation theorem
gives the per-zero Klein condition consumed by the existing forcer.  The
contradiction is exactly the no-cancellation step: off-line zeros make every
nonempty finite prime packet have strictly positive cosh excess, so a zero
packet cannot occur unless the zero is on the line. -/
theorem PerZeroKleinCondition_of_prime_harmonic_zero_balance
    (h_cosh : CoshNoCancellation_target_local)
    (h_balance : PrimeHarmonicZeroBalance_local) :
    PerZeroKleinCondition_local := by
  intro ρ hρ
  by_cases h_re_half : ρ.re = 1/2
  · refine ⟨2, Nat.prime_two, ?_⟩
    rw [h_re_half]
    ring_nf
  · obtain ⟨ps, hne, hps_prime, hsum_zero⟩ := h_balance ρ hρ h_re_half
    obtain ⟨_, h_no_cancel⟩ := h_cosh ρ hρ
    obtain ⟨_, h_packet_pos⟩ := h_no_cancel h_re_half
    have hpos : 0 < ∑ p ∈ ps, (coshDetector ρ.re (Real.log (↑p)) - 1) :=
      h_packet_pos ps hps_prime hne
    linarith

/-- Per-zero Klein condition from prime-harmonic zero balance, with the
cosh/no-cancellation package discharged locally. -/
theorem PerZeroKleinCondition_of_prime_harmonic_zero_balance_unconditional_cosh
    (h_balance : PrimeHarmonicZeroBalance_local) :
    PerZeroKleinCondition_local :=
  PerZeroKleinCondition_of_prime_harmonic_zero_balance
    CoshNoCancellation_target_local_holds h_balance

/-- The Weil-to-prime-balance bridge still to be proved: it must consume the
uncancelled Weil prime-side link, together with the cosh/no-cancellation
package, and produce finite prime-harmonic zero balance.  This is the exact
place where HB/Euler rotation symmetry must be connected to Weil's prime side. -/
def WeilPrimeBalanceBridge_target_local : Prop :=
  CoshNoCancellation_target_local →
    WeilPrimeSideLink_target_local →
    PrimeHarmonicZeroBalance_local

/-- The old bridge shape follows from the extraction bridge; the cosh argument
is not part of extraction itself, but is kept as a parameter for the endpoint
shape used below. -/
theorem WeilPrimeBalanceBridge_of_extraction_bridge
    (h_extract : WeilExtractionBridge_target_local) :
    WeilPrimeBalanceBridge_target_local := by
  intro _h_cosh h_link
  exact h_extract h_link

/-- The full prime-harmonic Klein bridge follows from the narrower
Weil-to-prime-balance bridge and the proved no-cancellation extraction above. -/
theorem PrimeHarmonicKleinBridge_of_prime_balance
    (h_balance_bridge : WeilPrimeBalanceBridge_target_local) :
    CoshNoCancellation_target_local →
      WeilPrimeSideLink_target_local →
      PerZeroKleinCondition_local := by
  intro h_cosh h_weil_link
  exact PerZeroKleinCondition_of_prime_harmonic_zero_balance h_cosh
    (h_balance_bridge h_cosh h_weil_link)

/-- Prime-harmonic Klein bridge with the cosh/no-cancellation theorem
discharged.  This is the closing shape needed once the Weil-to-prime-balance
bridge and prime-side link are supplied. -/
theorem PerZeroKleinCondition_of_prime_balance_unconditional_cosh
    (h_balance_bridge : WeilPrimeBalanceBridge_target_local)
    (h_weil_link : WeilPrimeSideLink_target_local) :
    PerZeroKleinCondition_local :=
  PrimeHarmonicKleinBridge_of_prime_balance h_balance_bridge
    CoshNoCancellation_target_local_holds h_weil_link

/-- The prime-harmonic bridge target in the shape consumed by the endpoint. -/
def PrimeHarmonicKleinBridge_target_local : Prop :=
  CoshNoCancellation_target_local →
    WeilPrimeSideLink_target_local →
    PerZeroKleinCondition_local

/-- Zero-wise Weil vanishing supplies the auxiliary per-zero Klein condition. -/
theorem PerZeroKleinCondition_of_WeilVanishesOnZeros
    (h_vanishes : ZD.WeilPositivity.WeilVanishesOnZeros) :
    PerZeroKleinCondition_local := by
  intro ρ hρ
  refine ⟨2, Nat.prime_two, ?_⟩
  have h_half : ρ.re = 1/2 :=
    re_half_of_gaussianPairDefect_zero ρ.re (h_vanishes ρ hρ)
  rw [h_half]
  ring_nf

/-- Prime-harmonic Klein bridge plus the existing forcer gives zero-wise Weil
vanishing. -/
theorem WeilVanishesOnZeros_of_prime_harmonic_bridge_and_forcer
    (h_weil_link : WeilPrimeSideLink_target_local)
    (h_cosh : CoshNoCancellation_target_local)
    (h_bridge : PrimeHarmonicKleinBridge_target_local) :
    ZD.WeilPositivity.WeilVanishesOnZeros := by
  intro ρ hρ
  have h_half : ρ.re = 1/2 :=
    ZD.KleinForcer.klein_forcer_per_zero_real (h_bridge h_cosh h_weil_link) ρ hρ
  exact ZD.KleinForcer.gaussianPairDefect_zero_of_online hρ h_half

/-- Zero-wise Weil vanishing from the prime-harmonic bridge, with the
cosh/no-cancellation theorem discharged locally. -/
theorem WeilVanishesOnZeros_of_prime_harmonic_bridge_and_forcer_unconditional_cosh
    (h_weil_link : WeilPrimeSideLink_target_local)
    (h_bridge : PrimeHarmonicKleinBridge_target_local) :
    ZD.WeilPositivity.WeilVanishesOnZeros :=
  WeilVanishesOnZeros_of_prime_harmonic_bridge_and_forcer
    h_weil_link CoshNoCancellation_target_local_holds h_bridge

/-- Endpoint for the intended route: if the Weil identity, cosh/no-cancellation,
prime-harmonic bridge, and existing forcer are composed, then RH follows. -/
theorem RiemannHypothesis_of_WeilIdentity_cosh_bridge_and_forcer
    (h_weil_link : WeilPrimeSideLink_target_local)
    (h_cosh : CoshNoCancellation_target_local)
    (h_bridge : PrimeHarmonicKleinBridge_target_local) :
    RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_of_WeilVanishesOnZeros
    (WeilVanishesOnZeros_of_prime_harmonic_bridge_and_forcer h_weil_link h_cosh h_bridge)

/-- RH endpoint with the cosh/no-cancellation theorem discharged locally.  The
remaining inputs are the prime-side link and the prime-harmonic Klein bridge. -/
theorem RiemannHypothesis_of_WeilIdentity_bridge_and_forcer_unconditional_cosh
    (h_weil_link : WeilPrimeSideLink_target_local)
    (h_bridge : PrimeHarmonicKleinBridge_target_local) :
    RiemannHypothesis :=
  RiemannHypothesis_of_WeilIdentity_cosh_bridge_and_forcer
    h_weil_link CoshNoCancellation_target_local_holds h_bridge

/-- The final local no-offline-zero close from the residue-rigidity extraction.
The only analytic input is explicit: for each nontrivial zero, the
Weil/Cauchy residue extraction must supply one prime-scale vanishing
double-cosh agreement residue. -/
theorem no_offline_zeros_final
    (h_residue : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧ pairAgreementDefect (↑p) ρ.re = 0) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  no_offline_zeros_of_residue_rigidity h_residue

/-- Final RH endpoint in the residue-rigidity form.  This does not hide the
hard step: the residue extraction is the theorem still needed from the
Weil/Cauchy side. -/
theorem rh_final
    (h_residue : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧ pairAgreementDefect (↑p) ρ.re = 0) :
    RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_of_WeilVanishesOnZeros
    (fun ρ hρ =>
      ZD.KleinForcer.gaussianPairDefect_zero_of_online hρ
        (no_offline_zeros_final h_residue ρ hρ))

/-- Final no-offline-zero endpoint in the prime-harmonic minimum-amplitude
coordinates.  This is the form suggested by comparing the observed amplitude
against the AM-GM minimum. -/
theorem no_offline_zeros_final_of_observed_prime_amplitude_minimum
    (h_min : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧
        actualReducedObservable ρ.re p = balancedPrimeObservable p) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2 :=
  no_offline_zeros_final
    (residue_rigidity_of_observed_prime_amplitude_minimum h_min)

/-- RH endpoint in the observed-prime-amplitude minimum coordinates. -/
theorem rh_final_of_observed_prime_amplitude_minimum
    (h_min : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∃ p : ℕ, Nat.Prime p ∧
        actualReducedObservable ρ.re p = balancedPrimeObservable p) :
    RiemannHypothesis :=
  rh_final (residue_rigidity_of_observed_prime_amplitude_minimum h_min)

/-- RH endpoint from every-prime inverse harmonic minimum. -/
theorem rh_final_of_inverse_prime_harmonic_minimum_every_prime
    (h_min : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        ZD.KleinForcer.amplitude (p : ℝ) ρ.re =
          2 / Real.sqrt (p : ℝ)) :
    RiemannHypothesis :=
  ZD.WeilPositivity.RiemannHypothesis_of_WeilVanishesOnZeros
    (fun ρ hρ =>
      ZD.KleinForcer.gaussianPairDefect_zero_of_online hρ
        (no_offline_zeros_final_of_inverse_prime_harmonic_minimum_every_prime
          h_min ρ hρ))

#print axioms CoshNoCancellation_target_local_holds
#print axioms WeilPrimeSideLink_of_star_and_archPrimeRotation
#print axioms WeilIdentity_of_star_and_archPrimeRotation
#print axioms WeilIdentity_of_prime_side_link
#print axioms WeilPrimeSideLink_of_WeilIdentity
#print axioms WeilPrimeSideLink_iff_WeilIdentity
#print axioms offline_zero_prime_side_link_has_positive_rhs
#print axioms offline_defect_flows_through_every_prime
#print axioms offline_zero_pair_envelope_exceeds_balanced_at_every_prime
#print axioms online_zero_has_no_defect_packet
#print axioms online_zero_pair_envelope_balanced_at_every_prime
#print axioms realAxisFold_eq_ofReal_re
#print axioms gaussianDefectEntireKernel_ofReal
#print axioms GaussianDefectCoefficient_eq_folded_entire
#print axioms energyDefect_zero_of_channels_balanced
#print axioms averageEnergyDefect_zero_of_channels_balanced
#print axioms WeilCauchyZeroDefectEnergy_of_energy_channel_balance
#print axioms no_offline_zeros_of_energy_channel_balance
#print axioms WeilEnergyChannelBalance_of_no_offline_zeros
#print axioms WeilEnergyChannelBalance_iff_no_offline_zeros
#print axioms WeilCauchyZeroDefectEnergy_of_zero_orthogonality
#print axioms WeilCauchyZeroDefectEnergy_of_cauchy_weil_extraction
#print axioms WeilCauchyZeroDefectEnergy_of_weil_gaussian_bridge
#print axioms weil_gaussian_bridge_of_WeilCauchyZeroDefectEnergy
#print axioms WeilCauchyZeroDefectEnergy_iff_weil_gaussian_bridge
#print axioms no_offline_zeros_of_weil_cauchy_zero_defect_energy
#print axioms PrimeChannelBalanced_of_weil_cauchy_zero_defect_energy
#print axioms WeilPrimeChannelBalanceExtraction_of_cauchy_zero_defect_energy
#print axioms PrimeHarmonicZeroBalance_of_prime_channel_balanced
#print axioms no_offline_zeros_of_prime_channel_balanced
#print axioms PerZeroKleinCondition_of_two_cosh_detector_bridge
#print axioms no_offline_zeros_of_two_cosh_detector_bridge
#print axioms critical_line_of_pairAgreementDefect_zero_at_prime
#print axioms no_offline_zeros_of_residue_rigidity
#print axioms residue_rigidity_iff_no_offline_zeros
#print axioms critical_line_of_observed_prime_amplitude_minimum
#print axioms pairAgreementDefect_zero_of_observed_prime_amplitude_minimum
#print axioms no_offline_zeros_of_observed_prime_amplitude_minimum
#print axioms residue_rigidity_of_observed_prime_amplitude_minimum
#print axioms minimum_prime_harmonic_amplitude
#print axioms actualReducedObservable_eq_balanced_of_inverse_prime_harmonic_minimum
#print axioms left_right_detectors_agree_of_inverse_prime_harmonic_minimum
#print axioms left_right_detectors_agree_every_prime_of_inverse_prime_harmonic_minimum
#print axioms pairAgreementDefect_zero_every_prime_of_inverse_prime_harmonic_minimum
#print axioms no_offline_zeros_final_of_inverse_prime_harmonic_minimum_every_prime
#print axioms pairAgreementDefect_zero_every_prime_of_online_zero
#print axioms pairAgreementDefect_pos_every_prime_of_offline_zero
#print axioms pairAgreementDefect_zero_or_positive_every_prime_at_zero
#print axioms pairAgreementDefect_zero_every_prime_iff_no_offline_zeros
#print axioms no_offline_zeros_final_of_pair_cosh_gauss_test_log_prime_zero
#print axioms no_offline_zeros_final_of_detectorPrimeHarmonicObservable_zero
#print axioms rh_final_of_detectorPrimeHarmonicObservable_zero
#print axioms offline_zero_two_cosh_detectors_disagree_at_every_prime
#print axioms WeilExtractionBridge_of_prime_channel_balance_extraction
#print axioms no_offline_zeros_of_prime_channel_balanced_unconditional_cosh
#print axioms no_offline_zeros_of_weil_extraction_bridge
#print axioms no_offline_zeros_of_weil_extraction_bridge_unconditional_cosh
#print axioms WeilExtractionBridge_of_no_offline_zeros_from_prime_side
#print axioms WeilPrimeBalanceBridge_of_extraction_bridge
#print axioms PerZeroKleinCondition_of_prime_harmonic_zero_balance
#print axioms PerZeroKleinCondition_of_prime_harmonic_zero_balance_unconditional_cosh
#print axioms PrimeHarmonicKleinBridge_of_prime_balance
#print axioms PerZeroKleinCondition_of_prime_balance_unconditional_cosh
#print axioms PerZeroKleinCondition_of_WeilVanishesOnZeros
#print axioms WeilVanishesOnZeros_of_prime_harmonic_bridge_and_forcer
#print axioms WeilVanishesOnZeros_of_prime_harmonic_bridge_and_forcer_unconditional_cosh
#print axioms RiemannHypothesis_of_WeilIdentity_cosh_bridge_and_forcer
#print axioms RiemannHypothesis_of_WeilIdentity_bridge_and_forcer_unconditional_cosh
#print axioms no_offline_zeros_final
#print axioms rh_final
#print axioms no_offline_zeros_final_of_observed_prime_amplitude_minimum
#print axioms rh_final_of_observed_prime_amplitude_minimum
#print axioms rh_final_of_inverse_prime_harmonic_minimum_every_prime

end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
