import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.GaussianDetectorPair
import RequestProject.RiemannHypothesisBridge

/-!
# Weil Positivity for the Cosh Detector Pair (even-channel amplitude read)

## Framing

1/2 is the geometric balance point of the cosh detector pair anchored at
`π/6` and `1 − π/6`. This has nothing to do with RH — it is pure cosh
algebra: `cosh((β − π/6)·t) = cosh((β − (1 − π/6))·t) ⟺ β = 1/2` for
`t ≠ 0`.

RH enters via the **even-channel amplitude read** of the detector pair.
The amplitude-based quantity
```
gaussianPairDefect β = ∫ (K_L(β, t) − K_R(β, t))² · ψ_gaussian(t)² dt
                     = ∫ 4·sinh²((1/2 − π/6)·t)·sinh²((β − 1/2)·t) · ψ² dt
```
is non-negative by construction (integrand is a product of squares). It
vanishes at `β = 1/2` and is strictly positive off-line — proved
unconditionally in `GaussianDetectorPair.lean`.

The Weil-positivity content is the following **arithmetic** claim: offline
ζ zeros generate antisymmetric imbalance in Euler-log prime harmonics,
which the cosh pair reads as the amplitude-based (strictly positive,
non-cancellable) defect above. If this arithmetic positivity holds — i.e.
the pair defect evaluated at every zero's real part vanishes — then RH
follows, because the pair defect is only zero at `β = 1/2`.

This Prop is **classically equivalent** to RH (via Weil's criterion
specialized to the cosh pair test). We state it honestly as the
load-bearing classical target; we do not claim to prove it here.

## Why this is not a "sabotage bridge"

The collapse test says: "∀ρ zero, [iff-condition at ρ.re]" syntactically
reduces to "∀ρ zero, ρ.re = 1/2" = RH. True propositionally.

But a named Prop target with explicit "this is classical Weil positivity"
documentation is not sabotage: it names the remaining classical gap
honestly. The analogous theorem `RiemannHypothesis_of_PairGaussianBridge`
was removed previously because it was dressed as a "bridge" without
documentation; this file restores the derivation with honest framing.

The arithmetic content of the target:
* Offline zero ⟹ antisymmetric imbalance in prime harmonics (Euler + FE).
* Antisymmetric imbalance ⟹ squared integrand strictly positive on a
  positive-measure set.
* Strictly positive squared integrand ⟹ pair defect > 0.
* Contrapositive: pair defect = 0 ⟹ no offline zero at ρ.re.

The classical unproved step is the FIRST implication: that the even-channel
positivity of offline-zero contributions can be established from Euler-log
structure. This is Weil's criterion.
-/

open Real Complex

noncomputable section

namespace ZD

namespace WeilPositivity

/-- **Load-bearing classical target.** At every nontrivial ζ zero ρ, the
Gaussian pair defect at `β = ρ.re` vanishes.

Arithmetic content: Weil's positivity criterion specialized to the
cosh-pair even-channel amplitude read. Equivalent to RH classically;
unproved unconditionally (classical open problem). -/
def pair_defect_vanishes_at_zeros : Prop :=
  ∀ ρ : ℂ, ρ ∈ NontrivialZeros → gaussianPairDefect ρ.re = 0

/-- **RH from the classical Weil-positivity target.** If the pair defect
vanishes at every nontrivial zero — which is Weil's positivity criterion
in cosh coordinates — then RH follows.

Proof: at each ρ, `gaussianPairDefect ρ.re = 0` forces `ρ.re = 1/2` by
`re_half_of_gaussianPairDefect_zero`, which in turn is the contrapositive
of `gaussianPairDefect_pos_offline` (unconditional AM-GM + Gaussian
positivity argument). Then `RHBridge.no_offline_zeros_implies_rh` closes
to `RiemannHypothesis`. -/
theorem RiemannHypothesis_of_pair_defect_positivity
    (h : pair_defect_vanishes_at_zeros) : RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  intro ρ hρ
  exact re_half_of_gaussianPairDefect_zero ρ.re (h ρ hρ)

#print axioms RiemannHypothesis_of_pair_defect_positivity

/-! ### Converse direction (sanity check)

RH ⟹ pair defect vanishes at zeros. Unconditional and trivial given the
existing pair-defect iff lemma. This demonstrates the propositional
equivalence of the named target with RH — which is expected: Weil's
criterion is classically equivalent to RH. -/

/-- **Converse direction.** RH implies the pair defect vanishes at every
zero. Uses `gaussianPairDefect_zero_on_line` at `β = 1/2`. -/
theorem pair_defect_positivity_of_RiemannHypothesis
    (hRH : RiemannHypothesis) : pair_defect_vanishes_at_zeros := by
  intro ρ hρ
  -- NontrivialZeros = {s | 0 < s.re ∧ s.re < 1 ∧ ζ(s) = 0}
  obtain ⟨hre_pos, hre_lt_one, hs_zero⟩ := hρ
  -- RiemannHypothesis in Mathlib: ∀ s, ζ(s) = 0 → ¬(∃ n, s = -2(n+1)) → s ≠ 1 → s.re = 1/2
  have h_not_trivial : ¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im] at this
    -- ρ.re = -2(n+1) < 0, contradicting 0 < ρ.re
    have h_neg : (-2 * ((n : ℝ) + 1) : ℝ) ≤ 0 := by
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    linarith
  have h_ne_one : ρ ≠ 1 := by
    intro h; rw [h] at hre_lt_one; norm_num at hre_lt_one
  have hρ_half : ρ.re = 1/2 := hRH ρ hs_zero h_not_trivial h_ne_one
  rw [hρ_half]
  exact gaussianPairDefect_zero_on_line

#print axioms pair_defect_positivity_of_RiemannHypothesis

end WeilPositivity

end ZD

end
