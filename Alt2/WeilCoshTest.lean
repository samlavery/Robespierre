import Mathlib
import RequestProject.PartialWeilFormula
import RequestProject.GaussianClosedForm
import RequestProject.ZetaZeroDefs
import RequestProject.MellinPathToXi

/-!
# Cosh Test Function in the Partial Weil Formula

The partial Weil formula (`PartialWeilFormula.lean`) packages the prime-side
summand
```
weilRHS_prime h = ∑_{p prime, k ≥ 1} (log p / p^{k/2}) · (h(k log p) + h(-k log p))
```
as an unconditional summation definition (not yet proved convergent in
general, but its summand structure is algebraic).

This file plugs the cosh test function
```
coshTest β x := cosh((β − 1/2) · x)
```
into that sum and evaluates the summand pointwise. The resulting per-term
expression is the symmetric log-derivative summand
```
log p · (p^{k(β−1)} + p^{−kβ})
```
which, when summed over primes and k ≥ 1 for `Re β > 1` (Euler product
convergence on both `β` and `1−β` sides is incompatible in the critical
strip — this file stays at the per-term level, where no convergence is
needed).

## Proved content

* `coshTest_even` — the cosh test function is symmetric under `x ↦ −x`.
* `weilRHS_prime_coshTest_summand` — per-term closed form of the Weil
  summand at `h = coshTest β`, matching the Euler-product log-derivative
  summand.

-/

open Real BigOperators

noncomputable section

namespace ZD

/-- **Cosh test function.** `coshTest β x = cosh((β − 1/2)·x)`. Even under
`x ↦ −x`; reduces to the constant `1` at `β = 1/2`. -/
def coshTest (β : ℝ) : ℝ → ℝ := fun x => Real.cosh ((β - 1/2) * x)

/-- The cosh test function is even. -/
theorem coshTest_even (β x : ℝ) : coshTest β (-x) = coshTest β x := by
  unfold coshTest
  rw [mul_neg, Real.cosh_neg]

/-- On the critical line, the cosh test function is identically `1`. -/
theorem coshTest_at_half (x : ℝ) : coshTest (1/2) x = 1 := by
  unfold coshTest
  have hzero : ((1 : ℝ)/2 - 1/2) * x = 0 := by ring
  rw [hzero, Real.cosh_zero]

/-- **Per-term identity.** At each prime-power `(p, k)` with `p` prime and
`k ≥ 1`, the Weil summand of `coshTest β` equals the symmetric
log-derivative summand `log p · (p^{k(β−1)} + p^{−kβ})`. Pure algebra via
`2·cosh = exp + exp` and rpow combination; no convergence or Euler
hypothesis. -/
theorem weilRHS_prime_coshTest_summand
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 1 ≤ k) (β : ℝ) :
    (Real.log p / (p : ℝ) ^ ((k : ℝ) / 2)) *
      (coshTest β ((k : ℝ) * Real.log p) +
        coshTest β (-((k : ℝ) * Real.log p))) =
    Real.log p *
      ((p : ℝ) ^ ((k : ℝ) * (β - 1)) + (p : ℝ) ^ (-((k : ℝ) * β))) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  -- The even-ness collapses the sum to 2·coshTest β (k log p).
  have h_even : coshTest β ((k : ℝ) * Real.log p) +
      coshTest β (-((k : ℝ) * Real.log p)) =
      2 * coshTest β ((k : ℝ) * Real.log p) := by
    rw [coshTest_even β ((k : ℝ) * Real.log p)]; ring
  rw [h_even]
  -- 2·cosh(a) = exp(a) + exp(-a), and exp(α · log p) = p^α via rpow.
  unfold coshTest
  set a : ℝ := (β - 1/2) * ((k : ℝ) * Real.log p) with ha_def
  have h2cosh : 2 * Real.cosh a = Real.exp a + Real.exp (-a) := by
    rw [Real.cosh_eq]; ring
  -- Express exp(a) and exp(-a) as rpow of p.
  have h_exp_pos : Real.exp a = (p : ℝ) ^ ((β - 1/2) * (k : ℝ)) := by
    rw [ha_def, Real.rpow_def_of_pos hp_pos]
    congr 1; ring
  have h_exp_neg : Real.exp (-a) = (p : ℝ) ^ (-((β - 1/2) * (k : ℝ))) := by
    rw [ha_def, Real.rpow_def_of_pos hp_pos]
    congr 1; ring
  -- Assemble: (log p / p^{k/2}) · (p^α + p^{-α}) = log p · (p^{α - k/2} + p^{-α - k/2})
  --   with α = (β-1/2)·k. Then α - k/2 = k(β-1) and -α - k/2 = -kβ.
  rw [h2cosh, h_exp_pos, h_exp_neg]
  -- Combine the two rpow terms with the 1/p^(k/2) prefactor.
  have h_div : Real.log p / (p : ℝ) ^ ((k : ℝ) / 2) =
      Real.log p * (p : ℝ) ^ (-((k : ℝ) / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hp_pos.le]
  rw [h_div]
  have h_lhs_combine :
      Real.log p * (p : ℝ) ^ (-((k : ℝ) / 2)) *
        ((p : ℝ) ^ ((β - 1/2) * (k : ℝ)) +
          (p : ℝ) ^ (-((β - 1/2) * (k : ℝ)))) =
      Real.log p *
        ((p : ℝ) ^ (-((k : ℝ) / 2) + (β - 1/2) * (k : ℝ)) +
          (p : ℝ) ^ (-((k : ℝ) / 2) + -((β - 1/2) * (k : ℝ)))) := by
    rw [Real.rpow_add hp_pos, Real.rpow_add hp_pos]; ring
  rw [h_lhs_combine]
  congr 2
  · congr 1; ring
  · congr 1; ring

/-! ### Gaussian-damped cosh test function

Gaussian damping makes the Weil prime-sum absolutely convergent at every
real `β` (the `exp(−x²)` factor dominates any polynomial or Euler-product
growth). The per-term identity just multiplies the undamped version by the
Gaussian factor. -/

/-- **Gaussian-damped cosh test function.** `coshGaussTest β x =
exp(−x²) · cosh((β − 1/2)·x)`. Schwartz; Weil prime sum converges
absolutely. -/
def coshGaussTest (β : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-x^2) * coshTest β x

/-- The Gaussian-damped cosh test function is even. -/
theorem coshGaussTest_even (β x : ℝ) :
    coshGaussTest β (-x) = coshGaussTest β x := by
  unfold coshGaussTest
  rw [coshTest_even]
  congr 1
  congr 1
  ring

/-- **Per-term identity for Gaussian-damped cosh test function.** At each
`(p, k)` with `p` prime and `k ≥ 1`, the Weil summand of `coshGaussTest β`
equals the log-derivative summand weighted by the Gaussian factor
`exp(−k²·(log p)²)`:
```
(log p / p^{k/2}) · (coshGaussTest β (k log p) + coshGaussTest β (-(k log p)))
  = log p · exp(−k²·(log p)²) · (p^{k(β-1)} + p^{-kβ}).
```
Follows from `weilRHS_prime_coshTest_summand` by factoring out the
Gaussian factor; no convergence required. -/
theorem weilRHS_prime_coshGaussTest_summand
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 1 ≤ k) (β : ℝ) :
    (Real.log p / (p : ℝ) ^ ((k : ℝ) / 2)) *
      (coshGaussTest β ((k : ℝ) * Real.log p) +
        coshGaussTest β (-((k : ℝ) * Real.log p))) =
    Real.log p * Real.exp (-((k : ℝ) * Real.log p)^2) *
      ((p : ℝ) ^ ((k : ℝ) * (β - 1)) + (p : ℝ) ^ (-((k : ℝ) * β))) := by
  -- Factor out the Gaussian damping. `exp(-x²)` is even, so both
  -- `coshGaussTest β (k log p)` and `coshGaussTest β (-(k log p))` carry the
  -- same Gaussian factor `exp(-(k log p)²)`.
  have h_gauss_even :
      Real.exp (-((-((k : ℝ) * Real.log p))^2)) =
      Real.exp (-((k : ℝ) * Real.log p)^2) := by
    congr 1; ring
  have h_split :
      coshGaussTest β ((k : ℝ) * Real.log p) +
        coshGaussTest β (-((k : ℝ) * Real.log p)) =
      Real.exp (-((k : ℝ) * Real.log p)^2) *
        (coshTest β ((k : ℝ) * Real.log p) +
          coshTest β (-((k : ℝ) * Real.log p))) := by
    unfold coshGaussTest
    rw [h_gauss_even]
    ring
  rw [h_split]
  have h_undamped := weilRHS_prime_coshTest_summand p hp k hk β
  have h_rearrange :
      Real.log p / (p : ℝ) ^ ((k : ℝ) / 2) *
        (Real.exp (-((k : ℝ) * Real.log p)^2) *
          (coshTest β ((k : ℝ) * Real.log p) +
            coshTest β (-((k : ℝ) * Real.log p)))) =
      Real.exp (-((k : ℝ) * Real.log p)^2) *
        (Real.log p / (p : ℝ) ^ ((k : ℝ) / 2) *
          (coshTest β ((k : ℝ) * Real.log p) +
            coshTest β (-((k : ℝ) * Real.log p)))) := by ring
  rw [h_rearrange, h_undamped]
  ring

#print axioms coshTest_even
#print axioms coshTest_at_half
#print axioms weilRHS_prime_coshTest_summand
#print axioms coshGaussTest_even
#print axioms weilRHS_prime_coshGaussTest_summand

/-! ### Gaussian Weil pair — root of the partial Weil formula

The Gaussian test pair `(h, φ) = (exp(−x²), exp(−z²/4))` gives the cleanest
concrete instance of the Weil explicit formula via this project's W1 closed
form (`GaussianClosedForm.I_theta_of_gaussian_closed_form`). The zero-side
sum collapses to a closed form via
`MellinAmplitudeBounds.weilLHS_exp_neg_quarter_sq_eq_observable_sum`
combined with W1; the prime side is the per-term identity above. The
archimedean side is `h(0)·log π + (1/2π)·∫ φ(γ)·log(1/4 + iγ/2) dγ`.

The three sides are each unconditional in closed-form; the Weil identity
itself `WeilFormula h φ` is the remaining classical analytic-number-theory
step. -/

/-- **Gaussian Weil pair, zero side in closed form.** Combining W1 with
the zero-sum collapse: `weilLHS(z ↦ exp(−z²/4)) = Σ_ρ exp((ρ − 1/2)²/4)`. -/
theorem weilLHS_gaussian_zero_sum_closed_form :
    weilLHS (fun z : ℂ => Complex.exp (-z^2 / 4)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        Complex.exp ((ρ.val - (1/2 : ℂ))^2 / 4) := by
  unfold weilLHS
  apply tsum_congr
  intro ρ
  show Complex.exp (-((ρ.val - (1/2 : ℂ)) / Complex.I)^2 / 4) =
    Complex.exp ((ρ.val - (1/2 : ℂ))^2 / 4)
  congr 1
  have h_algebra :
      -((ρ.val - (1/2 : ℂ)) / Complex.I)^2 / 4 = (ρ.val - (1/2 : ℂ))^2 / 4 := by
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  exact h_algebra

/-- **MellinXi-based zero-side identity.** At every nontrivial zero ρ,
`completedRiemannZeta₀(ρ) = −1/(ρ(ρ−1))` (from `MellinPathToXi`). Applied
to the Weil-LHS with test function `φ(z) := 1/(z² + 1/4)`:
```
φ((ρ−1/2)/I) = 1/((γ − i(β−1/2))² + 1/4) = -1/(ρ(ρ−1)) = completedRiemannZeta₀(ρ)
```
so `weilLHS φ = Σ_ρ completedRiemannZeta₀(ρ) = Σ_ρ -1/(ρ(ρ-1))`. Clean
route through MellinXi, no Gaussian needed. -/
theorem weilLHS_inv_quarter_plus_sq_eq_mellin_sum :
    weilLHS (fun z : ℂ => (1 : ℂ) / (z^2 + 1/4)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}, completedRiemannZeta₀ ρ.val := by
  unfold weilLHS
  apply tsum_congr
  intro ρ
  show (1 : ℂ) / (((ρ.val - (1/2 : ℂ)) / Complex.I)^2 + 1/4) =
    completedRiemannZeta₀ ρ.val
  -- Algebra: ((ρ-1/2)/I)² + 1/4 = -(ρ-1/2)² + 1/4 = -ρ² + ρ = -ρ(ρ-1)
  -- So 1/(((ρ-1/2)/I)² + 1/4) = -1/(ρ(ρ-1)) = completedRiemannZeta₀(ρ) at zero
  have hρ := ρ.property
  have hρ_re_pos : 0 < ρ.val.re := hρ.1
  have hρ_re_lt_one : ρ.val.re < 1 := hρ.2.1
  have hρ_ne_zero : ρ.val ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hρ_re_pos; linarith
  have hρ_ne_one : ρ.val ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hρ_re_lt_one; linarith
  have hprod_ne : ρ.val * (ρ.val - 1) ≠ 0 :=
    mul_ne_zero hρ_ne_zero (sub_ne_zero.mpr hρ_ne_one)
  have h_algebra :
      ((ρ.val - (1/2 : ℂ)) / Complex.I)^2 + 1/4 = -(ρ.val * (ρ.val - 1)) := by
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h_algebra]
  -- Unconditional completedRiemannZeta₀ value at zero, via Mellin identity.
  have h_mellin : completedRiemannZeta₀ ρ.val = -1 / (ρ.val * (ρ.val - 1)) := by
    rw [← I_theta_of_ψ_mellin_eq_completedRiemannZeta₀]
    exact observable_value_at_zero ρ.val hρ
  rw [h_mellin]
  field_simp

/-- **Gaussian Weil pair — unconditional zero-side identity.** This is the
root: the zero-side `weilLHS` for Weil-test `φ(z) := exp(-z²/4)` equals a
clean sum over nontrivial ζ-zeros of `exp((ρ-1/2)²/4)`. Every step is
axiom-clean, no RH assumed.

To complete the full Weil partial formula for the Gaussian pair
`(h, φ) = (exp(-x²), exp(-z²/4))`, combine this zero-side with:
* the prime side's per-term identity `weilRHS_prime_coshGaussTest_summand`
  (which gives the Euler-product log-derivative structure at each `(p, k)`);
* the arch side `weilRHS_arch h φ`, evaluable as a standard Gaussian × log
  integral;
* the Weil identity `WeilFormula h φ` tying them together — the one
  remaining classical ANT step. -/
theorem weil_gaussian_pair_zero_side :
    weilLHS (fun z : ℂ => Complex.exp (-z^2 / 4)) =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        Complex.exp ((ρ.val - (1/2 : ℂ))^2 / 4) :=
  weilLHS_gaussian_zero_sum_closed_form

#print axioms weilLHS_gaussian_zero_sum_closed_form
#print axioms weilLHS_inv_quarter_plus_sq_eq_mellin_sum
#print axioms weil_gaussian_pair_zero_side

/-! ### (1) Summability of the Gaussian-damped cosh prime sum

The user's convergence note: prime harmonics come from Euler's product
where it converges, so the prime-side sum is convergent. For the
Gaussian-damped cosh test `h(x) = exp(−x²)·cosh((β−1/2)·x)`, every
summand has the Gaussian factor `exp(−(k·log p)²)` that beats any
polynomial growth in `p^{k(β−1/2)}`, giving absolute convergence for every
real `β` (not only `β > 1`). -/

/-- **Prime-harmonic summand's Gaussian decay factor (simple form).** The
Gaussian-damped cosh prime summand at `(p, k)` has an explicit Gaussian
factor `exp(−(k·log p)²)` that beats any polynomial growth in `k·log p`,
giving per-term convergence. The per-term identity is
`weilRHS_prime_coshGaussTest_summand` above. -/
theorem coshGaussTest_summand_has_gaussian_factor
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 1 ≤ k) (β : ℝ) :
    (Real.log p / (p : ℝ) ^ ((k : ℝ) / 2)) *
      (coshGaussTest β ((k : ℝ) * Real.log p) +
        coshGaussTest β (-((k : ℝ) * Real.log p))) =
    Real.log p * Real.exp (-((k : ℝ) * Real.log p)^2) *
      ((p : ℝ) ^ ((k : ℝ) * (β - 1)) +
       (p : ℝ) ^ (-((k : ℝ) * β))) := by
  exact weilRHS_prime_coshGaussTest_summand p hp k hk β

/-- **Summability target.** The Gaussian-damped cosh prime sum is Summable
for every real `β`, via Euler-product absolute convergence plus the Gaussian
suppression factor. Named `Prop` target. -/
def coshGaussTest_prime_sum_summable_target (β : ℝ) : Prop :=
  Summable (fun pk : ℕ × ℕ =>
    if Nat.Prime pk.1 ∧ 1 ≤ pk.2 then
      (Real.log pk.1 / ((pk.1 : ℝ) ^ ((pk.2 : ℝ) / 2))) *
      (coshGaussTest β ((pk.2 : ℝ) * Real.log pk.1) +
        coshGaussTest β (-((pk.2 : ℝ) * Real.log pk.1)))
    else 0)

/-! ### (2) Gaussian Weil-pair identity assembly

Combining the closed-form zero side (via W1) with the classical Weil
identity for the Gaussian pair `(h, φ) = (exp(−x²)·cosh((β−1/2)·x),
exp(−z²/4))`: IF `WeilFormula h φ` holds (classical analytic number
theory, a single named Prop — not an RH-equivalent assumption), THEN
```
Σ_ρ exp((ρ−1/2)²/4) = weilRHS_arch h φ − weilRHS_prime h.
```
This is the **complete partial Weil formula** for the Gaussian pair,
unconditional on RH, conditional on the classical WeilFormula identity. -/

/-- **Gaussian Weil-pair identity (conditional on classical WeilFormula).**
If `WeilFormula (fun x => exp(−x²)) (fun z => exp(−z²/4))` holds, then
the zero-side sum `Σ_ρ exp((ρ−1/2)²/4)` equals the archimedean minus
prime-sum closed form. -/
theorem gaussian_weil_pair_identity
    (hWF : WeilFormula (fun x : ℝ => Real.exp (-x^2))
                       (fun z : ℂ => Complex.exp (-z^2/4))) :
    ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        Complex.exp ((ρ.val - (1/2 : ℂ))^2 / 4) =
      weilRHS_arch (fun x : ℝ => Real.exp (-x^2))
                   (fun z : ℂ => Complex.exp (-z^2/4)) -
        (weilRHS_prime (fun x : ℝ => Real.exp (-x^2)) : ℂ) := by
  rw [← weilLHS_gaussian_zero_sum_closed_form]
  exact hWF

/-- **MellinXi Weil-pair identity (conditional on classical WeilFormula).**
Analogous assembly for the MellinXi test function `φ(z) = 1/(z² + 1/4)`:
the zero-side sum `Σ_ρ completedRiemannZeta₀(ρ) = −Σ_ρ 1/(ρ(ρ−1))` equals
the arch-minus-prime closed form for the corresponding Fourier-partner `h`. -/
theorem mellin_weil_pair_identity
    (h : ℝ → ℝ)
    (hWF : WeilFormula h (fun z : ℂ => (1 : ℂ) / (z^2 + 1/4))) :
    ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        completedRiemannZeta₀ ρ.val =
      weilRHS_arch h (fun z : ℂ => (1 : ℂ) / (z^2 + 1/4)) -
        (weilRHS_prime h : ℂ) := by
  rw [← weilLHS_inv_quarter_plus_sq_eq_mellin_sum]
  exact hWF

#print axioms gaussian_weil_pair_identity
#print axioms mellin_weil_pair_identity

/-! ### Parseval L²-norm identity for I_theta_of ψ_gaussian on the critical line

Mellin-native consequence of W1: on the critical line `Re s = 1/2`, the
Gaussian observable's squared modulus is `π · exp(−γ²/2)`, and its
γ-integral over `Ioi 0` evaluates to `π · √(π/2)` — a closed-form
classical Parseval identity. Proved unconditionally via W1's closed form
+ the standard half-line Gaussian moment. -/

/-- **Closed-form squared modulus on the critical line.** From W1:
`|I_theta_of ψ_gaussian (1/2 + iγ)|² = π · exp(−γ²/2)`. -/
theorem I_theta_gaussian_normSq_critical_line (γ : ℝ) :
    Complex.normSq (I_theta_of ψ_gaussian ((1/2 : ℂ) + (γ : ℂ) * Complex.I)) =
      Real.pi * Real.exp (-γ^2 / 2) := by
  rw [I_theta_of_gaussian_closed_form]
  have h_arg : ((1/2 : ℂ) + (γ : ℂ) * Complex.I) - (1/2 : ℂ) = (γ : ℂ) * Complex.I := by
    ring
  rw [h_arg]
  have h_sq : ((γ : ℂ) * Complex.I)^2 = -(γ : ℂ)^2 := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [h_sq]
  have h_exp_real :
      Complex.exp (-(γ : ℂ)^2 / 4) = ((Real.exp (-γ^2 / 4) : ℝ) : ℂ) := by
    rw [show (-(γ : ℂ)^2 / 4) = ((-γ^2 / 4 : ℝ) : ℂ) from by push_cast; ring]
    rw [← Complex.ofReal_exp]
  rw [h_exp_real]
  rw [show ((Real.sqrt Real.pi : ℂ)) * ((Real.exp (-γ^2 / 4) : ℝ) : ℂ) =
        ((Real.sqrt Real.pi * Real.exp (-γ^2 / 4) : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.normSq_ofReal]
  have h_pi_nn : 0 ≤ Real.pi := Real.pi_pos.le
  have h_sq_pi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt h_pi_nn
  have h_exp_sq : Real.exp (-γ^2 / 4) * Real.exp (-γ^2 / 4) =
      Real.exp (-γ^2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  have : (Real.sqrt Real.pi * Real.exp (-γ^2 / 4))^2 =
      Real.pi * Real.exp (-γ^2 / 2) := by
    rw [sq]
    calc Real.sqrt Real.pi * Real.exp (-γ^2 / 4) *
          (Real.sqrt Real.pi * Real.exp (-γ^2 / 4))
        = (Real.sqrt Real.pi * Real.sqrt Real.pi) *
          (Real.exp (-γ^2 / 4) * Real.exp (-γ^2 / 4)) := by ring
      _ = Real.pi * Real.exp (-γ^2 / 2) := by rw [h_sq_pi, h_exp_sq]
  linarith [this]

/-- **Half-line L²-norm identity.** The γ > 0 integral of the squared
modulus of the Gaussian observable on the critical line equals
`π · √(π/2)`. Closed form via W1 + standard half-Gaussian moment. -/
theorem I_theta_gaussian_L2_norm_critical_line :
    ∫ γ in Set.Ioi (0:ℝ),
        Complex.normSq (I_theta_of ψ_gaussian ((1/2 : ℂ) + (γ : ℂ) * Complex.I)) =
      Real.pi * Real.sqrt (Real.pi / 2) := by
  have h_rewrite : ∀ γ : ℝ,
      Complex.normSq (I_theta_of ψ_gaussian ((1/2 : ℂ) + (γ : ℂ) * Complex.I)) =
      Real.pi * Real.exp (-γ^2 / 2) := I_theta_gaussian_normSq_critical_line
  simp_rw [h_rewrite]
  rw [MeasureTheory.integral_const_mul]
  have h_half_gauss : ∫ γ in Set.Ioi (0:ℝ), Real.exp (-γ^2 / 2) =
      Real.sqrt (Real.pi / 2) := by
    have h_eq : (fun γ : ℝ => Real.exp (-γ^2 / 2)) =
                (fun γ : ℝ => Real.exp (-(1/2) * γ^2)) := by
      funext γ; congr 1; ring
    rw [h_eq]
    rw [integral_gaussian_Ioi (1/2 : ℝ)]
    rw [show Real.pi / (1/2 : ℝ) = 4 * (Real.pi / 2) from by ring]
    rw [show (4 : ℝ) = 2^2 from by norm_num]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2^2)]
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [h_half_gauss]

#print axioms I_theta_gaussian_normSq_critical_line
#print axioms I_theta_gaussian_L2_norm_critical_line

end ZD

end
