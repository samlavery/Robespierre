import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilRightEdge

/-!
# Weil Arch–Prime Identity — Cycle 48 (load-bearing π/6 step)

Goal: prove the **algebraic identity** that the archimedean side of the Weil
explicit formula for the cosh-pair Gaussian test equals its prime side,
IDENTICALLY (not contingent on RH).

```
∫_{Re s = σ₀} arch(s) · pairTestMellin β s ds
  = ∫_{Re s = σ₀} (Σ_n Λ(n)/n^s) · pairTestMellin β s ds
```

for appropriate contour σ₀. The equality reduces (via the cosh-pair's sinh²
factorization + Gaussian Mellin closed form + digamma identities) to a relation
between:

* Digamma `Γ'/Γ` at shifted arguments `(s/2) ± (π/6)·(some coefficient)`.
* Von Mangoldt sums `Σ Λ(n)/n^s` evaluated against the cosh-pair readings.

The 6th-root-of-unity structure of `π/3` (`cos(π/3) = 1/2`, `sin(π/6) = 1/2`)
forces specific algebraic cancellations that make the two sides identically
equal. This is **geometric / algebraic**, not number-theoretic in the RH sense.

## Delivered in this file

* `WeilArchPrimeIdentityTarget` — named Prop target.
* `arch_via_cosh_pair_fourier` — the arch operator's `Gammaℝ'/Gammaℝ` split
  into `−(log π)/2 + (1/2)(Γ'/Γ)(s/2)` (from the `Gammaℝ = π^(−s/2)·Γ(s/2)`
  definition).

## Deferred (remaining in cycle 48, the heart of the proof)

* Explicit pairing of `arch(s)` against `pairTestMellin β s` on a vertical
  contour.
* Explicit evaluation of `Γ'/Γ(s/2)` at `s/2 = (2β − π/3)/4 + some imaginary`
  via digamma reflection + recursion.
* Matching term-by-term with von Mangoldt `Λ(p^k)·pairTestMellin β (2+it)` sums
  at axes `π/6`, `1 − π/6`.

Estimated remaining work: 800–1500 lines. The load-bearing cycle.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Arch operator in digamma form.** Log-derivative of `Gammaℝ(s) = π^(−s/2)·Γ(s/2)`:

```
Gammaℝ'(s)/Gammaℝ(s) = −(log π)/2 + (1/2) · (Γ'/Γ)(s/2).
```

Classical. Derivable from `Complex.Gammaℝ_def` + log-deriv of product + chain rule.
This is the explicit form of the arch operator used in cycle 48's pairing. -/
def gammaℝ_logDeriv_digamma_form_target : Prop :=
  ∀ s : ℂ, s.Gammaℝ ≠ 0 → (∀ n : ℕ, s ≠ -(2 * (n : ℂ))) →
    deriv Complex.Gammaℝ s / s.Gammaℝ =
      -(Complex.log Real.pi) / 2 + (1 / 2) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2))

/-- **Named target for cycle 48.** The arch–prime identity for the cosh-pair
Gaussian test function, on a vertical contour at fixed real part.

Form: for every `β` and appropriate `σ₀`,

```
∫_{Re s = σ₀} arch(s) · pairTestMellin β s · ds
  = ∫_{Re s = σ₀} (prime L-series) · pairTestMellin β s · ds.
```

The equality is algebraic (not RH-dependent), forced by the 6th-root-of-unity
structure of the cosh-pair axes at `π/6, 1−π/6` (strip width `1 − π/3`). -/
def WeilArchPrimeIdentityTarget (β : ℝ) : Prop :=
  ∀ σ₀ : ℝ, σ₀ > 1 →
    (∫ t : ℝ,
      (deriv Complex.Gammaℝ ((σ₀ : ℂ) + (t : ℂ) * I) /
        ((σ₀ : ℂ) + (t : ℂ) * I).Gammaℝ +
       deriv Complex.Gammaℝ (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) /
        (1 - ((σ₀ : ℂ) + (t : ℂ) * I)).Gammaℝ) *
      pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I))
    = (∫ t : ℝ,
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ₀ : ℂ) + (t : ℂ) * I) *
      pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I))

#print axioms gammaℝ_logDeriv_digamma_form_target
#print axioms WeilArchPrimeIdentityTarget

/-- **Arch operator digamma form — proved.** The log-derivative of
`Gammaℝ(s) = π^(−s/2)·Γ(s/2)` has the explicit form:

```
Gammaℝ'(s)/Gammaℝ(s) = −(log π)/2 + (1/2) · (Γ'/Γ)(s/2).
```

Discharges `gammaℝ_logDeriv_digamma_form_target`. -/
theorem gammaℝ_logDeriv_digamma_form :
    ∀ s : ℂ, s.Gammaℝ ≠ 0 → (∀ n : ℕ, s ≠ -(2 * (n : ℂ))) →
    deriv Complex.Gammaℝ s / s.Gammaℝ =
      -(Complex.log Real.pi) / 2 +
      (1 / 2) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) := by
  intro s hs_ne h_ne_2n
  -- s/2 ≠ -n via h_ne_2n.
  have h_half_ne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have : s = -(2 * (m : ℂ)) := by linear_combination 2 * h
    exact h_ne_2n m this
  -- Γ(s/2) ≠ 0 from Gammaℝ(s) ≠ 0.
  have hGamma_ne : Complex.Gamma (s / 2) ≠ 0 := by
    intro h
    apply hs_ne
    rw [Complex.Gammaℝ_def]
    rw [h]; ring
  -- π^(-s/2) ≠ 0 (π > 0).
  have hpi_cpow_ne : ((Real.pi : ℂ)) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_pos.ne'))
  -- Differentiability.
  have hΓ_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ h_half_ne
  have hΓ_comp_diff : DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (t / 2)) s := by
    have h1 : DifferentiableAt ℂ (fun t : ℂ => t / 2) s := differentiableAt_id.div_const 2
    exact hΓ_diff.comp s h1
  have hpi_diff : DifferentiableAt ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2)) s := by
    apply DifferentiableAt.const_cpow ((differentiableAt_id.neg).div_const 2)
    left; exact_mod_cast Real.pi_pos.ne'
  -- Combined HasDerivAt for Gammaℝ at s.
  have hpi_pos : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h_neg_half_hd : HasDerivAt (fun t : ℂ => -t / 2) (-(1/2)) s := by
    have := (hasDerivAt_id s).neg.div_const 2
    convert this using 1; ring
  have h_half_hd : HasDerivAt (fun t : ℂ => t / 2) (1/2) s :=
    (hasDerivAt_id s).div_const 2
  have h_pi_hd : HasDerivAt (fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-(1/2))) s :=
    h_neg_half_hd.const_cpow (Or.inl hpi_pos)
  have h_Gamma_hd : HasDerivAt (fun t : ℂ => Complex.Gamma (t / 2))
      (deriv Complex.Gamma (s / 2) * (1/2)) s :=
    hΓ_diff.hasDerivAt.comp s h_half_hd
  have h_prod_hd_raw := h_pi_hd.mul h_Gamma_hd
  have hfg_eq : ∀ t : ℂ,
      ((fun t : ℂ => (Real.pi : ℂ) ^ (-t / 2)) * fun t : ℂ => Complex.Gamma (t / 2)) t =
      Complex.Gammaℝ t := by
    intro t; show (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2) = t.Gammaℝ
    exact (Complex.Gammaℝ_def t).symm
  have h_prod_hd : HasDerivAt Complex.Gammaℝ
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-(1/2)) * Complex.Gamma (s / 2) +
        (Real.pi : ℂ) ^ (-s / 2) * (deriv Complex.Gamma (s / 2) * (1/2))) s :=
    h_prod_hd_raw.congr_of_eventuallyEq (Filter.Eventually.of_forall hfg_eq)
  rw [h_prod_hd.deriv]
  -- Now algebraic simplification: divide by Gammaℝ(s) = π^(-s/2) · Γ(s/2).
  have hGammaℝ_val : s.Gammaℝ = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
    Complex.Gammaℝ_def s
  rw [hGammaℝ_val]
  field_simp

#print axioms gammaℝ_logDeriv_digamma_form

/-- **Fully explicit arch form.** Combining cycle 35 (`zeta_logDeriv_arch_form`)
with cycle 48's `gammaℝ_logDeriv_digamma_form`:

```
−ζ'(s)/ζ(s) = −log π + (1/2)·(Γ'/Γ)(s/2) + (1/2)·(Γ'/Γ)((1−s)/2) + ζ'(1−s)/ζ(1−s).
```

This is the classical Weil arch-operator + prime-at-reflected-argument
decomposition, fully explicit in digamma. -/
theorem zeta_logDeriv_full_arch_form {s : ℂ}
    (hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1)
    (hζ_s_ne : riemannZeta s ≠ 0) (hζ_1s_ne : riemannZeta (1 - s) ≠ 0)
    (hGammaℝ_s : s.Gammaℝ ≠ 0) (hGammaℝ_1s : (1 - s).Gammaℝ ≠ 0)
    (h_s_ne_2n : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)))
    (h_1s_ne_2n : ∀ n : ℕ, (1 - s) ≠ -(2 * (n : ℂ))) :
    -(deriv riemannZeta s / riemannZeta s) =
      -(Complex.log Real.pi) +
      (1 / 2) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) +
      (1 / 2) * (deriv Complex.Gamma ((1 - s) / 2) / Complex.Gamma ((1 - s) / 2)) +
      deriv riemannZeta (1 - s) / riemannZeta (1 - s) := by
  have harch := zeta_logDeriv_arch_form hs_ne_zero hs_ne_one hζ_s_ne hζ_1s_ne
    hGammaℝ_s hGammaℝ_1s
  rw [harch]
  rw [gammaℝ_logDeriv_digamma_form s hGammaℝ_s h_s_ne_2n]
  rw [gammaℝ_logDeriv_digamma_form (1 - s) hGammaℝ_1s h_1s_ne_2n]
  ring

#print axioms zeta_logDeriv_full_arch_form

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 48 deeper build-out — digamma infrastructure (tasks A1–A4)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Digamma function** `ψ(s) = Γ'(s)/Γ(s)` — the logarithmic derivative of Γ.
Task 48-A1. -/
noncomputable def digamma (s : ℂ) : ℂ := deriv Complex.Gamma s / Complex.Gamma s

/-- Digamma in terms of `logDeriv` (alternate form). -/
theorem digamma_eq_logDeriv (s : ℂ) :
    digamma s = logDeriv Complex.Gamma s := by
  rw [logDeriv_apply]
  rfl

/-- **Task 48-A2 (named target, kept for backward compatibility).** -/
def digamma_differentiableAt_target (s : ℂ) : Prop :=
  (∀ m : ℕ, s ≠ -(m : ℂ)) → DifferentiableAt ℂ digamma s

/-- The set of complex numbers that are not non-positive integers is open. This is the
domain on which the Gamma function is holomorphic. Used as a helper for
`digamma_differentiableAt`. -/
lemma nonpole_isOpen : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  -- Step 1: for `m` sufficiently large, `dist s (-m) ≥ 1`.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ m ≥ M, dist s (-(m : ℂ)) ≥ 1 := by
    refine ⟨⌈1 - s.re⌉₊ + 1, ?_⟩
    intro m hm
    have h_re_ge : (s.re + m : ℝ) ≥ 1 := by
      have h1 : ((⌈1 - s.re⌉₊ : ℝ) : ℝ) ≥ 1 - s.re := Nat.le_ceil _
      have h2 : (m : ℝ) ≥ (⌈1 - s.re⌉₊ : ℝ) + 1 := by exact_mod_cast hm
      linarith
    have h_re : (s - (-(m : ℂ))).re = s.re + m := by simp
    rw [Complex.dist_eq]
    have := Complex.re_le_norm (s - (-(m : ℂ)))
    rw [h_re] at this
    linarith
  -- Step 2: for each `m`, `dist s (-m) > 0`.
  have hpos : ∀ m : ℕ, 0 < dist s (-(m : ℂ)) := fun m => dist_pos.mpr (hs m)
  -- Step 3: take `δ = min` of `dist s (-m)` for `m ≤ M` (finite nonempty set of positives).
  let f : ℕ → ℝ := fun m => dist s (-(m : ℂ))
  let T : Finset ℕ := Finset.range (M + 1)
  have hT_ne : T.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  let dists : Finset ℝ := T.image f
  have hdists_ne : dists.Nonempty := hT_ne.image f
  have hδ_pos : 0 < dists.min' hdists_ne := by
    rw [Finset.lt_min'_iff]
    intro y hy
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hy
    exact hpos m
  set δ := dists.min' hdists_ne
  -- Step 4: `ε = min(1/2, δ/2)`. On the open ball of radius `ε` around `s`, no point is `-m`.
  let ε : ℝ := min (1/2) (δ/2)
  have hε_pos : 0 < ε := lt_min (by norm_num) (by linarith)
  have hball : Metric.ball s ε ∈ nhds s := Metric.ball_mem_nhds s hε_pos
  apply Filter.mem_of_superset hball
  intro z hz m
  rw [Metric.mem_ball] at hz
  intro heq
  rw [heq] at hz
  have hz' : dist s (-(m : ℂ)) < ε := by rwa [dist_comm] at hz
  by_cases hmM : m ≤ M
  · have hmT : m ∈ T := Finset.mem_range.mpr (Nat.lt_succ_of_le hmM)
    have hmem : f m ∈ dists := Finset.mem_image.mpr ⟨m, hmT, rfl⟩
    have hδ_le : δ ≤ f m := Finset.min'_le _ _ hmem
    have hz'' : f m < δ/2 := lt_of_lt_of_le hz' (min_le_right _ _)
    simp only [f] at hδ_le hz''
    linarith
  · push_neg at hmM
    have h1 : 1 ≤ dist s (-(m : ℂ)) := hM m hmM.le
    have hz'' : dist s (-(m : ℂ)) < 1/2 := lt_of_lt_of_le hz' (min_le_left _ _)
    linarith

/-- **Task 48-A2 — proved.** The digamma function `ψ(s) = Γ'(s)/Γ(s)` is complex
differentiable at every point `s` that is not a non-positive integer.

Proof: on the open set `{z | ∀ m, z ≠ -m}`, `Γ` is differentiable, hence (by Cauchy's
theorem for holomorphic derivatives: `DifferentiableOn.deriv`) so is `deriv Γ`. Since
`Γ(s) ≠ 0` (by `Complex.Gamma_ne_zero`), the quotient `deriv Γ / Γ` is differentiable at
`s`. -/
theorem digamma_differentiableAt {s : ℂ} (h : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    DifferentiableAt ℂ digamma s := by
  let U : Set ℂ := {z : ℂ | ∀ m : ℕ, z ≠ -(m : ℂ)}
  have hU_open : IsOpen U := nonpole_isOpen
  have hsU : s ∈ U := h
  have hU_nhds : U ∈ nhds s := hU_open.mem_nhds hsU
  have hΓ_diffOn : DifferentiableOn ℂ Complex.Gamma U := fun z hz =>
    (Complex.differentiableAt_Gamma z hz).differentiableWithinAt
  have hderiv_diffOn : DifferentiableOn ℂ (deriv Complex.Gamma) U :=
    hΓ_diffOn.deriv hU_open
  have hderiv_diff : DifferentiableAt ℂ (deriv Complex.Gamma) s :=
    hderiv_diffOn.differentiableAt hU_nhds
  have hΓ_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma _ h
  have hΓ_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero h
  exact hderiv_diff.div hΓ_diff hΓ_ne

/-- **Task 48-A3 — proved.** Digamma recurrence `ψ(s+1) = ψ(s) + 1/s`.

Proof: from `Γ(s+1) = s · Γ(s)` (`Complex.Gamma_add_one`). Differentiating both sides
(using `HasDerivAt.congr_of_eventuallyEq` via `EventuallyEq.deriv_eq` on an open
neighborhood `{t | t ≠ 0}`) gives `Γ'(s+1) = Γ(s) + s·Γ'(s)`. Dividing by
`Γ(s+1) = s·Γ(s)` yields the recurrence. -/
theorem digamma_recurrence {s : ℂ} (h : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    digamma (s + 1) = digamma s + 1 / s := by
  -- `s ≠ 0` is `s ≠ -0`.
  have hs_ne : s ≠ 0 := by
    have := h 0; simpa using this
  -- `s + 1 ≠ -m` since that would mean `s = -(m+1)`.
  have h_s1 : ∀ m : ℕ, s + 1 ≠ -(m : ℂ) := by
    intro m heq
    have : s = -((m + 1 : ℕ) : ℂ) := by push_cast; linear_combination heq
    exact h (m + 1) this
  have hΓ_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero h
  have hΓ_s1_ne : Complex.Gamma (s + 1) ≠ 0 := Complex.Gamma_ne_zero h_s1
  have hΓ_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma _ h
  have hΓ_diff_s1 : DifferentiableAt ℂ Complex.Gamma (s + 1) :=
    Complex.differentiableAt_Gamma _ h_s1
  -- Differentiate `Γ(t+1) = t·Γ(t)` at `t = s`. Both sides have `HasDerivAt`s,
  -- and they agree on the open neighborhood `{t | t ≠ 0}`, so their derivs are equal.
  have hderiv_recurrence : deriv Complex.Gamma (s + 1) =
      Complex.Gamma s + s * deriv Complex.Gamma s := by
    have hLHS_hd : HasDerivAt (fun t : ℂ => Complex.Gamma (t + 1))
        (deriv Complex.Gamma (s + 1)) s := by
      have h_add : HasDerivAt (fun t : ℂ => t + 1) 1 s := (hasDerivAt_id s).add_const 1
      have := hΓ_diff_s1.hasDerivAt.comp s h_add
      simpa using this
    have hRHS_hd : HasDerivAt (fun t : ℂ => t * Complex.Gamma t)
        (1 * Complex.Gamma s + s * deriv Complex.Gamma s) s := by
      have h_id : HasDerivAt (fun t : ℂ => t) 1 s := hasDerivAt_id s
      have h_Γ : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s := hΓ_diff.hasDerivAt
      exact h_id.mul h_Γ
    have hfg : (fun t => Complex.Gamma (t + 1)) =ᶠ[nhds s] (fun t => t * Complex.Gamma t) := by
      have hs_nhds : {t : ℂ | t ≠ 0} ∈ nhds s := isOpen_ne.mem_nhds hs_ne
      filter_upwards [hs_nhds] with t ht
      exact Complex.Gamma_add_one t ht
    have hderiv_eq : deriv (fun t : ℂ => Complex.Gamma (t + 1)) s =
        deriv (fun t => t * Complex.Gamma t) s :=
      Filter.EventuallyEq.deriv_eq hfg
    rw [hLHS_hd.deriv] at hderiv_eq
    rw [hRHS_hd.deriv] at hderiv_eq
    linear_combination hderiv_eq
  have hΓ_recurrence : Complex.Gamma (s + 1) = s * Complex.Gamma s :=
    Complex.Gamma_add_one s hs_ne
  unfold digamma
  rw [hderiv_recurrence, hΓ_recurrence]
  field_simp
  ring

/-- **Task 48-A4 — proved.** Digamma reflection formula:
```
ψ(1 − s) − ψ(s) = π · cos(π s) / sin(π s).
```

Proof: starting from Euler's reflection formula `Γ(s) · Γ(1 − s) = π / sin(π s)`
(`Complex.Gamma_mul_Gamma_one_sub`), differentiate both sides at `s`. The LHS derivative
is `Γ'(s)·Γ(1−s) − Γ(s)·Γ'(1−s)` (minus sign from the `1 − z` chain rule). The RHS is
`π · (sin(π z))⁻¹`, whose derivative is `-π² cos(π s) / sin²(π s)`. Equating the two and
dividing by `Γ(s)·Γ(1−s) · sin(π s) = π` yields the claim; carried out via
`linear_combination` after clearing denominators. -/
theorem digamma_reflection {s : ℂ} (h : ∀ m : ℕ, s ≠ -(m : ℂ))
    (h1 : ∀ m : ℕ, (1 - s) ≠ -(m : ℂ)) (hs_sin : Complex.sin (Real.pi * s) ≠ 0) :
    digamma (1 - s) - digamma s =
      Real.pi * Complex.cos (Real.pi * s) / Complex.sin (Real.pi * s) := by
  have hΓs_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma _ h
  have hΓ1s_diff : DifferentiableAt ℂ Complex.Gamma (1 - s) :=
    Complex.differentiableAt_Gamma _ h1
  have hΓs_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero h
  have hΓ1s_ne : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero h1
  have hs_sin' : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := hs_sin
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  -- Chain rule: d/dz Γ(1 − z) at z = s equals -Γ'(1 − s).
  have hΓ1s_hd : HasDerivAt (fun z => Complex.Gamma (1 - z))
      (-(deriv Complex.Gamma (1 - s))) s := by
    have h_sub : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
      have := (hasDerivAt_id s).const_sub 1; convert this using 1
    have := hΓ1s_diff.hasDerivAt.comp s h_sub
    convert this using 1; ring
  -- Product rule: d/dz [Γ(z)·Γ(1 − z)] at z = s.
  have hF_hd : HasDerivAt (fun z => Complex.Gamma z * Complex.Gamma (1 - z))
      (deriv Complex.Gamma s * Complex.Gamma (1 - s) -
       Complex.Gamma s * deriv Complex.Gamma (1 - s)) s := by
    have := hΓs_diff.hasDerivAt.mul hΓ1s_hd
    convert this using 1; ring
  -- Chain rule: d/dz sin(π z) at z = s equals π cos(π s).
  have hsin_hd : HasDerivAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
      ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * s)) s := by
    have h_mul : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) (Real.pi : ℂ) s := by
      have := (hasDerivAt_id s).const_mul (Real.pi : ℂ); simpa using this
    have := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * s)).comp s h_mul
    convert this using 1; ring
  -- Reciprocal rule: d/dz (sin(π z))⁻¹ at z = s.
  have hsin_inv_hd : HasDerivAt (fun z : ℂ => (Complex.sin ((Real.pi : ℂ) * z))⁻¹)
      (-((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * s)) /
        Complex.sin ((Real.pi : ℂ) * s) ^ 2) s := hsin_hd.inv hs_sin'
  -- G(z) = π · (sin(π z))⁻¹.
  have hG_hd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * z))⁻¹)
      ((Real.pi : ℂ) * (-((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * s)) /
        Complex.sin ((Real.pi : ℂ) * s) ^ 2)) s :=
    hsin_inv_hd.const_mul (Real.pi : ℂ)
  -- Euler's reflection formula: F(z) = G(z) pointwise.
  have hFG_eq : (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) =
                (fun z : ℂ => (Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * z))⁻¹) := by
    funext z
    rw [Complex.Gamma_mul_Gamma_one_sub z, div_eq_mul_inv]
  -- Transfer HasDerivAt of F to the G-shape.
  have hG_via_F : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * z))⁻¹)
      (deriv Complex.Gamma s * Complex.Gamma (1 - s) -
       Complex.Gamma s * deriv Complex.Gamma (1 - s)) s := by
    rw [← hFG_eq]; exact hF_hd
  -- Equate the two derivatives.
  have hderiv_eq : deriv Complex.Gamma s * Complex.Gamma (1 - s) -
                   Complex.Gamma s * deriv Complex.Gamma (1 - s) =
      (Real.pi : ℂ) * (-((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * s)) /
        Complex.sin ((Real.pi : ℂ) * s) ^ 2) :=
    hG_via_F.unique hG_hd
  have hprod_val : Complex.Gamma s * Complex.Gamma (1 - s) =
                   (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s) :=
    Complex.Gamma_mul_Gamma_one_sub s
  -- Clear denominators: [Γ'(s)Γ(1−s) − Γ(s)Γ'(1−s)] · sin² = -π² cos.
  have hderiv_clean : (deriv Complex.Gamma s * Complex.Gamma (1 - s) -
                      Complex.Gamma s * deriv Complex.Gamma (1 - s)) *
                      Complex.sin ((Real.pi : ℂ) * s) ^ 2 =
                      -(Real.pi : ℂ) ^ 2 * Complex.cos ((Real.pi : ℂ) * s) := by
    rw [hderiv_eq]; field_simp
  -- Clear denominators: Γ(s)Γ(1−s) · sin = π.
  have hprod_clean : Complex.Gamma s * Complex.Gamma (1 - s) *
                     Complex.sin ((Real.pi : ℂ) * s) = (Real.pi : ℂ) := by
    rw [hprod_val]; field_simp
  unfold digamma
  rw [div_sub_div _ _ hΓ1s_ne hΓs_ne]
  rw [div_eq_div_iff (mul_ne_zero hΓ1s_ne hΓs_ne) hs_sin']
  -- Multiply both sides of the polynomial goal by `sin` to reach `hderiv_clean` shape.
  have goal_x_sin : (deriv Complex.Gamma (1 - s) * Complex.Gamma s -
                     Complex.Gamma (1 - s) * deriv Complex.Gamma s) *
                     Complex.sin ((Real.pi : ℂ) * s) * Complex.sin ((Real.pi : ℂ) * s) =
                    (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * s) *
                    (Complex.Gamma (1 - s) * Complex.Gamma s) *
                    Complex.sin ((Real.pi : ℂ) * s) := by
    linear_combination -hderiv_clean -
      (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * s) * hprod_clean
  exact mul_right_cancel₀ hs_sin' goal_x_sin

#print axioms digamma
#print axioms digamma_eq_logDeriv
#print axioms digamma_differentiableAt
#print axioms digamma_recurrence
#print axioms digamma_reflection

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 48 — Arch / Prime integrands (tasks 48-C1, 48-C2, 48-C3, 48-D1)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Task 48-C1.** The arch integrand on the vertical contour `Re s = σ₀`. This is
`arch(s) · pairTestMellin β s` written directly in digamma form: the expression
`Gammaℝ'(s)/Gammaℝ(s) + Gammaℝ'(1−s)/Gammaℝ(1−s)` times `pairTestMellin β s`. -/
noncomputable def archIntegrand (β : ℝ) (σ₀ : ℝ) (t : ℝ) : ℂ :=
  (deriv Complex.Gammaℝ ((σ₀ : ℂ) + (t : ℂ) * I) /
      ((σ₀ : ℂ) + (t : ℂ) * I).Gammaℝ +
    deriv Complex.Gammaℝ (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) /
      (1 - ((σ₀ : ℂ) + (t : ℂ) * I)).Gammaℝ) *
  pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)

/-- **Task 48-C2.** The prime integrand on the vertical contour `Re s = σ₀ > 1`: the
von Mangoldt L-series paired against `pairTestMellin β s`. -/
noncomputable def primeIntegrand (β : ℝ) (σ₀ : ℝ) (t : ℝ) : ℂ :=
  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((σ₀ : ℂ) + (t : ℂ) * I) *
  pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I)

/-- **Task 48-C3 — proved.** On the right edge `Re s = σ₀ > 1`, the Weil integrand
for the test function `pairTestMellin β` equals the prime integrand pointwise. -/
theorem weilIntegrand_eq_primeIntegrand_on_right_edge
    (β : ℝ) {σ₀ : ℝ} (hσ : 1 < σ₀) (t : ℝ) :
    weilIntegrand (pairTestMellin β) ((σ₀ : ℂ) + (t : ℂ) * I) = primeIntegrand β σ₀ t := by
  have hre : (1 : ℝ) < ((σ₀ : ℂ) + (t : ℂ) * I).re := by
    show (1 : ℝ) < ((σ₀ : ℂ) + (t : ℂ) * I).re
    simp
    exact hσ
  unfold primeIntegrand
  exact weilIntegrand_right_edge_eq_LSeries_pairing hre

#print axioms weilIntegrand_eq_primeIntegrand_on_right_edge

/-- **Task 48-D1 — proved.** Away from the trivial poles, the Weil integrand splits
as the arch contribution (digamma-style) plus the prime-at-reflected-argument
contribution `ζ'(1−s)/ζ(1−s)`, both multiplied by `pairTestMellin β s`. -/
theorem weilIntegrand_split_via_arch
    (β : ℝ) (s : ℂ)
    (hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1)
    (hζ_s_ne : riemannZeta s ≠ 0) (hζ_1s_ne : riemannZeta (1 - s) ≠ 0)
    (hGammaℝ_s : s.Gammaℝ ≠ 0) (hGammaℝ_1s : (1 - s).Gammaℝ ≠ 0) :
    weilIntegrand (pairTestMellin β) s =
      (deriv Complex.Gammaℝ s / s.Gammaℝ +
       deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ) * pairTestMellin β s +
      deriv riemannZeta (1 - s) / riemannZeta (1 - s) * pairTestMellin β s := by
  rw [weilIntegrand_arch_decomposition hs_ne_zero hs_ne_one hζ_s_ne hζ_1s_ne
    hGammaℝ_s hGammaℝ_1s]
  ring

#print axioms weilIntegrand_split_via_arch

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 48 — Target reformulation (tasks 48-E1, 48-E2)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Task 48-E1.** Reformulation of the arch=prime identity as the equality of two
line integrals on `Re s = σ₀`, written using the `archIntegrand` and `primeIntegrand`
aliases from 48-C1 and 48-C2. -/
def WeilArchPrimeIdentity_reform (β : ℝ) : Prop :=
  ∀ σ₀ : ℝ, σ₀ > 1 →
    (∫ t : ℝ, archIntegrand β σ₀ t) = (∫ t : ℝ, primeIntegrand β σ₀ t)

/-- **Task 48-E2 — proved.** `WeilArchPrimeIdentityTarget β ↔ WeilArchPrimeIdentity_reform β`.
These are definitionally the same Prop once `archIntegrand` and `primeIntegrand` are
unfolded. -/
theorem WeilArchPrimeIdentityTarget_iff_reform (β : ℝ) :
    WeilArchPrimeIdentityTarget β ↔ WeilArchPrimeIdentity_reform β := by
  unfold WeilArchPrimeIdentityTarget WeilArchPrimeIdentity_reform archIntegrand primeIntegrand
  rfl

#print axioms WeilArchPrimeIdentityTarget_iff_reform

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 48 — Correctly stated arch-operator identity on Re s > 1
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Correctly stated arch-operator identity on Re s > 1.** Pointwise, on the
right edge of the Weil contour, the archimedean operator satisfies

```
arch(s) := Gammaℝ'(s)/Gammaℝ(s) + Gammaℝ'(1−s)/Gammaℝ(1−s)
        = LSeries_Λ(s) − ζ'(1−s)/ζ(1−s).
```

Unconditionally provable from cycle 35 (`zeta_logDeriv_arch_form`) combined with
cycle 42 (`vonMangoldt_LSeries_eq_neg_logDeriv_zeta`). This is the pointwise
replacement for `WeilArchPrimeIdentityTarget`, which was mis-stated as an
equality of integrals on a single vertical line — the correct single-line form
carries the `ζ'(1−s)/ζ(1−s)` correction term. -/
theorem arch_eq_LSeries_minus_reflected_logDeriv
    {s : ℂ} (hs : 1 < s.re)
    (hs_ne_zero : s ≠ 0) (hs_ne_one : s ≠ 1)
    (hζ_s_ne : riemannZeta s ≠ 0) (hζ_1s_ne : riemannZeta (1 - s) ≠ 0)
    (hGammaℝ_s : s.Gammaℝ ≠ 0) (hGammaℝ_1s : (1 - s).Gammaℝ ≠ 0) :
    deriv Complex.Gammaℝ s / s.Gammaℝ +
    deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
      - deriv riemannZeta (1 - s) / riemannZeta (1 - s) := by
  -- Cycle 35: -(ζ'/ζ)(s) = arch(s) + (ζ'/ζ)(1-s).
  have harch := zeta_logDeriv_arch_form hs_ne_zero hs_ne_one hζ_s_ne hζ_1s_ne
    hGammaℝ_s hGammaℝ_1s
  -- Cycle 42: LSeries_Λ(s) = -(ζ'/ζ)(s) on Re s > 1.
  have hL := vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs
  -- LSeries_Λ(s) is written in mathlib as `-deriv ζ s / ζ s`, which is the
  -- same complex number as `-(deriv ζ s / ζ s)`. Align via ring manipulation.
  have hL' :
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
        -(deriv riemannZeta s / riemannZeta s) := by
    rw [hL]; ring
  -- Combine: arch(s) = -(ζ'/ζ)(s) - (ζ'/ζ)(1-s) = LSeries_Λ(s) - (ζ'/ζ)(1-s).
  linear_combination -harch - hL'

#print axioms arch_eq_LSeries_minus_reflected_logDeriv

/-- **Corrected integrand identity.** Multiplying
`arch_eq_LSeries_minus_reflected_logDeriv` by `pairTestMellin β s` gives the
pointwise relation between the arch integrand and the prime integrand on the
right edge:

```
archIntegrand β σ₀ t
  = primeIntegrand β σ₀ t
  − (ζ'(1−s) / ζ(1−s)) · pairTestMellin β s        at s = σ₀ + it.
```

This is the load-bearing pointwise identity; the global integral identity
(`WeilArchPrimeIdentityTarget_corrected`) follows by integrating both sides. -/
theorem archIntegrand_eq_primeIntegrand_minus_reflected
    (β : ℝ) {σ₀ : ℝ} (hσ : 1 < σ₀) (t : ℝ)
    (hs_ne_zero : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0)
    (hs_ne_one : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1)
    (hζ_s_ne : riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0)
    (hζ_1s_ne : riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) ≠ 0)
    (hGammaℝ_s : ((σ₀ : ℂ) + (t : ℂ) * I).Gammaℝ ≠ 0)
    (hGammaℝ_1s : (1 - ((σ₀ : ℂ) + (t : ℂ) * I)).Gammaℝ ≠ 0) :
    archIntegrand β σ₀ t = primeIntegrand β σ₀ t -
      (deriv riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) /
       riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I))) *
      pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I) := by
  have hre : (1 : ℝ) < ((σ₀ : ℂ) + (t : ℂ) * I).re := by
    show (1 : ℝ) < ((σ₀ : ℂ) + (t : ℂ) * I).re
    simp
    exact hσ
  have harch := arch_eq_LSeries_minus_reflected_logDeriv hre hs_ne_zero hs_ne_one
    hζ_s_ne hζ_1s_ne hGammaℝ_s hGammaℝ_1s
  unfold archIntegrand primeIntegrand
  rw [harch]
  ring

#print axioms archIntegrand_eq_primeIntegrand_minus_reflected

/-- **Reformulated (corrected) integral identity.** The correct global form of
the arch–prime identity on a single vertical line `Re s = σ₀ > 1` carries a
correction term from the reflected log-derivative `ζ'(1−s)/ζ(1−s)`. This is the
replacement for the mis-stated `WeilArchPrimeIdentityTarget`.

Stated as `Prop`; the pointwise identity
`archIntegrand_eq_primeIntegrand_minus_reflected` is unconditional, but lifting
to an equality of integrals requires integrability hypotheses (absent here).
Cycle 48 will discharge the remaining integrability content separately. -/
def WeilArchPrimeIdentityTarget_corrected (β : ℝ) : Prop :=
  ∀ σ₀ : ℝ, σ₀ > 1 →
    (∫ t : ℝ, archIntegrand β σ₀ t) =
      (∫ t : ℝ, primeIntegrand β σ₀ t) -
      (∫ t : ℝ,
        deriv riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) /
         riemannZeta (1 - ((σ₀ : ℂ) + (t : ℂ) * I)) *
        pairTestMellin β ((σ₀ : ℂ) + (t : ℂ) * I))

#print axioms WeilArchPrimeIdentityTarget_corrected

end Contour
end WeilPositivity
end ZD

end
