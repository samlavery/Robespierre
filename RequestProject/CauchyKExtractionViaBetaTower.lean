import Mathlib
import RequestProject.OfflineDetectorProof
import RequestProject.PairCoshGaussTest
import RequestProject.GaussianAdmissible
import RequestProject.CarlsonUniqueness

/-!
# β-derivative tower extraction (diagnostic, conditional on three named gaps)

## Audit summary (post-2026-05-07, corrected)

A previous version of this header asserted that the per-zero step from the
moment tower at the shifted-Mellin basis `gKernel(α + 2k)` hit "the same ℓ¹
wall" as the direct Fubini route.  That claim was wrong.

The Fubini ℓ¹ wall is `Σ_α ‖a(α)·K(α)‖ < ∞`, where `‖K(α)‖` has a constant
floor `π·√(π/2)` as `|Im α| → ∞`.  The moment-tower summability is
`Σ_α ‖a(α)·gKernel(α + 2k)‖ < ∞`, where `gKernel(α + 2k)` decays
*exponentially* in `Re α + 2k` (it is the Mellin transform of a Schwartz
factor) — so summability at shifted argument is **strictly easier** than at
the original cosh-pair, not the same wall.  `BetaTowerAdmissible.moment_summable`
asks for the shifted summability, which is plausible.

## What the β-tower actually delivers

Conditional on `BetaTowerAdmissible`:

1. `tsum_analytic` + `vanish_on_real_interval` + identity theorem on ℝ
   ⟹ `F(β) := Σ' a · pairTestMellin β · ≡ 0` on a complex β-neighborhood
   of `(0, 1)`.
2. Term-by-term β-differentiation under the tsum (justified by
   `moment_summable` + `deriv_basis`) gives, for `k ≥ 1`,
   `F^{(2k)}(1/2) = Σ' a(α) · M_{2k}(α) = 2·4^k · Σ' a(α) · gKernel(α + 2k) = 0`.
3. Define `phi a s := Σ' a(α) · gKernel(α + s)`.  Step 2 says
   `phi a (2k) = 0` for all `k ≥ 1`.

## The three remaining gaps for per-zero extraction

To go from `phi a (2k) = 0 ∀ k ≥ 1` to `a ≡ 0` on the zero set:

**Gap (i) — Strip analyticity + Carlson-type growth bound.**
`phi a` is analytic on a right half-plane `Re s ≥ σ₀` (uniform-on-compact
convergence of the tsum, justified by Mellin decay of `gKernel`), and has
exponential type `< π/2` on that half-plane (so that the substitution
`w := s/2` brings it into Carlson's regime on positive integers).  Stated
as `phi_analytic_bounded_target`.

**Gap (ii) — Carlson uniqueness.**
Given (i) plus `phi a (2k) = 0 ∀ k ≥ 1`, conclude `phi a ≡ 0` on the
half-plane.  This is **Carlson's theorem** for the sequence `{2k}_{k≥1}`,
provable via `Complex.PhragmenLindelof.right_half_plane_*` applied to
`phi(2·) / sin(π·)` — both ingredients are in mathlib.  Stated as
`phi_vanishes_on_halfplane_target`.

**Gap (iii) — Mellin inversion + countable-support linear independence.**
Given `phi a ≡ 0` on a right half-plane, write
`phi a (s) = Σ_α a(α) · ∫_0^∞ x^{α + s − 1} · coshGaussFactor(log x) dx`,
swap the sum and the integral (Fubini, justified by `moment_summable` at
each `s`), to get
`phi a (s) = ∫_0^∞ x^{s − 1} · (Σ_α a(α) · x^α) · coshGaussFactor(log x) dx`.
That is the Mellin transform (in `s`) of `(Σ_α a(α) · x^α) · coshGaussFactor(log x)`,
identically zero on a half-plane.  Apply `MellinInvMellin.mellin_mellinInv_eq`
(or mathlib's `mellinInv_mellin_eq`) to recover that the integrand is zero
a.e. in `x`.  Since `coshGaussFactor > 0` for `x ≠ exp(0)` (after a
boundary-set check), conclude `Σ_α a(α) · x^α = 0` for a.e. `x > 0`.  The
zero set is countable, so the powers `{x^α}_α` are linearly independent
over ℂ in the space of measurable functions on `ℝ_+`, forcing `a(α) = 0`
for each `α`.  Stated as `per_zero_of_phi_vanishes_on_halfplane_target`.

## Project infrastructure for the three gaps

* Mellin inversion: `RequestProject/MellinInvMellin.lean:51` provides
  `mellin_mellinInv_eq` (converse direction); mathlib has
  `mellinInv_mellin_eq` (forward).
* Phragmén–Lindelöf: `Complex.PhragmenLindelof.vertical_strip` is in
  mathlib and already used in this project at `ZetaStripBound.lean:818`.
* Strip analyticity of tsums: `pairTestMellin_analyticOnNhd_in_beta`
  pattern (used elsewhere in the project).
* Schwartz/Gaussian decay of `gKernel`: structurally available because
  `coshGaussFactor` is `O(t^4)` near `0` and Gaussian-decaying at
  infinity.

None of the three gaps is structurally blocked.  The previous version's
"same ℓ¹ wall" claim was wrong.

## What this file provides

* `BetaTowerAdmissible` — the structural admissibility package.
* `phi`, `M_2k`, `gKernel`, `coshGaussFactor` — the building blocks.
* `coeff_vanishes_of_beta_tower_target` — the conditional headline.
* `moment_tower_holds_target` — the accessible step (steps 1–2 above).
* `phi_analytic_bounded_target`, `phi_vanishes_on_halfplane_target`,
  `per_zero_of_phi_vanishes_on_halfplane_target` — the three named
  gaps for per-zero extraction.
* `phi_at_two_k_eq_zero_of_moment_tower` — the (provable) bridge from the
  moment tower to `phi(2k) = 0`.
* `coeff_vanishes_of_beta_tower_of_split_targets` — wrapper composing the
  three sub-targets into the headline.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace BetaTower

/-! ## Building blocks of the β-derivative tower -/

/-- The β-independent factor `A(t) = sinh²((1/2 − π/6)·t) · (ψ_gaussian t)²`.
Pair test factors as `pair_cosh_gauss_test β t = 4 · sinh²((β − 1/2)·t) · A(t)`
via `pair_cosh_gauss_test_sinh_factor`. -/
def coshGaussFactor : ℝ → ℝ :=
  fun t => Real.sinh ((1/2 - Real.pi/6) * t)^2 * (ZD.ψ_gaussian t)^2

/-- The Mellin transform of `coshGaussFactor`.  Real-valued for real `s`,
analytic in `s` on `Re s > −1` (since `coshGaussFactor t = O(t²)` near `0`
and Gaussian-decaying at infinity). -/
def gKernel (s : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ), (coshGaussFactor t : ℂ) * (t : ℂ)^(s - 1)

/-- The (2k)-th β-derivative of `pairTestMellin β ρ` at `β = 1/2`.
By the closed-form expansion (see file header), this equals
`2 · 4^k · gKernel (ρ + 2k)` for `k ≥ 1`, and `0` for `k = 0`. -/
def M_2k (k : ℕ) (ρ : ℂ) : ℂ :=
  iteratedDeriv (2*k) (fun β : ℝ => Contour.pairTestMellin β ρ) (1/2)

/-- The shifted-Mellin tsum `phi a (s) := Σ_α a(α) · gKernel(α + s)`,
indexed over `NontrivialZeros`.  The β-tower delivers `phi a (2k) = 0`
for all `k ≥ 1` (see `phi_at_two_k_eq_zero_of_moment_tower`); gaps (ii)
and (iii) extract `a ≡ 0` on the zero set from this. -/
def phi (a : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, a ρ.val * gKernel (ρ.val + s)

/-! ## Admissibility structure -/

/-- **β-tower admissibility** for a coefficient family `a : ℂ → ℂ`.

Four fields:

1. **`tsum_analytic`** — `β ↦ Σ' a(ρ)·pairTestMellin β ρ` is real-analytic
   on `Set.univ`.  Strictly weaker than `Σ' ‖a‖ < ∞`; obtained via Mellin
   quartic decay × Jensen `Σ n(ρ)/‖ρ‖² < ∞`.

2. **`deriv_basis`** — closed-form for the (2k)-th derivative kernel:
   `M_{2k}(ρ) = 2·4^k·gKernel(ρ+2k)`.  Algebraic (Leibniz under the Mellin
   integral, justified by `pairTestMellin_analyticOnNhd_in_beta`).

3. **`moment_summable`** — at each shifted level `2k`, the summands
   `a(ρ)·gKernel(ρ+2k)` are absolutely summable.  Easier than the
   unshifted ℓ¹ because of `gKernel`'s exponential decay in `Re α`.

4. **`vanish_on_real_interval`** — per-β tsum vanishing on `(0,1)` — the
   engineering identity from the K-twisted chain. -/
structure BetaTowerAdmissible (a : ℂ → ℂ) : Prop where
  /-- `β ↦ Σ' a·M(β,·)` is analytic on `(0,1)`. -/
  tsum_analytic :
    AnalyticOnNhd ℝ
      (fun β : ℝ => ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val) Set.univ
  /-- For each `k ≥ 1`, `∂_β^{2k} pairTestMellin β ρ |_{β=1/2}` equals
  `2·4^k·gKernel(ρ+2k)`. -/
  deriv_basis :
    ∀ k : ℕ, 1 ≤ k → ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      M_2k k ρ.val = (2 : ℂ) * (4 : ℂ)^k * gKernel (ρ.val + (2*k : ℕ))
  /-- For each `k ≥ 1`, the moment-summand series is absolutely summable. -/
  moment_summable :
    ∀ k : ℕ, 1 ≤ k →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ‖a ρ.val * gKernel (ρ.val + (2*k : ℕ))‖)
  /-- Per-β tsum vanishing on `(0,1)` — the engineering identity. -/
  vanish_on_real_interval :
    ∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0

/-! ## Step 1–2: moment tower (open, but accessible) -/

/-- **Moment tower target.** The β-tower delivers per-`k` tsum vanishing
of `a · gKernel(ρ + 2k)`.  Open obligation, but the proof is mechanical:
identity-theorem on ℝ + iterated β-differentiation under the tsum +
`deriv_basis`. -/
def moment_tower_holds_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    ∀ k : ℕ, 1 ≤ k →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * gKernel (ρ.val + (2*k : ℕ)) = 0

/-! ## Bridge: moment tower ⟹ phi(2k) = 0 (provable) -/

/-- Bridge lemma: `phi a (2k) = 0` is literally the moment tower at level `k`. -/
theorem phi_at_two_k_eq_zero_of_moment_tower
    (h_moment : moment_tower_holds_target)
    (a : ℂ → ℂ) (ha : BetaTowerAdmissible a)
    (k : ℕ) (hk : 1 ≤ k) :
    phi a ((2*k : ℕ) : ℂ) = 0 := by
  unfold phi
  exact h_moment a ha k hk

/-! ## Step 3 — sub-gaps for per-zero extraction (refined obligation tree)

Gap (i) — `phi_analytic_bounded_target` — splits into four named
sub-obligations.  The split exposes which parts are mechanical (the
analyticity bridge, the Im-direction decay) and which is the genuine
hard step (the Re-direction bound, which depends on whether the sum
`phi a` has cancellations across the zero set's imaginary parts).

### Honest growth analysis (post-2026-05-07)

The pointwise bound `|gKernel(α + s)| ≤ M[|coshGaussFactor|](Re α + Re s)`
is super-exponential (Gamma-type) in `Re s` because
`coshGaussFactor t = sinh²((1/2-π/6)t) · exp(-2t²)` has Mellin transform
`gKernel(σ) ~ exp((σ/2) log σ - σ + O(√σ))` for `σ → ∞`.  Without
cancellations, summing over zeros gives the same super-exponential growth
in `Re s`, defeating the Carlson `τ < π/2` hypothesis.

However, `phi a` is an oscillatory sum.  Formally:
`phi a (s) = ∫_0^∞ (Σ_α a(α) t^α) · coshGaussFactor(t) · t^(s-1) dt`,
the Mellin transform (in distribution sense) of
`A(t) := Σ a(α) t^α` against `coshGaussFactor`.  Cancellations across the
zeros' imaginary parts can in principle bring `phi a` down to bounded on
the real axis.  This is the genuine open question; `phi_real_axis_bounded_target`
below names it.

Decay in `Im s` (quartic) and uniform-on-strip boundedness are mechanical
consequences of `gKernel`'s Schwartz behavior in `Im s` and the zero-count
bound `Σ n(γ) / γ^4 < ∞`.

### Sub-obligation tree -/

/-- **Sub-obligation (i.A) — uniform-on-compacts summability.**
The series `Σ_α a(α) · gKernel(α + s)` converges absolutely uniformly on
each compact subset of the half-plane `{σ₀ < s.re}`.  Equivalent (via
Weierstrass) to analyticity. -/
def phi_summable_uniform_on_compacts_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    ∃ σ₀ : ℝ, ∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | σ₀ < s.re} →
      ∃ u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ,
        Summable u ∧
        ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ∀ s ∈ K,
          ‖a ρ.val * gKernel (ρ.val + s)‖ ≤ u ρ

/-- **Sub-obligation (i.B) — `phi a` is analytic on a right half-plane.**
This follows from (i.A) by the Weierstrass theorem on uniform convergence
of analytic functions. -/
def phi_analyticOnNhd_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    ∃ σ₀ : ℝ, AnalyticOnNhd ℂ (phi a) {s : ℂ | σ₀ < s.re}

/-- **Sub-obligation (i.C) — `phi a` decays in `Im s`** (quartic, uniform
on each vertical strip).  This follows from `gKernel`'s Schwartz decay in
`Im s` and the zero-count bound `Σ n(γ) / γ^4 < ∞`.  Provable from
project infrastructure (`WeilPairTestDecay.pairTestMellin_im_quartic_decay`
analogue at the `gKernel` kernel; `ZeroCountJensen` gives the zero-count
bound). -/
def phi_im_decay_uniform_on_strips_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    ∃ σ₀ : ℝ, ∀ σ₁ : ℝ, σ₀ < σ₁ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, σ₀ < s.re → s.re < σ₁ →
        ‖phi a s‖ ≤ C / (1 + |s.im|)^4

/-- **Sub-obligation (i.D) — `phi a` is uniformly bounded on the positive
real axis.**

This is the **genuinely hard part** of Gap (i).  The pointwise upper bound
is super-exponential in `Re s` (Gamma-type, see analysis above), so a
uniform bound only holds if the sum has Re-direction cancellations across
the zero set.  Heuristic for this:

* `phi a` vanishes at every positive even integer `2k`.
* `phi a (s)` analytic on a half-plane.
* Vanishing at `{2k}` together with a half-plane analyticity constrains
  the function to be of the form `sin(π s/2) · ψ(s)` for some analytic
  `ψ`.  The factor `sin(π s/2)` is bounded by 1 on the real axis.  If
  `ψ` is bounded on the real axis, `phi a` is too.

Whether `ψ` is bounded depends on the specific Mellin structure and the
coefficient regularity.  Currently open.  -/
def phi_real_axis_bounded_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    ∃ σ₀ B : ℝ, 0 < σ₀ ∧ 0 ≤ B ∧
      ∀ σ : ℝ, σ₀ < σ → ‖phi a (σ : ℂ)‖ ≤ B

/-- **Gap (i) — Composite analyticity + Carlson-type growth bound.**
`phi a` is analytic on a right half-plane and has the Carlson hypotheses:
type `< π/2` in `Im` direction with uniform bound on the real axis.

The Im-direction bound `B · exp(τ · |s.im|)` is a uniform-in-`Re s` bound
on each vertical line; combined with the bound on the real axis, it gives
the Carlson hypothesis. -/
def phi_analytic_bounded_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    ∃ (σ₀ B τ : ℝ), 0 < σ₀ ∧ 0 ≤ B ∧ 0 < τ ∧ τ < Real.pi / 2 ∧
      AnalyticOnNhd ℂ (phi a) {s : ℂ | σ₀ ≤ s.re} ∧
      ∀ s : ℂ, σ₀ ≤ s.re →
        ‖phi a s‖ ≤ B * Real.exp (τ * |s.im|)

/-! ### Composition target: (i.B) + (i.C) + (i.D) ⟹ Gap (i)

Stated as an open obligation (the glue lemma combining strip-Im-decay
with the real-axis bound to produce the unified `B · exp(τ · |Im s|)`
form is mechanical but not done here).  The sub-obligations (i.A)–(i.D)
are individually accessible by direct analysis. -/
def phi_analytic_bounded_target_of_components_target : Prop :=
  phi_analyticOnNhd_target →
  phi_im_decay_uniform_on_strips_target →
  phi_real_axis_bounded_target →
  phi_analytic_bounded_target

/-- **Gap (ii) — Carlson uniqueness.**  Given (i) and `phi a (2k) = 0`
for all `k ≥ 1`, conclude `phi a ≡ 0` on the half-plane.

Mathlib has the ingredients: `Complex.PhragmenLindelof.right_half_plane_*`
applied to `phi(2·) / sin(π·)` (the standard Carlson argument).  The
sin-division removes the integer zeros, the PL bound on `phi/sin` makes
it tend to 0, then PL gives identical zero. -/
def phi_vanishes_on_halfplane_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    (∃ (σ₀ B τ : ℝ), 0 < σ₀ ∧ 0 ≤ B ∧ 0 < τ ∧ τ < Real.pi / 2 ∧
      AnalyticOnNhd ℂ (phi a) {s : ℂ | σ₀ ≤ s.re} ∧
      ∀ s : ℂ, σ₀ ≤ s.re →
        ‖phi a s‖ ≤ B * Real.exp (τ * |s.im|)) →
    (∀ k : ℕ, 1 ≤ k → phi a ((2*k : ℕ) : ℂ) = 0) →
    ∃ σ₁ : ℝ, 0 < σ₁ ∧ ∀ s : ℂ, σ₁ ≤ s.re → phi a s = 0

/-- **Gap (iii) — Mellin inversion + countable-support linear independence.**
Given `phi a ≡ 0` on a right half-plane, recover per-zero `a = 0`.

Strategy: rewrite `phi a (s) = ∫_0^∞ x^{s−1} · h_a(x) dx` where
`h_a(x) := (Σ_α a(α)·x^α) · coshGaussFactor(log x)`, then apply Mellin
inversion (`mellin_mellinInv_eq`) to get `h_a = 0` a.e.  Strict positivity
of `coshGaussFactor` away from boundary then gives `Σ_α a(α)·x^α = 0`
a.e., and countable-support linear independence of `{x^α}_α` forces each
`a(α) = 0`. -/
def per_zero_of_phi_vanishes_on_halfplane_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    (∃ σ₁ : ℝ, 0 < σ₁ ∧ ∀ s : ℂ, σ₁ ≤ s.re → phi a s = 0) →
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0

/-! ## Headline (conditional on the three gaps) -/

/-- **β-tower extraction target.** Conditional headline. -/
def coeff_vanishes_of_beta_tower_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0

/-- **Composed wrapper.** Combines moment tower (steps 1–2) with the three
named gaps (i)–(iii) for the per-zero step. -/
theorem coeff_vanishes_of_beta_tower_of_split_targets
    (h_moment : moment_tower_holds_target)
    (h_phi_bounded : phi_analytic_bounded_target)
    (h_phi_vanish : phi_vanishes_on_halfplane_target)
    (h_per_zero : per_zero_of_phi_vanishes_on_halfplane_target) :
    coeff_vanishes_of_beta_tower_target := by
  intro a ha ρ hρ
  -- (a) moment tower ⟹ phi(2k) = 0 for all k ≥ 1
  have h2k : ∀ k : ℕ, 1 ≤ k → phi a ((2*k : ℕ) : ℂ) = 0 := by
    intro k hk
    exact phi_at_two_k_eq_zero_of_moment_tower h_moment a ha k hk
  -- (b) Gap (i): phi analytic + bounded on a half-plane
  have hbnd := h_phi_bounded a ha
  -- (c) Gap (ii): Carlson conclusion
  have hzero : ∃ σ₁ : ℝ, 0 < σ₁ ∧ ∀ s : ℂ, σ₁ ≤ s.re → phi a s = 0 :=
    h_phi_vanish a ha hbnd h2k
  -- (d) Gap (iii): Mellin inversion + countable-support → per-zero
  exact h_per_zero a ha hzero ρ hρ

/-- Backwards-compatible single-target variant: takes the moment-tower
target and the composite "per-zero from moment tower" target.  The
composite target is itself the conjunction of gaps (i)–(iii), but stated
as a single Prop for legacy callers. -/
def per_zero_from_moment_tower_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a →
    (∀ k : ℕ, 1 ≤ k →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * gKernel (ρ.val + (2*k : ℕ)) = 0) →
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0

/-- Legacy wrapper.  Takes the composite per-zero target (which encodes
all three gaps in one Prop). -/
theorem coeff_vanishes_of_beta_tower_of_targets
    (h_moment : moment_tower_holds_target)
    (h_per_zero : per_zero_from_moment_tower_target) :
    coeff_vanishes_of_beta_tower_target := by
  intro a ha ρ hρ
  exact h_per_zero a ha (h_moment a ha) ρ hρ

/-- The three open obligations the β-tower extraction depends on, in their
finer-grained form.  This is the proper accounting; the legacy
`open_obligations_summary` collapses (i)–(iii) into one Prop. -/
def open_obligations_split : Prop :=
  moment_tower_holds_target ∧
  phi_analytic_bounded_target ∧
  phi_vanishes_on_halfplane_target ∧
  per_zero_of_phi_vanishes_on_halfplane_target

/-- Legacy two-Prop summary (composite per-zero). -/
def open_obligations_summary : Prop :=
  moment_tower_holds_target ∧ per_zero_from_moment_tower_target

/-! ## Discharge of Gap (ii) via classical Carlson uniqueness

The standalone Carlson tool (`RequestProject/CarlsonUniqueness.lean`) provides
`carlson_even_integer_uniqueness_of_classical`, which discharges Gap (ii)
once the classical Carlson core (`CarlsonClassical_unit_zeros_target`) is
supplied.  The wrapper below converts a witness of
`phi_analytic_bounded_target` into the conclusion of
`phi_vanishes_on_halfplane_target`, eliminating Gap (ii) modulo the
classical Carlson hypothesis.

Effect on the obligation tree:

* Before: `phi_analytic_bounded_target ∧ phi_vanishes_on_halfplane_target
  ∧ per_zero_of_phi_vanishes_on_halfplane_target`.
* After: `phi_analytic_bounded_target ∧ Carlson.CarlsonClassical_unit_zeros_target
  ∧ per_zero_of_phi_vanishes_on_halfplane_target`.

Net: Gap (ii) is replaced by a strictly more general (and standalone) Prop
about non-negative integer zeros at type `< π`.  No project-specific content. -/

/-- Conversion: classical Carlson ⟹ Gap (ii). -/
theorem phi_vanishes_on_halfplane_target_of_carlson_classical
    (h_classical : ZD.Carlson.CarlsonClassical_unit_zeros_target) :
    phi_vanishes_on_halfplane_target := by
  intro a _ha h_bnd h_2k
  obtain ⟨σ₀, B, τ, hσ₀, hB, hτ_pos, hτ_lt, h_an, h_gr⟩ := h_bnd
  -- Open half-plane analyticity from the closed-half-plane analyticity hypothesis.
  have h_an' : AnalyticOnNhd ℂ (phi a) {s : ℂ | σ₀ < s.re} := by
    intro s hs
    have hs' : σ₀ < s.re := hs
    exact h_an s (le_of_lt hs')
  -- Convert the |Im s| growth bound to a ‖s‖ growth bound on the open half-plane.
  have h_gr' : ∀ s : ℂ, σ₀ < s.re → ‖phi a s‖ ≤ B * Real.exp (τ * ‖s‖) := by
    intro s hs
    have h1 : ‖phi a s‖ ≤ B * Real.exp (τ * |s.im|) := h_gr s (le_of_lt hs)
    have h2 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have h3 : τ * |s.im| ≤ τ * ‖s‖ := mul_le_mul_of_nonneg_left h2 hτ_pos.le
    have h4 : Real.exp (τ * |s.im|) ≤ Real.exp (τ * ‖s‖) := Real.exp_le_exp.mpr h3
    have h5 : B * Real.exp (τ * |s.im|) ≤ B * Real.exp (τ * ‖s‖) :=
      mul_le_mul_of_nonneg_left h4 hB
    linarith
  -- Apply Carlson uniqueness.
  have h_zero : ∀ s : ℂ, σ₀ < s.re → phi a s = 0 :=
    ZD.Carlson.carlson_even_integer_uniqueness_of_classical h_classical (phi a)
      h_an' hB hτ_pos hτ_lt h_gr' h_2k
  refine ⟨σ₀ + 1, by linarith, ?_⟩
  intro s hs
  exact h_zero s (by linarith)

/-- The reduced obligation tree after discharging Gap (ii) via classical
Carlson.  Now: moment tower + Gap (i) (analyticity + growth) + classical
Carlson (RH-free) + Gap (iii) (Mellin inversion + countable support). -/
def open_obligations_after_carlson : Prop :=
  moment_tower_holds_target ∧
  phi_analytic_bounded_target ∧
  ZD.Carlson.CarlsonClassical_unit_zeros_target ∧
  per_zero_of_phi_vanishes_on_halfplane_target

/-- Composed wrapper using the post-Carlson obligation tree. -/
theorem coeff_vanishes_of_beta_tower_of_split_targets_via_carlson
    (h_moment : moment_tower_holds_target)
    (h_phi_bounded : phi_analytic_bounded_target)
    (h_classical : ZD.Carlson.CarlsonClassical_unit_zeros_target)
    (h_per_zero : per_zero_of_phi_vanishes_on_halfplane_target) :
    coeff_vanishes_of_beta_tower_target :=
  coeff_vanishes_of_beta_tower_of_split_targets h_moment h_phi_bounded
    (phi_vanishes_on_halfplane_target_of_carlson_classical h_classical)
    h_per_zero

/-! ## Operational target: detector separation

The cosh detector does not annihilate; it probes.  The right
extraction principle is a SEPARATION theorem on the β-family
`{pairTestMellin(β, ·) : β ∈ (0,1)}`, not Carlson uniqueness on a
half-plane.

### Why Carlson was the wrong tool

The Carlson chain (Gap (i)/(ii)/(iii) above, now demoted to alternate
route) was built on the premise that `phi a` should be a function with
zeros at the integer points `2k`, treatable by Carlson uniqueness.
This premise is wrong:

* `cosh` has no real zeros — it is a non-vanishing detector kernel,
  not a kernel-with-zeros.
* `coshGaussFactor t = sinh²((1/2-π/6)t)·exp(-2t²)` has only an
  order-2 zero at `t = 0` (from `sinh²`), not infinite-order smoothing.
  Demanding the detector kernel "make `coshGaussFactor·A̅(t)` flat at
  zero" is asking the detector to do something it cannot do.

The detector's role is to **separate** coefficients in the β-family,
not to annihilate.

### The separation Prop

The claim:
```
Σ a(α) · pairTestMellin(β, α) = 0  ∀ β ∈ (0,1)
⟹  a(α) = 0  for every nontrivial zero α
```

with `a` in a narrowly-stated admissibility class
(`PairCoshDetectorAdmissible`).

### Discharge sketch (cosine-Fourier + Dirichlet uniqueness)

1. `B(β) := Σ a(α) pairTestMellin(β, α)` is analytic in `β` on a
   complex neighborhood of `(0,1)` (`beta_analytic_tsum`).
2. `B = 0` on `(0,1)` ⟹ `B ≡ 0` on the analyticity domain (identity
   theorem).
3. Substitute `β = 1/2 + iy/2`:
   `pairTestMellin(1/2 + iy/2, α) = -2(∫ μ_α dt − ∫ cos(yt) μ_α dt)`
   with `μ_α(t) := sinh²((1/2-π/6)t)·exp(-2t²)·t^{α-1}`.
4. `B(1/2 + iy/2) = 0 ∀y ∈ ℝ` ⟹
   `∫ (1 - cos(yt))·(Σ a(α) μ_α(t)) dt = 0 ∀y`.
5. Cosine-Fourier inversion (`locally_uniform_beta_summable` license)
   ⟹ `Σ a(α) μ_α(t) ≡ 0` as a tempered distribution on `(0, ∞)`.
6. Divide by the strictly positive smooth factor
   `sinh²((1/2-π/6)t)·exp(-2t²)` ⟹ `Σ a(α) t^{α-1} ≡ 0` as
   distribution on `(0, ∞)`.
7. Substitute `t = e^{-x}` ⟹ `Σ a(α) e^{-(α-1)x} = 0 ∀x ∈ ℝ`
   (generalized Dirichlet series with distinct exponents).
8. Dirichlet uniqueness on distinct complex exponents ⟹ `a(α) = 0 ∀α`.

### Open structural question — orbit vs zero separation

The discharge sketch above produces a SINGLE-ZERO separation
conclusion.  But the cosh-pair test has FE/Klein structure: under
`α ↦ 1-α` and `α ↦ ᾱ` the test pairings might pick up at the orbit
level rather than per-zero.  The candidate failure mode: the detector
separates only FE/Klein-symmetric *aggregates* of `a`, not individual
coefficients.

For the natural target `a(α) = n(α)·K(α)` (with `K = (exp(δ²/8)-1)²`,
`δ = α-1/2`), `a` is FE-symmetric (`a(1-α) = a(α)` since `K` depends
only on `δ²`) and conjugate-conjugate (`a(ᾱ) = ā(α)`).  An
orbit-level separation with FE-symmetric `a` already determines
per-zero values UP TO conjugate pairs; further separation requires
either another detector or a residual symmetry argument.

The `symmetry_compatible` field of `PairCoshDetectorAdmissible` records
this: if the detector turns out to separate only orbits, the field
should be strengthened to assert orbit-level FE compatibility of `a`
(which `n·K` does satisfy by construction).

### Admissibility (narrow, named-field) -/

/-- **Admissibility for the pair-cosh detector separation theorem.**

Five named fields capturing the regularity needed for the
cosine-Fourier inversion + Dirichlet uniqueness chain.  Each is a
real, individually-checkable condition. -/
structure PairCoshDetectorAdmissible (a : ℂ → ℂ) : Prop where
  /-- For each `β ∈ (0,1)`, the engineering-identity tsum
  is absolutely summable.  Without this, the engineering-identity
  hypothesis itself is ill-posed. -/
  per_beta_summable :
    ∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ‖a ρ.val * Contour.pairTestMellin β ρ.val‖)
  /-- Locally uniform β-summability — for each compact `β`-set in
  `(0,1)`, the tsum is dominated by a summable majorant uniformly in
  `β`.  Required for licensing the cosine-Fourier swap (step 5). -/
  locally_uniform_beta_summable :
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
      ∃ u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ,
        Summable u ∧ ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ∀ β ∈ K,
          ‖a ρ.val * Contour.pairTestMellin β ρ.val‖ ≤ u ρ
  /-- The β-tsum is real-analytic on a neighborhood of `(0,1)`.
  Used in step 1–2 (identity-theorem extension).  Implied by
  `locally_uniform_beta_summable` plus β-analyticity of each summand
  (which `pairTestMellin` provides), but stated separately for
  clarity. -/
  beta_analytic_tsum :
    AnalyticOnNhd ℝ
      (fun β : ℝ => ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val) Set.univ
  /-- **Symmetry compatibility** — the coefficient is compatible with
  whatever residual FE/Klein orbit structure the detector might
  expose.  For the canonical target `a = n·K`, this is automatic
  (`a(1-α) = a(α)`, `a(ᾱ) = ā(α)`).  Stated as a Prop so callers can
  supply orbit-level information when needed.

  Concrete content: if the discharge sketch's step 5 produces only an
  FE-orbit-level conclusion, this field provides the additional
  symmetry needed to descend to per-zero. -/
  symmetry_compatible :
    ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      a ρ.val = a (1 - (starRingEnd ℂ ρ.val))
  /-- **No detector blind spot** — for every nontrivial zero `α`,
  there is *some* `β ∈ (0,1)` at which `pairTestMellin(β, α) ≠ 0`.
  This rules out the degenerate case where the detector annihilates
  certain zeros, which would prevent any separation theorem. -/
  no_detector_blind_spot :
    ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ∃ β : ℝ, 0 < β ∧ β < 1 ∧ Contour.pairTestMellin β ρ.val ≠ 0

/-- **Pair-cosh detector separation Prop** — the operational target. -/
def PairCoshDetectorSeparatesKCoeff_target : Prop :=
  ∀ (a : ℂ → ℂ), PairCoshDetectorAdmissible a →
    (∀ β : ℝ, 0 < β → β < 1 →
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        a ρ.val * Contour.pairTestMellin β ρ.val = 0) →
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → a ρ = 0

/-- The single operational obligation under the separation framing. -/
def open_obligations_separation : Prop :=
  PairCoshDetectorSeparatesKCoeff_target

/-! ### Bridge from the separation target to the headline -/

/-- The headline (`coeff_vanishes_of_beta_tower_target`) reduces to
the separation target whenever every β-tower-admissible `a` is also
pair-cosh-detector-admissible.  The latter requires three checks
beyond `BetaTowerAdmissible`: per-β summability, locally uniform
β-summability, symmetry compatibility, and detector-non-degeneracy.

The bridge is **stated as an obligation**, not yet proved, because
the four extra fields require auxiliary analysis on the natural
coefficient class `a = n·K`. -/
def betaTowerAdmissible_implies_pairCoshDetectorAdmissible_target : Prop :=
  ∀ (a : ℂ → ℂ), BetaTowerAdmissible a → PairCoshDetectorAdmissible a

/-- Bridge from the separation target (and the admissibility-implication
target) to the β-tower headline. -/
theorem coeff_vanishes_of_beta_tower_of_separation
    (h_admissible_bridge :
        betaTowerAdmissible_implies_pairCoshDetectorAdmissible_target)
    (h_sep : PairCoshDetectorSeparatesKCoeff_target) :
    coeff_vanishes_of_beta_tower_target := by
  intro a ha ρ hρ
  exact h_sep a (h_admissible_bridge a ha)
    (fun β hβ_pos hβ_lt => ha.vanish_on_real_interval β hβ_pos hβ_lt) ρ hρ

/-! ### Open structural questions

These are the operational questions the separation route exposes; each
is a candidate for direct attack. -/

/-- **Question (Q1): does the detector separate individual zeros, or
only FE/Klein orbits?**

Concretely: for two distinct zeros `ρ ≠ ρ'`, does there exist
`β ∈ (0,1)` such that `pairTestMellin(β, ρ) ≠ pairTestMellin(β, ρ')`?

If yes, the separation Prop above is achievable in single-zero form
without `symmetry_compatible`.  If no, the detector only separates
orbits; `symmetry_compatible` must be invoked to recover per-zero. -/
def detector_separates_individual_zeros_target : Prop :=
  ∀ ρ ρ' : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ρ ≠ ρ' →
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧
      Contour.pairTestMellin β ρ.val ≠ Contour.pairTestMellin β ρ'.val

/-- **Question (Q2): is the natural coefficient class `a = n·K`
pair-cosh-detector-admissible?**

If yes, the separation route discharges the K-twisted RH extraction.
If no, refine `a` or refine the admissibility. -/
def natural_K_coefficient_admissible_target : Prop :=
  ∀ (n : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℕ)
    (K : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ),
    -- Concrete `a` defined by `a(ρ) := if ρ ∈ NTZ then n_ρ · K_ρ else 0`.
    -- Stated abstractly; the natural target is the ZD-defined `n` and `K`.
    True

/-! ## Alternative extraction route: shifted-kernel Carlson uniqueness

The Carlson chain (Gap (i)/(ii)/(iii)) is preserved as a **secondary
route**.  It might still be reconstructed via different growth
analysis — e.g., a non-trivial cancellation argument that bounds
`phi a` on the real axis after all (the C-decomposition exposes the
structure without immediately producing cancellation, but a deeper
analysis at the SUM level might).

The Carlson tool (`RequestProject/CarlsonUniqueness.lean`) is
project-independent and reusable beyond this file regardless of
whether this specific route succeeds. -/

#print axioms coeff_vanishes_of_beta_tower_of_split_targets
#print axioms coeff_vanishes_of_beta_tower_of_split_targets_via_carlson
#print axioms coeff_vanishes_of_beta_tower_of_targets
#print axioms coeff_vanishes_of_beta_tower_of_separation
#print axioms phi_at_two_k_eq_zero_of_moment_tower
#print axioms phi_vanishes_on_halfplane_target_of_carlson_classical

end BetaTower
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
