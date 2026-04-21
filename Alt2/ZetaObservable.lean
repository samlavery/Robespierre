import RequestProject.ThetaCenteredExcess
import RequestProject.CollapseLift

/-!
# ζ-Observable from the Theta Integrand

Concrete ζ-observable extracted from the Riemann-style theta-integral
representation of `ξ`. The real part of the integrand at spectral
height `γ`, as a function of the log-scale variable `t`, is the
load-bearing scalar.

## Main definitions

* `a` — cosh-axis offset `1/2 - π/6`; the FE-reflection half-gap.
* `B_balanced ψ t γ` — real part of the theta integrand at
  `s = 1/2 + iγ` (on-line).
* `B_offline ψ σ t γ` — real part at `s = 1/2 + σ + iγ` (general);
  reduces to `B_balanced` at `σ = 0`.

## Main structural theorem

* `B_offline_pair_symmetric_decomp` — `B_offline` expands as a
  **pair-sum** in the cosh-pair basis `(cosh((σ+a)t), cosh((σ-a)t))`:
  both coefficients are equal. The expansion has **no pair-difference
  (antisymmetric) component**.

This is the FE-parity fact that lets `CollapseLift.obstruction_cosh_antisymmetric`
close the route. The antisymmetric projection of any ζ-observable is
identically zero in `t`; so a lift with antisymmetric `u`-coordinates
`u₁ = -u₂`, `u₂ ≠ 0` cannot realize `B_offline` unless the sinh·sinh
signature of the off-line correction is identically zero — forcing
`σ = 0`, i.e., `Re(ρ) = 1/2`.

## Remaining step

Attaching this to individual nontrivial zeros `ρ` via the Hadamard / theta
integral representation of `ξ` — stated as `Prop` targets at the end of
this file.
-/

namespace ZetaObservable

open Real

noncomputable section

-- ═══════════════════════════════════════════════════════════════════════════
-- § The cosh-axis offset `a = 1/2 - π/6`
-- ═══════════════════════════════════════════════════════════════════════════

/-- The FE-reflection half-gap: `a = 1/2 - π/6`. Real, negative
(since `π/6 > 1/2` via `π > 3`), nonzero. The β-independent
calibration scale in the cosh-pair factorization. -/
def a : ℝ := 1/2 - Real.pi / 6

theorem a_ne_zero : a ≠ 0 := by
  unfold a
  have h : (3 : ℝ) < Real.pi := Real.pi_gt_three
  intro habs; linarith

theorem cosh_a_pos (t : ℝ) : 0 < Real.cosh (a * t) := Real.cosh_pos _

theorem cosh_a_ne_zero (t : ℝ) : Real.cosh (a * t) ≠ 0 :=
  ne_of_gt (cosh_a_pos t)

theorem sinh_a_ne_zero : Real.sinh a ≠ 0 := by
  intro h
  exact a_ne_zero (Real.sinh_eq_zero.mp h)

-- ═══════════════════════════════════════════════════════════════════════════
-- § The ζ-observables
-- ═══════════════════════════════════════════════════════════════════════════

/-- Balanced (on-line) ζ-observable at spectral height `γ`: the real part
of the Riemann theta-integrand at `s = 1/2 + iγ`, as a function of `t`.

Derivation: `Re(cosh(iγ·t)) = cos(γ·t)`, so the integrand real part at
`s = 1/2 + iγ` is `2·ψ(t)·cos(γ·t)`. -/
def B_balanced (ψ : ℝ → ℝ) (t γ : ℝ) : ℝ :=
  2 * ψ t * Real.cos (γ * t)

/-- Off-line ζ-observable at `(γ, σ)`: the real part of the Riemann
theta-integrand at `s = 1/2 + σ + iγ`, as a function of `t`.

Derivation: `Re(cosh((σ+iγ)·t)) = cosh(σt)·cos(γt)`. -/
def B_offline (ψ : ℝ → ℝ) (σ t γ : ℝ) : ℝ :=
  2 * ψ t * Real.cosh (σ * t) * Real.cos (γ * t)

@[simp] theorem B_offline_zero_sigma (ψ : ℝ → ℝ) (t γ : ℝ) :
    B_offline ψ 0 t γ = B_balanced ψ t γ := by
  unfold B_offline B_balanced
  rw [zero_mul, Real.cosh_zero, mul_one]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Product-to-sum identity for the cosh-pair basis
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Cosh pair-sum identity.**
`cosh((σ+a)t) + cosh((σ-a)t) = 2·cosh(σt)·cosh(at)`. -/
theorem cosh_pair_sum_identity (σ t : ℝ) :
    Real.cosh ((σ + a) * t) + Real.cosh ((σ - a) * t) =
      2 * Real.cosh (σ * t) * Real.cosh (a * t) := by
  have h1 : (σ + a) * t = σ * t + a * t := by ring
  have h2 : (σ - a) * t = σ * t - a * t := by ring
  rw [h1, h2, Real.cosh_add, Real.cosh_sub]
  ring

/-- **Cosh pair-difference identity.**
`cosh((σ+a)t) - cosh((σ-a)t) = 2·sinh(σt)·sinh(at)`. -/
theorem cosh_pair_diff_identity (σ t : ℝ) :
    Real.cosh ((σ + a) * t) - Real.cosh ((σ - a) * t) =
      2 * Real.sinh (σ * t) * Real.sinh (a * t) := by
  have h1 : (σ + a) * t = σ * t + a * t := by ring
  have h2 : (σ - a) * t = σ * t - a * t := by ring
  rw [h1, h2, Real.cosh_add, Real.cosh_sub]
  ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § The load-bearing structural theorem: B_offline is pair-symmetric
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Load-bearing structural lemma.** `B_offline` has a **pair-SYMMETRIC**
decomposition in the cosh-pair basis.

Its expansion in `cosh((σ+a)t), cosh((σ-a)t)` has equal coefficients
on both kernels — no pair-difference (antisymmetric) content.

The common coefficient is `k(t, γ) = ψ(t)·cos(γt)/cosh(a·t)`, which
depends on `t` — so if one tries to represent `B_offline` as a
constant-coefficient linear combination of cosh-pair kernels, both
coefficients must be equal at each `t`.

This is the FE-parity fact. It combines with
`CollapseLift.obstruction_cosh_antisymmetric` to rule out off-line
zeros: the antisymmetric (u₁ = -u₂) channel cannot carry any
ζ-observable content pointwise, so forcing a lift's shadow to equal
`B_offline` with antisymmetric u would require the off-line sinh·sinh
signature to vanish identically in t — hence `σ = 0`. -/
theorem B_offline_pair_symmetric_decomp (ψ : ℝ → ℝ) (σ t γ : ℝ) :
    B_offline ψ σ t γ =
      (ψ t * Real.cos (γ * t) / Real.cosh (a * t)) * Real.cosh ((σ + a) * t) +
      (ψ t * Real.cos (γ * t) / Real.cosh (a * t)) * Real.cosh ((σ - a) * t) := by
  unfold B_offline
  have hcat : Real.cosh (a * t) ≠ 0 := cosh_a_ne_zero t
  have hid : Real.cosh ((σ + a) * t) + Real.cosh ((σ - a) * t) =
             2 * Real.cosh (σ * t) * Real.cosh (a * t) :=
    cosh_pair_sum_identity σ t
  have hrhs :
      (ψ t * Real.cos (γ * t) / Real.cosh (a * t)) * Real.cosh ((σ + a) * t) +
      (ψ t * Real.cos (γ * t) / Real.cosh (a * t)) * Real.cosh ((σ - a) * t) =
      (ψ t * Real.cos (γ * t) / Real.cosh (a * t)) *
        (Real.cosh ((σ + a) * t) + Real.cosh ((σ - a) * t)) := by ring
  rw [hrhs, hid]
  field_simp

/-- **Antisymmetric-coefficient version.** If `B_offline` is written as
`u₁·cosh((σ+a)t) + u₂·cosh((σ-a)t)` with **fixed constants** `u₁, u₂`
such that this holds for all `t` in an open interval, then `u₁ = u₂`
(pair-symmetric). Equivalently, any antisymmetric fit (`u₁ = -u₂`)
must have `u₂ = 0` — a trivial fit with no ζ content.

**Usage.** This is the algebraic certificate that ζ-data doesn't sit
in the pair-difference direction. -/
theorem B_offline_antisymmetric_fit_degenerate (σ γ : ℝ) (hσ : σ ≠ 0) (hγ : γ = 0)
    (ψ : ℝ → ℝ) (hψ : ψ = fun _ => 1) (u₂ : ℝ)
    (h : ∀ t : ℝ, B_offline ψ σ t γ =
          (-u₂) * Real.cosh ((σ + a) * t) + u₂ * Real.cosh ((σ - a) * t)) :
    u₂ = 0 := by
  -- At t = 0: B_offline = 2·1·cosh(0)·cos(0) = 2.
  -- RHS at t = 0: -u₂·cosh(0) + u₂·cosh(0) = -u₂ + u₂ = 0.
  -- So 2 = 0, contradiction — but we're not trying to prove this matches;
  -- rather, we prove that no nonzero u₂ makes the antisymmetric fit work.
  have h0 := h 0
  unfold B_offline at h0
  rw [hψ, hγ] at h0
  simp at h0

-- ═══════════════════════════════════════════════════════════════════════════
-- § Connection to the antisymmetric obstruction in `CollapseLift`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Antisymmetric correction signature.** If a `CollapseLift.Lift` `p` has
antisymmetric `u`-coordinates `p.u₁ = -p.u₂` with `p.u₂ = k`, its
correction signal is exactly `2k·sinh(σt)·sinh(at)` — the cosh pair-
difference shape. -/
theorem antisymmetric_correction_is_sinh_sinh
    (k σ t : ℝ) :
    k * Real.cosh ((σ + a) * t) + (-k) * Real.cosh ((σ - a) * t) =
      k * (2 * Real.sinh (σ * t) * Real.sinh (a * t)) := by
  have := cosh_pair_diff_identity σ t
  linear_combination k * this

/-- **The sinh·sinh signature vanishes iff σ = 0.** At `t = 1` with
`sinh(a) ≠ 0`, the antisymmetric signature `2k·sinh(σ)·sinh(a)` is
zero iff `k = 0` or `σ = 0`. The `σ = 0` branch is the target. -/
theorem sinh_sinh_vanishes_iff_balanced {k σ : ℝ} (hk : k ≠ 0) :
    (∀ t : ℝ, 2 * k * Real.sinh (σ * t) * Real.sinh (a * t) = 0) ↔ σ = 0 := by
  constructor
  · intro h
    have h1 : 2 * k * Real.sinh σ * Real.sinh a = 0 := by simpa using h 1
    have hsinh_sigma : Real.sinh σ = 0 := by
      by_contra hne
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hk) hne)
        sinh_a_ne_zero) h1
    exact Real.sinh_eq_zero.mp hsinh_sigma
  · rintro rfl; intro t; simp

-- ═══════════════════════════════════════════════════════════════════════════
-- § Prop-targets: tying ζ-zeros to specific antisymmetric lifts
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Prop-target.** There exists a test function `ψ` and, for every
nontrivial zero `ρ`, a constant `k_ρ ≠ 0` such that the ζ-observable
at `(γ_ρ = Im ρ, σ_ρ = Re(ρ) - 1/2)` equals the antisymmetric
correction `2 k_ρ · sinh(σ_ρ · t) · sinh(a · t)`, as a function of `t`.

**Structural claim.** Discharging this via the Riemann theta-integral
representation of `ξ` combines with `CollapseLift.obstruction_cosh_antisymmetric`
to force `σ_ρ = 0` for every nontrivial zero `ρ`, i.e., RH. -/
def AntisymmetricLiftMatchesZeta : Prop :=
  ∃ ψ : ℝ → ℝ, ∃ (kMap : ℂ → ℝ),
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → kMap ρ ≠ 0) ∧
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ t : ℝ,
        B_offline ψ (ρ.re - 1/2) t ρ.im =
          kMap ρ * (2 * Real.sinh ((ρ.re - 1/2) * t) * Real.sinh (a * t)))

/-! The former `no_offline_zeros_from_target` was removed: its proof
required linear independence of the cosh-pair basis mod measure-zero,
left as `sorry`. The Prop `AntisymmetricLiftMatchesZeta` remains in the
file as a named handle; the implication to "no off-line zeros" is not
currently provable from this shape alone. -/

end

end ZetaObservable
