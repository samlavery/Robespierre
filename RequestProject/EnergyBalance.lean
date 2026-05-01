import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.EnergyDefect
import RequestProject.WeilBridge
import RequestProject.OfflineAmplitudeMethods

/-!
# Energy Balance — Excess Defect and the Critical Line

Unconditional theorems relating the averaged energy defect to the
critical line. The "excess defect changes the real part" content:
any `β` at which the averaged energy defect is strictly positive is
**off** the critical line.

### Proved (mathlib baseline axioms only)

* `excess_defect_moves_real_off_line` — `0 < avgEnergyDefect ψ β → β ≠ 1/2`.
* `on_line_no_excess` — `avgEnergyDefect ψ (1/2) = 0`.
* `energy_balance_iff_on_line` — assuming admissible `ψ`,
  `avgEnergyDefect ψ β = 0 ↔ β = 1/2`.

### Applied at nontrivial zeros

* `zero_with_excess_is_offline` — a nontrivial ζ zero with excess
  energy defect at `ρ.re` cannot be on the critical line.
* `zero_on_line_no_excess` — a nontrivial ζ zero on the critical
  line produces zero energy defect.

### Converse

The converse — "every nontrivial ζ zero has zero averaged energy
defect at `β = ρ.re`" — is the analytic content of the Weil explicit
formula for a custom test function. -/

open Real ZetaDefs MeasureTheory

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § Unconditional energy-balance theorems
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Excess defect moves the real part off the critical line.**

If the averaged energy defect at `β` is strictly positive, then
`β ≠ 1/2`. Proved by contraposition against `averageEnergyDefect_zero_on_line`. -/
theorem excess_defect_moves_real_off_line (ψ : ℝ → ℝ) {β : ℝ}
    (hExcess : 0 < averageEnergyDefect ψ β) :
    β ≠ 1 / 2 := by
  intro hβ
  rw [hβ] at hExcess
  have hzero := averageEnergyDefect_zero_on_line ψ
  linarith

/-- **On-line, no excess.** -/
theorem on_line_no_excess (ψ : ℝ → ℝ) :
    averageEnergyDefect ψ (1 / 2) = 0 :=
  averageEnergyDefect_zero_on_line ψ

/-- **Energy balance as a biconditional** (assuming `ψ` admissible):
averaged defect vanishes iff `β = 1/2`. -/
theorem energy_balance_iff_on_line (ψ : ℝ → ℝ)
    (hψ : AdmissibleThetaKernel ψ) (β : ℝ) :
    averageEnergyDefect ψ β = 0 ↔ β = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · intro hdef
    by_contra hne
    have hpos := averaged_positivity_offline ψ hψ hne
    linarith
  · intro hβ
    rw [hβ]
    exact averageEnergyDefect_zero_on_line ψ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Applied at nontrivial ζ zeros
-- ═══════════════════════════════════════════════════════════════════════════

/-- A nontrivial ζ zero with excess energy defect at `ρ.re` is
off-line. -/
theorem zero_with_excess_is_offline (ψ : ℝ → ℝ)
    {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros)
    (hExcess : 0 < averageEnergyDefect ψ ρ.re) :
    ρ.re ≠ 1 / 2 :=
  excess_defect_moves_real_off_line ψ hExcess

/-- A nontrivial ζ zero on the critical line produces zero energy
defect. -/
theorem zero_on_line_no_excess (ψ : ℝ → ℝ) {ρ : ℂ}
    (_hρ : ρ ∈ ZD.NontrivialZeros) (h : ρ.re = 1 / 2) :
    averageEnergyDefect ψ ρ.re = 0 := by
  rw [h]; exact averageEnergyDefect_zero_on_line ψ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Impossibility: an online zero cannot have even channel defect
--
-- Structural fact: at β = 1/2, the cosineDefectTransform is identically
-- zero (for every γ and every ψ). This makes it IMPOSSIBLE for an
-- online zero to exhibit any even channel energy defect.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The even channel vanishes identically on the critical line.**
`cosineDefectTransform ψ (1/2) γ = 0` for every ψ and every γ. -/
theorem even_channel_zero_on_line (ψ : ℝ → ℝ) (γ : ℝ) :
    cosineDefectTransform ψ (1 / 2) γ = 0 := by
  unfold cosineDefectTransform amplitudeDefectEnvelope
  have h : ∀ t : ℝ,
      (Real.cosh ((1 / 2 - 1 / 2) * t) - 1) * Real.cos (γ * t) * ψ t = 0 := by
    intro t; simp [Real.cosh_zero]
  simp_rw [h]; simp

/-- **Online zero has no even channel defect.** If `ρ` is a nontrivial
zero with `ρ.re = 1/2`, then `cosineDefectTransform ψ ρ.re γ = 0` for
every test function ψ and every γ. -/
theorem online_zero_no_even_channel_defect
    (ψ : ℝ → ℝ) {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros)
    (h_online : ρ.re = 1 / 2) (γ : ℝ) :
    cosineDefectTransform ψ ρ.re γ = 0 := by
  rw [h_online]; exact even_channel_zero_on_line ψ γ

/-- **Impossibility statement**: an online zero cannot have nonzero even
channel defect. The negation of "possible". -/
theorem impossible_online_zero_with_even_defect
    (ψ : ℝ → ℝ) {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros)
    (h_online : ρ.re = 1 / 2) (γ : ℝ) :
    ¬ (cosineDefectTransform ψ ρ.re γ ≠ 0) := by
  intro hne
  exact hne (online_zero_no_even_channel_defect ψ _hρ h_online γ)

/-- Online zero has zero averaged energy defect — impossibility of
any averaged excess at an online zero. -/
theorem online_zero_no_averaged_defect
    (ψ : ℝ → ℝ) {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros)
    (h_online : ρ.re = 1 / 2) :
    averageEnergyDefect ψ ρ.re = 0 := by
  rw [h_online]; exact averageEnergyDefect_zero_on_line ψ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Offline-zero detector excess (detector geometry only, no RH framing)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Offline nontrivial zeros produce detector excess.** Pure detector
geometry: `averageEnergyDefect ψ β` is the Parseval-rewritten weighted
L² norm `2π · ∫((cosh((β−1/2)t)−1)² + sinh²((β−1/2)t))·ψ(t)² dt`, whose
integrand vanishes pointwise iff `β = 1/2`. For a nontrivial zero `ρ`
with `ρ.re ≠ 1/2` — *offline* — the detector excess at `ρ.re` is strictly
positive. No RH content; it is `averaged_positivity_offline` specialized
to an offline zero. -/
theorem offlineZero_detector_excess_pos (ψ : ℝ → ℝ)
    (hψ : AdmissibleThetaKernel ψ) {ρ : ℂ}
    (_hρ : ρ ∈ ZD.NontrivialZeros) (h_off : ρ.re ≠ 1 / 2) :
    0 < averageEnergyDefect ψ ρ.re :=
  averaged_positivity_offline ψ hψ h_off

-- ═══════════════════════════════════════════════════════════════════════════
-- § Prime-harmonic probes
--
-- Analogous statements at prime scales: excess at a prime forces
-- `ρ.re ≠ 1/2`. Uses `OfflineAmplitudeMethods.pairAgreementDefect`.
-- ═══════════════════════════════════════════════════════════════════════════

end ZD

namespace EnergyBalancePrime

open Real ZetaDefs

/-- **Prime-harmonic excess moves real off-line** — contrapositive of the
unconditional biconditional `pairAgreementDefect_eq_zero_iff` at a
prime `p ≥ 2`. If the pair-agreement defect is strictly positive at
`p`, `β ≠ 1/2`. -/
theorem excess_prime_pair_defect_moves_real_off_line
    (p : ℕ) (hp : Nat.Prime p) {β : ℝ}
    (hExcess : 0 < pairAgreementDefect (p : ℝ) β) :
    β ≠ 1 / 2 := by
  intro hβ
  rw [hβ] at hExcess
  have hne1 : ((p : ℝ)) ≠ 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hzero := (pairAgreementDefect_eq_zero_iff hpos hne1 (β := (1/2 : ℝ))).mpr rfl
  linarith

/-- Applied to nontrivial ζ zeros: if *any* prime-harmonic pair-defect
is nonzero at `ρ`, then `ρ` is off the critical line. -/
theorem zeta_zero_with_prime_excess_is_offline
    {ρ : ℂ} (_hρ : ρ ∈ ZD.NontrivialZeros)
    {p : ℕ} (hp : Nat.Prime p)
    (hExcess : 0 < pairAgreementDefect (p : ℝ) ρ.re) :
    ρ.re ≠ 1 / 2 :=
  excess_prime_pair_defect_moves_real_off_line p hp hExcess

/-- **Klein-four form**: the averaged energy defect is constant across
the Klein-four orbit `{ρ, 1−ρ, ρ̄, 1−ρ̄}` of any zero `ρ`, so excess
at one element is excess at all four. Shown explicitly for
`ρ` vs `1 − ρ` (the `β ↔ 1−β` reflection). -/
theorem klein_four_excess_reflect (ψ : ℝ → ℝ) (β : ℝ)
    (hExcess : 0 < ZD.averageEnergyDefect ψ β) :
    0 < ZD.averageEnergyDefect ψ (1 - β) := by
  rw [ZD.averageEnergyDefect_reflect]
  exact hExcess

/-- Contrapositive of `klein_four_excess_reflect`: if `(1−β)` has no
excess, then `β` has no excess. -/
theorem klein_four_no_excess_reflect (ψ : ℝ → ℝ) (β : ℝ)
    (hNo : ZD.averageEnergyDefect ψ (1 - β) = 0) :
    ZD.averageEnergyDefect ψ β = 0 := by
  rw [← ZD.averageEnergyDefect_reflect]
  exact hNo

end EnergyBalancePrime
