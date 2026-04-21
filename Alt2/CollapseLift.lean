import Mathlib
import RequestProject.ZetaZeroDefs

/-!
# Helix-Shadow Collapse Lift — Function-Shadow Uniqueness Scaffold

Lift / projection / collapse-locus structure for the geometric
*uniqueness of the balanced collapse line* statement.

### Design (function-shadow, post-refactor)

* `ObservableShadow` carries `γ : ℝ` plus `B : ℝ → ℝ` — the observed
  reduced bridge as a *function* of the transport coordinate `t`.
* `Lift` carries `γ, σ, θ, u₁, u₂` (no `t` — `t` ranges freely in the
  observable).
* `CollapseData.π (p : Lift) : ObservableShadow` produces a function
  shadow `(t ↦ B₀(t, γ) + u₁ · G₁^σ(t, γ, θ) + u₂ · G₂^σ(t, γ, θ))`.

Matching two shadows now requires `γ`-agreement *and* pointwise
`B`-equality **over all t**. Single-point matching — the loophole in
the earlier pointwise scaffold — is no longer enough to share a shadow.

### Unconditional obstruction for cosh-pair

`obstruction_cosh_antisymmetric`: for the concrete `ofCoshPair B₀`
realization and any Lift `p` with antisymmetric latent coordinates
`p.u₁ = −p.u₂` and `p.u₂ ≠ 0`, shadow equality with a balanced lift
forces `σ = 0`. Proved **unconditionally** — no `RankTwoNonDegeneracy`
hypothesis. The mechanism: the antisymmetric combination isolates
the `sinh(σt) · sinh(at)` factor of the pair-agreement defect (with
`a = ½ − π/6`), and that factor vanishes iff `σ = 0`.

### Contents

* `ObservableShadow`, `Lift`, `CollapseData` — structures.
* `CollapseData.π`, `π_γ`, `π_B_apply` — projection.
* `amplitudeFactor`, `CollapseData.ofAmplitudeDeformed` — amplitude-deformed wiring.
* `CollapseData.ofCoshPair` — wiring to `ZetaDefs.coshDetectorLeft/Right`.
* `BalancedCollapse`, `CollapseLocus`.
* `RankTwoNonDegeneracy` — hypothesis form (for generic obstruction).
* `obstruction_theorem` — generic obstruction, conditional on RTND.
* `obstruction_cosh_antisymmetric` — **unconditional** obstruction for
  the cosh-pair realization with antisymmetric u.
* `ArchWitness.IsLocalObstruction` / `IsGlobalObstruction`.
-/

noncomputable section

namespace CollapseLift

-- ═══════════════════════════════════════════════════════════════════════════
-- § Base observable (function shadow)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Observable shadow** — `γ` plus the reduced-bridge value as a
function of the transport coordinate `t`. -/
structure ObservableShadow where
  /-- Spectral coordinate. -/
  γ : ℝ
  /-- Observed reduced-bridge function `B : t ↦ B(t)`. -/
  B : ℝ → ℝ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Lift (no `t` — shadow is a function of `t`, not a point at a fixed `t`)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lift** `X̃` — hidden coordinates only: `γ, σ, θ, u₁, u₂`.
Compared to the earlier pointwise scaffold, `t` is removed — it's
now a free variable in the function shadow. -/
structure Lift where
  /-- Spectral coordinate (visible in the shadow). -/
  γ  : ℝ
  /-- Off-line imbalance coordinate (hidden; `= 0` on balanced line). -/
  σ  : ℝ
  /-- Hidden phase coordinate. -/
  θ  : ℝ
  /-- Latent correction coordinate 1. -/
  u₁ : ℝ
  /-- Latent correction coordinate 2. -/
  u₂ : ℝ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Projection data
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Projection parameters.**

  * `B₀(t, γ)` — base bridge.
  * `G1 σ t γ θ` — first intrinsic channel `G₁^σ(t, γ, θ)`.
  * `G2 σ t γ θ` — second intrinsic channel `G₂^σ(t, γ, θ)`. -/
structure CollapseData where
  /-- Base bridge `B₀(t, γ)`. -/
  B₀ : ℝ → ℝ → ℝ
  /-- First intrinsic channel `G₁^σ(t, γ, θ)` with `σ` as first argument. -/
  G1 : ℝ → ℝ → ℝ → ℝ → ℝ
  /-- Second intrinsic channel `G₂^σ(t, γ, θ)`. -/
  G2 : ℝ → ℝ → ℝ → ℝ → ℝ

namespace CollapseData

variable (D : CollapseData)

/-- **The projection** `π : Lift → ObservableShadow`. The shadow's
`B` is now the function `t ↦ B₀(t, γ) + u₁ · G₁^σ(t, γ, θ) + u₂ · G₂^σ(t, γ, θ)`. -/
def π (p : Lift) : ObservableShadow where
  γ := p.γ
  B := fun t =>
    D.B₀ t p.γ
      + p.u₁ * D.G1 p.σ t p.γ p.θ
      + p.u₂ * D.G2 p.σ t p.γ p.θ

@[simp] theorem π_γ (p : Lift) : (D.π p).γ = p.γ := rfl

@[simp] theorem π_B_apply (p : Lift) (t : ℝ) :
    (D.π p).B t = D.B₀ t p.γ
      + p.u₁ * D.G1 p.σ t p.γ p.θ
      + p.u₂ * D.G2 p.σ t p.γ p.θ := rfl

end CollapseData

-- ═══════════════════════════════════════════════════════════════════════════
-- § Amplitude-deformed CollapseData  (unchanged interface)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Amplitude factor `A(σ, t) = exp(σ · t)` — the RH-style amplitude
deformation from the critical-line slice. `A(0, _) = 1`. -/
noncomputable def amplitudeFactor (σ t : ℝ) : ℝ := Real.exp (σ * t)

@[simp] theorem amplitudeFactor_zero_sigma (t : ℝ) : amplitudeFactor 0 t = 1 := by
  simp [amplitudeFactor]

theorem amplitudeFactor_pos (σ t : ℝ) : 0 < amplitudeFactor σ t :=
  Real.exp_pos _

/-- **Amplitude-deformed `CollapseData`.** `G_k^σ(t, γ, θ) = exp(σ · t) · G_k_base(t, γ, θ)`. -/
noncomputable def CollapseData.ofAmplitudeDeformed
    (B₀ : ℝ → ℝ → ℝ) (G1_base G2_base : ℝ → ℝ → ℝ → ℝ) : CollapseData where
  B₀ := B₀
  G1 := fun σ t γ θ => amplitudeFactor σ t * G1_base t γ θ
  G2 := fun σ t γ θ => amplitudeFactor σ t * G2_base t γ θ

namespace CollapseData

@[simp] theorem ofAmplitudeDeformed_G1_zero
    (B₀ : ℝ → ℝ → ℝ) (G1_base G2_base : ℝ → ℝ → ℝ → ℝ) (t γ θ : ℝ) :
    (CollapseData.ofAmplitudeDeformed B₀ G1_base G2_base).G1 0 t γ θ
      = G1_base t γ θ := by
  simp [CollapseData.ofAmplitudeDeformed]

@[simp] theorem ofAmplitudeDeformed_G2_zero
    (B₀ : ℝ → ℝ → ℝ) (G1_base G2_base : ℝ → ℝ → ℝ → ℝ) (t γ θ : ℝ) :
    (CollapseData.ofAmplitudeDeformed B₀ G1_base G2_base).G2 0 t γ θ
      = G2_base t γ θ := by
  simp [CollapseData.ofAmplitudeDeformed]

theorem ofAmplitudeDeformed_G1_factor
    (B₀ : ℝ → ℝ → ℝ) (G1_base G2_base : ℝ → ℝ → ℝ → ℝ) (σ t γ θ : ℝ) :
    (CollapseData.ofAmplitudeDeformed B₀ G1_base G2_base).G1 σ t γ θ
      = amplitudeFactor σ t
          * (CollapseData.ofAmplitudeDeformed B₀ G1_base G2_base).G1 0 t γ θ := by
  simp [CollapseData.ofAmplitudeDeformed]

theorem ofAmplitudeDeformed_G2_factor
    (B₀ : ℝ → ℝ → ℝ) (G1_base G2_base : ℝ → ℝ → ℝ → ℝ) (σ t γ θ : ℝ) :
    (CollapseData.ofAmplitudeDeformed B₀ G1_base G2_base).G2 σ t γ θ
      = amplitudeFactor σ t
          * (CollapseData.ofAmplitudeDeformed B₀ G1_base G2_base).G2 0 t γ θ := by
  simp [CollapseData.ofAmplitudeDeformed]

end CollapseData

-- ═══════════════════════════════════════════════════════════════════════════
-- § Concrete wiring to `ZetaDefs.coshDetectorLeft/Right`
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Cosh-pair `CollapseData`.** Wires `G_1, G_2` directly to
`ZetaDefs.coshDetectorLeft, coshDetectorRight` with the
RH-style substitution `β = 1/2 + σ`. -/
noncomputable def CollapseData.ofCoshPair (B₀ : ℝ → ℝ → ℝ) : CollapseData where
  B₀ := B₀
  G1 := fun σ t _γ _θ => ZetaDefs.coshDetectorLeft (1 / 2 + σ) t
  G2 := fun σ t _γ _θ => ZetaDefs.coshDetectorRight (1 / 2 + σ) t

namespace CollapseData

@[simp] theorem ofCoshPair_G1 (B₀ : ℝ → ℝ → ℝ) (σ t γ θ : ℝ) :
    (CollapseData.ofCoshPair B₀).G1 σ t γ θ
      = Real.cosh ((σ + (1 / 2 - Real.pi / 6)) * t) := by
  show ZetaDefs.coshDetectorLeft (1 / 2 + σ) t
      = Real.cosh ((σ + (1 / 2 - Real.pi / 6)) * t)
  unfold ZetaDefs.coshDetectorLeft
  congr 1; ring

@[simp] theorem ofCoshPair_G2 (B₀ : ℝ → ℝ → ℝ) (σ t γ θ : ℝ) :
    (CollapseData.ofCoshPair B₀).G2 σ t γ θ
      = Real.cosh ((σ - (1 / 2 - Real.pi / 6)) * t) := by
  show ZetaDefs.coshDetectorRight (1 / 2 + σ) t
      = Real.cosh ((σ - (1 / 2 - Real.pi / 6)) * t)
  unfold ZetaDefs.coshDetectorRight
  congr 1; ring

theorem ofCoshPair_detectors_agree_at_zero (B₀ : ℝ → ℝ → ℝ) (t γ θ : ℝ) :
    (CollapseData.ofCoshPair B₀).G1 0 t γ θ
      = (CollapseData.ofCoshPair B₀).G2 0 t γ θ := by
  simp only [ofCoshPair_G1, ofCoshPair_G2, zero_add, zero_sub]
  rw [show -(1 / 2 - Real.pi / 6) * t = -((1 / 2 - Real.pi / 6) * t) by ring,
      Real.cosh_neg]

end CollapseData

-- ═══════════════════════════════════════════════════════════════════════════
-- § Balanced collapse and collapse locus
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Balanced collapse** — the hidden imbalance coordinate vanishes. -/
def BalancedCollapse (p : Lift) : Prop := p.σ = 0

/-- **The collapse locus** `C := {p ∈ X̃ : σ(p) = 0}`. -/
def CollapseLocus : Set Lift := { p | BalancedCollapse p }

@[simp] theorem mem_collapseLocus {p : Lift} :
    p ∈ CollapseLocus ↔ p.σ = 0 := Iff.rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- § Generic obstruction — two satisfiable hypotheses
--
-- Replaces the earlier `RankTwoNonDegeneracy` (which was unsatisfiable
-- — trivial u₁ = u₂ = 0 was a counterexample for any concrete `D`) with
-- two cleanly stated predicates that the `ofCoshPair` construction
-- actually satisfies:
--   * `BalancedAgree` — at `σ = 0`, the two channels agree.
--   * `SigmaSeparates` — at σ ≠ 0, `v(G₂^σ − G₁^σ) = w·G₁^0` over all
--     `t` forces `σ = 0` (for `v ≠ 0`).
-- Under the antisymmetric combination `p.u₁ = −p.u₂, p.u₂ ≠ 0`,
-- these jointly imply the obstruction.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Balanced-slice agreement**: `G₁^0 = G₂^0` as functions of `(t, γ, θ)`.
Satisfied by `ofCoshPair` via `ofCoshPair_detectors_agree_at_zero`. -/
def BalancedAgree (D : CollapseData) : Prop :=
  ∀ t γ θ, D.G1 0 t γ θ = D.G2 0 t γ θ

/-- **Sigma separator**: the functional equation
`v · (G₂^σ(t,γ,θ) − G₁^σ(t,γ,θ)) = w · G₁^0(t,γ,θ₀)` at every `t`
forces `σ = 0`, whenever `v ≠ 0`. Satisfied by `ofCoshPair` via the
sinh factorization. -/
def SigmaSeparates (D : CollapseData) : Prop :=
  ∀ (γ σ θ θ₀ v w : ℝ), v ≠ 0 →
    (∀ t, v * (D.G2 σ t γ θ - D.G1 σ t γ θ) = w * D.G1 0 t γ θ₀) →
    σ = 0

/-- **Generic obstruction theorem.**

A lifted point `p` with antisymmetric, non-trivial latent coords
(`p.u₁ = -p.u₂`, `p.u₂ ≠ 0`) sharing a shadow with a balanced lift
`p₀` must itself be balanced, provided `D` satisfies `BalancedAgree`
and `SigmaSeparates`. -/
theorem obstruction_theorem (D : CollapseData)
    (hBA : BalancedAgree D) (hSS : SigmaSeparates D)
    (p p₀ : Lift)
    (h_asym : p.u₁ = -p.u₂)
    (h_nontriv : p.u₂ ≠ 0)
    (h₀ : BalancedCollapse p₀)
    (hπ : D.π p = D.π p₀) :
    BalancedCollapse p := by
  have hγ : p.γ = p₀.γ := by simpa using congrArg ObservableShadow.γ hπ
  have hσ₀ : p₀.σ = 0 := h₀
  have hB_fun : (D.π p).B = (D.π p₀).B := congrArg ObservableShadow.B hπ
  -- Cancel B₀ and substitute γ, σ₀:
  have hBt : ∀ t, p.u₁ * D.G1 p.σ t p₀.γ p.θ + p.u₂ * D.G2 p.σ t p₀.γ p.θ
              = p₀.u₁ * D.G1 0 t p₀.γ p₀.θ + p₀.u₂ * D.G2 0 t p₀.γ p₀.θ := by
    intro t
    have h := congrFun hB_fun t
    simp only [CollapseData.π_B_apply] at h
    rw [hγ, hσ₀] at h
    linarith
  -- Use `BalancedAgree` to collapse RHS to `(u₁₀ + u₂₀) · G₁^0`:
  -- Use antisymmetry to rewrite LHS as `p.u₂ · (G₂^σ − G₁^σ)`:
  have hKey : ∀ t, p.u₂ * (D.G2 p.σ t p₀.γ p.θ - D.G1 p.σ t p₀.γ p.θ)
                = (p₀.u₁ + p₀.u₂) * D.G1 0 t p₀.γ p₀.θ := by
    intro t
    have h := hBt t
    have hBA_t : D.G2 0 t p₀.γ p₀.θ = D.G1 0 t p₀.γ p₀.θ :=
      (hBA t p₀.γ p₀.θ).symm
    rw [h_asym, hBA_t] at h
    linarith
  -- Apply `SigmaSeparates` with v = p.u₂, w = p₀.u₁ + p₀.u₂:
  exact hSS p₀.γ p.σ p.θ p₀.θ p.u₂ (p₀.u₁ + p₀.u₂) h_nontriv hKey

/-- **Set-form corollary** of the generic obstruction theorem. -/
theorem in_collapseLocus_of_shadow_eq (D : CollapseData)
    (hBA : BalancedAgree D) (hSS : SigmaSeparates D)
    {p p₀ : Lift}
    (h_asym : p.u₁ = -p.u₂)
    (h_nontriv : p.u₂ ≠ 0)
    (h₀ : p₀ ∈ CollapseLocus)
    (hπ : D.π p = D.π p₀) :
    p ∈ CollapseLocus :=
  obstruction_theorem D hBA hSS p p₀ h_asym h_nontriv h₀ hπ

-- ═══════════════════════════════════════════════════════════════════════════
-- § `ofCoshPair` satisfies both hypotheses unconditionally
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`ofCoshPair` satisfies `BalancedAgree`.** -/
theorem ofCoshPair_balanced_agree (B₀ : ℝ → ℝ → ℝ) :
    BalancedAgree (CollapseData.ofCoshPair B₀) := by
  intro t γ θ
  exact CollapseData.ofCoshPair_detectors_agree_at_zero B₀ t γ θ

/-- **`ofCoshPair` satisfies `SigmaSeparates`.**

The functional equation `v · (cosh((σ−a)t) − cosh((σ+a)t)) = w · cosh(a·t)`
at every `t` (with `a = ½ − π/6`, `v ≠ 0`) forces `σ = 0`.

Sketch: `cosh((σ−a)t) − cosh((σ+a)t) = −2 sinh(σt) sinh(at)`. At `t = 0`
both sides are `0`, so `w · cosh(0) = 0`, hence `w = 0`. Plugging back,
`v · sinh(σt) · sinh(at) = 0` for all `t`. At `t = 1`, with `v ≠ 0` and
`sinh(a) ≠ 0` (since `π > 3` gives `a ≠ 0`), `sinh(σ) = 0`, so `σ = 0`. -/
theorem ofCoshPair_sigma_separates (B₀ : ℝ → ℝ → ℝ) :
    SigmaSeparates (CollapseData.ofCoshPair B₀) := by
  intro γ σ θ θ₀ v w hv hfn
  -- Simplify each term with the cosh closed form.
  -- Specifically: G2^σ t γ θ - G1^σ t γ θ = cosh((σ-a)t) - cosh((σ+a)t)
  -- and G1^0 t γ θ₀ = cosh(a*t), with a := 1/2 - π/6.
  set a : ℝ := 1 / 2 - Real.pi / 6 with ha_def
  have hfn' : ∀ t,
      v * (Real.cosh ((σ - a) * t) - Real.cosh ((σ + a) * t))
        = w * Real.cosh (a * t) := by
    intro t
    have h := hfn t
    simp only [CollapseData.ofCoshPair_G1, CollapseData.ofCoshPair_G2] at h
    -- Rewrite args in terms of `a`
    have hE1 : Real.cosh ((σ + (1/2 - Real.pi/6)) * t)
              = Real.cosh ((σ + a) * t) := by rfl
    have hE2 : Real.cosh ((σ - (1/2 - Real.pi/6)) * t)
              = Real.cosh ((σ - a) * t) := by rfl
    have hE3 : Real.cosh ((0 + (1/2 - Real.pi/6)) * t)
              = Real.cosh (a * t) := by
      show Real.cosh ((0 + (1/2 - Real.pi/6)) * t) = Real.cosh ((1/2 - Real.pi/6) * t)
      congr 1; ring
    rw [hE1, hE2, hE3] at h
    exact h
  -- At t = 0: LHS = v * 0 = 0, RHS = w * cosh(0) = w. So w = 0.
  have hw0 : w = 0 := by
    have h := hfn' 0
    simp at h
    exact h.symm
  -- With w = 0: v * (cosh((σ-a)t) - cosh((σ+a)t)) = 0 for all t.
  have hVanish : ∀ t,
      v * (Real.cosh ((σ - a) * t) - Real.cosh ((σ + a) * t)) = 0 := by
    intro t
    have h := hfn' t
    rw [hw0] at h
    linarith
  -- Convert to sinh form.
  have hSinh : ∀ t,
      Real.cosh ((σ - a) * t) - Real.cosh ((σ + a) * t)
      = -2 * Real.sinh (σ * t) * Real.sinh (a * t) := by
    intro t
    have h1 : (σ - a) * t = σ * t - a * t := by ring
    have h2 : (σ + a) * t = σ * t + a * t := by ring
    rw [h1, h2, Real.cosh_sub, Real.cosh_add]; ring
  have hKey : ∀ t, v * (-2 * Real.sinh (σ * t) * Real.sinh (a * t)) = 0 := by
    intro t
    rw [← hSinh t]; exact hVanish t
  -- At t = 1: v * (-2) * sinh(σ) * sinh(a) = 0.
  have hT1 : v * (-2 * Real.sinh σ * Real.sinh a) = 0 := by
    have := hKey 1
    simpa using this
  -- a ≠ 0 since π > 3.
  have ha_ne : a ≠ 0 := by
    show (1 : ℝ) / 2 - Real.pi / 6 ≠ 0
    have h_gt : (3 : ℝ) < Real.pi := Real.pi_gt_three
    intro h
    linarith
  have hsinh_a_ne : Real.sinh a ≠ 0 := fun h => ha_ne (Real.sinh_eq_zero.mp h)
  -- Extract sinh(σ) = 0 ⟹ σ = 0.
  have hsinh_sigma : Real.sinh σ = 0 := by
    have hfactor : (-2 : ℝ) ≠ 0 := by norm_num
    have hA : -2 * Real.sinh σ * Real.sinh a = 0 := by
      rcases mul_eq_zero.mp hT1 with h1 | h2
      · exact absurd h1 hv
      · exact h2
    have hB : -2 * Real.sinh σ = 0 := by
      rcases mul_eq_zero.mp hA with h1 | h2
      · exact h1
      · exact absurd h2 hsinh_a_ne
    rcases mul_eq_zero.mp hB with h1 | h2
    · exact absurd h1 hfactor
    · exact h2
  exact Real.sinh_eq_zero.mp hsinh_sigma

/-- **Unconditional obstruction — cosh-pair antisymmetric case.**

Corollary of `obstruction_theorem` applied to `ofCoshPair B₀`, using
the two satisfiability witnesses `ofCoshPair_balanced_agree` and
`ofCoshPair_sigma_separates`.

No open hypotheses — discharged directly from the cosh-pair geometry. -/
theorem obstruction_cosh_antisymmetric (B₀ : ℝ → ℝ → ℝ)
    (p p₀ : Lift)
    (h_asym : p.u₁ = -p.u₂)
    (h_nontriv : p.u₂ ≠ 0)
    (h₀ : BalancedCollapse p₀)
    (hπ : (CollapseData.ofCoshPair B₀).π p
            = (CollapseData.ofCoshPair B₀).π p₀) :
    BalancedCollapse p :=
  obstruction_theorem (CollapseData.ofCoshPair B₀)
    (ofCoshPair_balanced_agree B₀) (ofCoshPair_sigma_separates B₀)
    p p₀ h_asym h_nontriv h₀ hπ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Archimedean witness — local / global obstruction predicates (unchanged)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Archimedean witness** at a fixed `(t, γ)`. -/
@[reducible] def ArchWitness : Type := ℝ → ℝ

namespace ArchWitness

/-- **Local obstruction property.** -/
def IsLocalObstruction (O : ArchWitness) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ σ : ℝ, 0 < |σ| → |σ| < ε → O σ < O 0

/-- **Global obstruction property.** -/
def IsGlobalObstruction (O : ArchWitness) : Prop :=
  ∀ σ : ℝ, σ ≠ 0 → O σ < O 0

/-- Global obstruction strictly implies local obstruction. -/
theorem IsGlobalObstruction.isLocalObstruction
    {O : ArchWitness} (h : IsGlobalObstruction O) :
    IsLocalObstruction O :=
  ⟨1, one_pos, fun σ hσ _ => h σ (abs_pos.mp hσ)⟩

end ArchWitness

end CollapseLift
