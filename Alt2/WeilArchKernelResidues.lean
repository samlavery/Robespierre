import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import RequestProject.WeilContour

/-!
# Residue of `s · Γℝ'(s) / Γℝ(s)` at `s = 0`

`Γℝ(s) = π^(-s/2) · Γ(s/2)` has a simple pole at `s = 0` (with residue `2`),
so the logarithmic derivative `Γℝ'(s)/Γℝ(s)` behaves like `-1/s` near 0, and
`s · Γℝ'(s)/Γℝ(s) → -1`.

## Strategy

From the functional equation `s · Γℝ(s) = 2π · Γℝ(s+2)` (which is
`Complex.Gammaℝ_add_two` rearranged), differentiating yields, on the open set
`{s : s ≠ 0}`:

  `Γℝ(s) + s · Γℝ'(s) = 2π · Γℝ'(s+2)`.

Dividing by `Γℝ(s)` and substituting `Γℝ(s) = 2π · Γℝ(s+2) / s`:

  `s · Γℝ'(s) / Γℝ(s) = s · Γℝ'(s+2) / Γℝ(s+2) - 1`.

The RHS is continuous at `s = 0` with value `0 · Γℝ'(2)/Γℝ(2) - 1 = -1`,
giving the desired limit.
-/

noncomputable section

open Filter Topology Complex
open scoped Real

namespace ZD.WeilArchKernelResidues

/-- `Γℝ(2) ≠ 0`, since `Re 2 = 2 > 0`. -/
private lemma Gammaℝ_two_ne_zero : Complex.Gammaℝ 2 ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)

/-- `{s : ℂ | s.Gammaℝ ≠ 0}` is open. -/
private lemma Gammaℝ_ne_zero_isOpen : IsOpen {s : ℂ | s.Gammaℝ ≠ 0} := by
  have h_cont : Continuous (fun s : ℂ => s.Gammaℝ⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.continuous
  have h_eq : {s : ℂ | s.Gammaℝ ≠ 0} =
      (fun s : ℂ => s.Gammaℝ⁻¹) ⁻¹' {z : ℂ | z ≠ 0} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    refine ⟨inv_ne_zero, fun h hs => ?_⟩
    apply h; rw [hs, inv_zero]
  rw [h_eq]
  exact IsOpen.preimage h_cont isOpen_ne

/-- `Γℝ` is analytic on `{Γℝ ≠ 0}`. -/
private lemma Gammaℝ_analyticOnNhd :
    AnalyticOnNhd ℂ Complex.Gammaℝ {s : ℂ | s.Gammaℝ ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (ZD.WeilPositivity.Contour.differentiableAt_Gammaℝ_of_ne_zero hs).differentiableWithinAt
  · exact Gammaℝ_ne_zero_isOpen

/-- `deriv Γℝ` is analytic on `{Γℝ ≠ 0}`. -/
private lemma deriv_Gammaℝ_analyticOnNhd :
    AnalyticOnNhd ℂ (deriv Complex.Gammaℝ) {s : ℂ | s.Gammaℝ ≠ 0} :=
  Gammaℝ_analyticOnNhd.deriv

/-- The functional identity `s · Γℝ(s) = 2π · Γℝ(s+2)` for `s ≠ 0`,
rewritten from `Complex.Gammaℝ_add_two`. -/
private lemma s_mul_Gammaℝ_eq (s : ℂ) (hs : s ≠ 0) :
    s * Complex.Gammaℝ s = 2 * (Real.pi : ℂ) * Complex.Gammaℝ (s + 2) := by
  have h := Complex.Gammaℝ_add_two hs
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [h]; field_simp

/-- The differentiated form: at any `s ≠ 0` with `Γℝ(s) ≠ 0` and
`Γℝ(s+2) ≠ 0`, we have `Γℝ(s) + s · Γℝ'(s) = 2π · Γℝ'(s+2)`. -/
private lemma deriv_identity (s : ℂ) (hs : s ≠ 0)
    (hgs : Complex.Gammaℝ s ≠ 0) (hgs2 : Complex.Gammaℝ (s + 2) ≠ 0) :
    Complex.Gammaℝ s + s * deriv Complex.Gammaℝ s
      = 2 * (Real.pi : ℂ) * deriv Complex.Gammaℝ (s + 2) := by
  have hdiff_s :=
    ZD.WeilPositivity.Contour.differentiableAt_Gammaℝ_of_ne_zero hgs
  have hdiff_s2 :=
    ZD.WeilPositivity.Contour.differentiableAt_Gammaℝ_of_ne_zero hgs2
  -- d/ds [s · Γℝ(s)] = Γℝ(s) + s · Γℝ'(s)
  have hL : HasDerivAt (fun z : ℂ => z * Complex.Gammaℝ z)
      (1 * Complex.Gammaℝ s + s * deriv Complex.Gammaℝ s) s :=
    (hasDerivAt_id s).mul hdiff_s.hasDerivAt
  -- d/ds [2π · Γℝ(s+2)] = 2π · Γℝ'(s+2) (via chain rule with `id+2`)
  have hadd : HasDerivAt (fun z : ℂ => z + 2) 1 s := (hasDerivAt_id s).add_const 2
  have hcomp : HasDerivAt
      ((fun z : ℂ => Complex.Gammaℝ z) ∘ (fun z : ℂ => z + 2))
      (deriv Complex.Gammaℝ (s + 2) * 1) s :=
    hdiff_s2.hasDerivAt.comp s hadd
  have hR : HasDerivAt (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (z + 2))
      (2 * (Real.pi : ℂ) * (deriv Complex.Gammaℝ (s + 2) * 1)) s :=
    hcomp.const_mul _
  -- Both functions agree on a neighborhood of `s` (using `{0}ᶜ` ∈ 𝓝 s).
  have heq : (fun z : ℂ => z * Complex.Gammaℝ z) =ᶠ[𝓝 s]
      (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (z + 2)) := by
    have h_open : ({0}ᶜ : Set ℂ) ∈ 𝓝 s := isOpen_compl_singleton.mem_nhds hs
    filter_upwards [h_open] with z hz
    exact s_mul_Gammaℝ_eq z hz
  -- Therefore their `deriv`s coincide.
  have hderiv_eq : deriv (fun z : ℂ => z * Complex.Gammaℝ z) s
      = deriv (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.Gammaℝ (z + 2)) s :=
    heq.deriv_eq
  rw [hL.deriv, hR.deriv] at hderiv_eq
  linear_combination hderiv_eq

/-- The auxiliary function `s ↦ s · Γℝ'(s+2)/Γℝ(s+2) - 1` is continuous at 0
and equals `-1` there. -/
private lemma aux_continuousAt :
    ContinuousAt (fun s : ℂ =>
        s * deriv Complex.Gammaℝ (s + 2) / Complex.Gammaℝ (s + 2) - 1) 0 := by
  have h2 : Complex.Gammaℝ (2 : ℂ) ≠ 0 := Gammaℝ_two_ne_zero
  have h2mem : (2 : ℂ) ∈ {s : ℂ | s.Gammaℝ ≠ 0} := h2
  -- `deriv Γℝ` is continuous at 2.
  have hd_cont : ContinuousAt (deriv Complex.Gammaℝ) 2 :=
    (deriv_Gammaℝ_analyticOnNhd _ h2mem).continuousAt
  -- `Γℝ` is continuous at 2.
  have hg_cont : ContinuousAt Complex.Gammaℝ 2 :=
    (Gammaℝ_analyticOnNhd _ h2mem).continuousAt
  -- Compose with `s ↦ s + 2` (continuous at 0, sending 0 to 2).
  have hshift : ContinuousAt (fun s : ℂ => s + 2) 0 :=
    (continuous_id.add continuous_const).continuousAt
  have hd_shift : ContinuousAt (fun s : ℂ => deriv Complex.Gammaℝ (s + 2)) 0 := by
    have h := ContinuousAt.comp (g := deriv Complex.Gammaℝ)
      (f := fun s : ℂ => s + 2) (x := 0)
      (show ContinuousAt (deriv Complex.Gammaℝ) ((fun s : ℂ => s + 2) 0) by
        change ContinuousAt (deriv Complex.Gammaℝ) (0 + 2)
        rw [zero_add]; exact hd_cont) hshift
    exact h
  have hg_shift : ContinuousAt (fun s : ℂ => Complex.Gammaℝ (s + 2)) 0 := by
    have h := ContinuousAt.comp (g := Complex.Gammaℝ)
      (f := fun s : ℂ => s + 2) (x := 0)
      (show ContinuousAt Complex.Gammaℝ ((fun s : ℂ => s + 2) 0) by
        change ContinuousAt Complex.Gammaℝ (0 + 2)
        rw [zero_add]; exact hg_cont) hshift
    exact h
  have hg2_ne : Complex.Gammaℝ ((0 : ℂ) + 2) ≠ 0 := by
    simpa using h2
  -- Build the composite
  have h_id_cont : ContinuousAt (fun s : ℂ => s) 0 := continuous_id.continuousAt
  have h_num : ContinuousAt
      (fun s : ℂ => s * deriv Complex.Gammaℝ (s + 2)) 0 :=
    h_id_cont.mul hd_shift
  have h_div : ContinuousAt
      (fun s : ℂ => s * deriv Complex.Gammaℝ (s + 2) / Complex.Gammaℝ (s + 2)) 0 :=
    h_num.div hg_shift hg2_ne
  exact h_div.sub continuousAt_const

/-- Main lemma: the residue of `s · Γℝ'(s)/Γℝ(s)` at `s = 0` is `-1`. -/
theorem GammaR_logDeriv_residue_at_zero :
    Filter.Tendsto (fun s : ℂ => s * (deriv Complex.Gammaℝ s / s.Gammaℝ))
      (nhdsWithin 0 {0}ᶜ) (nhds (-1 : ℂ)) := by
  -- Strategy: show the function equals
  --   `s ↦ s · Γℝ'(s+2)/Γℝ(s+2) - 1`
  -- on a neighborhood of 0 (intersected with `{0}ᶜ`), then use continuity.
  have h2 : Complex.Gammaℝ (2 : ℂ) ≠ 0 := Gammaℝ_two_ne_zero
  -- The set `V := {z : Γℝ(z) ≠ 0}` is open and contains 2.
  have hV_open : IsOpen {z : ℂ | z.Gammaℝ ≠ 0} := Gammaℝ_ne_zero_isOpen
  -- Preimage of V under `s ↦ s + 2` is open and contains 0.
  have h_cont_shift : Continuous (fun s : ℂ => s + 2) :=
    continuous_id.add continuous_const
  have hU_open : IsOpen ((fun s : ℂ => s + 2) ⁻¹' {z : ℂ | z.Gammaℝ ≠ 0}) :=
    hV_open.preimage h_cont_shift
  have h0_mem : (0 : ℂ) ∈ (fun s : ℂ => s + 2) ⁻¹' {z : ℂ | z.Gammaℝ ≠ 0} := by
    show Complex.Gammaℝ ((0 : ℂ) + 2) ≠ 0
    simpa using h2
  have hU_nhds : (fun s : ℂ => s + 2) ⁻¹' {z : ℂ | z.Gammaℝ ≠ 0} ∈ 𝓝 (0 : ℂ) :=
    hU_open.mem_nhds h0_mem
  -- The function equals `s · Γℝ'(s+2)/Γℝ(s+2) - 1` on `{0}ᶜ ∩ U`.
  have h_eventuallyEq :
      (fun s : ℂ => s * (deriv Complex.Gammaℝ s / s.Gammaℝ))
        =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun s : ℂ => s * deriv Complex.Gammaℝ (s + 2) / Complex.Gammaℝ (s + 2) - 1) := by
    -- Within `{0}ᶜ`, the neighborhood `U` is in `nhdsWithin 0 {0}ᶜ` too.
    have hU_within : (fun s : ℂ => s + 2) ⁻¹' {z : ℂ | z.Gammaℝ ≠ 0}
        ∈ nhdsWithin (0 : ℂ) {0}ᶜ :=
      mem_nhdsWithin_of_mem_nhds hU_nhds
    have h_self : ({0}ᶜ : Set ℂ) ∈ nhdsWithin (0 : ℂ) {0}ᶜ := self_mem_nhdsWithin
    filter_upwards [hU_within, h_self] with z hzU hz0
    -- For `z ≠ 0` with `Γℝ(z+2) ≠ 0`, we also have `Γℝ(z) ≠ 0` (different proof).
    -- But here we use the differentiated identity directly.
    have hz_ne : z ≠ 0 := hz0
    have hgs2 : Complex.Gammaℝ (z + 2) ≠ 0 := hzU
    -- Need `Γℝ(z) ≠ 0` too. Use `s · Γℝ(s) = 2π · Γℝ(s+2)`: if `Γℝ(z) = 0`, then
    -- `0 = 2π · Γℝ(z+2)`, contradicting `hgs2` (and `2π ≠ 0`).
    have hgs : Complex.Gammaℝ z ≠ 0 := by
      intro hzero
      have hkey := s_mul_Gammaℝ_eq z hz_ne
      rw [hzero, mul_zero] at hkey
      -- 0 = 2 * π * Γℝ(z+2). Since 2π ≠ 0, conclude Γℝ(z+2) = 0.
      have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hpi_ne
      have : Complex.Gammaℝ (z + 2) = 0 := by
        have hkey' : 2 * (Real.pi : ℂ) * Complex.Gammaℝ (z + 2) = 0 := hkey.symm
        rcases mul_eq_zero.mp hkey' with h | h
        · exact (h2pi_ne h).elim
        · exact h
      exact hgs2 this
    -- Differentiated identity: Γℝ(z) + z · Γℝ'(z) = 2π · Γℝ'(z+2).
    have hd := deriv_identity z hz_ne hgs hgs2
    -- Functional eq: z · Γℝ(z) = 2π · Γℝ(z+2), so Γℝ(z) = 2π · Γℝ(z+2) / z.
    have hf := s_mul_Gammaℝ_eq z hz_ne
    -- Now we want: z · (Γℝ'(z) / Γℝ(z)) = z · Γℝ'(z+2)/Γℝ(z+2) - 1.
    -- From `hd`: z · Γℝ'(z) = 2π · Γℝ'(z+2) - Γℝ(z).
    -- So z · Γℝ'(z) / Γℝ(z) = 2π · Γℝ'(z+2) / Γℝ(z) - 1.
    -- And 2π · Γℝ'(z+2) / Γℝ(z) = z · Γℝ'(z+2) / Γℝ(z+2)
    --   since Γℝ(z) = 2π · Γℝ(z+2)/z, i.e., 2π · Γℝ(z+2) = z · Γℝ(z).
    -- Algebraic chase: cross-multiply.
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    field_simp
    -- Goal: `z * deriv Γℝ z * Γℝ(z+2) = (z * deriv Γℝ (z+2) - Γℝ(z+2)) * Γℝ(z)`
    -- (after field_simp normalizes division). Use linear_combination.
    linear_combination Complex.Gammaℝ (z + 2) * hd
      - deriv Complex.Gammaℝ (z + 2) * hf
  -- Use Tendsto.congr' with the eventual equality and continuity at 0.
  have h_aux_cont : ContinuousAt
      (fun s : ℂ => s * deriv Complex.Gammaℝ (s + 2) / Complex.Gammaℝ (s + 2) - 1) 0 :=
    aux_continuousAt
  -- ContinuousAt at 0 gives Tendsto (𝓝 0) (𝓝 (f 0)) where f 0 = 0 - 1 = -1.
  have h_tendsto_aux :
      Filter.Tendsto
        (fun s : ℂ => s * deriv Complex.Gammaℝ (s + 2) / Complex.Gammaℝ (s + 2) - 1)
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (-1 : ℂ)) := by
    have hcont : Filter.Tendsto
        (fun s : ℂ => s * deriv Complex.Gammaℝ (s + 2) / Complex.Gammaℝ (s + 2) - 1)
        (𝓝 (0 : ℂ)) (𝓝 (-1 : ℂ)) := by
      have h0 := h_aux_cont
      have h_eq : (0 : ℂ) * deriv Complex.Gammaℝ ((0 : ℂ) + 2)
          / Complex.Gammaℝ ((0 : ℂ) + 2) - 1 = (-1 : ℂ) := by simp
      rw [ContinuousAt] at h0
      simpa [h_eq] using h0
    exact hcont.mono_left nhdsWithin_le_nhds
  exact h_tendsto_aux.congr' h_eventuallyEq.symm

/-! ### Residue of `Γℝ'(1-s)/Γℝ(1-s)` at `s = 1`

Substitute `u = 1 - s`. As `s → 1` in `{1}ᶜ`, `u → 0` in `{0}ᶜ`, and
`(s - 1) = -u`, so `(s-1) · Γℝ'(1-s)/Γℝ(1-s) = -(u · Γℝ'(u)/Γℝ(u)) → -(-1) = 1`.
-/

/-- The map `s ↦ 1 - s` sends `nhdsWithin 1 {1}ᶜ` to `nhdsWithin 0 {0}ᶜ`. -/
private lemma tendsto_one_sub_within :
    Filter.Tendsto (fun s : ℂ => 1 - s)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhdsWithin (0 : ℂ) {0}ᶜ) := by
  have h_cont : Filter.Tendsto (fun s : ℂ => 1 - s) (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hc : Continuous (fun s : ℂ => 1 - s) := continuous_const.sub continuous_id
    have h := hc.continuousAt (x := (1 : ℂ))
    simpa [ContinuousAt] using h
  have h_within : Filter.Tendsto (fun s : ℂ => 1 - s)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (𝓝 (0 : ℂ)) := h_cont.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_within
  -- Eventually, for s ∈ {1}ᶜ, we have 1 - s ∈ {0}ᶜ
  have h_self : ({1}ᶜ : Set ℂ) ∈ nhdsWithin (1 : ℂ) {1}ᶜ := self_mem_nhdsWithin
  filter_upwards [h_self] with s hs
  -- hs : s ∈ {1}ᶜ, i.e., s ≠ 1.  Show 1 - s ≠ 0.
  intro h0
  -- h0 : 1 - s ∈ {0}, i.e., 1 - s = 0
  apply hs
  have hs_eq : s = 1 := by
    have : (1 : ℂ) - s = 0 := h0
    linear_combination -this
  exact hs_eq

/-- Main lemma: residue of `Γℝ'(1-s)/Γℝ(1-s)` at `s = 1` is `+1`. -/
theorem GammaR_logDeriv_at_one_sub_residue_at_one :
    Filter.Tendsto
      (fun s : ℂ => (s - 1) * (deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ))
      (nhdsWithin 1 {1}ᶜ) (nhds (1 : ℂ)) := by
  -- Compose with `s ↦ 1 - s`: pulls back the s=0 residue.
  have h_base := GammaR_logDeriv_residue_at_zero
  -- h_base : Tendsto (fun u => u * (Γℝ'(u)/Γℝ(u))) (nhdsWithin 0 {0}ᶜ) (𝓝 (-1))
  have h_comp :
      Filter.Tendsto
        ((fun u : ℂ => u * (deriv Complex.Gammaℝ u / u.Gammaℝ)) ∘
          (fun s : ℂ => 1 - s))
        (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (-1 : ℂ)) :=
    h_base.comp tendsto_one_sub_within
  -- The composed function is `s ↦ (1 - s) * (Γℝ'(1-s) / Γℝ(1-s))`.
  -- We want `s ↦ (s - 1) * (Γℝ'(1-s) / Γℝ(1-s))`, which is the negation.
  -- So multiply by -1: tendsto to (-1) * (-1) = 1.
  have h_neg : Filter.Tendsto
      (fun s : ℂ => (-1 : ℂ) *
        ((fun u : ℂ => u * (deriv Complex.Gammaℝ u / u.Gammaℝ)) ((fun s : ℂ => 1 - s) s)))
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds ((-1 : ℂ) * (-1 : ℂ))) :=
    (tendsto_const_nhds).mul h_comp
  have h_simp : ((-1 : ℂ) * (-1 : ℂ)) = (1 : ℂ) := by ring
  rw [h_simp] at h_neg
  -- Show pointwise the two functions agree.
  apply h_neg.congr
  intro s
  show (-1 : ℂ) * ((1 - s) * (deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ))
       = (s - 1) * (deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ)
  ring

/-! ### The arch kernel and its residues at 0 and 1 -/

/-- The full archimedean kernel. -/
noncomputable def archKernel (s : ℂ) : ℂ :=
  deriv Complex.Gammaℝ s / s.Gammaℝ +
  deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ

theorem archKernel_residue_at_zero :
    Filter.Tendsto (fun s : ℂ => s * archKernel s)
      (nhdsWithin 0 {0}ᶜ) (nhds (-1 : ℂ)) := by
  -- Split: s · K(s) = s · Γℝ'(s)/Γℝ(s) + s · Γℝ'(1-s)/Γℝ(1-s).
  -- First term → -1; second term has factor `s → 0` and a continuous quotient at s=0
  -- (since Γℝ(1) = 1 ≠ 0), so → 0. Sum → -1.
  have h1 : Filter.Tendsto (fun s : ℂ => s * (deriv Complex.Gammaℝ s / s.Gammaℝ))
      (nhdsWithin 0 {0}ᶜ) (nhds (-1 : ℂ)) :=
    GammaR_logDeriv_residue_at_zero
  -- `Γℝ(1) ≠ 0` since `Re 1 = 1 > 0`.
  have hg1 : Complex.Gammaℝ (1 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have h1mem : (1 : ℂ) ∈ {z : ℂ | z.Gammaℝ ≠ 0} := hg1
  -- Continuity of the second-term quotient at s = 0.
  have hg_cont1 : ContinuousAt Complex.Gammaℝ 1 :=
    (Gammaℝ_analyticOnNhd _ h1mem).continuousAt
  have hd_cont1 : ContinuousAt (deriv Complex.Gammaℝ) 1 :=
    (deriv_Gammaℝ_analyticOnNhd _ h1mem).continuousAt
  have hshift : ContinuousAt (fun s : ℂ => 1 - s) 0 :=
    (continuous_const.sub continuous_id).continuousAt
  have hshift_val : (fun s : ℂ => 1 - s) 0 = 1 := by simp
  have hd_shift : ContinuousAt (fun s : ℂ => deriv Complex.Gammaℝ (1 - s)) 0 := by
    exact ContinuousAt.comp (g := deriv Complex.Gammaℝ) (f := fun s : ℂ => 1 - s)
      (by rw [hshift_val]; exact hd_cont1) hshift
  have hg_shift : ContinuousAt (fun s : ℂ => Complex.Gammaℝ (1 - s)) 0 := by
    exact ContinuousAt.comp (g := Complex.Gammaℝ) (f := fun s : ℂ => 1 - s)
      (by rw [hshift_val]; exact hg_cont1) hshift
  have hg_shift_ne : Complex.Gammaℝ ((fun s : ℂ => 1 - s) 0) ≠ 0 := by
    rw [hshift_val]; exact hg1
  have h_quot : ContinuousAt
      (fun s : ℂ => deriv Complex.Gammaℝ (1 - s) / Complex.Gammaℝ (1 - s)) 0 :=
    hd_shift.div hg_shift hg_shift_ne
  -- Second term: s ↦ s · (Γℝ'(1-s)/Γℝ(1-s)) is continuous at 0 with value 0.
  have h_id : ContinuousAt (fun s : ℂ => s) 0 := continuous_id.continuousAt
  have h2_at_zero : ContinuousAt
      (fun s : ℂ => s * (deriv Complex.Gammaℝ (1 - s) / Complex.Gammaℝ (1 - s))) 0 :=
    h_id.mul h_quot
  have h2_val : ((0 : ℂ) * (deriv Complex.Gammaℝ (1 - (0 : ℂ)) /
      Complex.Gammaℝ (1 - (0 : ℂ)))) = (0 : ℂ) := by simp
  have h2_tendsto :
      Filter.Tendsto
        (fun s : ℂ => s * (deriv Complex.Gammaℝ (1 - s) / Complex.Gammaℝ (1 - s)))
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (0 : ℂ)) := by
    have h_full : Filter.Tendsto
        (fun s : ℂ => s * (deriv Complex.Gammaℝ (1 - s) / Complex.Gammaℝ (1 - s)))
        (𝓝 (0 : ℂ)) (nhds (0 : ℂ)) := by
      have := h2_at_zero
      rw [ContinuousAt] at this
      simpa [h2_val] using this
    exact h_full.mono_left nhdsWithin_le_nhds
  -- Sum: → -1 + 0 = -1.
  have h_sum := h1.add h2_tendsto
  have h_target : (-1 : ℂ) + (0 : ℂ) = (-1 : ℂ) := by ring
  rw [h_target] at h_sum
  -- Match shapes:  s * K(s) = s * (term1) + s * (term2)
  apply h_sum.congr
  intro s
  show s * (deriv Complex.Gammaℝ s / s.Gammaℝ)
       + s * (deriv Complex.Gammaℝ (1 - s) / Complex.Gammaℝ (1 - s))
       = s * archKernel s
  unfold archKernel
  ring

theorem archKernel_residue_at_one :
    Filter.Tendsto (fun s : ℂ => (s - 1) * archKernel s)
      (nhdsWithin 1 {1}ᶜ) (nhds (1 : ℂ)) := by
  -- Split: (s-1) · K(s) = (s-1) · Γℝ'(s)/Γℝ(s) + (s-1) · Γℝ'(1-s)/Γℝ(1-s).
  -- First term: Γℝ'(s)/Γℝ(s) is continuous at s=1 (since Γℝ(1) ≠ 0), and (s-1) → 0.
  -- Second term: residue from Target 1 → +1.  Sum → 0 + 1 = 1.
  have hg1 : Complex.Gammaℝ (1 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have h1mem : (1 : ℂ) ∈ {z : ℂ | z.Gammaℝ ≠ 0} := hg1
  have hg_cont1 : ContinuousAt Complex.Gammaℝ 1 :=
    (Gammaℝ_analyticOnNhd _ h1mem).continuousAt
  have hd_cont1 : ContinuousAt (deriv Complex.Gammaℝ) 1 :=
    (deriv_Gammaℝ_analyticOnNhd _ h1mem).continuousAt
  have h_quot1 : ContinuousAt
      (fun s : ℂ => deriv Complex.Gammaℝ s / Complex.Gammaℝ s) 1 :=
    hd_cont1.div hg_cont1 hg1
  have h_sub_id : ContinuousAt (fun s : ℂ => s - 1) 1 :=
    (continuous_id.sub continuous_const).continuousAt
  -- (s - 1) * Γℝ'(s)/Γℝ(s) is continuous at 1 with value 0.
  have h1_at_one : ContinuousAt
      (fun s : ℂ => (s - 1) * (deriv Complex.Gammaℝ s / Complex.Gammaℝ s)) 1 :=
    h_sub_id.mul h_quot1
  have h1_val :
      ((1 : ℂ) - 1) * (deriv Complex.Gammaℝ (1 : ℂ) / Complex.Gammaℝ (1 : ℂ)) = 0 := by
    simp
  have h1_tendsto :
      Filter.Tendsto
        (fun s : ℂ => (s - 1) * (deriv Complex.Gammaℝ s / Complex.Gammaℝ s))
        (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (0 : ℂ)) := by
    have h_full : Filter.Tendsto
        (fun s : ℂ => (s - 1) * (deriv Complex.Gammaℝ s / Complex.Gammaℝ s))
        (𝓝 (1 : ℂ)) (nhds (0 : ℂ)) := by
      have := h1_at_one
      rw [ContinuousAt] at this
      simpa [h1_val] using this
    exact h_full.mono_left nhdsWithin_le_nhds
  -- Second term: residue from Target 1.
  have h2_tendsto :
      Filter.Tendsto
        (fun s : ℂ => (s - 1) * (deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ))
        (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (1 : ℂ)) :=
    GammaR_logDeriv_at_one_sub_residue_at_one
  -- Sum: → 0 + 1 = 1.
  have h_sum := h1_tendsto.add h2_tendsto
  have h_target : (0 : ℂ) + (1 : ℂ) = (1 : ℂ) := by ring
  rw [h_target] at h_sum
  apply h_sum.congr
  intro s
  show (s - 1) * (deriv Complex.Gammaℝ s / Complex.Gammaℝ s)
       + (s - 1) * (deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ)
       = (s - 1) * archKernel s
  unfold archKernel
  ring

end ZD.WeilArchKernelResidues

/-- Top-level alias matching the original spec name. -/
theorem GammaR_logDeriv_residue_at_zero :
    Filter.Tendsto (fun s : ℂ => s * (deriv Complex.Gammaℝ s / s.Gammaℝ))
      (nhdsWithin 0 {0}ᶜ) (nhds (-1 : ℂ)) :=
  ZD.WeilArchKernelResidues.GammaR_logDeriv_residue_at_zero

-- Axiom checks
#print axioms GammaR_logDeriv_residue_at_zero
#print axioms ZD.WeilArchKernelResidues.GammaR_logDeriv_at_one_sub_residue_at_one
#print axioms ZD.WeilArchKernelResidues.archKernel_residue_at_zero
#print axioms ZD.WeilArchKernelResidues.archKernel_residue_at_one
