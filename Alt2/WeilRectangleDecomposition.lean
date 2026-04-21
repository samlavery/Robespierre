import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilRectangleZeros

/-!
# Weil integrand Laurent decomposition — residue-form at simple zeros

This file converts the cycle-28 local Laurent form
`weilIntegrand h s = -h(s)/(s - ρ) + φ(s)` (with `h(s)` on path, not `h(ρ)`)
into the **residue form**
`weilIntegrand h s = -h(ρ)/(s - ρ) + ψ(s)`
matching the signature expected by
`ZD.WeilPositivity.Contour.rectResidueTheorem_multi_pole_unconditional`.

## Key lemma

* `weilIntegrand_residue_form_at_simple_zero` — at a simple zero `ρ` of `ζ` with
  `h` analytic at `ρ`, the Weil integrand has Laurent expansion
  `-h(ρ)/(s−ρ) + ψ(s)` with `ψ` analytic at `ρ`. Residue is `-h(ρ)`.

The transformation from `-h(s)/(s-ρ)` (cycle 28) to `-h(ρ)/(s-ρ)` uses that
`(h(s) - h(ρ))/(s - ρ)` extends analytically at `ρ` (standard first-order
Taylor remainder), via Mathlib's analytic-order factorization
`natCast_le_analyticOrderAt`.

No new axioms.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Analytic extension of `(h(s) - h(ρ))/(s - ρ)` at `ρ`.**
If `h` is analytic at `ρ`, then the difference quotient extends analytically. -/
theorem diff_quotient_analyticAt {h : ℂ → ℂ} {ρ : ℂ} (hh : AnalyticAt ℂ h ρ) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, (h s - h ρ) / (s - ρ) = q s := by
  -- Let g(s) = h s - h ρ; g analytic at ρ, g ρ = 0.
  have hg_an : AnalyticAt ℂ (fun s => h s - h ρ) ρ := hh.sub analyticAt_const
  have hg_zero : (fun s => h s - h ρ) ρ = 0 := by simp
  -- analyticOrderAt g ρ ≥ 1 since g(ρ) = 0.
  have h_order_ge_one : (1 : ℕ∞) ≤ analyticOrderAt (fun s => h s - h ρ) ρ := by
    rw [ENat.one_le_iff_ne_zero]
    intro h_zero_order
    rw [hg_an.analyticOrderAt_eq_zero] at h_zero_order
    exact h_zero_order hg_zero
  -- Factor: g s = (s - ρ)^1 • q s for some analytic q.
  obtain ⟨q, hq_an, hq_eq⟩ :=
    ((natCast_le_analyticOrderAt hg_an).mp h_order_ge_one)
  refine ⟨q, hq_an, ?_⟩
  -- On punctured nhd, (s - ρ) ≠ 0, so we can divide.
  have hq_eq_nhds : (fun s => h s - h ρ) =ᶠ[nhds ρ] (fun s => (s - ρ) ^ 1 • q s) := hq_eq
  have hq_eq_punct : ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, h s - h ρ = (s - ρ) * q s := by
    have h_mono : (fun s : ℂ => h s - h ρ) =ᶠ[nhdsWithin ρ {ρ}ᶜ]
        (fun s => (s - ρ) ^ 1 • q s) :=
      hq_eq_nhds.filter_mono (nhdsWithin_le_nhds)
    filter_upwards [h_mono] with s hs
    simp only [pow_one, smul_eq_mul] at hs
    exact hs
  have h_sub_ne : ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, s - ρ ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_ne_zero_of_ne hs
  filter_upwards [hq_eq_punct, h_sub_ne] with s hs hne
  rw [hs]
  field_simp

/-- **Residue form at simple zero.** At a simple zero `ρ` of `ζ`, the Weil integrand
has Laurent expansion `-h(ρ)/(s−ρ) + ψ(s)` with `ψ` analytic at `ρ`. This is the
form expected by the multi-pole residue theorem: residue coefficient is `-h(ρ)`. -/
theorem weilIntegrand_residue_form_at_simple_zero
    {h : ℂ → ℂ} {ρ : ℂ}
    (hζ_an : AnalyticAt ℂ riemannZeta ρ)
    (hζ_zero : riemannZeta ρ = 0) (hζ_deriv : deriv riemannZeta ρ ≠ 0)
    (hh_an : AnalyticAt ℂ h ρ) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilIntegrand h s = -h ρ / (s - ρ) + ψ s := by
  -- Cycle 28: weilIntegrand h s = -h(s)/(s - ρ) + φ(s).
  obtain ⟨φ, hφ_an, hφ_eq⟩ :=
    weilIntegrand_leading_coefficient_at_zero hζ_an hζ_zero hζ_deriv hh_an
  -- Difference quotient extension: (h s - h ρ)/(s - ρ) = q s, q analytic at ρ.
  obtain ⟨q, hq_an, hq_eq⟩ := diff_quotient_analyticAt hh_an
  -- Build ψ = φ - q.
  refine ⟨fun s => φ s - q s, hφ_an.sub hq_an, ?_⟩
  -- -h(s)/(s - ρ) = -h(ρ)/(s - ρ) - (h(s) - h(ρ))/(s - ρ) = -h(ρ)/(s-ρ) - q(s)
  filter_upwards [hφ_eq, hq_eq, self_mem_nhdsWithin] with s hs hq_s hs_mem
  have hs_ne : s ≠ ρ := hs_mem
  have hsub_ne : s - ρ ≠ 0 := sub_ne_zero_of_ne hs_ne
  rw [hs]
  have h_split : -h s / (s - ρ) = -h ρ / (s - ρ) - (h s - h ρ) / (s - ρ) := by
    field_simp
    ring
  rw [h_split, hq_s]
  ring

#print axioms diff_quotient_analyticAt
#print axioms weilIntegrand_residue_form_at_simple_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Global multi-pole decomposition on an open set
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Per-zero residue-form ψ, packaged as `Classical.choose`.** For each simple
zero `ρ` of `ζ` with `h` analytic at `ρ`, selects a canonical analytic witness
`psiOf h ρ` that realizes the residue Laurent form. -/
noncomputable def psiOf (h : ℂ → ℂ) (ρ : ℂ)
    (hζ_an : AnalyticAt ℂ riemannZeta ρ) (hζ_zero : riemannZeta ρ = 0)
    (hζ_deriv : deriv riemannZeta ρ ≠ 0) (hh_an : AnalyticAt ℂ h ρ) : ℂ → ℂ :=
  Classical.choose (weilIntegrand_residue_form_at_simple_zero hζ_an hζ_zero hζ_deriv hh_an)

private lemma psiOf_spec (h : ℂ → ℂ) (ρ : ℂ)
    (hζ_an : AnalyticAt ℂ riemannZeta ρ) (hζ_zero : riemannZeta ρ = 0)
    (hζ_deriv : deriv riemannZeta ρ ≠ 0) (hh_an : AnalyticAt ℂ h ρ) :
    AnalyticAt ℂ (psiOf h ρ hζ_an hζ_zero hζ_deriv hh_an) ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilIntegrand h s =
          -h ρ / (s - ρ) + psiOf h ρ hζ_an hζ_zero hζ_deriv hh_an s :=
  Classical.choose_spec
    (weilIntegrand_residue_form_at_simple_zero hζ_an hζ_zero hζ_deriv hh_an)

/-- **Hypothesis bundle for the multi-pole decomposition.**
Given a finset of candidate poles `Z`, each is a simple zero of `ζ` and `h` is
analytic there. -/
structure SimpleZeroBundle (h : ℂ → ℂ) (Z : Finset ℂ) : Prop where
  ζ_an : ∀ ρ ∈ Z, AnalyticAt ℂ riemannZeta ρ
  ζ_zero : ∀ ρ ∈ Z, riemannZeta ρ = 0
  ζ_deriv : ∀ ρ ∈ Z, deriv riemannZeta ρ ≠ 0
  h_an : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ

/-- **Naive decomposition function.** On the complement of `Z`, this equals the
Weil integrand plus the sum of regularizing polar parts. At points of `Z` it is
temporarily defined by the same formula (with a singular term), to be repaired
via `Function.update` or by `AnalyticAt.congr_of_eventuallyEq` locally. -/
noncomputable def weilNaiveRemainder (h : ℂ → ℂ) (Z : Finset ℂ) (s : ℂ) : ℂ :=
  weilIntegrand h s + ∑ ρ ∈ Z, h ρ / (s - ρ)

/-- **Off-pole analyticity.** At `s ∉ Z ∪ {1}`, `weilNaiveRemainder h Z s` is
analytic whenever `h` is analytic at `s` and `ζ s ≠ 0`. -/
theorem weilNaiveRemainder_analyticAt_off_poles
    {h : ℂ → ℂ} {Z : Finset ℂ} {s : ℂ}
    (hs_not_one : s ≠ 1) (hs_not_Z : s ∉ Z) (hζ_ne : riemannZeta s ≠ 0)
    (hh : AnalyticAt ℂ h s) :
    AnalyticAt ℂ (weilNaiveRemainder h Z) s := by
  -- weilIntegrand analytic at s (from cycle 26).
  have hw_diff : DifferentiableAt ℂ (weilIntegrand h) s :=
    weilIntegrand_differentiableAt hs_not_one hζ_ne hh.differentiableAt
  have hw_an : AnalyticAt ℂ (weilIntegrand h) s := by
    -- Rewrap: weilIntegrand is analytic at s, not just differentiable.
    unfold weilIntegrand
    have hζ_an : AnalyticAt ℂ riemannZeta s := by
      have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
      have hζ_diff_on : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
        fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
      exact hζ_diff_on.analyticOnNhd hopen s hs_not_one
    have hζ_deriv_an : AnalyticAt ℂ (deriv riemannZeta) s := hζ_an.deriv
    exact (hζ_deriv_an.neg.div hζ_an hζ_ne).mul hh
  -- Each polar part h(ρ)/(s - ρ) is analytic at s (since s ≠ ρ).
  have hpolar_an : ∀ ρ ∈ Z, AnalyticAt ℂ (fun t => h ρ / (t - ρ)) s := by
    intro ρ hρ
    have hs_ne_ρ : s ≠ ρ := fun h => hs_not_Z (h ▸ hρ)
    have h_sub_ne : s - ρ ≠ 0 := sub_ne_zero_of_ne hs_ne_ρ
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) h_sub_ne
  -- Sum of analytic functions is analytic.
  have hsum_an : AnalyticAt ℂ (fun t => ∑ ρ ∈ Z, h ρ / (t - ρ)) s := by
    have := Finset.analyticAt_sum Z hpolar_an
    -- Convert ∑ n, fun n => ... to fun t, ∑ n, ...
    convert this using 1
    funext t
    simp [Finset.sum_apply]
  unfold weilNaiveRemainder
  exact hw_an.add hsum_an

/-- **At a zero `ρ ∈ Z`, `weilNaiveRemainder` has a removable singularity.**
The local formula is `ψ_ρ(s) + Σ_{ρ' ≠ ρ} h(ρ')/(s - ρ')`, both terms analytic
at `ρ`. We extract the analytic extension value and prove equality on a
punctured neighbourhood. -/
theorem weilNaiveRemainder_removable_at_zero
    {h : ℂ → ℂ} {Z : Finset ℂ} {ρ : ℂ}
    (hρ : ρ ∈ Z) (hρ_ne_one : ρ ≠ 1)
    (hB : SimpleZeroBundle h Z)
    (hh_analyticOn_Z : ∀ ρ' ∈ Z, AnalyticAt ℂ h ρ') :
    ∃ g_ext : ℂ → ℂ, AnalyticAt ℂ g_ext ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, weilNaiveRemainder h Z s = g_ext s := by
  -- ψ_ρ: local analytic witness at ρ.
  set ψ := psiOf h ρ (hB.ζ_an ρ hρ) (hB.ζ_zero ρ hρ) (hB.ζ_deriv ρ hρ) (hB.h_an ρ hρ)
    with hψ_def
  have hψ_spec := psiOf_spec h ρ (hB.ζ_an ρ hρ) (hB.ζ_zero ρ hρ) (hB.ζ_deriv ρ hρ) (hB.h_an ρ hρ)
  -- Remainder sum: Σ_{ρ' ≠ ρ, ρ' ∈ Z} h(ρ')/(s - ρ').
  set Z' := Z.erase ρ with hZ'_def
  set remainderSum : ℂ → ℂ := fun s => ∑ ρ' ∈ Z', h ρ' / (s - ρ') with hrs_def
  -- remainderSum is analytic at ρ since each term is (ρ ≠ ρ' for ρ' ∈ Z').
  have hrs_an : AnalyticAt ℂ remainderSum ρ := by
    have hterm_an : ∀ ρ' ∈ Z', AnalyticAt ℂ (fun t => h ρ' / (t - ρ')) ρ := by
      intro ρ' hρ'
      have hmem : ρ' ≠ ρ ∧ ρ' ∈ Z := Finset.mem_erase.mp hρ'
      have hne : ρ ≠ ρ' := fun heq => hmem.1 heq.symm
      have h_sub_ne : ρ - ρ' ≠ 0 := sub_ne_zero_of_ne hne
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) h_sub_ne
    have := Finset.analyticAt_sum Z' hterm_an
    convert this using 1
    funext t
    rw [hrs_def]
    simp [Finset.sum_apply]
  -- Candidate extension: g_ext s = ψ(s) + remainderSum(s).
  refine ⟨fun s => ψ s + remainderSum s, hψ_spec.1.add hrs_an, ?_⟩
  -- On punctured nhd of ρ: weilNaiveRemainder = weilIntegrand + Σ_{ρ' ∈ Z} ...
  -- By hψ_spec.2, weilIntegrand = -h(ρ)/(s-ρ) + ψ s on punctured nhd.
  -- Splitting the sum: Σ_{ρ' ∈ Z} = h(ρ)/(s-ρ) + Σ_{ρ' ∈ Z'}.
  filter_upwards [hψ_spec.2, self_mem_nhdsWithin] with s hs_eq hs_mem
  have hs_ne_ρ : s ≠ ρ := hs_mem
  have hsub_ne : s - ρ ≠ 0 := sub_ne_zero_of_ne hs_ne_ρ
  have hsum_split : (∑ ρ' ∈ Z, h ρ' / (s - ρ')) = h ρ / (s - ρ) + remainderSum s := by
    rw [hrs_def]
    rw [show Z = insert ρ Z' from (Finset.insert_erase hρ).symm]
    rw [Finset.sum_insert (fun h => ((Finset.mem_erase).mp h).1 rfl)]
  unfold weilNaiveRemainder
  rw [hsum_split, hs_eq]
  ring

#print axioms weilNaiveRemainder_analyticAt_off_poles
#print axioms weilNaiveRemainder_removable_at_zero

/-- **Isolated-point property for a Finset in ℂ (T2).** For each `ρ ∈ Z`, there's a
neighbourhood of `ρ` whose only element of `Z` is `ρ` itself. -/
theorem finset_isolated_nhds {Z : Finset ℂ} {ρ : ℂ} (hρ : ρ ∈ Z) :
    ∀ᶠ s in nhds ρ, s ∈ Z → s = ρ := by
  have h_not_mem : ρ ∉ Z.erase ρ := Finset.notMem_erase ρ Z
  obtain ⟨U, V, hU_open, _hV_open, hρ_U, hZ_V, hUV⟩ :=
    SeparatedNhds.of_singleton_finset h_not_mem
  have hρ_U' : ρ ∈ U := hρ_U rfl
  have hU_nhds : U ∈ nhds ρ := hU_open.mem_nhds hρ_U'
  filter_upwards [hU_nhds] with s hs_U hs_Z
  by_contra hne
  have hs_in_erase : s ∈ Z.erase ρ := Finset.mem_erase.mpr ⟨hne, hs_Z⟩
  have hs_V : s ∈ V := hZ_V hs_in_erase
  exact Set.disjoint_iff.mp hUV ⟨hs_U, hs_V⟩

/-- **Canonical choice of analytic extension at each zero**, packaged via
`Classical.choose` on `weilNaiveRemainder_removable_at_zero`. Used uniformly
for both the definition of `weilRemainderGlobal` and its analyticity proof. -/
noncomputable def chooseG (h : ℂ → ℂ) (Z : Finset ℂ) (hB : SimpleZeroBundle h Z)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1) (ρ : ℂ) (hρ : ρ ∈ Z) : ℂ → ℂ :=
  Classical.choose (weilNaiveRemainder_removable_at_zero
    (h := h) (Z := Z) (ρ := ρ) hρ (hZ_ne_one ρ hρ) hB (fun ρ' hρ' => hB.h_an ρ' hρ'))

private lemma chooseG_spec (h : ℂ → ℂ) (Z : Finset ℂ) (hB : SimpleZeroBundle h Z)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1) (ρ : ℂ) (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (chooseG h Z hB hZ_ne_one ρ hρ) ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilNaiveRemainder h Z s = chooseG h Z hB hZ_ne_one ρ hρ s :=
  Classical.choose_spec (weilNaiveRemainder_removable_at_zero
    (h := h) (Z := Z) (ρ := ρ) hρ (hZ_ne_one ρ hρ) hB (fun ρ' hρ' => hB.h_an ρ' hρ'))

/-- **Globally defined Weil remainder** `weilRemainderGlobal h Z hB hZne1`,
piecewise: value of `chooseG` at `ρ` if `s = ρ ∈ Z`, else `weilNaiveRemainder`. -/
noncomputable def weilRemainderGlobal (h : ℂ → ℂ) (Z : Finset ℂ)
    (hB : SimpleZeroBundle h Z) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1) : ℂ → ℂ := fun s =>
  if hs : s ∈ Z then chooseG h Z hB hZ_ne_one s hs s
  else weilNaiveRemainder h Z s

/-- Global `g` equals naive formula off `Z`. -/
theorem weilRemainderGlobal_off_Z {h : ℂ → ℂ} {Z : Finset ℂ}
    (hB : SimpleZeroBundle h Z) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {s : ℂ} (hs : s ∉ Z) :
    weilRemainderGlobal h Z hB hZ_ne_one s = weilNaiveRemainder h Z s := by
  unfold weilRemainderGlobal; simp [hs]

/-- Global `g` equals `chooseG ρ ρ` at `s = ρ ∈ Z`. -/
theorem weilRemainderGlobal_at_Z {h : ℂ → ℂ} {Z : Finset ℂ}
    (hB : SimpleZeroBundle h Z) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    weilRemainderGlobal h Z hB hZ_ne_one ρ = chooseG h Z hB hZ_ne_one ρ hρ ρ := by
  unfold weilRemainderGlobal; simp [hρ]

/-- **Global `g` is analytic at each zero of `Z`.** -/
theorem weilRemainderGlobal_analyticAt_zero {h : ℂ → ℂ} {Z : Finset ℂ}
    (hB : SimpleZeroBundle h Z)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (weilRemainderGlobal h Z hB hZ_ne_one) ρ := by
  -- g_ρ = chooseG ... ρ hρ : analytic at ρ, equals weilNaiveRemainder on punctured nhd.
  set g_ρ := chooseG h Z hB hZ_ne_one ρ hρ with hg_ρ_def
  have hg_ρ_an : AnalyticAt ℂ g_ρ ρ := (chooseG_spec h Z hB hZ_ne_one ρ hρ).1
  have hg_ρ_eq : ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
      weilNaiveRemainder h Z s = g_ρ s :=
    (chooseG_spec h Z hB hZ_ne_one ρ hρ).2
  -- Show weilRemainderGlobal =ᶠ[nhds ρ] g_ρ
  suffices hnhds : weilRemainderGlobal h Z hB hZ_ne_one =ᶠ[nhds ρ] g_ρ by
    exact hg_ρ_an.congr hnhds.symm
  -- On nhd ρ, isolated-point property + lifted punctured equality.
  have h_iso := finset_isolated_nhds hρ
  -- Lift hg_ρ_eq from nhdsWithin to nhds ρ via mem_nhdsWithin.
  have hg_ρ_eq_nhds : ∀ᶠ s in nhds ρ, s ≠ ρ → weilNaiveRemainder h Z s = g_ρ s := by
    rw [Filter.eventually_iff_exists_mem]
    have hmem := hg_ρ_eq
    rw [Filter.eventually_iff, mem_nhdsWithin] at hmem
    obtain ⟨U, hU_open, hρ_U, hU_sub⟩ := hmem
    refine ⟨U, hU_open.mem_nhds hρ_U, fun s hs hne => ?_⟩
    exact hU_sub ⟨hs, hne⟩
  filter_upwards [h_iso, hg_ρ_eq_nhds] with s hs_iso hs_punct_eq
  by_cases hsZ : s ∈ Z
  · -- s ∈ Z → s = ρ
    have hs_eq_ρ : s = ρ := hs_iso hsZ
    subst hs_eq_ρ
    exact weilRemainderGlobal_at_Z hB hZ_ne_one hρ
  · -- s ∉ Z → s ≠ ρ → weilRemainderGlobal = weilNaiveRemainder = g_ρ
    rw [weilRemainderGlobal_off_Z hB hZ_ne_one hsZ]
    have hs_ne_ρ : s ≠ ρ := fun heq => hsZ (heq ▸ hρ)
    exact hs_punct_eq hs_ne_ρ

#print axioms finset_isolated_nhds
#print axioms chooseG
#print axioms weilRemainderGlobal
#print axioms weilRemainderGlobal_off_Z
#print axioms weilRemainderGlobal_at_Z
#print axioms weilRemainderGlobal_analyticAt_zero

/-- **Global `g` is analytic at every off-pole point.** At `s ∉ Z ∪ {1}` with
`ζ s ≠ 0`, `weilRemainderGlobal = weilNaiveRemainder` in a neighbourhood (since
`Z` is isolated), and `weilNaiveRemainder` is analytic there. -/
theorem weilRemainderGlobal_analyticAt_off_poles
    {h : ℂ → ℂ} {Z : Finset ℂ}
    (hB : SimpleZeroBundle h Z)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {s : ℂ} (hs_not_one : s ≠ 1) (hs_not_Z : s ∉ Z)
    (hζ_ne : riemannZeta s ≠ 0) (hh : AnalyticAt ℂ h s) :
    AnalyticAt ℂ (weilRemainderGlobal h Z hB hZ_ne_one) s := by
  -- Eventually in nhd of s, s' ∉ Z (since Z is a finite set, closed in T2).
  have h_Z_closed : IsClosed (↑Z : Set ℂ) := Z.finite_toSet.isClosed
  have h_notZ_open : IsOpen ((↑Z : Set ℂ)ᶜ) := h_Z_closed.isOpen_compl
  have h_s_in_notZ : s ∈ (↑Z : Set ℂ)ᶜ := hs_not_Z
  have h_notZ_nhds : (↑Z : Set ℂ)ᶜ ∈ nhds s := h_notZ_open.mem_nhds h_s_in_notZ
  have h_eventual_notZ : ∀ᶠ s' in nhds s, s' ∉ Z := h_notZ_nhds
  -- weilRemainderGlobal = weilNaiveRemainder eventually near s.
  have h_eq : weilRemainderGlobal h Z hB hZ_ne_one =ᶠ[nhds s] weilNaiveRemainder h Z := by
    filter_upwards [h_eventual_notZ] with s' hs'
    exact weilRemainderGlobal_off_Z hB hZ_ne_one hs'
  have h_naive_an : AnalyticAt ℂ (weilNaiveRemainder h Z) s :=
    weilNaiveRemainder_analyticAt_off_poles hs_not_one hs_not_Z hζ_ne hh
  exact h_naive_an.congr h_eq.symm

#print axioms weilRemainderGlobal_analyticAt_off_poles

/-- **Decomposition equation off `Z`.** For `s ∉ Z`,
`weilIntegrand h s = Σ (-h(ρ))/(s-ρ) + weilRemainderGlobal(s)`. -/
theorem weilIntegrand_eq_polar_plus_global
    {h : ℂ → ℂ} {Z : Finset ℂ}
    (hB : SimpleZeroBundle h Z)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {s : ℂ} (hs_not_Z : s ∉ Z) :
    weilIntegrand h s = (∑ ρ ∈ Z, (-h ρ) / (s - ρ)) +
      weilRemainderGlobal h Z hB hZ_ne_one s := by
  rw [weilRemainderGlobal_off_Z hB hZ_ne_one hs_not_Z]
  unfold weilNaiveRemainder
  have hsum_cancel : (∑ ρ ∈ Z, (-h ρ) / (s - ρ)) + (∑ ρ ∈ Z, h ρ / (s - ρ)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro ρ _
    ring
  linear_combination -hsum_cancel

#print axioms weilIntegrand_eq_polar_plus_global

-- ═══════════════════════════════════════════════════════════════════════════
-- § Global `g` differentiable on closed rectangle (critical-strip case)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`weilRemainderGlobal` is `DifferentiableOn` a closed rectangle** in the
critical strip. Hypotheses:

* `Z` contains exactly the zeros of `ζ` in the closed rectangle (so off-`Z`
  points have `ζ ≠ 0`).
* `h` is analytic on the closed rectangle.
* The rectangle avoids `s = 1` (ensured by `σR < 1` via the critical strip
  hypothesis).

Concludes that `g := weilRemainderGlobal h Z hB hZne1` is `DifferentiableOn`
the full closed rectangle, ready to feed
`rectResidueTheorem_multi_pole_unconditional`. -/
theorem weilRemainderGlobal_differentiableOn_rect
    {h : ℂ → ℂ} {Z : Finset ℂ}
    (hB : SimpleZeroBundle h Z)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (σL σR T : ℝ) (hσord : σL ≤ σR) (hσR : σR < 1)
    (hh_an : ∀ s ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), AnalyticAt ℂ h s)
    (hζ_ne_off_Z : ∀ s ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        s ∉ Z → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ (weilRemainderGlobal h Z hB hZ_ne_one)
      (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) := by
  intro s hs
  have h_s_ne_one : s ≠ 1 := by
    intro h_eq
    have h_s_re : s.re ∈ Set.uIcc σL σR := hs.1
    rw [Set.uIcc_of_le hσord] at h_s_re
    have h_s_re_le : s.re ≤ σR := h_s_re.2
    rw [h_eq] at h_s_re_le
    simp at h_s_re_le
    linarith
  by_cases hsZ : s ∈ Z
  · exact (weilRemainderGlobal_analyticAt_zero hB hZ_ne_one hsZ).differentiableAt.differentiableWithinAt
  · have hζ_ne : riemannZeta s ≠ 0 := hζ_ne_off_Z s hs hsZ
    have hh_s : AnalyticAt ℂ h s := hh_an s hs
    exact (weilRemainderGlobal_analyticAt_off_poles hB hZ_ne_one
      h_s_ne_one hsZ hζ_ne hh_s).differentiableAt.differentiableWithinAt

#print axioms weilRemainderGlobal_differentiableOn_rect

end Contour
end WeilPositivity
end ZD

end
