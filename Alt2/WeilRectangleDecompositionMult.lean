import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilContourMultiplicity
import RequestProject.WeilRectangleDecomposition
import RequestProject.WeilRectangleZeros

/-!
# Weil integrand Laurent decomposition — residue-form at multi-order zeros

Multi-order analog of `WeilRectangleDecomposition.lean`. Replaces `SimpleZeroBundle`
with `MultZeroBundle` (parameterized by an explicit `order : ℂ → ℕ` matching
`analyticOrderAt ζ ρ`), and uses the polar weight `-(order ρ : ℂ) · h(ρ)` in place
of `-h(ρ)`.

Proof structure is identical to the simple-zero version; the per-zero residue
form at an order-`n` zero comes from
`WeilContourMultiplicity.weilIntegrand_residue_form_at_zero_of_order`,
replacing the simple-zero-specific `psiOf` from the original file.

`order` is an explicit structure parameter (not a bundle field) because
`Prop`-valued structures cannot carry function-typed data.

No new axioms.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Hypothesis bundle for the multi-pole decomposition (multi-order).**
Parameterized over an explicit `order : ℂ → ℕ` giving the analytic order at each
`ρ ∈ Z`. -/
structure MultZeroBundle (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ) : Prop where
  ζ_an : ∀ ρ ∈ Z, AnalyticAt ℂ riemannZeta ρ
  ζ_zero : ∀ ρ ∈ Z, riemannZeta ρ = 0
  order_pos : ∀ ρ ∈ Z, 1 ≤ order ρ
  order_eq : ∀ ρ ∈ Z, analyticOrderAt riemannZeta ρ = (order ρ : ℕ∞)
  h_an : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ

/-- **Per-zero ψ witness (multi-order).** -/
noncomputable def psiOfMult (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ)
    (hB : MultZeroBundle h Z order) (ρ : ℂ) (hρ : ρ ∈ Z) : ℂ → ℂ :=
  Classical.choose (weilIntegrand_residue_form_at_zero_of_order
    (hB.ζ_an ρ hρ) (hB.ζ_zero ρ hρ) (hB.order_eq ρ hρ) (hB.order_pos ρ hρ) (hB.h_an ρ hρ))

private lemma psiOfMult_spec (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ)
    (hB : MultZeroBundle h Z order) (ρ : ℂ) (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (psiOfMult h Z order hB ρ hρ) ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilIntegrand h s =
          -(order ρ : ℂ) * h ρ / (s - ρ) + psiOfMult h Z order hB ρ hρ s :=
  Classical.choose_spec (weilIntegrand_residue_form_at_zero_of_order
    (hB.ζ_an ρ hρ) (hB.ζ_zero ρ hρ) (hB.order_eq ρ hρ) (hB.order_pos ρ hρ) (hB.h_an ρ hρ))

/-- **Naive decomposition function (multi-order).** -/
noncomputable def weilNaiveRemainderMult (h : ℂ → ℂ) (Z : Finset ℂ)
    (order : ℂ → ℕ) (s : ℂ) : ℂ :=
  weilIntegrand h s + ∑ ρ ∈ Z, (order ρ : ℂ) * h ρ / (s - ρ)

/-- **Off-pole analyticity.** -/
theorem weilNaiveRemainderMult_analyticAt_off_poles
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ} {s : ℂ}
    (hs_not_one : s ≠ 1) (hs_not_Z : s ∉ Z) (hζ_ne : riemannZeta s ≠ 0)
    (hh : AnalyticAt ℂ h s) :
    AnalyticAt ℂ (weilNaiveRemainderMult h Z order) s := by
  have hw_diff : DifferentiableAt ℂ (weilIntegrand h) s :=
    weilIntegrand_differentiableAt hs_not_one hζ_ne hh.differentiableAt
  have hw_an : AnalyticAt ℂ (weilIntegrand h) s := by
    unfold weilIntegrand
    have hζ_an : AnalyticAt ℂ riemannZeta s := by
      have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
      have hζ_diff_on : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
        fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
      exact hζ_diff_on.analyticOnNhd hopen s hs_not_one
    have hζ_deriv_an : AnalyticAt ℂ (deriv riemannZeta) s := hζ_an.deriv
    exact (hζ_deriv_an.neg.div hζ_an hζ_ne).mul hh
  have hpolar_an : ∀ ρ ∈ Z,
      AnalyticAt ℂ (fun t => (order ρ : ℂ) * h ρ / (t - ρ)) s := by
    intro ρ hρ
    have hs_ne_ρ : s ≠ ρ := fun h => hs_not_Z (h ▸ hρ)
    have h_sub_ne : s - ρ ≠ 0 := sub_ne_zero_of_ne hs_ne_ρ
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) h_sub_ne
  have hsum_an : AnalyticAt ℂ
      (fun t => ∑ ρ ∈ Z, (order ρ : ℂ) * h ρ / (t - ρ)) s := by
    have := Finset.analyticAt_sum Z hpolar_an
    convert this using 1
    funext t
    simp [Finset.sum_apply]
  unfold weilNaiveRemainderMult
  exact hw_an.add hsum_an

/-- **At a zero `ρ ∈ Z`, `weilNaiveRemainderMult` has a removable singularity.** -/
theorem weilNaiveRemainderMult_removable_at_zero
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ} {ρ : ℂ}
    (hρ : ρ ∈ Z) (_hρ_ne_one : ρ ≠ 1)
    (hB : MultZeroBundle h Z order) :
    ∃ g_ext : ℂ → ℂ, AnalyticAt ℂ g_ext ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, weilNaiveRemainderMult h Z order s = g_ext s := by
  set ψ := psiOfMult h Z order hB ρ hρ with hψ_def
  have hψ_spec := psiOfMult_spec h Z order hB ρ hρ
  set Z' := Z.erase ρ with hZ'_def
  set remainderSum : ℂ → ℂ :=
    fun s => ∑ ρ' ∈ Z', (order ρ' : ℂ) * h ρ' / (s - ρ') with hrs_def
  have hrs_an : AnalyticAt ℂ remainderSum ρ := by
    have hterm_an : ∀ ρ' ∈ Z',
        AnalyticAt ℂ (fun t => (order ρ' : ℂ) * h ρ' / (t - ρ')) ρ := by
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
  refine ⟨fun s => ψ s + remainderSum s, hψ_spec.1.add hrs_an, ?_⟩
  filter_upwards [hψ_spec.2, self_mem_nhdsWithin] with s hs_eq hs_mem
  have hs_ne_ρ : s ≠ ρ := hs_mem
  have hsub_ne : s - ρ ≠ 0 := sub_ne_zero_of_ne hs_ne_ρ
  have hsum_split :
      (∑ ρ' ∈ Z, (order ρ' : ℂ) * h ρ' / (s - ρ')) =
        (order ρ : ℂ) * h ρ / (s - ρ) + remainderSum s := by
    rw [hrs_def]
    rw [show Z = insert ρ Z' from (Finset.insert_erase hρ).symm]
    rw [Finset.sum_insert (fun h => ((Finset.mem_erase).mp h).1 rfl)]
  unfold weilNaiveRemainderMult
  rw [hsum_split, hs_eq]
  ring

#print axioms weilNaiveRemainderMult_analyticAt_off_poles
#print axioms weilNaiveRemainderMult_removable_at_zero

/-- **Canonical choice of analytic extension at each zero (multi-order).** -/
noncomputable def chooseGMult (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ)
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (ρ : ℂ) (hρ : ρ ∈ Z) : ℂ → ℂ :=
  Classical.choose
    (weilNaiveRemainderMult_removable_at_zero (h := h) (Z := Z) (order := order)
      (ρ := ρ) hρ (hZ_ne_one ρ hρ) hB)

private lemma chooseGMult_spec (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ)
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (ρ : ℂ) (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (chooseGMult h Z order hB hZ_ne_one ρ hρ) ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilNaiveRemainderMult h Z order s = chooseGMult h Z order hB hZ_ne_one ρ hρ s :=
  Classical.choose_spec
    (weilNaiveRemainderMult_removable_at_zero (h := h) (Z := Z) (order := order)
      (ρ := ρ) hρ (hZ_ne_one ρ hρ) hB)

/-- **Globally defined Weil remainder (multi-order).** -/
noncomputable def weilRemainderGlobalMult (h : ℂ → ℂ) (Z : Finset ℂ)
    (order : ℂ → ℕ) (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1) :
    ℂ → ℂ := fun s =>
  if hs : s ∈ Z then chooseGMult h Z order hB hZ_ne_one s hs s
  else weilNaiveRemainderMult h Z order s

/-- Global equals naive formula off `Z`. -/
theorem weilRemainderGlobalMult_off_Z {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {s : ℂ} (hs : s ∉ Z) :
    weilRemainderGlobalMult h Z order hB hZ_ne_one s =
      weilNaiveRemainderMult h Z order s := by
  unfold weilRemainderGlobalMult; simp [hs]

/-- Global equals `chooseGMult ρ ρ` at `s = ρ ∈ Z`. -/
theorem weilRemainderGlobalMult_at_Z {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    weilRemainderGlobalMult h Z order hB hZ_ne_one ρ =
      chooseGMult h Z order hB hZ_ne_one ρ hρ ρ := by
  unfold weilRemainderGlobalMult; simp [hρ]

/-- **Global remainder is analytic at each zero of `Z`.** -/
theorem weilRemainderGlobalMult_analyticAt_zero {h : ℂ → ℂ} {Z : Finset ℂ}
    {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (weilRemainderGlobalMult h Z order hB hZ_ne_one) ρ := by
  set g_ρ := chooseGMult h Z order hB hZ_ne_one ρ hρ with hg_ρ_def
  have hg_ρ_an : AnalyticAt ℂ g_ρ ρ :=
    (chooseGMult_spec h Z order hB hZ_ne_one ρ hρ).1
  have hg_ρ_eq : ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
      weilNaiveRemainderMult h Z order s = g_ρ s :=
    (chooseGMult_spec h Z order hB hZ_ne_one ρ hρ).2
  suffices hnhds : weilRemainderGlobalMult h Z order hB hZ_ne_one =ᶠ[nhds ρ] g_ρ by
    exact hg_ρ_an.congr hnhds.symm
  have h_iso := finset_isolated_nhds hρ
  have hg_ρ_eq_nhds : ∀ᶠ s in nhds ρ, s ≠ ρ →
      weilNaiveRemainderMult h Z order s = g_ρ s := by
    rw [Filter.eventually_iff_exists_mem]
    have hmem := hg_ρ_eq
    rw [Filter.eventually_iff, mem_nhdsWithin] at hmem
    obtain ⟨U, hU_open, hρ_U, hU_sub⟩ := hmem
    refine ⟨U, hU_open.mem_nhds hρ_U, fun s hs hne => ?_⟩
    exact hU_sub ⟨hs, hne⟩
  filter_upwards [h_iso, hg_ρ_eq_nhds] with s hs_iso hs_punct_eq
  by_cases hsZ : s ∈ Z
  · have hs_eq_ρ : s = ρ := hs_iso hsZ
    subst hs_eq_ρ
    exact weilRemainderGlobalMult_at_Z hB hZ_ne_one hρ
  · rw [weilRemainderGlobalMult_off_Z hB hZ_ne_one hsZ]
    have hs_ne_ρ : s ≠ ρ := fun heq => hsZ (heq ▸ hρ)
    exact hs_punct_eq hs_ne_ρ

#print axioms chooseGMult
#print axioms weilRemainderGlobalMult
#print axioms weilRemainderGlobalMult_off_Z
#print axioms weilRemainderGlobalMult_at_Z
#print axioms weilRemainderGlobalMult_analyticAt_zero

/-- **Global remainder is analytic at every off-pole point.** -/
theorem weilRemainderGlobalMult_analyticAt_off_poles
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {s : ℂ} (hs_not_one : s ≠ 1) (hs_not_Z : s ∉ Z)
    (hζ_ne : riemannZeta s ≠ 0) (hh : AnalyticAt ℂ h s) :
    AnalyticAt ℂ (weilRemainderGlobalMult h Z order hB hZ_ne_one) s := by
  have h_Z_closed : IsClosed (↑Z : Set ℂ) := Z.finite_toSet.isClosed
  have h_notZ_open : IsOpen ((↑Z : Set ℂ)ᶜ) := h_Z_closed.isOpen_compl
  have h_s_in_notZ : s ∈ (↑Z : Set ℂ)ᶜ := hs_not_Z
  have h_notZ_nhds : (↑Z : Set ℂ)ᶜ ∈ nhds s := h_notZ_open.mem_nhds h_s_in_notZ
  have h_eventual_notZ : ∀ᶠ s' in nhds s, s' ∉ Z := h_notZ_nhds
  have h_eq : weilRemainderGlobalMult h Z order hB hZ_ne_one =ᶠ[nhds s]
      weilNaiveRemainderMult h Z order := by
    filter_upwards [h_eventual_notZ] with s' hs'
    exact weilRemainderGlobalMult_off_Z hB hZ_ne_one hs'
  have h_naive_an : AnalyticAt ℂ (weilNaiveRemainderMult h Z order) s :=
    weilNaiveRemainderMult_analyticAt_off_poles hs_not_one hs_not_Z hζ_ne hh
  exact h_naive_an.congr h_eq.symm

#print axioms weilRemainderGlobalMult_analyticAt_off_poles

/-- **Decomposition equation off `Z` (multi-order).** For `s ∉ Z`,
`weilIntegrand h s = Σ (-(order ρ) · h(ρ))/(s-ρ) + weilRemainderGlobalMult(s)`. -/
theorem weilIntegrand_eq_polar_plus_global_mult
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    {s : ℂ} (hs_not_Z : s ∉ Z) :
    weilIntegrand h s =
        (∑ ρ ∈ Z, (-(order ρ : ℂ) * h ρ) / (s - ρ)) +
          weilRemainderGlobalMult h Z order hB hZ_ne_one s := by
  rw [weilRemainderGlobalMult_off_Z hB hZ_ne_one hs_not_Z]
  unfold weilNaiveRemainderMult
  have hsum_cancel :
      (∑ ρ ∈ Z, (-(order ρ : ℂ) * h ρ) / (s - ρ)) +
        (∑ ρ ∈ Z, (order ρ : ℂ) * h ρ / (s - ρ)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro ρ _
    ring
  linear_combination -hsum_cancel

#print axioms weilIntegrand_eq_polar_plus_global_mult

/-- **`weilRemainderGlobalMult` is `DifferentiableOn` a closed rectangle** in the
critical strip. -/
theorem weilRemainderGlobalMult_differentiableOn_rect
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (σL σR T : ℝ) (hσord : σL ≤ σR) (hσR : σR < 1)
    (hh_an : ∀ s ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), AnalyticAt ℂ h s)
    (hζ_ne_off_Z : ∀ s ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        s ∉ Z → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ (weilRemainderGlobalMult h Z order hB hZ_ne_one)
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
  · exact (weilRemainderGlobalMult_analyticAt_zero hB hZ_ne_one hsZ).differentiableAt.differentiableWithinAt
  · have hζ_ne : riemannZeta s ≠ 0 := hζ_ne_off_Z s hs hsZ
    have hh_s : AnalyticAt ℂ h s := hh_an s hs
    exact (weilRemainderGlobalMult_analyticAt_off_poles hB hZ_ne_one
      h_s_ne_one hsZ hζ_ne hh_s).differentiableAt.differentiableWithinAt

#print axioms weilRemainderGlobalMult_differentiableOn_rect

end Contour
end WeilPositivity
end ZD

end
