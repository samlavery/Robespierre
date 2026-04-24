import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilContourMultiplicity
import RequestProject.WeilPoleAtOne
import RequestProject.WeilWindingIntegral
import RequestProject.WeilRectangleDecomposition
import RequestProject.WeilRectangleDecompositionMult
import RequestProject.WeilFinalAssembly
import RequestProject.WeilRectangleZeros
import RequestProject.WeilRectangleZerosFull
import RequestProject.WeilPairTestContinuity

/-!
# Weil rectangle residue sum — full form including pole at s = 1

Assembles `rectangleResidueIdentity_target β` at `σL = -1, σR = 2` for the
cosh-pair Gauss test `pairTestMellin β`, using:

* `weilIntegrand_eq_polar_plus_global_mult` — the multi-order per-zero polar
  decomposition (multiplicity-weighted).
* `weilIntegrand_residue_form_at_one` — the pole-at-one residue form with
  residue `+h(1)`.
* `rectResidueTheorem_multi_pole_unconditional` — the generic multi-pole
  rectangle residue theorem (generic ι-indexed pole set).

Output: `rectangleResidueIdentity_target β` for every β ∈ (0,1) and T > 1.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

open Contour

/-- **Full naive remainder (zeros + pole at 1).** -/
noncomputable def weilNaiveRemainderFull (h : ℂ → ℂ) (Z : Finset ℂ)
    (order : ℂ → ℕ) (s : ℂ) : ℂ :=
  weilNaiveRemainderMult h Z order s - h 1 / (s - 1)

/-- Off `Z ∪ {1}`, `weilNaiveRemainderFull` is analytic. -/
theorem weilNaiveRemainderFull_analyticAt_off_poles
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ} {s : ℂ}
    (hs_not_one : s ≠ 1) (hs_not_Z : s ∉ Z) (hζ_ne : riemannZeta s ≠ 0)
    (hh : AnalyticAt ℂ h s) :
    AnalyticAt ℂ (weilNaiveRemainderFull h Z order) s := by
  have h_naive_an : AnalyticAt ℂ (weilNaiveRemainderMult h Z order) s :=
    weilNaiveRemainderMult_analyticAt_off_poles hs_not_one hs_not_Z hζ_ne hh
  have h_pole_an : AnalyticAt ℂ (fun z => h 1 / (z - 1)) s := by
    have h_sub_ne : s - 1 ≠ 0 := sub_ne_zero_of_ne hs_not_one
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) h_sub_ne
  unfold weilNaiveRemainderFull
  exact h_naive_an.sub h_pole_an

/-- At `ρ ∈ Z` (with `ρ ≠ 1`), `weilNaiveRemainderFull` has a removable
singularity. -/
theorem weilNaiveRemainderFull_removable_at_zero
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ} {ρ : ℂ}
    (hρ : ρ ∈ Z) (hρ_ne_one : ρ ≠ 1)
    (hB : MultZeroBundle h Z order) :
    ∃ g_ext : ℂ → ℂ, AnalyticAt ℂ g_ext ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ, weilNaiveRemainderFull h Z order s = g_ext s := by
  obtain ⟨g_mult, hg_mult_an, hg_mult_eq⟩ :=
    weilNaiveRemainderMult_removable_at_zero hρ hρ_ne_one hB
  have h_pole_an : AnalyticAt ℂ (fun z => h 1 / (z - 1)) ρ := by
    have h_sub_ne : ρ - 1 ≠ 0 := sub_ne_zero_of_ne hρ_ne_one
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) h_sub_ne
  refine ⟨fun s => g_mult s - h 1 / (s - 1), hg_mult_an.sub h_pole_an, ?_⟩
  filter_upwards [hg_mult_eq] with s hs_eq
  unfold weilNaiveRemainderFull
  rw [hs_eq]

/-- At `s = 1`, `weilNaiveRemainderFull` has a removable singularity. -/
theorem weilNaiveRemainderFull_removable_at_one
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (h1_not_Z : (1 : ℂ) ∉ Z) (hh1 : AnalyticAt ℂ h 1)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ) :
    ∃ g_ext : ℂ → ℂ, AnalyticAt ℂ g_ext 1 ∧
      ∀ᶠ s in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
        weilNaiveRemainderFull h Z order s = g_ext s := by
  obtain ⟨ψ₁, hψ₁_an, hψ₁_eq⟩ := weilIntegrand_residue_form_at_one (h := h) hh1
  set remSum : ℂ → ℂ :=
    fun s => ∑ ρ ∈ Z, (order ρ : ℂ) * h ρ / (s - ρ) with hremSum_def
  have hrem_an : AnalyticAt ℂ remSum 1 := by
    have hterm_an : ∀ ρ ∈ Z, AnalyticAt ℂ (fun t => (order ρ : ℂ) * h ρ / (t - ρ)) 1 := by
      intro ρ hρ
      have hρ_ne_one : (1 : ℂ) ≠ ρ := fun h => h1_not_Z (h ▸ hρ)
      have h_sub_ne : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero_of_ne hρ_ne_one
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) h_sub_ne
    have := Finset.analyticAt_sum Z hterm_an
    convert this using 1
    funext t
    rw [hremSum_def]
    simp [Finset.sum_apply]
  refine ⟨fun s => ψ₁ s + remSum s, hψ₁_an.add hrem_an, ?_⟩
  filter_upwards [hψ₁_eq, self_mem_nhdsWithin] with s hs_eq hs_mem
  have hs_ne : s ≠ 1 := hs_mem
  have hsub_ne : s - 1 ≠ 0 := sub_ne_zero_of_ne hs_ne
  -- weilIntegrand h s = h 1 / (s - 1) + ψ₁ s
  -- weilNaiveRemainderFull = weilIntegrand h s + remSum s - h(1)/(s-1) = ψ₁ s + remSum s.
  unfold weilNaiveRemainderFull weilNaiveRemainderMult
  rw [hremSum_def] at *
  rw [hs_eq]
  ring

#print axioms weilNaiveRemainderFull_analyticAt_off_poles
#print axioms weilNaiveRemainderFull_removable_at_zero
#print axioms weilNaiveRemainderFull_removable_at_one

/-- **Canonical analytic extension at `s = 1`.** -/
noncomputable def chooseG1 (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ)
    (h1_not_Z : (1 : ℂ) ∉ Z) (hh1 : AnalyticAt ℂ h 1)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ) : ℂ → ℂ :=
  Classical.choose (weilNaiveRemainderFull_removable_at_one
    (h := h) (Z := Z) (order := order) h1_not_Z hh1 hh_an_Z)

private lemma chooseG1_spec (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ)
    (h1_not_Z : (1 : ℂ) ∉ Z) (hh1 : AnalyticAt ℂ h 1)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ) :
    AnalyticAt ℂ (chooseG1 h Z order h1_not_Z hh1 hh_an_Z) 1 ∧
      ∀ᶠ s in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
        weilNaiveRemainderFull h Z order s = chooseG1 h Z order h1_not_Z hh1 hh_an_Z s :=
  Classical.choose_spec (weilNaiveRemainderFull_removable_at_one
    (h := h) (Z := Z) (order := order) h1_not_Z hh1 hh_an_Z)

/-- **Canonical analytic extension at each ρ ∈ Z.** -/
noncomputable def chooseGZFull (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ)
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (ρ : ℂ) (hρ : ρ ∈ Z) : ℂ → ℂ :=
  Classical.choose
    (weilNaiveRemainderFull_removable_at_zero (h := h) (Z := Z) (order := order)
      (ρ := ρ) hρ (hZ_ne_one ρ hρ) hB)

private lemma chooseGZFull_spec (h : ℂ → ℂ) (Z : Finset ℂ) (order : ℂ → ℕ)
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (ρ : ℂ) (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (chooseGZFull h Z order hB hZ_ne_one ρ hρ) ρ ∧
      ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
        weilNaiveRemainderFull h Z order s = chooseGZFull h Z order hB hZ_ne_one ρ hρ s :=
  Classical.choose_spec
    (weilNaiveRemainderFull_removable_at_zero (h := h) (Z := Z) (order := order)
      (ρ := ρ) hρ (hZ_ne_one ρ hρ) hB)

/-- **Global full remainder** — defined piecewise, coincides with the naive form
off `Z ∪ {1}` and takes the canonical analytic extension value at each pole. -/
noncomputable def weilRemainderGlobalFull (h : ℂ → ℂ) (Z : Finset ℂ)
    (order : ℂ → ℕ) (hB : MultZeroBundle h Z order)
    (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ) : ℂ → ℂ := fun s =>
  if hs : s ∈ Z then chooseGZFull h Z order hB hZ_ne_one s hs s
  else if hs1 : s = 1 then chooseG1 h Z order h1_not_Z hh1 hh_an_Z 1
  else weilNaiveRemainderFull h Z order s

theorem weilRemainderGlobalFull_off_Z_and_one
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    {s : ℂ} (hs : s ∉ Z) (hs1 : s ≠ 1) :
    weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z s =
      weilNaiveRemainderFull h Z order s := by
  unfold weilRemainderGlobalFull; simp [hs, hs1]

theorem weilRemainderGlobalFull_at_Z
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z ρ =
      chooseGZFull h Z order hB hZ_ne_one ρ hρ ρ := by
  unfold weilRemainderGlobalFull; simp [hρ]

theorem weilRemainderGlobalFull_at_one
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ) :
    weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z 1 =
      chooseG1 h Z order h1_not_Z hh1 hh_an_Z 1 := by
  unfold weilRemainderGlobalFull; simp [h1_not_Z]

theorem weilRemainderGlobalFull_analyticAt_zero
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z) ρ := by
  set g_ρ := chooseGZFull h Z order hB hZ_ne_one ρ hρ with hg_ρ_def
  have hg_ρ_an : AnalyticAt ℂ g_ρ ρ :=
    (chooseGZFull_spec h Z order hB hZ_ne_one ρ hρ).1
  have hg_ρ_eq : ∀ᶠ s in nhdsWithin ρ {ρ}ᶜ,
      weilNaiveRemainderFull h Z order s = g_ρ s :=
    (chooseGZFull_spec h Z order hB hZ_ne_one ρ hρ).2
  suffices hnhds :
      weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z =ᶠ[nhds ρ] g_ρ by
    exact hg_ρ_an.congr hnhds.symm
  have h_iso := finset_isolated_nhds hρ
  have h_ρ_ne_one : ρ ≠ 1 := hZ_ne_one ρ hρ
  have hone_nhd : ∀ᶠ s in nhds ρ, s ≠ 1 := by
    have : {1}ᶜ ∈ nhds ρ := isOpen_compl_singleton.mem_nhds h_ρ_ne_one
    exact this
  have hg_ρ_eq_nhds : ∀ᶠ s in nhds ρ, s ≠ ρ →
      weilNaiveRemainderFull h Z order s = g_ρ s := by
    rw [Filter.eventually_iff_exists_mem]
    have hmem := hg_ρ_eq
    rw [Filter.eventually_iff, mem_nhdsWithin] at hmem
    obtain ⟨U, hU_open, hρ_U, hU_sub⟩ := hmem
    refine ⟨U, hU_open.mem_nhds hρ_U, fun s hs hne => ?_⟩
    exact hU_sub ⟨hs, hne⟩
  filter_upwards [h_iso, hg_ρ_eq_nhds, hone_nhd] with s hs_iso hs_punct_eq hs_ne_one
  by_cases hsZ : s ∈ Z
  · have hs_eq_ρ : s = ρ := hs_iso hsZ
    subst hs_eq_ρ
    exact weilRemainderGlobalFull_at_Z hB hZ_ne_one hh1 h1_not_Z hh_an_Z hρ
  · rw [weilRemainderGlobalFull_off_Z_and_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z hsZ hs_ne_one]
    have hs_ne_ρ : s ≠ ρ := fun heq => hsZ (heq ▸ hρ)
    exact hs_punct_eq hs_ne_ρ

theorem weilRemainderGlobalFull_analyticAt_one
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ) :
    AnalyticAt ℂ (weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z) 1 := by
  set g_1 := chooseG1 h Z order h1_not_Z hh1 hh_an_Z with hg1_def
  have hg1_an : AnalyticAt ℂ g_1 1 := (chooseG1_spec h Z order h1_not_Z hh1 hh_an_Z).1
  have hg1_eq : ∀ᶠ s in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
      weilNaiveRemainderFull h Z order s = g_1 s :=
    (chooseG1_spec h Z order h1_not_Z hh1 hh_an_Z).2
  suffices hnhds :
      weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z =ᶠ[nhds 1] g_1 by
    exact hg1_an.congr hnhds.symm
  -- Z closed, 1 ∉ Z, so eventually s ∉ Z.
  have h_Z_closed : IsClosed (↑Z : Set ℂ) := Z.finite_toSet.isClosed
  have h_notZ_nhds : (↑Z : Set ℂ)ᶜ ∈ nhds (1 : ℂ) :=
    h_Z_closed.isOpen_compl.mem_nhds h1_not_Z
  have h_eventual_notZ : ∀ᶠ s in nhds (1 : ℂ), s ∉ Z := h_notZ_nhds
  have hg1_eq_nhds : ∀ᶠ s in nhds (1 : ℂ), s ≠ 1 →
      weilNaiveRemainderFull h Z order s = g_1 s := by
    rw [Filter.eventually_iff_exists_mem]
    have hmem := hg1_eq
    rw [Filter.eventually_iff, mem_nhdsWithin] at hmem
    obtain ⟨U, hU_open, h1_U, hU_sub⟩ := hmem
    refine ⟨U, hU_open.mem_nhds h1_U, fun s hs hne => ?_⟩
    exact hU_sub ⟨hs, hne⟩
  filter_upwards [h_eventual_notZ, hg1_eq_nhds] with s hsZ hs_punct_eq
  by_cases hs1 : s = 1
  · subst hs1
    rw [hg1_def]
    exact weilRemainderGlobalFull_at_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z
  · rw [weilRemainderGlobalFull_off_Z_and_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z hsZ hs1]
    exact hs_punct_eq hs1

theorem weilRemainderGlobalFull_analyticAt_off_poles
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    {s : ℂ} (hs_not_one : s ≠ 1) (hs_not_Z : s ∉ Z)
    (hζ_ne : riemannZeta s ≠ 0) (hh : AnalyticAt ℂ h s) :
    AnalyticAt ℂ (weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z) s := by
  have h_Z_closed : IsClosed (↑Z : Set ℂ) := Z.finite_toSet.isClosed
  have h_notZ_nhds : (↑Z : Set ℂ)ᶜ ∈ nhds s :=
    h_Z_closed.isOpen_compl.mem_nhds hs_not_Z
  have h_eventual_notZ : ∀ᶠ s' in nhds s, s' ∉ Z := h_notZ_nhds
  have h_notOne_nhds : {(1 : ℂ)}ᶜ ∈ nhds s :=
    isOpen_compl_singleton.mem_nhds hs_not_one
  have h_eventual_notOne : ∀ᶠ s' in nhds s, s' ≠ 1 := h_notOne_nhds
  have h_eq :
      weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z =ᶠ[nhds s]
        weilNaiveRemainderFull h Z order := by
    filter_upwards [h_eventual_notZ, h_eventual_notOne] with s' hs' hs'_ne_one
    exact weilRemainderGlobalFull_off_Z_and_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z hs' hs'_ne_one
  have h_naive_an : AnalyticAt ℂ (weilNaiveRemainderFull h Z order) s :=
    weilNaiveRemainderFull_analyticAt_off_poles hs_not_one hs_not_Z hζ_ne hh
  exact h_naive_an.congr h_eq.symm

#print axioms weilRemainderGlobalFull_analyticAt_zero
#print axioms weilRemainderGlobalFull_analyticAt_one
#print axioms weilRemainderGlobalFull_analyticAt_off_poles

/-- **Decomposition equation off `Z ∪ {1}`.** -/
theorem weilIntegrand_eq_polar_plus_global_full
    {h : ℂ → ℂ} {Z : Finset ℂ} {order : ℂ → ℕ}
    (hB : MultZeroBundle h Z order) (hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1)
    (hh1 : AnalyticAt ℂ h 1) (h1_not_Z : (1 : ℂ) ∉ Z)
    (hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ)
    {s : ℂ} (hs_not_Z : s ∉ Z) (hs_not_one : s ≠ 1) :
    weilIntegrand h s =
        h 1 / (s - 1) +
        (∑ ρ ∈ Z, (-(order ρ : ℂ) * h ρ) / (s - ρ)) +
          weilRemainderGlobalFull h Z order hB hZ_ne_one hh1 h1_not_Z hh_an_Z s := by
  rw [weilRemainderGlobalFull_off_Z_and_one hB hZ_ne_one hh1 h1_not_Z hh_an_Z hs_not_Z hs_not_one]
  unfold weilNaiveRemainderFull
  -- weilNaiveRemainderMult = weilIntegrand h + Σ (order ρ) h ρ / (s - ρ).
  -- We want: weilIntegrand h = h(1)/(s-1) + Σ -(order ρ) h ρ / (s - ρ) + (weilIntegrand h + Σ (order ρ)…) - h(1)/(s-1).
  unfold weilNaiveRemainderMult
  have hsum_cancel :
      (∑ ρ ∈ Z, (-(order ρ : ℂ) * h ρ) / (s - ρ)) +
        (∑ ρ ∈ Z, (order ρ : ℂ) * h ρ / (s - ρ)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro ρ _
    ring
  linear_combination -hsum_cancel

#print axioms weilIntegrand_eq_polar_plus_global_full

end FinalAssembly
end WeilPositivity
end ZD

end
