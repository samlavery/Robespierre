import Mathlib
import RequestProject.WeilHadamardKernel
import RequestProject.WeilRectangleDecomposition

/-!
# Hadamard-kernel rectangle decomposition

This file builds the closed-rectangle holomorphic remainder for
`weilIntegrand (hadamardKernel s)`, with poles coming from:

* nontrivial zeros of `ζ` inside a finite set `Z`, weighted by multiplicity;
* the pole of `ζ` at `1`;
* the kernel pole at `z = s`.

It is the hadamard-specific analogue of `WeilRectangleDecomposition.lean`, but
without the simple-zero restriction.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- Multiplicity-weighted residue coefficient at a nontrivial zero `ρ`. -/
def hadamardZeroCoeff (s ρ : ℂ) : ℂ :=
  (ZD.xiOrderNat ρ : ℂ) * hadamardKernel s ρ

/-- Residue coefficient at the pole `z = 1`. -/
def hadamardOneCoeff (s : ℂ) : ℂ :=
  hadamardKernel s 1

/-- Residue coefficient at the kernel pole `z = 0`. -/
def hadamardOriginCoeff : ℂ :=
  -(deriv riemannZeta 0 / riemannZeta 0)

/-- Residue coefficient at the self-pole `z = s`. -/
def hadamardSelfCoeff (s : ℂ) : ℂ :=
  deriv riemannZeta s / riemannZeta s

/-- Naive remainder for `weilIntegrand (hadamardKernel s)`. Off the poles
`Z ∪ {1, s}`, it equals the integrand plus the cancelling polar parts. -/
def hadamardNaiveRemainder (s : ℂ) (Z : Finset ℂ) (z : ℂ) : ℂ :=
  weilIntegrand (hadamardKernel s) z +
    ∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (z - ρ) -
    hadamardOneCoeff s / (z - 1) -
    hadamardSelfCoeff s / (z - s)

private lemma nontrivialZero_ne_zero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 0 := by
  intro h
  rw [h] at hρ
  simp [NontrivialZeros] at hρ

private lemma nontrivialZero_ne_one {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 1 := by
  intro h
  rw [h] at hρ
  simp [NontrivialZeros] at hρ

private lemma one_not_mem_zeroFinset {Z : Finset ℂ} (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    (1 : ℂ) ∉ Z := by
  intro h1
  exact nontrivialZero_ne_one (hZ 1 h1) rfl

private lemma zero_not_mem_zeroFinset {Z : Finset ℂ} (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    (0 : ℂ) ∉ Z := by
  intro h0
  exact nontrivialZero_ne_zero (hZ 0 h0) rfl

private lemma self_not_mem_zeroFinset {s : ℂ} {Z : Finset ℂ} (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    s ∉ Z := by
  intro hsZ
  exact hsζ (hZ s hsZ).2.2

private theorem riemannZeta_analyticAt_of_re_lt_one {z : ℂ} (hz : z.re < 1) :
    AnalyticAt ℂ riemannZeta z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have h_diff_on : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    intro w hw
    exact (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact (h_diff_on.analyticOnNhd isOpen_compl_singleton) z hz1

/-- Off `Z ∪ {1, s}`, the hadamard naive remainder is analytic. -/
theorem hadamardNaiveRemainder_analyticAt_off_poles
    {s : ℂ} {Z : Finset ℂ} {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzZ : z ∉ Z) (hzs : z ≠ s)
    (hζ_ne : riemannZeta z ≠ 0) :
    AnalyticAt ℂ (hadamardNaiveRemainder s Z) z := by
  have hw_an : AnalyticAt ℂ (weilIntegrand (hadamardKernel s)) z := by
    unfold weilIntegrand
    have h_diff_on : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
      intro w hw
      exact (differentiableAt_riemannZeta hw).differentiableWithinAt
    have hζ_an : AnalyticAt ℂ riemannZeta z :=
      (h_diff_on.analyticOnNhd isOpen_compl_singleton) z hz1
    exact (hζ_an.deriv.neg.div hζ_an hζ_ne).mul (hadamardKernel_analyticAt hzs.symm hz0)
  have hzero_an :
      AnalyticAt ℂ (fun w => ∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (w - ρ)) z := by
    have hterm :
        ∀ ρ ∈ Z, AnalyticAt ℂ (fun w => hadamardZeroCoeff s ρ / (w - ρ)) z := by
      intro ρ hρ
      have hzρ : z ≠ ρ := fun h => hzZ (h ▸ hρ)
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const)
        (sub_ne_zero_of_ne hzρ)
    have hsum := Finset.analyticAt_sum Z hterm
    convert hsum using 1
    funext w
    simp [Finset.sum_apply]
  have hone_an : AnalyticAt ℂ (fun w => hadamardOneCoeff s / (w - 1)) z :=
    analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (sub_ne_zero_of_ne hz1)
  have hself_an : AnalyticAt ℂ (fun w => hadamardSelfCoeff s / (w - s)) z :=
    analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (sub_ne_zero_of_ne hzs)
  unfold hadamardNaiveRemainder
  exact hw_an.add hzero_an |>.sub hone_an |>.sub hself_an

/-- The naive hadamard remainder has a removable singularity at each zero in `Z`. -/
theorem hadamardNaiveRemainder_removable_at_zero
    {s : ℂ} {Z : Finset ℂ}
    (_hs0 : s ≠ 0) (_hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    ∃ g_ext : ℂ → ℂ, AnalyticAt ℂ g_ext ρ ∧
      ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, hadamardNaiveRemainder s Z z = g_ext z := by
  have hs_not_ntz : s ∉ NontrivialZeros := by
    intro hs_ntz
    exact hsζ hs_ntz.2.2
  have hρ_ntz : ρ ∈ NontrivialZeros := hZ ρ hρ
  have hρ_an : AnalyticAt ℂ riemannZeta ρ := riemannZeta_analyticAt_of_re_lt_one hρ_ntz.2.1
  obtain ⟨ψ, hψ_an, hψ_eq⟩ :=
    weilIntegrand_residue_form_at_zero_of_order
      hρ_an hρ_ntz.2.2 (analyticOrderAt_riemannZeta_eq_xiOrderNat hρ_ntz)
      (Nat.succ_le_of_lt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ_ntz))
      (hadamardKernel_analyticAt_nontrivialZero hs_not_ntz hρ_ntz)
  set Z' := Z.erase ρ with hZ'_def
  set remainderSum : ℂ → ℂ :=
    fun z => ∑ ρ' ∈ Z', hadamardZeroCoeff s ρ' / (z - ρ') with hremainder_def
  have hremainder_an : AnalyticAt ℂ remainderSum ρ := by
    have hterm :
        ∀ ρ' ∈ Z', AnalyticAt ℂ (fun z => hadamardZeroCoeff s ρ' / (z - ρ')) ρ := by
      intro ρ' hρ'
      have hmem : ρ' ≠ ρ ∧ ρ' ∈ Z := Finset.mem_erase.mp hρ'
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const)
        (sub_ne_zero_of_ne (fun h => hmem.1 h.symm))
    have hsum := Finset.analyticAt_sum Z' hterm
    convert hsum using 1
    funext z
    rw [hremainder_def]
    simp [Finset.sum_apply]
  have hone_an : AnalyticAt ℂ (fun z => hadamardOneCoeff s / (z - 1)) ρ := by
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const)
      (sub_ne_zero_of_ne (nontrivialZero_ne_one hρ_ntz))
  have hself_an : AnalyticAt ℂ (fun z => hadamardSelfCoeff s / (z - s)) ρ := by
    have hsρ : ρ ≠ s := by
      intro h
      exact hsζ (h ▸ hρ_ntz.2.2)
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const)
      (sub_ne_zero_of_ne hsρ)
  refine ⟨fun z => ψ z + remainderSum z - hadamardOneCoeff s / (z - 1) -
      hadamardSelfCoeff s / (z - s), ?_, ?_⟩
  · exact hψ_an.add hremainder_an |>.sub hone_an |>.sub hself_an
  · filter_upwards [hψ_eq, self_mem_nhdsWithin] with z hz hzmem
    have hzρ : z ≠ ρ := hzmem
    have hsum_split :
        (∑ ρ' ∈ Z, hadamardZeroCoeff s ρ' / (z - ρ')) =
          hadamardZeroCoeff s ρ / (z - ρ) + remainderSum z := by
      rw [hremainder_def]
      rw [show Z = insert ρ Z' from (Finset.insert_erase hρ).symm]
      rw [Finset.sum_insert (fun h => ((Finset.mem_erase.mp h).1 rfl))]
    have hcoeff :
        hadamardZeroCoeff s ρ = (ZD.xiOrderNat ρ : ℂ) * hadamardKernel s ρ := rfl
    unfold hadamardNaiveRemainder
    rw [hsum_split, hz, hcoeff]
    ring

/-- The naive hadamard remainder has a removable singularity at `z = 1`. -/
theorem hadamardNaiveRemainder_removable_at_one
    {s : ℂ} {Z : Finset ℂ}
    (_hs0 : s ≠ 0) (hs1 : s ≠ 1) (_hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    ∃ g_ext : ℂ → ℂ, AnalyticAt ℂ g_ext 1 ∧
      ∀ᶠ z in nhdsWithin (1 : ℂ) ({1}ᶜ), hadamardNaiveRemainder s Z z = g_ext z := by
  obtain ⟨ψ, hψ_an, hψ_eq⟩ :=
    weilIntegrand_residue_form_at_one
      (hadamardKernel_analyticAt (s := s) (ρ := 1) hs1 one_ne_zero)
  have hzero_an :
      AnalyticAt ℂ (fun z => ∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (z - ρ)) 1 := by
    have hterm :
        ∀ ρ ∈ Z, AnalyticAt ℂ (fun z => hadamardZeroCoeff s ρ / (z - ρ)) 1 := by
      intro ρ hρ
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const)
        (sub_ne_zero_of_ne (nontrivialZero_ne_one (hZ ρ hρ)).symm)
    have hsum := Finset.analyticAt_sum Z hterm
    convert hsum using 1
    funext z
    simp [Finset.sum_apply]
  have hself_an : AnalyticAt ℂ (fun z => hadamardSelfCoeff s / (z - s)) 1 := by
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (sub_ne_zero_of_ne hs1.symm)
  refine ⟨fun z => ψ z + ∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (z - ρ) -
      hadamardSelfCoeff s / (z - s), ?_, ?_⟩
  · exact hψ_an.add hzero_an |>.sub hself_an
  · filter_upwards [hψ_eq] with z hz
    unfold hadamardNaiveRemainder hadamardOneCoeff
    rw [hz]
    ring

/-- The naive hadamard remainder has a removable singularity at the self-pole
`z = s`. -/
theorem hadamardNaiveRemainder_removable_at_self
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    ∃ g_ext : ℂ → ℂ, AnalyticAt ℂ g_ext s ∧
      ∀ᶠ z in nhdsWithin s {s}ᶜ, hadamardNaiveRemainder s Z z = g_ext z := by
  obtain ⟨ψ, hψ_an, hψ_eq⟩ :=
    weilIntegrand_residue_form_hadamardKernel_at_self hs0 hs1 hsζ
  have hself_not_mem : s ∉ Z := self_not_mem_zeroFinset hsζ hZ
  have hzero_an :
      AnalyticAt ℂ (fun z => ∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (z - ρ)) s := by
    have hterm :
        ∀ ρ ∈ Z, AnalyticAt ℂ (fun z => hadamardZeroCoeff s ρ / (z - ρ)) s := by
      intro ρ hρ
      have hsρ : s ≠ ρ := by
        intro h
        exact hsζ (h ▸ (hZ ρ hρ).2.2)
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const)
        (sub_ne_zero_of_ne hsρ)
    have hsum := Finset.analyticAt_sum Z hterm
    convert hsum using 1
    funext z
    simp [Finset.sum_apply]
  have hone_an : AnalyticAt ℂ (fun z => hadamardOneCoeff s / (z - 1)) s := by
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (sub_ne_zero_of_ne hs1)
  refine ⟨fun z => ψ z + ∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (z - ρ) -
      hadamardOneCoeff s / (z - 1), ?_, ?_⟩
  · exact hψ_an.add hzero_an |>.sub hone_an
  · filter_upwards [hψ_eq] with z hz
    unfold hadamardNaiveRemainder hadamardSelfCoeff
    rw [hz]
    ring

/-- Canonical analytic extension chosen at a zero in `Z`. -/
noncomputable def hadamardChooseZero (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    (ρ : ℂ) (hρ : ρ ∈ Z) : ℂ → ℂ :=
  Classical.choose (hadamardNaiveRemainder_removable_at_zero hs0 hs1 hsζ hZ hρ)

private lemma hadamardChooseZero_spec (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    (ρ : ℂ) (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (hadamardChooseZero s Z hs0 hs1 hsζ hZ ρ hρ) ρ ∧
      ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ,
        hadamardNaiveRemainder s Z z = hadamardChooseZero s Z hs0 hs1 hsζ hZ ρ hρ z :=
  Classical.choose_spec (hadamardNaiveRemainder_removable_at_zero hs0 hs1 hsζ hZ hρ)

/-- Canonical analytic extension chosen at `z = 1`. -/
noncomputable def hadamardChooseOne (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) : ℂ → ℂ :=
  Classical.choose (hadamardNaiveRemainder_removable_at_one hs0 hs1 hsζ hZ)

private lemma hadamardChooseOne_spec (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    AnalyticAt ℂ (hadamardChooseOne s Z hs0 hs1 hsζ hZ) 1 ∧
      ∀ᶠ z in nhdsWithin (1 : ℂ) ({1}ᶜ),
        hadamardNaiveRemainder s Z z = hadamardChooseOne s Z hs0 hs1 hsζ hZ z :=
  Classical.choose_spec (hadamardNaiveRemainder_removable_at_one hs0 hs1 hsζ hZ)

/-- Canonical analytic extension chosen at the self-pole `z = s`. -/
noncomputable def hadamardChooseSelf (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) : ℂ → ℂ :=
  Classical.choose (hadamardNaiveRemainder_removable_at_self hs0 hs1 hsζ hZ)

private lemma hadamardChooseSelf_spec (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    AnalyticAt ℂ (hadamardChooseSelf s Z hs0 hs1 hsζ hZ) s ∧
      ∀ᶠ z in nhdsWithin s {s}ᶜ,
        hadamardNaiveRemainder s Z z = hadamardChooseSelf s Z hs0 hs1 hsζ hZ z :=
  Classical.choose_spec (hadamardNaiveRemainder_removable_at_self hs0 hs1 hsζ hZ)

/-- Global remainder with the zeros of `Z` patched by removable singularities. -/
noncomputable def hadamardZeroGlobal (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) : ℂ → ℂ := fun z =>
  if hz : z ∈ Z then hadamardChooseZero s Z hs0 hs1 hsζ hZ z hz z
  else hadamardNaiveRemainder s Z z

theorem hadamardZeroGlobal_of_notMem {s : ℂ} {Z : Finset ℂ}
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} {hsζ : riemannZeta s ≠ 0}
    {hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros}
    {z : ℂ} (hz : z ∉ Z) :
    hadamardZeroGlobal s Z hs0 hs1 hsζ hZ z = hadamardNaiveRemainder s Z z := by
  simp [hadamardZeroGlobal, hz]

theorem hadamardZeroGlobal_at_zero {s : ℂ} {Z : Finset ℂ}
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} {hsζ : riemannZeta s ≠ 0}
    {hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros}
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    hadamardZeroGlobal s Z hs0 hs1 hsζ hZ ρ =
      hadamardChooseZero s Z hs0 hs1 hsζ hZ ρ hρ ρ := by
  simp [hadamardZeroGlobal, hρ]

theorem hadamardZeroGlobal_analyticAt_zero {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (hadamardZeroGlobal s Z hs0 hs1 hsζ hZ) ρ := by
  set gρ := hadamardChooseZero s Z hs0 hs1 hsζ hZ ρ hρ with hgρ_def
  have hgρ_an : AnalyticAt ℂ gρ ρ := (hadamardChooseZero_spec s Z hs0 hs1 hsζ hZ ρ hρ).1
  have hgρ_eq :
      ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, hadamardNaiveRemainder s Z z = gρ z := by
    simpa [hgρ_def] using (hadamardChooseZero_spec s Z hs0 hs1 hsζ hZ ρ hρ).2
  suffices hnhds : hadamardZeroGlobal s Z hs0 hs1 hsζ hZ =ᶠ[nhds ρ] gρ by
    exact hgρ_an.congr hnhds.symm
  have h_iso := finset_isolated_nhds hρ
  have hgρ_eq_nhds : ∀ᶠ z in nhds ρ, z ≠ ρ → hadamardNaiveRemainder s Z z = gρ z := by
    rw [Filter.eventually_iff_exists_mem]
    rw [Filter.eventually_iff, mem_nhdsWithin] at hgρ_eq
    obtain ⟨U, hU_open, hρU, hU_sub⟩ := hgρ_eq
    refine ⟨U, hU_open.mem_nhds hρU, ?_⟩
    intro z hz hzρ
    exact hU_sub ⟨hz, hzρ⟩
  filter_upwards [h_iso, hgρ_eq_nhds] with z hz_iso hz_eq
  by_cases hzZ : z ∈ Z
  · have hzρ : z = ρ := hz_iso hzZ
    subst hzρ
    simpa [hgρ_def] using hadamardZeroGlobal_at_zero (s := s) (Z := Z)
      (hs0 := hs0) (hs1 := hs1) (hsζ := hsζ) (hZ := hZ) hρ
  · rw [hadamardZeroGlobal_of_notMem hzZ]
    exact hz_eq (fun h => hzZ (h ▸ hρ))

theorem hadamardZeroGlobal_analyticAt_off_Z {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzZ : z ∉ Z) (hzs : z ≠ s)
    (hζ_ne : riemannZeta z ≠ 0) :
    AnalyticAt ℂ (hadamardZeroGlobal s Z hs0 hs1 hsζ hZ) z := by
  have h_eq :
      hadamardZeroGlobal s Z hs0 hs1 hsζ hZ =ᶠ[nhds z] hadamardNaiveRemainder s Z := by
    have hZ_closed : IsClosed (↑Z : Set ℂ) := Z.finite_toSet.isClosed
    have h_notZ_nhds : (↑Z : Set ℂ)ᶜ ∈ nhds z := hZ_closed.isOpen_compl.mem_nhds hzZ
    filter_upwards [h_notZ_nhds] with w hw
    exact hadamardZeroGlobal_of_notMem hw
  exact (hadamardNaiveRemainder_analyticAt_off_poles hz0 hz1 hzZ hzs hζ_ne).congr h_eq.symm

/-- Zero-patched remainder, with the value at `1` replaced by its removable extension. -/
noncomputable def hadamardOneGlobal (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) : ℂ → ℂ :=
  Function.update (hadamardZeroGlobal s Z hs0 hs1 hsζ hZ) 1
    ((hadamardChooseOne s Z hs0 hs1 hsζ hZ) 1)

theorem hadamardOneGlobal_of_ne_one {s : ℂ} {Z : Finset ℂ}
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} {hsζ : riemannZeta s ≠ 0}
    {hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros}
    {z : ℂ} (hz : z ≠ 1) :
    hadamardOneGlobal s Z hs0 hs1 hsζ hZ z = hadamardZeroGlobal s Z hs0 hs1 hsζ hZ z := by
  simp [hadamardOneGlobal, Function.update_of_ne hz]

theorem hadamardOneGlobal_analyticAt_one {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    AnalyticAt ℂ (hadamardOneGlobal s Z hs0 hs1 hsζ hZ) 1 := by
  set g1 := hadamardChooseOne s Z hs0 hs1 hsζ hZ with hg1_def
  have hg1_an : AnalyticAt ℂ g1 1 := (hadamardChooseOne_spec s Z hs0 hs1 hsζ hZ).1
  have hg1_eq :
      ∀ᶠ z in nhdsWithin (1 : ℂ) ({1}ᶜ), hadamardNaiveRemainder s Z z = g1 z := by
    simpa [hg1_def] using (hadamardChooseOne_spec s Z hs0 hs1 hsζ hZ).2
  suffices hnhds : hadamardOneGlobal s Z hs0 hs1 hsζ hZ =ᶠ[nhds (1 : ℂ)] g1 by
    exact hg1_an.congr hnhds.symm
  have h_notZ_nhds : (↑Z : Set ℂ)ᶜ ∈ nhds (1 : ℂ) := by
    exact Z.finite_toSet.isClosed.isOpen_compl.mem_nhds (one_not_mem_zeroFinset hZ)
  have hg1_eq_nhds :
      ∀ᶠ z in nhds (1 : ℂ), z ≠ 1 → hadamardNaiveRemainder s Z z = g1 z := by
    rw [Filter.eventually_iff_exists_mem]
    rw [Filter.eventually_iff, mem_nhdsWithin] at hg1_eq
    obtain ⟨U, hU_open, h1U, hU_sub⟩ := hg1_eq
    refine ⟨U, hU_open.mem_nhds h1U, ?_⟩
    intro z hz hz1
    exact hU_sub ⟨hz, hz1⟩
  filter_upwards [h_notZ_nhds, hg1_eq_nhds] with z hzZ hz_eq
  by_cases hz1 : z = 1
  · subst hz1
    simp [hadamardOneGlobal, hg1_def]
  · rw [hadamardOneGlobal_of_ne_one hz1, hadamardZeroGlobal_of_notMem hzZ]
    exact hz_eq hz1

theorem hadamardOneGlobal_analyticAt_of_ne_one {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {z : ℂ} (hz1 : z ≠ 1)
    (hz_an : AnalyticAt ℂ (hadamardZeroGlobal s Z hs0 hs1 hsζ hZ) z) :
    AnalyticAt ℂ (hadamardOneGlobal s Z hs0 hs1 hsζ hZ) z := by
  have h_eq :
      hadamardOneGlobal s Z hs0 hs1 hsζ hZ =ᶠ[nhds z]
        hadamardZeroGlobal s Z hs0 hs1 hsζ hZ := by
    filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
    exact hadamardOneGlobal_of_ne_one hw
  exact hz_an.congr h_eq.symm

/-- Fully patched hadamard remainder. -/
noncomputable def hadamardRemainderGlobal (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) : ℂ → ℂ :=
  Function.update (hadamardOneGlobal s Z hs0 hs1 hsζ hZ) s
    ((hadamardChooseSelf s Z hs0 hs1 hsζ hZ) s)

theorem hadamardRemainderGlobal_of_ne_self {s : ℂ} {Z : Finset ℂ}
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} {hsζ : riemannZeta s ≠ 0}
    {hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros}
    {z : ℂ} (hz : z ≠ s) :
    hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z =
      hadamardOneGlobal s Z hs0 hs1 hsζ hZ z := by
  simp [hadamardRemainderGlobal, Function.update_of_ne hz]

theorem hadamardRemainderGlobal_analyticAt_self {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    AnalyticAt ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) s := by
  set gs := hadamardChooseSelf s Z hs0 hs1 hsζ hZ with hgs_def
  have hgs_an : AnalyticAt ℂ gs s := (hadamardChooseSelf_spec s Z hs0 hs1 hsζ hZ).1
  have hgs_eq :
      ∀ᶠ z in nhdsWithin s {s}ᶜ, hadamardNaiveRemainder s Z z = gs z := by
    simpa [hgs_def] using (hadamardChooseSelf_spec s Z hs0 hs1 hsζ hZ).2
  suffices hnhds : hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ =ᶠ[nhds s] gs by
    exact hgs_an.congr hnhds.symm
  have h_notZ_nhds : (↑Z : Set ℂ)ᶜ ∈ nhds s := by
    exact Z.finite_toSet.isClosed.isOpen_compl.mem_nhds (self_not_mem_zeroFinset hsζ hZ)
  have h_ne_one_nhds : {z : ℂ | z ≠ 1} ∈ nhds s := isOpen_ne.mem_nhds hs1
  have hgs_eq_nhds :
      ∀ᶠ z in nhds s, z ≠ s → hadamardNaiveRemainder s Z z = gs z := by
    rw [Filter.eventually_iff_exists_mem]
    rw [Filter.eventually_iff, mem_nhdsWithin] at hgs_eq
    obtain ⟨U, hU_open, hsU, hU_sub⟩ := hgs_eq
    refine ⟨U, hU_open.mem_nhds hsU, ?_⟩
    intro z hz hzs
    exact hU_sub ⟨hz, hzs⟩
  filter_upwards [h_notZ_nhds, h_ne_one_nhds, hgs_eq_nhds] with z hzZ hz1 hz_eq
  by_cases hzs : z = s
  · subst hzs
    simp [hadamardRemainderGlobal, hgs_def]
  · rw [hadamardRemainderGlobal_of_ne_self hzs, hadamardOneGlobal_of_ne_one hz1,
      hadamardZeroGlobal_of_notMem hzZ]
    exact hz_eq hzs

theorem hadamardRemainderGlobal_analyticAt_of_ne_self {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {z : ℂ} (hzs : z ≠ s)
    (hz_an : AnalyticAt ℂ (hadamardOneGlobal s Z hs0 hs1 hsζ hZ) z) :
    AnalyticAt ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) z := by
  have h_eq :
      hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ =ᶠ[nhds z]
        hadamardOneGlobal s Z hs0 hs1 hsζ hZ := by
    filter_upwards [isOpen_ne.mem_nhds hzs] with w hw
    exact hadamardRemainderGlobal_of_ne_self hw
  exact hz_an.congr h_eq.symm

theorem hadamardRemainderGlobal_analyticAt_zero {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {ρ : ℂ} (hρ : ρ ∈ Z) :
    AnalyticAt ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) ρ := by
  have hρ_ntz : ρ ∈ NontrivialZeros := hZ ρ hρ
  have hρ_ne_one : ρ ≠ 1 := nontrivialZero_ne_one hρ_ntz
  have hρ_ne_s : ρ ≠ s := by
    intro h
    exact hsζ (h ▸ hρ_ntz.2.2)
  exact hadamardRemainderGlobal_analyticAt_of_ne_self hs0 hs1 hsζ hZ hρ_ne_s <|
    hadamardOneGlobal_analyticAt_of_ne_one hs0 hs1 hsζ hZ hρ_ne_one <|
      hadamardZeroGlobal_analyticAt_zero hs0 hs1 hsζ hZ hρ

theorem hadamardRemainderGlobal_analyticAt_one {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    AnalyticAt ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) 1 := by
  exact hadamardRemainderGlobal_analyticAt_of_ne_self hs0 hs1 hsζ hZ hs1.symm <|
    hadamardOneGlobal_analyticAt_one hs0 hs1 hsζ hZ

theorem hadamardRemainderGlobal_analyticAt_off_poles {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzZ : z ∉ Z) (hzs : z ≠ s)
    (hζ_ne : riemannZeta z ≠ 0) :
    AnalyticAt ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) z := by
  exact hadamardRemainderGlobal_analyticAt_of_ne_self hs0 hs1 hsζ hZ hzs <|
    hadamardOneGlobal_analyticAt_of_ne_one hs0 hs1 hsζ hZ hz1 <|
      hadamardZeroGlobal_analyticAt_off_Z hs0 hs1 hsζ hZ hz0 hz1 hzZ hzs hζ_ne

/-- Off `Z ∪ {1, s}`, the fully patched remainder agrees with the naive formula. -/
theorem hadamardRemainderGlobal_off_poles {s : ℂ} {Z : Finset ℂ}
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} {hsζ : riemannZeta s ≠ 0}
    {hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros}
    {z : ℂ} (hzZ : z ∉ Z) (hz1 : z ≠ 1) (hzs : z ≠ s) :
    hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z = hadamardNaiveRemainder s Z z := by
  rw [hadamardRemainderGlobal_of_ne_self hzs, hadamardOneGlobal_of_ne_one hz1,
    hadamardZeroGlobal_of_notMem hzZ]

/-- Off the poles, `weilIntegrand (hadamardKernel s)` splits into its polar part
plus the global holomorphic remainder. -/
theorem weilIntegrand_hadamardKernel_eq_polar_plus_global
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {z : ℂ} (hzZ : z ∉ Z) (hz1 : z ≠ 1) (hzs : z ≠ s) :
    weilIntegrand (hadamardKernel s) z =
      (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
        hadamardOneCoeff s / (z - 1) +
        hadamardSelfCoeff s / (z - s) +
        hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z := by
  rw [hadamardRemainderGlobal_off_poles hzZ hz1 hzs]
  unfold hadamardNaiveRemainder
  have hsum_cancel :
      (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
        (∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (z - ρ)) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero ?_
    intro ρ hρ
    ring
  linear_combination -hsum_cancel

/-- The fully patched hadamard remainder is holomorphic on a closed rectangle
avoiding `0`, once the zeros inside it are listed in `Z`. -/
theorem hadamardRemainderGlobal_differentiableOn_rect
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    (σL σR T : ℝ) (hσord : σL ≤ σR) (hσL : 0 < σL)
    (hζ_ne_off_Z :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        z ≠ 1 → z ∉ Z → riemannZeta z ≠ 0) :
    DifferentiableOn ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ)
      (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) := by
  intro z hz
  have hz_re : z.re ∈ Set.uIcc σL σR := hz.1
  rw [Set.uIcc_of_le hσord] at hz_re
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz_re
    simp at hz_re
    linarith
  by_cases hzs : z = s
  · subst hzs
    have hdiff :
        DifferentiableAt ℂ (hadamardRemainderGlobal z Z hs0 hs1 hsζ hZ) z :=
      (hadamardRemainderGlobal_analyticAt_self hs0 hs1 hsζ hZ).differentiableAt
    exact hdiff.differentiableWithinAt
  · by_cases hz1 : z = 1
    · subst hz1
      have hdiff :
          DifferentiableAt ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) 1 :=
        (hadamardRemainderGlobal_analyticAt_one hs0 hs1 hsζ hZ).differentiableAt
      exact hdiff.differentiableWithinAt
    · by_cases hzZ : z ∈ Z
      · have hdiff :
            DifferentiableAt ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) z :=
          (hadamardRemainderGlobal_analyticAt_zero hs0 hs1 hsζ hZ hzZ).differentiableAt
        exact hdiff.differentiableWithinAt
      · have hζ_ne : riemannZeta z ≠ 0 := hζ_ne_off_Z z hz hz1 hzZ
        exact (hadamardRemainderGlobal_analyticAt_off_poles hs0 hs1 hsζ hZ
          hz0 hz1 hzZ hzs hζ_ne).differentiableAt.differentiableWithinAt

/-- The origin-adjusted Hadamard remainder subtracts the `z = 0` polar part
from the already-patched global remainder. -/
noncomputable def hadamardRemainderWithOriginNaive (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) : ℂ → ℂ := fun z =>
  hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z - hadamardOriginCoeff / z

theorem hadamardRemainderWithOriginNaive_analyticAt_of_ne_zero
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {z : ℂ} (hz0 : z ≠ 0)
    (hz_an : AnalyticAt ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) z) :
    AnalyticAt ℂ (hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ) z := by
  unfold hadamardRemainderWithOriginNaive hadamardOriginCoeff
  exact hz_an.sub <|
    analyticAt_const.div analyticAt_id hz0

/-- After the zero, one, and self poles have been patched, the only remaining
singularity is the kernel pole at `z = 0`, and it is removable after subtracting
its polar part. -/
theorem hadamardRemainderWithOriginNaive_removable_at_origin
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    ∃ g_ext : ℂ → ℂ, AnalyticAt ℂ g_ext 0 ∧
      ∀ᶠ z in nhdsWithin 0 {0}ᶜ,
        hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ z = g_ext z := by
  obtain ⟨ψ, hψ_an, hψ_eq⟩ := weilIntegrand_residue_form_hadamardKernel_at_zero hs0
  have hzero_an :
      AnalyticAt ℂ (fun z => ∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (z - ρ)) 0 := by
    have hterm :
        ∀ ρ ∈ Z, AnalyticAt ℂ (fun z => hadamardZeroCoeff s ρ / (z - ρ)) 0 := by
      intro ρ hρ
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const)
        (sub_ne_zero_of_ne (nontrivialZero_ne_zero (hZ ρ hρ)).symm)
    have hsum := Finset.analyticAt_sum Z hterm
    convert hsum using 1
    funext z
    simp [Finset.sum_apply]
  have hone_an : AnalyticAt ℂ (fun z => hadamardOneCoeff s / (z - 1)) 0 := by
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (sub_ne_zero_of_ne zero_ne_one)
  have hself_an : AnalyticAt ℂ (fun z => hadamardSelfCoeff s / (z - s)) 0 := by
    exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (sub_ne_zero_of_ne hs0.symm)
  have h_notZ :
      ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) ({0}ᶜ), z ∉ Z := by
    have h_notZ_nhds : (↑Z : Set ℂ)ᶜ ∈ nhds (0 : ℂ) :=
      Z.finite_toSet.isClosed.isOpen_compl.mem_nhds (zero_not_mem_zeroFinset hZ)
    exact nhdsWithin_le_nhds h_notZ_nhds
  have h_ne_one :
      ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) ({0}ᶜ), z ≠ (1 : ℂ) := by
    have h_ne_one_nhds : {z : ℂ | z ≠ 1} ∈ nhds (0 : ℂ) :=
      isOpen_ne.mem_nhds (show (0 : ℂ) ≠ 1 by exact zero_ne_one)
    exact nhdsWithin_le_nhds h_ne_one_nhds
  have h_ne_self :
      ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) ({0}ᶜ), z ≠ s := by
    have h_ne_self_nhds : {z : ℂ | z ≠ s} ∈ nhds (0 : ℂ) := isOpen_ne.mem_nhds hs0.symm
    exact nhdsWithin_le_nhds h_ne_self_nhds
  have h_ne_zero :
      ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) ({0}ᶜ), z ≠ 0 := by
    exact self_mem_nhdsWithin
  refine ⟨fun z => ψ z + ∑ ρ ∈ Z, hadamardZeroCoeff s ρ / (z - ρ) -
      hadamardOneCoeff s / (z - 1) - hadamardSelfCoeff s / (z - s), ?_, ?_⟩
  · exact hψ_an.add hzero_an |>.sub hone_an |>.sub hself_an
  · filter_upwards [hψ_eq, h_notZ, h_ne_one, h_ne_self, h_ne_zero]
      with z hψ hzZ hz1 hzs hz0
    rw [hadamardRemainderWithOriginNaive, hadamardRemainderGlobal_off_poles hzZ hz1 hzs]
    unfold hadamardNaiveRemainder hadamardOriginCoeff
    rw [hψ]
    field_simp [hz0]
    ring

/-- Canonical analytic extension chosen at the origin after subtracting the
kernel pole. -/
noncomputable def hadamardChooseOrigin (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) : ℂ → ℂ :=
  Classical.choose (hadamardRemainderWithOriginNaive_removable_at_origin hs0 hs1 hsζ hZ)

private lemma hadamardChooseOrigin_spec (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    AnalyticAt ℂ (hadamardChooseOrigin s Z hs0 hs1 hsζ hZ) 0 ∧
      ∀ᶠ z in nhdsWithin 0 {0}ᶜ,
        hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ z =
          hadamardChooseOrigin s Z hs0 hs1 hsζ hZ z :=
  Classical.choose_spec (hadamardRemainderWithOriginNaive_removable_at_origin hs0 hs1 hsζ hZ)

/-- Fully patched Hadamard remainder, now with the origin pole removed as well. -/
noncomputable def hadamardRemainderWithOriginGlobal (s : ℂ) (Z : Finset ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) : ℂ → ℂ :=
  Function.update (hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ) 0
    ((hadamardChooseOrigin s Z hs0 hs1 hsζ hZ) 0)

theorem hadamardRemainderWithOriginGlobal_of_ne_zero {s : ℂ} {Z : Finset ℂ}
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} {hsζ : riemannZeta s ≠ 0}
    {hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros}
    {z : ℂ} (hz : z ≠ 0) :
    hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z =
      hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ z := by
  simp [hadamardRemainderWithOriginGlobal, Function.update_of_ne hz]

theorem hadamardRemainderWithOriginGlobal_analyticAt_origin {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros) :
    AnalyticAt ℂ (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) 0 := by
  set g0 := hadamardChooseOrigin s Z hs0 hs1 hsζ hZ with hg0_def
  have hg0_an : AnalyticAt ℂ g0 0 := (hadamardChooseOrigin_spec s Z hs0 hs1 hsζ hZ).1
  have hg0_eq :
      ∀ᶠ z in nhdsWithin 0 {0}ᶜ,
        hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ z = g0 z := by
    simpa [hg0_def] using (hadamardChooseOrigin_spec s Z hs0 hs1 hsζ hZ).2
  suffices hnhds : hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ =ᶠ[nhds 0] g0 by
    exact hg0_an.congr hnhds.symm
  have hg0_eq_nhds :
      ∀ᶠ z in nhds 0, z ≠ 0 →
        hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ z = g0 z := by
    rw [Filter.eventually_iff_exists_mem]
    rw [Filter.eventually_iff, mem_nhdsWithin] at hg0_eq
    obtain ⟨U, hU_open, h0U, hU_sub⟩ := hg0_eq
    refine ⟨U, hU_open.mem_nhds h0U, ?_⟩
    intro z hz hz0
    exact hU_sub ⟨hz, hz0⟩
  filter_upwards [hg0_eq_nhds] with z hz_eq
  by_cases hz0 : z = 0
  · subst hz0
    simp [hadamardRemainderWithOriginGlobal, hg0_def]
  · rw [hadamardRemainderWithOriginGlobal_of_ne_zero hz0]
    exact hz_eq hz0

theorem hadamardRemainderWithOriginGlobal_analyticAt_of_ne_zero {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {z : ℂ} (hz0 : z ≠ 0)
    (hz_an : AnalyticAt ℂ (hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ) z) :
    AnalyticAt ℂ (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) z := by
  have h_eq :
      hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ =ᶠ[nhds z]
        hadamardRemainderWithOriginNaive s Z hs0 hs1 hsζ hZ := by
    filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
    exact hadamardRemainderWithOriginGlobal_of_ne_zero hw
  exact hz_an.congr h_eq.symm

/-- Off `0 ∪ Z ∪ {1, s}`, the Hadamard integrand splits into all four polar
parts plus the origin-adjusted holomorphic remainder. -/
theorem weilIntegrand_hadamardKernel_eq_polar_plus_origin_global
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {z : ℂ} (hz0 : z ≠ 0) (hzZ : z ∉ Z) (hz1 : z ≠ 1) (hzs : z ≠ s) :
    weilIntegrand (hadamardKernel s) z =
      hadamardOriginCoeff / z +
        (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
        hadamardOneCoeff s / (z - 1) +
        hadamardSelfCoeff s / (z - s) +
        hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z := by
  calc
    weilIntegrand (hadamardKernel s) z =
        (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
          hadamardOneCoeff s / (z - 1) +
          hadamardSelfCoeff s / (z - s) +
          hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z := by
            exact weilIntegrand_hadamardKernel_eq_polar_plus_global hs0 hs1 hsζ hZ hzZ hz1 hzs
    _ =
        hadamardOriginCoeff / z +
          (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
          hadamardOneCoeff s / (z - 1) +
          hadamardSelfCoeff s / (z - s) +
          hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z := by
            rw [hadamardRemainderWithOriginGlobal_of_ne_zero hz0, hadamardRemainderWithOriginNaive]
            ring

/-- The origin-adjusted remainder is holomorphic on any closed rectangle once
the nontrivial zeros inside it are listed in `Z`. -/
theorem hadamardRemainderWithOriginGlobal_differentiableOn_rect
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    (σL σR T : ℝ) (hσord : σL ≤ σR)
    (hζ_ne_off_Z :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        z ≠ 1 → z ∉ Z → riemannZeta z ≠ 0) :
    DifferentiableOn ℂ (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ)
      (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) := by
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    have hdiff : DifferentiableAt ℂ (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) 0 :=
      (hadamardRemainderWithOriginGlobal_analyticAt_origin hs0 hs1 hsζ hZ).differentiableAt
    exact hdiff.differentiableWithinAt
  · by_cases hzs : z = s
    · subst hzs
      have hdiff : DifferentiableAt ℂ (hadamardRemainderWithOriginGlobal z Z hs0 hs1 hsζ hZ) z :=
        (hadamardRemainderWithOriginGlobal_analyticAt_of_ne_zero hs0 hs1 hsζ hZ hs0 <|
          hadamardRemainderWithOriginNaive_analyticAt_of_ne_zero hs0 hs1 hsζ hZ hs0 <|
            hadamardRemainderGlobal_analyticAt_self hs0 hs1 hsζ hZ).differentiableAt
      exact hdiff.differentiableWithinAt
    · by_cases hz1 : z = 1
      · subst hz1
        have hdiff : DifferentiableAt ℂ (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) 1 :=
          (hadamardRemainderWithOriginGlobal_analyticAt_of_ne_zero hs0 hs1 hsζ hZ one_ne_zero <|
            hadamardRemainderWithOriginNaive_analyticAt_of_ne_zero hs0 hs1 hsζ hZ one_ne_zero <|
              hadamardRemainderGlobal_analyticAt_one hs0 hs1 hsζ hZ).differentiableAt
        exact hdiff.differentiableWithinAt
      · by_cases hzZ : z ∈ Z
        · have hρ0 : z ≠ 0 := hz0
          have hdiff : DifferentiableAt ℂ (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) z :=
            (hadamardRemainderWithOriginGlobal_analyticAt_of_ne_zero hs0 hs1 hsζ hZ hρ0 <|
              hadamardRemainderWithOriginNaive_analyticAt_of_ne_zero hs0 hs1 hsζ hZ hρ0 <|
                hadamardRemainderGlobal_analyticAt_zero hs0 hs1 hsζ hZ hzZ).differentiableAt
          exact hdiff.differentiableWithinAt
        · have hζ_ne : riemannZeta z ≠ 0 := hζ_ne_off_Z z hz hz1 hzZ
          have hdiff : DifferentiableAt ℂ (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) z :=
            (hadamardRemainderWithOriginGlobal_analyticAt_of_ne_zero hs0 hs1 hsζ hZ hz0 <|
              hadamardRemainderWithOriginNaive_analyticAt_of_ne_zero hs0 hs1 hsζ hZ hz0 <|
                hadamardRemainderGlobal_analyticAt_off_poles hs0 hs1 hsζ hZ
                  hz0 hz1 hzZ hzs hζ_ne).differentiableAt
          exact hdiff.differentiableWithinAt

end Contour
end WeilPositivity
end ZD

end
