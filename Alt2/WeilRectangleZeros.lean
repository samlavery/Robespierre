import Mathlib
import RequestProject.ZetaZeroDefs

/-!
# Finite zero set of `ζ` in a critical-strip rectangle

For a closed rectangle `[σL, σR] × [-T, T]` with `0 < σL ≤ σR < 1` and `T ≥ 0`,
the set of nontrivial zeros of `ζ` lying inside the rectangle is finite.

## Chain

1. `ζ` is analytic on `{1}ᶜ` (via `differentiableAt_riemannZeta`) and not
   identically zero there (e.g. `ζ(2) ≠ 0`).
2. By `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`, the preimage of
   `{0}ᶜ` under `ζ` is codiscrete within `{1}ᶜ`.
3. By `codiscreteWithin_iff_locallyFiniteComplementWithin`, this means every
   point of `{1}ᶜ` has a neighbourhood meeting the zero set finitely often.
4. The closed rectangle is compact and disjoint from `{1}`, so compactness
   gives a finite subcover and the zero set inside the rectangle is finite.

No new axioms. Pure Mathlib + isolated-zero infrastructure.
-/

open Complex Real Set Filter Topology

noncomputable section

namespace ZD

/-- **ζ is analytic on `{1}ᶜ`**, as a neighbourhood-wise analyticity statement. -/
theorem riemannZeta_analyticOnNhd_compl_one :
    AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  have h_diff : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact h_diff.analyticOnNhd isOpen_compl_singleton

/-- **`{1}ᶜ` in `ℂ` is connected.** Punctured plane via rank-2 real VS. -/
theorem complOne_isConnected : IsConnected ({1}ᶜ : Set ℂ) := by
  have h_rank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact_mod_cast one_lt_two
  exact isConnected_compl_singleton_of_one_lt_rank h_rank (1 : ℂ)

/-- **Zeros of `ζ` form a codiscrete complement in `{1}ᶜ`.** Classical isolated-zeros
theorem applied to the concrete `ζ` situation. -/
theorem riemannZeta_nonzero_codiscreteWithin :
    (riemannZeta ⁻¹' ({0} : Set ℂ)ᶜ) ∈ codiscreteWithin ({1}ᶜ : Set ℂ) := by
  refine AnalyticOnNhd.preimage_zero_mem_codiscreteWithin
    riemannZeta_analyticOnNhd_compl_one (x := (2 : ℂ)) ?_ ?_ complOne_isConnected
  · exact riemannZeta_ne_zero_of_one_lt_re (by norm_num : (1:ℝ) < (2:ℂ).re)
  · simp

/-- **Local finiteness of zero set in `{1}ᶜ`.** Every `z ≠ 1` has a neighbourhood
intersecting the zero set of `ζ` in only finitely many points. -/
theorem exists_nhds_finite_inter_zeros {z : ℂ} (hz : z ≠ 1) :
    ∃ t ∈ nhds z, Set.Finite (t ∩ {w : ℂ | riemannZeta w = 0}) := by
  have hcodisc := riemannZeta_nonzero_codiscreteWithin
  rw [codiscreteWithin_iff_locallyFiniteComplementWithin] at hcodisc
  obtain ⟨t, ht_nhds, ht_fin⟩ := hcodisc z hz
  refine ⟨t, ht_nhds, ?_⟩
  -- t ∩ {1}ᶜ \ (ζ⁻¹' {0}ᶜ) = t ∩ {w : w ≠ 1 ∧ ζ w = 0}.
  -- t ∩ {w | ζ w = 0} = (t ∩ {w | ζ w = 0 ∧ w ≠ 1}) ∪ (t ∩ {1}) ⊆ ... ∪ {1}.
  have h_sub : t ∩ {w : ℂ | riemannZeta w = 0} ⊆
               (t ∩ (({1}ᶜ : Set ℂ) \ (riemannZeta ⁻¹' ({0} : Set ℂ)ᶜ))) ∪ {1} := by
    intro x ⟨hx_t, hx_zero⟩
    by_cases hx1 : x = 1
    · right; exact hx1
    · left
      refine ⟨hx_t, hx1, ?_⟩
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
      exact hx_zero
  exact (ht_fin.union (Set.finite_singleton 1)).subset h_sub

/-- **Finite zero set in a critical-strip rectangle.**
For `0 < σL ≤ σR < 1` and `T ≥ 0`, the set of `ρ ∈ NontrivialZeros` with
`σL ≤ Re ρ ≤ σR` and `|Im ρ| ≤ T` is finite. -/
theorem nontrivialZeros_in_rect_finite
    (σL σR T : ℝ) (hσL : 0 < σL) (hσR : σR < 1) (hσord : σL ≤ σR) (hT : 0 ≤ T) :
    {ρ : ℂ | ρ ∈ ZD.NontrivialZeros ∧ σL ≤ ρ.re ∧ ρ.re ≤ σR ∧ |ρ.im| ≤ T}.Finite := by
  -- Step 1: the closed rectangle is compact.
  set K : Set ℂ := {z : ℂ | σL ≤ z.re ∧ z.re ≤ σR ∧ |z.im| ≤ T} with hK_def
  have hK_compact : IsCompact K := by
    have hK_eq : K = (Set.Icc σL σR ×ℂ Set.Icc (-T) T) := by
      ext z
      simp only [K, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_setOf_eq, abs_le]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨h1, h2⟩, ?_, ?_⟩
        · linarith [h3.1]
        · linarith [h3.2]
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨h1, h2, h3, h4⟩
    rw [hK_eq]
    exact isCompact_Icc.reProdIm isCompact_Icc
  -- Step 2: K ⊂ {1}ᶜ (since σR < 1 forces z.re < 1, so z ≠ 1).
  have hK_sub : K ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz hz1
    obtain ⟨_, h2, _⟩ := hz
    rw [hz1] at h2
    simp at h2
    linarith
  -- Step 3: cover K by open nhds with finite-zero intersection.
  have h_nhds_cover : ∀ z ∈ K, ∃ U : Set ℂ, U ∈ nhds z ∧
      Set.Finite (U ∩ {w : ℂ | riemannZeta w = 0}) := fun z hz =>
    exists_nhds_finite_inter_zeros (hK_sub hz)
  choose U hU_nhds hU_fin using h_nhds_cover
  obtain ⟨I, hI_sub⟩ := hK_compact.elim_nhds_subcover' U hU_nhds
  -- Finite union of finite sets is finite.
  have h_zeros_fin : (K ∩ {w : ℂ | riemannZeta w = 0}).Finite := by
    have h_sub_union : K ∩ {w : ℂ | riemannZeta w = 0} ⊆
        ⋃ z ∈ I, (U (z : ℂ) z.2 ∩ {w : ℂ | riemannZeta w = 0}) := by
      intro w hw
      obtain ⟨hw_K, hw_zero⟩ := hw
      have hw_in_cover := hI_sub hw_K
      rw [Set.mem_iUnion₂] at hw_in_cover
      obtain ⟨z, hz_I, hw_U⟩ := hw_in_cover
      refine Set.mem_iUnion₂.mpr ⟨z, hz_I, hw_U, hw_zero⟩
    refine (Set.Finite.biUnion I.finite_toSet ?_).subset h_sub_union
    intro z _
    exact hU_fin (z : ℂ) z.2
  -- Target ⊆ K ∩ zeros.
  apply h_zeros_fin.subset
  intro ρ hρ
  exact ⟨⟨hρ.2.1, hρ.2.2.1, hρ.2.2.2⟩, hρ.1.2.2⟩

end ZD

end

#print axioms ZD.nontrivialZeros_in_rect_finite
