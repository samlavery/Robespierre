import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.WeilRectangleZeros

/-!
# Helper lemmas for nontrivial-zero height bounds

Split out from `WeilRectangleZerosFull.lean` so `WeilFinalAssembly.lean` can
import them without creating a cyclic import (the original WRZF imports WFA
for bundle targets).

Contents:
- `riemannZeta_ne_zero_punctured_nhd_one` — ζ nonzero in a punctured nbhd of 1.
- `exists_nhds_one_finite_inter_zeros` — punctured nbhd of 1 has finite
  intersection with ζ-zero set.
- `nontrivialZeros_imBounded_finite` — `{ρ ∈ NontrivialZeros : |Im ρ| ≤ T}` is
  finite for each `T ≥ 0`.
- `exists_goodHeight_ge` — good heights (avoiding zero imaginary parts) are
  cofinite in bounded intervals; for any `A`, there's `T ≥ A` that's a good
  height.
-/

open Complex Real Set Filter Topology

noncomputable section

namespace ZD

theorem riemannZeta_ne_zero_punctured_nhd_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
  have h := riemannZeta_residue_one
  have hne : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
    h.eventually (isOpen_compl_singleton.mem_nhds (by norm_num : (1:ℂ) ≠ 0))
  filter_upwards [hne] with s hs hzero
  apply hs
  rw [hzero, mul_zero]

theorem exists_nhds_one_finite_inter_zeros :
    ∃ U ∈ nhds (1 : ℂ), Set.Finite (U ∩ {w : ℂ | riemannZeta w = 0}) := by
  have hev := riemannZeta_ne_zero_punctured_nhd_one
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨Metric.ball (1 : ℂ) ε, Metric.ball_mem_nhds _ hε, ?_⟩
  refine (Set.finite_singleton (1 : ℂ)).subset ?_
  intro w ⟨hw_ball, hw_zero⟩
  by_contra hw1
  exact hball hw_ball hw1 hw_zero

theorem nontrivialZeros_imBounded_finite (T : ℝ) (hT : 0 ≤ T) :
    {ρ : ℂ | ρ ∈ ZD.NontrivialZeros ∧ |ρ.im| ≤ T}.Finite := by
  set K : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T} with hK_def
  have hK_compact : IsCompact K := by
    have hK_eq : K = (Set.Icc (0:ℝ) 1 ×ℂ Set.Icc (-T) T) := by
      ext z
      simp only [K, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_setOf_eq, abs_le]
      refine ⟨fun ⟨h1,h2,h3⟩ => ⟨⟨h1,h2⟩, by linarith [h3.1], by linarith [h3.2]⟩, ?_⟩
      rintro ⟨⟨h1,h2⟩,h3,h4⟩; exact ⟨h1,h2,h3,h4⟩
    rw [hK_eq]; exact isCompact_Icc.reProdIm isCompact_Icc
  have h_cover : ∀ z ∈ K, ∃ U : Set ℂ, U ∈ nhds z ∧
      Set.Finite (U ∩ {w : ℂ | riemannZeta w = 0}) := by
    intro z _
    by_cases hz1 : z = 1
    · subst hz1; exact exists_nhds_one_finite_inter_zeros
    · exact exists_nhds_finite_inter_zeros hz1
  choose U hU_nhds hU_fin using h_cover
  obtain ⟨I, hI_sub⟩ := hK_compact.elim_nhds_subcover' U hU_nhds
  have h_zeros_fin : (K ∩ {w : ℂ | riemannZeta w = 0}).Finite := by
    have h_sub : K ∩ {w : ℂ | riemannZeta w = 0} ⊆
        ⋃ z ∈ I, (U (z : ℂ) z.2 ∩ {w : ℂ | riemannZeta w = 0}) := by
      intro w ⟨hw_K, hw_zero⟩
      obtain ⟨z, hz_I, hw_U⟩ := Set.mem_iUnion₂.mp (hI_sub hw_K)
      exact Set.mem_iUnion₂.mpr ⟨z, hz_I, hw_U, hw_zero⟩
    refine (Set.Finite.biUnion I.finite_toSet ?_).subset h_sub
    intro z _; exact hU_fin (z : ℂ) z.2
  refine h_zeros_fin.subset ?_
  intro ρ ⟨⟨hre_pos, hre_lt, hζ⟩, himT⟩
  exact ⟨⟨hre_pos.le, hre_lt.le, himT⟩, hζ⟩

/-- **Good-height existence.** For any real `A`, there exists `T ≥ A` such that
no nontrivial zero of ζ has imaginary part `±T`. The set of bad heights is
finite in any bounded interval (by `nontrivialZeros_imBounded_finite`), so
the complement is dense. -/
theorem exists_goodHeight_ge (A : ℝ) :
    ∃ T : ℝ, A ≤ T ∧ ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.im ≠ T ∧ ρ.im ≠ -T := by
  -- Work over [|A|+1, |A|+2] so both T and -T lie in [-(|A|+2), |A|+2],
  -- keeping finitely many candidate bad heights for both sign conventions.
  set B : ℝ := |A| + 2 with hB_def
  have hB_ge_A : A ≤ B := by rw [hB_def]; have := le_abs_self A; linarith
  have hB_pos : 0 < B := by rw [hB_def]; have := abs_nonneg A; linarith
  have hfin := nontrivialZeros_imBounded_finite B hB_pos.le
  set S : Set ℝ :=
      ((fun ρ : ℂ => ρ.im) '' {ρ | ρ ∈ ZD.NontrivialZeros ∧ |ρ.im| ≤ B}) ∪
      ((fun ρ : ℂ => -ρ.im) '' {ρ | ρ ∈ ZD.NontrivialZeros ∧ |ρ.im| ≤ B})
  have hS_fin : S.Finite := (hfin.image _).union (hfin.image _)
  -- Pick T ∈ [|A|+1, B] \ S. This interval is infinite and minus finite is nonempty.
  set lo : ℝ := |A| + 1 with hlo_def
  have hlo_lt_B : lo < B := by rw [hlo_def, hB_def]; linarith
  have hIcc_inf : (Set.Icc lo B).Infinite :=
    (Set.Ioo_infinite hlo_lt_B).mono (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  obtain ⟨T, hT_Icc, hT_notS⟩ : (Set.Icc lo B \ S).Nonempty :=
    (hIcc_inf.diff hS_fin).nonempty
  have hT_ge_A : A ≤ T := by
    have h1 : A ≤ lo := by rw [hlo_def]; have := le_abs_self A; linarith
    linarith [hT_Icc.1]
  have hT_nn : 0 ≤ T := by
    have : 0 ≤ lo := by rw [hlo_def]; have := abs_nonneg A; linarith
    linarith [hT_Icc.1]
  have hT_le_B : T ≤ B := hT_Icc.2
  have hnegT_abs_le_B : |(-T)| ≤ B := by rw [abs_neg, abs_of_nonneg hT_nn]; exact hT_le_B
  have hT_abs_le_B : |T| ≤ B := by rw [abs_of_nonneg hT_nn]; exact hT_le_B
  refine ⟨T, hT_ge_A, fun ρ hρ => ⟨?_, ?_⟩⟩
  · intro h_eq
    apply hT_notS
    left
    refine ⟨ρ, ⟨hρ, ?_⟩, h_eq⟩
    rw [h_eq]; exact hT_abs_le_B
  · intro h_eq
    apply hT_notS
    right
    refine ⟨ρ, ⟨hρ, ?_⟩, ?_⟩
    · rw [h_eq]; exact hnegT_abs_le_B
    · show -ρ.im = T; rw [h_eq]; ring

end ZD

end
