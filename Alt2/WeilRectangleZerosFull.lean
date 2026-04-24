import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.WeilRectangleZeros
import RequestProject.WeilFinalAssembly

open Complex Real Set Filter Topology

noncomputable section


namespace ZD.WeilPositivity.FinalAssembly

theorem nontrivialZerosInRectangle_finite_target_of_contains_critical_strip
    (σL σR T : ℝ) (_hσL : σL ≤ 0) (_hσR : 1 ≤ σR) :
    nontrivialZerosInRectangle_finite_target σL σR T := by
  unfold nontrivialZerosInRectangle_finite_target
  have hT' : (0 : ℝ) ≤ max T 0 := le_max_right _ _
  have hfin := ZD.nontrivialZeros_imBounded_finite (max T 0) hT'
  refine hfin.subset ?_
  intro ρ ⟨hNZ, _, _, hTneg, hTpos⟩
  refine ⟨hNZ, ?_⟩
  exact (abs_le.mpr ⟨hTneg.le, hTpos.le⟩).trans (le_max_left _ _)

theorem nontrivialZerosInRectangle_finite_target_holds_at_neg_one_two (T : ℝ) :
    nontrivialZerosInRectangle_finite_target (-1) 2 T :=
  nontrivialZerosInRectangle_finite_target_of_contains_critical_strip
    (-1) 2 T (by norm_num) (by norm_num)

/-- **Discharged unconditionally for arbitrary `σL σR T`.** Every nontrivial
zero has `0 < Re ρ < 1`, so the rectangle-contents set is a subset of the
height-bounded set `{ρ ∈ NontrivialZeros | |Im ρ| ≤ max T 0}`, which is finite
via `ZD.nontrivialZeros_imBounded_finite`. -/
theorem zeros_finite_in_rect_unconditional :
    ∀ σL σR T : ℝ, nontrivialZerosInRectangle_finite_target σL σR T := by
  intro σL σR T
  unfold nontrivialZerosInRectangle_finite_target
  have hT' : (0 : ℝ) ≤ max T 0 := le_max_right _ _
  have hfin := ZD.nontrivialZeros_imBounded_finite (max T 0) hT'
  refine hfin.subset ?_
  intro ρ ⟨hNZ, _, _, hTneg, hTpos⟩
  refine ⟨hNZ, ?_⟩
  exact (abs_le.mpr ⟨hTneg.le, hTpos.le⟩).trans (le_max_left _ _)

/-- **Convenience constructor: build `WeilFinalAssemblyBundle` from the three
remaining-unclosed fields.** Threads the two already-discharged partials
(`trivial_zero_residues_unconditional` in WFA, `zeros_finite_in_rect_unconditional`
here) internally, leaving only `horizontal_tails`, `arch_formula_global`, and
`weil_formula` as caller-supplied inputs. -/
theorem WeilFinalAssemblyBundle_of_three_remaining
    (h_horizontal : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      weilHorizontalTails_vanish_target β (-1 : ℝ) 2)
    (h_arch : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      Contour.WeilArchPrimeIdentityTarget_corrected β)
    (h_weil : ∀ β : ℝ, β ∈ Set.Ioo (0:ℝ) 1 →
      WeilExplicitFormula_pair_cosh_gauss_target β) :
    WeilFinalAssemblyBundle :=
  { horizontal_tails := h_horizontal
    trivial_zero_residues :=
      ZD.WeilPositivity.FinalAssembly.trivial_zero_residues_unconditional
    arch_formula_global := h_arch
    zeros_finite_in_rect := zeros_finite_in_rect_unconditional
    weil_formula := h_weil }

end ZD.WeilPositivity.FinalAssembly

end

#print axioms ZD.WeilPositivity.FinalAssembly.nontrivialZerosInRectangle_finite_target_holds_at_neg_one_two
#print axioms ZD.WeilPositivity.FinalAssembly.zeros_finite_in_rect_unconditional
#print axioms ZD.WeilPositivity.FinalAssembly.WeilFinalAssemblyBundle_of_three_remaining
