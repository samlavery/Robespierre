import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilContourMultiplicity
import RequestProject.WeilPoleAtOne
import RequestProject.WeilWindingIntegral
import RequestProject.WeilRectangleDecomposition
import RequestProject.WeilRectangleDecompositionMult
import RequestProject.WeilRectangleResidueSum
import RequestProject.WeilRectangleResidueSumFull
import RequestProject.WeilRectResidueDischarge
import RequestProject.WeilPairTestContinuity
import RequestProject.WeilPairTestMellinExtend
import RequestProject.WeilFinalAssembly
import RequestProject.ZetaBound

/-!
# Discharge of `rectangleResidueIdentity_target β` at σL = -1, σR = 2
-/

set_option maxHeartbeats 400000

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

open Contour

private theorem rectContourIntegral_congr'
    {σL σR T : ℝ} {f g : ℂ → ℂ}
    (h_bottom : ∀ x ∈ Set.uIcc σL σR, f (↑x + (-T : ℝ) * I) = g (↑x + (-T : ℝ) * I))
    (h_top : ∀ x ∈ Set.uIcc σL σR, f (↑x + (T : ℝ) * I) = g (↑x + (T : ℝ) * I))
    (h_right : ∀ y ∈ Set.uIcc (-T) T, f (↑σR + ↑y * I) = g (↑σR + ↑y * I))
    (h_left : ∀ y ∈ Set.uIcc (-T) T, f (↑σL + ↑y * I) = g (↑σL + ↑y * I)) :
    rectContourIntegral σL σR T f = rectContourIntegral σL σR T g := by
  unfold rectContourIntegral
  rw [intervalIntegral.integral_congr fun x hx => h_bottom x hx]
  rw [intervalIntegral.integral_congr fun x hx => h_top x hx]
  rw [intervalIntegral.integral_congr fun y hy => h_right y hy]
  rw [intervalIntegral.integral_congr fun y hy => h_left y hy]

private theorem bottom_edge_II_cont
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun x : ℝ => f (↑x + (-T : ℝ) * I)) MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro x hx
    constructor
    · simpa using hx
    · simp

private theorem top_edge_II_cont
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun x : ℝ => f (↑x + (T : ℝ) * I)) MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro x hx
    constructor
    · simpa using hx
    · simp

private theorem right_edge_II_cont
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun y : ℝ => f (↑σR + ↑y * I)) MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro y hy
    constructor
    · simp
    · simpa using hy

private theorem left_edge_II_cont
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun y : ℝ => f (↑σL + ↑y * I)) MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro y hy
    constructor
    · simp
    · simpa using hy

private theorem bottom_edge_II_pole
    {σL σR T : ℝ} (r p : ℂ) (hp_im : -T < p.im) :
    IntervalIntegrable (fun x : ℝ => r / ((x : ℂ) + (-T : ℝ) * I - p))
      MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro x _ hx0
    have him : (((x : ℂ) + (-T : ℝ) * I - p).im : ℝ) = -T - p.im := by simp
    rw [hx0] at him
    simp at him
    linarith

private theorem top_edge_II_pole
    {σL σR T : ℝ} (r p : ℂ) (hp_im : p.im < T) :
    IntervalIntegrable (fun x : ℝ => r / ((x : ℂ) + (T : ℝ) * I - p))
      MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro x _ hx0
    have him : (((x : ℂ) + (T : ℝ) * I - p).im : ℝ) = T - p.im := by simp
    rw [hx0] at him
    simp at him
    linarith

private theorem right_edge_II_pole
    {σR T : ℝ} (r p : ℂ) (hp_re : p.re < σR) :
    IntervalIntegrable (fun y : ℝ => r / ((σR : ℂ) + (y : ℂ) * I - p))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro y _ hy0
    have hre : (((σR : ℂ) + (y : ℂ) * I - p).re : ℝ) = σR - p.re := by simp
    rw [hy0] at hre
    simp at hre
    linarith

private theorem left_edge_II_pole
    {σL T : ℝ} (r p : ℂ) (hp_re : σL < p.re) :
    IntervalIntegrable (fun y : ℝ => r / ((σL : ℂ) + (y : ℂ) * I - p))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro y _ hy0
    have hre : (((σL : ℂ) + (y : ℂ) * I - p).re : ℝ) = σL - p.re := by simp
    rw [hy0] at hre
    simp at hre
    linarith

/-- **Zeta non-vanishing on `[-1,2] × [-T,T]` off `Z ∪ {1}`.** -/
private lemma zeta_ne_zero_on_rect_neg_one_two
    {T : ℝ} (_hT_pos : 0 < T) (hGood : goodHeight T)
    {Z : Finset ℂ}
    (hZ_complete : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ Z)
    {s : ℂ} (hs : s ∈ (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T))
    (hsZ : s ∉ Z) (_hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  have hs_re_mem : s.re ∈ Set.uIcc (-1 : ℝ) 2 := hs.1
  have hs_im_mem : s.im ∈ Set.uIcc (-T) T := hs.2
  have hσ_le : ((-1 : ℝ) ≤ 2) := by norm_num
  have hT_le : ((-T) ≤ T) := by linarith
  rw [Set.uIcc_of_le hσ_le] at hs_re_mem
  rw [Set.uIcc_of_le hT_le] at hs_im_mem
  obtain ⟨hs_re_lo, _hs_re_hi⟩ := hs_re_mem
  obtain ⟨hs_im_lo, hs_im_hi⟩ := hs_im_mem
  intro hζ0
  have h_not_triv : ∀ k : ℕ, s ≠ -2 * (↑k + 1) := by
    intro k hk
    have h_re : s.re = -2 * (↑k + 1) := by
      rw [hk]; simp
    have hbound : (-2 : ℝ) * (↑k + 1) ≤ -2 := by
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    linarith
  have h_bounds : 0 < s.re ∧ s.re < 1 :=
    riemannZeta_nontrivial_zero_re_bounds hζ0 h_not_triv
  have h_in_NZ : s ∈ NontrivialZeros := ⟨h_bounds.1, h_bounds.2, hζ0⟩
  have h_im_ne : s.im ≠ T ∧ s.im ≠ -T := hGood.1 s h_in_NZ
  have hs_im_lt : s.im < T := lt_of_le_of_ne hs_im_hi h_im_ne.1
  have hs_im_gt : -T < s.im := lt_of_le_of_ne hs_im_lo (fun h => h_im_ne.2 h.symm)
  have hs_re_lt_2 : s.re < 2 := by linarith [h_bounds.2]
  have hs_re_gt_neg1 : -1 < s.re := by linarith [h_bounds.1]
  exact hsZ (hZ_complete s h_in_NZ hs_re_gt_neg1 hs_re_lt_2 hs_im_gt hs_im_lt)

/-- **Top-level discharge of `rectangleResidueIdentity_target β` at
`σL = -1, σR = 2`** for the cosh-pair Gauss test `pairTestMellin β`. -/
theorem rectangleResidueIdentity_target_holds_neg_one_two
    (β : ℝ) (_hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    rectangleResidueIdentity_target β := by
  intro T hT hGood n Z hZ_mem hZ_complete
  set h : ℂ → ℂ := Contour.pairTestMellin β with hh_def
  have hT_pos : 0 < T := by linarith
  have hσLR : ((-1 : ℝ) : ℝ) < 2 := by norm_num
  have hZ_ne_one : ∀ ρ ∈ Z, ρ ≠ 1 := by
    intro ρ hρ heq
    obtain ⟨hNZ, _⟩ := hZ_mem ρ hρ
    obtain ⟨_, hlt1, _⟩ := hNZ
    rw [heq] at hlt1
    simp at hlt1
  have h1_not_Z : (1 : ℂ) ∉ Z := by
    intro hmem
    obtain ⟨hNZ, _⟩ := hZ_mem 1 hmem
    obtain ⟨_, hlt1, _⟩ := hNZ
    simp at hlt1
  have hh_an_at : ∀ s : ℂ, -4 < s.re → AnalyticAt ℂ h s := by
    intro s hs
    apply DifferentiableOn.analyticAt (s := {z | -4 < z.re})
    · intro z hz
      exact (Contour.pairTestMellin_differentiableAt_re_gt_neg_four β hz).differentiableWithinAt
    · exact IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) hs
  have hh1 : AnalyticAt ℂ h 1 := by
    apply hh_an_at
    show -4 < (1 : ℂ).re
    norm_num
  have hh_an_Z : ∀ ρ ∈ Z, AnalyticAt ℂ h ρ := by
    intro ρ hρ
    obtain ⟨_, hlo, _⟩ := hZ_mem ρ hρ
    apply hh_an_at
    linarith
  have hh_an_rect : ∀ s ∈ (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T),
      AnalyticAt ℂ h s := by
    intro s hs
    have hs_re_mem : s.re ∈ Set.uIcc (-1 : ℝ) 2 := hs.1
    have hσ_le : ((-1 : ℝ) ≤ 2) := by norm_num
    rw [Set.uIcc_of_le hσ_le] at hs_re_mem
    apply hh_an_at
    linarith [hs_re_mem.1]
  have hB : MultZeroBundle h Z n := by
    refine { ζ_an := ?_, ζ_zero := ?_, order_pos := ?_, order_eq := ?_, h_an := ?_ }
    · intro ρ hρ
      have hρ_ne_1 : ρ ≠ 1 := hZ_ne_one ρ hρ
      apply DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      · intro z hz
        exact (differentiableAt_riemannZeta hz).differentiableWithinAt
      · exact IsOpen.mem_nhds isOpen_ne hρ_ne_1
    · intro ρ hρ
      obtain ⟨hNZ, _⟩ := hZ_mem ρ hρ
      exact hNZ.2.2
    · intro ρ hρ
      obtain ⟨hNZ, _, _, _, _, hn_eq⟩ := hZ_mem ρ hρ
      obtain ⟨m, hm_ge, hm_eq⟩ :=
        analyticOrderAt_riemannZeta_nontrivialZero_pos_nat hNZ
      have hsame : (m : ℕ∞) = (n ρ : ℕ∞) := hm_eq.symm.trans hn_eq
      have hmeq : m = n ρ := by exact_mod_cast hsame
      rw [← hmeq]; exact hm_ge
    · intro ρ hρ
      obtain ⟨_, _, _, _, _, hn_eq⟩ := hZ_mem ρ hρ
      exact hn_eq
    · exact hh_an_Z
  have hζ_ne_off_Z_v1 :
      ∀ s ∈ (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T),
        s ∉ Z → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hsZ hs1
    exact zeta_ne_zero_on_rect_neg_one_two hT_pos hGood hZ_complete hs hsZ hs1
  have hg_diff :
      DifferentiableOn ℂ
        (weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z)
        (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T) :=
    weilRemainderGlobalFull_differentiableOn_rect_neg_one_two
      hB hZ_ne_one hh1 h1_not_Z hh_an_Z T hT_pos hh_an_rect hζ_ne_off_Z_v1
  have hg_cont :
      ContinuousOn
        (weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z)
        (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T) :=
    hg_diff.continuousOn
  let ι := Option {ρ : ℂ // ρ ∈ Z}
  let p : ι → ℂ := fun
    | none => (1 : ℂ)
    | some ⟨ρ, _⟩ => ρ
  let r : ι → ℂ := fun
    | none => h 1
    | some ⟨ρ, _⟩ => -(n ρ : ℂ) * h ρ
  have hp_re : ∀ i ∈ (Finset.univ : Finset ι),
      (-1 : ℝ) < (p i).re ∧ (p i).re < 2 := by
    intro i _
    cases i with
    | none =>
        refine ⟨?_, ?_⟩
        · show (-1 : ℝ) < (1 : ℂ).re
          simp
        · show (1 : ℂ).re < 2
          simp
    | some ρmem =>
        obtain ⟨ρ, hρ⟩ := ρmem
        obtain ⟨_, hlo, hhi, _, _, _⟩ := hZ_mem ρ hρ
        refine ⟨?_, ?_⟩
        · show (-1 : ℝ) < ρ.re; exact hlo
        · show ρ.re < 2; exact hhi
  have hp_im : ∀ i ∈ (Finset.univ : Finset ι),
      (-T) < (p i).im ∧ (p i).im < T := by
    intro i _
    cases i with
    | none =>
        refine ⟨?_, ?_⟩
        · show -T < (1 : ℂ).im
          simp; linarith
        · show (1 : ℂ).im < T
          simp; linarith
    | some ρmem =>
        obtain ⟨ρ, hρ⟩ := ρmem
        obtain ⟨_, _, _, hlo, hhi, _⟩ := hZ_mem ρ hρ
        refine ⟨?_, ?_⟩
        · show -T < ρ.im; exact hlo
        · show ρ.im < T; exact hhi
  let g := weilRemainderGlobalFull h Z n hB hZ_ne_one hh1 h1_not_Z hh_an_Z
  have h_polar_eq :
      ∀ z : ℂ, z ∉ Z → z ≠ 1 →
        weilIntegrand h z =
          (∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) + g z := by
    intro z hzZ hz1
    have hEq := weilIntegrand_eq_polar_plus_global_full
      (h := h) (Z := Z) (order := n) hB hZ_ne_one hh1 h1_not_Z hh_an_Z hzZ hz1
    rw [hEq]
    have hsum_opt :
        (∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) =
          r none / (z - p none) +
            ∑ i : {ρ : ℂ // ρ ∈ Z}, r (some i) / (z - p (some i)) := by
      classical
      exact Fintype.sum_option (fun i => r i / (z - p i))
    rw [hsum_opt]
    have hrp_none : r none / (z - p none) = h 1 / (z - 1) := rfl
    rw [hrp_none]
    have h_some_body :
        ∀ i : {ρ : ℂ // ρ ∈ Z},
          r (some i) / (z - p (some i)) = -(n i.val : ℂ) * h i.val / (z - i.val) := by
      rintro ⟨ρ, hρ⟩
      rfl
    rw [Finset.sum_congr rfl (fun i _ => h_some_body i)]
    have h_attach :
        (∑ i : {ρ : ℂ // ρ ∈ Z}, -(n i.val : ℂ) * h i.val / (z - i.val)) =
          ∑ ρ ∈ Z, -(n ρ : ℂ) * h ρ / (z - ρ) := by
      classical
      rw [show (Finset.univ : Finset {ρ : ℂ // ρ ∈ Z}) = Z.attach from rfl]
      exact Z.sum_attach (fun ρ => -(n ρ : ℂ) * h ρ / (z - ρ))
    rw [h_attach]
  have h_pole_b : ∀ i ∈ (Finset.univ : Finset ι),
      IntervalIntegrable
        (fun x : ℝ => r i / ((x : ℂ) + (-T : ℝ) * I - p i))
        MeasureTheory.volume (-1 : ℝ) 2 := by
    intro i hi
    exact bottom_edge_II_pole (r i) (p i) (hp_im i hi).1
  have h_pole_t : ∀ i ∈ (Finset.univ : Finset ι),
      IntervalIntegrable
        (fun x : ℝ => r i / ((x : ℂ) + (T : ℝ) * I - p i))
        MeasureTheory.volume (-1 : ℝ) 2 := by
    intro i hi
    exact top_edge_II_pole (r i) (p i) (hp_im i hi).2
  have h_pole_r : ∀ i ∈ (Finset.univ : Finset ι),
      IntervalIntegrable
        (fun y : ℝ => r i / (((2 : ℝ) : ℂ) + (y : ℂ) * I - p i))
        MeasureTheory.volume (-T) T := by
    intro i hi
    exact right_edge_II_pole (σR := (2 : ℝ)) (T := T) (r i) (p i) (hp_re i hi).2
  have h_pole_l : ∀ i ∈ (Finset.univ : Finset ι),
      IntervalIntegrable
        (fun y : ℝ => r i / (((-1 : ℝ) : ℂ) + (y : ℂ) * I - p i))
        MeasureTheory.volume (-T) T := by
    intro i hi
    exact left_edge_II_pole (σL := (-1 : ℝ)) (T := T) (r i) (p i) (hp_re i hi).1
  have hsum_b :
      IntervalIntegrable
        (fun x : ℝ => ∑ i ∈ (Finset.univ : Finset ι), r i /
            ((x : ℂ) + (-T : ℝ) * I - p i))
        MeasureTheory.volume (-1 : ℝ) 2 := by
    classical
    let F : ι → ℝ → ℂ := fun i x =>
      r i / ((x : ℂ) + (-T : ℝ) * I - p i)
    have hind :
        ∀ t : Finset ι,
          IntervalIntegrable (fun x : ℝ => Finset.sum t (fun i => F i x))
            MeasureTheory.volume (-1 : ℝ) 2 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_b i (by simp)) ih
    simpa [F] using hind (Finset.univ : Finset ι)
  have hsum_t :
      IntervalIntegrable
        (fun x : ℝ => ∑ i ∈ (Finset.univ : Finset ι), r i /
            ((x : ℂ) + (T : ℝ) * I - p i))
        MeasureTheory.volume (-1 : ℝ) 2 := by
    classical
    let F : ι → ℝ → ℂ := fun i x =>
      r i / ((x : ℂ) + (T : ℝ) * I - p i)
    have hind :
        ∀ t : Finset ι,
          IntervalIntegrable (fun x : ℝ => Finset.sum t (fun i => F i x))
            MeasureTheory.volume (-1 : ℝ) 2 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_t i (by simp)) ih
    simpa [F] using hind (Finset.univ : Finset ι)
  have hsum_r :
      IntervalIntegrable
        (fun y : ℝ => ∑ i ∈ (Finset.univ : Finset ι), r i /
            (((2 : ℝ) : ℂ) + (y : ℂ) * I - p i))
        MeasureTheory.volume (-T) T := by
    classical
    let F : ι → ℝ → ℂ := fun i y =>
      r i / (((2 : ℝ) : ℂ) + (y : ℂ) * I - p i)
    have hind :
        ∀ t : Finset ι,
          IntervalIntegrable (fun y : ℝ => Finset.sum t (fun i => F i y))
            MeasureTheory.volume (-T) T := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_r i (by simp)) ih
    simpa [F] using hind (Finset.univ : Finset ι)
  have hsum_l :
      IntervalIntegrable
        (fun y : ℝ => ∑ i ∈ (Finset.univ : Finset ι), r i /
            (((-1 : ℝ) : ℂ) + (y : ℂ) * I - p i))
        MeasureTheory.volume (-T) T := by
    classical
    let F : ι → ℝ → ℂ := fun i y =>
      r i / (((-1 : ℝ) : ℂ) + (y : ℂ) * I - p i)
    have hind :
        ∀ t : Finset ι,
          IntervalIntegrable (fun y : ℝ => Finset.sum t (fun i => F i y))
            MeasureTheory.volume (-T) T := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_l i (by simp)) ih
    simpa [F] using hind (Finset.univ : Finset ι)
  have hrem_b :
      IntervalIntegrable (fun x : ℝ => g (↑x + (-T : ℝ) * I))
        MeasureTheory.volume (-1 : ℝ) 2 :=
    bottom_edge_II_cont hg_cont
  have hrem_t :
      IntervalIntegrable (fun x : ℝ => g (↑x + (T : ℝ) * I))
        MeasureTheory.volume (-1 : ℝ) 2 :=
    top_edge_II_cont hg_cont
  have hrem_r :
      IntervalIntegrable (fun y : ℝ => g (((2 : ℝ) : ℂ) + ↑y * I))
        MeasureTheory.volume (-T) T :=
    right_edge_II_cont (σL := (-1 : ℝ)) (σR := (2 : ℝ)) (T := T) hg_cont
  have hrem_l :
      IntervalIntegrable (fun y : ℝ => g (((-1 : ℝ) : ℂ) + ↑y * I))
        MeasureTheory.volume (-T) T :=
    left_edge_II_cont (σL := (-1 : ℝ)) (σR := (2 : ℝ)) (T := T) hg_cont
  have h_poleSum_eq :
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => ∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) =
        ∑ i ∈ (Finset.univ : Finset ι),
          rectContourIntegral (-1 : ℝ) 2 T (fun z => r i / (z - p i)) :=
    rectContourIntegral_finset_sum (-1 : ℝ) 2 T
      (Finset.univ : Finset ι)
      (fun i z => r i / (z - p i))
      h_pole_b h_pole_t h_pole_r h_pole_l
  have h_integral_eq :
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => (∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) + g z) =
        (∑ i ∈ (Finset.univ : Finset ι),
          rectContourIntegral (-1 : ℝ) 2 T (fun z => r i / (z - p i))) +
          rectContourIntegral (-1 : ℝ) 2 T g := by
    calc
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => (∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) + g z) =
          rectContourIntegral (-1 : ℝ) 2 T
            (fun z => ∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) +
            rectContourIntegral (-1 : ℝ) 2 T g :=
        rectContourIntegral_add (-1 : ℝ) 2 T
          (fun z => ∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i))
          g hsum_b hrem_b hsum_t hrem_t hsum_r hrem_r hsum_l hrem_l
      _ =
          (∑ i ∈ (Finset.univ : Finset ι),
            rectContourIntegral (-1 : ℝ) 2 T (fun z => r i / (z - p i))) +
            rectContourIntegral (-1 : ℝ) 2 T g := by
              rw [h_poleSum_eq]
  have hmain := rectResidueTheorem_multi_pole_unconditional
      (σL := (-1 : ℝ)) (σR := 2) (T := T) hσLR hT_pos
      (poles := (Finset.univ : Finset ι))
      (p := p) (r := r) (g := g)
      hp_re hp_im hg_diff h_integral_eq
  have h_f_eq_decomp :
      rectContourIntegral (-1 : ℝ) 2 T (weilIntegrand h) =
        rectContourIntegral (-1 : ℝ) 2 T
          (fun z => (∑ i ∈ (Finset.univ : Finset ι), r i / (z - p i)) + g z) := by
    apply rectContourIntegral_congr'
    · intro x _hx
      have hx0 : ((x : ℂ) + (-T : ℝ) * I) ∉ Z := by
        intro hmem
        obtain ⟨_, _, _, hlo, _, _⟩ := hZ_mem _ hmem
        have him : (((x : ℂ) + (-T : ℝ) * I).im : ℝ) = -T := by simp
        have hk := hlo
        rw [him] at hk
        linarith
      have hx1 : ((x : ℂ) + (-T : ℝ) * I) ≠ 1 := by
        intro heq
        have himeq : ((x : ℂ) + (-T : ℝ) * I).im = (1 : ℂ).im := by rw [heq]
        simp at himeq
        linarith
      exact h_polar_eq _ hx0 hx1
    · intro x _hx
      have hx0 : ((x : ℂ) + (T : ℝ) * I) ∉ Z := by
        intro hmem
        obtain ⟨_, _, _, _, hhi, _⟩ := hZ_mem _ hmem
        have him : (((x : ℂ) + (T : ℝ) * I).im : ℝ) = T := by simp
        have hk := hhi
        rw [him] at hk
        linarith
      have hx1 : ((x : ℂ) + (T : ℝ) * I) ≠ 1 := by
        intro heq
        have himeq : ((x : ℂ) + (T : ℝ) * I).im = (1 : ℂ).im := by rw [heq]
        simp at himeq
        linarith
      exact h_polar_eq _ hx0 hx1
    · intro y _hy
      have hy0 : (((2 : ℝ) : ℂ) + (y : ℂ) * I) ∉ Z := by
        intro hmem
        obtain ⟨_, _, hhi, _, _, _⟩ := hZ_mem _ hmem
        have hre : ((((2 : ℝ) : ℂ) + (y : ℂ) * I).re : ℝ) = 2 := by simp
        have hk := hhi
        rw [hre] at hk
        linarith
      have hy1 : (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1 := by
        intro heq
        have hreeq : (((2 : ℝ) : ℂ) + (y : ℂ) * I).re = (1 : ℂ).re := by rw [heq]
        norm_num at hreeq
      exact h_polar_eq _ hy0 hy1
    · intro y _hy
      have hy0 : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ∉ Z := by
        intro hmem
        obtain ⟨_, hlo, _, _, _, _⟩ := hZ_mem _ hmem
        have hre : ((((-1 : ℝ) : ℂ) + (y : ℂ) * I).re : ℝ) = -1 := by simp
        have hk := hlo
        rw [hre] at hk
        linarith
      have hy1 : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1 := by
        intro heq
        have hreeq : (((-1 : ℝ) : ℂ) + (y : ℂ) * I).re = (1 : ℂ).re := by rw [heq]
        norm_num at hreeq
      exact h_polar_eq _ hy0 hy1
  have h_weil_eq :
      rectContourIntegral (-1 : ℝ) 2 T (weilIntegrand h) =
        2 * ↑Real.pi * I *
          (∑ i ∈ (Finset.univ : Finset ι), r i) := by
    rw [h_f_eq_decomp]
    exact hmain
  have h_sum_r :
      (∑ i ∈ (Finset.univ : Finset ι), r i) =
        h 1 - ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * h ρ := by
    classical
    have hsum_opt :
        (∑ i ∈ (Finset.univ : Finset ι), r i) =
          r none + ∑ i : {ρ : ℂ // ρ ∈ Z}, r (some i) :=
      Fintype.sum_option (fun i => r i)
    rw [hsum_opt]
    have hrn : r none = h 1 := rfl
    rw [hrn]
    have h_some_body : ∀ i : {ρ : ℂ // ρ ∈ Z},
        r (some i) = -(n i.val : ℂ) * h i.val := by
      rintro ⟨ρ, hρ⟩
      rfl
    rw [Finset.sum_congr rfl (fun i _ => h_some_body i)]
    have h_attach :
        (∑ i : {ρ : ℂ // ρ ∈ Z}, -(n i.val : ℂ) * h i.val) =
          ∑ ρ ∈ Z, -(n ρ : ℂ) * h ρ := by
      rw [show (Finset.univ : Finset {ρ : ℂ // ρ ∈ Z}) = Z.attach from rfl]
      exact Z.sum_attach (fun ρ => -(n ρ : ℂ) * h ρ)
    rw [h_attach]
    have hconv : (∑ ρ ∈ Z, -(n ρ : ℂ) * h ρ) =
        -(∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * h ρ) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ρ _
      push_cast
      ring
    rw [hconv]
    ring
  rw [h_weil_eq, h_sum_r]

#print axioms rectangleResidueIdentity_target_holds_neg_one_two

end FinalAssembly
end WeilPositivity
end ZD

end
