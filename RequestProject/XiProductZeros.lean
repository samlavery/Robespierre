import Mathlib
import RequestProject.XiProduct

/-!
# `xiProduct` is entire and its zero set coincides with nontrivial zeros of ζ

H3 of the Hadamard-track plan:

* **`xiProduct_differentiable`** — `xiProduct` is entire (i.e., differentiable on ℂ).
  Follows from `MultipliableLocallyUniformlyOn` + `TendstoLocallyUniformlyOn.differentiableOn`
  applied to the partial products, which are finite and differentiable.
* **`xiProduct_eq_zero_iff`** — `xiProduct z = 0` iff `z ∈ NontrivialZeros`.
  * If `z = ρ` for nontrivial ρ: the ρ-factor vanishes, hence product vanishes via
    `Multipliable.tprod_eq_mul_tprod_ite`.
  * If `z ∉ NontrivialZeros`: every factor is nonzero (`xiWeierstrassFactor`
    vanishes only at 1, i.e., `z/ρ = 1`), and the infinite product of
    `1 + f` is nonzero by `tprod_one_add_ne_zero_of_summable`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Set Filter Topology

noncomputable section

namespace ZD

/-- **`xiProduct` is entire**: follows from locally-uniform convergence of the
Weierstrass product + differentiability of each finite partial product. -/
theorem xiProduct_differentiable : Differentiable ℂ xiProduct := by
  intro z
  -- Unfold xiProduct to `∏' ρ, (1 + xiWeierstrassTerm ρ.val z)` and apply the locally-uniform
  -- limit theorem to the partial products.
  have h_univ_mem : z ∈ (Set.univ : Set ℂ) := mem_univ z
  have h_open : IsOpen (Set.univ : Set ℂ) := isOpen_univ
  have h_conv := xiWeierstrassProduct_multipliableLocallyUniformlyOn_univ
  have h_diffOn : DifferentiableOn ℂ xiProduct Set.univ := by
    apply (h_conv.hasProdLocallyUniformlyOn.differentiableOn ?_ h_open)
    -- Each partial product is differentiable on Set.univ.
    filter_upwards with s
    have h_each : ∀ ρ ∈ s,
        DifferentiableOn ℂ (fun x => 1 + xiWeierstrassTerm ρ.val x) Set.univ := by
      intro ρ _
      have hρ_ne : ρ.val ≠ 0 := by
        intro heq
        have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
        rw [heq] at hre
        simp at hre
      exact (one_add_xiWeierstrassTerm_differentiable hρ_ne).differentiableOn
    have := DifferentiableOn.finset_prod (u := s)
      (f := fun ρ => fun x => 1 + xiWeierstrassTerm ρ.val x) h_each
    convert this using 1
    funext x
    rw [Finset.prod_fn]
  exact (h_diffOn z h_univ_mem).differentiableAt (h_open.mem_nhds h_univ_mem)

#print axioms xiProduct_differentiable

/-- **xiProduct is continuous** — immediate. -/
theorem xiProduct_continuous : Continuous xiProduct :=
  xiProduct_differentiable.continuous

/-- **xiProduct is analytic on ℂ** — differentiability + open-set argument. -/
theorem xiProduct_analyticOnNhd_univ : AnalyticOnNhd ℂ xiProduct Set.univ :=
  xiProduct_differentiable.differentiableOn.analyticOnNhd isOpen_univ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Zero set of xiProduct
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Multipliability at each point**: the index-indexed product at every
`z ∈ ℂ` is `Multipliable`. -/
theorem xiProduct_multipliable (z : ℂ) :
    Multipliable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => 1 + xiWeierstrassTerm ρ.val z) :=
  xiWeierstrassProduct_multipliableLocallyUniformlyOn_univ.multipliable (mem_univ z)

/-- **Factor is nonzero at non-nontrivial-zero points**: `1 + xiWeierstrassTerm ρ z ≠ 0`
whenever `z ≠ ρ`. -/
theorem one_add_xiWeierstrassTerm_ne_zero_of_ne
    {ρ z : ℂ} (hρ : ρ ≠ 0) (h : z ≠ ρ) :
    1 + xiWeierstrassTerm ρ z ≠ 0 := by
  rw [one_add_xiWeierstrassTerm]
  unfold xiWeierstrassFactor
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  intro hsub
  have h_div_one : z / ρ = 1 := by linear_combination -hsub
  have h_z_eq : z = ρ := by
    have : z = (z / ρ) * ρ := by field_simp
    rw [this, h_div_one, one_mul]
  exact h h_z_eq

/-- **Product vanishes at nontrivial zeros**: if `ρ ∈ NontrivialZeros`, then
`xiProduct ρ = 0` since one factor vanishes.

Uses `Multipliable.tprod_eq_mul_tprod_ite` at index `ρ`. -/
theorem xiProduct_zero_of_mem_NontrivialZeros
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    xiProduct ρ = 0 := by
  have hρ_ne : ρ ≠ 0 := by
    intro heq
    have hre : (0 : ℝ) < ρ.re := hρ.1
    rw [heq] at hre
    simp at hre
  apply tprod_of_exists_eq_zero
  exact ⟨⟨ρ, hρ⟩, one_add_xiWeierstrassTerm_at_zero hρ_ne⟩

#print axioms xiProduct_zero_of_mem_NontrivialZeros

/-- **Product nonzero off nontrivial zeros**: if `z ∉ NontrivialZeros`, then
`xiProduct z ≠ 0`. All factors are nonzero and `Σ ‖term‖ < ∞`, so product is nonzero.

Uses `tprod_one_add_ne_zero_of_summable`. -/
theorem xiProduct_ne_zero_of_notMem_NontrivialZeros
    {z : ℂ} (hz : z ∉ NontrivialZeros) :
    xiProduct z ≠ 0 := by
  unfold xiProduct
  apply tprod_one_add_ne_zero_of_summable
  · -- Each factor nonzero: z ≠ ρ for all ρ ∈ NontrivialZeros.
    intro ρ
    have hρ_ne : ρ.val ≠ 0 := by
      intro heq
      have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
      rw [heq] at hre
      simp at hre
    apply one_add_xiWeierstrassTerm_ne_zero_of_ne hρ_ne
    intro heq
    exact hz (heq ▸ ρ.property)
  · -- Summable ‖xiWeierstrassTerm ρ z‖: uses H2's closed-ball bound at M = ‖z‖ + 1.
    set M : ℝ := ‖z‖ + 1 with hM_def
    have hM_pos : 0 < M := by rw [hM_def]; linarith [norm_nonneg z]
    have hz_in_ball : z ∈ Metric.closedBall (0 : ℂ) M := by
      rw [Metric.mem_closedBall, dist_zero_right, hM_def]; linarith
    have h_bd := xiWeierstrassTerm_closedBall_bound M hM_pos
    -- Majorant: 3 M² / ‖ρ‖².
    have h_summ : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        3 * M ^ 2 / ‖ρ.val‖ ^ 2) := by
      have := summable_inv_norm_sq_nontrivialZeros.mul_left (3 * M ^ 2)
      refine this.congr ?_
      intro ρ; show 3 * M ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2) = _; ring
    refine h_summ.of_norm_bounded_eventually ?_
    filter_upwards [h_bd] with ρ hρ_bd
    have h_bound_at_z : ‖xiWeierstrassTerm ρ.val z‖ ≤ 3 * M ^ 2 / ‖ρ.val‖ ^ 2 :=
      hρ_bd z hz_in_ball
    rw [Real.norm_of_nonneg (by positivity)]
    exact h_bound_at_z

#print axioms xiProduct_ne_zero_of_notMem_NontrivialZeros

/-- **Zero set of xiProduct** = nontrivial zeros of ζ. -/
theorem xiProduct_eq_zero_iff (z : ℂ) :
    xiProduct z = 0 ↔ z ∈ NontrivialZeros := by
  constructor
  · intro hxi
    by_contra h
    exact xiProduct_ne_zero_of_notMem_NontrivialZeros h hxi
  · exact xiProduct_zero_of_mem_NontrivialZeros

#print axioms xiProduct_eq_zero_iff

end ZD
