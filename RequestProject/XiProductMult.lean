import Mathlib
import RequestProject.XiOrderSummable
import RequestProject.XiWeierstrassFactor

/-!
# Multiplicity-indexed Weierstrass product `xiProductMult`

Reindexes the Weierstrass product by the multiset of nontrivial zeros: each
zero `ρ` appears `xiOrderNat ρ` times (with `xiOrderNat ρ = analyticOrderNatAt
riemannXi ρ`). This gives a product whose order of vanishing at each `ρ`
matches `riemannXi`'s exactly, enabling an entire zero-free quotient
`riemannXi / xiProductMult` (see H4 follow-up).

Index type: `MultiZeroIdx := Σ (ρ : {ρ // ρ ∈ NontrivialZeros}), Fin (xiOrderNat ρ.val)`.
Each `(ρ, k)` contributes the same factor `1 + xiWeierstrassTerm ρ.val z`, so
the product is `∏_ρ ((1-z/ρ)·exp(z/ρ))^{xiOrderNat ρ}`.

Summability/multipliability via `summable_xiOrderNat_div_norm_sq_nontrivialZeros`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Set Filter Topology

noncomputable section

namespace ZD

/-- Multiset index set: pairs `(ρ, k)` where `ρ` ∈ NontrivialZeros and
`k < xiOrderNat ρ.val`. -/
abbrev MultiZeroIdx : Type :=
  Σ (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros}), Fin (ZD.xiOrderNat ρ.val)

/-- **Multiplicity-indexed Weierstrass product.** Each zero `ρ` contributes
`xiOrderNat ρ` copies of the factor `(1 - z/ρ)·exp(z/ρ)`, matching the
classical Hadamard construction with multiset enumeration. -/
noncomputable def xiProductMult (z : ℂ) : ℂ :=
  ∏' p : MultiZeroIdx, (1 + xiWeierstrassTerm p.1.val z)

/-- **Summability of the multiplicity-indexed Weierstrass weights** on any
closed ball. The majorant `3M²/‖ρ‖²` for `‖z‖ ≤ M` and `‖ρ‖ ≥ M`, pulled
back through the sigma-index, sums to `3M² · Σ_ρ xiOrderNat ρ / ‖ρ‖² < ∞`. -/
theorem summable_multi_weierstrassTerm_bound (M : ℝ) (hM : 0 < M) :
    Summable (fun p : MultiZeroIdx => 3 * M ^ 2 / ‖p.1.val‖ ^ 2) := by
  -- Σ_{(ρ, k)} f(ρ) = Σ_ρ (xiOrderNat ρ) · f(ρ) for any f : ρ → ℝ.
  -- Equivalently: sigma-sum = sum-weighted-by-card-of-Fin.
  have h_summ_weighted :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (ZD.xiOrderNat ρ.val : ℝ) * (3 * M ^ 2 / ‖ρ.val‖ ^ 2)) := by
    have := (summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left (3 * M ^ 2)
    refine this.congr ?_
    intro ρ
    show 3 * M ^ 2 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
      (ZD.xiOrderNat ρ.val : ℝ) * (3 * M ^ 2 / ‖ρ.val‖ ^ 2)
    ring
  -- Use `Summable.sigma_of_nonneg` backwards — sigma summability from
  -- weighted base + each fiber bounded.
  rw [show (fun p : MultiZeroIdx => 3 * M ^ 2 / ‖p.1.val‖ ^ 2) =
      (fun p : MultiZeroIdx => 3 * M ^ 2 / ‖p.1.val‖ ^ 2) from rfl]
  -- Use `summable_sigma_of_nonneg`.
  apply (summable_sigma_of_nonneg (fun p => by positivity)).mpr
  refine ⟨fun ρ => ?_, ?_⟩
  · -- Each fiber is a finite sum (Fin is finite).
    exact Summable.of_finite
  · -- Outer sum equals the weighted one.
    refine h_summ_weighted.congr ?_
    intro ρ
    -- The fiber's tsum is over a constant (depends on ρ only, not the Fin index).
    show (ZD.xiOrderNat ρ.val : ℝ) * (3 * M ^ 2 / ‖ρ.val‖ ^ 2) =
      ∑' (_ : Fin (ZD.xiOrderNat ρ.val)), 3 * M ^ 2 / ‖ρ.val‖ ^ 2
    rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast
    ring

#print axioms summable_multi_weierstrassTerm_bound

/-- **Weierstrass term closed-ball bound** for multiplicity-indexed product:
for `z ∈ closedBall 0 M` and `‖p.1.val‖ ≥ M`, each term has the bound
`3M²/‖ρ‖²` (depends only on `p.1`). -/
theorem xiWeierstrassTerm_mult_closedBall_bound (M : ℝ) (hM : 0 < M) :
    ∀ᶠ p : MultiZeroIdx in cofinite,
      ∀ z ∈ Metric.closedBall (0 : ℂ) M,
        ‖xiWeierstrassTerm p.1.val z‖ ≤ 3 * M ^ 2 / ‖p.1.val‖ ^ 2 := by
  -- The set of "bad" indices: p with ‖p.1.val‖ < M.
  -- Since (a) finitely many ρ have ‖ρ‖ < M, and (b) each Fin (xiOrderNat ρ) is
  -- finite, the bad set is finite.
  have h_bad_fin :
      {p : MultiZeroIdx | ‖p.1.val‖ < M}.Finite := by
    -- Inject into the product `{ρ : ‖ρ‖ < M} × ℕ` (more practically, use Finset).
    -- The set of ρ with ‖ρ‖ < M is finite by NontrivialZeros_inter_closedBall_finite.
    have h_base_fin : {ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ < M}.Finite := by
      have h_ntz_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) M).Finite :=
        ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite M
      have h_image_fin :
          ((fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => ρ.val) ''
            {ρ | ‖ρ.val‖ < M}).Finite := by
        apply h_ntz_fin.subset
        intro w hw
        rcases hw with ⟨ρ, hρ_lt, hρ_eq⟩
        simp only [Set.mem_setOf_eq] at hρ_lt
        subst hρ_eq
        refine ⟨ρ.property, ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]; linarith
      exact h_image_fin.of_finite_image Subtype.val_injective.injOn
    -- The bad set is a subset of a finite biUnion.
    set bigFinset : Finset MultiZeroIdx :=
      h_base_fin.toFinset.attach.biUnion (fun ρ =>
        (Finset.univ : Finset (Fin (ZD.xiOrderNat ρ.val.val))).image (fun k =>
          (⟨ρ.val, k⟩ : MultiZeroIdx))) with hbig_def
    have h_subset : {p : MultiZeroIdx | ‖p.1.val‖ < M} ⊆ ↑bigFinset := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      have hp_in : p.1 ∈ h_base_fin.toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hp
      rw [Finset.mem_coe, hbig_def, Finset.mem_biUnion]
      refine ⟨⟨p.1, hp_in⟩, Finset.mem_attach _ _, ?_⟩
      rw [Finset.mem_image]
      refine ⟨p.2, Finset.mem_univ _, ?_⟩
      rfl
    exact bigFinset.finite_toSet.subset h_subset
  -- Cofinite: complement of finite set.
  filter_upwards [h_bad_fin.compl_mem_cofinite] with p hp
  have hp_ge_M : M ≤ ‖p.1.val‖ := by
    by_contra h; push_neg at h
    exact hp h
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  have hz_le_ρ : ‖z‖ ≤ ‖p.1.val‖ := le_trans hz hp_ge_M
  have hρ_ne : p.1.val ≠ 0 := by
    intro heq; rw [heq, norm_zero] at hp_ge_M; linarith
  have h_bd := norm_xiWeierstrassTerm_le hρ_ne hz_le_ρ
  -- Upgrade ‖z‖² to M².
  have hρ_sq_pos : (0 : ℝ) < ‖p.1.val‖ ^ 2 := by positivity
  calc ‖xiWeierstrassTerm p.1.val z‖
      ≤ 3 * ‖z‖ ^ 2 / ‖p.1.val‖ ^ 2 := h_bd
    _ ≤ 3 * M ^ 2 / ‖p.1.val‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ hρ_sq_pos.le
        have h_z_sq_le : ‖z‖ ^ 2 ≤ M ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg z) hz 2
        linarith

#print axioms xiWeierstrassTerm_mult_closedBall_bound

/-- **Multipliable on compact balls**: `∏ p, (1 + xiWeierstrassTerm p.1.val z)`
is uniformly convergent on `closedBall 0 M` for every `M > 0`. -/
theorem xiProductMult_multipliableUniformlyOn_closedBall (M : ℝ) (hM : 0 < M) :
    MultipliableUniformlyOn
      (fun p : MultiZeroIdx => fun z : ℂ => 1 + xiWeierstrassTerm p.1.val z)
      (Metric.closedBall (0 : ℂ) M) := by
  have h_summ := summable_multi_weierstrassTerm_bound M hM
  have h_bound := xiWeierstrassTerm_mult_closedBall_bound M hM
  apply Summable.multipliableUniformlyOn_one_add (isCompact_closedBall _ _) h_summ h_bound
  intro p
  have hρ_ne : p.1.val ≠ 0 := by
    intro heq
    have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
    rw [heq] at hre; simp at hre
  exact (xiWeierstrassTerm_differentiable hρ_ne).continuous.continuousOn

#print axioms xiProductMult_multipliableUniformlyOn_closedBall

/-- **Multipliable locally uniformly on ℂ**. -/
theorem xiProductMult_multipliableLocallyUniformlyOn_univ :
    MultipliableLocallyUniformlyOn
      (fun p : MultiZeroIdx => fun z : ℂ => 1 + xiWeierstrassTerm p.1.val z)
      Set.univ := by
  apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z _
  refine ⟨Metric.closedBall z 1, ?_, ?_⟩
  · exact nhdsWithin_le_nhds (Metric.closedBall_mem_nhds z zero_lt_one)
  · set M : ℝ := ‖z‖ + 1 with hM_def
    have hM_pos : 0 < M := by rw [hM_def]; linarith [norm_nonneg z]
    have h_sub : Metric.closedBall z 1 ⊆ Metric.closedBall (0 : ℂ) M := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall] at hw
      calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
            have := norm_sub_norm_le w z; linarith
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ 1 + ‖z‖ := by linarith
        _ = M := by rw [hM_def]; ring
    exact (xiProductMult_multipliableUniformlyOn_closedBall M hM_pos).mono h_sub

#print axioms xiProductMult_multipliableLocallyUniformlyOn_univ

-- ═══════════════════════════════════════════════════════════════════════════
-- § Differentiability and zero set of xiProductMult
-- ═══════════════════════════════════════════════════════════════════════════

/-- **`xiProductMult` is entire**. -/
theorem xiProductMult_differentiable : Differentiable ℂ xiProductMult := by
  intro z
  have h_open : IsOpen (Set.univ : Set ℂ) := isOpen_univ
  have h_conv := xiProductMult_multipliableLocallyUniformlyOn_univ
  have h_diffOn : DifferentiableOn ℂ xiProductMult Set.univ := by
    apply (h_conv.hasProdLocallyUniformlyOn.differentiableOn ?_ h_open)
    filter_upwards with s
    have h_each : ∀ p ∈ s,
        DifferentiableOn ℂ (fun x => 1 + xiWeierstrassTerm p.1.val x) Set.univ := by
      intro p _
      have hρ_ne : p.1.val ≠ 0 := by
        intro heq
        have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
        rw [heq] at hre; simp at hre
      exact (one_add_xiWeierstrassTerm_differentiable hρ_ne).differentiableOn
    have := DifferentiableOn.finset_prod (u := s)
      (f := fun p => fun x => 1 + xiWeierstrassTerm p.1.val x) h_each
    convert this using 1
    funext x
    rw [Finset.prod_fn]
  exact (h_diffOn z (Set.mem_univ z)).differentiableAt
    (h_open.mem_nhds (Set.mem_univ z))

#print axioms xiProductMult_differentiable

/-- **Multipliability at each point**. -/
theorem xiProductMult_multipliable (z : ℂ) :
    Multipliable (fun p : MultiZeroIdx => 1 + xiWeierstrassTerm p.1.val z) :=
  xiProductMult_multipliableLocallyUniformlyOn_univ.multipliable (Set.mem_univ z)

/-- **`xiProductMult` vanishes at nontrivial zeros**: take the index `(ρ, 0)`
where `0 < xiOrderNat ρ` (positivity from `xiOrderNat_pos_of_mem_NontrivialZeros`),
and the corresponding factor `1 + xiWeierstrassTerm ρ ρ = 0`. -/
theorem xiProductMult_zero_of_mem_NontrivialZeros
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    xiProductMult ρ = 0 := by
  have hρ_ne : ρ ≠ 0 := by
    intro heq
    have hre : (0 : ℝ) < ρ.re := hρ.1
    rw [heq] at hre; simp at hre
  have h_pos : 0 < ZD.xiOrderNat ρ := xiOrderNat_pos_of_mem_NontrivialZeros hρ
  apply tprod_of_exists_eq_zero
  refine ⟨⟨⟨ρ, hρ⟩, ⟨0, h_pos⟩⟩, ?_⟩
  exact one_add_xiWeierstrassTerm_at_zero hρ_ne

#print axioms xiProductMult_zero_of_mem_NontrivialZeros

/-- **`xiProductMult` is nonzero off nontrivial zeros**. All factors nonzero,
summable Σ‖term‖, so product nonzero. -/
theorem xiProductMult_ne_zero_of_notMem_NontrivialZeros
    {z : ℂ} (hz : z ∉ NontrivialZeros) :
    xiProductMult z ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable
  · intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq
      have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    apply one_add_xiWeierstrassTerm_ne_zero_of_ne hρ_ne
    intro heq
    exact hz (heq ▸ p.1.property)
  · -- Summable ‖xiWeierstrassTerm p.1.val z‖.
    set M : ℝ := ‖z‖ + 1 with hM_def
    have hM_pos : 0 < M := by rw [hM_def]; linarith [norm_nonneg z]
    have hz_in_ball : z ∈ Metric.closedBall (0 : ℂ) M := by
      rw [Metric.mem_closedBall, dist_zero_right, hM_def]; linarith
    have h_bd := xiWeierstrassTerm_mult_closedBall_bound M hM_pos
    have h_summ : Summable (fun p : MultiZeroIdx => 3 * M ^ 2 / ‖p.1.val‖ ^ 2) :=
      summable_multi_weierstrassTerm_bound M hM_pos
    refine h_summ.of_norm_bounded_eventually ?_
    filter_upwards [h_bd] with p hp_bd
    have h_at_z : ‖xiWeierstrassTerm p.1.val z‖ ≤ 3 * M ^ 2 / ‖p.1.val‖ ^ 2 :=
      hp_bd z hz_in_ball
    rw [Real.norm_of_nonneg (by positivity)]
    exact h_at_z

#print axioms xiProductMult_ne_zero_of_notMem_NontrivialZeros

/-- **Zero set of xiProductMult** = `NontrivialZeros`. -/
theorem xiProductMult_eq_zero_iff (z : ℂ) :
    xiProductMult z = 0 ↔ z ∈ NontrivialZeros := by
  constructor
  · intro hz
    by_contra h
    exact xiProductMult_ne_zero_of_notMem_NontrivialZeros h hz
  · exact xiProductMult_zero_of_mem_NontrivialZeros

#print axioms xiProductMult_eq_zero_iff

end ZD
