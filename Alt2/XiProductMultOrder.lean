import Mathlib
import RequestProject.XiProductMult
import RequestProject.XiHadamardQuotient

/-!
# Order matching: `analyticOrderAt xiProductMult ρ = xiOrderNat ρ`

The key technical lemma for the unconditional Hadamard chain. Splitting the
multiplicity-indexed Weierstrass product into the ρ-fiber (giving a zero of
order `xiOrderNat ρ`) and the rest (multipliable + nonzero at `z = ρ`).
-/

open Complex Set Filter Topology

set_option maxHeartbeats 800000

noncomputable section

namespace ZD

/-- **Closed form of xiProductMult via sigma split**: each nontrivial zero
ρ' contributes the factor `(1 + xiWeierstrassTerm ρ'.val z)^{xiOrderNat ρ'.val}`. -/
theorem xiProductMult_eq_tprod_pow (z : ℂ) :
    xiProductMult z =
    ∏' ρ' : {ρ' : ℂ // ρ' ∈ NontrivialZeros},
      (1 + xiWeierstrassTerm ρ'.val z) ^ (ZD.xiOrderNat ρ'.val) := by
  unfold xiProductMult
  have h_mult := xiProductMult_multipliable z
  rw [Multipliable.tprod_sigma' (fun b => Multipliable.of_finite) h_mult]
  apply tprod_congr
  intro ρ'
  show ∏' (_ : Fin (ZD.xiOrderNat ρ'.val)), (1 + xiWeierstrassTerm ρ'.val z) =
    (1 + xiWeierstrassTerm ρ'.val z) ^ (ZD.xiOrderNat ρ'.val)
  rw [tprod_eq_prod (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)]
  simp [Finset.prod_const]

/-- `fun w => 1 + xiWeierstrassTerm ρ w` is analytic everywhere. -/
theorem analyticAt_xiWeierstrassFactor (ρ z : ℂ) :
    AnalyticAt ℂ (fun w => 1 + xiWeierstrassTerm ρ w) z := by
  unfold xiWeierstrassTerm xiWeierstrassFactor
  show AnalyticAt ℂ (fun w => 1 + ((1 - w / ρ) * Complex.exp (w / ρ) - 1)) z
  have h_id : AnalyticAt ℂ (fun w : ℂ => w / ρ) z := by
    have : (fun w : ℂ => w / ρ) = (fun w : ℂ => w * ρ⁻¹) := by funext w; ring
    rw [this]; exact analyticAt_id.mul analyticAt_const
  have h_lin : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) - w / ρ) z :=
    analyticAt_const.sub h_id
  have h_exp : AnalyticAt ℂ (fun w : ℂ => Complex.exp (w / ρ)) z := h_id.cexp
  have h_prod : AnalyticAt ℂ (fun w : ℂ => (1 - w/ρ) * Complex.exp (w/ρ)) z :=
    h_lin.mul h_exp
  exact analyticAt_const.add (h_prod.sub analyticAt_const)

/-- `analyticOrderAt (fun w => 1 + xiWeierstrassTerm ρ w) ρ = 1` for nontrivial zeros `ρ`.
Factor = `(1-z/ρ)·exp(z/ρ) = -(z-ρ)/ρ · exp(z/ρ)`, so `factor = (z-ρ)·g(z)` with
`g(ρ) = -exp(1)/ρ ≠ 0`. -/
theorem analyticOrderAt_xiWeierstrassFactor_eq_one
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    analyticOrderAt (fun w => 1 + xiWeierstrassTerm ρ w) ρ = 1 := by
  have hρ_ne : ρ ≠ 0 := by
    intro heq
    have : (0 : ℝ) < ρ.re := hρ.1
    rw [heq] at this; simp at this
  have h_anal : AnalyticAt ℂ (fun w => 1 + xiWeierstrassTerm ρ w) ρ :=
    analyticAt_xiWeierstrassFactor ρ ρ
  -- factor w = -(w - ρ)/ρ · exp(w/ρ), so g(w) = -exp(w/ρ)/ρ.
  set g : ℂ → ℂ := fun w => -Complex.exp (w / ρ) / ρ with hg_def
  have hg_anal : AnalyticAt ℂ g ρ := by
    show AnalyticAt ℂ (fun w => -Complex.exp (w / ρ) / ρ) ρ
    have h_id : AnalyticAt ℂ (fun w : ℂ => w / ρ) ρ := by
      have : (fun w : ℂ => w / ρ) = (fun w : ℂ => w * ρ⁻¹) := by funext w; ring
      rw [this]; exact analyticAt_id.mul analyticAt_const
    have h_exp : AnalyticAt ℂ (fun w : ℂ => Complex.exp (w / ρ)) ρ := h_id.cexp
    have h_neg : AnalyticAt ℂ (fun w : ℂ => -Complex.exp (w / ρ)) ρ := h_exp.neg
    have h_fun_eq : (fun w : ℂ => -Complex.exp (w / ρ) / ρ) =
        (fun w : ℂ => -Complex.exp (w / ρ) * ρ⁻¹) := by funext w; ring
    rw [h_fun_eq]
    exact h_neg.mul analyticAt_const
  have hg_ne : g ρ ≠ 0 := by
    show (-Complex.exp (ρ / ρ) / ρ) ≠ 0
    have h_div : ρ / ρ = 1 := div_self hρ_ne
    rw [h_div]
    exact div_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero 1)) hρ_ne
  have h_eq : ∀ᶠ w in nhds ρ, (1 + xiWeierstrassTerm ρ w) = (w - ρ) ^ 1 • g w := by
    filter_upwards with w
    unfold xiWeierstrassTerm xiWeierstrassFactor
    show 1 + ((1 - w / ρ) * Complex.exp (w / ρ) - 1) = (w - ρ) ^ 1 • (-Complex.exp (w / ρ) / ρ)
    rw [pow_one, smul_eq_mul]
    field_simp
    ring
  rw [(h_anal.analyticOrderAt_eq_natCast).mpr ⟨g, hg_anal, hg_ne, h_eq⟩]
  rfl

/-- Splitting lemma: near ρ ∈ NontrivialZeros,
`xiProductMult z = (factor ρ)^{xiOrderNat ρ} · g(z)` with `g` analytic nonzero at ρ.

TRACKED: requires sigma-split of the tprod via `Multipliable.tprod_eq_mul_tprod_ite`. -/
theorem xiProductMult_eq_factor_mul_rest
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      xiProductMult =ᶠ[nhds ρ]
        (fun z => (1 + xiWeierstrassTerm ρ z) ^ (ZD.xiOrderNat ρ) * g z) := by
  have hρ_ne : ρ ≠ 0 := by
    intro heq
    have : (0 : ℝ) < ρ.re := hρ.1
    rw [heq] at this; simp at this
  -- Split the MultiZeroIdx product at the ρ-fiber S and its complement.
  set ρ_sub : {ρ' : ℂ // ρ' ∈ NontrivialZeros} := ⟨ρ, hρ⟩ with hρ_sub_def
  set S : Set MultiZeroIdx := {p : MultiZeroIdx | p.1 = ρ_sub} with hS_def
  set g : ℂ → ℂ := fun z =>
    ∏' p : (Sᶜ : Set MultiZeroIdx), (1 + xiWeierstrassTerm p.val.1.val z) with hg_def
  refine ⟨g, ?_, ?_, ?_⟩
  · -- **Analyticity of g at ρ** via local-uniform convergence of the subtype product.
    have h_mult_loc : MultipliableLocallyUniformlyOn
        (fun p : ↑(Sᶜ : Set MultiZeroIdx) => fun z : ℂ => 1 + xiWeierstrassTerm p.val.1.val z)
        Set.univ := by
      apply multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
      intro z _
      refine ⟨Metric.closedBall z 1, ?_, ?_⟩
      · exact nhdsWithin_le_nhds (Metric.closedBall_mem_nhds z zero_lt_one)
      · set M : ℝ := ‖z‖ + 1 with hMz_def
        have hMz_pos : 0 < M := by rw [hMz_def]; linarith [norm_nonneg z]
        have h_subM : Metric.closedBall z 1 ⊆ Metric.closedBall (0 : ℂ) M := by
          intro w hw
          rw [Metric.mem_closedBall, dist_zero_right]
          rw [Metric.mem_closedBall] at hw
          calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
                have := norm_sub_norm_le w z; linarith
            _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
            _ ≤ 1 + ‖z‖ := by linarith
            _ = M := by rw [hMz_def]; ring
        have h_summ_sub : Summable (fun p : ↑(Sᶜ : Set MultiZeroIdx) =>
            3 * M ^ 2 / ‖p.val.1.val‖ ^ 2) :=
          (summable_multi_weierstrassTerm_bound M hMz_pos).subtype _
        have h_bd_full := xiWeierstrassTerm_mult_closedBall_bound M hMz_pos
        have h_bd_sub : ∀ᶠ p : ↑(Sᶜ : Set MultiZeroIdx) in cofinite,
            ∀ w ∈ Metric.closedBall (0 : ℂ) M,
              ‖xiWeierstrassTerm p.val.1.val w‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 :=
          (Subtype.val_injective.tendsto_cofinite
            (α := (Sᶜ : Set MultiZeroIdx))).eventually h_bd_full
        have h_cts : ∀ p : ↑(Sᶜ : Set MultiZeroIdx),
            ContinuousOn (fun z => xiWeierstrassTerm p.val.1.val z)
              (Metric.closedBall (0 : ℂ) M) := by
          intro p
          have hρp_ne : p.val.1.val ≠ 0 := by
            intro heq; have hre : (0 : ℝ) < p.val.1.val.re := p.val.1.property.1
            rw [heq] at hre; simp at hre
          exact (xiWeierstrassTerm_differentiable hρp_ne).continuous.continuousOn
        have h_main : MultipliableUniformlyOn
            (fun p : ↑(Sᶜ : Set MultiZeroIdx) => fun z : ℂ => 1 + xiWeierstrassTerm p.val.1.val z)
            (Metric.closedBall (0 : ℂ) M) :=
          Summable.multipliableUniformlyOn_one_add
            (isCompact_closedBall _ _) h_summ_sub h_bd_sub h_cts
        exact h_main.mono h_subM
    have h_open : IsOpen (Set.univ : Set ℂ) := isOpen_univ
    have h_diffOn : DifferentiableOn ℂ g Set.univ := by
      apply (h_mult_loc.hasProdLocallyUniformlyOn.differentiableOn ?_ h_open)
      filter_upwards with s
      have h_each : ∀ p ∈ s,
          DifferentiableOn ℂ
            (fun x => (fun z : ℂ => 1 + xiWeierstrassTerm p.val.1.val z) x) Set.univ := by
        intro p _
        have hρp_ne : p.val.1.val ≠ 0 := by
          intro heq; have hre : (0 : ℝ) < p.val.1.val.re := p.val.1.property.1
          rw [heq] at hre; simp at hre
        exact (one_add_xiWeierstrassTerm_differentiable hρp_ne).differentiableOn
      have := DifferentiableOn.finset_prod (u := s)
        (f := fun p x => 1 + xiWeierstrassTerm p.val.1.val x) h_each
      convert this using 1
      funext x
      rw [Finset.prod_fn]
    exact (h_diffOn.analyticOnNhd h_open) ρ (Set.mem_univ ρ)
  · -- **g ρ ≠ 0**: each Sᶜ-factor at ρ is nonzero (index ≠ ρ) and the norm sum converges.
    show (∏' p : (Sᶜ : Set MultiZeroIdx), (1 + xiWeierstrassTerm p.val.1.val ρ)) ≠ 0
    apply tprod_one_add_ne_zero_of_summable
    · intro p
      have hp_ne_sub : p.val.1 ≠ ρ_sub := p.property
      have hp_val_ne : p.val.1.val ≠ ρ := fun heq =>
        hp_ne_sub (Subtype.ext heq)
      have h_ne1 : p.val.1.val ≠ 0 := by
        intro heq; have hre : (0 : ℝ) < p.val.1.val.re := p.val.1.property.1
        rw [heq] at hre; simp at hre
      exact one_add_xiWeierstrassTerm_ne_zero_of_ne h_ne1 hp_val_ne.symm
    · set M : ℝ := ‖ρ‖ + 1 with hMρ_def
      have hMρ_pos : 0 < M := by rw [hMρ_def]; linarith [norm_nonneg ρ]
      have hρ_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) M := by
        rw [Metric.mem_closedBall, dist_zero_right, hMρ_def]; linarith
      have h_summ_sub : Summable (fun p : ↑(Sᶜ : Set MultiZeroIdx) =>
          3 * M ^ 2 / ‖p.val.1.val‖ ^ 2) :=
        (summable_multi_weierstrassTerm_bound M hMρ_pos).subtype _
      have h_bd_full := xiWeierstrassTerm_mult_closedBall_bound M hMρ_pos
      have h_bd_sub : ∀ᶠ p : ↑(Sᶜ : Set MultiZeroIdx) in cofinite,
          ‖xiWeierstrassTerm p.val.1.val ρ‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 := by
        have : ∀ᶠ p : ↑(Sᶜ : Set MultiZeroIdx) in cofinite,
            ∀ w ∈ Metric.closedBall (0 : ℂ) M,
              ‖xiWeierstrassTerm p.val.1.val w‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 :=
          (Subtype.val_injective.tendsto_cofinite
            (α := (Sᶜ : Set MultiZeroIdx))).eventually h_bd_full
        filter_upwards [this] with p hp_bd
        exact hp_bd ρ hρ_in_ball
      exact h_summ_sub.of_norm_bounded_eventually (by
        filter_upwards [h_bd_sub] with p hp
        rwa [Real.norm_of_nonneg (by positivity)])
  · -- **Pointwise (hence eventual) identity** via tprod split at S vs Sᶜ.
    apply Filter.EventuallyEq.of_eq
    funext z
    have hS_fin : (S : Set MultiZeroIdx).Finite := by
      let bigSet : Finset MultiZeroIdx :=
        (Finset.univ : Finset (Fin (ZD.xiOrderNat ρ))).image
          (fun k : Fin (ZD.xiOrderNat ρ) => (⟨ρ_sub, k⟩ : MultiZeroIdx))
      apply bigSet.finite_toSet.subset
      intro p hp
      change p.1 = ρ_sub at hp
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨p.2.cast (by rw [hp]), Finset.mem_univ _, ?_⟩
      obtain ⟨p1, p2⟩ := p
      change p1 = ρ_sub at hp
      subst hp
      rfl
    have hS_mult : Multipliable ((fun p : MultiZeroIdx => 1 + xiWeierstrassTerm p.1.val z) ∘
        (Subtype.val : ↑(S : Set MultiZeroIdx) → MultiZeroIdx)) :=
      hS_fin.multipliable _
    have hSc_mult : Multipliable ((fun p : MultiZeroIdx => 1 + xiWeierstrassTerm p.1.val z) ∘
        (Subtype.val : ↑(Sᶜ : Set MultiZeroIdx) → MultiZeroIdx)) := by
      set M : ℝ := ‖z‖ + 1 with hMz_def
      have hMz_pos : 0 < M := by rw [hMz_def]; linarith [norm_nonneg z]
      have hz_in_ball : z ∈ Metric.closedBall (0 : ℂ) M := by
        rw [Metric.mem_closedBall, dist_zero_right, hMz_def]; linarith
      have h_summ_sub : Summable (fun p : ↑(Sᶜ : Set MultiZeroIdx) =>
          3 * M ^ 2 / ‖p.val.1.val‖ ^ 2) :=
        (summable_multi_weierstrassTerm_bound M hMz_pos).subtype _
      have h_bd_full := xiWeierstrassTerm_mult_closedBall_bound M hMz_pos
      have h_bd_sub : ∀ᶠ p : ↑(Sᶜ : Set MultiZeroIdx) in cofinite,
          ‖xiWeierstrassTerm p.val.1.val z‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 := by
        have : ∀ᶠ p : ↑(Sᶜ : Set MultiZeroIdx) in cofinite,
            ∀ w ∈ Metric.closedBall (0 : ℂ) M,
              ‖xiWeierstrassTerm p.val.1.val w‖ ≤ 3 * M ^ 2 / ‖p.val.1.val‖ ^ 2 :=
          (Subtype.val_injective.tendsto_cofinite
            (α := (Sᶜ : Set MultiZeroIdx))).eventually h_bd_full
        filter_upwards [this] with p hp_bd
        exact hp_bd z hz_in_ball
      have h_summ_term : Summable (fun p : ↑(Sᶜ : Set MultiZeroIdx) =>
          ‖xiWeierstrassTerm p.val.1.val z‖) :=
        h_summ_sub.of_norm_bounded_eventually (by
          filter_upwards [h_bd_sub] with p hp
          rwa [Real.norm_of_nonneg (by positivity)])
      exact multipliable_one_add_of_summable h_summ_term
    have h_full : (∏' p : (S : Set MultiZeroIdx), (1 + xiWeierstrassTerm p.val.1.val z)) *
        (∏' p : (Sᶜ : Set MultiZeroIdx), (1 + xiWeierstrassTerm p.val.1.val z)) =
        ∏' p : MultiZeroIdx, (1 + xiWeierstrassTerm p.1.val z) :=
      hS_mult.tprod_mul_tprod_compl hSc_mult
    -- S-side equals the n-th power of the ρ-factor via a Fin-equivalence.
    have hS_eq : ∏' p : (S : Set MultiZeroIdx), (1 + xiWeierstrassTerm p.val.1.val z) =
        (1 + xiWeierstrassTerm ρ z) ^ (ZD.xiOrderNat ρ) := by
      let e : Fin (ZD.xiOrderNat ρ) ≃ (S : Set MultiZeroIdx) := {
        toFun := fun k => ⟨⟨ρ_sub, k⟩, rfl⟩
        invFun := fun p => p.val.2.cast (congrArg
          (fun r : {r : ℂ // r ∈ NontrivialZeros} => ZD.xiOrderNat r.val) p.property)
        left_inv := fun k => by simp [Fin.cast]
        right_inv := fun p => by
          apply Subtype.ext
          obtain ⟨⟨p1, p2⟩, hp⟩ := p
          change p1 = ρ_sub at hp
          subst hp
          rfl
      }
      have h_rw := e.tprod_eq (fun p => (1 + xiWeierstrassTerm p.val.1.val z) : ↑S → ℂ)
      rw [← h_rw]
      rw [tprod_eq_prod (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)]
      show ∏ k : Fin (ZD.xiOrderNat ρ), (1 + xiWeierstrassTerm (e k).val.1.val z) = _
      have h_ev : ∀ k : Fin (ZD.xiOrderNat ρ), (e k).val.1.val = ρ := fun k => rfl
      simp_rw [h_ev]
      rw [Finset.prod_const]; simp
    rw [hS_eq] at h_full
    show xiProductMult z = (1 + xiWeierstrassTerm ρ z) ^ ZD.xiOrderNat ρ * g z
    unfold xiProductMult
    rw [← h_full]

/-- **Order at a nontrivial zero matches `xiOrderNat`.** -/
theorem analyticOrderAt_xiProductMult_eq_xiOrderNat
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    analyticOrderAt xiProductMult ρ = (ZD.xiOrderNat ρ : ℕ∞) := by
  obtain ⟨g, hg_anal, hg_ne, h_eq⟩ := xiProductMult_eq_factor_mul_rest hρ
  rw [analyticOrderAt_congr h_eq]
  -- Rewrite the lambda product as Pi-algebra product of the factor-pow and g.
  have h_fun_eq :
      (fun z => (1 + xiWeierstrassTerm ρ z) ^ ZD.xiOrderNat ρ * g z) =
        ((fun w => 1 + xiWeierstrassTerm ρ w) ^ ZD.xiOrderNat ρ) * g := by
    funext z; simp [Pi.pow_apply, Pi.mul_apply]
  rw [h_fun_eq]
  have h_anal_factor : AnalyticAt ℂ (fun w => 1 + xiWeierstrassTerm ρ w) ρ :=
    analyticAt_xiWeierstrassFactor ρ ρ
  have h_anal_pow : AnalyticAt ℂ
      ((fun w => 1 + xiWeierstrassTerm ρ w) ^ ZD.xiOrderNat ρ) ρ :=
    h_anal_factor.pow _
  have h_order_g : analyticOrderAt g ρ = 0 :=
    (hg_anal.analyticOrderAt_eq_zero).mpr hg_ne
  rw [analyticOrderAt_mul h_anal_pow hg_anal,
      analyticOrderAt_pow h_anal_factor,
      analyticOrderAt_xiWeierstrassFactor_eq_one hρ,
      h_order_g, add_zero]
  simp

end ZD
