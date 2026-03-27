/-
# Circle-Native Holomorphic Completion: Strip Theorem

The final internal strip theorem via the Hurwitz zero-free corollary,
applied to the θ-native kernel on off-axis strip domains.
-/
import Mathlib
import RequestProject.Defs

open Complex Real Finset Filter Topology Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace CircleNative

/-! ## Part A: Hurwitz Zero-Free Corollary

The classical Hurwitz theorem states: if holomorphic functions f_n converge
locally uniformly to f on an open connected domain D, and each f_n is
zero-free on D, then f is either identically zero on D or zero-free on D.

The zero-free corollary is: under the additional hypothesis that f is not
identically zero, f must be zero-free.
-/

/-
PROBLEM
**Hurwitz Zero-Free Corollary.**

Let D ⊆ ℂ be an open connected set. Let f_n : ℂ → ℂ be a sequence of
functions, each holomorphic and zero-free on D, converging locally uniformly
to f on D. If f is not identically zero on D, then f is zero-free on D.

This is the precise form needed for the strip theorem: it transfers the
zero-free property from finite kernels to the infinite kernel on off-axis
domains.

PROVIDED SOLUTION
Proof by contradiction using the maximum modulus principle:

1. Suppose g(s₀) = 0 for some s₀ ∈ D.
2. g is holomorphic on D (by TendstoLocallyUniformlyOn.differentiableOn applied to hf_holo, hf_conv, hD_open).
3. g is analytic on D (holomorphic ⟹ analytic).
4. Since g ≢ 0 (by hg_not_const_zero) and D is connected, the zeros of g are isolated (identity theorem: AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero).
5. s₀ is an isolated zero: there exists r > 0 with B(s₀,r) ⊆ D and g(z) ≠ 0 for 0 < |z-s₀| < r.
6. Let m = inf{‖g(z)‖ : |z-s₀| = r/2} > 0 (continuous function on compact set, positive).
7. f_n → g uniformly on the closed ball B̄(s₀, r/2) (from locally uniform convergence on the open set D).
8. For large n: ‖f_n - g‖ < m/2 on B̄(s₀, r/2).
9. For such n: ‖f_n(z)‖ ≥ m/2 on the circle |z-s₀| = r/2.
10. 1/f_n is holomorphic on B̄(s₀, r/2) with ‖1/f_n(z)‖ ≤ 2/m on the boundary.
11. By maximum modulus principle: ‖1/f_n(s₀)‖ ≤ 2/m, so ‖f_n(s₀)‖ ≥ m/2.
12. But f_n(s₀) → g(s₀) = 0, so ‖f_n(s₀)‖ → 0. Contradiction for large n.

Key Mathlib lemmas to use:
- TendstoLocallyUniformlyOn.differentiableOn (limit of holomorphic is holomorphic)
- DifferentiableOn.analyticOnNhd (holomorphic implies analytic on open sets)
- eqOn_zero_of_preconnected_of_eventuallyEq_zero (identity theorem)
- Complex.norm_eq_abs, various norm estimates
-/
theorem hurwitz_zero_free
    (D : Set ℂ) (hD_open : IsOpen D) (hD_conn : IsConnected D)
    (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hf_holo : ∀ n, DifferentiableOn ℂ (f n) D)
    (hf_conv : TendstoLocallyUniformlyOn f g atTop D)
    (hf_nz : ∀ n, ∀ s ∈ D, f n s ≠ 0)
    (hg_not_const_zero : ∃ s ∈ D, g s ≠ 0) :
    ∀ s ∈ D, g s ≠ 0 := by
  -- By the identity theorem, since $g$ is analytic and not identically zero on $D$, it must be zero-free on $D$.
  have h_analytic : AnalyticOnNhd ℂ g D := by
    apply_rules [ DifferentiableOn.analyticOnNhd, hf_conv.differentiableOn ];
    aesop;
  intro s hs hgs_zero
  have h_isolated_zero : ∀ᶠ z in nhds s, g z = 0 → z = s := by
    have := h_analytic s hs;
    have := this.eventually_eq_zero_or_eventually_ne_zero;
    cases' this with h h;
    · have h_const_zero : ∀ z ∈ D, g z = 0 := by
        apply_rules [ h_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero ];
        exact hD_conn.isPreconnected;
      aesop;
    · rw [ eventually_nhdsWithin_iff ] at h;
      filter_upwards [ h ] with x hx hx' using Classical.not_not.1 fun hx'' => hx hx'' hx';
  -- Choose $r > 0$ such that the closed ball $B(s, r)$ is contained in $D$ and $g(z) \neq 0$ for $0 < |z - s| < r$.
  obtain ⟨r, hr_pos, hr_ball⟩ : ∃ r > 0, Metric.closedBall s r ⊆ D ∧ ∀ z ∈ Metric.sphere s r, g z ≠ 0 := by
    -- Since $g$ is analytic and not identically zero on $D$, there exists a neighborhood $U$ of $s$ such that $g(z) \neq 0$ for all $z \in U \setminus \{s\}$.
    obtain ⟨U, hU_open, hU_s, hU_zero⟩ : ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ ∀ z ∈ U \ {s}, g z ≠ 0 := by
      rw [ Metric.eventually_nhds_iff ] at h_isolated_zero;
      exact ⟨ Metric.ball s h_isolated_zero.choose, Metric.isOpen_ball, Metric.mem_ball_self h_isolated_zero.choose_spec.1, fun z hz => fun hz' => hz.2 <| h_isolated_zero.choose_spec.2 hz.1 hz' ⟩;
    -- Choose $r > 0$ such that the closed ball $B(s, r)$ is contained in $U \cap D$.
    obtain ⟨r, hr_pos, hr_ball⟩ : ∃ r > 0, Metric.closedBall s r ⊆ U ∩ D := by
      exact Metric.mem_nhds_iff.mp ( Filter.inter_mem ( hU_open.mem_nhds hU_s ) ( hD_open.mem_nhds hs ) ) |> fun ⟨ r, hr₀, hr ⟩ => ⟨ r / 2, half_pos hr₀, fun z hz => hr <| Metric.mem_ball.mpr <| lt_of_le_of_lt ( Metric.mem_closedBall.mp hz ) <| half_lt_self hr₀ ⟩;
    exact ⟨ r, hr_pos, fun z hz => hr_ball hz |>.2, fun z hz => hU_zero z ⟨ hr_ball ( Metric.mem_closedBall.mpr <| by simpa using hz.le ) |>.1, by aesop ⟩ ⟩;
  -- By the maximum modulus principle, since $1/f_n$ is holomorphic on $B(s, r)$ and $|1/f_n(z)| \leq 2/m$ on the boundary, we have $|1/f_n(s)| \leq 2/m$.
  have h_max_modulus : ∀ᶠ n in Filter.atTop, ‖1 / f n s‖ ≤ 2 / (sInf {‖g z‖ | z ∈ Metric.sphere s r}) := by
    have h_max_modulus : ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.sphere s r, ‖1 / f n z‖ ≤ 2 / (sInf {‖g z‖ | z ∈ Metric.sphere s r}) := by
      have h_max_modulus : ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.sphere s r, ‖f n z - g z‖ < ‖g z‖ / 2 := by
        have h_max_modulus : ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.sphere s r, ‖f n z - g z‖ < ‖g z‖ / 2 := by
          have h_uniform : TendstoUniformlyOn (fun n z => f n z) g Filter.atTop (Metric.sphere s r) := by
            have h_uniform : TendstoLocallyUniformlyOn (fun n z => f n z) g Filter.atTop (Metric.sphere s r) := by
              exact hf_conv.mono ( by exact fun x hx => hr_ball.1 <| Metric.mem_closedBall.mpr <| by simpa using hx.le );
            have h_compact : IsCompact (Metric.sphere s r) := by
              exact isCompact_sphere _ _;
            exact?
          rw [ Metric.tendstoUniformlyOn_iff ] at h_uniform;
          have h_min : ∃ m > 0, ∀ z ∈ Metric.sphere s r, ‖g z‖ ≥ m := by
            have h_compact : IsCompact (Metric.sphere s r) := by
              exact isCompact_sphere _ _
            have h_continuous : ContinuousOn (fun z => ‖g z‖) (Metric.sphere s r) := by
              exact ContinuousOn.norm ( h_analytic.continuousOn.mono ( by exact fun x hx => hr_ball.1 <| Metric.mem_closedBall.mpr <| by simpa using hx.le ) )
            have := h_compact.exists_isMinOn ( Set.nonempty_of_mem ( show s + r ∈ Metric.sphere s r from by norm_num [ hr_pos.le ] ) ) h_continuous;
            exact ⟨ ‖g this.choose‖, norm_pos_iff.mpr ( hr_ball.2 _ this.choose_spec.1 ), fun z hz => this.choose_spec.2 hz ⟩;
          obtain ⟨ m, hm_pos, hm ⟩ := h_min; filter_upwards [ h_uniform ( m / 2 ) ( half_pos hm_pos ) ] with n hn z hz using by rw [ norm_sub_rev ] ; exact lt_of_lt_of_le ( hn z hz ) ( by linarith [ hm z hz ] ) ;
        exact h_max_modulus;
      filter_upwards [ h_max_modulus ] with n hn z hz
      have h_bound : ‖f n z‖ ≥ ‖g z‖ / 2 := by
        have := norm_sub_le ( f n z ) ( f n z - g z ) ; norm_num at * ; linarith [ hn z hz ] ;
      have h_inv_bound : ‖1 / f n z‖ ≤ 2 / ‖g z‖ := by
        simpa using inv_anti₀ ( half_pos ( norm_pos_iff.mpr ( hr_ball.2 z hz ) ) ) h_bound
      have h_inf_bound : ‖1 / f n z‖ ≤ 2 / sInf {‖g z‖ | z ∈ Metric.sphere s r} := by
        refine' le_trans h_inv_bound ( div_le_div_of_nonneg_left _ _ _ ) <;> norm_num at *;
        · -- Since $g$ is continuous on the compact set $Metric.sphere s r$, it attains a minimum value $m > 0$ on this set.
          have h_min_pos : ∃ m > 0, ∀ z ∈ Metric.sphere s r, ‖g z‖ ≥ m := by
            have h_min_pos : ∃ m ∈ (Set.image (fun z => ‖g z‖) (Metric.sphere s r)), ∀ y ∈ (Set.image (fun z => ‖g z‖) (Metric.sphere s r)), m ≤ y := by
              apply_rules [ IsCompact.exists_isLeast, CompactIccSpace.isCompact_Icc ];
              · exact IsCompact.image_of_continuousOn ( isCompact_sphere s r ) ( h_analytic.continuousOn.norm.mono ( by intro x hx; exact hr_ball.1 <| by simpa using hx.out.le ) );
              · exact ⟨ _, ⟨ z, by simpa using hz, rfl ⟩ ⟩;
            obtain ⟨ m, hm₁, hm₂ ⟩ := h_min_pos; use m; aesop;
          exact lt_of_lt_of_le h_min_pos.choose_spec.1 ( le_csInf ⟨ _, ⟨ z, hz, rfl ⟩ ⟩ fun x hx => hx.choose_spec.2 ▸ h_min_pos.choose_spec.2 _ hx.choose_spec.1 );
        · exact csInf_le ⟨ 0, by rintro x ⟨ w, hw₁, rfl ⟩ ; positivity ⟩ ⟨ z, hz, rfl ⟩
      exact h_inf_bound;
    filter_upwards [ h_max_modulus ] with n hn;
    have := @Complex.norm_le_of_forall_mem_frontier_norm_le;
    specialize this ( Metric.isBounded_closedBall ) ( show DiffContOnCl ℂ ( fun z => 1 / f n z ) ( Metric.closedBall s r ) from ?_ ) ( show ∀ z ∈ frontier ( Metric.closedBall s r ), ‖1 / f n z‖ ≤ 2 / sInf { x | ∃ z ∈ Metric.sphere s r, ‖g z‖ = x } from ?_ ) ( show s ∈ closure ( Metric.closedBall s r ) from ?_ );
    · refine' DifferentiableOn.diffContOnCl _;
      simp +zetaDelta at *;
      exact DifferentiableOn.inv ( hf_holo n |> DifferentiableOn.mono <| hr_ball.1 ) fun z hz => hf_nz n z <| hr_ball.1 hz;
    · simp_all +decide [ frontier_closedBall, hr_pos.ne' ];
    · exact subset_closure ( Metric.mem_closedBall_self hr_pos.le );
    · exact this;
  -- Since $f_n(s) \to g(s) = 0$, we have $\|f_n(s)\| \to 0$.
  have h_norm_zero : Filter.Tendsto (fun n => ‖f n s‖) Filter.atTop (nhds 0) := by
    have h_norm_zero : Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s)) := by
      have := hf_conv.tendsto_at hs;
      exact this;
    simpa [ hgs_zero ] using h_norm_zero.norm;
  have h_contradiction : Filter.Tendsto (fun n => ‖1 / f n s‖) Filter.atTop Filter.atTop := by
    norm_num +zetaDelta at *;
    refine' Filter.Tendsto.inv_tendsto_nhdsGT_zero _;
    rw [ tendsto_nhdsWithin_iff ] ; aesop;
  exact absurd ( h_contradiction.eventually_gt_atTop ( 2 / sInf { x | ∃ z ∈ Metric.sphere s r, ‖g z‖ = x } ) ) fun h => by have := h.and h_max_modulus; obtain ⟨ n, hn₁, hn₂ ⟩ := this.exists; linarith;

/-! ## Part B: Strip Theorem — Reduction to Four Hypotheses

The strip theorem states that Ξ_θ is zero-free on the off-axis strips
D⁺_{ε,δ} and D⁻_{ε,δ}, provided four hypotheses are verified.

We state the four hypotheses as standalone propositions, then assemble
the strip theorem. -/

/-- Hypothesis (1): Each finite kernel Ξ_{θ,n} is holomorphic on D. -/
def HypHolomorphic (D : Set ℂ) : Prop :=
  ∀ n : ℕ, DifferentiableOn ℂ (ΞFinite n) D

/-- Hypothesis (2): Ξ_{θ,n} → Ξ_θ locally uniformly on D. -/
def HypLocallyUniform (D : Set ℂ) : Prop :=
  TendstoLocallyUniformlyOn (fun n => ΞFinite n) ΞInfinite atTop D

/-- Hypothesis (3): Each finite Ξ_{θ,n} is zero-free on D. -/
def HypZeroFree (D : Set ℂ) : Prop :=
  ∀ n : ℕ, ∀ s ∈ D, ΞFinite n s ≠ 0

/-- Hypothesis (4): Ξ_θ is not identically zero on D. -/
def HypNotIdenticallyZero (D : Set ℂ) : Prop :=
  ∃ s ∈ D, ΞInfinite s ≠ 0

/-- **Strip Theorem (Right strip).**

If hypotheses (1)–(4) hold for D⁺_{ε,δ}, then Ξ_θ is zero-free
on D⁺_{ε,δ}. This is a direct application of the Hurwitz zero-free corollary. -/
theorem strip_theorem_plus
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ)
    (h1 : HypHolomorphic (StripPlus ε δ))
    (h2 : HypLocallyUniform (StripPlus ε δ))
    (h3 : HypZeroFree (StripPlus ε δ))
    (h4 : HypNotIdenticallyZero (StripPlus ε δ)) :
    ∀ s ∈ StripPlus ε δ, ΞInfinite s ≠ 0 :=
  hurwitz_zero_free (StripPlus ε δ)
    (isOpen_stripPlus ε δ) (isConnected_stripPlus hεδ)
    (fun n => ΞFinite n) ΞInfinite h1 h2 h3 h4

/-- **Strip Theorem (Left strip).**

If hypotheses (1)–(4) hold for D⁻_{ε,δ}, then Ξ_θ is zero-free
on D⁻_{ε,δ}. -/
theorem strip_theorem_minus
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ)
    (h1 : HypHolomorphic (StripMinus ε δ))
    (h2 : HypLocallyUniform (StripMinus ε δ))
    (h3 : HypZeroFree (StripMinus ε δ))
    (h4 : HypNotIdenticallyZero (StripMinus ε δ)) :
    ∀ s ∈ StripMinus ε δ, ΞInfinite s ≠ 0 :=
  hurwitz_zero_free (StripMinus ε δ)
    (isOpen_stripMinus ε δ) (isConnected_stripMinus hεδ)
    (fun n => ΞFinite n) ΞInfinite h1 h2 h3 h4

/-! ## Part C: Convergence Theorem

Working assumption for now: the series defining `Ξ_θ` converges absolutely
and locally uniformly on the endpoint-form strip

  0 < Re(s) < 1 + (π - 3) / 3,

equivalently on the centered strip `{ s : |Re(s) - θ| < θ }` with `θ = π / 6`.

### Key estimate

For s with `|Re(s) - θ| ≤ δ' < δ < 1`, we use the same pointwise majorant,
and assume summability on this larger range.

  |a_p · ((2θp)^(s-θ) + (2θp)^(-(s-θ)))|
    ≤ a_p · ((2θp)^δ' + (2θp)^(-δ'))
    ≤ 2 · a_p · (2θp)^δ'
-/

/-- The majorant term attached to the current coefficient law. -/
def majorant (δ : ℝ) (p : ℕ) : ℝ :=
  a p * ((φ p) ^ δ + (φ p) ^ (-δ))

/-- The base `φ(p)` is nonnegative for every natural input. -/
lemma phi_nonneg (p : ℕ) : 0 ≤ φ p := by
  unfold φ
  have hp : (0 : ℝ) ≤ p := by exact_mod_cast Nat.zero_le p
  nlinarith [two_theta_pos, hp]

/-- Every majorant term is nonnegative. -/
lemma majorant_nonneg (δ : ℝ) (p : ℕ) : 0 ≤ majorant δ p := by
  unfold majorant
  exact mul_nonneg (a_nonneg p)
    (add_nonneg (Real.rpow_nonneg (phi_nonneg p) _)
      (Real.rpow_nonneg (phi_nonneg p) _))

/-- Local convergence hypothesis for the current coefficient law:
    the majorant is summable throughout the classical-width range `δ < 1`. -/
def SummableMajorantHyp : Prop :=
  ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ →
    Summable (fun n => if Nat.Prime n then majorant δ n else 0)

/-
PROBLEM
**Pointwise bound.** For |Re(s) - θ| ≤ δ, each term of the kernel
    series is bounded by the majorant.

PROVIDED SOLUTION
The key is: ‖(a p : ℂ) * (cpowBase p (s-θ) + cpowBase p (-(s-θ)))‖ = |a p| * ‖cpowBase p (s-θ) + cpowBase p (-(s-θ))‖. Since a p ≥ 0, |a p| = a p.

By triangle inequality: ‖cpowBase p w + cpowBase p (-w)‖ ≤ ‖cpowBase p w‖ + ‖cpowBase p (-w)‖.

Now cpowBase p w = exp(w * log(φ p)), so ‖cpowBase p w‖ = exp(Re(w) * log(φ p)) = (φ p)^(Re w) (using rpow). Here w = s - θ so Re(w) = s.re - θ. Since |s.re - θ| ≤ δ, we have |Re(w)| ≤ δ.

The function t ↦ b^t + b^(-t) for b > 0 is even and increasing on [0,∞). So for |x| ≤ δ: b^x + b^(-x) ≤ b^δ + b^(-δ). Applying with b = φ p and x = s.re - θ:

(φ p)^(s.re-θ) + (φ p)^(-(s.re-θ)) ≤ (φ p)^δ + (φ p)^(-δ)

Therefore the full norm ≤ a p * ((φ p)^δ + (φ p)^(-δ)) = majorant δ p.
-/
lemma kernel_term_bound {δ : ℝ} (_hδ_nn : 0 ≤ δ) (s : ℂ)
    (hs : |s.re - θ| ≤ δ) (p : ℕ) (hp : Nat.Prime p) :
    ‖(↑(a p) : ℂ) * (cpowBase p (s - ↑θ) + cpowBase p (-(s - ↑θ)))‖ ≤
      majorant δ p := by
  have ha_nonneg : 0 ≤ a p := a_nonneg p
  -- Apply the triangle inequality to the norm.
  have h_triangle : ‖(cpowBase p (s - θ) + cpowBase p (-(s - θ)))‖ ≤ (φ p)^(s.re - θ) + (φ p)^(-(s.re - θ)) := by
    refine' le_trans ( norm_add_le _ _ ) _;
    unfold cpowBase; norm_num [ Complex.norm_exp ] ; ring;
    rw [ Real.rpow_def_of_pos ( show 0 < φ p from mul_pos ( mul_pos two_pos ( Real.arcsin_pos.mpr ( by norm_num ) ) ) ( Nat.cast_pos.mpr hp.pos ) ), Real.rpow_def_of_pos ( show 0 < φ p from mul_pos ( mul_pos two_pos ( Real.arcsin_pos.mpr ( by norm_num ) ) ) ( Nat.cast_pos.mpr hp.pos ) ) ] ; ring_nf ; norm_num;
  -- Apply the bound from the triangle inequality to the norm.
  suffices h_bound : (φ p)^(s.re - θ) + (φ p)^(-(s.re - θ)) ≤ (φ p)^δ + (φ p)^(-δ) by
    calc
      ‖(↑(a p) : ℂ) * (cpowBase p (s - ↑θ) + cpowBase p (-(s - ↑θ)))‖
          = a p * ‖cpowBase p (s - ↑θ) + cpowBase p (-(s - ↑θ))‖ := by
              rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha_nonneg]
      _ ≤ a p * ((φ p) ^ (s.re - θ) + (φ p) ^ (-(s.re - θ))) :=
            mul_le_mul_of_nonneg_left h_triangle ha_nonneg
      _ ≤ a p * ((φ p) ^ δ + (φ p) ^ (-δ)) :=
            mul_le_mul_of_nonneg_left h_bound ha_nonneg
      _ = majorant δ p := by simp [majorant]
  -- Since $|s.re - \theta| \leq \delta$, we have $-\delta \leq s.re - \theta \leq \delta$.
  have h_bounds : -δ ≤ s.re - θ ∧ s.re - θ ≤ δ := by
    exact abs_le.mp hs;
  -- Since $φ p > 1$, the function $b^t + b^{-t}$ is increasing on $[0, \infty)$.
  have h_inc : ∀ b : ℝ, 1 < b → ∀ x y : ℝ, 0 ≤ x → x ≤ y → b^x + b^(-x) ≤ b^y + b^(-y) := by
    intros b hb x y hx hy; rw [ Real.rpow_neg ( by linarith ), Real.rpow_neg ( by linarith ) ] ; ring_nf; (
    field_simp;
    nlinarith [ show b ^ x ≤ b ^ y by exact Real.rpow_le_rpow_of_exponent_le hb.le hy, show b ^ x ≥ 1 by exact Real.one_le_rpow hb.le hx, show b ^ y ≥ b ^ x by exact Real.rpow_le_rpow_of_exponent_le hb.le hy, mul_le_mul_of_nonneg_left ( show b ^ x ≤ b ^ y by exact Real.rpow_le_rpow_of_exponent_le hb.le hy ) ( show 0 ≤ b ^ x by positivity ), mul_le_mul_of_nonneg_left ( show b ^ x ≥ 1 by exact Real.one_le_rpow hb.le hx ) ( show 0 ≤ b ^ y by positivity ) ]);
  by_cases h_case : s.re - θ ≥ 0;
  · convert h_inc ( φ p ) _ _ _ h_case h_bounds.2 using 1 ; norm_num [ φ ];
    rw [ show θ = Real.pi / 6 by exact θ_eq ] ; nlinarith [ Real.pi_gt_three, show ( p : ℝ ) ≥ 2 by exact_mod_cast hp.two_le ];
  · convert h_inc ( φ p ) ( show 1 < φ p from ?_ ) ( - ( s.re - θ ) ) δ ( by linarith ) ( by linarith ) using 1 <;> ring;
    unfold φ;
    rw [ show θ = Real.pi / 6 by exact θ_eq ] ; nlinarith [ Real.pi_gt_three, show ( p : ℝ ) ≥ 2 by exact_mod_cast hp.two_le ]

/-
PROBLEM
**Absolute convergence.** For |Re(s) - θ| < δ < 1, the series
    defining Ξ_θ(s) converges absolutely.

PROVIDED SOLUTION
Pick δ' with |s.re - θ| < δ' < δ. Then |s.re - θ| ≤ δ' and δ' < 1. By kernel_term_bound with δ' and the chosen `SummableMajorantHyp`, use Summable.of_nonneg_of_le or Summable.of_norm_bounded to get summability.

Alternatively, use Summable.of_norm_bounded directly with the majorant at parameter δ' (or even at δ directly since kernel_term_bound works with ≤).

Actually, we can directly use the bound at some intermediate δ': define δ' = (|s.re - θ| + δ) / 2, so |s.re - θ| < δ' < δ < 1. Then |s.re - θ| ≤ δ' (strict, actually ≤ holds), and `SummableMajorantHyp` gives summability of the majorant. Then Summable.of_norm_bounded gives the result.
-/
theorem ΞInfinite_summable {δ : ℝ} (hδ : δ < 1) (hδ_pos : 0 < δ) (s : ℂ)
    (hmajorant : SummableMajorantHyp)
    (hs : |s.re - θ| < δ) :
    Summable (fun n => if Nat.Prime n then
      (↑(a n) : ℂ) * (cpowBase n (s - ↑θ) + cpowBase n (-(s - ↑θ)))
    else 0) := by
  -- Let's choose δ' such that |s.re - θ| < δ' < δ.
  obtain ⟨δ', hδ'_pos, hδ'_lt, hsδ'⟩ : ∃ δ', 0 < δ' ∧ δ' < δ ∧ |s.re - θ| < δ' := by
    exact ⟨ ( |s.re - θ| + δ ) / 2, by linarith [ abs_nonneg ( s.re - θ ) ], by linarith, by linarith ⟩;
  have h_summable : Summable (fun n => if Nat.Prime n then majorant δ' n else 0) := by
    exact hmajorant (lt_trans hδ'_lt hδ) hδ'_pos.le
  -- Apply the comparison test with the summable series of majorant terms.
  have h_comparison : ∀ n, ‖(if Nat.Prime n then (a n : ℂ) * (cpowBase n (s - θ) + cpowBase n (-(s - θ))) else 0)‖ ≤ (if Nat.Prime n then majorant δ' n else 0) := by
    intro n
    by_cases hn : Nat.Prime n
    · simpa [hn] using kernel_term_bound (show 0 ≤ δ' by linarith) s (show |s.re - θ| ≤ δ' by linarith [hsδ']) n hn
    · simp [hn]
  -- Apply the comparison test with the summable series of majorant terms to conclude that the original series is summable.
  apply Summable.of_norm_bounded; exact h_summable; exact h_comparison

/-
PROBLEM
**Hypothesis (1) verified:** Each finite kernel Ξ_{θ,n} is holomorphic
    (differentiable) on any open set, since it is a finite sum of entire functions.

PROVIDED SOLUTION
ΞFinite n is a finite sum over primes p ≤ n of terms of the form (a p) * (exp(w * log(φ p)) + exp(-w * log(φ p))) where w = s - θ. Each term is differentiable in s (composition of exp with a linear function), and a finite sum of differentiable functions is differentiable. Use DifferentiableOn.sum, DifferentiableOn.mul, DifferentiableOn.const, DifferentiableOn.cexp, etc.
-/
theorem hypothesis_1_verified (D : Set ℂ) (hD : IsOpen D) :
    HypHolomorphic D := by
  intro n;
  refine' Differentiable.differentiableOn _;
  intro s; exact (by
  refine' DifferentiableAt.congr_of_eventuallyEq _ _;
  exact fun s => ∑ p ∈ primesBelow n, ( a p : ℂ ) * ( Complex.exp ( ( s - θ ) * Real.log ( φ p ) ) + Complex.exp ( - ( s - θ ) * Real.log ( φ p ) ) );
  · fun_prop (disch := norm_num);
  · filter_upwards [ ] with s ; unfold ΞFinite ; aesop);

/-
PROBLEM
**Convergence theorem (Hypothesis 2).**
    For δ < 1, the finite kernels Ξ_{θ,n} converge locally uniformly to
    Ξ_θ on the open strip { s : |Re(s) - θ| < δ }.

    Proof outline: By the Weierstrass M-test, the series converges uniformly
    on every compact subset K ⊆ { |Re(s) - θ| < δ }. On K, there exists
    δ' < δ such that |Re(s) - θ| ≤ δ' for all s ∈ K. The majorant
    ∑_p majorant(δ', p) converges by the chosen `SummableMajorantHyp`.

PROVIDED SOLUTION
This is the Weierstrass M-test applied to the kernel series. For the locally uniform convergence on the open strip {|Re(s)-θ| < δ}, we need: for every s₀ in the strip, there's a neighborhood where the partial sums converge uniformly to the limit. Given s₀ with |s₀.re - θ| < δ, pick δ' with |s₀.re - θ| < δ' < δ. Then a ball around s₀ is contained in {|Re(s)-θ| ≤ δ'}. On this set, each term is bounded by majorant(δ', p) which is summable. By the Weierstrass M-test, the series converges uniformly.

This is a deep technical proof involving TendstoLocallyUniformlyOn for tprod/tsum. The key ingredients are:
- ΞFinite n is a partial sum of the series defining ΞInfinite
- The tail of the series (ΞInfinite - ΞFinite n) → 0 locally uniformly
- `SummableMajorantHyp` provides the dominating series
- kernel_term_bound provides the pointwise domination

This may be hard to formalize directly. If needed, leave as sorry.
-/
theorem convergence_theorem {δ : ℝ} (hδ : δ < 1) (hδ_pos : 0 < δ)
    (hmajorant : SummableMajorantHyp) :
    HypLocallyUniform { s : ℂ | |s.re - θ| < δ } := by
  -- By the Weierstrass M-test, the series converges uniformly on every compact subset K ⊆ { |Re(s) - θ| < δ }.
  have h_weierstrass : ∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | |s.re - θ| < δ} → TendstoLocallyUniformlyOn (fun n => ΞFinite n) ΞInfinite atTop K := by
    intros K hK hK_subset
    have h_weierstrass : ∀ s ∈ K, ∀ n : ℕ, ‖(ΞFinite n) s - (ΞInfinite) s‖ ≤ ∑' p : ℕ, if Nat.Prime p ∧ p > n then majorant δ p else 0 := by
      intros s hs n
      have h_tail : ‖(ΞFinite n) s - (ΞInfinite) s‖ ≤ ∑' p : ℕ, if Nat.Prime p ∧ p > n then ‖(a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ)))‖ else 0 := by
        have h_tail : ‖(ΞFinite n) s - (ΞInfinite) s‖ = ‖∑' p : ℕ, if Nat.Prime p ∧ p > n then (a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ))) else 0‖ := by
          have h_split : ∑' p : ℕ, (if Nat.Prime p then (a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ))) else 0) = ∑' p : ℕ, (if Nat.Prime p ∧ p ≤ n then (a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ))) else 0) + ∑' p : ℕ, (if Nat.Prime p ∧ p > n then (a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ))) else 0) := by
            rw [ ← Summable.tsum_add ] ; congr ; ext p ; aesop;
            · refine' summable_of_ne_finset_zero _;
              exacts [ Finset.range ( n + 1 ), fun p hp => if_neg fun h => hp <| Finset.mem_range_succ_iff.mpr h.2 ];
            · have h_summable : Summable (fun p : ℕ => if Nat.Prime p then (a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ))) else 0) := by
                have := ΞInfinite_summable hδ hδ_pos s hmajorant ( hK_subset hs );
                convert this using 1;
              rw [ ← summable_norm_iff ] at *;
              exact Summable.of_nonneg_of_le ( fun x => norm_nonneg _ ) ( fun x => by aesop ) h_summable;
          have h_split : ∑' p : ℕ, (if Nat.Prime p ∧ p ≤ n then (a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ))) else 0) = ∑ p ∈ primesBelow n, (a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ))) := by
            rw [ tsum_eq_sum ];
            any_goals exact Finset.filter Nat.Prime ( Finset.range ( n + 1 ) );
            · exact Finset.sum_congr rfl fun x hx => if_pos ⟨ Finset.mem_filter.mp hx |>.2, Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hx |>.1 ) ⟩;
            · grind;
          unfold ΞFinite ΞInfinite; aesop;
        convert norm_tsum_le_tsum_norm _ ; aesop;
        have h_summable : Summable (fun p : ℕ => if Nat.Prime p then ‖(a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ)))‖ else 0) := by
          have h_summable : Summable (fun p : ℕ => if Nat.Prime p then (a p : ℂ) * (cpowBase p (s - θ) + cpowBase p (-(s - θ))) else 0) := by
            convert ΞInfinite_summable hδ hδ_pos s hmajorant ( hK_subset hs ) using 1;
          convert h_summable.norm using 2 ; aesop;
        refine' .of_nonneg_of_le ( fun p => norm_nonneg _ ) ( fun p => _ ) h_summable.norm ; aesop;
      refine' le_trans h_tail ( Summable.tsum_le_tsum _ _ _ );
      · intro p; split_ifs <;> norm_num;
        convert kernel_term_bound hδ_pos.le s ( le_of_lt ( hK_subset hs ) ) p ( by tauto ) using 1 ; ring!;
        norm_num [ ← add_mul, abs_mul ];
        ring!;
      · have h_summable : Summable (fun p : ℕ => if Nat.Prime p then majorant δ p else 0) := by
          exact hmajorant hδ hδ_pos.le
        refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) h_summable;
        · split_ifs <;> positivity
        · by_cases hpn : Nat.Prime p ∧ p > n
          · rcases hpn with ⟨hp, hp_gt_n⟩
            simpa [hp, hp_gt_n] using
              (kernel_term_bound hδ_pos.le s (show |s.re - θ| ≤ δ by exact le_of_lt ( hK_subset hs )) p hp)
          · by_cases hp : Nat.Prime p
            · have hnot_gt_n : ¬ p > n := by
                intro hp_gt_n
                exact hpn ⟨hp, hp_gt_n⟩
              simp [hp, hnot_gt_n, majorant_nonneg]
            · simp [hp]
      · have h_summable : Summable (fun p : ℕ => if Nat.Prime p then majorant δ p else 0) := by
          exact hmajorant hδ hδ_pos.le
        refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) h_summable;
        · by_cases hpn : Nat.Prime p ∧ p > n <;> simp [hpn, majorant_nonneg]
        · by_cases hpn : Nat.Prime p ∧ p > n
          · rcases hpn with ⟨hp, hp_gt_n⟩
            simp [hp, hp_gt_n]
          · by_cases hp : Nat.Prime p
            · have hnot_gt_n : ¬ p > n := by
                intro hp_gt_n
                exact hpn ⟨hp, hp_gt_n⟩
              simp [hp, hnot_gt_n, majorant_nonneg]
            · simp [hp]
    -- Since the series ∑' p : ℕ, if Nat.Prime p ∧ p > n then majorant δ p else 0 converges to 0 as n tends to infinity, we can apply the Weierstrass M-test.
    have h_series_zero : Filter.Tendsto (fun n : ℕ => ∑' p : ℕ, if Nat.Prime p ∧ p > n then majorant δ p else 0) Filter.atTop (nhds 0) := by
      have h_series_zero : Filter.Tendsto (fun n : ℕ => ∑' p : ℕ, if Nat.Prime p ∧ p ≤ n then majorant δ p else 0) Filter.atTop (nhds (∑' p : ℕ, if Nat.Prime p then majorant δ p else 0)) := by
        convert Summable.hasSum _ |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 1;
        · ext n; simp +decide [ Finset.sum_ite ] ; ring;
          rw [ tsum_eq_sum ];
          any_goals exact Finset.range ( 1 + n ) |> Finset.filter Nat.Prime;
          · exact Finset.sum_congr rfl fun x hx => if_pos ⟨ Finset.mem_filter.mp hx |>.2, by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ] ⟩;
          · grind;
        · exact hmajorant hδ hδ_pos.le
      convert h_series_zero.const_sub ( ∑' p : ℕ, if Nat.Prime p then majorant δ p else 0 ) using 2 <;> norm_num;
      rw [ ← Summable.tsum_sub ] ; congr ; ext p ; split_ifs <;> first | linarith | aesop;
      · exact hmajorant hδ hδ_pos.le
      · refine' summable_of_ne_finset_zero _;
        exacts [ Finset.range ( ‹_› + 1 ), fun p hp => if_neg fun h => hp <| Finset.mem_range_succ_iff.mpr h.2 ];
    rw [ Metric.tendstoLocallyUniformlyOn_iff ];
    rw [ Metric.tendsto_nhds ] at h_series_zero;
    simp_all +decide [ dist_eq_norm' ];
    exact fun ε hε x hx => ⟨ K, self_mem_nhdsWithin, by obtain ⟨ N, hN ⟩ := h_series_zero ε hε; exact ⟨ N, fun n hn y hy => lt_of_le_of_lt ( h_weierstrass y hy n ) ( lt_of_abs_lt ( hN n hn ) ) ⟩ ⟩;
  intro ε hε x hx;
  obtain ⟨δ', hδ'_pos, hδ'_lt⟩ : ∃ δ' > 0, Metric.closedBall x δ' ⊆ {s : ℂ | |s.re - θ| < δ} := by
    exact Metric.nhds_basis_closedBall.mem_iff.mp ( IsOpen.mem_nhds ( isOpen_lt ( continuous_abs.comp ( Complex.continuous_re.sub continuous_const ) ) continuous_const ) hx );
  have := h_weierstrass ( Metric.closedBall x δ' ) ( ProperSpace.isCompact_closedBall x δ' ) hδ'_lt;
  rw [ Metric.tendstoLocallyUniformlyOn_iff ] at this;
  obtain ⟨ t, ht₁, ht₂ ⟩ := this ( Metric.mem_uniformity_dist.mp hε |> Classical.choose ) ( Metric.mem_uniformity_dist.mp hε |> Classical.choose_spec |> And.left ) x ( Metric.mem_closedBall_self hδ'_pos.le );
  refine' ⟨ t ∩ Metric.closedBall x δ', _, _ ⟩;
  · rw [ nhdsWithin ] at *;
    rw [ Filter.mem_inf_principal ] at *;
    filter_upwards [ ht₁, Metric.ball_mem_nhds x hδ'_pos ] with y hy₁ hy₂ using fun hy₃ => ⟨ hy₁ <| Metric.mem_closedBall.mpr <| le_of_lt <| by simpa using hy₂, Metric.mem_closedBall.mpr <| le_of_lt <| by simpa using hy₂ ⟩;
  · filter_upwards [ ht₂ ] with n hn y hy using Metric.mem_uniformity_dist.mp hε |> Classical.choose_spec |> And.right |> fun h => h <| hn y hy.1

/-! ## Verification of Hypothesis (2) on off-axis strips -/

/-
PROBLEM
The right strip D⁺_{ε,δ} is contained in { |Re(s) - θ| < δ }.

PROVIDED SOLUTION
For s ∈ StripPlus ε δ, we have ε < s.re - θ < δ. Since ε > 0, we get 0 < s.re - θ < δ, so |s.re - θ| = s.re - θ < δ.
-/
lemma stripPlus_subset_open_strip {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) :
    StripPlus ε δ ⊆ { s : ℂ | |s.re - θ| < δ } := by
  intro s hs; rw [ Set.mem_setOf_eq ] ; exact abs_lt.mpr ⟨ by linarith [ hs.1, hs.2 ], by linarith [ hs.1, hs.2 ] ⟩ ;

/-
PROBLEM
The left strip D⁻_{ε,δ} is contained in { |Re(s) - θ| < δ }.

PROVIDED SOLUTION
For s ∈ StripMinus ε δ, we have -δ < s.re - θ < -ε. Since ε > 0, s.re - θ < 0 so |s.re - θ| = -(s.re - θ) = θ - s.re. From -δ < s.re - θ we get θ - s.re < δ, so |s.re - θ| < δ.
-/
lemma stripMinus_subset_open_strip {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) :
    StripMinus ε δ ⊆ { s : ℂ | |s.re - θ| < δ } := by
  intro s hs;
  -- By definition of StripMinus, we have -δ < s.re - θ < -ε.
  obtain ⟨h_left, h_right⟩ : -δ < s.re - θ ∧ s.re - θ < -ε := by
    exact hs;
  grind

/-
PROBLEM
Hypothesis (2) holds on D⁺_{ε,δ} for δ < 1.

PROVIDED SOLUTION
Use convergence_theorem to get locally uniform convergence on {|Re(s)-θ| < δ}, then restrict to the subset StripPlus ε δ using stripPlus_subset_open_strip and TendstoLocallyUniformlyOn.mono.
-/
theorem hypothesis_2_stripPlus {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ : δ < 1)
    (hmajorant : SummableMajorantHyp) :
    HypLocallyUniform (StripPlus ε δ) := by
  -- Apply the convergence theorem with the given δ.
  have h_conv : HypLocallyUniform { s : ℂ | |s.re - θ| < δ } := by
    exact convergence_theorem hδ ( by linarith ) hmajorant;
  exact h_conv.mono ( by simpa [ Set.subset_def ] using stripPlus_subset_open_strip hε hεδ )

/-
PROBLEM
Hypothesis (2) holds on D⁻_{ε,δ} for δ < 1.

PROVIDED SOLUTION
Same as hypothesis_2_stripPlus: use convergence_theorem and TendstoLocallyUniformlyOn.mono with stripMinus_subset_open_strip.
-/
theorem hypothesis_2_stripMinus {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ : δ < 1)
    (hmajorant : SummableMajorantHyp) :
    HypLocallyUniform (StripMinus ε δ) := by
  have h_converge : HypLocallyUniform { s : ℂ | |s.re - θ| < δ } := by
    exact convergence_theorem hδ ( by linarith ) hmajorant;
  exact h_converge.mono ( stripMinus_subset_open_strip hε hεδ )

/-! ## Derivative identity on the critical line -/

/-
PROBLEM
The derivative identity: C_P'(t) = -∑_{p ≤ P} a_p · u_p · sin(t · u_p).
    This follows from differentiating cos(t · u_p) with respect to t.

PROVIDED SOLUTION
CriticalLineSum P t = ∑ p ∈ primesBelow P, a p * cos(t * u p). Each summand is differentiable: d/dt [a_p * cos(t * u_p)] = a_p * (-sin(t * u_p)) * u_p = -(a_p * u_p * sin(t * u_p)).

Use HasDerivAt.sum. For each p, use HasDerivAt.const_mul (a p) composed with:
HasDerivAt for cos(t * u p) = -sin(t * u p) * u p, obtained from Real.hasDerivAt_cos composed with hasDerivAt_mul_const.

Unfold CriticalLineSum and CriticalLineSumDeriv, then apply HasDerivAt.sum and show each term has the correct derivative.
-/
theorem criticalLine_deriv (P : ℕ) (t : ℝ) :
    HasDerivAt (CriticalLineSum P) (CriticalLineSumDeriv P t) t := by
  convert HasDerivAt.sum fun p hp => HasDerivAt.const_mul ( a p ) ( HasDerivAt.cos ( hasDerivAt_mul_const ( u p ) ) ) using 1;
  ext x; unfold CriticalLineSum; simp [Finset.sum_apply]

/-! ## Off-line decomposition -/

/-
PROBLEM
**Off-line decomposition.** For s = θ + x + it with x, t real:

  Ξ_{θ,P}(θ + x + it) = 2 ∑ a_p cosh(x·u_p) cos(t·u_p)
                        + 2i ∑ a_p sinh(x·u_p) sin(t·u_p)

This follows from the identity:
  w^z + w^(-z) = 2 cosh(z log w) = 2 cosh((x+it) log w)
    = 2(cosh(x log w) cos(t log w) + i sinh(x log w) sin(t log w))

PROVIDED SOLUTION
Unfold ΞFinite and cpowBase. For each prime p, the term is:
(a p) * (exp((s-θ)*log(φ p)) + exp(-(s-θ)*log(φ p)))

With s = θ + x + t*I, we get s - θ = x + t*I (as a complex number). So:
(s-θ) * log(φ p) = (x + t*I) * u_p = x*u_p + t*u_p*I

exp(x*u_p + t*u_p*I) = exp(x*u_p) * exp(t*u_p*I) = exp(x*u_p) * (cos(t*u_p) + I*sin(t*u_p))
exp(-(x*u_p + t*u_p*I)) = exp(-x*u_p) * (cos(t*u_p) - I*sin(t*u_p))

Sum = (exp(x*u_p) + exp(-x*u_p))*cos(t*u_p) + I*(exp(x*u_p) - exp(-x*u_p))*sin(t*u_p)
    = 2*cosh(x*u_p)*cos(t*u_p) + 2*I*sinh(x*u_p)*sin(t*u_p)

Multiply by a_p and sum. Factor out the 2 and 2I. Use Complex.exp_add, Complex.exp_mul_I, cosh/sinh definitions.
-/
theorem offline_decomposition (P : ℕ) (x t : ℝ) :
    ΞFinite P (↑θ + ↑x + ↑t * Complex.I) =
      2 * ∑ p ∈ primesBelow P,
        ↑(a p * Real.cosh (x * u p) * Real.cos (t * u p))
      + 2 * Complex.I * ∑ p ∈ primesBelow P,
        ↑(a p * Real.sinh (x * u p) * Real.sin (t * u p)) := by
  simp +decide only [ΞFinite, mul_comm, mul_left_comm _, mul_sum _ _ _, mul_assoc];
  simp +decide [ Complex.cos, Complex.sin, Complex.cosh, Complex.sinh, ← Complex.exp_add, ← Complex.exp_neg ] ; ring;
  rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun p hp => _ ; unfold cpowBase ; ring;
  unfold u; norm_num [ mul_assoc, ← Complex.exp_add ] ; ring;

/-- Named observable form of the finite off-axis decomposition. -/
theorem offline_decomposition_observables (P : ℕ) (x t : ℝ) :
    ΞFinite P (↑θ + ↑x + ↑t * Complex.I) =
      2 * ↑(OffAxisRealObservable P x t) +
      2 * Complex.I * ↑(OffAxisImagObservable P x t) := by
  rw [offline_decomposition]
  simp [OffAxisRealObservable, OffAxisImagObservable]

/-- On the kernel axis `s = θ + it`, the infinite Robespierre kernel is
    exactly twice the infinite harmonic cosine sum. -/
theorem ΞInfinite_theta_axis_eq_real (t : ℝ) :
    ΞInfinite (↑θ + ↑t * Complex.I) = 2 * ↑(CriticalLineSumInf t) := by
  unfold ΞInfinite CriticalLineSumInf
  calc
    (∑' p : ℕ,
        if Nat.Prime p then
          (↑(a p) : ℂ) * (cpowBase p ((↑θ + ↑t * Complex.I) - ↑θ) + cpowBase p (-(((↑θ + ↑t * Complex.I) - ↑θ))))
        else 0)
      =
        ∑' p : ℕ, if Nat.Prime p then (2 : ℂ) * ↑(a p * Real.cos (t * u p)) else 0 := by
          apply tsum_congr
          intro p
          by_cases hp : Nat.Prime p
          · simp only [if_pos hp]
            have hmul' : ↑t * Complex.I * ↑(Real.log (φ p)) = ↑(t * u p) * Complex.I := by
              simp [u]
              ring
            have hmul_neg'' : (-(↑t * Complex.I)) * ↑(Real.log (φ p)) = ↑(-(t * u p)) * Complex.I := by
              simp [u]
              ring
            rw [show ((↑θ + ↑t * Complex.I) - ↑θ : ℂ) = ↑t * Complex.I by ring]
            unfold cpowBase
            rw [hmul', hmul_neg'', Complex.exp_mul_I, Complex.exp_mul_I]
            simp [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
            ring
          · simp [hp]
    _ = ∑' p : ℕ, (2 : ℂ) * (if Nat.Prime p then ↑(a p) * Complex.cos (↑t * ↑(u p)) else 0) := by
          apply tsum_congr
          intro p
          by_cases hp : Nat.Prime p <;> simp [hp]
    _ = (2 : ℂ) * ∑' p : ℕ, if Nat.Prime p then ↑(a p) * Complex.cos (↑t * ↑(u p)) else 0 := by
          let g : ℕ → ℂ := fun p => if Nat.Prime p then ↑(a p) * Complex.cos (↑t * ↑(u p)) else 0
          let gR : ℕ → ℝ := fun p => if Nat.Prime p then a p * Real.cos (t * u p) else 0
          have hg : g = fun p => (gR p : ℂ) := by
            funext p
            by_cases hp : Nat.Prime p <;> simp [g, gR, hp, Complex.ofReal_cos, mul_assoc]
          have hs : Summable g := by
            rw [hg]
            exact (Complex.summable_ofReal).2 (criticalLineSumInf_summable t)
          simpa [g] using hs.tsum_mul_left (2 : ℂ)
    _ = 2 * ↑(∑' p : ℕ, if Nat.Prime p then a p * Real.cos (t * u p) else 0) := by
          let gR : ℕ → ℝ := fun p => if Nat.Prime p then a p * Real.cos (t * u p) else 0
          let g : ℕ → ℂ := fun p => if Nat.Prime p then ↑(a p) * Complex.cos (↑t * ↑(u p)) else 0
          have hg : g = fun p => (gR p : ℂ) := by
            funext p
            by_cases hp : Nat.Prime p <;> simp [g, gR, hp, Complex.ofReal_cos, mul_assoc]
          change (2 : ℂ) * ∑' p : ℕ, g p = 2 * ↑(∑' p : ℕ, gR p)
          rw [hg]
          congr 1
          simpa [gR] using (Complex.ofReal_tsum gR).symm

/-- On the kernel axis, an infinite Robespierre kernel zero is exactly a zero
    of the infinite harmonic cosine sum. -/
theorem ΞInfinite_theta_axis_zero_iff (t : ℝ) :
    ΞInfinite (↑θ + ↑t * Complex.I) = 0 ↔ CriticalLineSumInf t = 0 := by
  constructor
  · intro hz
    rw [ΞInfinite_theta_axis_eq_real] at hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  · intro hsum
    rw [ΞInfinite_theta_axis_eq_real, hsum]
    simp

/-- On the kernel axis `s = θ + it`, the finite Robespierre kernel is purely
    real and equals twice the critical-line sum. -/
theorem XiFinite_theta_axis_eq_real (P : ℕ) (t : ℝ) :
    ΞFinite P (↑θ + ↑t * Complex.I) = 2 * ↑(CriticalLineSum P t) := by
  simpa [offAxisRealObservable_axis, offAxisImagObservable_axis] using
    (offline_decomposition_observables P 0 t)

/-- On the kernel axis, a finite Robespierre kernel zero is exactly a zero of
    the harmonic cosine sum. This is the finite harmonic-collapse criterion. -/
theorem XiFinite_theta_axis_zero_iff (P : ℕ) (t : ℝ) :
    ΞFinite P (↑θ + ↑t * Complex.I) = 0 ↔ CriticalLineSum P t = 0 := by
  constructor
  · intro hz
    rw [XiFinite_theta_axis_eq_real] at hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  · intro hsum
    rw [XiFinite_theta_axis_eq_real, hsum]
    simp

/-- On the kernel axis `s = θ + it`, the finite Robespierre kernel has zero
    imaginary part. This is the explicit harmonic cancellation identity. -/
theorem XiFinite_theta_axis_im_eq_zero (P : ℕ) (t : ℝ) :
    (ΞFinite P (↑θ + ↑t * Complex.I)).im = 0 := by
  rw [XiFinite_theta_axis_eq_real]
  simp

/-- Along the real slice `t = 0`, every finite kernel prefix containing the
    prime `2` is nonzero. This is the first concrete off-axis noncancellation
    result obtained from the observable asymmetry/positivity package. -/
theorem XiFinite_real_slice_ne_zero {P : ℕ} (hP : 2 ≤ P) (x : ℝ) :
    ΞFinite P (↑θ + ↑x) ≠ 0 := by
  have hpos : 0 < OffAxisRealObservable P x 0 :=
    offAxisRealObservable_at_zero_pos hP x
  intro hz
  rw [show (↑θ + ↑x : ℂ) = ↑θ + ↑x + ↑(0 : ℝ) * Complex.I by simp] at hz
  rw [offline_decomposition_observables, offAxisImagObservable_at_zero] at hz
  simp at hz
  linarith

/-- A finite kernel zero forces both prime-density observable channels to vanish. -/
theorem XiFinite_zero_implies_observables_zero (P : ℕ) (x t : ℝ)
    (hz : ΞFinite P (↑θ + ↑x + ↑t * Complex.I) = 0) :
    OffAxisRealObservable P x t = 0 ∧ OffAxisImagObservable P x t = 0 := by
  have hsum :
      2 * ↑(OffAxisRealObservable P x t) +
        2 * Complex.I * ↑(OffAxisImagObservable P x t) = 0 := by
    simpa [hz] using (offline_decomposition_observables P x t).symm
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  simp [Complex.mul_re, Complex.mul_im] at hre him
  constructor <;> linarith

/-- A finite kernel zero also forces the rotation-aware prime-density detector
    to pass: every rotated observable frame sees the same vanishing signal. -/
theorem XiFinite_zero_implies_rotated_prime_density_detector
    (P : ℕ) (x t : ℝ)
    (hz : ΞFinite P (↑θ + ↑x + ↑t * Complex.I) = 0) :
    RotatedPrimeDensityDetector P x t := by
  have hdet : PrimeDensityDetector P x t :=
    XiFinite_zero_implies_observables_zero P x t hz
  exact (rotatedPrimeDensityDetector_iff P x t).2 hdet

/-- If both reflected finite prefixes vanish, then the odd observable channel
    must vanish. This packages the finite reflected-pair antisymmetry
    obstruction in the form needed for the Klein-four argument. -/
theorem reflected_zero_pair_imag_observable_eq_zero (P : ℕ) (x t : ℝ)
    (hz_pos : ΞFinite P (↑θ + ↑x + ↑t * Complex.I) = 0)
    (hz_neg : ΞFinite P (↑θ + ↑(-x) + ↑t * Complex.I) = 0) :
    OffAxisImagObservable P x t = 0 := by
  have him_pos : OffAxisImagObservable P x t = 0 :=
    (XiFinite_zero_implies_observables_zero P x t hz_pos).2
  have him_neg : OffAxisImagObservable P (-x) t = 0 :=
    (XiFinite_zero_implies_observables_zero P (-x) t hz_neg).2
  rw [offAxisImagObservable_neg_x] at him_neg
  linarith

/-- A reflected finite zero pair forces the two prime-density observables at the
    positive displacement to vanish: the real channel vanishes because each
    zero kills both channels, and the odd imaginary channel vanishes again by
    reflected antisymmetry. -/
theorem reflected_zero_pair_observables_zero (P : ℕ) (x t : ℝ)
    (hz_pos : ΞFinite P (↑θ + ↑x + ↑t * Complex.I) = 0)
    (hz_neg : ΞFinite P (↑θ + ↑(-x) + ↑t * Complex.I) = 0) :
    OffAxisRealObservable P x t = 0 ∧ OffAxisImagObservable P x t = 0 := by
  refine ⟨(XiFinite_zero_implies_observables_zero P x t hz_pos).1, ?_⟩
  exact reflected_zero_pair_imag_observable_eq_zero P x t hz_pos hz_neg

/-- A reflected finite zero pair satisfies the rotation-aware detector as well:
    the prime-density vector vanishes in every rotated frame. -/
theorem reflected_zero_pair_rotated_prime_density_detector (P : ℕ) (x t : ℝ)
    (hz_pos : ΞFinite P (↑θ + ↑x + ↑t * Complex.I) = 0)
    (hz_neg : ΞFinite P (↑θ + ↑(-x) + ↑t * Complex.I) = 0) :
    RotatedPrimeDensityDetector P x t := by
  have hdet : PrimeDensityDetector P x t :=
    reflected_zero_pair_observables_zero P x t hz_pos hz_neg
  exact (rotatedPrimeDensityDetector_iff P x t).2 hdet

/-- Hidden reflected finite zeros cannot occur on the real slice. The odd
    observable is forced to vanish by antisymmetry, while the even prime-density
    observable is strictly positive once the prefix contains the prime `2`. -/
theorem reflected_zero_pair_real_slice_impossible {P : ℕ} (hP : 2 ≤ P) (x : ℝ) :
    ¬ (ΞFinite P (↑θ + ↑x) = 0 ∧ ΞFinite P (↑θ - ↑x) = 0) := by
  intro hpair
  rcases hpair with ⟨hz_pos_raw, hz_neg_raw⟩
  have hz_pos : ΞFinite P (↑θ + ↑x + ↑(0 : ℝ) * Complex.I) = 0 := by
    simpa using hz_pos_raw
  have hz_neg : ΞFinite P (↑θ + ↑(-x) + ↑(0 : ℝ) * Complex.I) = 0 := by
    simpa [sub_eq_add_neg] using hz_neg_raw
  have hobs := reflected_zero_pair_observables_zero P x 0 hz_pos hz_neg
  have hreal_pos : 0 < OffAxisRealObservable P x 0 :=
    offAxisRealObservable_at_zero_pos hP x
  linarith [hobs.1, hreal_pos]

/-- A reflected finite zero pair forces the off-axis even distortion to be
    absorbed exactly by the symmetry-axis observable. This is the precise
    general-`t` conspiracy condition that any hidden off-axis pair would have
    to satisfy. -/
theorem reflected_zero_pair_forces_axis_absorption (P : ℕ) (x t : ℝ)
    (hz_pos : ΞFinite P (↑θ + ↑x + ↑t * Complex.I) = 0)
    (hz_neg : ΞFinite P (↑θ + ↑(-x) + ↑t * Complex.I) = 0) :
    RealObservableDistortion P x t = - CriticalLineSum P t := by
  have hreal : OffAxisRealObservable P x t = 0 :=
    (reflected_zero_pair_observables_zero P x t hz_pos hz_neg).1
  unfold RealObservableDistortion
  linarith

/-- On the real slice, axis absorption would force the real-axis distortion to
    cancel the positive critical-line prefix. Combined with positivity of the
    distortion, this recovers the real-slice obstruction. -/
theorem reflected_zero_pair_forces_real_axis_absorption (P : ℕ) (x : ℝ)
    (hz_pos : ΞFinite P (↑θ + ↑x) = 0)
    (hz_neg : ΞFinite P (↑θ - ↑x) = 0) :
    RealAxisDistortion P x = - CriticalLineSum P 0 := by
  have habsorb :=
    reflected_zero_pair_forces_axis_absorption P x 0
      (by simpa using hz_pos) (by simpa [sub_eq_add_neg] using hz_neg)
  simpa [realObservableDistortion_at_zero] using habsorb

end CircleNative

end
