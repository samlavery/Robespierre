import Mathlib

/-!
# Cosh-Symmetric Pole Structure for Meromorphic Functions

We prove that if a meromorphic function on a preconnected open set satisfies a
"cosh symmetry" — meaning `f(s) = f(c - s)` on some open subset (the region of
convergence overlapping the cosh strip) — then the meromorphic continuation has
cosh-symmetric pole structure: `meromorphicOrderAt f z = meromorphicOrderAt f (c - z)`
for all `z` in the domain.

This is a consequence of the **identity theorem for meromorphic functions**: if two
meromorphic functions on a preconnected open set agree on an open subset, they agree
everywhere (in the sense of having the same values on punctured neighborhoods, hence
the same meromorphic orders).

## Mathematical context

The "cosh symmetry" `s ↦ c - s` is the natural reflection associated with the hyperbolic
cosine: `cosh(z) = cosh(-z)`. For Dirichlet series with cosh-symmetric coefficients,
this symmetry holds on the region of absolute convergence. By analytic/meromorphic
continuation and the identity theorem, the symmetry extends to the full domain.
-/

open Complex Filter Set Topology

noncomputable section

/-! ## The cosh reflection map -/

/-- The cosh reflection map: `s ↦ c - s`, modeling the symmetry `cosh(z) = cosh(-z)`
shifted by center `c`. -/
def coshReflect (c : ℂ) (s : ℂ) : ℂ := c - s

/-- A set is cosh-symmetric around center `c` if it's invariant under `s ↦ c - s`. -/
def CoshSymmetric (c : ℂ) (U : Set ℂ) : Prop := ∀ s ∈ U, c - s ∈ U

lemma coshReflect_involutive (c : ℂ) : Function.Involutive (coshReflect c) := by
  intro s; simp [coshReflect, sub_sub_cancel]

lemma coshReflect_self_apply (c s : ℂ) : coshReflect c (coshReflect c s) = s :=
  coshReflect_involutive c s

/-! ## Analyticity of the reflection map -/

/-
PROVIDED SOLUTION
coshReflect c = fun s => c - s = (fun s => c) - id, which is the difference of a constant (analytic) and the identity (analytic). Use analyticAt_const.sub analyticAt_id or similar.
-/
lemma analyticAt_coshReflect (c z : ℂ) : AnalyticAt ℂ (coshReflect c) z := by
  apply_rules [ AnalyticAt.sub, analyticAt_id, analyticAt_const ]

/-
PROVIDED SOLUTION
coshReflect c is s ↦ c - s, which is a non-constant affine map. If it were eventually constant near z, then s ↦ c - s would be constant in some neighborhood, which is impossible since it's injective (in fact, an involution).
-/
lemma coshReflect_not_eventuallyConst (c z : ℂ) :
    ¬Filter.EventuallyConst (coshReflect c) (nhds z) := by
  unfold coshReflect;
  intro h;
  obtain ⟨ s, hs ⟩ := h;
  rcases Metric.mem_nhds_iff.mp hs.1 with ⟨ ε, εpos, hε ⟩;
  have := hs.2 ( hε ( Metric.mem_ball_self εpos ) ) ( hε ( show z + ε / 2 ∈ Metric.ball z ε from by simpa [ abs_of_pos εpos ] ) ) ; aesop

/-! ## Meromorphic composition with cosh reflection -/

/-
PROVIDED SOLUTION
Use MeromorphicAt.comp_analyticAt with the fact that coshReflect c is analytic at z (analyticAt_coshReflect) and that coshReflect c z = c - z. Need to unfold coshReflect to show the composition gives the right thing.
-/
lemma meromorphicAt_comp_coshReflect {f : ℂ → ℂ} {c z : ℂ}
    (hf : MeromorphicAt f (c - z)) :
    MeromorphicAt (f ∘ coshReflect c) z := by
  have := hf;
  convert this.comp_analyticAt ( analyticAt_coshReflect c z ) using 1

/-
PROVIDED SOLUTION
For each z ∈ U, we have c - z ∈ U by CoshSymmetric. Then f is meromorphic at c - z, and coshReflect c is analytic at z, so f ∘ coshReflect c is meromorphic at z by meromorphicAt_comp_coshReflect. Use coshReflect c z = c - z.
-/
lemma meromorphicOn_comp_coshReflect {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hU_sym : CoshSymmetric c U) :
    MeromorphicOn (f ∘ coshReflect c) U := by
  intro z hz;
  convert meromorphicAt_comp_coshReflect (hf (c - z) (hU_sym z hz)) using 1

/-! ## Identity theorem for meromorphic functions

The key technical engine: if a meromorphic function on a preconnected open set is
eventually zero near some point, then it is eventually zero near every point.
This is the meromorphic analogue of the identity theorem for analytic functions. -/

/-
PROBLEM
If a meromorphic function on a preconnected open set has `meromorphicOrderAt = ⊤`
at some point (i.e., is locally zero), then it has `meromorphicOrderAt = ⊤` everywhere
on the set. This is the identity theorem for meromorphic functions.

PROVIDED SOLUTION
Define S = {z ∈ U | ∀ᶠ w in nhdsWithin z {z}ᶜ, h w = 0}.

Step 1: z₀ ∈ S. Since h = 0 near z₀ (in nhds z₀), it's also zero in nhdsWithin z₀ {z₀}ᶜ.

Step 2: S is open. If z ∈ S, then h is meromorphic at z and eventually zero in punctured nhd, so meromorphicOrderAt h z = ⊤, meaning h = 0 in some full nhds of z (use meromorphicOrderAt_eq_top_iff). Then for any w in that nhds ∩ U, h = 0 near w too.

Step 3: U \ S is open in U (equivalently, S is closed in U). If z ∈ U \ S, then by MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero, since z ∉ S, h is eventually nonzero near z (the second case). So there's a punctured nhd where h ≠ 0. Then nearby points in U can't have h eventually zero (since h ≠ 0 on parts of their punctured nhds).

Actually more precisely: if z ∈ U \ S, h is eventually nonzero in nhdsWithin z {z}ᶜ, so there exists an open ball around z where h ≠ 0 on the ball minus z. For any w in this ball ∩ U with w ≠ z, if w ∈ S then h = 0 near w, but h ≠ 0 at w (since w is in the ball minus z). Contradiction. And for w = z, z ∉ S by assumption.

Step 4: Since U is preconnected and S is relatively clopen and nonempty (z₀ ∈ S), S ⊇ U.

Conclude: for all z ∈ U, h is eventually zero in nhdsWithin z {z}ᶜ.
-/
theorem meromorphic_identity_theorem {h : ℂ → ℂ} {U : Set ℂ}
    (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hh : MeromorphicOn h U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hz₀_zero : ∀ᶠ w in nhds z₀, h w = 0) :
    ∀ z ∈ U, ∀ᶠ w in nhdsWithin z {z}ᶜ, h w = 0 := by
  -- By definition of S, we know that h is meromorphic at every point in U.
  have h_meromorphic : ∀ z ∈ U, MeromorphicAt h z := by
    aesop;
  -- By definition of S, we know that h is eventually zero near every point in U.
  have h_eventually_zero : ∀ z ∈ U, (∀ᶠ w in nhdsWithin z {z}ᶜ, h w = 0) ∨ (∀ᶠ w in nhdsWithin z {z}ᶜ, h w ≠ 0) := by
    exact?;
  -- By definition of S, we know that h is eventually zero near every point in U. Hence, S is open.
  have hS_open : IsOpen {z ∈ U | ∀ᶠ w in nhdsWithin z {z}ᶜ, h w = 0} := by
    refine' isOpen_iff_mem_nhds.mpr _;
    intro z hz;
    -- Since $h$ is meromorphic at $z$, there exists a neighborhood $V$ of $z$ such that $h$ is analytic on $V \setminus \{z\}$.
    obtain ⟨V, hV_open, hV_z, hV_analytic⟩ : ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ ∀ w ∈ V \ {z}, h w = 0 := by
      rcases Metric.mem_nhdsWithin_iff.mp hz.2 with ⟨ ε, ε_pos, hε ⟩;
      exact ⟨ Metric.ball z ε, Metric.isOpen_ball, Metric.mem_ball_self ε_pos, fun w hw => hε ⟨ hw.1, hw.2 ⟩ ⟩;
    filter_upwards [ hU_open.mem_nhds hz.1, hV_open.mem_nhds hV_z ] with w hw₁ hw₂;
    by_cases hw₃ : w = z <;> simp_all +decide [ eventually_nhdsWithin_iff ];
    filter_upwards [ IsOpen.mem_nhds hV_open hw₂, IsOpen.mem_nhds ( isOpen_compl_singleton ) hw₃ ] with x hx₁ hx₂ using by aesop;
  -- By definition of S, we know that h is eventually zero near every point in U. Hence, U \ S is open.
  have hU_S_open : IsOpen {z ∈ U | ∀ᶠ w in nhdsWithin z {z}ᶜ, h w ≠ 0} := by
    refine' isOpen_iff_mem_nhds.mpr _;
    intro z hz;
    obtain ⟨ ε, ε_pos, hε ⟩ := Metric.mem_nhdsWithin_iff.mp hz.2;
    filter_upwards [ Metric.ball_mem_nhds z ε_pos, hU_open.mem_nhds hz.1 ] with w hw₁ hw₂;
    by_cases hw₃ : w = z <;> simp_all +decide [ Set.subset_def ];
    rw [ eventually_nhdsWithin_iff ] at *;
    filter_upwards [ IsOpen.mem_nhds ( Metric.isOpen_ball ) hw₁, IsOpen.mem_nhds ( isOpen_compl_singleton.preimage continuous_id' ) hw₃ ] with x hx₁ hx₂ using by aesop;
  have hS_nonempty : {z ∈ U | ∀ᶠ w in nhdsWithin z {z}ᶜ, h w = 0}.Nonempty := by
    exact ⟨ z₀, hz₀, hz₀_zero.filter_mono nhdsWithin_le_nhds ⟩;
  have hU_S_empty : {z ∈ U | ∀ᶠ w in nhdsWithin z {z}ᶜ, h w ≠ 0} = ∅ := by
    contrapose! hU_conn;
    norm_num [ IsPreconnected ];
    refine' ⟨ { z | z ∈ U ∧ ∀ᶠ w in nhdsWithin z { z } ᶜ, h w = 0 }, hS_open, { z | z ∈ U ∧ ∀ᶠ w in nhdsWithin z { z } ᶜ, h w ≠ 0 }, hU_S_open, _, _, _, _ ⟩ <;> simp_all +decide [ Set.Nonempty ];
    · exact fun x hx => by cases h_eventually_zero x hx <;> aesop;
    · exact fun x hx hx' => hx'.frequently;
  exact fun z hz => Or.resolve_right ( h_eventually_zero z hz ) fun h => hU_S_empty.subset ⟨ hz, h ⟩

/-! ## Meromorphic order under composition with cosh reflection -/

/-
PROVIDED SOLUTION
Use MeromorphicAt.meromorphicOrderAt_comp with g = coshReflect c, which is analytic and not eventually constant. We have coshReflect c z = c - z, so meromorphicOrderAt (f ∘ coshReflect c) z = meromorphicOrderAt f (coshReflect c z) * ENat.map ... (analyticOrderAt (coshReflect c - const) z). Since coshReflect c is affine (c - s), the map s ↦ (c - s) - (c - z) = z - s has analytic order 1 at z, so the multiplier is 1. Use coshReflect_not_eventuallyConst and analyticAt_coshReflect.
-/
lemma meromorphicOrderAt_comp_coshReflect {f : ℂ → ℂ} {c z : ℂ}
    (hf : MeromorphicAt f (c - z)) :
    meromorphicOrderAt (f ∘ coshReflect c) z = meromorphicOrderAt f (c - z) := by
  -- Apply the theorem that the order of the composition is the product of the orders.
  have h_order : meromorphicOrderAt (f ∘ coshReflect c) z = meromorphicOrderAt f (coshReflect c z) * ENat.map Nat.cast (analyticOrderAt (fun s => coshReflect c s - coshReflect c z) z) := by
    convert MeromorphicAt.meromorphicOrderAt_comp _ _ _ using 1;
    · exact hf;
    · exact?;
    · exact?;
  simp_all +decide [ coshReflect ];
  rw [ analyticOrderAt ];
  split_ifs <;> norm_num;
  · rw [ Metric.eventually_nhds_iff ] at *;
    obtain ⟨ ε, ε_pos, hε ⟩ := ‹_›; specialize hε ( show Dist.dist ( z + ε / 2 ) z < ε from by simpa [ abs_of_pos ε_pos ] ) ; norm_num [ sub_eq_zero, ε_pos.ne' ] at hε;
  · have := Exists.choose_spec ( show ∃ n : ℕ, 0 < n ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ ∀ᶠ s in nhds z, z - s = ( s - z ) ^ n * g s from by
                                  exact ⟨ 1, by norm_num, fun s => -1, by apply_rules [ AnalyticAt.neg, analyticAt_const ], Filter.Eventually.of_forall fun s => by ring ⟩ )
    generalize_proofs at *;
    rcases this with ⟨ hn, g, hg₁, hg₂ ⟩ ; rcases n : ‹∃ n : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ ¬g z = 0 ∧ ∀ᶠ s in nhds z, z - s = ( s - z ) ^ n * g s›.choose with ( _ | _ | n ) <;> simp_all +decide [ pow_succ, mul_assoc ] ;
    · have := ‹∃ n g, AnalyticAt ℂ g z ∧ ¬g z = 0 ∧ ∀ᶠ ( z_1 : ℂ ) in nhds z, z - z_1 = ( z_1 - z ) ^ n * g z_1›.choose_spec.choose_spec.2.2.self_of_nhds; simp_all +decide [ sub_eq_iff_eq_add ] ;
      grind +ring;
    · have := ‹∃ n : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ ¬g z = 0 ∧ ∀ᶠ s in nhds z, z - s = ( s - z ) ^ n * g s›.choose_spec.choose_spec.2.2; simp_all +decide [ pow_succ, mul_assoc ] ;
      have h_div : ∀ᶠ s in nhds z, s ≠ z → -1 = (s - z) ^ ‹ℕ› * ((s - z) * ‹∃ n : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ ¬g z = 0 ∧ ∀ᶠ s in nhds z, z - s = ( s - z ) ^ n * g s›.choose_spec.choose s) := by
        filter_upwards [ this ] with s hs hs' using mul_left_cancel₀ ( sub_ne_zero_of_ne hs' ) <| by linear_combination' hs;
      have h_div : Filter.Tendsto (fun s => (s - z) ^ ‹ℕ› * ((s - z) * ‹∃ n : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ ¬g z = 0 ∧ ∀ᶠ s in nhds z, z - s = ( s - z ) ^ n * g s›.choose_spec.choose s)) (nhdsWithin z {z}ᶜ) (nhds (-1)) := by
        exact tendsto_const_nhds.congr' ( by filter_upwards [ self_mem_nhdsWithin, h_div.filter_mono nhdsWithin_le_nhds ] with s hs hs'; aesop );
      have h_div : Filter.Tendsto (fun s => (s - z) ^ ‹ℕ› * ((s - z) * ‹∃ n : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ ¬g z = 0 ∧ ∀ᶠ s in nhds z, z - s = ( s - z ) ^ n * g s›.choose_spec.choose s)) (nhdsWithin z {z}ᶜ) (nhds 0) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( ContinuousAt.tendsto ( by exact ContinuousAt.mul ( ContinuousAt.pow ( continuousAt_id.sub continuousAt_const ) _ ) ( ContinuousAt.mul ( continuousAt_id.sub continuousAt_const ) ( ‹∃ n : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ ¬g z = 0 ∧ ∀ᶠ s in nhds z, z - s = ( s - z ) ^ n * g s›.choose_spec.choose_spec.1.continuousAt ) ) ) |> fun h => h.trans ( by norm_num ) );
      exact absurd ( tendsto_nhds_unique ‹Tendsto ( fun s => ( s - z ) ^ _ * ( ( s - z ) * _ ) ) ( nhdsWithin z { z } ᶜ ) ( nhds ( -1 ) ) › h_div ) ( by norm_num );
  · exact False.elim <| ‹¬AnalyticAt ℂ ( fun s => z - s ) z› <| by apply_rules [ AnalyticAt.sub, analyticAt_id, analyticAt_const ] ;

/-! ## Main theorem: Cosh-symmetric pole structure -/

/-
PROBLEM
**Cosh-Symmetric Pole Structure Theorem.**

If `f` is meromorphic on a preconnected open set `U` that is symmetric under the
cosh reflection `s ↦ c - s`, and `f(s) = f(c - s)` on some open nonempty subset
`V ⊆ U` (the region of convergence overlapping the cosh strip), then the meromorphic
order of `f` is symmetric:
  `meromorphicOrderAt f z = meromorphicOrderAt f (c - z)` for all `z ∈ U`.

In particular, poles and their orders are symmetric under the cosh reflection.

This is a consequence of the identity theorem for meromorphic functions: the function
`h(s) = f(s) - f(c - s)` is meromorphic on `U` and zero on `V`, hence zero everywhere
on `U`.

PROVIDED SOLUTION
Define g(s) = f(c - s) = f ∘ coshReflect c. Define h = f - g.

1. g is meromorphic on U by meromorphicOn_comp_coshReflect.
2. h = f - g is meromorphic on U.
3. h = 0 on V since f(s) = f(c-s) for s ∈ V (by hf_sym).
4. Pick z₀ ∈ V (hV_nonempty). Then h = 0 on V, which is open, so h = 0 near z₀ (in nhds z₀).
   More precisely, ∀ᶠ w in nhds z₀, h w = 0 follows from hV_open and hf_sym.
5. By meromorphic_identity_theorem, ∀ z ∈ U, ∀ᶠ w in nhdsWithin z {z}ᶜ, h w = 0.
6. This means ∀ z ∈ U, f =ᶠ[nhdsWithin z {z}ᶜ] g.
   (Since h w = f w - g w = 0 means f w = g w.)
7. By meromorphicOrderAt_congr, meromorphicOrderAt f z = meromorphicOrderAt g z for all z ∈ U.
8. By meromorphicOrderAt_comp_coshReflect, meromorphicOrderAt g z = meromorphicOrderAt f (c - z).
9. Combine steps 7 and 8.
-/
theorem cosh_symmetric_pole_structure
    (f : ℂ → ℂ) (c : ℂ) (U V : Set ℂ)
    (hU_open : IsOpen U)
    (hU_conn : IsPreconnected U)
    (hU_sym : CoshSymmetric c U)
    (hV_open : IsOpen V)
    (hV_sub : V ⊆ U)
    (hV_nonempty : V.Nonempty)
    (hf_mero : MeromorphicOn f U)
    (hf_sym : ∀ s ∈ V, f s = f (c - s)) :
    ∀ z ∈ U, meromorphicOrderAt f z = meromorphicOrderAt f (c - z) := by
  -- Let $h(s) = f(s) - f(c - s)$.
  set h : ℂ → ℂ := fun s => f s - f (c - s);
  -- By the identity theorem for meromorphic functions, since $h$ is meromorphic on $U$ and $h = 0$ on $V$, we have $h = 0$ everywhere on $U$.
  have h_zero : ∀ z ∈ U, ∀ᶠ w in nhdsWithin z {z}ᶜ, h w = 0 := by
    apply meromorphic_identity_theorem hU_open hU_conn;
    convert hf_mero.sub ( meromorphicOn_comp_coshReflect hf_mero hU_sym ) using 1;
    exact hV_sub hV_nonempty.some_mem;
    filter_upwards [ hV_open.mem_nhds hV_nonempty.some_mem ] with w hw using sub_eq_zero.mpr ( hf_sym w hw );
  -- Since $h = 0$ everywhere on $U$, we have $f = f \circ \text{coshReflect } c$ everywhere on $U$.
  have h_eq : ∀ z ∈ U, meromorphicOrderAt f z = meromorphicOrderAt (f ∘ coshReflect c) z := by
    intro z hz;
    apply_rules [ meromorphicOrderAt_congr ];
    filter_upwards [ h_zero z hz ] with w hw using sub_eq_zero.mp hw;
  intro z hz; rw [ h_eq z hz ] ; rw [ meromorphicOrderAt_comp_coshReflect ] ;
  exact hf_mero _ ( hU_sym _ hz )

end