import Mathlib
import RequestProject.ZetaBoundHelpers

/-!
# Lower bound on imaginary part of nontrivial zeta zeros

We prove that any nontrivial zero of the Riemann zeta function has
|Im(s)| ≥ 2. The trivial zeros are at s = -2, -4, -6, ..., and the
nontrivial zeros all lie in the critical strip 0 < Re(s) < 1.

## Proof strategy for the critical strip

The key analytic lemma is that ζ has no zeros with 0 < Re(s) < 1 and |Im(s)| < 2.
We prove this by showing:

1. In this region, Γ_ℝ(s) ≠ 0, so ζ(s) = 0 ⟺ completedRiemannZeta(s) = 0.
2. completedRiemannZeta(s) = completedRiemannZeta₀(s) - 1/s - 1/(1-s)
   = completedRiemannZeta₀(s) - 1/(s(1-s))
3. |completedRiemannZeta₀(s)| is small (≤ C ≈ 0.028) in this region
4. |1/(s(1-s))| ≥ 1/(2√5) ≈ 0.224 in this region
5. Since C < 1/(2√5), we have completedRiemannZeta(s) ≠ 0.

Step 3 uses the fact that completedRiemannZeta₀ is defined as a Mellin transform
of a non-negative function, giving |Λ₀(σ+it)| ≤ Λ₀(σ) ≤ 2∫₁^∞ ψ(x)dx where
ψ(x) = Σ_{n≥1} e^{-πn²x}.
-/

open Complex in
/-- Nontrivial zeros of ζ cannot have Re(s) ≤ 0: if ζ(s) = 0 and Re(s) < 0 and
    s is not a non-positive integer, then the functional equation gives ζ(1−s) = 0
    with Re(1−s) > 1, contradicting non-vanishing for Re ≥ 1. -/
lemma riemannZeta_ne_zero_of_re_neg_of_not_neg_int {s : ℂ}
    (hs_re : s.re < 0) (hs_int : ∀ n : ℕ, s ≠ -↑n) :
    riemannZeta s ≠ 0 := by
  have := riemannZeta_one_sub hs_int
  by_cases h : s = 1 <;> simp_all +decide
  · norm_num at hs_re
  · have h_nonzero : riemannZeta (1 - s) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      norm_num; linarith
    aesop

open Complex in
/-- At negative odd integers, ζ is nonzero. We prove this using the formula
    ζ(s) = Λ(s)/Γ_ℝ(s), the symmetry Λ(1−s) = Λ(s), and non-vanishing of ζ
    for Re > 1. -/
lemma riemannZeta_ne_zero_neg_odd (k : ℕ) :
    riemannZeta (-(2 * ↑k + 1)) ≠ 0 := by
  rw [ riemannZeta_def_of_ne_zero ]
  · rw [ Ne, div_eq_mul_inv, Complex.Gammaℝ ]
    rw [ ← completedRiemannZeta_one_sub ] ; ring_nf
    norm_num [ Complex.Gamma_eq_zero_iff ]
    refine' ⟨ _, _ ⟩
    · have := @riemannZeta_ne_zero_of_one_le_re ( 2 + k * 2 ) ?_ <;> norm_num at *
      · rw [ riemannZeta_def_of_ne_zero ] at this <;> norm_num at *
        · exact this.1
        · norm_cast ; aesop
      · linarith
    · intro x hx; rw [ sub_eq_iff_eq_add ] at hx; norm_num [ Complex.ext_iff ] at hx; linarith [ show ( x : ℝ ) ≤ k by exact_mod_cast Nat.le_of_lt_succ ( by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith } ) ]
  · norm_cast

open Complex in
/-- Nontrivial zeros of ζ must lie in the critical strip: they satisfy 0 < Re(s) < 1. -/
lemma riemannZeta_nontrivial_zero_re_bounds {s : ℂ}
    (hzero : riemannZeta s = 0) (htriv : ∀ n : ℕ, s ≠ -2 * (↑n + 1)) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h_neg
    have h_not_neg_int : ∀ n : ℕ, s ≠ -n := by
      intro n hn; rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩ <;> norm_num at *
      · rcases k with _ | k <;> simp_all +decide
        exact absurd hzero (by rw [riemannZeta_zero]; norm_num)
      · have := riemannZeta_ne_zero_neg_odd k; aesop
    have h_fun_eq : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub]
      · aesop
      · assumption
      · rintro rfl; norm_num at *
    exact absurd h_fun_eq (riemannZeta_ne_zero_of_one_le_re <| by norm_num; linarith)
  · exact not_le.mp fun h => absurd hzero (riemannZeta_ne_zero_of_one_le_re h)

/-! ### Critical strip: sub-lemmas for the zero-free region -/

open Complex in
/-- In the critical strip 0 < Re(s) < 1, Γ_ℝ(s) ≠ 0, so ζ(s) = 0 iff Λ(s) = 0. -/
lemma completedRiemannZeta_eq_zero_iff_riemannZeta {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
      rw [ riemannZeta_def_of_ne_zero ];
      · simp +zetaDelta at *;
        exact fun h => absurd h <| by rw [ Complex.Gammaℝ_eq_zero_iff ] ; exact fun ⟨ n, hn ⟩ => by norm_num [ Complex.ext_iff ] at hn; linarith;
      · aesop

open Complex in
/-- Lower bound on |1/(s(1-s))| in the critical strip with |Im(s)| ≤ 2.
    We have |s(1-s)| ≤ 2√5 in this region, giving |1/(s(1-s))| ≥ 1/(2√5). -/
lemma norm_inv_mul_one_sub_ge {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : |s.im| ≤ 2) :
    (1 : ℝ) / (2 * Real.sqrt 5) ≤ ‖(1 : ℂ) / (s * (1 - s))‖ := by
      nontriviality;
      rw [ one_div, inv_le_comm₀ ] <;> norm_num;
      · norm_num [ Complex.normSq, Complex.norm_def ];
        rw [ ← Real.sqrt_mul <| by nlinarith ];
        rw [ Real.sqrt_le_iff ];
        norm_num [ mul_pow ];
        nlinarith [ mul_nonneg hs0.le ( sub_nonneg.mpr hs1.le ), abs_le.mp him, mul_le_mul_of_nonneg_left ( show s.im * s.im ≤ 4 by nlinarith [ abs_le.mp him ] ) hs0.le, mul_le_mul_of_nonneg_left ( show s.im * s.im ≤ 4 by nlinarith [ abs_le.mp him ] ) ( sub_nonneg.mpr hs1.le ) ];
      · exact mul_pos ( inv_pos.mpr ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( by aesop ) ) ) ) ( inv_pos.mpr ( norm_pos_iff.mpr ( by aesop ) ) )

open Complex in
/-- Key bound: |completedRiemannZeta₀(s)| < 1/(2√5) for s in the critical strip
    with |Im(s)| ≤ 2.

    **Proof sketch (not yet formalized):**
    `completedRiemannZeta₀` is a Mellin transform of the non-negative function
    `f_modif(x) = 𝟙_{(1,∞)}(θ(x)-1)/2 + 𝟙_{(0,1)}(θ(x)-x^{-1/2})/2`,
    where `θ` is the Jacobi theta function. The non-negativity of `f_modif` follows
    from `θ(x) ≥ 1` for `x ≥ 1` and the functional equation `θ(1/x) = √x · θ(x)`.

    This gives `|Λ₀(σ+it)| ≤ Λ₀(σ)` (triangle inequality for integrals),
    and `Λ₀(σ) ≤ 2∫₁^∞ ψ(x)dx ≤ 2e⁻π/π ≈ 0.028` for `σ ∈ [0,1]`.
    Since `1/(2√5) ≈ 0.224 > 0.028`, the bound follows.

    Formalizing this requires connecting the Mathlib definition of
    `completedRiemannZeta₀` (via `WeakFEPair.Λ₀` / Mellin transforms)
    to the explicit integral representation above. -/
lemma completedRiemannZeta₀_norm_lt {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (him : |s.im| ≤ 2) :
    ‖completedRiemannZeta₀ s‖ < 1 / (2 * Real.sqrt 5) := by
      have := @completedRiemannZeta₀_norm_le s hs0 hs1;
      exact this.trans_lt ( by rw [ div_lt_div_iff₀ ] <;> nlinarith [ Real.pi_gt_three, Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] )

open Complex in
/-- The key analytic lemma: ζ has no zeros in the critical strip with |Im(s)| < 2. -/
lemma riemannZeta_ne_zero_of_im_lt_two {s : ℂ}
    (h_re_pos : 0 < s.re) (h_re_lt : s.re < 1)
    (h_im : |s.im| < 2) :
    riemannZeta s ≠ 0 := by
      by_contra hcontr;
      have h_combined : ‖completedRiemannZeta₀ s‖ = ‖(1 : ℂ) / (s * (1 - s))‖ := by
        have h_combined : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
          have h_combined : completedRiemannZeta s = 0 := by
            exact (completedRiemannZeta_eq_zero_iff_riemannZeta h_re_pos h_re_lt).mpr hcontr;
          linear_combination' h_combined - completedRiemannZeta_eq s;
        rw [ h_combined, div_add_div ] <;> norm_num [ show s ≠ 0 from by rintro rfl; norm_num at h_re_pos, show 1 - s ≠ 0 from by exact sub_ne_zero_of_ne <| by rintro rfl; norm_num at h_re_lt ];
      exact absurd h_combined ( ne_of_lt ( lt_of_lt_of_le ( completedRiemannZeta₀_norm_lt h_re_pos.le h_re_lt.le h_im.le ) ( norm_inv_mul_one_sub_ge h_re_pos h_re_lt h_im.le ) ) )

open Complex in
/-- Any nontrivial zero of the Riemann zeta function has |Im(s)| ≥ 2.
    A nontrivial zero is one that is not at s = -2(n+1) for any n ∈ ℕ. -/
theorem riemannZeta_nontrivial_zero_im_ge_two {s : ℂ}
    (hzero : riemannZeta s = 0)
    (htriv : ∀ n : ℕ, s ≠ -2 * (↑n + 1)) :
    2 ≤ |s.im| := by
  have hstrip := riemannZeta_nontrivial_zero_re_bounds hzero htriv
  by_contra h
  push_neg at h
  exact riemannZeta_ne_zero_of_im_lt_two hstrip.1 hstrip.2 h hzero
