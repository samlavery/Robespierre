import Mathlib

open Real Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace Robespierre

/-- The kernel center θ = π/6, the unique angle in [−π/2, π/2] with sin θ = 1/2. -/
def θ : ℝ := π / 6

/-- The weight decay ratio r = 2(π−3)/π. Since 3 < π < 4, we have 0 < r < 1. -/
def r : ℝ := 2 * (π - 3) / π

/-- The prime-scaling factor: primes are mapped to φ(p) = (π/3)·p on the π-lattice. -/
def primeScale : ℝ := π / 3

theorem θ_eq : θ = π / 6 := rfl

theorem θ_pos : 0 < θ := by
  unfold θ
  positivity

theorem two_θ_eq : 2 * θ = π / 3 := by
  unfold θ
  ring

theorem sin_θ : Real.sin θ = 1 / 2 := by
  unfold θ
  exact Real.sin_pi_div_six

theorem arcsin_half_eq_θ : Real.arcsin (1 / 2) = θ := by
  rw [θ_eq]
  rw [← Real.sin_pi_div_six]
  simpa using
    (Real.arcsin_sin
      (show -(π / 2) ≤ π / 6 by linarith [Real.pi_pos])
      (show π / 6 ≤ π / 2 by linarith [Real.pi_pos]))

theorem θ_ne_half : θ ≠ 1 / 2 := by
  unfold θ
  linarith [Real.pi_gt_three]

theorem r_pos : 0 < r := by
  unfold r
  exact div_pos (mul_pos zero_lt_two (sub_pos.mpr Real.pi_gt_three)) Real.pi_pos

theorem r_lt_one : r < 1 := by
  unfold r
  rw [div_lt_iff₀ Real.pi_pos]
  linarith [Real.pi_gt_three, Real.pi_le_four]

theorem r_nonneg : 0 ≤ r := le_of_lt r_pos

/-- The prime-log frequency for prime p: uₚ = log((π/3)·p). -/
def u (p : ℕ) : ℝ := Real.log (primeScale * p)

/-- The weight of the p-th prime term: aₚ = (π/6) · rᵖ. -/
def a (p : ℕ) : ℝ := (π / 6) * r ^ p

theorem a_pos (p : ℕ) : 0 < a p := by
  unfold a
  exact mul_pos (by positivity) (pow_pos r_pos p)

/-- A single term of the Robespierre zeta function for prime p. -/
def zetaTerm (s : ℂ) (p : ℕ) : ℂ :=
  ↑(a p) * Complex.cosh ((s - ↑θ) * ↑(u p))

/-- The Robespierre zeta function Ξ(s) = Σₚ aₚ · cosh((s − θ)·uₚ),
    summed over primes. Non-prime indices contribute 0. -/
def Ξ (s : ℂ) : ℂ :=
  ∑' (p : ℕ), if p.Prime then zetaTerm s p else 0

/-- The reflection map s ↦ 2θ − s. -/
def reflect (s : ℂ) : ℂ := 2 * ↑θ - s

/-- Each cosh term is invariant under s ↦ 2θ − s, because cosh is even. -/
theorem zetaTerm_reflect (s : ℂ) (p : ℕ) :
    zetaTerm (reflect s) p = zetaTerm s p := by
  unfold zetaTerm reflect
  congr 1
  have h : (2 * (θ : ℂ) - s - ↑θ) = -(s - ↑θ) := by
    ring
  rw [h, neg_mul, Complex.cosh_neg]

/-- The Robespierre zeta function satisfies Ξ(2θ − s) = Ξ(s). -/
theorem Ξ_reflect (s : ℂ) : Ξ (reflect s) = Ξ s := by
  unfold Ξ
  congr 1
  ext p
  split_ifs with hp
  · exact zetaTerm_reflect s p
  · rfl

/-- The reflect map is an involution. -/
theorem reflect_involutive : Function.Involutive reflect := by
  intro s
  unfold reflect
  ring

/-- On the critical line Re(s) = θ, each term of Ξ is real. -/
theorem zetaTerm_real_on_criticalLine (t : ℝ) (p : ℕ) :
    (zetaTerm (↑θ + ↑t * Complex.I) p).im = 0 := by
  unfold zetaTerm
  norm_num [Complex.cosh, Complex.exp_re, Complex.exp_im]

/-- Each term satisfies conj(Ξₚ(s)) = Ξₚ(conj s), since all coefficients are real. -/
theorem zetaTerm_conj (s : ℂ) (p : ℕ) :
    starRingEnd ℂ (zetaTerm s p) = zetaTerm (starRingEnd ℂ s) p := by
  unfold zetaTerm
  simp [Complex.ext_iff]
  norm_num [Complex.cosh, Complex.exp_re, Complex.exp_im, Complex.sub_re, Complex.sub_im]
  ring_nf
  aesop

/-- The generators σ and τ commute: σ(τ(s)) = τ(σ(s)). -/
theorem reflect_conj_comm (s : ℂ) :
    reflect (starRingEnd ℂ s) = starRingEnd ℂ (reflect s) := by
  unfold reflect
  norm_num [Complex.ext_iff]

/-- On the critical line, reflection equals conjugation: 2θ − (θ+it) = conj(θ+it). -/
theorem reflect_eq_conj_on_criticalLine (t : ℝ) :
    reflect (↑θ + ↑t * Complex.I) = starRingEnd ℂ (↑θ + ↑t * Complex.I) := by
  unfold reflect
  norm_num [Complex.ext_iff]
  ring

end Robespierre
end
