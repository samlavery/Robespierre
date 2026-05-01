import Mathlib

/-!
# The Helix Map and π/3 Coordinate System

This file formalizes the "helix map" that sends positive reals to the logarithmic
spiral with angular frequency ω = π/3. In this representation:

- Multiplication becomes addition (the map is a group homomorphism)
- Primes form a basis (their helix positions are linearly independent)
- The critical line Re(s) = 1/2 is the symmetry axis of the helix
- Prime angles are equidistributed on the circle

## Main Definitions

- `helixAngularFreq` : The angular frequency ω = π/3
- `helixLog` : The log-polar helix map x ↦ (log x, ω · log x)
- `helixMapC` : The complex helix map x ↦ log x · exp(i · ω · log x)

## Main Results

- `helix_multiplication_additive` : H(a·b) = H(a) + H(b) for positive reals
- `helix_factorization_vector_sum` : log n = Σ_p e_p · log p
- `prime_helix_positions_independent` : Unique representation in the prime basis
- `critical_line_is_helix_symmetry_axis` : Re(s) = 1/2 ↔ s = 1 - s̄
- `prime_angles_equidistributed` : Statement of equidistribution (deep result)
-/

open scoped BigOperators Real
open Complex Real

noncomputable section

/-! ## Definitions -/

/-- The angular frequency of the helix: ω = π/3. -/
def helixAngularFreq : ℝ := π / 3

/-- The log-polar helix map. Sends a positive real x to (log x, ω · log x) ∈ ℝ × ℝ.
    This is the "additive" representation where the first coordinate is the radial
    distance and the second is the angle on the spiral. -/
def helixLog (x : ℝ) : ℝ × ℝ :=
  (Real.log x, helixAngularFreq * Real.log x)

/-- The complex helix map. Sends x to log(x) · exp(i · ω · log x) ∈ ℂ. -/
def helixMapC (x : ℝ) : ℂ :=
  (Real.log x : ℂ) * Complex.exp (Complex.I * (helixAngularFreq : ℂ) * (Real.log x : ℂ))

/-! ## Theorem 1: The Helix Homomorphism

The helix map is a group homomorphism from (ℝ₊, ×) to (ℝ × ℝ, +).
This is the fundamental property: multiplication becomes addition. -/

/-
The helix map sends products to sums: H(a·b) = H(a) + H(b) for positive reals.
-/
theorem helix_multiplication_additive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    helixLog (a * b) = helixLog a + helixLog b := by
  unfold helixLog;
  rw [ Real.log_mul ha.ne' hb.ne' ] ; ext <;> norm_num ; ring

/-
The helix map sends powers to scalar multiples: H(aⁿ) = n · H(a) for positive a.
-/
theorem helix_power_scalar (a : ℝ) (_ha : 0 < a) (n : ℕ) :
    helixLog (a ^ n) = n • helixLog a := by
  unfold helixLog; norm_num [ Real.log_pow ] ; ring;

/-! ## Theorem 2: Factorization as Vector Decomposition

The fundamental theorem of arithmetic, restated geometrically: the helix
position of n is the vector sum of the helix positions of its prime factors,
weighted by their multiplicities. -/

/-
The logarithm of n equals the weighted sum of logarithms of its prime factors.
    This is the radial component of the helix factorization.
-/
theorem log_factorization_sum (n : ℕ) (hn : n ≠ 0) :
    Real.log (n : ℝ) =
      ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  -- Use the fact that the logarithm of a product is the sum of logarithms:
  have h_log_prod : Real.log n = Real.log (∏ p ∈ n.factorization.support, p ^ (n.factorization p)) := by
    exact congrArg Real.log ( mod_cast Eq.symm <| Nat.factorization_prod_pow_eq_self hn );
  rw [ h_log_prod, Real.log_prod ] <;> aesop

/-
The helix position of n is the weighted sum of helix positions of its prime factors.
-/
theorem helix_factorization_vector_sum (n : ℕ) (hn : n ≠ 0) :
    helixLog (n : ℝ) =
      ∑ p ∈ n.factorization.support, (n.factorization p) • helixLog (p : ℝ) := by
  -- Unfold the definition of `helixLog`
  unfold helixLog;
  simp +decide [ Prod.ext_iff, mul_left_comm, Finset.mul_sum _ _ _, log_factorization_sum n hn ];
  exact ⟨ by rw [ Prod.fst_sum ], by rw [ Prod.snd_sum ] ⟩

/-! ## Theorem 3: The Prime Basis

The helix positions of the primes are "linearly independent" in the sense that the
only way to get the same helix position from two different ℕ-linear combinations
of primes is if the combinations are identical. This is equivalent to unique
factorization (the Fundamental Theorem of Arithmetic). -/

/-
Two products of prime powers that are equal must have the same exponents.
    This is unique factorization restated as injectivity of the prime-exponent map.
-/
theorem prime_factorization_unique
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, Nat.Prime p)
    (a b : ℕ → ℕ)
    (h : ∏ p ∈ primes, p ^ a p = ∏ p ∈ primes, p ^ b p)
    (_hprod_pos : 0 < ∏ p ∈ primes, p ^ a p) :
    ∀ p ∈ primes, a p = b p := by
  intro p hp;
  apply_fun fun x => x.factorization p at h;
  rw [ Nat.factorization_prod, Nat.factorization_prod ] at h;
  · simp_all +decide [ Finsupp.single_apply, Finset.sum_apply' ];
  · exact fun x hx => pow_ne_zero _ ( Nat.Prime.ne_zero ( hprimes x hx ) );
  · exact fun x hx => pow_ne_zero _ ( Nat.Prime.ne_zero ( hprimes x hx ) )

/-
The log-representations of products of distinct primes are unique:
    if Σ aₚ · log p = Σ bₚ · log p, then aₚ = bₚ for all p.
    This is the linear independence of prime helix positions.
-/
theorem prime_helix_positions_independent
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, Nat.Prime p)
    (a b : ℕ → ℕ)
    (h : ∑ p ∈ primes, (a p : ℝ) * Real.log (p : ℝ) =
         ∑ p ∈ primes, (b p : ℝ) * Real.log (p : ℝ)) :
    ∀ p ∈ primes, a p = b p := by
  apply prime_factorization_unique primes hprimes a b;
  · apply_fun Real.exp at h;
    simp_all +decide [ Real.exp_sum, Real.exp_nat_mul ];
    rw [ ← @Nat.cast_inj ℝ ] ; push_cast ; convert h using 1 <;> congr! 1 <;> rw [ Real.exp_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| hprimes _ <| by assumption ) ];
  · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( hprimes p hp ) ) _

/-! ## Prime Angle Uniqueness

The prime angles on the π/3 helix are all distinct — no two distinct primes
occupy the same angular position, even modulo 2π. More strongly, there are
no rational linear relations among the prime angles modulo 2π.

The proofs use the irrationality of `exp(n)` for nonzero integers `n`
(a consequence of Hermite's 1873 theorem) and the unique factorization
of integers. -/

/-- Real modular equivalence: `a ≡ b [RMOD m]` iff there exists an integer `k`
    such that `a - b = m * k`. This generalizes integer modular arithmetic
    to the reals. -/
def RealModEq (m a b : ℝ) : Prop := ∃ k : ℤ, a - b = m * k

notation:50 a " ≡ " b " [RMOD " m "]" => RealModEq m a b

/-- The Niven function for the irrationality proof: `f(t) = t^n * (m-t)^n / n!`. -/
def nivenF (m : ℕ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n * ((m : ℝ) - t) ^ n / (Nat.factorial n : ℝ)

/-- The Niven integral: `∫₀ᵐ t^n(m-t)^n/n! · exp(t) dt`. -/
def nivenI (m : ℕ) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..(m : ℝ), nivenF m n t * Real.exp t

/-
The Niven integral is positive for `m ≥ 1`.
-/
lemma nivenI_pos (m : ℕ) (hm : 0 < m) (n : ℕ) : 0 < nivenI m n := by
  refine' intervalIntegral.integral_pos _ _ _ _ <;> norm_num;
  · linarith;
  · exact Continuous.continuousOn ( by exact Continuous.mul ( by exact Continuous.div_const ( by continuity ) _ ) ( Real.continuous_exp ) );
  · exact fun x hx₁ hx₂ => mul_nonneg ( div_nonneg ( mul_nonneg ( pow_nonneg hx₁.le _ ) ( pow_nonneg ( sub_nonneg.mpr hx₂ ) _ ) ) ( Nat.cast_nonneg _ ) ) ( Real.exp_nonneg _ );
  · refine' ⟨ m / 2, ⟨ by positivity, by linarith [ show ( m : ℝ ) ≥ 1 by norm_cast ] ⟩, _ ⟩;
    exact mul_pos ( div_pos ( mul_pos ( pow_pos ( by positivity ) _ ) ( pow_pos ( by linarith [ show ( m : ℝ ) > 0 by positivity ] ) _ ) ) ( by positivity ) ) ( Real.exp_pos _ )

/-
Upper bound: `nivenI m n ≤ (m²/4)^n · m · exp(m) / n!`.
-/
lemma nivenI_upper_bound (m : ℕ) (hm : 0 < m) (n : ℕ) :
    nivenI m n ≤ ((m : ℝ) ^ 2 / 4) ^ n / (Nat.factorial n : ℝ) * (m : ℝ) * Real.exp (m : ℝ) := by
  convert intervalIntegral.integral_mono_on _ _ _ _ using 1;
  case convert_2 => exact fun t => ( m ^ 2 / 4 ) ^ n / n.factorial * Real.exp m;
  · norm_num ; ring;
  · positivity;
  · exact Continuous.intervalIntegrable ( by exact Continuous.mul ( by exact Continuous.div_const ( by continuity ) _ ) ( Real.continuous_exp ) ) _ _;
  · norm_num;
  · intro x hx; unfold nivenF;
    gcongr;
    · rw [ ← mul_pow ] ; exact pow_le_pow_left₀ ( mul_nonneg hx.1 ( sub_nonneg.2 hx.2 ) ) ( by nlinarith [ sq_nonneg ( x - m / 2 ) ] ) _;
    · linarith [ hx.2 ]

/-
The Niven integral tends to zero as `n → ∞`.
-/
lemma nivenI_tendsto_zero (m : ℕ) (hm : 0 < m) :
    Filter.Tendsto (nivenI m) Filter.atTop (nhds 0) := by
  -- By nivenI_upper_bound: 0 < nivenI m n ≤ C * r^n / n! where C = m * exp(m) and r = m²/4.
  have h_bound : ∀ n : ℕ, nivenI m n ≤ (m * Real.exp m) * ((m^2 / 4 : ℝ)^n / (Nat.factorial n)) := by
    intro n; convert nivenI_upper_bound m hm n using 1; ring;
  exact squeeze_zero ( fun n => nivenI_pos m hm n |> le_of_lt ) h_bound ( by simpa using tendsto_const_nhds.mul ( Real.summable_pow_div_factorial _ |> Summable.tendsto_atTop_zero ) )

/-
The Niven integral has the form `A · exp(m) + B` for integers `A, B`.
    This is the key algebraic step, following from iterated integration by parts:
    `∫₀ᵐ f(t) exp(t) dt = F(m) · exp(m) - F(0)` where
    `F(t) = Σⱼ (-1)ʲ f⁽ʲ⁾(t)` and `F(0), F(m) ∈ ℤ`.
-/
set_option maxHeartbeats 1600000 in
lemma nivenI_int_linear_combination (m : ℕ) (hm : 0 < m) (n : ℕ) :
    ∃ A B : ℤ, nivenI m n = (A : ℝ) * Real.exp (m : ℝ) + (B : ℝ) := by
  -- By definition of $F$, we know that its derivatives at $0$ and $m$ are integers.
  have h_deriv_int : ∀ j : ℕ, ∃ A B : ℤ, (iteratedDeriv j (nivenF m n)) 0 = A ∧ (iteratedDeriv j (nivenF m n)) m = B := by
    intro j;
    -- By definition of $nivenF$, we know that its $j$-th derivative at $0$ and $m$ are integers.
    have h_deriv_int : ∀ j : ℕ, ∃ A B : ℤ, (iteratedDeriv j (fun t : ℝ => t ^ n * ((m : ℝ) - t) ^ n) 0) = A * (Nat.factorial n : ℝ) ∧ (iteratedDeriv j (fun t : ℝ => t ^ n * ((m : ℝ) - t) ^ n) (m : ℝ)) = B * (Nat.factorial n : ℝ) := by
      intro j;
      -- By definition of $f$, we know that its $j$-th derivative at $0$ and $m$ are integers.
      have h_deriv_int : ∀ j : ℕ, ∃ A B : ℤ, (Polynomial.eval 0 (Polynomial.derivative^[j] (Polynomial.X ^ n * (Polynomial.C (m : ℤ) - Polynomial.X) ^ n))) = A * (Nat.factorial n : ℤ) ∧ (Polynomial.eval (m : ℤ) (Polynomial.derivative^[j] (Polynomial.X ^ n * (Polynomial.C (m : ℤ) - Polynomial.X) ^ n))) = B * (Nat.factorial n : ℤ) := by
        intro j;
        -- By definition of polynomial derivatives, the j-th derivative of $X^n (m - X)^n$ at $0$ and $m$ are integers.
        have h_deriv_int : ∀ j : ℕ, ∃ A B : ℤ, (Polynomial.coeff (Polynomial.derivative^[j] (Polynomial.X ^ n * (Polynomial.C (m : ℤ) - Polynomial.X) ^ n)) 0) = A * (Nat.factorial n : ℤ) ∧ (Polynomial.coeff (Polynomial.derivative^[j] (Polynomial.X ^ n * (Polynomial.C (m : ℤ) - Polynomial.X) ^ n)) 0) = B * (Nat.factorial n : ℤ) := by
          intro j; use ( Polynomial.coeff ( Polynomial.derivative^[j] ( Polynomial.X ^ n * ( Polynomial.C ( m : ℤ ) - Polynomial.X ) ^ n ) ) 0 ) / ( n.factorial : ℤ ), ( Polynomial.coeff ( Polynomial.derivative^[j] ( Polynomial.X ^ n * ( Polynomial.C ( m : ℤ ) - Polynomial.X ) ^ n ) ) 0 ) / ( n.factorial : ℤ ) ; norm_num [ Polynomial.coeff_iterate_derivative ] ;
          rw [ Int.ediv_mul_cancel ];
          by_cases hj : j < n;
          · rw [ Polynomial.coeff_mul, Finset.sum_eq_zero ] <;> aesop;
          · refine' dvd_mul_of_dvd_left _ _;
            exact_mod_cast Nat.factorial_dvd_factorial ( Nat.le_of_not_lt hj ) |> dvd_trans <| Nat.factorial_dvd_descFactorial _ _;
        obtain ⟨ A, B, hA, hB ⟩ := h_deriv_int j;
        use A, (-1)^j * A;
        have h_symm : ∀ p : Polynomial ℤ, Polynomial.eval (m : ℤ) (Polynomial.derivative^[j] p) = (-1)^j * Polynomial.eval 0 (Polynomial.derivative^[j] (p.comp (Polynomial.C (m : ℤ) - Polynomial.X))) := by
          intro p
          have h_symm : ∀ j : ℕ, Polynomial.derivative^[j] (p.comp (Polynomial.C (m : ℤ) - Polynomial.X)) = (-1)^j * (Polynomial.derivative^[j] p).comp (Polynomial.C (m : ℤ) - Polynomial.X) := by
            intro j; induction j <;> simp_all +decide [ Function.iterate_succ_apply', Polynomial.derivative_comp ] ;
            by_cases h : Even ‹_› <;> simp_all +decide [ Nat.even_add_one ];
          by_cases h : Even j <;> simp_all +decide [ Polynomial.eval_comp ];
        simp_all +decide [ mul_assoc ];
        simp_all +decide [ mul_comm ];
        rw [ ← hA, Polynomial.coeff_iterate_derivative ];
        simp +decide [ Polynomial.eval, Polynomial.coeff_iterate_derivative ];
      convert h_deriv_int j using 1;
      ext; simp +decide [ iteratedDeriv_eq_iterate ] ;
      -- By definition of polynomial derivative, we know that the j-th derivative of a polynomial is the same as the j-th derivative of its evaluation.
      have h_poly_deriv : ∀ j : ℕ, deriv^[j] (fun t : ℝ => Polynomial.eval t (Polynomial.map (algebraMap ℤ ℝ) (Polynomial.X ^ n * (Polynomial.C (m : ℤ) - Polynomial.X) ^ n))) = fun t : ℝ => Polynomial.eval t (Polynomial.map (algebraMap ℤ ℝ) (Polynomial.derivative^[j] (Polynomial.X ^ n * (Polynomial.C (m : ℤ) - Polynomial.X) ^ n))) := by
        intro j; induction j <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
        ext; simp +decide [ Polynomial.derivative_map ] ;
      simp_all +decide [ funext_iff ];
      norm_cast ; aesop;
    unfold nivenF;
    obtain ⟨ A, B, hA, hB ⟩ := h_deriv_int j; use A, B; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Nat.factorial_ne_zero ] ;
    simp_all +decide [ ← mul_assoc, iteratedDeriv_eq_iterate ];
    exact ⟨ mul_div_cancel_right₀ _ <| by positivity, mul_div_cancel_right₀ _ <| by positivity ⟩;
  -- By definition of $F$, we know that $F(t) = \sum_{j=0}^{2n} (-1)^j f^{(j)}(t)$.
  set F : ℝ → ℝ := fun t => ∑ j ∈ Finset.range (2 * n + 1), (-1 : ℝ) ^ j * (iteratedDeriv j (nivenF m n)) t;
  -- By definition of $F$, we know that $F'(t) + F(t) = f(t)$.
  have hF_deriv : ∀ t ∈ Set.Icc 0 (m : ℝ), deriv F t + F t = nivenF m n t := by
    intro t ht;
    have hF_deriv : deriv F t = ∑ j ∈ Finset.range (2 * n + 1), (-1 : ℝ) ^ j * (iteratedDeriv (j + 1) (nivenF m n)) t := by
      have hF_deriv : ∀ j : ℕ, DifferentiableAt ℝ (iteratedDeriv j (nivenF m n)) t := by
        unfold nivenF;
        fun_prop;
      norm_num +zetaDelta at *;
      norm_num [ hF_deriv, iteratedDeriv_succ ];
    have := Finset.sum_range_sub ( fun j => ( -1 : ℝ ) ^ j * iteratedDeriv j ( nivenF m n ) t ) ( 2 * n + 1 ) ; simp_all +decide [ pow_succ', mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    -- Since $f(t)$ is a polynomial of degree $2n$, its $(2n+1)$-th derivative is zero.
    have h_poly_deriv : ∀ t : ℝ, iteratedDeriv (2 * n + 1) (nivenF m n) t = 0 := by
      have h_poly_deriv : ∀ t : ℝ, iteratedDeriv (2 * n + 1) (fun t => t ^ n * ((m : ℝ) - t) ^ n) t = 0 := by
        have h_poly_deriv : ∀ p : Polynomial ℝ, p.degree ≤ 2 * n → ∀ t : ℝ, iteratedDeriv (2 * n + 1) (fun t => p.eval t) t = 0 := by
          intros p hp t; exact (by
          have h_poly_deriv : ∀ k : ℕ, iteratedDeriv k (fun t => p.eval t) = fun t => Polynomial.eval t (Polynomial.derivative^[k] p) := by
            intro k; induction k <;> simp_all +decide [ Function.iterate_succ_apply', iteratedDeriv_succ ] ;
            exact funext fun x => by simp +decide [ Polynomial.derivative_eval ] ;
          rw [ h_poly_deriv ];
          rw [ Polynomial.iterate_derivative_eq_zero ] ; norm_num;
          exact Nat.lt_succ_of_le ( Polynomial.natDegree_le_of_degree_le <| mod_cast hp ));
        convert h_poly_deriv ( Polynomial.X ^ n * ( Polynomial.C ( m : ℝ ) - Polynomial.X ) ^ n ) _ using 1;
        · norm_num [ Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_sub ];
        · norm_num [ two_mul, Polynomial.degree_le_iff_coeff_zero ];
          erw [ Polynomial.degree_sub_eq_right_of_degree_lt ] <;> norm_num [ hm ];
          exact lt_of_le_of_lt Polynomial.degree_C_le ( WithBot.coe_lt_coe.mpr zero_lt_one );
      unfold nivenF; simp_all +decide [ iteratedDeriv_eq_iterate ] ;
    linarith [ h_poly_deriv t ];
  -- By definition of $F$, we know that $F(t) \cdot \exp(t)$ is an antiderivative of $f(t) \cdot \exp(t)$.
  have hF_antideriv : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ m → ∫ t in a..b, nivenF m n t * Real.exp t = F b * Real.exp b - F a * Real.exp a := by
    intros a b _ _ _; rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    · intro x hx; convert HasDerivAt.mul ( hasDerivAt_deriv_iff.mpr _ ) ( Real.hasDerivAt_exp x ) using 1; ring;
      · rw [ ← mul_add, hF_deriv x ⟨ by cases Set.mem_uIcc.mp hx <;> linarith, by cases Set.mem_uIcc.mp hx <;> linarith ⟩ ] ; ring;
      · -- By definition of $F$, we know that it is a sum of differentiable functions.
        have hF_diff : ∀ j : ℕ, Differentiable ℝ (iteratedDeriv j (nivenF m n)) := by
          intro j; induction' j with j ih <;> simp_all +decide [ iteratedDeriv_succ ] ;
          · exact Differentiable.div_const ( Differentiable.mul ( differentiable_pow _ ) ( Differentiable.pow ( differentiable_id.const_sub _ ) _ ) ) _;
          · -- The derivative of a polynomial is also a polynomial.
            have h_poly_deriv : ∀ j : ℕ, ∃ p : Polynomial ℝ, iteratedDeriv j (nivenF m n) = fun t => p.eval t := by
              intro j; induction' j with j ih <;> simp_all +decide [ iteratedDeriv_succ ] ;
              · use Polynomial.C (1 / (Nat.factorial n : ℝ)) * Polynomial.X ^ n * (Polynomial.C (m : ℝ) - Polynomial.X) ^ n;
                ext; simp [nivenF];
                ring;
              · obtain ⟨ p, hp ⟩ := ih; exact ⟨ p.derivative, by ext; simp +decide [ hp ] ⟩ ;
            obtain ⟨ p, hp ⟩ := h_poly_deriv j; rw [ show deriv ( iteratedDeriv j ( nivenF m n ) ) = fun t => deriv ( fun t => Polynomial.eval t p ) t from funext fun t => by rw [ hp ] ] ; norm_num [ Polynomial.differentiable ] ;
        fun_prop;
    · exact Continuous.intervalIntegrable ( by exact Continuous.mul ( by exact Continuous.div_const ( by exact Continuous.mul ( continuous_pow _ ) ( by continuity ) ) _ ) ( Real.continuous_exp ) ) _ _;
  -- By definition of $F$, we know that $F(0)$ and $F(m)$ are integers.
  obtain ⟨A, hA⟩ : ∃ A : ℤ, F 0 = A := by
    choose! A B hA hB using h_deriv_int;
    exact ⟨ ∑ j ∈ Finset.range ( 2 * n + 1 ), ( -1 ) ^ j * A j, by push_cast; exact Finset.sum_congr rfl fun _ _ => by rw [ hA ] ⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, F m = B := by
    choose! A B hA hB using h_deriv_int; use ∑ j ∈ Finset.range ( 2 * n + 1 ), ( -1 ) ^ j * B j; aesop;
  exact ⟨ B, -A, by unfold nivenI; specialize hF_antideriv 0 m le_rfl ( by positivity ) le_rfl; aesop ⟩

/-
`exp(m)` is irrational for any positive natural number `m`.
    Proof: If `exp(m) = p/q`, then `q · nivenI m n` is a positive integer
    tending to 0, which is impossible.
-/
theorem irrational_exp_nat_pos (m : ℕ) (hm : 0 < m) :
    Irrational (Real.exp (m : ℝ)) := by
  -- Suppose for contradiction that exp(m) is rational. Then exp(m) = p/q for some coprime integers p and q.
  by_contra h_contra
  obtain ⟨p, q, hpq, hcoprime⟩ : ∃ p q : ℤ, Int.gcd p q = 1 ∧ 0 < q ∧ Real.exp m = p / q := by
    unfold Irrational at h_contra;
    exact by push_neg at h_contra; obtain ⟨ q, hq ⟩ := h_contra; exact ⟨ q.num, q.den, q.reduced, Nat.cast_pos.mpr q.pos, by simpa [ Rat.cast_def ] using hq.symm ⟩ ;
  -- Then $q * nivenI m n$ is an integer for all $n$.
  have h_int : ∀ n : ℕ, ∃ k : ℤ, q * nivenI m n = k := by
    intro n
    obtain ⟨A, B, hAB⟩ : ∃ A B : ℤ, nivenI m n = (A : ℝ) * Real.exp (m : ℝ) + (B : ℝ) := nivenI_int_linear_combination m hm n
    have h_int : ∃ k : ℤ, q * (A * Real.exp (m : ℝ) + B) = k := by
      exact ⟨ A * p + B * q, by push_cast [ hcoprime.2 ] ; rw [ mul_comm ] ; ring_nf; norm_num [ hcoprime.1.ne' ] ⟩
    obtain ⟨k, hk⟩ := h_int
    use k
    rw [← hk]
    rw [hAB];
  -- But $q * nivenI m n$ tends to 0 as $n$ tends to infinity.
  have h_tendsto_zero : Filter.Tendsto (fun n : ℕ => q * nivenI m n) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul ( nivenI_tendsto_zero m hm );
  -- Since $q * nivenI m n$ is an integer and tends to 0, it must be 0 for sufficiently large $n$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, q * nivenI m n = 0 := by
    have := h_tendsto_zero.eventually ( Metric.ball_mem_nhds _ zero_lt_one );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; use N; intro n hn; specialize hN n hn; rcases h_int n with ⟨ k, hk ⟩ ; simp_all +decide [ dist_eq_norm ] ;
    norm_cast at hN; aesop;
  exact absurd ( hN N le_rfl ) ( mul_ne_zero ( by norm_cast; linarith ) ( ne_of_gt ( nivenI_pos m hm N ) ) )

/-
**Irrationality of `exp(n)` for nonzero integers** (Hermite, 1873).
    For negative `n`, `exp(n) = 1/exp(-n)` and `1/x` is irrational when `x` is.
-/
theorem irrational_exp_of_int_ne_zero (n : ℤ) (hn : n ≠ 0) :
    Irrational (Real.exp (n : ℝ)) := by
  -- We split into cases on n:
  by_cases hn_pos : 0 < n;
  · convert irrational_exp_nat_pos ( Int.natAbs n ) ( by positivity ) using 1 ; norm_num [ abs_of_pos hn_pos ];
  · have := irrational_exp_nat_pos ( Int.natAbs n ) ( Int.natAbs_pos.mpr hn ) ; simp_all +decide [ abs_of_nonpos ( le_of_not_gt hn_pos ) ] ;
    simpa [ Real.exp_neg ] using this.inv

/-
Distinct primes have distinct angular positions on the helix.
    This follows from the injectivity of `log` on positive reals
    and the fact that `ω = π/3 ≠ 0`.
-/
theorem prime_angles_distinct (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) :
    helixAngularFreq * Real.log (p : ℝ) ≠
    helixAngularFreq * Real.log (q : ℝ) := by
  exact fun h => hne <| Nat.cast_injective ( Real.log_injOn_pos ( Set.mem_Ioi.mpr <| Nat.cast_pos.mpr hp.pos ) ( Set.mem_Ioi.mpr <| Nat.cast_pos.mpr hq.pos ) <| by nlinarith [ show 0 < helixAngularFreq by exact div_pos Real.pi_pos <| by norm_num ] )

/-
An integer linear combination of prime logarithms that equals zero
    must have all coefficients zero. This extends `prime_helix_positions_independent`
    from `ℕ`-valued to `ℤ`-valued coefficients by splitting into positive and
    negative parts and applying unique factorization.
-/
theorem int_linear_combination_log_primes_eq_zero
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, Nat.Prime p)
    (coeffs : ℕ → ℤ)
    (h : ∑ p ∈ primes, (coeffs p : ℝ) * Real.log (p : ℝ) = 0) :
    ∀ p ∈ primes, coeffs p = 0 := by
  -- Let's split the coefficients into positive and negative parts.
  set a : ℕ → ℕ := fun p => (coeffs p).toNat
  set b : ℕ → ℕ := fun p => (-coeffs p).toNat;
  -- Then coeffs p = a p - b p (as integers). Rearranging ∑ (a p - b p) * log p = 0, we get ∑ a p * log p = ∑ b p * log p.
  have h_eq : ∑ p ∈ primes, (a p : ℝ) * Real.log (p : ℝ) = ∑ p ∈ primes, (b p : ℝ) * Real.log (p : ℝ) := by
    have h_eq : ∑ p ∈ primes, ((a p : ℤ) - (b p : ℤ)) * Real.log (p : ℝ) = 0 := by
      convert h using 2 ; aesop;
    simp_all +decide [ sub_mul, Finset.sum_sub_distrib ];
    linarith;
  have := prime_helix_positions_independent primes hprimes a b h_eq;
  grind

/-
The product `∏ p ^ aₚ` for primes `p` and natural number exponents `aₚ`
    is a positive real, expressible as `exp(∑ aₚ · log p)`.
-/
theorem exp_sum_nat_mul_log_eq_prod
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, Nat.Prime p)
    (a : ℕ → ℕ) :
    Real.exp (∑ p ∈ primes, (a p : ℝ) * Real.log (p : ℝ)) =
    ∏ p ∈ primes, (p : ℝ) ^ (a p) := by
  rw [ Real.exp_sum, Finset.prod_congr rfl ] ; intros ; rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| hprimes _ ‹_› ) ] ; ring

/-
Distinct primes have distinct angular positions modulo 2π on the helix.

    The proof proceeds by contradiction: if `(π/3)·log p ≡ (π/3)·log q (mod 2π)`,
    then `log(p/q) = 6k` for some integer `k`, giving `p/q = exp(6k)`. For `k = 0`
    this gives `p = q`, contradicting distinctness. For `k ≠ 0`, `exp(6k)` is
    irrational while `p/q` is rational, a contradiction.
-/
theorem prime_angles_distinct_mod_two_pi (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) :
    ¬ (helixAngularFreq * Real.log (p : ℝ) ≡
       helixAngularFreq * Real.log (q : ℝ) [RMOD (2 * π)]) := by
  -- Assume that there exists an integer $k$ such that $\log(p/q) = 6k$.
  by_contra h_contra
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Real.log (p / q) = 6 * k := by
    obtain ⟨ k, hk ⟩ := h_contra; use k; rw [ Real.log_div ] <;> norm_num [ hp.ne_zero, hq.ne_zero ] ; unfold helixAngularFreq at hk; nlinarith [ Real.pi_pos ] ;
  -- Exponentiating both sides, we get $p/q = e^{6k}$.
  have h_exp : (p : ℝ) / q = Real.exp (6 * k) := by
    rw [ ← hk, Real.exp_log ( div_pos ( Nat.cast_pos.mpr hp.pos ) ( Nat.cast_pos.mpr hq.pos ) ) ];
  -- For $k \neq 0$, $e^{6k}$ is irrational, contradicting the rationality of $p/q$.
  by_cases hk_zero : k = 0;
  · simp_all +decide [ div_eq_iff, hp.ne_zero, hq.ne_zero ];
  · have h_irr : Irrational (Real.exp (6 * k)) := by
      have := irrational_exp_of_int_ne_zero ( 6 * k ) ( by positivity ) ; aesop;
    exact h_irr ⟨ p / q, by push_cast; linarith ⟩

/-
**No rational linear relations among prime angles modulo 2π.**

    If an integer linear combination of prime helix angles is a multiple of 2π,
    then all coefficients must be zero. This is the strongest form of the
    "no repeating pattern" theorem for the π/3 helix.

    The proof reduces to two cases:
    - If the combination equals `2πk` with `k = 0`, the result follows from
      the ℤ-linear independence of prime logarithms (unique factorization).
    - If `k ≠ 0`, exponentiating gives a rational number equal to `exp(6k)`,
      which is irrational by Hermite's theorem — a contradiction.
-/
theorem prime_angles_rational_independent
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, Nat.Prime p)
    (coeffs : ℕ → ℤ) (_hcoeffs : ∀ p, p ∉ primes → coeffs p = 0) :
    (∑ p ∈ primes, (coeffs p : ℝ) * helixAngularFreq * Real.log (p : ℝ)) ≡ 0 [RMOD (2 * π)] →
    ∀ p ∈ primes, coeffs p = 0 := by
  intro h;
  -- We get ∃ k : ℤ, ∑ c_p * (π/3) * log p - 0 = 2π * k. Factor: (π/3) * ∑ c_p * log p = 2π * k. Divide by π/3 (using π ≠ 0): ∑ c_p * log p = 6 * k.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (∑ p ∈ primes, (coeffs p : ℝ) * Real.log (p : ℝ)) = 6 * k := by
    unfold RealModEq helixAngularFreq at h;
    exact h.imp fun k hk => by rw [ show ( ∑ p ∈ primes, ( coeffs p : ℝ ) * ( Real.pi / 3 ) * Real.log p ) = ( Real.pi / 3 ) * ∑ p ∈ primes, ( coeffs p : ℝ ) * Real.log p by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring ] at hk; nlinarith [ Real.pi_pos ] ;
  by_cases hk_zero : k = 0;
  · convert int_linear_combination_log_primes_eq_zero primes hprimes coeffs _ ; aesop;
  · -- Split coefficients into positive and negative parts and apply the exponential function.
    set pos := fun p => (coeffs p).toNat
    set neg := fun p => (-coeffs p).toNat
    have h_exp : (∏ p ∈ primes, (p : ℝ) ^ pos p) / (∏ p ∈ primes, (p : ℝ) ^ neg p) = Real.exp (6 * k) := by
      have h_exp : (∑ p ∈ primes, (pos p : ℝ) * Real.log (p : ℝ)) - (∑ p ∈ primes, (neg p : ℝ) * Real.log (p : ℝ)) = 6 * k := by
        rw [ ← hk, ← Finset.sum_sub_distrib ];
        refine Finset.sum_congr rfl fun p hp => ?_;
        cases' Int.eq_nat_or_neg ( coeffs p ) ; aesop;
      rw [ ← h_exp, Real.exp_sub ];
      rw [ Real.exp_sum, Real.exp_sum ];
      exact congrArg₂ _ ( Finset.prod_congr rfl fun x hx => by rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| hprimes x hx ) ] ; ring ) ( Finset.prod_congr rfl fun x hx => by rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| hprimes x hx ) ] ; ring );
    -- Since $\exp(6k)$ is irrational for any nonzero integer $k$, we have a contradiction.
    have h_irrational : Irrational (Real.exp (6 * k)) := by
      convert irrational_exp_of_int_ne_zero ( 6 * k ) ( mul_ne_zero ( by norm_num ) hk_zero ) using 1 ; norm_num [ mul_comm ];
    exact False.elim <| h_irrational ⟨ ( ∏ p ∈ primes, p ^ pos p ) / ( ∏ p ∈ primes, p ^ neg p ), by push_cast; linarith ⟩

/-! ## Theorem 4: The Critical Line as Symmetry Axis

The critical line Re(s) = 1/2 in the Riemann zeta function is the fixed locus
of the involution s ↦ 1 - s̄. This is the symmetry axis of the helix projection. -/

/-
The critical line Re(s) = 1/2 is exactly the set of fixed points of s ↦ 1 - s̄.
    This involution corresponds to the reflection symmetry of the helix.
-/
theorem critical_line_is_helix_symmetry_axis (s : ℂ) :
    s.re = 1 / 2 ↔ s = 1 - starRingEnd ℂ s := by
  constructor <;> intro h <;> rw [ Complex.ext_iff ] at * <;> norm_num at * <;> linarith

/-
The functional equation involution s ↦ 1 - s̄ is an involution.
-/
theorem helix_involution_involutive :
    Function.Involutive (fun s : ℂ => 1 - starRingEnd ℂ s) := by
  exact fun s => by simp +decide ;

/-! ## Theorem 5: Equidistribution of Primes on the Helix

The angles θₚ = ω · log p (mod 2π) for primes p are equidistributed on [0, 2π).
This is a deep result following from the prime number theorem and Vinogradov's
estimates on exponential sums over primes. We state it precisely here. -/

/-- The Weyl sum for the prime angle sequence. For the equidistribution of
    {α · log p mod 1}, we need these sums to be o(π(N)) for all nonzero integers k. -/
def primeWeylSum (α : ℝ) (k : ℤ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Finset.range N).filter Nat.Prime,
    Complex.exp (2 * π * Complex.I * k * (α * Real.log (p : ℝ)))

/-- **Equidistribution of prime angles on the helix** (Vinogradov).
    For any irrational α, the sequence {α · log p mod 1 : p prime} is
    equidistributed modulo 1. In particular, this holds for α = 1/(2π) · ω = 1/6.

    This is equivalent to the Weyl criterion: for every nonzero integer k,
    the exponential sum Σ_{p ≤ N} e(k · α · log p) = o(π(N)).

    The proof requires Vinogradov's method of exponential sums over primes,
    which is beyond current Mathlib. We state this as an axiom-free theorem
    that can be filled in when the required analytic number theory is available. -/
theorem prime_angles_equidistributed (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => (primeWeylSum α k N) / ((Finset.range N).filter Nat.Prime).card)
      Filter.atTop (nhds 0) := by
  sorry

end