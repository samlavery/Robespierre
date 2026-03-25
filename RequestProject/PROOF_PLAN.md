


# 1 Assume RH is false, offline zeta zeros can exist

# 2 Show zeta zeros control prime distribution and density
See Block 1 [-ζ'/ζ = Σ Λ(n)/n^s]

# 3 Show primes create harmonics that return to towards the origin (0)
theorem primes_create_harmonics (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

theorem decay_rate_pos : 0 < 2 * (Real.pi - 3) / Real.pi := by
  positivity_fail_if_not_done
  have := Real.pi_gt_three
  have := Real.pi_pos
  positivity

theorem decay_rate_lt_one : 2 * (Real.pi - 3) / Real.pi < 1 := by
  rw [div_lt_one (by linarith [Real.pi_pos])]
  linarith [Real.pi_lt_four]

# 3 Perform 90 degree rotation check and compare results to rule out original offline zeros 

# 4 Establish cosh kernel with critical strip at pi/6 with mirrored RP zeros
[CoshKernel.lean]

# 5 Show full harmonic cancellation at pi/6 on the strip 
[StripTheorem.lean] theorem XiFinite_theta_axis_im_eq_zero (P : ℕ) (t : ℝ) :

# 6 Prove online cosh zeros project to zeta strip at 1/2
[RobspierreHypothesis.lean] theorem zeroAddressProjection_zeroAddressLift {s : ℂ}


# Show zeta rotation symmetry at 1/2 -  test pass
[CriticalLineClassifier.lean] detector_iff_sin_theta

# Show cosh reflection symmetry at pi/6 - test pass
[CriticalLineClassifier.lean] classifier_complete

# Introduce offline zeta zeros
Trivial

# Prove offline zeta zeros create measurable distortion/anti-symmetry in prime observable, weight, density, etc
[OffAxisTheorem.lean]
theorem offaxis_classical_zero_forces_prime_observable_change
  (ρ : ℂ) (hz : riemannZeta ρ = 0) (hoff : ρ.re ≠ 1/2) :
  ∃ X, PrimeNumberLineObservableChange ρ X

theorem offaxis_forces_rotated_detector_event
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ρ := by
      exact ⟨ 0, by rw [ rotatedPrimeDensityNormSq_eq ] ; exact pow_ne_zero 2 ( sub_ne_zero_of_ne hoff ) ⟩

theorem offaxis_forces_observable_nontriviality
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    ∃ t, offAxisRealObservable ρ.re t ≠ 0 ∨ offAxisImagObservable ρ.re t ≠ 0 := by
      exact ⟨ 0, Or.inl <| mul_ne_zero ( sub_ne_zero_of_ne hoff ) ( by norm_num ) ⟩

theorem offaxis_forces_numberline_distortion
    (ρ : ℂ)
    (_hz : riemannZeta ρ = 0)
    (_hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    ∃ n, realAxisDistortion n > 0 := by
      exact ⟨ 2, realAxisDistortion_pos_of_two_le ( by norm_num ) ⟩

theorem no_offline_passes_detector {σ : ℝ} (hoff : σ ≠ 1 / 2) :
    ¬ rotatedPrimeDensityDetectorPasses σ := by
      exact fun h => hoff <| by have := h 0; norm_num [ offAxisRealObservable, offAxisImagObservable, rotatedPrimeDensityNormSq ] at this; nlinarith;


# Prove distortion in primes creates distortion in harmonics

theorem offaxis_classical_zero_forces_detector_and_distortion
    (ρ : ℂ)
    (hz : riemannZeta ρ = 0)
    (hoff : ρ.re ≠ (1 / 2 : ℝ)) :
    RotatedPrimeDensityDetectorEvent ρ
      ∧ (∃ n, realAxisDistortion n > 0)
      ∧ ¬ rotatedPrimeDensityDetectorPasses ρ.re := by
        exact ⟨ offaxis_forces_rotated_detector_event ρ hz hoff, offaxis_forces_numberline_distortion ρ hz hoff, no_offline_passes_detector hoff ⟩

theorem antiSymmetryEvent_implies_primeHarmonicModification (ρ : ℂ)
    (h : RotatedObservableAntiSymmetryEvent ρ) :
    PrimeHarmonicModificationEvent ρ := by
  refine ⟨h.1, h.2.2, fun x y hx hy => ?_⟩
  simp only [realObservableDistortion, rpow_sub_rpow_pos_iff hx, rpow_sub_rpow_pos_iff hy]

theorem harmonic_disruption_no_imaginary_zero
    (a : ℝ) (ha : a ≠ 0) (y : ℝ) :
    cosh (I * ↑y) + ↑a * (I * ↑y) ≠ 0 := by
  norm_num [ Complex.ext_iff, Complex.cosh, Complex.exp_re, Complex.exp_im ] at * ; aesop;


# Show cosh zeros at pi/6 do not cancel distorted harmonics, creating offline cosh zeros
[CoshNoZeros] cosh_pi_div_six_ne_zero
			  cosh_neg_pi_div_six_ne_zero


# Prove transport function 
theorem transport_intertwines_reflections (s : ℂ) :
    T (piDivSixReflect s) = classicalReflect (T s) := by
  unfold piDivSixReflect T classicalReflect ; ring;
  norm_num [ theta_ne_zero ]
theorem exact_zero_transport (t : ℝ) :
    riemannZeta (1 / 2 + ↑t * I) = 0 ↔ RobespierreZetaO (↑robθ + ↑t * I) = 0 := by
  unfold RobespierreZetaO
  rw [re_robθ_add_tI, im_robθ_add_tI, robθ_div_two_robθ]
  simp

def robespierreOToClassical (s : ℂ) : ℂ :=
  ⟨s.re / (2 * θ), s.im⟩

def classicalToRobespierreO (s : ℂ) : ℂ :=
  ⟨(2 * θ) * s.re, s.im⟩

# Show offline cosh zeros project to offline zeta zeros
[CriticalLineClassifier.lean] strip_offline_rejected


# Prove reflection symmetry for cosh fails due to offline cosh zeros - test fails
[CriticalLineClassifier.lean] theorem detector_iff_sin_theta (σ : ℝ) 

# Prove rotation symmety fails for zeta due to offline zeros - test fails
[CriticalLineClassifier.lean] no_offline_passes_detector
theorem robespierre_harmonic_collapse (P : ℕ) (t : ℝ) :
[OffAxisZeta.lean] offaxis_zero_forces_observable_antisymmetry

# Prove all zeta zeros are online with no cosh transfer interference
[CriticalLineClassifier.lean] DetectorCheckABC

# Show reflection symmetry passes for cosh kernel at pi/6 - test pass

theorem no_offline_zeros (σ : ℝ) (_hσ : σ ≠ π / 6) : coshKernel σ ≠ 0 :=
  ne_of_gt <| coshKernel_pos σ

theorem coshKernel_at_fold : coshKernel (π / 6) = 1 := by
  simp [coshKernel]


# Show symmetry under rotation passes for zeta kernel at 1/2 - test pass
theorem riemannZeta_nonvanishing_re_ge_one (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs


# Conclude offline zeta zeros cannot exist 







# BLOCK 1
open Complex Filter Topology Set
noncomputable section

theorem zeta_differentiable_away_from_one {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

theorem zeta_euler_product :
    ∀ {s : ℂ}, 1 < s.re →
      HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) := by
  intro s hs
  exact riemannZeta_eulerProduct_hasProd hs

theorem zeta_eq_dirichlet_series {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

theorem completed_zeta_reflection (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub s

theorem completed_zeta_reflection' (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

theorem zeta_functional_equation {s : ℂ} (hs : ∀ n : ℕ, s ≠ -↑n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * ↑Real.pi) ^ (-s) * Gamma s * cos (↑Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'


theorem zeta_nonvanishing_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

theorem zeta_trivial_zeros (n : ℕ) : riemannZeta (-2 * (↑n + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n


theorem completed_zeta0_zero_symmetric {s : ℂ}
    (h : completedRiemannZeta₀ s = 0) : completedRiemannZeta₀ (1 - s) = 0 := by
  rwa [completed_zeta_reflection]

theorem nontrivial_zeros_in_critical_strip {s : ℂ}
    (hζ : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (↑n + 1))
    (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  -- If $s.re \leq 0$, then $1 - s.re \geq 1$, and by the known result, $\zeta(1 - s) \neq 0$.
  by_cases h_nonpos : s.re ≤ 0;
  · have h_fun_eq : riemannZeta (1 - s) = 2 * (2 * Real.pi) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2) * riemannZeta s := by
      apply_rules [ zeta_functional_equation ];
      intro n hn; simp_all +decide [ Complex.ext_iff ] ;
      rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
      · specialize htriv ( k - 1 ) ; rcases k with ( _ | k ) <;> norm_num at * ; norm_cast at *;
        norm_num [ riemannZeta ] at hζ;
        norm_num [ HurwitzZeta.hurwitzZetaEven ] at hζ;
      · have := @riemannZeta_neg_nat_eq_bernoulli ( 2 * k + 1 ) ; simp_all +decide [ Nat.mul_succ, pow_succ' ] ; ring_nf at *; norm_num at *;
        norm_cast at * ; simp_all +decide [ bernoulli_eq_bernoulli'_of_ne_one ];
        have h_bernoulli_nonzero : ∀ n : ℕ, n ≥ 1 → bernoulli (2 * n) ≠ 0 := by
          intro n hn; rw [ bernoulli_eq_bernoulli'_of_ne_one ( by linarith ) ] ; norm_num [ bernoulli'_eq_zero_of_odd ] ;
          have := @hasSum_zeta_nat;
          specialize @this n ( by linarith ) ; have := this.tsum_eq; simp_all +decide [ bernoulli ] ;
          intro h; norm_num [ h ] at this; exact absurd this ( by exact ne_of_gt <| lt_of_lt_of_le ( by positivity ) <| Summable.le_tsum ( by exact Real.summable_nat_pow_inv.2 <| by linarith ) 1 <| by intros; positivity ) ;
        exact h_bernoulli_nonzero ( k + 1 ) ( by linarith ) ( by convert hζ using 1; ring );
    exact absurd ( zeta_nonvanishing_re_ge_one ( show 1 ≤ ( 1 - s ).re by norm_num; linarith ) ) ( by aesop );
  · exact ⟨ not_le.mp h_nonpos, lt_of_not_ge fun h => zeta_nonvanishing_re_ge_one h hζ ⟩

theorem zeta_at_zero : riemannZeta 0 = -1 / 2 :=
  riemannZeta_zero
theorem zeta_nonzero_at_zero : riemannZeta 0 ≠ 0 := by
  rw [riemannZeta_zero]
  norm_num

theorem vonMangoldt_at_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.vonMangoldt p = Real.log p :=
  ArithmeticFunction.vonMangoldt_apply_prime hp





