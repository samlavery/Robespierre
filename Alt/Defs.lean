/-
# Circle-Native Kernel: Definitions

Basic definitions for the θ-native kernel and related strip domains.
-/
import Mathlib

open Complex Real Finset Filter Topology Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace CircleNative

/-! ## The parameter θ = π/6 -/

/-- The parameter θ = arcsin(1/2) = π/6. -/
def θ : ℝ := Real.arcsin (1/2)

/-- θ equals π/6. -/
theorem θ_eq : θ = Real.pi / 6 := by
  unfold θ
  rw [← Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-! ## Kernel building blocks -/

/-- The base φ(p) = 2θp for the kernel's exponential terms. -/
def φ (p : ℕ) : ℝ := 2 * θ * p

/-- The coefficient a(p) = π/6 · (2(π - 3)/π)^p. -/
def a (p : ℕ) : ℝ := Real.pi / 6 * ((2 * (Real.pi - 3) / Real.pi) ^ p)

/-- The frequency u(p) = log(φ(p)) = log(2θp). -/
def u (p : ℕ) : ℝ := Real.log (φ p)

/-- The complex power base: cpowBase(p, w) = exp(w · log(φ(p))). -/
def cpowBase (p : ℕ) (w : ℂ) : ℂ := Complex.exp (w * ↑(Real.log (φ p)))

/-! ## Prime filtering -/

/-- The set of primes at most n. -/
def primesBelow (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime

/-- Membership in `primesBelow n` means exactly: primality plus the cutoff
    condition `p ≤ n`. -/
theorem mem_primesBelow_iff {n p : ℕ} :
    p ∈ primesBelow n ↔ p ≤ n ∧ Nat.Prime p := by
  simp [primesBelow]

/-- The generated prime prefixes are monotone in the cutoff parameter. -/
theorem primesBelow_mono {m n : ℕ} (h : m ≤ n) :
    primesBelow m ⊆ primesBelow n := by
  intro p hp
  rw [mem_primesBelow_iff] at hp ⊢
  exact ⟨le_trans hp.1 h, hp.2⟩

/-- The Robespierre scaling factor `2θ` is positive. -/
theorem two_theta_pos : 0 < 2 * θ := by
  rw [θ_eq]
  linarith [Real.pi_pos]

/-- The scaled prime observable `φ(p) = 2θp` is positive for positive inputs. -/
theorem phi_pos {p : ℕ} (hp : 0 < p) : 0 < φ p := by
  unfold φ
  exact mul_pos two_theta_pos (show (0 : ℝ) < p by exact_mod_cast hp)

/-- The Robespierre scaling factor `2θ` is strictly larger than `1`. -/
theorem one_lt_two_theta : 1 < 2 * θ := by
  rw [θ_eq]
  linarith [Real.pi_gt_three]

/-- The `theta`-product observable `φ(p) = 2θp` is strictly monotone. -/
theorem phi_strictMono : StrictMono φ := by
  intro p q hpq
  unfold φ
  have hscale : 0 < 2 * θ := two_theta_pos
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hpq) hscale

/-- The Robespierre products preserve strict order. -/
theorem phi_lt_phi {p q : ℕ} (hpq : p < q) : φ p < φ q :=
  phi_strictMono hpq

/-- For every input `p ≥ 2`, the scaled prime observable satisfies `1 < φ(p)`. -/
theorem one_lt_phi_of_two_le {p : ℕ} (hp : 2 ≤ p) : 1 < φ p := by
  unfold φ
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith [one_lt_two_theta, hp']

/-- The log-frequencies `u(p) = log(φ(p))` are strictly increasing on positive inputs. -/
theorem u_strictMono {p q : ℕ} (hp : 0 < p) (hpq : p < q) : u p < u q := by
  unfold u
  exact Real.log_lt_log (phi_pos hp) (phi_lt_phi hpq)

/-- In particular, the Robespierre prime frequencies are strictly increasing along primes. -/
theorem u_strictMono_on_primes {p q : ℕ} (hp : Nat.Prime p) (_hq : Nat.Prime q)
    (hpq : p < q) : u p < u q :=
  u_strictMono hp.pos hpq

/-- The kernel coefficient `a(p)` is always nonnegative. -/
theorem a_nonneg (p : ℕ) : 0 ≤ a p := by
  unfold a
  have hbase_nonneg : 0 ≤ 2 * (Real.pi - 3) / Real.pi := by
    have hnum : 0 ≤ 2 * (Real.pi - 3) := by
      linarith [Real.pi_gt_three]
    exact div_nonneg hnum Real.pi_pos.le
  exact mul_nonneg (by positivity) (pow_nonneg hbase_nonneg _)

/-- The kernel coefficient is strictly positive for every input `p ≥ 2`. -/
theorem a_pos_of_two_le {p : ℕ} (_hp : 2 ≤ p) : 0 < a p := by
  unfold a
  have hbase : 0 < 2 * (Real.pi - 3) / Real.pi := by
    have hnum : 0 < 2 * (Real.pi - 3) := by
      linarith [Real.pi_gt_three]
    exact div_pos hnum Real.pi_pos
  exact mul_pos (by positivity) (pow_pos hbase _)

/-- The coefficient decay base lies strictly below `1`. -/
theorem a_base_lt_one : 2 * (Real.pi - 3) / Real.pi < 1 := by
  have hnum : 2 * (Real.pi - 3) < Real.pi := by
    linarith [Real.pi_lt_four]
  exact (div_lt_one Real.pi_pos).2 hnum

/-- The coefficient sequence is summable by geometric decay. -/
theorem a_summable : Summable a := by
  unfold a
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (summable_geometric_of_lt_one
      (show 0 ≤ 2 * (Real.pi - 3) / Real.pi by
        have hnum : 0 ≤ 2 * (Real.pi - 3) := by
          linarith [Real.pi_gt_three]
        exact div_nonneg hnum Real.pi_pos.le)
      a_base_lt_one).mul_left (Real.pi / 6)

/-! ## Finite and infinite kernels -/

/-- The finite kernel Ξ_{θ,n}: partial sum over primes p ≤ n. -/
def ΞFinite (n : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ primesBelow n,
    (↑(a p) : ℂ) * (cpowBase p (s - ↑θ) + cpowBase p (-(s - ↑θ)))

/-- The infinite kernel Ξ_θ: full series over all primes. -/
def ΞInfinite (s : ℂ) : ℂ :=
  ∑' p, if Nat.Prime p then
    (↑(a p) : ℂ) * (cpowBase p (s - ↑θ) + cpowBase p (-(s - ↑θ)))
  else 0

/-! ## Strip domains -/

/-- The right off-axis strip D⁺_{ε,δ} = { s : ε < Re(s) - θ < δ }. -/
def StripPlus (ε δ : ℝ) : Set ℂ :=
  { s : ℂ | ε < s.re - θ ∧ s.re - θ < δ }

/-- The left off-axis strip D⁻_{ε,δ} = { s : -δ < Re(s) - θ < -ε }. -/
def StripMinus (ε δ : ℝ) : Set ℂ :=
  { s : ℂ | -δ < s.re - θ ∧ s.re - θ < -ε }

/-! ## Strip topology -/

theorem isOpen_stripPlus (ε δ : ℝ) : IsOpen (StripPlus ε δ) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (Complex.continuous_re.sub continuous_const)
  · exact isOpen_lt (Complex.continuous_re.sub continuous_const) continuous_const

theorem isOpen_stripMinus (ε δ : ℝ) : IsOpen (StripMinus ε δ) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (Complex.continuous_re.sub continuous_const)
  · exact isOpen_lt (Complex.continuous_re.sub continuous_const) continuous_const

/-
PROVIDED SOLUTION
The strip StripPlus ε δ = { s : ℂ | ε < s.re - θ ∧ s.re - θ < δ } is a convex subset of ℂ (for ε < δ). Use Convex.isPathConnected (with nonemptiness from θ + (ε+δ)/2) and IsPathConnected.isConnected. For convexity: if s₁, s₂ are in the strip and t ∈ [0,1], then Re(t*s₁ + (1-t)*s₂) - θ = t*(Re(s₁)-θ) + (1-t)*(Re(s₂)-θ) which is a convex combination of values in (ε,δ), hence in (ε,δ). But note the strict inequalities: convex combination of strict inequalities a < x < b with a ≤ t ≤ 1 and 0 ≤ (1-t) gives a < t*x₁ + (1-t)*x₂ < b. Actually for non-strict convexity we need to be careful. Since the set is defined by strict inequalities, convex combinations stay strictly inside (since the set {x : ε < x < δ} is convex). Use Convex.isPathConnected.
-/
theorem isConnected_stripPlus {ε δ : ℝ} (hεδ : ε < δ) : IsConnected (StripPlus ε δ) := by
  -- The strip StripPlus ε δ is a convex subset of ℂ.
  have h_convex : Convex ℝ (StripPlus ε δ) := by
    refine' convex_iff_forall_pos.mpr _;
    intro x hx y hy a b ha hb hab; unfold StripPlus at *; simp_all +decide;
    constructor <;> rw [ ← eq_sub_iff_add_eq' ] at hab <;> subst_vars <;> nlinarith [ mul_pos ha hb ] ;
  exact ⟨ ⟨ ⟨ ε + ( δ - ε ) / 2 + θ, 0 ⟩, ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ⟩, h_convex.isPreconnected ⟩

/-
PROVIDED SOLUTION
Same as isConnected_stripPlus but for the left strip. The set StripMinus ε δ = { s : ℂ | -δ < s.re - θ ∧ s.re - θ < -ε } is convex and nonempty (contains θ - (ε+δ)/2). Use Convex.isPathConnected and IsPathConnected.isConnected.
-/
theorem isConnected_stripMinus {ε δ : ℝ} (hεδ : ε < δ) : IsConnected (StripMinus ε δ) := by
  convert isConnected_stripPlus ( show -δ < -ε by linarith ) using 1

/-! ## Critical line functions -/

/-- The critical line sum C_P(t) = ∑_{p ≤ P} a_p · cos(t · u_p). -/
def CriticalLineSum (P : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ primesBelow P, a p * Real.cos (t * u p)

/-- The infinite critical-line harmonic sum
    `C_∞(t) = ∑_p a_p · cos(t · u_p)`. -/
def CriticalLineSumInf (t : ℝ) : ℝ :=
  ∑' p, if Nat.Prime p then a p * Real.cos (t * u p) else 0

/-- The prime-filtered coefficient series is summable. -/
theorem prime_weight_summable : Summable (fun p : ℕ => if Nat.Prime p then a p else 0) := by
  refine Summable.of_nonneg_of_le (fun p => by split_ifs <;> simp [a_nonneg]) (fun p => ?_) a_summable
  split_ifs with hp <;> simp [a_nonneg]

/-- The infinite critical-line harmonic sum is absolutely convergent. -/
theorem criticalLineSumInf_summable (t : ℝ) :
    Summable (fun p : ℕ => if Nat.Prime p then a p * Real.cos (t * u p) else 0) := by
  apply Summable.of_norm_bounded
  · exact prime_weight_summable
  · intro p
    by_cases hp : Nat.Prime p
    · rw [if_pos hp, if_pos hp]
      have hcos : |Real.cos (t * u p)| ≤ 1 := abs_cos_le_one (t * u p)
      rw [Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (a_nonneg p)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcos (a_nonneg p)
    · simp [hp]

/-- The real off-axis observable coming from the finite kernel decomposition. -/
def OffAxisRealObservable (P : ℕ) (x t : ℝ) : ℝ :=
  ∑ p ∈ primesBelow P, a p * Real.cosh (x * u p) * Real.cos (t * u p)

/-- The imaginary off-axis observable coming from the finite kernel decomposition. -/
def OffAxisImagObservable (P : ℕ) (x t : ℝ) : ℝ :=
  ∑ p ∈ primesBelow P, a p * Real.sinh (x * u p) * Real.sin (t * u p)

/-- The derivative of C_P: C_P'(t) = -∑_{p ≤ P} a_p · u_p · sin(t · u_p). -/
def CriticalLineSumDeriv (P : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ primesBelow P, a p * (-Real.sin (t * u p) * u p)

/-- The real-slice off-axis distortion, measured against the symmetry-axis
    observable. This is the finite prime-density distortion created by moving
    off the line `Re(s) = θ`. -/
def RealAxisDistortion (P : ℕ) (x : ℝ) : ℝ :=
  OffAxisRealObservable P x 0 - CriticalLineSum P 0

/-- The general even-channel off-axis distortion, measured against the
    symmetry-axis observable at the same imaginary height. -/
def RealObservableDistortion (P : ℕ) (x t : ℝ) : ℝ :=
  OffAxisRealObservable P x t - CriticalLineSum P t

/-- The unrotated prime-density detector: both observable channels vanish. -/
def PrimeDensityDetector (P : ℕ) (x t : ℝ) : Prop :=
  OffAxisRealObservable P x t = 0 ∧ OffAxisImagObservable P x t = 0

/-- The even prime-density channel after rotating the observable pair by `α`. -/
def RotatedOffAxisRealObservable (P : ℕ) (x t α : ℝ) : ℝ :=
  Real.cos α * OffAxisRealObservable P x t -
    Real.sin α * OffAxisImagObservable P x t

/-- The odd prime-density channel after rotating the observable pair by `α`. -/
def RotatedOffAxisImagObservable (P : ℕ) (x t α : ℝ) : ℝ :=
  Real.sin α * OffAxisRealObservable P x t +
    Real.cos α * OffAxisImagObservable P x t

/-- The rotation-aware prime-density detector checks every rotated frame. -/
def RotatedPrimeDensityDetector (P : ℕ) (x t : ℝ) : Prop :=
  ∀ α : ℝ,
    RotatedOffAxisRealObservable P x t α = 0 ∧
      RotatedOffAxisImagObservable P x t α = 0

/-- Squared norm of the rotated prime-density observable vector. -/
def RotatedPrimeDensityNormSq (P : ℕ) (x t α : ℝ) : ℝ :=
  (RotatedOffAxisRealObservable P x t α) ^ 2 +
    (RotatedOffAxisImagObservable P x t α) ^ 2

/-- On the symmetry axis `x = 0`, the real off-axis observable is exactly the
    critical-line sum. -/
theorem offAxisRealObservable_axis (P : ℕ) (t : ℝ) :
    OffAxisRealObservable P 0 t = CriticalLineSum P t := by
  unfold OffAxisRealObservable CriticalLineSum
  simp

/-- On the symmetry axis `x = 0`, the imaginary off-axis observable vanishes. -/
theorem offAxisImagObservable_axis (P : ℕ) (t : ℝ) :
    OffAxisImagObservable P 0 t = 0 := by
  unfold OffAxisImagObservable
  simp

/-- At imaginary part `t = 0`, the imaginary off-axis observable vanishes. -/
theorem offAxisImagObservable_at_zero (P : ℕ) (x : ℝ) :
    OffAxisImagObservable P x 0 = 0 := by
  unfold OffAxisImagObservable
  simp

/-- Zero rotation recovers the unrotated even prime-density channel. -/
theorem rotatedOffAxisRealObservable_zero_angle (P : ℕ) (x t : ℝ) :
    RotatedOffAxisRealObservable P x t 0 = OffAxisRealObservable P x t := by
  unfold RotatedOffAxisRealObservable
  simp

/-- Zero rotation recovers the unrotated odd prime-density channel. -/
theorem rotatedOffAxisImagObservable_zero_angle (P : ℕ) (x t : ℝ) :
    RotatedOffAxisImagObservable P x t 0 = OffAxisImagObservable P x t := by
  unfold RotatedOffAxisImagObservable
  simp

/-- At `t = 0`, the real off-axis observable reduces to the positive
    cosh-weighted prime sum. -/
theorem offAxisRealObservable_at_zero (P : ℕ) (x : ℝ) :
    OffAxisRealObservable P x 0 =
      ∑ p ∈ primesBelow P, a p * Real.cosh (x * u p) := by
  unfold OffAxisRealObservable
  simp

/-- Once the prime prefix contains `2`, the real off-axis observable at `t = 0`
    is strictly positive. -/
theorem offAxisRealObservable_at_zero_pos {P : ℕ} (hP : 2 ≤ P) (x : ℝ) :
    0 < OffAxisRealObservable P x 0 := by
  rw [offAxisRealObservable_at_zero]
  have hnonneg : ∀ p ∈ primesBelow P, 0 ≤ a p * Real.cosh (x * u p) := by
    intro p hp
    exact mul_nonneg (a_nonneg p) (Real.cosh_pos _).le
  have hmem2 : 2 ∈ primesBelow P := by
    rw [mem_primesBelow_iff]
    exact ⟨hP, by decide⟩
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnonneg hmem2)
  simpa using mul_pos (a_pos_of_two_le (by norm_num)) (Real.cosh_pos _)

/-- The real off-axis observable is even in the off-axis displacement `x`. -/
theorem offAxisRealObservable_neg_x (P : ℕ) (x t : ℝ) :
    OffAxisRealObservable P (-x) t = OffAxisRealObservable P x t := by
  unfold OffAxisRealObservable
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [neg_mul, Real.cosh_neg]

/-- The imaginary off-axis observable is odd in the off-axis displacement `x`. -/
theorem offAxisImagObservable_neg_x (P : ℕ) (x t : ℝ) :
    OffAxisImagObservable P (-x) t = - OffAxisImagObservable P x t := by
  unfold OffAxisImagObservable
  calc
    ∑ p ∈ primesBelow P, a p * Real.sinh (-x * u p) * Real.sin (t * u p)
      = ∑ p ∈ primesBelow P, -(a p * Real.sinh (x * u p) * Real.sin (t * u p)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [neg_mul, Real.sinh_neg]
          ring
    _ = - ∑ p ∈ primesBelow P, a p * Real.sinh (x * u p) * Real.sin (t * u p) := by
          rw [Finset.sum_neg_distrib]

/-- The real off-axis observable is even in the imaginary parameter `t`. -/
theorem offAxisRealObservable_neg_t (P : ℕ) (x t : ℝ) :
    OffAxisRealObservable P x (-t) = OffAxisRealObservable P x t := by
  unfold OffAxisRealObservable
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [neg_mul, Real.cos_neg]

/-- The imaginary off-axis observable is odd in the imaginary parameter `t`. -/
theorem offAxisImagObservable_neg_t (P : ℕ) (x t : ℝ) :
    OffAxisImagObservable P x (-t) = - OffAxisImagObservable P x t := by
  unfold OffAxisImagObservable
  calc
    ∑ p ∈ primesBelow P, a p * Real.sinh (x * u p) * Real.sin (-t * u p)
      = ∑ p ∈ primesBelow P, -(a p * Real.sinh (x * u p) * Real.sin (t * u p)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [neg_mul, Real.sin_neg]
          ring
    _ = - ∑ p ∈ primesBelow P, a p * Real.sinh (x * u p) * Real.sin (t * u p) := by
          rw [Finset.sum_neg_distrib]

/-- Rotation preserves the squared size of the prime-density observable pair. -/
theorem rotatedPrimeDensityNormSq_eq (P : ℕ) (x t α : ℝ) :
    RotatedPrimeDensityNormSq P x t α =
      (OffAxisRealObservable P x t) ^ 2 + (OffAxisImagObservable P x t) ^ 2 := by
  unfold RotatedPrimeDensityNormSq RotatedOffAxisRealObservable RotatedOffAxisImagObservable
  set c : ℝ := Real.cos α
  set s : ℝ := Real.sin α
  set reObs : ℝ := OffAxisRealObservable P x t
  set imObs : ℝ := OffAxisImagObservable P x t
  have htrig : c ^ 2 + s ^ 2 = 1 := by
    subst c s
    nlinarith [Real.sin_sq_add_cos_sq α]
  calc
    (c * reObs - s * imObs) ^ 2 + (s * reObs + c * imObs) ^ 2
        = (c ^ 2 + s ^ 2) * (reObs ^ 2 + imObs ^ 2) := by ring
    _ = reObs ^ 2 + imObs ^ 2 := by rw [htrig]; ring

/-- The rotation-aware detector is equivalent to the original detector. -/
theorem rotatedPrimeDensityDetector_iff (P : ℕ) (x t : ℝ) :
    RotatedPrimeDensityDetector P x t ↔ PrimeDensityDetector P x t := by
  constructor
  · intro hrot
    simpa [PrimeDensityDetector, RotatedOffAxisRealObservable, RotatedOffAxisImagObservable]
      using hrot 0
  · rintro ⟨hre, him⟩ α
    constructor <;>
      simp [RotatedOffAxisRealObservable, RotatedOffAxisImagObservable, hre, him]

/-- At `t = 0`, the critical-line sum is the unmodified weighted prime prefix. -/
theorem criticalLineSum_at_zero (P : ℕ) :
    CriticalLineSum P 0 = ∑ p ∈ primesBelow P, a p := by
  unfold CriticalLineSum
  simp

/-- Successor decomposition of the prime prefixes: moving from `n` to `n + 1`
    either inserts the new prime or leaves the prefix unchanged. -/
theorem primesBelow_succ (n : ℕ) :
    primesBelow (n + 1) =
      if Nat.Prime (n + 1) then insert (n + 1) (primesBelow n) else primesBelow n := by
  unfold primesBelow
  rw [Finset.range_add_one, Finset.filter_insert]

/-- The new cutoff point `n + 1` is not already in the previous prime prefix. -/
theorem succ_not_mem_primesBelow (n : ℕ) : n + 1 ∉ primesBelow n := by
  intro hmem
  rw [mem_primesBelow_iff] at hmem
  linarith

/-- Real-slice observable recurrence when the prime cutoff increases by one. -/
theorem offAxisRealObservable_at_zero_succ (n : ℕ) (x : ℝ) :
    OffAxisRealObservable (n + 1) x 0 =
      OffAxisRealObservable n x 0 +
        if Nat.Prime (n + 1) then a (n + 1) * Real.cosh (x * u (n + 1)) else 0 := by
  by_cases hp : Nat.Prime (n + 1)
  · rw [offAxisRealObservable_at_zero, offAxisRealObservable_at_zero, primesBelow_succ, if_pos hp,
      Finset.sum_insert, if_pos hp]
    · ring
    · exact succ_not_mem_primesBelow n
  · rw [offAxisRealObservable_at_zero, offAxisRealObservable_at_zero, primesBelow_succ, if_neg hp,
      if_neg hp]
    ring

/-- Critical-line prefix recurrence at `t = 0`. -/
theorem criticalLineSum_at_zero_succ (n : ℕ) :
    CriticalLineSum (n + 1) 0 =
      CriticalLineSum n 0 + if Nat.Prime (n + 1) then a (n + 1) else 0 := by
  by_cases hp : Nat.Prime (n + 1)
  · rw [criticalLineSum_at_zero, criticalLineSum_at_zero, primesBelow_succ, if_pos hp,
      Finset.sum_insert, if_pos hp]
    · ring
    · exact succ_not_mem_primesBelow n
  · rw [criticalLineSum_at_zero, criticalLineSum_at_zero, primesBelow_succ, if_neg hp, if_neg hp]
    ring

/-- The real-slice distortion is the weighted sum of the primewise deviations
    `cosh(x u_p) - 1`. -/
theorem realAxisDistortion_eq_sum (P : ℕ) (x : ℝ) :
    RealAxisDistortion P x =
      ∑ p ∈ primesBelow P, a p * (Real.cosh (x * u p) - 1) := by
  unfold RealAxisDistortion
  rw [offAxisRealObservable_at_zero, criticalLineSum_at_zero]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  ring

/-- The distortion grows by exactly the new prime's deviation when the cutoff
    increases. -/
theorem realAxisDistortion_succ (n : ℕ) (x : ℝ) :
    RealAxisDistortion (n + 1) x =
      RealAxisDistortion n x +
        if Nat.Prime (n + 1) then a (n + 1) * (Real.cosh (x * u (n + 1)) - 1) else 0 := by
  unfold RealAxisDistortion
  rw [offAxisRealObservable_at_zero_succ, criticalLineSum_at_zero_succ]
  by_cases hp : Nat.Prime (n + 1) <;> simp [hp]
  ring

/-- The one-step distortion increment is always nonnegative. -/
theorem realAxisDistortion_increment_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ if Nat.Prime (n + 1) then a (n + 1) * (Real.cosh (x * u (n + 1)) - 1) else 0 := by
  by_cases hp : Nat.Prime (n + 1)
  · simp [hp]
    refine mul_nonneg (a_nonneg _) ?_
    exact sub_nonneg.mpr (Real.one_le_cosh _)
  · simp [hp]

/-- Prime contributions strictly increase the real-slice distortion whenever a
    new prime enters and the displacement is genuinely off-axis. -/
theorem realAxisDistortion_increment_pos_of_prime {n : ℕ} (hp : Nat.Prime (n + 1))
    {x : ℝ} (hx : x ≠ 0) :
    0 < a (n + 1) * (Real.cosh (x * u (n + 1)) - 1) := by
  have htwo : 2 ≤ n + 1 := hp.two_le
  have hu_pos : 0 < u (n + 1) := by
    unfold u
    exact Real.log_pos (one_lt_phi_of_two_le htwo)
  have hxu_ne : x * u (n + 1) ≠ 0 := mul_ne_zero hx hu_pos.ne'
  refine mul_pos (a_pos_of_two_le htwo) ?_
  have hcosh : 1 < Real.cosh (x * u (n + 1)) := (Real.one_lt_cosh).2 hxu_ne
  linarith

/-- Once the prefix contains prime `2`, any genuine off-axis displacement has
    already created positive real-slice distortion. -/
theorem realAxisDistortion_pos_of_two_le {P : ℕ} (hP : 2 ≤ P) {x : ℝ} (hx : x ≠ 0) :
    0 < RealAxisDistortion P x := by
  rw [realAxisDistortion_eq_sum]
  have hnonneg : ∀ p ∈ primesBelow P, 0 ≤ a p * (Real.cosh (x * u p) - 1) := by
    intro p hp
    refine mul_nonneg (a_nonneg _) ?_
    exact sub_nonneg.mpr (Real.one_le_cosh _)
  have hmem2 : 2 ∈ primesBelow P := by
    rw [mem_primesBelow_iff]
    exact ⟨hP, by decide⟩
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnonneg hmem2)
  have htwo : 2 ≤ 2 := le_rfl
  have hterm : 0 < a 2 * (Real.cosh (x * u 2) - 1) := by
    have hu2_pos : 0 < u 2 := by
      unfold u
      exact Real.log_pos (one_lt_phi_of_two_le htwo)
    have hx2_ne : x * u 2 ≠ 0 := mul_ne_zero hx hu2_pos.ne'
    have hcosh : 1 < Real.cosh (x * u 2) := (Real.one_lt_cosh).2 hx2_ne
    refine mul_pos (a_pos_of_two_le htwo) ?_
    linarith
  simpa using hterm

/-- The general even-channel distortion is the weighted sum of the primewise
    deviations `(\cosh(x u_p) - 1)\cos(t u_p)`. -/
theorem realObservableDistortion_eq_sum (P : ℕ) (x t : ℝ) :
    RealObservableDistortion P x t =
      ∑ p ∈ primesBelow P, a p * (Real.cosh (x * u p) - 1) * Real.cos (t * u p) := by
  unfold RealObservableDistortion OffAxisRealObservable CriticalLineSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  ring

/-- On the real slice, the general distortion specializes to the previously
    defined real-axis distortion. -/
theorem realObservableDistortion_at_zero (P : ℕ) (x : ℝ) :
    RealObservableDistortion P x 0 = RealAxisDistortion P x := by
  unfold RealObservableDistortion RealAxisDistortion
  simp [offAxisRealObservable_at_zero, criticalLineSum_at_zero]

end CircleNative

end
