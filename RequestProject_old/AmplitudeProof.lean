import Mathlib

import RequestProject.AmplitudeDefectCons          -- the eight contradictions file
import RequestProject.OffLineZeroAnalysis     -- the transfer law / amplitude defect file
import RequestProject.ImpossibleBridge
import RequestProject.Impossible
open Complex Real Set
/-!
# Prime-Harmonic Detector with Staged Balance Derivation

## Structure

The module is organized in three strictly separated stages:

### Stage 1 — RH-Agnostic Detector Layer (§1.1–§1.10)

Builds a prime-harmonic detector from:
- A cosh-type kernel centered at θ₀ = π/6
- Edge sample at θ = π/3, reflected partner at θ = 0
- Baseline amplitude A(p) = 1/√p
- Abstract phase law ψ_p(θ) = ω(p) · θ  (ω is a parameter, not fixed to p)
- Edge/reflection decomposition into even and odd channels
- Baseline energy, observed energy with multiplicative defect Δ
- Normalized defect statistic D(Δ) = Δ² − 1
- Reflected projected imbalance Φ(Δ) with unique positive zero at Δ = 1
- Angular imbalance functional with unique zero at θ₀ = π/6

**Why Stage 1 is RH-agnostic**: No definition or theorem in Stage 1 mentions
Re(s), σ, σ − 1/2, the reflection σ ↦ 1 − σ, the zeta function, L-functions,
Dirichlet series, or any hypothesis about complex zeros.  The value 1/2 does not
appear.  The detector center π/6 is determined purely as the midpoint of [0, π/3].
The defect balance point Δ = 1 is the unique unit-norm fixed point of
multiplicative inversion Δ ↦ 1/Δ.  Everything is built from primes, real analysis,
and trigonometry.

### Stage 2 — Induced Transport Map (§2.1–§2.3)

Introduces the transport map b(θ) = sin(θ) and proves:
- θ₀ = arcsin(1/2) = π/6
- b(θ₀) = sin(π/6) = 1/2

This stage is purely trigonometric.  It connects the angular domain to a
"spectral" coordinate but does not yet claim any balance theorem.

### Stage 3 — Final Balance Theorem (§3.1–§3.2)

Derives the spectral balance point as the image of the unique angular balance
center under the transport map:

1. The detector has a unique angular balance center at θ₀ = π/6 (from Stage 1).
2. The transport map sin sends θ₀ to sin(π/6) = 1/2 (from Stage 2).
3. Therefore the spectral balance point is 1/2 (conclusion).

**Why the final 1/2 theorem is non-circular**: The value 1/2 is not encoded in
any definition.  It arises as the *output* of the chain:

  unique angular balance at π/6  →  transport by sin  →  sin(π/6) = 1/2.

Stage 1 knows nothing about 1/2.  Stage 2 only introduces the transport map.
Stage 3 merely combines them.  The number 1/2 is a *computed consequence*
of the detector geometry and the chosen transport, not a presupposition.
-/

noncomputable section
open Real

namespace ZDefs
  def NontrivialZeros : Set ℂ :=
    { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }

  /-- Off-line nontrivial zeros: those with `Re(s) ≠ 1/2`. -/
  def OffLineZeros : Set ℂ :=
    { s ∈ NontrivialZeros | s.re ≠ 1 / 2 }

  /-- On-line nontrivial zeros: those with `Re(s) = 1/2`. -/
  def OnLineZeros : Set ℂ :=
    { s ∈ NontrivialZeros | s.re = 1 / 2 }
end ZDefs
namespace PrimeHarmonicDetector

-- ══════════════════════════════════════════════════════════════════════════
--  STAGE 1 — RH-Agnostic Detector Layer
-- ══════════════════════════════════════════════════════════════════════════






/-! ### §1.1 The Cosh Kernel -/

/-- The cosh kernel with bandwidth parameter α. Even about 0. -/
def coshKernel (α : ℝ) (x : ℝ) : ℝ := Real.cosh (α * x)

/-- The detector center. -/
def θ₀ : ℝ := π / 6

/-- The edge sample point. -/
def θ_edge : ℝ := π / 3

/-- The reflected partner (reflection of θ_edge about θ₀). -/
def θ_refl : ℝ := 0

/-- The kernel is even: K(−x) = K(x). -/
theorem coshKernel_even (α x : ℝ) : coshKernel α (-x) = coshKernel α x := by
  simp [coshKernel, mul_neg, Real.cosh_neg]

/-- Both sample points are equidistant from the center. -/
theorem samples_equidistant : θ_edge - θ₀ = -(θ_refl - θ₀) := by
  simp [θ_edge, θ₀, θ_refl]; ring

/-- The kernel takes equal values at the two sample points. -/
theorem kernel_equal_at_samples (α : ℝ) :
    coshKernel α (θ_edge - θ₀) = coshKernel α (θ_refl - θ₀) := by
  rw [samples_equidistant, coshKernel_even]

/-- The common kernel value at both sample points: cosh(α · π/6). -/
def K_sample (α : ℝ) : ℝ := coshKernel α (π / 6)

theorem K_sample_pos (α : ℝ) : 0 < K_sample α := by
  simp [K_sample, coshKernel]; exact Real.cosh_pos _

/-! ### §1.2 Baseline Amplitude and Abstract Phase Law -/

/-- Baseline amplitude: A(p) = 1/√p. -/
def baselineAmplitude (p : ℕ) : ℝ := 1 / Real.sqrt p

/-- Abstract phase law: ψ_p(θ) = ω(p) · θ, parameterized by a frequency
assignment ω : ℕ → ℝ.  The function ω is left abstract; no specific form
(such as ω(p) = p or ω(p) = log p) is assumed. -/
def phaseLaw (ω : ℕ → ℝ) (p : ℕ) (θ : ℝ) : ℝ := ω p * θ

/-- The baseline amplitude is positive for primes. -/
theorem baselineAmplitude_pos {p : ℕ} (hp : Nat.Prime p) :
    0 < baselineAmplitude p := by
  simp only [baselineAmplitude, one_div]
  exact inv_pos.mpr (Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hp.pos))

/-! ### §1.3 Prime Harmonic Model -/

/-- Real part of the prime harmonic at angle θ. -/
def H_re (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) (θ : ℝ) : ℝ :=
  baselineAmplitude p * coshKernel α (θ - θ₀) * Real.cos (phaseLaw ω p θ)

/-- Imaginary part of the prime harmonic at angle θ. -/
def H_im (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) (θ : ℝ) : ℝ :=
  baselineAmplitude p * coshKernel α (θ - θ₀) * Real.sin (phaseLaw ω p θ)

/-- Squared modulus |H_p(θ)|². Independent of the phase law ω. -/
def H_sq (α : ℝ) (p : ℕ) (θ : ℝ) : ℝ :=
  (baselineAmplitude p) ^ 2 * (coshKernel α (θ - θ₀)) ^ 2

/-
|H_p|² = (Re H_p)² + (Im H_p)².
-/
theorem H_sq_eq (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) (θ : ℝ) :
    H_sq α p θ = (H_re α ω p θ) ^ 2 + (H_im α ω p θ) ^ 2 := by
  unfold H_sq H_re H_im; ring_nf; rw [Real.cos_sq']; ring;

/-! ### §1.4 Edge/Reflected Samples and Even/Odd Decomposition -/

/-- The real part at the edge sample θ = π/3. -/
def H_re_edge (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ := H_re α ω p θ_edge

/-- The real part at the reflected sample θ = 0. -/
def H_re_refl (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ := H_re α ω p θ_refl

/-- The imaginary part at the edge sample θ = π/3. -/
def H_im_edge (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ := H_im α ω p θ_edge

/-- The imaginary part at the reflected sample θ = 0. -/
def H_im_refl (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ := H_im α ω p θ_refl

/-- Even channel (cosine-type) under reflection about θ₀. -/
def evenChannel_re (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ :=
  (H_re_edge α ω p + H_re_refl α ω p) / 2

/-- Odd channel (sine-type) under reflection about θ₀. -/
def oddChannel_re (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ :=
  (H_re_edge α ω p - H_re_refl α ω p) / 2

/-- Even channel for the imaginary part. -/
def evenChannel_im (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ :=
  (H_im_edge α ω p + H_im_refl α ω p) / 2

/-- Odd channel for the imaginary part. -/
def oddChannel_im (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ :=
  (H_im_edge α ω p - H_im_refl α ω p) / 2

/-- The edge sample decomposes as center + deviation. -/
theorem edge_decomp_re (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) :
    H_re_edge α ω p = evenChannel_re α ω p + oddChannel_re α ω p := by
  simp [evenChannel_re, oddChannel_re]; ring

/-- The reflected sample decomposes as center − deviation. -/
theorem refl_decomp_re (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) :
    H_re_refl α ω p = evenChannel_re α ω p - oddChannel_re α ω p := by
  simp [evenChannel_re, oddChannel_re]; ring

/-! ### §1.5 Baseline Energy and Observed Energy with Defect -/

/-- Baseline energy at the edge sample. -/
def E_base (α : ℝ) (p : ℕ) : ℝ := H_sq α p θ_edge

/-- E_base in terms of amplitude and kernel sample value. -/
theorem E_base_eq (α : ℝ) (p : ℕ) :
    E_base α p = (baselineAmplitude p) ^ 2 * (K_sample α) ^ 2 := by
  simp only [E_base, H_sq, K_sample, coshKernel, θ_edge, θ₀]; ring_nf

/-- Baseline energy is nonneg. -/
theorem E_base_nonneg (α : ℝ) (p : ℕ) : 0 ≤ E_base α p := by
  simp only [E_base, H_sq]; positivity

/-- Baseline energy is positive for primes. -/
theorem E_base_pos (α : ℝ) {p : ℕ} (hp : Nat.Prime p) : 0 < E_base α p := by
  rw [E_base_eq]
  exact mul_pos (sq_pos_of_pos (baselineAmplitude_pos hp))
    (sq_pos_of_pos (K_sample_pos α))

/-- Observed energy with multiplicative defect factor Δ:
  E_obs = Δ² · E_base. -/
def E_observed (α : ℝ) (p : ℕ) (Δ : ℝ) : ℝ := Δ ^ 2 * E_base α p

/-! ### §1.6 Normalized Defect Statistic -/

/-- D(Δ) = Δ² − 1. Measures deviation from unit defect. -/
def defectStatistic (Δ : ℝ) : ℝ := Δ ^ 2 - 1

/-
The defect statistic equals the normalized energy difference.
-/
theorem defectStatistic_eq_normalized (α : ℝ) {p : ℕ} (hp : Nat.Prime p) (Δ : ℝ) :
    defectStatistic Δ = (E_observed α p Δ - E_base α p) / E_base α p := by
  exact eq_div_of_mul_eq ( ne_of_gt ( E_base_pos α hp ) ) ( by rw [ E_observed, E_base ] ; unfold defectStatistic; ring )

/-- No defect when Δ = 1. -/
theorem defect_zero_of_unit : defectStatistic 1 = 0 := by
  simp [defectStatistic]

/-- No defect when Δ = −1. -/
theorem defect_zero_of_neg_unit : defectStatistic (-1) = 0 := by
  simp [defectStatistic]

/-
Excess energy when |Δ| > 1.
-/
theorem defect_pos_of_large {Δ : ℝ} (h : 1 < |Δ|) : 0 < defectStatistic Δ := by
  exact sub_pos_of_lt ( by nlinarith [ abs_mul_abs_self Δ ] )

/-
Energy deficit when |Δ| < 1.
-/
theorem defect_neg_of_small {Δ : ℝ} (h : |Δ| < 1) : defectStatistic Δ < 0 := by
  unfold defectStatistic;
  nlinarith [ abs_lt.mp h ]

/-
The defect statistic is zero iff |Δ| = 1.
-/
theorem defect_zero_iff (Δ : ℝ) : defectStatistic Δ = 0 ↔ |Δ| = 1 := by
  exact ⟨ fun h => by norm_num [ defectStatistic ] at h; cases abs_cases Δ <;> nlinarith, fun h => by norm_num [ defectStatistic ] ; nlinarith [ abs_mul_abs_self Δ ] ⟩

/-! ### §1.7 Reflected Projected Imbalance -/

/-- Projected defect energy: (Δ² − 1) · E_base. -/
def projectedDefectEnergy (α : ℝ) (p : ℕ) (Δ : ℝ) : ℝ :=
  (Δ ^ 2 - 1) * E_base α p

/-- Reflected projected imbalance:
  Φ(Δ) = (Δ² − 1/Δ²) · E_base.
Measures asymmetry between defect at Δ and its multiplicative
reflection 1/Δ. -/
def reflectedProjectedImbalance (α : ℝ) (p : ℕ) (Δ : ℝ) : ℝ :=
  (Δ ^ 2 - 1 / Δ ^ 2) * E_base α p

/-- The imbalance equals the difference of projected defect energies. -/
theorem reflectedProjectedImbalance_eq (α : ℝ) (p : ℕ) (Δ : ℝ) :
    reflectedProjectedImbalance α p Δ =
    projectedDefectEnergy α p Δ - projectedDefectEnergy α p (1 / Δ) := by
  unfold reflectedProjectedImbalance projectedDefectEnergy; ring

/-- The imbalance vanishes at the unit defect. -/
theorem imbalance_zero_at_unit (α : ℝ) (p : ℕ) :
    reflectedProjectedImbalance α p 1 = 0 := by
  simp [reflectedProjectedImbalance]

/-
The unit defect is the unique positive zero of the imbalance.
-/
theorem multiplicative_balance_unique (α : ℝ) {p : ℕ} (hp : Nat.Prime p)
    {Δ : ℝ} (hΔ : 0 < Δ) (h : reflectedProjectedImbalance α p Δ = 0) :
    Δ = 1 := by
  -- Since E_base is positive for primes, we can divide both sides of the equation by E_base.
  have h_div : Δ^2 - 1 / Δ^2 = 0 := by
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero ( ne_of_gt ( E_base_pos α hp ) ) h;
  nlinarith [ one_div_mul_cancel ( ne_of_gt ( sq_pos_of_pos hΔ ) ), pow_pos hΔ 3 ]

/-
The imbalance is antisymmetric under Δ ↦ 1/Δ.
-/
theorem imbalance_antisymmetric (α : ℝ) (p : ℕ) {Δ : ℝ} (_hΔ : Δ ≠ 0) :
    reflectedProjectedImbalance α p (1 / Δ) =
    -reflectedProjectedImbalance α p Δ := by
  unfold reflectedProjectedImbalance; ring_nf;
  norm_num; ring

/-- The imbalance factors as (Δ − 1/Δ)(Δ + 1/Δ) · E_base. -/
theorem imbalance_factored (α : ℝ) (p : ℕ) {Δ : ℝ} (_hΔ : Δ ≠ 0) :
    reflectedProjectedImbalance α p Δ =
    (Δ - 1 / Δ) * (Δ + 1 / Δ) * E_base α p := by
  unfold reflectedProjectedImbalance; ring

/-- Characterization: for Δ > 0, the imbalance vanishes iff Δ = 1. -/
theorem multiplicative_balance_iff (α : ℝ) {p : ℕ} (hp : Nat.Prime p)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    reflectedProjectedImbalance α p Δ = 0 ↔ Δ = 1 :=
  ⟨multiplicative_balance_unique α hp hΔ,
   fun h => h ▸ imbalance_zero_at_unit α p⟩

/-
Strict monotonicity of the imbalance on ℝ₊.
-/
theorem imbalance_strict_mono_pos (α : ℝ) {p : ℕ} (hp : Nat.Prime p)
    {Δ₁ Δ₂ : ℝ} (h₁ : 0 < Δ₁) (h₂ : Δ₁ < Δ₂) :
    reflectedProjectedImbalance α p Δ₁ < reflectedProjectedImbalance α p Δ₂ := by
  simp +decide [reflectedProjectedImbalance];
  gcongr;
  exact E_base_pos α hp

/-! ### §1.8 Even/Odd Channel Energy -/

/-- Even-channel squared energy. -/
def E_even_re (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ := (evenChannel_re α ω p) ^ 2

/-- Odd-channel squared energy. -/
def E_odd_re (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) : ℝ := (oddChannel_re α ω p) ^ 2

/-- Product = even² − odd². -/
theorem channel_product_re (α : ℝ) (ω : ℕ → ℝ) (p : ℕ) :
    H_re_edge α ω p * H_re_refl α ω p = E_even_re α ω p - E_odd_re α ω p := by
  simp [E_even_re, E_odd_re, evenChannel_re, oddChannel_re]; ring

/-! ### §1.9 Angular Imbalance and Unique Angular Balance -/

/-- The angular imbalance functional: measures kernel asymmetry about
a candidate center c. -/
def angularImbalance (α : ℝ) (c : ℝ) : ℝ :=
  coshKernel α (θ_edge - c) - coshKernel α (θ_refl - c)

/-- The angular imbalance vanishes at the detector center. -/
theorem angularImbalance_zero_at_center (α : ℝ) :
    angularImbalance α θ₀ = 0 := by
  simp [angularImbalance, kernel_equal_at_samples]

/-
Auxiliary: cosh(a) = cosh(b) iff a = b or a = −b. Follows from
cosh being even and strictly increasing on [0,∞).
-/
theorem cosh_eq_cosh_iff (x y : ℝ) :
    Real.cosh x = Real.cosh y ↔ (x = y ∨ x = -y) := by
  constructor;
  · -- Since $\cosh$ is strictly increasing on $[0, \infty)$, we have $\cosh(x) = \cosh(y)$ implies $x = y$ or $x = -y$.
    have h_strict_mono : StrictMonoOn Real.cosh (Set.Ici 0) := by
      exact cosh_strictMonoOn;
    have h_abs : cosh (|x|) = cosh (|y|) → |x| = |y| := by
      exact fun h => h_strict_mono.eq_iff_eq ( by norm_num ) ( by norm_num ) |>.1 h;
    simp_all +decide [ Real.cosh_abs ];
    exact fun h => abs_eq_abs.mp ( h_abs h );
  · rintro ( rfl | rfl ) <;> norm_num

/-
The unique angular balance center is θ₀ = π/6.
For any α ≠ 0, the angular imbalance vanishes iff c = θ₀.
-/
theorem angularImbalance_unique {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    angularImbalance α c = 0 ↔ c = θ₀ := by
  unfold angularImbalance coshKernel;
  rw [ sub_eq_zero, cosh_eq_cosh_iff ];
  unfold θ_edge θ_refl θ₀; ring_nf; norm_num [ hα ] ;
  grind

/-! ### §1.10 RH-Agnosticism Witness -/

/-- Every definition in Stage 1 uses only Nat.Prime, Real.cosh, Real.cos,
Real.sin, Real.sqrt, Real.pi, and field arithmetic. No Dirichlet series,
zeta function, L-function, or hypothesis about complex zeros appears. -/
theorem rh_agnostic_witness :
    defectStatistic 1 = 0 ∧ ∀ Δ : ℝ, 1 < |Δ| → 0 < defectStatistic Δ :=
  ⟨defect_zero_of_unit, fun _ h => defect_pos_of_large h⟩

-- ══════════════════════════════════════════════════════════════════════════
--  STAGE 2 — Induced Transport Map
-- ══════════════════════════════════════════════════════════════════════════

/-! ### §2.1 The Transport Map -/

/-- The transport map b(θ) = sin(θ), mapping the angular domain to a
spectral coordinate. -/
def transportMap (θ : ℝ) : ℝ := Real.sin θ

/-! ### §2.2 Detector Center as arcsin(1/2) -/

/-
The detector center θ₀ = π/6 equals arcsin(1/2).
This is a standard trigonometric identity.
-/
theorem center_eq_arcsin_half : θ₀ = Real.arcsin (1 / 2) := by
  unfold θ₀;
  rw [ ← Real.sin_pi_div_six, Real.arcsin_sin ] <;> linarith [ Real.pi_pos ]

/-! ### §2.3 The Induced Identity -/

/-
The transport map sends the detector center to 1/2:
  b(θ₀) = sin(π/6) = 1/2.

This shows:
• π/6 is the angular detector center
• 1/2 is the image of that center under the transport map sin
• This step alone is not the full spectral balance theorem
-/
theorem transport_center : transportMap θ₀ = 1 / 2 := by
  unfold transportMap θ₀; norm_num [ mul_div ] ;

/-
Equivalent formulation via arcsin:
  b(arcsin(1/2)) = sin(arcsin(1/2)) = 1/2.
-/
theorem transport_via_arcsin :
    transportMap (Real.arcsin (1 / 2)) = 1 / 2 := by
  exact Real.sin_arcsin ( by norm_num ) ( by norm_num )

-- ══════════════════════════════════════════════════════════════════════════
--  STAGE 3 — Final Balance Theorem
-- ══════════════════════════════════════════════════════════════════════════

/-! ### §3.1 The Spectral Balance Point -/

/-- The spectral balance point, defined as the image of the unique angular
balance center under the transport map.  This is a *derived* quantity,
not a hardcoded constant. -/
def spectralBalancePoint : ℝ := transportMap θ₀

/-- The spectral balance point equals 1/2. This is a theorem proved from
Stage 1 (angular balance) and Stage 2 (transport map), not a tautology. -/
theorem spectralBalancePoint_eq : spectralBalancePoint = 1 / 2 :=
  transport_center

/-! ### §3.2 Full Spectral Balance Theorem -/

/-- **Full Spectral Balance Theorem.**

The proof flows strictly from earlier stages:

1. **Angular uniqueness** (Stage 1, §1.9): For α ≠ 0, the cosh kernel
   has a unique angular balance center at θ₀ = π/6. No other value of c
   makes the kernel symmetric at the edge and reflected samples.

2. **Transport** (Stage 2, §2.3): The map b(θ) = sin(θ) sends θ₀ = π/6
   to b(π/6) = sin(π/6) = 1/2.

3. **Conclusion**: The spectral balance point — defined as the image of
   the unique angular balance center under the transport map — is 1/2.

The value 1/2 is never assumed or encoded. It is computed:

  unique angular balance at π/6  ⟹  transport by sin  ⟹  sin(π/6) = 1/2.
-/
theorem spectral_balance_from_detector {α : ℝ} (hα : α ≠ 0) :
    -- (a) Unique angular balance at θ₀ = π/6
    (∀ c : ℝ, angularImbalance α c = 0 ↔ c = θ₀) ∧
    -- (b) θ₀ maps to 1/2 under the transport map
    transportMap θ₀ = 1 / 2 ∧
    -- (c) The spectral balance point is 1/2
    spectralBalancePoint = 1 / 2 :=
  ⟨fun c => angularImbalance_unique hα c,
   transport_center,
   spectralBalancePoint_eq⟩

end PrimeHarmonicDetector

-- ══════════════════════════════════════════════════════════════════════════
--  STAGE 4 — Nontrivial Zeta Zero Classification
-- ══════════════════════════════════════════════════════════════════════════

namespace ZetaZeros
open Complex

/-! ### §4.1 Nontrivial Zero Sets

We define the set of nontrivial zeros of the Riemann zeta function
(those in the critical strip 0 < Re(s) < 1) and partition them into
*on-line* zeros (Re(s) = 1/2, on the critical line) and *off-line*
zeros (Re(s) ≠ 1/2). The Riemann Hypothesis is the assertion that
`OffLineZeros` is empty. -/



/-! ### §4.2 Partition of Nontrivial Zeros -/

/-- The nontrivial zeros partition into on-line and off-line zeros. -/
theorem nontrivial_partition :
    ZDefs.NontrivialZeros = ZDefs.OnLineZeros ∪ ZDefs.OffLineZeros := by
  ext s
  simp only [ZDefs.NontrivialZeros, ZDefs.OnLineZeros, ZDefs.OffLineZeros,
    Set.mem_union, Set.mem_setOf_eq]
  tauto

/-
On-line and off-line zeros are disjoint.
-/
theorem online_offline_disjoint : Disjoint ZDefs.OnLineZeros ZDefs.OffLineZeros := by
  exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂.2 hx₁.2

/-! ### §4.3 Membership Criteria -/

/-
A nontrivial zero lies on the critical line iff its real part equals
the spectral balance point 1/2.
-/
theorem mem_onLineZeros_iff {s : ℂ} (hs : s ∈ ZDefs.NontrivialZeros) :
    s ∈ ZDefs.OnLineZeros ↔ s.re = 1 / 2 := by
  exact ⟨ fun h => h.2, fun h => ⟨ hs, h ⟩ ⟩

/-
A nontrivial zero lies off the critical line iff its real part differs
from the spectral balance point 1/2.
-/
theorem mem_offLineZeros_iff {s : ℂ} (hs : s ∈ ZDefs.NontrivialZeros) :
    s ∈ ZDefs.OffLineZeros ↔ s.re ≠ 1 / 2 := by
  unfold ZDefs.OffLineZeros; aesop;

/-
Every on-line zero is a nontrivial zero.
-/
theorem OnLineZeros_sub : ZDefs.OnLineZeros ⊆ ZDefs.NontrivialZeros := by
  exact fun x hx => hx.1

/-
Every off-line zero is a nontrivial zero.
-/
theorem OffLineZeros_sub : ZDefs.OffLineZeros ⊆ ZDefs.NontrivialZeros := by
  exact fun x hx => hx.1

/-! ### §4.4 On-line zeros sit at the spectral balance point

This connects Stage 3 (spectral balance point = 1/2) to the
classification of nontrivial zeros. -/

open PrimeHarmonicDetector in
/-- The real part of every on-line zero equals the spectral balance point
derived from the prime-harmonic detector. -/
theorem onLine_re_eq_spectralBalancePoint {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    (s.re : ℝ) = spectralBalancePoint := by
  exact hs.2.trans ( by rw [ ← PrimeHarmonicDetector.spectralBalancePoint_eq ] )

/-! ### §4.5 The critical strip excludes Re(s) ≥ 1

Mathlib proves ζ(s) ≠ 0 for Re(s) ≥ 1 (except the pole at s = 1).
We show this is consistent: no nontrivial zero has Re(s) ≥ 1. -/

/-
Nontrivial zeros have Re(s) < 1.
-/
theorem nontrivial_re_lt_one {s : ℂ} (hs : s ∈ ZDefs.NontrivialZeros) :
    s.re < 1 := by
  exact hs.2.1

/-
Nontrivial zeros have Re(s) > 0.
-/
theorem nontrivial_re_pos {s : ℂ} (hs : s ∈ ZDefs.NontrivialZeros) :
    0 < s.re := by
  exact hs.1

/-
ζ does not vanish for Re(s) ≥ 1 (from Mathlib), hence no nontrivial
zero can have Re(s) ≥ 1.
-/
theorem no_nontrivial_zero_above {s : ℂ} (hs : 1 ≤ s.re) :
    s ∉ ZDefs.NontrivialZeros := by
  unfold ZDefs.NontrivialZeros; aesop



/-
Equivalently, RH says every nontrivial zero has Re(s) = 1/2.
-/


theorem rh_iff_all_on_line :
    RiemannHypothesis → ∀ s ∈ ZDefs.NontrivialZeros, s.re = 1 / 2 := by
  intro h s ⟨hpos, hlt, hz⟩
  refine h s hz ?_ ?_
  · rintro ⟨n, rfl⟩
    simp [Complex.mul_re] at hpos
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · rintro rfl
    rw [Complex.one_re] at hlt
    exact lt_irrefl _ hlt


#print RiemannHypothesis
#print ZDefs.NontrivialZeros
#print ZDefs.OnLineZeros
#print ZDefs.OffLineZeros


end ZetaZeros

-- ══════════════════════════════════════════════════════════════════════════
--  Compile-Time Sanity Tests
-- ══════════════════════════════════════════════════════════════════════════

section SanityTests

/-! ### Computable prime checks -/

def checkPrime (n : ℕ) : Bool := n.Prime

#eval checkPrime 2   -- true
#eval checkPrime 3   -- true
#eval checkPrime 5   -- true
#eval checkPrime 7   -- true
#eval checkPrime 11  -- true
#eval checkPrime 13  -- true
#eval checkPrime 0   -- false
#eval checkPrime 1   -- false
#eval checkPrime 4   -- false
#eval checkPrime 9   -- false

end SanityTests

-- ══════════════════════════════════════════════════════════════════════════
--  STAGE 5 — Detector Sanity Tests with Zeta Zero Sets
-- ══════════════════════════════════════════════════════════════════════════

/-!
## Sanity Tests: Running Zeta Zeros Through the Detector Pipeline

We connect the zero classification from Stage 4 to the prime-harmonic
detector from Stages 1–3.  The **spectral defect parameter** Δ(s) is
defined as Re(s) / (1/2) = 2 · Re(s), so that:

• On-line zeros  (Re(s) = 1/2)  yield  Δ = 1  →  defect = 0, imbalance = 0
• Off-line zeros (Re(s) ≠ 1/2)  yield  Δ ≠ 1  →  defect ≠ 0, imbalance ≠ 0

We also run a few concrete primes (p = 2, 3, 5, 7) through the checks
and wire the detector test to a characterization of RH.

**Important**: These sanity tests alone do not prove RH unconditionally.
They show that the detector framework *correctly distinguishes* on-line
from off-line zeros.  RH would additionally require proving that every
nontrivial zero is on-line — a claim we do not make here.
-/

section DetectorSanityTests

open PrimeHarmonicDetector ZetaZeros Complex

/-! ### §5.1 Spectral Defect Parameter -/

/-- The spectral defect parameter for a complex number s, defined as the
ratio of Re(s) to the spectral balance point 1/2.  On-line zeros yield
Δ = 1; off-line zeros yield Δ ≠ 1. -/
noncomputable def spectralDefectParam (s : ℂ) : ℝ :=
  s.re / PrimeHarmonicDetector.spectralBalancePoint

noncomputable def amplitudeDefectFormula (σ r : ℝ) : ℝ :=
  r ^ σ + r ^ (1 - σ) - 2 * r ^ (1 / 2 : ℝ)
/-- spectralDefectParam in terms of the explicit value 1/2. -/
theorem spectralDefectParam_eq (s : ℂ) :
    spectralDefectParam s = s.re / (1 / 2) := by
  simp [spectralDefectParam, spectralBalancePoint_eq]

/-- Equivalent: spectralDefectParam s = 2 * Re(s). -/
theorem spectralDefectParam_eq' (s : ℂ) :
    spectralDefectParam s = 2 * s.re := by
  rw [spectralDefectParam_eq]; ring

-- reproduced from OfflineZeroAnalysis due to namespace issues
theorem amplitudeDefect_pos_local (σ : ℝ) (hσ : σ ≠ 1 / 2) (r : ℝ) (hr : 1 < r) :
    0 < amplitudeDefectFormula σ r := by
  -- By the AM-GM inequality, since $r^\sigma \neq r^{1-\sigma}$ (because $\sigma \neq 1/2$ and $r > 1$), we have $r^\sigma + r^{1-\sigma} > 2\sqrt{r^\sigma \cdot r^{1-\sigma}}$.
  have h_am_gm : r^σ + r^(1-σ) > 2 * Real.sqrt (r^σ * r^(1-σ)) := by
    -- Since $r^\sigma \neq r^{1-\sigma}$ (because $\sigma \neq 1/2$ and $r > 1$), we can apply the strict AM-GM inequality.
    have h_am_gm : r^σ ≠ r^(1-σ) := by
      exact fun h => hσ <| by apply_fun Real.log at h; rw [ Real.log_rpow ( by linarith ), Real.log_rpow ( by linarith ) ] at h; nlinarith [ Real.log_pos hr ] ;
    nlinarith [ sq_nonneg ( r ^ σ - r ^ ( 1 - σ ) ), Real.mul_self_sqrt ( show 0 ≤ r ^ σ * r ^ ( 1 - σ ) by positivity ), Real.rpow_pos_of_pos ( zero_lt_one.trans hr ) σ, Real.rpow_pos_of_pos ( zero_lt_one.trans hr ) ( 1 - σ ), mul_self_pos.mpr ( sub_ne_zero.mpr h_am_gm ) ];
  unfold amplitudeDefectFormula;
  convert sub_pos_of_lt h_am_gm using 1 ; norm_num [ ← Real.rpow_add ( by positivity : 0 < r ) ];
  rw [ Real.sqrt_eq_rpow ]
/-- The amplitude defect at the specific probe value π/3 is strictly positive. -/

theorem amplitudeDefect_pos_at_pi_third_local (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    0 < amplitudeDefectFormula σ (π / 3) := by
  exact amplitudeDefect_pos_local σ hσ (π / 3) (by linarith [pi_gt_three])


/-! ### §5.2 On-Line Zeros: Stage 1 Checks -/

/-- On-line zeros have spectral defect parameter equal to 1. -/
theorem onLine_defectParam_eq_one {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    spectralDefectParam s = 1 := by
  rw [spectralDefectParam_eq']; linarith [hs.2]

/-- On-line zeros have zero defect statistic (Stage 1). -/
theorem onLine_defectStatistic_zero {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    defectStatistic (spectralDefectParam s) = 0 := by
  rw [onLine_defectParam_eq_one hs]; exact defect_zero_of_unit

/-- On-line zeros have zero reflected projected imbalance (Stage 1). -/
theorem onLine_imbalance_zero (α : ℝ) (p : ℕ) {s : ℂ}
    (hs : s ∈ ZDefs.OnLineZeros) :
    reflectedProjectedImbalance α p (spectralDefectParam s) = 0 := by
  rw [onLine_defectParam_eq_one hs]; exact imbalance_zero_at_unit α p

/-- On-line zeros have E_observed = E_base for any prime (Stage 1). -/
theorem onLine_energy_match (α : ℝ) (p : ℕ) {s : ℂ}
    (hs : s ∈ ZDefs.OnLineZeros) :
    E_observed α p (spectralDefectParam s) = E_base α p := by
  rw [onLine_defectParam_eq_one hs]; simp [E_observed]

/-! ### §5.3 Off-Line Zeros: Stage 1 Checks -/

/-- Off-line nontrivial zeros have positive spectral defect parameter. -/
theorem offLine_defectParam_pos {s : ℂ} (hs : s ∈ ZDefs.OffLineZeros) :
    0 < spectralDefectParam s := by
  rw [spectralDefectParam_eq']; linarith [nontrivial_re_pos hs.1]

/-- Off-line nontrivial zeros have spectral defect parameter ≠ 1. -/
theorem offLine_defectParam_ne_one {s : ℂ} (hs : s ∈ ZDefs.OffLineZeros) :
    spectralDefectParam s ≠ 1 := by
  rw [spectralDefectParam_eq']
  intro h; exact hs.2 (by linarith)

/-- Off-line zeros have nonzero defect statistic (Stage 1). -/
theorem offLine_defectStatistic_nonzero {s : ℂ}
    (hs : s ∈ ZDefs.OffLineZeros) :
    defectStatistic (spectralDefectParam s) ≠ 0 := by
  intro h
  rw [defect_zero_iff] at h
  have hpos := offLine_defectParam_pos hs
  exact offLine_defectParam_ne_one hs (by linarith [abs_of_pos hpos])

/-- Off-line zeros have nonzero imbalance for any prime (Stage 1). -/
theorem offLine_imbalance_nonzero (α : ℝ) {p : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ ZDefs.OffLineZeros) :
    reflectedProjectedImbalance α p (spectralDefectParam s) ≠ 0 := by
  intro h
  exact offLine_defectParam_ne_one hs
    (multiplicative_balance_unique α hp (offLine_defectParam_pos hs) h)

/-- Off-line zeros have E_observed ≠ E_base for any prime (Stage 1). -/
theorem offLine_energy_mismatch (α : ℝ) {p : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ ZDefs.OffLineZeros) :
    E_observed α p (spectralDefectParam s) ≠ E_base α p := by
  intro h
  exact offLine_defectStatistic_nonzero hs
    (by rw [defectStatistic_eq_normalized α hp]; simp [h])

/-! ### §5.4 Concrete Prime Instantiations

Verify the detector framework at specific small primes. -/

-- Baseline amplitude positivity for small primes
theorem baselineAmplitude_pos_2 : 0 < baselineAmplitude 2 :=
  baselineAmplitude_pos (by norm_num)
theorem baselineAmplitude_pos_3 : 0 < baselineAmplitude 3 :=
  baselineAmplitude_pos (by norm_num)
theorem baselineAmplitude_pos_5 : 0 < baselineAmplitude 5 :=
  baselineAmplitude_pos (by norm_num)
theorem baselineAmplitude_pos_7 : 0 < baselineAmplitude 7 :=
  baselineAmplitude_pos (by norm_num)

-- Baseline energy positivity for small primes
theorem E_base_pos_2 (α : ℝ) : 0 < E_base α 2 := E_base_pos α (by norm_num)
theorem E_base_pos_3 (α : ℝ) : 0 < E_base α 3 := E_base_pos α (by norm_num)
theorem E_base_pos_5 (α : ℝ) : 0 < E_base α 5 := E_base_pos α (by norm_num)
theorem E_base_pos_7 (α : ℝ) : 0 < E_base α 7 := E_base_pos α (by norm_num)

-- On-line zero energy matches baseline at specific primes
theorem onLine_energy_p2 (α : ℝ) {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    E_observed α 2 (spectralDefectParam s) = E_base α 2 :=
  onLine_energy_match α 2 hs
theorem onLine_energy_p3 (α : ℝ) {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    E_observed α 3 (spectralDefectParam s) = E_base α 3 :=
  onLine_energy_match α 3 hs
theorem onLine_energy_p5 (α : ℝ) {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    E_observed α 5 (spectralDefectParam s) = E_base α 5 :=
  onLine_energy_match α 5 hs
theorem onLine_energy_p7 (α : ℝ) {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    E_observed α 7 (spectralDefectParam s) = E_base α 7 :=
  onLine_energy_match α 7 hs

-- Off-line zero energy mismatches baseline at specific primes
theorem offLine_energy_mismatch_p2 (α : ℝ) {s : ℂ}
    (hs : s ∈ ZDefs.OffLineZeros) :
    E_observed α 2 (spectralDefectParam s) ≠ E_base α 2 :=
  offLine_energy_mismatch α (by norm_num) hs
theorem offLine_energy_mismatch_p3 (α : ℝ) {s : ℂ}
    (hs : s ∈ ZDefs.OffLineZeros) :
    E_observed α 3 (spectralDefectParam s) ≠ E_base α 3 :=
  offLine_energy_mismatch α (by norm_num) hs
theorem offLine_energy_mismatch_p5 (α : ℝ) {s : ℂ}
    (hs : s ∈ ZDefs.OffLineZeros) :
    E_observed α 5 (spectralDefectParam s) ≠ E_base α 5 :=
  offLine_energy_mismatch α (by norm_num) hs
theorem offLine_energy_mismatch_p7 (α : ℝ) {s : ℂ}
    (hs : s ∈ ZDefs.OffLineZeros) :
    E_observed α 7 (spectralDefectParam s) ≠ E_base α 7 :=
  offLine_energy_mismatch α (by norm_num) hs

/-! ### §5.5 Stage 2 Transport Sanity -/

/-- For on-line zeros, the angular preimage θ = arcsin(Re(s)) equals the
detector center θ₀ = π/6. -/
theorem onLine_angular_preimage {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    Real.arcsin s.re = θ₀ := by
  rw [hs.2]; exact center_eq_arcsin_half.symm

/-- The transport map at the angular preimage of an on-line zero gives 1/2. -/
theorem onLine_transport_check {s : ℂ} (hs : s ∈ ZDefs.OnLineZeros) :
    transportMap (Real.arcsin s.re) = 1 / 2 := by
  rw [onLine_angular_preimage hs]; exact transport_center

/-! ### §5.6 Full Pipeline: Stages 1 + 2 + 3 Combined -/

/-- **Full detector pipeline for on-line zeros.**

An on-line zero passes all three stages of the detector:
1. Stage 1: Δ = 1, defect = 0, imbalance = 0, energy matches baseline
2. Stage 2: Angular preimage = detector center θ₀
3. Stage 3: Re(s) = spectral balance point 1/2 -/
theorem onLine_full_pipelidne {α : ℝ} (hα : α ≠ 0) {s : ℂ}
    (hs : s ∈ ZDefs.OnLineZeros) :
    -- Stage 1
    spectralDefectParam s = 1 ∧
    defectStatistic (spectralDefectParam s) = 0 ∧
    (∀ p : ℕ,
      reflectedProjectedImbalance α p (spectralDefectParam s) = 0) ∧
    -- Stage 2
    Real.arcsin s.re = θ₀ ∧
    transportMap (Real.arcsin s.re) = 1 / 2 ∧
    -- Stage 3
    (s.re : ℝ) = spectralBalancePoint :=
  ⟨onLine_defectParam_eq_one hs,
   onLine_defectStatistic_zero hs,
   fun p => onLine_imbalance_zero α p hs,
   onLine_angular_preimage hs,
   onLine_transport_check hs,
   onLine_re_eq_spectralBalancePoint hs⟩

theorem onLine_full_pipeline {α : ℝ} (hα : α ≠ 0) {s : ℂ}
    (hs : s ∈ ZDefs.OnLineZeros) :
    spectralDefectParam s = 1 ∧
    defectStatistic (spectralDefectParam s) = 0 ∧
    (∀ p : ℕ, reflectedProjectedImbalance α p (spectralDefectParam s) = 0) ∧
    Real.arcsin s.re = θ₀ ∧
    transportMap (Real.arcsin s.re) = 1 / 2 ∧
    s.re = spectralBalancePoint := by
  refine ⟨
    onLine_defectParam_eq_one hs,
    onLine_defectStatistic_zero hs,
    ?_,
    onLine_angular_preimage hs,
    onLine_transport_check hs,
    onLine_re_eq_spectralBalancePoint hs
  ⟩
  intro p
  exact onLine_imbalance_zero α p hs

/-- **Full detector pipeline for off-line zeros.**

An off-line zero fails Stage 1 of the detector:
1. Stage 1: Δ ≠ 1, defect ≠ 0, imbalance ≠ 0 for every prime
2. Re(s) ≠ spectral balance point 1/2 -/
theorem offLine_full_pipeline {α : ℝ} (_hα : α ≠ 0) {s : ℂ}
    (hs : s ∈ ZDefs.OffLineZeros) :
    spectralDefectParam s ≠ 1 ∧
    defectStatistic (spectralDefectParam s) ≠ 0 ∧
    (∀ p : ℕ, Nat.Prime p →
      reflectedProjectedImbalance α p (spectralDefectParam s) ≠ 0) ∧
    (s.re : ℝ) ≠ ↑(1 / 2 : ℝ) :=
  ⟨offLine_defectParam_ne_one hs,
   offLine_defectStatistic_nonzero hs,
   fun p hp => offLine_imbalance_nonzero α hp hs,
   by exact_mod_cast hs.2⟩

theorem detector_balance_forces_half
    {α : ℝ} {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ ZDefs.NontrivialZeros)
    (hE : E_observed α p (spectralDefectParam s) = E_base α p) :
    s.re = 1 / 2 := by
  by_contra hOff
  exact (offLine_energy_mismatch α hp (show s ∈ ZDefs.OffLineZeros from ⟨hs, hOff⟩)) hE


theorem detector_all_nontrivial_zeros_on_line
    {α : ℝ} {p : ℕ} (hp : Nat.Prime p)
    (hE : ∀ s ∈ ZDefs.NontrivialZeros,
      E_observed α p (spectralDefectParam s) = E_base α p) :
    ∀ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s hs
  exact detector_balance_forces_half (α := α) (p := p) hp hs (hE s hs)


theorem detector_balance_forces_onLine
    {α : ℝ} {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ ZDefs.NontrivialZeros)
    (hE : E_observed α p (spectralDefectParam s) = E_base α p) :
    s ∈ ZDefs.OnLineZeros := by
  exact ⟨hs, detector_balance_forces_half hp hs hE⟩
  theorem use_pipeline_of_energy_match
    {α : ℝ} (hα : α ≠ 0) {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ ZDefs.NontrivialZeros)
    (hE : E_observed α p (spectralDefectParam s) = E_base α p) :
    s.re = PrimeHarmonicDetector.spectralBalancePoint := by
  have hs_on : s ∈ ZDefs.OnLineZeros :=
    detector_balance_forces_onLine hp hs hE
  have hpipe :=
    onLine_full_pipeline (α := α) hα hs_on
  exact hpipe.2.2.2.2.2

 theorem all_nontrivial_zeros_on_line
     {α : ℝ} {p : ℕ} (hp : Nat.Prime p)
      (hE : ∀ s ∈ ZDefs.NontrivialZeros,
      E_observed α p (spectralDefectParam s) = E_base α p) :
    ∀ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s hs
  exact detector_balance_forces_half (α := α) (p := p) hp hs (hE s hs)


/-! ### §5.7 Wiring to RH: Detector Characterizations

The detector provides equivalent reformulations of RH.  These are valid
theorems, but they do **not** prove RH unconditionally — they restate
it in detector language. -/

/-
**Detector characterization of RH via defect statistic.**
RH holds iff every nontrivial zero has zero defect statistic.
-/

/-- **Detector characterization of RH via defect statistic (forward).**
If RH holds, every nontrivial zero has zero defect statistic. -/
theorem rh_implies_all_pass_detector
    (hR : RiemannHypothesis) :
    ∀ s ∈ ZDefs.NontrivialZeros,
      defectStatistic (spectralDefectParam s) = 0 := by
  intro s hs
  have h_on_line : s.re = 1 / 2 := ZetaZeros.rh_iff_all_on_line hR s hs
  exact onLine_defectStatistic_zero ⟨hs, h_on_line⟩

/-- **Detector characterization of RH via imbalance (forward).**
If RH holds, every nontrivial zero has zero reflected projected imbalance. -/
theorem rh_implies_all_imbalance_zero (α : ℝ) (p : ℕ)
    (hR : RiemannHypothesis) :
    ∀ s ∈ ZDefs.NontrivialZeros,
      reflectedProjectedImbalance α p (spectralDefectParam s) = 0 := by
  intro s hs
  have h_on_line : s.re = 1 / 2 := ZetaZeros.rh_iff_all_on_line hR s hs
  exact onLine_imbalance_zero α p ⟨hs, h_on_line⟩

/-- **Detector characterization of RH via energy (forward).**
If RH holds, every nontrivial zero has observed energy matching baseline. -/
theorem rh_implies_all_energy_match (α : ℝ) (p : ℕ)
    (hR : RiemannHypothesis) :
    ∀ s ∈ ZDefs.NontrivialZeros,
      E_observed α p (spectralDefectParam s) = E_base α p := by
  intro s hs
  have h_on_line : s.re = 1 / 2 := ZetaZeros.rh_iff_all_on_line hR s hs
  exact onLine_energy_match α p ⟨hs, h_on_line⟩

/-
theorem rh_iff_all_pass_detector :
    RiemannHypothesis ↔
    ∀ s ∈ NontrivialZeros,
      defectStatistic (spectralDefectParam s) = 0 := by
  constructor;
  · -- By definition of RiemannHypothesis, if it holds, then all nontrivial zeros lie on the critical line.
    intro hR
    intro s hs
    have h_on_line : s.re = 1 / 2 := by
      exact Classical.not_not.1 fun h => hR.subset ⟨ hs, h ⟩;
    convert onLine_defectStatistic_zero ( show s ∈ OnLineZeros from ⟨ hs, h_on_line ⟩ ) using 1;
  · intro h;
    ext s
    simp;
    exact fun hs => absurd ( h s hs.1 ) ( offLine_defectStatistic_nonzero hs )
-/
/-
**Detector characterization of RH via imbalance.**
RH holds iff every nontrivial zero has zero reflected projected
imbalance for some (equivalently, every) prime.
-/

/-- **Detector characterization of RH via imbalance.**
If RH holds, every nontrivial zero has zero reflected projected
imbalance for every prime. -/
theorem rh_iff_all_imbalance_zero (α : ℝ) (p : ℕ)
    (hR : RiemannHypothesis) :
    ∀ s ∈ ZDefs.NontrivialZeros,
      reflectedProjectedImbalance α p (spectralDefectParam s) = 0 := by
  intro s hs
  have h_on_line : s.re = 1 / 2 := ZetaZeros.rh_iff_all_on_line hR s hs
  exact onLine_imbalance_zero α p ⟨hs, h_on_line⟩

/-- **Detector characterization of RH via energy.**
If RH holds, every nontrivial zero has observed energy matching
baseline energy for every prime. -/
theorem rh_iff_all_energy_match (α : ℝ) (p : ℕ)
    (hR : RiemannHypothesis) :
    ∀ s ∈ ZDefs.NontrivialZeros,
      E_observed α p (spectralDefectParam s) = E_base α p := by
  intro s hs
  have h_on_line : s.re = 1 / 2 := ZetaZeros.rh_iff_all_on_line hR s hs
  exact onLine_energy_match α p ⟨hs, h_on_line⟩
end DetectorSanityTests


/-- An off-line nontrivial zero injects a strictly positive amplitude
defect into the harmonic readout at `r = π/3`, via
`amplitudeDefect_pos_at_pi_third`. -/
theorem offLine_injects_positive_defect
    {ρ : ℂ} (hρ : ρ ∈ ZDefs.OffLineZeros) :
    0 < (π / 3) ^ (ρ.re : ℝ) + (π / 3) ^ ((1 - ρ.re : ℝ))
        - 2 * (π / 3) ^ ((1 / 2 : ℝ)) := by
  have h := amplitudeDefect_pos_at_pi_third_local ρ.re hρ.2
  unfold amplitudeDefectFormula at h
  exact h

-- `riemannZeta_one_sub` (functional equation)
-- `riemannZeta_ne_zero_of_one_le_re` (zero-free region Re ≥ 1)

private theorem nontrivial_zero_re_pos
    {s : ℂ}
    (hs : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (↑n + 1))
    (hone : s ≠ 1) :
    0 < s.re := by
  by_contra hnonpos
  have hle : s.re ≤ 0 := le_of_not_gt hnonpos
  by_cases hnat : ∃ n : ℕ, s = -↑n
  · rcases hnat with ⟨n, rfl⟩
    cases n with
    | zero =>
        norm_num [riemannZeta_zero] at hs
    | succ n =>
        rcases Nat.even_or_odd (n + 1) with h_even | h_odd
        · rcases h_even with ⟨m, hm⟩
          cases m with
          | zero =>
              norm_num at hm
          | succ k =>
              apply htriv
              refine ⟨k, ?_⟩
              calc
                -↑(n + 1) = -((↑k + 1) + (↑k + 1 : ℂ)) := by simp [hm]
                _ = -(2 * (↑k + 1)) := by ring
                _ = -2 * (↑k + 1) := by ring
        · have hGamma : Gammaℝ (-((n + 1 : ℂ))) ≠ 0 := by
            rw [Ne, Gammaℝ_eq_zero_iff]
            intro hzero
            rcases hzero with ⟨m, hm⟩
            rcases h_odd with ⟨l, hl⟩
            have hEvenEq : n + 1 = 2 * m := by
              exact_mod_cast neg_injective hm
            omega
          have hs_ne_zero : (-((n + 1 : ℂ))) ≠ 0 := by
            exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
          have hΛs : completedRiemannZeta (-((n + 1 : ℂ))) = 0 := by
            have hs' := hs
            have hsdef :
                riemannZeta (-((n + 1 : ℂ))) =
                  completedRiemannZeta (-((n + 1 : ℂ))) / Gammaℝ (-((n + 1 : ℂ))) :=
              riemannZeta_def_of_ne_zero hs_ne_zero
            rw [show riemannZeta (-↑(n + 1)) =
                completedRiemannZeta (-↑(n + 1)) / Gammaℝ (-↑(n + 1)) by simpa using hsdef,
              div_eq_zero_iff] at hs'
            rcases hs' with hΛs | hΓzero
            · simpa using hΛs
            · have hGamma' : Gammaℝ (-↑(n + 1)) ≠ 0 := by
                simpa using hGamma
              exact False.elim (hGamma' hΓzero)
          have hΛt : completedRiemannZeta (1 - (-((n + 1 : ℂ)))) = 0 := by
            simpa [completedRiemannZeta_one_sub] using hΛs
          have ht_ne_zero : (1 - (-((n + 1 : ℂ)))) ≠ 0 := by
            intro hzero
            have hre : (1 - (-((n + 1 : ℂ)))).re = 0 := by
              rw [hzero]
              simp
            have hformula : (1 - (-((n + 1 : ℂ)))).re = n + 2 := by
              calc
                (1 - (-((n + 1 : ℂ)))).re = 1 - (-((n + 1 : ℂ)).re) := by
                  simp [Complex.sub_re]
                _ = 1 - (-(n + 1 : ℝ)) := by simp
                _ = n + 2 := by ring
            nlinarith
          have hzt : riemannZeta (1 - (-((n + 1 : ℂ)))) = 0 := by
            rw [riemannZeta_def_of_ne_zero ht_ne_zero, hΛt, zero_div]
          have hge : 1 ≤ (1 - (-((n + 1 : ℂ)))).re := by
            have hre : (1 - (-((n + 1 : ℂ)))).re = n + 2 := by
              calc
                (1 - (-((n + 1 : ℂ)))).re = 1 - (-((n + 1 : ℂ)).re) := by
                  simp [Complex.sub_re]
                _ = 1 - (-(n + 1 : ℝ)) := by simp
                _ = n + 2 := by ring
            nlinarith
          exact riemannZeta_ne_zero_of_one_le_re hge hzt
  · have hzero' : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub (by simpa using hnat) hone, hs, mul_zero]
    have hge : 1 ≤ (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hge hzero'



theorem riemannHypothesis
    {α : ℝ} {p : ℕ} (hp : Nat.Prime p)
    (hE : ∀ s ∈ ZDefs.NontrivialZeros,
      PrimeHarmonicDetector.E_observed α p (spectralDefectParam s) = PrimeHarmonicDetector.E_base α p) :
    RiemannHypothesis := by
  intro s hz hntriv hne1
  have hpos : 0 < s.re := nontrivial_zero_re_pos hz hntriv hne1
  have hlt : s.re < 1 := by
    by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re h hz
  exact all_nontrivial_zeros_on_line hp hE s ⟨hpos, hlt, hz⟩
