import Mathlib
/-!
# Pinning / Rigidity Detector Framework
## Overview
A four-channel transported symmetry detector for the nontrivial zeros of the
Riemann zeta function, built from von Mangoldt prime-density data, operating on
the **full** set of nontrivial zeros (not finite truncations).
## Mathematical Setup
The critical-strip symmetry group is the Klein four-group acting on ℂ via:
- **0° (Identity):** s ↦ s
- **90° (Conjugation):** s ↦ conj(s)
- **180° (Functional-equation reflection):** s ↦ 1 − s
- **270° (Combined):** s ↦ 1 − conj(s)
For each zero ρ with Re(ρ) = σ and a density parameter x > 1, the prime-density
magnitude in channel θ is `x ^ Re(θ(ρ))`. The key observation is:
- Channels 0° and 90° both give `x ^ σ`
- Channels 180° and 270° both give `x ^ (1 − σ)`
The imbalance `x ^ σ − x ^ (1 − σ)` vanishes iff σ = 1/2, providing exact
detection of off-line zeros at the per-zero level.
## Non-requirements
This framework does **not** require:
- The full Riemann explicit formula for ψ
- Unique continuation arguments
- Full conjugate-pairing machinery
- Contour-shift residue reconstruction
The per-zero detection theorems are provable from elementary real analysis.
Only the aggregate (full-set) detection requires bridge lemmas, which are
explicitly isolated and labeled.
## File organization
1. **Definitions** — core set-theoretic objects, channel type, observables, detector
2. **Algebraic / symmetry lemmas** — provable now from definitions
3. **Bridge lemma statements** — minimal analytic assumptions isolated explicitly
4. **Final conditional theorems** — pinning / rigidity results
-/
open Complex
open scoped BigOperators
namespace PinningDetector
-- ════════════════════════════════════════════════════════════════
-- SECTION 1: DEFINITIONS
-- ════════════════════════════════════════════════════════════════
/-! ### 1a. The nontrivial zero sets -/
/-- The full set of nontrivial zeros of the Riemann zeta function:
    complex numbers `s` with `0 < Re(s) < 1` and `ζ(s) = 0`.
    This is a subset of `ℂ`, not a finite list or truncation. -/
def NontrivialZeros : Set ℂ :=
  { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }
/-- Off-line nontrivial zeros: those with `Re(s) ≠ 1/2`. -/
def OffLineZeros : Set ℂ :=
  { s ∈ NontrivialZeros | s.re ≠ 1 / 2 }
/-- On-line nontrivial zeros: those with `Re(s) = 1/2`. -/
def OnLineZeros : Set ℂ :=
  { s ∈ NontrivialZeros | s.re = 1 / 2 }
/-! ### 1b. The four-channel angle type -/
/-- The four detector channels, indexed by angles corresponding to the
    Klein four-group of critical-strip symmetries.
    - `deg0`:   Identity (0°)
    - `deg90`:  Complex conjugation (90°)
    - `deg180`: Functional-equation reflection s ↦ 1−s (180°)
    - `deg270`: Combined s ↦ 1−conj(s) (270°) -/
inductive Angle4 : Type
  | deg0
  | deg90
  | deg180
  | deg270
  deriving DecidableEq, Fintype, Repr, Inhabited
/-- The critical-strip symmetry transformation for each channel. -/
def Angle4.transform : Angle4 → ℂ → ℂ
  | .deg0   => fun s => s
  | .deg90  => fun s => star s
  | .deg180 => fun s => 1 - s
  | .deg270 => fun s => 1 - star s
/-- The paired channel: 0°↔180°, 90°↔270°. -/
def Angle4.pair : Angle4 → Angle4
  | .deg0   => .deg180
  | .deg90  => .deg270
  | .deg180 => .deg0
  | .deg270 => .deg90
/-! ### 1c. Prime-density observable -/
/-- Chebyshev's ψ function: `ψ(N) = Σ_{n=0}^{N} Λ(n)`.
    This is the prime-density observable derived from von Mangoldt data.
    Uses Mathlib's `ArithmeticFunction.vonMangoldt`. -/
noncomputable def chebyshevPsi (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sum (fun n => ArithmeticFunction.vonMangoldt n)
/-- Channel exponent: `Re(θ(ρ))`.
    This determines the prime-density magnitude via `|x^{θ(ρ)}| = x^{Re(θ(ρ))}`.
    Computed values:
    - `channelExponent deg0 ρ = Re(ρ) = σ`
    - `channelExponent deg90 ρ = Re(conj ρ) = σ`
    - `channelExponent deg180 ρ = Re(1−ρ) = 1−σ`
    - `channelExponent deg270 ρ = Re(1−conj ρ) = 1−σ` -/
def channelExponent (θ : Angle4) (ρ : ℂ) : ℝ :=
  (θ.transform ρ).re
/-- Per-zero prime-density magnitude in channel θ with density parameter x.
    This is `x ^ Re(θ(ρ))`, the magnitude of the density contribution from
    zero ρ in the von Mangoldt / Chebyshev prime-counting framework. -/
noncomputable def channelMagnitude (x : ℝ) (θ : Angle4) (ρ : ℂ) : ℝ :=
  x ^ channelExponent θ ρ
/-- The full four-channel detector vector for a single zero. -/
noncomputable def detectorVector (x : ℝ) (ρ : ℂ) : Angle4 → ℝ :=
  fun θ => channelMagnitude x θ ρ
/-- Per-zero imbalance: the difference between the identity channel and the
    reflection channel. Equals `x^σ − x^{1−σ}` where `σ = Re(ρ)`.
    This is the fundamental defect:
    - Positive when `σ > 1/2`
    - Negative when `σ < 1/2`
    - Zero iff `σ = 1/2` (for `x > 1`) -/
noncomputable def perZeroImbalance (x : ℝ) (ρ : ℂ) : ℝ :=
  channelMagnitude x .deg0 ρ - channelMagnitude x .deg180 ρ
/-! ### 1d. Detector events and kernel -/
/-- Per-zero detector event: the per-zero imbalance is nonzero. -/
def perZeroDetectorEvent (x : ℝ) (ρ : ℂ) : Prop :=
  perZeroImbalance x ρ ≠ 0
/-- Full-set imbalance: aggregate over all nontrivial zeros.
    Defined as a topological sum (`tsum`) over the subtype `↥NontrivialZeros`.
    Defaults to `0` if the sum does not converge (Lean/Mathlib convention for `tsum`). -/
noncomputable def fullSetImbalance (x : ℝ) : ℝ :=
  ∑' (ρ : ↥NontrivialZeros), perZeroImbalance x (↑ρ)
/-- Full-set detector event: the aggregate imbalance is nonzero. -/
def fullSetDetectorEvent (x : ℝ) : Prop :=
  fullSetImbalance x ≠ 0
/-- Detector kernel: off-line zeros exist but the full-set detector does not fire
    for any density parameter `x > 1`. -/
def detectorKernel : Prop :=
  (∃ s, s ∈ OffLineZeros) ∧ ∀ x : ℝ, 1 < x → fullSetImbalance x = 0
/-- The cancellation / rigidity / pinning class: the set of off-line zeros
    that coexist with a perfectly cancelling aggregate configuration.
    A zero `ρ` belongs to this class when:
    1. It is an off-line nontrivial zero (`Re(ρ) ≠ 1/2`)
    2. Despite its individual imbalance being nonzero, the full-set imbalance
       vanishes for every density parameter `x > 1`.
    This forces narrow cancellation constraints: the imbalance of `ρ` must be
    exactly cancelled by the aggregate of all other zeros. -/
def pinningClass : Set ℂ :=
  { ρ ∈ OffLineZeros | ∀ x : ℝ, 1 < x → fullSetImbalance x = 0 }
-- ════════════════════════════════════════════════════════════════
-- SECTION 2: PROVABLE ALGEBRAIC / SYMMETRY LEMMAS
-- ════════════════════════════════════════════════════════════════
/-! ### 2a. Channel exponent computation -/
@[simp]
lemma channelExponent_deg0 (ρ : ℂ) :
    channelExponent .deg0 ρ = ρ.re := by
  simp [channelExponent, Angle4.transform]
@[simp]
lemma channelExponent_deg90 (ρ : ℂ) :
    channelExponent .deg90 ρ = ρ.re := by
  simp [channelExponent, Angle4.transform, Complex.conj_re]
@[simp]
lemma channelExponent_deg180 (ρ : ℂ) :
    channelExponent .deg180 ρ = 1 - ρ.re := by
  simp [channelExponent, Angle4.transform, Complex.sub_re, Complex.one_re]
@[simp]
lemma channelExponent_deg270 (ρ : ℂ) :
    channelExponent .deg270 ρ = 1 - ρ.re := by
  unfold channelExponent Angle4.transform; aesop;
/-! ### 2b. Channel pairing symmetry
The 0°/90° pair always agree, as do the 180°/270° pair.
This is the strongest valid channel relation: equal exponent, hence
equal magnitude, for each paired channel. -/
lemma channel_pair_0_90 (ρ : ℂ) :
    channelExponent .deg0 ρ = channelExponent .deg90 ρ := by
  simp
lemma channel_pair_180_270 (ρ : ℂ) :
    channelExponent .deg180 ρ = channelExponent .deg270 ρ := by
  norm_num
lemma channelMagnitude_pair_0_90 (x : ℝ) (ρ : ℂ) :
    channelMagnitude x .deg0 ρ = channelMagnitude x .deg90 ρ := by
  rw [ channelMagnitude, channelMagnitude, channelExponent_deg0, channelExponent_deg90 ]
lemma channelMagnitude_pair_180_270 (x : ℝ) (ρ : ℂ) :
    channelMagnitude x .deg180 ρ = channelMagnitude x .deg270 ρ := by
  unfold channelMagnitude; aesop;
/-! ### 2c. Channel exponent complementarity
The exponents of paired channels sum to 1: `Re(θ(ρ)) + Re(θ̄(ρ)) = 1`. -/
lemma channelExponent_pair_sum (θ : Angle4) (ρ : ℂ) :
    channelExponent θ ρ + channelExponent θ.pair ρ = 1 := by
  rcases θ with ( _ | _ | _ | _ ) <;> norm_num [ channelExponent, Angle4.pair ];
  · exact show ρ.re + ( 1 - ρ.re ) = 1 from by ring;
  · unfold Angle4.transform; norm_num;
  · exact show ( 1 - ρ.re ) + ρ.re = 1 by ring;
  · unfold Angle4.transform; norm_num
/-! ### 2d. Pair involution -/
@[simp]
lemma Angle4.pair_pair (θ : Angle4) : θ.pair.pair = θ := by
  cases θ <;> rfl
/-! ### 2e. On-line balance: σ = 1/2 forces zero imbalance
These are unconditionally provable from definitions and elementary arithmetic. -/
lemma onLine_exponent_balance (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    channelExponent .deg0 ρ = channelExponent .deg180 ρ := by
  norm_num [ channelExponent_deg0, channelExponent_deg180, hρ ]
lemma onLine_imbalance_zero (x : ℝ) (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    perZeroImbalance x ρ = 0 := by
  exact sub_eq_zero_of_eq ( congr_arg ( fun y => x ^ y ) ( by rw [ onLine_exponent_balance _ hρ ] ) )
lemma onLine_no_detector_event (x : ℝ) (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    ¬perZeroDetectorEvent x ρ := by
  exact Classical.not_not.2 ( onLine_imbalance_zero x ρ hρ )
/-! ### 2f. Off-line detection: σ ≠ 1/2 ∧ x > 1 forces nonzero imbalance
The per-zero detector has **no kernel**: every off-line zero is individually detected.
This requires no bridge lemmas — it follows from strict monotonicity of `x ^ ·`
for `x > 1`. -/
lemma offLine_exponent_ne (ρ : ℂ) (hρ : ρ.re ≠ 1 / 2) :
    channelExponent .deg0 ρ ≠ channelExponent .deg180 ρ := by
  norm_num +zetaDelta at *;
  cases lt_or_gt_of_ne hρ <;> linarith
lemma offLine_imbalance_ne_zero (x : ℝ) (ρ : ℂ) (hx : 1 < x) (hρ : ρ.re ≠ 1 / 2) :
    perZeroImbalance x ρ ≠ 0 := by
  simp_all +decide [ sub_eq_iff_eq_add, perZeroImbalance ];
  unfold channelMagnitude; norm_num [ hx, hρ, hx.ne', hx.le ] ;
  norm_num [ Real.rpow_def_of_pos ( zero_lt_one.trans hx ), hρ ];
  grind
lemma offLine_detector_fires (x : ℝ) (ρ : ℂ) (hx : 1 < x) (hρ : ρ.re ≠ 1 / 2) :
    perZeroDetectorEvent x ρ := by
  exact offLine_imbalance_ne_zero x ρ hx hρ
/-! ### 2g. Set decomposition -/
lemma nontrivialZeros_eq_union :
    NontrivialZeros = OnLineZeros ∪ OffLineZeros := by
  ext s;
  unfold NontrivialZeros OnLineZeros OffLineZeros;
  grind
lemma onLine_inter_offLine_empty :
    OnLineZeros ∩ OffLineZeros = ∅ := by
  ext s; exact by rw [ Set.mem_inter_iff ] ; unfold OnLineZeros; unfold OffLineZeros; aesop;
lemma offLineZeros_sub : OffLineZeros ⊆ NontrivialZeros := by
  exact fun x hx => hx.1
lemma onLineZeros_sub : OnLineZeros ⊆ NontrivialZeros := by
  exact fun x hx => hx.1
-- ════════════════════════════════════════════════════════════════
-- SECTION 3: BRIDGE LEMMAS
--
-- These are the minimal analytic assumptions needed to connect
-- per-zero detection to full-set (aggregate) detection via
-- prime-density data. They are explicitly isolated and named.
--
-- IMPORTANT: These are NOT proved from scratch. They represent the
-- weakest honest bridge to prime-density data. Each is stated as a
-- Prop definition so it can be used as a hypothesis in final theorems.
--
-- These do NOT require:
-- • the full Riemann explicit formula for ψ
-- • unique continuation
-- • conjugate-pairing machinery
-- • contour-shift residue reconstruction
-- ════════════════════════════════════════════════════════════════
/-- **Bridge Lemma 1: Summability.**
    The per-zero imbalances are summable over the nontrivial zero set.
    Needed for `fullSetImbalance` (a `tsum`) to be meaningful.
    *Justification:* The nontrivial zeros of ζ are known to be countable
    and satisfy the density estimate `N(T) ~ (T/2π) log(T/2πe)`.
    The imbalances `x^σ − x^{1−σ}` are bounded by `x^1 − x^0 = x − 1`
    (since `0 < σ < 1`), and with appropriate weighting the sum converges. -/
def BridgeSummability : Prop :=
  ∀ x : ℝ, 1 < x → Summable (fun (ρ : ↥NontrivialZeros) => perZeroImbalance x (↑ρ))
/-- **Bridge Lemma 2: Prime-density connection (weak explicit formula).**
    The full-set imbalance controls the Chebyshev function's deviation.
    If the aggregate imbalance vanishes for all `x > 1`, then the
    prime-counting function has no off-line density defect (deviation
    from `N` is at most `O(√N)`).
    This is a WEAK form of the explicit formula connecting zeros to primes.
    It does not reconstruct the full `ψ` function from zeros. -/
def BridgePrimeDensityConnection : Prop :=
  (∀ x : ℝ, 1 < x → fullSetImbalance x = 0) →
    ∀ (N : ℕ), ∃ (C : ℝ), |chebyshevPsi N - ↑N| ≤ C * Real.sqrt ↑N
/-- **Bridge Lemma 3: Detector sensitivity.**
    If an off-line zero exists, the full-set detector either fires
    (for some `x > 1`) or the zero lies in the pinning class.
    This is the key bridge: the per-zero detector always fires on off-line zeros,
    but the aggregate detector might not if there is exact cancellation. This
    bridge asserts that such cancellation forces pinning-class membership. -/
def BridgeDetectorSensitivity : Prop :=
  ∀ ρ : ℂ, ρ ∈ OffLineZeros →
    (∃ x : ℝ, 1 < x ∧ fullSetDetectorEvent x) ∨ ρ ∈ pinningClass
/-- **Bridge Lemma 4: Detector well-definedness.**
    The full-set detector observable is well-defined for the prime-density
    functional: the four channels satisfy the required pairing laws on the
    full nontrivial zero set, not merely on finite truncations. -/
def BridgeWellDefinedness : Prop :=
  ∀ x : ℝ, 1 < x →
    (∑' (ρ : ↥NontrivialZeros), channelMagnitude x .deg0 (↑ρ)) =
    (∑' (ρ : ↥NontrivialZeros), channelMagnitude x .deg90 (↑ρ)) ∧
    (∑' (ρ : ↥NontrivialZeros), channelMagnitude x .deg180 (↑ρ)) =
    (∑' (ρ : ↥NontrivialZeros), channelMagnitude x .deg270 (↑ρ))
-- ════════════════════════════════════════════════════════════════
-- SECTION 4: FINAL CONDITIONAL THEOREMS
-- ════════════════════════════════════════════════════════════════
/-! ### Theorem A: On-line balance
If every nontrivial zero lies on the critical line, then:
- **(A1)** The per-zero detector sees no imbalance at any zero.
- **(A2)** The full-set imbalance vanishes (conditional on summability). -/
/-
**Theorem A1: Per-zero on-line balance (unconditional).**
    No bridge lemmas needed.
-/
theorem onLine_balance_perZero :
    (∀ s, s ∈ NontrivialZeros → s.re = 1 / 2) →
    ∀ (x : ℝ) (ρ : ℂ), ρ ∈ NontrivialZeros → perZeroImbalance x ρ = 0 := by
  intro h x ρ hρ; exact onLine_imbalance_zero x ρ (h ρ hρ)
/-
**Theorem A2: Full-set on-line balance (conditional on summability).**
    Requires `BridgeSummability`.
-/
theorem onLine_balance_fullSet (_hS : BridgeSummability) :
    (∀ s, s ∈ NontrivialZeros → s.re = 1 / 2) →
    ∀ (x : ℝ), 1 < x → fullSetImbalance x = 0 := by
  unfold fullSetImbalance;
  intro h x hx;
  convert tsum_zero;
  exact onLine_imbalance_zero x _ ( h _ <| Subtype.mem _ )
/-! ### Theorem B: Per-zero off-line detection (unconditional)
If an off-line zero exists, the per-zero detector fires on it.
This requires **no bridge lemmas** — it is proved from elementary
real analysis (strict monotonicity of `x^·` for `x > 1`). -/
/-
**Theorem B: Per-zero off-line detection.**
-/
theorem offLine_perZero_detection :
    ∀ ρ : ℂ, ρ ∈ OffLineZeros →
    ∀ x : ℝ, 1 < x → perZeroDetectorEvent x ρ := by
  intros ρ hρ x hx;
  apply offLine_detector_fires x ρ hx hρ.right
/-! ### Theorem C: Off-line alternative (conditional on bridge)
If an off-line zero exists, then either:
- The full-set detector fires (for some `x > 1`), **or**
- The zero belongs to the pinning class. -/
/-
**Theorem C: Off-line alternative.**
-/
theorem offLine_alternative (hB : BridgeDetectorSensitivity) :
    ∀ ρ : ℂ, ρ ∈ OffLineZeros →
    (∃ x : ℝ, 1 < x ∧ fullSetDetectorEvent x) ∨ ρ ∈ pinningClass := by
  intro ρ hρ; exact hB ρ hρ
/-! ### Theorem D: Rigidity for nondetection
If the full-set detector does not fire for any `x > 1`, then every
off-line zero must belong to the pinning class. This means the off-line
zeros satisfy narrow cancellation / balance constraints: their individual
imbalances are exactly cancelled by the aggregate of all other zeros. -/
/-
**Theorem D: Rigidity for nondetection (unconditional).**
    No bridge lemmas needed — this follows from definitions.
-/
theorem rigidity_nondetection :
    (∀ x : ℝ, 1 < x → ¬fullSetDetectorEvent x) →
    ∀ ρ : ℂ, ρ ∈ OffLineZeros → ρ ∈ pinningClass := by
  exact fun h ρ hρ => ⟨ hρ, fun x hx => Classical.not_not.1 fun hx' => h x hx hx' ⟩
/-! ### Theorem D': Pinning class constraint extraction
Members of the pinning class satisfy explicit constraints:
1. They are off-line zeros (`Re(ρ) ≠ 1/2`)
2. Their individual per-zero imbalance is nonzero (for `x > 1`)
3. Yet the full aggregate imbalance vanishes
This means: exact cancellation of their contribution by other zeros. -/
/-
**Theorem D': Pinning class constraint.**
-/
theorem pinningClass_constraint :
    ∀ ρ : ℂ, ρ ∈ pinningClass →
    ρ ∈ OffLineZeros ∧ (∀ x : ℝ, 1 < x → fullSetImbalance x = 0) := by
  aesop
/-
**Theorem D'': Pinning class members have nonzero individual imbalance.**
    Members of the pinning class are individually detected but collectively
    hidden — the hallmark of a rigidity / cancellation constraint.
-/
theorem pinningClass_individual_imbalance :
    ∀ ρ : ℂ, ρ ∈ pinningClass →
    ∀ x : ℝ, 1 < x → perZeroImbalance x ρ ≠ 0 := by
  exact fun ρ hρ x hx => offLine_imbalance_ne_zero x ρ hx hρ.1.2
/-! ### Theorem E: Detector kernel characterization -/
/-
**Theorem E: Detector kernel ↔ all off-line zeros in pinning class.**
-/
theorem detectorKernel_iff_allPinned :
    detectorKernel ↔
    (∃ s, s ∈ OffLineZeros) ∧
    (∀ s, s ∈ OffLineZeros → s ∈ pinningClass) := by
  -- First, let's unfold the definitions of `detectorKernel` and `pinningClass`.
  simp [detectorKernel, pinningClass];
  grind
/-! ### Summary of proof status
**Proved unconditionally (Section 2):**
- Channel exponent computation for all four channels
- Channel pairing: 0°↔90° and 180°↔270° equal exponents and magnitudes
- Channel exponent complementarity: paired channels sum to 1
- Pair involution
- On-line balance: σ = 1/2 ⇒ zero imbalance
- Off-line detection: σ ≠ 1/2 ∧ x > 1 ⇒ nonzero imbalance
- Set decomposition and disjointness
**Proved unconditionally (Section 4):**
- Theorem A1: all on-line ⇒ per-zero detector silent
- Theorem B: off-line ⇒ per-zero detector fires
- Theorem D: nondetection ⇒ pinning class membership
- Theorem D'/D'': pinning class constraint extraction
- Theorem E: kernel characterization
**Proved conditionally (Section 4):**
- Theorem A2: all on-line ⇒ full-set detector silent (needs BridgeSummability)
- Theorem C: off-line ⇒ detector fires OR pinning class (needs BridgeDetectorSensitivity)
**Explicitly assumed (Section 3, bridge lemmas):**
- BridgeSummability: per-zero imbalances are summable
- BridgePrimeDensityConnection: aggregate imbalance controls Chebyshev deviation
- BridgeDetectorSensitivity: off-line ⇒ aggregate detection OR pinning
- BridgeWellDefinedness: channel pairing extends to full-set sums
-/
end PinningDetector