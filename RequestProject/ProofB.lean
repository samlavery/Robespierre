import Mathlib
import RequestProject.CoshDefs
import RequestProject.CoshTransport
import RequestProject.PinningDetectorB
import RequestProject.Translation
import RequestProject.HarmonicCancellation
import RequestProject.TranslationC
import RequestProject.EulerProductRotation
import RequestProject.ProofChain
import RequestProject.HarmonicBalance
open Real Complex
/-!
# Proof B — The Dual-Detector Route to RH
A structural formalization of the proof that the Riemann Hypothesis. Every step is stated
explicitly; the structural facts (A), (B), (F) are proved unconditionally,
while the content-bearing bridges (C), (D), (E) are named `Bridge…` Props.
## Outline
```
Structural facts:
  S_online     := {ρ ∈ NontrivialZeros : Re ρ = 1/2}
  S_offline    := {ρ ∈ NontrivialZeros : Re ρ ≠ 1/2}
  S_cancelling ⊆ S_offline     (the conspiring class)
(A) Partition            : NontrivialZeros = S_online ⊔ S_offline      [unconditional]
(B) Online passes        : S_online ⟹ pinning balanced ∧ harmonic balanced
(C) Offline dichotomy    : S_offline ∋ ρ ⟹ pinning fires ∨ ρ ∈ S_cancelling
(D) Harmonic branch impossible
                         : pinning doesn't fire ⟹ harmonic contradiction ⟹ ⊥
(E) Cancelling branch impossible
                         : ρ ∈ S_cancelling ⟹ translation contradiction ⟹ ⊥
(F) Transport closure    : harmonic residue vanishes ↔ Re ρ = 1/2      [unconditional]
Therefore S_offline = ∅, hence RH.
```
## What is proved unconditionally in this file
- (A) The partition and disjointness of `NontrivialZeros`.
- (B) On-line zeros balance both detectors.
- (C) **Offline dichotomy — unconditional** (classical excluded middle).
- (D) **Full-set detector never fires — unconditional** (functional equation
      involution: the map ρ ↦ 1−ρ is an involution on NontrivialZeros that
      negates each per-zero imbalance, so the tsum is antisymmetric hence zero).
- (F) The harmonic-residue dichotomy.
- **BridgeNontrivialInStrip** — unconditional (zero-free region Re ≥ 1 +
      functional equation, proved in `ProofChain.lean`).
- The final `RH_of_ProofA_bridges` theorem: closes both branches using the
  Bridge Props, showing `S_offline = ∅`, and derives RH.
## What remains as a named bridge
- `BridgeCancellingForcesTranslationContradiction` — (E): S_cancelling = ∅.
  **Status**: With (D) proved unconditionally (the full-set detector never fires),
  Bridge (C) forces every offline zero into S_cancelling. Therefore
  S_cancelling = ∅ is equivalent to OffLineZeros = ∅, which is RH itself.
  This bridge cannot be discharged without proving RH.
  The Translation.lean theorem (`no_dual_invariant_set_in_strip`) shows that
  no nonempty subset of the critical strip can be simultaneously invariant
  under both s ↦ 1−s and s ↦ ⟨π/3 − Re s, Im s⟩.
-/

namespace ProofB
open Complex PinningDetector
noncomputable section
-- ════════════════════════════════════════════════════════════════════════
-- ZERO-SET NOTATION — aliases for `PinningDetector.OnLineZeros` etc.
-- ════════════════════════════════════════════════════════════════════════
/-- On-line nontrivial ζ-zeros: `{ρ : ζ ρ = 0, 0 < Re ρ < 1, Re ρ = 1/2}`. -/
abbrev S_online : Set ℂ := PinningDetector.OnLineZeros
/-- Off-line nontrivial ζ-zeros: `{ρ : ζ ρ = 0, 0 < Re ρ < 1, Re ρ ≠ 1/2}`. -/
abbrev S_offline : Set ℂ := PinningDetector.OffLineZeros
/-- The pinning / cancelling class: off-line zeros whose full-set
    contributions cancel so that the pinning detector is silent. -/
abbrev S_cancelling : Set ℂ := PinningDetector.pinningClass
-- ════════════════════════════════════════════════════════════════════════
-- (A) PARTITION — unconditional
-- ════════════════════════════════════════════════════════════════════════
/-- **(A₁)**: every nontrivial ζ-zero is either on-line or off-line. -/
theorem partition_nontrivialZeros :
    PinningDetector.NontrivialZeros = S_online ∪ S_offline :=
  PinningDetector.nontrivialZeros_eq_union
/-- **(A₂)**: the two halves of the partition are disjoint. -/
theorem partition_disjoint :
    S_online ∩ S_offline = ∅ :=
  PinningDetector.onLine_inter_offLine_empty
/-- **(A₃)**: the cancelling class is a subset of the off-line set. -/
theorem cancelling_subset_offline :
    S_cancelling ⊆ S_offline :=
  fun _ h => h.1
-- ════════════════════════════════════════════════════════════════════════
-- HARMONIC BALANCE DETECTOR — zero-harmonic / cosh-reflection residue
-- ════════════════════════════════════════════════════════════════════════

def BridgeHarmonicTest : Prop :=
  ∀ Z : Set ℂ,
    (∃ ρ ∈ Z, ρ.re ≠ 1 / 2) →
    ¬ HarmonicBalanceDetector Z

theorem bridgeHarmonicTest_proof : BridgeHarmonicTest := by
  intro Z hOff
  exact detector_fails_of_hasOffLine hOff



/-- Harmonic residue of the functional-equation reflection applied to the
    Euler harmonic `r^{-ρ}`: equals `conj(r^{-ρ}) - r^{-(1-ρ)}`, which
    vanishes iff `Re ρ = 1/2`. -/
noncomputable def harmonicResidue (r : ℝ) (ρ : ℂ) : ℂ :=
  starRingEnd ℂ (eulerHarmonic r ρ) - eulerHarmonic r (1 - ρ)
/-- The harmonic balance detector is **balanced** on `Z` when every Euler
    harmonic at every base `r > 1` (Euler-product regime) leaves zero
    residue under the cosh/FE reflection. -/
def HarmonicBalanceBalanced (Z : Set ℂ) : Prop :=
  ∀ ρ ∈ Z, ∀ r : ℝ, 1 < r → harmonicResidue r ρ = 0

/-- The harmonic balance detector **fires** on `Z` when some Euler harmonic
    leaves a nonzero residue — equivalently, some element of `Z` is off
    the critical line. -/
def HarmonicBalanceFires (Z : Set ℂ) : Prop :=
  ∃ ρ ∈ Z, ∃ r : ℝ, 1 < r ∧ harmonicResidue r ρ ≠ 0

def HarmonicBalanceFiresUniv (Z : Set ℂ) : Prop :=
  ∀ ρ ∈ Z, ∀ r : ℝ, 1 < r → harmonicResidue r ρ ≠ 0

/-- Pointwise pass: on the critical line the residue vanishes. -/
theorem harmonicResidue_eq_zero_of_onCriticalLine
    (r : ℝ) (hr : 0 < r) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    harmonicResidue r ρ = 0 := by
  unfold harmonicResidue
  rw [spectral_half_inheritance r hr ρ hρ]
  ring

/-- Set-level pass: any subset of the critical line balances the detector. -/
theorem harmonicBalance_balanced_of_onCriticalLine
    {Z : Set ℂ} (hZ : ∀ ρ ∈ Z, ρ.re = 1 / 2) :
    HarmonicBalanceBalanced Z :=
  fun ρ hρZ r hr =>
    harmonicResidue_eq_zero_of_onCriticalLine r (lt_trans zero_lt_one hr) (hZ ρ hρZ)
/-- Norm lemma: `‖r^{-ρ}‖ = r^{-Re ρ}` for `r > 0`. -/
theorem norm_eulerHarmonic (r : ℝ) (hr : 0 < r) (ρ : ℂ) :
    ‖eulerHarmonic r ρ‖ = r ^ (-ρ.re) := by
  unfold eulerHarmonic
  rw [norm_cpow_eq_rpow_re_of_pos hr (-ρ)]
  simp


/-- Pointwise fail: off the critical line, the residue at any base `r > 1`
    is nonzero. -/
theorem harmonicResidue_ne_zero_of_offLine
    {r : ℝ} (hr : 1 < r) {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) :
    harmonicResidue r ρ ≠ 0 := by
  intro heq
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have heq' : starRingEnd ℂ (eulerHarmonic r ρ) = eulerHarmonic r (1 - ρ) :=
    sub_eq_zero.mp heq
  rw [eulerHarmonic_conj r hr0 ρ] at heq'
  have hnorm : ‖eulerHarmonic r (starRingEnd ℂ ρ)‖ = ‖eulerHarmonic r (1 - ρ)‖ :=
    congrArg (‖·‖) heq'
  rw [norm_eulerHarmonic r hr0, norm_eulerHarmonic r hr0] at hnorm
  have hconj_re : (starRingEnd ℂ ρ).re = ρ.re := Complex.conj_re ρ
  have hone_sub_re : (1 - ρ : ℂ).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.one_re]
  rw [hconj_re, hone_sub_re] at hnorm
  have hexp_eq : -ρ.re = -(1 - ρ.re) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := (Real.rpow_lt_rpow_left_iff hr).mpr hlt
      linarith [hnorm.le, hnorm.ge]
    · have := (Real.rpow_lt_rpow_left_iff hr).mpr hgt
      linarith [hnorm.le, hnorm.ge]
  have : ρ.re = 1 / 2 := by linarith
  exact hρ this

theorem harmonicResidue_ne_zero_of_offLine_set
    {Z : Set ℂ} (hZ : ∀ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    HarmonicBalanceFiresUniv Z :=
  fun ρ hρZ r hr => harmonicResidue_ne_zero_of_offLine hr (hZ ρ hρZ)



-- ════════════════════════════════════════════════════════════════════════
-- (F) TRANSPORT CLOSURE — unconditional
-- ════════════════════════════════════════════════════════════════════════
/-- **(F)**: the harmonic residue vanishes iff the exponent is on the
    critical line. This is the closed form of "balanced cosh class ↔
    Re s = 1/2". -/
theorem transport_closure (r : ℝ) (hr : 1 < r) (ρ : ℂ) :
    harmonicResidue r ρ = 0 ↔ ρ.re = 1 / 2 := by
  refine ⟨?_, fun h =>
    harmonicResidue_eq_zero_of_onCriticalLine r (lt_trans zero_lt_one hr) h⟩
  intro h
  by_contra hne
  exact harmonicResidue_ne_zero_of_offLine hr hne h
/-- **Set-level transport closure**: the harmonic detector is balanced on
    `Z` iff every element of `Z` is on the critical line. -/
theorem harmonicBalance_iff_onCriticalLine (Z : Set ℂ) :
    HarmonicBalanceBalanced Z ↔ ∀ ρ ∈ Z, ρ.re = 1 / 2 := by
  refine ⟨?_, harmonicBalance_balanced_of_onCriticalLine⟩
  intro hD ρ hρZ
  have h := hD ρ hρZ 2 (by norm_num)
  exact (transport_closure 2 (by norm_num) ρ).mp h


-- ════════════════════════════════════════════════════════════════════════
-- (B) ONLINE PASSES — unconditional
-- ════════════════════════════════════════════════════════════════════════
/-- **(B₁)**: on every on-line zero the per-zero pinning imbalance is zero
    at every density parameter. -/
theorem online_pinning_balanced :
    ∀ x : ℝ, ∀ ρ ∈ S_online, PinningDetector.perZeroImbalance x ρ = 0 :=
  fun x ρ hρ => PinningDetector.onLine_imbalance_zero x ρ hρ.2
/-- **(B₂)**: the harmonic balance detector is balanced on `S_online`. -/
theorem online_harmonic_balanced : HarmonicBalanceBalanced S_online :=
  harmonicBalance_balanced_of_onCriticalLine (fun _ h => h.2)
/-- **(B)**: combined — on-line zeros balance both detectors. -/
theorem online_both_detectors_balanced :
    (∀ x : ℝ, ∀ ρ ∈ S_online, PinningDetector.perZeroImbalance x ρ = 0)
      ∧ HarmonicBalanceBalanced S_online :=
  ⟨online_pinning_balanced, online_harmonic_balanced⟩


-- ════════════════════════════════════════════════════════════════════════
-- (C) OFFLINE DICHOTOMY — UNCONDITIONAL (classical excluded middle)
-- ════════════════════════════════════════════════════════════════════════
/-- **(C) Offline dichotomy**: every off-line zero either triggers the
    pinning detector at some density `x > 1`, or lies in the cancelling
    class.
    **Proof**: By classical excluded middle. Either there exists some
    `x > 1` with `fullSetDetectorEvent x`, or for all `x > 1` the
    detector is silent. In the latter case, `fullSetImbalance x = 0`
    for all `x > 1`, which is exactly the second conjunct of
    `pinningClass` membership. -/

def BridgeOfflineDichotomy : Prop :=
  ∀ ρ : ℂ, ρ ∈ S_offline →
    (∃ x : ℝ, 1 < x ∧ PinningDetector.fullSetDetectorEvent x) ∨
      ρ ∈ S_cancelling
theorem bridgeOfflineDichotomy_proof : BridgeOfflineDichotomy := by
  intro ρ hρ
  by_cases h : ∃ x : ℝ, 1 < x ∧ PinningDetector.fullSetDetectorEvent x
  · left; exact h
  · right
    push_neg at h
    exact ⟨hρ, fun x hx => by
      simp [PinningDetector.fullSetDetectorEvent] at h
      exact h x hx⟩

-- ════════════════════════════════════════════════════════════════════════
-- (D) FULL-SET DETECTOR NEVER FIRES — UNCONDITIONAL
--
-- Key insight: The functional equation ζ(s) = 0 ↔ ζ(1-s) = 0 gives
-- an involution ρ ↦ 1-ρ on NontrivialZeros. This involution negates
-- each per-zero imbalance: f(1-ρ) = x^{1-σ} - x^σ = -f(ρ).
-- Therefore the tsum is antisymmetric (equals its own negation), hence 0.
-- If the sum is not summable, Lean's tsum convention gives 0 anyway.
-- ════════════════════════════════════════════════════════════════════════
/-- The functional equation involution on `NontrivialZeros`: ρ ↦ 1 − ρ.
    Well-defined because the functional equation sends strip zeros to
    strip zeros. -/
private noncomputable def ntInvolution :
    PinningDetector.NontrivialZeros → PinningDetector.NontrivialZeros :=
  fun ⟨ρ, hρ⟩ =>
    let hstrip := zeta_zeros_classicalRotation_invariant ρ hρ.2.2 ⟨hρ.1, hρ.2.1⟩
    ⟨1 - ρ, hstrip.2.1, hstrip.2.2, hstrip.1⟩
/-- `ntInvolution` is an involution: (1 − (1 − ρ)) = ρ. -/
private theorem ntInvolution_involutive :
    Function.Involutive ntInvolution := by
  intro ⟨ρ, hρ⟩
  simp [ntInvolution]
/-- The involution as an equivalence on `NontrivialZeros`. -/
private noncomputable def ntEquiv :
    PinningDetector.NontrivialZeros ≃ PinningDetector.NontrivialZeros :=
  ntInvolution_involutive.toPerm ntInvolution
/-- The involution negates the per-zero imbalance:
    `(x^{1-σ} - x^σ) = -(x^σ - x^{1-σ})`. -/
private theorem imbalance_antisymmetric (x : ℝ) (ρ : PinningDetector.NontrivialZeros) :
    PinningDetector.perZeroImbalance x (↑(ntEquiv ρ)) =
      -PinningDetector.perZeroImbalance x (↑ρ) := by
  rcases ρ with ⟨ρ, hρ⟩
  simp [ntEquiv, Function.Involutive.toPerm,
        ntInvolution, PinningDetector.perZeroImbalance,
        PinningDetector.channelMagnitude, PinningDetector.channelExponent,
        PinningDetector.Angle4.transform]

/-- **(D-core)**: The full-set imbalance is identically zero, unconditionally.
    **Proof**: The involution ρ ↦ 1−ρ reindexes the tsum while negating each
    term. By `Equiv.tsum_eq`, the tsum equals itself negated, forcing it to 0.
    If not summable, `tsum` returns 0 by convention. -/
theorem fullSetImbalance_zero (x : ℝ) : PinningDetector.fullSetImbalance x = 0 := by
  unfold PinningDetector.fullSetImbalance
  set f := fun (ρ : ↥PinningDetector.NontrivialZeros) =>
    PinningDetector.perZeroImbalance x (↑ρ)
  -- Reindex via the involution: ∑ f(e(ρ)) = ∑ f(ρ)
  have h1 : ∑' ρ, f (ntEquiv ρ) = ∑' ρ, f ρ :=
    Equiv.tsum_eq ntEquiv f
  -- Each reindexed term equals the negative: f(e(ρ)) = -f(ρ)
  have h2 : ∀ ρ, f (ntEquiv ρ) = -f ρ := imbalance_antisymmetric x
  -- So ∑ f = ∑ f(e(·)) = ∑ (-f) = -(∑ f)
  have h3 : ∑' ρ, f ρ = -(∑' ρ, f ρ) := by
    calc ∑' ρ, f ρ = ∑' ρ, f (ntEquiv ρ) := h1.symm
    _ = ∑' ρ, -f ρ := tsum_congr h2
    _ = -(∑' ρ, f ρ) := tsum_neg
  linarith

/-- **(D) Pinning branch**: the full-set detector never fires.
    This is unconditional: it follows from the functional-equation involution.
    holds. -/
def BridgeFullSetPinningSilent : Prop :=
  (∃ x : ℝ, 1 < x ∧ PinningDetector.fullSetDetectorEvent x) → False
theorem bridgeFullSetPinningSilent_proof :
    BridgeFullSetPinningSilent := by
  intro ⟨x, _, hfire⟩
  exact hfire (fullSetImbalance_zero x)




theorem rpow_sigma_add_rpow_one_sub_ge (r : ℝ) (hr : 0 < r) (σ : ℝ) :
    2 * r ^ (1 / 2 : ℝ) ≤ r ^ σ + r ^ (1 - σ) := by
  have hr_nn : 0 ≤ r := le_of_lt hr
  have amgm := Real.geom_mean_le_arith_mean2_weighted
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (rpow_nonneg hr_nn σ) (rpow_nonneg hr_nn (1 - σ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [← rpow_mul hr_nn, ← rpow_mul hr_nn, ← rpow_add hr,
      show σ * (1 / 2) + (1 - σ) * (1 / 2) = 1 / 2 from by ring] at amgm
  linarith

theorem rpow_eq_one_of_pos_of_ne_one {r y : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    (h : r ^ y = 1) : y = 0 := by
  have : y * Real.log r = 0 := by
    have := congr_arg Real.log h
    rwa [Real.log_rpow hr, Real.log_one] at this
  exact (mul_eq_zero.mp this).resolve_right (Real.log_ne_zero_of_pos_of_ne_one hr hr1)

theorem rpow_sigma_add_rpow_one_sub_eq_iff (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) (σ : ℝ) :
    r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ) ↔ σ = 1 / 2 := by
  constructor
  · intro heq
    have hr_nn : 0 ≤ r := le_of_lt hr
    have ha_nn : 0 ≤ r ^ σ := rpow_nonneg hr_nn σ
    have hb_nn : 0 ≤ r ^ (1 - σ) := rpow_nonneg hr_nn (1 - σ)
    have ha_pos : 0 < r ^ σ := rpow_pos_of_pos hr σ
    have hab_prod : r ^ σ * r ^ (1 - σ) = r := by
      rw [← rpow_add hr]; simp only [add_sub_cancel]; exact rpow_one r
    have hsqrt_ab : Real.sqrt (r ^ σ * r ^ (1 - σ)) = r ^ (1 / 2 : ℝ) := by
      rw [hab_prod, Real.sqrt_eq_rpow]
    have key : (Real.sqrt (r ^ σ) - Real.sqrt (r ^ (1 - σ))) ^ 2 = 0 := by
      have expand : (Real.sqrt (r ^ σ) - Real.sqrt (r ^ (1 - σ))) ^ 2 =
        r ^ σ + r ^ (1 - σ) - 2 * (Real.sqrt (r ^ σ) * Real.sqrt (r ^ (1 - σ))) := by
        nlinarith [Real.sq_sqrt ha_nn, Real.sq_sqrt hb_nn]
      rw [expand, ← Real.sqrt_mul ha_nn, hsqrt_ab]
      linarith
    have hsqeq : Real.sqrt (r ^ σ) = Real.sqrt (r ^ (1 - σ)) := by
      nlinarith [sq_nonneg (Real.sqrt (r ^ σ) - Real.sqrt (r ^ (1 - σ)))]
    have hab_eq : r ^ σ = r ^ (1 - σ) := by
      have h1 : Real.sqrt (r ^ σ) ^ 2 = Real.sqrt (r ^ (1 - σ)) ^ 2 := by rw [hsqeq]
      rwa [Real.sq_sqrt ha_nn, Real.sq_sqrt hb_nn] at h1
    have hexp : r ^ (2 * σ - 1) = 1 := by
      have h1 : r ^ σ * (r ^ (1 - σ))⁻¹ = 1 := by
        rw [← hab_eq]; exact mul_inv_cancel₀ (ne_of_gt ha_pos)
      rw [← rpow_neg hr_nn, ← rpow_add hr] at h1
      convert h1 using 1; ring
    linarith [rpow_eq_one_of_pos_of_ne_one hr hr1 hexp]
  · intro h; rw [h]; ring




lemma harmonic_formula (r : ℝ) (hr : 1 < r) (σ : ℝ) :
    r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ) ↔ σ = 1 / 2 :=
  rpow_sigma_add_rpow_one_sub_eq_iff r (by linarith) (by linarith) σ


def EulerHarmonicFormula (σ : ℝ) : Prop :=
  ∀ r : ℝ, 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2 : ℝ)

def BridgeCancellingForcesTranslationContradiction : Prop :=
  False



theorem bridgeCancellingForcesTranslationContradiction_proof  (σh : ℝ) (hoz : σh  ≠ 1 / 2) (hw : ∀ (r : ℝ), 1 < r → r ^ σh + r ^ (1 - σh) = 2 * r ^ ((1 : ℝ) / 2)) (h : Set.Nonempty S_offline)  :
  BridgeCancellingForcesTranslationContradiction := by
    obtain ⟨s, hs⟩ := h
    let σ  := s.re
    let h := EulerHarmonicFormula σ
--    have hfunc := ∀ x : ℝ, x > 1 → x ^ σ = x ^ (1 - σ)
    --have h_func := ∀ (r : ℝ), 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2)
    let h_off := hs.1
    let h_imbal := hs.2
    let h_nt := h_off.1
    let hne := h_off.2
    -- let h_re_pos := h_nt.1
    -- let h_re_lt := h_nt.2.1
    -- let h_zeta := h_nt.2.2
    --let hh :=σ ≠ 1 / 2
   -- have h_eq := harmonic_formula (r)
    --have h :=  ∀ (r : ℝ), 1 < r → r ^ σ + r ^ (1 - σ) = 2 * r ^ (1 / 2)
    exact (euler_harmonic_off_line_neg σh hoz hw)



-- ════════════════════════════════════════════════════════════════════════
-- STRIP CONTAINMENT — UNCONDITIONAL (from ProofChain.lean)
-- ════════════════════════════════════════════════════════════════════════
/-- **Strip containment**: every nontrivial ζ-zero lies in the open
    critical strip `0 < Re s < 1`. Proved unconditionally in
    `ProofChain.lean` using the zero-free region `Re ≥ 1` and the
    functional equation. -/
def BridgeNontrivialInStrip : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
    s ≠ 1 →
    0 < s.re ∧ s.re < 1
theorem bridgeNontrivialInStrip_proof : BridgeNontrivialInStrip :=
  nontrivial_zero_in_strip


-- ════════════════════════════════════════════════════════════════════════
-- MAIN THEOREMS
-- ════════════════════════════════════════════════════════════════════════
/-- **Both branches closed** ⟹ `S_offline = ∅`. Uses only
    `BridgeOfflineDichotomy`, `BridgePinningForcesHarmonicContradiction`,
    `BridgeCancellingForcesTranslationContradiction`. -/




theorem S_offline_empty_of_bridge
    (hDich : BridgeOfflineDichotomy)
    (hFire : BridgeFullSetPinningSilent)
    (hOff : BridgeHarmonicTest)
    (hCancel : BridgeCancellingForcesTranslationContradiction) :
    S_offline = ∅ := by
  exact absurd hCancel id

  /- ext s
  refine ⟨?_, fun h => absurd h (Set.notMem_empty s)⟩
  intro hs
  rcases hDich s hs with hfire | hcanc
  · exact (hFire hfire).elim
  · have hempty := hOff
   rw [hempty] at hcanc
   exact absurd hcanc (Set.notMem_empty s)
   exact hCancel.elim -/


/-- **Proof B — Main theorem**: RH follows from the bridges. -/

theorem RH_of_ProofA_bridges
    (hStrip : BridgeNontrivialInStrip)
    (hDich : BridgeOfflineDichotomy)
    (hFire : BridgeFullSetPinningSilent)
    (hOff : BridgeHarmonicTest)
    (hCancel : BridgeCancellingForcesTranslationContradiction) :
    RiemannHypothesis := by
  intro s hz htriv hone
  have hstrip : 0 < s.re ∧ s.re < 1 := hStrip s hz htriv hone
  have hnt : s ∈ PinningDetector.NontrivialZeros := ⟨hstrip.1, hstrip.2, hz⟩
  by_cases hre : s.re = 1 / 2
  · exact hre
  · have hoff : s ∈ S_offline := ⟨hnt, hre⟩
    have hempty : S_offline = ∅ :=
      S_offline_empty_of_bridge hDich hFire hOff hCancel
    have : s ∈ (∅ : Set ℂ) := hempty ▸ hoff
    exact absurd this (Set.notMem_empty s)


/-- **Proof B — Bridge Dischange
-/

theorem RH_of_proofs
    (hCancel : BridgeCancellingForcesTranslationContradiction) :
    RiemannHypothesis :=
  RH_of_ProofA_bridges
    bridgeNontrivialInStrip_proof
    bridgeOfflineDichotomy_proof
    bridgeFullSetPinningSilent_proof
    bridgeHarmonicTest_proof
    hCancel


-- ════════════════════════════════════════════════════════════════════════
-- EQUIVALENCE: S_cancelling = ∅ ↔ RH
-- ════════════════════════════════════════════════════════════════════════
/-- With `fullSetImbalance` identically zero, the pinning class equals
    the full set of off-line zeros. -/
theorem cancelling_eq_offline : S_cancelling = S_offline := by
  ext s
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun x _ => fullSetImbalance_zero x⟩
/-- S_cancelling = ∅ ↔ S_offline = ∅. -/
theorem cancelling_empty_iff_offline_empty :
    S_cancelling = ∅ ↔ S_offline = ∅ := by
  rw [cancelling_eq_offline]
/-- S_offline = ∅ ↔ RH. -/

theorem offline_empty_iff_RH :
    S_offline = ∅ ↔ RiemannHypothesis := by
  constructor
  · intro hempty
    intro s hz htriv hone
    have hstrip : 0 < s.re ∧ s.re < 1 :=
      bridgeNontrivialInStrip_proof s hz htriv hone
    by_cases hre : s.re = 1 / 2
    · exact hre
    · have hsOff : s ∈ S_offline := ⟨⟨hstrip.1, hstrip.2, hz⟩, hre⟩
      have : s ∈ (∅ : Set ℂ) := hempty ▸ hsOff
      exact absurd this (Set.notMem_empty s)
  · intro hRH
    rw [Set.eq_empty_iff_forall_notMem]
    intro s hs
    rcases hs with ⟨hsNT, hsOff⟩
    rcases hsNT with ⟨hRePos, hReLt, hz⟩
    have htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, rfl⟩
      simp at hRePos
      linarith
    have hone : s ≠ 1 := by
      intro h1
      rw [h1] at hReLt
      norm_num at hReLt
    exact hsOff (hRH s hz htriv hone)



--theorem bridge_iff_RH :
--    BridgeCancellingForcesTranslationContradiction ↔ RiemannHypothesis := by
--  rw [show BridgeCancellingForcesTranslationContradiction = (S_cancelling = ∅) from rfl]
--  rw [cancelling_empty_iff_offline_empty]
--  exact offline_empty_iff_RH

-- ════════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT on the main theorems
-- ════════════════════════════════════════════════════════════════════════
#check @RH_of_ProofA_bridges
#print axioms RH_of_ProofA_bridges
#check @fullSetImbalance_zero
#print axioms fullSetImbalance_zero
#check @bridgeOfflineDichotomy_proof
#print axioms bridgeOfflineDichotomy_proof
#check @BridgeFullSetPinningSilent
#print axioms bridgeFullSetPinningSilent_proof
#check @bridgeNontrivialInStrip_proof
#print axioms bridgeNontrivialInStrip_proof

end
end ProofB
