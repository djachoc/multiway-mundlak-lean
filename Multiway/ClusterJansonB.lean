/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Multiway.ClusterJanson

/-!
# Theorem 5(b) at arbitrary `ε > 0` via Janson's Theorem 2

This file formalizes Theorem 5(b) of the paper (asymptotic normality under multiway
clustering, unbounded disturbances) and the second sentence of Corollary SM.D.3, for an
arbitrary `ε > 0`. The proof truncates `ν_o` at a level `τ_n`, bounds the tail variance, and
applies Janson (1988), Theorem 2, at the moment index `m := max{3, ⌈2/ε⌉}` to the truncated
array standardized by its own `σ_n`; `ε` enters only through `(n/D_n)^{2/m} ≤ (n/D_n)^ε`.

The truncation level is `τ_n² := ψ_n²(1 + 128n(D_n+1)ψ_n²) + n(D_n+1)ψ_n⁴/√(e_n)` with
`e_n := (n/D_n)^ε·n(D_n+1)³ψ_n⁴`; the first summand gives `Var(S^>_n) ≤ 1/16` at every `n`, the
second gives `Var(S^>_n) ≤ 8√(e_n)`.

## Main results

* `cltcluster_b_general_janson_expect`: Theorem 5(b) on the array, in test-function form.
* `cltcluster_b_general_betaJM_janson_printed`: Theorem 5(b) for `β̂_JM` with random `𝓡_n`.
* `clustershock_b_general_janson_nonneg`: Corollary SM.D.3, second sentence.
-/

namespace Multiway.ClusterJanson

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators MatrixOrder
open Matrix
open Causalean.Mathlib.Probability.SteinMethod
open Multiway.SteinCluster
open Multiway.ClusterShock

/-! ### `δ^{(ε)}_n` and its arithmetic -/

section EpsRate

/-- `δ^{(ε)}_n := (n/D_n)^ε δ_n`. `SteinCluster.steinRate` is the case `ε = 1/3`. -/
noncomputable def epsRate (N Dn : ℕ) (lmin ε : ℝ) : ℝ :=
  ((N : ℝ) / (Dn : ℝ)) ^ ε * accumRate N Dn lmin

theorem epsRate_nonneg (N Dn : ℕ) (lmin ε : ℝ) : 0 ≤ epsRate N Dn lmin ε :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (accumRate_nonneg N Dn)

/-- `SteinCluster.steinRate` is `epsRate` at `ε = 1/3`, definitionally. -/
theorem steinRate_eq_epsRate (N Dn : ℕ) (lmin : ℝ) :
    steinRate N Dn lmin = epsRate N Dn lmin ((1 : ℝ) / 3) := rfl

/-- `δ_n ≤ δ^{(ε)}_n` when `D_n ≤ n`. -/
theorem accumRate_le_epsRate {N Dn : ℕ} (hD1 : 1 ≤ Dn) (hDN : Dn ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (lmin : ℝ) : accumRate N Dn lmin ≤ epsRate N Dn lmin ε := by
  have hDpos : (0 : ℝ) < (Dn : ℝ) := by exact_mod_cast hD1
  have hone : (1 : ℝ) ≤ (N : ℝ) / (Dn : ℝ) := by
    rw [le_div_iff₀ hDpos, one_mul]
    exact_mod_cast hDN
  have hrp : (1 : ℝ) ≤ ((N : ℝ) / (Dn : ℝ)) ^ ε := Real.one_le_rpow hone hε
  unfold epsRate
  nth_rewrite 1 [← one_mul (accumRate N Dn lmin)]
  exact mul_le_mul_of_nonneg_right hrp (accumRate_nonneg N Dn)

/-- The first error scalar at the exponent `ε`: `SteinCluster.firstRate_le` multiplied through
by `(n/D_n)^ε ≥ 0`. -/
theorem epsFirstRate_le {N D : ℕ} (hD1 : 1 ≤ D) {lmin B Cnu ε : ℝ} (hl : 0 < lmin) :
    ((N : ℝ) / (D : ℝ)) ^ ε * ((N : ℝ) * ((D + 1 : ℕ) : ℝ) ^ 3 * (B * Cnu / Real.sqrt lmin) ^ 4)
      ≤ 8 * B ^ 4 * Cnu ^ 4 * epsRate N D lmin ε := by
  have h := firstRate_le (N := N) (D := D) hD1 (lmin := lmin) (B := B) (Cnu := Cnu) hl
  have hr : (0 : ℝ) ≤ ((N : ℝ) / (D : ℝ)) ^ ε := Real.rpow_nonneg (by positivity) _
  calc ((N : ℝ) / (D : ℝ)) ^ ε
        * ((N : ℝ) * ((D + 1 : ℕ) : ℝ) ^ 3 * (B * Cnu / Real.sqrt lmin) ^ 4)
      ≤ ((N : ℝ) / (D : ℝ)) ^ ε * (8 * B ^ 4 * Cnu ^ 4 * accumRate N D lmin) :=
        mul_le_mul_of_nonneg_left h hr
    _ = 8 * B ^ 4 * Cnu ^ 4 * epsRate N D lmin ε := by
        unfold epsRate; ring

end EpsRate

/-! ### The truncation level and its inequalities -/

section TruncArith

/-- **The truncation level at a single `n`.** With `Nr = n`, `Mr = D_n`, `P = D_n + 1`,
`p = ψ_n`, `w = n(D_n+1)³ψ_n⁴`, `e = (n/D_n)^ε w`, `T = τ_n²` and `mr = 2/m` subject to
`mr ≤ 1` and `mr ≤ ε`: the truncation is above the moment scale; the tail variance is at most
`1/16`; the tail variance is at most `8√e`; and Janson's `(1.5)`, squared with `σ_n ≥ 1/2`
absorbed, is at most `2(3√e + 128e)`. -/
theorem truncSq_facts {Nr Mr p ε mr : ℝ} (hN1 : 1 ≤ Nr) (hM1 : 1 ≤ Mr) (hMN : Mr ≤ Nr)
    (hp : 0 < p) (hmr0 : 0 < mr) (hmr1 : mr ≤ 1) (hmrε : mr ≤ ε) :
    p ^ 2 ≤ p ^ 2 * (1 + 128 * Nr * (Mr + 1) * p ^ 2)
        + Nr * (Mr + 1) * p ^ 4
          / Real.sqrt ((Nr / Mr) ^ ε * (Nr * (Mr + 1) ^ 3 * p ^ 4))
      ∧ 8 * Nr * (Mr + 1) * (p ^ 4 / (p ^ 2 * (1 + 128 * Nr * (Mr + 1) * p ^ 2)
          + Nr * (Mr + 1) * p ^ 4
            / Real.sqrt ((Nr / Mr) ^ ε * (Nr * (Mr + 1) ^ 3 * p ^ 4)))) ≤ 1 / 16
      ∧ 8 * Nr * (Mr + 1) * (p ^ 4 / (p ^ 2 * (1 + 128 * Nr * (Mr + 1) * p ^ 2)
          + Nr * (Mr + 1) * p ^ 4
            / Real.sqrt ((Nr / Mr) ^ ε * (Nr * (Mr + 1) ^ 3 * p ^ 4))))
          ≤ 8 * Real.sqrt ((Nr / Mr) ^ ε * (Nr * (Mr + 1) ^ 3 * p ^ 4))
      ∧ ((Nr + 1) / (Mr + 1)) ^ mr * (Mr + 1) ^ 2
            * (p ^ 2 * (1 + 128 * Nr * (Mr + 1) * p ^ 2)
              + Nr * (Mr + 1) * p ^ 4
                / Real.sqrt ((Nr / Mr) ^ ε * (Nr * (Mr + 1) ^ 3 * p ^ 4)))
          ≤ 2 * (3 * Real.sqrt ((Nr / Mr) ^ ε * (Nr * (Mr + 1) ^ 3 * p ^ 4))
              + 128 * ((Nr / Mr) ^ ε * (Nr * (Mr + 1) ^ 3 * p ^ 4))) := by
  have hN0 : (0 : ℝ) < Nr := lt_of_lt_of_le zero_lt_one hN1
  have hM0 : (0 : ℝ) < Mr := lt_of_lt_of_le zero_lt_one hM1
  set P : ℝ := Mr + 1 with hP
  have hP0 : (0 : ℝ) < P := by rw [hP]; linarith
  have hP2 : (2 : ℝ) ≤ P := by rw [hP]; linarith
  set x : ℝ := Nr / Mr with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx, le_div_iff₀ hM0, one_mul]; exact hMN
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  set w : ℝ := Nr * P ^ 3 * p ^ 4 with hw
  have hw0 : (0 : ℝ) < w := by rw [hw]; positivity
  set e : ℝ := x ^ ε * w with he
  have hxe0 : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have he0 : (0 : ℝ) < e := by rw [he]; positivity
  set se : ℝ := Real.sqrt e with hse
  have hse0 : (0 : ℝ) < se := by rw [hse]; exact Real.sqrt_pos.mpr he0
  have hsesq : se ^ 2 = e := by rw [hse]; exact Real.sq_sqrt he0.le
  -- the two summands of `T`
  set T1 : ℝ := p ^ 2 * (1 + 128 * Nr * P * p ^ 2) with hT1
  set T2 : ℝ := Nr * P * p ^ 4 / se with hT2
  have hT10 : (0 : ℝ) < T1 := by rw [hT1]; positivity
  have hT20 : (0 : ℝ) < T2 := by rw [hT2]; positivity
  set T : ℝ := T1 + T2 with hT
  have hT0 : (0 : ℝ) < T := by rw [hT]; linarith
  -- the `x ^ mr` facts used throughout
  have hxmr0 : (0 : ℝ) < x ^ mr := Real.rpow_pos_of_pos hx0 mr
  have hxmr_le_x : x ^ mr ≤ x := by
    calc x ^ mr ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hmr1
      _ = x := Real.rpow_one x
  have hxmr_le_xe : x ^ mr ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_le hx1 hmrε
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `p² ≤ T`
    have h1 : p ^ 2 ≤ T1 := by
      rw [hT1]
      nth_rewrite 1 [← mul_one (p ^ 2)]
      have : (0 : ℝ) ≤ 128 * Nr * P * p ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hT]; linarith
  · -- the tail variance is `≤ 1/16` at every `n`
    have hge : 128 * (Nr * P * p ^ 4) ≤ T := by
      have h1 : 128 * (Nr * P * p ^ 4) ≤ T1 := by rw [hT1]; nlinarith [hp.le, hP0.le, hN0.le]
      rw [hT]; linarith
    have hdiv : p ^ 4 / T ≤ p ^ 4 / (128 * (Nr * P * p ^ 4)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hge
    calc 8 * Nr * P * (p ^ 4 / T)
        ≤ 8 * Nr * P * (p ^ 4 / (128 * (Nr * P * p ^ 4))) := by
          have : (0 : ℝ) ≤ 8 * Nr * P := by positivity
          exact mul_le_mul_of_nonneg_left hdiv this
      _ = 1 / 16 := by field_simp; ring
  · -- the tail variance is `≤ 8√e`
    have hge : Nr * P * p ^ 4 / se ≤ T := by rw [hT]; linarith
    have hdiv : p ^ 4 / T ≤ p ^ 4 / (Nr * P * p ^ 4 / se) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hge
    calc 8 * Nr * P * (p ^ 4 / T)
        ≤ 8 * Nr * P * (p ^ 4 / (Nr * P * p ^ 4 / se)) := by
          have : (0 : ℝ) ≤ 8 * Nr * P := by positivity
          exact mul_le_mul_of_nonneg_left hdiv this
      _ = 8 * se := by field_simp
  · -- Janson's `(1.5)`, squared
    -- step 1: `((Nr+1)/P)^mr ≤ 2 x^mr`
    have hbase : (Nr + 1) / P ≤ 2 * x := by
      have h2x : 2 * x = (2 * Nr) / Mr := by rw [hx]; ring
      rw [h2x, hP, div_le_div_iff₀ (by linarith) hM0]
      nlinarith [mul_nonneg hN0.le hM0.le]
    have hbase0 : (0 : ℝ) ≤ (Nr + 1) / P := by positivity
    have hstep1 : ((Nr + 1) / P) ^ mr ≤ 2 * x ^ mr := by
      have h1 : ((Nr + 1) / P) ^ mr ≤ (2 * x) ^ mr :=
        Real.rpow_le_rpow hbase0 hbase hmr0.le
      have h2 : (2 * x) ^ mr = (2 : ℝ) ^ mr * x ^ mr :=
        Real.mul_rpow (by norm_num) hx0.le
      have h3 : (2 : ℝ) ^ mr ≤ 2 := by
        calc (2 : ℝ) ^ mr ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hmr1
          _ = 2 := Real.rpow_one 2
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right h3 hxmr0.le)
    -- step 2: `x^mr P² T ≤ 3√e + 128e`
    have hA : x ^ mr * P ^ 2 * p ^ 2 ≤ 2 * se := by
      have hA0 : (0 : ℝ) ≤ x ^ mr * P ^ 2 * p ^ 2 := by positivity
      have hsq : (x ^ mr * P ^ 2 * p ^ 2) ^ 2 ≤ 2 * e := by
        have h1 : (x ^ mr * P ^ 2 * p ^ 2) ^ 2 = (x ^ mr) ^ 2 * P ^ 4 * p ^ 4 := by ring
        have h2 : (x ^ mr) ^ 2 * P ^ 4 * p ^ 4 ≤ (x ^ mr * x) * P ^ 4 * p ^ 4 := by
          have : (x ^ mr) ^ 2 ≤ x ^ mr * x := by nlinarith
          nlinarith [pow_nonneg hP0.le 4, pow_nonneg hp.le 4]
        have h3 : (x ^ mr * x) * P ^ 4 * p ^ 4 ≤ x ^ mr * (2 * w) := by
          have hPM : P ≤ 2 * Mr := by rw [hP]; linarith
          have hxP : x * P ^ 4 ≤ 2 * (Nr * P ^ 3) := by
            rw [hx, div_mul_eq_mul_div, div_le_iff₀ hM0]
            have hkey : (0 : ℝ) ≤ Nr * P ^ 3 * (2 * Mr - P) :=
              mul_nonneg (by positivity) (by linarith)
            nlinarith [hkey]
          have hkey : (x * P ^ 4) * p ^ 4 ≤ (2 * (Nr * P ^ 3)) * p ^ 4 :=
            mul_le_mul_of_nonneg_right hxP (by positivity)
          have : (x ^ mr * x) * P ^ 4 * p ^ 4 = x ^ mr * ((x * P ^ 4) * p ^ 4) := by ring
          rw [this]
          have h2w : x ^ mr * ((2 * (Nr * P ^ 3)) * p ^ 4) = x ^ mr * (2 * w) := by
            rw [hw]; ring
          rw [← h2w]
          exact mul_le_mul_of_nonneg_left hkey hxmr0.le
        have h4 : x ^ mr * (2 * w) ≤ 2 * e := by
          rw [he]
          have : x ^ mr * (2 * w) = 2 * (x ^ mr * w) := by ring
          rw [this]
          have := mul_le_mul_of_nonneg_right hxmr_le_xe hw0.le
          linarith
        linarith [h1 ▸ h2, h2, h3, h4]
      have hle : Real.sqrt ((x ^ mr * P ^ 2 * p ^ 2) ^ 2) ≤ Real.sqrt (2 * e) :=
        Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq hA0] at hle
      refine hle.trans ?_
      have h2e : Real.sqrt (2 * e) = Real.sqrt 2 * se := by
        rw [hse, Real.sqrt_mul (by norm_num)]
      have hs2 : Real.sqrt 2 ≤ 2 := by
        have : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
      rw [h2e]
      exact mul_le_mul_of_nonneg_right hs2 hse0.le
    have hB : x ^ mr * P ^ 2 * (128 * Nr * P * p ^ 4) ≤ 128 * e := by
      have h1 : x ^ mr * P ^ 2 * (128 * Nr * P * p ^ 4) = 128 * (x ^ mr * w) := by
        rw [hw]; ring
      have h2 : x ^ mr * w ≤ x ^ ε * w := mul_le_mul_of_nonneg_right hxmr_le_xe hw0.le
      rw [h1, he]
      linarith
    have hC : x ^ mr * P ^ 2 * T2 ≤ se := by
      have h1 : x ^ mr * P ^ 2 * T2 = x ^ mr * w / se := by
        rw [hT2, hw]; field_simp
      have h2 : x ^ mr * w ≤ e := by
        rw [he]
        exact mul_le_mul_of_nonneg_right hxmr_le_xe hw0.le
      rw [h1]
      rw [div_le_iff₀ hse0]
      calc x ^ mr * w ≤ e := h2
        _ = se * se := by rw [← hsesq]; ring
    have hstep2 : x ^ mr * P ^ 2 * T ≤ 3 * se + 128 * e := by
      have hT1exp : x ^ mr * P ^ 2 * T1
          = x ^ mr * P ^ 2 * p ^ 2 + x ^ mr * P ^ 2 * (128 * Nr * P * p ^ 4) := by
        rw [hT1]; ring
      have : x ^ mr * P ^ 2 * T = x ^ mr * P ^ 2 * T1 + x ^ mr * P ^ 2 * T2 := by
        rw [hT]; ring
      rw [this, hT1exp]
      linarith
    -- combine
    have hPT0 : (0 : ℝ) ≤ P ^ 2 * T := by positivity
    calc ((Nr + 1) / P) ^ mr * P ^ 2 * T = ((Nr + 1) / P) ^ mr * (P ^ 2 * T) := by ring
      _ ≤ (2 * x ^ mr) * (P ^ 2 * T) := mul_le_mul_of_nonneg_right hstep1 hPT0
      _ = 2 * (x ^ mr * P ^ 2 * T) := by ring
      _ ≤ 2 * (3 * se + 128 * e) := by linarith

end TruncArith

/-! ### Janson's Theorem 2 at a general `m`, in test-function form -/

section JansonGeneral

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- `Janson.tendsto_rate_of_janson15` at a general `m ≥ 1`, with closed-degree convention and
the `(1.5)` hypothesis taken as given. -/
theorem tendsto_janson_rate_of_15 {Nc Mc : ℕ → ℕ} {u : ℕ → ℝ} {mj : ℕ} (hmj : 1 ≤ mj)
    (hu : ∀ n, 0 ≤ u n) (hN1 : ∀ n, 1 ≤ Nc n) (hMN : ∀ n, Mc n ≤ Nc n)
    (h15 : Tendsto (fun n => (((Nc n : ℝ) + 1) / ((Mc n : ℝ) + 1)) ^ ((mj : ℝ)⁻¹)
      * (((Mc n : ℝ) + 1) * u n)) atTop (𝓝 0))
    {j : ℕ} (hj : mj ≤ j) :
    Tendsto (fun n => (Nc n : ℝ) * ((Mc n : ℝ) + 1) ^ (j - 1) * u n ^ j) atTop (𝓝 0) := by
  have hNc1 : ∀ n, (1 : ℝ) ≤ (Nc n : ℝ) := fun n => by exact_mod_cast hN1 n
  have hMNr : ∀ n, ((Mc n : ℝ) + 1) ≤ (Nc n : ℝ) + 1 := by
    intro n
    have : ((Mc n : ℝ)) ≤ (Nc n : ℝ) := by exact_mod_cast hMN n
    linarith
  have hbig := Janson.tendsto_rate_of_janson15 (N := fun n => (Nc n : ℝ) + 1)
    (Md := fun n => ((Mc n : ℝ) + 1)) (u := u) (m := mj) hmj
    (fun n => by positivity) hMNr hu h15 hj
  refine squeeze_zero (fun n => by
    have : (0 : ℝ) ≤ u n ^ j := pow_nonneg (hu n) j
    positivity) (fun n => ?_) hbig
  have hrest : (0 : ℝ) ≤ ((Mc n : ℝ) + 1) ^ (j - 1) * u n ^ j :=
    mul_nonneg (by positivity) (pow_nonneg (hu n) j)
  have h2 : (Nc n : ℝ) ≤ (Nc n : ℝ) + 1 := by linarith
  calc (Nc n : ℝ) * ((Mc n : ℝ) + 1) ^ (j - 1) * u n ^ j
      = (Nc n : ℝ) * (((Mc n : ℝ) + 1) ^ (j - 1) * u n ^ j) := by ring
    _ ≤ ((Nc n : ℝ) + 1) * (((Mc n : ℝ) + 1) ^ (j - 1) * u n ^ j) :=
        mul_le_mul_of_nonneg_right h2 hrest
    _ = ((Nc n : ℝ) + 1) * ((Mc n : ℝ) + 1) ^ (j - 1) * u n ^ j := by ring

/-- **Janson's Theorem 2 at a general `m ≥ 3`, as a test-function limit.** Under the
hypotheses of `cltcluster_a_general_janson_charFun` with the rate given as Janson's `(1.5)`,
`∫h(∑_oY_o) → E h(Z)` for every bounded continuous `h`. -/
theorem janson_expect_of_bounded_array
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Y : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (Y n) (μ n))
    (φ : ℕ → ℝ) (Mb : ℕ → ℕ) (mj : ℕ) (hmj : 3 ≤ mj)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |Y n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ Mb n + 1)
    (hm1 : ∀ n, 1 ≤ Mb n) (hmN : ∀ n, Mb n ≤ Fintype.card (O n))
    (hmean : ∀ n o, ∫ ω, Y n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (Y n) ω) ^ 2 ∂(μ n) = 1)
    (h15 : Tendsto (fun n => (((Fintype.card (O n) : ℝ) + 1) / ((Mb n : ℝ) + 1)) ^ ((mj : ℝ)⁻¹)
      * (((Mb n : ℝ) + 1) * φ n)) atTop (𝓝 0))
    {h : ℝ → ℝ} {C : ℝ} (hcont : Continuous h) (hbd : ∀ x, |h x| ≤ C) :
    Tendsto (fun n => ∫ ω, h (depSum (Y n) ω) ∂(μ n)) atTop (𝓝 (gExpect h)) := by
  classical
  have hint : ∀ n o, Integrable (Y n o) (μ n) := by
    intro n o
    refine Integrable.of_bound ((D n).meas o).aestronglyMeasurable (φ n)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hφ n o ω
  have hsum0 : ∀ n, ∫ ω, (∑ i, Y n i ω) ∂(μ n) = 0 := by
    intro n
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => hint n i)]
    simp [hmean n]
  have hdegJ : ∀ n, ∀ i : O n, (((D n).nbhd i).erase i).card ≤ Mb n := by
    intro n i
    rw [Finset.card_erase_of_mem ((D n).self_mem_nbhd i)]
    have := hdeg n i
    omega
  have hvar' : ∀ n, ∫ ω, (∑ i, Y n i ω) ^ 2 ∂(μ n) = 1 := hvar
  have hσsq : ∀ n, (1 : ℝ) ^ 2 = Cumulant.cumulant (fun ω => ∑ i, Y n i ω) 2 (μ n) := by
    intro n
    rw [Cumulant.cumulant_two, hsum0 n, hvar' n]
    norm_num
  have hN1 : ∀ n, 1 ≤ Fintype.card (O n) := fun n => le_trans (hm1 n) (hmN n)
  have hrateJ : ∀ j, mj ≤ j → Tendsto (fun n => (Fintype.card (O n) : ℝ)
      * ((Mb n : ℝ) + 1) ^ (j - 1) * (φ n / (1 : ℝ)) ^ j) atTop (𝓝 0) := by
    intro j hj
    simp only [div_one]
    exact tendsto_janson_rate_of_15 (Nc := fun n => Fintype.card (O n)) (Mc := Mb)
      (le_trans (by norm_num) hmj) hφ0 hN1 hmN h15 hj
  have hJ := Janson.tendsto_gaussPM_of_depGraph (μ := μ) (X := Y) D hdegJ
    (A := φ) hφ0 (fun n i => Filter.Eventually.of_forall fun ω => hφ n i ω)
    (σ := fun _ => (1 : ℝ)) (fun _ => one_pos) hσsq (m := mj) hmj hrateJ
  -- the standardized law is the law of `∑_oY_o`
  have hlaw : ∀ n, ((Janson.stdSumPM (D n) (1 : ℝ)
      (-(∫ ω, (∑ i, Y n i ω) ∂(μ n)) / 1) : ProbabilityMeasure ℝ) : Measure ℝ)
      = (μ n).map (depSum (Y n)) := by
    intro n
    have hfn : (fun ω => (∑ i, Y n i ω) / (1 : ℝ) + -(∫ ω, (∑ i, Y n i ω) ∂(μ n)) / 1)
        = depSum (Y n) := by
      rw [hsum0 n]
      funext ω
      simp [depSum]
    rw [Janson.stdSumPM_toMeasure, hfn]
  have hg : ((Janson.gaussPM 0 1 : ProbabilityMeasure ℝ) : Measure ℝ) = gaussianReal 0 1 := by
    rw [Janson.gaussPM_toMeasure, Real.toNNReal_one]
  -- the bounded continuous test function
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hbd 0)
  set f : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup h hcont C
      (fun x => by rw [Real.norm_eq_abs]; exact hbd x) with hf
  have hfapp : ∀ x, f x = h x := fun x => rfl
  have hbc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hJ f
  simp only [hlaw, hg, hfapp] at hbc
  have hYmeas : ∀ n, Measurable (depSum (Y n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => (D n).meas o)
  have hmap : ∀ n, ∫ x, h x ∂((μ n).map (depSum (Y n))) = ∫ ω, h (depSum (Y n) ω) ∂(μ n) := by
    intro n
    rw [integral_map (hYmeas n).aemeasurable hcont.aestronglyMeasurable]
  simp only [hmap] at hbc
  exact hbc

end JansonGeneral

/-! ### Theorem 5(b) on the array -/

section PartBArray

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Theorem 5(b) on the array, in test-function form.** The only moment hypothesis is
`∫X_{n,o}⁴ ≤ ψ_n⁴`, the rate hypothesis is `(n/D_n)^ε δ_n → 0` for the given `ε > 0`, and
`1 ≤ D_n ≤ n`. The proof truncates, bounds the tail variance, standardizes by the truncated
array's own `σ_n`, applies Janson's Theorem 2 at `m = max{3, ⌈2/ε⌉}`, and transfers by
Slutsky. -/
theorem cltcluster_b_general_janson_expect
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (ψ : ℕ → ℝ) (Mb : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hψ : ∀ n, 0 < ψ n)
    (hint4 : ∀ n o, Integrable (fun ω => (X n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (X n o ω) ^ 4 ∂(μ n) ≤ (ψ n) ^ 4)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ Mb n + 1)
    (hm1 : ∀ n, 1 ≤ Mb n) (hmN : ∀ n, Mb n ≤ Fintype.card (O n))
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => ((Fintype.card (O n) : ℝ) / (Mb n : ℝ)) ^ ε
      * ((Fintype.card (O n) : ℝ) * ((Mb n + 1 : ℕ) : ℝ) ^ 3 * (ψ n) ^ 4)) atTop (𝓝 0))
    (hfun : ℝ → ℝ) {Cb L : ℝ} (hb : ∀ x, |hfun x| ≤ Cb) (hderiv : ∀ x, |deriv hfun x| ≤ L)
    (hdiff : Differentiable ℝ hfun) :
    Tendsto (fun n => ∫ ω, hfun (depSum (X n) ω) ∂(μ n)) atTop (𝓝 (gExpect hfun)) := by
  classical
  -- the moment index `m := max{3, ⌈2/ε⌉}`
  set mj : ℕ := max 3 ⌈(2 : ℝ) / ε⌉₊ with hmjdef
  have hmj3 : 3 ≤ mj := le_max_left _ _
  have hmjR : (3 : ℝ) ≤ (mj : ℝ) := by exact_mod_cast hmj3
  have hmjpos : (0 : ℝ) < (mj : ℝ) := by linarith
  set mr : ℝ := 2 / (mj : ℝ) with hmrdef
  have hmr0 : 0 < mr := by rw [hmrdef]; positivity
  have hmr1 : mr ≤ 1 := by rw [hmrdef, div_le_one hmjpos]; linarith
  have hmrε : mr ≤ ε := by
    have hceil : ((⌈(2 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (mj : ℝ) := by
      exact_mod_cast le_max_right 3 ⌈(2 : ℝ) / ε⌉₊
    have h2ε : (2 : ℝ) / ε ≤ (mj : ℝ) := le_trans (Nat.le_ceil _) hceil
    rw [div_le_iff₀ hε] at h2ε
    rw [hmrdef, div_le_iff₀ hmjpos]
    nlinarith
  -- the real shorthands `n`, `D_n + 1` and `δ^{(ε)}_n`
  set NR : ℕ → ℝ := fun n => (Fintype.card (O n) : ℝ) with hNR
  set PR : ℕ → ℝ := fun n => (Mb n : ℝ) + 1 with hPR
  have hN1 : ∀ n, 1 ≤ Fintype.card (O n) := fun n => le_trans (hm1 n) (hmN n)
  have hNR1 : ∀ n, (1 : ℝ) ≤ NR n := fun n => by simp only [hNR]; exact_mod_cast hN1 n
  have hMR1 : ∀ n, (1 : ℝ) ≤ (Mb n : ℝ) := fun n => by exact_mod_cast hm1 n
  have hMN' : ∀ n, (Mb n : ℝ) ≤ NR n := fun n => by simp only [hNR]; exact_mod_cast hmN n
  set ee : ℕ → ℝ := fun n => (NR n / (Mb n : ℝ)) ^ ε * (NR n * PR n ^ 3 * (ψ n) ^ 4) with hee
  have hee0 : ∀ n, 0 < ee n := by
    intro n
    have h1 : (0 : ℝ) < NR n / (Mb n : ℝ) := by
      have := hNR1 n; have := hMR1 n; positivity
    have h2 : (0 : ℝ) < (NR n / (Mb n : ℝ)) ^ ε := Real.rpow_pos_of_pos h1 ε
    have h3 : (0 : ℝ) < NR n * PR n ^ 3 * (ψ n) ^ 4 := by
      have := hNR1 n
      have hP : (0 : ℝ) < PR n := by rw [hPR]; linarith [hMR1 n]
      have := hψ n
      positivity
    rw [hee]
    exact mul_pos h2 h3
  have heeto0 : Tendsto ee atTop (𝓝 0) := by
    refine hrate.congr fun n => ?_
    rw [hee, hNR, hPR]
    push_cast
    ring
  have hsee0 : ∀ n, 0 < Real.sqrt (ee n) := fun n => Real.sqrt_pos.mpr (hee0 n)
  -- the truncation level `τ_n` and its inequalities
  set TT : ℕ → ℝ := fun n => (ψ n) ^ 2 * (1 + 128 * NR n * PR n * (ψ n) ^ 2)
      + NR n * PR n * (ψ n) ^ 4 / Real.sqrt (ee n) with hTT
  have hfacts : ∀ n, (ψ n) ^ 2 ≤ TT n
      ∧ 8 * NR n * PR n * ((ψ n) ^ 4 / TT n) ≤ 1 / 16
      ∧ 8 * NR n * PR n * ((ψ n) ^ 4 / TT n) ≤ 8 * Real.sqrt (ee n)
      ∧ ((NR n + 1) / PR n) ^ mr * PR n ^ 2 * TT n
          ≤ 2 * (3 * Real.sqrt (ee n) + 128 * ee n) := by
    intro n
    exact truncSq_facts (hNR1 n) (hMR1 n) (hMN' n) (hψ n) hmr0 hmr1 hmrε
  have hTT0 : ∀ n, 0 < TT n := fun n => lt_of_lt_of_le (pow_pos (hψ n) 2) (hfacts n).1
  set τ : ℕ → ℝ := fun n => Real.sqrt (TT n) with hτdef
  have hτpos : ∀ n, 0 < τ n := fun n => by rw [hτdef]; exact Real.sqrt_pos.mpr (hTT0 n)
  have hτsq : ∀ n, (τ n) ^ 2 = TT n := fun n => by
    rw [hτdef]; exact Real.sq_sqrt (hTT0 n).le
  have hψτ : ∀ n, ψ n ≤ τ n := by
    intro n
    have h1 : Real.sqrt ((ψ n) ^ 2) ≤ Real.sqrt (TT n) := Real.sqrt_le_sqrt (hfacts n).1
    rw [Real.sqrt_sq (hψ n).le] at h1
    exact h1
  -- the tail `Z_o` and its total variance `V_n`
  set V : ℕ → ℝ := fun n => ∫ ω, (depSum (truncTail (μ n) (X n) (τ n)) ω) ^ 2 ∂(μ n) with hVdef
  have hV0 : ∀ n, 0 ≤ V n := fun n => integral_nonneg (fun ω => sq_nonneg _)
  have hVbd : ∀ n, V n ≤ 8 * NR n * PR n * ((ψ n) ^ 4 / TT n) := by
    intro n
    have h1 := integral_depSum_truncTail_sq_le (D n) (hτpos n) (hψτ n) (hψ n).le
      (hint4 n) (hfour n) (hmean n) (hdeg n)
    refine le_trans h1 (le_of_eq ?_)
    rw [hτsq n, hNR, hPR]
    push_cast
    ring
  have hVsmall : ∀ n, V n ≤ 1 / 16 := fun n => le_trans (hVbd n) (hfacts n).2.1
  have hVto0 : Tendsto V atTop (𝓝 0) := by
    refine squeeze_zero hV0 (fun n => le_trans (hVbd n) (hfacts n).2.2.1) ?_
    have hsq : Tendsto (fun n => Real.sqrt (ee n)) atTop (𝓝 0) := by
      have hc : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.tendsto 0)
      exact hc.comp heeto0
    simpa using hsq.const_mul (8 : ℝ)
  -- `σ_n² = ∫(∑_oY_o)²`, `σ_n → 1` and `σ_n ≥ 1/2`
  have hZsum : ∀ (n : ℕ) (ω : Ω n), depSum (truncTail (μ n) (X n) (τ n)) ω
      = depSum (X n) ω - depSum (truncCent (μ n) (X n) (τ n)) ω := by
    intro n ω
    simp only [depSum, truncTail]
    rw [Finset.sum_sub_distrib]
  have hXmem : ∀ n o, MemLp (X n o) 2 (μ n) := fun n o =>
    memLp_two_of_integrable_pow_four ((D n).meas o) (hint4 n o)
  have hAmem : ∀ n, MemLp (depSum (X n)) 2 (μ n) := by
    intro n
    have hre : (depSum (X n)) = fun ω => ∑ o, X n o ω := rfl
    rw [hre]
    exact memLp_finsetSum _ (fun o _ => hXmem n o)
  have hZmem : ∀ n, MemLp (depSum (truncTail (μ n) (X n) (τ n))) 2 (μ n) := by
    intro n
    have hre : (depSum (truncTail (μ n) (X n) (τ n)))
        = fun ω => ∑ o, truncTail (μ n) (X n) (τ n) o ω := rfl
    rw [hre]
    exact memLp_finsetSum _ (fun o _ =>
      memLp_two_truncTail (D n) (hτpos n) (hψτ n) (hψ n).le (hint4 n) (hfour n) (hmean n) o)
  set s2 : ℕ → ℝ := fun n => ∫ ω, (depSum (truncCent (μ n) (X n) (τ n)) ω) ^ 2 ∂(μ n)
    with hs2def
  have hs2bd : ∀ (c : ℝ), 0 < c → ∀ n, |s2 n - 1| ≤ c + V n / c + V n := by
    intro c hc n
    have hEq : s2 n = ∫ ω, (depSum (X n) ω
        - depSum (truncTail (μ n) (X n) (τ n)) ω) ^ 2 ∂(μ n) := by
      rw [hs2def]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      show (depSum (truncCent (μ n) (X n) (τ n)) ω) ^ 2
        = (depSum (X n) ω - depSum (truncTail (μ n) (X n) (τ n)) ω) ^ 2
      rw [hZsum n ω]
      ring
    rw [hEq]
    exact abs_integral_sub_sq_sub_one_le (hAmem n) (hZmem n) (hvar n) hc
  have hs2to1 : Tendsto s2 atTop (𝓝 1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_zero_of_le_add_div (fun n => dist_nonneg) hV0 hVto0 (fun c hc n => ?_)
    rw [Real.dist_eq]
    exact hs2bd c hc n
  have hs2ge : ∀ n, (1 : ℝ) / 4 ≤ s2 n := by
    intro n
    have h1 := hs2bd (1 / 4) (by norm_num) n
    have h3 : V n / (1 / 4) = 4 * V n := by ring
    rw [h3] at h1
    have h2 := hVsmall n
    have h5 := abs_le.mp h1
    linarith [h5.1]
  set sg : ℕ → ℝ := fun n => Real.sqrt (s2 n) with hsgdef
  have hsgge : ∀ n, (1 : ℝ) / 2 ≤ sg n := by
    intro n
    rw [hsgdef,
      show (1 : ℝ) / 2 = Real.sqrt (1 / 4) from by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (hs2ge n)
  have hsgpos : ∀ n, 0 < sg n := fun n => lt_of_lt_of_le (by norm_num) (hsgge n)
  have hsg2 : ∀ n, (sg n) ^ 2 = s2 n := by
    intro n
    rw [hsgdef]
    exact Real.sq_sqrt (le_trans (by norm_num) (hs2ge n))
  have hsgto1 : Tendsto sg atTop (𝓝 1) := by
    have hc := (Real.continuous_sqrt.tendsto 1).comp hs2to1
    rw [Real.sqrt_one] at hc
    exact hc
  -- the standardized truncated array, and Janson's theorem applied to it
  set Ys : ∀ n, O n → Ω n → ℝ := fun n => truncStd (μ n) (X n) (τ n) (sg n) with hYs
  set DY : ∀ n, DepGraph (Ys n) (μ n) :=
    fun n => truncStdDepGraph (D n) (τ n) (sg n) with hDY
  have hYsbd : ∀ n o ω, |Ys n o ω| ≤ 2 * τ n / sg n := fun n o ω =>
    abs_truncStd_le (D n) (hτpos n) (hψτ n) (hψ n).le (hsgpos n) (hint4 n) (hfour n)
      (hmean n) o ω
  have hYsmean : ∀ n o, ∫ ω, Ys n o ω ∂(μ n) = 0 := fun n o =>
    integral_truncStd_eq_zero (D n) (hτpos n) o
  have hYsdepSum : ∀ (n : ℕ) (ω : Ω n),
      depSum (Ys n) ω = depSum (truncCent (μ n) (X n) (τ n)) ω / sg n :=
    fun n ω => depSum_truncStd (X n) (τ n) (sg n) ω
  have hYsvar : ∀ n, ∫ ω, (depSum (Ys n) ω) ^ 2 ∂(μ n) = 1 := by
    intro n
    have hre : ∀ ω, (depSum (Ys n) ω) ^ 2
        = (depSum (truncCent (μ n) (X n) (τ n)) ω) ^ 2 / (sg n) ^ 2 := by
      intro ω; rw [hYsdepSum n ω, div_pow]
    simp only [hre]
    rw [integral_div, hsg2 n]
    exact div_self (by linarith [hs2ge n] : s2 n ≠ 0)
  have hYsdeg : ∀ n o, ((DY n).nbhd o).card ≤ Mb n + 1 := fun n o => hdeg n o
  -- Janson's `(1.5)` on the truncated array
  have hq0 : ∀ n, 0 ≤ ((NR n + 1) / PR n) ^ ((mj : ℝ)⁻¹) * (PR n * (2 * τ n / sg n)) := by
    intro n
    have hP : (0 : ℝ) < PR n := by rw [hPR]; linarith [hMR1 n]
    have h1 : (0 : ℝ) ≤ ((NR n + 1) / PR n) ^ ((mj : ℝ)⁻¹) :=
      Real.rpow_nonneg (by positivity) _
    have h2 : (0 : ℝ) ≤ PR n * (2 * τ n / sg n) := by
      have := (hτpos n).le; have := (hsgpos n).le; positivity
    exact mul_nonneg h1 h2
  have hqsq : ∀ n, (((NR n + 1) / PR n) ^ ((mj : ℝ)⁻¹) * (PR n * (2 * τ n / sg n))) ^ 2
      ≤ 32 * (3 * Real.sqrt (ee n) + 128 * ee n) := by
    intro n
    have hP : (0 : ℝ) < PR n := by rw [hPR]; linarith [hMR1 n]
    have hbase0 : (0 : ℝ) ≤ (NR n + 1) / PR n := by
      have := hNR1 n; positivity
    have hrp : (((NR n + 1) / PR n) ^ ((mj : ℝ)⁻¹)) ^ 2 = ((NR n + 1) / PR n) ^ mr := by
      rw [← Real.rpow_natCast (((NR n + 1) / PR n) ^ ((mj : ℝ)⁻¹)) 2,
        ← Real.rpow_mul hbase0, hmrdef]
      norm_num
      rw [inv_mul_eq_div]
    have hsgsq : (1 : ℝ) / (sg n) ^ 2 ≤ 4 := by
      have h1 : (1 : ℝ) / 4 ≤ (sg n) ^ 2 := by
        have := hsgge n
        nlinarith [hsgpos n]
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hfac : (PR n * (2 * τ n / sg n)) ^ 2 ≤ 16 * (PR n ^ 2 * TT n) := by
      have h1 : (PR n * (2 * τ n / sg n)) ^ 2 = PR n ^ 2 * (4 * TT n) * (1 / (sg n) ^ 2) := by
        field_simp
        rw [← hτsq n]
        ring
      rw [h1]
      have h2 : (0 : ℝ) ≤ PR n ^ 2 * (4 * TT n) := by
        have := (hTT0 n).le; positivity
      calc PR n ^ 2 * (4 * TT n) * (1 / (sg n) ^ 2)
          ≤ PR n ^ 2 * (4 * TT n) * 4 := mul_le_mul_of_nonneg_left hsgsq h2
        _ = 16 * (PR n ^ 2 * TT n) := by ring
    calc (((NR n + 1) / PR n) ^ ((mj : ℝ)⁻¹) * (PR n * (2 * τ n / sg n))) ^ 2
        = (((NR n + 1) / PR n) ^ ((mj : ℝ)⁻¹)) ^ 2 * (PR n * (2 * τ n / sg n)) ^ 2 := by ring
      _ = ((NR n + 1) / PR n) ^ mr * (PR n * (2 * τ n / sg n)) ^ 2 := by rw [hrp]
      _ ≤ ((NR n + 1) / PR n) ^ mr * (16 * (PR n ^ 2 * TT n)) :=
          mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hbase0 _)
      _ = 16 * (((NR n + 1) / PR n) ^ mr * PR n ^ 2 * TT n) := by ring
      _ ≤ 16 * (2 * (3 * Real.sqrt (ee n) + 128 * ee n)) := by
          have := (hfacts n).2.2.2
          linarith
      _ = 32 * (3 * Real.sqrt (ee n) + 128 * ee n) := by ring
  have h15 : Tendsto (fun n => (((Fintype.card (O n) : ℝ) + 1) / ((Mb n : ℝ) + 1))
      ^ ((mj : ℝ)⁻¹) * (((Mb n : ℝ) + 1) * (2 * τ n / sg n))) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n => Real.sqrt (ee n)) atTop (𝓝 0) := by
      have hc : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.tendsto 0)
      exact hc.comp heeto0
    have hbound : Tendsto
        (fun n => Real.sqrt (32 * (3 * Real.sqrt (ee n) + 128 * ee n))) atTop (𝓝 0) := by
      have hc : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.tendsto 0)
      have hinner : Tendsto (fun n => 32 * (3 * Real.sqrt (ee n) + 128 * ee n)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => 3 * Real.sqrt (ee n) + 128 * ee n) atTop (𝓝 0) := by
          simpa using (hsq.const_mul (3 : ℝ)).add (heeto0.const_mul (128 : ℝ))
        simpa using h1.const_mul (32 : ℝ)
      exact hc.comp hinner
    refine squeeze_zero (fun n => hq0 n) (fun n => ?_) hbound
    have h1 := hqsq n
    have h2 : Real.sqrt ((((NR n + 1) / PR n) ^ ((mj : ℝ)⁻¹) * (PR n * (2 * τ n / sg n))) ^ 2)
        ≤ Real.sqrt (32 * (3 * Real.sqrt (ee n) + 128 * ee n)) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (hq0 n)] at h2
  have hengine : Tendsto (fun n => ∫ ω, hfun (depSum (Ys n) ω) ∂(μ n)) atTop
      (𝓝 (gExpect hfun)) :=
    janson_expect_of_bounded_array μ Ys DY (fun n => 2 * τ n / sg n) Mb mj hmj3
      (fun n => by have := (hτpos n).le; have := (hsgpos n).le; positivity)
      hYsbd hYsdeg hm1 hmN hYsmean hYsvar h15 hdiff.continuous hb
  -- transfer from the truncated array to `∑_oX_{n,o}`
  have hL0 : (0 : ℝ) ≤ L := le_trans (abs_nonneg _) (hderiv 0)
  have hlip : ∀ x y, |hfun x - hfun y| ≤ L * |x - y| := by
    have hlw : LipschitzWith (Real.toNNReal L) hfun := by
      refine lipschitzWith_of_nnnorm_deriv_le hdiff (fun x => ?_)
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal L hL0, Real.norm_eq_abs]
      exact hderiv x
    intro x y
    have h := hlw.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL0] at h
    exact h
  have hAmeas : ∀ n, Measurable (depSum (X n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => (D n).meas o)
  have hBmeas : ∀ n, Measurable (depSum (Ys n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => (DY n).meas o)
  have hdiffAB : ∀ (n : ℕ) (ω : Ω n), depSum (X n) ω - sg n * depSum (Ys n) ω
      = depSum (truncTail (μ n) (X n) (τ n)) ω := by
    intro n ω
    rw [hYsdepSum n ω, mul_div_cancel₀ _ (ne_of_gt (hsgpos n)), hZsum n ω]
  have hABi : ∀ n, Integrable (fun ω => |depSum (X n) ω - sg n * depSum (Ys n) ω|) (μ n) := by
    intro n
    have hre : (fun ω => |depSum (X n) ω - sg n * depSum (Ys n) ω|)
        = fun ω => |depSum (truncTail (μ n) (X n) (τ n)) ω| := by
      funext ω; rw [hdiffAB n ω]
    rw [hre]
    exact ((hZmem n).integrable (by norm_num)).abs
  have hd0 : Tendsto (fun n => ∫ ω, |depSum (X n) ω - sg n * depSum (Ys n) ω| ∂(μ n))
      atTop (𝓝 0) := by
    have hre : ∀ n, (fun ω => |depSum (X n) ω - sg n * depSum (Ys n) ω|)
        = fun ω => |depSum (truncTail (μ n) (X n) (τ n)) ω| := by
      intro n; funext ω; rw [hdiffAB n ω]
    simp only [hre]
    refine tendsto_zero_of_le_add_div (fun n => integral_nonneg (fun ω => abs_nonneg _))
      hV0 hVto0 (fun c hc n => ?_)
    have h1 : ∫ ω, |depSum (truncTail (μ n) (X n) (τ n)) ω| ∂(μ n) ≤ (V n / c + c) / 2 :=
      integral_abs_le_of_sq (hZmem n) hc
    have h2 : (0 : ℝ) ≤ V n / c := by positivity
    linarith [h1, hV0 n, hc.le]
  have hBi : ∀ n, Integrable (fun ω => |depSum (Ys n) ω|) (μ n) := by
    intro n
    refine (Integrable.abs ?_)
    refine integrable_of_abs_le (hBmeas n)
      (C := (Fintype.card (O n) : ℝ) * (2 * τ n / sg n)) (fun ω => ?_)
    calc |depSum (Ys n) ω| ≤ ∑ o, |Ys n o ω| := by
          simpa [depSum] using Finset.abs_sum_le_sum_abs (fun o => Ys n o ω) Finset.univ
      _ ≤ ∑ _o : O n, 2 * τ n / sg n := Finset.sum_le_sum (fun o _ => hYsbd n o ω)
      _ = (Fintype.card (O n) : ℝ) * (2 * τ n / sg n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hBmem : ∀ n, MemLp (depSum (Ys n)) 2 (μ n) := by
    intro n
    refine memLp_two_of_abs_le (hBmeas n)
      (C := (Fintype.card (O n) : ℝ) * (2 * τ n / sg n)) (fun ω => ?_)
    calc |depSum (Ys n) ω| ≤ ∑ o, |Ys n o ω| := by
          simpa [depSum] using Finset.abs_sum_le_sum_abs (fun o => Ys n o ω) Finset.univ
      _ ≤ ∑ _o : O n, 2 * τ n / sg n := Finset.sum_le_sum (fun o _ => hYsbd n o ω)
      _ = (Fintype.card (O n) : ℝ) * (2 * τ n / sg n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hB1 : ∀ n, ∫ ω, |depSum (Ys n) ω| ∂(μ n) ≤ 1 := by
    intro n
    have h1 := integral_abs_le_of_sq (hBmem n) (c := 1) (by norm_num)
    rw [hYsvar n] at h1
    linarith
  exact tendsto_integral_of_approx μ (fun n => depSum (X n)) (fun n => depSum (Ys n))
    hAmeas hBmeas sg hdiff.continuous.measurable hb hL0 hlip hABi hd0 hBi hB1 hsgto1 hengine

/-- **Theorem 5(b) on the array, characteristic-function form.** -/
theorem cltcluster_b_general_janson_charFun
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (ψ : ℕ → ℝ) (Mb : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hψ : ∀ n, 0 < ψ n)
    (hint4 : ∀ n o, Integrable (fun ω => (X n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (X n o ω) ^ 4 ∂(μ n) ≤ (ψ n) ^ 4)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ Mb n + 1)
    (hm1 : ∀ n, 1 ≤ Mb n) (hmN : ∀ n, Mb n ≤ Fintype.card (O n))
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => ((Fintype.card (O n) : ℝ) / (Mb n : ℝ)) ^ ε
      * ((Fintype.card (O n) : ℝ) * ((Mb n + 1 : ℕ) : ℝ) ^ 3 * (ψ n) ^ 4)) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (depSum (X n))) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => (D n).meas o)
  refine charFun_tendsto_of_expect μ (fun n => depSum (X n)) hWmeas (fun h C L hb hd hdf => ?_) t
  exact cltcluster_b_general_janson_expect μ X D ψ Mb ε hε hψ hint4 hfour hdeg hm1 hmN
    hmean hvar hrate h hb hd hdf

/-- Theorem 5(b) on the array, in CDF form. -/
theorem cltcluster_b_general_janson
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (ψ : ℕ → ℝ) (Mb : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hψ : ∀ n, 0 < ψ n)
    (hint4 : ∀ n o, Integrable (fun ω => (X n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (X n o ω) ^ 4 ∂(μ n) ≤ (ψ n) ^ 4)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ Mb n + 1)
    (hm1 : ∀ n, 1 ≤ Mb n) (hmN : ∀ n, Mb n ≤ Fintype.card (O n))
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => ((Fintype.card (O n) : ℝ) / (Mb n : ℝ)) ^ ε
      * ((Fintype.card (O n) : ℝ) * ((Mb n + 1 : ℕ) : ℝ) ^ 3 * (ψ n) ^ 4)) atTop (𝓝 0))
    (s : ℝ) :
    Tendsto (fun n => ((μ n).map (depSum (X n))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => (D n).meas o)
  haveI : ∀ n, IsProbabilityMeasure ((μ n).map (depSum (X n))) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hWmeas n).aemeasurable).2 inferInstance
  set lawn : ℕ → ProbabilityMeasure ℝ :=
    fun n => ⟨(μ n).map (depSum (X n)), inferInstance⟩ with hlawn
  let ν₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  letI : NullSingletonClass (ν₀ : Measure ℝ) := nullSingletonClass_gaussianReal one_ne_zero
  refine cdf_tendsto_of_charFun_tendsto lawn ν₀ (fun t => ?_) s
  exact cltcluster_b_general_janson_charFun μ X D ψ Mb ε hε hψ hint4 hfour hdeg hm1 hmN
    hmean hvar hrate t

/-- Theorem 5(b) on the array, as `⟶ᵈ N(0,1)`. -/
theorem cltcluster_b_general_janson_tendstoInDistribution
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (ψ : ℕ → ℝ) (Mb : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hψ : ∀ n, 0 < ψ n)
    (hint4 : ∀ n o, Integrable (fun ω => (X n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (X n o ω) ^ 4 ∂(μ n) ≤ (ψ n) ^ 4)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ Mb n + 1)
    (hm1 : ∀ n, 1 ≤ Mb n) (hmN : ∀ n, Mb n ≤ Fintype.card (O n))
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => ((Fintype.card (O n) : ℝ) / (Mb n : ℝ)) ^ ε
      * ((Fintype.card (O n) : ℝ) * ((Mb n + 1 : ℕ) : ℝ) ^ 3 * (ψ n) ^ 4)) atTop (𝓝 0)) :
    TendstoInDistribution (fun n => depSum (X n)) atTop (id : ℝ → ℝ) μ (gaussianReal 0 1) := by
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => (D n).meas o)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hWmeas n).aemeasurable)
    aemeasurable_id fun t => ?_
  rw [Measure.map_id]
  exact cltcluster_b_general_janson_charFun μ X D ψ Mb ε hε hψ hint4 hfour hdeg hm1 hmN
    hmean hvar hrate t

end PartBArray

/-! ### `β̂_JM` at general `J` -/

section PartBBetaJM

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {r : Type*} [Fintype r] [DecidableEq r]

/-- **Theorem 5(b) for `β̂_JM` at general `J`**, in the conditional frame, under the rate
`(n/D_n)^ε δ_n → 0` for a given `ε > 0`. -/
theorem cltcluster_b_general_betaJM_janson
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n) (Om n))
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n) = Om n o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂(μ n) ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (ε : ℝ) (hε : 0 < ε)
    (hrate : Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n) (lmin n) ε) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  have hPD : ∀ n, (scoreVar (Xt n) (Om n)).PosDef := fun n =>
    Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlmin n)) (hfloor n)
  have hstat : ∀ n, (fun ω => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n ω - β n))))
      = depSum (scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) := by
    intro n
    funext ω
    rw [hscore n ω]
    exact dotProduct_standardized_eq_depSum (Xt n) (Om n) (Rn n) b (ν n) ω
  simp only [hstat]
  refine cltcluster_b_general_janson μ
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * C4 / Real.sqrt (lmin n)) Dn ε hε
    (fun n => div_pos (mul_pos hB0 hC40) (Real.sqrt_pos.mpr (hlmin n))) ?_ ?_ ?_ hDn1 hDnN
    ?_ ?_ ?_ s
  · exact fun n o => integrable_scoreArray_pow_four (hint4 n) (Xt n) _ o
  · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hA n) (hlmin n) (hfloor n)
      hB0.le hC40.le (hB n) (hint4 n) (hfour n) hb o
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hint4 n) (hOm n) hb
  · refine squeeze_zero (fun n => ?_) (fun n => ?_)
      (by simpa using hrate.const_mul (8 * B ^ 4 * C4 ^ 4))
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
    · exact epsFirstRate_le (hDn1 n) (hlmin n)

/-- The same for a constant family, as convergence in distribution. -/
theorem cltcluster_b_general_betaJM_janson_const
    {W : Type*} [mW : MeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W → ℝ) (bhat : ℕ → W → (K → ℝ)) (β : ℕ → K → ℝ)
    (Dv : ∀ n, DepGraph (ν n) μ)
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n) (Om n))
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂μ = Om n o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂μ = 0)
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) μ)
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂μ ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (ε : ℝ) (hε : 0 < ε)
    (hrate : Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n) (lmin n) ε) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) :
    TendstoInDistribution (m := fun _ : ℕ => mW)
      (fun n ω => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n ω - β n)))) atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 1) := by
  have hPD : ∀ n, (scoreVar (Xt n) (Om n)).PosDef := fun n =>
    Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlmin n)) (hfloor n)
  have hstat : ∀ n, (fun ω => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n ω - β n))))
      = depSum (scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) := by
    intro n
    funext ω
    rw [hscore n ω]
    exact dotProduct_standardized_eq_depSum (Xt n) (Om n) (Rn n) b (ν n) ω
  have hfun : (fun (n : ℕ) (ω : W) => b ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun n => depSum (scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) :=
    funext hstat
  rw [hfun]
  refine cltcluster_b_general_janson_tendstoInDistribution (Ω := fun _ => W) (fun _ => μ)
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * C4 / Real.sqrt (lmin n)) Dn ε hε
    (fun n => div_pos (mul_pos hB0 hC40) (Real.sqrt_pos.mpr (hlmin n))) ?_ ?_ ?_ hDn1 hDnN
    ?_ ?_ ?_
  · exact fun n o => integrable_scoreArray_pow_four (hint4 n) (Xt n) _ o
  · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hA n) (hlmin n) (hfloor n)
      hB0.le hC40.le (hB n) (hint4 n) (hfour n) hb o
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hint4 n) (hOm n) hb
  · refine squeeze_zero (fun n => ?_) (fun n => ?_)
      (by simpa using hrate.const_mul (8 * B ^ 4 * C4 ^ 4))
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
    · exact epsFirstRate_le (hDn1 n) (hlmin n)

end PartBBetaJM

/-! ### Cramér–Wold and removal of the conditioning on `𝒟` -/

section PartBDeconditioning

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Cramér–Wold for part (b), in the conditional frame. -/
theorem cltcluster_b_general_betaJM_janson_vector
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    {W : Type*} [mW : MeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → W → ℝ) (bhat : ℕ → W → (K → ℝ)) (β : ℕ → K → ℝ)
    (Dv : ∀ n, DepGraph (ν n) μ)
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n) (Om n))
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂μ = Om n o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂μ = 0)
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) μ)
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂μ ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (ε : ℝ) (hε : 0 < ε)
    (hrate : Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n) (lmin n) ε) atTop (𝓝 0))
    (hWvm : ∀ n, Measurable fun ω =>
      restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n)) :
    TendstoInDistribution (m := fun _ : ℕ => mW)
      (fun n ω => restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => μ)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  refine tendstoInDistribution_stdGaussian_of_unit_directions
    (fun n => (hWvm n).aemeasurable) fun b hb => ?_
  have hs : ∀ n, (fun ω => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun ω => ⟪restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n), b⟫ :=
    fun n => funext fun ω => (inner_restrictedStat (Xt n) (Om n) (Rn n) _ b).symm
  have h := cltcluster_b_general_betaJM_janson_const μ Xt Om Rn ν bhat β Dv hscore hA
    lmin hlmin hfloor hOm hmean B C4 hB0 hC40 hB hint4 hfour Dn hDn1 hDnN hdeg ε hε hrate
    (WithLp.ofLp b) (dotProduct_self_ofLp b hb)
  have hfun : (fun (n : ℕ) (ω : W) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun (n : ℕ) (ω : W) =>
        ⟪restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Theorem 5(b) for `β̂_JM` under `P`**, with a random design. The deconditioning uses
`SteinCluster.ae_ae_eq_frozen_design` and `SteinCluster.cltcluster_a_unconditional_of_frozen_stat`. -/
theorem cltcluster_b_general_betaJM_janson_unconditional
    {r : Type*} [Fintype r] [DecidableEq r]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1)
    (hWm : ∀ n, Measurable fun y =>
      b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n))))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  refine cltcluster_a_unconditional_of_frozen_stat h𝒟 P (W := fun n y =>
      b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n)))) hWm
    (Wfr := fun ω n => depSum (scoreArray (Xt n ω)
      (steinWeight (Xt n ω) (Om n ω) (Rn n) b) (ν n))) ?_ ?_
  · filter_upwards [ae_ae_eq_frozen_design h𝒟 P hXtD hOmD] with ω hω n
    filter_upwards [hω n] with y hy
    show b ⬝ᵥ _ = _
    rw [hscore n y, dotProduct_standardized_eq_depSum, hy.1, hy.2]
  · filter_upwards [hdep, hA, hlmin, hfloor, hOmeq, hmean, hB, hint4, hfour, hDn1, hDnN, hrate]
      with ω hdepω hAω hlminω hfloorω hOmω hmeanω hBω hint4ω hfourω hDn1ω hDnNω hrateω
    obtain ⟨Dv, hdegω⟩ := hdepω
    have hPD : ∀ n, (scoreVar (Xt n ω) (Om n ω)).PosDef := fun n =>
      Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlminω n)) (hfloorω n)
    refine cltcluster_b_general_janson_tendstoInDistribution
      (Ω := fun _ => Ω) (fun _ => condExpKernel P 𝒟 ω)
      (fun n => scoreArray (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b) (ν n))
      (fun n => scoreArrayDepGraph (Dv n) (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b))
      (fun n => B * C4 / Real.sqrt (lmin n ω)) (fun n => Dn n ω) ε hε
      (fun n => div_pos (mul_pos hB0 hC40) (Real.sqrt_pos.mpr (hlminω n))) ?_ ?_ ?_
      hDn1ω hDnNω ?_ ?_ ?_
    · exact fun n o => integrable_scoreArray_pow_four (hint4ω n) (Xt n ω) _ o
    · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hAω n) (hlminω n) (hfloorω n)
        hB0.le hC40.le (hBω n) (hint4ω n) (hfourω n) hb o
    · intro n o
      rw [nbhd_scoreArrayDepGraph]
      exact hdegω n o
    · exact fun n o => integral_scoreArray (fun o => hmeanω n o) (Xt n ω) _ o
    · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hAω n)
        (fun o => (Dv n).meas o) (hint4ω n) (hOmω n) hb
    · refine squeeze_zero (fun n => ?_) (fun n => ?_)
        (by simpa using hrateω.const_mul (8 * B ^ 4 * C4 ^ 4))
      · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
      · exact epsFirstRate_le (hDn1ω n) (hlminω n)

/-- **Theorem 5(b), vector form.** `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)` under `P` with a
random design, at general `J`. -/
theorem cltcluster_b_general_betaJM_janson_unconditional_vector
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (hWvm : ∀ n, Measurable fun y =>
      restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  refine tendstoInDistribution_stdGaussian_of_unit_directions
    (fun n => (hWvm n).aemeasurable) fun b hb => ?_
  have hs : ∀ n, (fun y => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))))
      = fun y => ⟪restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n), b⟫ :=
    fun n => funext fun y => (inner_restrictedStat (Xt n y) (Om n y) (Rn n) _ b).symm
  have hWm : ∀ n, Measurable fun y => (WithLp.ofLp b) ⬝ᵥ
      ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))) := by
    intro n
    rw [hs n]
    exact (by fun_prop : Measurable fun v : EuclideanSpace ℝ rr => ⟪v, b⟫).comp (hWvm n)
  have h := cltcluster_b_general_betaJM_janson_unconditional h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B C4 hB0 hC40 (WithLp.ofLp b)
    (dotProduct_self_ofLp b hb) hWm hdep hA hlmin hfloor hOmeq hmean hB hint4 hfour
    hDn1 hDnN ε hε hrate
  have hfun : (fun (n : ℕ) (y : Ω) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))))
      = fun (n : ℕ) (y : Ω) =>
        ⟪restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

end PartBDeconditioning

/-! ### Corollary SM.D.3, second sentence -/

section PartBClustershock

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- Under the floor `λ_min(Ω_n) ≥ cn` and the degree bound `D_n ≤ JḠ_n`,
`δ^{(ε)}_n = D_n^{3−ε}/(c²n^{1−ε}) ≤ (J^{3−ε}/c²)·Ḡ_n^{3−ε}/n^{1−ε}` for `ε ≤ 3`. -/
theorem epsRate_le_cluster {Nc Dc Gc Jc : ℕ} {c ε : ℝ} (hc : 0 < c) (hε3 : ε ≤ 3)
    (hN : 1 ≤ Nc) (hD1 : 1 ≤ Dc) (hDJG : Dc ≤ Jc * Gc) :
    epsRate Nc Dc (c * (Nc : ℝ)) ε
      ≤ ((Jc : ℝ) ^ ((3 : ℝ) - ε) / c ^ 2)
        * ((Gc : ℝ) ^ ((3 : ℝ) - ε) / (Nc : ℝ) ^ ((1 : ℝ) - ε)) := by
  have hN0 : (0 : ℝ) < (Nc : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hD0 : (0 : ℝ) < (Dc : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hD1
  have hDJ : (Dc : ℝ) ≤ (Jc : ℝ) * (Gc : ℝ) := by exact_mod_cast hDJG
  have h3e : (0 : ℝ) ≤ (3 : ℝ) - ε := by linarith
  have hNe0 : (0 : ℝ) < (Nc : ℝ) ^ ε := Real.rpow_pos_of_pos hN0 ε
  have hN1e0 : (0 : ℝ) < (Nc : ℝ) ^ ((1 : ℝ) - ε) := Real.rpow_pos_of_pos hN0 _
  have hN1ene : (Nc : ℝ) ^ ((1 : ℝ) - ε) ≠ 0 := ne_of_gt hN1e0
  have hcne : c ≠ 0 := ne_of_gt hc
  have hNne : (Nc : ℝ) ≠ 0 := ne_of_gt hN0
  set y : ℝ := ((Nc : ℝ) / (Dc : ℝ)) ^ ε with hy
  have hER : epsRate Nc Dc (c * (Nc : ℝ)) ε = (y * (Dc : ℝ) ^ 3) / (c ^ 2 * (Nc : ℝ)) := by
    unfold epsRate accumRate
    rw [← hy]
    field_simp
  have hK : y * (Dc : ℝ) ^ 3 ≤ ((Jc : ℝ) * (Gc : ℝ)) ^ ((3 : ℝ) - ε) * (Nc : ℝ) ^ ε := by
    have hdiv : y = (Nc : ℝ) ^ ε / (Dc : ℝ) ^ ε := by
      rw [hy, div_eq_mul_inv, Real.mul_rpow hN0.le (by positivity), Real.inv_rpow hD0.le,
        ← div_eq_mul_inv]
    have hD3 : (Dc : ℝ) ^ (3 : ℕ) = (Dc : ℝ) ^ ((3 : ℝ)) := by
      rw [← Real.rpow_natCast (Dc : ℝ) 3]; norm_num
    have hsub : (Dc : ℝ) ^ ((3 : ℝ) - ε) = (Dc : ℝ) ^ ((3 : ℝ)) / (Dc : ℝ) ^ ε :=
      Real.rpow_sub hD0 3 ε
    have hle : (Dc : ℝ) ^ ((3 : ℝ) - ε) ≤ ((Jc : ℝ) * (Gc : ℝ)) ^ ((3 : ℝ) - ε) :=
      Real.rpow_le_rpow hD0.le hDJ h3e
    rw [hdiv, hD3]
    calc (Nc : ℝ) ^ ε / (Dc : ℝ) ^ ε * (Dc : ℝ) ^ ((3 : ℝ))
        = (Nc : ℝ) ^ ε * ((Dc : ℝ) ^ ((3 : ℝ)) / (Dc : ℝ) ^ ε) := by ring
      _ = (Nc : ℝ) ^ ε * (Dc : ℝ) ^ ((3 : ℝ) - ε) := by rw [hsub]
      _ ≤ (Nc : ℝ) ^ ε * ((Jc : ℝ) * (Gc : ℝ)) ^ ((3 : ℝ) - ε) :=
          mul_le_mul_of_nonneg_left hle hNe0.le
      _ = ((Jc : ℝ) * (Gc : ℝ)) ^ ((3 : ℝ) - ε) * (Nc : ℝ) ^ ε := by ring
  have hmul : ((Jc : ℝ) * (Gc : ℝ)) ^ ((3 : ℝ) - ε)
      = (Jc : ℝ) ^ ((3 : ℝ) - ε) * (Gc : ℝ) ^ ((3 : ℝ) - ε) :=
    Real.mul_rpow (by positivity) (by positivity)
  have hprod : (Nc : ℝ) ^ ε * (Nc : ℝ) ^ ((1 : ℝ) - ε) = (Nc : ℝ) := by
    rw [← Real.rpow_add hN0, show ε + ((1 : ℝ) - ε) = 1 by ring, Real.rpow_one]
  have hNdiv : (Nc : ℝ) / (Nc : ℝ) ^ ((1 : ℝ) - ε) = (Nc : ℝ) ^ ε := by
    rw [div_eq_iff hN1ene]
    exact hprod.symm
  rw [hER, div_le_iff₀ (by positivity : (0 : ℝ) < c ^ 2 * (Nc : ℝ))]
  have hRHS : ((Jc : ℝ) ^ ((3 : ℝ) - ε) / c ^ 2
        * ((Gc : ℝ) ^ ((3 : ℝ) - ε) / (Nc : ℝ) ^ ((1 : ℝ) - ε))) * (c ^ 2 * (Nc : ℝ))
      = ((Jc : ℝ) ^ ((3 : ℝ) - ε) * (Gc : ℝ) ^ ((3 : ℝ) - ε))
        * ((Nc : ℝ) / (Nc : ℝ) ^ ((1 : ℝ) - ε)) := by
    field_simp
  rw [hRHS, hNdiv, ← hmul]
  exact hK

/-- `Ḡ_n^{3−ε}/n^{1−ε} → 0` implies `δ^{(ε)}_n → 0`. -/
theorem tendsto_epsRate_of_cluster_size {N D Gb : ℕ → ℕ} {Jc : ℕ} {c ε : ℝ} (hc : 0 < c)
    (hε3 : ε ≤ 3) (hN : ∀ n, 1 ≤ N n) (hD1 : ∀ n, 1 ≤ D n) (hDJG : ∀ n, D n ≤ Jc * Gb n)
    (hG : Tendsto (fun n => (Gb n : ℝ) ^ ((3 : ℝ) - ε) / (N n : ℝ) ^ ((1 : ℝ) - ε))
      atTop (𝓝 0)) :
    Tendsto (fun n => epsRate (N n) (D n) (c * (N n : ℝ)) ε) atTop (𝓝 0) :=
  squeeze_zero (fun n => epsRate_nonneg _ _ _ _)
    (fun n => epsRate_le_cluster hc hε3 (hN n) (hD1 n) (hDJG n))
    (by simpa using hG.const_mul ((Jc : ℝ) ^ ((3 : ℝ) - ε) / c ^ 2))

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Dm : Type*} [DecidableEq Dm]
variable {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Corollary SM.D.3, second sentence**, at general `J` under the rate
`Ḡ_n^{3−ε}/n^{1−ε} → 0` for a given `ε > 0`, with `0 < B` and `0 < C₄`. -/
theorem clustershock_b_general_janson
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n) dims o o')
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (sc : ℕ → Dm → ℝ) (ve : ∀ n, O n → ℝ) (hsc : ∀ n, ∀ j ∈ dims, 0 ≤ sc n j)
    (s2 : ℝ) (hs2 : 0 < s2) (hve : ∀ n o, s2 ≤ ve n o)
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n)
      = Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n) o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂(μ n) ≤ C4 ^ 4)
    (θ : ℝ) (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (ε : ℝ) (hε : 0 < ε) (hε3 : ε ≤ 3)
    (hGrate : Tendsto (fun n => (Gb n : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n)
              (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  have hfloorOm : ∀ n, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n) :=
    fun n => Multiway.Sharing.smul_one_le_clusterOmega (hsc n) (hve n)
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hfloorK : ∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n) (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) := by
    intro n
    have h1 : s2 • ((θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ))
        ≤ s2 • ((Xt n)ᵀ * Xt n) := Multiway.loewner_smul_le_smul hs2.le (hdesign n)
    rw [smul_smul, ← mul_assoc] at h1
    exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj (hfloorOm n) (Xt n))
  have hnbhd : ∀ n o, (Dv n).nbhd o = Multiway.Sharing.closedNbhd (c n) dims o := by
    intro n o
    ext o'
    rw [DepGraph.mem_nbhd_iff, Multiway.Sharing.mem_closedNbhd]
    exact hshare n o o'
  set Dn : ℕ → ℕ := fun n => min (dims.card * Gb n) (Fintype.card (O n)) with hDndef
  have hdegF : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n := by
    intro n o
    refine le_min ?_ ?_
    · rw [hnbhd n o]; exact card_closedNbhd_le_mul (hGb n) o
    · exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  have hDn1 : ∀ n, 1 ≤ Dn n := by
    intro n
    obtain ⟨o⟩ := hne n
    refine le_trans ?_ (hdegF n o)
    exact Finset.card_pos.mpr ⟨o, (Dv n).self_mem_nbhd o⟩
  refine cltcluster_b_general_betaJM_janson μ Xt
    (fun n => Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) Rn ν bhat β Dv hscore hA
    (fun n => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n => mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n)) hfloorK hOm hmean
    B C4 hB0 hC40 hB hint4 hfour Dn hDn1 (fun n => min_le_right _ _)
    (fun n o => le_trans (hdegF n o) (Nat.le_succ _)) ε hε ?_ b hb s
  exact tendsto_epsRate_of_cluster_size (mul_pos hs2 hθ) hε3 (fun n => hcard n) hDn1
    (fun n => min_le_left _ _) hGrate

end PartBClustershock

/-! ### Witness with an unbounded disturbance and `ε = 1/4` -/

section PartBWitness

open Filter
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.Multilinear
open Multiway.ClusterShock

namespace UnboundedWitness

/-- The coin read by component `k` of observation `o`; distinct observations read disjoint
blocks of `n+1` coins. -/
def ubIdx (n : ℕ) (o : Fin (n + 3)) (k : Fin (n + 1)) : Fin ((n + 3) * (n + 1)) :=
  ⟨o.val * (n + 1) + k.val, by
    have h1 : o.val + 1 ≤ n + 3 := o.isLt
    have h2 : k.val < n + 1 := k.isLt
    calc o.val * (n + 1) + k.val < o.val * (n + 1) + (n + 1) := by omega
      _ = (o.val + 1) * (n + 1) := by ring
      _ ≤ (n + 3) * (n + 1) := Nat.mul_le_mul_right _ h1⟩

theorem ubIdx_eq_iff (n : ℕ) (o o' : Fin (n + 3)) (k k' : Fin (n + 1)) :
    ubIdx n o k = ubIdx n o' k' ↔ (o = o' ∧ k = k') := by
  constructor
  · intro h
    have hv : o.val * (n + 1) + k.val = o'.val * (n + 1) + k'.val := congrArg Fin.val h
    have hk : k.val < n + 1 := k.isLt
    have hk' : k'.val < n + 1 := k'.isLt
    have e1 : (o.val * (n + 1) + k.val) % (n + 1) = k.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
    have e2 : (o'.val * (n + 1) + k'.val) % (n + 1) = k'.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk']
    have hkk : k.val = k'.val := by rw [← e1, ← e2, hv]
    have hoo : o.val * (n + 1) = o'.val * (n + 1) := by omega
    exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) hoo), Fin.ext hkk⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem ubIdx_ne_of_not_pathG (n : ℕ) (o o' : Fin (n + 3))
    (h : ¬ Multiway.SteinCluster.pathG (n + 3) o o') (k k' : Fin (n + 1)) :
    ubIdx n o k ≠ ubIdx n o' k' := by
  intro heq
  exact h (((ubIdx_eq_iff n o o' k k').mp heq).1 ▸ Or.inl rfl)

theorem ubIdx_injective (n : ℕ) (o : Fin (n + 3)) : Function.Injective (ubIdx n o) :=
  fun k k' h => ((ubIdx_eq_iff n o o k k').mp h).2

/-- The disturbance `ν_{n,o} = (n+1)^{-1/2}∑_{k≤n}s_{o,k}`, a standardized sum of `n+1`
private fair signs: `E[ν_o⁴] ≤ 3` for every `n`, while `sup_ω|ν_{n,o}(ω)| = √(n+1)`. -/
noncomputable def ubNu (n : ℕ) (o : Fin (n + 3)) (ω : Fin ((n + 3) * (n + 1)) → Bool) : ℝ :=
  shockSum (ubIdx n) o ω / Real.sqrt ((n : ℝ) + 1)

/-- The sharing graph `|o − o'| ≤ 1` is a dependency graph for `ν`. -/
noncomputable def ubDep (n : ℕ) :
    DepGraph (ubNu n) (coins ((n + 3) * (n + 1))) :=
  Multiway.SteinCluster.mapDepGraph
    (shockDep (ubIdx n) (Multiway.SteinCluster.pathG (n + 3)) (fun _ => Or.inl rfl)
      (fun o o' h => by unfold Multiway.SteinCluster.pathG at h ⊢; omega)
      (ubIdx_ne_of_not_pathG n))
    (fun _ x => x / Real.sqrt ((n : ℝ) + 1))
    (fun _ => measurable_id.div_const _)

theorem ubDep_nbhd_card (n : ℕ) (o : Fin (n + 3)) : ((ubDep n).nbhd o).card ≤ 3 := by
  have he : (ubDep n).nbhd o = (Multiway.SteinCluster.pathDep n).nbhd o := by
    ext o'
    rw [DepGraph.mem_nbhd_iff, DepGraph.mem_nbhd_iff]
    exact Iff.rfl
  rw [he]
  exact Multiway.SteinCluster.pathDep_nbhd_card n o

theorem ubNu_apply (n : ℕ) (o : Fin (n + 3)) (ω : Fin ((n + 3) * (n + 1)) → Bool) :
    ubNu n o ω = shockSum (ubIdx n) o ω / Real.sqrt ((n : ℝ) + 1) := rfl

theorem sqrtK_pos (n : ℕ) : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) :=
  Real.sqrt_pos.mpr (by positivity)

theorem one_le_sqrtK (n : ℕ) : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 : Real.sqrt 1 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_one] at h2

theorem abs_ubNu_le (n : ℕ) (o : Fin (n + 3)) (ω : Fin ((n + 3) * (n + 1)) → Bool) :
    |ubNu n o ω| ≤ (n : ℝ) + 1 := by
  have h1 : |shockSum (ubIdx n) o ω| ≤ (Fintype.card (Fin (n + 1)) : ℝ) :=
    abs_shockSum_le (ubIdx n) o ω
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = (n : ℝ) + 1 := by
    simp
  rw [hcard] at h1
  rw [ubNu_apply, abs_div, abs_of_pos (sqrtK_pos n)]
  rw [div_le_iff₀ (sqrtK_pos n)]
  nlinarith [one_le_sqrtK n, h1, abs_nonneg (shockSum (ubIdx n) o ω)]

/-- `E[ν_{n,o}] = 0`. -/
theorem integral_ubNu (n : ℕ) (o : Fin (n + 3)) :
    ∫ ω, ubNu n o ω ∂(coins ((n + 3) * (n + 1))) = 0 := by
  simp only [ubNu_apply]
  rw [integral_div, integral_shockSum (ubIdx n) o, zero_div]

/-- `Ω_n = I`. -/
theorem integral_ubNu_mul (n : ℕ) (o o' : Fin (n + 3)) :
    ∫ ω, ubNu n o ω * ubNu n o' ω ∂(coins ((n + 3) * (n + 1)))
      = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) o o' := by
  classical
  have hKpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hre : ∀ ω, ubNu n o ω * ubNu n o' ω
      = (shockSum (ubIdx n) o ω * shockSum (ubIdx n) o' ω) / ((n : ℝ) + 1) := by
    intro ω
    simp only [ubNu_apply]
    rw [div_mul_div_comm, Real.mul_self_sqrt hKpos.le]
  simp only [hre]
  rw [integral_div,
    integral_shockSum_mul (fun a b k k' h => ((ubIdx_eq_iff n a b k k').mp h).2) o o']
  by_cases h : o = o'
  · subst h
    have hone : ∀ k : Fin (n + 1),
        (if ubIdx n o k = ubIdx n o k then (1 : ℝ) else 0) = 1 := by
      intro k; simp
    rw [Finset.sum_congr rfl (fun k _ => hone k)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Matrix.one_apply_eq]
    push_cast
    field_simp
  · have hzero : ∀ k : Fin (n + 1),
        (if ubIdx n o k = ubIdx n o' k then (1 : ℝ) else 0) = 0 := by
      intro k
      rw [ite_eq_right]
      intro hk
      exact absurd ((ubIdx_eq_iff n o o' k k).mp hk).1 h
    rw [Finset.sum_congr rfl (fun k _ => hzero k), Finset.sum_const_zero, zero_div,
      Matrix.one_apply_ne h]

/-- `E[ν_o⁴] ≤ 3`, by `Multilinear.integral_pow_four_linear_le` with coefficients
`(n+1)^{-1/2}`. -/
theorem integral_ubNu_pow_four_le (n : ℕ) (o : Fin (n + 3)) :
    ∫ ω, (ubNu n o ω) ^ 4 ∂(coins ((n + 3) * (n + 1))) ≤ 3 := by
  classical
  have hKpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set F : Finset (Fin ((n + 3) * (n + 1))) := Finset.univ.image (ubIdx n o) with hF
  have hinjOn : ∀ x ∈ (Finset.univ : Finset (Fin (n + 1))),
      ∀ y ∈ (Finset.univ : Finset (Fin (n + 1))), ubIdx n o x = ubIdx n o y → x = y :=
    fun x _ y _ h => ubIdx_injective n o h
  have hsum : ∀ ω, ubNu n o ω
      = ∑ i ∈ F, (1 / Real.sqrt ((n : ℝ) + 1)) * sign2 i ω := by
    intro ω
    rw [← Finset.mul_sum, hF, Finset.sum_image hinjOn, ubNu_apply, shockSum]
    rw [div_eq_inv_mul, one_div]
  have hcardF : F.card = n + 1 := by
    rw [hF, Finset.card_image_of_injective _ (ubIdx_injective n o), Finset.card_univ,
      Fintype.card_fin]
  have hcoef : ∑ _i ∈ F, (1 / Real.sqrt ((n : ℝ) + 1)) ^ 2 = 1 := by
    rw [Finset.sum_const, hcardF, nsmul_eq_mul, div_pow, one_pow,
      Real.sq_sqrt hKpos.le]
    push_cast
    field_simp
  have hmain := Multiway.Multilinear.integral_pow_four_linear_le
    (μ := coins ((n + 3) * (n + 1))) (ξ := fun i : Fin ((n + 3) * (n + 1)) => sign2 i)
    (a := fun _ => 1 / Real.sqrt ((n : ℝ) + 1)) (B := 1)
    (iIndepFun_sign2 _) measurable_sign2 (fun i => integral_sign2 i)
    (fun i => Filter.Eventually.of_forall
      (fun ω => Multiway.SteinCluster.abs_sign2_le' i ω)) F
  simp only [hcoef] at hmain
  calc ∫ ω, (ubNu n o ω) ^ 4 ∂(coins ((n + 3) * (n + 1)))
      = ∫ ω, (∑ i ∈ F, (1 / Real.sqrt ((n : ℝ) + 1)) * sign2 i ω) ^ 4
        ∂(coins ((n + 3) * (n + 1))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show (ubNu n o ω) ^ 4
          = (∑ i ∈ F, (1 / Real.sqrt ((n : ℝ) + 1)) * sign2 i ω) ^ 4
        rw [hsum ω]
    _ ≤ 3 * (1 : ℝ) ^ 4 * (1 : ℝ) ^ 2 := hmain
    _ = 3 := by norm_num

theorem integrable_ubNu_pow_four (n : ℕ) (o : Fin (n + 3)) :
    Integrable (fun ω => (ubNu n o ω) ^ 4) (coins ((n + 3) * (n + 1))) := by
  refine integrable_of_abs_le (((ubDep n).meas o).pow_const 4)
    (C := ((n : ℝ) + 1) ^ 4) (fun ω => ?_)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_ubNu_le n o ω) 4

/-- At the all-heads realization `ν_{n,o} = √(n+1)`, so the disturbance is not uniformly
bounded in `n`. -/
theorem ubNu_all_true (n : ℕ) (o : Fin (n + 3)) :
    ubNu n o (fun _ => true) = Real.sqrt ((n : ℝ) + 1) := by
  have hs : ∀ i : Fin ((n + 3) * (n + 1)), sign2 i (fun _ => true) = 1 := by
    intro i; simp [sign2]
  have hsum : shockSum (ubIdx n) o (fun _ => true) = (n : ℝ) + 1 := by
    rw [shockSum]
    simp only [hs]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [ubNu_apply, hsum]
  exact Real.div_sqrt

theorem ubNu_unbounded (C : ℝ) :
    ∃ (n : ℕ) (o : Fin (n + 3)) (ω : Fin ((n + 3) * (n + 1)) → Bool), C < ubNu n o ω := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2)
  refine ⟨n, ⟨0, by omega⟩, fun _ => true, ?_⟩
  rw [ubNu_all_true]
  have h1 : C ^ 2 < (n : ℝ) + 1 := by linarith
  have h2 : Real.sqrt (C ^ 2) < Real.sqrt ((n : ℝ) + 1) :=
    Real.sqrt_lt_sqrt (by positivity) h1
  calc C ≤ |C| := le_abs_self C
    _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
    _ < Real.sqrt ((n : ℝ) + 1) := h2

/-- The witness rate at `ε = 1/4`: `δ^{(1/4)}_n = ((n+3)/2)^{1/4}·8/(n+3) → 0`. -/
theorem tendsto_epsRate_witness :
    Tendsto (fun n : ℕ => epsRate (n + 3) 2 ((n : ℝ) + 3) ((1 : ℝ) / 4)) atTop (𝓝 0) := by
  have hf0 : ∀ n : ℕ, 0 ≤ epsRate (n + 3) 2 ((n : ℝ) + 3) ((1 : ℝ) / 4) :=
    fun n => epsRate_nonneg _ _ _ _
  have hf4 : ∀ n : ℕ, (epsRate (n + 3) 2 ((n : ℝ) + 3) ((1 : ℝ) / 4)) ^ 4
      = 2048 / ((n : ℝ) + 3) ^ 3 := by
    intro n
    have hx : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by
      have : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
      rw [this]
      norm_num
      positivity
    have hq : ((((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ ((1 : ℝ) / 4)) ^ 4
        = ((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast ((((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ ((1 : ℝ) / 4)) 4,
        ← Real.rpow_mul hx.le]
      norm_num
    unfold epsRate accumRate
    rw [mul_pow, hq]
    have hc : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hc, h2]
    have hne : (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    ring
  have hg : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (2048 / ((n : ℝ) + 3) ^ 3)))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    have hin : Tendsto (fun n : ℕ => 2048 / ((n : ℝ) + 3) ^ 3) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine squeeze_zero (fun n => by positivity) (fun n => ?_)
        (by simpa using h0.const_mul (2048 : ℝ))
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hge : (n : ℝ) + 1 ≤ ((n : ℝ) + 3) ^ 3 := by
        nlinarith [hn0, mul_nonneg hn0 hn0, mul_nonneg (mul_nonneg hn0 hn0) hn0]
      calc (2048 : ℝ) / ((n : ℝ) + 3) ^ 3 ≤ 2048 / ((n : ℝ) + 1) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hge
        _ = 2048 * ((n : ℝ) + 1)⁻¹ := by
            rw [div_eq_mul_inv]
    exact hc.comp (hc.comp hin)
  refine Tendsto.congr (fun n => ?_) hg
  rw [← hf4 n]
  have hx := hf0 n
  have h4' : (epsRate (n + 3) 2 ((n : ℝ) + 3) ((1 : ℝ) / 4)) ^ 4
      = ((epsRate (n + 3) 2 ((n : ℝ) + 3) ((1 : ℝ) / 4)) ^ 2) ^ 2 := by ring
  rw [h4', Real.sqrt_sq (by positivity), Real.sqrt_sq hx]

end UnboundedWitness

open UnboundedWitness

/-- The hypotheses of `cltcluster_b_general_betaJM_janson` are jointly satisfiable with an
unbounded disturbance at `ε = 1/4`: `n+3` observations, one regressor `x̃_o = 1`, `𝓡_n = I_1`,
`Ω_n = I`, and the non-transitive `J = 2` sharing relation `|o − o'| ≤ 1`. -/
theorem cltcluster_b_general_betaJM_janson_witness (s : ℝ) :
    Tendsto (fun n => ((coins ((n + 3) * (n + 1))).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt (n + 2))
              (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
                  ((redXt (n + 2))ᵀ *ᵥ (fun o => ubNu n o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine cltcluster_b_general_betaJM_janson (O := fun n => Fin (n + 3))
    (fun n => coins ((n + 3) * (n + 1))) (fun n => redXt (n + 2)) (fun n => 1) (fun n => 1)
    ubNu
    (fun n ω => ((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
      ((redXt (n + 2))ᵀ *ᵥ (fun o => ubNu n o ω)))
    (fun _ => 0) ubDep (fun _ _ => by simp)
    (fun n => redXt_scoreMap_isUnit (n + 2)) (fun n => (n : ℝ) + 3) (fun n => by positivity)
    ?_ integral_ubNu_mul integral_ubNu
    1 2 zero_lt_one (by norm_num) ?_ integrable_ubNu_pow_four ?_
    (fun _ => 2) (fun _ => by norm_num) ?_ ?_ ((1 : ℝ) / 4) (by norm_num) ?_
    (fun _ => (1 : ℝ)) ?_ s
  · intro n
    rw [redXt_scoreVar]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · intro _ _
    simp [redXt, dotProduct]
  · intro n o
    refine le_trans (integral_ubNu_pow_four_le n o) ?_
    norm_num
  · intro n
    simp
  · intro n o
    exact le_trans (ubDep_nbhd_card n o) (by norm_num)
  · simpa only [Fintype.card_fin] using tendsto_epsRate_witness
  · simp [dotProduct]

/-- The cluster-shock witness rate at `ε = 1/4`: `Ḡ_n^{3−ε}/n^{1−ε} = 2^{11/4}/(n+3)^{3/4}`,
bounded by `8/√(n+3)`. -/
theorem gc_hGrate_eps :
    Tendsto (fun n : ℕ => (((2 : ℕ) : ℝ)) ^ ((3 : ℝ) - (1 : ℝ) / 4)
      / (((n + 3 : ℕ) : ℝ)) ^ ((1 : ℝ) - (1 : ℝ) / 4)) atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ,
      (((2 : ℕ) : ℝ)) ^ ((3 : ℝ) - (1 : ℝ) / 4) / (((n + 3 : ℕ) : ℝ)) ^ ((1 : ℝ) - (1 : ℝ) / 4)
        ≤ 8 * Real.sqrt (1 / ((n : ℝ) + 1)) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx1 : (1 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by push_cast; linarith
    have hx0 : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hx1
    have hnum : (((2 : ℕ) : ℝ)) ^ ((3 : ℝ) - (1 : ℝ) / 4) ≤ 8 := by
      have h1 : (((2 : ℕ) : ℝ)) ^ ((3 : ℝ) - (1 : ℝ) / 4) ≤ (((2 : ℕ) : ℝ)) ^ ((3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h2 : (((2 : ℕ) : ℝ)) ^ ((3 : ℝ)) = 8 := by
        rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [h2] at h1
      exact h1
    have hden : Real.sqrt (((n + 3 : ℕ) : ℝ))
        ≤ (((n + 3 : ℕ) : ℝ)) ^ ((1 : ℝ) - (1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hsq0 : (0 : ℝ) < Real.sqrt (((n + 3 : ℕ) : ℝ)) := Real.sqrt_pos.mpr hx0
    have hX0 : (0 : ℝ) < (((n + 3 : ℕ) : ℝ)) ^ ((1 : ℝ) - (1 : ℝ) / 4) :=
      Real.rpow_pos_of_pos hx0 _
    have hA0 : (0 : ℝ) ≤ (((2 : ℕ) : ℝ)) ^ ((3 : ℝ) - (1 : ℝ) / 4) :=
      Real.rpow_nonneg (by norm_num) _
    have hstep1 : (((2 : ℕ) : ℝ)) ^ ((3 : ℝ) - (1 : ℝ) / 4)
        / (((n + 3 : ℕ) : ℝ)) ^ ((1 : ℝ) - (1 : ℝ) / 4)
          ≤ 8 / Real.sqrt (((n + 3 : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ hX0 hsq0]
      nlinarith [hnum, hden, hsq0.le, hA0]
    have hstep2 : (8 : ℝ) / Real.sqrt (((n + 3 : ℕ) : ℝ))
        ≤ 8 * Real.sqrt (1 / ((n : ℝ) + 1)) := by
      have he : Real.sqrt (1 / ((n : ℝ) + 1)) = (Real.sqrt ((n : ℝ) + 1))⁻¹ := by
        rw [one_div, Real.sqrt_inv]
      rw [he, ← div_eq_mul_inv]
      have hle : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (((n + 3 : ℕ) : ℝ)) := by
        refine Real.sqrt_le_sqrt ?_
        push_cast
        linarith
      exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (by linarith)) hle
    exact hstep1.trans hstep2
  refine squeeze_zero (fun n => by positivity) hbound ?_
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0)
  have hcomp : Tendsto (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1))) atTop (𝓝 0) :=
    hc.comp h0
  simpa using hcomp.const_mul (8 : ℝ)

/-- The hypotheses of `clustershock_b_general_janson` are jointly satisfiable at `ε = 1/4`,
on the `J = 2` cluster-shock design of `ClusterShock.clustershock_b_general_witness`. -/
theorem clustershock_b_general_janson_witness (s : ℝ) :
    Tendsto (fun n => ((coins (3 * (n + 3))).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt (n + 2))
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => 1) (fun _ => 1))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
                  ((redXt (n + 2))ᵀ *ᵥ (fun o => shockSum (wtIdx n) o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  have habs : ∀ (n : ℕ) (o : Fin (n + 3)) (ω : Fin (3 * (n + 3)) → Bool),
      |shockSum (wtIdx n) o ω| ≤ 3 := by
    intro n o ω
    simpa using abs_shockSum_le (wtIdx n) o ω
  have hpow : ∀ (n : ℕ) (o : Fin (n + 3)) (ω : Fin (3 * (n + 3)) → Bool),
      (shockSum (wtIdx n) o ω) ^ 4 ≤ 3 ^ 4 := by
    intro n o ω
    have h1 : (shockSum (wtIdx n) o ω) ^ 4 = |shockSum (wtIdx n) o ω| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h1]
    exact pow_le_pow_left₀ (abs_nonneg _) (habs n o ω) 4
  have hint4 : ∀ (n : ℕ) (o : Fin (n + 3)),
      Integrable (fun ω => (shockSum (wtIdx n) o ω) ^ 4) (coins (3 * (n + 3))) := by
    intro n o
    refine Multiway.SteinCluster.integrable_of_abs_le
      ((measurable_shockSum (wtIdx n) o).pow_const 4) (C := 3 ^ 4) (fun ω => ?_)
    rw [abs_of_nonneg (by positivity)]
    exact hpow n o ω
  refine clustershock_b_general_janson (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    (fun n => coins (3 * (n + 3))) (fun n => redXt (n + 2)) (fun _ => 1)
    (fun n => shockSum (wtIdx n))
    (fun n ω => ((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
      ((redXt (n + 2))ᵀ *ᵥ (fun o => shockSum (wtIdx n) o ω)))
    (fun _ => 0) wtC Finset.univ wtDep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    (fun n => redXt_scoreMap_isUnit (n + 2))
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => zero_le_one) 1 zero_lt_one (fun _ _ => le_refl 1)
    ?_ (fun n o => integral_shockSum (wtIdx n) o)
    1 3 zero_lt_one (by norm_num) ?_ (fun n o => hint4 n o) ?_
    1 zero_lt_one ?_ (fun n => ⟨⟨0, by omega⟩⟩)
    (fun _ => 2) (fun n j _ γ => wtCluster_card n j γ)
    ((1 : ℝ) / 4) (by norm_num) (by norm_num) ?_ (fun _ => (1 : ℝ)) ?_ s
  · intro n o o'
    rw [integral_shockSum_mul (wtIdx_component n), Multiway.Sharing.clusterOmega_apply,
      Fin.sum_univ_three, Fin.sum_univ_two]
    have e0 : (wtIdx n o 0 = wtIdx n o' 0) ↔ Multiway.SameOn (wtC n) {0} o o' := by
      rw [wtIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_zero_iff]
    have e1 : (wtIdx n o 1 = wtIdx n o' 1) ↔ Multiway.SameOn (wtC n) {1} o o' := by
      rw [wtIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_one_iff]
    have e2 : (wtIdx n o 2 = wtIdx n o' 2) ↔ (o = o') := by
      rw [wtIdx_eq_iff, wtLab_eq_two_iff]
    rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  · intro _ _
    simp [redXt, dotProduct]
  · intro n o
    calc ∫ ω, (shockSum (wtIdx n) o ω) ^ 4 ∂(coins (3 * (n + 3)))
        ≤ ∫ _ω, (3 : ℝ) ^ 4 ∂(coins (3 * (n + 3))) :=
          integral_mono (hint4 n o) (integrable_const _) (fun ω => hpow n o ω)
      _ = 3 ^ 4 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  · intro n
    simp only [Fintype.card_fin]
    rw [redXt_transpose_mul_self]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · simp only [Fintype.card_fin]
    exact gc_hGrate_eps
  · simp [dotProduct]

end PartBWitness

/-! ### Positivity of `ψ_n` from the standardization

`ψ_n > 0` follows from `∫X_{n,o}⁴ ≤ ψ_n⁴` and `∫(∑_oX_{n,o})² = 1`, so the theorems below hold
under `0 ≤ B` and `0 ≤ C₄`. -/

section NonnegConstants

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- If `∫X_o⁴ ≤ ψ⁴` for every `o` and `∫(∑_oX_o)² = 1`, then `ψ > 0`. -/
theorem psi_pos_of_total_variance {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ} {p : ℝ} (hp : 0 ≤ p)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ p ^ 4)
    (hvar : ∫ ω, (depSum X ω) ^ 2 ∂μ = 1) : 0 < p := by
  rcases hp.lt_or_eq with h | h
  · exact h
  · exfalso
    have hp0 : p = 0 := h.symm
    have hzero : ∀ o : ι, ∀ᵐ ω ∂μ, X o ω = 0 := by
      intro o
      have hnn : (0 : Ω → ℝ) ≤ fun ω => (X o ω) ^ 4 := fun ω => by positivity
      have hle : ∫ ω, (X o ω) ^ 4 ∂μ ≤ 0 := by
        have h4 := hfour o
        rw [hp0] at h4
        simpa using h4
      have hge : (0 : ℝ) ≤ ∫ ω, (X o ω) ^ 4 ∂μ := integral_nonneg fun ω => by positivity
      have heq : ∫ ω, (X o ω) ^ 4 ∂μ = 0 := le_antisymm hle hge
      have hae := (integral_eq_zero_iff_of_nonneg hnn (hint4 o)).1 heq
      filter_upwards [hae] with ω hω
      have h4 : (X o ω) ^ 4 = 0 := hω
      exact pow_eq_zero_iff (n := 4) (by norm_num) |>.1 h4
    have hsum : ∀ᵐ ω ∂μ, depSum X ω = 0 := by
      filter_upwards [ae_all_iff.2 hzero] with ω hω
      exact Finset.sum_eq_zero fun o _ => hω o
    have hz : ∫ ω, (depSum X ω) ^ 2 ∂μ = ∫ _ω, (0 : ℝ) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hsum] with ω hω
      rw [hω]
      ring
    rw [hz, integral_zero] at hvar
    exact zero_ne_one hvar

/-- `ψ_n := BC₄λ_min(Ω_n)^{-1/2} > 0` on the score array, under `0 ≤ B` and `0 ≤ C₄`. -/
theorem scoreArray_psi_pos {O K rr W : Type*} [Fintype O] [Fintype K] [DecidableEq K]
    [Fintype rr] [DecidableEq rr] [MeasurableSpace W] {μ : Measure W} [IsProbabilityMeasure μ]
    {Xt : Matrix O K ℝ} {Om : Matrix O O ℝ} {Rn : Matrix rr K ℝ}
    (hPD : (scoreVar Xt Om).PosDef) (hA : Function.Injective (scoreMap Xt Rn).mulVec)
    {lmin : ℝ} (hlmin : 0 < lmin) (hfloor : lmin • (1 : Matrix K K ℝ) ≤ scoreVar Xt Om)
    {B C4 : ℝ} (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hB : ∀ o, (fun k => Xt o k) ⬝ᵥ (fun k => Xt o k) ≤ B ^ 2)
    {v : O → W → ℝ} (hmeas : ∀ o, Measurable (v o))
    (hint4 : ∀ o, Integrable (fun ω => (v o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (v o ω) ^ 4 ∂μ ≤ C4 ^ 4)
    (hOm : ∀ o o', ∫ ω, v o ω * v o' ω ∂μ = Om o o')
    {b : rr → ℝ} (hb : b ⬝ᵥ b = 1) :
    0 < B * C4 / Real.sqrt lmin :=
  psi_pos_of_total_variance (div_nonneg (mul_nonneg hB0 hC40) (Real.sqrt_nonneg _))
    (fun o => integrable_scoreArray_pow_four hint4 Xt _ o)
    (fun o => integral_scoreArray_pow_four_le hPD hA hlmin hfloor hB0 hC40 hB hint4 hfour hb o)
    (integral_depSum_scoreArray_sq_eq_one_moment hPD hA hmeas hint4 hOm hb)

end NonnegConstants
/-! ### Part (b) at `0 ≤ B` and `0 ≤ C₄` -/

section PartBNonneg

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Theorem 5(b) for `β̂_JM` at general `J`**, at `0 ≤ B`, `0 ≤ C₄`. -/
theorem cltcluster_b_general_betaJM_janson_nonneg
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n) (Om n))
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n) = Om n o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂(μ n) ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (ε : ℝ) (hε : 0 < ε)
    (hrate : Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n) (lmin n) ε) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  have hPD : ∀ n, (scoreVar (Xt n) (Om n)).PosDef := fun n =>
    Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlmin n)) (hfloor n)
  have hstat : ∀ n, (fun ω => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n ω - β n))))
      = depSum (scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) := by
    intro n
    funext ω
    rw [hscore n ω]
    exact dotProduct_standardized_eq_depSum (Xt n) (Om n) (Rn n) b (ν n) ω
  simp only [hstat]
  refine cltcluster_b_general_janson μ
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * C4 / Real.sqrt (lmin n)) Dn ε hε
    (fun n => scoreArray_psi_pos (hPD n) (hA n) (hlmin n) (hfloor n) hB0 hC40 (hB n)
      (fun o => (Dv n).meas o) (hint4 n) (hfour n) (hOm n) hb) ?_ ?_ ?_ hDn1 hDnN
    ?_ ?_ ?_ s
  · exact fun n o => integrable_scoreArray_pow_four (hint4 n) (Xt n) _ o
  · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hA n) (hlmin n) (hfloor n)
      hB0 hC40 (hB n) (hint4 n) (hfour n) hb o
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hint4 n) (hOm n) hb
  · refine squeeze_zero (fun n => ?_) (fun n => ?_)
      (by simpa using hrate.const_mul (8 * B ^ 4 * C4 ^ 4))
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
    · exact epsFirstRate_le (hDn1 n) (hlmin n)

/-- The same for a constant family, as convergence in distribution. -/
theorem cltcluster_b_general_betaJM_janson_const_nonneg
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : Type*} [mW : MeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W → ℝ) (bhat : ℕ → W → (K → ℝ)) (β : ℕ → K → ℝ)
    (Dv : ∀ n, DepGraph (ν n) μ)
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n) (Om n))
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂μ = Om n o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂μ = 0)
    (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) μ)
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂μ ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (ε : ℝ) (hε : 0 < ε)
    (hrate : Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n) (lmin n) ε) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) :
    TendstoInDistribution (m := fun _ : ℕ => mW)
      (fun n ω => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n ω - β n)))) atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 1) := by
  have hPD : ∀ n, (scoreVar (Xt n) (Om n)).PosDef := fun n =>
    Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlmin n)) (hfloor n)
  have hstat : ∀ n, (fun ω => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n ω - β n))))
      = depSum (scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) := by
    intro n
    funext ω
    rw [hscore n ω]
    exact dotProduct_standardized_eq_depSum (Xt n) (Om n) (Rn n) b (ν n) ω
  have hfun : (fun (n : ℕ) (ω : W) => b ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun n => depSum (scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) :=
    funext hstat
  rw [hfun]
  refine cltcluster_b_general_janson_tendstoInDistribution (Ω := fun _ => W) (fun _ => μ)
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * C4 / Real.sqrt (lmin n)) Dn ε hε
    (fun n => scoreArray_psi_pos (hPD n) (hA n) (hlmin n) (hfloor n) hB0 hC40 (hB n)
      (fun o => (Dv n).meas o) (hint4 n) (hfour n) (hOm n) hb) ?_ ?_ ?_ hDn1 hDnN
    ?_ ?_ ?_
  · exact fun n o => integrable_scoreArray_pow_four (hint4 n) (Xt n) _ o
  · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hA n) (hlmin n) (hfloor n)
      hB0 hC40 (hB n) (hint4 n) (hfour n) hb o
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hint4 n) (hOm n) hb
  · refine squeeze_zero (fun n => ?_) (fun n => ?_)
      (by simpa using hrate.const_mul (8 * B ^ 4 * C4 ^ 4))
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
    · exact epsFirstRate_le (hDn1 n) (hlmin n)

/-- Cramér–Wold for part (b) in the conditional frame, at `0 ≤ B` and `0 ≤ C₄`. -/
theorem cltcluster_b_general_betaJM_janson_vector_nonneg
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    {W : Type*} [mW : MeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → W → ℝ) (bhat : ℕ → W → (K → ℝ)) (β : ℕ → K → ℝ)
    (Dv : ∀ n, DepGraph (ν n) μ)
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n) (Om n))
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂μ = Om n o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂μ = 0)
    (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) μ)
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂μ ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (ε : ℝ) (hε : 0 < ε)
    (hrate : Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n) (lmin n) ε) atTop (𝓝 0))
    (hWvm : ∀ n, Measurable fun ω =>
      restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n)) :
    TendstoInDistribution (m := fun _ : ℕ => mW)
      (fun n ω => restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => μ)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  refine tendstoInDistribution_stdGaussian_of_unit_directions
    (fun n => (hWvm n).aemeasurable) fun b hb => ?_
  have hs : ∀ n, (fun ω => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun ω => ⟪restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n), b⟫ :=
    fun n => funext fun ω => (inner_restrictedStat (Xt n) (Om n) (Rn n) _ b).symm
  have h := cltcluster_b_general_betaJM_janson_const_nonneg μ Xt Om Rn ν bhat β Dv hscore hA
    lmin hlmin hfloor hOm hmean B C4 hB0 hC40 hB hint4 hfour Dn hDn1 hDnN hdeg ε hε hrate
    (WithLp.ofLp b) (dotProduct_self_ofLp b hb)
  have hfun : (fun (n : ℕ) (ω : W) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun (n : ℕ) (ω : W) =>
        ⟪restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Theorem 5(b) under `P`** with a random design, at `0 ≤ B`, `0 ≤ C₄`. -/
theorem cltcluster_b_general_betaJM_janson_unconditional_nonneg
    {r : Type*} [Fintype r] [DecidableEq r]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1)
    (hWm : ∀ n, Measurable fun y =>
      b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n))))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  refine cltcluster_a_unconditional_of_frozen_stat h𝒟 P (W := fun n y =>
      b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n)))) hWm
    (Wfr := fun ω n => depSum (scoreArray (Xt n ω)
      (steinWeight (Xt n ω) (Om n ω) (Rn n) b) (ν n))) ?_ ?_
  · filter_upwards [ae_ae_eq_frozen_design h𝒟 P hXtD hOmD] with ω hω n
    filter_upwards [hω n] with y hy
    show b ⬝ᵥ _ = _
    rw [hscore n y, dotProduct_standardized_eq_depSum, hy.1, hy.2]
  · filter_upwards [hdep, hA, hlmin, hfloor, hOmeq, hmean, hB, hint4, hfour, hDn1, hDnN, hrate]
      with ω hdepω hAω hlminω hfloorω hOmω hmeanω hBω hint4ω hfourω hDn1ω hDnNω hrateω
    obtain ⟨Dv, hdegω⟩ := hdepω
    have hPD : ∀ n, (scoreVar (Xt n ω) (Om n ω)).PosDef := fun n =>
      Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlminω n)) (hfloorω n)
    refine cltcluster_b_general_janson_tendstoInDistribution
      (Ω := fun _ => Ω) (fun _ => condExpKernel P 𝒟 ω)
      (fun n => scoreArray (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b) (ν n))
      (fun n => scoreArrayDepGraph (Dv n) (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b))
      (fun n => B * C4 / Real.sqrt (lmin n ω)) (fun n => Dn n ω) ε hε
      (fun n => scoreArray_psi_pos (hPD n) (hAω n) (hlminω n) (hfloorω n) hB0 hC40 (hBω n)
        (fun o => (Dv n).meas o) (hint4ω n) (hfourω n) (hOmω n) hb) ?_ ?_ ?_
      hDn1ω hDnNω ?_ ?_ ?_
    · exact fun n o => integrable_scoreArray_pow_four (hint4ω n) (Xt n ω) _ o
    · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hAω n) (hlminω n) (hfloorω n)
        hB0 hC40 (hBω n) (hint4ω n) (hfourω n) hb o
    · intro n o
      rw [nbhd_scoreArrayDepGraph]
      exact hdegω n o
    · exact fun n o => integral_scoreArray (fun o => hmeanω n o) (Xt n ω) _ o
    · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hAω n)
        (fun o => (Dv n).meas o) (hint4ω n) (hOmω n) hb
    · refine squeeze_zero (fun n => ?_) (fun n => ?_)
        (by simpa using hrateω.const_mul (8 * B ^ 4 * C4 ^ 4))
      · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
      · exact epsFirstRate_le (hDn1ω n) (hlminω n)

/-- **Theorem 5(b), vector form**, at `0 ≤ B` and `0 ≤ C₄`. -/
theorem cltcluster_b_general_betaJM_janson_unconditional_vector_nonneg
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hWvm : ∀ n, Measurable fun y =>
      restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  refine tendstoInDistribution_stdGaussian_of_unit_directions
    (fun n => (hWvm n).aemeasurable) fun b hb => ?_
  have hs : ∀ n, (fun y => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))))
      = fun y => ⟪restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n), b⟫ :=
    fun n => funext fun y => (inner_restrictedStat (Xt n y) (Om n y) (Rn n) _ b).symm
  have hWm : ∀ n, Measurable fun y => (WithLp.ofLp b) ⬝ᵥ
      ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))) := by
    intro n
    rw [hs n]
    exact (by fun_prop : Measurable fun v : EuclideanSpace ℝ rr => ⟪v, b⟫).comp (hWvm n)
  have h := cltcluster_b_general_betaJM_janson_unconditional_nonneg h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B C4 hB0 hC40 (WithLp.ofLp b)
    (dotProduct_self_ofLp b hb) hWm hdep hA hlmin hfloor hOmeq hmean hB hint4 hfour
    hDn1 hDnN ε hε hrate
  have hfun : (fun (n : ℕ) (y : Ω) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))))
      = fun (n : ℕ) (y : Ω) =>
        ⟪restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

end PartBNonneg

section PartBClustershockNonneg

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Dm : Type*} [DecidableEq Dm]
variable {L : ℕ → Type*} [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Corollary SM.D.3, second sentence**, at `0 ≤ B` and `0 ≤ C₄`. -/
theorem clustershock_b_general_janson_nonneg
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n) dims o o')
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (sc : ℕ → Dm → ℝ) (ve : ∀ n, O n → ℝ) (hsc : ∀ n, ∀ j ∈ dims, 0 ≤ sc n j)
    (s2 : ℝ) (hs2 : 0 < s2) (hve : ∀ n o, s2 ≤ ve n o)
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n)
      = Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n) o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂(μ n) ≤ C4 ^ 4)
    (θ : ℝ) (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (ε : ℝ) (hε : 0 < ε) (hε3 : ε ≤ 3)
    (hGrate : Tendsto (fun n => (Gb n : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n)
              (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  have hfloorOm : ∀ n, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n) :=
    fun n => Multiway.Sharing.smul_one_le_clusterOmega (hsc n) (hve n)
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hfloorK : ∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n) (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) := by
    intro n
    have h1 : s2 • ((θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ))
        ≤ s2 • ((Xt n)ᵀ * Xt n) := Multiway.loewner_smul_le_smul hs2.le (hdesign n)
    rw [smul_smul, ← mul_assoc] at h1
    exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj (hfloorOm n) (Xt n))
  have hnbhd : ∀ n o, (Dv n).nbhd o = Multiway.Sharing.closedNbhd (c n) dims o := by
    intro n o
    ext o'
    rw [DepGraph.mem_nbhd_iff, Multiway.Sharing.mem_closedNbhd]
    exact hshare n o o'
  set Dn : ℕ → ℕ := fun n => min (dims.card * Gb n) (Fintype.card (O n)) with hDndef
  have hdegF : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n := by
    intro n o
    refine le_min ?_ ?_
    · rw [hnbhd n o]; exact card_closedNbhd_le_mul (hGb n) o
    · exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  have hDn1 : ∀ n, 1 ≤ Dn n := by
    intro n
    obtain ⟨o⟩ := hne n
    refine le_trans ?_ (hdegF n o)
    exact Finset.card_pos.mpr ⟨o, (Dv n).self_mem_nbhd o⟩
  refine cltcluster_b_general_betaJM_janson_nonneg μ Xt
    (fun n => Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) Rn ν bhat β Dv hscore hA
    (fun n => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n => mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n)) hfloorK hOm hmean
    B C4 hB0 hC40 hB hint4 hfour Dn hDn1 (fun n => min_le_right _ _)
    (fun n o => le_trans (hdegF n o) (Nat.le_succ _)) ε hε ?_ b hb s
  exact tendsto_epsRate_of_cluster_size (mul_pos hs2 hθ) hε3 (fun n => hcard n) hDn1
    (fun n => min_le_left _ _) hGrate

end PartBClustershockNonneg
/-! ### Part (b) with the measurability, score and rank hypotheses discharged

The measurability results of `Multiway/ClusterJanson.lean` (`meas_of_ae_depGraph`,
`measurable_score_of_hscore`, `measurable_standardized_comp`, `measurable_restrictedStat_comp`)
apply unchanged. -/

section PartBDischarged

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Theorem 5(b) under `P`**, with `hWm` discharged, at `0 ≤ B`, `0 ≤ C₄`. -/
theorem cltcluster_b_general_betaJM_janson_unconditional_of_dep
    {r : Type*} [Fintype r] [DecidableEq r]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  have hXtm : ∀ n, Measurable (Xt n) := fun n => measurable_of_entrywise_D h𝒟 (hXtD n)
  have hOmm : ∀ n, Measurable (Om n) := fun n => measurable_of_entrywise_D h𝒟 (hOmD n)
  have hdm := measurable_score_of_hscore hXtm (meas_of_ae_depGraph hdep) hscore
  exact cltcluster_b_general_betaJM_janson_unconditional_nonneg h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B C4 hB0 hC40 b hb
    (fun n => measurable_standardized_comp (Rn n) (hXtm n) (hOmm n) (hdm n) b)
    hdep hA hlmin hfloor hOmeq hmean hB hint4 hfour hDn1 hDnN ε hε hrate

/-- **Theorem 5(b), vector form**, with `hWm` and `hWvm` discharged. -/
theorem cltcluster_b_general_betaJM_janson_unconditional_vector_of_dep
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hXtm : ∀ n, Measurable (Xt n) := fun n => measurable_of_entrywise_D h𝒟 (hXtD n)
  have hOmm : ∀ n, Measurable (Om n) := fun n => measurable_of_entrywise_D h𝒟 (hOmD n)
  have hdm := measurable_score_of_hscore hXtm (meas_of_ae_depGraph hdep) hscore
  exact cltcluster_b_general_betaJM_janson_unconditional_vector_nonneg h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B C4 hB0 hC40
    (fun n => measurable_restrictedStat_comp (Rn n) (hXtm n) (hOmm n) (hdm n))
    hdep hA hlmin hfloor hOmeq hmean hB hint4 hfour hDn1 hDnN ε hε hrate

end PartBDischarged

section PartBScoreDischarge

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
variable {Dm : Type*} [Fintype Dm]

/-- **Theorem 5(b)** with `hscore`, `hA` and `hOm` discharged, via
`SteinCluster.score_and_rank_of_jm` and `Ω_n := SteinCluster.secondMoment (μ n) (ν n)`. -/
theorem cltcluster_b_general_betaJM_janson_of_jm
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    {Sm : ∀ n, Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n)} (Xt : ∀ n, Matrix (O n) K ℝ)
    (hwithin : ∀ n, IsWithinMatrix (⨆ k, Sm n k) (Xop n) (Xt n))
    (hid : ∀ n, Multiway.Identified (⨆ k, Sm n k) (Xop n))
    {iota : ∀ n, EuclideanSpace ℝ (O n)} (hiota : ∀ n, iota n ∈ (⨆ k, Sm n k))
    {fe : ∀ n, Dm → EuclideanSpace ℝ (O n)} (hfe : ∀ n m, fe n m ∈ Sm n m)
    {yv : ∀ n, W n → EuclideanSpace ℝ (O n)}
    (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (hmodel : ∀ n ω, yv n ω
      = Xop n (β n) + (∑ m, fe n m) + WithLp.toLp 2 (fun o => ν n o ω))
    (hJM : ∀ n ω, Multiway.IsAugSlope
      (Multiway.jmControls (iota n) (⨆ k, Sm n k) (Xop n)) (Xop n) (yv n ω) (bhat n ω))
    (hR : ∀ n, Function.Injective ((Rn n)ᵀ).mulVec)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n) (secondMoment (μ n) (ν n)))
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂(μ n) ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (ε : ℝ) (hε : 0 < ε)
    (hrate : Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n) (lmin n) ε) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (secondMoment (μ n) (ν n)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  obtain ⟨hscore, hA⟩ :=
    score_and_rank_of_jm hwithin hid hiota hfe hmodel hJM (Rn := Rn) hR
  exact cltcluster_b_general_betaJM_janson_nonneg μ Xt (fun n => secondMoment (μ n) (ν n)) Rn
    ν bhat β Dv hscore hA lmin hlmin hfloor (fun n => secondMoment_spec (μ n) (ν n)) hmean
    B C4 hB0 hC40 hB hint4 hfour Dn hDn1 hDnN hdeg ε hε hrate b hb s

end PartBScoreDischarge
/-! ### Theorem 5(b) with a random restriction matrix

`𝓡_n` is random, `𝒟`-measurable and of full row rank almost surely, and the score equation and
`hA` are derived. The freezing and measurability results of `Multiway/ClusterJanson.lean` apply
unchanged. -/

section PartBRandomRestriction

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Theorem 5(b) under `P`** with `𝓡_n` random and `𝒟`-measurable. -/
theorem cltcluster_b_general_betaJM_janson_unconditional_randomR
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rv : ℕ → Ω → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hRD : ∀ n i k, Measurable[𝒟] fun ω => Rv n ω i k)
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (b : rr → ℝ) (hb : b ⬝ᵥ b = 1)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rv n ω)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rv n y)))⁻¹ *ᵥ
        (Rv n y *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  have hXtm : ∀ n, Measurable (Xt n) := fun n => measurable_of_entrywise_D h𝒟 (hXtD n)
  have hOmm : ∀ n, Measurable (Om n) := fun n => measurable_of_entrywise_D h𝒟 (hOmD n)
  have hRm : ∀ n, Measurable (Rv n) := fun n => measurable_of_entrywise_D h𝒟 (hRD n)
  have hdm := measurable_score_of_hscore hXtm (meas_of_ae_depGraph hdep) hscore
  refine cltcluster_a_unconditional_of_frozen_stat h𝒟 P (W := fun n y =>
      b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rv n y)))⁻¹ *ᵥ
        (Rv n y *ᵥ (bhat n y - β n))))
    (fun n => measurable_standardized_comp_rand (hXtm n) (hOmm n) (hRm n) (hdm n) b)
    (Wfr := fun ω n => depSum (scoreArray (Xt n ω)
      (steinWeight (Xt n ω) (Om n ω) (Rv n ω) b) (ν n))) ?_ ?_
  · filter_upwards [ae_ae_eq_frozen_restriction h𝒟 P hXtD hOmD hRD] with ω hω n
    filter_upwards [hω n] with y hy
    show b ⬝ᵥ _ = _
    rw [hscore n y, dotProduct_standardized_eq_depSum, hy.1, hy.2.1, hy.2.2]
  · filter_upwards [hdep, hA, hlmin, hfloor, hOmeq, hmean, hB, hint4, hfour, hDn1, hDnN, hrate]
      with ω hdepω hAω hlminω hfloorω hOmω hmeanω hBω hint4ω hfourω hDn1ω hDnNω hrateω
    obtain ⟨Dv, hdegω⟩ := hdepω
    have hPD : ∀ n, (scoreVar (Xt n ω) (Om n ω)).PosDef := fun n =>
      Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlminω n)) (hfloorω n)
    refine cltcluster_b_general_janson_tendstoInDistribution
      (Ω := fun _ => Ω) (fun _ => condExpKernel P 𝒟 ω)
      (fun n => scoreArray (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rv n ω) b) (ν n))
      (fun n => scoreArrayDepGraph (Dv n) (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rv n ω) b))
      (fun n => B * C4 / Real.sqrt (lmin n ω)) (fun n => Dn n ω) ε hε
      (fun n => scoreArray_psi_pos (hPD n) (hAω n) (hlminω n) (hfloorω n) hB0 hC40 (hBω n)
        (fun o => (Dv n).meas o) (hint4ω n) (hfourω n) (hOmω n) hb) ?_ ?_ ?_
      hDn1ω hDnNω ?_ ?_ ?_
    · exact fun n o => integrable_scoreArray_pow_four (hint4ω n) (Xt n ω) _ o
    · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hAω n) (hlminω n) (hfloorω n)
        hB0 hC40 (hBω n) (hint4ω n) (hfourω n) hb o
    · intro n o
      rw [nbhd_scoreArrayDepGraph]
      exact hdegω n o
    · exact fun n o => integral_scoreArray (fun o => hmeanω n o) (Xt n ω) _ o
    · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hAω n)
        (fun o => (Dv n).meas o) (hint4ω n) (hOmω n) hb
    · refine squeeze_zero (fun n => ?_) (fun n => ?_)
        (by simpa using hrateω.const_mul (8 * B ^ 4 * C4 ^ 4))
      · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
      · exact epsFirstRate_le (hDn1ω n) (hlminω n)

/-- **Theorem 5(b), vector form**, with `𝓡_n` random. -/
theorem cltcluster_b_general_betaJM_janson_unconditional_vector_randomR
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rv : ℕ → Ω → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hRD : ∀ n i k, Measurable[𝒟] fun ω => Rv n ω i k)
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rv n ω)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y) (Om n y) (Rv n y) (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hXtm : ∀ n, Measurable (Xt n) := fun n => measurable_of_entrywise_D h𝒟 (hXtD n)
  have hOmm : ∀ n, Measurable (Om n) := fun n => measurable_of_entrywise_D h𝒟 (hOmD n)
  have hRm : ∀ n, Measurable (Rv n) := fun n => measurable_of_entrywise_D h𝒟 (hRD n)
  have hdm := measurable_score_of_hscore hXtm (meas_of_ae_depGraph hdep) hscore
  refine tendstoInDistribution_stdGaussian_of_unit_directions
    (fun n => (measurable_restrictedStat_comp_rand (hXtm n) (hOmm n) (hRm n) (hdm n)).aemeasurable)
    fun b hb => ?_
  have hs : ∀ n, (fun y => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rv n y)))⁻¹ *ᵥ (Rv n y *ᵥ (bhat n y - β n))))
      = fun y => ⟪restrictedStat (Xt n y) (Om n y) (Rv n y) (bhat n y - β n), b⟫ :=
    fun n => funext fun y => (inner_restrictedStat (Xt n y) (Om n y) (Rv n y) _ b).symm
  have h := cltcluster_b_general_betaJM_janson_unconditional_randomR h𝒟 P Xt Om Rv ν bhat β
    hXtD hOmD hRD hscore lmin Dn B C4 hB0 hC40 (WithLp.ofLp b)
    (dotProduct_self_ofLp b hb) hdep hA hlmin hfloor hOmeq hmean hB hint4 hfour
    hDn1 hDnN ε hε hrate
  have hfun : (fun (n : ℕ) (y : Ω) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rv n y)))⁻¹ *ᵥ
          (Rv n y *ᵥ (bhat n y - β n))))
      = fun (n : ℕ) (y : Ω) =>
        ⟪restrictedStat (Xt n y) (Om n y) (Rv n y) (bhat n y - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

end PartBRandomRestriction

section PartBPrinted

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {Dm : Type*} [Fintype Dm]

/-- **Theorem 5(b).** If the fourth-moment assumption holds and `(n/D_n)^ε δ_n ⟶^p 0` for some
`ε > 0`, then `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)`, with `𝓡_n` random, `𝒟`-measurable and of
full row rank almost surely. -/
theorem cltcluster_b_general_betaJM_janson_printed
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    {Sm : ∀ n, Ω → Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, Ω → ((K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n))}
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rv : ℕ → Ω → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hwithin : ∀ n y, IsWithinMatrix (⨆ k, Sm n y k) (Xop n y) (Xt n y))
    (hid : ∀ n y, Multiway.Identified (⨆ k, Sm n y k) (Xop n y))
    {iota : ∀ n, Ω → EuclideanSpace ℝ (O n)} (hiota : ∀ n y, iota n y ∈ (⨆ k, Sm n y k))
    {fe : ∀ n, Ω → Dm → EuclideanSpace ℝ (O n)} (hfe : ∀ n y m, fe n y m ∈ Sm n y m)
    {yv : ∀ n, Ω → EuclideanSpace ℝ (O n)}
    (hmodel : ∀ n y, yv n y
      = Xop n y (β n) + (∑ m, fe n y m) + WithLp.toLp 2 (fun o => ν n o y))
    (hJM : ∀ n y, Multiway.IsAugSlope
      (Multiway.jmControls (iota n y) (⨆ k, Sm n y k) (Xop n y)) (Xop n y) (yv n y) (bhat n y))
    (hR : ∀ᵐ ω ∂P, ∀ n, Function.Injective ((Rv n ω)ᵀ).mulVec)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hRD : ∀ n i k, Measurable[𝒟] fun ω => Rv n ω i k)
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B C4 : ℝ) (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o,
      Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => epsRate (Fintype.card (O n)) (Dn n ω) (lmin n ω) ε) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y) (Om n y) (Rv n y) (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rv n ω)).mulVec := by
    filter_upwards [hR] with ω hRω n
    exact injective_scoreMap_mulVec
      (isUnit_det_gram_of_identified (hwithin n ω) (hid n ω)) (hRω n)
  exact cltcluster_b_general_betaJM_janson_unconditional_vector_randomR h𝒟 P Xt Om Rv ν bhat β
    hXtD hOmD hRD (score_of_jm_random hwithin hid hiota hfe hmodel hJM)
    lmin Dn B C4 hB0 hC40 hdep hA hlmin hfloor hOmeq hmean hB hint4 hfour hDn1 hDnN ε hε hrate

end PartBPrinted
end Multiway.ClusterJanson
