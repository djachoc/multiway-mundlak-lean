import Multiway.Cgm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The limit clause of Lemma SM.B.8(b)

This file formalizes the final clause of Lemma SM.B.8(b) of the paper (the multiway
cluster-robust estimator under absorbed clustering): `‖Ξ_n‖/n → 0` whenever
`(d_[Δ] - N_m + K) G^{(m)}_max = o(n)` and `d_[Δ]/n → 0`.

The finite-sample bound `Cgm.xiMat_opNorm_le`, read at sample size `k`, is an inequality between
real numbers, so the limit statement is proved for arbitrary real sequences satisfying it, with
`Xi k = ‖Ξ_k‖`, `dA k = d_[Δ] - N_m`, `dL k = K`, `tPi k = d_[Δ] + K`, `Gmax k = G^{(m)}_max`
and `card k = n`. The key step is the identity `√(d·(G·n))/n = √(d·G/n)`.

## Main results

* `sqrt_div_eq`: `√(d·(G·n))/n = √(d·G/n)` for `n > 0`.
* `xi_div_card_tendsto_zero`: the limit clause.
* `xi_div_card_tendsto_zero_witness`: the hypotheses hold jointly with `Xi k → ∞`.
-/

namespace Multiway
namespace CgmLimit

open Filter Topology

/-- `√(d·(G·n))/n = √(d·G/n)` for `n > 0`. -/
theorem sqrt_div_eq {d G n : ℝ} (hn : 0 < n) :
    Real.sqrt (d * (G * n)) / n = Real.sqrt (d * G / n) := by
  have hn' : n ≠ 0 := hn.ne'
  have hsq : Real.sqrt (d * (G * n)) = n * Real.sqrt (d * G / n) := by
    conv_lhs => rw [show d * (G * n) = n ^ 2 * (d * G / n) by field_simp]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hn.le]
  rw [hsq, mul_comm, mul_div_assoc, div_self hn', mul_one]

/-- **Lemma SM.B.8(b), limit clause.** `‖Ξ_n‖/n → 0` whenever
`(d_[Δ]-N_m+K)G^{(m)}_max = o(n)` and `(d_[Δ]+K)/n → 0`. The hypothesis `hbound` is the bound
`Cgm.xiMat_opNorm_le` at sample size `k`; `B` bounds the regressors and enters only through `B²`. -/
theorem xi_div_card_tendsto_zero {B : ℝ} {Xi dA dL tPi Gmax card : ℕ → ℝ}
    (hXi0 : ∀ k, 0 ≤ Xi k) (hcard : ∀ k, 0 < card k)
    (hdA : ∀ k, 0 ≤ dA k) (hdL : ∀ k, 0 ≤ dL k) (hG : ∀ k, 0 ≤ Gmax k)
    (hbound : ∀ k, Xi k ≤ B ^ 2 * (Real.sqrt (dA k * (Gmax k * card k))
      + Real.sqrt (dL k * (Gmax k * card k)) + tPi k))
    (hsum : Tendsto (fun k => (dA k + dL k) * Gmax k / card k) atTop (𝓝 0))
    (hPi : Tendsto (fun k => tPi k / card k) atTop (𝓝 0)) :
    Tendsto (fun k => Xi k / card k) atTop (𝓝 0) := by
  -- the two summands of `hsum`, separated
  have hA0 : Tendsto (fun k => dA k * Gmax k / card k) atTop (𝓝 0) := by
    refine squeeze_zero
      (fun k => div_nonneg (mul_nonneg (hdA k) (hG k)) (hcard k).le) (fun k => ?_) hsum
    have h1 := hdL k
    have h2 := hG k
    have h3 := hcard k
    gcongr
    linarith
  have hL0 : Tendsto (fun k => dL k * Gmax k / card k) atTop (𝓝 0) := by
    refine squeeze_zero
      (fun k => div_nonneg (mul_nonneg (hdL k) (hG k)) (hcard k).le) (fun k => ?_) hsum
    have h1 := hdA k
    have h2 := hG k
    have h3 := hcard k
    gcongr
    linarith
  -- their square roots
  have hsA : Tendsto (fun k => Real.sqrt (dA k * Gmax k / card k)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hA0
    rwa [Real.sqrt_zero] at h
  have hsL : Tendsto (fun k => Real.sqrt (dL k * Gmax k / card k)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hL0
    rwa [Real.sqrt_zero] at h
  -- the divided bound
  have hdivbound : ∀ k, Xi k / card k
      ≤ B ^ 2 * (Real.sqrt (dA k * Gmax k / card k)
        + Real.sqrt (dL k * Gmax k / card k) + tPi k / card k) := by
    intro k
    have hc := hcard k
    have h := div_le_div_of_nonneg_right (c := card k) (hbound k) hc.le
    calc Xi k / card k
        ≤ B ^ 2 * (Real.sqrt (dA k * (Gmax k * card k))
            + Real.sqrt (dL k * (Gmax k * card k)) + tPi k) / card k := h
      _ = B ^ 2 * (Real.sqrt (dA k * (Gmax k * card k)) / card k
            + Real.sqrt (dL k * (Gmax k * card k)) / card k + tPi k / card k) := by
          field_simp
      _ = B ^ 2 * (Real.sqrt (dA k * Gmax k / card k)
            + Real.sqrt (dL k * Gmax k / card k) + tPi k / card k) := by
          rw [sqrt_div_eq hc, sqrt_div_eq hc]
  have hlim : Tendsto (fun k => B ^ 2 * (Real.sqrt (dA k * Gmax k / card k)
      + Real.sqrt (dL k * Gmax k / card k) + tPi k / card k)) atTop (𝓝 0) := by
    have h := ((hsA.add hsL).add hPi).const_mul (B ^ 2)
    simpa using h
  exact squeeze_zero (fun k => div_nonneg (hXi0 k) (hcard k).le) hdivbound hlim

/-! ### Examples

The sequences below satisfy `hbound` with equality, with `Xi k = 2√(k+1) + 2 → ∞` while
`Xi k / (k+1) → 0`. -/

section Witness

/-- Example sequences with `tr A = tr Λ = 1`, `G = 1`, `tr Π = 2` and `n = k+1`. -/
noncomputable def xiW (k : ℕ) : ℝ := 2 * Real.sqrt ((k : ℝ) + 1) + 2

theorem xiW_tendsto_atTop : Tendsto xiW atTop atTop := by
  have hlin : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsq : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlin
  have h2 : Tendsto (fun k : ℕ => 2 * Real.sqrt ((k : ℝ) + 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hsq
  exact h2.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))

/-- The hypotheses of `xi_div_card_tendsto_zero` hold jointly on one sequence with
`Xi k` unbounded. -/
theorem xi_div_card_tendsto_zero_witness :
    Tendsto (fun k : ℕ => xiW k / ((k : ℝ) + 1)) atTop (𝓝 0)
    ∧ Tendsto xiW atTop atTop := by
  have hcard : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hone : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htwo : Tendsto (fun k : ℕ => (2 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => (2 : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 (2 * 0)) :=
      hone.const_mul (2 : ℝ)
    rw [mul_zero] at h
    exact h.congr fun k => by ring
  have hxiW0 : ∀ k : ℕ, 0 ≤ xiW k := by
    intro k
    simp only [xiW]
    positivity
  refine ⟨?_, xiW_tendsto_atTop⟩
  refine xi_div_card_tendsto_zero (B := 1) (dA := fun _ => 1) (dL := fun _ => 1)
    (tPi := fun _ => 2) (Gmax := fun _ => 1) (card := fun k => (k : ℝ) + 1)
    hxiW0 hcard (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun _ => zero_le_one) (fun k => ?_) (htwo.congr fun k => by norm_num) htwo
  simp only [xiW, one_pow, one_mul]
  norm_num
  linarith

end Witness

end CgmLimit
end Multiway
