/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Multiway.SteinCluster
import Multiway.ClusterShock
import Multiway.JansonCLT

/-!
# Asymptotic normality under multiway clustering, via Janson's theorem

This file proves part (a) of Theorem 5 of the paper (asymptotic normality under multiway
clustering) at a general number `J` of clustering dimensions, under the accumulation condition
`δ_n := nD_n³/λ_min(Ω_n)² → 0`, together with the first sentence of Corollary SM.D.3
(feasible inference under the cluster-shock model). The engine is the dependency-graph central
limit theorem of Janson (1988, Theorem 2), `Janson.tendsto_gaussPM_of_depGraph`.

In a unit direction the array `X_{n,o} = (a_n'x̃_o)ν_o` has `|X_{n,o}| ≤ φ_n` and unit variance,
and Janson's condition `(1.5)` at `m = 4` reads `(n/D_n)^{1/4}D_nφ_n = BC_ν·δ_n^{1/4}`; raised to
the fourth power it is `n(D_n+1)³φ_n⁴ → 0`.

## Main results

* `cltcluster_a_general_betaJM_janson`: the conditional statement for `β̂_JM`.
* `cltcluster_a_general_betaJM_janson_unconditional` and its vector forms: the statement under
  the full measure with a random design, with the measurability side conditions derived.
* `clustershock_a_general_janson_unconditional`: Corollary SM.D.3 under `Ḡ_n³/n → 0`.
* Sections 9 and 10: the statement with `𝓡_n` random and `𝒟`-measurable.
-/

namespace Multiway.ClusterJanson

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators MatrixOrder
open Matrix
open Causalean.Mathlib.Probability.SteinMethod
open Multiway.SteinCluster
open Multiway.ClusterShock

/-! ### Section 1. Janson's condition `(1.5)` at `m = 4` -/

section Rate

/-- Janson's `(1.5)` at `m = 4` follows from `n(D_n+1)³φ_n⁴ → 0`: the fourth power of the rate
is `N_nM_n³u_n⁴`. -/
theorem tendsto_janson15_of_first {Nr Md u : ℕ → ℝ}
    (hNr : ∀ n, 0 < Nr n) (hMd : ∀ n, 0 < Md n) (hu : ∀ n, 0 ≤ u n)
    (h1 : Tendsto (fun n => Nr n * Md n ^ 3 * u n ^ 4) atTop (𝓝 0)) :
    Tendsto (fun n => (Nr n / Md n) ^ (((4 : ℕ) : ℝ)⁻¹) * (Md n * u n)) atTop (𝓝 0) := by
  have hbase : ∀ n, (0 : ℝ) ≤ Nr n / Md n := fun n => (div_pos (hNr n) (hMd n)).le
  have hf0 : ∀ n, 0 ≤ (Nr n / Md n) ^ (((4 : ℕ) : ℝ)⁻¹) * (Md n * u n) := fun n =>
    mul_nonneg (Real.rpow_nonneg (hbase n) _) (mul_nonneg (hMd n).le (hu n))
  have hf4 : ∀ n, ((Nr n / Md n) ^ (((4 : ℕ) : ℝ)⁻¹) * (Md n * u n)) ^ 4
      = Nr n * Md n ^ 3 * u n ^ 4 := by
    intro n
    rw [mul_pow, Real.rpow_inv_natCast_pow (hbase n) (by norm_num)]
    have h : Md n ≠ 0 := ne_of_gt (hMd n)
    field_simp
  have hsq : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0)
  have hg : Tendsto (fun n => Real.sqrt (Real.sqrt (Nr n * Md n ^ 3 * u n ^ 4))) atTop (𝓝 0) := by
    have := hsq.comp (hsq.comp h1)
    simpa [Function.comp_def] using this
  refine Tendsto.congr (fun n => ?_) hg
  rw [← hf4 n]
  have hx := hf0 n
  have h4' : ((Nr n / Md n) ^ (((4 : ℕ) : ℝ)⁻¹) * (Md n * u n)) ^ 4
      = (((Nr n / Md n) ^ (((4 : ℕ) : ℝ)⁻¹) * (Md n * u n)) ^ 2) ^ 2 := by ring
  rw [h4', Real.sqrt_sq (by positivity), Real.sqrt_sq hx]

/-- The rate hypothesis of `Janson.tendsto_gaussPM_of_depGraph` at `m = 4`, from the single
scalar `n(M_n+1)³u_n⁴ → 0`. The rate is taken at `N_n := n + 1` and compared back to `n`. -/
theorem tendsto_janson_rate_of_first {Nc Mc : ℕ → ℕ} {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hN1 : ∀ n, 1 ≤ Nc n) (hMN : ∀ n, Mc n ≤ Nc n)
    (h1 : Tendsto (fun n => (Nc n : ℝ) * ((Mc n : ℝ) + 1) ^ 3 * u n ^ 4) atTop (𝓝 0))
    {j : ℕ} (hj : 4 ≤ j) :
    Tendsto (fun n => (Nc n : ℝ) * ((Mc n : ℝ) + 1) ^ (j - 1) * u n ^ j) atTop (𝓝 0) := by
  have hNc1 : ∀ n, (1 : ℝ) ≤ (Nc n : ℝ) := fun n => by exact_mod_cast hN1 n
  have hMNr : ∀ n, ((Mc n : ℝ) + 1) ≤ (Nc n : ℝ) + 1 := by
    intro n
    have : ((Mc n : ℝ)) ≤ (Nc n : ℝ) := by exact_mod_cast hMN n
    linarith
  -- `(1.5)` at `m = 4`, on `N_n := n + 1`.
  have h15 : Tendsto (fun n => (((Nc n : ℝ) + 1) / ((Mc n : ℝ) + 1)) ^ (((4 : ℕ) : ℝ)⁻¹)
      * (((Mc n : ℝ) + 1) * u n)) atTop (𝓝 0) := by
    refine tendsto_janson15_of_first (fun n => by positivity) (fun n => by positivity) hu ?_
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using h1.const_mul (2 : ℝ))
    have hrest : (0 : ℝ) ≤ ((Mc n : ℝ) + 1) ^ 3 * u n ^ 4 := by positivity
    have h2 : (Nc n : ℝ) + 1 ≤ 2 * (Nc n : ℝ) := by linarith [hNc1 n]
    calc ((Nc n : ℝ) + 1) * ((Mc n : ℝ) + 1) ^ 3 * u n ^ 4
        = ((Nc n : ℝ) + 1) * (((Mc n : ℝ) + 1) ^ 3 * u n ^ 4) := by ring
      _ ≤ (2 * (Nc n : ℝ)) * (((Mc n : ℝ) + 1) ^ 3 * u n ^ 4) :=
          mul_le_mul_of_nonneg_right h2 hrest
      _ = 2 * ((Nc n : ℝ) * ((Mc n : ℝ) + 1) ^ 3 * u n ^ 4) := by ring
  have hbig := Janson.tendsto_rate_of_janson15 (N := fun n => (Nc n : ℝ) + 1)
    (Md := fun n => ((Mc n : ℝ) + 1)) (u := u) (m := 4) (by norm_num)
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

end Rate

/-! ### Section 2. The array theorem -/

section Array

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Theorem 5(a)** on the array, in characteristic-function form: a dependency graph with
closed-neighbourhood sizes at most `M_n + 1`, a uniform bound `φ_n`, mean zero and unit variance,
and `n(M_n+1)³φ_n⁴ → 0` with `1 ≤ M_n ≤ n`. -/
theorem cltcluster_a_general_janson_charFun
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (φ : ℕ → ℝ) (Mb : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ Mb n + 1)
    (hm1 : ∀ n, 1 ≤ Mb n) (hmN : ∀ n, Mb n ≤ Fintype.card (O n))
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => (Fintype.card (O n) : ℝ) * ((Mb n + 1 : ℕ) : ℝ) ^ 3 * (φ n) ^ 4)
      atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (depSum (X n))) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  classical
  -- integrability of every summand, hence `E S_n = 0`
  have hint : ∀ n o, Integrable (X n o) (μ n) := by
    intro n o
    refine Integrable.of_bound ((D n).meas o).aestronglyMeasurable (φ n)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hφ n o ω
  have hsum0 : ∀ n, ∫ ω, (∑ i, X n i ω) ∂(μ n) = 0 := by
    intro n
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => hint n i)]
    simp [hmean n]
  -- Janson counts the open neighbourhood; `DepGraph.nbhd` is the closed one
  have hdegJ : ∀ n, ∀ i : O n, (((D n).nbhd i).erase i).card ≤ Mb n := by
    intro n i
    rw [Finset.card_erase_of_mem ((D n).self_mem_nbhd i)]
    have := hdeg n i
    omega
  -- `σ_n = 1`, because `κ₂(S_n) = E S_n² − (E S_n)² = 1`
  have hvar' : ∀ n, ∫ ω, (∑ i, X n i ω) ^ 2 ∂(μ n) = 1 := hvar
  have hσsq : ∀ n, (1 : ℝ) ^ 2 = Cumulant.cumulant (fun ω => ∑ i, X n i ω) 2 (μ n) := by
    intro n
    rw [Cumulant.cumulant_two, hsum0 n, hvar' n]
    norm_num
  -- the rate, in Janson's form
  have hN1 : ∀ n, 1 ≤ Fintype.card (O n) := fun n => le_trans (hm1 n) (hmN n)
  have hrate' : Tendsto (fun n => (Fintype.card (O n) : ℝ) * ((Mb n : ℝ) + 1) ^ 3 * (φ n) ^ 4)
      atTop (𝓝 0) := by
    refine hrate.congr fun n => ?_
    push_cast
    ring
  have hrateJ : ∀ j, 4 ≤ j → Tendsto (fun n => (Fintype.card (O n) : ℝ)
      * ((Mb n : ℝ) + 1) ^ (j - 1) * (φ n / (1 : ℝ)) ^ j) atTop (𝓝 0) := by
    intro j hj
    simp only [div_one]
    exact tendsto_janson_rate_of_first hφ0 hN1 hmN hrate' hj
  -- Janson `Theorem 2`
  have hJ := Janson.tendsto_gaussPM_of_depGraph (μ := μ) (X := X) D hdegJ
    (A := φ) hφ0 (fun n i => Filter.Eventually.of_forall fun ω => hφ n i ω)
    (σ := fun _ => (1 : ℝ)) (fun _ => one_pos) hσsq (m := 4) (by norm_num) hrateJ
  -- the centring is zero and the standardized law is the law of `S_n`
  have hlaw : ∀ n, ((Janson.stdSumPM (D n) (1 : ℝ)
      (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / 1) : ProbabilityMeasure ℝ) : Measure ℝ)
      = (μ n).map (depSum (X n)) := by
    intro n
    have hfn : (fun ω => (∑ i, X n i ω) / (1 : ℝ) + -(∫ ω, (∑ i, X n i ω) ∂(μ n)) / 1)
        = depSum (X n) := by
      rw [hsum0 n]
      funext ω
      simp [depSum]
    rw [Janson.stdSumPM_toMeasure, hfn]
  have hg : ((Janson.gaussPM 0 1 : ProbabilityMeasure ℝ) : Measure ℝ) = gaussianReal 0 1 := by
    rw [Janson.gaussPM_toMeasure, Real.toNNReal_one]
  have hchar := MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hJ t
  simpa only [hlaw, hg] using hchar

/-- The same, as convergence in distribution to `N(0,1)`, by Lévy's continuity theorem. -/
theorem cltcluster_a_general_janson_tendstoInDistribution
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (φ : ℕ → ℝ) (Mb : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ Mb n + 1)
    (hm1 : ∀ n, 1 ≤ Mb n) (hmN : ∀ n, Mb n ≤ Fintype.card (O n))
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => (Fintype.card (O n) : ℝ) * ((Mb n + 1 : ℕ) : ℝ) ^ 3 * (φ n) ^ 4)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun n => depSum (X n)) atTop (id : ℝ → ℝ) μ (gaussianReal 0 1) := by
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => (D n).meas o)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hWmeas n).aemeasurable)
    aemeasurable_id fun t => ?_
  rw [Measure.map_id]
  exact cltcluster_a_general_janson_charFun μ X D φ Mb hφ0 hφ hdeg hm1 hmN hmean hvar hrate t

/-- The same, in CDF form. -/
theorem cltcluster_a_general_janson
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (φ : ℕ → ℝ) (Mb : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ Mb n + 1)
    (hm1 : ∀ n, 1 ≤ Mb n) (hmN : ∀ n, Mb n ≤ Fintype.card (O n))
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => (Fintype.card (O n) : ℝ) * ((Mb n + 1 : ℕ) : ℝ) ^ 3 * (φ n) ^ 4)
      atTop (𝓝 0))
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
  exact cltcluster_a_general_janson_charFun μ X D φ Mb hφ0 hφ hdeg hm1 hmN hmean hvar hrate t

end Array

/-! ### Section 3. `β̂_JM` under the accumulation condition -/

section BetaJM

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {r : Type*} [Fintype r] [DecidableEq r]

/-- **Theorem 5(a)** for `β̂_JM`, conditionally on the design, under the accumulation condition
`δ_n → 0`. The only rate lemma used is `SteinCluster.firstRate_le`, with constant
`8B⁴C_ν⁴δ_n`. -/
theorem cltcluster_a_general_betaJM_janson
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
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  refine cltcluster_a_general_janson μ
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * Cnu / Real.sqrt (lmin n)) Dn
    (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ ?_ hDn1 hDnN ?_ ?_ ?_ s
  · exact fun n o ω =>
      abs_scoreArray_le (hPD n) (hA n) (hlmin n) (hfloor n) hB0 (hB n) (hnu n) hb o ω
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hnu n) (hOm n) hb
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hrate.const_mul (8 * B ^ 4 * Cnu ^ 4))
    exact firstRate_le (hDn1 n) (hlmin n)

/-- The same theorem for a constant family, as convergence in distribution. -/
theorem cltcluster_a_general_betaJM_janson_const
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
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  refine cltcluster_a_general_janson_tendstoInDistribution (Ω := fun _ => W) (fun _ => μ)
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * Cnu / Real.sqrt (lmin n)) Dn
    (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ ?_ hDn1 hDnN ?_ ?_ ?_
  · exact fun n o ω =>
      abs_scoreArray_le (hPD n) (hA n) (hlmin n) (hfloor n) hB0 (hB n) (hnu n) hb o ω
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hnu n) (hOm n) hb
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hrate.const_mul (8 * B ^ 4 * Cnu ^ 4))
    exact firstRate_le (hDn1 n) (hlmin n)

end BetaJM

/-! ### Section 4. Cramér--Wold, and removing the conditioning on `𝒟` -/

section Deconditioning

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The vector statement conditionally on the design, by the Cramér--Wold device. -/
theorem cltcluster_a_general_betaJM_janson_vector
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
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  have h := cltcluster_a_general_betaJM_janson_const μ Xt Om Rn ν bhat β Dv hscore hA
    lmin hlmin hfloor hOm hmean B Cnu hB0 hCnu0 hB hnu Dn hDn1 hDnN hdeg hrate
    (WithLp.ofLp b) (dotProduct_self_ofLp b hb)
  have hfun : (fun (n : ℕ) (ω : W) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun (n : ℕ) (ω : W) =>
        ⟪restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Theorem 5(a)** for `β̂_JM` in a unit direction, under the full measure, with a random
design. -/
theorem cltcluster_a_general_betaJM_janson_unconditional
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
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
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
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
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
  · filter_upwards [hdep, hA, hlmin, hfloor, hOmeq, hmean, hB, hDn1, hDnN, hrate]
      with ω hdepω hAω hlminω hfloorω hOmω hmeanω hBω hDn1ω hDnNω hrateω
    obtain ⟨Dv, hdegω⟩ := hdepω
    have hPD : ∀ n, (scoreVar (Xt n ω) (Om n ω)).PosDef := fun n =>
      Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlminω n)) (hfloorω n)
    refine cltcluster_a_general_janson_tendstoInDistribution
      (Ω := fun _ => Ω) (fun _ => condExpKernel P 𝒟 ω)
      (fun n => scoreArray (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b) (ν n))
      (fun n => scoreArrayDepGraph (Dv n) (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b))
      (fun n => B * Cnu / Real.sqrt (lmin n ω)) (fun n => Dn n ω)
      (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ ?_ hDn1ω hDnNω ?_ ?_ ?_
    · exact fun n o y => abs_scoreArray_le (hPD n) (hAω n) (hlminω n) (hfloorω n) hB0
        (hBω n) (hnu n) hb o y
    · intro n o
      rw [nbhd_scoreArrayDepGraph]
      exact hdegω n o
    · exact fun n o => integral_scoreArray (fun o => hmeanω n o) (Xt n ω) _ o
    · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hAω n)
        (fun o => (Dv n).meas o) (hnu n) (hOmω n) hb
    · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
        (by simpa using hrateω.const_mul (8 * B ^ 4 * Cnu ^ 4))
      exact firstRate_le (hDn1ω n) (hlminω n)

/-- **Theorem 5(a)** under the full measure with a random design:
`𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)`. -/
theorem cltcluster_a_general_betaJM_janson_unconditional_vector
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
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
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
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
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
  have h := cltcluster_a_general_betaJM_janson_unconditional h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B Cnu hB0 hCnu0 hnu (WithLp.ofLp b)
    (dotProduct_self_ofLp b hb) hWm hdep hA hlmin hfloor hOmeq hmean hB hDn1 hDnN hrate
  have hfun : (fun (n : ℕ) (y : Ω) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))))
      = fun (n : ℕ) (y : Ω) =>
        ⟪restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

end Deconditioning

/-! ### Section 5. Corollary SM.D.3, first sentence, under `Ḡ_n³/n → 0` -/

section Clustershock

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- `Ḡ_n³/n → 0` implies `δ_n → 0`, under the variance floor `λ_min(Ω_n) ≥ cn` and the degree
bound `D_n ≤ JḠ_n`: `δ_n = D_n³/(c²n) ≤ (J³/c²)(Ḡ_n³/n)`. -/
theorem tendsto_accumRate_of_cluster_size {N D Gb : ℕ → ℕ} {Jc : ℕ} {c : ℝ} (hc : 0 < c)
    (hN : ∀ n, 1 ≤ N n) (hDJG : ∀ n, D n ≤ Jc * Gb n)
    (hG : Tendsto (fun n => (Gb n : ℝ) ^ 3 / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => accumRate (N n) (D n) (c * (N n : ℝ))) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => accumRate_nonneg _ _) (fun n => ?_)
    (by simpa using hG.const_mul ((Jc : ℝ) ^ 3 / c ^ 2))
  have hNR : (0 : ℝ) < (N n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hN n)
  have hDR : (0 : ℝ) ≤ (D n : ℝ) := by positivity
  have hDJ : (D n : ℝ) ≤ (Jc : ℝ) * (Gb n : ℝ) := by exact_mod_cast hDJG n
  have h3 : (D n : ℝ) ^ 3 ≤ ((Jc : ℝ) * (Gb n : ℝ)) ^ 3 := pow_le_pow_left₀ hDR hDJ 3
  have hL : accumRate (N n) (D n) (c * (N n : ℝ)) = (D n : ℝ) ^ 3 / (c ^ 2 * (N n : ℝ)) := by
    unfold accumRate
    field_simp
  have hR : ((Jc : ℝ) ^ 3 / c ^ 2) * ((Gb n : ℝ) ^ 3 / (N n : ℝ))
      = ((Jc : ℝ) * (Gb n : ℝ)) ^ 3 / (c ^ 2 * (N n : ℝ)) := by
    field_simp
  rw [hL, hR]
  exact div_le_div_of_nonneg_right h3 (by positivity)

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Dm : Type*} [DecidableEq Dm]
variable {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Corollary SM.D.3**, first sentence, at general `J` under
`Ḡ_n³/n → 0`. -/
theorem clustershock_a_general_janson
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
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (θ : ℝ) (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (hGrate : Tendsto (fun n => (Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0))
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
  refine cltcluster_a_general_betaJM_janson μ Xt
    (fun n => Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) Rn ν bhat β Dv hscore hA
    (fun n => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n => mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n)) hfloorK hOm hmean
    B Cnu hB0 hCnu0 hB hnu Dn hDn1 (fun n => min_le_right _ _)
    (fun n o => le_trans (hdegF n o) (Nat.le_succ _)) ?_ b hb s
  exact tendsto_accumRate_of_cluster_size (mul_pos hs2 hθ) (fun n => hcard n)
    (fun n => min_le_left _ _) hGrate

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The almost-everywhere facts shared by the unconditional forms of the corollary. -/
theorem clustershock_general_uncond_package_janson
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (ν : ∀ n, O n → Ω → ℝ)
    (c : ∀ n, Ω → Dm → O n → L n) (dims : Finset Dm)
    (sc : ℕ → Ω → Dm → ℝ) (ve : ∀ n, Ω → O n → ℝ)
    {s2 θ : ℝ} (hs2 : 0 < s2) (hθ : 0 < θ) (Gb : ℕ → Ω → ℕ)
    (hne : ∀ n, Nonempty (O n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n ω) dims o o')
    (hsc : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, 0 ≤ sc n ω j)
    (hve : ∀ᵐ ω ∂P, ∀ n o, s2 ≤ ve n ω o)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => (Gb n ω : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P,
      (∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
        ∀ n o, ((Dv n).nbhd o).card ≤ min (dims.card * Gb n ω) (Fintype.card (O n)) + 1)
      ∧ (∀ n, 1 ≤ min (dims.card * Gb n ω) (Fintype.card (O n)))
      ∧ (∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
          ≤ scoreVar (Xt n ω) (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)))
      ∧ Tendsto (fun n => accumRate (Fintype.card (O n))
          (min (dims.card * Gb n ω) (Fintype.card (O n)))
          ((s2 * θ) * (Fintype.card (O n) : ℝ))) atTop (𝓝 0) := by
  classical
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  filter_upwards [hdep, hsc, hve, hdesign, hGb, hGrate]
    with ω hdepω hscω hveω hdesω hGbω hGrω
  obtain ⟨Dv, hshareω⟩ := hdepω
  have hfloorOm : ∀ n, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) :=
    fun n => Multiway.Sharing.smul_one_le_clusterOmega (hscω n) (hveω n)
  have hfloorK : ∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n ω) (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) := by
    intro n
    have h1 : s2 • ((θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ))
        ≤ s2 • ((Xt n ω)ᵀ * Xt n ω) := Multiway.loewner_smul_le_smul hs2.le (hdesω n)
    rw [smul_smul, ← mul_assoc] at h1
    exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj (hfloorOm n) (Xt n ω))
  have hnbhd : ∀ n o, (Dv n).nbhd o = Multiway.Sharing.closedNbhd (c n ω) dims o := by
    intro n o
    ext o'
    rw [DepGraph.mem_nbhd_iff, Multiway.Sharing.mem_closedNbhd]
    exact hshareω n o o'
  have hdegF : ∀ n o, ((Dv n).nbhd o).card
      ≤ min (dims.card * Gb n ω) (Fintype.card (O n)) := by
    intro n o
    refine le_min ?_ ?_
    · rw [hnbhd n o]; exact card_closedNbhd_le_mul (hGbω n) o
    · exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  have hDn1 : ∀ n, 1 ≤ min (dims.card * Gb n ω) (Fintype.card (O n)) := by
    intro n
    obtain ⟨o⟩ := hne n
    refine le_trans ?_ (hdegF n o)
    exact Finset.card_pos.mpr ⟨o, (Dv n).self_mem_nbhd o⟩
  refine ⟨⟨Dv, fun n o => le_trans (hdegF n o) (Nat.le_succ _)⟩, hDn1, hfloorK, ?_⟩
  exact tendsto_accumRate_of_cluster_size (mul_pos hs2 hθ) (fun n => hcard n)
    (fun n => min_le_left _ _) hGrω

/-- **Corollary SM.D.3**, first sentence, under the full measure with a random design. -/
theorem clustershock_a_general_janson_unconditional
    {r : Type*} [Fintype r] [DecidableEq r]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Ω → Dm → O n → L n) (dims : Finset Dm)
    (sc : ℕ → Ω → Dm → ℝ) (ve : ∀ n, Ω → O n → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω =>
      Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (s2 : ℝ) (hs2 : 0 < s2) (θ : ℝ) (hθ : 0 < θ) (Gb : ℕ → Ω → ℕ)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1)
    (hWm : ∀ n, Measurable fun y => b ⬝ᵥ
      ((sqrtPD (restrictedVar (Xt n y)
          (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n))))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n ω) dims o o')
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hsc : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, 0 ≤ sc n ω j)
    (hve : ∀ᵐ ω ∂P, ∀ n o, s2 ≤ ve n ω o)
    (hOm : ∀ᵐ ω ∂P, ∀ n o o', ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω)
      = Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hne : ∀ n, Nonempty (O n))
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => (Gb n ω : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y)
            (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hpkg := clustershock_general_uncond_package_janson (𝒟 := 𝒟) P Xt ν c dims sc ve hs2 hθ
    Gb hne hdep hsc hve hdesign hGb hGrate
  exact cltcluster_a_general_betaJM_janson_unconditional h𝒟 P Xt
    (fun n ω => Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) Rn ν bhat β
    hXtD hOmD hscore
    (fun n _ => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n ω => min (dims.card * Gb n ω) (Fintype.card (O n)))
    B Cnu hB0 hCnu0 hnu b hb hWm
    (hpkg.mono fun _ h => h.1) hA
    (Filter.Eventually.of_forall fun _ n =>
      mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n))
    (hpkg.mono fun _ h => h.2.2.1) hOm hmean hB
    (hpkg.mono fun _ h => h.2.1)
    (Filter.Eventually.of_forall fun _ _ => min_le_right _ _)
    (hpkg.mono fun _ h => h.2.2.2)

/-- **Corollary SM.D.3**, first sentence, vector form:
`𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)` under the full measure. -/
theorem clustershock_a_general_janson_unconditional_vector
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Ω → Dm → O n → L n) (dims : Finset Dm)
    (sc : ℕ → Ω → Dm → ℝ) (ve : ∀ n, Ω → O n → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω =>
      Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (s2 : ℝ) (hs2 : 0 < s2) (θ : ℝ) (hθ : 0 < θ) (Gb : ℕ → Ω → ℕ)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (hWvm : ∀ n, Measurable fun y =>
      restrictedStat (Xt n y)
        (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)
        (bhat n y - β n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n ω) dims o o')
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hsc : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, 0 ≤ sc n ω j)
    (hve : ∀ᵐ ω ∂P, ∀ n o, s2 ≤ ve n ω o)
    (hOm : ∀ᵐ ω ∂P, ∀ n o o', ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω)
      = Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hne : ∀ n, Nonempty (O n))
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => (Gb n ω : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y)
        (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)
        (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hpkg := clustershock_general_uncond_package_janson (𝒟 := 𝒟) P Xt ν c dims sc ve hs2 hθ
    Gb hne hdep hsc hve hdesign hGb hGrate
  exact cltcluster_a_general_betaJM_janson_unconditional_vector h𝒟 P Xt
    (fun n ω => Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) Rn ν bhat β
    hXtD hOmD hscore
    (fun n _ => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n ω => min (dims.card * Gb n ω) (Fintype.card (O n)))
    B Cnu hB0 hCnu0 hnu hWvm
    (hpkg.mono fun _ h => h.1) hA
    (Filter.Eventually.of_forall fun _ n =>
      mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n))
    (hpkg.mono fun _ h => h.2.2.1) hOm hmean hB
    (hpkg.mono fun _ h => h.2.1)
    (Filter.Eventually.of_forall fun _ _ => min_le_right _ _)
    (hpkg.mono fun _ h => h.2.2.2)

end Clustershock

/-! ### Section 6. Satisfiability of the hypotheses

The models below have `J = 2`, sharing relation `SteinCluster.pathG` (`|o − o'| ≤ 1` on
`Fin (n+3)`, the union of two clustering dimensions and not an equivalence relation), fair-sign
disturbances and `r = 1`. -/

section Witnesses

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.Multilinear

/-- The rate of the model: `δ_n = 8/(n+3) → 0`. -/
theorem tendsto_accumRate_witness :
    Tendsto (fun n : ℕ => accumRate (n + 3) 2 ((n : ℝ) + 3)) atTop (𝓝 0) := by
  have hacc : ∀ n : ℕ, accumRate (n + 3) 2 ((n : ℝ) + 3) = 8 / ((n : ℝ) + 3) := by
    intro n
    unfold accumRate
    have hc : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    rw [hc]
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2]
    field_simp
    ring
  simp only [hacc]
  have hd : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa using (tendsto_const_nhds (x := (8 : ℝ)) (f := atTop (α := ℕ))).div_atTop hd

/-- A model satisfying the hypotheses of `cltcluster_a_general_betaJM_janson`: `n+3`
observations, one regressor `x̃_o = 1`, `𝓡_n = I_1`, one fair sign per observation, sharing
along `SteinCluster.pathG`. -/
theorem cltcluster_a_general_betaJM_janson_witness (s : ℝ) :
    Tendsto (fun n => ((coins (n + 3)).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt (n + 2))
              (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
                  ((redXt (n + 2))ᵀ *ᵥ (fun o => sign2 o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine cltcluster_a_general_betaJM_janson (O := fun n => Fin (n + 3))
    (fun n => coins (n + 3)) (fun n => redXt (n + 2)) (fun n => 1) (fun n => 1)
    (fun _ o => sign2 o)
    (fun n ω => ((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
      ((redXt (n + 2))ᵀ *ᵥ (fun o => sign2 o ω)))
    (fun _ => 0) pathDep (fun _ _ => by simp)
    (fun n => redXt_scoreMap_isUnit (n + 2)) (fun n => (n : ℝ) + 3) (fun n => by positivity)
    ?_ (fun n => red_second_moment (n + 2)) (fun n o => integral_sign2 o)
    1 1 zero_le_one zero_le_one ?_ ?_ (fun _ => 2) (fun _ => by norm_num) ?_ ?_ ?_
    (fun _ => (1 : ℝ)) ?_ s
  · intro n
    rw [redXt_scoreVar]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · intro _ _
    simp [redXt, dotProduct]
  · intro _ o ω
    exact abs_sign2_le' o ω
  · intro n
    simp
  · intro n o
    exact pathDep_nbhd_card n o
  · simpa using tendsto_accumRate_witness
  · simp [dotProduct]

end Witnesses

section UnconditionalWitness

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.Multilinear
open Multiway.SteinCluster.FrozenDesignWitness
open Multiway.SteinCluster.FrozenGeneralWitness

/-- A model satisfying the hypotheses of `cltcluster_a_general_betaJM_janson_unconditional`, on
`Bool × ((ℕ × ℕ) → Bool)`, with `𝒟` a proper sub-σ-algebra and a random `𝒟`-measurable design
`X̃_n(ω) = ±ι_{n+3}`. -/
theorem cltcluster_a_general_betaJM_janson_unconditional_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), gXt n y = (if y.1 then (1 : ℝ) else -1) • redXt (n + 2))
    ∧ (∀ n : ℕ, ∃ a b c : Fin (n + 3),
        pathG (n + 3) a b ∧ pathG (n + 3) b c ∧ ¬ pathG (n + 3) a c)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2)) (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (guSign n)) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => wb ⬝ᵥ
          ((sqrtPD (restrictedVar (gXt n y) (gOm n y) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gBhat n y - (0 : Fin 1 → ℝ)))))
        atTop (id : ℝ → ℝ) (fun _ => Pw) (gaussianReal 0 1) := by
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ => rfl,
    pathG_not_transitive, g_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine cltcluster_a_general_betaJM_janson_unconditional (O := fun n => Fin (n + 3))
    Dw_le Pw gXt gOm (fun _ => 1) guSign gBhat (fun _ => 0)
    g_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    (fun n _ => (n : ℝ) + 3) (fun _ _ => 2) 1 1 zero_le_one zero_le_one
    (fun n o y => abs_gvSign_le n o y.2) wb wb_dot g_hWm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [map_snd_condExpKernel] with ω hω
    exact ⟨fun n => gPathDep hω n, fun n o => gPathDep_nbhd_card hω n o⟩
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show gXt n ω = sgnA ω • redXt (n + 2) from rfl, scoreMap_smul (sgnA_mul ω)]
    exact redXt_scoreMap_isUnit (n + 2)
  · exact Filter.Eventually.of_forall fun _ n => by positivity
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show gXt n ω = sgnA ω • redXt (n + 2) from rfl, scoreVar_smul (sgnA_mul ω),
      show gOm n ω = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) from rfl, redXt_scoreVar]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o o'
    exact (integral_of_snd hω ((meas_gvSign n o).mul (meas_gvSign n o'))).trans
      (integral_gvSign_mul n o o')
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o
    exact (integral_of_snd hω (meas_gvSign n o)).trans (integral_gvSign n o)
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun k => gXt n ω o k) ⬝ᵥ (fun k => gXt n ω o k) = 1 := by
      simp [gXt, redXt, dotProduct, sgnA_mul ω]
    rw [h]
    norm_num
  · exact Filter.Eventually.of_forall fun _ _ => by norm_num
  · refine Filter.Eventually.of_forall fun _ n => ?_
    rw [Fintype.card_fin]
    omega
  · exact Filter.Eventually.of_forall fun _ => by simpa using tendsto_accumRate_witness

end UnconditionalWitness

section ShockWitness

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.SteinCluster.FrozenDesignWitness
open Multiway.ClusterShock.FrozenGeneralShockWitness

/-- The cluster-shock rate of the model: `Ḡ_n³/n = 8/(n+3)`. -/
theorem gc_hGrate_cube : Tendsto (fun n : ℕ => (((2 : ℕ) : ℝ)) ^ 3 / ((n + 3 : ℕ) : ℝ))
    atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop := by
    have hcast : ∀ n : ℕ, ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := fun n => by push_cast; ring
    simp only [hcast]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa using (tendsto_const_nhds (x := (((2 : ℕ) : ℝ)) ^ 3) (f := atTop (α := ℕ))).div_atTop hd

/-- A model satisfying the hypotheses of `clustershock_a_general_janson_unconditional`, with a
non-trivial `𝒟`, a random design and a shared cluster shock, so that `Ω` is not diagonal. -/
theorem clustershock_a_general_janson_unconditional_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), gcXt n y = (if y.1 then (1 : ℝ) else -1) • redXt (n + 2))
    ∧ (∀ n : ℕ, ∃ a b d : Fin (n + 3),
        Multiway.Linked (wtC n) Finset.univ a b
        ∧ Multiway.Linked (wtC n) Finset.univ b d
        ∧ ¬ Multiway.Linked (wtC n) Finset.univ a d)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, coinShockSumA (gcIdx n) ⟨0, by omega⟩ y
        * coinShockSumA (gcIdx n) ⟨1, by omega⟩ y ∂(condExpKernel Pw Dw ω) = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2))
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSumA (gcIdx n))) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => wb ⬝ᵥ
          ((sqrtPD (restrictedVar (gcXt n y)
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
                (fun _ => (1 : ℝ)))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gcBhat n y - (0 : Fin 1 → ℝ)))))
        atTop (id : ℝ → ℝ) (fun _ => Pw) (gaussianReal 0 1) := by
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ => rfl,
    wtLinked_not_transitive, gc_within_cond, gc_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine clustershock_a_general_janson_unconditional (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    Dw_le Pw gcXt (fun _ => 1) (fun n => coinShockSumA (gcIdx n)) gcBhat (fun _ => 0)
    (fun n _ => wtC n) Finset.univ (fun _ _ _ => 1) (fun _ _ _ => 1)
    gc_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    1 zero_lt_one 1 zero_lt_one (fun _ _ => 2)
    1 3 zero_le_one (by norm_num)
    (fun n o y => by simpa using abs_coinShockSumA_le (gcIdx n) o y)
    wb wb_dot gc_hWm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun n => ⟨⟨0, by omega⟩⟩) ?_ ?_
  · filter_upwards [map_snd_condExpKernel] with ω hω
    exact ⟨fun n => gcDep hω n, fun _ _ _ => Iff.rfl⟩
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, scoreMap_smul (sgnA_mul ω)]
    exact redXt_scoreMap_isUnit (n + 2)
  · exact Filter.Eventually.of_forall fun _ _ _ _ => zero_le_one
  · exact Filter.Eventually.of_forall fun _ _ _ => le_refl 1
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o o'
    refine (integral_of_snd hω ((measurable_coinShockSum (gcIdx n) o).mul
      (measurable_coinShockSum (gcIdx n) o'))).trans ?_
    simp only [Pi.mul_apply]
    exact gc_hOm n o o'
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o
    exact (integral_of_snd hω (measurable_coinShockSum (gcIdx n) o)).trans
      (integral_coinShockSum (gcIdx n) o)
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun k => gcXt n ω o k) ⬝ᵥ (fun k => gcXt n ω o k) = 1 := by
      simp [gcXt, redXt, dotProduct, sgnA_mul ω]
    rw [h]
    norm_num
  · refine Filter.Eventually.of_forall fun ω n => ?_
    have h : (gcXt n ω)ᵀ * gcXt n ω
        = (((n + 2 : ℕ) : ℝ) + 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, gram_smul (sgnA_mul ω),
        redXt_transpose_mul_self]
    rw [h, Fintype.card_fin]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · exact Filter.Eventually.of_forall fun _ n j _ γ => wtCluster_card n j γ
  · refine Filter.Eventually.of_forall fun _ => ?_
    simp only [Fintype.card_fin]
    exact gc_hGrate_cube

/-- A model satisfying the hypotheses of `clustershock_a_general_janson_unconditional_vector`,
at `r = 1`. -/
theorem clustershock_a_general_janson_unconditional_vector_witness :
    (∀ n : ℕ, ∃ a b d : Fin (n + 3),
        Multiway.Linked (wtC n) Finset.univ a b
        ∧ Multiway.Linked (wtC n) Finset.univ b d
        ∧ ¬ Multiway.Linked (wtC n) Finset.univ a d)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, coinShockSumA (gcIdx n) ⟨0, by omega⟩ y
        * coinShockSumA (gcIdx n) ⟨1, by omega⟩ y ∂(condExpKernel Pw Dw ω) = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2))
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSumA (gcIdx n))) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => restrictedStat (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) (gcBhat n y - (0 : Fin 1 → ℝ))) atTop
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (fun _ => Pw)
        (stdGaussian (EuclideanSpace ℝ (Fin 1))) := by
  refine ⟨wtLinked_not_transitive, gc_within_cond, gc_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine clustershock_a_general_janson_unconditional_vector (O := fun n => Fin (n + 3))
    (Dm := Fin 2) (L := fun n => Fin (n + 3))
    Dw_le Pw gcXt (fun _ => 1) (fun n => coinShockSumA (gcIdx n)) gcBhat (fun _ => 0)
    (fun n _ => wtC n) Finset.univ (fun _ _ _ => 1) (fun _ _ _ => 1)
    gc_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    1 zero_lt_one 1 zero_lt_one (fun _ _ => 2)
    1 3 zero_le_one (by norm_num)
    (fun n o y => by simpa using abs_coinShockSumA_le (gcIdx n) o y)
    gc_hWvm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun n => ⟨⟨0, by omega⟩⟩) ?_ ?_
  · filter_upwards [map_snd_condExpKernel] with ω hω
    exact ⟨fun n => gcDep hω n, fun _ _ _ => Iff.rfl⟩
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, scoreMap_smul (sgnA_mul ω)]
    exact redXt_scoreMap_isUnit (n + 2)
  · exact Filter.Eventually.of_forall fun _ _ _ _ => zero_le_one
  · exact Filter.Eventually.of_forall fun _ _ _ => le_refl 1
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o o'
    refine (integral_of_snd hω ((measurable_coinShockSum (gcIdx n) o).mul
      (measurable_coinShockSum (gcIdx n) o'))).trans ?_
    simp only [Pi.mul_apply]
    exact gc_hOm n o o'
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o
    exact (integral_of_snd hω (measurable_coinShockSum (gcIdx n) o)).trans
      (integral_coinShockSum (gcIdx n) o)
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun k => gcXt n ω o k) ⬝ᵥ (fun k => gcXt n ω o k) = 1 := by
      simp [gcXt, redXt, dotProduct, sgnA_mul ω]
    rw [h]
    norm_num
  · refine Filter.Eventually.of_forall fun ω n => ?_
    have h : (gcXt n ω)ᵀ * gcXt n ω
        = (((n + 2 : ℕ) : ℝ) + 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, gram_smul (sgnA_mul ω),
        redXt_transpose_mul_self]
    rw [h, Fintype.card_fin]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · exact Filter.Eventually.of_forall fun _ n j _ γ => wtCluster_card n j γ
  · refine Filter.Eventually.of_forall fun _ => ?_
    simp only [Fintype.card_fin]
    exact gc_hGrate_cube

end ShockWitness

/-! ### Section 7. Measurability of the standardized statistic

The measurability hypotheses `hWm` and `hWvm` are derived from the `𝒟`-measurability of `X̃_n`
and `Ω_n`, using `Multiway.Wald.measurable_sqrtPD` for the matrix square root and rectangular
matrix products. The measurability of `ν` follows from the `meas` field of `DepGraph`. -/

section Measurability

open Matrix

variable {α : Type*} [MeasurableSpace α]

/-- Transposition of a measurable matrix-valued map. -/
theorem measurable_matrix_transpose {m nn : Type*} {f : α → Matrix m nn ℝ} (hf : Measurable f) :
    Measurable fun a => (f a)ᵀ :=
  Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix

/-- The product of two measurable matrix-valued maps, at rectangular shapes. -/
theorem measurable_matrix_mul_rect {m nn p : Type*} [Fintype nn]
    {f : α → Matrix m nn ℝ} {g : α → Matrix nn p ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a * g a := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have h : (fun a => (f a * g a) i j) = fun a => ∑ k, f a i k * g a k j := funext fun _ => rfl
  rw [h]
  exact Finset.measurable_sum _ fun _ _ => hf.eval_matrix.mul hg.eval_matrix

/-- `M *ᵥ v` is measurable in both arguments. -/
theorem measurable_mulVec_comp {m nn : Type*} [Fintype nn]
    {f : α → Matrix m nn ℝ} {v : α → nn → ℝ} (hf : Measurable f) (hv : Measurable v) :
    Measurable fun a => f a *ᵥ v a := by
  refine Measurable.of_eval fun i => ?_
  have h : (fun a => (f a *ᵥ v a) i) = fun a => ∑ j, f a i j * v a j := funext fun _ => rfl
  rw [h]
  exact Finset.measurable_sum _ fun _ _ => hf.eval_matrix.mul hv.eval

/-- `b ⬝ᵥ v` is measurable in `v`. -/
theorem measurable_dotProduct_const {nn : Type*} [Fintype nn] (b : nn → ℝ)
    {v : α → nn → ℝ} (hv : Measurable v) : Measurable fun a => b ⬝ᵥ v a := by
  have h : (fun a => b ⬝ᵥ v a) = fun a => ∑ i, b i * v a i := funext fun _ => rfl
  rw [h]
  exact Finset.measurable_sum _ fun _ _ => measurable_const.mul hv.eval

variable {O K : Type*} [Fintype O] [Fintype K] [DecidableEq K]
variable {rr : Type*} [Fintype rr] [DecidableEq rr]

omit [Fintype rr] [DecidableEq rr] in
/-- `A_n := (X̃'X̃)^{-1}𝓡_n'` is measurable in `X̃`. -/
theorem measurable_scoreMap_comp {Xt : α → Matrix O K ℝ} (hXt : Measurable Xt)
    (Rn : Matrix rr K ℝ) : Measurable fun a => scoreMap (Xt a) Rn :=
  measurable_matrix_mul_rect
    (Multiway.Wald.measurable_matrix_inv.comp
      (measurable_matrix_mul_rect (measurable_matrix_transpose hXt) hXt))
    measurable_const

omit [Fintype K] [DecidableEq K] in
/-- `Ω_n := X̃'ΩX̃` is measurable in `X̃` and `Ω`. -/
theorem measurable_scoreVar_comp {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    (hXt : Measurable Xt) (hOm : Measurable Om) :
    Measurable fun a => scoreVar (Xt a) (Om a) :=
  measurable_matrix_mul_rect
    (measurable_matrix_mul_rect (measurable_matrix_transpose hXt) hOm) hXt

omit [Fintype rr] [DecidableEq rr] in
/-- `𝒱_n := A_n'Ω_nA_n` is measurable in `X̃` and `Ω`. -/
theorem measurable_restrictedVar_comp {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    (Rn : Matrix rr K ℝ) (hXt : Measurable Xt) (hOm : Measurable Om) :
    Measurable fun a => restrictedVar (Xt a) (Om a) Rn :=
  measurable_matrix_mul_rect
    (measurable_matrix_mul_rect
      (measurable_matrix_transpose (measurable_scoreMap_comp hXt Rn))
      (measurable_scoreVar_comp hXt hOm))
    (measurable_scoreMap_comp hXt Rn)

/-- `𝒱_n^{-1/2}` is measurable. -/
theorem measurable_invSqrt_restrictedVar {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    (Rn : Matrix rr K ℝ) (hXt : Measurable Xt) (hOm : Measurable Om) :
    Measurable fun a => (sqrtPD (restrictedVar (Xt a) (Om a) Rn))⁻¹ :=
  Multiway.Wald.measurable_matrix_inv.comp
    (Multiway.Wald.measurable_sqrtPD.comp (measurable_restrictedVar_comp Rn hXt hOm))

/-- The scalar standardized statistic is measurable. -/
theorem measurable_standardized_comp {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    {d : α → K → ℝ} (Rn : Matrix rr K ℝ) (hXt : Measurable Xt) (hOm : Measurable Om)
    (hd : Measurable d) (b : rr → ℝ) :
    Measurable fun a =>
      b ⬝ᵥ ((sqrtPD (restrictedVar (Xt a) (Om a) Rn))⁻¹ *ᵥ (Rn *ᵥ d a)) :=
  measurable_dotProduct_const b
    (measurable_mulVec_comp (measurable_invSqrt_restrictedVar Rn hXt hOm)
      (measurable_mulVec_comp measurable_const hd))

/-- The vector standardized statistic is measurable. -/
theorem measurable_restrictedStat_comp {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    {d : α → K → ℝ} (Rn : Matrix rr K ℝ) (hXt : Measurable Xt) (hOm : Measurable Om)
    (hd : Measurable d) : Measurable fun a => restrictedStat (Xt a) (Om a) Rn (d a) :=
  (WithLp.measurable_toLp 2 (rr → ℝ)).comp
    (measurable_mulVec_comp (measurable_invSqrt_restrictedVar Rn hXt hOm)
      (measurable_mulVec_comp measurable_const hd))

end Measurability

section HypothesesDischarged

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [(n : ℕ) → DecidableEq (O n)] in
/-- `ν` is measurable, since `hdep` provides a dependency graph at some `ω`. -/
theorem meas_of_ae_depGraph {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : ∀ n, O n → Ω → ℝ} {Dn : ℕ → Ω → ℕ}
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1) :
    ∀ n o, Measurable (ν n o) := by
  obtain ⟨_, Dv, _⟩ := hdep.exists
  exact fun n o => (Dv n).meas o

omit [(n : ℕ) → DecidableEq (O n)] [StandardBorelSpace Ω] in
/-- `β̂_JM − β` is measurable, from the score representation and the measurability of `X̃` and
`ν`. -/
theorem measurable_score_of_hscore {Xt : ∀ n, Ω → Matrix (O n) K ℝ}
    {ν : ∀ n, O n → Ω → ℝ} {bhat : ℕ → Ω → (K → ℝ)} {β : ℕ → K → ℝ}
    (hXtm : ∀ n, Measurable (Xt n)) (hnum : ∀ n o, Measurable (ν n o))
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y))) :
    ∀ n, Measurable fun y => bhat n y - β n := by
  intro n
  have h : (fun y => bhat n y - β n)
      = fun y => ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)) :=
    funext (hscore n)
  rw [h]
  exact measurable_mulVec_comp
    (Multiway.Wald.measurable_matrix_inv.comp
      (measurable_matrix_mul_rect (measurable_matrix_transpose (hXtm n)) (hXtm n)))
    (measurable_mulVec_comp (measurable_matrix_transpose (hXtm n))
      (Measurable.of_eval fun o => hnum n o))

omit [StandardBorelSpace Ω] in
/-- `X̃_n` as a matrix-valued map, from its entrywise `𝒟`-measurability. -/
theorem measurable_of_entrywise_D {m nn : Type*} {F : Ω → Matrix m nn ℝ}
    (h𝒟 : 𝒟 ≤ mΩ) (hF : ∀ i j, Measurable[𝒟] fun ω => F ω i j) : Measurable F :=
  Measurable.of_eval_matrix _ fun i j => (hF i j).mono h𝒟 le_rfl

/-- **Theorem 5(a)** in a unit direction, under the full measure, with `hWm` derived. -/
theorem cltcluster_a_general_betaJM_janson_unconditional_of_dep
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
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
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
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  have hXtm : ∀ n, Measurable (Xt n) := fun n => measurable_of_entrywise_D h𝒟 (hXtD n)
  have hOmm : ∀ n, Measurable (Om n) := fun n => measurable_of_entrywise_D h𝒟 (hOmD n)
  have hdm := measurable_score_of_hscore hXtm (meas_of_ae_depGraph hdep) hscore
  exact cltcluster_a_general_betaJM_janson_unconditional h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B Cnu hB0 hCnu0 hnu b hb
    (fun n => measurable_standardized_comp (Rn n) (hXtm n) (hOmm n) (hdm n) b)
    hdep hA hlmin hfloor hOmeq hmean hB hDn1 hDnN hrate

/-- **Theorem 5(a)**, vector form under the full measure, with `hWvm` derived. -/
theorem cltcluster_a_general_betaJM_janson_unconditional_vector_of_dep
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
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hXtm : ∀ n, Measurable (Xt n) := fun n => measurable_of_entrywise_D h𝒟 (hXtD n)
  have hOmm : ∀ n, Measurable (Om n) := fun n => measurable_of_entrywise_D h𝒟 (hOmD n)
  have hdm := measurable_score_of_hscore hXtm (meas_of_ae_depGraph hdep) hscore
  exact cltcluster_a_general_betaJM_janson_unconditional_vector h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B Cnu hB0 hCnu0 hnu
    (fun n => measurable_restrictedStat_comp (Rn n) (hXtm n) (hOmm n) (hdm n))
    hdep hA hlmin hfloor hOmeq hmean hB hDn1 hDnN hrate

end HypothesesDischarged

section ScoreDischargeJanson

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
variable {Dm : Type*} [Fintype Dm]

/-- **Theorem 5(a)** with the score representation `hscore`, the rank condition `hA` and `hOm`
derived from the model, identification and the normal equations defining `β̂_JM`, with
`Ω_n := Var(ν ∣ 𝒟)`. -/
theorem cltcluster_a_general_betaJM_janson_of_jm
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
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (secondMoment (μ n) (ν n)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  obtain ⟨hscore, hA⟩ :=
    score_and_rank_of_jm hwithin hid hiota hfe hmodel hJM (Rn := Rn) hR
  exact cltcluster_a_general_betaJM_janson μ Xt (fun n => secondMoment (μ n) (ν n)) Rn ν bhat β
    Dv hscore hA lmin hlmin hfloor (fun n => secondMoment_spec (μ n) (ν n)) hmean
    B Cnu hB0 hCnu0 hB hnu Dn hDn1 hDnN hdeg hrate b hb s

end ScoreDischargeJanson
/-! ### Section 8. The score representation at a random design

`SteinCluster.score_representation` is applied at each realization, so that `hscore` and `hA`
are derived when the design is random. -/

section UnconditionalScoreDischarge

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {Dm : Type*} [Fintype Dm]

omit [(n : ℕ) → DecidableEq (O n)] mΩ [StandardBorelSpace Ω] in
/-- The score representation and `hA` at a random design. -/
theorem score_and_rank_of_jm_random
    {rr : Type*} [Fintype rr]
    {Sm : ∀ n, Ω → Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, Ω → ((K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n))}
    {Xt : ∀ n, Ω → Matrix (O n) K ℝ}
    (hwithin : ∀ n y, IsWithinMatrix (⨆ k, Sm n y k) (Xop n y) (Xt n y))
    (hid : ∀ n y, Multiway.Identified (⨆ k, Sm n y k) (Xop n y))
    {iota : ∀ n, Ω → EuclideanSpace ℝ (O n)} (hiota : ∀ n y, iota n y ∈ (⨆ k, Sm n y k))
    {fe : ∀ n, Ω → Dm → EuclideanSpace ℝ (O n)} (hfe : ∀ n y m, fe n y m ∈ Sm n y m)
    {yv : ∀ n, Ω → EuclideanSpace ℝ (O n)} {ν : ∀ n, O n → Ω → ℝ}
    {bhat : ℕ → Ω → (K → ℝ)} {β : ℕ → K → ℝ}
    (hmodel : ∀ n y, yv n y
      = Xop n y (β n) + (∑ m, fe n y m) + WithLp.toLp 2 (fun o => ν n o y))
    (hJM : ∀ n y, Multiway.IsAugSlope
      (Multiway.jmControls (iota n y) (⨆ k, Sm n y k) (Xop n y)) (Xop n y) (yv n y) (bhat n y))
    {Rn : ℕ → Matrix rr K ℝ} (hR : ∀ n, Function.Injective ((Rn n)ᵀ).mulVec) :
    (∀ n y, bhat n y - β n
        = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
      ∧ (∀ y : Ω, ∀ n, Function.Injective (scoreMap (Xt n y) (Rn n)).mulVec) := by
  refine ⟨fun n y => ?_, fun y n => injective_scoreMap_mulVec
    (isUnit_det_gram_of_identified (hwithin n y) (hid n y)) (hR n)⟩
  simpa using score_representation (Sm := Sm n y) (hwithin n y) (hid n y) (hiota n y)
    (fun m => hfe n y m) (hmodel n y) (hJM n y)

/-- **Theorem 5(a)** under the full measure, at a random design, as `⟶ᵈ N(0, I_r)`, assuming
the model, identification, the normal equations defining `β̂_JM`, full row rank of `𝓡_n`,
`𝒟`-measurability of `X̃_n` and `Ω_n`, `Ω_n = Var(ν ∣ 𝒟)`, the variance floor, the moment
bounds, the dependency structure and the rate. -/
theorem cltcluster_a_general_betaJM_janson_unconditional_vector_of_jm
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    {Sm : ∀ n, Ω → Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, Ω → ((K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n))}
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix rr K ℝ)
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
    (hR : ∀ n, Function.Injective ((Rn n)ᵀ).mulVec)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  obtain ⟨hscore, hA⟩ :=
    score_and_rank_of_jm_random hwithin hid hiota hfe hmodel hJM (Rn := Rn) hR
  exact cltcluster_a_general_betaJM_janson_unconditional_vector_of_dep h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B Cnu hB0 hCnu0 hnu hdep
    (Filter.Eventually.of_forall hA) hlmin hfloor hOmeq hmean hB hDn1 hDnN hrate

end UnconditionalScoreDischarge
/-! ### Section 9. Random `𝒟`-measurable restriction matrices

Here `𝓡_n` is a sequence of `𝒟`-measurable `r × K` matrices. The conditional argument is applied
at `𝓡_n(ω)`, freezing `𝓡_n` alongside `X̃_n` and `Ω_n`. -/

section RandomRestriction

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {α : Type*} [MeasurableSpace α]
variable {O K : Type*} [Fintype O] [Fintype K] [DecidableEq K]
variable {rr : Type*} [Fintype rr] [DecidableEq rr]

omit [Fintype rr] [DecidableEq rr] in
/-- `A_n := (X̃'X̃)^{-1}𝓡_n'` is measurable in both arguments. -/
theorem measurable_scoreMap_comp_rand {Xt : α → Matrix O K ℝ} {Rv : α → Matrix rr K ℝ}
    (hXt : Measurable Xt) (hRv : Measurable Rv) :
    Measurable fun a => scoreMap (Xt a) (Rv a) :=
  measurable_matrix_mul_rect
    (Multiway.Wald.measurable_matrix_inv.comp
      (measurable_matrix_mul_rect (measurable_matrix_transpose hXt) hXt))
    (measurable_matrix_transpose hRv)

omit [DecidableEq rr] in
/-- `𝒱_n := A_n'Ω_nA_n` is measurable in all three arguments. -/
theorem measurable_restrictedVar_comp_rand {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    {Rv : α → Matrix rr K ℝ} (hXt : Measurable Xt) (hOm : Measurable Om)
    (hRv : Measurable Rv) : Measurable fun a => restrictedVar (Xt a) (Om a) (Rv a) :=
  measurable_matrix_mul_rect
    (measurable_matrix_mul_rect
      (measurable_matrix_transpose (measurable_scoreMap_comp_rand hXt hRv))
      (measurable_scoreVar_comp hXt hOm))
    (measurable_scoreMap_comp_rand hXt hRv)

/-- `𝒱_n^{-1/2}` is measurable in all three arguments. -/
theorem measurable_invSqrt_restrictedVar_rand {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    {Rv : α → Matrix rr K ℝ} (hXt : Measurable Xt) (hOm : Measurable Om) (hRv : Measurable Rv) :
    Measurable fun a => (sqrtPD (restrictedVar (Xt a) (Om a) (Rv a)))⁻¹ :=
  Multiway.Wald.measurable_matrix_inv.comp
    (Multiway.Wald.measurable_sqrtPD.comp (measurable_restrictedVar_comp_rand hXt hOm hRv))

/-- The scalar standardized statistic is measurable at a random `𝓡_n`. -/
theorem measurable_standardized_comp_rand {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    {Rv : α → Matrix rr K ℝ} {d : α → K → ℝ}
    (hXt : Measurable Xt) (hOm : Measurable Om) (hRv : Measurable Rv) (hd : Measurable d)
    (b : rr → ℝ) :
    Measurable fun a =>
      b ⬝ᵥ ((sqrtPD (restrictedVar (Xt a) (Om a) (Rv a)))⁻¹ *ᵥ (Rv a *ᵥ d a)) :=
  measurable_dotProduct_const b
    (measurable_mulVec_comp (measurable_invSqrt_restrictedVar_rand hXt hOm hRv)
      (measurable_mulVec_comp hRv hd))

/-- The vector standardized statistic is measurable at a random `𝓡_n`. -/
theorem measurable_restrictedStat_comp_rand {Xt : α → Matrix O K ℝ} {Om : α → Matrix O O ℝ}
    {Rv : α → Matrix rr K ℝ} {d : α → K → ℝ}
    (hXt : Measurable Xt) (hOm : Measurable Om) (hRv : Measurable Rv) (hd : Measurable d) :
    Measurable fun a => restrictedStat (Xt a) (Om a) (Rv a) (d a) :=
  (WithLp.measurable_toLp 2 (rr → ℝ)).comp
    (measurable_mulVec_comp (measurable_invSqrt_restrictedVar_rand hXt hOm hRv)
      (measurable_mulVec_comp hRv hd))

end RandomRestriction

section RandomRestrictionCLT

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [(n : ℕ) → DecidableEq (O n)] in
/-- Freezing the design, the variance and `𝓡_n` at almost every `ω`, entry by entry. -/
theorem ae_ae_eq_frozen_restriction (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P]
    {rr : Type*} [Fintype rr]
    {Xt : ∀ n, Ω → Matrix (O n) K ℝ} {Om : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    {Rv : ℕ → Ω → Matrix rr K ℝ}
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hRD : ∀ n i k, Measurable[𝒟] fun ω => Rv n ω i k) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Xt n y = Xt n ω ∧ Om n y = Om n ω ∧ Rv n y = Rv n ω := by
  refine ae_all_iff.2 fun n => ?_
  have h1 : ∀ᵐ ω ∂P, ∀ p : O n × K, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Xt n y p.1 p.2 = Xt n ω p.1 p.2 :=
    ae_all_iff.2 fun p => ae_ae_eq_condExpKernel h𝒟 P (hXtD n p.1 p.2)
  have h2 : ∀ᵐ ω ∂P, ∀ p : O n × O n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Om n y p.1 p.2 = Om n ω p.1 p.2 :=
    ae_all_iff.2 fun p => ae_ae_eq_condExpKernel h𝒟 P (hOmD n p.1 p.2)
  have h3 : ∀ᵐ ω ∂P, ∀ p : rr × K, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Rv n y p.1 p.2 = Rv n ω p.1 p.2 :=
    ae_all_iff.2 fun p => ae_ae_eq_condExpKernel h𝒟 P (hRD n p.1 p.2)
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  filter_upwards [ae_all_iff.2 hω1, ae_all_iff.2 hω2, ae_all_iff.2 hω3] with y hy1 hy2 hy3
  exact ⟨Matrix.ext fun o a => hy1 (o, a), Matrix.ext fun o o' => hy2 (o, o'),
    Matrix.ext fun i a => hy3 (i, a)⟩

/-- **Theorem 5(a)** in a unit direction under the full measure, with `𝓡_n` random and
`𝒟`-measurable. -/
theorem cltcluster_a_general_betaJM_janson_unconditional_randomR
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
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
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
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
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
  · filter_upwards [hdep, hA, hlmin, hfloor, hOmeq, hmean, hB, hDn1, hDnN, hrate]
      with ω hdepω hAω hlminω hfloorω hOmω hmeanω hBω hDn1ω hDnNω hrateω
    obtain ⟨Dv, hdegω⟩ := hdepω
    have hPD : ∀ n, (scoreVar (Xt n ω) (Om n ω)).PosDef := fun n =>
      Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlminω n)) (hfloorω n)
    refine cltcluster_a_general_janson_tendstoInDistribution
      (Ω := fun _ => Ω) (fun _ => condExpKernel P 𝒟 ω)
      (fun n => scoreArray (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rv n ω) b) (ν n))
      (fun n => scoreArrayDepGraph (Dv n) (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rv n ω) b))
      (fun n => B * Cnu / Real.sqrt (lmin n ω)) (fun n => Dn n ω)
      (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ ?_ hDn1ω hDnNω ?_ ?_ ?_
    · exact fun n o y => abs_scoreArray_le (hPD n) (hAω n) (hlminω n) (hfloorω n) hB0
        (hBω n) (hnu n) hb o y
    · intro n o
      rw [nbhd_scoreArrayDepGraph]
      exact hdegω n o
    · exact fun n o => integral_scoreArray (fun o => hmeanω n o) (Xt n ω) _ o
    · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hAω n)
        (fun o => (Dv n).meas o) (hnu n) (hOmω n) hb
    · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
        (by simpa using hrateω.const_mul (8 * B ^ 4 * Cnu ^ 4))
      exact firstRate_le (hDn1ω n) (hlminω n)

/-- **Theorem 5(a)** with `𝓡_n` a sequence of `𝒟`-measurable `r × K` matrices of full row rank
almost surely: `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)` under the full measure. -/
theorem cltcluster_a_general_betaJM_janson_unconditional_vector_randomR
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
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rv n ω)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
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
  have h := cltcluster_a_general_betaJM_janson_unconditional_randomR h𝒟 P Xt Om Rv ν bhat β
    hXtD hOmD hRD hscore lmin Dn B Cnu hB0 hCnu0 hnu (WithLp.ofLp b)
    (dotProduct_self_ofLp b hb) hdep hA hlmin hfloor hOmeq hmean hB hDn1 hDnN hrate
  have hfun : (fun (n : ℕ) (y : Ω) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rv n y)))⁻¹ *ᵥ
          (Rv n y *ᵥ (bhat n y - β n))))
      = fun (n : ℕ) (y : Ω) =>
        ⟪restrictedStat (Xt n y) (Om n y) (Rv n y) (bhat n y - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

end RandomRestrictionCLT
/-! ### Section 10. Theorem 5(a)

Sections 8 and 9 combined: `𝓡_n` random and `𝒟`-measurable, and the score representation and
`hA` derived from the model and Theorem 3. -/

section PrintedA

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {Dm : Type*} [Fintype Dm]

omit [(n : ℕ) → DecidableEq (O n)] mΩ [StandardBorelSpace Ω] in
/-- The score representation at a random design. -/
theorem score_of_jm_random
    {Sm : ∀ n, Ω → Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, Ω → ((K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n))}
    {Xt : ∀ n, Ω → Matrix (O n) K ℝ}
    (hwithin : ∀ n y, IsWithinMatrix (⨆ k, Sm n y k) (Xop n y) (Xt n y))
    (hid : ∀ n y, Multiway.Identified (⨆ k, Sm n y k) (Xop n y))
    {iota : ∀ n, Ω → EuclideanSpace ℝ (O n)} (hiota : ∀ n y, iota n y ∈ (⨆ k, Sm n y k))
    {fe : ∀ n, Ω → Dm → EuclideanSpace ℝ (O n)} (hfe : ∀ n y m, fe n y m ∈ Sm n y m)
    {yv : ∀ n, Ω → EuclideanSpace ℝ (O n)} {ν : ∀ n, O n → Ω → ℝ}
    {bhat : ℕ → Ω → (K → ℝ)} {β : ℕ → K → ℝ}
    (hmodel : ∀ n y, yv n y
      = Xop n y (β n) + (∑ m, fe n y m) + WithLp.toLp 2 (fun o => ν n o y))
    (hJM : ∀ n y, Multiway.IsAugSlope
      (Multiway.jmControls (iota n y) (⨆ k, Sm n y k) (Xop n y)) (Xop n y) (yv n y) (bhat n y)) :
    ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)) := fun n y => by
  simpa using score_representation (Sm := Sm n y) (hwithin n y) (hid n y) (hiota n y)
    (fun m => hfe n y m) (hmodel n y) (hJM n y)

/-- **Theorem 5(a)** (asymptotic normality under multiway clustering). Under the model, the
exogeneity condition, identification, Regime 3 of the dependence assumption, the variance floor
and the accumulation condition, with `𝓡_n` a sequence of `𝒟`-measurable `r × K` matrices of full
row rank almost surely and `sup_o|ν_o| ≤ C_ν` almost surely,
`𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)`.

`hmodel`/`hJM`: the model and the normal equations defining `β̂_JM`; `hwithin`/`hid`:
`X̃ := Q_[Δ]X` and identification; `hOmeq`/`hOmD`: `Ω_n := Var(ν ∣ 𝒟)` and its
`𝒟`-measurability; `hdep`: the dependency structure; `hfloor`/`hlmin`: the variance floor;
`hnu`: the uniform bound; `hrate`: the accumulation condition; `hR`/`hRD`: full row rank of
`𝓡_n` and its `𝒟`-measurability. -/
theorem cltcluster_a_general_betaJM_janson_printed
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
    (lmin : ℕ → Ω → ℝ) (Dn : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ Dn n ω + 1)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hDn1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Dn n ω)
    (hDnN : ∀ᵐ ω ∂P, ∀ n, Dn n ω ≤ Fintype.card (O n))
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y) (Om n y) (Rv n y) (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rv n ω)).mulVec := by
    filter_upwards [hR] with ω hRω n
    exact injective_scoreMap_mulVec
      (isUnit_det_gram_of_identified (hwithin n ω) (hid n ω)) (hRω n)
  exact cltcluster_a_general_betaJM_janson_unconditional_vector_randomR h𝒟 P Xt Om Rv ν bhat β
    hXtD hOmD hRD (score_of_jm_random hwithin hid hiota hfe hmodel hJM)
    lmin Dn B Cnu hB0 hCnu0 hnu hdep hA hlmin hfloor hOmeq hmean hB hDn1 hDnN hrate

end PrintedA
end Multiway.ClusterJanson
