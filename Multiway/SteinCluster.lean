import Multiway.SteinCLT.CLT
import Multiway.SteinCLT.DepGraphCLT
import Multiway.Multilinear
import Multiway.Restricted
import Multiway.CLTMartingale
import Multiway.JointProjection
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.CramerWold
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Asymptotic normality under multiway clustering

This file formalizes Theorem 5 of the paper (asymptotic normality under multiway clustering),
parts (a) and (b), through a Stein dependency-graph bound. For the standardized score array
`X_{n,o} = (a_n'x̃_o)ν_o` the two Stein error terms are `E₁ = Var(∑_o X_o T_o)` and
`E₂ = ∑_o E[|X_o| T_o²]`, with `T_o = ∑_{k ∼ o} X_k`. With one clustering dimension (`J = 1`)
both are controlled by `Ḡ_nφ_n`; for an arbitrary sharing relation of degree at most `D_n` the
rate condition is `(n/D_n)^{1/3}δ_n → 0`.

## Main results

* `cltcluster_a_oneDimension_betaJM`: part (a) at `J = 1` for `β̂_JM`.
* `cltcluster_a_general_betaJM`: part (a) for an arbitrary sharing relation.
* `cltcluster_b_general_betaJM`: part (b), by truncation and fourth moments.
* `cltcluster_a_unconditional_of_design`: removal of the conditioning on the design σ-field.
* `cltcluster_a_unconditional_vector_of_design`: the vector limit `N(0, I_r)` by Cramér–Wold.
-/

namespace Multiway.SteinCluster

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators
open Causalean.Mathlib.Probability.SteinMethod

section Cluster

variable {O : Type*} [Fintype O]
variable {Gp : Type*} [Fintype Gp] [DecidableEq Gp]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The cluster (fibre) of `γ` under the single maintained clustering map `g`.  At `J = 1` this
is the dependence neighbourhood of each of its members. -/
def cluster (g : O → Gp) (γ : Gp) : Finset O :=
  Finset.univ.filter (fun o => g o = γ)

omit [Fintype Gp] in
@[simp] theorem mem_cluster {g : O → Gp} {γ : Gp} {o : O} : o ∈ cluster g γ ↔ g o = γ := by
  simp [cluster]

/-- `S_γ := ∑_{k ∈ γ} X_k`, the cluster sum. -/
noncomputable def clusterSum (X : O → Ω → ℝ) (g : O → Gp) (γ : Gp) : Ω → ℝ :=
  fun ω => ∑ o ∈ cluster g γ, X o ω

omit [Fintype Gp] in
theorem measurable_clusterSum {X : O → Ω → ℝ} (hX : ∀ o, Measurable (X o)) (g : O → Gp)
    (γ : Gp) : Measurable (clusterSum X g γ) :=
  Finset.measurable_sum _ (fun o _ => hX o)

omit [MeasurableSpace Ω] in
/-- The cluster sums add up to the standardized sum. -/
theorem sum_clusterSum (X : O → Ω → ℝ) (g : O → Gp) (ω : Ω) :
    ∑ γ, clusterSum X g γ ω = ∑ o, X o ω :=
  Finset.sum_fiberwise (Finset.univ : Finset O) g (fun o => X o ω)

/-- `Finset.sum_fiberwise` stated in terms of `cluster`. -/
theorem sum_fiberwise_cluster {M : Type*} [AddCommMonoid M] (g : O → Gp) (f : O → M) :
    ∑ γ, ∑ o ∈ cluster g γ, f o = ∑ o, f o :=
  Finset.sum_fiberwise (Finset.univ : Finset O) g f

/-- `Finset.sum_fiberwise'` stated in terms of `cluster`. -/
theorem sum_fiberwise_cluster' {M : Type*} [AddCommMonoid M] (g : O → Gp) (f : Gp → M) :
    ∑ γ, ∑ _o ∈ cluster g γ, f γ = ∑ o, f (g o) :=
  Finset.sum_fiberwise' (Finset.univ : Finset O) g f

omit [Fintype Gp] [MeasurableSpace Ω] in
theorem abs_clusterSum_le {X : O → Ω → ℝ} {g : O → Gp} {φ : ℝ} (hφ : ∀ o ω, |X o ω| ≤ φ)
    (γ : Gp) (ω : Ω) : |clusterSum X g γ ω| ≤ ((cluster g γ).card : ℝ) * φ := by
  calc |clusterSum X g γ ω| ≤ ∑ o ∈ cluster g γ, |X o ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _o ∈ cluster g γ, φ := Finset.sum_le_sum (fun o _ => hφ o ω)
    _ = ((cluster g γ).card : ℝ) * φ := by rw [Finset.sum_const, nsmul_eq_mul]

omit [Fintype Gp] [MeasurableSpace Ω] in
/-- With `Ḡ` a bound on the cluster sizes, `|S_γ| ≤ Ḡφ`. -/
theorem abs_clusterSum_le' {X : O → Ω → ℝ} {g : O → Gp} {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ : ∀ o ω, |X o ω| ≤ φ) {Gb : ℕ} (hGb : ∀ γ, (cluster g γ).card ≤ Gb)
    (γ : Gp) (ω : Ω) : |clusterSum X g γ ω| ≤ (Gb : ℝ) * φ :=
  (abs_clusterSum_le hφ γ ω).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hGb γ) hφ0)

omit [Fintype Gp] in
/-- At `J = 1` the closed dependence neighbourhood of `o` is its cluster. -/
theorem nbhd_eq_cluster {X : O → Ω → ℝ} {g : O → Gp} (D : DepGraph X μ)
    (hshare : ∀ o o', D.G o o' ↔ g o = g o') (o : O) : D.nbhd o = cluster g (g o) := by
  ext j
  rw [D.mem_nbhd_iff, mem_cluster, hshare]
  exact eq_comm

omit [Fintype Gp] in
theorem nbhdSum_eq_clusterSum {X : O → Ω → ℝ} {g : O → Gp} (D : DepGraph X μ)
    (hshare : ∀ o o', D.G o o' ↔ g o = g o') (o : O) (ω : Ω) :
    nbhdSum X D.nbhd o ω = clusterSum X g (g o) ω := by
  simp only [nbhdSum, clusterSum, nbhd_eq_cluster D hshare o]

omit [Fintype Gp] in
/-- The sums over distinct clusters are independent. -/
theorem indepFun_clusterSum {X : O → Ω → ℝ} {g : O → Gp} (D : DepGraph X μ)
    (hshare : ∀ o o', D.G o o' ↔ g o = g o') {γ γ' : Gp} (hne : γ ≠ γ') :
    IndepFun (clusterSum X g γ) (clusterSum X g γ') μ := by
  have hnoedge : ∀ a ∈ cluster g γ, ∀ b ∈ cluster g γ', ¬ D.G a b := by
    intro a ha b hb hab
    rw [hshare] at hab
    rw [mem_cluster] at ha hb
    exact hne (by rw [← ha, hab]; exact hb)
  have h := D.indep (cluster g γ) (cluster g γ') hnoedge
  have hm : ∀ s : Finset O, Measurable (fun v : (↥s → ℝ) => ∑ k, v k) := by
    intro s
    exact Finset.measurable_sum _ (fun k _ => measurable_pi_apply k)
  have h2 := h.comp (hm (cluster g γ)) (hm (cluster g γ'))
  have e1 : ((fun v : (↥(cluster g γ) → ℝ) => ∑ k, v k) ∘ fun ω (k : ↥(cluster g γ)) => X k ω)
      = clusterSum X g γ := by
    funext ω
    simpa [clusterSum] using Finset.sum_coe_sort (cluster g γ) (fun o => X o ω)
  have e2 : ((fun v : (↥(cluster g γ') → ℝ) => ∑ k, v k) ∘ fun ω (k : ↥(cluster g γ')) => X k ω)
      = clusterSum X g γ' := by
    funext ω
    simpa [clusterSum] using Finset.sum_coe_sort (cluster g γ') (fun o => X o ω)
  rwa [e1, e2] at h2

end Cluster

section Errors

variable {O : Type*} [Fintype O]
variable {Gp : Type*} [Fintype Gp] [DecidableEq Gp]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded measurable function is integrable under a probability measure. -/
private theorem integrable_of_bdd {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact h ω))

/-- A bounded measurable function is in `L²` under a probability measure. -/
private theorem memLp_two_of_bdd {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ ω, |f ω| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact h ω))

variable {X : O → Ω → ℝ} {g : O → Gp}

omit [Fintype Gp] in
theorem integral_clusterSum_eq_zero {φ : ℝ} (hX : ∀ o, Measurable (X o))
    (hφ : ∀ o ω, |X o ω| ≤ φ) (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (γ : Gp) :
    ∫ ω, clusterSum X g γ ω ∂μ = 0 := by
  simp only [clusterSum]
  rw [MeasureTheory.integral_finsetSum _ (fun o _ => integrable_of_bdd (hX o) (hφ o))]
  simp [hmean]

omit [Fintype Gp] in
theorem variance_clusterSum_eq {φ : ℝ} (hX : ∀ o, Measurable (X o))
    (hφ : ∀ o ω, |X o ω| ≤ φ) (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (γ : Gp) :
    variance (clusterSum X g γ) μ = ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ :=
  variance_of_integral_eq_zero (measurable_clusterSum hX g γ).aemeasurable
    (integral_clusterSum_eq_zero hX hφ hmean γ)

/-- The cluster variances sum to `1`, since distinct clusters are independent and the total
variance is standardized to `1`. -/
theorem sum_integral_clusterSum_sq (D : DepGraph X μ)
    (hshare : ∀ o o', D.G o o' ↔ g o = g o') {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ : ∀ o ω, |X o ω| ≤ φ) {Gb : ℕ} (hGb : ∀ γ, (cluster g γ).card ≤ Gb)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (hvar : ∫ ω, (depSum X ω) ^ 2 ∂μ = 1) :
    ∑ γ, ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ = 1 := by
  have hX : ∀ o, Measurable (X o) := fun o => D.meas o
  have hmem : ∀ γ : Gp, MemLp (clusterSum X g γ) 2 μ := fun γ =>
    memLp_two_of_bdd (measurable_clusterSum hX g γ) (abs_clusterSum_le' hφ0 hφ hGb γ)
  have hpair : ((Finset.univ : Finset Gp) : Set Gp).Pairwise
      (fun i j => IndepFun (clusterSum X g i) (clusterSum X g j) μ) := by
    intro i _ j _ hij
    exact indepFun_clusterSum D hshare hij
  have hsum := IndepFun.variance_sum (μ := μ) (X := fun γ : Gp => clusterSum X g γ)
    (s := Finset.univ) (fun γ _ => hmem γ) hpair
  have hfun : (∑ γ ∈ Finset.univ, clusterSum X g γ) = depSum X := by
    funext ω
    simpa [depSum] using sum_clusterSum X g ω
  rw [hfun] at hsum
  have hmean0 : ∫ ω, depSum X ω ∂μ = 0 := by
    simp only [depSum]
    rw [MeasureTheory.integral_finsetSum _ (fun o _ => integrable_of_bdd (hX o) (hφ o))]
    simp [hmean]
  have hmeasSum : Measurable (depSum X) :=
    Finset.measurable_sum _ (fun o _ => hX o)
  have hlhs : variance (depSum X) μ = 1 := by
    rw [variance_of_integral_eq_zero hmeasSum.aemeasurable hmean0, hvar]
  rw [hlhs] at hsum
  calc ∑ γ, ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ
      = ∑ γ, variance (clusterSum X g γ) μ :=
        Finset.sum_congr rfl (fun γ _ => (variance_clusterSum_eq hX hφ hmean γ).symm)
    _ = 1 := hsum.symm

/-- The second Stein error term at `J = 1`: `∑_o E[|X_o|T_o²] ≤ Ḡφ`. -/
theorem secondError_le (D : DepGraph X μ) (hshare : ∀ o o', D.G o o' ↔ g o = g o')
    {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : ∀ o ω, |X o ω| ≤ φ)
    {Gb : ℕ} (hGb : ∀ γ, (cluster g γ).card ≤ Gb)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (hvar : ∫ ω, (depSum X ω) ^ 2 ∂μ = 1) :
    ∑ o, ∫ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ∂μ ≤ (Gb : ℝ) * φ := by
  have hX : ∀ o, Measurable (X o) := fun o => D.meas o
  have hSbd : ∀ (γ : Gp) (ω : Ω), |clusterSum X g γ ω| ≤ (Gb : ℝ) * φ :=
    abs_clusterSum_le' hφ0 hφ hGb
  have hSq : ∀ (γ : Gp) (ω : Ω), (clusterSum X g γ ω) ^ 2 ≤ ((Gb : ℝ) * φ) ^ 2 := by
    intro γ ω
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hSbd γ ω) 2
  have hintsq : ∀ γ : Gp, Integrable (fun ω => (clusterSum X g γ ω) ^ 2) μ := by
    intro γ
    refine integrable_of_bdd ((measurable_clusterSum hX g γ).pow_const 2)
      (C := ((Gb : ℝ) * φ) ^ 2) (fun ω => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hSq γ ω
  have hnn : ∀ γ : Gp, 0 ≤ ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ := fun γ =>
    integral_nonneg (fun ω => sq_nonneg _)
  -- pull the bound `|X_o| ≤ φ` out of each term
  have step1 : ∀ o : O, ∫ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ∂μ
      ≤ φ * ∫ ω, (clusterSum X g (g o) ω) ^ 2 ∂μ := by
    intro o
    have hrw : (fun ω => |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2)
        = fun ω => |X o ω| * (clusterSum X g (g o) ω) ^ 2 := by
      funext ω; rw [nbhdSum_eq_clusterSum D hshare o ω]
    rw [hrw, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono ?_ ((hintsq (g o)).const_mul φ) (fun ω => ?_)
    · refine integrable_of_bdd
        (((hX o).abs).mul ((measurable_clusterSum hX g (g o)).pow_const 2))
        (C := φ * ((Gb : ℝ) * φ) ^ 2) (fun ω => ?_)
      have hnn1 : (0 : ℝ) ≤ |X o ω| * (clusterSum X g (g o) ω) ^ 2 := by positivity
      rw [abs_of_nonneg hnn1]
      exact mul_le_mul (hφ o ω) (hSq (g o) ω) (sq_nonneg _) hφ0
    · exact mul_le_mul_of_nonneg_right (hφ o ω) (sq_nonneg _)
  -- regroup the sum over observations into a sum over clusters
  have step2 : ∑ o : O, ∫ ω, (clusterSum X g (g o) ω) ^ 2 ∂μ
      = ∑ γ : Gp, ((cluster g γ).card : ℝ) * ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ := by
    rw [← sum_fiberwise_cluster' g (fun γ => ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ)]
    exact Finset.sum_congr rfl (fun γ _ => by rw [Finset.sum_const, nsmul_eq_mul])
  have step3 : ∑ γ : Gp, ((cluster g γ).card : ℝ) * ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ
      ≤ (Gb : ℝ) := by
    have hone := sum_integral_clusterSum_sq D hshare hφ0 hφ hGb hmean hvar
    calc ∑ γ : Gp, ((cluster g γ).card : ℝ) * ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ
        ≤ ∑ γ : Gp, (Gb : ℝ) * ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ :=
          Finset.sum_le_sum (fun γ _ =>
            mul_le_mul_of_nonneg_right (by exact_mod_cast hGb γ) (hnn γ))
      _ = (Gb : ℝ) * ∑ γ : Gp, ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ := by
          rw [Finset.mul_sum]
      _ = (Gb : ℝ) := by rw [hone, mul_one]
  calc ∑ o, ∫ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ∂μ
      ≤ ∑ o : O, φ * ∫ ω, (clusterSum X g (g o) ω) ^ 2 ∂μ :=
        Finset.sum_le_sum (fun o _ => step1 o)
    _ = φ * ∑ o : O, ∫ ω, (clusterSum X g (g o) ω) ^ 2 ∂μ := by rw [Finset.mul_sum]
    _ = φ * ∑ γ : Gp, ((cluster g γ).card : ℝ) * ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ := by
        rw [step2]
    _ ≤ φ * (Gb : ℝ) := mul_le_mul_of_nonneg_left step3 hφ0
    _ = (Gb : ℝ) * φ := mul_comm _ _

omit [IsProbabilityMeasure μ] in
/-- At `J = 1`, `∑_o X_o T_o = ∑_γ S_γ²`. Since the neighbourhood is closed, the localized
double sum is `∑_{o ∼ o'} X_o X_{o'}`, and this equals the sum of squared cluster sums. -/
theorem sum_mul_nbhdSum_eq (D : DepGraph X μ) (hshare : ∀ o o', D.G o o' ↔ g o = g o')
    (ω : Ω) : ∑ o, X o ω * nbhdSum X D.nbhd o ω = ∑ γ, (clusterSum X g γ ω) ^ 2 := by
  have h1 : ∀ o : O, X o ω * nbhdSum X D.nbhd o ω = X o ω * clusterSum X g (g o) ω := by
    intro o; rw [nbhdSum_eq_clusterSum D hshare o ω]
  rw [Finset.sum_congr rfl (fun o _ => h1 o),
    ← sum_fiberwise_cluster g (fun o => X o ω * clusterSum X g (g o) ω)]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  have h2 : ∀ o ∈ cluster g γ, X o ω * clusterSum X g (g o) ω = X o ω * clusterSum X g γ ω := by
    intro o ho
    rw [mem_cluster.mp ho]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
  simp [clusterSum, sq]

/-- The first Stein error term at `J = 1`: `Var(∑_o X_o T_o) ≤ (Ḡφ)²`, from cluster
independence. -/
theorem firstError_le (D : DepGraph X μ) (hshare : ∀ o o', D.G o o' ↔ g o = g o')
    {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : ∀ o ω, |X o ω| ≤ φ)
    {Gb : ℕ} (hGb : ∀ γ, (cluster g γ).card ≤ Gb)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (hvar : ∫ ω, (depSum X ω) ^ 2 ∂μ = 1) :
    variance (fun ω => ∑ o, X o ω * nbhdSum X D.nbhd o ω) μ ≤ ((Gb : ℝ) * φ) ^ 2 := by
  have hX : ∀ o, Measurable (X o) := fun o => D.meas o
  have hSbd : ∀ (γ : Gp) (ω : Ω), |clusterSum X g γ ω| ≤ (Gb : ℝ) * φ :=
    abs_clusterSum_le' hφ0 hφ hGb
  have hSq : ∀ (γ : Gp) (ω : Ω), (clusterSum X g γ ω) ^ 2 ≤ ((Gb : ℝ) * φ) ^ 2 := by
    intro γ ω
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hSbd γ ω) 2
  have hmeasSq : ∀ γ : Gp, Measurable (fun ω => (clusterSum X g γ ω) ^ 2) := fun γ =>
    (measurable_clusterSum hX g γ).pow_const 2
  -- rewrite the localized double sum as the sum of squared cluster sums
  have hfun : (fun ω => ∑ o, X o ω * nbhdSum X D.nbhd o ω)
      = ∑ γ ∈ Finset.univ, (fun ω => (clusterSum X g γ ω) ^ 2) := by
    funext ω
    rw [sum_mul_nbhdSum_eq D hshare ω]
    simp
  rw [hfun]
  -- the squared cluster sums are pairwise independent, so their variances add
  have hmem : ∀ γ : Gp, MemLp (fun ω => (clusterSum X g γ ω) ^ 2) 2 μ := by
    intro γ
    refine memLp_two_of_bdd (hmeasSq γ) (C := ((Gb : ℝ) * φ) ^ 2) (fun ω => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hSq γ ω
  have hpair : ((Finset.univ : Finset Gp) : Set Gp).Pairwise
      (fun i j => IndepFun (fun ω => (clusterSum X g i ω) ^ 2)
        (fun ω => (clusterSum X g j ω) ^ 2) μ) := by
    intro i _ j _ hij
    exact (indepFun_clusterSum D hshare hij).comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2)
  rw [IndepFun.variance_sum (fun γ _ => hmem γ) hpair]
  -- `Var(S_γ²) ≤ E[S_γ⁴] ≤ (Ḡφ)² E[S_γ²]`, and the `E[S_γ²]` add to `1`
  have hnn : ∀ γ : Gp, 0 ≤ ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ := fun γ =>
    integral_nonneg (fun ω => sq_nonneg _)
  have hintsq : ∀ γ : Gp, Integrable (fun ω => (clusterSum X g γ ω) ^ 2) μ := fun γ =>
    (hmem γ).integrable (by norm_num)
  have hint4 : ∀ γ : Gp, Integrable (fun ω => (clusterSum X g γ ω) ^ 4) μ := by
    intro γ
    refine integrable_of_bdd ((measurable_clusterSum hX g γ).pow_const 4)
      (C := ((Gb : ℝ) * φ) ^ 4) (fun ω => ?_)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hSbd γ ω) 4
  have key : ∀ γ : Gp, variance (fun ω => (clusterSum X g γ ω) ^ 2) μ
      ≤ ((Gb : ℝ) * φ) ^ 2 * ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ := by
    intro γ
    have h1 : variance (fun ω => (clusterSum X g γ ω) ^ 2) μ
        ≤ ∫ ω, ((clusterSum X g γ ω) ^ 2) ^ 2 ∂μ := by
      simpa using variance_le_expectation_sq (μ := μ)
        (X := fun ω => (clusterSum X g γ ω) ^ 2) (hmeasSq γ).aestronglyMeasurable
    refine h1.trans ?_
    have h2 : ∀ ω, ((clusterSum X g γ ω) ^ 2) ^ 2
        ≤ ((Gb : ℝ) * φ) ^ 2 * (clusterSum X g γ ω) ^ 2 := by
      intro ω
      rw [sq ((clusterSum X g γ ω) ^ 2)]
      exact mul_le_mul_of_nonneg_right (hSq γ ω) (sq_nonneg _)
    have h3 : Integrable (fun ω => ((clusterSum X g γ ω) ^ 2) ^ 2) μ := by
      have : (fun ω => ((clusterSum X g γ ω) ^ 2) ^ 2)
          = fun ω => (clusterSum X g γ ω) ^ 4 := by funext ω; ring
      rw [this]; exact hint4 γ
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono h3 ((hintsq γ).const_mul _) h2
  calc ∑ γ, variance (fun ω => (clusterSum X g γ ω) ^ 2) μ
      ≤ ∑ γ : Gp, ((Gb : ℝ) * φ) ^ 2 * ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ :=
        Finset.sum_le_sum (fun γ _ => key γ)
    _ = ((Gb : ℝ) * φ) ^ 2 * ∑ γ : Gp, ∫ ω, (clusterSum X g γ ω) ^ 2 ∂μ := by
        rw [Finset.mul_sum]
    _ = ((Gb : ℝ) * φ) ^ 2 := by
        rw [sum_integral_clusterSum_sq D hshare hφ0 hφ hGb hmean hvar, mul_one]

end Errors

section CLT

/-! ### The two Stein error terms -/

/-- `E₂ ≤ Ḡ_nφ_n → 0`, by `secondError_le`. -/
theorem secondError_tendsto_zero
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (g : ∀ n, O n → Gp n)
    (D : ∀ n, DepGraph (X n) (μ n))
    (hshare : ∀ n o o', (D n).G o o' ↔ g n o = g n o')
    (φ : ℕ → ℝ) (Gb : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n)
    (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * φ n) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ o, ∫ ω, |X n o ω| * (nbhdSum (X n) (D n).nbhd o ω) ^ 2 ∂(μ n))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hrate
  · exact Finset.sum_nonneg (fun o _ => integral_nonneg (fun ω => by positivity))
  · exact secondError_le (D n) (hshare n) (hφ0 n) (hφ n) (hGb n) (hmean n) (hvar n)

/-- `E₁ ≤ (Ḡ_nφ_n)² → 0`, by `firstError_le`. -/
theorem firstError_tendsto_zero
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (g : ∀ n, O n → Gp n)
    (D : ∀ n, DepGraph (X n) (μ n))
    (hshare : ∀ n o o', (D n).G o o' ↔ g n o = g n o')
    (φ : ℕ → ℝ) (Gb : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n)
    (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * φ n) atTop (𝓝 0)) :
    Tendsto (fun n => variance (fun ω => ∑ o, X n o ω * nbhdSum (X n) (D n).nbhd o ω) (μ n))
      atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => ((Gb n : ℝ) * φ n) ^ 2) atTop (𝓝 0) := by
    simpa using hrate.pow 2
  refine squeeze_zero (fun n => variance_nonneg _ _) (fun n => ?_) hsq
  exact firstError_le (D n) (hshare n) (hφ0 n) (hφ n) (hGb n) (hmean n) (hvar n)

/-- **Theorem 5(a), at `J = 1`.** Consider a standardized array `{X_{n,o}}` with one clustering
dimension given by the cluster map `g n` (`hshare`), mean-zero summands bounded by `φ n`, clusters
of size at most `Ḡ n` and `Var(∑_o X_{n,o}) = 1`. If `Ḡ_n φ_n → 0`, the CDF of `∑_o X_{n,o}`
converges to the standard normal CDF at every threshold. -/
theorem cltcluster_a_oneDimension
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (g : ∀ n, O n → Gp n)
    (D : ∀ n, DepGraph (X n) (μ n))
    (hshare : ∀ n o o', (D n).G o o' ↔ g n o = g n o')
    (φ : ℕ → ℝ) (Gb : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n)
    (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * φ n) atTop (𝓝 0))
    (s : ℝ) :
    Tendsto (fun n => ((μ n).map (depSum (X n))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  exact stein_cdf_clt μ X (fun n => (D n).nbhd) (fun n o => (D n).meas o)
    φ hφ0 hφ hmean (fun n o => (D n).indepFun_leaveOut o) hvar
    (firstError_tendsto_zero μ X g D hshare φ Gb hφ0 hφ hGb hmean hvar hrate)
    (secondError_tendsto_zero μ X g D hshare φ Gb hφ0 hφ hGb hmean hvar hrate) s

/-- The same theorem under the rate condition `δ_n → 0`, given the bound
`Ḡ_nφ_n ≤ κ√δ_n` (`hsharing`), which follows from Lemma SM.B.11(e). -/
theorem cltcluster_a_oneDimension_of_delta
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (g : ∀ n, O n → Gp n)
    (D : ∀ n, DepGraph (X n) (μ n))
    (hshare : ∀ n o o', (D n).G o o' ↔ g n o = g n o')
    (φ : ℕ → ℝ) (Gb : ℕ → ℕ) (δ : ℕ → ℝ) (κ : ℝ)
    (hφ0 : ∀ n, 0 ≤ φ n)
    (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hsharing : ∀ n, (Gb n : ℝ) * φ n ≤ κ * Real.sqrt (δ n))
    (hδ : Tendsto δ atTop (𝓝 0))
    (s : ℝ) :
    Tendsto (fun n => ((μ n).map (depSum (X n))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine cltcluster_a_oneDimension μ X g D hshare φ Gb hφ0 hφ hGb hmean hvar ?_ s
  have hsqrt : Tendsto (fun n => Real.sqrt (δ n)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hδ
    simp only [Real.sqrt_zero] at h
    exact h
  refine squeeze_zero (fun n => ?_) hsharing (by simpa using hsqrt.const_mul κ)
  exact mul_nonneg (Nat.cast_nonneg _) (hφ0 n)

end CLT

section Reduction

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {W : Type*} [MeasurableSpace W] {μ : Measure W}

/-! #### The objects of the array reduction -/

/-- `A_n := (X̃'X̃)^{-1}𝓡_n'`, a `K × r` matrix. -/
noncomputable def scoreMap (Xt : Matrix O K ℝ) (Rn : Matrix r K ℝ) : Matrix K r ℝ :=
  (Xtᵀ * Xt)⁻¹ * Rnᵀ

/-- `Ω_n := X̃'ΩX̃`, the exact conditional variance of the within score. -/
def scoreVar (Xt : Matrix O K ℝ) (Om : Matrix O O ℝ) : Matrix K K ℝ := Xtᵀ * Om * Xt

/-- `𝒱_n := A_n'Ω_nA_n`, the exact conditional variance of `𝓡_n(β̂_JM − β)`. -/
noncomputable def restrictedVar (Xt : Matrix O K ℝ) (Om : Matrix O O ℝ) (Rn : Matrix r K ℝ) :
    Matrix r r ℝ := (scoreMap Xt Rn)ᵀ * scoreVar Xt Om * scoreMap Xt Rn

/-- `G_n := A_n𝒱_n^{-1/2}` (Lemma SM.B.12 applied to `Ω_n` and `A_n`). -/
noncomputable def steinStd (Xt : Matrix O K ℝ) (Om : Matrix O O ℝ) (Rn : Matrix r K ℝ) :
    Matrix K r ℝ := Multiway.restrictedStd (scoreVar Xt Om) (scoreMap Xt Rn)

omit [DecidableEq O] in
theorem steinStd_eq (Xt : Matrix O K ℝ) (Om : Matrix O O ℝ) (Rn : Matrix r K ℝ) :
    steinStd Xt Om Rn = scoreMap Xt Rn * (sqrtPD (restrictedVar Xt Om Rn))⁻¹ := rfl

/-- `a_n := G_nb` for a unit `b`. -/
noncomputable def steinWeight (Xt : Matrix O K ℝ) (Om : Matrix O O ℝ) (Rn : Matrix r K ℝ)
    (b : r → ℝ) : K → ℝ := steinStd Xt Om Rn *ᵥ b

/-- `X_{n,o} := (a_n'x̃_o)ν_o`, the array to which the scalar theorem is applied. -/
def scoreArray (Xt : Matrix O K ℝ) (a : K → ℝ) (v : O → W → ℝ) : O → W → ℝ :=
  fun o ω => (Xt *ᵥ a) o * v o ω

/-! #### The identity `b'𝒱_n^{-1/2}𝓡_n(β̂_JM − β) = ∑_o X_{n,o}` -/

omit [DecidableEq O] [DecidableEq K] in
/-- The adjoint identity `(Ma)'w = a'(M'w)`. -/
theorem dotProduct_mulVec_adjoint (M : Matrix O K ℝ) (a : K → ℝ) (w : O → ℝ) :
    (M *ᵥ a) ⬝ᵥ w = a ⬝ᵥ (Mᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

omit [DecidableEq O] [DecidableEq K] [MeasurableSpace W] in
theorem depSum_scoreArray (Xt : Matrix O K ℝ) (a : K → ℝ) (v : O → W → ℝ) (ω : W) :
    depSum (scoreArray Xt a v) ω = a ⬝ᵥ (Xtᵀ *ᵥ (fun o => v o ω)) := by
  have h : depSum (scoreArray Xt a v) ω = (Xt *ᵥ a) ⬝ᵥ (fun o => v o ω) := rfl
  rw [h, dotProduct_mulVec_adjoint]

omit [DecidableEq O] [MeasurableSpace W] in
/-- The reduction identity. With `A_n := (X̃'X̃)^{-1}𝓡_n'`, `𝒱_n := A_n'Ω_nA_n`,
`G_n := A_n𝒱_n^{-1/2}` and `a_n := G_nb`, the score representation `β̂_JM − β = (X̃'X̃)^{-1}X̃'ν`
turns `b'𝒱_n^{-1/2}𝓡_n(β̂_JM − β)` into `∑_o (a_n'x̃_o)ν_o`. The identity requires only the
symmetry of `sqrtPD`. -/
theorem dotProduct_standardized_eq_depSum (Xt : Matrix O K ℝ) (Om : Matrix O O ℝ)
    (Rn : Matrix r K ℝ) (b : r → ℝ) (v : O → W → ℝ) (ω : W) :
    b ⬝ᵥ ((sqrtPD (restrictedVar Xt Om Rn))⁻¹ *ᵥ
        (Rn *ᵥ ((Xtᵀ * Xt)⁻¹ *ᵥ (Xtᵀ *ᵥ (fun o => v o ω)))))
      = depSum (scoreArray Xt (steinWeight Xt Om Rn b) v) ω := by
  rw [depSum_scoreArray]
  set S : Matrix r r ℝ := sqrtPD (restrictedVar Xt Om Rn) with hS
  set u : K → ℝ := Xtᵀ *ᵥ (fun o => v o ω) with hu
  have hSsym : (S⁻¹)ᵀ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv,
      Multiway.transpose_eq_self (Multiway.sqrtPD_posSemidef).isHermitian]
  have hAt : (scoreMap Xt Rn)ᵀ = Rn * (Xtᵀ * Xt)⁻¹ := by
    rw [scoreMap, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hW : steinWeight Xt Om Rn b = scoreMap Xt Rn *ᵥ (S⁻¹ *ᵥ b) := by
    rw [steinWeight, steinStd_eq, ← hS, ← Matrix.mulVec_mulVec]
  calc b ⬝ᵥ (S⁻¹ *ᵥ (Rn *ᵥ ((Xtᵀ * Xt)⁻¹ *ᵥ u)))
      = b ⬝ᵥ ((S⁻¹)ᵀ *ᵥ (Rn *ᵥ ((Xtᵀ * Xt)⁻¹ *ᵥ u))) := by rw [hSsym]
    _ = (S⁻¹ *ᵥ b) ⬝ᵥ (Rn *ᵥ ((Xtᵀ * Xt)⁻¹ *ᵥ u)) :=
        (dotProduct_mulVec_adjoint S⁻¹ b _).symm
    _ = (S⁻¹ *ᵥ b) ⬝ᵥ ((Rn * (Xtᵀ * Xt)⁻¹) *ᵥ u) := by rw [Matrix.mulVec_mulVec]
    _ = (S⁻¹ *ᵥ b) ⬝ᵥ ((scoreMap Xt Rn)ᵀ *ᵥ u) := by rw [hAt]
    _ = (scoreMap Xt Rn *ᵥ (S⁻¹ *ᵥ b)) ⬝ᵥ u :=
        (dotProduct_mulVec_adjoint (scoreMap Xt Rn) (S⁻¹ *ᵥ b) u).symm
    _ = steinWeight Xt Om Rn b ⬝ᵥ u := by rw [hW]

/-! #### The hypotheses of the array theorem, verified from the design -/

omit [DecidableEq K] in
/-- Cauchy–Schwarz for the dot product, in `√` form. -/
theorem abs_dotProduct_le (x y : K → ℝ) :
    |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have hx : Real.sqrt (x ⬝ᵥ x) = ‖(EuclideanSpace.equiv K ℝ).symm x‖ := by
    rw [Multiway.dot_self_eq]; exact Real.sqrt_sq (norm_nonneg _)
  have hy : Real.sqrt (y ⬝ᵥ y) = ‖(EuclideanSpace.equiv K ℝ).symm y‖ := by
    rw [Multiway.dot_self_eq]; exact Real.sqrt_sq (norm_nonneg _)
  have hinner : x ⬝ᵥ y
      = ⟪(EuclideanSpace.equiv K ℝ).symm x, (EuclideanSpace.equiv K ℝ).symm y⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp
    exact dotProduct_comm x y
  rw [hx, hy, hinner]
  exact abs_real_inner_le_norm _ _

omit [DecidableEq K] in
/-- `‖Gb‖ ≤ ‖G‖‖b‖` in the `√` form, with the l2 operator norm. -/
theorem sqrt_dot_mulVec_le (G : Matrix K r ℝ) (b : r → ℝ) :
    Real.sqrt ((G *ᵥ b) ⬝ᵥ (G *ᵥ b)) ≤ ‖G‖ * Real.sqrt (b ⬝ᵥ b) := by
  rw [Multiway.dot_self_eq, Multiway.dot_self_eq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact Matrix.l2_opNorm_mulVec G _

omit [DecidableEq O] [MeasurableSpace W] in
/-- The bound `|X_{n,o}| ≤ φ_n := BC_ν λ_min(Ω_n)^{-1/2}`, from `sup_o|ν_o| ≤ C_ν`,
`sup_o‖x̃_o‖ ≤ B` and Lemma SM.B.12. For `λ_min(Ω_n)` the statement uses any `c > 0` with
`cI ⪯ Ω_n`. -/
theorem abs_scoreArray_le {Xt : Matrix O K ℝ} {Om : Matrix O O ℝ} {Rn : Matrix r K ℝ}
    (hPD : (scoreVar Xt Om).PosDef) (hA : Function.Injective (scoreMap Xt Rn).mulVec)
    {c : ℝ} (hc : 0 < c) (hcOm : c • (1 : Matrix K K ℝ) ≤ scoreVar Xt Om)
    {B Cnu : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ o, (fun k => Xt o k) ⬝ᵥ (fun k => Xt o k) ≤ B ^ 2)
    {v : O → W → ℝ} (hnu : ∀ o ω, |v o ω| ≤ Cnu)
    {b : r → ℝ} (hb : b ⬝ᵥ b = 1) (o : O) (ω : W) :
    |scoreArray Xt (steinWeight Xt Om Rn b) v o ω| ≤ B * Cnu / Real.sqrt c := by
  have hGnorm : ‖steinStd Xt Om Rn‖ ≤ Real.sqrt c⁻¹ := by
    have h := Multiway.sq_l2_opNorm_restrictedStd_le hPD hA hc hcOm
    have h2 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (norm_nonneg _)] at h2
  have hanorm : Real.sqrt (steinWeight Xt Om Rn b ⬝ᵥ steinWeight Xt Om Rn b)
      ≤ Real.sqrt c⁻¹ := by
    have h := sqrt_dot_mulVec_le (steinStd Xt Om Rn) b
    rw [hb, Real.sqrt_one, mul_one] at h
    exact h.trans hGnorm
  have hrow : Real.sqrt ((fun k => Xt o k) ⬝ᵥ (fun k => Xt o k)) ≤ B := by
    have := Real.sqrt_le_sqrt (hB o)
    rwa [Real.sqrt_sq hB0] at this
  have hcoef : |(Xt *ᵥ steinWeight Xt Om Rn b) o| ≤ B * Real.sqrt c⁻¹ := by
    have hdot : (Xt *ᵥ steinWeight Xt Om Rn b) o
        = (fun k => Xt o k) ⬝ᵥ steinWeight Xt Om Rn b := rfl
    rw [hdot]
    refine (abs_dotProduct_le _ _).trans ?_
    exact mul_le_mul hrow hanorm (Real.sqrt_nonneg _) hB0
  calc |scoreArray Xt (steinWeight Xt Om Rn b) v o ω|
      = |(Xt *ᵥ steinWeight Xt Om Rn b) o| * |v o ω| := by
        rw [scoreArray, abs_mul]
    _ ≤ (B * Real.sqrt c⁻¹) * Cnu :=
        mul_le_mul hcoef (hnu o ω) (abs_nonneg _) (by positivity)
    _ = B * Cnu / Real.sqrt c := by
        rw [Real.sqrt_inv, div_eq_mul_inv]; ring

omit [Fintype O] [DecidableEq O] [DecidableEq K] in
/-- The array has mean zero, by exogeneity. -/
theorem integral_scoreArray {v : O → W → ℝ} (hmean : ∀ o, ∫ ω, v o ω ∂μ = 0)
    (Xt : Matrix O K ℝ) (a : K → ℝ) (o : O) :
    ∫ ω, scoreArray Xt a v o ω ∂μ = 0 := by
  simp only [scoreArray]
  rw [MeasureTheory.integral_const_mul, hmean o, mul_zero]

variable [IsProbabilityMeasure μ]

omit [DecidableEq O] [DecidableEq K] in
/-- The total variance is `∫(∑_oX_{n,o})² = a'Ω_na`, where `Ω_n` is the second-moment matrix
of `ν` (`hOm`). -/
theorem integral_depSum_scoreArray_sq {v : O → W → ℝ} {Om : Matrix O O ℝ} {C : ℝ}
    (hmeas : ∀ o, Measurable (v o)) (hbd : ∀ o ω, |v o ω| ≤ C)
    (hOm : ∀ o o', ∫ ω, v o ω * v o' ω ∂μ = Om o o')
    (Xt : Matrix O K ℝ) (a : K → ℝ) :
    ∫ ω, (depSum (scoreArray Xt a v) ω) ^ 2 ∂μ = a ⬝ᵥ (scoreVar Xt Om *ᵥ a) := by
  set cw : O → ℝ := Xt *ᵥ a with hcw
  have hsq : ∀ ω, (depSum (scoreArray Xt a v) ω) ^ 2
      = ∑ o, ∑ o', (cw o * cw o') * (v o ω * v o' ω) := by
    intro ω
    have h0 : depSum (scoreArray Xt a v) ω = ∑ o, cw o * v o ω := rfl
    rw [h0, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun o' _ => by ring
  have hint : ∀ o o' : O, Integrable (fun ω => (cw o * cw o') * (v o ω * v o' ω)) μ := by
    intro o o'
    refine integrable_of_bdd (((hmeas o).mul (hmeas o')).const_mul _)
      (C := |cw o * cw o'| * (C * C)) (fun ω => ?_)
    rw [abs_mul (cw o * cw o') (v o ω * v o' ω), abs_mul (v o ω) (v o' ω)]
    have h1 : |v o ω| * |v o' ω| ≤ C * C :=
      mul_le_mul (hbd o ω) (hbd o' ω) (abs_nonneg _) ((abs_nonneg _).trans (hbd o ω))
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hintsum : ∀ o : O, Integrable (fun ω => ∑ o', (cw o * cw o') * (v o ω * v o' ω)) μ :=
    fun o => integrable_finsetSum _ (fun o' _ => hint o o')
  calc ∫ ω, (depSum (scoreArray Xt a v) ω) ^ 2 ∂μ
      = ∫ ω, ∑ o, ∑ o', (cw o * cw o') * (v o ω * v o' ω) ∂μ :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsq)
    _ = ∑ o, ∑ o', (cw o * cw o') * Om o o' := by
        rw [MeasureTheory.integral_finsetSum _ (fun o _ => hintsum o)]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [MeasureTheory.integral_finsetSum _ (fun o' _ => hint o o')]
        exact Finset.sum_congr rfl fun o' _ => by
          rw [MeasureTheory.integral_const_mul, hOm o o']
    _ = cw ⬝ᵥ (Om *ᵥ cw) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        have hmv : (Om *ᵥ cw) o = ∑ o', Om o o' * cw o' := rfl
        rw [hmv, Finset.mul_sum]
        exact Finset.sum_congr rfl fun o' _ => by ring
    _ = a ⬝ᵥ (scoreVar Xt Om *ᵥ a) := Multiway.dotProduct_mulVec_conj Xt Om a

omit [DecidableEq O] in
/-- The standardization `∫(∑_oX_{n,o})² = b'G_n'Ω_nG_nb = 1` for a unit `b`. -/
theorem integral_depSum_scoreArray_sq_eq_one {Xt : Matrix O K ℝ} {Om : Matrix O O ℝ}
    {Rn : Matrix r K ℝ} (hPD : (scoreVar Xt Om).PosDef)
    (hA : Function.Injective (scoreMap Xt Rn).mulVec)
    {v : O → W → ℝ} {C : ℝ} (hmeas : ∀ o, Measurable (v o)) (hbd : ∀ o ω, |v o ω| ≤ C)
    (hOm : ∀ o o', ∫ ω, v o ω * v o' ω ∂μ = Om o o')
    {b : r → ℝ} (hb : b ⬝ᵥ b = 1) :
    ∫ ω, (depSum (scoreArray Xt (steinWeight Xt Om Rn b) v) ω) ^ 2 ∂μ = 1 := by
  rw [integral_depSum_scoreArray_sq hmeas hbd hOm]
  have h := Multiway.dotProduct_mulVec_conj (steinStd Xt Om Rn) (scoreVar Xt Om) b
  have hGOG : (steinStd Xt Om Rn)ᵀ * scoreVar Xt Om * steinStd Xt Om Rn = 1 :=
    Multiway.transpose_mul_mul_restrictedStd hPD hA
  rw [hGOG, Matrix.one_mulVec, hb] at h
  exact h

/-- A dependency graph for `ν` is a dependency graph for `X_{n,o} = (a_n'x̃_o)ν_o`, with the
same relation. -/
noncomputable def scoreArrayDepGraph {v : O → W → ℝ}
    (D : DepGraph v μ) (Xt : Matrix O K ℝ) (a : K → ℝ) :
    DepGraph (scoreArray Xt a v) μ where
  G := D.G
  decG := D.decG
  refl := D.refl
  symm := D.symm
  meas := fun o => (D.meas o).const_mul ((Xt *ᵥ a) o)
  indep := by
    intro A Bs hsep
    have h0 := D.indep A Bs hsep
    have hmA : Measurable (fun t : (↥A → ℝ) => fun k : ↥A => (Xt *ᵥ a) (k : O) * t k) := by
      refine Measurable.of_eval fun k => ?_
      have h1 : Measurable (fun t : (↥A → ℝ) => t k) := measurable_pi_apply k
      exact h1.const_mul ((Xt *ᵥ a) (k : O))
    have hmB : Measurable (fun t : (↥Bs → ℝ) => fun k : ↥Bs => (Xt *ᵥ a) (k : O) * t k) := by
      refine Measurable.of_eval fun k => ?_
      have h1 : Measurable (fun t : (↥Bs → ℝ) => t k) := measurable_pi_apply k
      exact h1.const_mul ((Xt *ᵥ a) (k : O))
    exact h0.comp hmA hmB

end Reduction

section Witness

open Multiway.Multilinear

/-- An example design. At sample size `n` there are `n+1` observations in singleton clusters
(`g = id`, so `Ḡ = 1`), each a fair sign scaled by `(n+1)^{-1/2}`. -/
noncomputable def witX (n : ℕ) (o : Fin (n + 1)) (ω : Fin (n + 1) → Bool) : ℝ :=
  sign2 o ω / Real.sqrt ((n : ℝ) + 1)

theorem witX_measurable (n : ℕ) (o : Fin (n + 1)) : Measurable (witX n o) :=
  (measurable_sign2 o).div_const _

theorem witX_iIndepFun (n : ℕ) : iIndepFun (witX n) (coins (n + 1)) :=
  (iIndepFun_sign2 (n + 1)).comp (fun _ x => x / Real.sqrt ((n : ℝ) + 1))
    (fun _ => measurable_id.div_const _)

/-- The sharing graph of the example design is equality of indices. -/
noncomputable def witDep (n : ℕ) : DepGraph (witX n) (coins (n + 1)) where
  G := fun o o' => o = o'
  decG := fun _ _ => inferInstance
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  meas := witX_measurable n
  indep := by
    intro A B h
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact h a ha a hb rfl
    exact (witX_iIndepFun n).indepFun_finset A B hdisj (witX_measurable n)

theorem witX_abs_le (n : ℕ) (o : Fin (n + 1)) (ω : Fin (n + 1) → Bool) :
    |witX n o ω| ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h1 : |sign2 o ω| ≤ 1 := by
    unfold sign2; by_cases h : ω o <;> simp [h]
  rw [witX, abs_div, abs_of_pos hpos]
  gcongr

theorem witX_mean (n : ℕ) (o : Fin (n + 1)) : ∫ ω, witX n o ω ∂(coins (n + 1)) = 0 := by
  simp only [witX]
  rw [MeasureTheory.integral_div, integral_sign2, zero_div]

theorem witX_sq (n : ℕ) (o : Fin (n + 1)) :
    ∫ ω, (witX n o ω) ^ 2 ∂(coins (n + 1)) = 1 / ((n : ℝ) + 1) := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hrw : (fun ω : Fin (n + 1) → Bool => (witX n o ω) ^ 2)
      = fun ω => (sign2 o ω) ^ 2 / ((n : ℝ) + 1) := by
    funext ω
    rw [witX, div_pow, Real.sq_sqrt hnn]
  rw [hrw, MeasureTheory.integral_div, witness_nondegenerate]

theorem witX_var (n : ℕ) : ∫ ω, (depSum (witX n) ω) ^ 2 ∂(coins (n + 1)) = 1 := by
  have hbd : ∀ o : Fin (n + 1), ∀ ω, |witX n o ω| ≤ 1 / Real.sqrt ((n : ℝ) + 1) :=
    witX_abs_le n
  have hmem : ∀ o : Fin (n + 1), MemLp (witX n o) 2 (coins (n + 1)) := fun o =>
    MemLp.of_bound (witX_measurable n o).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs]; exact hbd o ω))
  have hpair : ((Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).Pairwise
      (fun i j => IndepFun (witX n i) (witX n j) (coins (n + 1))) := by
    intro i _ j _ hij
    exact (witX_iIndepFun n).indepFun hij
  have hsum := IndepFun.variance_sum (μ := coins (n + 1)) (X := witX n)
    (s := Finset.univ) (fun o _ => hmem o) hpair
  have hfun : (∑ o ∈ Finset.univ, witX n o) = depSum (witX n) := by
    funext ω
    exact Finset.sum_apply ω Finset.univ (witX n)
  rw [hfun] at hsum
  have hmeasSum : Measurable (depSum (witX n)) :=
    Finset.measurable_sum _ (fun o _ => witX_measurable n o)
  have hmean0 : ∫ ω, depSum (witX n) ω ∂(coins (n + 1)) = 0 := by
    simp only [depSum]
    rw [MeasureTheory.integral_finsetSum _ (fun o _ => (hmem o).integrable (by norm_num))]
    simp [witX_mean]
  have hvarO : ∀ o : Fin (n + 1), variance (witX n o) (coins (n + 1)) = 1 / ((n : ℝ) + 1) := by
    intro o
    rw [variance_of_integral_eq_zero (witX_measurable n o).aemeasurable (witX_mean n o),
      witX_sq]
  rw [← variance_of_integral_eq_zero hmeasSum.aemeasurable hmean0, hsum]
  rw [Finset.sum_congr rfl (fun o _ => hvarO o), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

theorem witX_cluster_card (n : ℕ) (γ : Fin (n + 1)) :
    (cluster (id : Fin (n + 1) → Fin (n + 1)) γ).card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
  rw [mem_cluster] at ha hb
  simpa using ha.trans hb.symm

/-- The hypotheses of `cltcluster_a_oneDimension` hold on `n+1` singleton clusters of one fair
sign each, scaled by `(n+1)^{-1/2}`. Then `Ḡ_n = 1`, `φ_n = (n+1)^{-1/2} → 0` and the total
variance is `1`. -/
theorem cltcluster_a_oneDimension_witness (s : ℝ) :
    Tendsto (fun n => ((coins (n + 1)).map (depSum (witX n))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine cltcluster_a_oneDimension (fun n => coins (n + 1)) witX
    (fun n => (id : Fin (n + 1) → Fin (n + 1))) witDep (fun n o o' => Iff.rfl)
    (fun n => 1 / Real.sqrt ((n : ℝ) + 1)) (fun _ => 1) (fun n => by positivity)
    (fun n o ω => witX_abs_le n o ω) (fun n γ => witX_cluster_card n γ)
    (fun n o => witX_mean n o) (fun n => witX_var n) ?_ s
  -- `Ḡ_n φ_n = (n+1)^{-1/2} → 0`.
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  simp only [Nat.cast_one, one_mul, one_div]
  exact hsqrt.inv_tendsto_atTop

end Witness

section BetaJM

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- **Theorem 5(a) for `β̂_JM`, at `J = 1`.** The theorem applies `cltcluster_a_oneDimension`
to `X_{n,o} := (a_n'x̃_o)ν_o` with `a_n := G_nb`, and the score representation gives
`b'𝒱_n^{-1/2}𝓡_n(β̂_JM − β) = ∑_oX_{n,o}`. For a fixed direction `b`, the CDF of this scalar
statistic converges to the standard normal CDF. -/
theorem cltcluster_a_oneDimension_betaJM
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, O n → Gp n)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ g n o = g n o')
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
    (Gb : ℕ → ℕ) (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * (B * Cnu / Real.sqrt (lmin n))) atTop (𝓝 0))
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
  refine cltcluster_a_oneDimension μ
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) g
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n o o' => hshare n o o')
    (fun n => B * Cnu / Real.sqrt (lmin n)) Gb
    (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ hGb ?_ ?_ hrate s
  · exact fun n o ω =>
      abs_scoreArray_le (hPD n) (hA n) (hlmin n) (hfloor n) hB0 (hB n) (hnu n) hb o ω
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hnu n) (hOm n) hb

/-- The same theorem under the rate condition `δ_n → 0`, through
`cltcluster_a_oneDimension_of_delta`. The rate enters as `Ḡ_nφ_n ≤ κ√δ_n` with `δ_n → 0`, as in
Corollary SM.D.3. -/
theorem cltcluster_a_oneDimension_betaJM_of_delta
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, O n → Gp n)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ g n o = g n o')
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
    (Gb : ℕ → ℕ) (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (δ : ℕ → ℝ) (κ : ℝ)
    (hsharing : ∀ n, (Gb n : ℝ) * (B * Cnu / Real.sqrt (lmin n)) ≤ κ * Real.sqrt (δ n))
    (hδ : Tendsto δ atTop (𝓝 0))
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
  refine cltcluster_a_oneDimension_of_delta μ
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) g
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n o o' => hshare n o o')
    (fun n => B * Cnu / Real.sqrt (lmin n)) Gb δ κ
    (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ hGb ?_ ?_
    hsharing hδ s
  · exact fun n o ω =>
      abs_scoreArray_le (hPD n) (hA n) (hlmin n) (hfloor n) hB0 (hB n) (hnu n) hb o ω
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hnu n) (hOm n) hb

end BetaJM

section BetaJMWitness

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.Multilinear

/-- An example design for the array reduction. At sample size `n` there are `n+1`
observations in singleton clusters, one regressor equal to `1`, `𝓡_n = I_1`, and a fair sign as
the disturbance of each observation. -/
noncomputable def redXt (n : ℕ) : Matrix (Fin (n + 1)) (Fin 1) ℝ := fun _ _ => 1

/-- The dependency graph of the example disturbances is equality of indices. -/
noncomputable def redDep (n : ℕ) :
    DepGraph (fun o : Fin (n + 1) => sign2 o) (coins (n + 1)) where
  G := fun o o' => o = o'
  decG := fun _ _ => inferInstance
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  meas := measurable_sign2
  indep := by
    intro A Bs h
    have hdisj : Disjoint A Bs := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact h a ha a hb rfl
    exact (iIndepFun_sign2 (n + 1)).indepFun_finset A Bs hdisj measurable_sign2

theorem abs_sign2_le' {m : ℕ} (i : Fin m) (ω : Fin m → Bool) : |sign2 i ω| ≤ 1 := by
  unfold sign2; by_cases h : ω i <;> simp [h]

theorem redXt_transpose_mul_self (n : ℕ) :
    (redXt n)ᵀ * redXt n = ((n : ℝ) + 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [redXt, Matrix.mul_apply]

theorem redXt_scoreVar (n : ℕ) :
    scoreVar (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      = ((n : ℝ) + 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [scoreVar, Matrix.mul_one, redXt_transpose_mul_self]

theorem redXt_scoreMap_isUnit (n : ℕ) :
    Function.Injective (scoreMap (redXt n) (1 : Matrix (Fin 1) (Fin 1) ℝ)).mulVec := by
  refine Matrix.mulVec_injective_of_isUnit ?_
  have h : scoreMap (redXt n) (1 : Matrix (Fin 1) (Fin 1) ℝ) = ((redXt n)ᵀ * redXt n)⁻¹ := by
    rw [scoreMap, Matrix.transpose_one, Matrix.mul_one]
  rw [h, Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det,
    redXt_transpose_mul_self, Matrix.det_smul, Matrix.det_one]
  refine isUnit_iff_ne_zero.mpr ?_
  simp
  positivity

/-- The second moments of the fair signs: `E[s_is_j] = 1{i = j}`. -/
theorem integral_sign2_mul {m : ℕ} (i j : Fin m) :
    ∫ ω, sign2 i ω * sign2 j ω ∂(coins m) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simpa [sq] using witness_nondegenerate (n := m) i
  · rw [ite_eq_right h]
    have hg : Function.Injective (![i, j] : Fin 2 → Fin m) := by
      intro a c hac
      fin_cases a <;> fin_cases c <;> simp_all
    have hm : NeZero m := ⟨by rintro rfl; exact i.elim0⟩
    have := integral_prod_sign2_eq_zero (n := m) (m := 2) hg
    simpa [Fin.prod_univ_two] using this

theorem red_second_moment (n : ℕ) (o o' : Fin (n + 1)) :
    ∫ ω, sign2 o ω * sign2 o' ω ∂(coins (n + 1))
      = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) o o' := by
  rw [integral_sign2_mul, Matrix.one_apply]

/-- The hypotheses of `cltcluster_a_oneDimension_betaJM` hold with `n+1` observations, one
regressor `x̃_o = 1`, `𝓡_n = I_1`, `Ω_n = X̃'X̃ = n+1`, singleton clusters and one fair sign per
observation. The total variance is `1` at every `n` and `φ_n = (n+1)^{-1/2} → 0`. -/
theorem cltcluster_a_oneDimension_betaJM_witness (s : ℝ) :
    Tendsto (fun n => ((coins (n + 1)).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt n)ᵀ * redXt n)⁻¹ *ᵥ ((redXt n)ᵀ *ᵥ (fun o => sign2 o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine cltcluster_a_oneDimension_betaJM (O := fun n => Fin (n + 1))
    (Gp := fun n => Fin (n + 1)) (fun n => coins (n + 1)) redXt (fun n => 1) (fun n => 1)
    (fun _ o => sign2 o)
    (fun n ω => ((redXt n)ᵀ * redXt n)⁻¹ *ᵥ ((redXt n)ᵀ *ᵥ (fun o => sign2 o ω)))
    (fun _ => 0) (fun _ => id) redDep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    redXt_scoreMap_isUnit (fun n => (n : ℝ) + 1) (fun n => by positivity) ?_ red_second_moment
    (fun n o => integral_sign2 o) 1 1 zero_le_one zero_le_one ?_ ?_ (fun _ => 1) ?_ ?_
    (fun _ => (1 : ℝ)) ?_ s
  · intro n
    rw [redXt_scoreVar]
  · intro _ _
    simp [redXt, dotProduct]
  · intro _ o ω
    exact abs_sign2_le' o ω
  · intro _ _
    refine Finset.card_le_one.mpr (fun a ha c hc => ?_)
    rw [mem_cluster] at ha hc
    simpa using ha.trans hc.symm
  · have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simp only [Nat.cast_one, one_mul, one_div]
    exact hsqrt.inv_tendsto_atTop
  · simp [dotProduct]

end BetaJMWitness

section CharFun

/-- The characteristic-function form of the Stein bound, with the two Stein error limits as
inputs. It is derived from `stein_expect_tendsto` at the test functions `cos(t·)` and `sin(t·)`,
and is used for both the `J = 1` and the general-`J` results. -/
theorem charFun_tendsto_of_errors
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (N : ∀ n, O n → Finset (O n))
    (hmeas : ∀ n o, Measurable (X n o))
    (φ : ℕ → ℝ) (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hindep : ∀ n o, IndepFun (X n o) (fun ω => ∑ j ∈ Finset.univ \ N n o, X n j ω) (μ n))
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (herr1 : Tendsto
      (fun n => variance (fun ω => ∑ o, X n o ω * nbhdSum (X n) (N n) o ω) (μ n)) atTop (𝓝 0))
    (herr2 : Tendsto
      (fun n => ∑ o, ∫ ω, |X n o ω| * (nbhdSum (X n) (N n) o ω) ^ 2 ∂(μ n)) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (depSum (X n))) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  classical
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n => by
    unfold depSum; exact Finset.measurable_sum _ (fun o _ => hmeas n o)
  -- the two test functions: bounded by `1`, derivative bounded by `|t|`
  have hcos_diff : Differentiable ℝ (fun x => Real.cos (t * x)) := by fun_prop
  have hcos_b : ∀ x, |Real.cos (t * x)| ≤ 1 := fun x => Real.abs_cos_le_one _
  have hcos_d : ∀ x, |deriv (fun x => Real.cos (t * x)) x| ≤ |t| := by
    intro x
    have hderiv : deriv (fun x => Real.cos (t * x)) x = -(t * Real.sin (t * x)) := by
      have h := (Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t)
      simpa [mul_comm, Function.comp_def] using h.deriv
    rw [hderiv, abs_neg, abs_mul]
    calc |t| * |Real.sin (t * x)| ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |t| := mul_one _
  have hsin_diff : Differentiable ℝ (fun x => Real.sin (t * x)) := by fun_prop
  have hsin_b : ∀ x, |Real.sin (t * x)| ≤ 1 := fun x => Real.abs_sin_le_one _
  have hsin_d : ∀ x, |deriv (fun x => Real.sin (t * x)) x| ≤ |t| := by
    intro x
    have hderiv : deriv (fun x => Real.sin (t * x)) x = t * Real.cos (t * x) := by
      have h := (Real.hasDerivAt_sin (t * x)).comp x ((hasDerivAt_id x).const_mul t)
      simpa [mul_comm, Function.comp_def] using h.deriv
    rw [hderiv, abs_mul]
    calc |t| * |Real.cos (t * x)| ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |t| := mul_one _
  have hcos_tendsto :
      Tendsto (fun n => ∫ ω, Real.cos (t * depSum (X n) ω) ∂(μ n)) atTop
        (𝓝 (gExpect (fun x => Real.cos (t * x)))) :=
    stein_expect_tendsto μ X N hmeas φ hφ0 hφ hmean hindep hvar herr1 herr2
      (fun x => Real.cos (t * x)) hcos_b hcos_d hcos_diff
  have hsin_tendsto :
      Tendsto (fun n => ∫ ω, Real.sin (t * depSum (X n) ω) ∂(μ n)) atTop
        (𝓝 (gExpect (fun x => Real.sin (t * x)))) :=
    stein_expect_tendsto μ X N hmeas φ hφ0 hφ hmean hindep hvar herr1 herr2
      (fun x => Real.sin (t * x)) hsin_b hsin_d hsin_diff
  have hgauss : charFun (gaussianReal 0 1) t
      = (↑(gExpect (fun x => Real.cos (t * x))) : ℂ)
        + (↑(gExpect (fun x => Real.sin (t * x))) : ℂ) * Complex.I := by
    have hmap : (gaussianReal 0 1).map id = gaussianReal 0 1 := Measure.map_id
    have h := charFun_map_eq_cos_sin (gaussianReal 0 1) id measurable_id t
    rw [hmap] at h
    simpa [gExpect, Function.comp] using h
  have hlaw : ∀ n, charFun ((μ n).map (depSum (X n))) t
      = (↑(∫ ω, Real.cos (t * depSum (X n) ω) ∂(μ n)) : ℂ)
        + (↑(∫ ω, Real.sin (t * depSum (X n) ω) ∂(μ n)) : ℂ) * Complex.I := fun n =>
    charFun_map_eq_cos_sin (μ n) (depSum (X n)) (hWmeas n) t
  rw [hgauss]
  simp_rw [hlaw]
  refine Tendsto.add ?_ (Tendsto.mul_const Complex.I ?_)
  · exact (Complex.continuous_ofReal.tendsto _).comp hcos_tendsto
  · exact (Complex.continuous_ofReal.tendsto _).comp hsin_tendsto

/-- **Theorem 5(a) at `J = 1`, in characteristic-function form.** The characteristic
functions of `∑_o X_{n,o}` converge to `e^{-t²/2}`. -/
theorem cltcluster_a_oneDimension_charFun
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (g : ∀ n, O n → Gp n)
    (D : ∀ n, DepGraph (X n) (μ n))
    (hshare : ∀ n o o', (D n).G o o' ↔ g n o = g n o')
    (φ : ℕ → ℝ) (Gb : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n)
    (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * φ n) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (depSum (X n))) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  exact charFun_tendsto_of_errors μ X (fun n => (D n).nbhd) (fun n o => (D n).meas o)
    φ hφ0 hφ hmean (fun n o => (D n).indepFun_leaveOut o) hvar
    (firstError_tendsto_zero μ X g D hshare φ Gb hφ0 hφ hGb hmean hvar hrate)
    (secondError_tendsto_zero μ X g D hshare φ Gb hφ0 hφ hGb hmean hvar hrate) t

/-- The same theorem as convergence in distribution, by Lévy's continuity theorem. -/
theorem cltcluster_a_oneDimension_tendstoInDistribution
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (g : ∀ n, O n → Gp n)
    (D : ∀ n, DepGraph (X n) (μ n))
    (hshare : ∀ n o o', (D n).G o o' ↔ g n o = g n o')
    (φ : ℕ → ℝ) (Gb : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n)
    (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * φ n) atTop (𝓝 0)) :
    TendstoInDistribution (fun n => depSum (X n)) atTop (id : ℝ → ℝ) μ (gaussianReal 0 1) := by
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n => by
    unfold depSum; exact Finset.measurable_sum _ (fun o _ => (D n).meas o)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hWmeas n).aemeasurable)
    aemeasurable_id fun t => ?_
  rw [Measure.map_id]
  exact cltcluster_a_oneDimension_charFun μ X g D hshare φ Gb hφ0 hφ hGb hmean hvar hrate t

end CharFun

/-! ## Removing the conditioning on `𝒟`

The results above hold under a single measure `μ n`, interpreted as the regular conditional law
`ℙ_ω` given the design σ-field `𝒟`. The unconditional limit law follows from
`Multiway.CLTMartingale.CondD`, by a subsequence argument for the design convergences, dominated
convergence of the conditional characteristic function, the tower property and Lévy's continuity
theorem. -/

section Deconditioning

open Multiway.CLTMartingale.CondD

/-- **The unconditional form of the `J = 1` cluster CLT.** `W n` is the standardized
statistic on the unconditional space, `𝒟` the design σ-field and `d` the vector of design
convergences, in probability. The conclusion is a limit law under the full measure `P`. -/
theorem cltcluster_a_unconditional
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    {F : Type*} [PseudoEMetricSpace F] {d : ℕ → Ω → F} {L : Ω → F}
    (hdes : TendstoInMeasure P d atTop L)
    {W : ℕ → Ω → ℝ} (hW : ∀ n, AEMeasurable (W n) P)
    (hcond : ∀ t : ℝ, ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      (∀ᵐ ω ∂P, Tendsto (fun i => d (ns i) ω) atTop (𝓝 (L ω))) →
      ∀ᵐ ω ∂P, Tendsto (fun i => condCharFunD 𝒟 P (W (ns i)) t ω) atTop
        (𝓝 (charFun (gaussianReal 0 1) t))) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ) W atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  refine tendstoInDistribution_of_deconditioning 𝒟 h𝒟 P hdes hW aemeasurable_id fun t => ?_
  rw [Measure.map_id]
  exact hcond t

/-- The unconditional limit law when the conditional convergence holds along the whole
sequence, so that no subsequence extraction is needed. -/
theorem cltcluster_a_unconditional_of_tendsto_condCharFunD
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    {W : ℕ → Ω → ℝ} (hW : ∀ n, AEMeasurable (W n) P)
    (hcond : ∀ t : ℝ, ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => condCharFunD 𝒟 P (W n) t ω) atTop
      (𝓝 (charFun (gaussianReal 0 1) t))) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ) W atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  have htriv : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => (0 : ℝ)) := by
    intro ε hε
    have hset : {_x : Ω | ε ≤ edist (0 : ℝ) 0} = (∅ : Set Ω) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, edist_self,
        nonpos_iff_eq_zero]
      exact hε.ne'
    simp only [hset, measure_empty]
    exact tendsto_const_nhds
  refine cltcluster_a_unconditional 𝒟 h𝒟 P htriv hW ?_
  intro t ns hns _
  filter_upwards [hcond t] with ω hω
  exact hω.comp hns

/-- **The unconditional `J = 1` cluster CLT from a given conditional law.** `Q ω` is a
sequence of laws playing the role of `ℙ_ω` and `W₀ ω` the statistic computed there; `hfreeze` is
the defining property of `ℙ_ω` and `hfrozen` the conditional CLT along the realization. -/
theorem cltcluster_a_unconditional_of_frozen
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    {W : ℕ → Ω → ℝ} (hW : ∀ n, AEMeasurable (W n) P)
    {Ω₀ : ℕ → Type*} [∀ n, MeasurableSpace (Ω₀ n)]
    (Q : Ω → ∀ n, Measure (Ω₀ n)) [∀ ω n, IsProbabilityMeasure (Q ω n)]
    (W₀ : Ω → ∀ n, Ω₀ n → ℝ)
    (hfreeze : ∀ (n : ℕ) (t : ℝ),
      condCharFunD 𝒟 P (W n) t =ᵐ[P] fun ω => charFun ((Q ω n).map (W₀ ω n)) t)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (W₀ ω) atTop (id : ℝ → ℝ) (Q ω)
      (gaussianReal 0 1)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ) W atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  refine cltcluster_a_unconditional_of_tendsto_condCharFunD 𝒟 h𝒟 P hW fun t => ?_
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      condCharFunD 𝒟 P (W n) t ω = charFun ((Q ω n).map (W₀ ω n)) t :=
    ae_all_iff.2 fun n => hfreeze n t
  filter_upwards [hall, hfrozen] with ω hω hcl
  have h : Tendsto (fun n : ℕ => charFun ((Q ω n).map (W₀ ω n)) t) atTop
      (𝓝 (charFun ((gaussianReal 0 1).map (id : ℝ → ℝ)) t)) := hcl.tendsto_charFun t
  rw [Measure.map_id] at h
  exact Tendsto.congr (fun n => (hω n).symm) h

/-- The unconditional conclusion in CDF form, `P[W_n ≤ s] → Φ(s)`, through
`cdf_tendsto_of_charFun_tendsto`. -/
theorem cltcluster_a_unconditional_cdf
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} [IsProbabilityMeasure P]
    {W : ℕ → Ω → ℝ} (hW : ∀ n, AEMeasurable (W n) P)
    (h : TendstoInDistribution (m := fun _ : ℕ => mΩ) W atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1))
    (s : ℝ) :
    Tendsto (fun n => (@Measure.map Ω ℝ mΩ _ (W n) P).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  have : ∀ n, IsProbabilityMeasure (@Measure.map Ω ℝ mΩ _ (W n) P) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hW n)).2 inferInstance
  set lawn : ℕ → ProbabilityMeasure ℝ :=
    fun n => ⟨@Measure.map Ω ℝ mΩ _ (W n) P, inferInstance⟩ with hlawn
  let ν₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  let _ : NullSingletonClass (ν₀ : Measure ℝ) := nullSingletonClass_gaussianReal one_ne_zero
  have hchar : ∀ t : ℝ, Tendsto (fun n => charFun (lawn n : Measure ℝ) t) atTop
      (𝓝 (charFun (ν₀ : Measure ℝ) t)) := by
    intro t
    have := h.tendsto_charFun t
    rwa [Measure.map_id] at this
  exact cdf_tendsto_of_charFun_tendsto lawn ν₀ hchar s

end Deconditioning

section UnconditionalWitness

open Multiway.Multilinear

/-! ### An example on one probability space

An unconditional theorem is stated on a single `Ω`, `P` and `𝒟`, so the example array is defined
on one space. `ProbabilityTheory.exists_iid` gives an i.i.d. family of fair coins indexed by
`ℕ × ℕ`, and row `n` uses `n+1` of them. -/

/-- Row `n` of the example array, `n+1` fair signs in singleton clusters scaled by
`(n+1)^{-1/2}`, all on one probability space. -/
noncomputable def iidSign {Ω : Type*} (ξ : ℕ × ℕ → Ω → Bool) (n : ℕ) (o : Fin (n + 1))
    (ω : Ω) : ℝ :=
  (if ξ (n, o.val) ω then (1 : ℝ) else -1) / Real.sqrt ((n : ℝ) + 1)

theorem measurable_iidSign {Ω : Type*} [MeasurableSpace Ω] {ξ : ℕ × ℕ → Ω → Bool}
    (hξ : ∀ i, Measurable (ξ i)) (n : ℕ) (o : Fin (n + 1)) : Measurable (iidSign ξ n o) :=
  ((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp (hξ _)).div_const _

theorem iIndepFun_iidSign {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : ℕ × ℕ → Ω → Bool} (hindep : iIndepFun ξ P) (n : ℕ) :
    iIndepFun (iidSign ξ n) P :=
  (hindep.precomp (g := fun o : Fin (n + 1) => (n, o.val))
      (fun _ _ hab => Fin.val_injective (congrArg Prod.snd hab))).comp
    (fun _ b => (if b then (1 : ℝ) else -1) / Real.sqrt ((n : ℝ) + 1))
    (fun _ => measurable_of_finite _)

theorem abs_iidSign_le {Ω : Type*} (ξ : ℕ × ℕ → Ω → Bool) (n : ℕ) (o : Fin (n + 1)) (ω : Ω) :
    |iidSign ξ n o ω| ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h1 : |(if ξ (n, o.val) ω then (1 : ℝ) else -1)| ≤ 1 := by
    by_cases h : ξ (n, o.val) ω <;> simp [h]
  rw [iidSign, abs_div, abs_of_pos hpos]
  gcongr

theorem integral_iidSign {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : ℕ × ℕ → Ω → Bool} (hlaw : ∀ i, HasLaw (ξ i) coin P) (n : ℕ) (o : Fin (n + 1)) :
    ∫ ω, iidSign ξ n o ω ∂P = 0 := by
  have h : ∫ ω, (if ξ (n, o.val) ω then (1 : ℝ) else -1) ∂P
      = ∫ b, (if b then (1 : ℝ) else -1) ∂coin := by
    simpa [Function.comp_def] using
      (hlaw (n, o.val)).integral_comp (f := fun b : Bool => if b then (1 : ℝ) else -1)
        (measurable_of_finite _).aestronglyMeasurable
  simp only [iidSign]
  rw [MeasureTheory.integral_div, h, integral_coin]
  norm_num

theorem integral_iidSign_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ξ : ℕ × ℕ → Ω → Bool) (n : ℕ) (o : Fin (n + 1)) :
    ∫ ω, (iidSign ξ n o ω) ^ 2 ∂P = 1 / ((n : ℝ) + 1) := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hrw : (fun ω : Ω => (iidSign ξ n o ω) ^ 2) = fun _ : Ω => 1 / ((n : ℝ) + 1) := by
    funext ω
    rw [iidSign, div_pow, Real.sq_sqrt hnn]
    by_cases h : ξ (n, o.val) ω <;> simp [h]
  rw [hrw]
  simp

/-- The sharing graph of the example design is equality of indices, so every cluster is a
singleton and `Ḡ_n = 1`. -/
noncomputable def iidDep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ × ℕ → Ω → Bool} (hξ : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) (n : ℕ) : DepGraph (iidSign ξ n) P where
  G := fun o o' => o = o'
  decG := fun _ _ => inferInstance
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  meas := measurable_iidSign hξ n
  indep := by
    intro A B h
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact h a ha a hb rfl
    exact (iIndepFun_iidSign hindep n).indepFun_finset A B hdisj (measurable_iidSign hξ n)

/-- The total has variance `1` at every `n`. -/
theorem integral_depSum_iidSign_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ × ℕ → Ω → Bool} (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) coin P) (hindep : iIndepFun ξ P) (n : ℕ) :
    ∫ ω, (depSum (iidSign ξ n) ω) ^ 2 ∂P = 1 := by
  have hmem : ∀ o : Fin (n + 1), MemLp (iidSign ξ n o) 2 P := fun o =>
    MemLp.of_bound (measurable_iidSign hξ n o).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs]; exact abs_iidSign_le ξ n o ω))
  have hpair : ((Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).Pairwise
      (fun i j => IndepFun (iidSign ξ n i) (iidSign ξ n j) P) := by
    intro i _ j _ hij
    exact (iIndepFun_iidSign hindep n).indepFun hij
  have hsum := IndepFun.variance_sum (μ := P) (X := iidSign ξ n)
    (s := Finset.univ) (fun o _ => hmem o) hpair
  have hfun : (∑ o ∈ Finset.univ, iidSign ξ n o) = depSum (iidSign ξ n) := by
    funext ω
    exact Finset.sum_apply ω Finset.univ (iidSign ξ n)
  rw [hfun] at hsum
  have hmeasSum : Measurable (depSum (iidSign ξ n)) :=
    Finset.measurable_sum _ (fun o _ => measurable_iidSign hξ n o)
  have hmean0 : ∫ ω, depSum (iidSign ξ n) ω ∂P = 0 := by
    simp only [depSum]
    rw [MeasureTheory.integral_finsetSum _ (fun o _ => (hmem o).integrable (by norm_num))]
    simp [integral_iidSign hlaw]
  have hvarO : ∀ o : Fin (n + 1), variance (iidSign ξ n o) P = 1 / ((n : ℝ) + 1) := by
    intro o
    rw [variance_of_integral_eq_zero (measurable_iidSign hξ n o).aemeasurable
      (integral_iidSign hlaw n o), integral_iidSign_sq]
  rw [← variance_of_integral_eq_zero hmeasSum.aemeasurable hmean0, hsum]
  rw [Finset.sum_congr rfl (fun o _ => hvarO o), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- The hypotheses of `cltcluster_a_unconditional_of_frozen` hold on `n+1` singleton clusters
of one fair sign each, scaled by `(n+1)^{-1/2}`, at `𝒟 = ⊥`. `hfrozen` is proved by
`cltcluster_a_oneDimension_tendstoInDistribution` and `hfreeze` by `condExp_bot`. The statement
gives the unit total variance, the limit law and its CDF form. -/
theorem cltcluster_a_unconditional_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → Bool),
      (∀ n : ℕ, ∫ ω, (depSum (iidSign ξ n) ω) ^ 2 ∂P = 1)
    ∧ TendstoInDistribution (fun n : ℕ => depSum (iidSign ξ n)) atTop (id : ℝ → ℝ)
        (fun _ => P) (gaussianReal 0 1)
    ∧ (∀ s : ℝ, Tendsto (fun n : ℕ => (P.map (depSum (iidSign ξ n))).real (Set.Iic s)) atTop
        (𝓝 ((gaussianReal 0 1).real (Set.Iic s)))) := by
  obtain ⟨Ω, mΩ, P, ξ, hξ, hlaw, hindep, hprob⟩ := exists_iid (ℕ × ℕ) coin
  have hmeasSum : ∀ n : ℕ, Measurable (depSum (iidSign ξ n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => measurable_iidSign hξ n o)
  have hvar : ∀ n : ℕ, ∫ ω, (depSum (iidSign ξ n) ω) ^ 2 ∂P = 1 :=
    integral_depSum_iidSign_sq hξ hlaw hindep
  have hrate : Tendsto (fun n : ℕ => ((1 : ℕ) : ℝ) * (1 / Real.sqrt ((n : ℝ) + 1))) atTop
      (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simp only [Nat.cast_one, one_mul, one_div]
    exact hsqrt.inv_tendsto_atTop
  have hfrozen : TendstoInDistribution (fun n : ℕ => depSum (iidSign ξ n)) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 1) :=
    cltcluster_a_oneDimension_tendstoInDistribution (Ω := fun _ => Ω) (fun _ => P) (iidSign ξ)
      (fun n => (id : Fin (n + 1) → Fin (n + 1))) (fun n => iidDep hξ hindep n)
      (fun _ _ _ => Iff.rfl) (fun n => 1 / Real.sqrt ((n : ℝ) + 1)) (fun _ => 1)
      (fun n => by positivity) (fun n o ω => abs_iidSign_le ξ n o ω)
      (fun n γ => witX_cluster_card n γ) (fun n o => integral_iidSign hlaw n o) hvar hrate
  have hfreeze : ∀ (n : ℕ) (t : ℝ),
      Multiway.CLTMartingale.CondD.condCharFunD ⊥ P (depSum (iidSign ξ n)) t
        =ᵐ[P] fun _ => charFun (P.map (depSum (iidSign ξ n))) t := by
    intro n t
    have hbot : Multiway.CLTMartingale.CondD.condCharFunD ⊥ P (depSum (iidSign ξ n)) t
        = fun _ => charFun (P.map (depSum (iidSign ξ n))) t := by
      rw [Multiway.CLTMartingale.CondD.condCharFunD, condExp_bot, charFun_apply,
        integral_map (hmeasSum n).aemeasurable (by fun_prop)]
    exact Filter.Eventually.of_forall fun ω => congrFun hbot ω
  have huncond : TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n : ℕ => depSum (iidSign ξ n)) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) :=
    cltcluster_a_unconditional_of_frozen (Ω₀ := fun _ => Ω) ⊥ bot_le P
      (fun n => (hmeasSum n).aemeasurable) (fun _ _ => P)
      (fun _ n => depSum (iidSign ξ n)) hfreeze
      (Filter.Eventually.of_forall fun _ => hfrozen)
  exact ⟨Ω, mΩ, P, hprob, ξ, hvar, huncond,
    cltcluster_a_unconditional_cdf (fun n => (hmeasSum n).aemeasurable) huncond⟩

end UnconditionalWitness

/-! ## The unconditional limit law from the design's `𝒟`-measurability

The defining property of `ℙ_ω` is proved from `Multiway.CLTMartingale.CondD` and Mathlib's
`condExpKernel`. The conditional characteristic function is the characteristic function under
`condExpKernel P 𝒟 ω`, and a `𝒟`-measurable design is almost surely constant under it. This
requires `[StandardBorelSpace Ω]`. The results apply to the `J = 1`, general-`J` and part (b)
conditional limits. -/

section DesignDeconditioning

open Multiway.CLTMartingale.CondD

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The unconditional cluster CLT from the design's `𝒟`-measurability.** `W n` is the
standardized statistic on the unconditional space, `D n` the design and `𝒟` the design σ-field;
the statistic is a measurable function `F n` of the design and the disturbances (`hD`, `hF`,
`hW`). `hfrozen` is the conditional limit law at the frozen design under `condExpKernel P 𝒟 ω`. -/
theorem cltcluster_a_unconditional_of_design
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    {γ : Type*} [MeasurableSpace γ] [MeasurableEq γ]
    {D : ℕ → Ω → γ} (hD : ∀ n, Measurable[𝒟] (D n))
    {F : ℕ → γ → Ω → ℝ} (hF : ∀ n, Measurable (Function.uncurry (F n)))
    {W : ℕ → Ω → ℝ} (hW : ∀ n ω, W n ω = F n (D n ω) ω)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun (n : ℕ) (y : Ω) => F n (D n ω) y) atTop (id : ℝ → ℝ)
      (fun _ => condExpKernel P 𝒟 ω) (gaussianReal 0 1)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ) W atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) :=
  tendstoInDistribution_of_design (E := ℝ) h𝒟 P hD hF hW aemeasurable_id hfrozen

/-- The same conclusion in CDF form, `P[W_n ≤ s] → Φ(s)`. -/
theorem cltcluster_a_unconditional_cdf_of_design
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    {γ : Type*} [MeasurableSpace γ] [MeasurableEq γ]
    {D : ℕ → Ω → γ} (hD : ∀ n, Measurable[𝒟] (D n))
    {F : ℕ → γ → Ω → ℝ} (hF : ∀ n, Measurable (Function.uncurry (F n)))
    {W : ℕ → Ω → ℝ} (hW : ∀ n ω, W n ω = F n (D n ω) ω)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun (n : ℕ) (y : Ω) => F n (D n ω) y) atTop (id : ℝ → ℝ)
      (fun _ => condExpKernel P 𝒟 ω) (gaussianReal 0 1))
    (s : ℝ) :
    Tendsto (fun n => (@Measure.map Ω ℝ mΩ _ (W n) P).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  have hWm : ∀ n, Measurable (W n) := by
    intro n
    have heq : W n = fun ω => F n (D n ω) ω := funext (hW n)
    rw [heq]
    exact (hF n).comp (((hD n).mono h𝒟 le_rfl).prodMk measurable_id)
  exact cltcluster_a_unconditional_cdf (fun n => (hWm n).aemeasurable)
    (cltcluster_a_unconditional_of_design h𝒟 P hD hF hW hfrozen) s

end DesignDeconditioning

/-! ### An example with a nontrivial design σ-field

On `Ω = Bool × ℝ` the first coordinate is a fair design coin and the second an independent
standard Gaussian disturbance, and `𝒟 = σ(coin)` is a proper sub-σ-field. The design at index `n` is `±(n+1)^{-1}` with its sign
read off the coin, and the statistic depends on the design. The conditional law of the
disturbance is identified as `N(0,1)` through independence (`map_snd_condExpKernel`). The frozen
statistic has law `N(0,1)` at every `n`. -/

namespace DesignWitness

open Multiway.CLTMartingale.CondD
open Multiway.CLTMartingale.CondD.FrozenWitness (coin coin_singleton)

/-- The sample space of the example, a design coin and a standard Gaussian disturbance. -/
abbrev DOmg : Type := Bool × ℝ

/-- The law of the example, under which the coin is fair and independent of the disturbance. -/
noncomputable def Pdes : Measure DOmg := coin.prod (gaussianReal 0 1)

instance instIsProbabilityMeasurePdes : IsProbabilityMeasure Pdes := by
  unfold Pdes; infer_instance

example : StandardBorelSpace DOmg := inferInstance

set_option warn.classDefReducibility false in
/-- The design σ-field, generated by the coin. -/
def Ddes : MeasurableSpace DOmg := MeasurableSpace.comap Prod.fst inferInstance

theorem Ddes_le : Ddes ≤ (inferInstance : MeasurableSpace DOmg) :=
  measurable_fst.comap_le

/-- The coin is `𝒟`-measurable by construction. -/
theorem meas_fst_des : Measurable[Ddes] (Prod.fst : DOmg → Bool) :=
  measurable_iff_comap_le.2 le_rfl

/-- The design is random: each face has probability `1/2`. -/
theorem Pdes_fst (b : Bool) : Pdes {y : DOmg | y.1 = b} = 2⁻¹ := by
  have hset : {y : DOmg | y.1 = b} = ({b} : Set Bool) ×ˢ (Set.univ : Set ℝ) :=
    Set.ext fun y => by simp [Set.mem_prod, Set.mem_singleton_iff]
  rw [hset, Pdes, Measure.prod_prod, coin_singleton, measure_univ, mul_one]

/-- `𝒟` is a proper sub-σ-field: a `𝒟`-measurable set is a preimage under the coin, so it
cannot separate `(true,1)` from `(true,-1)`. -/
theorem Ddes_proper : ∃ B : Set DOmg, MeasurableSet B ∧ ¬ MeasurableSet[Ddes] B := by
  refine ⟨Prod.snd ⁻¹' Set.Ioi (0 : ℝ), measurable_snd measurableSet_Ioi, ?_⟩
  rintro ⟨t, -, ht⟩
  have h1 : ((true, (1 : ℝ)) : DOmg) ∈ Prod.fst ⁻¹' t := by rw [ht]; norm_num
  have h2 : ((true, (-1 : ℝ)) : DOmg) ∉ Prod.fst ⁻¹' t := by rw [ht]; norm_num
  exact h2 h1

/-- The disturbance is standard Gaussian under `P`. -/
theorem map_snd_Pdes : Measure.map (Prod.snd : DOmg → ℝ) Pdes = gaussianReal 0 1 :=
  Measure.snd_prod

/-- The disturbance is independent of the design σ-field. -/
theorem indep_snd_Ddes :
    IndepFun (Prod.snd : DOmg → ℝ) (Prod.fst : DOmg → Bool) Pdes := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_snd.aemeasurable
    measurable_fst.aemeasurable]
  have h2 : Measure.map (Prod.fst : DOmg → Bool) Pdes = coin := Measure.fst_prod
  rw [map_snd_Pdes, h2]
  exact Measure.prod_swap

/-- The conditional probability of a disturbance event is its unconditional probability, for
almost every realization of the design. -/
theorem condExpKernel_real_preimage (A : Set ℝ) (hA : MeasurableSet A) :
    ∀ᵐ ω ∂Pdes, (condExpKernel Pdes Ddes ω).real (Prod.snd ⁻¹' A)
      = Pdes.real (Prod.snd ⁻¹' A) := by
  have hs : MeasurableSet (Prod.snd ⁻¹' A : Set DOmg) := measurable_snd hA
  have h1 := condExpKernel_ae_eq_condExp (m := Ddes) (μ := Pdes) Ddes_le hs
  have hsm : StronglyMeasurable[MeasurableSpace.comap (Prod.snd : DOmg → ℝ) inferInstance]
      ((Prod.snd ⁻¹' A : Set DOmg).indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator ⟨A, hA, rfl⟩
  have h2 := condExp_indep_eq (m₁ := MeasurableSpace.comap (Prod.snd : DOmg → ℝ) inferInstance)
    (m₂ := Ddes) measurable_snd.comap_le Ddes_le hsm indep_snd_Ddes
  have h3 : ∫ y, (Prod.snd ⁻¹' A : Set DOmg).indicator (fun _ => (1 : ℝ)) y ∂Pdes
      = Pdes.real (Prod.snd ⁻¹' A) := integral_indicator_one hs
  filter_upwards [h1, h2] with ω hω hω2
  rw [hω, hω2, h3]

/-- The conditional law of the disturbance is `N(0,1)` for almost every realization of the
design, via the countable π-system of rational half-lines. -/
theorem map_snd_condExpKernel :
    ∀ᵐ ω ∂Pdes, Measure.map (Prod.snd : DOmg → ℝ) (condExpKernel Pdes Ddes ω)
      = gaussianReal 0 1 := by
  have hall : ∀ᵐ ω ∂Pdes, ∀ q : ℚ,
      (condExpKernel Pdes Ddes ω).real (Prod.snd ⁻¹' Set.Iio ((q : ℝ)))
        = Pdes.real (Prod.snd ⁻¹' Set.Iio ((q : ℝ))) :=
    ae_all_iff.2 fun q => condExpKernel_real_preimage _ measurableSet_Iio
  filter_upwards [hall] with ω hω
  have hprob : IsProbabilityMeasure
      (Measure.map (Prod.snd : DOmg → ℝ) (condExpKernel Pdes Ddes ω)) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance
  refine MeasureTheory.ext_of_generate_finite (⋃ a : ℚ, {Set.Iio ((a : ℝ))})
    (BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Iio_rat)
    Real.isPiSystem_Iio_rat ?_ (by simp)
  rintro s hs
  simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
  obtain ⟨q, rfl⟩ := hs
  have hq : (condExpKernel Pdes Ddes ω) (Prod.snd ⁻¹' Set.Iio ((q : ℝ)))
      = Pdes (Prod.snd ⁻¹' Set.Iio ((q : ℝ))) :=
    (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).1 (hω q)
  rw [Measure.map_apply measurable_snd measurableSet_Iio, hq, ← map_snd_Pdes,
    Measure.map_apply measurable_snd measurableSet_Iio]

/-- The sign of the design, `+1` on one face of the coin and `-1` on the other. -/
noncomputable def sgnDes (ω : DOmg) : ℝ := if ω.1 then (1 : ℝ) else -1

theorem sgnDes_sq (ω : DOmg) : (sgnDes ω) ^ 2 = 1 := by
  cases h : ω.1 <;> simp [sgnDes, h]

/-- The sequence of designs: at index `n` the design is `±(n+1)^{-1}`, its sign read off the
coin. It is `𝒟`-measurable because it factors through the coin. -/
noncomputable def ddes (n : ℕ) (ω : DOmg) : ℝ := ((n : ℝ) + 1)⁻¹ * sgnDes ω

theorem ddes_apply (n : ℕ) (ω : DOmg) :
    ddes n ω = ((n : ℝ) + 1)⁻¹ * (if ω.1 then (1 : ℝ) else -1) := rfl

theorem meas_ddes (n : ℕ) : Measurable[Ddes] (ddes n) := by
  have h : ddes n = (fun b : Bool => ((n : ℝ) + 1)⁻¹ * (if b then (1 : ℝ) else -1)) ∘ Prod.fst :=
    rfl
  rw [h]
  exact Measurable.of_discrete.comp meas_fst_des

/-- The statistic as a measurable function of the design and the disturbance: at `g` it is
`(n+1)g` times the disturbance. -/
noncomputable def Fdes (n : ℕ) (g : ℝ) (y : DOmg) : ℝ := ((n : ℝ) + 1) * g * y.2

theorem meas_Fdes (n : ℕ) : Measurable (Function.uncurry (Fdes n)) := by
  unfold Function.uncurry Fdes
  fun_prop

/-- At the frozen design the statistic is `±` the disturbance, the `(n+1)` of `F` cancelling the
`(n+1)^{-1}` of the design. -/
theorem Fdes_frozen (n : ℕ) (ω : DOmg) : Fdes n (ddes n ω) = fun y => sgnDes ω * y.2 := by
  funext y
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  show ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * sgnDes ω) * y.2 = sgnDes ω * y.2
  rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

instance instIsProbabilityMeasure_condExpKernel_Pdes (ω : DOmg) :
    IsProbabilityMeasure (condExpKernel Pdes Ddes ω) := inferInstance

/-- The frozen statistic has law `N(0,1)` under `ℙ_ω`, by the neg-invariance of the
standard Gaussian. -/
theorem map_Fdes_frozen {ω : DOmg}
    (hω : Measure.map (Prod.snd : DOmg → ℝ) (condExpKernel Pdes Ddes ω) = gaussianReal 0 1)
    (n : ℕ) :
    Measure.map (Fdes n (ddes n ω)) (condExpKernel Pdes Ddes ω) = gaussianReal 0 1 := by
  have hcomp : (fun y : DOmg => sgnDes ω * y.2)
      = (fun x : ℝ => sgnDes ω * x) ∘ (Prod.snd : DOmg → ℝ) := rfl
  rw [Fdes_frozen, hcomp, ← Measure.map_map (by fun_prop) measurable_snd, hω,
    gaussianReal_map_const_mul (sgnDes ω)]
  congr 1
  · ring
  · rw [mul_one]
    refine NNReal.coe_injective ?_
    simpa using sgnDes_sq ω

/-- `hfrozen` for this model: the frozen statistic converges in distribution to `N(0,1)` under
`ℙ_ω` for almost every realization, since it has that law at every `n`. -/
theorem hfrozen_des : ∀ᵐ ω ∂Pdes,
    TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace DOmg))
      (fun (n : ℕ) (y : DOmg) => Fdes n (ddes n ω) y) atTop (id : ℝ → ℝ)
      (fun _ => condExpKernel Pdes Ddes ω) (gaussianReal 0 1) := by
  filter_upwards [map_snd_condExpKernel] with ω hω
  have hm : ∀ n : ℕ, Measurable (fun y : DOmg => Fdes n (ddes n ω) y) := by
    intro n
    unfold Fdes
    fun_prop
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hm n).aemeasurable)
    aemeasurable_id fun t => ?_
  rw [Measure.map_id]
  have hconst : ∀ n : ℕ,
      charFun (Measure.map (fun y : DOmg => Fdes n (ddes n ω) y) (condExpKernel Pdes Ddes ω)) t
        = charFun (gaussianReal 0 1) t := fun n => by rw [map_Fdes_frozen hω n]
  simp only [hconst]
  exact tendsto_const_nhds

/-- `ℙ_ω` is not `P`: freezing forces `ℙ_ω` onto the half of the space where the coin agrees
with `ω`, which has `P`-measure `1/2`. -/
theorem condExpKernel_ne_Pdes : ¬ (∀ᵐ ω ∂Pdes, condExpKernel Pdes Ddes ω = Pdes) := by
  intro h
  have hfz := ae_ae_eq_condExpKernel Ddes_le Pdes meas_fst_des
  have hall : ∀ᵐ ω ∂Pdes, ∀ᵐ y ∂Pdes, y.1 = ω.1 := by
    filter_upwards [h, hfz] with ω hq hf
    rwa [hq] at hf
  obtain ⟨ω₀, hω₀⟩ := hall.exists
  have hz : Pdes {y : DOmg | ¬ (y.1 = ω₀.1)} = 0 := ae_iff.1 hω₀
  have hset : {y : DOmg | ¬ (y.1 = ω₀.1)} = {y : DOmg | y.1 = !ω₀.1} := by
    ext y
    obtain ⟨y1, y2⟩ := y
    cases y1 <;> cases ω₀.1 <;> simp
  rw [hset, Pdes_fst] at hz
  exact (ENNReal.inv_ne_zero.2 (by simp)) hz

/-- The hypotheses of `cltcluster_a_unconditional_of_design` hold on this model. In order, the
conjuncts state that the design is `±(n+1)^{-1}` with the sign of the coin, that the statistic
depends on the design, that each face of the coin has probability `1/2`, that `𝒟` is a proper
sub-σ-field and that `ℙ_ω ≠ P`, followed by the unconditional limit law `N(0,1)` and its CDF
form. -/
theorem cltcluster_a_unconditional_design_witness :
    (∀ (n : ℕ) (ω : DOmg),
        ddes n ω = ((n : ℝ) + 1)⁻¹ * (if ω.1 then (1 : ℝ) else -1))
    ∧ (∀ (n : ℕ) (y : DOmg), Fdes n 1 y = ((n : ℝ) + 1) * y.2
        ∧ Fdes n (-1) y = -(((n : ℝ) + 1) * y.2))
    ∧ Pdes {y : DOmg | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set DOmg, MeasurableSet B ∧ ¬ MeasurableSet[Ddes] B)
    ∧ ¬ (∀ᵐ ω ∂Pdes, condExpKernel Pdes Ddes ω = Pdes)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace DOmg))
        (fun (n : ℕ) (ω : DOmg) => Fdes n (ddes n ω) ω) atTop (id : ℝ → ℝ)
        (fun _ => Pdes) (gaussianReal 0 1)
    ∧ (∀ s : ℝ, Tendsto (fun n : ℕ =>
        (Measure.map (fun ω : DOmg => Fdes n (ddes n ω) ω) Pdes).real (Set.Iic s)) atTop
        (𝓝 ((gaussianReal 0 1).real (Set.Iic s)))) := by
  refine ⟨ddes_apply, fun n y => ⟨by simp [Fdes], by simp [Fdes]; ring⟩, Pdes_fst true,
    Ddes_proper, condExpKernel_ne_Pdes, ?_, ?_⟩
  · exact cltcluster_a_unconditional_of_design (𝒟 := Ddes) Ddes_le Pdes
      (D := ddes) meas_ddes (F := Fdes) meas_Fdes (fun _ _ => rfl) hfrozen_des
  · exact fun s => cltcluster_a_unconditional_cdf_of_design (𝒟 := Ddes) Ddes_le Pdes
      (D := ddes) meas_ddes (F := Fdes) meas_Fdes (fun _ _ => rfl) hfrozen_des s

end DesignWitness

/-! ## General `J`: an arbitrary sharing relation

The sharing relation is an arbitrary `DepGraph` with a bound `m n` on its neighbourhood
cardinalities; no cluster map appears, so the number `J` of clustering dimensions plays no role.
The rate condition is `(n/D_n)^{1/3}δ_n → 0`. The first Stein error term is bounded by counting
the edge products in `∑_oX_oT_o = ∑_{o∼o'}X_oX_{o'}`. Two edge products are uncorrelated unless
they share a neighbour, and each covariance is at most `2φ⁴`, which gives `E₁ ≤ 8nm³φ⁴`. -/

section GeneralErrors

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : O → Ω → ℝ}

/-- `|Cov(f,g)| ≤ 2c²` for two variables bounded by `c`. -/
theorem abs_covariance_le_two_mul_sq {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {c : ℝ} (hc : 0 ≤ c) (hfc : ∀ ω, |f ω| ≤ c) (hgc : ∀ ω, |g ω| ≤ c) :
    |covariance f g μ| ≤ 2 * c ^ 2 := by
  have hMf : MemLp f 2 μ := memLp_two_of_bdd hf hfc
  have hMg : MemLp g 2 μ := memLp_two_of_bdd hg hgc
  rw [covariance_eq_sub hMf hMg]
  have hprod : |μ[f * g]| ≤ c ^ 2 := by
    have hint : Integrable (f * g) μ := hMf.integrable_mul hMg
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |(f * g) ω| ∂μ ≤ ∫ _ω, c ^ 2 ∂μ := by
          refine integral_mono hint.abs (integrable_const _) (fun ω => ?_)
          rw [Pi.mul_apply, abs_mul, sq]
          exact mul_le_mul (hfc ω) (hgc ω) (abs_nonneg _) hc
      _ = c ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  have hEf : |μ[f]| ≤ c := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |f ω| ∂μ ≤ ∫ _ω, c ∂μ :=
          integral_mono (hMf.integrable one_le_two).abs (integrable_const _) hfc
      _ = c := by rw [integral_const, probReal_univ, one_smul]
  have hEg : |μ[g]| ≤ c := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |g ω| ∂μ ≤ ∫ _ω, c ∂μ :=
          integral_mono (hMg.integrable one_le_two).abs (integrable_const _) hgc
      _ = c := by rw [integral_const, probReal_univ, one_smul]
  calc |μ[f * g] - μ[f] * μ[g]| ≤ |μ[f * g]| + |μ[f] * μ[g]| := abs_sub _ _
    _ ≤ c ^ 2 + c ^ 2 := by
        refine add_le_add hprod ?_
        rw [abs_mul, sq]
        exact mul_le_mul hEf hEg (abs_nonneg _) hc
    _ = 2 * c ^ 2 := by ring

/-- The summands of the localized double sum, indexed by ordered pairs, are `X_oX_{o'}` on a
sharing pair `o ∼ o'` and `0` otherwise. -/
noncomputable def pairProd (X : O → Ω → ℝ) (N : O → Finset O) (p : O × O) : Ω → ℝ :=
  fun ω => if p.2 ∈ N p.1 then X p.1 ω * X p.2 ω else 0

omit [MeasurableSpace Ω] in
/-- The two decompositions of the localized double sum agree:
`∑_oX_oT_o = ∑_{(o,o')}W_{(o,o')}`. -/
theorem sum_pairProd (X : O → Ω → ℝ) (N : O → Finset O) (ω : Ω) :
    ∑ p : O × O, pairProd X N p ω = ∑ o, X o ω * nbhdSum X N o ω := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [pairProd, nbhdSum]
  rw [Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]

/-- The first Stein error term at general `J`, `Var(∑_oX_oT_o) ≤ 8nm³φ⁴`, where `m`
bounds the closed neighbourhood sizes and `|X_o| ≤ φ`. Two edge products are uncorrelated unless
some vertex of one shares with some vertex of the other, which leaves at most `4m²` partners per
edge; each covariance is at most `2φ⁴`, and there are at most `nm` edges. -/
theorem firstError_le_general (D : DepGraph X μ) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ : ∀ o ω, |X o ω| ≤ φ) {m : ℕ} (hdeg : ∀ o, (D.nbhd o).card ≤ m) :
    variance (fun ω => ∑ o, X o ω * nbhdSum X D.nbhd o ω) μ
      ≤ 8 * (Fintype.card O : ℝ) * (m : ℝ) ^ 3 * φ ^ 4 := by
  classical
  set W : O × O → Ω → ℝ := pairProd X D.nbhd with hWdef
  have hWapp : ∀ (p : O × O) (ω : Ω),
      W p ω = if p.2 ∈ D.nbhd p.1 then X p.1 ω * X p.2 ω else 0 := fun _ _ => rfl
  have hWmeas : ∀ p, Measurable (W p) := by
    intro p
    have hre : W p = fun ω => if p.2 ∈ D.nbhd p.1 then X p.1 ω * X p.2 ω else 0 := rfl
    rw [hre]
    split_ifs with h
    · exact (D.meas p.1).mul (D.meas p.2)
    · exact measurable_const
  have hWbd : ∀ p ω, |W p ω| ≤ φ ^ 2 := by
    intro p ω
    rw [hWapp]
    split_ifs with h
    · rw [abs_mul, sq]
      exact mul_le_mul (hφ _ _) (hφ _ _) (abs_nonneg _) hφ0
    · rw [abs_zero]; positivity
  have hWmem : ∀ p, MemLp (W p) 2 μ := fun p => memLp_two_of_bdd (hWmeas p) (hWbd p)
  have hfun : (fun ω => ∑ o, X o ω * nbhdSum X D.nbhd o ω) = fun ω => ∑ p : O × O, W p ω := by
    funext ω; rw [hWdef, sum_pairProd]
  rw [hfun, variance_fun_sum hWmem]
  -- an edge product off the sharing relation is identically zero
  have hWzero : ∀ p : O × O, p.2 ∉ D.nbhd p.1 → W p = 0 := by
    intro p hp
    funext ω
    rw [hWapp]
    simp [hp]
  -- separated edges are uncorrelated
  have hsep_zero : ∀ p q : O × O, p.2 ∈ D.nbhd p.1 → q.2 ∈ D.nbhd q.1 →
      (∀ a ∈ ({p.1, p.2} : Finset O), ∀ b ∈ ({q.1, q.2} : Finset O), ¬ D.G a b) →
      covariance (W p) (W q) μ = 0 := by
    intro p q hp hq hs
    have h1 : p.1 ∈ ({p.1, p.2} : Finset O) := Finset.mem_insert_self _ _
    have h2 : p.2 ∈ ({p.1, p.2} : Finset O) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have k1 : q.1 ∈ ({q.1, q.2} : Finset O) := Finset.mem_insert_self _ _
    have k2 : q.2 ∈ ({q.1, q.2} : Finset O) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hind := D.indep ({p.1, p.2} : Finset O) ({q.1, q.2} : Finset O) hs
    have hmp : Measurable
        (fun t : (↥({p.1, p.2} : Finset O) → ℝ) => t ⟨p.1, h1⟩ * t ⟨p.2, h2⟩) :=
      (measurable_pi_apply _).mul (measurable_pi_apply _)
    have hmq : Measurable
        (fun t : (↥({q.1, q.2} : Finset O) → ℝ) => t ⟨q.1, k1⟩ * t ⟨q.2, k2⟩) :=
      (measurable_pi_apply _).mul (measurable_pi_apply _)
    have hcomp := hind.comp hmp hmq
    have ep : ((fun t : (↥({p.1, p.2} : Finset O) → ℝ) => t ⟨p.1, h1⟩ * t ⟨p.2, h2⟩)
        ∘ (fun ω => fun k : ({p.1, p.2} : Finset O) => X k ω)) = W p := by
      funext ω; rw [hWapp]; simp [hp]
    have eq' : ((fun t : (↥({q.1, q.2} : Finset O) → ℝ) => t ⟨q.1, k1⟩ * t ⟨q.2, k2⟩)
        ∘ (fun ω => fun k : ({q.1, q.2} : Finset O) => X k ω)) = W q := by
      funext ω; rw [hWapp]; simp [hq]
    rw [ep, eq'] at hcomp
    exact hcomp.covariance_eq_zero (hWmem p) (hWmem q)
  -- the partners of an edge: those with a vertex in its two-step neighbourhood
  set S : O × O → Finset O := fun p => D.nbhd p.1 ∪ D.nbhd p.2 with hSdef
  set T : O × O → Finset (O × O) := fun p =>
    (S p).biUnion (fun a => {a} ×ˢ D.nbhd a) ∪ (S p).biUnion (fun a => D.nbhd a ×ˢ {a})
    with hTdef
  have hout : ∀ p q : O × O, p.2 ∈ D.nbhd p.1 → q ∉ T p → covariance (W p) (W q) μ = 0 := by
    intro p q hp hqT
    by_cases hq : q.2 ∈ D.nbhd q.1
    · refine hsep_zero p q hp hq ?_
      intro a ha b hb hab
      exfalso
      apply hqT
      have hbS : b ∈ S p := by
        rcases Finset.mem_insert.mp ha with h | h
        · subst h; exact Finset.mem_union_left _ (D.mem_nbhd_iff.mpr hab)
        · rw [Finset.mem_singleton] at h; subst h
          exact Finset.mem_union_right _ (D.mem_nbhd_iff.mpr hab)
      rcases Finset.mem_insert.mp hb with h | h
      · rw [hTdef]
        refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q.1, ?_, ?_⟩)
        · rw [← h]; exact hbS
        · rw [Finset.mem_product]
          exact ⟨Finset.mem_singleton_self _, hq⟩
      · rw [Finset.mem_singleton] at h
        have hq1 : q.1 ∈ D.nbhd q.2 :=
          D.mem_nbhd_iff.mpr (D.symm _ _ (D.mem_nbhd_iff.mp hq))
        rw [hTdef]
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q.2, ?_, ?_⟩)
        · rw [← h]; exact hbS
        · rw [Finset.mem_product]
          exact ⟨hq1, Finset.mem_singleton_self _⟩
    · rw [hWzero q hq]
      exact covariance_zero_right
  have hcardS : ∀ p, (S p).card ≤ 2 * m := by
    intro p
    refine (Finset.card_union_le _ _).trans ?_
    have := hdeg p.1
    have := hdeg p.2
    omega
  have hcardT : ∀ p, (T p).card ≤ 4 * m ^ 2 := by
    intro p
    have hA : ((S p).biUnion (fun a => ({a} : Finset O) ×ˢ D.nbhd a)).card ≤ 2 * m * m := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ a ∈ S p, (({a} : Finset O) ×ˢ D.nbhd a).card
          ≤ ∑ _a ∈ S p, m := by
            refine Finset.sum_le_sum (fun a _ => ?_)
            rw [Finset.card_product, Finset.card_singleton, one_mul]
            exact hdeg a
        _ = (S p).card * m := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (2 * m) * m := Nat.mul_le_mul_right m (hcardS p)
    have hB : ((S p).biUnion (fun a => D.nbhd a ×ˢ ({a} : Finset O))).card ≤ 2 * m * m := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ a ∈ S p, (D.nbhd a ×ˢ ({a} : Finset O)).card
          ≤ ∑ _a ∈ S p, m := by
            refine Finset.sum_le_sum (fun a _ => ?_)
            rw [Finset.card_product, Finset.card_singleton, mul_one]
            exact hdeg a
        _ = (S p).card * m := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (2 * m) * m := Nat.mul_le_mul_right m (hcardS p)
    have := (Finset.card_union_le ((S p).biUnion (fun a => ({a} : Finset O) ×ˢ D.nbhd a))
      ((S p).biUnion (fun a => D.nbhd a ×ˢ ({a} : Finset O))))
    rw [hTdef]
    nlinarith [this, hA, hB]
  have hinner : ∀ p : O × O, p.2 ∈ D.nbhd p.1 →
      ∑ q : O × O, covariance (W p) (W q) μ ≤ 8 * (m : ℝ) ^ 2 * φ ^ 4 := by
    intro p hp
    have hrestrict : ∑ q : O × O, covariance (W p) (W q) μ
        = ∑ q ∈ T p, covariance (W p) (W q) μ := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => hout p q hp hq)
    rw [hrestrict]
    have hTcard : ((T p).card : ℝ) ≤ 4 * (m : ℝ) ^ 2 := by
      have := hcardT p
      exact_mod_cast this
    calc ∑ q ∈ T p, covariance (W p) (W q) μ
        ≤ ∑ q ∈ T p, |covariance (W p) (W q) μ| :=
          Finset.sum_le_sum (fun q _ => le_abs_self _)
      _ ≤ ∑ _q ∈ T p, 2 * (φ ^ 2) ^ 2 :=
          Finset.sum_le_sum (fun q _ => abs_covariance_le_two_mul_sq (hWmeas p) (hWmeas q)
            (by positivity) (hWbd p) (hWbd q))
      _ = ((T p).card : ℝ) * (2 * (φ ^ 2) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * (m : ℝ) ^ 2) * (2 * (φ ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_right hTcard (by positivity)
      _ = 8 * (m : ℝ) ^ 2 * φ ^ 4 := by ring
  have hinner0 : ∀ p : O × O, p.2 ∉ D.nbhd p.1 →
      ∑ q : O × O, covariance (W p) (W q) μ = 0 := by
    intro p hp
    rw [hWzero p hp]
    simp
  have hnn : (0 : ℝ) ≤ 8 * (m : ℝ) ^ 2 * φ ^ 4 := by positivity
  calc ∑ p : O × O, ∑ q : O × O, covariance (W p) (W q) μ
      = ∑ o : O, ∑ k : O, ∑ q : O × O, covariance (W (o, k)) (W q) μ := by
        rw [Fintype.sum_prod_type]
    _ = ∑ o : O, ∑ k ∈ D.nbhd o, ∑ q : O × O, covariance (W (o, k)) (W q) μ := by
        refine Finset.sum_congr rfl (fun o _ => ?_)
        symm
        refine Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => hinner0 (o, k) hk)
    _ ≤ ∑ o : O, ∑ _k ∈ D.nbhd o, 8 * (m : ℝ) ^ 2 * φ ^ 4 :=
        Finset.sum_le_sum (fun o _ => Finset.sum_le_sum (fun k hk => hinner (o, k) hk))
    _ = ∑ o : O, ((D.nbhd o).card : ℝ) * (8 * (m : ℝ) ^ 2 * φ ^ 4) := by
        refine Finset.sum_congr rfl (fun o _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _o : O, (m : ℝ) * (8 * (m : ℝ) ^ 2 * φ ^ 4) := by
        refine Finset.sum_le_sum (fun o _ => ?_)
        refine mul_le_mul_of_nonneg_right ?_ hnn
        exact_mod_cast hdeg o
    _ = (Fintype.card O : ℝ) * ((m : ℝ) * (8 * (m : ℝ) ^ 2 * φ ^ 4)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 8 * (Fintype.card O : ℝ) * (m : ℝ) ^ 3 * φ ^ 4 := by ring

omit [DecidableEq O] in
/-- The second Stein error term at general `J`, `∑_oE[|X_o|T_o²] ≤ nm²φ³`. -/
theorem secondError_le_general (D : DepGraph X μ) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ : ∀ o ω, |X o ω| ≤ φ) {m : ℕ} (hdeg : ∀ o, (D.nbhd o).card ≤ m) :
    ∑ o, ∫ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ∂μ
      ≤ (Fintype.card O : ℝ) * (m : ℝ) ^ 2 * φ ^ 3 :=
  (DepGraph.sum_E_nbhd_sq_le D.nbhd (fun o => D.meas o) hφ0 hφ hdeg).trans (le_of_eq (by ring))

end GeneralErrors

section GeneralRates

/-! ### The rate scalars

`accumRate` is `δ_n`, `steinRate` is `(n/D_n)^{1/3}δ_n` and `secondRate` bounds `E₂`. The identity
`secondRate⁴ = steinRate³`, between integer powers, lets one hypothesis control both error terms,
and `δ_n ≤ steinRate` since `D_n ≤ n`. -/

/-- `δ_n := nD_n³/λ_min(Ω_n)²`. -/
noncomputable def accumRate (N Dn : ℕ) (lmin : ℝ) : ℝ := (N : ℝ) * (Dn : ℝ) ^ 3 / lmin ^ 2

/-- `(n/D_n)^{1/3}δ_n`, the rate of the general-`J` theorems. -/
noncomputable def steinRate (N Dn : ℕ) (lmin : ℝ) : ℝ :=
  ((N : ℝ) / (Dn : ℝ)) ^ ((1 : ℝ) / 3) * accumRate N Dn lmin

/-- `nD_n²/λ_min(Ω_n)^{3/2}`, the scalar that bounds `E₂` at general `J`. -/
noncomputable def secondRate (N Dn : ℕ) (lmin : ℝ) : ℝ :=
  (N : ℝ) * (Dn : ℝ) ^ 2 / (lmin * Real.sqrt lmin)

theorem accumRate_nonneg (N Dn : ℕ) {lmin : ℝ} : 0 ≤ accumRate N Dn lmin := by
  unfold accumRate; positivity

theorem secondRate_nonneg (N Dn : ℕ) {lmin : ℝ} (h : 0 ≤ lmin) :
    0 ≤ secondRate N Dn lmin := by
  unfold secondRate; positivity

theorem steinRate_nonneg (N Dn : ℕ) (lmin : ℝ) : 0 ≤ steinRate N Dn lmin := by
  unfold steinRate
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (accumRate_nonneg N Dn)

/-- `δ_n ≤ (n/D_n)^{1/3}δ_n`, since `D_n ≤ n`. -/
theorem accumRate_le_steinRate {N Dn : ℕ} (hD1 : 1 ≤ Dn) (hDN : Dn ≤ N) (lmin : ℝ) :
    accumRate N Dn lmin ≤ steinRate N Dn lmin := by
  have hDpos : (0 : ℝ) < (Dn : ℝ) := by exact_mod_cast hD1
  have hone : (1 : ℝ) ≤ (N : ℝ) / (Dn : ℝ) := by
    rw [le_div_iff₀ hDpos, one_mul]
    exact_mod_cast hDN
  have hrp : (1 : ℝ) ≤ ((N : ℝ) / (Dn : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow hone (by norm_num)
  unfold steinRate
  nth_rewrite 1 [← one_mul (accumRate N Dn lmin)]
  exact mul_le_mul_of_nonneg_right hrp (accumRate_nonneg N Dn)

/-- `(nD_n²/λ^{3/2})⁴ = ((n/D_n)^{1/3}δ_n)³`, since both sides equal `n⁴D_n⁸/λ⁶`. -/
theorem secondRate_pow_four {N Dn : ℕ} (hD1 : 1 ≤ Dn) {lmin : ℝ} (hl : 0 < lmin) :
    secondRate N Dn lmin ^ 4 = steinRate N Dn lmin ^ 3 := by
  have hDpos : (0 : ℝ) < (Dn : ℝ) := by exact_mod_cast hD1
  have hs : Real.sqrt lmin ^ 2 = lmin := Real.sq_sqrt hl.le
  have hcube : (((N : ℝ) / (Dn : ℝ)) ^ ((1 : ℝ) / 3)) ^ 3 = (N : ℝ) / (Dn : ℝ) := by
    rw [← Real.rpow_natCast (((N : ℝ) / (Dn : ℝ)) ^ ((1 : ℝ) / 3)) 3,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hs4 : (Real.sqrt lmin) ^ 4 = lmin ^ 2 := by
    have h2 : (Real.sqrt lmin) ^ 4 = ((Real.sqrt lmin) ^ 2) ^ 2 := by ring
    rw [h2, hs]
  have hden : (lmin * Real.sqrt lmin) ^ 4 = lmin ^ 6 := by
    rw [mul_pow, hs4]; ring
  have hL : secondRate N Dn lmin ^ 4 = ((N : ℝ) * (Dn : ℝ) ^ 2) ^ 4 / lmin ^ 6 := by
    unfold secondRate; rw [div_pow, hden]
  have hR : steinRate N Dn lmin ^ 3
      = ((N : ℝ) / (Dn : ℝ)) * ((N : ℝ) * (Dn : ℝ) ^ 3) ^ 3 / lmin ^ 6 := by
    unfold steinRate accumRate
    rw [mul_pow, hcube, div_pow]
    ring
  rw [hL, hR]
  field_simp

theorem tendsto_secondRate {N Dn : ℕ → ℕ} {lmin : ℕ → ℝ}
    (hD1 : ∀ n, 1 ≤ Dn n) (hl : ∀ n, 0 < lmin n)
    (h : Tendsto (fun n => steinRate (N n) (Dn n) (lmin n)) atTop (𝓝 0)) :
    Tendsto (fun n => secondRate (N n) (Dn n) (lmin n)) atTop (𝓝 0) := by
  have h3 : Tendsto (fun n => steinRate (N n) (Dn n) (lmin n) ^ 3) atTop (𝓝 0) := by
    simpa using h.pow 3
  have hsq : ∀ x : ℝ, 0 ≤ x → x = Real.sqrt (Real.sqrt (x ^ 4)) := by
    intro x hx
    have h4 : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [h4, Real.sqrt_sq (by positivity), Real.sqrt_sq hx]
  have hre : ∀ n, secondRate (N n) (Dn n) (lmin n)
      = Real.sqrt (Real.sqrt (steinRate (N n) (Dn n) (lmin n) ^ 3)) := by
    intro n
    rw [← secondRate_pow_four (hD1 n) (hl n)]
    exact hsq _ (secondRate_nonneg _ _ (hl n).le)
  have hcont : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0)
  simp only [hre]
  exact hcont.comp (hcont.comp h3)

theorem tendsto_accumRate {N Dn : ℕ → ℕ} {lmin : ℕ → ℝ}
    (hD1 : ∀ n, 1 ≤ Dn n) (hDN : ∀ n, Dn n ≤ N n)
    (h : Tendsto (fun n => steinRate (N n) (Dn n) (lmin n)) atTop (𝓝 0)) :
    Tendsto (fun n => accumRate (N n) (Dn n) (lmin n)) atTop (𝓝 0) :=
  squeeze_zero (fun _n => accumRate_nonneg _ _)
    (fun n => accumRate_le_steinRate (hD1 n) (hDN n) (lmin n)) h

private theorem div_le_div_of_num_le (c : ℝ) (hc : 0 < c) {a b : ℝ} (h : a ≤ b) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- The first error scalar: `n(D_n+1)³φ_n⁴ ≤ 8B⁴C_ν⁴δ_n`, using `D_n+1 ≤ 2D_n` and
`φ_n = BC_νλ_min(Ω_n)^{-1/2}`. -/
theorem firstRate_le {N D : ℕ} (hD1 : 1 ≤ D) {lmin B Cnu : ℝ} (hl : 0 < lmin) :
    (N : ℝ) * ((D + 1 : ℕ) : ℝ) ^ 3 * (B * Cnu / Real.sqrt lmin) ^ 4
      ≤ 8 * B ^ 4 * Cnu ^ 4 * accumRate N D lmin := by
  have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hs4 : (Real.sqrt lmin) ^ 4 = lmin ^ 2 := by
    have h2 : (Real.sqrt lmin) ^ 4 = ((Real.sqrt lmin) ^ 2) ^ 2 := by ring
    rw [h2, Real.sq_sqrt hl.le]
  have hcast : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
  have hlam : (0 : ℝ) < lmin ^ 2 := by positivity
  have hD3 : ((D : ℝ) + 1) ^ 3 ≤ 8 * (D : ℝ) ^ 3 := by
    calc ((D : ℝ) + 1) ^ 3 ≤ (2 * (D : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 3
      _ = 8 * (D : ℝ) ^ 3 := by ring
  have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hnum : (N : ℝ) * ((D : ℝ) + 1) ^ 3 * (B * Cnu) ^ 4
      ≤ 8 * B ^ 4 * Cnu ^ 4 * ((N : ℝ) * (D : ℝ) ^ 3) := by
    calc (N : ℝ) * ((D : ℝ) + 1) ^ 3 * (B * Cnu) ^ 4
        ≤ (N : ℝ) * (8 * (D : ℝ) ^ 3) * (B * Cnu) ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD3 hN) (by positivity)
      _ = 8 * B ^ 4 * Cnu ^ 4 * ((N : ℝ) * (D : ℝ) ^ 3) := by ring
  rw [hcast, div_pow, hs4]
  unfold accumRate
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact div_le_div_of_num_le _ hlam hnum

/-- The second error scalar: `n(D_n+1)²φ_n³ ≤ 4B³C_ν³nD_n²λ^{-3/2}`. -/
theorem secondRate_le {N D : ℕ} (hD1 : 1 ≤ D) {lmin B Cnu : ℝ}
    (hl : 0 < lmin) (hB0 : 0 ≤ B) (hC0 : 0 ≤ Cnu) :
    (N : ℝ) * ((D + 1 : ℕ) : ℝ) ^ 2 * (B * Cnu / Real.sqrt lmin) ^ 3
      ≤ 4 * B ^ 3 * Cnu ^ 3 * secondRate N D lmin := by
  have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hspos : 0 < Real.sqrt lmin := Real.sqrt_pos.mpr hl
  have hs3 : (Real.sqrt lmin) ^ 3 = lmin * Real.sqrt lmin := by
    have h2 : (Real.sqrt lmin) ^ 3 = ((Real.sqrt lmin) ^ 2) * Real.sqrt lmin := by ring
    rw [h2, Real.sq_sqrt hl.le]
  have hcast : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
  have hlam : (0 : ℝ) < lmin * Real.sqrt lmin := by positivity
  have hD2 : ((D : ℝ) + 1) ^ 2 ≤ 4 * (D : ℝ) ^ 2 := by
    calc ((D : ℝ) + 1) ^ 2 ≤ (2 * (D : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ = 4 * (D : ℝ) ^ 2 := by ring
  have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hnum : (N : ℝ) * ((D : ℝ) + 1) ^ 2 * (B * Cnu) ^ 3
      ≤ 4 * B ^ 3 * Cnu ^ 3 * ((N : ℝ) * (D : ℝ) ^ 2) := by
    calc (N : ℝ) * ((D : ℝ) + 1) ^ 2 * (B * Cnu) ^ 3
        ≤ (N : ℝ) * (4 * (D : ℝ) ^ 2) * (B * Cnu) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD2 hN) (by positivity)
      _ = 4 * B ^ 3 * Cnu ^ 3 * ((N : ℝ) * (D : ℝ) ^ 2) := by ring
  rw [hcast, div_pow, hs3]
  unfold secondRate
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact div_le_div_of_num_le _ hlam hnum

end GeneralRates

section GeneralCLT

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- `E₁ ≤ 8nm³φ⁴ → 0`, by `firstError_le_general`. -/
theorem firstError_tendsto_zero_general
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (φ : ℕ → ℝ) (m : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hrate : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (φ n) ^ 4)
      atTop (𝓝 0)) :
    Tendsto (fun n => variance (fun ω => ∑ o, X n o ω * nbhdSum (X n) (D n).nbhd o ω) (μ n))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun n => variance_nonneg _ _) (fun n => ?_)
    (by simpa using hrate.const_mul (8 : ℝ))
  simpa [mul_assoc] using firstError_le_general (D n) (hφ0 n) (hφ n) (hdeg n)

omit [∀ n, DecidableEq (O n)] in
/-- `E₂ ≤ nm²φ³ → 0`, by `secondError_le_general`. -/
theorem secondError_tendsto_zero_general
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (φ : ℕ → ℝ) (m : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hrate : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (φ n) ^ 3)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∑ o, ∫ ω, |X n o ω| * (nbhdSum (X n) (D n).nbhd o ω) ^ 2 ∂(μ n))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hrate
  · exact Finset.sum_nonneg (fun o _ => integral_nonneg (fun ω => by positivity))
  · exact secondError_le_general (D n) (hφ0 n) (hφ n) (hdeg n)

/-- **Theorem 5(a) at general `J`, on the array.** The sharing relation is an arbitrary
`DepGraph` with neighbourhoods of size at most `m n`, and there is one scalar rate hypothesis per
Stein error term; `cltcluster_a_general_betaJM` derives both from `(n/D_n)^{1/3}δ_n → 0`. -/
theorem cltcluster_a_general
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (φ : ℕ → ℝ) (m : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate1 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (φ n) ^ 4)
      atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (φ n) ^ 3)
      atTop (𝓝 0))
    (s : ℝ) :
    Tendsto (fun n => ((μ n).map (depSum (X n))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) :=
  stein_cdf_clt μ X (fun n => (D n).nbhd) (fun n o => (D n).meas o)
    φ hφ0 hφ hmean (fun n o => (D n).indepFun_leaveOut o) hvar
    (firstError_tendsto_zero_general μ X D φ m hφ0 hφ hdeg hrate1)
    (secondError_tendsto_zero_general μ X D φ m hφ0 hφ hdeg hrate2) s

/-- The general-`J` theorem in characteristic-function form, through
`charFun_tendsto_of_errors`. -/
theorem cltcluster_a_general_charFun
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (φ : ℕ → ℝ) (m : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate1 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (φ n) ^ 4)
      atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (φ n) ^ 3)
      atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (depSum (X n))) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) :=
  charFun_tendsto_of_errors μ X (fun n => (D n).nbhd) (fun n o => (D n).meas o)
    φ hφ0 hφ hmean (fun n o => (D n).indepFun_leaveOut o) hvar
    (firstError_tendsto_zero_general μ X D φ m hφ0 hφ hdeg hrate1)
    (secondError_tendsto_zero_general μ X D φ m hφ0 hφ hdeg hrate2) t

/-- The general-`J` theorem as `⟶ᵈ N(0,1)`, by Lévy's continuity theorem. -/
theorem cltcluster_a_general_tendstoInDistribution
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (φ : ℕ → ℝ) (m : ℕ → ℕ)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ : ∀ n o ω, |X n o ω| ≤ φ n)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate1 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (φ n) ^ 4)
      atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (φ n) ^ 3)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun n => depSum (X n)) atTop (id : ℝ → ℝ) μ (gaussianReal 0 1) := by
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n => by
    unfold depSum; exact Finset.measurable_sum _ (fun o _ => (D n).meas o)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hWmeas n).aemeasurable)
    aemeasurable_id fun t => ?_
  rw [Measure.map_id]
  exact cltcluster_a_general_charFun μ X D φ m hφ0 hφ hdeg hmean hvar hrate1 hrate2 t

end GeneralCLT

section GeneralBetaJM

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- The transported dependency graph has the same neighbourhoods. -/
theorem nbhd_scoreArrayDepGraph {O : Type*} [Fintype O] [DecidableEq O]
    {K : Type*} [Fintype K] [DecidableEq K]
    {W : Type*} [MeasurableSpace W] {μ : Measure W} [IsProbabilityMeasure μ]
    {v : O → W → ℝ} (D : DepGraph v μ) (Xt : Matrix O K ℝ) (a : K → ℝ) (o : O) :
    (scoreArrayDepGraph D Xt a).nbhd o = D.nbhd o := rfl

/-- **Theorem 5(a) at general `J`, for `β̂_JM`, under `(n/D_n)^{1/3}δ_n → 0`.** The array
reduction is as in `cltcluster_a_oneDimension_betaJM`, with `hshare` replaced by the degree bound
`hdeg`, so the sharing relation is arbitrary. `hDn1` is `D_n ≥ 1` and `hDnN` is `D_n ≤ n`. -/
theorem cltcluster_a_general_betaJM
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  have hacc : Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0) :=
    tendsto_accumRate hDn1 hDnN hrate
  have hsec : Tendsto (fun n => secondRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0) :=
    tendsto_secondRate hDn1 hlmin hrate
  simp only [hstat]
  refine cltcluster_a_general μ
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * Cnu / Real.sqrt (lmin n)) (fun n => Dn n + 1)
    (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ ?_ ?_ ?_ ?_ ?_ s
  · exact fun n o ω =>
      abs_scoreArray_le (hPD n) (hA n) (hlmin n) (hfloor n) hB0 (hB n) (hnu n) hb o ω
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hnu n) (hOm n) hb
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hacc.const_mul (8 * B ^ 4 * Cnu ^ 4))
    exact firstRate_le (hDn1 n) (hlmin n)
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hsec.const_mul (4 * B ^ 3 * Cnu ^ 3))
    exact secondRate_le (hDn1 n) (hlmin n) hB0 hCnu0

end GeneralBetaJM

section GeneralWitness

/-! ### An example with `J = 2`

The design has `n+3` observations and the sharing relation `|o − o'| ≤ 1`, the union of the two
clustering maps `g₁ o = ⌊o/2⌋` and `g₂ o = ⌊(o+1)/2⌋` (`pathG_iff_two_dimensions`). It is not
transitive (`pathG_not_transitive`), so the `J = 1` theorems do not apply. The disturbances are
independent fair signs. -/

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.Multilinear

/-- The sharing relation `|o − o'| ≤ 1` on `Fin N`. -/
def pathG (N : ℕ) : Fin N → Fin N → Prop :=
  fun o o' => o'.val = o.val ∨ o'.val + 1 = o.val ∨ o.val + 1 = o'.val

instance instDecidablePathG (N : ℕ) : DecidableRel (pathG N) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The relation `pathG` is the union of the two clustering maps `g₁ o = ⌊o/2⌋` and
`g₂ o = ⌊(o+1)/2⌋`. -/
theorem pathG_iff_two_dimensions {N : ℕ} (o o' : Fin N) :
    pathG N o o' ↔ (o.val / 2 = o'.val / 2 ∨ (o.val + 1) / 2 = (o'.val + 1) / 2) := by
  unfold pathG
  omega

/-- The relation `pathG` is not transitive, since `0 ∼ 1` and `1 ∼ 2` while `0 ≁ 2`. -/
theorem pathG_not_transitive (n : ℕ) :
    ∃ a b c : Fin (n + 3), pathG (n + 3) a b ∧ pathG (n + 3) b c ∧ ¬ pathG (n + 3) a c :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, Or.inr (Or.inr rfl), Or.inr (Or.inr rfl),
    by simp [pathG]⟩

/-- The example dependency graph, with `n+3` independent fair signs sharing along `pathG`. -/
noncomputable def pathDep (n : ℕ) :
    DepGraph (fun o : Fin (n + 3) => sign2 o) (coins (n + 3)) where
  G := pathG (n + 3)
  decG := fun _ _ => inferInstance
  refl := fun _ => Or.inl rfl
  symm := fun o o' h => by unfold pathG at h ⊢; omega
  meas := measurable_sign2
  indep := by
    intro A Bs h
    have hdisj : Disjoint A Bs := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact h a ha a hb (Or.inl rfl)
    exact (iIndepFun_sign2 (n + 3)).indepFun_finset A Bs hdisj measurable_sign2

/-- Every closed neighbourhood has at most three members, so `D_n = 2` for this design. -/
theorem pathDep_nbhd_card (n : ℕ) (o : Fin (n + 3)) : ((pathDep n).nbhd o).card ≤ 3 := by
  classical
  have hsub : (pathDep n).nbhd o ⊆
      ((Finset.univ.filter (fun o' : Fin (n + 3) => o'.val = o.val))
        ∪ (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val + 1 = o.val)))
      ∪ (Finset.univ.filter (fun o' : Fin (n + 3) => o.val + 1 = o'.val)) := by
    intro j hj
    have hG : pathG (n + 3) o j := (pathDep n).mem_nbhd_iff.mp hj
    rcases hG with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [h]))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [h]))
    · exact Finset.mem_union_right _ (by simp [h])
  have c1 : (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val = o.val)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter] at ha hb
    exact Fin.ext (ha.2.trans hb.2.symm)
  have c2 : (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val + 1 = o.val)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter] at ha hb
    exact Fin.ext (by omega)
  have c3 : (Finset.univ.filter (fun o' : Fin (n + 3) => o.val + 1 = o'.val)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter] at ha hb
    exact Fin.ext (by omega)
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have := (Finset.card_union_le
    (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val = o.val))
    (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val + 1 = o.val)))
  omega

/-- In the example `δ_n = 8/(n+3)` and `(n/D_n)^{1/3}δ_n ≤ 8(n+3)^{-1/2} → 0`. -/
theorem tendsto_steinRate_witness :
    Tendsto (fun n : ℕ => steinRate (n + 3) 2 ((n : ℝ) + 3)) atTop (𝓝 0) := by
  have hbd : ∀ n : ℕ, steinRate (n + 3) 2 ((n : ℝ) + 3) ≤ 8 / Real.sqrt ((n : ℝ) + 3) := by
    intro n
    have hxpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    have hspos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 3) := Real.sqrt_pos.mpr hxpos
    have hacc : accumRate (n + 3) 2 ((n : ℝ) + 3) = 8 / ((n : ℝ) + 3) := by
      unfold accumRate
      have hc : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
      rw [hc]
      have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [h2]
      field_simp
      ring
    have hone : (1 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by
      push_cast
      rw [le_div_iff₀ (by norm_num)]
      linarith
    have hrp : (((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
        ≤ (((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
    have hsq : (((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)
        = Real.sqrt (((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) := (Real.sqrt_eq_rpow _).symm
    have hle : Real.sqrt (((n + 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ≤ Real.sqrt ((n : ℝ) + 3) := by
      refine Real.sqrt_le_sqrt ?_
      push_cast
      linarith
    have hfin : Real.sqrt ((n : ℝ) + 3) * (8 / ((n : ℝ) + 3)) = 8 / Real.sqrt ((n : ℝ) + 3) := by
      rw [eq_div_iff (ne_of_gt hspos)]
      have hxs : Real.sqrt ((n : ℝ) + 3) * Real.sqrt ((n : ℝ) + 3) = (n : ℝ) + 3 :=
        Real.mul_self_sqrt (by positivity)
      field_simp
      nlinarith [hxs]
    unfold steinRate
    rw [hacc, ← hfin]
    refine mul_le_mul_of_nonneg_right ((hrp.trans (le_of_eq hsq)).trans hle) (by positivity)
  refine squeeze_zero (fun n => steinRate_nonneg _ _ _) hbd ?_
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 3)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  simpa [div_eq_mul_inv] using (hsqrt.inv_tendsto_atTop.const_mul (8 : ℝ))

/-- The hypotheses of `cltcluster_a_general_betaJM` hold with `n+3` observations, one regressor
`x̃_o = 1`, `𝓡_n = I_1`, `Ω_n = X̃'X̃ = n+3`, one fair sign per observation and the `J = 2`
sharing relation `|o − o'| ≤ 1`. The total variance is `1` at every `n`,
`φ_n = (n+3)^{-1/2} → 0` and `D_n = 2`. -/
theorem cltcluster_a_general_betaJM_witness (s : ℝ) :
    Tendsto (fun n => ((coins (n + 3)).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt (n + 2))
              (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
                  ((redXt (n + 2))ᵀ *ᵥ (fun o => sign2 o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine cltcluster_a_general_betaJM (O := fun n => Fin (n + 3))
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
  · simpa using tendsto_steinRate_witness
  · simp [dotProduct]

end GeneralWitness

section PartBElementary

/-- `2|xy| ≤ x² + y²`. -/
theorem two_mul_abs_mul_le_sq_add_sq (x y : ℝ) : 2 * |x * y| ≤ x ^ 2 + y ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]

/-- `x²y² ≤ (x⁴ + y⁴)/2`. -/
theorem sq_mul_sq_le (x y : ℝ) : x ^ 2 * y ^ 2 ≤ (x ^ 4 + y ^ 4) / 2 := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]

/-- The three-factor Young inequality at the scale `ψ`: `4ψ|xyz| ≤ x⁴+y⁴+z⁴+ψ⁴`. -/
theorem four_mul_abs_mul_mul_le (x y z ψ : ℝ) (hψ : 0 ≤ ψ) :
    4 * ψ * |x * y * z| ≤ x ^ 4 + y ^ 4 + z ^ 4 + ψ ^ 4 := by
  have h1 : 2 * |x * y| ≤ x ^ 2 + y ^ 2 := two_mul_abs_mul_le_sq_add_sq x y
  have h2 : 2 * (ψ * |z|) ≤ z ^ 2 + ψ ^ 2 := by
    nlinarith [sq_nonneg (ψ - |z|), sq_abs z, abs_nonneg z]
  have h3 : (2 * |x * y|) * (2 * (ψ * |z|)) ≤ (x ^ 2 + y ^ 2) * (z ^ 2 + ψ ^ 2) := by
    refine mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : (x ^ 2 + y ^ 2) * (z ^ 2 + ψ ^ 2) ≤ x ^ 4 + y ^ 4 + z ^ 4 + ψ ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - z ^ 2), sq_nonneg (x ^ 2 - ψ ^ 2),
      sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (y ^ 2 - ψ ^ 2)]
  have h5 : 4 * ψ * |x * y * z| = (2 * |x * y|) * (2 * (ψ * |z|)) := by
    rw [abs_mul]; ring
  linarith [h3, h4, h5.le, h5.ge]

/-- `|x| ≤ 1 + x⁴` and `x² ≤ 1 + x⁴`. -/
theorem abs_le_one_add_pow_four (x : ℝ) : |x| ≤ 1 + x ^ 4 := by
  rcases le_or_gt |x| 1 with h | h
  · nlinarith [sq_nonneg (x ^ 2)]
  · have h1 : 1 ≤ |x| := h.le
    have : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    nlinarith [pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 4)]

theorem sq_le_one_add_pow_four (x : ℝ) : x ^ 2 ≤ 1 + x ^ 4 := by
  rcases le_or_gt (x ^ 2) 1 with h | h
  · nlinarith [sq_nonneg (x ^ 2)]
  · nlinarith [sq_nonneg (x ^ 2 - 1)]

end PartBElementary

section PartBIntegrability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded measurable function is integrable under a probability measure. -/
theorem integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact h ω))

/-- A bounded measurable function is in `L²` under a probability measure. -/
theorem memLp_two_of_abs_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ ω, |f ω| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact h ω))

/-- A measurable variable with an integrable fourth power is integrable. -/
theorem integrable_of_integrable_pow_four {f : Ω → ℝ} (hf : Measurable f)
    (h4 : Integrable (fun ω => (f ω) ^ 4) μ) : Integrable f μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h4) hf.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_le_one_add_pow_four (f ω)

/-- A measurable variable with an integrable fourth power is square integrable. -/
theorem integrable_sq_of_integrable_pow_four {f : Ω → ℝ} (hf : Measurable f)
    (h4 : Integrable (fun ω => (f ω) ^ 4) μ) : Integrable (fun ω => (f ω) ^ 2) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h4)
    ((hf.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_one_add_pow_four (f ω)

/-- A measurable variable with an integrable fourth power is in `L²`. -/
theorem memLp_two_of_integrable_pow_four {f : Ω → ℝ} (hf : Measurable f)
    (h4 : Integrable (fun ω => (f ω) ^ 4) μ) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
  exact integrable_sq_of_integrable_pow_four hf h4

/-- `|Cov(f,g)| ≤ 2c` when `∫f², ∫g² ≤ c`. -/
theorem abs_covariance_le_two_mul_of_sq {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {c : ℝ} (hfc : ∫ ω, (f ω) ^ 2 ∂μ ≤ c) (hgc : ∫ ω, (g ω) ^ 2 ∂μ ≤ c) :
    |covariance f g μ| ≤ 2 * c := by
  have hfsq : Integrable (fun ω => (f ω) ^ 2) μ := hf.integrable_sq
  have hgsq : Integrable (fun ω => (g ω) ^ 2) μ := hg.integrable_sq
  have hprodint : Integrable (fun ω => f ω * g ω) μ := hf.integrable_mul hg
  -- `|E[fg]| ≤ c`, by the pointwise `2|fg| ≤ f² + g²`
  have hprod : |∫ ω, f ω * g ω ∂μ| ≤ c := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |f ω * g ω| ∂μ ≤ ∫ ω, ((f ω) ^ 2 + (g ω) ^ 2) / 2 ∂μ := by
          refine integral_mono hprodint.abs ((hfsq.add hgsq).div_const 2) (fun ω => ?_)
          have := two_mul_abs_mul_le_sq_add_sq (f ω) (g ω)
          linarith
      _ = (∫ ω, (f ω) ^ 2 ∂μ + ∫ ω, (g ω) ^ 2 ∂μ) / 2 := by
          rw [integral_div, integral_add hfsq hgsq]
      _ ≤ c := by linarith
  -- `(E[f])² ≤ E[f²]`, from `0 ≤ Var f`
  have hmeansq : ∀ {h : Ω → ℝ}, MemLp h 2 μ → (∫ ω, h ω ∂μ) ^ 2 ≤ ∫ ω, (h ω) ^ 2 ∂μ := by
    intro h hh
    have hv := variance_nonneg h μ
    rw [variance_eq_sub hh] at hv
    simpa using hv
  have hf2 : (∫ ω, f ω ∂μ) ^ 2 ≤ c := le_trans (hmeansq hf) hfc
  have hg2 : (∫ ω, g ω ∂μ) ^ 2 ≤ c := le_trans (hmeansq hg) hgc
  have hmean : |(∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)| ≤ c := by
    have := two_mul_abs_mul_le_sq_add_sq (∫ ω, f ω ∂μ) (∫ ω, g ω ∂μ)
    linarith
  rw [covariance_eq_sub hf hg]
  calc |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)|
      ≤ |∫ ω, f ω * g ω ∂μ| + |(∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)| := abs_sub _ _
    _ ≤ c + c := add_le_add hprod hmean
    _ = 2 * c := by ring

end PartBIntegrability

section PartBErrors

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : O → Ω → ℝ}

omit [Fintype O] [MeasurableSpace Ω] in
/-- The pointwise bound `(X_{p.1}X_{p.2})² ≤ (X_{p.1}⁴ + X_{p.2}⁴)/2`, extended by `0` off the
sharing relation. -/
theorem sq_pairProd_le (X : O → Ω → ℝ) (N : O → Finset O) (p : O × O) (ω : Ω) :
    (pairProd X N p ω) ^ 2 ≤ ((X p.1 ω) ^ 4 + (X p.2 ω) ^ 4) / 2 := by
  have h1 : (0 : ℝ) ≤ (X p.1 ω) ^ 4 := by positivity
  have h2 : (0 : ℝ) ≤ (X p.2 ω) ^ 4 := by positivity
  rw [pairProd]
  split_ifs with h
  · rw [mul_pow]
    exact sq_mul_sq_le (X p.1 ω) (X p.2 ω)
  · rw [show ((0 : ℝ)) ^ 2 = 0 from by norm_num]
    linarith

/-- The first Stein error term from fourth moments, `Var(∑_oX_oT_o) ≤ 8nm³ψ⁴` whenever
`∫X_o⁴ ≤ ψ⁴`. No uniform bound on the array is assumed. -/
theorem firstError_le_moment (D : DepGraph X μ) {ψ : ℝ}
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    {m : ℕ} (hdeg : ∀ o, (D.nbhd o).card ≤ m) :
    variance (fun ω => ∑ o, X o ω * nbhdSum X D.nbhd o ω) μ
      ≤ 8 * (Fintype.card O : ℝ) * (m : ℝ) ^ 3 * ψ ^ 4 := by
  classical
  set W : O × O → Ω → ℝ := pairProd X D.nbhd with hWdef
  have hWapp : ∀ (p : O × O) (ω : Ω),
      W p ω = if p.2 ∈ D.nbhd p.1 then X p.1 ω * X p.2 ω else 0 := fun _ _ => rfl
  have hWmeas : ∀ p, Measurable (W p) := by
    intro p
    have hre : W p = fun ω => if p.2 ∈ D.nbhd p.1 then X p.1 ω * X p.2 ω else 0 := rfl
    rw [hre]
    split_ifs with h
    · exact (D.meas p.1).mul (D.meas p.2)
    · exact measurable_const
  have hmaj : ∀ p : O × O,
      Integrable (fun ω => ((X p.1 ω) ^ 4 + (X p.2 ω) ^ 4) / 2) μ :=
    fun p => ((hint4 p.1).add (hint4 p.2)).div_const 2
  have hWsqint : ∀ p : O × O, Integrable (fun ω => (W p ω) ^ 2) μ := by
    intro p
    refine Integrable.mono' (hmaj p) ((hWmeas p).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_pairProd_le X D.nbhd p ω
  have hWsq : ∀ p : O × O, ∫ ω, (W p ω) ^ 2 ∂μ ≤ ψ ^ 4 := by
    intro p
    calc ∫ ω, (W p ω) ^ 2 ∂μ ≤ ∫ ω, ((X p.1 ω) ^ 4 + (X p.2 ω) ^ 4) / 2 ∂μ :=
          integral_mono (hWsqint p) (hmaj p) (fun ω => sq_pairProd_le X D.nbhd p ω)
      _ = (∫ ω, (X p.1 ω) ^ 4 ∂μ + ∫ ω, (X p.2 ω) ^ 4 ∂μ) / 2 := by
          rw [integral_div, integral_add (hint4 p.1) (hint4 p.2)]
      _ ≤ ψ ^ 4 := by
          have h1 := hfour p.1
          have h2 := hfour p.2
          linarith
  have hWmem : ∀ p, MemLp (W p) 2 μ := fun p =>
    (memLp_two_iff_integrable_sq (hWmeas p).aestronglyMeasurable).2 (hWsqint p)
  have hfun : (fun ω => ∑ o, X o ω * nbhdSum X D.nbhd o ω) = fun ω => ∑ p : O × O, W p ω := by
    funext ω; rw [hWdef, sum_pairProd]
  rw [hfun, variance_fun_sum hWmem]
  have hWzero : ∀ p : O × O, p.2 ∉ D.nbhd p.1 → W p = 0 := by
    intro p hp
    funext ω
    rw [hWapp]
    simp [hp]
  have hsep_zero : ∀ p q : O × O, p.2 ∈ D.nbhd p.1 → q.2 ∈ D.nbhd q.1 →
      (∀ a ∈ ({p.1, p.2} : Finset O), ∀ b ∈ ({q.1, q.2} : Finset O), ¬ D.G a b) →
      covariance (W p) (W q) μ = 0 := by
    intro p q hp hq hs
    have h1 : p.1 ∈ ({p.1, p.2} : Finset O) := Finset.mem_insert_self _ _
    have h2 : p.2 ∈ ({p.1, p.2} : Finset O) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have k1 : q.1 ∈ ({q.1, q.2} : Finset O) := Finset.mem_insert_self _ _
    have k2 : q.2 ∈ ({q.1, q.2} : Finset O) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hind := D.indep ({p.1, p.2} : Finset O) ({q.1, q.2} : Finset O) hs
    have hmp : Measurable
        (fun t : (↥({p.1, p.2} : Finset O) → ℝ) => t ⟨p.1, h1⟩ * t ⟨p.2, h2⟩) :=
      (measurable_pi_apply _).mul (measurable_pi_apply _)
    have hmq : Measurable
        (fun t : (↥({q.1, q.2} : Finset O) → ℝ) => t ⟨q.1, k1⟩ * t ⟨q.2, k2⟩) :=
      (measurable_pi_apply _).mul (measurable_pi_apply _)
    have hcomp := hind.comp hmp hmq
    have ep : ((fun t : (↥({p.1, p.2} : Finset O) → ℝ) => t ⟨p.1, h1⟩ * t ⟨p.2, h2⟩)
        ∘ (fun ω => fun k : ({p.1, p.2} : Finset O) => X k ω)) = W p := by
      funext ω; rw [hWapp]; simp [hp]
    have eq' : ((fun t : (↥({q.1, q.2} : Finset O) → ℝ) => t ⟨q.1, k1⟩ * t ⟨q.2, k2⟩)
        ∘ (fun ω => fun k : ({q.1, q.2} : Finset O) => X k ω)) = W q := by
      funext ω; rw [hWapp]; simp [hq]
    rw [ep, eq'] at hcomp
    exact hcomp.covariance_eq_zero (hWmem p) (hWmem q)
  set S : O × O → Finset O := fun p => D.nbhd p.1 ∪ D.nbhd p.2 with hSdef
  set T : O × O → Finset (O × O) := fun p =>
    (S p).biUnion (fun a => {a} ×ˢ D.nbhd a) ∪ (S p).biUnion (fun a => D.nbhd a ×ˢ {a})
    with hTdef
  have hout : ∀ p q : O × O, p.2 ∈ D.nbhd p.1 → q ∉ T p → covariance (W p) (W q) μ = 0 := by
    intro p q hp hqT
    by_cases hq : q.2 ∈ D.nbhd q.1
    · refine hsep_zero p q hp hq ?_
      intro a ha b hb hab
      exfalso
      apply hqT
      have hbS : b ∈ S p := by
        rcases Finset.mem_insert.mp ha with h | h
        · subst h; exact Finset.mem_union_left _ (D.mem_nbhd_iff.mpr hab)
        · rw [Finset.mem_singleton] at h; subst h
          exact Finset.mem_union_right _ (D.mem_nbhd_iff.mpr hab)
      rcases Finset.mem_insert.mp hb with h | h
      · rw [hTdef]
        refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q.1, ?_, ?_⟩)
        · rw [← h]; exact hbS
        · rw [Finset.mem_product]
          exact ⟨Finset.mem_singleton_self _, hq⟩
      · rw [Finset.mem_singleton] at h
        have hq1 : q.1 ∈ D.nbhd q.2 :=
          D.mem_nbhd_iff.mpr (D.symm _ _ (D.mem_nbhd_iff.mp hq))
        rw [hTdef]
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q.2, ?_, ?_⟩)
        · rw [← h]; exact hbS
        · rw [Finset.mem_product]
          exact ⟨hq1, Finset.mem_singleton_self _⟩
    · rw [hWzero q hq]
      exact covariance_zero_right
  have hcardS : ∀ p, (S p).card ≤ 2 * m := by
    intro p
    refine (Finset.card_union_le _ _).trans ?_
    have := hdeg p.1
    have := hdeg p.2
    omega
  have hcardT : ∀ p, (T p).card ≤ 4 * m ^ 2 := by
    intro p
    have hA : ((S p).biUnion (fun a => ({a} : Finset O) ×ˢ D.nbhd a)).card ≤ 2 * m * m := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ a ∈ S p, (({a} : Finset O) ×ˢ D.nbhd a).card
          ≤ ∑ _a ∈ S p, m := by
            refine Finset.sum_le_sum (fun a _ => ?_)
            rw [Finset.card_product, Finset.card_singleton, one_mul]
            exact hdeg a
        _ = (S p).card * m := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (2 * m) * m := Nat.mul_le_mul_right m (hcardS p)
    have hB : ((S p).biUnion (fun a => D.nbhd a ×ˢ ({a} : Finset O))).card ≤ 2 * m * m := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ a ∈ S p, (D.nbhd a ×ˢ ({a} : Finset O)).card
          ≤ ∑ _a ∈ S p, m := by
            refine Finset.sum_le_sum (fun a _ => ?_)
            rw [Finset.card_product, Finset.card_singleton, mul_one]
            exact hdeg a
        _ = (S p).card * m := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (2 * m) * m := Nat.mul_le_mul_right m (hcardS p)
    have := (Finset.card_union_le ((S p).biUnion (fun a => ({a} : Finset O) ×ˢ D.nbhd a))
      ((S p).biUnion (fun a => D.nbhd a ×ˢ ({a} : Finset O))))
    rw [hTdef]
    nlinarith [this, hA, hB]
  have hinner : ∀ p : O × O, p.2 ∈ D.nbhd p.1 →
      ∑ q : O × O, covariance (W p) (W q) μ ≤ 8 * (m : ℝ) ^ 2 * ψ ^ 4 := by
    intro p hp
    have hrestrict : ∑ q : O × O, covariance (W p) (W q) μ
        = ∑ q ∈ T p, covariance (W p) (W q) μ := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => hout p q hp hq)
    rw [hrestrict]
    have hTcard : ((T p).card : ℝ) ≤ 4 * (m : ℝ) ^ 2 := by
      have := hcardT p
      exact_mod_cast this
    have hψ4 : (0 : ℝ) ≤ ψ ^ 4 := by positivity
    calc ∑ q ∈ T p, covariance (W p) (W q) μ
        ≤ ∑ q ∈ T p, |covariance (W p) (W q) μ| :=
          Finset.sum_le_sum (fun q _ => le_abs_self _)
      _ ≤ ∑ _q ∈ T p, 2 * ψ ^ 4 :=
          Finset.sum_le_sum (fun q _ => abs_covariance_le_two_mul_of_sq (hWmem p) (hWmem q)
            (hWsq p) (hWsq q))
      _ = ((T p).card : ℝ) * (2 * ψ ^ 4) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * (m : ℝ) ^ 2) * (2 * ψ ^ 4) :=
          mul_le_mul_of_nonneg_right hTcard (by positivity)
      _ = 8 * (m : ℝ) ^ 2 * ψ ^ 4 := by ring
  have hinner0 : ∀ p : O × O, p.2 ∉ D.nbhd p.1 →
      ∑ q : O × O, covariance (W p) (W q) μ = 0 := by
    intro p hp
    rw [hWzero p hp]
    simp
  have hnn : (0 : ℝ) ≤ 8 * (m : ℝ) ^ 2 * ψ ^ 4 := by positivity
  calc ∑ p : O × O, ∑ q : O × O, covariance (W p) (W q) μ
      = ∑ o : O, ∑ k : O, ∑ q : O × O, covariance (W (o, k)) (W q) μ := by
        rw [Fintype.sum_prod_type]
    _ = ∑ o : O, ∑ k ∈ D.nbhd o, ∑ q : O × O, covariance (W (o, k)) (W q) μ := by
        refine Finset.sum_congr rfl (fun o _ => ?_)
        symm
        refine Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => hinner0 (o, k) hk)
    _ ≤ ∑ o : O, ∑ _k ∈ D.nbhd o, 8 * (m : ℝ) ^ 2 * ψ ^ 4 :=
        Finset.sum_le_sum (fun o _ => Finset.sum_le_sum (fun k hk => hinner (o, k) hk))
    _ = ∑ o : O, ((D.nbhd o).card : ℝ) * (8 * (m : ℝ) ^ 2 * ψ ^ 4) := by
        refine Finset.sum_congr rfl (fun o _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _o : O, (m : ℝ) * (8 * (m : ℝ) ^ 2 * ψ ^ 4) := by
        refine Finset.sum_le_sum (fun o _ => ?_)
        refine mul_le_mul_of_nonneg_right ?_ hnn
        exact_mod_cast hdeg o
    _ = (Fintype.card O : ℝ) * ((m : ℝ) * (8 * (m : ℝ) ^ 2 * ψ ^ 4)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 8 * (Fintype.card O : ℝ) * (m : ℝ) ^ 3 * ψ ^ 4 := by ring

/-- The second Stein error term from fourth moments, `∑_oE[|X_o|T_o²] ≤ nm²ψ³` whenever
`∫X_o⁴ ≤ ψ⁴`. Each triple product `|X_oX_kX_l|` is bounded by `(X_o⁴+X_k⁴+X_l⁴+ψ⁴)/(4ψ)`. -/
theorem secondError_le_moment (D : DepGraph X μ) {ψ : ℝ} (hψ : 0 < ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    {m : ℕ} (hdeg : ∀ o, (D.nbhd o).card ≤ m) :
    ∑ o, ∫ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ∂μ
      ≤ (Fintype.card O : ℝ) * (m : ℝ) ^ 2 * ψ ^ 3 := by
  classical
  have hψ4 : (0 : ℝ) < 4 * ψ := by linarith
  have key : ∀ o : O, ∫ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ∂μ ≤ (m : ℝ) ^ 2 * ψ ^ 3 := by
    intro o
    set N : Finset O := D.nbhd o with hN
    set g : Ω → ℝ := fun ω => ∑ k ∈ N, ∑ l ∈ N,
      (((X o ω) ^ 4 + (X k ω) ^ 4 + (X l ω) ^ 4 + ψ ^ 4) / (4 * ψ)) with hg
    have hA : ∀ k : O, Integrable (fun ω => (X o ω) ^ 4 + (X k ω) ^ 4) μ :=
      fun k => (hint4 o).add (hint4 k)
    have hB : ∀ k l : O, Integrable
        (fun ω => (X o ω) ^ 4 + (X k ω) ^ 4 + (X l ω) ^ 4) μ :=
      fun k l => (hA k).add (hint4 l)
    have hC : ∀ k l : O, Integrable
        (fun ω => (X o ω) ^ 4 + (X k ω) ^ 4 + (X l ω) ^ 4 + ψ ^ 4) μ :=
      fun k l => (hB k l).add (integrable_const _)
    have hterm : ∀ k l : O, Integrable
        (fun ω => ((X o ω) ^ 4 + (X k ω) ^ 4 + (X l ω) ^ 4 + ψ ^ 4) / (4 * ψ)) μ :=
      fun k l => (hC k l).div_const _
    have hI : ∀ k l : O, ∫ ω, ((X o ω) ^ 4 + (X k ω) ^ 4 + (X l ω) ^ 4 + ψ ^ 4) ∂μ
        = (∫ ω, (X o ω) ^ 4 ∂μ) + (∫ ω, (X k ω) ^ 4 ∂μ) + (∫ ω, (X l ω) ^ 4 ∂μ) + ψ ^ 4 := by
      intro k l
      rw [integral_add (hB k l) (integrable_const _), integral_add (hA k) (hint4 l),
        integral_add (hint4 o) (hint4 k), integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hgint : Integrable g μ := by
      refine integrable_finsetSum _ (fun k _ => ?_)
      exact integrable_finsetSum _ (fun l _ => hterm k l)
    have hle : ∀ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ≤ g ω := by
      intro ω
      have hexp : |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2
          = ∑ k ∈ N, ∑ l ∈ N, |X o ω| * (X k ω * X l ω) := by
        simp only [nbhdSum, sq, ← hN]
        have hprod : (∑ x ∈ N, X x ω) * (∑ x ∈ N, X x ω)
            = ∑ k ∈ N, ∑ l ∈ N, X k ω * X l ω := by rw [Finset.sum_mul_sum]
        rw [hprod, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
      rw [hexp, hg]
      refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
      have h := four_mul_abs_mul_mul_le (X o ω) (X k ω) (X l ω) ψ hψ.le
      have h2 : |X o ω| * (X k ω * X l ω) ≤ |X o ω * X k ω * X l ω| := by
        rw [abs_mul, abs_mul, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← abs_mul]
        exact le_abs_self _
      rw [le_div_iff₀ hψ4]
      calc |X o ω| * (X k ω * X l ω) * (4 * ψ)
          = (4 * ψ) * (|X o ω| * (X k ω * X l ω)) := by ring
        _ ≤ (4 * ψ) * |X o ω * X k ω * X l ω| :=
            mul_le_mul_of_nonneg_left h2 hψ4.le
        _ ≤ (X o ω) ^ 4 + (X k ω) ^ 4 + (X l ω) ^ 4 + ψ ^ 4 := by
            rw [mul_assoc] at h; linarith [h]
    have hfmeas : Measurable (fun ω => |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2) :=
      (D.meas o).abs.mul ((D.measurable_nbhdSum o).pow_const 2)
    have hfint : Integrable (fun ω => |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2) μ := by
      refine Integrable.mono' hgint hfmeas.aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hle ω
    calc ∫ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ∂μ ≤ ∫ ω, g ω ∂μ :=
          integral_mono hfint hgint hle
      _ = ∑ k ∈ N, ∑ l ∈ N,
            ((∫ ω, (X o ω) ^ 4 ∂μ) + (∫ ω, (X k ω) ^ 4 ∂μ) + (∫ ω, (X l ω) ^ 4 ∂μ)
              + ψ ^ 4) / (4 * ψ) := by
          rw [hg, MeasureTheory.integral_finsetSum _
            (fun k _ => integrable_finsetSum _ (fun l _ => hterm k l))]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [MeasureTheory.integral_finsetSum _ (fun l _ => hterm k l)]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [integral_div, hI k l]
      _ ≤ ∑ _k ∈ N, ∑ _l ∈ N, ψ ^ 3 := by
          refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
          rw [div_le_iff₀ hψ4]
          have h1 := hfour o
          have h2 := hfour k
          have h3 := hfour l
          have : ψ ^ 3 * (4 * ψ) = 4 * ψ ^ 4 := by ring
          linarith
      _ = (N.card : ℝ) * ((N.card : ℝ) * ψ ^ 3) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      _ ≤ (m : ℝ) ^ 2 * ψ ^ 3 := by
          have hcard : (N.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdeg o
          have hc0 : (0 : ℝ) ≤ (N.card : ℝ) := by positivity
          have hψ3 : (0 : ℝ) ≤ ψ ^ 3 := by positivity
          have hsq : (N.card : ℝ) * (N.card : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
            mul_le_mul hcard hcard hc0 (le_trans hc0 hcard)
          calc (N.card : ℝ) * ((N.card : ℝ) * ψ ^ 3)
              = ((N.card : ℝ) * (N.card : ℝ)) * ψ ^ 3 := by ring
            _ ≤ ((m : ℝ) * (m : ℝ)) * ψ ^ 3 := mul_le_mul_of_nonneg_right hsq hψ3
            _ = (m : ℝ) ^ 2 * ψ ^ 3 := by ring
  calc ∑ o, ∫ ω, |X o ω| * (nbhdSum X D.nbhd o ω) ^ 2 ∂μ
      ≤ ∑ _o : O, (m : ℝ) ^ 2 * ψ ^ 3 := Finset.sum_le_sum (fun o _ => key o)
    _ = (Fintype.card O : ℝ) * (m : ℝ) ^ 2 * ψ ^ 3 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

end PartBErrors

section PartBTruncation

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : O → Ω → ℝ}

/-- A dependency graph for `X` is one for any family of fixed functions of the individual
`X_o`, with the same relation. -/
noncomputable def mapDepGraph (D : DepGraph X μ) (f : O → ℝ → ℝ)
    (hf : ∀ o, Measurable (f o)) : DepGraph (fun o ω => f o (X o ω)) μ where
  G := D.G
  decG := D.decG
  refl := D.refl
  symm := D.symm
  meas := fun o => (hf o).comp (D.meas o)
  indep := by
    intro A Bs hsep
    have h0 := D.indep A Bs hsep
    have hmA : Measurable (fun t : (↥A → ℝ) => fun k : ↥A => f (k : O) (t k)) :=
      Measurable.of_eval fun k => (hf k).comp (measurable_pi_apply k)
    have hmB : Measurable (fun t : (↥Bs → ℝ) => fun k : ↥Bs => f (k : O) (t k)) :=
      Measurable.of_eval fun k => (hf k).comp (measurable_pi_apply k)
    exact h0.comp hmA hmB

@[simp] theorem nbhd_mapDepGraph (D : DepGraph X μ) (f : O → ℝ → ℝ)
    (hf : ∀ o, Measurable (f o)) (o : O) : (mapDepGraph D f hf).nbhd o = D.nbhd o := rfl

/-- The truncation-and-centring map at level `τ` with centre `c`: `x ↦ x·1{|x| ≤ τ} − c`. -/
noncomputable def truncMap (τ c : ℝ) : ℝ → ℝ := fun x => (if |x| ≤ τ then x else 0) - c

theorem measurable_truncMap (τ c : ℝ) : Measurable (truncMap τ c) := by
  unfold truncMap
  refine Measurable.sub ?_ measurable_const
  refine Measurable.ite ?_ measurable_id measurable_const
  exact measurableSet_le measurable_id.abs measurable_const

omit [Fintype O] [DecidableEq O] in
/-- `|truncMap τ c x| ≤ τ + |c|`. -/
theorem abs_truncMap_add_le (τ c x : ℝ) (hτ : 0 ≤ τ) :
    |truncMap τ c x| ≤ τ + |c| := by
  have h1 : |if |x| ≤ τ then x else 0| ≤ τ := by
    split_ifs with h
    · exact h
    · rw [abs_zero]; exact hτ
  have h2 : |truncMap τ c x| ≤ |if |x| ≤ τ then x else 0| + |c| := abs_sub _ _
  linarith

omit [Fintype O] [DecidableEq O] in
theorem abs_truncMap_le_abs_add (τ c x : ℝ) : |truncMap τ c x| ≤ |x| + |c| := by
  have h1 : |if |x| ≤ τ then x else 0| ≤ |x| := by
    split_ifs with h
    · exact le_rfl
    · rw [abs_zero]; exact abs_nonneg x
  have h2 : |truncMap τ c x| ≤ |if |x| ≤ τ then x else 0| + |c| := abs_sub _ _
  linarith

omit [Fintype O] [DecidableEq O] in
/-- `|x − x·1{|x| ≤ τ}| ≤ x⁴/τ³`. -/
theorem abs_sub_trunc_le (τ x : ℝ) (hτ : 0 < τ) :
    |x - (if |x| ≤ τ then x else 0)| ≤ x ^ 4 / τ ^ 3 := by
  split_ifs with h
  · rw [sub_self, abs_zero]; positivity
  · rw [sub_zero]
    rw [le_div_iff₀ (by positivity)]
    have hx : τ < |x| := lt_of_not_ge h
    have h4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    have h3 : τ ^ 3 ≤ |x| ^ 3 := pow_le_pow_left₀ hτ.le hx.le 3
    calc |x| * τ ^ 3 ≤ |x| * |x| ^ 3 :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg x)
      _ = x ^ 4 := by rw [← h4]; ring

omit [Fintype O] [DecidableEq O] in
/-- `(x − x·1{|x| ≤ τ})² ≤ x⁴/τ²`. -/
theorem sq_sub_trunc_le (τ x : ℝ) (hτ : 0 < τ) :
    (x - (if |x| ≤ τ then x else 0)) ^ 2 ≤ x ^ 4 / τ ^ 2 := by
  split_ifs with h
  · rw [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]; positivity
  · rw [sub_zero]
    rw [le_div_iff₀ (by positivity)]
    have hx : τ < |x| := lt_of_not_ge h
    have h4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    have h2 : τ ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ hτ.le hx.le 2
    have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    calc x ^ 2 * τ ^ 2 = |x| ^ 2 * τ ^ 2 := by rw [hsq]
      _ ≤ |x| ^ 2 * |x| ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = x ^ 4 := by rw [← h4]; ring

/-- `(a+b)⁴ ≤ 8(a⁴+b⁴)`. -/
theorem add_pow_four_le (a b : ℝ) :
    (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2),
    sq_nonneg (a * a - a * b), sq_nonneg (b * b - a * b),
    sq_nonneg (a * b), sq_nonneg (a ^ 2 + b ^ 2)]

/-- `m_o := E[X_o·1{|X_o| ≤ τ}]`, the mean of the truncation. -/
noncomputable def truncMean (μ : Measure Ω) (X : O → Ω → ℝ) (τ : ℝ) (o : O) : ℝ :=
  ∫ ω, (if |X o ω| ≤ τ then X o ω else 0) ∂μ

/-- `Y_o := X_o·1{|X_o| ≤ τ} − m_o`, the centred truncation. -/
noncomputable def truncCent (μ : Measure Ω) (X : O → Ω → ℝ) (τ : ℝ) : O → Ω → ℝ :=
  fun o ω => truncMap τ (truncMean μ X τ o) (X o ω)

/-- `Z_o := X_o − Y_o`, the tail. -/
noncomputable def truncTail (μ : Measure Ω) (X : O → Ω → ℝ) (τ : ℝ) : O → Ω → ℝ :=
  fun o ω => X o ω - truncCent μ X τ o ω

omit [Fintype O] [DecidableEq O] [IsProbabilityMeasure μ] in
theorem truncCent_apply (τ : ℝ) (o : O) (ω : Ω) :
    truncCent μ X τ o ω = (if |X o ω| ≤ τ then X o ω else 0) - truncMean μ X τ o := rfl

/-- The sharing graph is a dependency graph for the truncated array, with the same relation. -/
noncomputable def truncDepGraph (D : DepGraph X μ) (τ : ℝ) : DepGraph (truncCent μ X τ) μ :=
  mapDepGraph D (fun o => truncMap τ (truncMean μ X τ o)) (fun o => measurable_truncMap _ _)

@[simp] theorem nbhd_truncDepGraph (D : DepGraph X μ) (τ : ℝ) (o : O) :
    (truncDepGraph D τ).nbhd o = D.nbhd o := rfl

section TruncFacts

variable {τ ψ : ℝ}

theorem measurable_truncPart (D : DepGraph X μ) (τ : ℝ) (o : O) :
    Measurable (fun ω => if |X o ω| ≤ τ then X o ω else 0) := by
  refine Measurable.ite ?_ (D.meas o) measurable_const
  exact measurableSet_le (D.meas o).abs measurable_const

theorem integrable_truncPart (D : DepGraph X μ) (hτ : 0 ≤ τ) (o : O) :
    Integrable (fun ω => if |X o ω| ≤ τ then X o ω else 0) μ := by
  refine integrable_of_abs_le (measurable_truncPart D τ o) (C := τ) (fun ω => ?_)
  split_ifs with h
  · exact h
  · rw [abs_zero]; exact hτ

/-- `|m_o| ≤ ψ⁴/τ³`. -/
theorem abs_truncMean_le (D : DepGraph X μ) (hτ : 0 < τ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    |truncMean μ X τ o| ≤ ψ ^ 4 / τ ^ 3 := by
  have hXi : Integrable (X o) μ := integrable_of_integrable_pow_four (D.meas o) (hint4 o)
  have hTi := integrable_truncPart D hτ.le o
  have hkey : truncMean μ X τ o
      = - ∫ ω, (X o ω - (if |X o ω| ≤ τ then X o ω else 0)) ∂μ := by
    rw [integral_sub hXi hTi, hmean o, zero_sub, neg_neg]
    rfl
  rw [hkey, abs_neg]
  calc |∫ ω, (X o ω - (if |X o ω| ≤ τ then X o ω else 0)) ∂μ|
      ≤ ∫ ω, |X o ω - (if |X o ω| ≤ τ then X o ω else 0)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (X o ω) ^ 4 / τ ^ 3 ∂μ :=
        integral_mono (hXi.sub hTi).abs ((hint4 o).div_const _)
          (fun ω => abs_sub_trunc_le τ (X o ω) hτ)
    _ = (∫ ω, (X o ω) ^ 4 ∂μ) / τ ^ 3 := integral_div _ _
    _ ≤ ψ ^ 4 / τ ^ 3 := by
        exact div_le_div_of_nonneg_right (hfour o) (by positivity)

theorem abs_truncMean_le_psi (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    |truncMean μ X τ o| ≤ ψ := by
  refine (abs_truncMean_le D hτ hint4 hfour hmean o).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have h4 : ψ ^ 4 ≤ ψ * τ ^ 3 := by
    calc ψ ^ 4 = ψ * ψ ^ 3 := by ring
      _ ≤ ψ * τ ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hψ0 hψτ 3) hψ0
  exact h4

/-- `|Y_o| ≤ 2τ`. -/
theorem abs_truncCent_le (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) (ω : Ω) :
    |truncCent μ X τ o ω| ≤ 2 * τ := by
  have h := abs_truncMap_add_le τ (truncMean μ X τ o) (X o ω) hτ.le
  have hm := abs_truncMean_le_psi D hτ hψτ hψ0 hint4 hfour hmean o
  have : |truncCent μ X τ o ω| ≤ τ + |truncMean μ X τ o| := h
  linarith

theorem abs_truncCent_le_abs_add (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) (ω : Ω) :
    |truncCent μ X τ o ω| ≤ |X o ω| + ψ := by
  have h := abs_truncMap_le_abs_add τ (truncMean μ X τ o) (X o ω)
  have hm := abs_truncMean_le_psi D hτ hψτ hψ0 hint4 hfour hmean o
  have h2 : |truncCent μ X τ o ω| ≤ |X o ω| + |truncMean μ X τ o| := h
  linarith

/-- The centred truncation has mean zero. -/
theorem integral_truncCent_eq_zero (D : DepGraph X μ) (hτ : 0 < τ) (o : O) :
    ∫ ω, truncCent μ X τ o ω ∂μ = 0 := by
  have hTi := integrable_truncPart D hτ.le o
  simp only [truncCent_apply]
  rw [integral_sub hTi (integrable_const _), integral_const, probReal_univ, smul_eq_mul,
    one_mul]
  have h : ∫ ω, (if |X o ω| ≤ τ then X o ω else 0) ∂μ = truncMean μ X τ o := rfl
  rw [h, sub_self]

theorem integrable_truncCent_pow_four (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    Integrable (fun ω => (truncCent μ X τ o ω) ^ 4) μ := by
  refine integrable_of_abs_le (((truncDepGraph D τ).meas o).pow_const 4)
    (C := (2 * τ) ^ 4) (fun ω => ?_)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_truncCent_le D hτ hψτ hψ0 hint4 hfour hmean o ω) 4

/-- The fourth moment of the centred truncation: `∫Y_o⁴ ≤ (2ψ)⁴`. -/
theorem integral_truncCent_pow_four_le (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    ∫ ω, (truncCent μ X τ o ω) ^ 4 ∂μ ≤ (2 * ψ) ^ 4 := by
  have hmaj : Integrable (fun ω => 8 * ((X o ω) ^ 4 + ψ ^ 4)) μ :=
    ((hint4 o).add (integrable_const _)).const_mul 8
  have hle : ∀ ω, (truncCent μ X τ o ω) ^ 4 ≤ 8 * ((X o ω) ^ 4 + ψ ^ 4) := by
    intro ω
    have h1 : (truncCent μ X τ o ω) ^ 4 = |truncCent μ X τ o ω| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    have h2 : |truncCent μ X τ o ω| ^ 4 ≤ (|X o ω| + ψ) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _)
        (abs_truncCent_le_abs_add D hτ hψτ hψ0 hint4 hfour hmean o ω) 4
    have h3 : (|X o ω| + ψ) ^ 4 ≤ 8 * (|X o ω| ^ 4 + ψ ^ 4) := add_pow_four_le _ _
    have h4 : |X o ω| ^ 4 = (X o ω) ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h1, ← h4]
    linarith
  calc ∫ ω, (truncCent μ X τ o ω) ^ 4 ∂μ ≤ ∫ ω, 8 * ((X o ω) ^ 4 + ψ ^ 4) ∂μ :=
        integral_mono (integrable_truncCent_pow_four D hτ hψτ hψ0 hint4 hfour hmean o)
          hmaj hle
    _ = 8 * ((∫ ω, (X o ω) ^ 4 ∂μ) + ψ ^ 4) := by
        rw [integral_const_mul, integral_add (hint4 o) (integrable_const _), integral_const,
          probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (2 * ψ) ^ 4 := by
        have := hfour o
        nlinarith [this]

/-- Two non-adjacent coordinates of a dependency graph are independent. -/
theorem indepFun_of_not_G (D : DepGraph X μ) {o o' : O} (h : ¬ D.G o o') :
    IndepFun (X o) (X o') μ := by
  have hsep : ∀ a ∈ ({o} : Finset O), ∀ b ∈ ({o'} : Finset O), ¬ D.G a b := by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    subst ha; subst hb; exact h
  have hind := D.indep {o} {o'} hsep
  have hmp : Measurable (fun v : (↥({o} : Finset O) → ℝ) =>
      v ⟨o, Finset.mem_singleton_self o⟩) := measurable_pi_apply _
  have hmq : Measurable (fun v : (↥({o'} : Finset O) → ℝ) =>
      v ⟨o', Finset.mem_singleton_self o'⟩) := measurable_pi_apply _
  exact hind.comp hmp hmq

/-- The sharing graph is a dependency graph for the tail, with the same relation. -/
noncomputable def tailDepGraph (D : DepGraph X μ) (τ : ℝ) : DepGraph (truncTail μ X τ) μ :=
  mapDepGraph D (fun o x => x - truncMap τ (truncMean μ X τ o) x)
    (fun o => measurable_id.sub (measurable_truncMap _ _))

@[simp] theorem nbhd_tailDepGraph (D : DepGraph X μ) (τ : ℝ) (o : O) :
    (tailDepGraph D τ).nbhd o = D.nbhd o := rfl

section TailFacts

variable {τ ψ : ℝ}

theorem truncTail_apply (τ : ℝ) (o : O) (ω : Ω) :
    truncTail μ X τ o ω
      = (X o ω - (if |X o ω| ≤ τ then X o ω else 0)) + truncMean μ X τ o := by
  rw [truncTail, truncCent_apply]; ring

/-- The squared tail `Z_o²` is integrable. -/
theorem integrable_truncTail_sq (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    Integrable (fun ω => (truncTail μ X τ o ω) ^ 2) μ := by
  have hmajint : Integrable
      (fun ω => 2 * ((X o ω) ^ 4 / τ ^ 2) + 2 * (truncMean μ X τ o) ^ 2) μ :=
    (((hint4 o).div_const _).const_mul 2).add (integrable_const _)
  refine Integrable.mono' hmajint
    ((((tailDepGraph D τ).meas o).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), truncTail_apply]
  have h1 : (X o ω - (if |X o ω| ≤ τ then X o ω else 0)) ^ 2 ≤ (X o ω) ^ 4 / τ ^ 2 :=
    sq_sub_trunc_le τ (X o ω) hτ
  nlinarith [sq_nonneg ((X o ω - (if |X o ω| ≤ τ then X o ω else 0)) - truncMean μ X τ o),
    h1, sq_nonneg (truncMean μ X τ o)]

theorem integral_truncTail_sq_le (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    ∫ ω, (truncTail μ X τ o ω) ^ 2 ∂μ ≤ 4 * (ψ ^ 4 / τ ^ 2) := by
  have hm := abs_truncMean_le D hτ hint4 hfour hmean o
  have hm2 : (truncMean μ X τ o) ^ 2 ≤ ψ ^ 4 / τ ^ 2 := by
    have habs : (truncMean μ X τ o) ^ 2 = |truncMean μ X τ o| ^ 2 := (sq_abs _).symm
    have hsq : |truncMean μ X τ o| ^ 2 ≤ (ψ ^ 4 / τ ^ 3) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hm 2
    have hchain : (ψ ^ 4 / τ ^ 3) ^ 2 ≤ ψ ^ 4 / τ ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have hψ4 : ψ ^ 4 ≤ τ ^ 4 := pow_le_pow_left₀ hψ0 hψτ 4
      have h := mul_le_mul_of_nonneg_left hψ4 (by positivity : (0 : ℝ) ≤ ψ ^ 4 * τ ^ 2)
      nlinarith [h]
    rw [habs]; linarith
  have hmajint : Integrable
      (fun ω => 2 * ((X o ω) ^ 4 / τ ^ 2) + 2 * (truncMean μ X τ o) ^ 2) μ :=
    (((hint4 o).div_const _).const_mul 2).add (integrable_const _)
  calc ∫ ω, (truncTail μ X τ o ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * ((X o ω) ^ 4 / τ ^ 2) + 2 * (truncMean μ X τ o) ^ 2) ∂μ := by
        refine integral_mono
          (integrable_truncTail_sq D hτ hψτ hψ0 hint4 hfour hmean o) hmajint (fun ω => ?_)
        rw [truncTail_apply]
        have h1 : (X o ω - (if |X o ω| ≤ τ then X o ω else 0)) ^ 2 ≤ (X o ω) ^ 4 / τ ^ 2 :=
          sq_sub_trunc_le τ (X o ω) hτ
        nlinarith [sq_nonneg ((X o ω - (if |X o ω| ≤ τ then X o ω else 0))
          - truncMean μ X τ o), h1, sq_nonneg (truncMean μ X τ o)]
    _ = 2 * ((∫ ω, (X o ω) ^ 4 ∂μ) / τ ^ 2) + 2 * (truncMean μ X τ o) ^ 2 := by
        rw [integral_add (((hint4 o).div_const _).const_mul 2) (integrable_const _),
          integral_const_mul, integral_div, integral_const, probReal_univ, smul_eq_mul,
          one_mul]
    _ ≤ 4 * (ψ ^ 4 / τ ^ 2) := by
        have h1 : (∫ ω, (X o ω) ^ 4 ∂μ) / τ ^ 2 ≤ ψ ^ 4 / τ ^ 2 :=
          div_le_div_of_nonneg_right (hfour o) (by positivity)
        linarith

theorem memLp_two_truncTail (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    MemLp (truncTail μ X τ o) 2 μ :=
  (memLp_two_iff_integrable_sq ((tailDepGraph D τ).meas o).aestronglyMeasurable).2
    (integrable_truncTail_sq D hτ hψτ hψ0 hint4 hfour hmean o)

theorem integral_truncTail_eq_zero (D : DepGraph X μ) (hτ : 0 < τ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    ∫ ω, truncTail μ X τ o ω ∂μ = 0 := by
  have hXi : Integrable (X o) μ := integrable_of_integrable_pow_four (D.meas o) (hint4 o)
  have hTi := integrable_truncPart D hτ.le o
  have hYi : Integrable (truncCent μ X τ o) μ := by
    have hre : truncCent μ X τ o
        = fun ω => (if |X o ω| ≤ τ then X o ω else 0) - truncMean μ X τ o := rfl
    rw [hre]
    exact hTi.sub (integrable_const _)
  simp only [truncTail]
  rw [integral_sub hXi hYi, hmean o, integral_truncCent_eq_zero D hτ o, sub_zero]

/-- The tail variance: `Var(∑_oZ_o) ≤ 8nmψ⁴/τ²`. Off the sharing relation the covariances
vanish; on it there are at most `nm` ordered pairs, each with covariance at most `2·4ψ⁴/τ²`. -/
theorem integral_depSum_truncTail_sq_le (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ)
    (hψ0 : 0 ≤ ψ)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0)
    {m : ℕ} (hdeg : ∀ o, (D.nbhd o).card ≤ m) :
    ∫ ω, (depSum (truncTail μ X τ) ω) ^ 2 ∂μ
      ≤ 8 * (Fintype.card O : ℝ) * (m : ℝ) * (ψ ^ 4 / τ ^ 2) := by
  classical
  have hZmem : ∀ o, MemLp (truncTail μ X τ o) 2 μ :=
    fun o => memLp_two_truncTail D hτ hψτ hψ0 hint4 hfour hmean o
  have hZsq : ∀ o, ∫ ω, (truncTail μ X τ o ω) ^ 2 ∂μ ≤ 4 * (ψ ^ 4 / τ ^ 2) :=
    fun o => integral_truncTail_sq_le D hτ hψτ hψ0 hint4 hfour hmean o
  have hsum0 : ∫ ω, depSum (truncTail μ X τ) ω ∂μ = 0 := by
    have hre : (fun ω => depSum (truncTail μ X τ) ω)
        = fun ω => ∑ o, truncTail μ X τ o ω := rfl
    rw [hre, MeasureTheory.integral_finsetSum _
      (fun o _ => (hZmem o).integrable (by norm_num))]
    exact Finset.sum_eq_zero (fun o _ => integral_truncTail_eq_zero D hτ hint4 hmean o)
  have hmeasSum : Measurable (depSum (truncTail μ X τ)) :=
    Finset.measurable_sum _ (fun o _ => (tailDepGraph D τ).meas o)
  have hfun : (fun ω => ∑ o, truncTail μ X τ o ω) = depSum (truncTail μ X τ) := rfl
  have hrw : ∫ ω, (depSum (truncTail μ X τ) ω) ^ 2 ∂μ
      = variance (depSum (truncTail μ X τ)) μ :=
    (variance_of_integral_eq_zero hmeasSum.aemeasurable hsum0).symm
  rw [hrw, ← hfun, variance_fun_sum hZmem]
  have hcov : ∀ o o' : O, |covariance (truncTail μ X τ o) (truncTail μ X τ o') μ|
      ≤ 2 * (4 * (ψ ^ 4 / τ ^ 2)) :=
    fun o o' => abs_covariance_le_two_mul_of_sq (hZmem o) (hZmem o') (hZsq o) (hZsq o')
  have hzero : ∀ o o' : O, o' ∉ D.nbhd o →
      covariance (truncTail μ X τ o) (truncTail μ X τ o') μ = 0 := by
    intro o o' ho'
    have hG : ¬ (tailDepGraph D τ).G o o' := by
      intro hG
      exact ho' ((D.mem_nbhd_iff).mpr hG)
    exact (indepFun_of_not_G (tailDepGraph D τ) hG).covariance_eq_zero (hZmem o) (hZmem o')
  have hnn : (0 : ℝ) ≤ 8 * (ψ ^ 4 / τ ^ 2) := by positivity
  calc ∑ o, ∑ o', covariance (truncTail μ X τ o) (truncTail μ X τ o') μ
      = ∑ o, ∑ o' ∈ D.nbhd o, covariance (truncTail μ X τ o) (truncTail μ X τ o') μ := by
        refine Finset.sum_congr rfl (fun o _ => ?_)
        symm
        exact Finset.sum_subset (Finset.subset_univ _) (fun o' _ h => hzero o o' h)
    _ ≤ ∑ o, ∑ _o' ∈ D.nbhd o, 8 * (ψ ^ 4 / τ ^ 2) := by
        refine Finset.sum_le_sum (fun o _ => Finset.sum_le_sum (fun o' _ => ?_))
        refine le_trans (le_abs_self _) ?_
        have := hcov o o'
        linarith
    _ = ∑ o, ((D.nbhd o).card : ℝ) * (8 * (ψ ^ 4 / τ ^ 2)) := by
        refine Finset.sum_congr rfl (fun o _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _o : O, (m : ℝ) * (8 * (ψ ^ 4 / τ ^ 2)) := by
        refine Finset.sum_le_sum (fun o _ => ?_)
        refine mul_le_mul_of_nonneg_right ?_ hnn
        exact_mod_cast hdeg o
    _ = (Fintype.card O : ℝ) * ((m : ℝ) * (8 * (ψ ^ 4 / τ ^ 2))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 8 * (Fintype.card O : ℝ) * (m : ℝ) * (ψ ^ 4 / τ ^ 2) := by ring

end TailFacts

end TruncFacts

section TruncStd

variable {τ s ψ : ℝ}

/-- The centred truncation `Y_o` standardized by `σ`. -/
noncomputable def truncStd (μ : Measure Ω) (X : O → Ω → ℝ) (τ s : ℝ) : O → Ω → ℝ :=
  fun o ω => truncCent μ X τ o ω / s

/-- The sharing graph is a dependency graph for the standardized truncation. -/
noncomputable def truncStdDepGraph (D : DepGraph X μ) (τ s : ℝ) :
    DepGraph (truncStd μ X τ s) μ :=
  mapDepGraph D (fun o x => truncMap τ (truncMean μ X τ o) x / s)
    (fun o => (measurable_truncMap _ _).div_const s)

@[simp] theorem nbhd_truncStdDepGraph (D : DepGraph X μ) (τ s : ℝ) (o : O) :
    (truncStdDepGraph D τ s).nbhd o = D.nbhd o := rfl

theorem depSum_truncStd (X : O → Ω → ℝ) (τ s : ℝ) (ω : Ω) :
    depSum (truncStd μ X τ s) ω = depSum (truncCent μ X τ) ω / s := by
  simp only [depSum, truncStd]
  rw [Finset.sum_div]

theorem abs_truncStd_le (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ) (hψ0 : 0 ≤ ψ)
    (hs : 0 < s)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) (ω : Ω) :
    |truncStd μ X τ s o ω| ≤ 2 * τ / s := by
  rw [truncStd, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right
    (abs_truncCent_le D hτ hψτ hψ0 hint4 hfour hmean o ω) hs.le

theorem integral_truncStd_eq_zero (D : DepGraph X μ) (hτ : 0 < τ) (o : O) :
    ∫ ω, truncStd μ X τ s o ω ∂μ = 0 := by
  simp only [truncStd]
  rw [integral_div, integral_truncCent_eq_zero D hτ o, zero_div]

theorem integral_truncStd_pow_four_le (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ)
    (hψ0 : 0 ≤ ψ) (hs : 0 < s)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    ∫ ω, (truncStd μ X τ s o ω) ^ 4 ∂μ ≤ (2 * ψ / s) ^ 4 := by
  have hre : ∀ ω, (truncStd μ X τ s o ω) ^ 4 = (truncCent μ X τ o ω) ^ 4 / s ^ 4 := by
    intro ω; rw [truncStd, div_pow]
  simp only [hre]
  rw [integral_div, div_pow]
  exact div_le_div_of_nonneg_right
    (integral_truncCent_pow_four_le D hτ hψτ hψ0 hint4 hfour hmean o) (by positivity)

theorem integrable_truncStd_pow_four (D : DepGraph X μ) (hτ : 0 < τ) (hψτ : ψ ≤ τ)
    (hψ0 : 0 ≤ ψ) (hs : 0 < s)
    (hint4 : ∀ o, Integrable (fun ω => (X o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (X o ω) ^ 4 ∂μ ≤ ψ ^ 4)
    (hmean : ∀ o, ∫ ω, X o ω ∂μ = 0) (o : O) :
    Integrable (fun ω => (truncStd μ X τ s o ω) ^ 4) μ := by
  refine integrable_of_abs_le (((truncStdDepGraph D τ s).meas o).pow_const 4)
    (C := (2 * τ / s) ^ 4) (fun ω => ?_)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_truncStd_le D hτ hψτ hψ0 hs hint4 hfour hmean o ω) 4

end TruncStd

end PartBTruncation

section PartBSigma

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `∫|W| ≤ (V/c + c)/2` for every `c > 0`, where `V = ∫W²`, from the pointwise
`2c|W| ≤ W² + c²`. -/
theorem integral_abs_le_of_sq {W : Ω → ℝ} (hW : MemLp W 2 μ) {c : ℝ} (hc : 0 < c) :
    ∫ ω, |W ω| ∂μ ≤ ((∫ ω, (W ω) ^ 2 ∂μ) / c + c) / 2 := by
  have hsq : Integrable (fun ω => (W ω) ^ 2) μ := hW.integrable_sq
  have hle : ∀ ω, |W ω| ≤ ((W ω) ^ 2 / c + c) / 2 := by
    intro ω
    have hrhs : ((W ω) ^ 2 / c + c) / 2 = ((W ω) ^ 2 + c ^ 2) / (2 * c) := by
      field_simp
    rw [hrhs, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|W ω| - c), sq_abs (W ω), abs_nonneg (W ω)]
  calc ∫ ω, |W ω| ∂μ ≤ ∫ ω, ((W ω) ^ 2 / c + c) / 2 ∂μ :=
        integral_mono (hW.integrable (by norm_num)).abs
          (((hsq.div_const c).add (integrable_const _)).div_const 2) hle
    _ = ((∫ ω, (W ω) ^ 2 ∂μ) / c + c) / 2 := by
        rw [integral_div, integral_add (hsq.div_const c) (integrable_const _), integral_div,
          integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- `|∫(A−Z)² − 1| ≤ c + V/c + V` for every `c > 0`, where `∫A² = 1` and `V = ∫Z²`. -/
theorem abs_integral_sub_sq_sub_one_le {A Z : Ω → ℝ} (hA : MemLp A 2 μ) (hZ : MemLp Z 2 μ)
    (hA1 : ∫ ω, (A ω) ^ 2 ∂μ = 1) {c : ℝ} (hc : 0 < c) :
    |(∫ ω, (A ω - Z ω) ^ 2 ∂μ) - 1|
      ≤ c + (∫ ω, (Z ω) ^ 2 ∂μ) / c + (∫ ω, (Z ω) ^ 2 ∂μ) := by
  set V : ℝ := ∫ ω, (Z ω) ^ 2 ∂μ with hVdef
  have hi1 : Integrable (fun ω => (A ω) ^ 2) μ := hA.integrable_sq
  have hi2 : Integrable (fun ω => A ω * Z ω) μ := hA.integrable_mul hZ
  have hi3 : Integrable (fun ω => (Z ω) ^ 2) μ := hZ.integrable_sq
  have hV0 : 0 ≤ V := integral_nonneg (fun ω => sq_nonneg _)
  have hI : ∫ ω, (A ω - Z ω) ^ 2 ∂μ = 1 - 2 * (∫ ω, A ω * Z ω ∂μ) + V := by
    have hexp : ∀ ω, (A ω - Z ω) ^ 2 = ((A ω) ^ 2 - 2 * (A ω * Z ω)) + (Z ω) ^ 2 :=
      fun ω => by ring
    have hi2' : Integrable (fun ω => 2 * (A ω * Z ω)) μ := hi2.const_mul 2
    have hi12 : Integrable (fun ω => (A ω) ^ 2 - 2 * (A ω * Z ω)) μ := hi1.sub hi2'
    simp only [hexp]
    rw [integral_add hi12 hi3, integral_sub hi1 hi2', integral_const_mul, hA1]
  have hbd : |∫ ω, A ω * Z ω ∂μ| ≤ (c * 1 + V / c) / 2 := by
    refine (abs_integral_le_integral_abs).trans ?_
    have hle : ∀ ω, |A ω * Z ω| ≤ (c * (A ω) ^ 2 + (Z ω) ^ 2 / c) / 2 := by
      intro ω
      have hrhs : (c * (A ω) ^ 2 + (Z ω) ^ 2 / c) / 2
          = (c ^ 2 * (A ω) ^ 2 + (Z ω) ^ 2) / (2 * c) := by field_simp
      rw [hrhs, le_div_iff₀ (by positivity), abs_mul]
      nlinarith [sq_nonneg (c * |A ω| - |Z ω|), sq_abs (A ω), sq_abs (Z ω),
        abs_nonneg (A ω), abs_nonneg (Z ω)]
    calc ∫ ω, |A ω * Z ω| ∂μ ≤ ∫ ω, (c * (A ω) ^ 2 + (Z ω) ^ 2 / c) / 2 ∂μ :=
          integral_mono hi2.abs (((hi1.const_mul c).add (hi3.div_const c)).div_const 2) hle
      _ = (c * 1 + V / c) / 2 := by
          rw [integral_div, integral_add (hi1.const_mul c) (hi3.div_const c),
            integral_const_mul, integral_div, hA1]
  rw [hI]
  have : (1 : ℝ) - 2 * (∫ ω, A ω * Z ω ∂μ) + V - 1 = V - 2 * (∫ ω, A ω * Z ω ∂μ) := by ring
  rw [this]
  calc |V - 2 * (∫ ω, A ω * Z ω ∂μ)| ≤ |V| + |2 * (∫ ω, A ω * Z ω ∂μ)| := abs_sub _ _
    _ = V + 2 * |∫ ω, A ω * Z ω ∂μ| := by
        rw [abs_of_nonneg hV0, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ V + 2 * ((c * 1 + V / c) / 2) := by linarith [hbd]
    _ = c + V / c + V := by ring

end PartBSigma

section PartBSeq

open Filter

/-- A nonnegative sequence bounded by `c + V_n/c + V_n` for every `c > 0`, with `V_n → 0`,
converges to `0`. -/
theorem tendsto_zero_of_le_add_div {f V : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hV0 : ∀ n, 0 ≤ V n)
    (hV : Tendsto V atTop (𝓝 0))
    (h : ∀ c : ℝ, 0 < c → ∀ n, f n ≤ c + V n / c + V n) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hV ⊢
  intro ε hε
  have hδ0 : (0 : ℝ) < min (ε ^ 2 / 16) (ε / 8) := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := hV _ hδ0
  refine ⟨N, fun n hn => ?_⟩
  have h1 : V n < min (ε ^ 2 / 16) (ε / 8) := by
    have h2 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hV0 n)] at h2
    exact h2
  have hVa : V n ≤ ε ^ 2 / 16 := le_trans h1.le (min_le_left _ _)
  have hVb : V n ≤ ε / 8 := le_trans h1.le (min_le_right _ _)
  have hc : (0 : ℝ) < ε / 4 := by positivity
  have h3 := h (ε / 4) hc n
  have h4 : V n / (ε / 4) ≤ (ε ^ 2 / 16) / (ε / 4) :=
    div_le_div_of_nonneg_right hVa hc.le
  have h5 : (ε ^ 2 / 16) / (ε / 4) = ε / 4 := by field_simp; ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)]
  rw [h5] at h4
  linarith

end PartBSeq

section PartBTransfer

open Filter

/-- A Slutsky-type transfer on test-function integrals. For a bounded Lipschitz `h`,
`|∫h(A_n) − ∫h(σ_nB_n)| ≤ L∫|A_n − σ_nB_n|` and `|∫h(σ_nB_n) − ∫h(B_n)| ≤ L|σ_n − 1|∫|B_n|`, so
`∫h(B_n) → E h(Z)` together with `∫|A_n − σ_nB_n| → 0` and `σ_n → 1` gives `∫h(A_n) → E h(Z)`. -/
theorem tendsto_integral_of_approx
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → ℝ) (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (σ : ℕ → ℝ) {L c C : ℝ} {h : ℝ → ℝ} (hmh : Measurable h) (hbh : ∀ x, |h x| ≤ C)
    (hL : 0 ≤ L) (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|)
    (hABi : ∀ n, Integrable (fun ω => |A n ω - σ n * B n ω|) (μ n))
    (hd : Tendsto (fun n => ∫ ω, |A n ω - σ n * B n ω| ∂(μ n)) atTop (𝓝 0))
    (hBi : ∀ n, Integrable (fun ω => |B n ω|) (μ n))
    (hB1 : ∀ n, ∫ ω, |B n ω| ∂(μ n) ≤ 1)
    (hσ : Tendsto σ atTop (𝓝 1))
    (hlim : Tendsto (fun n => ∫ ω, h (B n ω) ∂(μ n)) atTop (𝓝 c)) :
    Tendsto (fun n => ∫ ω, h (A n ω) ∂(μ n)) atTop (𝓝 c) := by
  have hint : ∀ (n : ℕ) (f : Ω n → ℝ), Measurable f → Integrable (fun ω => h (f ω)) (μ n) :=
    fun n f hf => integrable_of_abs_le (hmh.comp hf) (C := C) (fun ω => hbh _)
  have key : ∀ n, |(∫ ω, h (A n ω) ∂(μ n)) - (∫ ω, h (B n ω) ∂(μ n))|
      ≤ L * (∫ ω, |A n ω - σ n * B n ω| ∂(μ n)) + L * |σ n - 1| := by
    intro n
    have hAh := hint n (A n) (hA n)
    have hSh := hint n (fun ω => σ n * B n ω) ((hB n).const_mul (σ n))
    have hBh := hint n (B n) (hB n)
    have e1 : |(∫ ω, h (A n ω) ∂(μ n)) - (∫ ω, h (σ n * B n ω) ∂(μ n))|
        ≤ L * (∫ ω, |A n ω - σ n * B n ω| ∂(μ n)) := by
      rw [← integral_sub hAh hSh, ← integral_const_mul]
      refine (abs_integral_le_integral_abs).trans ?_
      exact integral_mono (hAh.sub hSh).abs ((hABi n).const_mul L) (fun ω => hlip _ _)
    have e2 : |(∫ ω, h (σ n * B n ω) ∂(μ n)) - (∫ ω, h (B n ω) ∂(μ n))|
        ≤ L * |σ n - 1| := by
      rw [← integral_sub hSh hBh]
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ ω, |h (σ n * B n ω) - h (B n ω)| ∂(μ n)
          ≤ ∫ ω, (L * |σ n - 1|) * |B n ω| ∂(μ n) := by
            refine integral_mono (hSh.sub hBh).abs ((hBi n).const_mul _) (fun ω => ?_)
            calc |h (σ n * B n ω) - h (B n ω)| ≤ L * |σ n * B n ω - B n ω| := hlip _ _
              _ = L * (|σ n - 1| * |B n ω|) := by
                  rw [← abs_mul]
                  congr 2
                  ring
              _ = (L * |σ n - 1|) * |B n ω| := by ring
        _ = (L * |σ n - 1|) * ∫ ω, |B n ω| ∂(μ n) := integral_const_mul _ _
        _ ≤ (L * |σ n - 1|) * 1 := mul_le_mul_of_nonneg_left (hB1 n) (by positivity)
        _ = L * |σ n - 1| := by ring
    calc |(∫ ω, h (A n ω) ∂(μ n)) - (∫ ω, h (B n ω) ∂(μ n))|
        ≤ |(∫ ω, h (A n ω) ∂(μ n)) - (∫ ω, h (σ n * B n ω) ∂(μ n))|
          + |(∫ ω, h (σ n * B n ω) ∂(μ n)) - (∫ ω, h (B n ω) ∂(μ n))| :=
          abs_sub_le _ _ _
      _ ≤ L * (∫ ω, |A n ω - σ n * B n ω| ∂(μ n)) + L * |σ n - 1| := add_le_add e1 e2
  have hzero : Tendsto (fun n => (∫ ω, h (A n ω) ∂(μ n)) - (∫ ω, h (B n ω) ∂(μ n)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => L * (∫ ω, |A n ω - σ n * B n ω| ∂(μ n))) atTop (𝓝 0) := by
      simpa using hd.const_mul L
    have h2 : Tendsto (fun n => L * |σ n - 1|) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n => σ n - 1) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.2 hσ
      have h4 : Tendsto (fun n => |σ n - 1|) atTop (𝓝 0) := by simpa using h3.abs
      simpa using h4.const_mul L
    have hg : Tendsto (fun n => L * (∫ ω, |A n ω - σ n * B n ω| ∂(μ n)) + L * |σ n - 1|)
        atTop (𝓝 0) := by simpa using h1.add h2
    refine squeeze_zero_norm (fun n => ?_) hg
    rw [Real.norm_eq_abs]
    exact key n
  have hsum := hzero.add hlim
  simpa using hsum

end PartBTransfer

section PartBCLT

open Filter

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Theorem 5(b) on the array, in test-function form.** The only moment hypothesis is
`∫X_{n,o}⁴ ≤ ψ_n⁴`, and the rate hypotheses are those of part (a) with `φ_n` replaced by `ψ_n`.
The truncation level enters only the uniform bound in the Stein estimate; the two error terms are
controlled by `firstError_le_moment` and `secondError_le_moment`. -/
theorem cltcluster_b_expect
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (ψ : ℕ → ℝ) (m : ℕ → ℕ)
    (hψ : ∀ n, 0 < ψ n)
    (hint4 : ∀ n o, Integrable (fun ω => (X n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (X n o ω) ^ 4 ∂(μ n) ≤ (ψ n) ^ 4)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate1 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (ψ n) ^ 4)
      atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (ψ n) ^ 3)
      atTop (𝓝 0))
    (hfun : ℝ → ℝ) {Cb L : ℝ} (hb : ∀ x, |hfun x| ≤ Cb) (hderiv : ∀ x, |deriv hfun x| ≤ L)
    (hdiff : Differentiable ℝ hfun) :
    Tendsto (fun n => ∫ ω, hfun (depSum (X n) ω) ∂(μ n)) atTop (𝓝 (gExpect hfun)) := by
  classical
  -- the truncation level, chosen so that the tail variance is `≤ 1/(16(n+1))`
  set NR : ℕ → ℝ := fun n => (Fintype.card (O n) : ℝ) with hNR
  set R : ℕ → ℝ := fun n => 1 + 128 * ((n : ℝ) + 1) * NR n * (m n : ℝ) * (ψ n) ^ 2 with hRdef
  have hNRnn : ∀ n : ℕ, (0 : ℝ) ≤ NR n := by
    intro n; simp only [hNR]; positivity
  have hRx : ∀ n : ℕ, 0 ≤ 128 * ((n : ℝ) + 1) * NR n * (m n : ℝ) * (ψ n) ^ 2 := by
    intro n; simp only [hNR]; positivity
  have hR1 : ∀ n, 1 ≤ R n := by intro n; rw [hRdef]; linarith [hRx n]
  set τ : ℕ → ℝ := fun n => ψ n * Real.sqrt (R n) with hτdef
  have hsqrtR1 : ∀ n, 1 ≤ Real.sqrt (R n) := by
    intro n
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (hR1 n)
  have hτpos : ∀ n, 0 < τ n := by
    intro n
    rw [hτdef]
    exact mul_pos (hψ n) (lt_of_lt_of_le zero_lt_one (hsqrtR1 n))
  have hψτ : ∀ n, ψ n ≤ τ n := by
    intro n
    rw [hτdef]
    nth_rewrite 1 [← mul_one (ψ n)]
    exact mul_le_mul_of_nonneg_left (hsqrtR1 n) (hψ n).le
  have hτsq : ∀ n, (τ n) ^ 2 = (ψ n) ^ 2 * R n := by
    intro n
    rw [hτdef, mul_pow, Real.sq_sqrt (le_trans zero_le_one (hR1 n))]
  -- the tail `Z_o` and its total variance `V_n`
  set V : ℕ → ℝ := fun n => ∫ ω, (depSum (truncTail (μ n) (X n) (τ n)) ω) ^ 2 ∂(μ n) with hVdef
  have hV0 : ∀ n, 0 ≤ V n := fun n => integral_nonneg (fun ω => sq_nonneg _)
  have hVbd : ∀ n, V n ≤ 1 / (16 * ((n : ℝ) + 1)) := by
    intro n
    have h1 := integral_depSum_truncTail_sq_le (D n) (hτpos n) (hψτ n) (hψ n).le
      (hint4 n) (hfour n) (hmean n) (hdeg n)
    refine le_trans h1 ?_
    rw [hτsq n]
    have hRpos : (0 : ℝ) < R n := lt_of_lt_of_le zero_lt_one (hR1 n)
    have hψ2 : (0 : ℝ) < (ψ n) ^ 2 := pow_pos (hψ n) 2
    have heq : 8 * NR n * (m n : ℝ) * ((ψ n) ^ 4 / ((ψ n) ^ 2 * R n))
        = 8 * (NR n * (m n : ℝ) * (ψ n) ^ 2) / R n := by
      field_simp
    rw [heq, hRdef, div_le_div_iff₀ hRpos (by positivity)]
    nlinarith [hRx n, mul_nonneg (mul_nonneg (hNRnn n)
      (by positivity : (0:ℝ) ≤ (m n : ℝ))) (by positivity : (0:ℝ) ≤ (ψ n) ^ 2)]
  have hVsmall : ∀ n, V n ≤ 1 / 16 := by
    intro n
    refine le_trans (hVbd n) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hVto0 : Tendsto V atTop (𝓝 0) := by
    refine squeeze_zero hV0 (fun n => le_trans (hVbd n) ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  -- `σ_n² = ∫(∑_oY_o)²`, and `σ_n → 1` with `σ_n ≥ 1/2` at every `n`
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
  set σ : ℕ → ℝ := fun n => Real.sqrt (s2 n) with hσdef
  have hσge : ∀ n, (1 : ℝ) / 2 ≤ σ n := by
    intro n
    rw [hσdef,
      show (1 : ℝ) / 2 = Real.sqrt (1 / 4) from by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (hs2ge n)
  have hσpos : ∀ n, 0 < σ n := fun n => lt_of_lt_of_le (by norm_num) (hσge n)
  have hσ2 : ∀ n, (σ n) ^ 2 = s2 n := by
    intro n
    rw [hσdef]
    exact Real.sq_sqrt (le_trans (by norm_num) (hs2ge n))
  have hσto1 : Tendsto σ atTop (𝓝 1) := by
    have hc := (Real.continuous_sqrt.tendsto 1).comp hs2to1
    rw [Real.sqrt_one] at hc
    exact hc
  have hσinv : ∀ n, 1 / σ n ≤ 2 := by
    intro n
    rw [div_le_iff₀ (hσpos n)]
    linarith [hσge n]
  -- the standardized truncated array, and the Stein bound applied to it
  set Ys : ∀ n, O n → Ω n → ℝ := fun n => truncStd (μ n) (X n) (τ n) (σ n) with hYs
  set DY : ∀ n, DepGraph (Ys n) (μ n) :=
    fun n => truncStdDepGraph (D n) (τ n) (σ n) with hDY
  have hYsmeas : ∀ n o, Measurable (Ys n o) := fun n o => (DY n).meas o
  have hYsbd : ∀ n o ω, |Ys n o ω| ≤ 2 * τ n / σ n := fun n o ω =>
    abs_truncStd_le (D n) (hτpos n) (hψτ n) (hψ n).le (hσpos n) (hint4 n) (hfour n)
      (hmean n) o ω
  have hYsmean : ∀ n o, ∫ ω, Ys n o ω ∂(μ n) = 0 := fun n o =>
    integral_truncStd_eq_zero (D n) (hτpos n) o
  have hYsdepSum : ∀ (n : ℕ) (ω : Ω n),
      depSum (Ys n) ω = depSum (truncCent (μ n) (X n) (τ n)) ω / σ n :=
    fun n ω => depSum_truncStd (X n) (τ n) (σ n) ω
  have hYsvar : ∀ n, ∫ ω, (depSum (Ys n) ω) ^ 2 ∂(μ n) = 1 := by
    intro n
    have hre : ∀ ω, (depSum (Ys n) ω) ^ 2
        = (depSum (truncCent (μ n) (X n) (τ n)) ω) ^ 2 / (σ n) ^ 2 := by
      intro ω; rw [hYsdepSum n ω, div_pow]
    simp only [hre]
    rw [integral_div, hσ2 n]
    exact div_self (by linarith [hs2ge n] : s2 n ≠ 0)
  have hYsfour : ∀ n o, ∫ ω, (Ys n o ω) ^ 4 ∂(μ n) ≤ (2 * ψ n / σ n) ^ 4 := fun n o =>
    integral_truncStd_pow_four_le (D n) (hτpos n) (hψτ n) (hψ n).le (hσpos n) (hint4 n)
      (hfour n) (hmean n) o
  have hYsint4 : ∀ n o, Integrable (fun ω => (Ys n o ω) ^ 4) (μ n) := fun n o =>
    integrable_truncStd_pow_four (D n) (hτpos n) (hψτ n) (hψ n).le (hσpos n) (hint4 n)
      (hfour n) (hmean n) o
  have hYsdeg : ∀ n o, ((DY n).nbhd o).card ≤ m n := fun n o => hdeg n o
  -- the two Stein error terms, at the constant `2ψ_n/σ_n ≤ 4ψ_n`
  have hbnd4 : ∀ n, (2 * ψ n / σ n) ^ 4 ≤ 256 * (ψ n) ^ 4 := by
    intro n
    have h1 : 2 * ψ n / σ n ≤ 4 * ψ n := by
      rw [div_le_iff₀ (hσpos n)]
      nlinarith [hσge n, (hψ n).le]
    have h2 : (0 : ℝ) ≤ 2 * ψ n / σ n :=
      div_nonneg (by linarith [(hψ n).le]) (hσpos n).le
    calc (2 * ψ n / σ n) ^ 4 ≤ (4 * ψ n) ^ 4 := pow_le_pow_left₀ h2 h1 4
      _ = 256 * (ψ n) ^ 4 := by ring
  have hbnd3 : ∀ n, (2 * ψ n / σ n) ^ 3 ≤ 64 * (ψ n) ^ 3 := by
    intro n
    have h1 : 2 * ψ n / σ n ≤ 4 * ψ n := by
      rw [div_le_iff₀ (hσpos n)]
      nlinarith [hσge n, (hψ n).le]
    have h2 : (0 : ℝ) ≤ 2 * ψ n / σ n :=
      div_nonneg (by linarith [(hψ n).le]) (hσpos n).le
    calc (2 * ψ n / σ n) ^ 3 ≤ (4 * ψ n) ^ 3 := pow_le_pow_left₀ h2 h1 3
      _ = 64 * (ψ n) ^ 3 := by ring
  have herr1 : Tendsto
      (fun n => variance (fun ω => ∑ o, Ys n o ω * nbhdSum (Ys n) (DY n).nbhd o ω) (μ n))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => variance_nonneg _ _) (fun n => ?_)
      (by simpa using hrate1.const_mul (8 * 256 : ℝ))
    refine le_trans (firstError_le_moment (DY n) (hYsint4 n) (hYsfour n) (hYsdeg n)) ?_
    have h1 : (0 : ℝ) ≤ 8 * NR n * (m n : ℝ) ^ 3 := by
      have := hNRnn n; positivity
    calc 8 * (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (2 * ψ n / σ n) ^ 4
        ≤ 8 * NR n * (m n : ℝ) ^ 3 * (256 * (ψ n) ^ 4) :=
          mul_le_mul_of_nonneg_left (hbnd4 n) h1
      _ = 8 * 256 * ((Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (ψ n) ^ 4) := by
          simp only [hNR]; ring
  have herr2 : Tendsto
      (fun n => ∑ o, ∫ ω, |Ys n o ω| * (nbhdSum (Ys n) (DY n).nbhd o ω) ^ 2 ∂(μ n))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => Finset.sum_nonneg
      (fun o _ => integral_nonneg (fun ω => by positivity))) (fun n => ?_)
      (by simpa using hrate2.const_mul (64 : ℝ))
    refine le_trans (secondError_le_moment (DY n)
      (div_pos (by linarith [hψ n]) (hσpos n)) (hYsint4 n) (hYsfour n)
      (hYsdeg n)) ?_
    have h1 : (0 : ℝ) ≤ NR n * (m n : ℝ) ^ 2 := by
      have := hNRnn n; positivity
    calc (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (2 * ψ n / σ n) ^ 3
        ≤ NR n * (m n : ℝ) ^ 2 * (64 * (ψ n) ^ 3) :=
          mul_le_mul_of_nonneg_left (hbnd3 n) h1
      _ = 64 * ((Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (ψ n) ^ 3) := by
          simp only [hNR]; ring
  have hengine : Tendsto (fun n => ∫ ω, hfun (depSum (Ys n) ω) ∂(μ n)) atTop
      (𝓝 (gExpect hfun)) :=
    stein_expect_tendsto μ Ys (fun n => (DY n).nbhd) hYsmeas
      (fun n => 2 * τ n / σ n)
      (fun n => div_nonneg (by linarith [(hτpos n).le]) (hσpos n).le) hYsbd hYsmean
      (fun n o => (DY n).indepFun_leaveOut o) hYsvar herr1 herr2 hfun hb hderiv hdiff
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
  have hdiffAB : ∀ (n : ℕ) (ω : Ω n), depSum (X n) ω - σ n * depSum (Ys n) ω
      = depSum (truncTail (μ n) (X n) (τ n)) ω := by
    intro n ω
    rw [hYsdepSum n ω, mul_div_cancel₀ _ (ne_of_gt (hσpos n)), hZsum n ω]
  have hABi : ∀ n, Integrable (fun ω => |depSum (X n) ω - σ n * depSum (Ys n) ω|) (μ n) := by
    intro n
    have hre : (fun ω => |depSum (X n) ω - σ n * depSum (Ys n) ω|)
        = fun ω => |depSum (truncTail (μ n) (X n) (τ n)) ω| := by
      funext ω; rw [hdiffAB n ω]
    rw [hre]
    exact ((hZmem n).integrable (by norm_num)).abs
  have hd0 : Tendsto (fun n => ∫ ω, |depSum (X n) ω - σ n * depSum (Ys n) ω| ∂(μ n))
      atTop (𝓝 0) := by
    have hre : ∀ n, (fun ω => |depSum (X n) ω - σ n * depSum (Ys n) ω|)
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
      (C := (Fintype.card (O n) : ℝ) * (2 * τ n / σ n)) (fun ω => ?_)
    calc |depSum (Ys n) ω| ≤ ∑ o, |Ys n o ω| := by
          simpa [depSum] using Finset.abs_sum_le_sum_abs (fun o => Ys n o ω) Finset.univ
      _ ≤ ∑ _o : O n, 2 * τ n / σ n := Finset.sum_le_sum (fun o _ => hYsbd n o ω)
      _ = (Fintype.card (O n) : ℝ) * (2 * τ n / σ n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hBmem : ∀ n, MemLp (depSum (Ys n)) 2 (μ n) := by
    intro n
    refine memLp_two_of_abs_le (hBmeas n)
      (C := (Fintype.card (O n) : ℝ) * (2 * τ n / σ n)) (fun ω => ?_)
    calc |depSum (Ys n) ω| ≤ ∑ o, |Ys n o ω| := by
          simpa [depSum] using Finset.abs_sum_le_sum_abs (fun o => Ys n o ω) Finset.univ
      _ ≤ ∑ _o : O n, 2 * τ n / σ n := Finset.sum_le_sum (fun o _ => hYsbd n o ω)
      _ = (Fintype.card (O n) : ℝ) * (2 * τ n / σ n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hB1 : ∀ n, ∫ ω, |depSum (Ys n) ω| ∂(μ n) ≤ 1 := by
    intro n
    have h1 := integral_abs_le_of_sq (hBmem n) (c := 1) (by norm_num)
    rw [hYsvar n] at h1
    linarith
  exact tendsto_integral_of_approx μ (fun n => depSum (X n)) (fun n => depSum (Ys n))
    hAmeas hBmeas σ hdiff.continuous.measurable hb hL0 hlip hABi hd0 hBi hB1 hσto1 hengine

/-- The characteristic-function limit from the test-function limits at `cos(t·)` and
`sin(t·)`. -/
theorem charFun_tendsto_of_expect
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (W : ∀ n, Ω n → ℝ) (hW : ∀ n, Measurable (W n))
    (hexp : ∀ (h : ℝ → ℝ) (C L : ℝ), (∀ x, |h x| ≤ C) → (∀ x, |deriv h x| ≤ L) →
      Differentiable ℝ h → Tendsto (fun n => ∫ ω, h (W n ω) ∂(μ n)) atTop (𝓝 (gExpect h)))
    (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (W n)) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  have hcos_diff : Differentiable ℝ (fun x => Real.cos (t * x)) := by fun_prop
  have hcos_b : ∀ x, |Real.cos (t * x)| ≤ 1 := fun x => Real.abs_cos_le_one _
  have hcos_d : ∀ x, |deriv (fun x => Real.cos (t * x)) x| ≤ |t| := by
    intro x
    have hderiv : deriv (fun x => Real.cos (t * x)) x = -(t * Real.sin (t * x)) := by
      have h := (Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t)
      simpa [mul_comm, Function.comp_def] using h.deriv
    rw [hderiv, abs_neg, abs_mul]
    calc |t| * |Real.sin (t * x)| ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |t| := mul_one _
  have hsin_diff : Differentiable ℝ (fun x => Real.sin (t * x)) := by fun_prop
  have hsin_b : ∀ x, |Real.sin (t * x)| ≤ 1 := fun x => Real.abs_sin_le_one _
  have hsin_d : ∀ x, |deriv (fun x => Real.sin (t * x)) x| ≤ |t| := by
    intro x
    have hderiv : deriv (fun x => Real.sin (t * x)) x = t * Real.cos (t * x) := by
      have h := (Real.hasDerivAt_sin (t * x)).comp x ((hasDerivAt_id x).const_mul t)
      simpa [mul_comm, Function.comp_def] using h.deriv
    rw [hderiv, abs_mul]
    calc |t| * |Real.cos (t * x)| ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |t| := mul_one _
  have hcos_tendsto := hexp (fun x => Real.cos (t * x)) 1 |t| hcos_b hcos_d hcos_diff
  have hsin_tendsto := hexp (fun x => Real.sin (t * x)) 1 |t| hsin_b hsin_d hsin_diff
  have hgauss : charFun (gaussianReal 0 1) t
      = (↑(gExpect (fun x => Real.cos (t * x))) : ℂ)
        + (↑(gExpect (fun x => Real.sin (t * x))) : ℂ) * Complex.I := by
    have hmap : (gaussianReal 0 1).map id = gaussianReal 0 1 := Measure.map_id
    have h := charFun_map_eq_cos_sin (gaussianReal 0 1) id measurable_id t
    rw [hmap] at h
    simpa [gExpect, Function.comp] using h
  have hlaw : ∀ n, charFun ((μ n).map (W n)) t
      = (↑(∫ ω, Real.cos (t * W n ω) ∂(μ n)) : ℂ)
        + (↑(∫ ω, Real.sin (t * W n ω) ∂(μ n)) : ℂ) * Complex.I := fun n =>
    charFun_map_eq_cos_sin (μ n) (W n) (hW n) t
  rw [hgauss]
  simp_rw [hlaw]
  refine Tendsto.add ?_ (Tendsto.mul_const Complex.I ?_)
  · exact (Complex.continuous_ofReal.tendsto _).comp hcos_tendsto
  · exact (Complex.continuous_ofReal.tendsto _).comp hsin_tendsto

/-- **Theorem 5(b) at general `J`, on the array**, in characteristic-function form. -/
theorem cltcluster_b_general_charFun
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (ψ : ℕ → ℝ) (m : ℕ → ℕ)
    (hψ : ∀ n, 0 < ψ n)
    (hint4 : ∀ n o, Integrable (fun ω => (X n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (X n o ω) ^ 4 ∂(μ n) ≤ (ψ n) ^ 4)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate1 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (ψ n) ^ 4)
      atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (ψ n) ^ 3)
      atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (depSum (X n))) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  refine charFun_tendsto_of_expect μ (fun n => depSum (X n))
    (fun n => Finset.measurable_sum _ (fun o _ => (D n).meas o)) (fun h C L hb hd hdiff => ?_) t
  exact cltcluster_b_expect μ X D ψ m hψ hint4 hfour hdeg hmean hvar hrate1 hrate2 h hb hd hdiff

/-- **Theorem 5(b) at general `J`, on the array**, in CDF form. -/
theorem cltcluster_b_general
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (ψ : ℕ → ℝ) (m : ℕ → ℕ)
    (hψ : ∀ n, 0 < ψ n)
    (hint4 : ∀ n o, Integrable (fun ω => (X n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (X n o ω) ^ 4 ∂(μ n) ≤ (ψ n) ^ 4)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate1 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (ψ n) ^ 4)
      atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (ψ n) ^ 3)
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
  exact cltcluster_b_general_charFun μ X D ψ m hψ hint4 hfour hdeg hmean hvar hrate1 hrate2 t

/-- The same, as `⟶ᵈ N(0,1)`, by Lévy's continuity theorem. -/
theorem cltcluster_b_general_tendstoInDistribution
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, O n → Ω n → ℝ) (D : ∀ n, DepGraph (X n) (μ n))
    (ψ : ℕ → ℝ) (m : ℕ → ℕ)
    (hψ : ∀ n, 0 < ψ n)
    (hint4 : ∀ n o, Integrable (fun ω => (X n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (X n o ω) ^ 4 ∂(μ n) ≤ (ψ n) ^ 4)
    (hdeg : ∀ n o, ((D n).nbhd o).card ≤ m n)
    (hmean : ∀ n o, ∫ ω, X n o ω ∂(μ n) = 0)
    (hvar : ∀ n, ∫ ω, (depSum (X n) ω) ^ 2 ∂(μ n) = 1)
    (hrate1 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 3 * (ψ n) ^ 4)
      atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => (Fintype.card (O n) : ℝ) * (m n : ℝ) ^ 2 * (ψ n) ^ 3)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun n => depSum (X n)) atTop (id : ℝ → ℝ) μ (gaussianReal 0 1) := by
  have hWmeas : ∀ n, Measurable (depSum (X n)) := fun n =>
    Finset.measurable_sum _ (fun o _ => (D n).meas o)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hWmeas n).aemeasurable)
    aemeasurable_id fun t => ?_
  rw [Measure.map_id]
  exact cltcluster_b_general_charFun μ X D ψ m hψ hint4 hfour hdeg hmean hvar hrate1 hrate2 t

end PartBCLT

section PartBReduction

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {W : Type*} [MeasurableSpace W] {μ : Measure W}

omit [DecidableEq O] in
/-- The weight bound `|a_n'x̃_o| ≤ Bλ_min(Ω_n)^{-1/2}`. -/
theorem abs_scoreCoef_le {Xt : Matrix O K ℝ} {Om : Matrix O O ℝ} {Rn : Matrix r K ℝ}
    (hPD : (scoreVar Xt Om).PosDef) (hA : Function.Injective (scoreMap Xt Rn).mulVec)
    {c : ℝ} (hc : 0 < c) (hcOm : c • (1 : Matrix K K ℝ) ≤ scoreVar Xt Om)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ o, (fun k => Xt o k) ⬝ᵥ (fun k => Xt o k) ≤ B ^ 2)
    {b : r → ℝ} (hb : b ⬝ᵥ b = 1) (o : O) :
    |(Xt *ᵥ steinWeight Xt Om Rn b) o| ≤ B / Real.sqrt c := by
  have hGnorm : ‖steinStd Xt Om Rn‖ ≤ Real.sqrt c⁻¹ := by
    have h := Multiway.sq_l2_opNorm_restrictedStd_le hPD hA hc hcOm
    have h2 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (norm_nonneg _)] at h2
  have hanorm : Real.sqrt (steinWeight Xt Om Rn b ⬝ᵥ steinWeight Xt Om Rn b)
      ≤ Real.sqrt c⁻¹ := by
    have h := sqrt_dot_mulVec_le (steinStd Xt Om Rn) b
    rw [hb, Real.sqrt_one, mul_one] at h
    exact h.trans hGnorm
  have hrow : Real.sqrt ((fun k => Xt o k) ⬝ᵥ (fun k => Xt o k)) ≤ B := by
    have := Real.sqrt_le_sqrt (hB o)
    rwa [Real.sqrt_sq hB0] at this
  have hdot : (Xt *ᵥ steinWeight Xt Om Rn b) o
      = (fun k => Xt o k) ⬝ᵥ steinWeight Xt Om Rn b := rfl
  rw [hdot]
  refine (abs_dotProduct_le _ _).trans ?_
  have h := mul_le_mul hrow hanorm (Real.sqrt_nonneg _) hB0
  rw [Real.sqrt_inv] at h
  rwa [div_eq_mul_inv]

omit [DecidableEq O] [DecidableEq K] in
theorem integrable_scoreArray_pow_four {v : O → W → ℝ}
    (hint4 : ∀ o, Integrable (fun ω => (v o ω) ^ 4) μ) (Xt : Matrix O K ℝ) (a : K → ℝ)
    (o : O) : Integrable (fun ω => (scoreArray Xt a v o ω) ^ 4) μ := by
  have hre : (fun ω => (scoreArray Xt a v o ω) ^ 4)
      = fun ω => ((Xt *ᵥ a) o) ^ 4 * (v o ω) ^ 4 := by
    funext ω; rw [scoreArray, mul_pow]
  rw [hre]
  exact (hint4 o).const_mul _

omit [DecidableEq O] in
/-- The fourth-moment bound transported to the array:
`∫X_{n,o}⁴ ≤ (Bλ_min(Ω_n)^{-1/2}C^{1/4})⁴`. -/
theorem integral_scoreArray_pow_four_le {Xt : Matrix O K ℝ} {Om : Matrix O O ℝ}
    {Rn : Matrix r K ℝ}
    (hPD : (scoreVar Xt Om).PosDef) (hA : Function.Injective (scoreMap Xt Rn).mulVec)
    {c : ℝ} (hc : 0 < c) (hcOm : c • (1 : Matrix K K ℝ) ≤ scoreVar Xt Om)
    {B C4 : ℝ} (hB0 : 0 ≤ B) (hC40 : 0 ≤ C4)
    (hB : ∀ o, (fun k => Xt o k) ⬝ᵥ (fun k => Xt o k) ≤ B ^ 2)
    {v : O → W → ℝ} (hint4 : ∀ o, Integrable (fun ω => (v o ω) ^ 4) μ)
    (hfour : ∀ o, ∫ ω, (v o ω) ^ 4 ∂μ ≤ C4 ^ 4)
    {b : r → ℝ} (hb : b ⬝ᵥ b = 1) (o : O) :
    ∫ ω, (scoreArray Xt (steinWeight Xt Om Rn b) v o ω) ^ 4 ∂μ
      ≤ (B * C4 / Real.sqrt c) ^ 4 := by
  set w : ℝ := (Xt *ᵥ steinWeight Xt Om Rn b) o with hw
  have hcoef : |w| ≤ B / Real.sqrt c := abs_scoreCoef_le hPD hA hc hcOm hB0 hB hb o
  have hw4 : w ^ 4 ≤ (B / Real.sqrt c) ^ 4 := by
    have h1 : w ^ 4 = |w| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h1]
    exact pow_le_pow_left₀ (abs_nonneg _) hcoef 4
  have hre : ∀ ω, (scoreArray Xt (steinWeight Xt Om Rn b) v o ω) ^ 4
      = w ^ 4 * (v o ω) ^ 4 := by
    intro ω; rw [scoreArray, mul_pow]
  simp only [hre]
  rw [integral_const_mul]
  have hnn : (0 : ℝ) ≤ ∫ ω, (v o ω) ^ 4 ∂μ := integral_nonneg (fun ω => by positivity)
  calc w ^ 4 * ∫ ω, (v o ω) ^ 4 ∂μ ≤ (B / Real.sqrt c) ^ 4 * ∫ ω, (v o ω) ^ 4 ∂μ :=
        mul_le_mul_of_nonneg_right hw4 hnn
    _ ≤ (B / Real.sqrt c) ^ 4 * C4 ^ 4 :=
        mul_le_mul_of_nonneg_left (hfour o) (by positivity)
    _ = (B * C4 / Real.sqrt c) ^ 4 := by
        rw [div_pow, div_pow, mul_pow]; ring

variable [IsProbabilityMeasure μ]

omit [DecidableEq O] [DecidableEq K] in
/-- The total variance `∫(∑_oX_{n,o})² = a'Ω_na` under fourth moments. -/
theorem integral_depSum_scoreArray_sq_moment {v : O → W → ℝ} {Om : Matrix O O ℝ}
    (hmeas : ∀ o, Measurable (v o))
    (hint4 : ∀ o, Integrable (fun ω => (v o ω) ^ 4) μ)
    (hOm : ∀ o o', ∫ ω, v o ω * v o' ω ∂μ = Om o o')
    (Xt : Matrix O K ℝ) (a : K → ℝ) :
    ∫ ω, (depSum (scoreArray Xt a v) ω) ^ 2 ∂μ = a ⬝ᵥ (scoreVar Xt Om *ᵥ a) := by
  set cw : O → ℝ := Xt *ᵥ a with hcw
  have hsq : ∀ ω, (depSum (scoreArray Xt a v) ω) ^ 2
      = ∑ o, ∑ o', (cw o * cw o') * (v o ω * v o' ω) := by
    intro ω
    have h0 : depSum (scoreArray Xt a v) ω = ∑ o, cw o * v o ω := rfl
    rw [h0, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun o' _ => by ring
  have hmul : ∀ o o' : O, Integrable (fun ω => v o ω * v o' ω) μ := by
    intro o o'
    have hmaj : Integrable (fun ω => ((v o ω) ^ 2 + (v o' ω) ^ 2) / 2) μ :=
      ((integrable_sq_of_integrable_pow_four (hmeas o) (hint4 o)).add
        (integrable_sq_of_integrable_pow_four (hmeas o') (hint4 o'))).div_const 2
    refine Integrable.mono' hmaj ((hmeas o).mul (hmeas o')).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    have := two_mul_abs_mul_le_sq_add_sq (v o ω) (v o' ω)
    linarith
  have hint : ∀ o o' : O, Integrable (fun ω => (cw o * cw o') * (v o ω * v o' ω)) μ :=
    fun o o' => (hmul o o').const_mul _
  have hintsum : ∀ o : O, Integrable (fun ω => ∑ o', (cw o * cw o') * (v o ω * v o' ω)) μ :=
    fun o => integrable_finsetSum _ (fun o' _ => hint o o')
  calc ∫ ω, (depSum (scoreArray Xt a v) ω) ^ 2 ∂μ
      = ∫ ω, ∑ o, ∑ o', (cw o * cw o') * (v o ω * v o' ω) ∂μ :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsq)
    _ = ∑ o, ∑ o', (cw o * cw o') * Om o o' := by
        rw [MeasureTheory.integral_finsetSum _ (fun o _ => hintsum o)]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [MeasureTheory.integral_finsetSum _ (fun o' _ => hint o o')]
        exact Finset.sum_congr rfl fun o' _ => by
          rw [MeasureTheory.integral_const_mul, hOm o o']
    _ = cw ⬝ᵥ (Om *ᵥ cw) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        have hmv : (Om *ᵥ cw) o = ∑ o', Om o o' * cw o' := rfl
        rw [hmv, Finset.mul_sum]
        exact Finset.sum_congr rfl fun o' _ => by ring
    _ = a ⬝ᵥ (scoreVar Xt Om *ᵥ a) := Multiway.dotProduct_mulVec_conj Xt Om a

omit [DecidableEq O] in
/-- The standardization from fourth moments: `∫(∑_oX_{n,o})² = 1`. -/
theorem integral_depSum_scoreArray_sq_eq_one_moment {Xt : Matrix O K ℝ} {Om : Matrix O O ℝ}
    {Rn : Matrix r K ℝ} (hPD : (scoreVar Xt Om).PosDef)
    (hA : Function.Injective (scoreMap Xt Rn).mulVec)
    {v : O → W → ℝ} (hmeas : ∀ o, Measurable (v o))
    (hint4 : ∀ o, Integrable (fun ω => (v o ω) ^ 4) μ)
    (hOm : ∀ o o', ∫ ω, v o ω * v o' ω ∂μ = Om o o')
    {b : r → ℝ} (hb : b ⬝ᵥ b = 1) :
    ∫ ω, (depSum (scoreArray Xt (steinWeight Xt Om Rn b) v) ω) ^ 2 ∂μ = 1 := by
  rw [integral_depSum_scoreArray_sq_moment hmeas hint4 hOm]
  have h := Multiway.dotProduct_mulVec_conj (steinStd Xt Om Rn) (scoreVar Xt Om) b
  have hGOG : (steinStd Xt Om Rn)ᵀ * scoreVar Xt Om * steinStd Xt Om Rn = 1 :=
    Multiway.transpose_mul_mul_restrictedStd hPD hA
  rw [hGOG, Matrix.one_mulVec, hb] at h
  exact h

end PartBReduction

section PartBBetaJM

open Filter
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- **Theorem 5(b) at general `J`, for `β̂_JM`, under `(n/D_n)^{1/3}δ_n → 0`.** The bound
`sup_o|ν_o| ≤ C_ν` of part (a) is replaced by the fourth-moment bound `∫ν_o⁴ ≤ C`, written
`C = C₄⁴`. The truncation does not enter the rate, since both Stein error terms are controlled by
the fourth moment of the truncated array, which is at most `(2ψ_n)⁴` with `ψ_n = BC₄λ_min(Ω_n)^{-1/2}`. The conditions
`0 < B` and `0 < C₄` make `ψ_n > 0`. -/
theorem cltcluster_b_general_betaJM
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂(μ n) ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  have hacc : Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0) :=
    tendsto_accumRate hDn1 hDnN hrate
  have hsec : Tendsto (fun n => secondRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0) :=
    tendsto_secondRate hDn1 hlmin hrate
  simp only [hstat]
  refine cltcluster_b_general μ
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * C4 / Real.sqrt (lmin n)) (fun n => Dn n + 1)
    (fun n => div_pos (mul_pos hB0 hC40) (Real.sqrt_pos.mpr (hlmin n))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ s
  · exact fun n o => integrable_scoreArray_pow_four (hint4 n) (Xt n) _ o
  · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hA n) (hlmin n) (hfloor n)
      hB0.le hC40.le (hB n) (hint4 n) (hfour n) hb o
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hint4 n) (hOm n) hb
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hacc.const_mul (8 * B ^ 4 * C4 ^ 4))
    exact firstRate_le (hDn1 n) (hlmin n)
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hsec.const_mul (4 * B ^ 3 * C4 ^ 3))
    exact secondRate_le (hDn1 n) (hlmin n) hB0.le hC40.le

end PartBBetaJM

section PartBWitness

open Filter
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.Multilinear

/-- The hypotheses of `cltcluster_b_general_betaJM` hold on the `J = 2` design of
`cltcluster_a_general_betaJM_witness`. The total variance is `1` at every `n` by the
fourth-moment standardization, `ψ_n = (n+3)^{-1/2} → 0` and `D_n = 2`. The disturbance is
bounded, as is every variable on a finite probability space. -/
theorem cltcluster_b_general_betaJM_witness (s : ℝ) :
    Tendsto (fun n => ((coins (n + 3)).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt (n + 2))
              (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
                  ((redXt (n + 2))ᵀ *ᵥ (fun o => sign2 o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  have hsq4 : ∀ (m : ℕ) (o : Fin m) (ω : Fin m → Bool), (sign2 o ω) ^ 4 ≤ 1 := by
    intro m o ω
    have h1 : (sign2 o ω) ^ 4 = |sign2 o ω| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h1]
    calc |sign2 o ω| ^ 4 ≤ (1 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_sign2_le' o ω) 4
      _ = 1 := one_pow 4
  have hint4 : ∀ (m : ℕ) (o : Fin m), Integrable (fun ω => (sign2 o ω) ^ 4) (coins m) := by
    intro m o
    refine integrable_of_abs_le ((measurable_sign2 o).pow_const 4) (C := 1) (fun ω => ?_)
    rw [abs_of_nonneg (by positivity)]
    exact hsq4 m o ω
  refine cltcluster_b_general_betaJM (O := fun n => Fin (n + 3))
    (fun n => coins (n + 3)) (fun n => redXt (n + 2)) (fun n => 1) (fun n => 1)
    (fun _ o => sign2 o)
    (fun n ω => ((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
      ((redXt (n + 2))ᵀ *ᵥ (fun o => sign2 o ω)))
    (fun _ => 0) pathDep (fun _ _ => by simp)
    (fun n => redXt_scoreMap_isUnit (n + 2)) (fun n => (n : ℝ) + 3) (fun n => by positivity)
    ?_ (fun n => red_second_moment (n + 2)) (fun n o => integral_sign2 o)
    1 1 zero_lt_one zero_lt_one ?_ (fun n o => hint4 (n + 3) o) ?_
    (fun _ => 2) (fun _ => by norm_num) ?_ ?_ ?_ (fun _ => (1 : ℝ)) ?_ s
  · intro n
    rw [redXt_scoreVar]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · intro _ _
    simp [redXt, dotProduct]
  · intro n o
    calc ∫ ω, (sign2 o ω) ^ 4 ∂(coins (n + 3)) ≤ ∫ _ω, (1 : ℝ) ∂(coins (n + 3)) :=
          integral_mono (hint4 (n + 3) o) (integrable_const _) (fun ω => hsq4 (n + 3) o ω)
      _ = 1 ^ 4 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul, one_pow]
  · intro n
    simp
  · intro n o
    exact pathDep_nbhd_card n o
  · simpa using tendsto_steinRate_witness
  · simp [dotProduct]

end PartBWitness


/-! ## The score representation from Theorem 3

The score representation `β̂_JM − β = (X̃'X̃)^{-1}X̃'ν` follows from Theorem 3(a), through
`Multiway.jm_equiv`, and Theorem 3(c), through `Multiway.within_inner_dummy_eq_zero`, and `A_n`
has full column rank.

#### Hypotheses

* `Sm`, `Xop`: the fixed-effect spaces `𝒮_m = col(Δ_m)` and the regressor map `a ↦ Xa`;
* `hwithin`: `X̃ = Q_[Δ]X`, written as `X̃a = Q_[Δ]Xa` for every `a`;
* `hid`: identification (`Xa ∈ 𝒮 ⟹ a = 0`), which makes `X̃'X̃` invertible;
* `hiota`: `ι_n ∈ 𝒮`;
* `hfe`, `hmodel`: the model `y = Xβ + ∑_mΔ_mα^{(m)} + ν` with `Δ_mα^{(m)} ∈ 𝒮_m`;
* `hJM`: `β̂_JM` is the coefficient on `X` in the joint-projection regression;
* `hR`: `𝓡_n` has full row rank. -/


section ScoreRepresentation

open Matrix
open scoped RealInnerProductSpace

variable {O : Type*} [Fintype O]
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem inner_euclideanSpace_eq_dotProduct (u v : EuclideanSpace ℝ O) :
    ⟪u, v⟫ = (WithLp.ofLp u) ⬝ᵥ (WithLp.ofLp v) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]

theorem eq_zero_of_dotProduct_eq_zero {w : K → ℝ} (h : ∀ a : K → ℝ, a ⬝ᵥ w = 0) : w = 0 := by
  funext k
  have := h (Pi.single k 1)
  simpa using this

theorem eq_of_dotProduct_eq {w w' : K → ℝ} (h : ∀ a : K → ℝ, a ⬝ᵥ w = a ⬝ᵥ w') : w = w' := by
  refine sub_eq_zero.mp (eq_zero_of_dotProduct_eq_zero fun a => ?_)
  rw [dotProduct_sub, h a, sub_self]

/-- `X̃ = Q_[Δ]X`, written as a matrix. -/
def IsWithinMatrix (S : Submodule ℝ (EuclideanSpace ℝ O))
    (Xop : (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ O) (Xt : Matrix O K ℝ) : Prop :=
  ∀ a : K → ℝ, WithLp.ofLp (Multiway.jointWithin S (Xop a)) = Xt *ᵥ a

variable {S : Submodule ℝ (EuclideanSpace ℝ O)}
  {Xop : (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ O} {Xt : Matrix O K ℝ}

omit [DecidableEq K] in
/-- `a'(X̃'v) = (Q_[Δ]Xa)'v`. -/
theorem dotProduct_transpose_within (hw : IsWithinMatrix S Xop Xt) (a : K → ℝ)
    (v : EuclideanSpace ℝ O) :
    a ⬝ᵥ (Xtᵀ *ᵥ (WithLp.ofLp v)) = ⟪Multiway.jointWithin S (Xop a), v⟫ := by
  rw [← dotProduct_mulVec_adjoint Xt a (WithLp.ofLp v), ← hw a,
    inner_euclideanSpace_eq_dotProduct]

theorem transpose_within_mulVec_eq_zero_of_mem (hw : IsWithinMatrix S Xop Xt)
    {s : EuclideanSpace ℝ O} (hs : s ∈ S) : Xtᵀ *ᵥ (WithLp.ofLp s) = 0 :=
  eq_zero_of_dotProduct_eq_zero fun a => by
    rw [dotProduct_transpose_within hw a s]
    exact Multiway.inner_jointWithin_right hs (Xop a)

theorem transpose_within_mulVec_dummy_eq_zero {D : Type*}
    {Sm : D → Submodule ℝ (EuclideanSpace ℝ O)}
    (hw : IsWithinMatrix (⨆ k, Sm k) Xop Xt) (m : D) {d : EuclideanSpace ℝ O}
    (hd : d ∈ Sm m) : Xtᵀ *ᵥ (WithLp.ofLp d) = 0 :=
  eq_zero_of_dotProduct_eq_zero fun a => by
    rw [dotProduct_transpose_within hw a d]
    exact Multiway.within_inner_dummy_eq_zero m hd a

theorem transpose_within_mulVec_regressor (hw : IsWithinMatrix S Xop Xt) (c : K → ℝ) :
    Xtᵀ *ᵥ (WithLp.ofLp (Xop c)) = (Xtᵀ * Xt) *ᵥ c := by
  refine eq_of_dotProduct_eq fun a => ?_
  rw [dotProduct_transpose_within hw a (Xop c),
    Multiway.inner_jointWithin_comp' S (Xop a) (Xop c),
    inner_euclideanSpace_eq_dotProduct, hw a, hw c,
    dotProduct_mulVec_adjoint Xt a (Xt *ᵥ c), mulVec_mulVec]

theorem transpose_within_residual_eq_zero (hw : IsWithinMatrix S Xop Xt)
    {y : EuclideanSpace ℝ O} {b : K → ℝ} (hb : Multiway.IsMFESlope S Xop y b) :
    Xtᵀ *ᵥ (WithLp.ofLp (y - Xop b)) = 0 :=
  eq_zero_of_dotProduct_eq_zero fun a => by
    rw [dotProduct_transpose_within hw a (y - Xop b), Multiway.inner_jointWithin_symm]
    exact hb a

/-- `X̃'X̃(b − β) = X̃'ν`. -/
theorem gram_mulVec_sub_eq_score (hw : IsWithinMatrix S Xop Xt)
    {y s v : EuclideanSpace ℝ O} {β b : K → ℝ}
    (hs : Xtᵀ *ᵥ (WithLp.ofLp s) = 0) (hy : y = Xop β + s + v)
    (hb : Multiway.IsMFESlope S Xop y b) :
    (Xtᵀ * Xt) *ᵥ (b - β) = Xtᵀ *ᵥ (WithLp.ofLp v) := by
  have h0 := transpose_within_residual_eq_zero hw hb
  rw [hy] at h0
  have hexp : WithLp.ofLp (Xop β + s + v - Xop b)
      = WithLp.ofLp (Xop β) + WithLp.ofLp s + WithLp.ofLp v - WithLp.ofLp (Xop b) := by
    simp
  rw [hexp] at h0
  simp only [mulVec_sub, mulVec_add, hs, transpose_within_mulVec_regressor hw] at h0
  rw [mulVec_sub]
  have := sub_eq_zero.mp h0
  linear_combination (norm := module) -this

theorem isUnit_det_gram_of_identified (hw : IsWithinMatrix S Xop Xt)
    (hid : Multiway.Identified S Xop) : IsUnit (Xtᵀ * Xt).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro a1 a2 h
  have hz : (Xtᵀ * Xt) *ᵥ (a1 - a2) = 0 := by
    rw [mulVec_sub]
    simpa using sub_eq_zero.mpr h
  have hq : (Xt *ᵥ (a1 - a2)) ⬝ᵥ (Xt *ᵥ (a1 - a2)) = 0 := by
    rw [dotProduct_mulVec_adjoint Xt (a1 - a2) (Xt *ᵥ (a1 - a2)), mulVec_mulVec, hz,
      dotProduct_zero]
  have hxz : Xt *ᵥ (a1 - a2) = 0 := dotProduct_star_self_eq_zero.mp (by simpa using hq)
  have hj : Multiway.jointWithin S (Xop (a1 - a2)) = 0 := by
    have := hw (a1 - a2)
    rw [hxz] at this
    exact (WithLp.ofLp_eq_zero _).mp this
  exact sub_eq_zero.mp (hid (a1 - a2) (Multiway.jointWithin_eq_zero_iff.mp hj))

/-- The score representation `β̂_JM − β = (X̃'X̃)^{-1}X̃'ν`, from Theorem 3(a) and (c). -/
theorem score_representation {D : Type*} [Fintype D]
    {Sm : D → Submodule ℝ (EuclideanSpace ℝ O)}
    (hw : IsWithinMatrix (⨆ k, Sm k) Xop Xt)
    (hid : Multiway.Identified (⨆ k, Sm k) Xop)
    {iota : EuclideanSpace ℝ O} (hiota : iota ∈ (⨆ k, Sm k))
    {fe : D → EuclideanSpace ℝ O} (hfe : ∀ m, fe m ∈ Sm m)
    {y v : EuclideanSpace ℝ O} {β b : K → ℝ}
    (hy : y = Xop β + (∑ m, fe m) + v)
    (hb : Multiway.IsAugSlope (Multiway.jmControls iota (⨆ k, Sm k) Xop) Xop y b) :
    b - β = (Xtᵀ * Xt)⁻¹ *ᵥ (Xtᵀ *ᵥ (WithLp.ofLp v)) := by
  have hmfe : Multiway.IsMFESlope (⨆ k, Sm k) Xop y b := (Multiway.jm_equiv hid hiota y b).mp hb
  have hs : Xtᵀ *ᵥ (WithLp.ofLp (∑ m, fe m)) = 0 := by
    have hsum : WithLp.ofLp (∑ m, fe m) = ∑ m, WithLp.ofLp (fe m) := by simp
    rw [hsum, Matrix.mulVec_sum]
    exact Finset.sum_eq_zero fun m _ => transpose_within_mulVec_dummy_eq_zero hw m (hfe m)
  have hgram := gram_mulVec_sub_eq_score hw hs hy hmfe
  rw [← hgram, mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_gram_of_identified hw hid),
    one_mulVec]

variable {r : Type*} [Fintype r]

/-- `A_n := (X̃'X̃)^{-1}𝓡_n'` has full column rank. -/
theorem injective_scoreMap_mulVec {Rn : Matrix r K ℝ}
    (hdet : IsUnit (Xtᵀ * Xt).det) (hR : Function.Injective ((Rn)ᵀ).mulVec) :
    Function.Injective (scoreMap Xt Rn).mulVec := by
  have h1 : ∀ w : K → ℝ, (Xtᵀ * Xt) *ᵥ ((Xtᵀ * Xt)⁻¹ *ᵥ w) = w := fun w => by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have h2 : ∀ u : r → ℝ, (scoreMap Xt Rn) *ᵥ u = (Xtᵀ * Xt)⁻¹ *ᵥ ((Rn)ᵀ *ᵥ u) := fun u => by
    rw [scoreMap, ← mulVec_mulVec]
  intro u u' h
  rw [h2, h2] at h
  refine hR ?_
  calc (Rn)ᵀ *ᵥ u = (Xtᵀ * Xt) *ᵥ ((Xtᵀ * Xt)⁻¹ *ᵥ ((Rn)ᵀ *ᵥ u)) := (h1 _).symm
    _ = (Xtᵀ * Xt) *ᵥ ((Xtᵀ * Xt)⁻¹ *ᵥ ((Rn)ᵀ *ᵥ u')) := by rw [h]
    _ = (Rn)ᵀ *ᵥ u' := h1 _

end ScoreRepresentation

section ScoreDischarge

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {W : ℕ → Type*}
variable {Dm : Type*} [Fintype Dm]

omit [(n : ℕ) → DecidableEq (O n)] [DecidableEq r] in
/-- The score representation and the full column rank of `A_n`, from the model,
identification, the full row rank of `𝓡_n` and Theorem 3(a). -/
theorem score_and_rank_of_jm
    {Sm : ∀ n, Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n)} {Xt : ∀ n, Matrix (O n) K ℝ}
    (hwithin : ∀ n, IsWithinMatrix (⨆ k, Sm n k) (Xop n) (Xt n))
    (hid : ∀ n, Multiway.Identified (⨆ k, Sm n k) (Xop n))
    {iota : ∀ n, EuclideanSpace ℝ (O n)} (hiota : ∀ n, iota n ∈ (⨆ k, Sm n k))
    {fe : ∀ n, Dm → EuclideanSpace ℝ (O n)} (hfe : ∀ n m, fe n m ∈ Sm n m)
    {yv : ∀ n, W n → EuclideanSpace ℝ (O n)} {ν : ∀ n, O n → W n → ℝ}
    {bhat : ∀ n, W n → (K → ℝ)} {β : ℕ → K → ℝ}
    (hmodel : ∀ n ω, yv n ω
      = Xop n (β n) + (∑ m, fe n m) + WithLp.toLp 2 (fun o => ν n o ω))
    (hJM : ∀ n ω, Multiway.IsAugSlope
      (Multiway.jmControls (iota n) (⨆ k, Sm n k) (Xop n)) (Xop n) (yv n ω) (bhat n ω))
    {Rn : ℕ → Matrix r K ℝ} (hR : ∀ n, Function.Injective ((Rn n)ᵀ).mulVec) :
    (∀ n ω, bhat n ω - β n
        = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
      ∧ (∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec) := by
  refine ⟨fun n ω => ?_, fun n => injective_scoreMap_mulVec
    (isUnit_det_gram_of_identified (hwithin n) (hid n)) (hR n)⟩
  simpa using score_representation (Sm := Sm n) (hwithin n) (hid n) (hiota n)
    (fun m => hfe n m) (hmodel n ω) (hJM n ω)

variable {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
variable [∀ n, MeasurableSpace (W n)]

/-- **Theorem 5(a) at `J = 1` for `β̂_JM`**, with the score representation and the rank of
`A_n` derived from Theorem 3. -/
theorem cltcluster_a_oneDimension_betaJM_of_jm
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    {Sm : ∀ n, Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n)} (Xt : ∀ n, Matrix (O n) K ℝ)
    (hwithin : ∀ n, IsWithinMatrix (⨆ k, Sm n k) (Xop n) (Xt n))
    (hid : ∀ n, Multiway.Identified (⨆ k, Sm n k) (Xop n))
    {iota : ∀ n, EuclideanSpace ℝ (O n)} (hiota : ∀ n, iota n ∈ (⨆ k, Sm n k))
    {fe : ∀ n, Dm → EuclideanSpace ℝ (O n)} (hfe : ∀ n m, fe n m ∈ Sm n m)
    {yv : ∀ n, W n → EuclideanSpace ℝ (O n)}
    (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (hmodel : ∀ n ω, yv n ω
      = Xop n (β n) + (∑ m, fe n m) + WithLp.toLp 2 (fun o => ν n o ω))
    (hJM : ∀ n ω, Multiway.IsAugSlope
      (Multiway.jmControls (iota n) (⨆ k, Sm n k) (Xop n)) (Xop n) (yv n ω) (bhat n ω))
    (hR : ∀ n, Function.Injective ((Rn n)ᵀ).mulVec)
    (g : ∀ n, O n → Gp n)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ g n o = g n o')
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n) (Om n))
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n) = Om n o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (Gb : ℕ → ℕ) (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * (B * Cnu / Real.sqrt (lmin n))) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  obtain ⟨hscore, hA⟩ :=
    score_and_rank_of_jm hwithin hid hiota hfe hmodel hJM (Rn := Rn) hR
  exact cltcluster_a_oneDimension_betaJM μ Xt Om Rn ν bhat β g Dv hshare hscore hA lmin hlmin
    hfloor hOm hmean B Cnu hB0 hCnu0 hB hnu Gb hGb hrate b hb s

/-- **Theorem 5(a) at general `J` for `β̂_JM`**, with the score representation and the rank
of `A_n` derived from Theorem 3. -/
theorem cltcluster_a_general_betaJM_of_jm
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    {Sm : ∀ n, Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n)} (Xt : ∀ n, Matrix (O n) K ℝ)
    (hwithin : ∀ n, IsWithinMatrix (⨆ k, Sm n k) (Xop n) (Xt n))
    (hid : ∀ n, Multiway.Identified (⨆ k, Sm n k) (Xop n))
    {iota : ∀ n, EuclideanSpace ℝ (O n)} (hiota : ∀ n, iota n ∈ (⨆ k, Sm n k))
    {fe : ∀ n, Dm → EuclideanSpace ℝ (O n)} (hfe : ∀ n m, fe n m ∈ Sm n m)
    {yv : ∀ n, W n → EuclideanSpace ℝ (O n)}
    (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (hmodel : ∀ n ω, yv n ω
      = Xop n (β n) + (∑ m, fe n m) + WithLp.toLp 2 (fun o => ν n o ω))
    (hJM : ∀ n ω, Multiway.IsAugSlope
      (Multiway.jmControls (iota n) (⨆ k, Sm n k) (Xop n)) (Xop n) (yv n ω) (bhat n ω))
    (hR : ∀ n, Function.Injective ((Rn n)ᵀ).mulVec)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (lmin : ℕ → ℝ) (hlmin : ∀ n, 0 < lmin n)
    (hfloor : ∀ n, lmin n • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n) (Om n))
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n) = Om n o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  obtain ⟨hscore, hA⟩ :=
    score_and_rank_of_jm hwithin hid hiota hfe hmodel hJM (Rn := Rn) hR
  exact cltcluster_a_general_betaJM μ Xt Om Rn ν bhat β Dv hscore hA lmin hlmin hfloor hOm
    hmean B Cnu hB0 hCnu0 hB hnu Dn hDn1 hDnN hdeg hrate b hb s

/-- **Theorem 5(b) at general `J` for `β̂_JM`**, with the score representation and the rank
of `A_n` derived from Theorem 3. -/
theorem cltcluster_b_general_betaJM_of_jm
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    {Sm : ∀ n, Dm → Submodule ℝ (EuclideanSpace ℝ (O n))}
    {Xop : ∀ n, (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (O n)} (Xt : ∀ n, Matrix (O n) K ℝ)
    (hwithin : ∀ n, IsWithinMatrix (⨆ k, Sm n k) (Xop n) (Xt n))
    (hid : ∀ n, Multiway.Identified (⨆ k, Sm n k) (Xop n))
    {iota : ∀ n, EuclideanSpace ℝ (O n)} (hiota : ∀ n, iota n ∈ (⨆ k, Sm n k))
    {fe : ∀ n, Dm → EuclideanSpace ℝ (O n)} (hfe : ∀ n m, fe n m ∈ Sm n m)
    {yv : ∀ n, W n → EuclideanSpace ℝ (O n)}
    (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (hmodel : ∀ n ω, yv n ω
      = Xop n (β n) + (∑ m, fe n m) + WithLp.toLp 2 (fun o => ν n o ω))
    (hJM : ∀ n ω, Multiway.IsAugSlope
      (Multiway.jmControls (iota n) (⨆ k, Sm n k) (Xop n)) (Xop n) (yv n ω) (bhat n ω))
    (hR : ∀ n, Function.Injective ((Rn n)ᵀ).mulVec)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
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
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  obtain ⟨hscore, hA⟩ :=
    score_and_rank_of_jm hwithin hid hiota hfe hmodel hJM (Rn := Rn) hR
  exact cltcluster_b_general_betaJM μ Xt Om Rn ν bhat β Dv hscore hA lmin hlmin hfloor hOm
    hmean B C4 hB0 hC40 hB hint4 hfour Dn hDn1 hDnN hdeg hrate b hb s

end ScoreDischarge

section ScoreWitness

open Matrix
open scoped RealInnerProductSpace

namespace ScoreWitness

/-- `ι_n`, the single fixed-effect direction: `(1,0)'`. -/
noncomputable def wiota : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- `𝒮_1 = col(Δ_1) = span(ι_n)`, a nonzero proper subspace of `ℝ²`. -/
noncomputable def wS : Fin 1 → Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := fun _ => ℝ ∙ wiota

/-- The raw regressor column `X = (1,1)'`, not orthogonal to `𝒮`. -/
noncomputable def wx : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 1]

/-- `X : ℝ¹ → ℝ²`, `a ↦ aX`. -/
noncomputable def wXop : (Fin 1 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun a := a 0 • wx
  map_add' := fun a b => by simp [add_smul]
  map_smul' := fun c a => by simp [mul_smul]

/-- `X̃ = Q_[Δ]X = (0,1)'`. -/
def wXt : Matrix (Fin 2) (Fin 1) ℝ := ![![0], ![1]]

/-- The disturbance `ν = (3,5)'`. -/
noncomputable def wnu : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![3, 5]

theorem wS_iSup : (⨆ k, wS k) = ℝ ∙ wiota := iSup_const

theorem norm_wiota : ‖wiota‖ = 1 := by
  rw [EuclideanSpace.norm_eq]; simp [wiota, Fin.sum_univ_two]

theorem inner_wiota (u : EuclideanSpace ℝ (Fin 2)) : ⟪wiota, u⟫ = u 0 := by
  simp [PiLp.inner_apply, RCLike.inner_apply, wiota, Fin.sum_univ_two]

/-- The within transformation of this design is `Q_[Δ]u = u − u_1ι_n`. -/
theorem wjointWithin (u : EuclideanSpace ℝ (Fin 2)) :
    Multiway.jointWithin (⨆ k, wS k) u = u - (u 0) • wiota := by
  rw [wS_iSup, Multiway.jointWithin_apply, Submodule.starProjection_singleton, norm_wiota,
    inner_wiota]
  norm_num

theorem wIsWithinMatrix : IsWithinMatrix (⨆ k, wS k) wXop wXt := by
  intro a
  funext i
  rw [wjointWithin]
  fin_cases i <;>
    simp [wXop, wx, wXt, wiota, Matrix.mulVec, dotProduct]

theorem wIdentified : Multiway.Identified (⨆ k, wS k) wXop := by
  intro a ha
  rw [wS_iSup, Submodule.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ := ha
  have h1 : (c • wiota) 1 = (wXop a) 1 := by rw [hc]
  simp only [wXop, wx, wiota] at h1
  funext k
  fin_cases k
  simpa using h1.symm

theorem wiota_mem : wiota ∈ (⨆ k, wS k) := by
  rw [wS_iSup]; exact Submodule.mem_span_singleton_self _

theorem wfe_mem : ∀ m : Fin 1, wiota ∈ wS m := fun _ => Submodule.mem_span_singleton_self wiota

/-- `y = Xβ + Δα + ν` at `β = 2`, `Δα = ι_n` and `ν = (3,5)'`, so `y = (6,7)'`. -/
noncomputable def wy : EuclideanSpace ℝ (Fin 2) :=
  wXop ![2] + (∑ _m : Fin 1, wiota) + wnu

/-- `β̂_JM = 7` solves the joint-projection normal equations at `y`. -/
theorem wIsAugSlope :
    Multiway.IsAugSlope (Multiway.jmControls wiota (⨆ k, wS k) wXop) wXop wy ![7] := by
  have hres : wy - wXop ![7] = (-1 : ℝ) • wiota := by
    ext i
    fin_cases i <;> simp [wy, wXop, wx, wnu, wiota] <;> norm_num
  refine ⟨wy - wXop ![7], ?_, ?_, ?_⟩
  · rw [hres, Multiway.jmControls]
    exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · intro a; simp
  · intro v _; simp

/-- The hypotheses of `score_representation` hold on this two-observation design. -/
theorem score_representation_witness :
    (![7] : Fin 1 → ℝ) - ![2]
      = (wXtᵀ * wXt)⁻¹ *ᵥ (wXtᵀ *ᵥ (WithLp.ofLp wnu)) :=
  score_representation (D := Fin 1) (Sm := wS) wIsWithinMatrix wIdentified wiota_mem
    wfe_mem rfl wIsAugSlope

/-- In this example `β̂_JM − β ≠ 0`, and the fixed-effect direction is nonzero and annihilated
by the within transformation. -/
theorem score_representation_witness_nondegenerate :
    ((![7] : Fin 1 → ℝ) - ![2]) ≠ 0
      ∧ Multiway.jointWithin (⨆ k, wS k) wiota = 0
      ∧ wiota ≠ (0 : EuclideanSpace ℝ (Fin 2))
      ∧ (∑ _m : Fin 1, wiota) ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
  have hne : wiota ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
    intro h
    have := congrFun (congrArg WithLp.ofLp h) 0
    simp [wiota] at this
  refine ⟨?_, ?_, hne, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · rw [wjointWithin]
    have h0 : wiota 0 = (1 : ℝ) := by simp [wiota]
    rw [h0, one_smul, sub_self]
  · simpa using hne

end ScoreWitness

end ScoreWitness

section SecondMoment

open Matrix

/-- The second-moment matrix of the disturbance, `Ω_{oo'} = E[ν_oν_{o'}]`. -/
noncomputable def secondMoment {O W : Type*} [MeasurableSpace W] (μ : Measure W)
    (ν : O → W → ℝ) : Matrix O O ℝ := fun o o' => ∫ ω, ν o ω * ν o' ω ∂μ

/-- At `Ω_n := secondMoment (μ n) (ν n)` the hypothesis `hOm` of the `betaJM` theorems holds
by `rfl`. -/
theorem secondMoment_spec {O W : Type*} [MeasurableSpace W] (μ : Measure W) (ν : O → W → ℝ) :
    ∀ o o', ∫ ω, ν o ω * ν o' ω ∂μ = secondMoment μ ν o o' := fun _ _ => rfl

end SecondMoment

/-! ## The Cramér–Wold step

`cltcluster_a_unconditional_vector_of_design` gives `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)`
under the full measure `P`, with `N(0, I_r)` Mathlib's `stdGaussian (EuclideanSpace ℝ r)`. It
applies `TendstoInDistribution.of_inner`, with `map_inner_stdGaussian` identifying
`⟪Z,t⟫ ∼ N(0,‖t‖²)` for `Z ∼ N(0,I)`; the direction `t = 0` is handled separately. The
hypothesis `hfrozen` is indexed by the unit direction `b`, and `inner_restrictedStat` identifies
the scalar statistic `b'𝒱_n^{-1/2}𝓡_n(β̂_JM − β)` with `⟪·, b⟫` of the vector statistic. -/


section CramerWold

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- Two limits with the same law are interchangeable in a convergence-in-distribution
statement. -/
theorem tendstoInDistribution_congr_law {ι F Ω Ω' Ω'' : Type*} {mF : MeasurableSpace F}
    [TopologicalSpace F] [OpensMeasurableSpace F] {l : Filter ι}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mΩ'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {X : ι → Ω → F} {Z : Ω' → F} {V : Ω'' → F}
    (h : TendstoInDistribution X l Z (fun _ => P) μ')
    (hV : AEMeasurable V μ'') (hlaw : μ''.map V = μ'.map Z) :
    TendstoInDistribution X l V (fun _ => P) μ'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hV
  tendsto := by
    rw! [hlaw]
    exact h.tendsto

/-- `⟪Z, t⟫ ∼ N(0, ‖t‖²)` when `Z ∼ N(0, I)`. -/
theorem map_inner_stdGaussian (t : E) :
    (stdGaussian E).map (fun x => ⟪x, t⟫) = gaussianReal 0 (‖t‖ ^ 2).toNNReal := by
  have hfun : (fun x : E => ⟪x, t⟫) = fun x : E => (innerSL ℝ t) x := by
    funext x; exact (real_inner_comm x t).symm
  rw [hfun]
  have hgl : HasGaussianLaw (fun x : E => (innerSL ℝ t) x) (stdGaussian E) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun (innerSL ℝ t)
  rw [hgl.map_eq_gaussianReal]
  congr 1
  · rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]
  · rw [variance_dual_stdGaussian, innerSL_apply_norm]

/-- The Cramér–Wold device, `⟶ᵈ N(0, I_r)` from the scalar limits in every unit direction. -/
theorem tendstoInDistribution_stdGaussian_of_unit_directions
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Wv : ℕ → Ω → E} (hmeas : ∀ n, AEMeasurable (Wv n) P)
    (hdir : ∀ b : E, ‖b‖ = 1 → TendstoInDistribution (fun (n : ℕ) ω => ⟪Wv n ω, b⟫) atTop
      (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1)) :
    TendstoInDistribution Wv atTop (id : E → E) (fun _ => P) (stdGaussian E) := by
  refine TendstoInDistribution.of_inner (by fun_prop) hmeas ?_
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [inner_zero_right, id_eq]
    refine tendstoInDistribution_congr_law
      (tendstoInDistribution_const (Z := fun _ : Ω => (0 : ℝ)) (l := atTop) aemeasurable_const)
      aemeasurable_const ?_
    simp [Measure.map_const]
  · have hc : (0 : ℝ) < ‖t‖ := norm_pos_iff.mpr ht
    have hb : ‖(‖t‖⁻¹ • t : E)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
    have hEq : (fun (n : ℕ) (ω : Ω) => ⟪Wv n ω, t⟫)
        = fun (n : ℕ) (ω : Ω) => ‖t‖ * ⟪Wv n ω, (‖t‖⁻¹ • t : E)⟫ := by
      funext n ω
      rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    have hscal := (hdir _ hb).continuous_comp
      (g := fun x : ℝ => ‖t‖ * x) (by fun_prop)
    rw [hEq]
    refine tendstoInDistribution_congr_law hscal (by fun_prop) ?_
    have hL : (gaussianReal 0 1).map (fun x : ℝ => ‖t‖ * x)
        = gaussianReal 0 (‖t‖ ^ 2).toNNReal := by
      rw [show (fun x : ℝ => ‖t‖ * x) = (‖t‖ * ·) from rfl, gaussianReal_map_const_mul]
      simp [Real.toNNReal_of_nonneg (sq_nonneg ‖t‖)]
    have hid : ((fun x : ℝ => ‖t‖ * x) ∘ id) = fun x : ℝ => ‖t‖ * x := rfl
    rw [hid, hL]
    simp only [id_eq]
    rw [map_inner_stdGaussian]

end CramerWold

section VectorStatistic

open Matrix
open scoped RealInnerProductSpace

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {rr : Type*} [Fintype rr] [DecidableEq rr]

omit [DecidableEq rr] in
/-- `b'b = 1` is `‖b‖ = 1`. -/
theorem dotProduct_self_ofLp (b : EuclideanSpace ℝ rr) (hb : ‖b‖ = 1) :
    (WithLp.ofLp b) ⬝ᵥ (WithLp.ofLp b) = 1 := by
  rw [← inner_euclideanSpace_eq_dotProduct, real_inner_self_eq_norm_sq, hb, one_pow]

/-- The vector statistic `𝒱_n^{-1/2}𝓡_n(β̂_JM − β)`. -/
noncomputable def restrictedStat (Xt : Matrix O K ℝ) (Om : Matrix O O ℝ) (Rn : Matrix rr K ℝ)
    (d : K → ℝ) : EuclideanSpace ℝ rr :=
  WithLp.toLp 2 ((sqrtPD (restrictedVar Xt Om Rn))⁻¹ *ᵥ (Rn *ᵥ d))

omit [DecidableEq O] in
/-- The scalar statistic of the `betaJM` theorems is `⟪·, b⟫` of the vector statistic. -/
theorem inner_restrictedStat (Xt : Matrix O K ℝ) (Om : Matrix O O ℝ) (Rn : Matrix rr K ℝ)
    (d : K → ℝ) (b : EuclideanSpace ℝ rr) :
    ⟪restrictedStat Xt Om Rn d, b⟫
      = (WithLp.ofLp b) ⬝ᵥ ((sqrtPD (restrictedVar Xt Om Rn))⁻¹ *ᵥ (Rn *ᵥ d)) := by
  rw [inner_euclideanSpace_eq_dotProduct, dotProduct_comm]
  rfl

end VectorStatistic

section DesignCramerWold

open scoped RealInnerProductSpace

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The unconditional cluster CLT in vector form.** If the scalar statistic `⟪W_n, b⟫`
converges to `N(0,1)` under `ℙ_ω` for every unit `b` and almost every `ω` (`hfrozen`), then
`W_n ⟶ᵈ N(0, I_r)` under `P`. -/
theorem cltcluster_a_unconditional_vector_of_design
    {rr : Type*} [Fintype rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    {γ : Type*} [MeasurableSpace γ] [MeasurableEq γ]
    {D : ℕ → Ω → γ} (hD : ∀ n, Measurable[𝒟] (D n))
    {Fv : ℕ → γ → Ω → EuclideanSpace ℝ rr}
    (hF : ∀ n, Measurable (Function.uncurry (Fv n)))
    {Wv : ℕ → Ω → EuclideanSpace ℝ rr} (hW : ∀ n ω, Wv n ω = Fv n (D n ω) ω)
    (hfrozen : ∀ b : EuclideanSpace ℝ rr, ‖b‖ = 1 → ∀ᵐ ω ∂P,
      TendstoInDistribution (m := fun _ : ℕ => mΩ)
        (fun (n : ℕ) (y : Ω) => ⟪Fv n (D n ω) y, b⟫) atTop (id : ℝ → ℝ)
        (fun _ => condExpKernel P 𝒟 ω) (gaussianReal 0 1)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ) Wv atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hWm : ∀ n, Measurable (Wv n) := by
    intro n
    have heq : Wv n = fun ω => Fv n (D n ω) ω := funext (hW n)
    rw [heq]
    exact (hF n).comp (((hD n).mono h𝒟 le_rfl).prodMk measurable_id)
  refine tendstoInDistribution_stdGaussian_of_unit_directions
    (fun n => (hWm n).aemeasurable) ?_
  intro b hb
  refine cltcluster_a_unconditional_of_design h𝒟 P hD
    (F := fun n g y => ⟪Fv n g y, b⟫) ?_ (fun n ω => by rw [hW n ω]) (hfrozen b hb)
  intro n
  exact (by fun_prop : Measurable fun v : EuclideanSpace ℝ rr => ⟪v, b⟫).comp (hF n)

end DesignCramerWold

section CramerWoldWitness

open scoped RealInnerProductSpace

namespace CWWitness

/-- The example space, `ℝ²` under the standard Gaussian. -/
abbrev wE : Type := EuclideanSpace ℝ (Fin 2)

/-- Every unit direction of `N(0,I₂)` is `N(0,1)`. -/
theorem wdir (b : wE) (hb : ‖b‖ = 1) :
    TendstoInDistribution (fun (_ : ℕ) (ω : wE) => ⟪ω, b⟫) atTop (id : ℝ → ℝ)
      (fun _ => stdGaussian wE) (gaussianReal 0 1) := by
  refine tendstoInDistribution_congr_law
    (tendstoInDistribution_const (Z := fun ω : wE => ⟪ω, b⟫) (l := atTop) (by fun_prop))
    aemeasurable_id ?_
  rw [Measure.map_id, map_inner_stdGaussian, hb]
  norm_num

/-- The hypotheses of the Cramér–Wold step hold for the standard Gaussian on `ℝ²`. -/
theorem cramerWold_witness :
    TendstoInDistribution (fun (_ : ℕ) (ω : wE) => ω) atTop (id : wE → wE)
      (fun _ => stdGaussian wE) (stdGaussian wE) :=
  tendstoInDistribution_stdGaussian_of_unit_directions (fun _ => aemeasurable_id) wdir

/-- The assembled limit is two-dimensional and nondegenerate in both coordinates. -/
theorem cramerWold_witness_nondegenerate :
    Module.finrank ℝ wE = 2
      ∧ (stdGaussian wE).map (fun x => ⟪x, (EuclideanSpace.single 0 (1:ℝ) : wE)⟫)
          = gaussianReal 0 1
      ∧ (stdGaussian wE).map (fun x => ⟪x, (EuclideanSpace.single 1 (1:ℝ) : wE)⟫)
          = gaussianReal 0 1 := by
  refine ⟨by simp, ?_, ?_⟩ <;>
  · rw [map_inner_stdGaussian, PiLp.norm_single]
    norm_num

end CWWitness

end CramerWoldWitness


/-! ### An example for `cltcluster_a_unconditional_vector_of_design` at `r = 1`

This reuses the `DesignWitness` model, with its nontrivial design σ-field, and adds the vector
statistic `FdesV` and the per-direction `hfrozen`. Each unit `b` of `EuclideanSpace ℝ (Fin 1)`
has `(b_0)² = 1`. -/


section DesignVectorWitness

open scoped RealInnerProductSpace

namespace DesignWitness

/-- The vector statistic at `r = 1`. -/
noncomputable def FdesV (n : ℕ) (g : ℝ) (y : DOmg) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 ![Fdes n g y]

theorem meas_FdesV (n : ℕ) : Measurable (Function.uncurry (FdesV n)) := by
  have h : Function.uncurry (FdesV n)
      = (fun x : ℝ => (WithLp.toLp 2 ![x] : EuclideanSpace ℝ (Fin 1)))
        ∘ Function.uncurry (Fdes n) := rfl
  rw [h]
  exact (by fun_prop : Measurable
    (fun x : ℝ => (WithLp.toLp 2 ![x] : EuclideanSpace ℝ (Fin 1)))).comp (meas_Fdes n)

theorem inner_FdesV (n : ℕ) (g : ℝ) (y : DOmg) (b : EuclideanSpace ℝ (Fin 1)) :
    ⟪FdesV n g y, b⟫ = b 0 * Fdes n g y := by
  simp [FdesV, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem sq_coord_of_norm_one {b : EuclideanSpace ℝ (Fin 1)} (hb : ‖b‖ = 1) :
    (b 0) ^ 2 = 1 := by
  have h := dotProduct_self_ofLp b hb
  simpa [dotProduct, sq] using h

theorem hfrozenV (b : EuclideanSpace ℝ (Fin 1)) (hb : ‖b‖ = 1) :
    ∀ᵐ ω ∂Pdes, TendstoInDistribution
      (m := fun _ : ℕ => (inferInstance : MeasurableSpace DOmg))
      (fun (n : ℕ) (y : DOmg) => ⟪FdesV n (ddes n ω) y, b⟫) atTop (id : ℝ → ℝ)
      (fun _ => condExpKernel Pdes Ddes ω) (gaussianReal 0 1) := by
  filter_upwards [map_snd_condExpKernel] with ω hω
  have hm : ∀ n : ℕ, Measurable (fun y : DOmg => ⟪FdesV n (ddes n ω) y, b⟫) := by
    intro n
    simp only [inner_FdesV]
    unfold Fdes
    fun_prop
  have hlaw : ∀ n : ℕ,
      Measure.map (fun y : DOmg => ⟪FdesV n (ddes n ω) y, b⟫) (condExpKernel Pdes Ddes ω)
        = gaussianReal 0 1 := by
    intro n
    have hcomp : (fun y : DOmg => ⟪FdesV n (ddes n ω) y, b⟫)
        = (fun x : ℝ => b 0 * x) ∘ (fun y : DOmg => Fdes n (ddes n ω) y) := by
      funext y; exact inner_FdesV n (ddes n ω) y b
    have hmF : Measurable (fun y : DOmg => Fdes n (ddes n ω) y) := by unfold Fdes; fun_prop
    rw [hcomp, ← Measure.map_map (by fun_prop) hmF, map_Fdes_frozen hω n,
      gaussianReal_map_const_mul (b 0)]
    congr 1
    · ring
    · rw [mul_one]
      refine NNReal.coe_injective ?_
      simpa using sq_coord_of_norm_one hb
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hm n).aemeasurable)
    aemeasurable_id fun t => ?_
  rw [Measure.map_id]
  simp only [hlaw]
  exact tendsto_const_nhds

/-- The hypotheses of `cltcluster_a_unconditional_vector_of_design` hold on this model. -/
theorem cltcluster_a_unconditional_vector_design_witness :
    TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace DOmg))
      (fun (n : ℕ) (ω : DOmg) => FdesV n (ddes n ω) ω) atTop
      (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (fun _ => Pdes)
      (stdGaussian (EuclideanSpace ℝ (Fin 1))) :=
  cltcluster_a_unconditional_vector_of_design Ddes_le Pdes meas_ddes meas_FdesV
    (fun _ _ => rfl) hfrozenV

end DesignWitness

end DesignVectorWitness

/-! ## The `betaJM` limit laws with a random design

The conditional theorems `cltcluster_a_oneDimension_betaJM`, `cltcluster_a_general_betaJM` and
`cltcluster_b_general_betaJM` are instantiated at `W n := Ω`, `μ n := condExpKernel P 𝒟 ω` and
the design frozen at `ω`, with the hypotheses read under `ℙ_ω` at `P`-almost every `ω`; the
conclusion is a limit law under `P`. The design is frozen entry by entry
(`ae_ae_eq_frozen_design`). Each hypothesis is a single `∀ᵐ ω ∂P` with the quantifiers over `n`
inside, and the dependency graph under `ℙ_ω` is quantified existentially inside the `∀ᵐ`. The
binders `hXtD`, `hOmD` make the design `𝒟`-measurable, and `hWm` is measurability of the
statistic. -/

section FrozenDesign

open Multiway.CLTMartingale.CondD
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- A `𝒟`-measurable design matrix is
`ℙ_ω`-almost surely equal to its value at `ω`, for every `n`, by
`CLTMartingale.CondD.ae_ae_eq_condExpKernel` applied to each entry. -/
theorem ae_ae_eq_frozen_design (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] {K : Type*} [Fintype K]
    {Xt : ∀ n, Ω → Matrix (O n) K ℝ} {Om : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o') :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ y ∂(condExpKernel P 𝒟 ω), Xt n y = Xt n ω ∧ Om n y = Om n ω := by
  refine ae_all_iff.2 fun n => ?_
  have h1 : ∀ᵐ ω ∂P, ∀ p : O n × K, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Xt n y p.1 p.2 = Xt n ω p.1 p.2 :=
    ae_all_iff.2 fun p => ae_ae_eq_condExpKernel h𝒟 P (hXtD n p.1 p.2)
  have h2 : ∀ᵐ ω ∂P, ∀ p : O n × O n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Om n y p.1 p.2 = Om n ω p.1 p.2 :=
    ae_all_iff.2 fun p => ae_ae_eq_condExpKernel h𝒟 P (hOmD n p.1 p.2)
  filter_upwards [h1, h2] with ω hω1 hω2
  filter_upwards [ae_all_iff.2 hω1, ae_all_iff.2 hω2] with y hy1 hy2
  exact ⟨Matrix.ext fun o a => hy1 (o, a), Matrix.ext fun o o' => hy2 (o, o')⟩

/-- If the statistic is `ℙ_ω`-almost surely equal to a frozen form `Wfr` whose conditional
limit law is `N(0,1)` for almost every `ω`, then the statistic converges to `N(0,1)` under `P`. -/
theorem cltcluster_a_unconditional_of_frozen_stat
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    {W : ℕ → Ω → ℝ} (hWm : ∀ n, Measurable (W n))
    {Wfr : Ω → ℕ → Ω → ℝ}
    (hfrz : ∀ᵐ ω ∂P, ∀ n : ℕ, W n =ᵐ[condExpKernel P 𝒟 ω] Wfr ω n)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mΩ) (Wfr ω) atTop
      (id : ℝ → ℝ) (fun _ => condExpKernel P 𝒟 ω) (gaussianReal 0 1)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ) W atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  refine tendstoInDistribution_of_tendsto_condCharFunD h𝒟 P
    (fun n => (hWm n).aemeasurable) aemeasurable_id fun t => ?_
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, condCharFunD 𝒟 P (W n) t ω
      = charFun (@Measure.map Ω ℝ mΩ _ (W n) (condExpKernel P 𝒟 ω)) t :=
    ae_all_iff.2 fun n => condCharFunD_eq_charFun_condExpKernel h𝒟 P (hWm n) t
  filter_upwards [hall, hfrz, hfrozen] with ω hω hfr hcl
  have h : Tendsto (fun n : ℕ => charFun
      (@Measure.map Ω ℝ mΩ _ (Wfr ω n) (condExpKernel P 𝒟 ω)) t) atTop
      (𝓝 (charFun ((gaussianReal 0 1).map (id : ℝ → ℝ)) t)) := hcl.tendsto_charFun t
  refine Tendsto.congr (fun n => ?_) h
  rw [hω n, Measure.map_congr (hfr n)]

/-- **Theorem 5(a) at `J = 1`, for `β̂_JM`, under the full measure with a random design.**
The conclusion is `b'𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0,1)` under `P`, with `X̃_n`, `Ω_n`, the
cluster map, `Ḡ_n` and `λ_min(Ω_n)` functions of `ω`, and the hypotheses of
`cltcluster_a_oneDimension_betaJM` read under `ℙ_ω := condExpKernel P 𝒟 ω` almost surely. -/
theorem cltcluster_a_oneDimension_betaJM_unconditional
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, Ω → O n → Gp n)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Gb : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1)
    (hWm : ∀ n, Measurable fun y =>
      b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n))))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ g n ω o = g n ω o')
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hGb : ∀ᵐ ω ∂P, ∀ n γ, (cluster (g n ω) γ).card ≤ Gb n ω)
    (hrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) * (B * Cnu / Real.sqrt (lmin n ω)))
      atTop (𝓝 0)) :
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
  · filter_upwards [hdep, hA, hlmin, hfloor, hOmeq, hmean, hB, hGb, hrate]
      with ω hdepω hAω hlminω hfloorω hOmω hmeanω hBω hGbω hrateω
    obtain ⟨Dv, hDv⟩ := hdepω
    have hPD : ∀ n, (scoreVar (Xt n ω) (Om n ω)).PosDef := fun n =>
      Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlminω n)) (hfloorω n)
    refine cltcluster_a_oneDimension_tendstoInDistribution
      (Ω := fun _ => Ω) (fun _ => condExpKernel P 𝒟 ω)
      (fun n => scoreArray (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b) (ν n))
      (fun n => g n ω)
      (fun n => scoreArrayDepGraph (Dv n) (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b))
      (fun n o o' => hDv n o o')
      (fun n => B * Cnu / Real.sqrt (lmin n ω)) (fun n => Gb n ω)
      (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ hGbω ?_ ?_ hrateω
    · exact fun n o y => abs_scoreArray_le (hPD n) (hAω n) (hlminω n) (hfloorω n) hB0
        (hBω n) (hnu n) hb o y
    · exact fun n o => integral_scoreArray (fun o => hmeanω n o) (Xt n ω) _ o
    · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hAω n)
        (fun o => (Dv n).meas o) (hnu n) (hOmω n) hb

/-- **Theorem 5(a) at general `J`, for `β̂_JM`, under the full measure with a random
design.** This is `cltcluster_a_general_betaJM` read at the frozen design, with the degree bound
`hdeg` inside `hdep`. -/
theorem cltcluster_a_general_betaJM_unconditional
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
      Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
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
    have hacc : Tendsto (fun n =>
        accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0) :=
      tendsto_accumRate hDn1ω hDnNω hrateω
    have hsec : Tendsto (fun n =>
        secondRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0) :=
      tendsto_secondRate hDn1ω hlminω hrateω
    refine cltcluster_a_general_tendstoInDistribution
      (Ω := fun _ => Ω) (fun _ => condExpKernel P 𝒟 ω)
      (fun n => scoreArray (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b) (ν n))
      (fun n => scoreArrayDepGraph (Dv n) (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b))
      (fun n => B * Cnu / Real.sqrt (lmin n ω)) (fun n => Dn n ω + 1)
      (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun n o y => abs_scoreArray_le (hPD n) (hAω n) (hlminω n) (hfloorω n) hB0
        (hBω n) (hnu n) hb o y
    · intro n o
      rw [nbhd_scoreArrayDepGraph]
      exact hdegω n o
    · exact fun n o => integral_scoreArray (fun o => hmeanω n o) (Xt n ω) _ o
    · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hAω n)
        (fun o => (Dv n).meas o) (hnu n) (hOmω n) hb
    · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
        (by simpa using hacc.const_mul (8 * B ^ 4 * Cnu ^ 4))
      exact firstRate_le (hDn1ω n) (hlminω n)
    · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
        (by simpa using hsec.const_mul (4 * B ^ 3 * Cnu ^ 3))
      exact secondRate_le (hDn1ω n) (hlminω n) hB0 hCnu0

/-- **Theorem 5(b) at general `J`, for `β̂_JM`, under the full measure with a random
design.** This is `cltcluster_b_general_betaJM` read at the frozen design, with the fourth-moment
bound `∫ν_o⁴ ≤ C₄⁴` under `ℙ_ω`. -/
theorem cltcluster_b_general_betaJM_unconditional
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
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
  · filter_upwards [hdep, hA, hlmin, hfloor, hOmeq, hmean, hB, hint4, hfour, hDn1, hDnN,
      hrate] with ω hdepω hAω hlminω hfloorω hOmω hmeanω hBω hint4ω hfourω hDn1ω hDnNω hrateω
    obtain ⟨Dv, hdegω⟩ := hdepω
    have hPD : ∀ n, (scoreVar (Xt n ω) (Om n ω)).PosDef := fun n =>
      Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one (hlminω n)) (hfloorω n)
    have hacc : Tendsto (fun n =>
        accumRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0) :=
      tendsto_accumRate hDn1ω hDnNω hrateω
    have hsec : Tendsto (fun n =>
        secondRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0) :=
      tendsto_secondRate hDn1ω hlminω hrateω
    refine cltcluster_b_general_tendstoInDistribution
      (Ω := fun _ => Ω) (fun _ => condExpKernel P 𝒟 ω)
      (fun n => scoreArray (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b) (ν n))
      (fun n => scoreArrayDepGraph (Dv n) (Xt n ω) (steinWeight (Xt n ω) (Om n ω) (Rn n) b))
      (fun n => B * C4 / Real.sqrt (lmin n ω)) (fun n => Dn n ω + 1)
      (fun n => div_pos (mul_pos hB0 hC40) (Real.sqrt_pos.mpr (hlminω n)))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun n o => integrable_scoreArray_pow_four (hint4ω n) (Xt n ω) _ o
    · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hAω n) (hlminω n) (hfloorω n)
        hB0.le hC40.le (hBω n) (hint4ω n) (hfourω n) hb o
    · intro n o
      rw [nbhd_scoreArrayDepGraph]
      exact hdegω n o
    · exact fun n o => integral_scoreArray (fun o => hmeanω n o) (Xt n ω) _ o
    · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hAω n)
        (fun o => (Dv n).meas o) (hint4ω n) (hOmω n) hb
    · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
        (by simpa using hacc.const_mul (8 * B ^ 4 * C4 ^ 4))
      exact firstRate_le (hDn1ω n) (hlminω n)
    · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
        (by simpa using hsec.const_mul (4 * B ^ 3 * C4 ^ 3))
      exact secondRate_le (hDn1ω n) (hlminω n) hB0.le hC40.le

end FrozenDesign


/-! ### An example with a random design and a growing array

On `Ω = Bool × ((ℕ × ℕ) → Bool)` the first coordinate is a fair design coin and the second an
independent i.i.d. fair coin for every `(n, o)`; `𝒟 = σ(design coin)` is a proper sub-σ-field and `ℙ_ω ≠ P`. The conditional law
of the disturbance coordinate is identified as the product measure through
`Measure.eq_infinitePi`, checking the countably many measurable boxes with `ae_all_iff` and
`condExp_indep_eq`. At index `n` there are `n+1` singleton clusters, one regressor
`X̃_n(ω) = ±ι_{n+1}` with the sign read off the design coin, `𝓡_n = I_1`, `Ω_n = I` and
`φ_n = (n+1)^{-1/2}`; the total conditional variance is `1` at every `n`. -/

section FrozenDesignWitness

namespace FrozenDesignWitness

open Multiway.Multilinear

/-- The disturbance coordinate: an i.i.d. fair coin per `(n,o)`. -/
abbrev Cw : Type := (ℕ × ℕ) → Bool
/-- The whole sample space: a design coin and the disturbance coins. -/
abbrev Aw : Type := Bool × Cw

noncomputable def P1 : Measure Cw := Measure.infinitePi (fun _ : ℕ × ℕ => coin)
instance : IsProbabilityMeasure P1 := by unfold P1; infer_instance
noncomputable def Pw : Measure Aw := coin.prod P1
instance : IsProbabilityMeasure Pw := by unfold Pw; infer_instance

example : StandardBorelSpace Aw := inferInstance
example : Nonempty Aw := inferInstance
example : Finite (Set Bool) := inferInstance
example (s : Finset (ℕ × ℕ)) : Finite (↥s → Set Bool) := inferInstance
example : Countable (Σ s : Finset (ℕ × ℕ), (↥s → Set Bool)) := inferInstance

set_option warn.classDefReducibility false in
def Dw : MeasurableSpace Aw := MeasurableSpace.comap Prod.fst inferInstance

theorem Dw_le : Dw ≤ (inferInstance : MeasurableSpace Aw) :=
  measurable_fst.comap_le

theorem map_snd_Pw : Measure.map (Prod.snd : Aw → Cw) Pw = P1 := by
  unfold Pw
  exact Measure.snd_prod

theorem indep_snd_Dw : IndepFun (Prod.snd : Aw → Cw) (Prod.fst : Aw → Bool) Pw := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_snd.aemeasurable
    measurable_fst.aemeasurable]
  have h2 : Measure.map (Prod.fst : Aw → Bool) Pw = coin := Measure.fst_prod
  rw [map_snd_Pw, h2]
  exact Measure.prod_swap

theorem condExpKernel_snd_preimage (A : Set Cw) (hA : MeasurableSet A) :
    ∀ᵐ ω ∂Pw, (condExpKernel Pw Dw ω).real (Prod.snd ⁻¹' A) = Pw.real (Prod.snd ⁻¹' A) := by
  have hs : MeasurableSet (Prod.snd ⁻¹' A : Set Aw) := measurable_snd hA
  have h1 := condExpKernel_ae_eq_condExp (m := Dw) (μ := Pw) Dw_le hs
  have hsm : StronglyMeasurable[MeasurableSpace.comap (Prod.snd : Aw → Cw) inferInstance]
      ((Prod.snd ⁻¹' A : Set Aw).indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator ⟨A, hA, rfl⟩
  have h2 := condExp_indep_eq (m₁ := MeasurableSpace.comap (Prod.snd : Aw → Cw) inferInstance)
    (m₂ := Dw) measurable_snd.comap_le Dw_le hsm indep_snd_Dw
  have h3 : ∫ y, (Prod.snd ⁻¹' A : Set Aw).indicator (fun _ => (1 : ℝ)) y ∂Pw
      = Pw.real (Prod.snd ⁻¹' A) := integral_indicator_one hs
  filter_upwards [h1, h2] with ω hω hω2
  rw [hω, hω2, h3]

/-- Extend a partial box to a full one. -/
def boxExt (s : Finset (ℕ × ℕ)) (t : ↥s → Set Bool) : (ℕ × ℕ) → Set Bool :=
  fun i => if h : i ∈ s then t ⟨i, h⟩ else Set.univ

theorem boxExt_meas (s : Finset (ℕ × ℕ)) (t : ↥s → Set Bool) (i : ℕ × ℕ) :
    MeasurableSet (boxExt s t i) := by
  unfold boxExt; split <;> exact trivial

theorem pi_boxExt (s : Finset (ℕ × ℕ)) (t : (ℕ × ℕ) → Set Bool) :
    Set.pi (↑s) t = Set.pi (↑s) (boxExt s (fun i => t (i : ℕ × ℕ))) := by
  refine Set.pi_congr rfl fun i hi => ?_
  have hi' : i ∈ s := hi
  simp [boxExt, hi']

theorem map_snd_condExpKernel :
    ∀ᵐ ω ∂Pw, Measure.map (Prod.snd : Aw → Cw) (condExpKernel Pw Dw ω) = P1 := by
  have hall : ∀ᵐ ω ∂Pw, ∀ p : Σ s : Finset (ℕ × ℕ), (↥s → Set Bool),
      (condExpKernel Pw Dw ω).real (Prod.snd ⁻¹' (Set.pi (↑p.1) (boxExt p.1 p.2)))
        = Pw.real (Prod.snd ⁻¹' (Set.pi (↑p.1) (boxExt p.1 p.2))) :=
    ae_all_iff.2 fun p =>
      condExpKernel_snd_preimage _ (MeasurableSet.pi (Finset.countable_toSet _)
        (fun i _ => boxExt_meas p.1 p.2 i))
  filter_upwards [hall] with ω hω
  rw [P1]
  refine Measure.eq_infinitePi (fun _ : ℕ × ℕ => coin) (fun s t ht => ?_)
  have hmeas : MeasurableSet (Set.pi (↑s) (boxExt s (fun i => t (i : ℕ × ℕ)))) :=
    MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => boxExt_meas s _ i)
  have heq := hω ⟨s, fun i => t (i : ℕ × ℕ)⟩
  have heq' : (condExpKernel Pw Dw ω)
      (Prod.snd ⁻¹' (Set.pi (↑s) (boxExt s (fun i => t (i : ℕ × ℕ)))))
      = Pw (Prod.snd ⁻¹' (Set.pi (↑s) (boxExt s (fun i => t (i : ℕ × ℕ))))) :=
    (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).1 heq
  have hstep : Measure.map (Prod.snd : Aw → Cw) (condExpKernel Pw Dw ω) (Set.pi (↑s) t)
      = P1 (Set.pi (↑s) t) := by
    rw [pi_boxExt s t, Measure.map_apply measurable_snd hmeas, heq',
      ← Measure.map_apply measurable_snd hmeas, map_snd_Pw]
  rw [hstep, P1]
  exact Measure.infinitePi_pi (fun _ : ℕ × ℕ => coin) (fun i _ => ht i)


/-! ### The unscaled fair signs on the disturbance coordinate -/

noncomputable def vSign (n : ℕ) (o : Fin (n + 1)) (z : Cw) : ℝ :=
  if z (n, o.val) then (1 : ℝ) else -1

noncomputable def uSign (n : ℕ) (o : Fin (n + 1)) (y : Aw) : ℝ := vSign n o y.2

theorem meas_vSign (n : ℕ) (o : Fin (n + 1)) : Measurable (vSign n o) :=
  (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
    (measurable_pi_apply (n, o.val))

theorem meas_uSign (n : ℕ) (o : Fin (n + 1)) : Measurable (uSign n o) :=
  (meas_vSign n o).comp measurable_snd

theorem abs_vSign_le (n : ℕ) (o : Fin (n + 1)) (z : Cw) : |vSign n o z| ≤ 1 := by
  unfold vSign; by_cases h : z (n, o.val) <;> simp [h]

theorem vSign_sq (n : ℕ) (o : Fin (n + 1)) (z : Cw) : vSign n o z * vSign n o z = 1 := by
  unfold vSign; by_cases h : z (n, o.val) <;> simp [h]

theorem eval_law (i : ℕ × ℕ) : HasLaw (Function.eval i : Cw → Bool) coin P1 := by
  unfold P1
  exact MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi _ _)

theorem eval_indep : iIndepFun (fun i => (Function.eval i : Cw → Bool)) P1 := by
  unfold P1
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => measurable_pi_apply i)]
  have hid : (fun (z : Cw) (i : ℕ × ℕ) => (Function.eval i : Cw → Bool) z) = fun z => z := rfl
  rw [hid, Measure.map_id']
  · congr
    funext i
    exact ((measurePreserving_eval_infinitePi (fun _ : ℕ × ℕ => coin) i).map_eq).symm

theorem indep_vSign (n : ℕ) : iIndepFun (vSign n) P1 :=
  (eval_indep.precomp (g := fun o : Fin (n + 1) => (n, o.val))
      (fun _ _ hab => Fin.val_injective (congrArg Prod.snd hab))).comp
    (fun _ b => if b then (1 : ℝ) else -1) (fun _ => measurable_of_finite _)

theorem integral_vSign (n : ℕ) (o : Fin (n + 1)) : ∫ z, vSign n o z ∂P1 = 0 := by
  have h : ∫ z : Cw, (if z (n, o.val) then (1 : ℝ) else -1) ∂P1
      = ∫ b, (if b then (1 : ℝ) else -1) ∂coin := by
    simpa [Function.comp_def] using
      (eval_law (n, o.val)).integral_comp (f := fun b : Bool => if b then (1 : ℝ) else -1)
        (measurable_of_finite _).aestronglyMeasurable
  simp only [vSign]
  rw [h, integral_coin]
  norm_num

theorem integral_vSign_mul (n : ℕ) (o o' : Fin (n + 1)) :
    ∫ z, vSign n o z * vSign n o' z ∂P1
      = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) o o' := by
  rw [Matrix.one_apply]
  by_cases h : o = o'
  · subst h
    simp only [vSign_sq]
    simp
  · have hzero : (if o = o' then (1 : ℝ) else 0) = 0 := by simp [h]
    rw [hzero]
    have hind : IndepFun (vSign n o) (vSign n o') P1 := (indep_vSign n).indepFun h
    have hi1 : Integrable (vSign n o) P1 :=
      (memLp_top_of_bound (meas_vSign n o).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun z => by
          rw [Real.norm_eq_abs]; exact abs_vSign_le n o z))).integrable le_top
    have hi2 : Integrable (vSign n o') P1 :=
      (memLp_top_of_bound (meas_vSign n o').aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun z => by
          rw [Real.norm_eq_abs]; exact abs_vSign_le n o' z))).integrable le_top
    have hmul := ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral hind
      hi1.aestronglyMeasurable hi2.aestronglyMeasurable
    simp only [Pi.mul_apply] at hmul
    rw [hmul, integral_vSign, zero_mul]


/-! ### Transport along `map snd = P1` -/

theorem indepFun_of_snd {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure Aw} [IsProbabilityMeasure μ] (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1)
    {F : Cw → γ} {G : Cw → δ} (hF : Measurable F) (hG : Measurable G)
    (h : IndepFun F G P1) : IndepFun (fun y : Aw => F y.2) (fun y : Aw => G y.2) μ := by
  have e1 : (fun y : Aw => F y.2) = F ∘ Prod.snd := rfl
  have e2 : (fun y : Aw => G y.2) = G ∘ Prod.snd := rfl
  rw [e1, e2, indepFun_iff_map_prod_eq_prod_map_map
    ((hF.comp measurable_snd).aemeasurable) ((hG.comp measurable_snd).aemeasurable)]
  rw [indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hG.aemeasurable] at h
  have e0 : (fun y : Aw => ((F ∘ Prod.snd) y, (G ∘ Prod.snd) y))
      = (fun z : Cw => (F z, G z)) ∘ Prod.snd := rfl
  rw [e0, ← Measure.map_map (hF.prodMk hG) measurable_snd,
    ← Measure.map_map hF measurable_snd, ← Measure.map_map hG measurable_snd, hmap, h]

theorem integral_of_snd {μ : Measure Aw}
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1)
    {f : Cw → ℝ} (hf : Measurable f) : ∫ y, f y.2 ∂μ = ∫ z, f z ∂P1 := by
  have := integral_map (φ := (Prod.snd : Aw → Cw)) (μ := μ) measurable_snd.aemeasurable
    hf.aestronglyMeasurable
  rw [hmap] at this
  exact this.symm

/-- The dependency graph of the disturbances under `ℙ_ω`: equality of indices. -/
noncomputable def uDep {μ : Measure Aw} [IsProbabilityMeasure μ]
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1) (n : ℕ) :
    DepGraph (uSign n) μ where
  G := fun o o' => o = o'
  decG := fun _ _ => inferInstance
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  meas := meas_uSign n
  indep := by
    intro A B h
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact h a ha a hb rfl
    have hP1 : IndepFun (fun z : Cw => fun k : ↥A => vSign n (k : Fin (n + 1)) z)
        (fun z : Cw => fun k : ↥B => vSign n (k : Fin (n + 1)) z) P1 :=
      (indep_vSign n).indepFun_finset A B hdisj (meas_vSign n)
    exact indepFun_of_snd (F := fun z : Cw => fun k : ↥A => vSign n (k : Fin (n + 1)) z)
      (G := fun z : Cw => fun k : ↥B => vSign n (k : Fin (n + 1)) z) hmap
      (Measurable.of_eval fun k : ↥A => meas_vSign n (k : Fin (n + 1)))
      (Measurable.of_eval fun k : ↥B => meas_vSign n (k : Fin (n + 1))) hP1


/-! ### The random, `𝒟`-measurable design -/

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- The design sign, read off the design coin. -/
noncomputable def sgnA (y : Aw) : ℝ := if y.1 then (1 : ℝ) else -1

theorem sgnA_mul (y : Aw) : sgnA y * sgnA y = 1 := by
  unfold sgnA; by_cases h : y.1 <;> simp [h]

theorem meas_fstA : Measurable[Dw] (Prod.fst : Aw → Bool) :=
  measurable_iff_comap_le.2 le_rfl

theorem meas_sgnA : Measurable[Dw] sgnA :=
  (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp meas_fstA

/-- The design at index `n`: the all-ones regressor, with the sign of the design coin. -/
noncomputable def wXt (n : ℕ) (y : Aw) : Matrix (Fin (n + 1)) (Fin 1) ℝ := sgnA y • redXt n

/-- The conditional second-moment matrix of the disturbances. -/
noncomputable def wOm (n : ℕ) (_ : Aw) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1

theorem gram_smul {O K : Type*} [Fintype O] {ε : ℝ} (hε : ε * ε = 1) (A : Matrix O K ℝ) :
    (ε • A)ᵀ * (ε • A) = Aᵀ * A := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε, one_smul]

theorem scoreVar_smul {O K : Type*} [Fintype O] {ε : ℝ} (hε : ε * ε = 1)
    (A : Matrix O K ℝ) (Om : Matrix O O ℝ) :
    scoreVar (ε • A) Om = scoreVar A Om := by
  simp only [scoreVar, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε,
    one_smul]

theorem scoreMap_smul {O K rr : Type*} [Fintype O] [Fintype K] [DecidableEq K] {ε : ℝ}
    (hε : ε * ε = 1) (A : Matrix O K ℝ) (Rn : Matrix rr K ℝ) :
    scoreMap (ε • A) Rn = scoreMap A Rn := by
  rw [scoreMap, scoreMap, gram_smul hε]

theorem restrictedVar_smul {O K rr : Type*} [Fintype O] [Fintype K] [DecidableEq K] {ε : ℝ}
    (hε : ε * ε = 1) (A : Matrix O K ℝ) (Om : Matrix O O ℝ)
    (Rn : Matrix rr K ℝ) : restrictedVar (ε • A) Om Rn = restrictedVar A Om Rn := by
  rw [restrictedVar, restrictedVar, scoreMap_smul hε, scoreVar_smul hε]

theorem steinWeight_smul {O K rr : Type*} [Fintype O] [Fintype K] [DecidableEq K]
    [Fintype rr] [DecidableEq rr] {ε : ℝ}
    (hε : ε * ε = 1) (A : Matrix O K ℝ) (Om : Matrix O O ℝ)
    (Rn : Matrix rr K ℝ) (b : rr → ℝ) :
    steinWeight (ε • A) Om Rn b = steinWeight A Om Rn b := by
  rw [steinWeight, steinWeight, steinStd, steinStd, scoreVar_smul hε, scoreMap_smul hε]

theorem depSum_scoreArray_smul {O K : Type*} [Fintype O] [Fintype K] {ε : ℝ}
    {W : Type*} [MeasurableSpace W]
    (A : Matrix O K ℝ) (a : K → ℝ) (v : O → W → ℝ) (y : W) :
    depSum (scoreArray (ε • A) a v) y = ε * depSum (scoreArray A a v) y := by
  simp only [depSum, scoreArray, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun o _ => by ring


noncomputable def wBhat (n : ℕ) (y : Aw) : Fin 1 → ℝ :=
  ((wXt n y)ᵀ * wXt n y)⁻¹ *ᵥ ((wXt n y)ᵀ *ᵥ (fun o => uSign n o y))

noncomputable def wb : Fin 1 → ℝ := fun _ => 1

theorem wb_dot : wb ⬝ᵥ wb = 1 := by simp [wb, dotProduct]

theorem w_hXtD (n : ℕ) (o : Fin (n + 1)) (k : Fin 1) :
    Measurable[Dw] fun y => wXt n y o k := by
  have : (fun y : Aw => wXt n y o k) = fun y => sgnA y * 1 := rfl
  rw [this]
  exact meas_sgnA.mul_const 1

theorem w_statistic (n : ℕ) :
    (fun y : Aw => wb ⬝ᵥ
        ((sqrtPD (restrictedVar (wXt n y) (wOm n y) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (wBhat n y - (0 : Fin 1 → ℝ)))))
      = fun y => sgnA y *
          depSum (scoreArray (redXt n)
            (steinWeight (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
              (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (uSign n)) y := by
  funext y
  rw [show wBhat n y - (0 : Fin 1 → ℝ)
      = ((wXt n y)ᵀ * wXt n y)⁻¹ *ᵥ ((wXt n y)ᵀ *ᵥ (fun o => uSign n o y)) from sub_zero _,
    dotProduct_standardized_eq_depSum,
    show wXt n y = sgnA y • redXt n from rfl,
    steinWeight_smul (sgnA_mul y), depSum_scoreArray_smul]
  rfl

theorem w_hWm (n : ℕ) : Measurable fun y : Aw => wb ⬝ᵥ
    ((sqrtPD (restrictedVar (wXt n y) (wOm n y) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (wBhat n y - (0 : Fin 1 → ℝ)))) := by
  rw [w_statistic n]
  exact (meas_sgnA.mono Dw_le le_rfl).mul
    (Finset.measurable_sum _ fun o _ => (meas_uSign n o).const_mul _)

theorem w_hrate : Tendsto (fun n : ℕ => ((1 : ℕ) : ℝ) * (1 * 1 / Real.sqrt ((n : ℝ) + 1)))
    atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  simp only [Nat.cast_one, one_mul, one_div]
  exact hsqrt.inv_tendsto_atTop


theorem coin_singleton (b : Bool) : coin {b} = 2⁻¹ := by
  cases b <;>
  · rw [coin]
    simp

theorem Pw_fst (b : Bool) : Pw {y : Aw | y.1 = b} = 2⁻¹ := by
  have hset : {y : Aw | y.1 = b} = ({b} : Set Bool) ×ˢ (Set.univ : Set Cw) :=
    Set.ext fun y => by simp [Set.mem_prod, Set.mem_singleton_iff]
  rw [hset, Pw, Measure.prod_prod, coin_singleton, measure_univ, mul_one]

theorem Dw_proper : ∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B := by
  have hm : Measurable (fun z : Cw => z (0, 0)) := measurable_pi_apply ((0, 0) : ℕ × ℕ)
  refine ⟨Prod.snd ⁻¹' ((fun z : Cw => z (0, 0)) ⁻¹' {true}),
    measurable_snd (hm (measurableSet_singleton true)), ?_⟩
  rintro ⟨t, -, ht⟩
  have h1 : ((true, (fun _ => true : Cw)) : Aw) ∈ Prod.fst ⁻¹' t := by rw [ht]; simp
  have h2 : ((true, (fun _ => false : Cw)) : Aw) ∉ Prod.fst ⁻¹' t := by rw [ht]; simp
  exact h2 h1

theorem condExpKernel_ne_Pw : ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw) := by
  intro h
  have hfz := Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel Dw_le Pw meas_fstA
  have hall : ∀ᵐ ω ∂Pw, ∀ᵐ y ∂Pw, y.1 = ω.1 := by
    filter_upwards [h, hfz] with ω hq hf
    rwa [hq] at hf
  obtain ⟨ω₀, hω₀⟩ := hall.exists
  have hz : Pw {y : Aw | ¬ (y.1 = ω₀.1)} = 0 := ae_iff.1 hω₀
  have hset : {y : Aw | ¬ (y.1 = ω₀.1)} = {y : Aw | y.1 = !ω₀.1} := by
    ext y
    obtain ⟨y1, y2⟩ := y
    cases y1 <;> cases ω₀.1 <;> simp
  rw [hset, Pw_fst] at hz
  exact (ENNReal.inv_ne_zero.2 (by simp)) hz

theorem w_hPD (n : ℕ) :
    (scoreVar (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).PosDef := by
  refine Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one
    (show (0 : ℝ) < (n : ℝ) + 1 by positivity)) ?_
  rw [redXt_scoreVar]

/-- The total conditional variance is `1` at every `n`. -/
theorem w_total_variance (n : ℕ) :
    ∫ z, (depSum (scoreArray (redXt n)
      (steinWeight (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (vSign n)) z) ^ 2 ∂P1 = 1 :=
  integral_depSum_scoreArray_sq_eq_one (w_hPD n) (redXt_scoreMap_isUnit n) (meas_vSign n)
    (fun o z => abs_vSign_le n o z) (integral_vSign_mul n) wb_dot

/-- The total variance is `1` under `ℙ_ω` itself. The array is a function of the disturbance
coordinate, so `integral_of_snd` moves the integral across `map_snd_condExpKernel`. -/
theorem w_total_variance_cond :
    ∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt n)
        (steinWeight (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (uSign n)) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n
  have hmeas : Measurable fun z : Cw => (depSum (scoreArray (redXt n)
      (steinWeight (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (vSign n)) z) ^ 2 :=
    (Finset.measurable_sum _ fun o _ => (meas_vSign n o).const_mul _).pow_const 2
  exact (integral_of_snd hω hmeas).trans (w_total_variance n)

/-- The hypotheses of `cltcluster_a_oneDimension_betaJM_unconditional` hold on this model. -/
theorem cltcluster_a_oneDimension_betaJM_unconditional_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), wXt n y = (if y.1 then (1 : ℝ) else -1) • redXt n)
    ∧ (∀ n : ℕ, ∫ z, (depSum (scoreArray (redXt n)
        (steinWeight (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (vSign n)) z) ^ 2 ∂P1 = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt n)
        (steinWeight (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (uSign n)) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => wb ⬝ᵥ
          ((sqrtPD (restrictedVar (wXt n y) (wOm n y) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (wBhat n y - (0 : Fin 1 → ℝ)))))
        atTop (id : ℝ → ℝ) (fun _ => Pw) (gaussianReal 0 1) := by
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ => rfl, w_total_variance,
    w_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine cltcluster_a_oneDimension_betaJM_unconditional
    (O := fun n => Fin (n + 1)) (Gp := fun n => Fin (n + 1))
    Dw_le Pw wXt wOm (fun _ => 1) uSign wBhat (fun _ => 0) (fun _ _ o => o)
    w_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    (fun n _ => (n : ℝ) + 1) (fun _ _ => 1) 1 1 zero_le_one zero_le_one
    (fun n o y => abs_vSign_le n o y.2) wb wb_dot w_hWm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [map_snd_condExpKernel] with ω hω
    exact ⟨fun n => uDep hω n, fun _ _ _ => Iff.rfl⟩
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show wXt n ω = sgnA ω • redXt n from rfl, scoreMap_smul (sgnA_mul ω)]
    exact redXt_scoreMap_isUnit n
  · exact Filter.Eventually.of_forall fun _ n => by positivity
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show wXt n ω = sgnA ω • redXt n from rfl, scoreVar_smul (sgnA_mul ω),
      show wOm n ω = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) from rfl, redXt_scoreVar]
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o o'
    exact (integral_of_snd hω ((meas_vSign n o).mul (meas_vSign n o'))).trans
      (integral_vSign_mul n o o')
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o
    exact (integral_of_snd hω (meas_vSign n o)).trans (integral_vSign n o)
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun k => wXt n ω o k) ⬝ᵥ (fun k => wXt n ω o k) = 1 := by
      simp [wXt, redXt, dotProduct, sgnA_mul ω]
    rw [h]
    norm_num
  · refine Filter.Eventually.of_forall fun ω n γ => ?_
    refine Finset.card_le_one.mpr (fun a ha c hc => ?_)
    rw [mem_cluster] at ha hc
    simpa using ha.trans hc.symm
  · exact Filter.Eventually.of_forall fun _ => w_hrate

end FrozenDesignWitness

end FrozenDesignWitness

/-! ## Cramér–Wold in the conditional frame

Mathlib's `tendstoInDistribution_iff_tendstoInDistribution_inner` requires a constant measure
family on one space. The conditional frame is constant (`W n := Ω`, `μ n := ℙ_ω`), so
`cltcluster_a_oneDimension_betaJM_const` states the `J = 1` theorem at one `(W, μ)` as
convergence in distribution, and `cltcluster_a_oneDimension_betaJM_vector` gives
`𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)` under `μ`. No almost-everywhere hypothesis of the
unconditional theorem mentions the direction `b`, so the unconditional vector form applies the
scalar theorem once per direction; `hWvm` is measurability of the vector statistic. -/

section ConditionalCramerWold

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

/-- The `J = 1` conditional theorem at a constant family, as convergence in distribution. -/
theorem cltcluster_a_oneDimension_betaJM_const
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : Type*} [mW : MeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W → ℝ) (bhat : ℕ → W → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, O n → Gp n)
    (Dv : ∀ n, DepGraph (ν n) μ)
    (hshare : ∀ n o o', (Dv n).G o o' ↔ g n o = g n o')
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
    (Gb : ℕ → ℕ) (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * (B * Cnu / Real.sqrt (lmin n))) atTop (𝓝 0))
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
  refine cltcluster_a_oneDimension_tendstoInDistribution (Ω := fun _ => W) (fun _ => μ)
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n)) g
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n o o' => hshare n o o')
    (fun n => B * Cnu / Real.sqrt (lmin n)) Gb
    (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ hGb ?_ ?_ hrate
  · exact fun n o ω =>
      abs_scoreArray_le (hPD n) (hA n) (hlmin n) (hfloor n) hB0 (hB n) (hnu n) hb o ω
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hnu n) (hOm n) hb

/-- Cramér–Wold in the conditional frame, at `J = 1`. -/
theorem cltcluster_a_oneDimension_betaJM_vector
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    {W : Type*} [mW : MeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → W → ℝ) (bhat : ℕ → W → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, O n → Gp n)
    (Dv : ∀ n, DepGraph (ν n) μ)
    (hshare : ∀ n o o', (Dv n).G o o' ↔ g n o = g n o')
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
    (Gb : ℕ → ℕ) (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hrate : Tendsto (fun n => (Gb n : ℝ) * (B * Cnu / Real.sqrt (lmin n))) atTop (𝓝 0))
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
  have h := cltcluster_a_oneDimension_betaJM_const μ Xt Om Rn ν bhat β g Dv hshare hscore hA
    lmin hlmin hfloor hOm hmean B Cnu hB0 hCnu0 hB hnu Gb hGb hrate
    (WithLp.ofLp b) (dotProduct_self_ofLp b hb)
  have hfun : (fun (n : ℕ) (ω : W) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun (n : ℕ) (ω : W) =>
        ⟪restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h


theorem cltcluster_a_oneDimension_betaJM_unconditional_vector
    {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, Ω → O n → Gp n)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => Om n ω o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (lmin : ℕ → Ω → ℝ) (Gb : ℕ → Ω → ℕ) (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (hWvm : ∀ n, Measurable fun y =>
      restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ g n ω o = g n ω o')
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hlmin : ∀ᵐ ω ∂P, ∀ n, 0 < lmin n ω)
    (hfloor : ∀ᵐ ω ∂P, ∀ n, lmin n ω • (1 : Matrix K K ℝ) ≤ scoreVar (Xt n ω) (Om n ω))
    (hOmeq : ∀ᵐ ω ∂P, ∀ n o o',
      ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω) = Om n ω o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hGb : ∀ᵐ ω ∂P, ∀ n γ, (cluster (g n ω) γ).card ≤ Gb n ω)
    (hrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) * (B * Cnu / Real.sqrt (lmin n ω)))
      atTop (𝓝 0)) :
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
  have h := cltcluster_a_oneDimension_betaJM_unconditional h𝒟 P Xt Om Rn ν bhat β g
    hXtD hOmD hscore lmin Gb B Cnu hB0 hCnu0 hnu (WithLp.ofLp b)
    (dotProduct_self_ofLp b hb) hWm hdep hA hlmin hfloor hOmeq hmean hB hGb hrate
  have hfun : (fun (n : ℕ) (y : Ω) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))))
      = fun (n : ℕ) (y : Ω) =>
        ⟪restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

end ConditionalCramerWold

/-! ## The general-`J` and part (b) vector forms

The general-`J` and part (b) theorems are instantiated at a constant family and quantified over
unit directions, as in the `J = 1` case above. The general-`J` rate condition is
`(n/D_n)^{1/3}δ_n → 0`. -/

section ConditionalCramerWoldGeneral

open scoped RealInnerProductSpace
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.CLTMartingale.CondD

/-- The general-`J` conditional theorem at a constant family, as convergence in
distribution. -/
theorem cltcluster_a_general_betaJM_const
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  have hacc : Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0) :=
    tendsto_accumRate hDn1 hDnN hrate
  have hsec : Tendsto (fun n => secondRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0) :=
    tendsto_secondRate hDn1 hlmin hrate
  rw [hfun]
  refine cltcluster_a_general_tendstoInDistribution (Ω := fun _ => W) (fun _ => μ)
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * Cnu / Real.sqrt (lmin n)) (fun n => Dn n + 1)
    (fun n => div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun n o ω =>
      abs_scoreArray_le (hPD n) (hA n) (hlmin n) (hfloor n) hB0 (hB n) (hnu n) hb o ω
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hnu n) (hOm n) hb
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hacc.const_mul (8 * B ^ 4 * Cnu ^ 4))
    exact firstRate_le (hDn1 n) (hlmin n)
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hsec.const_mul (4 * B ^ 3 * Cnu ^ 3))
    exact secondRate_le (hDn1 n) (hlmin n) hB0 hCnu0

/-- Cramér–Wold in the conditional frame, at general `J`. -/
theorem cltcluster_a_general_betaJM_vector
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  have h := cltcluster_a_general_betaJM_const μ Xt Om Rn ν bhat β Dv hscore hA
    lmin hlmin hfloor hOm hmean B Cnu hB0 hCnu0 hB hnu Dn hDn1 hDnN hdeg hrate
    (WithLp.ofLp b) (dotProduct_self_ofLp b hb)
  have hfun : (fun (n : ℕ) (ω : W) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun (n : ℕ) (ω : W) =>
        ⟪restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

theorem cltcluster_a_general_betaJM_unconditional_vector
    {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
      Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
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
  have h := cltcluster_a_general_betaJM_unconditional h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B Cnu hB0 hCnu0 hnu (WithLp.ofLp b)
    (dotProduct_self_ofLp b hb) hWm hdep hA hlmin hfloor hOmeq hmean hB hDn1 hDnN hrate
  have hfun : (fun (n : ℕ) (y : Ω) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))))
      = fun (n : ℕ) (y : Ω) =>
        ⟪restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

/-- Part (b) at a constant family, as convergence in distribution. -/
theorem cltcluster_b_general_betaJM_const
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) μ)
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂μ ≤ C4 ^ 4)
    (Dn : ℕ → ℕ) (hDn1 : ∀ n, 1 ≤ Dn n) (hDnN : ∀ n, Dn n ≤ Fintype.card (O n))
    (hdeg : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n + 1)
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  have hacc : Tendsto (fun n => accumRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0) :=
    tendsto_accumRate hDn1 hDnN hrate
  have hsec : Tendsto (fun n => secondRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0) :=
    tendsto_secondRate hDn1 hlmin hrate
  rw [hfun]
  refine cltcluster_b_general_tendstoInDistribution (Ω := fun _ => W) (fun _ => μ)
    (fun n => scoreArray (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b) (ν n))
    (fun n => scoreArrayDepGraph (Dv n) (Xt n) (steinWeight (Xt n) (Om n) (Rn n) b))
    (fun n => B * C4 / Real.sqrt (lmin n)) (fun n => Dn n + 1)
    (fun n => div_pos (mul_pos hB0 hC40) (Real.sqrt_pos.mpr (hlmin n))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun n o => integrable_scoreArray_pow_four (hint4 n) (Xt n) _ o
  · exact fun n o => integral_scoreArray_pow_four_le (hPD n) (hA n) (hlmin n) (hfloor n)
      hB0.le hC40.le (hB n) (hint4 n) (hfour n) hb o
  · intro n o
    rw [nbhd_scoreArrayDepGraph]
    exact hdeg n o
  · exact fun n o => integral_scoreArray (fun o => hmean n o) (Xt n) _ o
  · exact fun n => integral_depSum_scoreArray_sq_eq_one_moment (hPD n) (hA n)
      (fun o => (Dv n).meas o) (hint4 n) (hOm n) hb
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hacc.const_mul (8 * B ^ 4 * C4 ^ 4))
    exact firstRate_le (hDn1 n) (hlmin n)
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using hsec.const_mul (4 * B ^ 3 * C4 ^ 3))
    exact secondRate_le (hDn1 n) (hlmin n) hB0.le hC40.le

/-- Cramér–Wold in the conditional frame, for part (b). -/
theorem cltcluster_b_general_betaJM_vector
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n) (lmin n)) atTop (𝓝 0))
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
  have h := cltcluster_b_general_betaJM_const μ Xt Om Rn ν bhat β Dv hscore hA
    lmin hlmin hfloor hOm hmean B C4 hB0 hC40 hB hint4 hfour Dn hDn1 hDnN hdeg hrate
    (WithLp.ofLp b) (dotProduct_self_ofLp b hb)
  have hfun : (fun (n : ℕ) (ω : W) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n ω - β n))))
      = fun (n : ℕ) (ω : W) =>
        ⟪restrictedStat (Xt n) (Om n) (Rn n) (bhat n ω - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

theorem cltcluster_b_general_betaJM_unconditional_vector
    {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
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
    (hrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => steinRate (Fintype.card (O n)) (Dn n ω) (lmin n ω)) atTop (𝓝 0)) :
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
  have h := cltcluster_b_general_betaJM_unconditional h𝒟 P Xt Om Rn ν bhat β
    hXtD hOmD hscore lmin Dn B C4 hB0 hC40 (WithLp.ofLp b)
    (dotProduct_self_ofLp b hb) hWm hdep hA hlmin hfloor hOmeq hmean hB hint4 hfour
    hDn1 hDnN hrate
  have hfun : (fun (n : ℕ) (y : Ω) => (WithLp.ofLp b) ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (Om n y) (Rn n)))⁻¹ *ᵥ (Rn n *ᵥ (bhat n y - β n))))
      = fun (n : ℕ) (y : Ω) =>
        ⟪restrictedStat (Xt n y) (Om n y) (Rn n) (bhat n y - β n), b⟫ := funext hs
  rw [hfun] at h
  exact h

end ConditionalCramerWoldGeneral

/-! ### Fair signs indexed by the coin

The lemmas about `vSign` are stated on the coin index `ℕ × ℕ`, so that any injection into the
coin lattice specializes them through `iIndepFun.precomp`. `vSign n o` is definitionally
`coinSign (n, o.val)`. -/

section CoinSignLayer

namespace FrozenDesignWitness

open Multiway.Multilinear

noncomputable def coinSign (i : ℕ × ℕ) (z : Cw) : ℝ := if z i then (1 : ℝ) else -1

theorem meas_coinSign (i : ℕ × ℕ) : Measurable (coinSign i) :=
  (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
    (measurable_pi_apply i)

theorem abs_coinSign_le (i : ℕ × ℕ) (z : Cw) : |coinSign i z| ≤ 1 := by
  unfold coinSign; by_cases h : z i <;> simp [h]

theorem coinSign_sq (i : ℕ × ℕ) (z : Cw) : coinSign i z * coinSign i z = 1 := by
  unfold coinSign; by_cases h : z i <;> simp [h]

theorem coinSign_pow_four (i : ℕ × ℕ) (z : Cw) : (coinSign i z) ^ 4 = 1 := by
  unfold coinSign; by_cases h : z i <;> norm_num [h]

theorem indep_coinSign : iIndepFun coinSign P1 :=
  eval_indep.comp (fun _ b => if b then (1 : ℝ) else -1) (fun _ => measurable_of_finite _)

theorem integrable_coinSign (i : ℕ × ℕ) : Integrable (coinSign i) P1 :=
  (memLp_top_of_bound (meas_coinSign i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs]; exact abs_coinSign_le i z))).integrable le_top

theorem integrable_coinSign_mul (i j : ℕ × ℕ) :
    Integrable (fun z => coinSign i z * coinSign j z) P1 := by
  refine Integrable.of_bound
    ((meas_coinSign i).mul (meas_coinSign j)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := abs_coinSign_le i z
  have h2 := abs_coinSign_le j z
  nlinarith [abs_nonneg (coinSign i z), abs_nonneg (coinSign j z)]

theorem integral_coinSign (i : ℕ × ℕ) : ∫ z, coinSign i z ∂P1 = 0 := by
  have h : ∫ z : Cw, (if z i then (1 : ℝ) else -1) ∂P1
      = ∫ b, (if b then (1 : ℝ) else -1) ∂coin := by
    simpa [Function.comp_def] using
      (eval_law i).integral_comp (f := fun b : Bool => if b then (1 : ℝ) else -1)
        (measurable_of_finite _).aestronglyMeasurable
  simp only [coinSign]
  rw [h, integral_coin]
  norm_num

theorem integral_coinSign_mul (i j : ℕ × ℕ) :
    ∫ z, coinSign i z * coinSign j z ∂P1 = if i = j then (1 : ℝ) else 0 := by
  by_cases h : i = j
  · subst h
    simp only [coinSign_sq]
    simp
  · rw [ite_eq_right h]
    have hind : IndepFun (coinSign i) (coinSign j) P1 := indep_coinSign.indepFun h
    have hmul := ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral hind
      (integrable_coinSign i).aestronglyMeasurable
      (integrable_coinSign j).aestronglyMeasurable
    simp only [Pi.mul_apply] at hmul
    rw [hmul, integral_coinSign, zero_mul]

end FrozenDesignWitness

end CoinSignLayer

/-! ### Examples for the general-`J` and part (b) unconditional theorems

The `J = 2` design is placed on the product space of `FrozenDesignWitness`, with its nontrivial
`𝒟`. It has `n+3` observations and the sharing relation `|o − o'| ≤ 1`, which is the union of two
clustering maps and is not transitive, and `D_n = 2`. The design `X̃_n(ω) = ±ι_{n+3}` has its sign read off the
design coin, `λ_min(Ω_n) = n+3`, and `(n/D_n)^{1/3}δ_n ≤ 8(n+3)^{-1/2} → 0`. The total
conditional variance is `1` at every `n`. The disturbance is a fair sign, so it is bounded. -/

section FrozenGeneralWitness

namespace FrozenGeneralWitness

open Multiway.SteinCluster.FrozenDesignWitness
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- The disturbance of observation `o` at index `n`, on the disturbance coordinate. -/
noncomputable def gvSign (n : ℕ) (o : Fin (n + 3)) (z : Cw) : ℝ := coinSign (n, o.val) z

/-- The same on the whole space. -/
noncomputable def guSign (n : ℕ) (o : Fin (n + 3)) (y : Aw) : ℝ := gvSign n o y.2

theorem meas_gvSign (n : ℕ) (o : Fin (n + 3)) : Measurable (gvSign n o) :=
  meas_coinSign (n, o.val)

theorem meas_guSign (n : ℕ) (o : Fin (n + 3)) : Measurable (guSign n o) :=
  (meas_gvSign n o).comp measurable_snd

theorem abs_gvSign_le (n : ℕ) (o : Fin (n + 3)) (z : Cw) : |gvSign n o z| ≤ 1 :=
  abs_coinSign_le (n, o.val) z

theorem guSign_pow_four (n : ℕ) (o : Fin (n + 3)) (y : Aw) : (guSign n o y) ^ 4 = 1 :=
  coinSign_pow_four (n, o.val) y.2

theorem indep_gvSign (n : ℕ) : iIndepFun (gvSign n) P1 :=
  indep_coinSign.precomp (g := fun o : Fin (n + 3) => (n, o.val))
    (fun _ _ hab => Fin.val_injective (congrArg Prod.snd hab))

theorem integral_gvSign (n : ℕ) (o : Fin (n + 3)) : ∫ z, gvSign n o z ∂P1 = 0 :=
  integral_coinSign (n, o.val)

theorem integral_gvSign_mul (n : ℕ) (o o' : Fin (n + 3)) :
    ∫ z, gvSign n o z * gvSign n o' z ∂P1
      = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) o o' := by
  have h : (∫ z, gvSign n o z * gvSign n o' z ∂P1)
      = if ((n, o.val) = (n, o'.val)) then (1 : ℝ) else 0 :=
    integral_coinSign_mul (n, o.val) (n, o'.val)
  rw [h, Matrix.one_apply]
  by_cases hh : o = o'
  · subst hh; simp
  · have hne : ¬ ((n, o.val) = (n, o'.val)) :=
      fun hc => hh (Fin.val_injective (congrArg Prod.snd hc))
    rw [ite_eq_right hne, ite_eq_right hh]

/-- The `J = 2` dependency graph under `ℙ_ω`. -/
noncomputable def gPathDep {μ : Measure Aw} [IsProbabilityMeasure μ]
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1) (n : ℕ) :
    DepGraph (guSign n) μ where
  G := pathG (n + 3)
  decG := fun _ _ => inferInstance
  refl := fun _ => Or.inl rfl
  symm := fun o o' h => by unfold pathG at h ⊢; omega
  meas := meas_guSign n
  indep := by
    intro A Bs h
    have hdisj : Disjoint A Bs := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact h a ha a hb (Or.inl rfl)
    have hP1 : IndepFun (fun z : Cw => fun k : ↥A => gvSign n (k : Fin (n + 3)) z)
        (fun z : Cw => fun k : ↥Bs => gvSign n (k : Fin (n + 3)) z) P1 :=
      (indep_gvSign n).indepFun_finset A Bs hdisj (meas_gvSign n)
    exact indepFun_of_snd (F := fun z : Cw => fun k : ↥A => gvSign n (k : Fin (n + 3)) z)
      (G := fun z : Cw => fun k : ↥Bs => gvSign n (k : Fin (n + 3)) z) hmap
      (Measurable.of_eval fun k : ↥A => meas_gvSign n (k : Fin (n + 3)))
      (Measurable.of_eval fun k : ↥Bs => meas_gvSign n (k : Fin (n + 3))) hP1

/-- Every closed neighbourhood has at most three members, so `D_n = 2` for this design. -/
theorem gPathDep_nbhd_card {μ : Measure Aw} [IsProbabilityMeasure μ]
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1) (n : ℕ) (o : Fin (n + 3)) :
    ((gPathDep hmap n).nbhd o).card ≤ 3 := by
  classical
  have hsub : (gPathDep hmap n).nbhd o ⊆
      ((Finset.univ.filter (fun o' : Fin (n + 3) => o'.val = o.val))
        ∪ (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val + 1 = o.val)))
      ∪ (Finset.univ.filter (fun o' : Fin (n + 3) => o.val + 1 = o'.val)) := by
    intro j hj
    have hG : pathG (n + 3) o j := (gPathDep hmap n).mem_nbhd_iff.mp hj
    rcases hG with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [h]))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [h]))
    · exact Finset.mem_union_right _ (by simp [h])
  have c1 : (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val = o.val)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter] at ha hb
    exact Fin.ext (ha.2.trans hb.2.symm)
  have c2 : (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val + 1 = o.val)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter] at ha hb
    exact Fin.ext (by omega)
  have c3 : (Finset.univ.filter (fun o' : Fin (n + 3) => o.val + 1 = o'.val)).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    simp only [Finset.mem_filter] at ha hb
    exact Fin.ext (by omega)
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have := (Finset.card_union_le
    (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val = o.val))
    (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val + 1 = o.val)))
  omega

/-- The design at index `n`: the all-ones regressor over `n+3` observations, with the sign of
the design coin. -/
noncomputable def gXt (n : ℕ) (y : Aw) : Matrix (Fin (n + 3)) (Fin 1) ℝ :=
  sgnA y • redXt (n + 2)

/-- The conditional second-moment matrix of the disturbances. -/
noncomputable def gOm (n : ℕ) (_ : Aw) : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ := 1

noncomputable def gBhat (n : ℕ) (y : Aw) : Fin 1 → ℝ :=
  ((gXt n y)ᵀ * gXt n y)⁻¹ *ᵥ ((gXt n y)ᵀ *ᵥ (fun o => guSign n o y))

theorem g_hXtD (n : ℕ) (o : Fin (n + 3)) (k : Fin 1) :
    Measurable[Dw] fun y => gXt n y o k := by
  have : (fun y : Aw => gXt n y o k) = fun y => sgnA y * 1 := rfl
  rw [this]
  exact meas_sgnA.mul_const 1

theorem g_statistic (n : ℕ) :
    (fun y : Aw => wb ⬝ᵥ
        ((sqrtPD (restrictedVar (gXt n y) (gOm n y) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gBhat n y - (0 : Fin 1 → ℝ)))))
      = fun y => sgnA y *
          depSum (scoreArray (redXt (n + 2))
            (steinWeight (redXt (n + 2)) (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
              (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (guSign n)) y := by
  funext y
  rw [show gBhat n y - (0 : Fin 1 → ℝ)
      = ((gXt n y)ᵀ * gXt n y)⁻¹ *ᵥ ((gXt n y)ᵀ *ᵥ (fun o => guSign n o y)) from sub_zero _,
    dotProduct_standardized_eq_depSum,
    show gXt n y = sgnA y • redXt (n + 2) from rfl,
    steinWeight_smul (sgnA_mul y), depSum_scoreArray_smul]
  rfl

theorem g_hWm (n : ℕ) : Measurable fun y : Aw => wb ⬝ᵥ
    ((sqrtPD (restrictedVar (gXt n y) (gOm n y) (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gBhat n y - (0 : Fin 1 → ℝ)))) := by
  rw [g_statistic n]
  exact (meas_sgnA.mono Dw_le le_rfl).mul
    (Finset.measurable_sum _ fun o _ => (meas_guSign n o).const_mul _)

/-- The total conditional variance is `1` at every `n`. -/
theorem g_total_variance (n : ℕ) :
    ∫ z, (depSum (scoreArray (redXt (n + 2))
      (steinWeight (redXt (n + 2)) (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (gvSign n)) z) ^ 2 ∂P1 = 1 :=
  integral_depSum_scoreArray_sq_eq_one (w_hPD (n + 2)) (redXt_scoreMap_isUnit (n + 2))
    (meas_gvSign n) (fun o z => abs_gvSign_le n o z) (integral_gvSign_mul n) wb_dot

theorem g_total_variance_cond :
    ∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2)) (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (guSign n)) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n
  have hmeas : Measurable fun z : Cw => (depSum (scoreArray (redXt (n + 2))
      (steinWeight (redXt (n + 2)) (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (gvSign n)) z) ^ 2 :=
    (Finset.measurable_sum _ fun o _ => (meas_gvSign n o).const_mul _).pow_const 2
  exact (integral_of_snd hω hmeas).trans (g_total_variance n)


/-- The hypotheses of `cltcluster_a_general_betaJM_unconditional` hold on this model. -/
theorem cltcluster_a_general_betaJM_unconditional_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), gXt n y = (if y.1 then (1 : ℝ) else -1) • redXt (n + 2))
    ∧ (∀ n : ℕ, ∃ a b c : Fin (n + 3),
        pathG (n + 3) a b ∧ pathG (n + 3) b c ∧ ¬ pathG (n + 3) a c)
    ∧ (∀ n : ℕ, ∫ z, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2)) (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (gvSign n)) z) ^ 2 ∂P1 = 1)
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
    pathG_not_transitive, g_total_variance, g_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine cltcluster_a_general_betaJM_unconditional (O := fun n => Fin (n + 3))
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
  · exact Filter.Eventually.of_forall fun _ => by simpa using tendsto_steinRate_witness

/-- The hypotheses of `cltcluster_b_general_betaJM_unconditional` hold on the same `J = 2`
design. -/
theorem cltcluster_b_general_betaJM_unconditional_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), gXt n y = (if y.1 then (1 : ℝ) else -1) • redXt (n + 2))
    ∧ (∀ n : ℕ, ∃ a b c : Fin (n + 3),
        pathG (n + 3) a b ∧ pathG (n + 3) b c ∧ ¬ pathG (n + 3) a c)
    ∧ (∀ (n : ℕ) (o : Fin (n + 3)) (y : Aw), (guSign n o y) ^ 4 = 1)
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
    pathG_not_transitive, guSign_pow_four, g_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine cltcluster_b_general_betaJM_unconditional (O := fun n => Fin (n + 3))
    Dw_le Pw gXt gOm (fun _ => 1) guSign gBhat (fun _ => 0)
    g_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    (fun n _ => (n : ℝ) + 3) (fun _ _ => 2) 1 1 zero_lt_one zero_lt_one
    wb wb_dot g_hWm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun y : Aw => (guSign n o y) ^ 4) = fun _ => (1 : ℝ) :=
      funext (guSign_pow_four n o)
    rw [h]
    exact integrable_const 1
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun y : Aw => (guSign n o y) ^ 4) = fun _ => (1 : ℝ) :=
      funext (guSign_pow_four n o)
    rw [h]
    simp
  · exact Filter.Eventually.of_forall fun _ _ => by norm_num
  · refine Filter.Eventually.of_forall fun _ n => ?_
    rw [Fintype.card_fin]
    omega
  · exact Filter.Eventually.of_forall fun _ => by simpa using tendsto_steinRate_witness

end FrozenGeneralWitness

end FrozenGeneralWitness

/-! ### Examples for the vector forms at `r = 1`

At `r = 1` the vector statistic is the scalar one in its single coordinate (`g_vectorStat`), so
measurability of the vector statistic follows from that of the scalar one. -/

section FrozenGeneralVectorWitness

namespace FrozenGeneralWitness

open Multiway.SteinCluster.FrozenDesignWitness
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- At `r = 1` the vector statistic is the scalar one in its single coordinate. -/
theorem g_vectorStat (n : ℕ) :
    (fun y : Aw => restrictedStat (gXt n y) (gOm n y) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (gBhat n y - (0 : Fin 1 → ℝ)))
      = fun y => (WithLp.toLp 2
          ![wb ⬝ᵥ ((sqrtPD (restrictedVar (gXt n y) (gOm n y)
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gBhat n y - (0 : Fin 1 → ℝ))))]
          : EuclideanSpace ℝ (Fin 1)) := by
  funext y
  refine congrArg (WithLp.toLp 2) ?_
  funext k
  fin_cases k
  simp [wb, dotProduct]

theorem g_hWvm (n : ℕ) : Measurable fun y : Aw =>
    restrictedStat (gXt n y) (gOm n y) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (gBhat n y - (0 : Fin 1 → ℝ)) := by
  rw [g_vectorStat n]
  exact (by fun_prop : Measurable
    (fun x : ℝ => (WithLp.toLp 2 ![x] : EuclideanSpace ℝ (Fin 1)))).comp (g_hWm n)

/-- The hypotheses of `cltcluster_a_general_betaJM_unconditional_vector` hold on this model. -/
theorem cltcluster_a_general_betaJM_unconditional_vector_witness :
    (∀ n : ℕ, ∃ a b c : Fin (n + 3),
        pathG (n + 3) a b ∧ pathG (n + 3) b c ∧ ¬ pathG (n + 3) a c)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2)) (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (guSign n)) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => restrictedStat (gXt n y) (gOm n y)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) (gBhat n y - (0 : Fin 1 → ℝ))) atTop
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (fun _ => Pw)
        (stdGaussian (EuclideanSpace ℝ (Fin 1))) := by
  refine ⟨pathG_not_transitive, g_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine cltcluster_a_general_betaJM_unconditional_vector (O := fun n => Fin (n + 3))
    Dw_le Pw gXt gOm (fun _ => 1) guSign gBhat (fun _ => 0)
    g_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    (fun n _ => (n : ℝ) + 3) (fun _ _ => 2) 1 1 zero_le_one zero_le_one
    (fun n o y => abs_gvSign_le n o y.2) g_hWvm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
  · exact Filter.Eventually.of_forall fun _ => by simpa using tendsto_steinRate_witness

/-- The hypotheses of `cltcluster_b_general_betaJM_unconditional_vector` hold on this model. -/
theorem cltcluster_b_general_betaJM_unconditional_vector_witness :
    (∀ n : ℕ, ∃ a b c : Fin (n + 3),
        pathG (n + 3) a b ∧ pathG (n + 3) b c ∧ ¬ pathG (n + 3) a c)
    ∧ (∀ (n : ℕ) (o : Fin (n + 3)) (y : Aw), (guSign n o y) ^ 4 = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2)) (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (guSign n)) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => restrictedStat (gXt n y) (gOm n y)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) (gBhat n y - (0 : Fin 1 → ℝ))) atTop
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (fun _ => Pw)
        (stdGaussian (EuclideanSpace ℝ (Fin 1))) := by
  refine ⟨pathG_not_transitive, guSign_pow_four, g_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine cltcluster_b_general_betaJM_unconditional_vector (O := fun n => Fin (n + 3))
    Dw_le Pw gXt gOm (fun _ => 1) guSign gBhat (fun _ => 0)
    g_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    (fun n _ => (n : ℝ) + 3) (fun _ _ => 2) 1 1 zero_lt_one zero_lt_one
    g_hWvm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun y : Aw => (guSign n o y) ^ 4) = fun _ => (1 : ℝ) :=
      funext (guSign_pow_four n o)
    rw [h]
    exact integrable_const 1
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun y : Aw => (guSign n o y) ^ 4) = fun _ => (1 : ℝ) :=
      funext (guSign_pow_four n o)
    rw [h]
    simp
  · exact Filter.Eventually.of_forall fun _ _ => by norm_num
  · refine Filter.Eventually.of_forall fun _ n => ?_
    rw [Fintype.card_fin]
    omega
  · exact Filter.Eventually.of_forall fun _ => by simpa using tendsto_steinRate_witness

end FrozenGeneralWitness

end FrozenGeneralVectorWitness


/-! ## Part (b) at `J = 1`

`cltcluster_b_oneDimension_betaJM` states Theorem 5(b) with a cluster map `g_n` (`hshare`) and a
cluster-size bound `Ḡ_n`, as a specialization of `cltcluster_b_general_betaJM` at `D_n := Ḡ_n`.
The rate is `(n/D_n)^{1/3}δ_n → 0`. The side conditions `hGb1` (`Ḡ_n ≥ 1`) and `hGbN`
(`Ḡ_n ≤ n`) make `Ḡ_n` a valid degree sequence. -/

section PartBOneDimension

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.Multilinear

/-- **Theorem 5(b) at `J = 1`, for `β̂_JM`.** The hypotheses are those of
`cltcluster_b_general_betaJM`, with the degree bound `hdeg` replaced by `hshare` (the dependency
graph is "same cluster") and `hGb` (`Ḡ_n` bounds every cluster). -/
theorem cltcluster_b_oneDimension_betaJM
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Gp : ℕ → Type*} [∀ n, Fintype (Gp n)] [∀ n, DecidableEq (Gp n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Om : ∀ n, Matrix (O n) (O n) ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, O n → Gp n)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ g n o = g n o')
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
    (Gb : ℕ → ℕ) (hGb1 : ∀ n, 1 ≤ Gb n) (hGbN : ∀ n, Gb n ≤ Fintype.card (O n))
    (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hrate : Tendsto (fun n => steinRate (Fintype.card (O n)) (Gb n) (lmin n)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (Om n) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine cltcluster_b_general_betaJM μ Xt Om Rn ν bhat β Dv hscore hA lmin hlmin hfloor hOm
    hmean B C4 hB0 hC40 hB hint4 hfour Gb hGb1 hGbN ?_ hrate b hb s
  intro n o
  rw [nbhd_eq_cluster (Dv n) (hshare n) o]
  exact le_trans (hGb n (g n o)) (Nat.le_succ _)

/-- A fair sign has fourth power `1`. -/
theorem sign2_pow_four {m : ℕ} (i : Fin m) (ω : Fin m → Bool) : (sign2 i ω) ^ 4 = 1 := by
  unfold sign2
  by_cases h : ω i <;> norm_num [h]

/-- In the example at `J = 1`, `D_n = 1` and `λ_min(Ω_n) = n+1`, so
`(n/D_n)^{1/3}δ_n = (n+1)^{-2/3} ≤ (n+1)^{-1/2} → 0`. -/
theorem tendsto_steinRate_oneDimension_witness :
    Tendsto (fun n : ℕ => steinRate (n + 1) 1 ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hbd : ∀ n : ℕ, steinRate (n + 1) 1 ((n : ℝ) + 1) ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by
    intro n
    have hxpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hspos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hxpos
    have hacc : accumRate (n + 1) 1 ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by
      unfold accumRate
      have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hc]
      have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
      rw [h1]
      field_simp
    have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
      push_cast
      rw [le_div_iff₀ (by norm_num)]
      linarith
    have hrp : (((n + 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
        ≤ (((n + 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
    have hsq : (((n + 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)
        = Real.sqrt (((n + 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) := (Real.sqrt_eq_rpow _).symm
    have hle : Real.sqrt (((n + 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ≤ Real.sqrt ((n : ℝ) + 1) := by
      refine Real.sqrt_le_sqrt ?_
      push_cast
      linarith
    have hfin : Real.sqrt ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))
        = 1 / Real.sqrt ((n : ℝ) + 1) := by
      rw [eq_div_iff (ne_of_gt hspos)]
      have hxs : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      field_simp
      nlinarith [hxs]
    unfold steinRate
    rw [hacc, ← hfin]
    refine mul_le_mul_of_nonneg_right ((hrp.trans (le_of_eq hsq)).trans hle) (by positivity)
  refine squeeze_zero (fun n => steinRate_nonneg _ _ _) hbd ?_
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    hsqrt.inv_tendsto_atTop
  simpa [div_eq_mul_inv] using hinv

/-- The hypotheses of `cltcluster_b_oneDimension_betaJM` hold with `n+1` observations, one
regressor `x̃_o = 1`, `𝓡_n = I_1`, `Ω_n = X̃'X̃ = n+1`, singleton clusters and one fair sign per
observation. The first conjunct states that the fourth moment is `1`. -/
theorem cltcluster_b_oneDimension_betaJM_witness (s : ℝ) :
    (∀ (n : ℕ) (o : Fin (n + 1)) (ω : Fin (n + 1) → Bool), (sign2 o ω) ^ 4 = 1)
    ∧ Tendsto (fun n => ((coins (n + 1)).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt n)ᵀ * redXt n)⁻¹ *ᵥ ((redXt n)ᵀ *ᵥ (fun o => sign2 o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine ⟨fun n o ω => sign2_pow_four o ω, ?_⟩
  refine cltcluster_b_oneDimension_betaJM (O := fun n => Fin (n + 1))
    (Gp := fun n => Fin (n + 1)) (fun n => coins (n + 1)) redXt (fun n => 1) (fun n => 1)
    (fun _ o => sign2 o)
    (fun n ω => ((redXt n)ᵀ * redXt n)⁻¹ *ᵥ ((redXt n)ᵀ *ᵥ (fun o => sign2 o ω)))
    (fun _ => 0) (fun _ => id) redDep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    redXt_scoreMap_isUnit (fun n => (n : ℝ) + 1) (fun n => by positivity) ?_ red_second_moment
    (fun n o => integral_sign2 o) 1 1 zero_lt_one zero_lt_one ?_ ?_ ?_
    (fun _ => 1) (fun _ => le_refl 1) ?_ ?_ ?_ (fun _ => (1 : ℝ)) ?_ s
  · intro n
    rw [redXt_scoreVar]
  · intro _ _
    simp [redXt, dotProduct]
  · intro n o
    have h : (fun ω : Fin (n + 1) → Bool => (sign2 o ω) ^ 4) = fun _ => (1 : ℝ) :=
      funext (sign2_pow_four o)
    rw [h]
    exact integrable_const 1
  · intro n o
    have h : (fun ω : Fin (n + 1) → Bool => (sign2 o ω) ^ 4) = fun _ => (1 : ℝ) :=
      funext (sign2_pow_four o)
    rw [h]
    simp
  · intro n
    rw [Fintype.card_fin]
    omega
  · intro _ _
    refine Finset.card_le_one.mpr (fun a ha c hc => ?_)
    rw [mem_cluster] at ha hc
    simpa using ha.trans hc.symm
  · simp only [Fintype.card_fin]
    exact tendsto_steinRate_oneDimension_witness
  · simp [dotProduct]

end PartBOneDimension

end Multiway.SteinCluster
