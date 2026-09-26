import Multiway.JointProjection
import Multiway.BrownCLT.Lindeberg
import Multiway.CLTMartingale
import Multiway.Multilinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.CramerWold
import Mathlib.Probability.HasLawExists
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Asymptotic normality of the joint-projection Mundlak estimator

This file formalizes Theorem 4 of the paper (Asymptotic normality of the joint-projection
Mundlak estimator). Part (a), under Regime 1 (multiway error components), is proved through the
triangular-array Lindeberg central limit theorem of `Multiway/BrownCLT/Lindeberg.lean` and the
Cramér–Wold device; part (b), under Regime 2, is reduced to a directional score limit. The
limit is written as `H⁻¹Z` with `Z ∼ N(0,S)`, which has law `N(0, H⁻¹SH⁻¹)` since `H⁻¹` is
symmetric.

## Main results

* `clt_a`, `clt_a_of_gram_limit`: the limit laws of part (a) for `β̂_JM` and `β̂_MFE`.
* `clt_a_consistency`, `clt_b_consistency`: consistency `β̂ ⟶^p β` in both regimes.
* `clt_a_unconditional_of_design`: the unconditional limit law, with a random design.
* `clt_b`: the limit laws of part (b).
* `variance_score_eq`, `variance_score_eq_E2`: the variance identities for the score.
-/

open Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Matrix

namespace Multiway
namespace CLT

/-! ### Convergence in distribution -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Transport the limit of a convergence in distribution to any variable with the same law;
unlike `TendstoInDistribution.congr`, no almost-everywhere equality is required. -/
theorem tendstoInDistribution_of_law_eq {ι E Ω' Ω'' : Type*} {mE : MeasurableSpace E}
    [TopologicalSpace E] [OpensMeasurableSpace E] {l : Filter ι}
    {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mΩ'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {X : ι → Ω → E} {Z : Ω' → E} {W : Ω'' → E}
    (h : TendstoInDistribution X l Z (fun _ => P) μ')
    (hW : AEMeasurable W μ'') (hlaw : μ''.map W = μ'.map Z) :
    TendstoInDistribution X l W (fun _ => P) μ'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hW
  tendsto := by
    rw! [hlaw]
    exact h.tendsto

/-- The degenerate case of the Cramér--Wold reduction, at `t = 0`: the constant sequence `0`
converges in distribution to the constant `0` on any probability space. -/
theorem tendstoInDistribution_zero {Ω'' : Type*} [MeasurableSpace Ω''] {μ'' : Measure Ω''}
    [IsProbabilityMeasure μ''] :
    TendstoInDistribution (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ : Ω'' => (0 : ℝ))
      (fun _ => P) μ'' := by
  refine tendstoInDistribution_of_law_eq
    (tendstoInDistribution_const (Z := fun _ : Ω => (0 : ℝ)) (l := atTop) aemeasurable_const)
    aemeasurable_const ?_
  simp [Measure.map_const]

/-- Convergence in distribution is transported along an almost-everywhere equality that holds
only eventually in `n`. -/
theorem tendstoInDistribution_of_eventually_ae_eq {E Ω'' : Type*} {mE : MeasurableSpace E}
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {mΩ'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {X Y : ℕ → Ω → E} {W : Ω'' → E}
    (h : TendstoInDistribution X atTop W (fun _ => P) μ'')
    (hY : ∀ n, AEMeasurable (Y n) P)
    (hXY : ∀ᶠ n in atTop, X n =ᵐ[P] Y n) :
    TendstoInDistribution Y atTop W (fun _ => P) μ'' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    refine h.tendsto.congr' ?_
    filter_upwards [hXY] with n hn
    exact Subtype.ext (Measure.map_congr hn)

/-! ### Units of `E →L[ℝ] E` -/

/-- A continuous linear endomorphism of a finite-dimensional real inner product space with
positive definite quadratic form is invertible. -/
theorem isUnit_of_inner_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (h : ∀ a : E, a ≠ 0 → 0 < ⟪a, T a⟫) : IsUnit T := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj : Function.Injective ⇑T := by
    intro a b hab
    by_contra hne
    have hd : a - b ≠ 0 := sub_ne_zero.2 hne
    have hpos := h (a - b) hd
    rw [map_sub, hab, sub_self, inner_zero_right] at hpos
    exact lt_irrefl 0 hpos
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (T : E →ₗ[ℝ] E))).1 hinj⟩

/-- A nonzero scalar multiple of a unit is a unit. -/
theorem isUnit_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E →L[ℝ] E} (hT : IsUnit T) {c : ℝ} (hc : c ≠ 0) : IsUnit (c • T) := by
  have h1 : IsUnit (c • (1 : E →L[ℝ] E)) := by
    refine ⟨⟨c • (1 : E →L[ℝ] E), c⁻¹ • (1 : E →L[ℝ] E), ?_, ?_⟩, rfl⟩ <;>
      rw [smul_mul_smul_comm, one_mul]
    · rw [mul_inv_cancel₀ hc, one_smul]
    · rw [inv_mul_cancel₀ hc, one_smul]
  have h2 : c • T = (c • (1 : E →L[ℝ] E)) * T := by rw [smul_mul_assoc, one_mul]
  rw [h2]
  exact h1.mul hT

/-- The continuous mapping theorem for inversion at an invertible limit, via
`NormedRing.inverse_continuousAt`. -/
theorem tendsto_inverse {R : Type*} [NormedRing R] [CompleteSpace R] [HasSummableGeomSeries R]
    {f : ℕ → R} {x : R} (hf : Tendsto f atTop (𝓝 x)) (hx : IsUnit x) :
    Tendsto (fun n => Ring.inverse (f n)) atTop (𝓝 (Ring.inverse x)) := by
  obtain ⟨u, rfl⟩ := hx
  exact ((NormedRing.inverse_continuousAt u).tendsto).comp hf

/-- A deterministic sequence converges in probability to its ordinary limit. -/
theorem tendstoInMeasure_of_tendsto_const {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] {a : ℕ → E} {c : E} (h : Tendsto a atTop (𝓝 c)) :
    TendstoInMeasure P (fun n _ => a n) atTop (fun _ => c) :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (Filter.Eventually.of_forall fun _ => h)

/-! ### The scalar Lindeberg CLT for a weighted sum -/

/-- The scalar central limit theorem for `Y_{n,o} = n^{-1/2} w_{n,o} ε_o` with deterministic
weights. `hSn` is the variance condition, and `hlin4` (`n^{-2}∑_o w_{n,o}^4 → 0`) together with
the fourth-moment bound `hmom` yields the Lindeberg condition. -/
theorem scalar_clt {O : ℕ → Type} [∀ n, Fintype (O n)] (hcard : ∀ n, Fintype.card (O n) = n)
    (w : ∀ n, O n → ℝ) (e : ∀ n, O n → Ω → ℝ) (sev : ∀ n, O n → ℝ) (C σ2 : ℝ)
    (hmeas : ∀ n o, Measurable (e n o))
    (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n o, ∫ ω, e n o ω ∂P = 0)
    (hL2 : ∀ n o, MemLp (e n o) 2 P)
    (hint4 : ∀ n o, Integrable (fun ω => e n o ω ^ 4) P)
    (hvar : ∀ n o, Var[e n o; P] = sev n o)
    (hmom : ∀ n o, ∫ ω, e n o ω ^ 4 ∂P ≤ C)
    (hσ2 : 0 < σ2)
    (hSn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ o, w n o ^ 2 * sev n o) atTop (𝓝 σ2))
    (hlin4 : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ * ∑ o, w n o ^ 4) atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ o, w n o * e n o ω) atTop
      (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 σ2.toNNReal) := by
  classical
  set σ : ℝ := Real.sqrt σ2 with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hσ2
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt hσ2.le
  set q : (n : ℕ) → Fin n → O n := fun n i => (Fintype.equivFinOfCardEq (hcard n)).symm i with hq
  have hsum : ∀ (n : ℕ) (f : O n → ℝ), ∑ i : Fin n, f (q n i) = ∑ o, f o := fun n f =>
    Equiv.sum_comp _ f
  set c : (n : ℕ) → Fin n → ℝ := fun n i => (σ * Real.sqrt n)⁻¹ * w n (q n i) with hc
  set A : (n : ℕ) → Fin n → Ω → ℝ := fun n i ω => c n i * e n (q n i) ω with hA
  have hsqn : ∀ n : ℕ, (Real.sqrt n) ^ 2 = (n : ℝ) := fun n => Real.sq_sqrt (Nat.cast_nonneg n)
  have hc2 : ∀ (n : ℕ) (i : Fin n), c n i ^ 2 = (σ2 * n)⁻¹ * w n (q n i) ^ 2 := by
    intro n i
    simp only [hc, mul_pow, inv_pow, hsqn, hσsq]
  have hmeasA : ∀ (n : ℕ) (i : Fin n), Measurable (A n i) := fun n i =>
    (hmeas n (q n i)).const_mul _
  have hindepA : ∀ n : ℕ, iIndepFun (A n) P := by
    intro n
    have h1 : iIndepFun (fun i : Fin n => e n (q n i)) P := (hindep n).precomp (Equiv.injective _)
    exact h1.comp _ (fun i => measurable_const_mul (c n i))
  have hL2A : ∀ (n : ℕ) (i : Fin n), MemLp (A n i) 2 P := fun n i =>
    (hL2 n (q n i)).const_mul _
  have hmeanA : ∀ (n : ℕ) (i : Fin n), ∫ ω, A n i ω ∂P = 0 := by
    intro n i
    simp only [hA, integral_const_mul, hmean, mul_zero]
  have hvarA : ∀ n : ℕ, ∑ i, Var[A n i; P] = σ2⁻¹ * ((n : ℝ)⁻¹ * ∑ o, w n o ^ 2 * sev n o) := by
    intro n
    have h1 : ∀ i : Fin n, Var[A n i; P] = (σ2 * n)⁻¹ * (w n (q n i) ^ 2 * sev n (q n i)) := by
      intro i
      rw [hA]
      rw [variance_const_mul, hvar, hc2, mul_assoc]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum,
      hsum n (fun o => w n o ^ 2 * sev n o), mul_inv]
    ring
  have hvarlim : Tendsto (fun n : ℕ => ∑ i, Var[A n i; P]) atTop (𝓝 1) := by
    have := hSn.const_mul σ2⁻¹
    rw [inv_mul_cancel₀ (ne_of_gt hσ2)] at this
    exact this.congr (fun n => (hvarA n).symm)
  have hint4A : ∀ (n : ℕ) (i : Fin n), Integrable (fun ω => A n i ω ^ 4) P := by
    intro n i
    simpa [hA, mul_pow] using (hint4 n (q n i)).const_mul (c n i ^ 4)
  have hc4 : ∀ (n : ℕ) (i : Fin n), c n i ^ 4 = ((σ2 * n) ^ 2)⁻¹ * w n (q n i) ^ 4 := by
    intro n i
    have h : c n i ^ 4 = (c n i ^ 2) ^ 2 := by ring
    rw [h, hc2]
    ring
  have hA4 : ∀ (n : ℕ) (i : Fin n),
      ∫ ω, A n i ω ^ 4 ∂P = c n i ^ 4 * ∫ ω, e n (q n i) ω ^ 4 ∂P := by
    intro n i
    simp [hA, mul_pow, integral_const_mul]
  have hlinA : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => ∑ i, ∫ ω in {ω | δ < |A n i ω|}, A n i ω ^ 2 ∂P) atTop (𝓝 0) := by
    intro δ hδ
    have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
    have hterm : ∀ (n : ℕ) (i : Fin n),
        ∫ ω in {ω | δ < |A n i ω|}, A n i ω ^ 2 ∂P ≤ (δ ^ 2)⁻¹ * (c n i ^ 4 * C) := by
      intro n i
      have hset : MeasurableSet {ω | δ < |A n i ω|} :=
        measurableSet_lt measurable_const (hmeasA n i).abs
      have hle : ∫ ω in {ω | δ < |A n i ω|}, A n i ω ^ 2 ∂P
          ≤ ∫ ω in {ω | δ < |A n i ω|}, (δ ^ 2)⁻¹ * A n i ω ^ 4 ∂P := by
        refine setIntegral_mono_on ((hL2A n i).integrable_sq.integrableOn)
          (((hint4A n i).const_mul _).integrableOn) hset ?_
        intro ω hω
        have hω' : δ < |A n i ω| := hω
        have h1 : δ ^ 2 < A n i ω ^ 2 := by nlinarith [sq_abs (A n i ω), abs_nonneg (A n i ω)]
        rw [inv_mul_eq_div, le_div_iff₀ hδ2]
        nlinarith [sq_nonneg (A n i ω), sub_pos.mpr h1]
      refine hle.trans ?_
      have h2 : ∫ ω in {ω | δ < |A n i ω|}, (δ ^ 2)⁻¹ * A n i ω ^ 4 ∂P
          ≤ ∫ ω, (δ ^ 2)⁻¹ * A n i ω ^ 4 ∂P := by
        refine setIntegral_le_integral ((hint4A n i).const_mul _) ?_
        filter_upwards with ω
        positivity
      refine h2.trans ?_
      rw [integral_const_mul, hA4]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hmom n (q n i)) (by positivity)) (by positivity)
    refine squeeze_zero (fun n => Finset.sum_nonneg fun i _ =>
        setIntegral_nonneg (measurableSet_lt measurable_const (hmeasA n i).abs)
          (fun ω _ => sq_nonneg _)) (fun n => ?_)
      (?_ : Tendsto (fun n : ℕ => ((δ ^ 2)⁻¹ * C * (σ2 ^ 2)⁻¹) *
        (((n : ℝ) ^ 2)⁻¹ * ∑ o, w n o ^ 4)) atTop (𝓝 0))
    · refine (Finset.sum_le_sum fun i _ => hterm n i).trans (le_of_eq ?_)
      have h3 : ∀ i : Fin n, (δ ^ 2)⁻¹ * (c n i ^ 4 * C)
          = ((δ ^ 2)⁻¹ * C * (σ2 ^ 2)⁻¹ * ((n : ℝ) ^ 2)⁻¹) * w n (q n i) ^ 4 := by
        intro i
        rw [hc4, mul_pow]
        ring
      rw [Finset.sum_congr rfl (fun i _ => h3 i), ← Finset.mul_sum,
        hsum n (fun o => w n o ^ 4)]
      ring
    · simpa using hlin4.const_mul ((δ ^ 2)⁻¹ * C * (σ2 ^ 2)⁻¹)
  have hZ : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have T1 := StatLean.HypothesisTesting.lindeberg_clt hmeasA hindepA hL2A hmeanA hvarlim hlinA hZ
  have T2 := T1.continuous_comp (g := fun x : ℝ => σ * x) (by fun_prop)
  have hlaw : (gaussianReal 0 σ2.toNNReal).map (id : ℝ → ℝ)
      = (gaussianReal (0 : ℝ) 1).map ((fun x : ℝ => σ * x) ∘ (id : ℝ → ℝ)) := by
    rw [Measure.map_id]
    show _ = (gaussianReal (0 : ℝ) 1).map (fun x : ℝ => σ * x)
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · rw [mul_one]
      refine NNReal.coe_injective ?_
      simp [Real.coe_toNNReal _ hσ2.le, hσsq]
  have T3 := tendstoInDistribution_of_law_eq T2 aemeasurable_id hlaw
  have hrow : ∀ (n : ℕ) (ω : Ω),
      σ * ∑ i, A n i ω = (Real.sqrt n)⁻¹ * ∑ o, w n o * e n o ω := by
    intro n ω
    have h1 : ∀ i : Fin n, A n i ω = (σ * Real.sqrt n)⁻¹ * (w n (q n i) * e n (q n i) ω) := by
      intro i; rw [hA, hc]; ring
    have h2 : σ * (σ * Real.sqrt n)⁻¹ = (Real.sqrt n)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hσpos.ne', one_mul]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum,
      hsum n (fun o => w n o * e n o ω), ← mul_assoc, h2]
  refine T3.congr (fun n => ?_) (by rfl)
  filter_upwards with ω
  exact hrow n ω

/-! ### The Cramér–Wold step -/

variable {K : ℕ}

/-- The law of a linear functional of a centered multivariate Gaussian. -/
theorem map_inner_multivariateGaussian {S : Matrix (Fin K) (Fin K) ℝ} (hS : S.PosSemidef)
    (t : EuclideanSpace ℝ (Fin K)) :
    (multivariateGaussian 0 S).map (fun x => ⟪x, t⟫)
      = gaussianReal 0 (t ⬝ᵥ (S *ᵥ t)).toNNReal := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin K) => ⟪x, t⟫)
      = fun x : EuclideanSpace ℝ (Fin K) => (innerSL ℝ t) x := by
    funext x; exact (real_inner_comm x t).symm
  rw [hfun]
  have hgl : HasGaussianLaw (fun x : EuclideanSpace ℝ (Fin K) => (innerSL ℝ t) x)
      (multivariateGaussian 0 S) :=
    (IsGaussian.hasGaussianLaw_id
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin K)) S)).map_fun (innerSL ℝ t)
  rw [hgl.map_eq_gaussianReal]
  congr 1
  · rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian, map_zero]
  · have hvar : Var[fun x : EuclideanSpace ℝ (Fin K) => (innerSL ℝ t) x;
        multivariateGaussian 0 S] = t ⬝ᵥ (S *ᵥ t) := by
      simp only [innerSL_apply_apply]
      rw [← covariance_self (by fun_prop),
        ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id t t,
        covarianceBilin_multivariateGaussian hS]
    rw [hvar]

/-- `t'St > 0` for `t ≠ 0` when `S ≻ 0`, in the `EuclideanSpace` packaging. -/
theorem dotProduct_mulVec_pos_of_posDef {S : Matrix (Fin K) (Fin K) ℝ} (hS : S.PosDef)
    {t : EuclideanSpace ℝ (Fin K)} (ht : t ≠ 0) : 0 < t ⬝ᵥ (S *ᵥ t) := by
  have h : (t.ofLp : Fin K → ℝ) ≠ 0 := by simpa using ht
  simpa using hS.dotProduct_mulVec_pos (x := (t.ofLp : Fin K → ℝ)) h

/-- The score central limit theorem: `n^{-1/2}∑_o x̃_o ε_o ⟶^d N(0,S)`, by the scalar CLT in
each direction and the Cramér–Wold device. -/
theorem score_clt {O : ℕ → Type} [∀ n, Fintype (O n)] (hcard : ∀ n, Fintype.card (O n) = n)
    (xt : ∀ n, O n → EuclideanSpace ℝ (Fin K))
    (e : ∀ n, O n → Ω → ℝ) (sev : ∀ n, O n → ℝ) (C : ℝ)
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    (hmeas : ∀ n o, Measurable (e n o))
    (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n o, ∫ ω, e n o ω ∂P = 0)
    (hL2 : ∀ n o, MemLp (e n o) 2 P)
    (hint4 : ∀ n o, Integrable (fun ω => e n o ω ^ 4) P)
    (hvar : ∀ n o, Var[e n o; P] = sev n o)
    (hmom : ∀ n o, ∫ ω, e n o ω ^ 4 ∂P ≤ C)
    (hSn : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ o, ⟪xt n o, t⟫ ^ 2 * sev n o) atTop
        (𝓝 (t ⬝ᵥ (Smat *ᵥ t))))
    (hlin4 : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ * ∑ o, ⟪xt n o, t⟫ ^ 4) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ • ∑ o, e n o ω • xt n o) atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Smat) := by
  have hmeasW : ∀ n : ℕ, Measurable (fun ω => (Real.sqrt n)⁻¹ • ∑ o, e n o ω • xt n o) := by
    intro n
    have hterm : ∀ o : O n, Measurable (fun ω => e n o ω • xt n o) := by
      intro o
      have h := hmeas n o
      fun_prop
    exact (Finset.measurable_sum _ (fun o _ => hterm o)).const_smul
      ((Real.sqrt n)⁻¹ : ℝ)
  have hproj : ∀ (n : ℕ) (ω : Ω) (t : EuclideanSpace ℝ (Fin K)),
      ⟪(Real.sqrt n)⁻¹ • ∑ o, e n o ω • xt n o, t⟫
        = (Real.sqrt n)⁻¹ * ∑ o, ⟪xt n o, t⟫ * e n o ω := by
    intro n ω t
    rw [real_inner_smul_left, sum_inner]
    congr 1
    exact Finset.sum_congr rfl (fun o _ => by rw [real_inner_smul_left]; ring)
  refine TendstoInDistribution.of_inner (by fun_prop) (fun n => (hmeasW n).aemeasurable) ?_
  intro t
  by_cases ht : t = 0
  · subst ht
    simpa using
      (tendstoInDistribution_zero (P := P) (μ'' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin K)) Smat))
  · have hσ2 : 0 < t ⬝ᵥ (Smat *ᵥ t) := dotProduct_mulVec_pos_of_posDef hSpd ht
    have T := scalar_clt (P := P) hcard (fun n o => ⟪xt n o, t⟫) e sev C _ hmeas hindep hmean
      hL2 hint4 hvar hmom hσ2 (hSn t) (hlin4 t)
    have hlaw : (multivariateGaussian 0 Smat).map (fun x => ⟪x, t⟫)
        = (gaussianReal 0 (t ⬝ᵥ (Smat *ᵥ t)).toNNReal).map (id : ℝ → ℝ) := by
      rw [Measure.map_id, map_inner_multivariateGaussian hSpd.posSemidef t]
    have T2 := tendstoInDistribution_of_law_eq T (by fun_prop) hlaw
    refine T2.congr (fun n => ?_) (by rfl)
    filter_upwards with ω
    exact (hproj n ω t).symm


/-! ### Design algebra: `x̃_o`, `X̃'ν`, `X̃'X̃` and exact absorption -/

section Design

variable {K : ℕ} {O : Type*} [Fintype O]

omit [Fintype O] in
/-- Coordinatewise evaluation of a finite sum of `EuclideanSpace` vectors. -/
lemma euclideanSum_apply {ι : Type*} (s : Finset ι) (f : ι → EuclideanSpace ℝ O) (o : O) :
    (∑ i ∈ s, f i) o = ∑ i ∈ s, f i o := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/-- The standard basis expansion in `ℝ^K`. -/
lemma eq_sum_single (a : EuclideanSpace ℝ (Fin K)) :
    a = ∑ k : Fin K, a k • (EuclideanSpace.single k (1 : ℝ)) := by
  ext j
  rw [euclideanSum_apply]
  simp [PiLp.single_apply]

/-- The within row `x̃_o ∈ ℝ^K`: the `o`-th row of `X̃ = Q_[Δ]X`. -/
noncomputable def withinRow (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (o : O) :
    EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 fun k : Fin K => jointWithin S (X (EuclideanSpace.single k (1 : ℝ))) o

/-- `a'x̃_o = (Q_[Δ]Xa)_o`: the defining property of the within rows. -/
lemma inner_withinRow (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (a : EuclideanSpace ℝ (Fin K)) (o : O) :
    ⟪a, withinRow S X o⟫ = jointWithin S (X a) o := by
  have h : X a = ∑ k : Fin K, a k • X (EuclideanSpace.single k (1 : ℝ)) := by
    conv_lhs => rw [eq_sum_single a]
    simp [map_sum]
  rw [h]
  simp only [map_sum, map_smul, withinRow, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [euclideanSum_apply]
  exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]

/-- The score `X̃'v = ∑_o v_o x̃_o ∈ ℝ^K`. -/
noncomputable def score (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (v : EuclideanSpace ℝ O) :
    EuclideanSpace ℝ (Fin K) :=
  ∑ o : O, v o • withinRow S X o

/-- `a'(X̃'v) = (Q_[Δ]Xa)'v`. -/
lemma inner_score (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (a : EuclideanSpace ℝ (Fin K)) (v : EuclideanSpace ℝ O) :
    ⟪a, score S X v⟫ = ⟪jointWithin S (X a), v⟫ := by
  rw [score, inner_sum]
  simp only [real_inner_smul_right, inner_withinRow]
  simp [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

lemma score_add (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (u v : EuclideanSpace ℝ O) :
    score S X (u + v) = score S X u + score S X v := by
  refine ext_inner_left ℝ fun a => ?_
  rw [inner_add_right, inner_score, inner_score, inner_score, inner_add_right]

lemma score_smul (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (r : ℝ) (v : EuclideanSpace ℝ O) :
    score S X (r • v) = r • score S X v := by
  refine ext_inner_left ℝ fun a => ?_
  rw [real_inner_smul_right, inner_score, inner_score, real_inner_smul_right]

/-- The score annihilates every additive component (Theorem 3(c), via
`JointProjection.within_inner_dummy_eq_zero`). -/
lemma score_dummy_eq_zero {D : Type*} {Sm : D → Submodule ℝ (EuclideanSpace ℝ O)}
    {X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O} {m : D}
    {d : EuclideanSpace ℝ O} (hd : d ∈ Sm m) :
    score (⨆ k, Sm k) X d = 0 := by
  refine ext_inner_left ℝ fun a => ?_
  rw [inner_score, inner_zero_right]
  exact within_inner_dummy_eq_zero m hd a

/-- Exact absorption: `X̃'ν = X̃'ε` when `ν = ∑_m Δ_ma^{(m)} + ε`. -/
theorem score_absorb {D : Type*} [Fintype D] {Sm : D → Submodule ℝ (EuclideanSpace ℝ O)}
    {X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O}
    {d : D → EuclideanSpace ℝ O} (hd : ∀ m, d m ∈ Sm m) (v : EuclideanSpace ℝ O) :
    score (⨆ k, Sm k) X ((∑ m, d m) + v) = score (⨆ k, Sm k) X v := by
  rw [score_add]
  have hzero : score (⨆ k, Sm k) X (∑ m, d m) = 0 := by
    classical
    have : ∀ s : Finset D, score (⨆ k, Sm k) X (∑ m ∈ s, d m) = 0 := by
      intro s
      induction s using Finset.induction with
      | empty => simp [score]
      | insert m s hm ih =>
          rw [Finset.sum_insert hm, score_add, ih, score_dummy_eq_zero (hd m), add_zero]
    exact this Finset.univ
  rw [hzero, zero_add]

/-- The Gram map `a ↦ X̃'X̃a`. -/
noncomputable def gram (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (a : EuclideanSpace ℝ (Fin K)) :
    EuclideanSpace ℝ (Fin K) :=
  score S X (X a)

lemma gram_smul (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (r : ℝ)
    (a : EuclideanSpace ℝ (Fin K)) : gram S X (r • a) = r • gram S X a := by
  rw [gram, gram, map_smul, score_smul]

lemma gram_add (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (a b : EuclideanSpace ℝ (Fin K)) :
    gram S X (a + b) = gram S X a + gram S X b := by
  rw [gram, gram, gram, map_add, score_add]

/-- `X̃'X̃` as an element of the normed ring `ℝ^K →L[ℝ] ℝ^K`. -/
noncomputable def gramCLM (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) :
    EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  LinearMap.toContinuousLinearMap
    { toFun := gram S X
      map_add' := gram_add S X
      map_smul' := gram_smul S X }

@[simp] lemma gramCLM_apply (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (a : EuclideanSpace ℝ (Fin K)) :
    gramCLM S X a = gram S X a := rfl

/-- `a'X̃'X̃a = (Xa)'Q_[Δ](Xa)`. -/
theorem inner_gram_self (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (a : EuclideanSpace ℝ (Fin K)) :
    ⟪a, gram S X a⟫ = ⟪X a, jointWithin S (X a)⟫ := by
  rw [gram, inner_score, inner_jointWithin_comp' S (X a) (X a),
    ← inner_jointWithin_comp S (X a) (X a)]

/-- Identification makes `X̃'X̃` invertible. -/
theorem isUnit_gramCLM (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (hid : Identified S X) :
    IsUnit (gramCLM S X) := by
  refine isUnit_of_inner_pos fun a ha => ?_
  rw [gramCLM_apply, inner_gram_self]
  exact (identified_iff_inner_pos S X).1 hid a ha

/-- The score equation `X̃'X̃(b - β) = X̃'ν` for a multiway fixed-effects slope `b`, under
`y = Xβ + s + ν` with `s ∈ 𝒮`. -/
theorem gram_sub_eq_score {S : Submodule ℝ (EuclideanSpace ℝ O)}
    {X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O} {y s v : EuclideanSpace ℝ O}
    {β b : EuclideanSpace ℝ (Fin K)}
    (hy : y = X β + s + v) (hs : s ∈ S) (hb : IsMFESlope S X y b) :
    gram S X (b - β) = score S X v := by
  refine ext_inner_left ℝ fun a => ?_
  have h1 : ⟪jointWithin S (X a), y - X b⟫ = 0 := by
    rw [inner_jointWithin_comp' S (X a) (y - X b), ← inner_jointWithin_comp S (X a) (y - X b)]
    exact hb a
  have hyb : y - X b = X (β - b) + s + v := by
    rw [hy, map_sub]; abel
  rw [hyb, inner_add_right, inner_add_right, inner_jointWithin_right hs] at h1
  rw [gram, inner_score, inner_score, map_sub]
  have h2 : (X b - X β) = -(X (β - b)) := by rw [map_sub]; abel
  rw [h2, inner_neg_right]
  linarith [h1]

/-- Conversely, any `b` solving `X̃'X̃(b - β) = X̃'ν` is a multiway fixed-effects slope. -/
theorem isMFESlope_of_gram_sub_eq_score {S : Submodule ℝ (EuclideanSpace ℝ O)}
    {X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O} {y s v : EuclideanSpace ℝ O}
    {β b : EuclideanSpace ℝ (Fin K)}
    (hy : y = X β + s + v) (hs : s ∈ S)
    (h : gram S X (b - β) = score S X v) : IsMFESlope S X y b := by
  intro a
  have hyb : y - X b = X (β - b) + s + v := by rw [hy, map_sub]; abel
  have key : ⟪jointWithin S (X a), y - X b⟫ = 0 := by
    rw [hyb, inner_add_right, inner_add_right, inner_jointWithin_right hs,
      ← inner_score, ← inner_score]
    have h4 : gram S X (β - b) = -(gram S X (b - β)) := by
      have hsm : (β - b) = (-1 : ℝ) • (b - β) := by module
      rw [hsm, gram_smul]
      simp
    show ⟪a, gram S X (β - b)⟫ + 0 + ⟪a, score S X v⟫ = 0
    rw [h4, h, inner_neg_right]
    ring
  rw [inner_jointWithin_comp S (X a) (y - X b), ← inner_jointWithin_comp' S (X a) (y - X b)]
  exact key

set_option linter.unusedSectionVars false in
/-- The score of a measurable `ℝ^𝒪`-valued variable is measurable. -/
theorem measurable_score (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) {f : Ω → EuclideanSpace ℝ O}
    (hf : ∀ o, Measurable fun ω => f ω o) : Measurable fun ω => score S X (f ω) :=
  Finset.measurable_sum _ fun o _ => (hf o).smul_const _

end Design


/-! ### From the score's limit law to the slope's -/

section Main

variable {K : ℕ}

/-- `(A_n)† t → Hinv† t` from `A_n → Hinv` in operator norm. -/
theorem tendsto_adjoint_apply {A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))}
    {Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)}
    (hAlim : Tendsto A atTop (𝓝 Hinv)) (t : EuclideanSpace ℝ (Fin K)) :
    Tendsto (fun n => (ContinuousLinearMap.adjoint (A n)) t) atTop
      (𝓝 ((ContinuousLinearMap.adjoint Hinv) t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (?_ : Tendsto (fun n => ‖A n - Hinv‖ * ‖t‖) atTop (𝓝 0))
  · have h : (ContinuousLinearMap.adjoint (A n)) t - (ContinuousLinearMap.adjoint Hinv) t
        = (ContinuousLinearMap.adjoint (A n - Hinv)) t := by
      rw [map_sub]; rfl
    rw [h]
    refine (ContinuousLinearMap.le_opNorm _ t).trans ?_
    exact mul_le_mul_of_nonneg_right
      (le_of_eq (LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _)) (norm_nonneg t)
  · have h0 : Tendsto (fun n => ‖A n - Hinv‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hAlim
    simpa using h0.mul_const ‖t‖

/-- From the score's limit law to the slope's, in either regime: given the limit law of
`n^{-1/2}X̃'ν` and `(n^{-1}X̃'X̃)^{-1} → H^{-1}`, Slutsky's theorem, applied one direction at a
time and assembled by Cramér–Wold, gives the limit law of `√n(β̂_MFE - β)`. -/
theorem slope_clt_of_score
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (Smat : Matrix (Fin K) (Fin K) ℝ)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ • score (⨆ m, Sm n m) (Xm n) (nu n ω)) atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Smat))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (b : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbmeas : ∀ n, AEMeasurable (b n) P)
    (hb : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (b n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (b n ω - β)) atTop
      (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  set W : ℕ → Ω → EuclideanSpace ℝ (Fin K) :=
    fun n ω => (Real.sqrt n)⁻¹ • score (⨆ m, Sm n m) (Xm n) (nu n ω) with hWdef
  have hgram : ∀ᶠ n : ℕ in atTop, ∀ ω : Ω,
      gram (⨆ m, Sm n m) (Xm n) (b n ω - β) = score (⨆ m, Sm n m) (Xm n) (nu n ω) := by
    filter_upwards [hb] with n hbn ω
    have hs : (∑ m, fe n m) ∈ (⨆ m, Sm n m) :=
      Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m (hfe n m)
    exact gram_sub_eq_score (hmodel n ω) hs (hbn ω)
  have hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω : Ω, Real.sqrt n • (b n ω - β) = A n (W n ω) := by
    filter_upwards [hgram, hAsolve, eventually_gt_atTop 0] with n hgn hAn hn ω
    have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hnn : (Real.sqrt n) * (Real.sqrt n) = (n : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hkey : ∀ r : ℝ, 0 < r → r * r = (n : ℝ) → (n : ℝ)⁻¹ * r = r⁻¹ := by
      intro r hr hrr
      rw [← hrr, mul_inv, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
    have hid : (n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) (Real.sqrt n • (b n ω - β)) = W n ω := by
      rw [gram_smul, hgn ω, smul_smul, hWdef]
      congr 1
      exact hkey _ hsq hnn
    rw [← hid, hAn]
  have hbW : ∀ n : ℕ, AEMeasurable (fun ω => Real.sqrt n • (b n ω - β)) P :=
    fun n => ((hbmeas n).sub_const β).const_smul (Real.sqrt n : ℝ)
  refine TendstoInDistribution.of_inner (by fun_prop) hbW ?_
  intro t
  have hY : TendstoInMeasure P
      (fun (n : ℕ) (_ : Ω) => (ContinuousLinearMap.adjoint (A n)) t) atTop
      (fun _ => (ContinuousLinearMap.adjoint Hinv) t) :=
    tendstoInMeasure_of_tendsto_const (tendsto_adjoint_apply hAlim t)
  have hSl := hscore.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) => ⟪p.1, p.2⟫)
    (by fun_prop) hY (fun n => aemeasurable_const)
  refine tendstoInDistribution_of_eventually_ae_eq
    (hSl.congr (fun _ => Filter.EventuallyEq.rfl) ?_)
    (fun n => (Continuous.measurable (by fun_prop :
      Continuous fun x : EuclideanSpace ℝ (Fin K) => ⟪x, t⟫)).comp_aemeasurable (hbW n)) ?_
  · filter_upwards with z
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rfl
  · filter_upwards [hsolve] with n hn
    filter_upwards with ω
    rw [hn ω, ← ContinuousLinearMap.adjoint_inner_right]

/-- **Theorem 4(a)** for `β̂_MFE`: `√n(β̂_MFE - β) ⟶^d H⁻¹Z` with `Z ∼ N(0,S)`. -/
theorem clt_a_mfe
    {O : ℕ → Type} [∀ n, Fintype (O n)] (hcard : ∀ n, Fintype.card (O n) = n)
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    -- the model: `y = Xβ + ∑_m Δ_mα^{(m)} + ν`
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    -- Regime 1: `ν = ∑_m Δ_ma^{(m)} + ε`
    (aa : ∀ n, Fin M → Ω → EuclideanSpace ℝ (O n)) (haa : ∀ n m ω, aa n m ω ∈ Sm n m)
    (e : ∀ n, O n → Ω → ℝ) (sev : ∀ n, O n → ℝ) (C : ℝ)
    (hregime : ∀ n ω, nu n ω = (∑ m, aa n m ω) + (WithLp.toLp 2 fun o => e n o ω))
    (hmeas : ∀ n o, Measurable (e n o)) (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n o, ∫ ω, e n o ω ∂P = 0) (hL2 : ∀ n o, MemLp (e n o) 2 P)
    (hint4 : ∀ n o, Integrable (fun ω => e n o ω ^ 4) P)
    (hvar : ∀ n o, Var[e n o; P] = sev n o)
    (hmom : ∀ n o, ∫ ω, e n o ω ^ 4 ∂P ≤ C)
    -- variance and design limits
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    (hSn : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 2 * sev n o) atTop (𝓝 (t ⬝ᵥ (Smat *ᵥ t))))
    (hlin4 : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ *
      ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 4) atTop (𝓝 0))
    -- `(n^{-1}X̃'X̃)^{-1} → H^{-1}`
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    -- `β̂_MFE`, by its normal equations
    (b : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbmeas : ∀ n, AEMeasurable (b n) P)
    (hb : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (b n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (b n ω - β)) atTop
      (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  set xt : ∀ n, O n → EuclideanSpace ℝ (Fin K) :=
    fun n o => withinRow (⨆ m, Sm n m) (Xm n) o with hxt
  have hscore := score_clt (P := P) hcard xt e sev C Smat hSpd hmeas hindep hmean hL2 hint4
    hvar hmom hSn hlin4
  -- exact absorption reduces the score to that of `ε`
  refine slope_clt_of_score Sm Xm β fe hfe nu yv hmodel Smat ?_ A Hinv hAsolve hAlim b hbmeas hb
  refine hscore.congr (fun n => ?_) (by rfl)
  filter_upwards with ω
  rw [hregime n ω, score_absorb (fun m => haa n m ω)]
  rfl


/-! ### The variance identity -/

set_option linter.unusedSectionVars false in
/-- `Var(X̃'ν ∣ 𝒟) = ∑_{o∈𝒪} x̃_ox̃_o'σ²_ε(o)` in the quadratic-form reading `t'Var(X̃'ν)t`,
along a realization of `𝒟`. Proved from exact absorption `X̃'ν = X̃'ε` and the variance of a
sum of independent terms. -/
theorem variance_score_eq {O : Type*} [Fintype O] {M : ℕ}
    (Sm : Fin M → Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (aa : Fin M → Ω → EuclideanSpace ℝ O) (haa : ∀ m ω, aa m ω ∈ Sm m)
    (e : O → Ω → ℝ) (sev : O → ℝ) (nu : Ω → EuclideanSpace ℝ O)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + (WithLp.toLp 2 fun o => e o ω))
    (hindep : iIndepFun e P)
    (hL2 : ∀ o, MemLp (e o) 2 P) (hvar : ∀ o, Var[e o; P] = sev o)
    (t : EuclideanSpace ℝ (Fin K)) :
    Var[fun ω => ⟪score (⨆ m, Sm m) X (nu ω), t⟫; P]
      = ∑ o, ⟪withinRow (⨆ m, Sm m) X o, t⟫ ^ 2 * sev o := by
  classical
  set xt : O → EuclideanSpace ℝ (Fin K) := fun o => withinRow (⨆ m, Sm m) X o with hxt
  set Y : O → Ω → ℝ := fun o ω => ⟪xt o, t⟫ * e o ω with hY
  have habs : ∀ ω, ⟪score (⨆ m, Sm m) X (nu ω), t⟫ = ∑ o, Y o ω := by
    intro ω
    rw [hregime ω, score_absorb (fun m => haa m ω)]
    have : score (⨆ m, Sm m) X (WithLp.toLp 2 fun o => e o ω) = ∑ o, e o ω • xt o := rfl
    rw [this, sum_inner]
    exact Finset.sum_congr rfl fun o _ => by rw [real_inner_smul_left, hY]; ring
  have hfun : (fun ω => ⟪score (⨆ m, Sm m) X (nu ω), t⟫) = ∑ o, Y o := by
    funext ω; rw [habs ω, Finset.sum_apply]
  rw [hfun]
  have hYL2 : ∀ o ∈ (Finset.univ : Finset O), MemLp (Y o) 2 P := fun o _ => (hL2 o).const_mul _
  have hYindep : Set.Pairwise (↑(Finset.univ : Finset O)) fun o o' => IndepFun (Y o) (Y o') P := by
    intro o _ o' _ hne
    exact ((hindep.indepFun hne).comp (measurable_const_mul _) (measurable_const_mul _))
  rw [IndepFun.variance_sum hYL2 hYindep]
  exact Finset.sum_congr rfl fun o _ => by rw [hY, variance_const_mul, hvar]

/-! ### Transfer to the joint-projection Mundlak estimator -/

/-- A joint-projection Mundlak slope is a multiway fixed-effects slope (Theorem 3(a)). -/
theorem isMFESlope_of_isAugSlope_jm {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F]
    {ι : E} {S : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hid : Identified S X) (hι : ι ∈ S)
    (y : E) (b : F) (h : IsAugSlope (jmControls ι S X) X y b) : IsMFESlope S X y b :=
  (jm_equiv hid hι y b).mp h


/-- **Theorem 4(a).** `√n(β̂_JM - β)` and `√n(β̂_MFE - β)` both converge in distribution to
`H⁻¹Z` with `Z ∼ N(0,S)`. -/
theorem clt_a
    {O : ℕ → Type} [∀ n, Fintype (O n)] (hcard : ∀ n, Fintype.card (O n) = n)
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (aa : ∀ n, Fin M → Ω → EuclideanSpace ℝ (O n)) (haa : ∀ n m ω, aa n m ω ∈ Sm n m)
    (e : ∀ n, O n → Ω → ℝ) (sev : ∀ n, O n → ℝ) (C : ℝ)
    (hregime : ∀ n ω, nu n ω = (∑ m, aa n m ω) + (WithLp.toLp 2 fun o => e n o ω))
    (hmeas : ∀ n o, Measurable (e n o)) (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n o, ∫ ω, e n o ω ∂P = 0) (hL2 : ∀ n o, MemLp (e n o) 2 P)
    (hint4 : ∀ n o, Integrable (fun ω => e n o ω ^ 4) P)
    (hvar : ∀ n o, Var[e n o; P] = sev n o)
    (hmom : ∀ n o, ∫ ω, e n o ω ^ 4 ∂P ≤ C)
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    (hSn : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 2 * sev n o) atTop (𝓝 (t ⬝ᵥ (Smat *ᵥ t))))
    (hlin4 : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ *
      ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 4) atTop (𝓝 0))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    -- identification and `ι_n ∈ 𝒮`
    (ιv : ∀ n, EuclideanSpace ℝ (O n)) (hι : ∀ n, ιv n ∈ ⨆ m, Sm n m)
    (hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, Sm n m) (Xm n))
    -- `β̂_JM` and `β̂_MFE`, by their normal equations
    (bJM bMFE : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbJMmeas : ∀ n, AEMeasurable (bJM n) P) (hbMFEmeas : ∀ n, AEMeasurable (bMFE n) P)
    (hbJM : ∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (ιv n) (⨆ m, Sm n m) (Xm n)) (Xm n)
      (yv n ω) (bJM n ω))
    (hbMFE : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (bMFE n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bJM n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat)
      ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bMFE n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine ⟨?_, ?_⟩
  · refine clt_a_mfe hcard Sm Xm β fe hfe nu yv hmodel aa haa e sev C hregime hmeas hindep
      hmean hL2 hint4 hvar hmom Smat hSpd hSn hlin4 A Hinv hAsolve hAlim bJM hbJMmeas ?_
    filter_upwards [hid, hbJM] with n hidn hbn ω
    exact isMFESlope_of_isAugSlope_jm hidn (hι n) _ _ (hbn ω)
  · exact clt_a_mfe hcard Sm Xm β fe hfe nu yv hmodel aa haa e sev C hregime hmeas hindep
      hmean hL2 hint4 hvar hmom Smat hSpd hSn hlin4 A Hinv hAsolve hAlim bMFE hbMFEmeas hbMFE


/-- **Theorem 4(a)** with the inverse Gram limit derived: from `n^{-1}X̃'X̃ → H` with `H`
positive definite, the inverses `A n = Ring.inverse (n^{-1}X̃'X̃)` and `Ring.inverse H` are
constructed. -/
theorem clt_a_of_gram_limit
    {O : ℕ → Type} [∀ n, Fintype (O n)] (hcard : ∀ n, Fintype.card (O n) = n)
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (aa : ∀ n, Fin M → Ω → EuclideanSpace ℝ (O n)) (haa : ∀ n m ω, aa n m ω ∈ Sm n m)
    (e : ∀ n, O n → Ω → ℝ) (sev : ∀ n, O n → ℝ) (C : ℝ)
    (hregime : ∀ n ω, nu n ω = (∑ m, aa n m ω) + (WithLp.toLp 2 fun o => e n o ω))
    (hmeas : ∀ n o, Measurable (e n o)) (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n o, ∫ ω, e n o ω ∂P = 0) (hL2 : ∀ n o, MemLp (e n o) 2 P)
    (hint4 : ∀ n o, Integrable (fun ω => e n o ω ^ 4) P)
    (hvar : ∀ n o, Var[e n o; P] = sev n o)
    (hmom : ∀ n o, ∫ ω, e n o ω ^ 4 ∂P ≤ C)
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    (hSn : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 2 * sev n o) atTop (𝓝 (t ⬝ᵥ (Smat *ᵥ t))))
    (hlin4 : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ *
      ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 4) atTop (𝓝 0))
    -- `n^{-1}X̃'X̃ → H`, with `H ≻ 0`
    (H : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hHpos : ∀ a : EuclideanSpace ℝ (Fin K), a ≠ 0 → 0 < ⟪a, H a⟫)
    (hHlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • gramCLM (⨆ m, Sm n m) (Xm n)) atTop (𝓝 H))
    (ιv : ∀ n, EuclideanSpace ℝ (O n)) (hι : ∀ n, ιv n ∈ ⨆ m, Sm n m)
    (hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, Sm n m) (Xm n))
    (bJM bMFE : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbJMmeas : ∀ n, AEMeasurable (bJM n) P) (hbMFEmeas : ∀ n, AEMeasurable (bMFE n) P)
    (hbJM : ∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (ιv n) (⨆ m, Sm n m) (Xm n)) (Xm n)
      (yv n ω) (bJM n ω))
    (hbMFE : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (bMFE n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bJM n ω - β)) atTop
        (fun z => Ring.inverse H z) (fun _ => P) (multivariateGaussian 0 Smat)
      ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bMFE n ω - β)) atTop
        (fun z => Ring.inverse H z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine clt_a hcard Sm Xm β fe hfe nu yv hmodel aa haa e sev C hregime hmeas hindep hmean
    hL2 hint4 hvar hmom Smat hSpd hSn hlin4
    (fun n => Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, Sm n m) (Xm n)))
    (Ring.inverse H) ?_ ?_ ιv hι hid bJM bMFE hbJMmeas hbMFEmeas hbJM hbMFE
  · filter_upwards [hid, eventually_ne_atTop 0] with n hidn hn0 a
    have hu : IsUnit ((n : ℝ)⁻¹ • gramCLM (⨆ m, Sm n m) (Xm n)) :=
      isUnit_smul (isUnit_gramCLM _ _ hidn) (inv_ne_zero (Nat.cast_ne_zero.2 hn0))
    have hmul := Ring.inverse_mul_cancel _ hu
    calc Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, Sm n m) (Xm n))
            ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a)
        = (Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, Sm n m) (Xm n)) *
            ((n : ℝ)⁻¹ • gramCLM (⨆ m, Sm n m) (Xm n))) a := rfl
      _ = a := by rw [hmul]; rfl
  · exact tendsto_inverse hHlim (isUnit_of_inner_pos hHpos)


/-! ### Consistency

`β̂ ⟶^p β` follows from the second moment of the score: the variance identity gives
`E‖X̃'ν‖² = ∑_k∑_o⟪x̃_o,e_k⟫²σ²_ε(o)`, whose `n^{-1}` multiple converges, and Chebyshev's
inequality concludes. -/

section Consistency

variable {O : Type*} [Fintype O] {Mfe : ℕ}

omit [IsProbabilityMeasure P] in
/-- `⟪x, e_k⟫ = x_k`. -/
lemma inner_single_eq (x : EuclideanSpace ℝ (Fin K)) (k : Fin K) :
    ⟪x, EuclideanSpace.single k (1:ℝ)⟫ = x k := by
  simp [PiLp.inner_apply, RCLike.inner_apply]

omit [IsProbabilityMeasure P] in
/-- `‖x‖² = ∑_k ⟪x,e_k⟫²`. -/
lemma norm_sq_eq_sum_inner (x : EuclideanSpace ℝ (Fin K)) :
    ‖x‖ ^ 2 = ∑ k, ⟪x, EuclideanSpace.single k (1:ℝ)⟫ ^ 2 := by
  simp only [inner_single_eq]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs]

omit [MeasurableSpace Ω] in
/-- Pathwise, `⟪X̃'ν, t⟫ = ∑_o⟪x̃_o,t⟫ε_o`. -/
lemma inner_score_eq_sum (Sm : Fin Mfe → Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (aa : Fin Mfe → Ω → EuclideanSpace ℝ O) (haa : ∀ m ω, aa m ω ∈ Sm m)
    (e : O → Ω → ℝ) (nu : Ω → EuclideanSpace ℝ O)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + (WithLp.toLp 2 fun o => e o ω))
    (t : EuclideanSpace ℝ (Fin K)) (ω : Ω) :
    ⟪score (⨆ m, Sm m) X (nu ω), t⟫
      = ∑ o, ⟪withinRow (⨆ m, Sm m) X o, t⟫ * e o ω := by
  rw [hregime ω, score_absorb (fun m => haa m ω)]
  have h : score (⨆ m, Sm m) X (WithLp.toLp 2 fun o => e o ω)
      = ∑ o, e o ω • withinRow (⨆ m, Sm m) X o := rfl
  rw [h, sum_inner]
  exact Finset.sum_congr rfl fun o _ => by rw [real_inner_smul_left]; ring

/-- The score has mean zero in every direction. -/
theorem integral_inner_score_eq_zero (Sm : Fin Mfe → Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (aa : Fin Mfe → Ω → EuclideanSpace ℝ O) (haa : ∀ m ω, aa m ω ∈ Sm m)
    (e : O → Ω → ℝ) (nu : Ω → EuclideanSpace ℝ O)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + (WithLp.toLp 2 fun o => e o ω))
    (hL2 : ∀ o, MemLp (e o) 2 P) (hmean : ∀ o, ∫ ω, e o ω ∂P = 0)
    (t : EuclideanSpace ℝ (Fin K)) :
    ∫ ω, ⟪score (⨆ m, Sm m) X (nu ω), t⟫ ∂P = 0 := by
  have hint : ∀ o : O, Integrable (fun ω => ⟪withinRow (⨆ m, Sm m) X o, t⟫ * e o ω) P :=
    fun o => ((hL2 o).integrable (by norm_num)).const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => inner_score_eq_sum Sm X aa haa e nu hregime t ω))]
  rw [integral_finsetSum _ (fun o _ => hint o)]
  refine Finset.sum_eq_zero fun o _ => ?_
  rw [integral_const_mul, hmean o, mul_zero]

/-- The directional second moment of the score equals its variance. -/
theorem integral_inner_score_sq (Sm : Fin Mfe → Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (aa : Fin Mfe → Ω → EuclideanSpace ℝ O) (haa : ∀ m ω, aa m ω ∈ Sm m)
    (e : O → Ω → ℝ) (sev : O → ℝ) (nu : Ω → EuclideanSpace ℝ O)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + (WithLp.toLp 2 fun o => e o ω))
    (hindep : iIndepFun e P) (hmeas : ∀ o, Measurable (e o))
    (hL2 : ∀ o, MemLp (e o) 2 P) (hmean : ∀ o, ∫ ω, e o ω ∂P = 0)
    (hvar : ∀ o, Var[e o; P] = sev o)
    (t : EuclideanSpace ℝ (Fin K)) :
    ∫ ω, ⟪score (⨆ m, Sm m) X (nu ω), t⟫ ^ 2 ∂P
      = ∑ o, ⟪withinRow (⨆ m, Sm m) X o, t⟫ ^ 2 * sev o := by
  have hmeasf : AEMeasurable (fun ω => ⟪score (⨆ m, Sm m) X (nu ω), t⟫) P := by
    refine AEMeasurable.congr ?_ (Filter.Eventually.of_forall
      (fun ω => (inner_score_eq_sum Sm X aa haa e nu hregime t ω).symm))
    exact (Finset.measurable_sum _ fun o _ => (hmeas o).const_mul _).aemeasurable
  rw [← variance_of_integral_eq_zero hmeasf
    (integral_inner_score_eq_zero Sm X aa haa e nu hregime hL2 hmean t)]
  exact variance_score_eq Sm X aa haa e sev nu hregime hindep hL2 hvar t

omit [IsProbabilityMeasure P] in
theorem integrable_norm_score_sq (Sm : Fin Mfe → Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (aa : Fin Mfe → Ω → EuclideanSpace ℝ O) (haa : ∀ m ω, aa m ω ∈ Sm m)
    (e : O → Ω → ℝ) (nu : Ω → EuclideanSpace ℝ O)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + (WithLp.toLp 2 fun o => e o ω))
    (hL2 : ∀ o, MemLp (e o) 2 P) :
    Integrable (fun ω => ‖score (⨆ m, Sm m) X (nu ω)‖ ^ 2) P := by
  have hint : ∀ k : Fin K,
      Integrable (fun ω => ⟪score (⨆ m, Sm m) X (nu ω),
        EuclideanSpace.single k (1:ℝ)⟫ ^ 2) P := by
    intro k
    have hmemLp : MemLp (fun ω => ⟪score (⨆ m, Sm m) X (nu ω),
        EuclideanSpace.single k (1:ℝ)⟫) 2 P := by
      refine MemLp.ae_eq (Filter.Eventually.of_forall
        (fun ω => (inner_score_eq_sum Sm X aa haa e nu hregime _ ω).symm)) ?_
      exact memLp_finsetSum _ (fun o _ => (hL2 o).const_mul _)
    exact hmemLp.integrable_sq
  refine Integrable.congr
    (integrable_finsetSum (Finset.univ : Finset (Fin K)) (fun k _ => hint k)) ?_
  exact Filter.Eventually.of_forall
    (fun ω => (norm_sq_eq_sum_inner (score (⨆ m, Sm m) X (nu ω))).symm)

/-- `E‖X̃'ν‖² = ∑_k∑_o⟪x̃_o,e_k⟫²σ²_ε(o)`. -/
theorem integral_norm_score_sq (Sm : Fin Mfe → Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (aa : Fin Mfe → Ω → EuclideanSpace ℝ O) (haa : ∀ m ω, aa m ω ∈ Sm m)
    (e : O → Ω → ℝ) (sev : O → ℝ) (nu : Ω → EuclideanSpace ℝ O)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + (WithLp.toLp 2 fun o => e o ω))
    (hindep : iIndepFun e P) (hmeas : ∀ o, Measurable (e o))
    (hL2 : ∀ o, MemLp (e o) 2 P) (hmean : ∀ o, ∫ ω, e o ω ∂P = 0)
    (hvar : ∀ o, Var[e o; P] = sev o) :
    ∫ ω, ‖score (⨆ m, Sm m) X (nu ω)‖ ^ 2 ∂P
      = ∑ k : Fin K, ∑ o, ⟪withinRow (⨆ m, Sm m) X o,
          EuclideanSpace.single k (1:ℝ)⟫ ^ 2 * sev o := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => norm_sq_eq_sum_inner (score (⨆ m, Sm m) X (nu ω))))]
  rw [integral_finsetSum _ (fun k _ => by
    refine MemLp.integrable_sq ?_
    refine MemLp.ae_eq (Filter.Eventually.of_forall
      (fun ω => (inner_score_eq_sum Sm X aa haa e nu hregime _ ω).symm)) ?_
    exact memLp_finsetSum _ (fun o _ => (hL2 o).const_mul _))]
  exact Finset.sum_congr rfl fun k _ =>
    integral_inner_score_sq Sm X aa haa e sev nu hregime hindep hmeas hL2 hmean hvar _

end Consistency

set_option linter.unusedSectionVars false in
/-- Consistency of the slope from the normalized second moment of the score,
`n^{-1}E‖X̃'ν‖² → Q < ∞`, in any regime. -/
theorem tendstoInMeasure_slope_of_score_L2
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (hQint : ∀ n : ℕ, Integrable (fun ω => ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2) P)
    {Q : ℝ}
    (hQlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) atTop (𝓝 Q))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (b : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (hbmeas : ∀ n, AEMeasurable (b n) P)
    (hb : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (b n ω)) :
    TendstoInMeasure P b atTop (fun _ => β) := by
  classical
  have hsol : ∀ᶠ n : ℕ in atTop, ∀ ω, b n ω - β
      = (n : ℝ)⁻¹ • A n (score (⨆ m, Sm n m) (Xm n) (nu n ω)) := by
    filter_upwards [hAsolve, hb] with n hAn hbn ω
    have hs : (∑ m, fe n m) ∈ (⨆ m, Sm n m) :=
      Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m (hfe n m)
    have h1 := gram_sub_eq_score (hmodel n ω) hs (hbn ω)
    have h2 := hAn (b n ω - β)
    rw [h1] at h2
    rw [← h2, map_smul]
  have hptwise : ∀ᶠ n : ℕ in atTop, ∀ ω, ‖b n ω - β‖ ^ 2
      ≤ ((n : ℝ)⁻¹ * ‖A n‖) ^ 2 * ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 := by
    filter_upwards [hsol] with n hsn ω
    have h1 : ‖(n : ℝ)⁻¹ • A n (score (⨆ m, Sm n m) (Xm n) (nu n ω))‖
        ≤ ((n : ℝ)⁻¹ * ‖A n‖) * ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by positivity)
    calc ‖b n ω - β‖ ^ 2
        = ‖(n : ℝ)⁻¹ • A n (score (⨆ m, Sm n m) (Xm n) (nu n ω))‖ ^ 2 := by rw [hsn ω]
      _ ≤ (((n : ℝ)⁻¹ * ‖A n‖) * ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ((n : ℝ)⁻¹ * ‖A n‖) ^ 2 * ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 := by ring
  have hclim : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ * ‖A n‖) ^ 2 *
      ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) atTop (𝓝 0) := by
    have hfun : ∀ n : ℕ, ((n : ℝ)⁻¹ * ‖A n‖) ^ 2 *
        (∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P)
        = ((n : ℝ)⁻¹ * ‖A n‖ ^ 2) *
          ((n : ℝ)⁻¹ * ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) := by
      intro n; ring
    refine Tendsto.congr (fun n => (hfun n).symm) ?_
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ‖A n‖ ^ 2) atTop (𝓝 (0 * ‖Hinv‖ ^ 2)) :=
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul (hAlim.norm.pow 2)
    rw [zero_mul] at h1
    simpa using h1.mul hQlim
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hε2 : (0:ℝ) < ε ^ 2 := by positivity
  have hofne : ENNReal.ofReal (ε ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hε2).ne'
  have hkey : ∀ᶠ n : ℕ in atTop, P {ω | ε ≤ ‖b n ω - β‖}
      ≤ ENNReal.ofReal (((n : ℝ)⁻¹ * ‖A n‖) ^ 2 *
          ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) *
        (ENNReal.ofReal (ε ^ 2))⁻¹ := by
    filter_upwards [hptwise] with n hpn
    have hmeasg : AEMeasurable (fun ω => ENNReal.ofReal (‖b n ω - β‖ ^ 2)) P :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((((hbmeas n).sub_const β).norm).pow_const 2)
    have hsub : {ω | ε ≤ ‖b n ω - β‖}
        ⊆ {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal (‖b n ω - β‖ ^ 2)} := by
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hω 2)
    have hmk := mul_meas_ge_le_lintegral₀ hmeasg (ENNReal.ofReal (ε ^ 2))
    have hbound : ∫⁻ ω, ENNReal.ofReal (‖b n ω - β‖ ^ 2) ∂P
        ≤ ENNReal.ofReal (((n : ℝ)⁻¹ * ‖A n‖) ^ 2 *
            ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) := by
      calc ∫⁻ ω, ENNReal.ofReal (‖b n ω - β‖ ^ 2) ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (((n : ℝ)⁻¹ * ‖A n‖) ^ 2 *
              ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2) ∂P :=
            lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpn ω)
        _ = ENNReal.ofReal (((n : ℝ)⁻¹ * ‖A n‖) ^ 2) *
              ∫⁻ ω, ENNReal.ofReal (‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2) ∂P := by
            simp_rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((n : ℝ)⁻¹ * ‖A n‖) ^ 2)]
            exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (((n : ℝ)⁻¹ * ‖A n‖) ^ 2) *
              ENNReal.ofReal (∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) := by
            rw [← ofReal_integral_eq_lintegral_ofReal (hQint n)
              (Filter.Eventually.of_forall fun ω => by positivity)]
        _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
    have hchain : ENNReal.ofReal (ε ^ 2) * P {ω | ε ≤ ‖b n ω - β‖}
        ≤ ENNReal.ofReal (((n : ℝ)⁻¹ * ‖A n‖) ^ 2 *
            ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) :=
      le_trans (le_trans (by gcongr) hmk) hbound
    rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hofne)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hchain
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Filter.Eventually.of_forall fun _ => zero_le) hkey
  have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (((n : ℝ)⁻¹ * ‖A n‖) ^ 2 *
      ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hclim
  have hfin : (ENNReal.ofReal (ε ^ 2))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hofne
  simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hfin)

/-- Consistency of `β̂_MFE` under Regime 1, from
`E‖β̂_n - β‖² ≤ n^{-1}‖A_n‖²·(n^{-1}E‖X̃'ν‖²)` and Chebyshev's inequality. -/
theorem tendstoInMeasure_slope
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (aa : ∀ n, Fin M → Ω → EuclideanSpace ℝ (O n)) (haa : ∀ n m ω, aa n m ω ∈ Sm n m)
    (e : ∀ n, O n → Ω → ℝ) (sev : ∀ n, O n → ℝ)
    (hregime : ∀ n ω, nu n ω = (∑ m, aa n m ω) + (WithLp.toLp 2 fun o => e n o ω))
    (hmeas : ∀ n o, Measurable (e n o)) (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n o, ∫ ω, e n o ω ∂P = 0) (hL2 : ∀ n o, MemLp (e n o) 2 P)
    (hvar : ∀ n o, Var[e n o; P] = sev n o)
    (Smat : Matrix (Fin K) (Fin K) ℝ)
    (hSn : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 2 * sev n o) atTop (𝓝 (t ⬝ᵥ (Smat *ᵥ t))))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (b : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (hbmeas : ∀ n, AEMeasurable (b n) P)
    (hb : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (b n ω)) :
    TendstoInMeasure P b atTop (fun _ => β) := by
  classical
  have hQint : ∀ n : ℕ, Integrable
      (fun ω => ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2) P := fun n =>
    integrable_norm_score_sq (Sm n) (Xm n) (aa n) (haa n) (e n) (nu n) (hregime n) (hL2 n)
  have hQlim : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) atTop
      (𝓝 (∑ k : Fin K, (EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin K)) ⬝ᵥ
        (Smat *ᵥ (EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin K))))) := by
    have hval : ∀ n : ℕ,
        (n : ℝ)⁻¹ * ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P
          = ∑ k : Fin K, ((n : ℝ)⁻¹ * ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o,
              (EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin K))⟫ ^ 2 * sev n o) := by
      intro n
      rw [integral_norm_score_sq (Sm n) (Xm n) (aa n) (haa n) (e n) (sev n) (nu n)
        (hregime n) (hindep n) (hmeas n) (hL2 n) (hmean n) (hvar n), Finset.mul_sum]
    refine Tendsto.congr (fun n => (hval n).symm) ?_
    exact tendsto_finsetSum _ (fun k _ => hSn _)
  exact tendstoInMeasure_slope_of_score_L2 Sm Xm β fe hfe nu yv hmodel hQint hQlim
    A Hinv hAsolve hAlim b hbmeas hb


/-- **Theorem 4(a)**, consistency: `β̂_JM ⟶^p β` and `β̂_MFE ⟶^p β`. -/
theorem clt_a_consistency
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (aa : ∀ n, Fin M → Ω → EuclideanSpace ℝ (O n)) (haa : ∀ n m ω, aa n m ω ∈ Sm n m)
    (e : ∀ n, O n → Ω → ℝ) (sev : ∀ n, O n → ℝ)
    (hregime : ∀ n ω, nu n ω = (∑ m, aa n m ω) + (WithLp.toLp 2 fun o => e n o ω))
    (hmeas : ∀ n o, Measurable (e n o)) (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n o, ∫ ω, e n o ω ∂P = 0) (hL2 : ∀ n o, MemLp (e n o) 2 P)
    (hvar : ∀ n o, Var[e n o; P] = sev n o)
    (Smat : Matrix (Fin K) (Fin K) ℝ)
    (hSn : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 2 * sev n o) atTop (𝓝 (t ⬝ᵥ (Smat *ᵥ t))))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (ιv : ∀ n, EuclideanSpace ℝ (O n)) (hι : ∀ n, ιv n ∈ ⨆ m, Sm n m)
    (hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, Sm n m) (Xm n))
    (bJM bMFE : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbJMmeas : ∀ n, AEMeasurable (bJM n) P) (hbMFEmeas : ∀ n, AEMeasurable (bMFE n) P)
    (hbJM : ∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (ιv n) (⨆ m, Sm n m) (Xm n)) (Xm n)
      (yv n ω) (bJM n ω))
    (hbMFE : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (bMFE n ω)) :
    TendstoInMeasure P bJM atTop (fun _ => β) ∧ TendstoInMeasure P bMFE atTop (fun _ => β) := by
  refine ⟨?_, ?_⟩
  · refine tendstoInMeasure_slope Sm Xm β fe hfe nu yv hmodel aa haa e sev hregime hmeas
      hindep hmean hL2 hvar Smat hSn A Hinv hAsolve hAlim bJM hbJMmeas ?_
    filter_upwards [hid, hbJM] with n hidn hbn ω
    exact isMFESlope_of_isAugSlope_jm hidn (hι n) _ _ (hbn ω)
  · exact tendstoInMeasure_slope Sm Xm β fe hfe nu yv hmodel aa haa e sev hregime hmeas
      hindep hmean hL2 hvar Smat hSn A Hinv hAsolve hAlim bMFE hbMFEmeas hbMFE


/-! ### The Lindeberg input from the design conditions -/

/-- The Lindeberg input `n^{-2}∑_o⟪x̃_o,t⟫^4 → 0` follows from
`max_o‖x̃_o‖²/∑_o‖x̃_o‖² → 0` and `n^{-1}∑_o‖x̃_o‖² → tr(H) < ∞`, via
`⟪x̃_o,t⟫² ≤ ‖t‖²‖x̃_o‖²` and `∑_o‖x̃_o‖⁴ ≤ (max_o‖x̃_o‖²)∑_o‖x̃_o‖²`. -/
theorem lin4_of_design {O : ℕ → Type} [∀ n, Fintype (O n)]
    (xt : ∀ n, O n → EuclideanSpace ℝ (Fin K)) (τ : ℝ)
    (hIV : Tendsto (fun n : ℕ => (⨆ o, ‖xt n o‖ ^ 2) / (∑ o, ‖xt n o‖ ^ 2)) atTop (𝓝 0))
    (hII : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ o, ‖xt n o‖ ^ 2) atTop (𝓝 τ))
    (t : EuclideanSpace ℝ (Fin K)) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ * ∑ o, ⟪xt n o, t⟫ ^ 4) atTop (𝓝 0) := by
  classical
  refine squeeze_zero (fun n => ?_) (fun n => ?_)
    (?_ : Tendsto (fun n : ℕ => ‖t‖ ^ 4 * ((⨆ o, ‖xt n o‖ ^ 2) / (∑ o, ‖xt n o‖ ^ 2))
      * ((n : ℝ)⁻¹ * ∑ o, ‖xt n o‖ ^ 2) ^ 2) atTop (𝓝 0))
  · have h : (0 : ℝ) ≤ ∑ o, ⟪xt n o, t⟫ ^ 4 :=
      Finset.sum_nonneg fun o _ => by positivity
    positivity
  · -- Cauchy–Schwarz and the max bound
    set sumsq : ℝ := ∑ o, ‖xt n o‖ ^ 2 with hsumsq
    set mx : ℝ := ⨆ o, ‖xt n o‖ ^ 2 with hmx
    have hcs : ∀ o : O n, ⟪xt n o, t⟫ ^ 4 ≤ ‖t‖ ^ 4 * ‖xt n o‖ ^ 4 := by
      intro o
      have h1 : |⟪xt n o, t⟫| ≤ ‖xt n o‖ * ‖t‖ := abs_real_inner_le_norm _ _
      have h2 : ⟪xt n o, t⟫ ^ 4 = (|⟪xt n o, t⟫|) ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity)]
      rw [h2]
      calc (|⟪xt n o, t⟫|) ^ 4 ≤ (‖xt n o‖ * ‖t‖) ^ 4 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 4
        _ = ‖t‖ ^ 4 * ‖xt n o‖ ^ 4 := by ring
    have hnn : ∀ o : O n, ‖xt n o‖ ^ 2 ≤ sumsq := by
      intro o
      rw [hsumsq]
      exact Finset.single_le_sum (f := fun o => ‖xt n o‖ ^ 2)
        (fun o _ => by positivity) (Finset.mem_univ o)
    rcases eq_or_ne sumsq 0 with hz | hz
    · have hall : ∀ o : O n, xt n o = 0 := by
        intro o
        have h1 := hnn o
        rw [hz] at h1
        have h2 : ‖xt n o‖ = 0 := by nlinarith [norm_nonneg (xt n o)]
        simpa using h2
      have hzero : ∑ o, ⟪xt n o, t⟫ ^ 4 = 0 :=
        Finset.sum_eq_zero fun o _ => by rw [hall o]; simp
      rw [hzero, mul_zero, hz]
      simp
    · have hsumpos : 0 < sumsq := lt_of_le_of_ne
        (by rw [hsumsq]; exact Finset.sum_nonneg fun o _ => by positivity) (Ne.symm hz)
      have hle : ∀ o : O n, ‖xt n o‖ ^ 2 ≤ mx := fun o =>
        le_ciSup (Finite.bddAbove_range (fun o => ‖xt n o‖ ^ 2)) o
      have h4 : ∑ o, ‖xt n o‖ ^ 4 ≤ mx * sumsq := by
        rw [hsumsq, Finset.mul_sum]
        refine Finset.sum_le_sum fun o _ => ?_
        have hsq : ‖xt n o‖ ^ 4 = ‖xt n o‖ ^ 2 * ‖xt n o‖ ^ 2 := by ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_right (hle o) (by positivity)
      have hsum : ∑ o, ⟪xt n o, t⟫ ^ 4 ≤ ‖t‖ ^ 4 * (mx * sumsq) := by
        refine (Finset.sum_le_sum fun o _ => hcs o).trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
      have hfin : ((n : ℝ) ^ 2)⁻¹ * (‖t‖ ^ 4 * (mx * sumsq))
          = ‖t‖ ^ 4 * (mx / sumsq) * ((n : ℝ)⁻¹ * sumsq) ^ 2 := by
        field_simp
      calc ((n : ℝ) ^ 2)⁻¹ * ∑ o, ⟪xt n o, t⟫ ^ 4
          ≤ ((n : ℝ) ^ 2)⁻¹ * (‖t‖ ^ 4 * (mx * sumsq)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = ‖t‖ ^ 4 * (mx / sumsq) * ((n : ℝ)⁻¹ * sumsq) ^ 2 := hfin
  · have h1 : Tendsto (fun n : ℕ => ‖t‖ ^ 4 * ((⨆ o, ‖xt n o‖ ^ 2) / (∑ o, ‖xt n o‖ ^ 2))
        * ((n : ℝ)⁻¹ * ∑ o, ‖xt n o‖ ^ 2) ^ 2) atTop (𝓝 (‖t‖ ^ 4 * 0 * τ ^ 2)) :=
      (tendsto_const_nhds.mul hIV).mul (hII.pow 2)
    simpa using h1

end Main

/-! ### A model for `clt_a`

A sequence of designs on which every hypothesis of `clt_a` holds: `𝒪_n = Fin n`, `K = M = 1`,
`𝒮_n = ℝ∙d_n` with `d_n` the indicator of the first observation, and the regressor `a ↦ a_0v_n`
with `v_n` the indicator of the remaining observations. The fixed effect and the Regime-1
component are nonzero elements of `𝒮_n`, and the errors are an i.i.d. Rademacher array. For
`n ≥ 2`, `Var(⟪√n(β̂_n - β), t⟫) = (t_0)²·n/(n-1)`, so the limit is non-degenerate. -/

namespace Witness

open scoped ENNReal

/-! ### The Rademacher law

Since `ε² = ε⁴ = 1` pointwise, all moment conditions hold trivially. -/

/-- The law `(δ₁ + δ₋₁)/2`. -/
noncomputable def rade : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (1 : ℝ) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (-1 : ℝ)

instance : IsProbabilityMeasure rade := by
  constructor
  show (2⁻¹ : ℝ≥0∞) * _ + (2⁻¹ : ℝ≥0∞) * _ = 1
  simp
  rw [ENNReal.inv_two_add_inv_two]

theorem integrable_rade {f : ℝ → ℝ} (hf : Measurable f) : Integrable f rade := by
  unfold rade
  refine Integrable.add_measure ?_ ?_ <;>
    exact (integrable_smul_measure (by norm_num) (by norm_num)).2
      (integrable_dirac' hf.stronglyMeasurable (by finiteness))

theorem integral_rade {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂rade = (f 1 + f (-1)) / 2 := by
  have h1 : Integrable f ((2⁻¹ : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
    (integrable_smul_measure (by norm_num) (by norm_num)).2 (integrable_dirac (by finiteness))
  have h2 : Integrable f ((2⁻¹ : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) :=
    (integrable_smul_measure (by norm_num) (by norm_num)).2 (integrable_dirac (by finiteness))
  unfold rade
  rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac' _ _ hf.stronglyMeasurable, integral_dirac' _ _ hf.stronglyMeasurable]
  norm_num
  ring

theorem integral_id_rade : ∫ x, x ∂rade = 0 := by
  simpa using integral_rade (f := fun x : ℝ => x) measurable_id

theorem integral_pow4_rade : ∫ x, x ^ 4 ∂rade = 1 := by
  rw [integral_rade (f := fun x : ℝ => x ^ 4) (by fun_prop)]; norm_num

theorem memLp_id_rade : MemLp (id : ℝ → ℝ) 2 rade :=
  (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
    (by simpa using integrable_rade (f := fun x : ℝ => x ^ 2) (by fun_prop))

theorem integrable_pow4_rade : Integrable (fun x : ℝ => x ^ 4) rade :=
  integrable_rade (by fun_prop)

theorem variance_id_rade : Var[(id : ℝ → ℝ); rade] = 1 := by
  rw [variance_of_integral_eq_zero aemeasurable_id (by simpa using integral_id_rade)]
  have h := integral_rade (f := fun x : ℝ => x ^ 2) (by fun_prop)
  norm_num at h
  simpa using h

/-! ### The sequence of designs -/

/-- `Δ_1`'s single column: the indicator of the first observation. -/
noncomputable def dvec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun o => if o.val = 0 then 1 else 0

/-- The single regressor column: the indicator of every observation but the first,
orthogonal to `dvec n`. -/
noncomputable def xvec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun o => if o.val = 0 then 0 else 1

/-- `𝒮_n = ℝ∙d_n`, at `M = 1`. -/
noncomputable def feSpace (n : ℕ) : Fin 1 → Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  fun _ => ℝ ∙ dvec n

/-- `X_n : ℝ¹ → ℝ^n`, `a ↦ a_0v_n`. -/
noncomputable def Xmap (n : ℕ) : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun a := a 0 • xvec n
  map_add' a b := by simp [add_smul]
  map_smul' r a := by simp [mul_smul]

theorem iSup_feSpace (n : ℕ) : (⨆ m, feSpace n m) = ℝ ∙ dvec n := by
  simp [feSpace]

theorem xvec_mem_orth (n : ℕ) : xvec n ∈ (ℝ ∙ dvec n)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp only [dvec, xvec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_eq_zero fun x _ => by split <;> simp

/-- `Q_[Δ]X = X` on this design: the regressor is already within-transformed. -/
theorem jointWithin_Xmap (n : ℕ) (a : EuclideanSpace ℝ (Fin 1)) :
    jointWithin (⨆ m, feSpace n m) (Xmap n a) = Xmap n a := by
  rw [iSup_feSpace, jointWithin_apply, (Submodule.starProjection_apply_eq_zero_iff _).2, sub_zero]
  exact Submodule.smul_mem _ _ (xvec_mem_orth n)

theorem sum_ite_fin (n : ℕ) (c : ℝ) :
    ∑ o : Fin n, (if o.val = 0 then (0:ℝ) else c) = ((n - 1 : ℕ) : ℝ) * c := by
  rcases n with _ | m
  · simp
  · rw [Fin.sum_univ_succ]; simp

theorem inner_xvec_self (n : ℕ) : ⟪xvec n, xvec n⟫ = ((n - 1 : ℕ) : ℝ) := by
  simp only [xvec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h : ∀ o : Fin n, (if o.val = 0 then (0:ℝ) else 1) * (if o.val = 0 then (0:ℝ) else 1)
      = (if o.val = 0 then (0:ℝ) else 1) := by intro o; split <;> simp
  rw [Finset.sum_congr rfl fun o _ => h o, sum_ite_fin n 1]
  ring

theorem inner_fin_one (b a : EuclideanSpace ℝ (Fin 1)) : ⟪b, a⟫ = b 0 * a 0 := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem eq_zero_of_apply_zero {a : EuclideanSpace ℝ (Fin 1)} (h : a 0 = 0) : a = 0 := by
  ext j
  fin_cases j
  simpa using h

theorem xvec_apply (n : ℕ) (o : Fin n) : xvec n o = if o.val = 0 then 0 else 1 := rfl

/-- The within rows of the witness design, read through `⟪·,t⟫`: `x̃_o = 0` at the first
observation and `x̃_o = 1` at every other. -/
theorem inner_withinRow_witness (n : ℕ) (o : Fin n) (t : EuclideanSpace ℝ (Fin 1)) :
    ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ = t 0 * (if o.val = 0 then (0:ℝ) else 1) := by
  rw [real_inner_comm, inner_withinRow, jointWithin_Xmap]
  show (t 0 • xvec n) o = _
  rw [PiLp.smul_apply, xvec_apply]
  simp

/-- `X̃'X̃ = (n-1)I₁` on the witness design. -/
theorem gram_witness (n : ℕ) (a : EuclideanSpace ℝ (Fin 1)) :
    gram (⨆ m, feSpace n m) (Xmap n) a = ((n - 1 : ℕ) : ℝ) • a := by
  refine ext_inner_left ℝ fun b => ?_
  rw [gram, inner_score, jointWithin_Xmap]
  show ⟪b 0 • xvec n, a 0 • xvec n⟫ = _
  rw [real_inner_smul_left, real_inner_smul_right, inner_xvec_self, real_inner_smul_right,
    inner_fin_one]
  ring

/-- The witness design is identified for `n ≥ 2`. -/
theorem identified_witness {n : ℕ} (hn : 2 ≤ n) : Identified (⨆ m, feSpace n m) (Xmap n) := by
  intro a ha
  rw [iSup_feSpace, Submodule.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ := ha
  have hXa : (Xmap n) a = a 0 • xvec n := rfl
  rw [hXa] at hc
  have h := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z ⟨1, by omega⟩) hc
  simp only [PiLp.smul_apply, smul_eq_mul] at h
  refine eq_zero_of_apply_zero ?_
  show a 0 = 0
  have hd : dvec n ⟨1, by omega⟩ = 0 := by simp [dvec]
  have hx : xvec n ⟨1, by omega⟩ = 1 := by simp [xvec]
  rw [hd, hx] at h
  simpa using h.symm

/-! ### Design limits -/

theorem tendsto_pred_div : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have h : (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ)) =ᶠ[atTop] (fun n : ℕ => 1 - (n : ℝ)⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h1 : (1:ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h1]
      ring
    rw [hc]
    field_simp
  refine Tendsto.congr' h.symm ?_
  simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem tendsto_div_pred : Tendsto (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h := tendsto_pred_div.inv₀ one_ne_zero
  simpa [inv_div] using h

theorem dotProduct_one_fin_one (t : EuclideanSpace ℝ (Fin 1)) :
    t ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ t) = (t 0) ^ 2 := by
  rw [Matrix.one_mulVec]
  simp [dotProduct, sq]

theorem sum_inner_sq (n : ℕ) (t : EuclideanSpace ℝ (Fin 1)) {p : ℕ} (hp : p ≠ 0) :
    ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ p * (1:ℝ)
      = ((n - 1 : ℕ) : ℝ) * (t 0) ^ p := by
  have hterm : ∀ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ p * (1:ℝ)
      = if o.val = 0 then (0:ℝ) else (t 0) ^ p := by
    intro o
    rw [inner_withinRow_witness]
    split <;> simp [hp]
  rw [Finset.sum_congr rfl fun o _ => hterm o, sum_ite_fin]

/-- On the witness design `S_n = (n-1)/n → 1 = S`. -/
theorem hSn_witness (t : EuclideanSpace ℝ (Fin 1)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ 2 * (1:ℝ)) atTop
      (𝓝 (t ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ t))) := by
  rw [dotProduct_one_fin_one]
  have hfun : ∀ n : ℕ, (n : ℝ)⁻¹ *
      ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ 2 * (1:ℝ)
      = (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * (t 0) ^ 2 := by
    intro n
    rw [sum_inner_sq n t (by norm_num), div_eq_mul_inv]
    ring
  refine Tendsto.congr (fun n => (hfun n).symm) ?_
  simpa using tendsto_pred_div.mul_const ((t 0) ^ 2)

/-- The fourth-power Lindeberg input on the witness design. -/
theorem hlin4_witness (t : EuclideanSpace ℝ (Fin 1)) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ *
        ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ 4) atTop (𝓝 0) := by
  have hfun : ∀ n : ℕ, ((n : ℝ) ^ 2)⁻¹ *
      ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ 4
      = (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * ((n : ℝ)⁻¹ * (t 0) ^ 4) := by
    intro n
    have h := sum_inner_sq n t (p := 4) (by norm_num)
    simp only [mul_one] at h
    rw [h, div_eq_mul_inv, ← inv_pow]
    ring
  refine Tendsto.congr (fun n => (hfun n).symm) ?_
  have h2 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (t 0) ^ 4) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ((t 0) ^ 4)
  simpa using tendsto_pred_div.mul h2

/-- `(n^{-1}X̃'X̃)^{-1} = n/(n-1)` on the witness design. -/
noncomputable def Aop (n : ℕ) :
    EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

theorem hAlim_witness :
    Tendsto Aop atTop (𝓝 (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))) := by
  have h := tendsto_div_pred.smul_const (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))
  rw [one_smul] at h
  exact h

/-- `X̃'X̃ = (n-1)I₁` again, now in the normed ring `ℝ¹ →L[ℝ] ℝ¹`. -/
theorem gramCLM_witness (n : ℕ) :
    gramCLM (⨆ m, feSpace n m) (Xmap n)
      = ((n - 1 : ℕ) : ℝ) • (1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [gramCLM_apply, gram_witness]
  rfl

/-- `H = I₁` is positive definite on the witness design. -/
theorem hHpos_witness (a : EuclideanSpace ℝ (Fin 1)) (ha : a ≠ 0) :
    0 < ⟪a, (1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) a⟫ :=
  real_inner_self_pos.2 ha

/-- On the witness design `n^{-1}X̃'X̃ = (n-1)/n → I₁`. -/
theorem hHlim_witness :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (Xmap n)) atTop
      (𝓝 (1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))) := by
  have hfun : ∀ n : ℕ, (n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (Xmap n)
      = (((n - 1 : ℕ) : ℝ) / (n : ℝ)) •
        (1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
    intro n
    rw [gramCLM_witness, smul_smul, div_eq_mul_inv, mul_comm]
  refine Tendsto.congr (fun n => (hfun n).symm) ?_
  have h := tendsto_pred_div.smul_const
    (1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
  rw [one_smul] at h
  exact h

theorem hAsolve_witness :
    ∀ᶠ n : ℕ in atTop, ∀ a : EuclideanSpace ℝ (Fin 1),
      Aop n ((n : ℝ)⁻¹ • gram (⨆ m, feSpace n m) (Xmap n) a) = a := by
  filter_upwards [eventually_ge_atTop 2] with n hn a
  have hn0 : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [gram_witness, smul_smul, Aop]
  show ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) • (((n : ℝ)⁻¹ * ((n - 1 : ℕ) : ℝ)) • a) = a
  rw [smul_smul]
  have h : ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) * ((n : ℝ)⁻¹ * ((n - 1 : ℕ) : ℝ)) = 1 := by
    field_simp
  rw [h, one_smul]

/-! ### The model and Regime-1 disturbance -/

/-- The error array, `ε_{n,o} = ξ_{(n,o)}`. -/
noncomputable def errW (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (o : Fin n) : Ω → ℝ := fun ω => ξ (n, o.val) ω

/-- The Regime-1 random component `a^{(1)}`, a nonzero random element of `𝒮_n`, driven by
`ξ_{(0,0)}`. -/
noncomputable def aaW (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (_ : Fin 1) (ω : Ω) :
    EuclideanSpace ℝ (Fin n) := ξ (0, 0) ω • dvec n

/-- The deterministic fixed effect, nonzero for `n ≥ 1`. -/
noncomputable def feW (n : ℕ) (_ : Fin 1) : EuclideanSpace ℝ (Fin n) := (3 : ℝ) • dvec n

noncomputable def nuW (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  (∑ m, aaW ξ n m ω) + (WithLp.toLp 2 fun o => errW ξ n o ω)

noncomputable def yW (ξ : ℕ × ℕ → Ω → ℝ) (β : EuclideanSpace ℝ (Fin 1)) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin n) := Xmap n β + (∑ m, feW n m) + nuW ξ n ω

/-- The estimator `β̂_n = β + (n-1)^{-1}X̃'ν`, constructed from the score. -/
noncomputable def bW (ξ : ℕ × ℕ → Ω → ℝ) (β : EuclideanSpace ℝ (Fin 1)) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin 1) :=
  β + (((n - 1 : ℕ) : ℝ))⁻¹ • score (⨆ m, feSpace n m) (Xmap n) (nuW ξ n ω)

theorem feW_mem (n : ℕ) (m : Fin 1) : feW n m ∈ feSpace n m :=
  Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

omit [MeasurableSpace Ω] in
theorem aaW_mem (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (m : Fin 1) (ω : Ω) : aaW ξ n m ω ∈ feSpace n m :=
  Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem dvec_mem (n : ℕ) : dvec n ∈ ⨆ m, feSpace n m := by
  rw [iSup_feSpace]; exact Submodule.mem_span_singleton_self _

omit [MeasurableSpace Ω] in
theorem nuW_apply (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (o : Fin n) :
    nuW ξ n ω o = ξ (0, 0) ω * dvec n o + ξ (n, o.val) ω := by
  simp [nuW, aaW, errW]

theorem measurable_bW {ξ : ℕ × ℕ → Ω → ℝ} (hξ : ∀ i, Measurable (ξ i))
    (β : EuclideanSpace ℝ (Fin 1)) (n : ℕ) : Measurable (bW ξ β n) := by
  have h : Measurable fun ω => score (⨆ m, feSpace n m) (Xmap n) (nuW ξ n ω) := by
    refine measurable_score _ _ fun o => ?_
    simp only [nuW_apply]
    exact ((hξ (0, 0)).mul_const _).add (hξ (n, o.val))
  exact (h.const_smul (((n - 1 : ℕ) : ℝ))⁻¹).const_add β

omit [MeasurableSpace Ω] in
/-- `β̂_n` solves the multiway fixed-effects normal equations for `n ≥ 2`. -/
theorem isMFESlope_bW (ξ : ℕ × ℕ → Ω → ℝ) (β : EuclideanSpace ℝ (Fin 1)) {n : ℕ} (hn : 2 ≤ n)
    (ω : Ω) : IsMFESlope (⨆ m, feSpace n m) (Xmap n) (yW ξ β n ω) (bW ξ β n ω) := by
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine isMFESlope_of_gram_sub_eq_score (s := ∑ m, feW n m) (v := nuW ξ n ω) rfl
    (Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m (feW_mem n m)) ?_
  have hsub : bW ξ β n ω - β
      = (((n - 1 : ℕ) : ℝ))⁻¹ • score (⨆ m, feSpace n m) (Xmap n) (nuW ξ n ω) := by
    simp [bW]
  rw [hsub, gram_witness, smul_smul, mul_inv_cancel₀ hn1, one_smul]

/-- The variance of the standardized estimator in direction `t` is `(t_0)²n/(n-1)`, computed
through `variance_score_eq`. -/
theorem variance_bW (ξ : ℕ × ℕ → Ω → ℝ)
    (β : EuclideanSpace ℝ (Fin 1)) {n : ℕ} (hn : 2 ≤ n)
    (hindep : iIndepFun (errW ξ n) P) (hL2 : ∀ o, MemLp (errW ξ n o) 2 P)
    (hvar : ∀ o, Var[errW ξ n o; P] = 1) (t : EuclideanSpace ℝ (Fin 1)) :
    Var[fun ω => ⟪Real.sqrt n • (bW ξ β n ω - β), t⟫; P]
      = (t 0) ^ 2 * ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hrw : (fun ω => ⟪Real.sqrt n • (bW ξ β n ω - β), t⟫)
      = fun ω => (Real.sqrt n * (((n - 1 : ℕ) : ℝ))⁻¹) *
          ⟪score (⨆ m, feSpace n m) (Xmap n) (nuW ξ n ω), t⟫ := by
    funext ω
    have hsub : bW ξ β n ω - β
        = (((n - 1 : ℕ) : ℝ))⁻¹ • score (⨆ m, feSpace n m) (Xmap n) (nuW ξ n ω) := by
      simp [bW]
    rw [hsub, smul_smul, real_inner_smul_left]
  rw [hrw, variance_const_mul,
    variance_score_eq (feSpace n) (Xmap n) (aaW ξ n) (aaW_mem ξ n) (errW ξ n) (fun _ => 1)
      (nuW ξ n) (fun ω => rfl) hindep hL2 hvar t,
    sum_inner_sq n t (p := 2) (by norm_num)]
  have hsq : (Real.sqrt n * (((n - 1 : ℕ) : ℝ))⁻¹) ^ 2
      = (n : ℝ) * ((((n - 1 : ℕ) : ℝ))⁻¹) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hsq]
  field_simp

/-- Every hypothesis of `clt_a` holds on the witness model, and its conclusion follows. The
first two conjuncts say `β̂_n` is both a joint-projection Mundlak slope and a multiway
fixed-effects slope; the last is the variance formula of `variance_bW`. -/
theorem clt_a_witness (β : EuclideanSpace ℝ (Fin 1)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (Xmap n))
          (Xmap n) (yW ξ β n ω) (bW ξ β n ω))
    ∧ (∀ᶠ n : ℕ in atTop, ∀ ω,
        IsMFESlope (⨆ m, feSpace n m) (Xmap n) (yW ξ β n ω) (bW ξ β n ω))
    ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bW ξ β n ω - β)) atTop
        (fun z => (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) z) (fun _ => P)
        (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
    ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bW ξ β n ω - β)) atTop
        (fun z => Ring.inverse
          (1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) z) (fun _ => P)
        (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
    ∧ TendstoInMeasure P (bW ξ β) atTop (fun _ => β)
    ∧ (∀ᶠ n : ℕ in atTop, ∀ t : EuclideanSpace ℝ (Fin 1),
        Var[fun ω => ⟪Real.sqrt n • (bW ξ β n ω - β), t⟫; P]
          = (t 0) ^ 2 * ((n : ℝ) / ((n - 1 : ℕ) : ℝ))) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hmeas : ∀ (n : ℕ) (o : Fin n), Measurable (errW ξ n o) := fun n o => hmeasξ _
  have hindep : ∀ n : ℕ, iIndepFun (errW ξ n) P := fun n =>
    hindepξ.precomp (g := fun o : Fin n => (n, o.val))
      (fun a b hab => Fin.val_injective (congrArg Prod.snd hab))
  have hmean : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ∂P = 0 := by
    intro n o
    show ∫ ω, ξ (n, o.val) ω ∂P = 0
    rw [(hlawξ (n, o.val)).integral_eq, integral_id_rade]
  have hL2 : ∀ (n : ℕ) (o : Fin n), MemLp (errW ξ n o) 2 P := fun n o =>
    (hlawξ (n, o.val)).memLp memLp_id_rade
  have hint4 : ∀ (n : ℕ) (o : Fin n), Integrable (fun ω => errW ξ n o ω ^ 4) P := fun n o =>
    (hlawξ (n, o.val)).integrable_fun_comp integrable_pow4_rade
  have hvar : ∀ (n : ℕ) (o : Fin n), Var[errW ξ n o; P] = 1 := by
    intro n o
    show Var[ξ (n, o.val); P] = 1
    rw [(hlawξ (n, o.val)).variance_eq, variance_id_rade]
  have hmom : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ^ 4 ∂P ≤ 1 := by
    intro n o
    show ∫ ω, ξ (n, o.val) ω ^ 4 ∂P ≤ 1
    have h : ∫ ω, ξ (n, o.val) ω ^ 4 ∂P = ∫ x, x ^ 4 ∂rade := by
      simpa [Function.comp_def] using
        (hlawξ (n, o.val)).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [h, integral_pow4_rade]
  have hMFE : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsMFESlope (⨆ m, feSpace n m) (Xmap n) (yW ξ β n ω) (bW ξ β n ω) := by
    filter_upwards [eventually_ge_atTop 2] with n hn ω
    exact isMFESlope_bW ξ β hn ω
  have hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, feSpace n m) (Xmap n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact identified_witness hn
  have hJM : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (Xmap n))
        (Xmap n) (yW ξ β n ω) (bW ξ β n ω) := by
    filter_upwards [hid, hMFE] with n hidn hMFEn ω
    exact (jm_equiv hidn (dvec_mem n) _ _).mpr (hMFEn ω)
  refine ⟨Ω, mΩ, P, hprobξ, ξ, hJM, hMFE, ?_, ?_, ?_, ?_⟩
  · exact (clt_a (O := fun n => Fin n) (fun n => Fintype.card_fin n) feSpace Xmap β
      feW (fun n m => feW_mem n m) (nuW ξ) (yW ξ β) (fun n ω => rfl)
      (aaW ξ) (fun n m ω => aaW_mem ξ n m ω) (errW ξ) (fun _ _ => 1) 1
      (fun n ω => rfl) hmeas hindep hmean hL2 hint4 hvar hmom
      1 Matrix.PosDef.one hSn_witness hlin4_witness Aop
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) hAsolve_witness hAlim_witness
      dvec dvec_mem hid (bW ξ β) (bW ξ β)
      (fun n => (measurable_bW hmeasξ β n).aemeasurable)
      (fun n => (measurable_bW hmeasξ β n).aemeasurable) hJM hMFE).1
  · exact (clt_a_of_gram_limit (O := fun n => Fin n) (fun n => Fintype.card_fin n) feSpace Xmap β
      feW (fun n m => feW_mem n m) (nuW ξ) (yW ξ β) (fun n ω => rfl)
      (aaW ξ) (fun n m ω => aaW_mem ξ n m ω) (errW ξ) (fun _ _ => 1) 1
      (fun n ω => rfl) hmeas hindep hmean hL2 hint4 hvar hmom
      1 Matrix.PosDef.one hSn_witness hlin4_witness 1 hHpos_witness hHlim_witness
      dvec dvec_mem hid (bW ξ β) (bW ξ β)
      (fun n => (measurable_bW hmeasξ β n).aemeasurable)
      (fun n => (measurable_bW hmeasξ β n).aemeasurable) hJM hMFE).1
  · exact (clt_a_consistency feSpace Xmap β feW (fun n m => feW_mem n m) (nuW ξ) (yW ξ β)
      (fun n ω => rfl) (aaW ξ) (fun n m ω => aaW_mem ξ n m ω) (errW ξ) (fun _ _ => 1)
      (fun n ω => rfl) hmeas hindep hmean hL2 hvar 1 hSn_witness Aop
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) hAsolve_witness hAlim_witness
      dvec dvec_mem hid (bW ξ β) (bW ξ β)
      (fun n => (measurable_bW hmeasξ β n).aemeasurable)
      (fun n => (measurable_bW hmeasξ β n).aemeasurable) hJM hMFE).1
  · filter_upwards [eventually_ge_atTop 2] with n hn t
    exact variance_bW ξ β hn (hindep n) (hL2 n) (hvar n) t

end Witness

/-! ### Removing the conditioning on the design

The theorems of this section are unconditional limit laws under the full measure `P`, with the
design allowed to be random. The design enters through `d`, the vector of design convergences
(in probability), and through `hcond`. The argument passes to a subsequence along which `d`
converges almost surely, applies dominated convergence to the conditional characteristic
function `φ_n(t) = 𝔼[exp(i⟪Y_n,t⟫) ∣ 𝒟]`, and concludes with the tower property and Lévy's
continuity theorem, via `Multiway.CLTMartingale.CondD`. -/

section Deconditioning

open CLTMartingale.CondD

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The constant sequence `0` converges to `0` in probability, with the measurable space
written out explicitly. -/
theorem tendstoInMeasure_trivialDesign (P : @Measure Ω mΩ) [IsProbabilityMeasure P] :
    TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => (0 : ℝ)) := by
  intro ε hε
  have hset : {_x : Ω | ε ≤ edist (0 : ℝ) 0} = (∅ : Set Ω) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, edist_self,
      nonpos_iff_eq_zero]
    exact hε.ne'
  simp only [hset, measure_empty]
  exact tendsto_const_nhds

/-- At the trivial σ-field the conditional characteristic function is the ordinary one:
`𝔼[exp(i⟪Y,t⟫) ∣ ⊥] = charFun(law Y)(t)`. -/
theorem condCharFunD_bot {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P] {Y : Ω → E} (hY : AEMeasurable Y P) (t : E) :
    condCharFunD ⊥ P Y t = fun _ => charFun (@Measure.map Ω E mΩ _ Y P) t := by
  have hcont : Continuous fun x : E => Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) := by fun_prop
  rw [condCharFunD, condExp_bot, charFun_apply, integral_map hY hcont.aestronglyMeasurable]

/-- Almost-everywhere convergence of `φ_n(t)` from a frozen conditional law. `Q ω` is a
conditional law of the disturbances given the design, `Y₀ ω` the statistic in the design frozen
at `ω`; `hfreeze` identifies `φ_n(t)` with the frozen characteristic function and `hfrozen` is the
frozen limit theorem. -/
theorem tendsto_condCharFunD_of_frozen
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (𝒟 : MeasurableSpace Ω) (P : @Measure Ω mΩ) (Y : ℕ → Ω → E)
    {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} (Q : Ω → @Measure Ω₀ mΩ₀)
    [∀ ω, IsProbabilityMeasure (Q ω)] (Y₀ : Ω → ℕ → Ω₀ → E)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (P' : @Measure Ω' mΩ') [IsProbabilityMeasure P']
    (Z : Ω' → E)
    (hfreeze : ∀ (n : ℕ) (t : E), condCharFunD 𝒟 P (Y n) t
      =ᵐ[P] fun ω => charFun (@Measure.map Ω₀ E mΩ₀ _ (Y₀ ω n) (Q ω)) t)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mΩ₀)
      (Y₀ ω) atTop Z (fun _ => Q ω) P')
    (t : E) :
    ∀ᵐ ω ∂P, Tendsto (fun n => condCharFunD 𝒟 P (Y n) t ω) atTop
      (𝓝 (charFun (@Measure.map Ω' E mΩ' _ Z P') t)) := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      condCharFunD 𝒟 P (Y n) t ω = charFun (@Measure.map Ω₀ E mΩ₀ _ (Y₀ ω n) (Q ω)) t :=
    ae_all_iff.2 fun n => hfreeze n t
  filter_upwards [hall, hfrozen] with ω hω hcl
  have h : Tendsto (fun n : ℕ => charFun (@Measure.map Ω₀ E mΩ₀ _ (Y₀ ω n) (Q ω)) t) atTop
      (𝓝 (charFun (@Measure.map Ω' E mΩ' _ Z P') t)) := hcl.tendsto_charFun t
  exact Tendsto.congr (fun n => (hω n).symm) h

/-- **Theorem 4(a), unconditional form.** If the design convergences hold in probability and
the conditional limit holds along subsequences (`hcond`), then `√n(β̂_n - β)` converges in
distribution under `P`. -/
theorem clt_a_unconditional
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    {F : Type*} [PseudoEMetricSpace F] {d : ℕ → Ω → F} {L : Ω → F}
    (hdes : TendstoInMeasure P d atTop L)
    (β : EuclideanSpace ℝ (Fin K)) {b : ℕ → Ω → EuclideanSpace ℝ (Fin K)}
    (hY : ∀ n : ℕ, AEMeasurable (fun ω => Real.sqrt n • (b n ω - β)) P)
    (Smat : Matrix (Fin K) (Fin K) ℝ)
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hcond : ∀ t : EuclideanSpace ℝ (Fin K), ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      (∀ᵐ ω ∂P, Tendsto (fun i => d (ns i) ω) atTop (𝓝 (L ω))) →
      ∀ᵐ ω ∂P, Tendsto (fun i => condCharFunD 𝒟 P
          (fun ω => Real.sqrt (ns i) • (b (ns i) ω - β)) t ω) atTop
        (𝓝 (charFun ((multivariateGaussian 0 Smat).map (fun z => Hinv z)) t))) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun (n : ℕ) ω => Real.sqrt n • (b n ω - β)) atTop
      (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  have hZ : AEMeasurable (fun z : EuclideanSpace ℝ (Fin K) => Hinv z)
      (multivariateGaussian 0 Smat) := Hinv.continuous.measurable.aemeasurable
  exact tendstoInDistribution_of_deconditioning 𝒟 h𝒟 P hdes hY hZ hcond

/-- The unconditional limit law when `φ_n(t) → ψ` almost surely along the whole sequence. -/
theorem clt_a_unconditional_of_tendsto_condCharFunD
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (β : EuclideanSpace ℝ (Fin K)) {b : ℕ → Ω → EuclideanSpace ℝ (Fin K)}
    (hY : ∀ n : ℕ, AEMeasurable (fun ω => Real.sqrt n • (b n ω - β)) P)
    (Smat : Matrix (Fin K) (Fin K) ℝ)
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hcond : ∀ t : EuclideanSpace ℝ (Fin K), ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => condCharFunD 𝒟 P
          (fun ω => Real.sqrt n • (b n ω - β)) t ω) atTop
        (𝓝 (charFun ((multivariateGaussian 0 Smat).map (fun z => Hinv z)) t))) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun (n : ℕ) ω => Real.sqrt n • (b n ω - β)) atTop
      (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine clt_a_unconditional 𝒟 h𝒟 P (tendstoInMeasure_trivialDesign P) β hY Smat Hinv ?_
  intro t ns hns _
  filter_upwards [hcond t] with ω hω
  exact hω.comp hns

/-- The unconditional limit law from a frozen conditional law `Q ω` and frozen estimator
`b₀ ω`: `hfreeze` identifies the conditional characteristic function with the frozen one, and
`hfrozen` is the frozen limit theorem (the conclusion of `clt_a`). -/
theorem clt_a_unconditional_of_frozen
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (β : EuclideanSpace ℝ (Fin K)) {b : ℕ → Ω → EuclideanSpace ℝ (Fin K)}
    (hY : ∀ n : ℕ, AEMeasurable (fun ω => Real.sqrt n • (b n ω - β)) P)
    (Smat : Matrix (Fin K) (Fin K) ℝ)
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} (Q : Ω → @Measure Ω₀ mΩ₀)
    [∀ ω, IsProbabilityMeasure (Q ω)]
    (b₀ : Ω → ℕ → Ω₀ → EuclideanSpace ℝ (Fin K))
    (hfreeze : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin K)),
      condCharFunD 𝒟 P (fun ω => Real.sqrt n • (b n ω - β)) t
        =ᵐ[P] fun ω => charFun (@Measure.map Ω₀ (EuclideanSpace ℝ (Fin K)) mΩ₀ _
          (fun ω₀ => Real.sqrt n • (b₀ ω n ω₀ - β)) (Q ω)) t)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mΩ₀)
      (fun (n : ℕ) (ω₀ : Ω₀) => Real.sqrt n • (b₀ ω n ω₀ - β)) atTop
      (fun z => Hinv z) (fun _ => Q ω) (multivariateGaussian 0 Smat)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun (n : ℕ) ω => Real.sqrt n • (b n ω - β)) atTop
      (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine clt_a_unconditional_of_tendsto_condCharFunD 𝒟 h𝒟 P β hY Smat Hinv fun t => ?_
  exact tendsto_condCharFunD_of_frozen 𝒟 P (fun n ω => Real.sqrt n • (b n ω - β)) Q
    (fun ω n ω₀ => Real.sqrt n • (b₀ ω n ω₀ - β)) (multivariateGaussian 0 Smat)
    (fun z => Hinv z) hfreeze hfrozen t

end Deconditioning

/-! ### The unconditional limit law from a measurable design

Here the frozen conditional law is `ProbabilityTheory.condExpKernel P 𝒟`, and the freezing
property is proved in `Multiway.CLTMartingale.CondD`: a `𝒟`-measurable variable is almost surely
constant under the conditional law. The hypotheses are that `β̂_n` is a measurable function of
a `𝒟`-measurable design and the disturbances, with `Ω` standard Borel. -/

section FrozenDesign

open CLTMartingale.CondD

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {K : ℕ}

/-- **Theorem 4(a), unconditional form**, for an estimator that is a measurable function of a
`𝒟`-measurable design and the disturbances: `√n(β̂_n - β) ⟶^d H^{-1}N(0,S)` under `P`, given
the frozen limit theorem `hfrozen` under `condExpKernel P 𝒟`. -/
theorem clt_a_unconditional_of_design (h𝒟 : 𝒟 ≤ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (β : EuclideanSpace ℝ (Fin K))
    {γ : Type*} [MeasurableSpace γ] [MeasurableEq γ]
    {D : ℕ → Ω → γ} (hD : ∀ n, Measurable[𝒟] (D n))
    {F : ℕ → γ → Ω → EuclideanSpace ℝ (Fin K)}
    (hF : ∀ n, Measurable (Function.uncurry (F n)))
    {b : ℕ → Ω → EuclideanSpace ℝ (Fin K)} (hb : ∀ n ω, b n ω = F n (D n ω) ω)
    (Smat : Matrix (Fin K) (Fin K) ℝ)
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun (n : ℕ) (y : Ω) => Real.sqrt n • (F n (D n ω) y - β)) atTop
      (fun z => Hinv z) (fun _ => condExpKernel P 𝒟 ω) (multivariateGaussian 0 Smat)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun (n : ℕ) ω => Real.sqrt n • (b n ω - β)) atTop
      (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  have hZ : AEMeasurable (fun z : EuclideanSpace ℝ (Fin K) => Hinv z)
      (multivariateGaussian 0 Smat) := Hinv.continuous.measurable.aemeasurable
  refine tendstoInDistribution_of_design (E := EuclideanSpace ℝ (Fin K)) h𝒟 P hD
    (F := fun n g y => Real.sqrt n • (F n g y - β)) (fun n => ?_)
    (Y := fun n ω => Real.sqrt n • (b n ω - β)) (fun n ω => by rw [hb n ω]) hZ hfrozen
  have h : Measurable fun z : γ × Ω => F n z.1 z.2 := hF n
  show Measurable fun z : γ × Ω => Real.sqrt n • (F n z.1 z.2 - β)
  fun_prop

end FrozenDesign

/-! ### A model for the unconditional theorem at the trivial σ-field -/

namespace Witness

/-- The hypotheses of `clt_a_unconditional_of_frozen` hold on the model of `clt_a_witness`
at `𝒟 = ⊥`, with `hfrozen` supplied by `clt_a` and `hfreeze` by `condCharFunD_bot`. The second
conjunct is the variance formula `(t_0)²n/(n-1)`. -/
theorem clt_a_unconditional_witness (β : EuclideanSpace ℝ (Fin 1)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bW ξ β n ω - β)) atTop
        (fun z => (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) z) (fun _ => P)
        (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
    ∧ (∀ᶠ n : ℕ in atTop, ∀ t : EuclideanSpace ℝ (Fin 1),
        Var[fun ω => ⟪Real.sqrt n • (bW ξ β n ω - β), t⟫; P]
          = (t 0) ^ 2 * ((n : ℝ) / ((n - 1 : ℕ) : ℝ))) := by
  obtain ⟨Ω, mΩ, P, hP, ξ, _, _, hclt, _, _, hvar⟩ := clt_a_witness β
  refine ⟨Ω, mΩ, P, hP, ξ, ?_, hvar⟩
  exact clt_a_unconditional_of_frozen ⊥ bot_le P β hclt.forall_aemeasurable 1
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) (fun _ => P)
    (fun _ n ω => bW ξ β n ω)
    (fun n t => by rw [condCharFunD_bot P (hclt.forall_aemeasurable n) t])
    (Filter.Eventually.of_forall fun _ => hclt)

end Witness


/-! ### A model for `clt_a_unconditional_of_design` with a nontrivial design σ-field

On the two-coin model of `Multiway.CLTMartingale.CondD.FrozenWitness`, `𝒟 = σ(first coin)` is a
proper sub-σ-field, the design is the first coin, and the conditional law differs from the
unconditional one. The limit here is degenerate. -/

namespace FrozenWitness

open CLTMartingale.CondD.FrozenWitness

/-- `√n/(n+1) → 0`. -/
theorem tendsto_sqrt_div :
    Tendsto (fun n : ℕ => Real.sqrt n * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    refine Filter.Tendsto.inv_tendsto_atTop ?_
    exact Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hg
  have h1 : Real.sqrt n ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  calc Real.sqrt n * ((n : ℝ) + 1)⁻¹
      ≤ Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (Real.sqrt ((n : ℝ) + 1))⁻¹ := by
        rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]

/-- A deterministic sequence converging in `E` converges in distribution to its limit under
any probability measure. -/
theorem tendstoInDistribution_of_tendsto_const {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω' Ω'' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mΩ'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {v : ℕ → E} {v₀ : E} {Z : Ω'' → E} (hZ : ∀ ω, Z ω = v₀)
    (hv : Tendsto v atTop (𝓝 v₀)) :
    TendstoInDistribution (fun (n : ℕ) (_ : Ω') => v n) atTop Z (fun _ => μ') μ'' := by
  have hZeq : Z = fun _ => v₀ := funext hZ
  have hZm : AEMeasurable Z μ'' := by rw [hZeq]; exact aemeasurable_const
  refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun _ => aemeasurable_const) hZm).2 fun f => ?_
  have h2 : ∫ ω, f (Z ω) ∂μ'' = f v₀ := by rw [hZeq]; simp
  have hone : μ'.real (Set.univ : Set Ω') = 1 := by simp [MeasureTheory.measureReal_def]
  simp only [h2, integral_const, hone, one_smul]
  exact (f.continuous.tendsto v₀).comp hv

/-- The unit of `ℝ^1`. -/
noncomputable def uvec : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 fun _ => (1 : ℝ)

/-- The design sequence `±(n+1)^{-1}`, with sign given by the first coin. -/
noncomputable def dsn (n : ℕ) (ω : Omg) : EuclideanSpace ℝ (Fin 1) :=
  (((n : ℝ) + 1)⁻¹ * (if ω.1 then (1 : ℝ) else -1)) • uvec

theorem dsn_apply (n : ℕ) (ω : Omg) :
    dsn n ω 0 = ((n : ℝ) + 1)⁻¹ * (if ω.1 then (1 : ℝ) else -1) := by
  cases h : ω.1 <;> simp [dsn, uvec, h]

theorem meas_dsn (n : ℕ) : Measurable[Dsig] (dsn n) := by
  have h : dsn n = (fun b : Bool =>
      (((n : ℝ) + 1)⁻¹ * (if b then (1 : ℝ) else -1)) • uvec) ∘ Prod.fst := rfl
  rw [h]
  exact Measurable.of_discrete.comp meas_fst

theorem tendsto_stat (ω : Omg) :
    Tendsto (fun n : ℕ => Real.sqrt n • dsn n ω) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ =>
      (Real.sqrt n * (((n : ℝ) + 1)⁻¹ * (if ω.1 then (1 : ℝ) else -1))) • uvec) atTop
      (𝓝 ((0 : ℝ) • uvec)) := by
    refine Filter.Tendsto.smul_const ?_ uvec
    have := tendsto_sqrt_div.mul_const (if ω.1 then (1 : ℝ) else -1)
    simpa [mul_assoc] using this
  simpa [dsn, smul_smul] using h

/-- Every hypothesis of `clt_a_unconditional_of_design` holds on the two-coin model, and its
conclusion follows. The first conjunct says the design is nonzero, varies with `n`, and is
random. -/
theorem design_witness (β : EuclideanSpace ℝ (Fin 1)) :
    (∀ n ω, dsn n ω 0 = ((n : ℝ) + 1)⁻¹ * (if ω.1 then (1 : ℝ) else -1))
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Omg))
        (fun (n : ℕ) ω => Real.sqrt n • ((β + dsn n ω) - β)) atTop
        (fun z => (0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) z)
        (fun _ => Pw) (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have : ∀ ω : Omg, IsProbabilityMeasure (condExpKernel Pw Dsig ω) := fun _ => inferInstance
  refine ⟨dsn_apply, ?_⟩
  refine clt_a_unconditional_of_design (𝒟 := Dsig) Dsig_le Pw β
    (D := dsn) meas_dsn (F := fun _ g _ => β + g) (fun n => by fun_prop)
    (b := fun n ω => β + dsn n ω) (fun _ _ => rfl)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hfun : (fun (n : ℕ) (_ : Omg) => Real.sqrt n • (β + dsn n ω - β))
      = fun (n : ℕ) (_ : Omg) => Real.sqrt n • dsn n ω := by
    funext n y
    congr 1
    abel
  rw [hfun]
  refine tendstoInDistribution_of_tendsto_const (v := fun n => Real.sqrt n • dsn n ω)
    (μ' := condExpKernel Pw Dsig ω)
    (μ'' := multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)) (v₀ := 0)
    (Z := fun z => (0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) z)
    (fun _ => rfl) ?_
  simpa using tendsto_stat ω

end FrozenWitness
/-! ### Part (b): Regime 2

Under Regime 2 the score is `X̃'ν = ∑_{2≤|e|≤M}∑_{t∈𝒯_e}w^{(e)}_th^{(e)}(U_t) + ∑_o x̃_oε_o`.
The limit laws of part (b) are derived from the directional hypothesis `hdir`,
`n^{-1/2}c'X̃'ν ⟶^d N(0,c'Sc)` for each `c`, together with the design algebra and the score
equation. The directional limit is obtained in `Multiway.CLTMartingale` from a martingale CLT and
a truncation argument. -/

section PartB

variable {K : ℕ}

/-- The Cramér–Wold assembly of a Gaussian limit from its directional limits. -/
theorem tendstoInDistribution_gaussian_of_inner
    {W : ℕ → Ω → EuclideanSpace ℝ (Fin K)} (hW : ∀ n, AEMeasurable (W n) P)
    {Smat : Matrix (Fin K) (Fin K) ℝ} (hSpd : Smat.PosDef)
    (h : ∀ t : EuclideanSpace ℝ (Fin K), t ≠ 0 →
      TendstoInDistribution (fun (n : ℕ) ω => ⟪W n ω, t⟫) atTop (id : ℝ → ℝ) (fun _ => P)
        (gaussianReal 0 (t ⬝ᵥ (Smat *ᵥ t)).toNNReal)) :
    TendstoInDistribution W atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Smat) := by
  refine TendstoInDistribution.of_inner (by fun_prop) hW ?_
  intro t
  by_cases ht : t = 0
  · subst ht
    simpa using (tendstoInDistribution_zero (P := P)
      (μ'' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin K)) Smat))
  · have hlaw : (multivariateGaussian 0 Smat).map (fun x => ⟪x, t⟫)
        = (gaussianReal 0 (t ⬝ᵥ (Smat *ᵥ t)).toNNReal).map (id : ℝ → ℝ) := by
      rw [Measure.map_id, map_inner_multivariateGaussian hSpd.posSemidef t]
    exact tendstoInDistribution_of_law_eq (h t ht) (by fun_prop) hlaw

/-- **Theorem 4(b)** for `β̂_MFE`. -/
theorem clt_b_mfe
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (hnumeas : ∀ n o, Measurable fun ω => nu n ω o)
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    (hdir : ∀ t : EuclideanSpace ℝ (Fin K), t ≠ 0 →
      TendstoInDistribution
        (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ⟪score (⨆ m, Sm n m) (Xm n) (nu n ω), t⟫) atTop
        (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 (t ⬝ᵥ (Smat *ᵥ t)).toNNReal))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (b : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbmeas : ∀ n, AEMeasurable (b n) P)
    (hb : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (b n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (b n ω - β)) atTop
      (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine slope_clt_of_score Sm Xm β fe hfe nu yv hmodel Smat ?_ A Hinv hAsolve hAlim b hbmeas hb
  refine tendstoInDistribution_gaussian_of_inner ?_ hSpd ?_
  · intro n
    exact ((measurable_score _ _ (hnumeas n)).const_smul ((Real.sqrt n)⁻¹ : ℝ)).aemeasurable
  · intro t ht
    refine (hdir t ht).congr (fun n => ?_) (by rfl)
    filter_upwards with ω
    rw [real_inner_smul_left]

/-- **Theorem 4(b).** The limit laws for `β̂_JM` and `β̂_MFE`. -/
theorem clt_b
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (hnumeas : ∀ n o, Measurable fun ω => nu n ω o)
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    (hdir : ∀ t : EuclideanSpace ℝ (Fin K), t ≠ 0 →
      TendstoInDistribution
        (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ⟪score (⨆ m, Sm n m) (Xm n) (nu n ω), t⟫) atTop
        (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 (t ⬝ᵥ (Smat *ᵥ t)).toNNReal))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (ιv : ∀ n, EuclideanSpace ℝ (O n)) (hι : ∀ n, ιv n ∈ ⨆ m, Sm n m)
    (hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, Sm n m) (Xm n))
    (bJM bMFE : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbJMmeas : ∀ n, AEMeasurable (bJM n) P) (hbMFEmeas : ∀ n, AEMeasurable (bMFE n) P)
    (hbJM : ∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (ιv n) (⨆ m, Sm n m) (Xm n)) (Xm n)
      (yv n ω) (bJM n ω))
    (hbMFE : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (bMFE n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bJM n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat)
      ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bMFE n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine ⟨?_, ?_⟩
  · refine clt_b_mfe Sm Xm β fe hfe nu yv hmodel hnumeas Smat hSpd hdir A Hinv hAsolve hAlim
      bJM hbJMmeas ?_
    filter_upwards [hid, hbJM] with n hidn hbn ω
    exact isMFESlope_of_isAugSlope_jm hidn (hι n) _ _ (hbn ω)
  · exact clt_b_mfe Sm Xm β fe hfe nu yv hmodel hnumeas Smat hSpd hdir A Hinv hAsolve hAlim
      bMFE hbMFEmeas hbMFE

end PartB

/-! ### A model for `clt_b`

A sequence of designs on which every hypothesis of `clt_b` holds, with `hdir` supplied by
`scalar_clt`. -/

namespace Witness

/-- Every hypothesis of `clt_b` holds on the witness model, and its conclusion follows. -/
theorem clt_b_witness (β : EuclideanSpace ℝ (Fin 1)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (Xmap n))
          (Xmap n) (yW ξ β n ω) (bW ξ β n ω))
    ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bW ξ β n ω - β)) atTop
        (fun z => (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) z) (fun _ => P)
        (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
    ∧ (∀ᶠ n : ℕ in atTop, ∀ t : EuclideanSpace ℝ (Fin 1),
        Var[fun ω => ⟪Real.sqrt n • (bW ξ β n ω - β), t⟫; P]
          = (t 0) ^ 2 * ((n : ℝ) / ((n - 1 : ℕ) : ℝ))) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hmeas : ∀ (n : ℕ) (o : Fin n), Measurable (errW ξ n o) := fun n o => hmeasξ _
  have hindep : ∀ n : ℕ, iIndepFun (errW ξ n) P := fun n =>
    hindepξ.precomp (g := fun o : Fin n => (n, o.val))
      (fun a b hab => Fin.val_injective (congrArg Prod.snd hab))
  have hmean : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ∂P = 0 := by
    intro n o
    show ∫ ω, ξ (n, o.val) ω ∂P = 0
    rw [(hlawξ (n, o.val)).integral_eq, integral_id_rade]
  have hL2 : ∀ (n : ℕ) (o : Fin n), MemLp (errW ξ n o) 2 P := fun n o =>
    (hlawξ (n, o.val)).memLp memLp_id_rade
  have hint4 : ∀ (n : ℕ) (o : Fin n), Integrable (fun ω => errW ξ n o ω ^ 4) P := fun n o =>
    (hlawξ (n, o.val)).integrable_fun_comp integrable_pow4_rade
  have hvar : ∀ (n : ℕ) (o : Fin n), Var[errW ξ n o; P] = 1 := by
    intro n o
    show Var[ξ (n, o.val); P] = 1
    rw [(hlawξ (n, o.val)).variance_eq, variance_id_rade]
  have hmom : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ^ 4 ∂P ≤ 1 := by
    intro n o
    show ∫ ω, ξ (n, o.val) ω ^ 4 ∂P ≤ 1
    have h : ∫ ω, ξ (n, o.val) ω ^ 4 ∂P = ∫ x, x ^ 4 ∂rade := by
      simpa [Function.comp_def] using
        (hlawξ (n, o.val)).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [h, integral_pow4_rade]
  have hMFE : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsMFESlope (⨆ m, feSpace n m) (Xmap n) (yW ξ β n ω) (bW ξ β n ω) := by
    filter_upwards [eventually_ge_atTop 2] with n hn ω
    exact isMFESlope_bW ξ β hn ω
  have hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, feSpace n m) (Xmap n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact identified_witness hn
  have hJM : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (Xmap n))
        (Xmap n) (yW ξ β n ω) (bW ξ β n ω) := by
    filter_upwards [hid, hMFE] with n hidn hMFEn ω
    exact (jm_equiv hidn (dvec_mem n) _ _).mpr (hMFEn ω)
  have hnumeas : ∀ (n : ℕ) (o : Fin n), Measurable fun ω => nuW ξ n ω o := by
    intro n o
    simp only [nuW_apply]
    exact ((hmeasξ (0, 0)).mul_const _).add (hmeasξ (n, o.val))
  have hdir : ∀ t : EuclideanSpace ℝ (Fin 1), t ≠ 0 →
      TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
          ⟪score (⨆ m, feSpace n m) (Xmap n) (nuW ξ n ω), t⟫) atTop
        (id : ℝ → ℝ) (fun _ => P)
        (gaussianReal 0 (t ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ t)).toNNReal) := by
    intro t ht
    have hs2 : 0 < t ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ t) :=
      dotProduct_mulVec_pos_of_posDef Matrix.PosDef.one ht
    have T := scalar_clt (P := P) (O := fun n => Fin n) (fun n => Fintype.card_fin n)
      (fun n o => ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫) (errW ξ) (fun _ _ => (1 : ℝ))
      1 _ hmeas hindep hmean hL2 hint4 hvar hmom hs2 (hSn_witness t) (hlin4_witness t)
    refine T.congr (fun n => ?_) (by rfl)
    filter_upwards with ω
    rw [inner_score_eq_sum (feSpace n) (Xmap n) (aaW ξ n) (fun m ω => aaW_mem ξ n m ω)
      (errW ξ n) (nuW ξ n) (fun ω => rfl) t ω]
  refine ⟨Ω, mΩ, P, hprobξ, ξ, hJM, ?_, ?_⟩
  · exact (clt_b (O := fun n => Fin n) feSpace Xmap β feW (fun n m => feW_mem n m)
      (nuW ξ) (yW ξ β) (fun n ω => rfl) hnumeas 1 Matrix.PosDef.one hdir Aop
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) hAsolve_witness hAlim_witness
      dvec dvec_mem hid (bW ξ β) (bW ξ β)
      (fun n => (measurable_bW hmeasξ β n).aemeasurable)
      (fun n => (measurable_bW hmeasξ β n).aemeasurable) hJM hMFE).1
  · filter_upwards [eventually_ge_atTop 2] with n hn t
    exact variance_bW ξ β hn (hindep n) (hL2 n) (hvar n) t

end Witness

/-! ### The Regime-2 variance identity and consistency

The disturbance is
`ν = ∑_m a^{(m)} + ∑_{2≤|e|≤M}∑_{t∈𝒯_e}h^{(e)}(U_t)·𝟙_{cell t} + ε`, with the interaction terms
indexed by a finite type `G` (one element per pair `(e,t)`). This section proves
`Var(X̃'ν ∣ 𝒟) = ∑_o x̃_ox̃_o'σ²_ε(o) + ∑_{g}σ_g² w_g w_g' = nS_n` along a realization of `𝒟`,
and consistency `β̂ ⟶^p β` for both estimators. The orthogonality `hZorth` of distinct interaction
terms is proved in `Multiway.CLTMartingale.Orth`. -/

/-- `X̃'(∑_i v_i) = ∑_i X̃'v_i`. -/
lemma score_finsetSum {O : Type*} [Fintype O] {A : Type*} (S : Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O) (s : Finset A)
    (v : A → EuclideanSpace ℝ O) :
    score S X (∑ i ∈ s, v i) = ∑ i ∈ s, score S X (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [score]
  | insert i s hi ih => rw [Finset.sum_insert hi, score_add, ih, Finset.sum_insert hi]

set_option linter.unusedSectionVars false in
/-- Pathwise, the Regime-2 score is the weighted sum of the interaction terms plus the
cell-level part. -/
lemma inner_score_eq_sum_E2 {O : Type*} [Fintype O] {M : ℕ} {Γ : Type*} [Fintype Γ]
    (Sm : Fin M → Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (aa : Fin M → Ω → EuclideanSpace ℝ O) (haa : ∀ m ω, aa m ω ∈ Sm m)
    (wvec : Γ → EuclideanSpace ℝ O) (Z : Γ → Ω → ℝ)
    (e : O → Ω → ℝ) (nu : Ω → EuclideanSpace ℝ O)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + ((∑ γ, Z γ ω • wvec γ)
      + (WithLp.toLp 2 fun o => e o ω)))
    (t : EuclideanSpace ℝ (Fin K)) (ω : Ω) :
    ⟪score (⨆ m, Sm m) X (nu ω), t⟫
      = (∑ γ, ⟪score (⨆ m, Sm m) X (wvec γ), t⟫ * Z γ ω)
        + ∑ o, ⟪withinRow (⨆ m, Sm m) X o, t⟫ * e o ω := by
  rw [hregime ω, score_absorb (fun m => haa m ω), score_add]
  rw [inner_add_left, score_finsetSum]
  congr 1
  · rw [sum_inner]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [score_smul, real_inner_smul_left, mul_comm]
  · have h : score (⨆ m, Sm m) X (WithLp.toLp 2 fun o => e o ω)
        = ∑ o, e o ω • withinRow (⨆ m, Sm m) X o := rfl
    rw [h, sum_inner]
    exact Finset.sum_congr rfl fun o _ => by rw [real_inner_smul_left]; ring

/-- `Var(X̃'ν ∣ 𝒟) = nS_n` under Regime 2, in the quadratic-form reading and along a realization
of `𝒟`. -/
theorem variance_score_eq_E2 {O : Type*} [Fintype O] {M : ℕ} {G : Type*} [Fintype G]
    (Sm : Fin M → Submodule ℝ (EuclideanSpace ℝ O))
    (X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O)
    (aa : Fin M → Ω → EuclideanSpace ℝ O) (haa : ∀ m ω, aa m ω ∈ Sm m)
    (wvec : G → EuclideanSpace ℝ O) (Z : G → Ω → ℝ) (sigE : G → ℝ)
    (e : O → Ω → ℝ) (sev : O → ℝ) (nu : Ω → EuclideanSpace ℝ O)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + ((∑ g, Z g ω • wvec g)
      + (WithLp.toLp 2 fun o => e o ω)))
    (hZL2 : ∀ g, MemLp (Z g) 2 P) (hZmean : ∀ g, ∫ ω, Z g ω ∂P = 0)
    (hZsq : ∀ g, ∫ ω, Z g ω ^ 2 ∂P = sigE g)
    (hZorth : ∀ g g', g ≠ g' → ∫ ω, Z g ω * Z g' ω ∂P = 0)
    (hindep : iIndepFun e P) (heL2 : ∀ o, MemLp (e o) 2 P)
    (hemean : ∀ o, ∫ ω, e o ω ∂P = 0) (hevar : ∀ o, Var[e o; P] = sev o)
    (hZe : ∀ (g : G) (o : O), IndepFun (Z g) (e o) P)
    (t : EuclideanSpace ℝ (Fin K)) :
    Var[fun ω => ⟪score (⨆ m, Sm m) X (nu ω), t⟫; P]
      = (∑ g, ⟪score (⨆ m, Sm m) X (wvec g), t⟫ ^ 2 * sigE g)
        + ∑ o, ⟪withinRow (⨆ m, Sm m) X o, t⟫ ^ 2 * sev o := by
  classical
  set Y : G ⊕ O → Ω → ℝ := Sum.elim Z e with hY
  set wt : G ⊕ O → ℝ := Sum.elim (fun g => ⟪score (⨆ m, Sm m) X (wvec g), t⟫)
    (fun o => ⟪withinRow (⨆ m, Sm m) X o, t⟫) with hwt
  have hYL2 : ∀ a, MemLp (Y a) 2 P := by rintro (g | o) <;> simp [hY, hZL2, heL2]
  have hYmean : ∀ a, ∫ ω, Y a ω ∂P = 0 := by rintro (g | o) <;> simp [hY, hZmean, hemean]
  have hesq : ∀ o, ∫ ω, e o ω ^ 2 ∂P = sev o := fun o => by
    rw [← variance_of_integral_eq_zero (heL2 o).aemeasurable (hemean o), hevar o]
  have hprod : ∀ {f g : Ω → ℝ}, IndepFun f g P → AEStronglyMeasurable f P →
      AEStronglyMeasurable g P → ∫ ω, f ω ∂P = 0 → ∫ ω, f ω * g ω ∂P = 0 := by
    intro f g hfg hf hg hf0
    have h := hfg.integral_mul_eq_mul_integral hf hg
    simp only [Pi.mul_apply] at h
    rw [h, hf0, zero_mul]
  have hYorth : ∀ a b, a ≠ b → ∫ ω, Y a ω * Y b ω ∂P = 0 := by
    rintro (g | o) (g' | o') hab <;> simp only [hY, Sum.elim_inl, Sum.elim_inr]
    · exact hZorth g g' (fun h => hab (by rw [h]))
    · exact hprod (hZe g o') (hZL2 g).aestronglyMeasurable (heL2 o').aestronglyMeasurable
        (hZmean g)
    · exact hprod ((hZe g' o).symm) (heL2 o).aestronglyMeasurable (hZL2 g').aestronglyMeasurable
        (hemean o)
    · exact hprod (hindep.indepFun (fun h => hab (by rw [h])))
        (heL2 o).aestronglyMeasurable (heL2 o').aestronglyMeasurable (hemean o)
  have hfun : (fun ω => ⟪score (⨆ m, Sm m) X (nu ω), t⟫) = fun ω => ∑ a, wt a * Y a ω := by
    funext ω
    rw [inner_score_eq_sum_E2 Sm X aa haa wvec Z e nu hregime t ω, Fintype.sum_sum_type]
    simp only [hY, hwt, Sum.elim_inl, Sum.elim_inr]
  rw [hfun, CLTMartingale.variance_sum_of_uncorrelated Y wt hYL2 hYmean hYorth,
    Fintype.sum_sum_type]
  congr 1
  · exact Finset.sum_congr rfl fun g _ => by rw [hY, hwt]; simp [hZsq g]
  · exact Finset.sum_congr rfl fun o _ => by rw [hY, hwt]; simp [hesq o]

section E2Moments

variable {O : Type*} [Fintype O] {M : ℕ} {G : Type*} [Fintype G]
  {Sm : Fin M → Submodule ℝ (EuclideanSpace ℝ O)}
  {X : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ O}
  {aa : Fin M → Ω → EuclideanSpace ℝ O} {wvec : G → EuclideanSpace ℝ O}
  {Z : G → Ω → ℝ} {e : O → Ω → ℝ} {nu : Ω → EuclideanSpace ℝ O}

set_option linter.unusedSectionVars false in
/-- The Regime-2 score is square integrable in every direction. -/
lemma memLp_inner_score_E2 (haa : ∀ m ω, aa m ω ∈ Sm m)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + ((∑ g, Z g ω • wvec g)
      + (WithLp.toLp 2 fun o => e o ω)))
    (hZL2 : ∀ g, MemLp (Z g) 2 P) (heL2 : ∀ o, MemLp (e o) 2 P)
    (t : EuclideanSpace ℝ (Fin K)) :
    MemLp (fun ω => ⟪score (⨆ m, Sm m) X (nu ω), t⟫) 2 P := by
  have hfun : (fun ω => ⟪score (⨆ m, Sm m) X (nu ω), t⟫)
      = fun ω => (∑ g, ⟪score (⨆ m, Sm m) X (wvec g), t⟫ * Z g ω)
        + ∑ o, ⟪withinRow (⨆ m, Sm m) X o, t⟫ * e o ω :=
    funext fun ω => inner_score_eq_sum_E2 Sm X aa haa wvec Z e nu hregime t ω
  rw [hfun]
  exact (memLp_finsetSum _ (fun g _ => (hZL2 g).const_mul _)).add
    (memLp_finsetSum _ (fun o _ => (heL2 o).const_mul _))

/-- The Regime-2 score has mean zero in every direction. -/
lemma integral_inner_score_eq_zero_E2 (haa : ∀ m ω, aa m ω ∈ Sm m)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + ((∑ g, Z g ω • wvec g)
      + (WithLp.toLp 2 fun o => e o ω)))
    (hZL2 : ∀ g, MemLp (Z g) 2 P) (heL2 : ∀ o, MemLp (e o) 2 P)
    (hZmean : ∀ g, ∫ ω, Z g ω ∂P = 0) (hemean : ∀ o, ∫ ω, e o ω ∂P = 0)
    (t : EuclideanSpace ℝ (Fin K)) :
    ∫ ω, ⟪score (⨆ m, Sm m) X (nu ω), t⟫ ∂P = 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => inner_score_eq_sum_E2 Sm X aa haa wvec Z e nu hregime t ω))]
  rw [integral_add (integrable_finsetSum _ (fun g _ =>
      ((hZL2 g).integrable one_le_two).const_mul _))
    (integrable_finsetSum _ (fun o _ => ((heL2 o).integrable one_le_two).const_mul _))]
  rw [integral_finsetSum _ (fun g _ => ((hZL2 g).integrable one_le_two).const_mul _),
    integral_finsetSum _ (fun o _ => ((heL2 o).integrable one_le_two).const_mul _)]
  rw [Finset.sum_eq_zero fun g _ => by rw [integral_const_mul, hZmean g, mul_zero],
    Finset.sum_eq_zero fun o _ => by rw [integral_const_mul, hemean o, mul_zero], add_zero]

variable {sigE : G → ℝ} {sev : O → ℝ}

/-- The directional second moment of the Regime-2 score equals its variance. -/
theorem integral_inner_score_sq_E2 (haa : ∀ m ω, aa m ω ∈ Sm m)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + ((∑ g, Z g ω • wvec g)
      + (WithLp.toLp 2 fun o => e o ω)))
    (hZL2 : ∀ g, MemLp (Z g) 2 P) (hZmean : ∀ g, ∫ ω, Z g ω ∂P = 0)
    (hZsq : ∀ g, ∫ ω, Z g ω ^ 2 ∂P = sigE g)
    (hZorth : ∀ g g', g ≠ g' → ∫ ω, Z g ω * Z g' ω ∂P = 0)
    (hindep : iIndepFun e P) (heL2 : ∀ o, MemLp (e o) 2 P)
    (hemean : ∀ o, ∫ ω, e o ω ∂P = 0) (hevar : ∀ o, Var[e o; P] = sev o)
    (hZe : ∀ (g : G) (o : O), IndepFun (Z g) (e o) P)
    (t : EuclideanSpace ℝ (Fin K)) :
    ∫ ω, ⟪score (⨆ m, Sm m) X (nu ω), t⟫ ^ 2 ∂P
      = (∑ g, ⟪score (⨆ m, Sm m) X (wvec g), t⟫ ^ 2 * sigE g)
        + ∑ o, ⟪withinRow (⨆ m, Sm m) X o, t⟫ ^ 2 * sev o := by
  rw [← variance_of_integral_eq_zero
    (memLp_inner_score_E2 haa hregime hZL2 heL2 t).aemeasurable
    (integral_inner_score_eq_zero_E2 haa hregime hZL2 heL2 hZmean hemean t)]
  exact variance_score_eq_E2 Sm X aa haa wvec Z sigE e sev nu hregime hZL2 hZmean hZsq hZorth
    hindep heL2 hemean hevar hZe t

theorem integrable_norm_score_sq_E2 (haa : ∀ m ω, aa m ω ∈ Sm m)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + ((∑ g, Z g ω • wvec g)
      + (WithLp.toLp 2 fun o => e o ω)))
    (hZL2 : ∀ g, MemLp (Z g) 2 P) (heL2 : ∀ o, MemLp (e o) 2 P) :
    Integrable (fun ω => ‖score (⨆ m, Sm m) X (nu ω)‖ ^ 2) P := by
  refine Integrable.congr (integrable_finsetSum (Finset.univ : Finset (Fin K))
    (fun k _ => (memLp_inner_score_E2 (X := X) haa hregime hZL2 heL2
      (EuclideanSpace.single k (1:ℝ))).integrable_sq)) ?_
  exact Filter.Eventually.of_forall
    (fun ω => (norm_sq_eq_sum_inner (score (⨆ m, Sm m) X (nu ω))).symm)

/-- `E‖X̃'ν‖²` under Regime 2. -/
theorem integral_norm_score_sq_E2 (haa : ∀ m ω, aa m ω ∈ Sm m)
    (hregime : ∀ ω, nu ω = (∑ m, aa m ω) + ((∑ g, Z g ω • wvec g)
      + (WithLp.toLp 2 fun o => e o ω)))
    (hZL2 : ∀ g, MemLp (Z g) 2 P) (hZmean : ∀ g, ∫ ω, Z g ω ∂P = 0)
    (hZsq : ∀ g, ∫ ω, Z g ω ^ 2 ∂P = sigE g)
    (hZorth : ∀ g g', g ≠ g' → ∫ ω, Z g ω * Z g' ω ∂P = 0)
    (hindep : iIndepFun e P) (heL2 : ∀ o, MemLp (e o) 2 P)
    (hemean : ∀ o, ∫ ω, e o ω ∂P = 0) (hevar : ∀ o, Var[e o; P] = sev o)
    (hZe : ∀ (g : G) (o : O), IndepFun (Z g) (e o) P) :
    ∫ ω, ‖score (⨆ m, Sm m) X (nu ω)‖ ^ 2 ∂P
      = ∑ k : Fin K, ((∑ g, ⟪score (⨆ m, Sm m) X (wvec g),
            EuclideanSpace.single k (1:ℝ)⟫ ^ 2 * sigE g)
          + ∑ o, ⟪withinRow (⨆ m, Sm m) X o,
            EuclideanSpace.single k (1:ℝ)⟫ ^ 2 * sev o) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => norm_sq_eq_sum_inner (score (⨆ m, Sm m) X (nu ω))))]
  rw [integral_finsetSum _ (fun k _ => (memLp_inner_score_E2 (X := X) haa hregime hZL2 heL2
    (EuclideanSpace.single k (1:ℝ))).integrable_sq)]
  exact Finset.sum_congr rfl fun k _ =>
    integral_inner_score_sq_E2 haa hregime hZL2 hZmean hZsq hZorth hindep heL2 hemean hevar
      hZe _

end E2Moments

/-- **Theorem 4(b)**, consistency: `β̂_JM ⟶^p β` and `β̂_MFE ⟶^p β`. -/
theorem clt_b_consistency
    {O : ℕ → Type} [∀ n, Fintype (O n)] {G : ℕ → Type} [∀ n, Fintype (G n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (aa : ∀ n, Fin M → Ω → EuclideanSpace ℝ (O n)) (haa : ∀ n m ω, aa n m ω ∈ Sm n m)
    (wvec : ∀ n, G n → EuclideanSpace ℝ (O n)) (Z : ∀ n, G n → Ω → ℝ) (sigE : ∀ n, G n → ℝ)
    (e : ∀ n, O n → Ω → ℝ) (sev : ∀ n, O n → ℝ)
    (hregime : ∀ n ω, nu n ω = (∑ m, aa n m ω) + ((∑ g, Z n g ω • wvec n g)
      + (WithLp.toLp 2 fun o => e n o ω)))
    (hZL2 : ∀ n g, MemLp (Z n g) 2 P) (hZmean : ∀ n g, ∫ ω, Z n g ω ∂P = 0)
    (hZsq : ∀ n g, ∫ ω, Z n g ω ^ 2 ∂P = sigE n g)
    (hZorth : ∀ n, ∀ g g', g ≠ g' → ∫ ω, Z n g ω * Z n g' ω ∂P = 0)
    (hindep : ∀ n, iIndepFun (e n) P) (heL2 : ∀ n o, MemLp (e n o) 2 P)
    (hemean : ∀ n o, ∫ ω, e n o ω ∂P = 0) (hevar : ∀ n o, Var[e n o; P] = sev n o)
    (hZe : ∀ n, ∀ (g : G n) (o : O n), IndepFun (Z n g) (e n o) P)
    (Smat : Matrix (Fin K) (Fin K) ℝ)
    (hSn : ∀ t : EuclideanSpace ℝ (Fin K), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ((∑ g, ⟪score (⨆ m, Sm n m) (Xm n) (wvec n g), t⟫ ^ 2 * sigE n g)
        + ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o, t⟫ ^ 2 * sev n o)) atTop
      (𝓝 (t ⬝ᵥ (Smat *ᵥ t))))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (ιv : ∀ n, EuclideanSpace ℝ (O n)) (hι : ∀ n, ιv n ∈ ⨆ m, Sm n m)
    (hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, Sm n m) (Xm n))
    (bJM bMFE : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbJMmeas : ∀ n, AEMeasurable (bJM n) P) (hbMFEmeas : ∀ n, AEMeasurable (bMFE n) P)
    (hbJM : ∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (ιv n) (⨆ m, Sm n m) (Xm n)) (Xm n)
      (yv n ω) (bJM n ω))
    (hbMFE : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (bMFE n ω)) :
    TendstoInMeasure P bJM atTop (fun _ => β) ∧ TendstoInMeasure P bMFE atTop (fun _ => β) := by
  classical
  have hQint : ∀ n : ℕ, Integrable
      (fun ω => ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2) P := fun n =>
    integrable_norm_score_sq_E2 (haa n) (hregime n) (hZL2 n) (heL2 n)
  have hQlim : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P) atTop
      (𝓝 (∑ k : Fin K, (EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin K)) ⬝ᵥ
        (Smat *ᵥ (EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin K))))) := by
    have hval : ∀ n : ℕ,
        (n : ℝ)⁻¹ * ∫ ω, ‖score (⨆ m, Sm n m) (Xm n) (nu n ω)‖ ^ 2 ∂P
          = ∑ k : Fin K, ((n : ℝ)⁻¹ *
              ((∑ g, ⟪score (⨆ m, Sm n m) (Xm n) (wvec n g),
                  (EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin K))⟫ ^ 2 * sigE n g)
                + ∑ o, ⟪withinRow (⨆ m, Sm n m) (Xm n) o,
                  (EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin K))⟫ ^ 2
                    * sev n o)) := by
      intro n
      rw [integral_norm_score_sq_E2 (haa n) (hregime n) (hZL2 n) (hZmean n) (hZsq n)
        (hZorth n) (hindep n) (heL2 n) (hemean n) (hevar n) (hZe n), Finset.mul_sum]
    refine Tendsto.congr (fun n => (hval n).symm) ?_
    exact tendsto_finsetSum _ (fun k _ => hSn _)
  refine ⟨?_, ?_⟩
  · refine tendstoInMeasure_slope_of_score_L2 Sm Xm β fe hfe nu yv hmodel hQint hQlim
      A Hinv hAsolve hAlim bJM hbJMmeas ?_
    filter_upwards [hid, hbJM] with n hidn hbn ω
    exact isMFESlope_of_isAugSlope_jm hidn (hι n) _ _ (hbn ω)
  · exact tendstoInMeasure_slope_of_score_L2 Sm Xm β fe hfe nu yv hmodel hQint hQlim
      A Hinv hAsolve hAlim bMFE hbMFEmeas hbMFE

/-! ### A model with a Regime-2 disturbance

The design is that of `clt_a_witness`; the disturbance adds two level-`{1,2}` interaction terms
on the cells `{1,2}` and `{3,4}`, with kernel `h(u,v) = ψ(u)ψ(v)`, so that
`Z_0 = ψ(U^{(1)}_1)ψ(U^{(2)}_1)` and `Z_1 = ψ(U^{(1)}_1)ψ(U^{(2)}_2)` share a latent variable.
The witness computes `Var(⟪X̃'ν,t⟫) = (n-1)t_0² + 8t_0²` through `variance_score_eq_E2`, shows that
the Regime-1 identity fails on this design, and derives consistency through
`clt_b_consistency`. -/

namespace Witness


/-- The interaction terms `Z_g`, built from `ξ_{(0,1)}`, `ξ_{(0,2)}` and `ξ_{(0,3)}`; the two
share the dimension-1 variable. -/
noncomputable def zE2 (ξ : ℕ × ℕ → Ω → ℝ) (g : Fin 2) : Ω → ℝ :=
  fun ω => ξ (0, 1) ω * ξ (0, g.val + 2) ω

/-- The indicators of the two level-`{1,2}` cells `{1,2}` and `{3,4}`. -/
noncomputable def wE2 (n : ℕ) (g : Fin 2) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun o : Fin n =>
    (if o.val = 2 * g.val + 1 then (1:ℝ) else 0) + (if o.val = 2 * g.val + 2 then (1:ℝ) else 0)

noncomputable def nuE2 (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  (∑ m, aaW ξ n m ω) + ((∑ g, zE2 ξ g ω • wE2 n g) + (WithLp.toLp 2 fun o => errW ξ n o ω))

noncomputable def yE2 (ξ : ℕ × ℕ → Ω → ℝ) (β : EuclideanSpace ℝ (Fin 1)) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin n) := Xmap n β + (∑ m, feW n m) + nuE2 ξ n ω

/-- The estimator, constructed from the score. -/
noncomputable def bE2 (ξ : ℕ × ℕ → Ω → ℝ) (β : EuclideanSpace ℝ (Fin 1)) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin 1) :=
  β + (((n - 1 : ℕ) : ℝ))⁻¹ • score (⨆ m, feSpace n m) (Xmap n) (nuE2 ξ n ω)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem sum_mul_indicator (n a : ℕ) (ha : a < n) (f : Fin n → ℝ) :
    ∑ o : Fin n, f o * (if o.val = a then (1:ℝ) else 0) = f ⟨a, ha⟩ := by
  rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin n)]
  · simp
  · intro o _ hne
    have h : o.val ≠ a := fun h => hne (Fin.ext h)
    simp [h]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem wE2_apply (n : ℕ) (g : Fin 2) (o : Fin n) :
    wE2 n g o = (if o.val = 2 * g.val + 1 then (1:ℝ) else 0)
      + (if o.val = 2 * g.val + 2 then (1:ℝ) else 0) := rfl

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The cell weights are `w^{(e)}_t = ∑_{o ∈ t}x̃_o = 2`. -/
theorem inner_score_wE2 {n : ℕ} (hn : 5 ≤ n) (g : Fin 2) (t : EuclideanSpace ℝ (Fin 1)) :
    ⟪score (⨆ m, feSpace n m) (Xmap n) (wE2 n g), t⟫ = 2 * t 0 := by
  have hglt : g.val < 2 := g.isLt
  have ha : 2 * g.val + 1 < n := by omega
  have hb : 2 * g.val + 2 < n := by omega
  rw [real_inner_comm, inner_score, jointWithin_Xmap]
  have hXt : (Xmap n) t = (t 0) • xvec n := rfl
  rw [hXt, real_inner_smul_left]
  have hinner : ⟪xvec n, wE2 n g⟫ = ∑ o : Fin n, xvec n o * wE2 n g o := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  rw [hinner]
  have hsplit : ∑ o : Fin n, xvec n o * wE2 n g o
      = (∑ o : Fin n, xvec n o * (if o.val = 2 * g.val + 1 then (1:ℝ) else 0))
        + ∑ o : Fin n, xvec n o * (if o.val = 2 * g.val + 2 then (1:ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun o _ => by rw [wE2_apply]; ring
  rw [hsplit, sum_mul_indicator n _ ha, sum_mul_indicator n _ hb]
  simp only [xvec_apply]
  rw [ite_eq_right (by omega : ¬ (2 * g.val + 1 = 0)),
    ite_eq_right (by omega : ¬ (2 * g.val + 2 = 0))]
  ring

section E2Law

variable {ξ : ℕ × ℕ → Ω → ℝ}

theorem integral_sq_rade : ∫ x, x ^ 2 ∂rade = 1 := by
  rw [integral_rade (f := fun x : ℝ => x ^ 2) (by fun_prop)]; norm_num

theorem integrable_sq_rade : Integrable (fun x : ℝ => x ^ 2) rade := integrable_rade (by fun_prop)

variable (hlawξ : ∀ i, HasLaw (ξ i) rade P)
  (hindepξ : iIndepFun ξ P) (hmeasξ : ∀ i, Measurable (ξ i))

include hlawξ in
set_option linter.unusedSectionVars false in
theorem integral_xi (i : ℕ × ℕ) : ∫ ω, ξ i ω ∂P = 0 := by
  rw [(hlawξ i).integral_eq]
  simpa using integral_id_rade

include hlawξ in
set_option linter.unusedSectionVars false in
theorem integral_xi_sq (i : ℕ × ℕ) : ∫ ω, ξ i ω ^ 2 ∂P = 1 := by
  have h : ∫ ω, ξ i ω ^ 2 ∂P = ∫ x, x ^ 2 ∂rade := by
    simpa [Function.comp_def] using (hlawξ i).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [h, integral_sq_rade]

include hlawξ in
set_option linter.unusedSectionVars false in
theorem integrable_xi_sq (i : ℕ × ℕ) : Integrable (fun ω => ξ i ω ^ 2) P :=
  (hlawξ i).integrable_fun_comp integrable_sq_rade

include hlawξ hindepξ hmeasξ in
theorem memLp_zE2 (g : Fin 2) : MemLp (zE2 ξ g) 2 P := by
  have hne : ((0:ℕ), (1:ℕ)) ≠ (0, g.val + 2) := by simp
  have hind : IndepFun (fun ω => ξ (0,1) ω ^ 2) (fun ω => ξ (0, g.val + 2) ω ^ 2) P :=
    (hindepξ.indepFun hne).comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
      (by fun_prop) (by fun_prop)
  have hint : Integrable (fun ω => ξ (0,1) ω ^ 2 * ξ (0, g.val + 2) ω ^ 2) P :=
    hind.integrable_mul (integrable_xi_sq hlawξ _) (integrable_xi_sq hlawξ _)
  refine (memLp_two_iff_integrable_sq ?_).2 ?_
  · exact (((hmeasξ _).mul (hmeasξ _)).aestronglyMeasurable)
  · exact hint.congr (Filter.Eventually.of_forall fun ω => by simp only [zE2]; ring)

include hlawξ hindepξ hmeasξ in
theorem integral_zE2 (g : Fin 2) : ∫ ω, zE2 ξ g ω ∂P = 0 := by
  have hne : ((0:ℕ), (1:ℕ)) ≠ (0, g.val + 2) := by simp
  have h := (hindepξ.indepFun hne).integral_mul_eq_mul_integral
    (hmeasξ _).aestronglyMeasurable (hmeasξ _).aestronglyMeasurable
  simp only [Pi.mul_apply] at h
  show ∫ ω, ξ (0,1) ω * ξ (0, g.val + 2) ω ∂P = 0
  rw [h, integral_xi hlawξ, zero_mul]

include hlawξ hindepξ hmeasξ in
theorem integral_zE2_sq (g : Fin 2) : ∫ ω, zE2 ξ g ω ^ 2 ∂P = 1 := by
  have hne : ((0:ℕ), (1:ℕ)) ≠ (0, g.val + 2) := by simp
  have hind : IndepFun (fun ω => ξ (0,1) ω ^ 2) (fun ω => ξ (0, g.val + 2) ω ^ 2) P :=
    (hindepξ.indepFun hne).comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
      (by fun_prop) (by fun_prop)
  have h := hind.integral_mul_eq_mul_integral
    (((hmeasξ (0,1)).pow_const 2).aestronglyMeasurable)
    (((hmeasξ (0, g.val + 2)).pow_const 2).aestronglyMeasurable)
  simp only [Pi.mul_apply] at h
  have hrw : ∫ ω, zE2 ξ g ω ^ 2 ∂P = ∫ ω, ξ (0,1) ω ^ 2 * ξ (0, g.val + 2) ω ^ 2 ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [zE2]; ring)
  rw [hrw, h, integral_xi_sq hlawξ, integral_xi_sq hlawξ, one_mul]

include hlawξ hindepξ hmeasξ in
/-- The two interaction terms are orthogonal: the shared factor contributes `𝔼[ψ²] = 1`, and
the unshared factor has mean zero. -/
theorem integral_zE2_mul (g g' : Fin 2) (hgg : g ≠ g') :
    ∫ ω, zE2 ξ g ω * zE2 ξ g' ω ∂P = 0 := by
  have hval : g.val ≠ g'.val := fun h => hgg (Fin.ext h)
  have h1 : ((0:ℕ), (1:ℕ)) ≠ (0, g'.val + 2) := by simp
  have h2 : ((0:ℕ), g.val + 2) ≠ (0, g'.val + 2) := by simp [hval]
  have hind : IndepFun (fun ω => ξ (0,1) ω ^ 2 * ξ (0, g.val + 2) ω)
      (ξ (0, g'.val + 2)) P := by
    have h := hindepξ.indepFun_prodMk hmeasξ (0,1) (0, g.val + 2) (0, g'.val + 2) h1 h2
    exact h.comp (φ := fun p : ℝ × ℝ => p.1 ^ 2 * p.2) (by fun_prop) measurable_id
  have h := hind.integral_mul_eq_mul_integral
    (((hmeasξ _).pow_const 2).mul (hmeasξ _)).aestronglyMeasurable
    (hmeasξ _).aestronglyMeasurable
  simp only [Pi.mul_apply] at h
  have hrw : ∫ ω, zE2 ξ g ω * zE2 ξ g' ω ∂P
      = ∫ ω, (ξ (0,1) ω ^ 2 * ξ (0, g.val + 2) ω) * ξ (0, g'.val + 2) ω ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [zE2]; ring)
  rw [hrw, h, integral_xi hlawξ, mul_zero]

set_option linter.unusedSectionVars false in
include hindepξ hmeasξ in
/-- Regime 2(c): the latent collection is independent of the cell-level disturbances. -/
theorem indepFun_zE2_err (g : Fin 2) {n : ℕ} (hn : 1 ≤ n) (o : Fin n) :
    IndepFun (zE2 ξ g) (errW ξ n o) P := by
  have h1 : ((0:ℕ), (1:ℕ)) ≠ (n, o.val) := by
    intro h; exact absurd (congrArg Prod.fst h) (by omega)
  have h2 : ((0:ℕ), g.val + 2) ≠ (n, o.val) := by
    intro h; exact absurd (congrArg Prod.fst h) (by omega)
  have h := hindepξ.indepFun_prodMk hmeasξ (0,1) (0, g.val + 2) (n, o.val) h1 h2
  exact h.comp (φ := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) measurable_id

end E2Law

section E2Design

variable {ξ : ℕ × ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem nuE2_apply (n : ℕ) (ω : Ω) (o : Fin n) :
    nuE2 ξ n ω o = (∑ _m : Fin 1, ξ (0,0) ω * dvec n o)
      + ((∑ g : Fin 2, zE2 ξ g ω * wE2 n g o) + ξ (n, o.val) ω) := by
  show ((∑ m, aaW ξ n m ω) + ((∑ g, zE2 ξ g ω • wE2 n g)
    + (WithLp.toLp 2 fun o => errW ξ n o ω))) o = _
  rw [PiLp.add_apply, euclideanSum_apply, PiLp.add_apply, euclideanSum_apply]
  rfl

omit [IsProbabilityMeasure P] in
theorem measurable_nuE2 (hmeasξ : ∀ i, Measurable (ξ i)) (n : ℕ) (o : Fin n) :
    Measurable fun ω => nuE2 ξ n ω o := by
  simp only [funext fun ω => nuE2_apply (ξ := ξ) n ω o]
  refine Measurable.add ?_ (Measurable.add ?_ (hmeasξ _))
  · exact Finset.measurable_sum _ fun m _ => (hmeasξ _).mul_const _
  · exact Finset.measurable_sum _ fun g _ =>
      (((hmeasξ _).mul (hmeasξ _)).mul_const _)

omit [IsProbabilityMeasure P] in
theorem measurable_bE2 (hmeasξ : ∀ i, Measurable (ξ i)) (β : EuclideanSpace ℝ (Fin 1)) (n : ℕ) :
    Measurable (bE2 ξ β n) := by
  have h : Measurable fun ω => score (⨆ m, feSpace n m) (Xmap n) (nuE2 ξ n ω) :=
    measurable_score _ _ fun o => measurable_nuE2 hmeasξ n o
  exact (h.const_smul (((n - 1 : ℕ) : ℝ))⁻¹).const_add β

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem isMFESlope_bE2 (β : EuclideanSpace ℝ (Fin 1)) {n : ℕ} (hn : 2 ≤ n) (ω : Ω) :
    IsMFESlope (⨆ m, feSpace n m) (Xmap n) (yE2 ξ β n ω) (bE2 ξ β n ω) := by
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine isMFESlope_of_gram_sub_eq_score (s := ∑ m, feW n m) (v := nuE2 ξ n ω) rfl
    (Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m (feW_mem n m)) ?_
  have hsub : bE2 ξ β n ω - β
      = (((n - 1 : ℕ) : ℝ))⁻¹ • score (⨆ m, feSpace n m) (Xmap n) (nuE2 ξ n ω) := by
    simp [bE2]
  rw [hsub, gram_witness, smul_smul, mul_inv_cancel₀ hn1, one_smul]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- On the witness design `S_n = n^{-1}[(n-1) + 8]` in direction `t`, so `S = 1 ≻ 0`. -/
theorem hSn_E2 (t : EuclideanSpace ℝ (Fin 1)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ((∑ g : Fin 2, ⟪score (⨆ m, feSpace n m) (Xmap n) (wE2 n g), t⟫ ^ 2 * (1:ℝ))
        + ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ 2 * (1:ℝ))) atTop
      (𝓝 (t ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ t))) := by
  rw [dotProduct_one_fin_one]
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ *
      ((∑ g : Fin 2, ⟪score (⨆ m, feSpace n m) (Xmap n) (wE2 n g), t⟫ ^ 2 * (1:ℝ))
        + ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ 2 * (1:ℝ))
      = ((n : ℝ)⁻¹ * (8 * (t 0) ^ 2)) + (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * (t 0) ^ 2 := by
    filter_upwards [eventually_ge_atTop 5] with n hn
    have hg : ∀ g : Fin 2, ⟪score (⨆ m, feSpace n m) (Xmap n) (wE2 n g), t⟫ ^ 2 * (1:ℝ)
        = 4 * (t 0) ^ 2 := fun g => by
      rw [inner_score_wE2 hn g]; ring
    rw [Finset.sum_congr rfl fun g _ => hg g, sum_inner_sq n t (p := 2) (by norm_num)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, div_eq_mul_inv]
    push_cast
    ring
  refine Tendsto.congr' (hev.mono fun n h => h.symm) ?_
  have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (8 * (t 0) ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (8 * (t 0) ^ 2)
  simpa using h1.add (tendsto_pred_div.mul_const ((t 0) ^ 2))

end E2Design

/-- The Regime-2 variance identity and consistency hold on a model with a genuine Regime-2
disturbance, and the Regime-1 identity fails there. -/
theorem clt_b_regime2_witness (β : EuclideanSpace ℝ (Fin 1)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (Xmap n))
          (Xmap n) (yE2 ξ β n ω) (bE2 ξ β n ω))
    ∧ TendstoInMeasure P (bE2 ξ β) atTop (fun _ => β)
    ∧ (∀ᶠ n : ℕ in atTop, ∀ t : EuclideanSpace ℝ (Fin 1),
        Var[fun ω => ⟪score (⨆ m, feSpace n m) (Xmap n) (nuE2 ξ n ω), t⟫; P]
          = ((n - 1 : ℕ) : ℝ) * (t 0) ^ 2 + 8 * (t 0) ^ 2)
    ∧ (∀ᶠ n : ℕ in atTop, ∀ t : EuclideanSpace ℝ (Fin 1), t 0 ≠ 0 →
        Var[fun ω => ⟪score (⨆ m, feSpace n m) (Xmap n) (nuE2 ξ n ω), t⟫; P]
          ≠ ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (Xmap n) o, t⟫ ^ 2 * (1:ℝ)) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hmeas : ∀ (n : ℕ) (o : Fin n), Measurable (errW ξ n o) := fun n o => hmeasξ _
  have hindep : ∀ n : ℕ, iIndepFun (errW ξ n) P := fun n =>
    hindepξ.precomp (g := fun o : Fin n => (n, o.val))
      (fun a b hab => Fin.val_injective (congrArg Prod.snd hab))
  have hmean : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ∂P = 0 := fun n o =>
    integral_xi hlawξ (n, o.val)
  have hL2 : ∀ (n : ℕ) (o : Fin n), MemLp (errW ξ n o) 2 P := fun n o =>
    (hlawξ (n, o.val)).memLp memLp_id_rade
  have hvar : ∀ (n : ℕ) (o : Fin n), Var[errW ξ n o; P] = 1 := by
    intro n o
    show Var[ξ (n, o.val); P] = 1
    rw [(hlawξ (n, o.val)).variance_eq, variance_id_rade]
  have hZL2 : ∀ (n : ℕ) (g : Fin 2), MemLp (zE2 ξ g) 2 P := fun _ g =>
    memLp_zE2 hlawξ hindepξ hmeasξ g
  have hZmean : ∀ (n : ℕ) (g : Fin 2), ∫ ω, zE2 ξ g ω ∂P = 0 := fun _ g =>
    integral_zE2 hlawξ hindepξ hmeasξ g
  have hZsq : ∀ (n : ℕ) (g : Fin 2), ∫ ω, zE2 ξ g ω ^ 2 ∂P = 1 := fun _ g =>
    integral_zE2_sq hlawξ hindepξ hmeasξ g
  have hZorth : ∀ (n : ℕ), ∀ g g' : Fin 2, g ≠ g' → ∫ ω, zE2 ξ g ω * zE2 ξ g' ω ∂P = 0 :=
    fun _ g g' h => integral_zE2_mul hlawξ hindepξ hmeasξ g g' h
  have hZe : ∀ (n : ℕ), ∀ (g : Fin 2) (o : Fin n), IndepFun (zE2 ξ g) (errW ξ n o) P := by
    intro n g o
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact o.elim0
    · exact indepFun_zE2_err hindepξ hmeasξ g hn o
  have hMFE : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsMFESlope (⨆ m, feSpace n m) (Xmap n) (yE2 ξ β n ω) (bE2 ξ β n ω) := by
    filter_upwards [eventually_ge_atTop 2] with n hn ω
    exact isMFESlope_bE2 β hn ω
  have hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, feSpace n m) (Xmap n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact identified_witness hn
  have hJM : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (Xmap n))
        (Xmap n) (yE2 ξ β n ω) (bE2 ξ β n ω) := by
    filter_upwards [hid, hMFE] with n hidn hMFEn ω
    exact (jm_equiv hidn (dvec_mem n) _ _).mpr (hMFEn ω)
  have hvarE2 : ∀ᶠ n : ℕ in atTop, ∀ t : EuclideanSpace ℝ (Fin 1),
      Var[fun ω => ⟪score (⨆ m, feSpace n m) (Xmap n) (nuE2 ξ n ω), t⟫; P]
        = ((n - 1 : ℕ) : ℝ) * (t 0) ^ 2 + 8 * (t 0) ^ 2 := by
    filter_upwards [eventually_ge_atTop 5] with n hn t
    rw [variance_score_eq_E2 (feSpace n) (Xmap n) (aaW ξ n) (aaW_mem ξ n) (wE2 n)
      (fun g => zE2 ξ g) (fun _ => (1:ℝ)) (errW ξ n) (fun _ => (1:ℝ)) (nuE2 ξ n)
      (fun ω => rfl) (hZL2 n) (hZmean n) (hZsq n) (hZorth n) (hindep n) (hL2 n) (hmean n)
      (hvar n) (hZe n) t]
    have hg : ∀ g : Fin 2, ⟪score (⨆ m, feSpace n m) (Xmap n) (wE2 n g), t⟫ ^ 2 * (1:ℝ)
        = 4 * (t 0) ^ 2 := fun g => by rw [inner_score_wE2 hn g]; ring
    rw [Finset.sum_congr rfl fun g _ => hg g, sum_inner_sq n t (p := 2) (by norm_num)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  refine ⟨Ω, mΩ, P, hprobξ, ξ, hJM, ?_, hvarE2, ?_⟩
  · exact (clt_b_consistency (O := fun n => Fin n) (G := fun _ => Fin 2) feSpace Xmap β
      feW (fun n m => feW_mem n m) (nuE2 ξ) (yE2 ξ β) (fun n ω => rfl) (aaW ξ)
      (fun n m ω => aaW_mem ξ n m ω) (fun n => wE2 n) (fun _ g => zE2 ξ g)
      (fun _ _ => (1:ℝ)) (errW ξ) (fun _ _ => (1:ℝ)) (fun n ω => rfl) hZL2 hZmean hZsq hZorth
      hindep hL2 hmean hvar hZe 1 hSn_E2 Aop
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) hAsolve_witness hAlim_witness
      dvec dvec_mem hid (bE2 ξ β) (bE2 ξ β)
      (fun n => (measurable_bE2 hmeasξ β n).aemeasurable)
      (fun n => (measurable_bE2 hmeasξ β n).aemeasurable) hJM hMFE).1
  · filter_upwards [hvarE2, eventually_ge_atTop 5] with n hvn hn t ht
    rw [hvn t, sum_inner_sq n t (p := 2) (by norm_num)]
    intro hcon
    have h8 : (8:ℝ) * (t 0) ^ 2 = 0 := by linarith [hcon]
    exact ht (by nlinarith [sq_nonneg (t 0), h8])

end Witness

/-! ### The directional limit from the truncation argument

`scalar_clt_of_truncation` composes the martingale CLT at each truncation level `L`
(`CLTMartingale.Var.tendsto_charFun_degenSum_of_concentration`) with the truncation limit
`L → ∞` (`CLTMartingale.Trunc.tendstoInDistribution_of_l2_approx`), yielding the directional
limit `n^{-1/2}c'X̃'ν ⟶^d N(0,c'Sc)` that `clt_b` takes as `hdir`. The remaining hypotheses are
`halg`, `hstep4` (`|s_n²(L)/n - c'S_nc| ≤ δ(L)`), `hstep5` (the `L²` truncation gap), `hsecond`
and `hnorm`. -/

section Compose

open DegenerateSum CLTMartingale CLTMartingale.Var StatLean.TimeSeries

/-- The directional limit law from the truncation data. At each level `L`, `g L n` is the
truncated kernel, `cf L n` its coefficients divided by `s_n(L)`, `arr L n γ` the matricized
coefficient array and `sc L n = s_n(L)/√n`; the latent variables, their ordering, the support and
the site model do not depend on `L`. -/
theorem scalar_clt_of_truncation
    {ι : Type*} [Fintype ι] [Nonempty ι] {T : Type*} [Fintype T] [DecidableEq T]
    {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {S : ℕ → Γ → Type*} [∀ n γ, Fintype (S n γ)]
    {Ix : ℕ → Type*} [∀ n, Fintype (Ix n)] {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site K N → Ω → ℝ}
    {sites : ∀ (n : ℕ) (γ : Γ), S n γ → Finset (Site K N)}
    {rIdx : ∀ _n : ℕ, Γ → Site K N → R}
    {arr : ∀ (_L n : ℕ) (γ : Γ), S n γ → Ix n → ℝ}
    {lev : Γ → Finset K} {pt : ∀ (n : ℕ) (γ : Γ), S n γ → K → Site K N}
    {lam : ℕ → Γ → ℝ} {cellc cutmax totmax : ℕ → ℕ → ℝ}
    {coord : ℕ → T → ι → Site K N} {g : ℕ → ℕ → (ι → ℝ) → ℝ} {cf : ℕ → ℕ → T → ℝ}
    {stp : ℕ → Site K N → ℕ} {kk : ℕ → ℕ}
    {xi : ℕ → Ω → ℝ} {sc : ℕ → ℕ → ℝ} {del : ℕ → ℝ} {sig2 : ℝ}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hg : ∀ L n, Measurable (g L n))
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdeg : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : S n q), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q') (a b : K),
      pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinj : ∀ (n : ℕ) (q : Γ) (x y : S n q), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q'), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ L, ∑ γ, lam L γ ^ 2 ≤ 1)
    (hcut : ∀ (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr L n γ) * (Matrix.of (arr L n γ))ᵀ) ≤ cutmax L n)
    (hcutA : ∀ (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr L n q)))ᵀ) ≤ cutmax L n)
    (htot : ∀ (L n : ℕ) (γ : Γ), rectFrobSq (arr L n γ) ≤ totmax L n)
    (hnorm : ∀ L n, (∑ γ, lam L γ ^ 2 * rectFrobSq (arr L n γ)) + cellc L n = 1)
    (halg : ∀ L n,
      mdsCondVariance kk (rowDiff P U coord (g L) (cf L) stp kk) (rowSigma U stp kk) P n
        =ᵐ[P] fun ω =>
          quadForm (U n) ψ (sites n) (rIdx n) (arr L n) tag (lam L) ω + cellc L n)
    (hrate : ∀ L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card K)
          * (cutmax L n * totmax L n)) atTop (𝓝 0))
    (hlind : ∀ (L : ℕ) (ε : ℝ), 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P U coord (g L) (cf L) stp kk n i ω|},
        (rowDiff P U coord (g L) (cf L) stp kk n i ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsig2 : 0 < sig2) (hxi : ∀ n, MemLp (xi n) 2 P)
    (hTr : ∀ L n, MemLp (degenSum (U n) (coord n) (g L n) (cf L n)) 2 P)
    (hsc : ∀ L n, 0 ≤ sc L n) (hdel : Tendsto del atTop (𝓝 0))
    (hsecond : ∀ L n, ∫ ω, degenSum (U n) (coord n) (g L n) (cf L n) ω ^ 2 ∂P ≤ 1)
    (hstep4 : ∀ L, ∀ᶠ n in atTop, |sc L n ^ 2 - sig2| ≤ del L)
    (hstep5 : ∀ L, ∀ᶠ n in atTop,
      ∫ ω, (xi n ω - sc L n * degenSum (U n) (coord n) (g L n) (cf L n) ω) ^ 2 ∂P ≤ del L) :
    TendstoInDistribution xi atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal sig2)) := by
  refine Trunc.tendstoInDistribution_of_l2_approx hsig2 hxi hTr hsc hdel hsecond ?_ hstep4 hstep5
  intro L u
  exact tendsto_charFun_degenSum_of_concentration (S := S) (Ix := Ix) (tag := tag)
    (arr := arr L) (lev := lev) (pt := pt) (lam := lam L) (cellc := cellc L)
    (cutmax := cutmax L) (totmax := totmax L)
    hbs (hg L) (hsq L) (hdeg L) hN hsite hptc hptf hpos hinj hsep (hlam L) (hcut L) (hcutA L)
    (htot L) (hnorm L) (halg L) (hrate L) (hlind L) u

end Compose

/-! ### Part (b) from the truncation data

`clt_b_of_truncation` is `clt_b` with `hdir` supplied by `scalar_clt_of_truncation` in each
direction. Of the truncation objects, only `cf`, `arr`, `lam`, `cellc`, `cutmax`, `totmax`, `sc`
and `del` depend on the direction; the latent array, support, kernels, ordering, step count and
site model do not. `hxi` requires the statistic `n^{-1/2}c'X̃'ν` to be in `L²`. -/

section ComposeB

open DegenerateSum CLTMartingale CLTMartingale.Var StatLean.TimeSeries

/-- **Theorem 4(b)** with the directional limit derived from the truncation data. -/
theorem clt_b_of_truncation {K : ℕ}
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (hnumeas : ∀ n o, Measurable fun ω => nu n ω o)
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    -- the truncation model, the direction-free part
    {ι : Type*} [Fintype ι] [Nonempty ι] {T : Type*} [Fintype T] [DecidableEq T]
    {Kd : Type*} [Fintype Kd] [DecidableEq Kd] {N : Kd → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {S : ℕ → Γ → Type*} [∀ n γ, Fintype (S n γ)]
    {Ix : ℕ → Type*} [∀ n, Fintype (Ix n)] {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site Kd N → Ω → ℝ}
    {sites : ∀ (n : ℕ) (γ : Γ), S n γ → Finset (Site Kd N)}
    {rIdx : ∀ _n : ℕ, Γ → Site Kd N → R}
    {lev : Γ → Finset Kd} {pt : ∀ (n : ℕ) (γ : Γ), S n γ → Kd → Site Kd N}
    {coord : ℕ → T → ι → Site Kd N} {g : ℕ → ℕ → (ι → ℝ) → ℝ}
    {stp : ℕ → Site Kd N → ℕ} {kk : ℕ → ℕ}
    -- the direction-dependent part
    {arr : ∀ (_c : EuclideanSpace ℝ (Fin K)) (_L n : ℕ) (γ : Γ), S n γ → Ix n → ℝ}
    {lam : EuclideanSpace ℝ (Fin K) → ℕ → Γ → ℝ}
    {cellc cutmax totmax sc : EuclideanSpace ℝ (Fin K) → ℕ → ℕ → ℝ}
    {cf : EuclideanSpace ℝ (Fin K) → ℕ → ℕ → T → ℝ}
    {del : EuclideanSpace ℝ (Fin K) → ℕ → ℝ}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hg : ∀ L n, Measurable (g L n))
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdegk : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : S n q), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q') (a b : Kd),
      pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinjs : ∀ (n : ℕ) (q : Γ) (x y : S n q), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q'), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ c L, ∑ γ, lam c L γ ^ 2 ≤ 1)
    (hcut : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr c L n γ) * (Matrix.of (arr c L n γ))ᵀ) ≤ cutmax c L n)
    (hcutA : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr c L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr c L n q)))ᵀ) ≤ cutmax c L n)
    (htot : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (γ : Γ),
      rectFrobSq (arr c L n γ) ≤ totmax c L n)
    (hnorm : ∀ c L n, (∑ γ, lam c L γ ^ 2 * rectFrobSq (arr c L n γ)) + cellc c L n = 1)
    (halg : ∀ c L n,
      mdsCondVariance kk (rowDiff P U coord (g L) (cf c L) stp kk) (rowSigma U stp kk) P n
        =ᵐ[P] fun ω =>
          quadForm (U n) ψ (sites n) (rIdx n) (arr c L n) tag (lam c L) ω + cellc c L n)
    (hrate : ∀ c L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card Kd)
          * (cutmax c L n * totmax c L n)) atTop (𝓝 0))
    (hlind : ∀ (c : EuclideanSpace ℝ (Fin K)) (L : ℕ) (ε : ℝ), 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P U coord (g L) (cf c L) stp kk n i ω|},
        (rowDiff P U coord (g L) (cf c L) stp kk n i ω) ^ 2 ∂P) atTop (𝓝 0))
    (hxi : ∀ (c : EuclideanSpace ℝ (Fin K)) (n : ℕ),
      MemLp (fun ω => (Real.sqrt n)⁻¹ * ⟪score (⨆ m, Sm n m) (Xm n) (nu n ω), c⟫) 2 P)
    (hTr : ∀ c L n, MemLp (degenSum (U n) (coord n) (g L n) (cf c L n)) 2 P)
    (hsc : ∀ c L n, 0 ≤ sc c L n) (hdel : ∀ c, Tendsto (del c) atTop (𝓝 0))
    (hsecond : ∀ c L n, ∫ ω, degenSum (U n) (coord n) (g L n) (cf c L n) ω ^ 2 ∂P ≤ 1)
    (hstep4 : ∀ c L, ∀ᶠ (n : ℕ) in atTop, |sc c L n ^ 2 - c ⬝ᵥ (Smat *ᵥ c)| ≤ del c L)
    (hstep5 : ∀ c L, ∀ᶠ (n : ℕ) in atTop,
      ∫ ω, ((Real.sqrt n)⁻¹ * ⟪score (⨆ m, Sm n m) (Xm n) (nu n ω), c⟫
        - sc c L n * degenSum (U n) (coord n) (g L n) (cf c L n) ω) ^ 2 ∂P ≤ del c L)
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (ιv : ∀ n, EuclideanSpace ℝ (O n)) (hι : ∀ n, ιv n ∈ ⨆ m, Sm n m)
    (hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, Sm n m) (Xm n))
    (bJM bMFE : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbJMmeas : ∀ n, AEMeasurable (bJM n) P) (hbMFEmeas : ∀ n, AEMeasurable (bMFE n) P)
    (hbJM : ∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (ιv n) (⨆ m, Sm n m) (Xm n)) (Xm n)
      (yv n ω) (bJM n ω))
    (hbMFE : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (bMFE n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bJM n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat)
      ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bMFE n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine clt_b Sm Xm β fe hfe nu yv hmodel hnumeas Smat hSpd ?_ A Hinv hAsolve hAlim
    ιv hι hid bJM bMFE hbJMmeas hbMFEmeas hbJM hbMFE
  intro c hc
  exact scalar_clt_of_truncation (S := S) (Ix := Ix) (tag := tag) (arr := arr c)
    (lev := lev) (pt := pt) (lam := lam c) (cellc := cellc c) (cutmax := cutmax c)
    (totmax := totmax c) (cf := cf c) (sc := sc c) (del := del c)
    hbs hg hsq hdegk hN hsite hptc hptf hpos hinjs hsep (hlam c) (hcut c) (hcutA c) (htot c)
    (hnorm c) (halg c) (hrate c) (hlind c)
    (dotProduct_mulVec_pos_of_posDef hSpd hc) (hxi c) (hTr c) (hsc c) (hdel c) (hsecond c)
    (hstep4 c) (hstep5 c)

end ComposeB

/-! ### The Lindeberg condition from fourth moments

The conditional Lindeberg condition `hlind` is reduced to `s_n(L)^{-4}∑_κ 𝔼[D_κ⁴] → 0`
(`lindeberg_of_tendsto_sum_pow_four`), and each `𝔼[D_κ⁴]` is bounded by Lemma SM.C.4 (Fourth
moments of bounded multilinear forms), extended from a product index set to an irregular support
`𝒯_e` (`integral_pow_four_irregular_le`); the extension requires the index map `idx` to be
injective. `lindeberg_rowDiff_of_multilinear` assembles these under the design condition
`hdesign`, `(3B_0⁴)^j∑_i(∑_{t ∈ R_i}c_t²)² → 0`. -/

section Lindeberg

open DegenerateSum CLTMartingale

omit [IsProbabilityMeasure P] in
/-- `∫_{|X| ≥ ε}X² ≤ ε^{-2}∫X⁴`. -/
theorem setIntegral_sq_le_integral_pow_four {X : Ω → ℝ} (hX : Measurable X) {ε : ℝ} (hε : 0 < ε)
    (hint : Integrable (fun ω => X ω ^ 4) P) :
    ∫ ω in {ω | ε ≤ |X ω|}, X ω ^ 2 ∂P ≤ (ε ^ 2)⁻¹ * ∫ ω, X ω ^ 4 ∂P := by
  have hS : MeasurableSet {ω | ε ≤ |X ω|} := measurableSet_le measurable_const hX.abs
  have hpos : (0 : ℝ) < ε ^ 2 := by positivity
  have hgi : Integrable (fun ω => (ε ^ 2)⁻¹ * X ω ^ 4) (P.restrict {ω | ε ≤ |X ω|}) :=
    (hint.restrict).const_mul _
  have hstep : ∫ ω in {ω | ε ≤ |X ω|}, X ω ^ 2 ∂P
      ≤ ∫ ω in {ω | ε ≤ |X ω|}, (ε ^ 2)⁻¹ * X ω ^ 4 ∂P := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hgi ?_
    filter_upwards [ae_restrict_mem hS] with ω hω
    have h1 : ε ≤ |X ω| := hω
    have hεx : ε ^ 2 ≤ X ω ^ 2 := by
      have h2 : |X ω| ^ 2 = X ω ^ 2 := sq_abs _
      nlinarith [abs_nonneg (X ω)]
    have key : ε ^ 2 * X ω ^ 2 ≤ X ω ^ 4 := by nlinarith [sq_nonneg (X ω)]
    calc X ω ^ 2 = (ε ^ 2)⁻¹ * (ε ^ 2 * X ω ^ 2) := by field_simp
      _ ≤ (ε ^ 2)⁻¹ * X ω ^ 4 := mul_le_mul_of_nonneg_left key (by positivity)
  refine hstep.trans ?_
  rw [← integral_const_mul]
  refine setIntegral_le_integral (hint.const_mul _) ?_
  filter_upwards with ω
  positivity

omit [IsProbabilityMeasure P] in
/-- The fourth-moment sufficient condition for the conditional Lindeberg condition of a
triangular array, in the form taken by `StatLean.TimeSeries.mds_clt`. -/
theorem lindeberg_of_tendsto_sum_pow_four {kk : ℕ → ℕ} {X : (n : ℕ) → Fin (kk n) → Ω → ℝ}
    (hX : ∀ n i, Measurable (X n i))
    (hint : ∀ n i, Integrable (fun ω => X n i ω ^ 4) P)
    (h4 : Tendsto (fun n => ∑ i, ∫ ω, X n i ω ^ 4 ∂P) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
  intro ε hε
  have hpos : (0 : ℝ) < ε ^ 2 := by positivity
  refine squeeze_zero (g := fun n => (ε ^ 2)⁻¹ * ∑ i, ∫ ω, X n i ω ^ 4 ∂P)
    (fun n => ?_) (fun n => ?_) ?_
  · exact Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      setIntegral_sq_le_integral_pow_four (hX n i) hε (hint n i)
  · simpa using h4.const_mul ((ε ^ 2)⁻¹)

/-- Lemma SM.C.4 on an irregular support: for a `Finset` of sub-tuples mapped injectively into
the product index set by `idx`, the fourth-moment bound holds with the same constant `(3B⁴)^j`. -/
theorem integral_pow_four_irregular_le {j : ℕ} {I : Fin j → Type*}
    [∀ k, Fintype (I k)] (ξ : ∀ k : Fin j, I k → Ω → ℝ) {B : ℝ}
    (hindep : iIndepFun (fun p : Σ k : Fin j, I k => ξ p.1 p.2) P)
    (hmeas : ∀ (k : Fin j) (i : I k), Measurable (ξ k i))
    (hmean : ∀ (k : Fin j) (i : I k), ∫ ω, ξ k i ω ∂P = 0)
    (hbdd : ∀ (k : Fin j) (i : I k), ∀ᵐ ω ∂P, |ξ k i ω| ≤ B)
    {T : Type*} [Fintype T] [DecidableEq T] {idx : T → ∀ k, I k}
    (hinj : Function.Injective idx) (cc : T → ℝ) (Rst : Finset T) :
    ∫ ω, (∑ t ∈ Rst, cc t * ∏ k, ξ k (idx t k) ω) ^ 4 ∂P
      ≤ (3 * B ^ 4) ^ j * (∑ t ∈ Rst, cc t ^ 2) ^ 2 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : (∀ k, I k) → ℝ, a = fun s => ∑ t ∈ Rst with idx t = s, cc t := ⟨_, rfl⟩
  have hfib : ∀ s : (∀ k, I k), (Rst.filter fun t => idx t = s) = ∅ ∨
      ∃ x, (Rst.filter fun t => idx t = s) = {x} := by
    intro s
    rcases Finset.eq_empty_or_nonempty (Rst.filter fun t => idx t = s) with h | ⟨x, hx⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, fun y hy => ?_⟩⟩
      exact hinj ((Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hx).2.symm)
  have h1 : ∀ ω, ∑ s ∈ Fintype.piFinset (fun k => (Finset.univ : Finset (I k))),
      a s * ∏ k, ξ k (s k) ω = ∑ t ∈ Rst, cc t * ∏ k, ξ k (idx t k) ω := by
    intro ω
    rw [Fintype.piFinset_univ,
      ← Finset.sum_fiberwise Rst idx (fun t => cc t * ∏ k, ξ k (idx t k) ω)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ha, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_filter.mp ht).2]
  have h2 : ∑ s ∈ Fintype.piFinset (fun k => (Finset.univ : Finset (I k))), a s ^ 2
      = ∑ t ∈ Rst, cc t ^ 2 := by
    rw [Fintype.piFinset_univ, ← Finset.sum_fiberwise Rst idx (fun t => cc t ^ 2)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases hfib s with h | ⟨x, h⟩
    · rw [ha]; simp [h]
    · rw [ha]; simp [h]
  have hmain := Multilinear.integral_pow_four_multilinear_le (μ := P) (B := B) j I ξ a
    (fun _ => Finset.univ) hindep hmeas hmean hbdd
  rw [h2] at hmain
  refine le_trans (le_of_eq ?_) hmain
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [h1 ω])

/-- The conditional Lindeberg condition `hlind` of `CLTMartingale.tendsto_charFun_degenSum`,
from the fourth-moment bound and the design condition `hdesign`. -/
theorem lindeberg_rowDiff_of_multilinear
    {V ι T : Type*} [Fintype ι] [Fintype T] [DecidableEq T]
    {U : ℕ → V → Ω → ℝ} {coord : ℕ → T → ι → V} {g : ℕ → (ι → ℝ) → ℝ}
    {cf : ℕ → T → ℝ} {stp : ℕ → V → ℕ} {kk : ℕ → ℕ}
    {j : ℕ} {I : ℕ → Fin j → Type*} [∀ n k, Fintype (I n k)]
    {ξ : ∀ (n : ℕ) (k : Fin j), I n k → Ω → ℝ} {B : ℝ}
    {idx : ∀ _n : ℕ, T → ∀ k : Fin j, I _n k}
    (hU : ∀ n v, Measurable (U n v)) (hindepU : ∀ n, iIndepFun (U n) P)
    (hg : ∀ n, Measurable (g n))
    (hint : ∀ n t, Integrable (degenTerm (U n) (coord n) (g n) t) P)
    (hdeg : ∀ (n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hprod : ∀ n t ω, degenTerm (U n) (coord n) (g n) t ω = ∏ k, ξ n k (idx n t k) ω)
    (hindep : ∀ n, iIndepFun (fun p : Σ k : Fin j, I n k => ξ n p.1 p.2) P)
    (hmeas : ∀ n k i, Measurable (ξ n k i))
    (hmean : ∀ n k i, ∫ ω, ξ n k i ω ∂P = 0)
    (hbdd : ∀ n k i, ∀ᵐ ω ∂P, |ξ n k i ω| ≤ B)
    (hinj : ∀ n, Function.Injective (idx n))
    (hmeasrow : ∀ n i, Measurable (rowDiff P U coord g cf stp kk n i))
    (hint4 : ∀ n i, Integrable (fun ω => rowDiff P U coord g cf stp kk n i ω ^ 4) P)
    (hdesign : Tendsto (fun n => (3 * B ^ 4) ^ j *
        ∑ i : Fin (kk n),
          (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf n t ^ 2) ^ 2) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P U coord g cf stp kk n i ω|},
        (rowDiff P U coord g cf stp kk n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
  refine lindeberg_of_tendsto_sum_pow_four hmeasrow hint4 ?_
  refine squeeze_zero (g := fun n => (3 * B ^ 4) ^ j *
      ∑ i : Fin (kk n),
        (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf n t ^ 2) ^ 2)
    (fun n => ?_) (fun n => ?_) hdesign
  · exact Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by positivity
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hae : ∀ᵐ ω ∂P, rowDiff P U coord g cf stp kk n i ω ^ 4
        = (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ),
            cf n t * ∏ k, ξ n k (idx n t k) ω) ^ 4 := by
      filter_upwards [degenDiff_eq_sum_completedAt (μ := P) (U := U n) (coord := coord n)
        (g := g n) (c := cf n) (step := stp n) (hU n) (hindepU n) (hg n) (hint n) (hdeg n)
        (i : ℕ)] with ω hω
      have h : rowDiff P U coord g cf stp kk n i ω
          = ∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf n t * ∏ k, ξ n k (idx n t k) ω := by
        rw [show rowDiff P U coord g cf stp kk n i ω
          = degenDiff P (U n) (coord n) (g n) (cf n) (stp n) (i : ℕ) ω from rfl, hω]
        exact Finset.sum_congr rfl fun t _ => by rw [hprod n t ω]
      rw [h]
    rw [integral_congr_ae hae]
    exact integral_pow_four_irregular_le (ξ n) (hindep n) (hmeas n) (hmean n) (hbdd n)
      (hinj n) (cf n) (completedAt (coord n) (stp n) (i : ℕ))

end Lindeberg

/-! ### A completely degenerate kernel

`orth_witness` exhibits a completely degenerate kernel on the Rademacher array and derives the
orthogonality of distinct interaction terms through `Orth.integral_degenTerm_mul_eq_zero_of_or`.
The level is `Fin 2`, the sub-tuples are `coord t = ![(0,1),(0,t+2)]` and `g x = x₀x₁`, so the
kernel term is `zE2`. The two cells share `ξ_{(0,1)}`, and `𝔼[h(U_t)²] = 1`. -/

namespace Witness

open DegenerateSum

/-- The coordinate map: coordinate `0` of both sub-tuples carries the shared variable
`ξ_{(0,1)}`, coordinate `1` a private one. -/
def e2coord (t : Fin 2) : Fin 2 → ℕ × ℕ := ![(0, 1), (0, t.val + 2)]

/-- The rank-one kernel `h(u,v) = uv` on `Fin 2 → ℝ`. -/
def e2ker : (Fin 2 → ℝ) → ℝ := fun x => x 0 * x 1

theorem e2coord_zero (t : Fin 2) : e2coord t 0 = (0, 1) := rfl

theorem e2coord_one (t : Fin 2) : e2coord t 1 = (0, t.val + 2) := rfl

theorem fin_two_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k; decide

theorem e2coord_ne (t : Fin 2) : e2coord t 0 ≠ e2coord t 1 := by
  rw [e2coord_zero, e2coord_one]
  intro h
  exact absurd (congrArg Prod.snd h) (by omega)

theorem measurable_e2ker : Measurable e2ker := by
  unfold e2ker; fun_prop

omit [MeasurableSpace Ω] in
/-- The kernel term is `zE2`. -/
theorem degenTerm_e2 (ξ : ℕ × ℕ → Ω → ℝ) (t : Fin 2) :
    degenTerm ξ e2coord e2ker t = zE2 ξ t := rfl

omit [MeasurableSpace Ω] in
theorem degenTerm_e2_mul (ξ : ℕ × ℕ → Ω → ℝ) (t : Fin 2) :
    degenTerm ξ e2coord e2ker t = ξ (e2coord t 0) * ξ (e2coord t 1) := rfl

omit [MeasurableSpace Ω] in
/-- The kernel term is a product over the level's coordinates. -/
theorem degenTerm_e2_prod (ξ : ℕ × ℕ → Ω → ℝ) (t : Fin 2) (ω : Ω) :
    degenTerm ξ e2coord e2ker t ω = ∏ k : Fin 2, ξ (e2coord t k) ω := by
  rw [Fin.prod_univ_two]
  rfl

section Deg

variable {ξ : ℕ × ℕ → Ω → ℝ}

/-- The pull-out step at an abstract sub-σ-field. -/
theorem condExp_mul_eq_zero_of_condExp_eq_zero {α : Type*} {m0 m : MeasurableSpace α}
    {Q : @Measure α m0} {f g : α → ℝ}
    (hf : StronglyMeasurable[m] f) (hfg : Integrable (f * g) Q) (hg : Integrable g Q)
    (hg0 : Q[g | m] =ᵐ[Q] 0) : Q[f * g | m] =ᵐ[Q] 0 := by
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := Q) hf hfg hg
  filter_upwards [hpull, hg0] with ω h1 h2
  rw [h1]
  simp only [Pi.mul_apply, h2, mul_zero, Pi.zero_apply]

/-- `E[f | m₂] = E[f] = 0` for an `m₁`-measurable `f` independent of `m₂`. -/
theorem condExp_eq_zero_of_indep {α : Type*} {m0 m1 m2 : MeasurableSpace α}
    {Q : @Measure α m0} [IsFiniteMeasure Q] (h1 : m1 ≤ m0) (h2 : m2 ≤ m0) {f : α → ℝ}
    (hf : StronglyMeasurable[m1] f) (hindep : Indep m1 m2 Q) (hmean : ∫ ω, f ω ∂Q = 0) :
    Q[f | m2] =ᵐ[Q] 0 := by
  have hsf : SigmaFinite (Q.trim h2) := by
    have : IsFiniteMeasure (Q.trim h2) := isFiniteMeasure_trim h2
    infer_instance
  refine (condExp_indep_eq h1 h2 hf hindep).trans ?_
  filter_upwards with _
  exact hmean

/-- `E[ξ_b | σ(ξ_v : v ≠ b)] = E[ξ_b] = 0`. -/
theorem condExp_xi_compl_eq_zero (hmeasξ : ∀ v, Measurable (ξ v)) (hindepξ : iIndepFun ξ P)
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) (b : ℕ × ℕ) :
    P[ξ b | latentSigma ξ ({b}ᶜ : Set (ℕ × ℕ))] =ᵐ[P] 0 :=
  condExp_eq_zero_of_indep (latentSigma_le hmeasξ _) (latentSigma_le hmeasξ _)
    (measurable_latentSigma ξ (S := ({b} : Set (ℕ × ℕ))) rfl).stronglyMeasurable
    (latentSigma_indep hmeasξ hindepξ (S := ({b} : Set (ℕ × ℕ)))
      (S' := ({b}ᶜ : Set (ℕ × ℕ))) disjoint_compl_right) (integral_xi hlawξ b)

/-- `E[ξ_aξ_b | σ(ξ_v : v ≠ b)] = 0` for `a ≠ b`. -/
theorem condExp_mul_compl_eq_zero (hmeasξ : ∀ v, Measurable (ξ v)) (hindepξ : iIndepFun ξ P)
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) {a b : ℕ × ℕ} (hab : a ≠ b) :
    P[ξ a * ξ b | latentSigma ξ ({b}ᶜ : Set (ℕ × ℕ))] =ᵐ[P] 0 :=
  condExp_mul_eq_zero_of_condExp_eq_zero
    (measurable_latentSigma ξ (v := a) hab).stronglyMeasurable
    (((hlawξ a).memLp memLp_id_rade).integrable_mul ((hlawξ b).memLp memLp_id_rade))
    (((hlawξ b).memLp memLp_id_rade).integrable one_le_two)
    (condExp_xi_compl_eq_zero hmeasξ hindepξ hlawξ b)

/-- Complete degeneracy of `h(u,v) = uv` on independent mean-zero signs. -/
theorem hdeg_e2 (hmeasξ : ∀ v, Measurable (ξ v)) (hindepξ : iIndepFun ξ P)
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) (t : Fin 2) (e' : Set (Fin 2)) (hne : e' ≠ Set.univ) :
    P[degenTerm ξ e2coord e2ker t | latentSigma ξ (e2coord t '' e')] =ᵐ[P] 0 := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, k ∉ e' := by
    by_contra h
    exact hne (Set.eq_univ_of_forall fun k => not_not.mp fun hk => h (Exists.intro k hk))
  -- the term vanishes conditionally on the complement of the absent coordinate's variable
  have hcompl : P[degenTerm ξ e2coord e2ker t | latentSigma ξ {e2coord t k}ᶜ] =ᵐ[P] 0 := by
    rcases fin_two_cases k with rfl | rfl
    · have h := condExp_mul_compl_eq_zero (ξ := ξ) (a := e2coord t 1) (b := e2coord t 0)
        hmeasξ hindepξ hlawξ (e2coord_ne t).symm
      refine (condExp_congr_ae ?_).trans h
      rw [degenTerm_e2_mul]
      filter_upwards with ω
      exact mul_comm _ _
    · rw [degenTerm_e2_mul]
      exact condExp_mul_compl_eq_zero (ξ := ξ) (a := e2coord t 0) (b := e2coord t 1)
        hmeasξ hindepξ hlawξ (e2coord_ne t)
  have hsub : e2coord t '' e' ⊆ {e2coord t k}ᶜ := by
    rintro _ ⟨jj, hj, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    rcases fin_two_cases jj with rfl | rfl <;> rcases fin_two_cases k with rfl | rfl
    · exact hk hj
    · exact e2coord_ne t hcon
    · exact e2coord_ne t hcon.symm
    · exact hk hj
  have hmono : latentSigma ξ (e2coord t '' e') ≤ latentSigma ξ {e2coord t k}ᶜ :=
    latentSigma_mono ξ hsub
  have hle2 : latentSigma ξ ({e2coord t k}ᶜ : Set (ℕ × ℕ)) ≤ ‹MeasurableSpace Ω› :=
    latentSigma_le hmeasξ _
  have hsf : SigmaFinite (P.trim hle2) := by
    have : IsFiniteMeasure (P.trim hle2) := isFiniteMeasure_trim hle2
    infer_instance
  have htower := condExp_condExp_of_le (μ := P) (f := degenTerm ξ e2coord e2ker t) hmono hle2
  refine htower.symm.trans ?_
  refine (condExp_congr_ae hcompl).trans ?_
  rw [condExp_zero]

/-- The two sub-tuples do not share the latent variable `coord 1 1 = (0,3)`. -/
theorem e2_unshared : e2coord 1 1 ∉ tupleSupport e2coord 0 := by
  rintro ⟨jj, hj⟩
  rcases fin_two_cases jj with rfl | rfl <;>
    exact absurd (congrArg Prod.snd hj) (by norm_num [e2coord])

end Deg

/-- The hypotheses of `Orth.integral_degenTerm_mul_eq_zero_of_or` hold on the witness model,
the kernel is not identically zero, and the orthogonality follows. -/
theorem orth_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∀ v, Measurable (ξ v)) ∧ iIndepFun ξ P
    ∧ (∀ (t : Fin 2) (e' : Set (Fin 2)), e' ≠ Set.univ →
        P[degenTerm ξ e2coord e2ker t | latentSigma ξ (e2coord t '' e')] =ᵐ[P] 0)
    ∧ (∀ t : Fin 2, ∫ ω, degenTerm ξ e2coord e2ker t ω ^ 2 ∂P = 1)
    ∧ ∫ ω, degenTerm ξ e2coord e2ker 0 ω * degenTerm ξ e2coord e2ker 1 ω ∂P = 0 := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hdeg := hdeg_e2 hmeasξ hindepξ hlawξ
  have hL2 : ∀ t : Fin 2, MemLp (degenTerm ξ e2coord e2ker t) 2 P := fun t =>
    memLp_zE2 hlawξ hindepξ hmeasξ t
  refine ⟨Ω, mΩ, P, hprobξ, ξ, hmeasξ, hindepξ, hdeg, fun t => ?_, ?_⟩
  · exact integral_zE2_sq hlawξ hindepξ hmeasξ t
  · exact CLTMartingale.Orth.integral_degenTerm_mul_eq_zero_of_or (μ := P) (U := ξ)
      (coord := e2coord) (g := e2ker) (coord' := e2coord) (g' := e2ker) (t := 0) (s := 1)
      hmeasξ hindepξ measurable_e2ker measurable_e2ker (hdeg 0) (hdeg 1) (hL2 0) (hL2 1)
      (Or.inl ⟨1, e2_unshared⟩)

end Witness

/-! ### Models for the Lindeberg condition and the multi-component martingale

Both models use the i.i.d. Rademacher array with ordering `lstep v = min v.1 1` (dimension `0`
first, then dimension `1`). `lindeberg_witness` satisfies every hypothesis of
`lindeberg_rowDiff_of_multilinear` with `j = 2`, two sub-tuples sharing `ξ_{(0,0)}`, and
coefficients `(n+1)^{-1}`; `∫T_n² = 2(n+1)^{-2} > 0`. `multi_martingale_witness` has two
components of arities `1` and `2` that complete at different steps, with `∫(∑_γT^γ)² = 4`. -/

namespace Witness

open DegenerateSum


/-- The Rademacher law is carried by `{-1,1}`. -/
theorem ae_abs_le_one_rade : ∀ᵐ x ∂rade, |x| ≤ 1 := by
  have hm0 : MeasurableSet {x : ℝ | |x| ≤ 1} :=
    measurableSet_le measurable_id.abs measurable_const
  have hm : MeasurableSet {x : ℝ | ¬ |x| ≤ 1} := hm0.compl
  rw [ae_iff]
  show rade {x : ℝ | ¬ |x| ≤ 1} = 0
  simp only [rade, Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply,
    Measure.dirac_apply' _ hm, smul_eq_mul]
  rw [Set.indicator_of_notMem (by norm_num), Set.indicator_of_notMem (by norm_num)]
  simp

section Deg2

variable {ξ : ℕ × ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
theorem ae_abs_xi_le_one (hlawξ : ∀ i, HasLaw (ξ i) rade P) (v : ℕ × ℕ) :
    ∀ᵐ ω ∂P, |ξ v ω| ≤ 1 := by
  have hm : MeasurableSet {x : ℝ | |x| ≤ 1} := measurableSet_le measurable_id.abs measurable_const
  have h := ae_map_iff (μ := P) (f := ξ v) (hlawξ v).aemeasurable
    (p := fun x : ℝ => |x| ≤ 1) hm
  rw [(hlawξ v).map_eq] at h
  exact h.1 ae_abs_le_one_rade

/-- `E[ξ_b | σ(ξ_v : v ∈ S)] = E[ξ_b] = 0` whenever `b ∉ S`. -/
theorem condExp_xi_eq_zero_of_notMem (hmeasξ : ∀ v, Measurable (ξ v)) (hindepξ : iIndepFun ξ P)
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) {b : ℕ × ℕ} {S : Set (ℕ × ℕ)} (hb : b ∉ S) :
    P[ξ b | latentSigma ξ S] =ᵐ[P] 0 :=
  condExp_eq_zero_of_indep (latentSigma_le hmeasξ _) (latentSigma_le hmeasξ _)
    (measurable_latentSigma ξ (S := ({b} : Set (ℕ × ℕ))) rfl).stronglyMeasurable
    (latentSigma_indep hmeasξ hindepξ (S := ({b} : Set (ℕ × ℕ))) (S' := S)
      (Set.disjoint_singleton_left.2 hb)) (integral_xi hlawξ b)

variable {Tt : Type*}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem degenTerm_pair (cd : Tt → Fin 2 → ℕ × ℕ) (t : Tt) :
    degenTerm ξ cd e2ker t = ξ (cd t 0) * ξ (cd t 1) := rfl

/-- Complete degeneracy of a rank-one kernel on two distinct latent variables, for an arbitrary
coordinate map. -/
theorem hdeg_pair (hmeasξ : ∀ v, Measurable (ξ v)) (hindepξ : iIndepFun ξ P)
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) (cd : Tt → Fin 2 → ℕ × ℕ)
    (hcd : ∀ t, cd t 0 ≠ cd t 1) (t : Tt) (e' : Set (Fin 2)) (hne : e' ≠ Set.univ) :
    P[degenTerm ξ cd e2ker t | latentSigma ξ (cd t '' e')] =ᵐ[P] 0 := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, k ∉ e' := by
    by_contra h
    exact hne (Set.eq_univ_of_forall fun k => not_not.mp fun hk => h (Exists.intro k hk))
  have hcompl : P[degenTerm ξ cd e2ker t | latentSigma ξ {cd t k}ᶜ] =ᵐ[P] 0 := by
    rcases fin_two_cases k with rfl | rfl
    · have h := condExp_mul_compl_eq_zero (ξ := ξ) (a := cd t 1) (b := cd t 0)
        hmeasξ hindepξ hlawξ (hcd t).symm
      refine (condExp_congr_ae ?_).trans h
      rw [degenTerm_pair]
      filter_upwards with ω
      exact mul_comm _ _
    · rw [degenTerm_pair]
      exact condExp_mul_compl_eq_zero (ξ := ξ) (a := cd t 0) (b := cd t 1)
        hmeasξ hindepξ hlawξ (hcd t)
  have hsub : cd t '' e' ⊆ {cd t k}ᶜ := by
    rintro _ ⟨jj, hj, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    rcases fin_two_cases jj with rfl | rfl <;> rcases fin_two_cases k with rfl | rfl
    · exact hk hj
    · exact hcd t hcon
    · exact hcd t hcon.symm
    · exact hk hj
  have hmono : latentSigma ξ (cd t '' e') ≤ latentSigma ξ {cd t k}ᶜ := latentSigma_mono ξ hsub
  have hle2 : latentSigma ξ ({cd t k}ᶜ : Set (ℕ × ℕ)) ≤ ‹MeasurableSpace Ω› :=
    latentSigma_le hmeasξ _
  have hsf : SigmaFinite (P.trim hle2) := by
    have : IsFiniteMeasure (P.trim hle2) := isFiniteMeasure_trim hle2
    infer_instance
  have htower := condExp_condExp_of_le (μ := P) (f := degenTerm ξ cd e2ker t) hmono hle2
  refine htower.symm.trans ?_
  refine (condExp_congr_ae hcompl).trans ?_
  rw [condExp_zero]

omit [IsProbabilityMeasure P] in
/-- The kernel term of a rank-one pair is bounded by `1`. -/
theorem ae_abs_degenTerm_pair_le (hlawξ : ∀ i, HasLaw (ξ i) rade P)
    (cd : Tt → Fin 2 → ℕ × ℕ) (t : Tt) :
    ∀ᵐ ω ∂P, |degenTerm ξ cd e2ker t ω| ≤ 1 := by
  filter_upwards [ae_abs_xi_le_one hlawξ (cd t 0), ae_abs_xi_le_one hlawξ (cd t 1)] with ω h0 h1
  show |ξ (cd t 0) ω * ξ (cd t 1) ω| ≤ 1
  rw [abs_mul]
  calc |ξ (cd t 0) ω| * |ξ (cd t 1) ω| ≤ 1 * 1 :=
        mul_le_mul h0 h1 (abs_nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem integrable_degenTerm_pair (hmeasξ : ∀ v, Measurable (ξ v))
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) (cd : Tt → Fin 2 → ℕ × ℕ) (t : Tt) :
    Integrable (degenTerm ξ cd e2ker t) P := by
  refine Integrable.mono' (g := fun _ => (1:ℝ)) (integrable_const _)
    (((hmeasξ (cd t 0)).mul (hmeasξ (cd t 1))).aestronglyMeasurable) ?_
  filter_upwards [ae_abs_degenTerm_pair_le hlawξ cd t] with ω hω
  rwa [Real.norm_eq_abs]

theorem memLp_degenTerm_pair (hmeasξ : ∀ v, Measurable (ξ v))
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) (cd : Tt → Fin 2 → ℕ × ℕ) (t : Tt) :
    MemLp (degenTerm ξ cd e2ker t) 2 P := by
  have hm : AEStronglyMeasurable (degenTerm ξ cd e2ker t) P :=
    ((hmeasξ (cd t 0)).mul (hmeasξ (cd t 1))).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine Integrable.mono' (g := fun _ => (1:ℝ)) (integrable_const _)
    ((hm.pow 2)) ?_
  filter_upwards [ae_abs_degenTerm_pair_le hlawξ cd t] with ω hω
  rw [Real.norm_eq_abs, abs_pow]
  calc |degenTerm ξ cd e2ker t ω| ^ 2 ≤ (1:ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hω 2
    _ = 1 := by norm_num

end Deg2
section Lind

open CLTMartingale CLTMartingale.Step45

/-- The coordinate map: coordinate `0` carries the shared dimension-0 variable `ξ_{(0,0)}`,
coordinate `1` a private dimension-1 variable. -/
def lcoord : Fin 2 → Fin 2 → ℕ × ℕ := fun t k => (k.val, if k.val = 0 then 0 else t.val + 1)

/-- The index of the sub-tuple's `k`-th coordinate inside dimension `k`. -/
def lidx : Fin 2 → Fin 2 → Fin 3 := fun t k => if k.val = 0 then 0 else t.succ

/-- The dimension-separated array: `ξ_{k,i}` is the latent variable `(k,i)`. -/
def lxi (ξ : ℕ × ℕ → Ω → ℝ) : Fin 2 → Fin 3 → Ω → ℝ := fun k i => ξ (k.val, i.val)

/-- The ordering: dimension `0` first, then dimension `1`; bounded by `2`. -/
def lstep : ℕ × ℕ → ℕ := fun v => min v.1 1

/-- The coefficients `(n+1)^{-1}`. -/
noncomputable def lc (n : ℕ) : Fin 2 → ℝ := fun _ => 1 / ((n : ℝ) + 1)

theorem lcoord_zero (t : Fin 2) : lcoord t 0 = (0, 0) := rfl

theorem lcoord_one (t : Fin 2) : lcoord t 1 = (1, t.val + 1) := rfl

theorem lcoord_ne (t : Fin 2) : lcoord t 0 ≠ lcoord t 1 := by
  intro h
  exact absurd (congrArg Prod.fst h) (by norm_num [lcoord])

theorem lidx_injective : Function.Injective lidx := by
  intro t s h
  have h1 : (t.succ : Fin 3) = s.succ := congrFun h 1
  have h2 : t.val + 1 = s.val + 1 := congrArg Fin.val h1
  exact Fin.ext (by omega)

theorem lphi_injective :
    Function.Injective (fun p : Σ _k : Fin 2, Fin 3 => ((p.1.val, p.2.val) : ℕ × ℕ)) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  have h1 : k.val = k'.val := congrArg Prod.fst h
  have h2 : i.val = i'.val := congrArg Prod.snd h
  obtain rfl := Fin.ext h1
  obtain rfl := Fin.ext h2
  rfl

theorem lstep_lt (v : ℕ × ℕ) : lstep v < 2 := by
  unfold lstep; omega

theorem lcompleted_zero : completedAt lcoord lstep 0 = (∅ : Finset (Fin 2)) := by decide

theorem lcompleted_one : completedAt lcoord lstep 1 = (Finset.univ : Finset (Fin 2)) := by decide

section Model

variable {ξ : ℕ × ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem lprod (t : Fin 2) (ω : Ω) :
    degenTerm ξ lcoord e2ker t ω = ∏ k : Fin 2, lxi ξ k (lidx t k) ω := by
  rw [Fin.prod_univ_two]
  rfl

omit [IsProbabilityMeasure P] in
theorem lindep_arr (hindepξ : iIndepFun ξ P) :
    iIndepFun (fun p : Σ _k : Fin 2, Fin 3 => lxi ξ p.1 p.2) P :=
  hindepξ.precomp (g := fun p : Σ _k : Fin 2, Fin 3 => ((p.1.val, p.2.val) : ℕ × ℕ))
    lphi_injective

end Model

/-- The design sum of `hdesign`, computed: `(3B⁴)^j∑_i(∑_{t ∈ R_i}c_t²)² = 36(n+1)^{-4}`. -/
theorem ldesign_eq (n : ℕ) :
    (3 * (1:ℝ) ^ 4) ^ 2 *
        ∑ i : Fin 2, (∑ t ∈ completedAt lcoord lstep (i : ℕ), lc n t ^ 2) ^ 2
      = 36 * (1 / ((n : ℝ) + 1)) ^ 4 := by
  have h0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  rw [Fin.sum_univ_two, h0, h1, lcompleted_zero, lcompleted_one]
  simp only [Finset.sum_empty, lc, Fin.sum_univ_two]
  ring

theorem ldesign : Tendsto (fun n : ℕ => (3 * (1:ℝ) ^ 4) ^ 2 *
    ∑ i : Fin 2, (∑ t ∈ completedAt lcoord lstep (i : ℕ), lc n t ^ 2) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 36 * (1 / ((n : ℝ) + 1)) ^ 4) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 4) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 4
    simpa using hb.const_mul (36 : ℝ)
  exact h.congr fun n => (ldesign_eq n).symm

end Lind
section Lind2

open CLTMartingale CLTMartingale.Step45

section Model2

variable {ξ : ℕ × ℕ → Ω → ℝ}

/-- `𝔼[g(U_t)²] = 1`. -/
theorem integral_degenTerm_pair_sq {Tt : Type*} (hmeasξ : ∀ v, Measurable (ξ v))
    (hindepξ : iIndepFun ξ P) (hlawξ : ∀ i, HasLaw (ξ i) rade P)
    (cd : Tt → Fin 2 → ℕ × ℕ) (hcd : ∀ t, cd t 0 ≠ cd t 1) (t : Tt) :
    ∫ ω, degenTerm ξ cd e2ker t ω ^ 2 ∂P = 1 := by
  have hne : cd t 0 ≠ cd t 1 := hcd t
  have hind : IndepFun (fun ω => ξ (cd t 0) ω ^ 2) (fun ω => ξ (cd t 1) ω ^ 2) P :=
    (hindepξ.indepFun hne).comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
      (by fun_prop) (by fun_prop)
  have h := hind.integral_mul_eq_mul_integral
    (((hmeasξ (cd t 0)).pow_const 2).aestronglyMeasurable)
    (((hmeasξ (cd t 1)).pow_const 2).aestronglyMeasurable)
  simp only [Pi.mul_apply] at h
  have hrw : ∫ ω, degenTerm ξ cd e2ker t ω ^ 2 ∂P
      = ∫ ω, ξ (cd t 0) ω ^ 2 * ξ (cd t 1) ω ^ 2 ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      show (ξ (cd t 0) ω * ξ (cd t 1) ω) ^ 2 = _
      ring)
  rw [hrw, h, integral_xi_sq hlawξ, integral_xi_sq hlawξ, one_mul]

end Model2

/-- The two sub-tuples share `ξ_{(0,0)}` and differ in dimension `1`. -/
theorem lsep (t s : Fin 2) (hts : t ≠ s) :
    (∃ k : Fin 2, lcoord s k ∉ tupleSupport lcoord t) ∨
    (∃ k : Fin 2, lcoord t k ∉ tupleSupport lcoord s) := by
  refine Or.inl ⟨1, ?_⟩
  rintro ⟨k, hk⟩
  rcases fin_two_cases k with rfl | rfl
  · exact absurd (congrArg Prod.fst hk) (by norm_num [lcoord])
  · have h : t.val + 1 = s.val + 1 := congrArg Prod.snd hk
    exact hts (Fin.ext (by omega))

/-- Every hypothesis of `lindeberg_rowDiff_of_multilinear` holds on the witness model. -/
theorem lindeberg_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P (fun _ => ξ) (fun _ => lcoord)
              (fun _ => e2ker) lc (fun _ => lstep) (fun _ => 2) n i ω|},
            (rowDiff P (fun _ => ξ) (fun _ => lcoord) (fun _ => e2ker) lc
              (fun _ => lstep) (fun _ => 2) n i ω) ^ 2 ∂P) atTop (𝓝 0))
    ∧ (∀ n : ℕ, ∫ ω, degenSum ξ lcoord e2ker (lc n) ω ^ 2 ∂P = 2 / ((n : ℝ) + 1) ^ 2)
    ∧ (∀ n : ℕ, (0:ℝ) < 2 / ((n : ℝ) + 1) ^ 2)
    ∧ completedAt lcoord lstep 0 = (∅ : Finset (Fin 2))
    ∧ completedAt lcoord lstep 1 = (Finset.univ : Finset (Fin 2))
    ∧ (∀ n : ℕ, ∫ ω, degenSum ξ lcoord e2ker (lc (n + 1)) ω ^ 2 ∂P ≤ 1) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hdeg : ∀ (t : Fin 2) (e' : Set (Fin 2)), e' ≠ Set.univ →
      P[degenTerm ξ lcoord e2ker t | latentSigma ξ (lcoord t '' e')] =ᵐ[P] 0 :=
    hdeg_pair hmeasξ hindepξ hlawξ lcoord lcoord_ne
  have hint : ∀ t : Fin 2, Integrable (degenTerm ξ lcoord e2ker t) P := fun t =>
    integrable_degenTerm_pair hmeasξ hlawξ lcoord t
  have hbd : ∀ t : Fin 2, ∀ᵐ ω ∂P, |degenTerm ξ lcoord e2ker t ω| ≤ 1 := fun t =>
    ae_abs_degenTerm_pair_le hlawξ lcoord t
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, ?_, ?_, lcompleted_zero, lcompleted_one, ?_⟩
  · exact lindeberg_rowDiff_of_multilinear (I := fun _ _ => Fin 3) (ξ := fun _ => lxi ξ) (B := 1)
      (idx := fun _ => lidx) (U := fun _ => ξ) (coord := fun _ => lcoord)
      (g := fun _ => e2ker) (cf := lc) (stp := fun _ => lstep) (kk := fun _ => 2)
      (fun _ v => hmeasξ v) (fun _ => hindepξ) (fun _ => measurable_e2ker)
      (fun _ t => hint t) (fun _ => hdeg) (fun _ => lprod)
      (fun _ => lindep_arr hindepξ) (fun _ k i => hmeasξ _) (fun _ k i => integral_xi hlawξ _)
      (fun _ k i => ae_abs_xi_le_one hlawξ _) (fun _ => lidx_injective)
      (fun n i => measurable_degenDiff (c := lc n) (step := lstep) hmeasξ (i : ℕ))
      (fun n i => integrable_pow_four_degenDiff (c := lc n) (step := lstep) zero_le_one
        hmeasξ hindepξ measurable_e2ker hint hdeg hbd (i : ℕ))
      ldesign
  · intro n
    rw [integral_degenSum_sq (c := lc n) hmeasξ hindepξ measurable_e2ker
      (fun t => memLp_degenTerm_pair hmeasξ hlawξ lcoord t) hdeg lsep]
    simp only [lc, Fin.sum_univ_two,
      integral_degenTerm_pair_sq hmeasξ hindepξ hlawξ lcoord lcoord_ne]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · intro n
    positivity
  · intro n
    refine hsecond_of_coefficients (c := lc (n + 1)) hmeasξ hindepξ measurable_e2ker
      (fun t => memLp_degenTerm_pair hmeasξ hlawξ lcoord t) hdeg lsep
      (fun t => integral_degenTerm_pair_sq hmeasξ hindepξ hlawξ lcoord lcoord_ne t) ?_
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
    simp only [lc, Fin.sum_univ_two, hcast]
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_pow, one_pow, ← add_div, div_le_one (by positivity)]
    nlinarith [hn]

end Lind2
section Multi

open CLTMartingale CLTMartingale.Step45

/-- Two components of arities `|e_0| = 1` and `|e_1| = 2`. -/
abbrev mIota : Fin 2 → Type := fun γ => Fin (γ.val + 1)

/-- Two realized sub-tuples in each component. -/
abbrev mTup : Fin 2 → Type := fun _ => Fin 2

/-- The sites: component `0` uses `(0,0)` and `(0,1)`; component `1` uses `(0,3)` together
with `(1,t+1)`. All five are distinct. -/
def mcoord : ∀ γ : Fin 2, mTup γ → mIota γ → ℕ × ℕ :=
  fun γ t k => (k.val, if k.val = 0 then (if γ.val = 0 then t.val else 3) else t.val + 1)

/-- The kernel of every component is the product over its own level. -/
def mker : ∀ γ : Fin 2, (mIota γ → ℝ) → ℝ := fun _ x => ∏ k, x k

/-- Unit coefficients. -/
def mc : ∀ γ : Fin 2, mTup γ → ℝ := fun _ _ => 1

theorem mker_zero : mker 0 = fun x : mIota 0 → ℝ => x 0 :=
  funext fun x => Fin.prod_univ_one x

theorem mker_one : mker 1 = e2ker :=
  funext fun x => Fin.prod_univ_two x

theorem mcoord_zero_apply (t : mTup 0) : mcoord 0 t 0 = (0, t.val) := rfl

theorem mcoord_one_ne (t : mTup 1) : mcoord 1 t 0 ≠ mcoord 1 t 1 := by
  intro h
  exact absurd (congrArg Prod.fst h) (by norm_num [mcoord])

theorem measurable_mker (γ : Fin 2) : Measurable (mker γ) :=
  Finset.measurable_prod _ fun k _ => measurable_pi_apply k

theorem mcompleted_zero_zero : completedAt (mcoord 0) lstep 0 = (Finset.univ : Finset (Fin 2)) := by
  decide

theorem mcompleted_zero_one : completedAt (mcoord 0) lstep 1 = (∅ : Finset (Fin 2)) := by decide

theorem mcompleted_one_zero : completedAt (mcoord 1) lstep 0 = (∅ : Finset (Fin 2)) := by decide

theorem mcompleted_one_one : completedAt (mcoord 1) lstep 1 = (Finset.univ : Finset (Fin 2)) := by
  decide

/-- The separation condition of `integral_multiDegenSum_sq`, over the sigma type: every two
distinct `(γ,t)` differ at some coordinate. -/
theorem mcoord_one_zero (t : mTup 1) : mcoord 1 t 0 = (0, 3) := rfl

theorem mcoord_one_one (t : mTup 1) : mcoord 1 t 1 = (1, t.val + 1) := rfl

theorem msep (γ γ' : Fin 2) (t : mTup γ) (s : mTup γ')
    (h : (⟨γ, t⟩ : Σ q : Fin 2, mTup q) ≠ ⟨γ', s⟩) :
    (∃ k : mIota γ', mcoord γ' s k ∉ tupleSupport (mcoord γ) t) ∨
    (∃ k : mIota γ, mcoord γ t k ∉ tupleSupport (mcoord γ') s) := by
  rcases fin_two_cases γ with rfl | rfl <;> rcases fin_two_cases γ' with rfl | rfl
  · have hts : t ≠ s := fun he => h (by rw [he])
    refine Or.inl ⟨0, ?_⟩
    rintro ⟨k, hk⟩
    obtain rfl : k = 0 := @Subsingleton.elim (Fin 1) _ k 0
    rw [mcoord_zero_apply, mcoord_zero_apply] at hk
    exact hts (Fin.ext (congrArg Prod.snd hk))
  · refine Or.inl ⟨1, ?_⟩
    rintro ⟨k, hk⟩
    obtain rfl : k = 0 := @Subsingleton.elim (Fin 1) _ k 0
    rw [mcoord_zero_apply, mcoord_one_one] at hk
    exact absurd (congrArg Prod.fst hk) (by norm_num)
  · refine Or.inl ⟨0, ?_⟩
    rintro ⟨k, hk⟩
    rw [mcoord_zero_apply] at hk
    rcases fin_two_cases k with rfl | rfl
    · rw [mcoord_one_zero] at hk
      have h3 : (3 : ℕ) = s.val := congrArg Prod.snd hk
      have := s.isLt
      omega
    · rw [mcoord_one_one] at hk
      exact absurd (congrArg Prod.fst hk) (by norm_num)
  · have hts : t ≠ s := fun he => h (by rw [he])
    refine Or.inl ⟨1, ?_⟩
    rintro ⟨k, hk⟩
    rw [mcoord_one_one] at hk
    rcases fin_two_cases k with rfl | rfl
    · rw [mcoord_one_zero] at hk
      exact absurd (congrArg Prod.fst hk) (by norm_num)
    · rw [mcoord_one_one] at hk
      have h1 : t.val + 1 = s.val + 1 := congrArg Prod.snd hk
      exact hts (Fin.ext (by omega))

end Multi
section Multi2

open CLTMartingale CLTMartingale.Step45

section Model3

variable {ξ : ℕ × ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem mdegenTerm_zero (t : mTup 0) :
    degenTerm ξ (mcoord 0) (mker 0) t = ξ (0, t.val) := by
  funext ω
  show (∏ k : Fin 1, ξ (mcoord 0 t k) ω) = ξ (0, t.val) ω
  rw [Fin.prod_univ_one]
  rfl

theorem mhdeg (hmeasξ : ∀ v, Measurable (ξ v)) (hindepξ : iIndepFun ξ P)
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) (γ : Fin 2) (t : mTup γ) (e' : Set (mIota γ))
    (hne : e' ≠ Set.univ) :
    P[degenTerm ξ (mcoord γ) (mker γ) t | latentSigma ξ (mcoord γ t '' e')] =ᵐ[P] 0 := by
  revert t e'
  rcases fin_two_cases γ with rfl | rfl
  · intro t e' hne
    have he : e' = (∅ : Set (mIota 0)) := by
      ext k
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hk
      exact hne (Set.eq_univ_of_forall fun j => by
        rwa [@Subsingleton.elim (Fin 1) _ j k])
    subst he
    rw [Set.image_empty, mdegenTerm_zero]
    exact condExp_xi_eq_zero_of_notMem hmeasξ hindepξ hlawξ
      (by simp : ((0:ℕ), t.val) ∉ (∅ : Set (ℕ × ℕ)))
  · intro t e' hne
    rw [mker_one]
    exact hdeg_pair hmeasξ hindepξ hlawξ (mcoord 1) mcoord_one_ne t e' hne

theorem mhsq (hmeasξ : ∀ v, Measurable (ξ v)) (hlawξ : ∀ i, HasLaw (ξ i) rade P)
    (γ : Fin 2) (t : mTup γ) : MemLp (degenTerm ξ (mcoord γ) (mker γ) t) 2 P := by
  revert t
  rcases fin_two_cases γ with rfl | rfl
  · intro t
    rw [mdegenTerm_zero]
    exact (hlawξ (0, t.val)).memLp memLp_id_rade
  · intro t
    rw [mker_one]
    exact memLp_degenTerm_pair hmeasξ hlawξ (mcoord 1) t

theorem mhone (hmeasξ : ∀ v, Measurable (ξ v)) (hindepξ : iIndepFun ξ P)
    (hlawξ : ∀ i, HasLaw (ξ i) rade P) (γ : Fin 2) (t : mTup γ) :
    ∫ ω, degenTerm ξ (mcoord γ) (mker γ) t ω ^ 2 ∂P = 1 := by
  revert t
  rcases fin_two_cases γ with rfl | rfl
  · intro t
    rw [mdegenTerm_zero]
    exact integral_xi_sq hlawξ _
  · intro t
    rw [mker_one]
    exact integral_degenTerm_pair_sq hmeasξ hindepξ hlawξ (mcoord 1) mcoord_one_ne t

end Model3

/-- A model for the multi-component martingale representation of `Multiway.Martingale`. -/
theorem multi_martingale_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      ((∀ κ, P[multiDegenDiff P ξ mcoord mker mc lstep κ |
            latentSigma ξ (revealed lstep κ)] =ᵐ[P] 0) ∧
        multiDegenSum ξ mcoord mker mc
          =ᵐ[P] (fun ω => ∑ κ ∈ Finset.range 2,
            multiDegenDiff P ξ mcoord mker mc lstep κ ω) ∧
        (∀ κ, multiDegenDiff P ξ mcoord mker mc lstep κ
          =ᵐ[P] fun ω => ∑ γ : Fin 2, ∑ t ∈ completedAt (mcoord γ) lstep κ,
            mc γ t * degenTerm ξ (mcoord γ) (mker γ) t ω) ∧
        (∀ (γ : Fin 2) (t : mTup γ), ∃! κ, t ∈ completedAt (mcoord γ) lstep κ))
    ∧ (∫ ω, multiDegenSum ξ mcoord mker mc ω ^ 2 ∂P = 4)
    ∧ completedAt (mcoord 0) lstep 0 = (Finset.univ : Finset (Fin 2))
    ∧ completedAt (mcoord 1) lstep 0 = (∅ : Finset (Fin 2))
    ∧ completedAt (mcoord 0) lstep 1 = (∅ : Finset (Fin 2))
    ∧ completedAt (mcoord 1) lstep 1 = (Finset.univ : Finset (Fin 2))
    ∧ Integrable (multiDegenSum ξ mcoord mker mc) P := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, ?_, mcompleted_zero_zero, mcompleted_one_zero,
    mcompleted_zero_one, mcompleted_one_one, ?_⟩
  · exact multi_martingale_representation (c := mc) hmeasξ hindepξ measurable_mker
      (mhsq hmeasξ hlawξ) (mhdeg hmeasξ hindepξ hlawξ) 2 lstep_lt
  · rw [integral_multiDegenSum_sq (c := mc) hmeasξ hindepξ measurable_mker
      (mhsq hmeasξ hlawξ) (mhdeg hmeasξ hindepξ hlawξ) msep]
    simp only [mc, mhone hmeasξ hindepξ hlawξ, Fin.sum_univ_two]
    norm_num
  · exact integrable_multiDegenSum (c := mc)
      (fun γ t => (mhsq hmeasξ hlawξ γ t).integrable one_le_two)

end Multi2

end Witness

/-! ### Part (b) with `hnorm` and `hsecond` derived

`hnorm` follows from the definition of `s_n²(L)` and the scaling of the coefficients
(`CLTMartingale.Step45.hnorm_of_scaling`); `hsecond` follows from the separation condition
`hsept`, the kernel second moment `hmom` and the bound `hcfmom`, `(∑_tc_t²)·mom ≤ 1`
(`CLTMartingale.Step2.hsecond_of_moment`). The remaining hypotheses are `halg`, `hstep4` and
`hstep5`. -/

section ComposeScaled

open DegenerateSum CLTMartingale CLTMartingale.Var StatLean.TimeSeries

/-- `scalar_clt_of_truncation` with `hnorm` and `hsecond` derived. The coefficient arrays and
the cell constant are `W^{(e_γ)}_c` and `∑_o(c'x̃_o)²σ²_ε(o)` divided by `s_n(L)` and `s_n²(L)`. -/
theorem scalar_clt_of_truncation_scaled
    {ι : Type*} [Fintype ι] [Nonempty ι] {T : Type*} [Fintype T] [DecidableEq T]
    {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {S : ℕ → Γ → Type*} [∀ n γ, Fintype (S n γ)]
    {Ix : ℕ → Type*} [∀ n, Fintype (Ix n)] {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site K N → Ω → ℝ}
    {sites : ∀ (n : ℕ) (γ : Γ), S n γ → Finset (Site K N)}
    {rIdx : ∀ _n : ℕ, Γ → Site K N → R}
    {arr arrRaw : ∀ (_L n : ℕ) (γ : Γ), S n γ → Ix n → ℝ}
    {lev : Γ → Finset K} {pt : ∀ (n : ℕ) (γ : Γ), S n γ → K → Site K N}
    {lam : ℕ → Γ → ℝ} {cellc cellRaw s2 mom cutmax totmax : ℕ → ℕ → ℝ}
    {coord : ℕ → T → ι → Site K N} {g : ℕ → ℕ → (ι → ℝ) → ℝ} {cf : ℕ → ℕ → T → ℝ}
    {stp : ℕ → Site K N → ℕ} {kk : ℕ → ℕ}
    {xi : ℕ → Ω → ℝ} {sc : ℕ → ℕ → ℝ} {del : ℕ → ℝ} {sig2 : ℝ}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hg : ∀ L n, Measurable (g L n))
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdeg : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : S n q), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q') (a b : K),
      pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinj : ∀ (n : ℕ) (q : Γ) (x y : S n q), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q'), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ L, ∑ γ, lam L γ ^ 2 ≤ 1)
    (hcut : ∀ (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr L n γ) * (Matrix.of (arr L n γ))ᵀ) ≤ cutmax L n)
    (hcutA : ∀ (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr L n q)))ᵀ) ≤ cutmax L n)
    (htot : ∀ (L n : ℕ) (γ : Γ), rectFrobSq (arr L n γ) ≤ totmax L n)
    (hs2def : ∀ L n, s2 L n = (∑ γ, lam L γ ^ 2 * rectFrobSq (arrRaw L n γ)) + cellRaw L n)
    (hs2pos : ∀ L n, 0 < s2 L n)
    (harr : ∀ (L n : ℕ) (γ : Γ) (s : S n γ) (i : Ix n),
      arr L n γ s i = arrRaw L n γ s i / Real.sqrt (s2 L n))
    (hcell : ∀ L n, cellc L n = cellRaw L n / s2 L n)
    (halg : ∀ L n,
      mdsCondVariance kk (rowDiff P U coord (g L) (cf L) stp kk) (rowSigma U stp kk) P n
        =ᵐ[P] fun ω =>
          quadForm (U n) ψ (sites n) (rIdx n) (arr L n) tag (lam L) ω + cellc L n)
    (hrate : ∀ L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card K)
          * (cutmax L n * totmax L n)) atTop (𝓝 0))
    (hlind : ∀ (L : ℕ) (ε : ℝ), 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P U coord (g L) (cf L) stp kk n i ω|},
        (rowDiff P U coord (g L) (cf L) stp kk n i ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsig2 : 0 < sig2) (hxi : ∀ n, MemLp (xi n) 2 P)
    (hTr : ∀ L n, MemLp (degenSum (U n) (coord n) (g L n) (cf L n)) 2 P)
    (hsc : ∀ L n, 0 ≤ sc L n) (hdel : Tendsto del atTop (𝓝 0))
    (hsept : ∀ (n : ℕ) (t s : T), t ≠ s →
      (∃ k : ι, coord n s k ∉ tupleSupport (coord n) t) ∨
      (∃ k : ι, coord n t k ∉ tupleSupport (coord n) s))
    (hmom : ∀ L n t, ∫ ω, degenTerm (U n) (coord n) (g L n) t ω ^ 2 ∂P = mom L n)
    (hcfmom : ∀ L n, (∑ t : T, cf L n t ^ 2) * mom L n ≤ 1)
    (hstep4 : ∀ L, ∀ᶠ n in atTop, |sc L n ^ 2 - sig2| ≤ del L)
    (hstep5 : ∀ L, ∀ᶠ n in atTop,
      ∫ ω, (xi n ω - sc L n * degenSum (U n) (coord n) (g L n) (cf L n) ω) ^ 2 ∂P ≤ del L) :
    TendstoInDistribution xi atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal sig2)) := by
  refine scalar_clt_of_truncation (S := S) (Ix := Ix) (tag := tag) (arr := arr)
    (lev := lev) (pt := pt) (lam := lam) (cellc := cellc) (cutmax := cutmax) (totmax := totmax)
    hbs hg hsq hdeg hN hsite hptc hptf hpos hinj hsep hlam hcut hcutA htot ?_ halg hrate hlind
    hsig2 hxi hTr hsc hdel ?_ hstep4 hstep5
  · intro L n
    have hA : ∀ γ : Γ, arr L n γ = fun s i => arrRaw L n γ s i / Real.sqrt (s2 L n) :=
      fun γ => funext fun s => funext fun i => harr L n γ s i
    simp only [hA, hcell L n]
    exact Step45.hnorm_of_scaling (lam L) (arrRaw L n) (cellRaw L n) (s2 L n)
      (hs2def L n) (hs2pos L n)
  · intro L n
    exact Step2.hsecond_of_moment (hbs n).measurable_latent (hbs n).indep (hg L n) (hsq L n)
      (hdeg L n) (hsept n) (hmom L n) (hcfmom L n)

/-- **Theorem 4(b)** with `hnorm` and `hsecond` derived: `clt_b` with `hdir` supplied by
`scalar_clt_of_truncation_scaled` in each direction. -/
theorem clt_b_of_truncation_scaled {K : ℕ}
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (hnumeas : ∀ n o, Measurable fun ω => nu n ω o)
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    {ι : Type*} [Fintype ι] [Nonempty ι] {T : Type*} [Fintype T] [DecidableEq T]
    {Kd : Type*} [Fintype Kd] [DecidableEq Kd] {N : Kd → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {S : ℕ → Γ → Type*} [∀ n γ, Fintype (S n γ)]
    {Ix : ℕ → Type*} [∀ n, Fintype (Ix n)] {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site Kd N → Ω → ℝ}
    {sites : ∀ (n : ℕ) (γ : Γ), S n γ → Finset (Site Kd N)}
    {rIdx : ∀ _n : ℕ, Γ → Site Kd N → R}
    {lev : Γ → Finset Kd} {pt : ∀ (n : ℕ) (γ : Γ), S n γ → Kd → Site Kd N}
    {coord : ℕ → T → ι → Site Kd N} {g : ℕ → ℕ → (ι → ℝ) → ℝ}
    {stp : ℕ → Site Kd N → ℕ} {kk : ℕ → ℕ}
    {arr arrRaw : ∀ (_c : EuclideanSpace ℝ (Fin K)) (_L n : ℕ) (γ : Γ), S n γ → Ix n → ℝ}
    {lam : EuclideanSpace ℝ (Fin K) → ℕ → Γ → ℝ}
    {cellc cellRaw s2 cutmax totmax sc : EuclideanSpace ℝ (Fin K) → ℕ → ℕ → ℝ}
    {mom : ℕ → ℕ → ℝ}
    {cf : EuclideanSpace ℝ (Fin K) → ℕ → ℕ → T → ℝ}
    {del : EuclideanSpace ℝ (Fin K) → ℕ → ℝ}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hg : ∀ L n, Measurable (g L n))
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdegk : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : S n q), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q') (a b : Kd),
      pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinjs : ∀ (n : ℕ) (q : Γ) (x y : S n q), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q'), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ c L, ∑ γ, lam c L γ ^ 2 ≤ 1)
    (hcut : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr c L n γ) * (Matrix.of (arr c L n γ))ᵀ) ≤ cutmax c L n)
    (hcutA : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr c L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr c L n q)))ᵀ) ≤ cutmax c L n)
    (htot : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (γ : Γ),
      rectFrobSq (arr c L n γ) ≤ totmax c L n)
    (hs2def : ∀ c L n,
      s2 c L n = (∑ γ, lam c L γ ^ 2 * rectFrobSq (arrRaw c L n γ)) + cellRaw c L n)
    (hs2pos : ∀ c L n, 0 < s2 c L n)
    (harr : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (γ : Γ) (s : S n γ) (i : Ix n),
      arr c L n γ s i = arrRaw c L n γ s i / Real.sqrt (s2 c L n))
    (hcell : ∀ c L n, cellc c L n = cellRaw c L n / s2 c L n)
    (halg : ∀ c L n,
      mdsCondVariance kk (rowDiff P U coord (g L) (cf c L) stp kk) (rowSigma U stp kk) P n
        =ᵐ[P] fun ω =>
          quadForm (U n) ψ (sites n) (rIdx n) (arr c L n) tag (lam c L) ω + cellc c L n)
    (hrate : ∀ c L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card Kd)
          * (cutmax c L n * totmax c L n)) atTop (𝓝 0))
    (hlind : ∀ (c : EuclideanSpace ℝ (Fin K)) (L : ℕ) (ε : ℝ), 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P U coord (g L) (cf c L) stp kk n i ω|},
        (rowDiff P U coord (g L) (cf c L) stp kk n i ω) ^ 2 ∂P) atTop (𝓝 0))
    (hxi : ∀ (c : EuclideanSpace ℝ (Fin K)) (n : ℕ),
      MemLp (fun ω => (Real.sqrt n)⁻¹ * ⟪score (⨆ m, Sm n m) (Xm n) (nu n ω), c⟫) 2 P)
    (hTr : ∀ c L n, MemLp (degenSum (U n) (coord n) (g L n) (cf c L n)) 2 P)
    (hsc : ∀ c L n, 0 ≤ sc c L n) (hdel : ∀ c, Tendsto (del c) atTop (𝓝 0))
    (hsept : ∀ (n : ℕ) (t s : T), t ≠ s →
      (∃ k : ι, coord n s k ∉ tupleSupport (coord n) t) ∨
      (∃ k : ι, coord n t k ∉ tupleSupport (coord n) s))
    (hmom : ∀ L n t, ∫ ω, degenTerm (U n) (coord n) (g L n) t ω ^ 2 ∂P = mom L n)
    (hcfmom : ∀ c L n, (∑ t : T, cf c L n t ^ 2) * mom L n ≤ 1)
    (hstep4 : ∀ c L, ∀ᶠ (n : ℕ) in atTop, |sc c L n ^ 2 - c ⬝ᵥ (Smat *ᵥ c)| ≤ del c L)
    (hstep5 : ∀ c L, ∀ᶠ (n : ℕ) in atTop,
      ∫ ω, ((Real.sqrt n)⁻¹ * ⟪score (⨆ m, Sm n m) (Xm n) (nu n ω), c⟫
        - sc c L n * degenSum (U n) (coord n) (g L n) (cf c L n) ω) ^ 2 ∂P ≤ del c L)
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (ιv : ∀ n, EuclideanSpace ℝ (O n)) (hι : ∀ n, ιv n ∈ ⨆ m, Sm n m)
    (hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, Sm n m) (Xm n))
    (bJM bMFE : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbJMmeas : ∀ n, AEMeasurable (bJM n) P) (hbMFEmeas : ∀ n, AEMeasurable (bMFE n) P)
    (hbJM : ∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (ιv n) (⨆ m, Sm n m) (Xm n)) (Xm n)
      (yv n ω) (bJM n ω))
    (hbMFE : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (bMFE n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bJM n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat)
      ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bMFE n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine clt_b Sm Xm β fe hfe nu yv hmodel hnumeas Smat hSpd ?_ A Hinv hAsolve hAlim
    ιv hι hid bJM bMFE hbJMmeas hbMFEmeas hbJM hbMFE
  intro c hc
  exact scalar_clt_of_truncation_scaled (S := S) (Ix := Ix) (tag := tag) (arr := arr c)
    (arrRaw := arrRaw c) (lev := lev) (pt := pt) (lam := lam c) (cellc := cellc c)
    (cellRaw := cellRaw c) (s2 := s2 c) (mom := mom) (cutmax := cutmax c)
    (totmax := totmax c) (cf := cf c) (sc := sc c) (del := del c)
    hbs hg hsq hdegk hN hsite hptc hptf hpos hinjs hsep (hlam c) (hcut c) (hcutA c) (htot c)
    (hs2def c) (hs2pos c) (harr c) (hcell c) (halg c) (hrate c) (hlind c)
    (dotProduct_mulVec_pos_of_posDef hSpd hc) (hxi c) (hTr c) (hsc c) (hdel c)
    hsept hmom (hcfmom c) (hstep4 c) (hstep5 c)

end ComposeScaled

/-! ### Models for the tensor-basis layer of `Multiway.CLTMartingale`

These models take a level of size `2`, two sub-tuples completing at one step, a proper truncation
set with gap `1`, and a nonzero cell term. `radeBasis` is a complete orthonormal basis `{1, sgn}`
of `L²(rade)`; `sgn` is used in place of `id` because `IsBasisSystem.bound` is a bound on all of
`ℝ`. -/

namespace Witness

open DegenerateSum CLTMartingale
open scoped InnerProductSpace

/-- The sign function, a bounded representative of `id` under `rade`. -/
noncomputable def sgn : ℝ → ℝ := fun x => if 0 ≤ x then 1 else -1

theorem measurable_sgn : Measurable sgn :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const

theorem abs_sgn (x : ℝ) : |sgn x| = 1 := by
  unfold sgn; split_ifs <;> norm_num

/-- The system `{ψ_0 ≡ 1, ψ_1 = sgn}` for the two-point latent law. -/
noncomputable def psiR : Fin 2 → ℝ → ℝ := ![fun _ => 1, sgn]

theorem psiR_zero : psiR 0 = fun _ : ℝ => 1 := rfl
theorem psiR_one : psiR 1 = sgn := rfl

theorem measurable_psiR (r : Fin 2) : Measurable (psiR r) := by
  fin_cases r
  · exact measurable_const
  · exact measurable_sgn

theorem abs_psiR_le (r : Fin 2) (x : ℝ) : |psiR r x| ≤ 1 := by
  fin_cases r
  · simp [psiR]
  · simp [psiR, abs_sgn]

theorem integral_psiR_mul (r r' : Fin 2) :
    ∫ x, psiR r x * psiR r' x ∂rade = if r = r' then (1 : ℝ) else 0 := by
  have hm : Measurable (fun x => psiR r x * psiR r' x) :=
    (measurable_psiR r).mul (measurable_psiR r')
  rw [integral_rade hm]
  fin_cases r <;> fin_cases r' <;> simp [psiR, sgn] <;> norm_num

theorem integral_psiR_one : ∫ x, psiR 1 x ∂rade = 0 := by
  rw [integral_rade (measurable_psiR 1)]
  simp [psiR, sgn]
  norm_num

theorem memLp_psiR (r : Fin 2) : MemLp (psiR r) 2 rade := by
  refine (memLp_two_iff_integrable_sq (measurable_psiR r).aestronglyMeasurable).2 ?_
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _)
    (((measurable_psiR r).pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  calc |psiR r x| ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_psiR_le r x) 2
    _ = 1 := by norm_num

noncomputable def bvec : Fin 2 → Lp ℝ 2 rade := fun r => (memLp_psiR r).toLp _

theorem coeFn_bvec (r : Fin 2) : (bvec r : ℝ → ℝ) =ᵐ[rade] psiR r := MemLp.coeFn_toLp _

theorem inner_bvec (r r' : Fin 2) : ⟪bvec r, bvec r'⟫_ℝ = if r = r' then (1 : ℝ) else 0 := by
  rw [MeasureTheory.L2.inner_def, ← integral_psiR_mul r r']
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bvec r, coeFn_bvec r'] with x h1 h2
  show ⟪(bvec r : ℝ → ℝ) x, (bvec r' : ℝ → ℝ) x⟫_ℝ = psiR r x * psiR r' x
  rw [h1, h2]
  exact real_inner_comm _ _

theorem orthonormal_bvec : Orthonormal ℝ bvec := orthonormal_iff_ite.2 inner_bvec

/-- `{1, sgn}` is complete in `L²(rade)`. -/
theorem orthogonal_bvec : (Submodule.span ℝ (Set.range bvec))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  set f' : ℝ → ℝ := (Lp.aestronglyMeasurable f).mk (f : ℝ → ℝ) with hf'def
  have hf'ae : (f : ℝ → ℝ) =ᵐ[rade] f' := (Lp.aestronglyMeasurable f).ae_eq_mk
  have hf'm : Measurable f' := ((Lp.aestronglyMeasurable f).stronglyMeasurable_mk).measurable
  have hinner : ∀ r : Fin 2, ∫ x, psiR r x * f' x ∂rade = 0 := by
    intro r
    have h := (Submodule.mem_orthogonal _ f).mp hf (bvec r) (Submodule.subset_span ⟨r, rfl⟩)
    rw [MeasureTheory.L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_bvec r, hf'ae] with x h1 h2
    show psiR r x * f' x = ⟪(bvec r : ℝ → ℝ) x, (f : ℝ → ℝ) x⟫_ℝ
    rw [h1, h2]
    exact real_inner_comm (psiR r x) (f' x)
  have e0 := hinner 0
  have e1 := hinner 1
  have hm0 : Measurable (fun x => psiR 0 x * f' x) := (measurable_psiR 0).mul hf'm
  have hm1 : Measurable (fun x => psiR 1 x * f' x) := (measurable_psiR 1).mul hf'm
  rw [integral_rade hm0] at e0
  rw [integral_rade hm1] at e1
  simp only [psiR, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at e0 e1
  have hs1 : sgn 1 = 1 := by norm_num [sgn]
  have hsm1 : sgn (-1) = -1 := by norm_num [sgn]
  rw [hs1, hsm1] at e1
  have hval1 : f' 1 = 0 := by linarith
  have hvalm1 : f' (-1) = 0 := by linarith
  have hzero : (f : ℝ → ℝ) =ᵐ[rade] 0 := by
    refine hf'ae.trans ?_
    have hmA : MeasurableSet {x : ℝ | ¬ (f' x = 0)} :=
      (hf'm (measurableSet_singleton (0 : ℝ))).compl
    rw [EventuallyEq, ae_iff]
    show rade {x : ℝ | ¬ (f' x = (0 : ℝ → ℝ) x)} = 0
    have hset : {x : ℝ | ¬ (f' x = (0 : ℝ → ℝ) x)} = {x : ℝ | ¬ (f' x = 0)} := rfl
    rw [hset]
    simp only [rade, Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply,
      Measure.dirac_apply' _ hmA, smul_eq_mul]
    rw [Set.indicator_of_notMem (by simp [hval1]), Set.indicator_of_notMem (by simp [hvalm1])]
    simp
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hzero

/-- An orthonormal basis of `L²(rade)`. -/
noncomputable def radeBasis : HilbertBasis (Fin 2) ℝ (Lp ℝ 2 rade) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_bvec orthogonal_bvec

@[simp] theorem coe_radeBasis : ⇑radeBasis = bvec :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

theorem coeFn_radeBasis (r : Fin 2) : (radeBasis r : ℝ → ℝ) =ᵐ[rade] psiR r := by
  rw [coe_radeBasis]
  exact coeFn_bvec r

/-! ### The tensor-basis model -/

/-- The two-dimensional level `e = {1,2}`: coordinate `0` lies in dimension `0` and coordinate
`1` in dimension `1`, so `scoord t` is injective for every sub-tuple. -/
def scoord : Fin 4 → Fin 2 → ℕ × ℕ :=
  fun t k => if k = 0 then (0, t.val % 2) else (1, t.val / 2 + 1)

theorem scoord_injective (t : Fin 4) : Function.Injective (scoord t) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [scoord]

/-- The multi-index `(1,1)`, all of whose components are mean-zero basis elements. -/
def rho1 : Fin 2 → Fin 2 := fun _ => 1

/-- The multi-index `(0,1)`, lying outside the truncation set. -/
def rho2 : Fin 2 → Fin 2 := ![0, 1]

theorem rho1_ne_rho2 : rho1 ≠ rho2 := by
  intro h
  have h0 := congrFun h 0
  simp [rho1, rho2] at h0

noncomputable abbrev bpRade (r : Fin 2 → Fin 2) :
    Lp ℝ 2 (Measure.pi (fun _ : Fin 2 => rade)) :=
  TensorBasis.basisProd (fun _ : Fin 2 => radeBasis) r

noncomputable abbrev PBrade :
    HilbertBasis (Fin 2 → Fin 2) ℝ (Lp ℝ 2 (Measure.pi (fun _ : Fin 2 => rade))) :=
  TensorBasis.prodHilbertBasis (fun _ : Fin 2 => radeBasis)

theorem inner_bpRade (r r' : Fin 2 → Fin 2) :
    ⟪bpRade r, bpRade r'⟫_ℝ = if r = r' then (1 : ℝ) else 0 :=
  orthonormal_iff_ite.1 (TensorBasis.orthonormal_basisProd (fun _ : Fin 2 => radeBasis)) r r'

theorem norm_bpRade (r : Fin 2 → Fin 2) : ‖bpRade r‖ = 1 :=
  (TensorBasis.orthonormal_basisProd (fun _ : Fin 2 => radeBasis)).1 r

/-- The witness kernel `h^{(e)} = ψ_1 ⊗ ψ_1 + ψ_0 ⊗ ψ_1`. -/
noncomputable def xwit : Lp ℝ 2 (Measure.pi (fun _ : Fin 2 => rade)) := bpRade rho1 + bpRade rho2

/-- The truncation set `{(1,1)}`, a proper subset of the index set. -/
def Fwit : Finset (Fin 2 → Fin 2) := {rho1}

theorem lam_rho1 : ⟪bpRade rho1, xwit⟫_ℝ = 1 := by
  rw [xwit, inner_add_right, inner_bpRade, inner_bpRade]
  simp [rho1_ne_rho2]

theorem trunc_wit : TensorBasis.trunc PBrade xwit Fwit = bpRade rho1 := by
  rw [TensorBasis.trunc_prodHilbertBasis, Fwit, Finset.sum_singleton, lam_rho1, one_smul]

theorem sub_trunc_wit : xwit - TensorBasis.trunc PBrade xwit Fwit = bpRade rho2 := by
  rw [trunc_wit, xwit, add_sub_cancel_left]

theorem norm_trunc_sq : ‖TensorBasis.trunc PBrade xwit Fwit‖ ^ 2 = 1 := by
  rw [trunc_wit, norm_bpRade]; norm_num

theorem norm_gap_sq : ‖xwit - TensorBasis.trunc PBrade xwit Fwit‖ ^ 2 = 1 := by
  rw [sub_trunc_wit, norm_bpRade]; norm_num

theorem norm_xwit_sq : ‖xwit‖ ^ 2 = 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (bpRade rho1) (bpRade rho2)
    (by rw [inner_bpRade]; simp [rho1_ne_rho2])
  rw [xwit, pow_two, h, norm_bpRade, norm_bpRade]
  norm_num

/-- The pointwise representative of the witness kernel. -/
noncomputable def G0 : (Fin 2 → ℝ) → ℝ :=
  fun u => Step2.prodKernel psiR rho1 u + Step2.prodKernel psiR rho2 u

theorem measurable_G0 : Measurable G0 :=
  (Step2.measurable_prodKernel measurable_psiR rho1).add
    (Step2.measurable_prodKernel measurable_psiR rho2)

theorem coeFn_xwit : G0 =ᵐ[Measure.pi (fun _ : Fin 2 => rade)] (xwit : (Fin 2 → ℝ) → ℝ) := by
  filter_upwards [Lp.coeFn_add (bpRade rho1) (bpRade rho2),
    Step2.coeFn_tensorBasisProd radeBasis coeFn_radeBasis rho1,
    Step2.coeFn_tensorBasisProd radeBasis coeFn_radeBasis rho2] with u h1 h2 h3
  show Step2.prodKernel psiR rho1 u + Step2.prodKernel psiR rho2 u
      = (xwit : (Fin 2 → ℝ) → ℝ) u
  rw [xwit, h1]
  simp only [Pi.add_apply, h2, h3]

/-- A model for the tensor-basis layer: the two-point latent law, the complete basis
`{1, sgn}`, a level with `k = 2`, and a proper truncation set; the truncation gap is `1` and the
truncated kernel has second moment `1`. -/
theorem seam_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      IsBasisSystem P ξ psiR ({1} : Set (Fin 2)) 1
    ∧ (∀ t : Fin 4, P.map (latentTuple ξ scoord t) = Measure.pi (fun _ : Fin 2 => rade))
    ∧ (∀ t : Fin 4, ∫ ω, degenTerm ξ scoord (Step2.prodKernel psiR rho1) t ω ^ 2 ∂P = 1)
    ∧ (∀ (t : Fin 4) (e' : Set (Fin 2)), e' ≠ Set.univ →
        P[degenTerm ξ scoord (Step2.prodKernel psiR rho1) t |
          latentSigma ξ (scoord t '' e')] =ᵐ[P] 0)
    ∧ (∀ (t : Fin 4) (e' : Set (Fin 2)), e' ≠ Set.univ →
        P[degenTerm ξ scoord
            (Step2.kernelTrunc psiR (fun r => ⟪bpRade r, xwit⟫_ℝ) Fwit) t |
          latentSigma ξ (scoord t '' e')] =ᵐ[P] 0)
    ∧ (∀ t : Fin 4, ∫ ω, degenTerm ξ scoord
        (Step2.kernelTrunc psiR (fun r => ⟪bpRade r, xwit⟫_ℝ) Fwit) t ω ^ 2 ∂P = 1)
    ∧ (∀ t : Fin 4, ∫ ω, degenTerm ξ scoord
        (G0 - Step2.kernelTrunc psiR (fun r => ⟪bpRade r, xwit⟫_ℝ) Fwit) t ω ^ 2 ∂P = 1)
    ∧ (∀ t : Fin 4, ∫ ω, degenTerm ξ scoord G0 t ω ^ 2 ∂P = 2) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = rade := fun v => (hlawξ v).map_eq
  have hbs : IsBasisSystem P ξ psiR ({1} : Set (Fin 2)) 1 :=
    Step2.isBasisSystem_of_hilbertBasis radeBasis hmeasξ measurable_psiR hindepξ hlaw
      abs_psiR_le coeFn_radeBasis (by
        intro r hr
        have : r = 1 := hr
        rw [this]
        exact integral_psiR_one)
  have hrho1 : ∀ i : Fin 2, rho1 i ∈ ({1} : Set (Fin 2)) := fun _ => rfl
  have hF : ∀ r ∈ Fwit, ∀ i : Fin 2, r i ∈ ({1} : Set (Fin 2)) := by
    intro r hr i
    simp only [Fwit, Finset.mem_singleton] at hr
    rw [hr]
    exact hrho1 i
  refine ⟨Ω, mΩ, P, hprobξ, ξ, hbs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t => Step2.map_latentTuple_eq_pi hmeasξ hindepξ hlaw (scoord_injective t)
  · exact fun t => Step2.integral_degenTerm_prodKernel_sq hbs (scoord_injective t) rho1
  · exact fun t e' hne =>
      Step2.condExp_degenTerm_prodKernel_eq_zero hbs (scoord_injective t) hrho1 e' hne
  · exact fun t e' hne =>
      Step2.condExp_degenTerm_kernelTrunc_eq_zero hbs (scoord_injective t) hF e' hne
  · intro t
    rw [Step2.integral_degenTerm_kernelTrunc_sq hmeasξ hindepξ hlaw (scoord_injective t)
      radeBasis measurable_psiR coeFn_radeBasis xwit Fwit]
    exact norm_trunc_sq
  · intro t
    rw [Step2.integral_degenTerm_sub_kernelTrunc_sq hmeasξ hindepξ hlaw (scoord_injective t)
      radeBasis measurable_psiR coeFn_radeBasis xwit measurable_G0 coeFn_xwit Fwit]
    exact norm_gap_sq
  · intro t
    rw [Step2.integral_degenTerm_sq_eq_norm_sq hmeasξ hindepξ hlaw (scoord_injective t)
      xwit measurable_G0 coeFn_xwit]
    exact norm_xwit_sq

/-- The same values assembled by `integral_degenTerm_pythagoras`: `1 + 1 = 2`. -/
theorem seam_pythagoras_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ), ∀ t : Fin 4,
      (∫ ω, degenTerm ξ scoord
          (Step2.kernelTrunc psiR (fun r => ⟪bpRade r, xwit⟫_ℝ) Fwit) t ω ^ 2 ∂P)
        + (∫ ω, degenTerm ξ scoord
          (G0 - Step2.kernelTrunc psiR (fun r => ⟪bpRade r, xwit⟫_ℝ) Fwit) t ω ^ 2 ∂P)
        = ∫ ω, degenTerm ξ scoord G0 t ω ^ 2 ∂P := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = rade := fun v => (hlawξ v).map_eq
  exact ⟨Ω, mΩ, P, hprobξ, ξ, fun t =>
    Step2.integral_degenTerm_pythagoras hmeasξ hindepξ hlaw (scoord_injective t)
      radeBasis measurable_psiR coeFn_radeBasis xwit measurable_G0 coeFn_xwit Fwit⟩

/-! ### The factorization model -/

/-- The revealing order: all dimension-`0` variables first, then the dimension-`1` variables
one at a time. -/
def sstep : ℕ × ℕ → ℕ := fun v => if v.1 = 0 then 0 else v.2

theorem completedAt_one : completedAt scoord sstep 1 = ({0, 1} : Finset (Fin 4)) := by decide

theorem hw_one : ∀ t ∈ completedAt scoord sstep 1, scoord t 1 = ((1, 1) : ℕ × ℕ) := by decide

theorem hrev_one : ∀ t ∈ completedAt scoord sstep 1, ∀ i : Fin 2, i ≠ 1 →
    sstep (scoord t i) < 1 := by decide

theorem sstep_w : (1 : ℕ) ≤ sstep ((1, 1) : ℕ × ℕ) := by decide

theorem zero_mem_revealed : ((0, 0) : ℕ × ℕ) ∈ revealed sstep 1 := by
  show sstep ((0, 0) : ℕ × ℕ) < 1
  norm_num [sstep]

/-- The coefficients: four distinct nonzero values. -/
noncomputable def cwit : Fin 4 → ℝ := fun t => (t.val : ℝ) + 1

theorem sgn_mul_self (x : ℝ) : sgn x * sgn x = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem sgn_sq (x : ℝ) : sgn x ^ 2 = 1 := by
  rw [pow_two]; exact sgn_mul_self x

/-- A model for the factorization `D^γ_κ = ψ_{r_{k⋆}}(U_w)·A^γ_w`: at the step `κ = 1`
revealing the site `(1,1)`, two sub-tuples complete, so the block `A^γ` is a genuine sum. -/
theorem factor_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (degenDiff P ξ scoord (Step2.prodKernel psiR rho1) cwit sstep 1
        =ᵐ[P] fun ω => psiR (rho1 1) (ξ (1, 1) ω) *
          ∑ t ∈ completedAt scoord sstep 1, cwit t *
            ∏ i ∈ Finset.univ.erase (1 : Fin 2), psiR (rho1 i) (ξ (scoord t i) ω))
    ∧ completedAt scoord sstep 1 = ({0, 1} : Finset (Fin 4))
    ∧ (∀ ω : Ω, |∑ t ∈ completedAt scoord sstep 1, cwit t *
          ∏ i ∈ Finset.univ.erase (1 : Fin 2), psiR (rho1 i) (ξ (scoord t i) ω)|
        ≤ (∑ t : Fin 4, |cwit t|) * max (1 : ℝ) 1 ^ Fintype.card (Fin 2))
    ∧ StronglyMeasurable[latentSigma ξ (revealed sstep 1)]
        (fun ω => ∑ t ∈ completedAt scoord sstep 1, cwit t *
          ∏ i ∈ Finset.univ.erase (1 : Fin 2), psiR (rho1 i) (ξ (scoord t i) ω)) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = rade := fun v => (hlawξ v).map_eq
  have hbs : IsBasisSystem P ξ psiR ({1} : Set (Fin 2)) 1 :=
    Step2.isBasisSystem_of_hilbertBasis radeBasis hmeasξ measurable_psiR hindepξ hlaw
      abs_psiR_le coeFn_radeBasis (by
        intro r hr
        have hr1 : r = 1 := hr
        rw [hr1]
        exact integral_psiR_one)
  have hrho1 : ∀ i : Fin 2, rho1 i ∈ ({1} : Set (Fin 2)) := fun _ => rfl
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, completedAt_one, ?_, ?_⟩
  · exact Step2.degenDiff_prodKernel_factor hbs scoord_injective hrho1 1 hw_one
  · intro ω
    exact Step2.abs_blockA_le hbs (coord := scoord) (ρ := rho1) (c := cwit) ω
  · exact Step2.stronglyMeasurable_blockA hbs (c := cwit) hrev_one

/-- A model for the one-step conditional variance, with two components carrying different
multi-indices at the revealed coordinate; the value is `5`. -/
theorem step_variance_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      P[fun ω => (∑ γ : Fin 2, (1 : ℝ) *
          (psiR γ (ξ (1, 1) ω) * (((γ.val : ℝ) + 1) * psiR 1 (ξ (0, 0) ω)))) ^ 2 |
          latentSigma ξ (revealed sstep 1)] =ᵐ[P] fun _ => (5 : ℝ) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = rade := fun v => (hlawξ v).map_eq
  have hbs : IsBasisSystem P ξ psiR ({1} : Set (Fin 2)) 1 :=
    Step2.isBasisSystem_of_hilbertBasis radeBasis hmeasξ measurable_psiR hindepξ hlaw
      abs_psiR_le coeFn_radeBasis (by
        intro r hr
        have hr1 : r = 1 := hr
        rw [hr1]
        exact integral_psiR_one)
  set A : Fin 2 → Ω → ℝ := fun γ ω => ((γ.val : ℝ) + 1) * psiR 1 (ξ (0, 0) ω) with hA
  have hAsm : ∀ γ : Fin 2, StronglyMeasurable[latentSigma ξ (revealed sstep 1)] (A γ) := by
    intro γ
    have h : Measurable[latentSigma ξ (revealed sstep 1)] (A γ) :=
      ((measurable_psiR 1).comp
        (measurable_latentSigma ξ (S := revealed sstep 1) zero_mem_revealed)).const_mul _
    exact h.stronglyMeasurable
  have hAmeas : ∀ γ : Fin 2, Measurable (A γ) := fun γ =>
    ((measurable_psiR 1).comp (hmeasξ (0, 0))).const_mul _
  have hAbd : ∀ (γ : Fin 2) (ω : Ω), |A γ ω| ≤ 2 := by
    intro γ ω
    rw [hA]
    show |((γ.val : ℝ) + 1) * psiR 1 (ξ (0, 0) ω)| ≤ 2
    rw [abs_mul]
    have h1 : |((γ.val : ℝ) + 1)| ≤ 2 := by
      have : (γ.val : ℝ) ≤ 1 := by
        have := γ.isLt
        have : γ.val ≤ 1 := by omega
        exact_mod_cast this
      rw [abs_of_nonneg (by positivity)]
      linarith
    calc |((γ.val : ℝ) + 1)| * |psiR 1 (ξ (0, 0) ω)| ≤ 2 * 1 :=
          mul_le_mul h1 (abs_psiR_le 1 _) (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_⟩
  refine (Step2.condExp_sq_step_of_prodKernel hbs (κ := 1) (w := (1, 1)) sstep_w
    (lam := fun _ => 1) (ρ' := id) (A := A) (D := fun γ ω => psiR γ (ξ (1, 1) ω) * A γ ω)
    hAsm hAmeas hAbd (fun γ => EventuallyEq.rfl)).trans ?_
  filter_upwards with ω
  simp only [hA, Fin.sum_univ_two, id]
  norm_num [sgn_mul_self, psiR]
  ring_nf
  rw [sgn_sq]
  norm_num

/-! ### Models for the variance comparison and the truncation gap -/

/-- The variance comparison on a design with two levels, `σ_e² = 2`, `τ_e²(L) = 1/2`,
`‖W^{(e)}_c‖_F² = 4 = 1·n` at `n = 4`, and a positive cell term. -/
theorem varcomp_witness :
    |((∑ _e : Fin 2, ((2 : ℝ) - 1 / 2) * 4) + 1) / 4 - ((∑ _e : Fin 2, (2 : ℝ) * 4) + 1) / 4|
      ≤ 1 * ∑ _e : Fin 2, (1 : ℝ) / 2 :=
  Step2.abs_varcomp_le Finset.univ (fun _ => 2) (fun _ => 1 / 2) (fun _ => 4) 1 4 1
    (by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)

/-- The bound is attained: both sides equal `1`. -/
theorem varcomp_witness_value :
    |((∑ _e : Fin 2, ((2 : ℝ) - 1 / 2) * 4) + 1) / 4 - ((∑ _e : Fin 2, (2 : ℝ) * 4) + 1) / 4|
      = 1 ∧ (1 : ℝ) * ∑ _e : Fin 2, (1 : ℝ) / 2 = 1 := by
  refine ⟨?_, ?_⟩
  · simp
    try norm_num
  · simp
    try norm_num

/-- `δ(L) → 0`, with `τ_e(L) = 1/(L+1)` positive at every level. -/
theorem delta_witness :
    Tendsto (fun L : ℕ => 3 * ∑ _e : Fin 2, (1 : ℝ) / ((L : ℝ) + 1)) atTop (𝓝 0)
      ∧ ∀ L : ℕ, 0 < (1 : ℝ) / ((L : ℝ) + 1) := by
  refine ⟨Step2.tendsto_delta Finset.univ 3 (fun _ L => 1 / ((L : ℝ) + 1)) (fun _ _ => ?_),
    fun L => by positivity⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- `τ_e²(L) → 0` for the infinite Fourier system of `TensorBasis`, where the gap is positive at
every finite `L`. -/
theorem tau_witness :
    Tendsto (fun L : ℕ => ‖TensorBasis.Witness.wit -
        TensorBasis.trunc TensorBasis.Witness.PB TensorBasis.Witness.wit
          (TensorBasis.box (Fin 2) L)‖ ^ 2) atTop (𝓝 0)
      ∧ ∀ L : ℕ, 0 < ‖TensorBasis.Witness.wit -
        TensorBasis.trunc TensorBasis.Witness.PB TensorBasis.Witness.wit
          (TensorBasis.box (Fin 2) L)‖ ^ 2 := by
  refine ⟨Step2.tendsto_normSq_sub_truncBox TensorBasis.Witness.PB TensorBasis.Witness.wit,
    fun L => ?_⟩
  exact pow_pos (TensorBasis.Witness.tensorBasis_witness.2.1 L) 2

/-! ### A model for `hsecond` -/

theorem hsept_scoord : ∀ t s : Fin 4, t ≠ s →
    (∃ k : Fin 2, scoord s k ∉ tupleSupport scoord t) ∨
    (∃ k : Fin 2, scoord t k ∉ tupleSupport scoord s) := by
  intro t s hts
  have hts' : t.val ≠ s.val := fun h => hts (Fin.ext h)
  left
  by_cases h : t.val % 2 = s.val % 2
  · refine ⟨1, ?_⟩
    rintro ⟨k, hk⟩
    fin_cases k <;> (simp [scoord] at hk; try omega)
  · refine ⟨0, ?_⟩
    rintro ⟨k, hk⟩
    fin_cases k <;> (simp [scoord] at hk; try omega)

/-- `hsecond` with equality: four sub-tuples, coefficients `1/2` and second moment `1`, so
`𝔼[T²] = 1`. -/
theorem hsecond_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∫ ω, degenSum ξ scoord (Step2.prodKernel psiR rho1) (fun _ => 1 / 2) ω ^ 2 ∂P ≤ 1)
    ∧ (∫ ω, degenSum ξ scoord (Step2.prodKernel psiR rho1) (fun _ => 1 / 2) ω ^ 2 ∂P = 1) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = rade := fun v => (hlawξ v).map_eq
  have hbs : IsBasisSystem P ξ psiR ({1} : Set (Fin 2)) 1 :=
    Step2.isBasisSystem_of_hilbertBasis radeBasis hmeasξ measurable_psiR hindepξ hlaw
      abs_psiR_le coeFn_radeBasis (by
        intro r hr
        have hr1 : r = 1 := hr
        rw [hr1]
        exact integral_psiR_one)
  have hrho1 : ∀ i : Fin 2, rho1 i ∈ ({1} : Set (Fin 2)) := fun _ => rfl
  have hmom : ∀ t : Fin 4,
      ∫ ω, degenTerm ξ scoord (Step2.prodKernel psiR rho1) t ω ^ 2 ∂P = 1 := fun t =>
    Step2.integral_degenTerm_prodKernel_sq hbs (scoord_injective t) rho1
  have hcf : (∑ _t : Fin 4, ((1 : ℝ) / 2) ^ 2) * 1 ≤ 1 := by
    simp
    norm_num
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, ?_⟩
  · exact Step2.hsecond_of_moment hbs.measurable_latent hbs.indep
      (Step2.measurable_prodKernel measurable_psiR rho1)
      (fun t => Step2.memLp_degenTerm_prodKernel hbs scoord t rho1)
      (fun t e' hne => Step2.condExp_degenTerm_prodKernel_eq_zero hbs (scoord_injective t)
        hrho1 e' hne)
      hsept_scoord hmom hcf
  · rw [Step45.integral_degenSum_sq hbs.measurable_latent hbs.indep
      (Step2.measurable_prodKernel measurable_psiR rho1)
      (fun t => Step2.memLp_degenTerm_prodKernel hbs scoord t rho1)
      (fun t e' hne => Step2.condExp_degenTerm_prodKernel_eq_zero hbs (scoord_injective t)
        hrho1 e' hne) hsept_scoord]
    simp only [hmom, mul_one]
    simp
    norm_num

end Witness

/-! ### Part (b) with `halg`, `hstep4` and `hstep5` derived

`scalar_clt_of_truncation_alg` is `scalar_clt_of_truncation_scaled` with `halg`, `hstep4` and
`hstep5` supplied from `Multiway.CLTMartingale`. Its inputs are the components `γ` with
multi-indices `ρ γ` and coefficients `λ_γ`, the revealing order and its `k⋆`, the design values of
`s_n²(L)` and `nc'S_nc`, and the untruncated kernel `h^{(e)}` with tail second moment `τ_e²(L)`.
It is stated for the latent array, with `cellc = 0`.

The models below use `wal`, the uniform law on `{0,1,2,3} ⊂ ℝ`, with two Walsh functions as a
bounded, mean-zero orthonormal system, so that two components can carry different basis indices
at `k⋆`. -/

namespace Witness

open DegenerateSum CLTMartingale StatLean.TimeSeries
open scoped ENNReal

/-! ### The four-point latent law -/

/-- The uniform law on `{0,1,2,3} ⊂ ℝ`. -/
noncomputable def wal : Measure ℝ :=
  (4⁻¹ : ℝ≥0∞) • (Measure.dirac (0 : ℝ) + Measure.dirac 1 + Measure.dirac 2 + Measure.dirac 3)

instance isProbabilityMeasure_wal : IsProbabilityMeasure wal := by
  constructor
  unfold wal
  rw [Measure.smul_apply, smul_eq_mul]
  simp only [Measure.coe_add, Pi.add_apply, measure_univ]
  rw [show (1 : ℝ≥0∞) + 1 + 1 + 1 = 4 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem integrable_wal {f : ℝ → ℝ} (hf : Measurable f) : Integrable f wal := by
  have hI : ∀ a : ℝ, Integrable f (Measure.dirac a) := fun a =>
    integrable_dirac' hf.stronglyMeasurable (by finiteness)
  have hsum : Integrable f
      (Measure.dirac (0 : ℝ) + Measure.dirac 1 + Measure.dirac 2 + Measure.dirac 3) :=
    (((hI 0).add_measure (hI 1)).add_measure (hI 2)).add_measure (hI 3)
  unfold wal
  exact (integrable_smul_measure (by norm_num : (4⁻¹ : ℝ≥0∞) ≠ 0) (by norm_num)).2 hsum

theorem integral_wal {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂wal = (f 0 + f 1 + f 2 + f 3) / 4 := by
  have hI : ∀ a : ℝ, Integrable f (Measure.dirac a) := fun a =>
    integrable_dirac' hf.stronglyMeasurable (by finiteness)
  unfold wal
  rw [integral_smul_measure,
    integral_add_measure (((hI 0).add_measure (hI 1)).add_measure (hI 2)) (hI 3),
    integral_add_measure ((hI 0).add_measure (hI 1)) (hI 2),
    integral_add_measure (hI 0) (hI 1),
    integral_dirac' _ _ hf.stronglyMeasurable, integral_dirac' _ _ hf.stronglyMeasurable,
    integral_dirac' _ _ hf.stronglyMeasurable, integral_dirac' _ _ hf.stronglyMeasurable]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  norm_num
  ring

/-! ### Two bounded, mean-zero, orthonormal functions on it -/

noncomputable def walA : ℝ → ℝ := fun x => if x = 1 ∨ x = 3 then -1 else 1
noncomputable def walB : ℝ → ℝ := fun x => if x = 1 ∨ x = 2 then -1 else 1
noncomputable def walPsi : Fin 2 → ℝ → ℝ := ![walA, walB]

theorem walPsi_zero : walPsi 0 = walA := rfl
theorem walPsi_one : walPsi 1 = walB := rfl

theorem measurableSet_pairA : MeasurableSet {x : ℝ | x = 1 ∨ x = 3} := by
  have h : {x : ℝ | x = 1 ∨ x = 3} = ({1} : Set ℝ) ∪ {3} := rfl
  rw [h]
  exact (measurableSet_singleton 1).union (measurableSet_singleton 3)

theorem measurableSet_pairB : MeasurableSet {x : ℝ | x = 1 ∨ x = 2} := by
  have h : {x : ℝ | x = 1 ∨ x = 2} = ({1} : Set ℝ) ∪ {2} := rfl
  rw [h]
  exact (measurableSet_singleton 1).union (measurableSet_singleton 2)

theorem measurable_walA : Measurable walA :=
  Measurable.ite measurableSet_pairA measurable_const measurable_const

theorem measurable_walB : Measurable walB :=
  Measurable.ite measurableSet_pairB measurable_const measurable_const

theorem measurable_walPsi (r : Fin 2) : Measurable (walPsi r) := by
  rcases fin_two_cases r with h | h <;> rw [h]
  · exact measurable_walA
  · exact measurable_walB

theorem abs_walPsi_le (r : Fin 2) (x : ℝ) : |walPsi r x| ≤ 2 := by
  rcases fin_two_cases r with h | h <;> rw [h]
  · show |walA x| ≤ 2
    unfold walA; split_ifs <;> norm_num
  · show |walB x| ≤ 2
    unfold walB; split_ifs <;> norm_num

theorem integral_walPsi (r : Fin 2) : ∫ x, walPsi r x ∂wal = 0 := by
  rcases fin_two_cases r with h | h <;> rw [h]
  · show ∫ x, walA x ∂wal = 0
    rw [integral_wal measurable_walA]
    norm_num [walA]
  · show ∫ x, walB x ∂wal = 0
    rw [integral_wal measurable_walB]
    norm_num [walB]

theorem integral_walPsi_mul (r r' : Fin 2) :
    ∫ x, walPsi r x * walPsi r' x ∂wal = if r = r' then (1 : ℝ) else 0 := by
  rcases fin_two_cases r with h | h <;> rcases fin_two_cases r' with h' | h' <;> rw [h, h']
  · show ∫ x, walA x * walA x ∂wal = _
    rw [integral_wal (f := fun x => walA x * walA x) (measurable_walA.mul measurable_walA)]
    norm_num [walA]
  · show ∫ x, walA x * walB x ∂wal = _
    rw [integral_wal (f := fun x => walA x * walB x) (measurable_walA.mul measurable_walB)]
    norm_num [walA, walB]
  · show ∫ x, walB x * walA x ∂wal = _
    rw [integral_wal (f := fun x => walB x * walA x) (measurable_walB.mul measurable_walA)]
    norm_num [walA, walB]
  · show ∫ x, walB x * walB x ∂wal = _
    rw [integral_wal (f := fun x => walB x * walB x) (measurable_walB.mul measurable_walB)]
    norm_num [walB]

/-! ### The `halg` model -/

def rhoW : Fin 2 → Fin 2 → Fin 2 := fun γ i => if i = 1 then γ else 0

def tagW : Fin 2 → Fin 2 := fun γ => rhoW γ 1

def rIdxW : Fin 2 → ℕ × ℕ → Fin 2 := fun γ v => if v.1 = 0 then 0 else γ

def sitesW : Fin 2 → Fin 4 → Finset (ℕ × ℕ) :=
  fun _ t => (Finset.univ.erase (1 : Fin 2)).image (scoord t)

noncomputable def arrW : Fin 2 → Fin 4 → Fin 3 → ℝ :=
  fun _ t j => if t ∈ completedAt scoord sstep (j : ℕ) then cwit t else 0

noncomputable def lamW : Fin 2 → ℝ := fun γ => (γ : ℝ) + 1

def wsiteW : ℕ → ℕ × ℕ := fun κ => if κ = 0 then (0, 0) else (1, κ)

theorem hw_W : ∀ κ < 3, ∀ t ∈ completedAt scoord sstep κ, scoord t 1 = wsiteW κ := by
  intro κ hκ
  interval_cases κ <;> decide

theorem hwstep_W : ∀ κ < 3, κ ≤ sstep (wsiteW κ) := by
  intro κ hκ
  interval_cases κ <;> decide

theorem hrev_W : ∀ κ < 3, ∀ t ∈ completedAt scoord sstep κ, ∀ i : Fin 2, i ≠ 1 →
    sstep (scoord t i) < κ := by
  intro κ hκ
  interval_cases κ <;> decide

theorem completedAt_two : completedAt scoord sstep 2 = ({2, 3} : Finset (Fin 4)) := by decide

theorem rhoW_ne : rhoW 0 1 ≠ rhoW 1 1 := by decide

theorem hrIdx_W : ∀ (γ : Fin 2) (t : Fin 4) (i : Fin 2), i ≠ 1 →
    rIdxW γ (scoord t i) = rhoW γ i := by
  intro γ t i hi
  have hi0 : i = 0 := by
    rcases fin_two_cases i with h | h
    · exact h
    · exact absurd h hi
  subst hi0
  rfl


theorem halg_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      mdsCondVariance (fun _ => 3)
          (rowDiff P (fun _ => ξ) (fun _ => scoord)
            (fun _ => Alg.multiKernel walPsi rhoW lamW) (fun _ => cwit) (fun _ => sstep)
            (fun _ => 3))
          (rowSigma (fun _ => ξ) (fun _ => sstep) (fun _ => 3)) P 0
        =ᵐ[P] (fun ω => Var.quadForm ξ walPsi sitesW rIdxW arrW tagW lamW ω + 0)
    ∧ completedAt scoord sstep 1 = ({0, 1} : Finset (Fin 4))
    ∧ completedAt scoord sstep 2 = ({2, 3} : Finset (Fin 4))
    ∧ rhoW 0 1 ≠ rhoW 1 1 := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) wal
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = wal := fun v => (hlawξ v).map_eq
  have hbs : IsBasisSystem P ξ walPsi (Set.univ : Set (Fin 2)) 2 :=
    Step2.isBasisSystem_of_law hmeasξ measurable_walPsi hindepξ hlaw abs_walPsi_le
      (fun r _ => integral_walPsi r) integral_walPsi_mul
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, completedAt_one, completedAt_two, rhoW_ne⟩
  exact Alg.halg_of_multiKernel (U := fun _ => ξ) (coord := fun _ => scoord)
    (g := fun _ => Alg.multiKernel walPsi rhoW lamW) (c := fun _ => cwit)
    (step := fun _ => sstep) (k := fun _ => 3) (n := 0)
    (sites := sitesW) (rIdx := rIdxW) (arr := arrW) (tag := tagW)
    (ρ := rhoW) (lam := lamW) (kstar := 1) (wsite := wsiteW) (cellc := 0)
    hbs scoord_injective (fun _ _ => Set.mem_univ _) rfl
    hw_W hwstep_W hrev_W (fun _ _ => Iff.rfl) (fun _ _ => rfl) hrIdx_W (fun _ _ _ => rfl) rfl


/-! ### Models for `hstep4` -/

/-- `s_n²(L)/n` for a design with two levels, `σ_e² = 2`, `τ_e²(L) = 1/2`, `‖W^{(e)}_c‖_F² = n`
and a cell term of `1`, so `σ²_{n,L} = 3 + 1/n`. -/
noncomputable def scW : ℕ → ℝ := fun n => Real.sqrt ((3 * (n : ℝ) + 1) / (n : ℝ))

/-- `c'S_nc` of the same design: `4 + 1/n`. -/
noncomputable def SnW : ℕ → ℝ := fun n => (4 * (n : ℝ) + 1) / (n : ℝ)

theorem tendsto_SnW : Tendsto SnW atTop (𝓝 4) := by
  have h : Tendsto (fun n : ℕ => (4 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 (4 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at h
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  show (4 : ℝ) + 1 / (n : ℝ) = SnW n
  rw [SnW]
  field_simp

/-- `hstep4` on a design with two levels, `σ_e² = 2`, `τ_e²(L) = 1/2`, a positive cell term,
`c'S_nc → 4`, and `δ(L) = 3/2`. -/
theorem hstep4_witness : ∀ᶠ n : ℕ in atTop, |scW n ^ 2 - 4| ≤ 3 / 2 := by
  refine Alg.hstep4_of_varcomp Finset.univ (fun _ : Fin 2 => (2 : ℝ)) (fun _ => 1 / 2)
    (fun n _ => (n : ℝ)) (fun _ => 1) 1 scW SnW ?_ ?_ (fun _ _ => by norm_num)
    (fun _ _ _ => by positivity) (fun _ _ _ => by norm_num) tendsto_SnW ?_
  · intro n hn
    have hnn : (0 : ℝ) ≤ (3 * (n : ℝ) + 1) / (n : ℝ) := by positivity
    rw [scW, Real.sq_sqrt hnn]
    norm_num [Fin.sum_univ_two]
    ring
  · intro n hn
    rw [SnW]
    norm_num [Fin.sum_univ_two]
    ring
  · norm_num [Fin.sum_univ_two]

/-- The unpadded `δ(L)` equals `1` here, below `3/2`, and tends to `0`. -/
theorem delta_pad_witness :
    Tendsto (fun L : ℕ => 3 * (∑ _e : Fin 2, (1 : ℝ) / ((L : ℝ) + 1)) + 1 / ((L : ℝ) + 1))
        atTop (𝓝 0)
      ∧ ∀ L : ℕ, 3 * (∑ _e : Fin 2, (1 : ℝ) / ((L : ℝ) + 1))
        < 3 * (∑ _e : Fin 2, (1 : ℝ) / ((L : ℝ) + 1)) + 1 / ((L : ℝ) + 1) := by
  refine ⟨Alg.tendsto_delta_pad Finset.univ 3 (fun _ L => 1 / ((L : ℝ) + 1)) (fun _ _ => ?_),
    Alg.lt_delta_pad Finset.univ 3 (fun _ L => 1 / ((L : ℝ) + 1))⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-! ### Models for `hstep5` -/

/-- The untruncated kernel: twice the retained one, so the tail is the retained kernel and the
`L²` gap is positive. -/
noncomputable def Gw : (Fin 2 → ℝ) → ℝ := fun u => 2 * Step2.prodKernel walPsi (rhoW 1) u

/-- The retained kernel `h^{(e)}_L`. -/
noncomputable def gw : (Fin 2 → ℝ) → ℝ := fun u => Step2.prodKernel walPsi (rhoW 1) u

theorem Gw_sub_gw : Gw - gw = Step2.prodKernel walPsi (rhoW 1) := by
  funext u
  show 2 * Step2.prodKernel walPsi (rhoW 1) u - Step2.prodKernel walPsi (rhoW 1) u = _
  ring

/-- `hstep5` at one level with the bound attained: four sub-tuples, coefficients `(t+1)/2`,
`σ_{n,L} = 1/2` and tail second moment `1`, so the gap is `15/2`. -/
theorem hstep5_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∫ ω, (degenSum ξ scoord Gw (fun t => cwit t / 2) ω
        - (1 / 2) * degenSum ξ scoord gw cwit ω) ^ 2 ∂P ≤ 15 / 2)
    ∧ (∀ t : Fin 4, ∫ ω, degenTerm ξ scoord (Gw - gw) t ω ^ 2 ∂P = 1) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) wal
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = wal := fun v => (hlawξ v).map_eq
  have hbs : IsBasisSystem P ξ walPsi (Set.univ : Set (Fin 2)) 2 :=
    Step2.isBasisSystem_of_law hmeasξ measurable_walPsi hindepξ hlaw abs_walPsi_le
      (fun r _ => integral_walPsi r) integral_walPsi_mul
  have hmom : ∀ t : Fin 4, ∫ ω, degenTerm ξ scoord (Gw - gw) t ω ^ 2 ∂P = 1 := by
    intro t
    rw [Gw_sub_gw]
    exact Step2.integral_degenTerm_prodKernel_sq hbs (scoord_injective t) (rhoW 1)
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, hmom⟩
  refine Alg.hstep5_of_tail (G := Gw) (g := gw) (cfull := fun t => cwit t / 2)
    hbs.measurable_latent hbs.indep ?_ ?_ ?_ hsept_scoord hmom (fun _ => rfl)
    (fun t => by ring) ?_
  · rw [Gw_sub_gw]
    exact Step2.measurable_prodKernel measurable_walPsi (rhoW 1)
  · intro t
    rw [Gw_sub_gw]
    exact Step2.memLp_degenTerm_prodKernel hbs scoord t (rhoW 1)
  · intro t e' hne
    rw [Gw_sub_gw]
    exact Step2.condExp_degenTerm_prodKernel_eq_zero hbs (scoord_injective t)
      (fun _ => Set.mem_univ _) e' hne
  · norm_num [cwit, Fin.sum_univ_four]

/-- `hstep5` summed over two levels of arities `1` and `2`, with the bound attained: the tail
kernel is the full kernel, so `τ_e²(L) = 1` at both levels and `∑_e τ_e²(L)∑_tc²_t = 1`. -/
theorem hstep5_multi_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∫ ω, (multiDegenSum ξ mcoord (fun l x => 2 * mker l x) (fun _ _ => (1 : ℝ) / 2) ω
        - (1 / 2) * multiDegenSum ξ mcoord mker mc ω) ^ 2 ∂P ≤ 1)
    ∧ (∀ (l : Fin 2) (t : mTup l), ∫ ω, degenTerm ξ (mcoord l) (mker l) t ω ^ 2 ∂P = 1)
    ∧ Fintype.card (mIota 0) ≠ Fintype.card (mIota 1) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, mhone hmeasξ hindepξ hlawξ, by decide⟩
  refine Alg.hstep5_of_tail_multi (G := fun l x => 2 * mker l x) (g := mker) (d := mker)
    (cfull := fun _ _ => (1 : ℝ) / 2) (taus := fun _ => 1)
    hmeasξ hindepξ ?_ measurable_mker (mhsq hmeasξ hlawξ) (mhdeg hmeasξ hindepξ hlawξ) msep
    (mhone hmeasξ hindepξ hlawξ) (fun _ => rfl) (fun l t => by norm_num [mc]) ?_
  · intro l
    funext x
    show mker l x = 2 * mker l x - mker l x
    ring
  · norm_num [Fin.sum_univ_two]

end Witness

section ComposeAlg

open DegenerateSum CLTMartingale CLTMartingale.Var StatLean.TimeSeries

/-- `scalar_clt_of_truncation_scaled` with `halg`, `hstep4` and `hstep5` derived from the
components, their multi-indices and coefficients, the revealing order, the design values of
`s_n²(L)` and `nc'S_nc`, and the tail second moment `τ_e²(L)`. Stated for the latent array, with
`hcellc : cellc L n = 0`. -/
theorem scalar_clt_of_truncation_alg
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {T : Type*} [Fintype T] [DecidableEq T]
    {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site K N → Ω → ℝ}
    {sites : ∀ (_n : ℕ), Γ → T → Finset (Site K N)}
    {rIdx : ∀ _n : ℕ, Γ → Site K N → R}
    {lev : Γ → Finset K} {pt : ∀ (_n : ℕ), Γ → T → K → Site K N}
    {lam : ℕ → Γ → ℝ} {cellc cellRaw s2 mom cutmax totmax : ℕ → ℕ → ℝ}
    {coord : ℕ → T → ι → Site K N} {g : ℕ → ℕ → (ι → ℝ) → ℝ} {cf : ℕ → ℕ → T → ℝ}
    {stp : ℕ → Site K N → ℕ} {kk : ℕ → ℕ}
    {arr arrRaw : ∀ (_L n : ℕ), Γ → T → Fin (kk n) → ℝ}
    {xi : ℕ → Ω → ℝ} {sc : ℕ → ℕ → ℝ} {del : ℕ → ℝ} {sig2 : ℝ}
    -- the components, their multi-indices, the ordering and its `k⋆`
    {rho : Γ → ι → R} {kstar : ι} {wsite : ℕ → ℕ → Site K N}
    -- the design values, level by level
    {E : Type*} (Es : Finset E) (sig : E → ℝ) (tau : ℕ → E → ℝ) (W : ℕ → E → ℝ)
    (cell Sn : ℕ → ℝ) (Cw : ℝ)
    -- the untruncated kernel and its tail
    {G : ℕ → (ι → ℝ) → ℝ} {cfull : ℕ → T → ℝ} {taus : ℕ → ℕ → ℝ}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hg : ∀ L n, Measurable (g L n))
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdeg : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : T), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x y : T) (a b : K),
      pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : T), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : T), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinj : ∀ (n : ℕ) (q : Γ) (x y : T), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x y : T), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ L, ∑ γ, lam L γ ^ 2 ≤ 1)
    (hcut : ∀ (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr L n γ) * (Matrix.of (arr L n γ))ᵀ) ≤ cutmax L n)
    (hcutA : ∀ (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr L n q)))ᵀ) ≤ cutmax L n)
    (htot : ∀ (L n : ℕ) (γ : Γ), rectFrobSq (arr L n γ) ≤ totmax L n)
    (hs2def : ∀ L n, s2 L n = (∑ γ, lam L γ ^ 2 * rectFrobSq (arrRaw L n γ)) + cellRaw L n)
    (hs2pos : ∀ L n, 0 < s2 L n)
    (harr : ∀ (L n : ℕ) (γ : Γ) (s : T) (i : Fin (kk n)),
      arr L n γ s i = arrRaw L n γ s i / Real.sqrt (s2 L n))
    (hcell : ∀ L n, cellc L n = cellRaw L n / s2 L n)
    (hrate : ∀ L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card K)
          * (cutmax L n * totmax L n)) atTop (𝓝 0))
    (hlind : ∀ (L : ℕ) (ε : ℝ), 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P U coord (g L) (cf L) stp kk n i ω|},
        (rowDiff P U coord (g L) (cf L) stp kk n i ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsig2 : 0 < sig2) (hxi : ∀ n, MemLp (xi n) 2 P)
    (hTr : ∀ L n, MemLp (degenSum (U n) (coord n) (g L n) (cf L n)) 2 P)
    (hsc : ∀ L n, 0 ≤ sc L n) (hdel : Tendsto del atTop (𝓝 0))
    (hsept : ∀ (n : ℕ) (t s : T), t ≠ s →
      (∃ k : ι, coord n s k ∉ tupleSupport (coord n) t) ∨
      (∃ k : ι, coord n t k ∉ tupleSupport (coord n) s))
    (hmom : ∀ L n t, ∫ ω, degenTerm (U n) (coord n) (g L n) t ω ^ 2 ∂P = mom L n)
    (hcfmom : ∀ L n, (∑ t : T, cf L n t ^ 2) * mom L n ≤ 1)
    -- `halg`
    (hcellc : ∀ L n, cellc L n = 0)
    (hgdef : ∀ L n, g L n = Alg.multiKernel ψ rho (lam L))
    (hinjc : ∀ n t, Function.Injective (coord n t))
    (hrhopos : ∀ γ i, rho γ i ∈ Rpos)
    (hwsite : ∀ (n : ℕ), ∀ κ < kk n, ∀ t ∈ completedAt (coord n) (stp n) κ,
      coord n t kstar = wsite n κ)
    (hwstep : ∀ (n : ℕ), ∀ κ < kk n, κ ≤ stp n (wsite n κ))
    (hrev : ∀ (n : ℕ), ∀ κ < kk n, ∀ t ∈ completedAt (coord n) (stp n) κ, ∀ i : ι, i ≠ kstar →
      stp n (coord n t i) < κ)
    (htag : ∀ γ γ' : Γ, tag γ = tag γ' ↔ rho γ kstar = rho γ' kstar)
    (hsitesdef : ∀ (n : ℕ) (γ : Γ) (t : T),
      sites n γ t = (Finset.univ.erase kstar).image (coord n t))
    (hrIdxdef : ∀ (n : ℕ) (γ : Γ) (t : T) (i : ι), i ≠ kstar →
      rIdx n γ (coord n t i) = rho γ i)
    (harrdef : ∀ (L n : ℕ) (γ : Γ) (t : T) (j : Fin (kk n)),
      arr L n γ t j = if t ∈ completedAt (coord n) (stp n) (j : ℕ) then cf L n t else 0)
    -- `hstep4`, from the variance comparison and the design limit
    (hscdef : ∀ (L : ℕ), ∀ n : ℕ, 0 < n →
      sc L n ^ 2 = ((∑ e ∈ Es, (sig e - tau L e) * W n e) + cell n) / (n : ℝ))
    (hSndef : ∀ n : ℕ, 0 < n → Sn n = ((∑ e ∈ Es, sig e * W n e) + cell n) / (n : ℝ))
    (htaunn : ∀ (L : ℕ), ∀ e ∈ Es, 0 ≤ tau L e) (hWnn : ∀ (n : ℕ), ∀ e ∈ Es, 0 ≤ W n e)
    (hWb : ∀ (n : ℕ), ∀ e ∈ Es, W n e ≤ Cw * (n : ℝ))
    (hSn : Tendsto Sn atTop (𝓝 sig2)) (hDdel : ∀ L, Cw * ∑ e ∈ Es, tau L e < del L)
    -- `hstep5`, the `L²` gap
    (hGg : ∀ L n, Measurable (G n - g L n))
    (hsqd : ∀ L n t, MemLp (degenTerm (U n) (coord n) (G n - g L n) t) 2 P)
    (hdegd : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (G n - g L n) t |
        latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hmomd : ∀ L n t, ∫ ω, degenTerm (U n) (coord n) (G n - g L n) t ω ^ 2 ∂P = taus L n)
    (hxifull : ∀ (n : ℕ) (ω : Ω), xi n ω = degenSum (U n) (coord n) (G n) (cfull n) ω)
    (hscale : ∀ (L n : ℕ) (t : T), sc L n * cf L n t = cfull n t)
    (hgapb : ∀ L n, (∑ t : T, cfull n t ^ 2) * taus L n ≤ del L) :
    TendstoInDistribution xi atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal sig2)) := by
  refine scalar_clt_of_truncation_scaled (S := fun _ _ => T) (Ix := fun n => Fin (kk n))
    (tag := tag) (arr := arr) (arrRaw := arrRaw) (lev := lev) (pt := pt) (lam := lam)
    (cellc := cellc) (cellRaw := cellRaw) (s2 := s2) (mom := mom) (cutmax := cutmax)
    (totmax := totmax) (sc := sc) (del := del)
    hbs hg hsq hdeg hN hsite hptc hptf hpos hinj hsep hlam hcut hcutA htot hs2def hs2pos
    harr hcell ?_ hrate hlind hsig2 hxi hTr hsc hdel hsept hmom hcfmom ?_ ?_
  · intro L n
    exact Alg.halg_of_multiKernel (U := U) (coord := coord) (g := g L) (c := cf L)
      (step := stp) (k := kk) (n := n) (sites := sites n) (rIdx := rIdx n) (arr := arr L n)
      (tag := tag) (ρ := rho) (lam := lam L) (kstar := kstar) (wsite := wsite n)
      (cellc := cellc L n) (hbs n) (hinjc n) hrhopos (hgdef L n) (hwsite n) (hwstep n)
      (hrev n) htag (hsitesdef n) (hrIdxdef n) (harrdef L n) (hcellc L n)
  · intro L
    exact Alg.hstep4_of_varcomp Es sig (tau L) W cell Cw (sc L) Sn (hscdef L) hSndef
      (htaunn L) hWnn hWb hSn (hDdel L)
  · intro L
    refine Filter.Eventually.of_forall fun n => ?_
    exact Alg.hstep5_of_tail (G := G n) (g := g L n) (cfull := cfull n)
      (hbs n).measurable_latent (hbs n).indep (hGg L n) (hsqd L n) (hdegd L n) (hsept n)
      (hmomd L n) (hxifull n) (hscale L n) (hgapb L n)

end ComposeAlg

/-! ### The Lindeberg condition for a sum of product kernels, and the cell half

The truncated kernel `h^{(e)}_L = ∑_𝐫λ_𝐫⨂_kψ_{r_k}` is a finite sum of products. For a fixed
component the fourth-moment bound of `integral_pow_four_irregular_le` applies, and the components
are recombined by `(∑_γa_γ)⁴ ≤ |Γ|³∑_γa_γ⁴` (`integral_pow_four_multiKernel_le`). The design
condition `hdesign` is unchanged, the extra constant being absorbed. In
`lindeberg_rowDiff_multiKernel_of_basis`, the independence, mean and bound conditions are read off
`IsBasisSystem`. -/

section Lind3

open DegenerateSum CLTMartingale


/-- `(∑_{i∈s}a_i)⁴ ≤ |s|³∑_{i∈s}a_i⁴`: Cauchy--Schwarz twice. -/
theorem pow_four_sum_le_card_pow_three {κ : Type*} (s : Finset κ) (f : κ → ℝ) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h1 : (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : (∑ i ∈ s, f i ^ 2) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i ^ 2) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  calc (∑ i ∈ s, f i) ^ 4 = ((∑ i ∈ s, f i) ^ 2) ^ 2 := by ring
    _ ≤ ((s.card : ℝ) * ∑ i ∈ s, f i ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, (f i ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
        rw [Finset.sum_congr rfl fun i _ => (by ring : (f i ^ 2) ^ 2 = f i ^ 4)]
        ring

/-- The fourth-moment bound for a linear combination of `|Γ|` multilinear forms: each component
is bounded by `integral_pow_four_irregular_le`, and the components are recombined by
`pow_four_sum_le_card_pow_three`. -/
theorem integral_pow_four_multiKernel_le
    {Γ : Type*} [Fintype Γ] {j : ℕ} {I : Fin j → Type*} [∀ k, Fintype (I k)]
    (ξ : Γ → ∀ k : Fin j, I k → Ω → ℝ) {B : ℝ} (lam : Γ → ℝ)
    (hindep : ∀ γ, iIndepFun (fun p : Σ k : Fin j, I k => ξ γ p.1 p.2) P)
    (hmeas : ∀ γ k i, Measurable (ξ γ k i))
    (hmean : ∀ γ k i, ∫ ω, ξ γ k i ω ∂P = 0)
    (hbdd : ∀ γ k i, ∀ᵐ ω ∂P, |ξ γ k i ω| ≤ B)
    {T : Type*} [Fintype T] [DecidableEq T] {idx : T → ∀ k, I k}
    (hinj : Function.Injective idx) (cc : T → ℝ) (Rst : Finset T) :
    ∫ ω, (∑ t ∈ Rst, cc t * ∑ γ, lam γ * ∏ k, ξ γ k (idx t k) ω) ^ 4 ∂P
      ≤ (Fintype.card Γ : ℝ) ^ 3 * (∑ γ, lam γ ^ 4)
          * ((3 * B ^ 4) ^ j * (∑ t ∈ Rst, cc t ^ 2) ^ 2) := by
  classical
  -- the component multilinear forms
  have hMb : ∀ γ : Γ, Multilinear.AEBdd P
      (fun ω => ∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω) := by
    intro γ
    exact Multilinear.AEBdd.sum
      (fun t => (Multilinear.AEBdd.const (cc t)).mul
        (Multilinear.AEBdd.prod (fun k => ⟨B, hbdd γ k (idx t k)⟩) Finset.univ)) Rst
  have hMmeas : ∀ γ : Γ, Measurable (fun ω => ∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω) :=
    fun γ => Finset.measurable_sum _ fun t _ =>
      measurable_const.mul (Finset.measurable_prod _ fun k _ => hmeas γ k (idx t k))
  have hMint : ∀ γ : Γ, Integrable
      (fun ω => lam γ ^ 4 * (∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω) ^ 4) P := by
    intro γ
    exact (((hMb γ).pow 4).integrable ((hMmeas γ).pow_const 4)).const_mul (lam γ ^ 4)
  -- the pointwise bound
  have hswap : ∀ ω : Ω, (∑ t ∈ Rst, cc t * ∑ γ, lam γ * ∏ k, ξ γ k (idx t k) ω)
      = ∑ γ : Γ, lam γ * ∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω := by
    intro ω
    calc ∑ t ∈ Rst, cc t * ∑ γ, lam γ * ∏ k, ξ γ k (idx t k) ω
        = ∑ t ∈ Rst, ∑ γ : Γ, lam γ * (cc t * ∏ k, ξ γ k (idx t k) ω) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun γ _ => by ring
      _ = ∑ γ : Γ, ∑ t ∈ Rst, lam γ * (cc t * ∏ k, ξ γ k (idx t k) ω) := Finset.sum_comm
      _ = ∑ γ : Γ, lam γ * ∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω := by
          exact Finset.sum_congr rfl fun γ _ => (Finset.mul_sum _ _ _).symm
  have hpt : ∀ ω : Ω, (∑ t ∈ Rst, cc t * ∑ γ, lam γ * ∏ k, ξ γ k (idx t k) ω) ^ 4
      ≤ (Fintype.card Γ : ℝ) ^ 3
        * ∑ γ : Γ, lam γ ^ 4 * (∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω) ^ 4 := by
    intro ω
    rw [hswap ω]
    refine le_trans (pow_four_sum_le_card_pow_three Finset.univ
      (fun γ => lam γ * ∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω)) (le_of_eq ?_)
    rw [Finset.card_univ]
    congr 1
    exact Finset.sum_congr rfl fun γ _ => by ring
  -- integrate
  have hQnn : (0 : ℝ) ≤ (3 * B ^ 4) ^ j * (∑ t ∈ Rst, cc t ^ 2) ^ 2 := by positivity
  have hbound : ∀ γ : Γ, ∫ ω, (∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω) ^ 4 ∂P
      ≤ (3 * B ^ 4) ^ j * (∑ t ∈ Rst, cc t ^ 2) ^ 2 := fun γ =>
    integral_pow_four_irregular_le (ξ γ) (hindep γ) (hmeas γ) (hmean γ) (hbdd γ) hinj cc Rst
  calc ∫ ω, (∑ t ∈ Rst, cc t * ∑ γ, lam γ * ∏ k, ξ γ k (idx t k) ω) ^ 4 ∂P
      ≤ ∫ ω, ((Fintype.card Γ : ℝ) ^ 3
          * ∑ γ : Γ, lam γ ^ 4 * (∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω) ^ 4) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
          ((integrable_finsetSum _ fun γ _ => hMint γ).const_mul _)
          (Filter.Eventually.of_forall hpt)
    _ = (Fintype.card Γ : ℝ) ^ 3
          * ∑ γ : Γ, lam γ ^ 4 * ∫ ω, (∑ t ∈ Rst, cc t * ∏ k, ξ γ k (idx t k) ω) ^ 4 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun γ _ => hMint γ]
        exact congrArg _ (Finset.sum_congr rfl fun γ _ => integral_const_mul _ _)
    _ ≤ (Fintype.card Γ : ℝ) ^ 3
          * ∑ γ : Γ, lam γ ^ 4 * ((3 * B ^ 4) ^ j * (∑ t ∈ Rst, cc t ^ 2) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun γ _ => ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (hbound γ) (by positivity)
    _ = (Fintype.card Γ : ℝ) ^ 3 * (∑ γ, lam γ ^ 4)
          * ((3 * B ^ 4) ^ j * (∑ t ∈ Rst, cc t ^ 2) ^ 2) := by
        rw [← Finset.sum_mul, mul_assoc]


/-- The conditional Lindeberg condition `hlind` for a kernel that is a finite sum of products
of independent mean-zero factors, under the same design condition `hdesign`. -/
theorem lindeberg_rowDiff_of_multiKernel
    {V ι T : Type*} [Fintype ι] [Fintype T] [DecidableEq T]
    {Γ : Type*} [Fintype Γ]
    {U : ℕ → V → Ω → ℝ} {coord : ℕ → T → ι → V} {g : ℕ → (ι → ℝ) → ℝ}
    {cf : ℕ → T → ℝ} {stp : ℕ → V → ℕ} {kk : ℕ → ℕ}
    {j : ℕ} {I : ℕ → Fin j → Type*} [∀ n k, Fintype (I n k)]
    {ξ : ∀ (n : ℕ) (_γ : Γ) (k : Fin j), I n k → Ω → ℝ} {B : ℝ} {lam : Γ → ℝ}
    {idx : ∀ _n : ℕ, T → ∀ k : Fin j, I _n k}
    (hU : ∀ n v, Measurable (U n v)) (hindepU : ∀ n, iIndepFun (U n) P)
    (hg : ∀ n, Measurable (g n))
    (hint : ∀ n t, Integrable (degenTerm (U n) (coord n) (g n) t) P)
    (hdeg : ∀ (n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hprod : ∀ n t ω, degenTerm (U n) (coord n) (g n) t ω
      = ∑ γ, lam γ * ∏ k, ξ n γ k (idx n t k) ω)
    (hindep : ∀ n γ, iIndepFun (fun p : Σ k : Fin j, I n k => ξ n γ p.1 p.2) P)
    (hmeas : ∀ n γ k i, Measurable (ξ n γ k i))
    (hmean : ∀ n γ k i, ∫ ω, ξ n γ k i ω ∂P = 0)
    (hbdd : ∀ n γ k i, ∀ᵐ ω ∂P, |ξ n γ k i ω| ≤ B)
    (hinj : ∀ n, Function.Injective (idx n))
    (hmeasrow : ∀ n i, Measurable (rowDiff P U coord g cf stp kk n i))
    (hint4 : ∀ n i, Integrable (fun ω => rowDiff P U coord g cf stp kk n i ω ^ 4) P)
    (hdesign : Tendsto (fun n => (3 * B ^ 4) ^ j *
        ∑ i : Fin (kk n),
          (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf n t ^ 2) ^ 2) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P U coord g cf stp kk n i ω|},
        (rowDiff P U coord g cf stp kk n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  refine lindeberg_of_tendsto_sum_pow_four hmeasrow hint4 ?_
  refine squeeze_zero (g := fun n => ((Fintype.card Γ : ℝ) ^ 3 * ∑ γ, lam γ ^ 4) *
      ((3 * B ^ 4) ^ j *
        ∑ i : Fin (kk n),
          (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf n t ^ 2) ^ 2))
    (fun n => ?_) (fun n => ?_) ?_
  · exact Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by positivity
  · have hrw : ∀ cst : ℝ, cst *
        ((3 * B ^ 4) ^ j *
          ∑ i : Fin (kk n),
            (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf n t ^ 2) ^ 2)
        = ∑ i : Fin (kk n), cst *
            ((3 * B ^ 4) ^ j *
              (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf n t ^ 2) ^ 2) := by
      intro cst
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hrw]
    refine Finset.sum_le_sum fun i _ => ?_
    have hae : ∀ᵐ ω ∂P, rowDiff P U coord g cf stp kk n i ω ^ 4
        = (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ),
            cf n t * ∑ γ, lam γ * ∏ k, ξ n γ k (idx n t k) ω) ^ 4 := by
      filter_upwards [degenDiff_eq_sum_completedAt (μ := P) (U := U n) (coord := coord n)
        (g := g n) (c := cf n) (step := stp n) (hU n) (hindepU n) (hg n) (hint n) (hdeg n)
        (i : ℕ)] with ω hω
      have h : rowDiff P U coord g cf stp kk n i ω
          = ∑ t ∈ completedAt (coord n) (stp n) (i : ℕ),
              cf n t * ∑ γ, lam γ * ∏ k, ξ n γ k (idx n t k) ω := by
        rw [show rowDiff P U coord g cf stp kk n i ω
          = degenDiff P (U n) (coord n) (g n) (cf n) (stp n) (i : ℕ) ω from rfl, hω]
        exact Finset.sum_congr rfl fun t _ => by rw [hprod n t ω]
      rw [h]
    rw [integral_congr_ae hae]
    exact integral_pow_four_multiKernel_le (ξ n) lam (hindep n) (hmeas n) (hmean n) (hbdd n)
      (hinj n) (cf n) (completedAt (coord n) (stp n) (i : ℕ))
  · simpa using hdesign.const_mul ((Fintype.card Γ : ℝ) ^ 3 * ∑ γ, lam γ ^ 4)

/-- `lindeberg_rowDiff_of_multiKernel` at the kernel `h^{(e)}_L = ∑_𝐫λ_𝐫⨂_kψ_{r_k}`, with the
independence, mean and bound conditions read off `IsBasisSystem`. `eqv` enumerates the level
`e`, `site` indexes the latent variables `U^{(k)}_i` by dimension, and `sidx` gives the index in
each dimension carried by a sub-tuple. -/
theorem lindeberg_rowDiff_multiKernel_of_basis
    {V T : Type*} [Fintype T] [DecidableEq T] {ι : Type*} [Fintype ι]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] {ρ : Γ → ι → R} {lam : Γ → ℝ}
    {U : ℕ → V → Ω → ℝ} {coord : ℕ → T → ι → V}
    {cf : ℕ → T → ℝ} {stp : ℕ → V → ℕ} {kk : ℕ → ℕ}
    {j : ℕ} (eqv : Fin j ≃ ι)
    {Idx : ℕ → Fin j → Type*} [∀ n k, Fintype (Idx n k)]
    {site : ∀ (n : ℕ) (k : Fin j), Idx n k → V} {sidx : ∀ _n : ℕ, T → ∀ k : Fin j, Idx _n k}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hrho : ∀ γ i, ρ γ i ∈ Rpos)
    (hsiteinj : ∀ n, Function.Injective (fun p : Σ k : Fin j, Idx n k => site n p.1 p.2))
    (hcoord : ∀ n t k, coord n t (eqv k) = site n k (sidx n t k))
    (hsidxinj : ∀ n, Function.Injective (sidx n))
    (hint : ∀ n t, Integrable
      (degenTerm (U n) (coord n) (CLTMartingale.Alg.multiKernel ψ ρ lam) t) P)
    (hdeg : ∀ (n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (CLTMartingale.Alg.multiKernel ψ ρ lam) t |
        latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hmeasrow : ∀ n i, Measurable (rowDiff P U coord
      (fun _ => CLTMartingale.Alg.multiKernel ψ ρ lam) cf stp kk n i))
    (hint4 : ∀ n i, Integrable (fun ω => rowDiff P U coord
      (fun _ => CLTMartingale.Alg.multiKernel ψ ρ lam) cf stp kk n i ω ^ 4) P)
    (hdesign : Tendsto (fun n => (3 * B₀ ^ 4) ^ j *
        ∑ i : Fin (kk n),
          (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf n t ^ 2) ^ 2) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P U coord
          (fun _ => CLTMartingale.Alg.multiKernel ψ ρ lam) cf stp kk n i ω|},
        (rowDiff P U coord (fun _ => CLTMartingale.Alg.multiKernel ψ ρ lam)
          cf stp kk n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  refine lindeberg_rowDiff_of_multiKernel (I := Idx) (B := B₀) (lam := lam)
    (ξ := fun n γ k i => fun ω => ψ (ρ γ (eqv k)) (U n (site n k i) ω))
    (idx := fun n t k => sidx n t k)
    (fun n v => (hbs n).measurable_latent v) (fun n => (hbs n).indep)
    (fun _ => CLTMartingale.Alg.measurable_multiKernel (hbs 0).measurable_psi ρ lam)
    hint hdeg ?_ ?_ (fun n γ k i => ((hbs n).measurable_psi (ρ γ (eqv k))).comp
      ((hbs n).measurable_latent (site n k i)))
    (fun n γ k i => (hbs n).integral_eq_zero (site n k i) (hrho γ (eqv k)))
    (fun n γ k i => Filter.Eventually.of_forall fun ω => (hbs n).bound _ _)
    hsidxinj hmeasrow hint4 hdesign
  · -- `hprod`: the kernel evaluated at the sub-tuple's latent variables
    intro n t ω
    show CLTMartingale.Alg.multiKernel ψ ρ lam (latentTuple (U n) (coord n) t ω) = _
    refine Finset.sum_congr rfl fun γ _ => ?_
    refine congrArg (fun x => lam γ * x) ?_
    show ∏ i : ι, ψ (ρ γ i) (U n (coord n t i) ω) = _
    refine (Fintype.prod_equiv eqv (fun k => ψ (ρ γ (eqv k)) (U n (site n k (sidx n t k)) ω))
      (fun i => ψ (ρ γ i) (U n (coord n t i) ω)) fun k => ?_).symm
    rw [← hcoord n t k]
  · -- `hindep`: an injective reindexing of the latent family
    intro n γ
    exact (((hbs n).indep.precomp (hsiteinj n)).comp
      (fun p => fun x : ℝ => ψ (ρ γ (eqv p.1)) x)
      (fun p => (hbs n).measurable_psi (ρ γ (eqv p.1))))

/-! ### The directional limit on the array with cell steps

Here the martingale array carries both the latent half and the cell steps, so the truncation
limit is taken on `T_n(L) = ∑_tc_tg(U_t) + ∑_oc'x̃_oε_o`. `halg` is required on the latent half
at `cellc = 0`, and `cellc L n` is the cell constant `∑_o(c'x̃_o)²σ²_ε(o)`. -/

section ComposeCell

open DegenerateSum CLTMartingale CLTMartingale.Var CLTMartingale.Cell StatLean.TimeSeries

/-- `scalar_clt_of_truncation` for the array carrying both the latent half and the cell steps
`∑_oc'x̃_oε_o`; `halg` is required on the latent half at `cellc = 0`. -/
theorem scalar_clt_of_truncation_cell
    {ι : Type*} [Fintype ι] [Nonempty ι] {T : Type*} [Fintype T] [DecidableEq T]
    {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {S : ℕ → Γ → Type*} [∀ n γ, Fintype (S n γ)]
    {Ix : ℕ → Type*} [∀ n, Fintype (Ix n)] {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site K N → Ω → ℝ}
    {sites : ∀ (n : ℕ) (γ : Γ), S n γ → Finset (Site K N)}
    {rIdx : ∀ _n : ℕ, Γ → Site K N → R}
    {arr : ∀ (_L n : ℕ) (γ : Γ), S n γ → Ix n → ℝ}
    {lev : Γ → Finset K} {pt : ∀ (n : ℕ) (γ : Γ), S n γ → K → Site K N}
    {lam : ℕ → Γ → ℝ} {cellc cutmax totmax : ℕ → ℕ → ℝ}
    {coord : ℕ → T → ι → Site K N} {g : ℕ → ℕ → (ι → ℝ) → ℝ} {cf : ℕ → ℕ → T → ℝ}
    {stp : ℕ → Site K N → ℕ} {kk : ℕ → ℕ}
    {ac : ℕ → ℕ → ℕ → ℝ} {eps : ℕ → ℕ → Ω → ℝ} {sg : ℕ → ℕ → ℝ} {mc : ℕ → ℕ}
    {xi : ℕ → Ω → ℝ} {sc : ℕ → ℕ → ℝ} {del : ℕ → ℝ} {sig2 : ℝ}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hg : ∀ L n, Measurable (g L n))
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdeg : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hcm : IsCellModel P (latentBase U stp kk) eps sg mc)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : S n q), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q') (a b : K),
      pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : S n q), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinj : ∀ (n : ℕ) (q : Γ) (x y : S n q), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x : S n q) (y : S n q'), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ L, ∑ γ, lam L γ ^ 2 ≤ 1)
    (hcut : ∀ (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr L n γ) * (Matrix.of (arr L n γ))ᵀ) ≤ cutmax L n)
    (hcutA : ∀ (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr L n q)))ᵀ) ≤ cutmax L n)
    (htot : ∀ (L n : ℕ) (γ : Γ), rectFrobSq (arr L n γ) ≤ totmax L n)
    (hnorm : ∀ L n, (∑ γ, lam L γ ^ 2 * rectFrobSq (arr L n γ)) + cellc L n = 1)
    (hcellc : ∀ L n, cellc L n = cellConst (ac L) sg mc n)
    (halg : ∀ L n,
      mdsCondVariance kk (rowDiff P U coord (g L) (cf L) stp kk) (rowSigma U stp kk) P n
        =ᵐ[P] fun ω =>
          quadForm (U n) ψ (sites n) (rIdx n) (arr L n) tag (lam L) ω + 0)
    (hrate : ∀ L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card K)
          * (cutmax L n * totmax L n)) atTop (𝓝 0))
    (hlind : ∀ (L : ℕ) (ε : ℝ), 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in
          {ω | ε ≤ |totalDiff P U coord (g L) (cf L) stp kk (ac L) eps mc n i ω|},
        (totalDiff P U coord (g L) (cf L) stp kk (ac L) eps mc n i ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsig2 : 0 < sig2) (hxi : ∀ n, MemLp (xi n) 2 P)
    (hTr : ∀ L n, MemLp (fun ω => degenSum (U n) (coord n) (g L n) (cf L n) ω
      + cellSum (ac L) eps mc n ω) 2 P)
    (hsc : ∀ L n, 0 ≤ sc L n) (hdel : Tendsto del atTop (𝓝 0))
    (hsecond : ∀ L n, ∫ ω, (degenSum (U n) (coord n) (g L n) (cf L n) ω
      + cellSum (ac L) eps mc n ω) ^ 2 ∂P ≤ 1)
    (hstep4 : ∀ L, ∀ᶠ n in atTop, |sc L n ^ 2 - sig2| ≤ del L)
    (hstep5 : ∀ L, ∀ᶠ n in atTop,
      ∫ ω, (xi n ω - sc L n * (degenSum (U n) (coord n) (g L n) (cf L n) ω
        + cellSum (ac L) eps mc n ω)) ^ 2 ∂P ≤ del L) :
    TendstoInDistribution xi atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal sig2)) := by
  refine Trunc.tendstoInDistribution_of_l2_approx hsig2 hxi hTr hsc hdel hsecond ?_ hstep4 hstep5
  intro L u
  exact tendsto_charFun_total_of_concentration (S := S) (Ix := Ix) (tag := tag)
    (arr := arr L) (lev := lev) (pt := pt) (lam := lam L) (cellc := cellc L)
    (cutmax := cutmax L) (totmax := totmax L) (a := ac L) (eps := eps) (sg := sg) (m := mc)
    hbs (hg L) (hsq L) (hdeg L) hN hcm hsite hptc hptf hpos hinj hsep (hlam L) (hcut L)
    (hcutA L) (htot L) (hnorm L) (hcellc L) (halg L) (hrate L) (hlind L) u

end ComposeCell

/-! ### The cell half of the Lindeberg sum

`hfourth` is the fourth-moment bound `𝔼[ε_o⁴] ≤ C` (Lemma SM.B.5), and `hdesign` is
`∑_{cell steps}𝔼[D_κ⁴] ≤ C max_o‖x̃_o‖²∑_o‖x̃_o‖²` after division by `s_n⁴(L)`. -/

section CellLind

open DegenerateSum CLTMartingale CLTMartingale.Cell

omit [IsProbabilityMeasure P] in
/-- The Lindeberg condition for the cell steps, from `𝔼[ε_o⁴] ≤ C` and the design
condition `hdesign`. -/
theorem lindeberg_cellDiff_of_fourth
    {a : ℕ → ℕ → ℝ} {eps : ℕ → ℕ → Ω → ℝ} {m : ℕ → ℕ} {C4 : ℝ}
    (hmeas : ∀ n j, Measurable (eps n j))
    (hint4 : ∀ n j, Integrable (fun ω => eps n j ω ^ 4) P)
    (hfourth : ∀ n j, ∫ ω, eps n j ω ^ 4 ∂P ≤ C4)
    (hdesign : Tendsto (fun n => C4 * ∑ j : Fin (m n), a n (j : ℕ) ^ 4) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ j, ∫ ω in {ω | ε ≤ |cellDiff a eps m n j ω|},
        (cellDiff a eps m n j ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hpow : ∀ (n : ℕ) (j : Fin (m n)), (fun ω => cellDiff a eps m n j ω ^ 4)
      = fun ω => a n (j : ℕ) ^ 4 * eps n (j : ℕ) ω ^ 4 := by
    intro n j
    funext ω
    show (a n (j : ℕ) * eps n (j : ℕ) ω) ^ 4 = _
    ring
  refine lindeberg_of_tendsto_sum_pow_four
    (fun n j => (hmeas n (j : ℕ)).const_mul _)
    (fun n j => by rw [hpow n j]; exact (hint4 n (j : ℕ)).const_mul _) ?_
  refine squeeze_zero (g := fun n => C4 * ∑ j : Fin (m n), a n (j : ℕ) ^ 4)
    (fun n => ?_) (fun n => ?_) hdesign
  · exact Finset.sum_nonneg fun j _ => integral_nonneg fun ω => by positivity
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hpow n j, integral_const_mul, mul_comm C4 (a n (j : ℕ) ^ 4)]
    exact mul_le_mul_of_nonneg_left (hfourth n (j : ℕ)) (by positivity)

end CellLind

/-! ### `halg` and `hlind` at the same kernel

`scalar_clt_of_truncation_cell_alg` derives `halg` from `CLTMartingale.Alg.halg_of_multiKernel`
via `CLTMartingale.Cell.condVar_total_of_latent`, with `cellc` the cell constant, and `hlind`
from `lindeberg_rowDiff_multiKernel_of_basis` and `lindeberg_cellDiff_of_fourth`. Its remaining
hypotheses are `hnorm`, `hsecond`, `hTr`, `hstep4` and `hstep5`. -/

section ComposeCellAlg

open DegenerateSum CLTMartingale CLTMartingale.Var CLTMartingale.Cell StatLean.TimeSeries

/-- The directional limit with `halg` and `hlind` derived at the same kernel
`Alg.multiKernel ψ rho (lam L)`, with the cell steps in the array. -/
theorem scalar_clt_of_truncation_cell_alg
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {T : Type*} [Fintype T] [DecidableEq T]
    {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site K N → Ω → ℝ}
    {sites : ∀ (_n : ℕ), Γ → T → Finset (Site K N)}
    {rIdx : ∀ _n : ℕ, Γ → Site K N → R}
    {lev : Γ → Finset K} {pt : ∀ (_n : ℕ), Γ → T → K → Site K N}
    {lam : ℕ → Γ → ℝ} {cellc cutmax totmax : ℕ → ℕ → ℝ}
    {coord : ℕ → T → ι → Site K N} {g : ℕ → ℕ → (ι → ℝ) → ℝ} {cf : ℕ → ℕ → T → ℝ}
    {stp : ℕ → Site K N → ℕ} {kk : ℕ → ℕ}
    {arr : ∀ (_L n : ℕ), Γ → T → Fin (kk n) → ℝ}
    {ac : ℕ → ℕ → ℕ → ℝ} {eps : ℕ → ℕ → Ω → ℝ} {sg : ℕ → ℕ → ℝ} {mc : ℕ → ℕ}
    {xi : ℕ → Ω → ℝ} {sc : ℕ → ℕ → ℝ} {del : ℕ → ℝ} {sig2 : ℝ}
    -- the basis-expansion data
    {rho : Γ → ι → R} {kstar : ι} {wsite : ℕ → ℕ → Site K N}
    -- the multilinear data: the level enumerated, and the latent variables by dimension
    {j : ℕ} (eqv : Fin j ≃ ι)
    {Idx : ℕ → Fin j → Type*} [∀ n k, Fintype (Idx n k)]
    {site : ∀ (n : ℕ) (k : Fin j), Idx n k → Site K N}
    {sidx : ∀ _n : ℕ, T → ∀ k : Fin j, Idx _n k} {C4 : ℝ}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdeg : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hcm : IsCellModel P (latentBase U stp kk) eps sg mc)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : T), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x y : T) (a b : K), pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : T), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : T), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinj : ∀ (n : ℕ) (q : Γ) (x y : T), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x y : T), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ L, ∑ γ, lam L γ ^ 2 ≤ 1)
    (hcut : ∀ (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr L n γ) * (Matrix.of (arr L n γ))ᵀ) ≤ cutmax L n)
    (hcutA : ∀ (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr L n q)))ᵀ) ≤ cutmax L n)
    (htot : ∀ (L n : ℕ) (γ : Γ), rectFrobSq (arr L n γ) ≤ totmax L n)
    (hnorm : ∀ L n, (∑ γ, lam L γ ^ 2 * rectFrobSq (arr L n γ)) + cellc L n = 1)
    (hcellc : ∀ L n, cellc L n = cellConst (ac L) sg mc n)
    (hrate : ∀ L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card K)
          * (cutmax L n * totmax L n)) atTop (𝓝 0))
    -- `halg`
    (hgdef : ∀ L n, g L n = CLTMartingale.Alg.multiKernel ψ rho (lam L))
    (hinjc : ∀ n t, Function.Injective (coord n t))
    (hrhopos : ∀ γ i, rho γ i ∈ Rpos)
    (hwsite : ∀ (n : ℕ), ∀ κ < kk n, ∀ t ∈ completedAt (coord n) (stp n) κ,
      coord n t kstar = wsite n κ)
    (hwstep : ∀ (n : ℕ), ∀ κ < kk n, κ ≤ stp n (wsite n κ))
    (hrev : ∀ (n : ℕ), ∀ κ < kk n, ∀ t ∈ completedAt (coord n) (stp n) κ, ∀ i : ι, i ≠ kstar →
      stp n (coord n t i) < κ)
    (htag : ∀ γ γ' : Γ, tag γ = tag γ' ↔ rho γ kstar = rho γ' kstar)
    (hsitesdef : ∀ (n : ℕ) (γ : Γ) (t : T),
      sites n γ t = (Finset.univ.erase kstar).image (coord n t))
    (hrIdxdef : ∀ (n : ℕ) (γ : Γ) (t : T) (i : ι), i ≠ kstar →
      rIdx n γ (coord n t i) = rho γ i)
    (harrdef : ∀ (L n : ℕ) (γ : Γ) (t : T) (q : Fin (kk n)),
      arr L n γ t q = if t ∈ completedAt (coord n) (stp n) (q : ℕ) then cf L n t else 0)
    -- `hlind`, the latent half
    (hsiteinj : ∀ n, Function.Injective (fun p : Σ k : Fin j, Idx n k => site n p.1 p.2))
    (hcoordsite : ∀ n t k, coord n t (eqv k) = site n k (sidx n t k))
    (hsidxinj : ∀ n, Function.Injective (sidx n))
    (hmeasrow : ∀ L n i, Measurable (rowDiff P U coord (g L) (cf L) stp kk n i))
    (hint4row : ∀ L n i, Integrable
      (fun ω => rowDiff P U coord (g L) (cf L) stp kk n i ω ^ 4) P)
    (hdesign : ∀ L, Tendsto (fun n => (3 * B₀ ^ 4) ^ j *
        ∑ i : Fin (kk n),
          (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf L n t ^ 2) ^ 2) atTop (𝓝 0))
    -- `hlind`, the cell half
    (hepsint4 : ∀ n q, Integrable (fun ω => eps n q ω ^ 4) P)
    (hepsfourth : ∀ n q, ∫ ω, eps n q ω ^ 4 ∂P ≤ C4)
    (hdesignCell : ∀ L, Tendsto (fun n => C4 * ∑ q : Fin (mc n), ac L n (q : ℕ) ^ 4)
      atTop (𝓝 0))
    -- the variance comparison and the truncation gap
    (hsig2 : 0 < sig2) (hxi : ∀ n, MemLp (xi n) 2 P)
    (hTr : ∀ L n, MemLp (fun ω => degenSum (U n) (coord n) (g L n) (cf L n) ω
      + cellSum (ac L) eps mc n ω) 2 P)
    (hsc : ∀ L n, 0 ≤ sc L n) (hdel : Tendsto del atTop (𝓝 0))
    (hsecond : ∀ L n, ∫ ω, (degenSum (U n) (coord n) (g L n) (cf L n) ω
      + cellSum (ac L) eps mc n ω) ^ 2 ∂P ≤ 1)
    (hstep4 : ∀ L, ∀ᶠ n in atTop, |sc L n ^ 2 - sig2| ≤ del L)
    (hstep5 : ∀ L, ∀ᶠ n in atTop,
      ∫ ω, (xi n ω - sc L n * (degenSum (U n) (coord n) (g L n) (cf L n) ω
        + cellSum (ac L) eps mc n ω)) ^ 2 ∂P ≤ del L) :
    TendstoInDistribution xi atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal sig2)) := by
  have hgm : ∀ L n, Measurable (g L n) := by
    intro L n
    rw [hgdef L n]
    exact CLTMartingale.Alg.measurable_multiKernel (hbs 0).measurable_psi rho (lam L)
  refine scalar_clt_of_truncation_cell (S := fun _ _ => T) (Ix := fun n => Fin (kk n))
    (tag := tag) (arr := arr) (lev := lev) (pt := pt) (lam := lam) (cellc := cellc)
    (cutmax := cutmax) (totmax := totmax) (ac := ac) (eps := eps) (sg := sg) (mc := mc)
    (sc := sc) (del := del)
    hbs hgm hsq hdeg hN hcm hsite hptc hptf hpos hinj hsep hlam hcut hcutA htot hnorm hcellc
    ?_ hrate ?_ hsig2 hxi hTr hsc hdel hsecond hstep4 hstep5
  · -- `halg` at the latent half, at `cellc = 0`
    intro L n
    exact CLTMartingale.Alg.halg_of_multiKernel (U := U) (coord := coord) (g := g L)
      (c := cf L) (step := stp) (k := kk) (n := n) (sites := sites n) (rIdx := rIdx n)
      (arr := arr L n) (tag := tag) (ρ := rho) (lam := lam L) (kstar := kstar)
      (wsite := wsite n) (cellc := 0) (hbs n) (hinjc n) hrhopos (hgdef L n) (hwsite n)
      (hwstep n) (hrev n) htag (hsitesdef n) (hrIdxdef n) (harrdef L n) rfl
  · -- `hlind` on the total array
    intro L
    refine CLTMartingale.Cell.lindeberg_total ?_ ?_
    · have h := lindeberg_rowDiff_multiKernel_of_basis (P := P) (ψ := ψ) (Rpos := Rpos)
        (B₀ := B₀) (ρ := rho) (lam := lam L) (U := U) (coord := coord) (cf := cf L)
        (stp := stp) (kk := kk) eqv (Idx := Idx) (site := site) (sidx := sidx)
        hbs hrhopos hsiteinj hcoordsite hsidxinj
        (fun n t => by
          rw [← hgdef L n]; exact (hsq L n t).integrable one_le_two)
        (fun n t e' he' => by rw [← hgdef L n]; exact hdeg L n t e' he')
        (fun n i => by
          have := hmeasrow L n i
          rwa [funext (hgdef L)] at this)
        (fun n i => by
          have := hint4row L n i
          rwa [funext (hgdef L)] at this)
        (hdesign L)
      intro ε hε
      have h2 := h ε hε
      rwa [← funext (hgdef L)] at h2
    · exact lindeberg_cellDiff_of_fourth (a := ac L) (eps := eps) (m := mc) (C4 := C4)
        (fun n q => hcm.meas n q) hepsint4 hepsfourth (hdesignCell L)

end ComposeCellAlg
end Lind3


/-! ### The directional limit with all hypotheses derived

`scalar_clt_of_truncation_cell_full` takes the components with their multi-indices and
coefficients, the revealing order, the site model, the design values of `s_n²(L)` and `nc'S_nc`,
the untruncated kernel with tail second moment `τ_e²(L)`, the cell model and `𝔼[ε_o⁴] ≤ C`, and
derives `halg`, `hlind`, `hTr`, `hsecond`, `hstep4` and `hstep5`. The design conditions `hdesign`
and `hdesignCell` and the regularity conditions `hmeasrow`, `hint4row` and `hepsint4` remain
hypotheses. -/

section ComposeCellFull

open DegenerateSum CLTMartingale CLTMartingale.Var CLTMartingale.Cell StatLean.TimeSeries

/-- The directional limit law for the array carrying both halves of `T_n(L)`, with every
intermediate hypothesis derived. -/
theorem scalar_clt_of_truncation_cell_full
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {T : Type*} [Fintype T] [DecidableEq T]
    {K : Type*} [Fintype K] [DecidableEq K] {N : K → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site K N → Ω → ℝ}
    {sites : ∀ (_n : ℕ), Γ → T → Finset (Site K N)}
    {rIdx : ∀ _n : ℕ, Γ → Site K N → R}
    {lev : Γ → Finset K} {pt : ∀ (_n : ℕ), Γ → T → K → Site K N}
    {lam : ℕ → Γ → ℝ} {cellc cutmax totmax : ℕ → ℕ → ℝ}
    {coord : ℕ → T → ι → Site K N} {g : ℕ → ℕ → (ι → ℝ) → ℝ} {cf : ℕ → ℕ → T → ℝ}
    {stp : ℕ → Site K N → ℕ} {kk : ℕ → ℕ}
    {arr : ∀ (_L n : ℕ), Γ → T → Fin (kk n) → ℝ}
    {ac acFull : ℕ → ℕ → ℕ → ℝ} {eps : ℕ → ℕ → Ω → ℝ} {sg : ℕ → ℕ → ℝ} {mc : ℕ → ℕ}
    {xi : ℕ → Ω → ℝ} {sc : ℕ → ℕ → ℝ} {del : ℕ → ℝ} {sig2 : ℝ}
    -- the basis-expansion data
    {rho : Γ → ι → R} {kstar : ι} {wsite : ℕ → ℕ → Site K N}
    -- the multilinear data
    {j : ℕ} (eqv : Fin j ≃ ι)
    {Idx : ℕ → Fin j → Type*} [∀ n k, Fintype (Idx n k)]
    {site : ∀ (n : ℕ) (k : Fin j), Idx n k → Site K N}
    {sidx : ∀ _n : ℕ, T → ∀ k : Fin j, Idx _n k} {C4 : ℝ}
    -- the design values, level by level
    {E : Type*} (Es : Finset E) (sig : E → ℝ) (tau : ℕ → E → ℝ) (W : ℕ → E → ℝ)
    (cell Sn : ℕ → ℝ) (Cw : ℝ)
    -- the untruncated kernel and its tail
    {G : ℕ → (ι → ℝ) → ℝ} {cfull : ℕ → T → ℝ} {taus : ℕ → ℕ → ℝ}
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdeg : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hcm : IsCellModel P (latentBase U stp kk) eps sg mc)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : T), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x y : T) (a b : K), pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : T), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : T), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinj : ∀ (n : ℕ) (q : Γ) (x y : T), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x y : T), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ L, ∑ γ, lam L γ ^ 2 ≤ 1)
    (hcut : ∀ (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr L n γ) * (Matrix.of (arr L n γ))ᵀ) ≤ cutmax L n)
    (hcutA : ∀ (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr L n q)))ᵀ) ≤ cutmax L n)
    (htot : ∀ (L n : ℕ) (γ : Γ), rectFrobSq (arr L n γ) ≤ totmax L n)
    (hnorm : ∀ L n, (∑ γ, lam L γ ^ 2 * rectFrobSq (arr L n γ)) + cellc L n = 1)
    (hcellc : ∀ L n, cellc L n = cellConst (ac L) sg mc n)
    (hrate : ∀ L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card K)
          * (cutmax L n * totmax L n)) atTop (𝓝 0))
    -- `halg`
    (hgdef : ∀ L n, g L n = CLTMartingale.Alg.multiKernel ψ rho (lam L))
    (hinjc : ∀ n t, Function.Injective (coord n t))
    (hrhopos : ∀ γ i, rho γ i ∈ Rpos)
    (hwsite : ∀ (n : ℕ), ∀ κ < kk n, ∀ t ∈ completedAt (coord n) (stp n) κ,
      coord n t kstar = wsite n κ)
    (hwstep : ∀ (n : ℕ), ∀ κ < kk n, κ ≤ stp n (wsite n κ))
    (hrev : ∀ (n : ℕ), ∀ κ < kk n, ∀ t ∈ completedAt (coord n) (stp n) κ, ∀ i : ι, i ≠ kstar →
      stp n (coord n t i) < κ)
    (htag : ∀ γ γ' : Γ, tag γ = tag γ' ↔ rho γ kstar = rho γ' kstar)
    (hsitesdef : ∀ (n : ℕ) (γ : Γ) (t : T),
      sites n γ t = (Finset.univ.erase kstar).image (coord n t))
    (hrIdxdef : ∀ (n : ℕ) (γ : Γ) (t : T) (i : ι), i ≠ kstar →
      rIdx n γ (coord n t i) = rho γ i)
    (harrdef : ∀ (L n : ℕ) (γ : Γ) (t : T) (q : Fin (kk n)),
      arr L n γ t q = if t ∈ completedAt (coord n) (stp n) (q : ℕ) then cf L n t else 0)
    -- `hlind`, both halves
    (hsiteinj : ∀ n, Function.Injective (fun p : Σ k : Fin j, Idx n k => site n p.1 p.2))
    (hcoordsite : ∀ n t k, coord n t (eqv k) = site n k (sidx n t k))
    (hsidxinj : ∀ n, Function.Injective (sidx n))
    (hmeasrow : ∀ L n i, Measurable (rowDiff P U coord (g L) (cf L) stp kk n i))
    (hint4row : ∀ L n i, Integrable
      (fun ω => rowDiff P U coord (g L) (cf L) stp kk n i ω ^ 4) P)
    (hdesign : ∀ L, Tendsto (fun n => (3 * B₀ ^ 4) ^ j *
        ∑ i : Fin (kk n),
          (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf L n t ^ 2) ^ 2) atTop (𝓝 0))
    (hepsint4 : ∀ n q, Integrable (fun ω => eps n q ω ^ 4) P)
    (hepsfourth : ∀ n q, ∫ ω, eps n q ω ^ 4 ∂P ≤ C4)
    (hdesignCell : ∀ L, Tendsto (fun n => C4 * ∑ q : Fin (mc n), ac L n (q : ℕ) ^ 4)
      atTop (𝓝 0))
    -- `hstep4`, from the variance comparison and the design limit
    (hsig2 : 0 < sig2) (hxi : ∀ n, MemLp (xi n) 2 P) (hsc : ∀ L n, 0 ≤ sc L n)
    (hdel : Tendsto del atTop (𝓝 0))
    (hscdef : ∀ (L : ℕ), ∀ n : ℕ, 0 < n →
      sc L n ^ 2 = ((∑ e ∈ Es, (sig e - tau L e) * W n e) + cell n) / (n : ℝ))
    (hSndef : ∀ n : ℕ, 0 < n → Sn n = ((∑ e ∈ Es, sig e * W n e) + cell n) / (n : ℝ))
    (htaunn : ∀ (L : ℕ), ∀ e ∈ Es, 0 ≤ tau L e) (hWnn : ∀ (n : ℕ), ∀ e ∈ Es, 0 ≤ W n e)
    (hWb : ∀ (n : ℕ), ∀ e ∈ Es, W n e ≤ Cw * (n : ℝ))
    (hSn : Tendsto Sn atTop (𝓝 sig2)) (hDdel : ∀ L, Cw * ∑ e ∈ Es, tau L e < del L)
    -- `hstep5`, the `L²` gap
    (hsept : ∀ (n : ℕ) (t s : T), t ≠ s →
      (∃ i : ι, coord n s i ∉ tupleSupport (coord n) t) ∨
      (∃ i : ι, coord n t i ∉ tupleSupport (coord n) s))
    (hGg : ∀ L n, Measurable (G n - g L n))
    (hsqd : ∀ L n t, MemLp (degenTerm (U n) (coord n) (G n - g L n) t) 2 P)
    (hdegd : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (G n - g L n) t |
        latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hmomd : ∀ L n t, ∫ ω, degenTerm (U n) (coord n) (G n - g L n) t ω ^ 2 ∂P = taus L n)
    (hxifull : ∀ (L n : ℕ) (ω : Ω), xi n ω
      = degenSum (U n) (coord n) (G n) (cfull n) ω + cellSum (acFull L) eps mc n ω)
    (hscale : ∀ (L n : ℕ) (t : T), sc L n * cf L n t = cfull n t)
    (hscalecell : ∀ (L n : ℕ) (q : ℕ), sc L n * ac L n q = acFull L n q)
    (hgapb : ∀ L n, (∑ t : T, cfull n t ^ 2) * taus L n ≤ del L) :
    TendstoInDistribution xi atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal sig2)) := by
  have hgm : ∀ L n, Measurable (g L n) := by
    intro L n
    rw [hgdef L n]
    exact CLTMartingale.Alg.measurable_multiKernel (hbs 0).measurable_psi rho (lam L)
  have hlat : ∀ L n, MemLp (degenSum (U n) (coord n) (g L n) (cf L n)) 2 P := by
    intro L n
    exact memLp_finsetSum' (Finset.univ : Finset T) fun t _ => (hsq L n t).const_smul (cf L n t)
  have halg : ∀ L n,
      mdsCondVariance kk (rowDiff P U coord (g L) (cf L) stp kk) (rowSigma U stp kk) P n
        =ᵐ[P] fun ω =>
          quadForm (U n) ψ (sites n) (rIdx n) (arr L n) tag (lam L) ω + 0 := by
    intro L n
    exact CLTMartingale.Alg.halg_of_multiKernel (U := U) (coord := coord) (g := g L)
      (c := cf L) (step := stp) (k := kk) (n := n) (sites := sites n) (rIdx := rIdx n)
      (arr := arr L n) (tag := tag) (ρ := rho) (lam := lam L) (kstar := kstar)
      (wsite := wsite n) (cellc := 0) (hbs n) (hinjc n) hrhopos (hgdef L n) (hwsite n)
      (hwstep n) (hrev n) htag (hsitesdef n) (hrIdxdef n) (harrdef L n) rfl
  refine scalar_clt_of_truncation_cell (S := fun _ _ => T) (Ix := fun n => Fin (kk n))
    (tag := tag) (arr := arr) (lev := lev) (pt := pt) (lam := lam) (cellc := cellc)
    (cutmax := cutmax) (totmax := totmax) (ac := ac) (eps := eps) (sg := sg) (mc := mc)
    (sc := sc) (del := del)
    hbs hgm hsq hdeg hN hcm hsite hptc hptf hpos hinj hsep hlam hcut hcutA htot hnorm hcellc
    halg hrate ?_ hsig2 hxi ?_ hsc hdel ?_ ?_ ?_
  · -- `hlind` on the total array
    intro L
    refine CLTMartingale.Cell.lindeberg_total ?_ ?_
    · have h := lindeberg_rowDiff_multiKernel_of_basis (P := P) (ψ := ψ) (Rpos := Rpos)
        (B₀ := B₀) (ρ := rho) (lam := lam L) (U := U) (coord := coord) (cf := cf L)
        (stp := stp) (kk := kk) eqv (Idx := Idx) (site := site) (sidx := sidx)
        hbs hrhopos hsiteinj hcoordsite hsidxinj
        (fun n t => by rw [← hgdef L n]; exact (hsq L n t).integrable one_le_two)
        (fun n t e' he' => by rw [← hgdef L n]; exact hdeg L n t e' he')
        (fun n i => by have := hmeasrow L n i; rwa [funext (hgdef L)] at this)
        (fun n i => by have := hint4row L n i; rwa [funext (hgdef L)] at this)
        (hdesign L)
      intro ε hε
      have h2 := h ε hε
      rwa [← funext (hgdef L)] at h2
    · exact lindeberg_cellDiff_of_fourth (a := ac L) (eps := eps) (m := mc) (C4 := C4)
        (fun n q => hcm.meas n q) hepsint4 hepsfourth (hdesignCell L)
  · -- `hTr`
    exact fun L n => memLp_total (sg := sg) hcm (hlat L n)
  · -- `hsecond`, as an equality
    intro L n
    refine le_of_eq ?_
    exact integral_total_sq (hbs n) (fun n v => (hbs n).measurable_latent v)
      (fun n => (hbs n).indep) (hgm L) (hsq L) (hdeg L) hN hcm (hpos n) (hinj n) (hsep n)
      (halg L n) (hcellc L n) (hnorm L n)
  · -- `hstep4`
    intro L
    exact CLTMartingale.Alg.hstep4_of_varcomp Es sig (tau L) W cell Cw (sc L) Sn (hscdef L)
      hSndef (htaunn L) hWnn hWb hSn (hDdel L)
  · -- `hstep5`
    intro L
    refine Filter.Eventually.of_forall fun n => ?_
    exact CLTMartingale.Cell.hstep5_total_of_tail (G := G n) (g := g L n) (cfull := cfull n)
      (a := ac L) (acFull := acFull L) (eps := eps) (m := mc) (n := n)
      (hbs n).measurable_latent (hbs n).indep (hGg L n) (hsqd L n) (hdegd L n) (hsept n)
      (hmomd L n) (hxifull L n) (hscale L n) (hscalecell L n) (hgapb L n)

end ComposeCellFull

/-! ### Part (b) on the array with cell steps

`clt_b_of_truncation_cell_full` is `clt_b` with `hdir` supplied by
`scalar_clt_of_truncation_cell_full` in each direction. The direction-dependent objects are
those of `clt_b_of_truncation` together with the cell coefficients `ac` and `acFull` and the design
values `W`, `cell` and `Sn`. -/

section ComposeBCell

open DegenerateSum CLTMartingale CLTMartingale.Var CLTMartingale.Cell StatLean.TimeSeries

/-- **Theorem 4(b)** with the cell term `∑_oc'x̃_oε_o` in the martingale and every
intermediate hypothesis derived. -/
theorem clt_b_of_truncation_cell_full {K : ℕ}
    {O : ℕ → Type} [∀ n, Fintype (O n)]
    {M : ℕ} (Sm : ∀ n, Fin M → Submodule ℝ (EuclideanSpace ℝ (O n)))
    (Xm : ∀ n, EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (O n))
    (β : EuclideanSpace ℝ (Fin K))
    (fe : ∀ n, Fin M → EuclideanSpace ℝ (O n)) (hfe : ∀ n m, fe n m ∈ Sm n m)
    (nu : ∀ n, Ω → EuclideanSpace ℝ (O n)) (yv : ∀ n, Ω → EuclideanSpace ℝ (O n))
    (hmodel : ∀ n ω, yv n ω = Xm n β + (∑ m, fe n m) + nu n ω)
    (hnumeas : ∀ n o, Measurable fun ω => nu n ω o)
    (Smat : Matrix (Fin K) (Fin K) ℝ) (hSpd : Smat.PosDef)
    -- the truncation model, the direction-free part
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {T : Type*} [Fintype T] [DecidableEq T]
    {Kd : Type*} [Fintype Kd] [DecidableEq Kd] {N : Kd → Type*}
    [∀ k, Fintype (N k)] [∀ k, DecidableEq (N k)]
    {R : Type*} [DecidableEq R] {ψ : R → ℝ → ℝ} {Rpos : Set R} {B₀ : ℝ}
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {τ : Type*} [DecidableEq τ] {tag : Γ → τ}
    {U : ℕ → Site Kd N → Ω → ℝ}
    {sites : ∀ (_n : ℕ), Γ → T → Finset (Site Kd N)}
    {rIdx : ∀ _n : ℕ, Γ → Site Kd N → R}
    {lev : Γ → Finset Kd} {pt : ∀ (_n : ℕ), Γ → T → Kd → Site Kd N}
    {coord : ℕ → T → ι → Site Kd N} {g : ℕ → ℕ → (ι → ℝ) → ℝ}
    {stp : ℕ → Site Kd N → ℕ} {kk : ℕ → ℕ}
    {eps : ℕ → ℕ → Ω → ℝ} {sg : ℕ → ℕ → ℝ} {mc : ℕ → ℕ}
    {rho : Γ → ι → R} {kstar : ι} {wsite : ℕ → ℕ → Site Kd N}
    {j : ℕ} (eqv : Fin j ≃ ι)
    {Idx : ℕ → Fin j → Type*} [∀ n k, Fintype (Idx n k)]
    {site : ∀ (n : ℕ) (k : Fin j), Idx n k → Site Kd N}
    {sidx : ∀ _n : ℕ, T → ∀ k : Fin j, Idx _n k} {C4 : ℝ}
    {E : Type*} (Es : Finset E) (sig : E → ℝ) (tau : ℕ → E → ℝ)
    {G : ℕ → (ι → ℝ) → ℝ} {taus : ℕ → ℕ → ℝ}
    -- the direction-dependent part, including the cell coefficients
    {arr : ∀ (_c : EuclideanSpace ℝ (Fin K)) (_L n : ℕ), Γ → T → Fin (kk n) → ℝ}
    {lam : EuclideanSpace ℝ (Fin K) → ℕ → Γ → ℝ}
    {cellc cutmax totmax sc : EuclideanSpace ℝ (Fin K) → ℕ → ℕ → ℝ}
    {cf : EuclideanSpace ℝ (Fin K) → ℕ → ℕ → T → ℝ}
    {ac acFull : EuclideanSpace ℝ (Fin K) → ℕ → ℕ → ℕ → ℝ}
    {cfull : EuclideanSpace ℝ (Fin K) → ℕ → T → ℝ}
    {del : EuclideanSpace ℝ (Fin K) → ℕ → ℝ}
    (W : EuclideanSpace ℝ (Fin K) → ℕ → E → ℝ)
    (cell Sn : EuclideanSpace ℝ (Fin K) → ℕ → ℝ) (Cw : EuclideanSpace ℝ (Fin K) → ℝ)
    (hbs : ∀ n, IsBasisSystem P (U n) ψ Rpos B₀)
    (hsq : ∀ L n t, MemLp (degenTerm (U n) (coord n) (g L n) t) 2 P)
    (hdegk : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (g L n) t | latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hN : ∀ n v, stp n v < kk n)
    (hcm : IsCellModel P (latentBase U stp kk) eps sg mc)
    (hsite : ∀ (n : ℕ) (q : Γ) (x : T), sites n q x = (lev q).image (pt n q x))
    (hptc : ∀ (n : ℕ) (q q' : Γ) (x y : T) (a b : Kd), pt n q x a = pt n q' y b → a = b)
    (hptf : ∀ (n : ℕ) (q : Γ) (x : T), ∀ a ∈ lev q, (pt n q x a).1 = a)
    (hpos : ∀ (n : ℕ) (q : Γ) (x : T), ∀ w ∈ sites n q x, rIdx n q w ∈ Rpos)
    (hinjs : ∀ (n : ℕ) (q : Γ) (x y : T), sites n q x = sites n q y → x = y)
    (hsep : ∀ (n : ℕ) (q q' : Γ) (x y : T), tag q = tag q' →
      sites n q x = sites n q' y → (∀ w ∈ sites n q x, rIdx n q w = rIdx n q' w) → q = q')
    (hlam : ∀ c L, ∑ γ, lam c L γ ^ 2 ≤ 1)
    (hcut : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (γ : Γ),
      rectFrobNorm (Matrix.of (arr c L n γ) * (Matrix.of (arr c L n γ))ᵀ) ≤ cutmax c L n)
    (hcutA : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (q : Γ), ∀ Bs ⊂ lev q,
      rectFrobNorm (Matrix.of (levMat lev (pt n) Bs q (arr c L n q)) *
        (Matrix.of (levMat lev (pt n) Bs q (arr c L n q)))ᵀ) ≤ cutmax c L n)
    (htot : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (γ : Γ),
      rectFrobSq (arr c L n γ) ≤ totmax c L n)
    (hnorm : ∀ c L n, (∑ γ, lam c L γ ^ 2 * rectFrobSq (arr c L n γ)) + cellc c L n = 1)
    (hcellc : ∀ c L n, cellc c L n = cellConst (ac c L) sg mc n)
    (hrate : ∀ c L, Tendsto (fun n =>
        clauseBConst B₀ (Fintype.card Γ) (Fintype.card Kd)
          * (cutmax c L n * totmax c L n)) atTop (𝓝 0))
    (hgdef : ∀ c L n, g L n = CLTMartingale.Alg.multiKernel ψ rho (lam c L))
    (hinjc : ∀ n t, Function.Injective (coord n t))
    (hrhopos : ∀ γ i, rho γ i ∈ Rpos)
    (hwsite : ∀ (n : ℕ), ∀ κ < kk n, ∀ t ∈ completedAt (coord n) (stp n) κ,
      coord n t kstar = wsite n κ)
    (hwstep : ∀ (n : ℕ), ∀ κ < kk n, κ ≤ stp n (wsite n κ))
    (hrev : ∀ (n : ℕ), ∀ κ < kk n, ∀ t ∈ completedAt (coord n) (stp n) κ, ∀ i : ι, i ≠ kstar →
      stp n (coord n t i) < κ)
    (htag : ∀ γ γ' : Γ, tag γ = tag γ' ↔ rho γ kstar = rho γ' kstar)
    (hsitesdef : ∀ (n : ℕ) (γ : Γ) (t : T),
      sites n γ t = (Finset.univ.erase kstar).image (coord n t))
    (hrIdxdef : ∀ (n : ℕ) (γ : Γ) (t : T) (i : ι), i ≠ kstar →
      rIdx n γ (coord n t i) = rho γ i)
    (harrdef : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (γ : Γ) (t : T) (q : Fin (kk n)),
      arr c L n γ t q = if t ∈ completedAt (coord n) (stp n) (q : ℕ) then cf c L n t else 0)
    (hsiteinj : ∀ n, Function.Injective (fun p : Σ k : Fin j, Idx n k => site n p.1 p.2))
    (hcoordsite : ∀ n t k, coord n t (eqv k) = site n k (sidx n t k))
    (hsidxinj : ∀ n, Function.Injective (sidx n))
    (hmeasrow : ∀ c L n i, Measurable (rowDiff P U coord (g L) (cf c L) stp kk n i))
    (hint4row : ∀ c L n i, Integrable
      (fun ω => rowDiff P U coord (g L) (cf c L) stp kk n i ω ^ 4) P)
    (hdesign : ∀ c L, Tendsto (fun n => (3 * B₀ ^ 4) ^ j *
        ∑ i : Fin (kk n),
          (∑ t ∈ completedAt (coord n) (stp n) (i : ℕ), cf c L n t ^ 2) ^ 2) atTop (𝓝 0))
    (hepsint4 : ∀ n q, Integrable (fun ω => eps n q ω ^ 4) P)
    (hepsfourth : ∀ n q, ∫ ω, eps n q ω ^ 4 ∂P ≤ C4)
    (hdesignCell : ∀ c L, Tendsto (fun n => C4 * ∑ q : Fin (mc n), ac c L n (q : ℕ) ^ 4)
      atTop (𝓝 0))
    (hxi : ∀ (c : EuclideanSpace ℝ (Fin K)) (n : ℕ),
      MemLp (fun ω => (Real.sqrt n)⁻¹ * ⟪score (⨆ m, Sm n m) (Xm n) (nu n ω), c⟫) 2 P)
    (hsc : ∀ c L n, 0 ≤ sc c L n) (hdel : ∀ c, Tendsto (del c) atTop (𝓝 0))
    (hscdef : ∀ (c : EuclideanSpace ℝ (Fin K)) (L : ℕ), ∀ n : ℕ, 0 < n →
      sc c L n ^ 2 = ((∑ e ∈ Es, (sig e - tau L e) * W c n e) + cell c n) / (n : ℝ))
    (hSndef : ∀ (c : EuclideanSpace ℝ (Fin K)), ∀ n : ℕ, 0 < n →
      Sn c n = ((∑ e ∈ Es, sig e * W c n e) + cell c n) / (n : ℝ))
    (htaunn : ∀ (L : ℕ), ∀ e ∈ Es, 0 ≤ tau L e)
    (hWnn : ∀ (c : EuclideanSpace ℝ (Fin K)) (n : ℕ), ∀ e ∈ Es, 0 ≤ W c n e)
    (hWb : ∀ (c : EuclideanSpace ℝ (Fin K)) (n : ℕ), ∀ e ∈ Es, W c n e ≤ Cw c * (n : ℝ))
    (hSn : ∀ c : EuclideanSpace ℝ (Fin K), Tendsto (Sn c) atTop (𝓝 (c ⬝ᵥ (Smat *ᵥ c))))
    (hDdel : ∀ c L, Cw c * ∑ e ∈ Es, tau L e < del c L)
    (hsept : ∀ (n : ℕ) (t s : T), t ≠ s →
      (∃ i : ι, coord n s i ∉ tupleSupport (coord n) t) ∨
      (∃ i : ι, coord n t i ∉ tupleSupport (coord n) s))
    (hGg : ∀ L n, Measurable (G n - g L n))
    (hsqd : ∀ L n t, MemLp (degenTerm (U n) (coord n) (G n - g L n) t) 2 P)
    (hdegd : ∀ (L n : ℕ) (t : T) (e' : Set ι), e' ≠ Set.univ →
      P[degenTerm (U n) (coord n) (G n - g L n) t |
        latentSigma (U n) (coord n t '' e')] =ᵐ[P] 0)
    (hmomd : ∀ L n t, ∫ ω, degenTerm (U n) (coord n) (G n - g L n) t ω ^ 2 ∂P = taus L n)
    (hxifull : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (ω : Ω),
      (Real.sqrt n)⁻¹ * ⟪score (⨆ m, Sm n m) (Xm n) (nu n ω), c⟫
        = degenSum (U n) (coord n) (G n) (cfull c n) ω + cellSum (acFull c L) eps mc n ω)
    (hscale : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n : ℕ) (t : T),
      sc c L n * cf c L n t = cfull c n t)
    (hscalecell : ∀ (c : EuclideanSpace ℝ (Fin K)) (L n q : ℕ),
      sc c L n * ac c L n q = acFull c L n q)
    (hgapb : ∀ c L n, (∑ t : T, cfull c n t ^ 2) * taus L n ≤ del c L)
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Hinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ᶠ n : ℕ in atTop, ∀ a, A n ((n : ℝ)⁻¹ • gram (⨆ m, Sm n m) (Xm n) a) = a)
    (hAlim : Tendsto A atTop (𝓝 Hinv))
    (ιv : ∀ n, EuclideanSpace ℝ (O n)) (hι : ∀ n, ιv n ∈ ⨆ m, Sm n m)
    (hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, Sm n m) (Xm n))
    (bJM bMFE : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hbJMmeas : ∀ n, AEMeasurable (bJM n) P) (hbMFEmeas : ∀ n, AEMeasurable (bMFE n) P)
    (hbJM : ∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (ιv n) (⨆ m, Sm n m) (Xm n)) (Xm n)
      (yv n ω) (bJM n ω))
    (hbMFE : ∀ᶠ n : ℕ in atTop, ∀ ω, IsMFESlope (⨆ m, Sm n m) (Xm n) (yv n ω) (bMFE n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bJM n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat)
      ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bMFE n ω - β)) atTop
        (fun z => Hinv z) (fun _ => P) (multivariateGaussian 0 Smat) := by
  refine clt_b Sm Xm β fe hfe nu yv hmodel hnumeas Smat hSpd ?_ A Hinv hAsolve hAlim
    ιv hι hid bJM bMFE hbJMmeas hbMFEmeas hbJM hbMFE
  intro c hc
  exact scalar_clt_of_truncation_cell_full (tag := tag) (arr := arr c) (lev := lev) (pt := pt)
    (lam := lam c) (cellc := cellc c) (cutmax := cutmax c) (totmax := totmax c)
    (cf := cf c) (ac := ac c) (acFull := acFull c) (eps := eps) (sg := sg) (mc := mc)
    (sc := sc c) (del := del c) (rho := rho) (kstar := kstar) (wsite := wsite)
    (Idx := Idx) (site := site) (sidx := sidx) (C4 := C4) (G := G) (cfull := cfull c)
    (taus := taus)
    eqv Es sig tau (W c) (cell c) (Sn c) (Cw c)
    hbs hsq hdegk hN hcm hsite hptc hptf hpos hinjs hsep (hlam c) (hcut c) (hcutA c) (htot c)
    (hnorm c) (hcellc c) (hrate c) (hgdef c) hinjc hrhopos hwsite hwstep hrev htag hsitesdef
    hrIdxdef (harrdef c) hsiteinj hcoordsite hsidxinj (hmeasrow c) (hint4row c) (hdesign c)
    hepsint4 hepsfourth (hdesignCell c)
    (dotProduct_mulVec_pos_of_posDef hSpd hc) (hxi c) (hsc c) (hdel c) (hscdef c) (hSndef c)
    htaunn (hWnn c) (hWb c) (hSn c) (hDdel c) hsept hGg hsqd hdegd hmomd (hxifull c)
    (hscale c) (hscalecell c) (hgapb c)

end ComposeBCell
/-! ### Models for the cell-carrying array

`halg_cell_witness` extends the `halg` model by two cells with coefficients `1` and `2`, so that
`cellc = 5`. The cell sites `(9, q+3)` are revealed after every latent step, so the disturbances
`walA ∘ ξ` are independent of the latent σ-field. `lindeberg_multiKernel_witness` runs
`lindeberg_rowDiff_multiKernel_of_basis` at the kernel `Alg.multiKernel walPsi rhoW lamW`, with
two components, coefficients `1` and `2`, `j = 2`, `B₀ = 2`, and design coefficients nonzero at
every `n`. -/

namespace Witness

open DegenerateSum CLTMartingale CLTMartingale.Cell StatLean.TimeSeries
open scoped ENNReal

/-! ### The cell model of the witness -/

/-- The cell sites `(9, q+3)`, revealed after the three latent steps. -/
def cellSite : ℕ → ℕ × ℕ := fun q => (9, q + 3)

theorem cellSite_injective : Function.Injective cellSite := by
  intro x y h
  have h2 : x + 3 = y + 3 := congrArg Prod.snd h
  omega

theorem cellSite_not_revealed (q : ℕ) : cellSite q ∉ revealed sstep 3 := by
  show ¬ (sstep (cellSite q) < 3)
  show ¬ ((if (9 : ℕ) = 0 then 0 else q + 3) < 3)
  simp

theorem abs_walA_le_one (x : ℝ) : |walA x| ≤ 1 := by
  unfold walA; split_ifs <;> norm_num

variable {ξ : ℕ × ℕ → Ω → ℝ}

/-- The disturbances `ε_o`: a Walsh function of a latent variable at a cell site, bounded by
`1`, with mean zero and unit second moment. -/
noncomputable def epsW (ξ : ℕ × ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ :=
  fun _n q ω => walA (ξ (cellSite q) ω)

/-- Two cells, with different nonzero coefficients `c'x̃_o`. -/
noncomputable def acW : ℕ → ℕ → ℝ := fun _n q => (q : ℝ) + 1

/-- `σ²_ε(o) = 1`. -/
noncomputable def sgW : ℕ → ℕ → ℝ := fun _n _q => 1

theorem cellConst_witness : cellConst acW sgW (fun _ => 2) 0 = 5 := by
  show ∑ q : Fin 2, acW 0 (q : ℕ) ^ 2 * sgW 0 (q : ℕ) = 5
  simp only [Fin.sum_univ_two, acW, sgW]
  norm_num

theorem isCellModel_witness
    (hmeasξ : ∀ v, Measurable (ξ v)) (hindepξ : iIndepFun ξ P)
    (hlaw : ∀ v, P.map (ξ v) = wal) :
    IsCellModel P (latentBase (fun _ => ξ) (fun _ => sstep) (fun _ => 3)) (epsW ξ) sgW
      (fun _ => 2) where
  base_le _ := latentSigma_le hmeasξ _
  meas _ q := measurable_walA.comp (hmeasξ (cellSite q))
  l2 n q := MemLp.of_bound
    (Measurable.aestronglyMeasurable (measurable_walA.comp (hmeasξ (cellSite q)))) 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_walA_le_one _)
  indep n q := by
    have hcomap : MeasurableSpace.comap (epsW ξ n (q : ℕ))
        (inferInstance : MeasurableSpace ℝ)
        ≤ MeasurableSpace.comap (ξ (cellSite (q : ℕ))) (inferInstance : MeasurableSpace ℝ) := by
      have hc : MeasurableSpace.comap (epsW ξ n (q : ℕ)) (inferInstance : MeasurableSpace ℝ)
          = MeasurableSpace.comap (ξ (cellSite (q : ℕ)))
            (MeasurableSpace.comap walA (inferInstance : MeasurableSpace ℝ)) := by
        rw [MeasurableSpace.comap_comp]
        rfl
      rw [hc]
      exact MeasurableSpace.comap_mono measurable_walA.comap_le
    have hsingle : MeasurableSpace.comap (ξ (cellSite (q : ℕ)))
        (inferInstance : MeasurableSpace ℝ) ≤ latentSigma ξ {cellSite (q : ℕ)} :=
      le_iSup₂ (f := fun w (_ : w ∈ ({cellSite (q : ℕ)} : Set (ℕ × ℕ))) =>
        MeasurableSpace.comap (ξ w) inferInstance) (cellSite (q : ℕ)) rfl
    have hpast : cellSigma (latentBase (fun _ => ξ) (fun _ => sstep) (fun _ => 3))
        (epsW ξ) (fun _ => 2) n q.castSucc
        ≤ latentSigma ξ (revealed sstep 3 ∪ cellSite '' {i : ℕ | i < (q : ℕ)}) := by
      refine sup_le (latentSigma_mono ξ Set.subset_union_left) ?_
      refine iSup₂_le fun i hi => ?_
      refine le_trans ?_ (le_iSup₂ (f := fun w (_ : w ∈ (revealed sstep 3 ∪
        cellSite '' {i : ℕ | i < (q : ℕ)})) => MeasurableSpace.comap (ξ w) inferInstance)
        (cellSite i) (Or.inr ⟨i, hi, rfl⟩))
      have hc : MeasurableSpace.comap (epsW ξ n i) (inferInstance : MeasurableSpace ℝ)
          = MeasurableSpace.comap (ξ (cellSite i))
            (MeasurableSpace.comap walA (inferInstance : MeasurableSpace ℝ)) := by
        rw [MeasurableSpace.comap_comp]
        rfl
      rw [hc]
      exact MeasurableSpace.comap_mono measurable_walA.comap_le
    have hdisj : Disjoint ({cellSite (q : ℕ)} : Set (ℕ × ℕ))
        (revealed sstep 3 ∪ cellSite '' {i : ℕ | i < (q : ℕ)}) := by
      rw [Set.disjoint_singleton_left]
      rintro (h | ⟨i, hi, hieq⟩)
      · exact cellSite_not_revealed (q : ℕ) h
      · have hi' : i < (q : ℕ) := hi
        have heq : i = (q : ℕ) := cellSite_injective hieq
        omega
    exact indep_of_indep_of_le_left
      (indep_of_indep_of_le_right (latentSigma_indep hmeasξ hindepξ hdisj) hpast)
      (le_trans hcomap hsingle)
  mean n q := by
    have h : ∫ y, walA y ∂(P.map (ξ (cellSite q))) = ∫ ω, walA (ξ (cellSite q) ω) ∂P :=
      integral_map (hmeasξ _).aemeasurable measurable_walA.aestronglyMeasurable
    show ∫ ω, walA (ξ (cellSite q) ω) ∂P = 0
    rw [← h, hlaw]
    exact integral_walPsi 0
  var n q := by
    have h : ∫ y, walA y * walA y ∂(P.map (ξ (cellSite q)))
        = ∫ ω, walA (ξ (cellSite q) ω) * walA (ξ (cellSite q) ω) ∂P :=
      integral_map (hmeasξ _).aemeasurable
        (measurable_walA.mul measurable_walA).aestronglyMeasurable
    show ∫ ω, walA (ξ (cellSite q) ω) ^ 2 ∂P = 1
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (pow_two (walA (ξ (cellSite q) ω))))]
    rw [← h, hlaw]
    have h2 := integral_walPsi_mul (0 : Fin 2) 0
    rw [walPsi_zero] at h2
    simpa using h2

/-! ### `halg` with cell steps -/

set_option maxHeartbeats 1000000 in
/-- `halg` for the array carrying both halves, at `cellc = 1·1 + 4·1 = 5`: the latent half is
the model of `halg_witness`, and the cell half adds two cells with coefficients `1` and `2`. -/
theorem halg_cell_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      mdsCondVariance (fun n => (fun _ => 3) n + (fun _ => 2) n)
          (totalDiff P (fun _ => ξ) (fun _ => scoord)
            (fun _ => Alg.multiKernel walPsi rhoW lamW) (fun _ => cwit) (fun _ => sstep)
            (fun _ => 3) acW (epsW ξ) (fun _ => 2))
          (totalSigma (fun _ => ξ) (fun _ => sstep) (fun _ => 3) (epsW ξ) (fun _ => 2)) P 0
        =ᵐ[P] (fun ω => Var.quadForm ξ walPsi sitesW rIdxW arrW tagW lamW ω + 5)
    ∧ cellConst acW sgW (fun _ => 2) 0 = 5
    ∧ (5 : ℝ) ≠ 0
    ∧ rhoW 0 1 ≠ rhoW 1 1 := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) wal
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = wal := fun v => (hlawξ v).map_eq
  have hbs : IsBasisSystem P ξ walPsi (Set.univ : Set (Fin 2)) 2 :=
    Step2.isBasisSystem_of_law hmeasξ measurable_walPsi hindepξ hlaw abs_walPsi_le
      (fun r _ => integral_walPsi r) integral_walPsi_mul
  have hcm := isCellModel_witness (P := P) (ξ := ξ) hmeasξ hindepξ hlaw
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, cellConst_witness, by norm_num, rhoW_ne⟩
  refine condVar_total_of_latent (a := acW) (sg := sgW) hcm ?_ cellConst_witness.symm
  exact Alg.halg_of_multiKernel (U := fun _ => ξ) (coord := fun _ => scoord)
    (g := fun _ => Alg.multiKernel walPsi rhoW lamW) (c := fun _ => cwit)
    (step := fun _ => sstep) (k := fun _ => 3) (n := 0)
    (sites := sitesW) (rIdx := rIdxW) (arr := arrW) (tag := tagW)
    (ρ := rhoW) (lam := lamW) (kstar := 1) (wsite := wsiteW) (cellc := 0)
    hbs scoord_injective (fun _ _ => Set.mem_univ _) rfl
    hw_W hwstep_W hrev_W (fun _ _ => Iff.rfl) (fun _ _ => rfl) hrIdx_W (fun _ _ _ => rfl) rfl


/-! ### The Lindeberg condition for a sum of product kernels -/

/-- The latent variables of the `halg` model indexed by dimension: two indices in dimension `0`
and two in dimension `1`. -/
def siteW : ℕ → Fin 2 → Fin 2 → ℕ × ℕ :=
  fun _n k i => if k = 0 then (0, i.val) else (1, i.val + 1)

/-- Which index of each dimension the sub-tuple `t` carries: `scoord` read off. -/
def sidxW : ℕ → Fin 4 → ∀ _k : Fin 2, Fin 2 :=
  fun _n t k => if k = 0 then ⟨t.val % 2, Nat.mod_lt _ (by norm_num)⟩
    else ⟨t.val / 2, by have := t.isLt; omega⟩

theorem hcoordsite_W (n : ℕ) (t : Fin 4) (k : Fin 2) :
    scoord t ((Equiv.refl (Fin 2)) k) = siteW n k (sidxW n t k) := by
  fin_cases t <;> fin_cases k <;> rfl

theorem hsiteinj_W (n : ℕ) :
    Function.Injective (fun p : Σ _k : Fin 2, Fin 2 => siteW n p.1 p.2) := by
  have h : (fun p : Σ _k : Fin 2, Fin 2 => siteW n p.1 p.2)
      = fun p : Σ _k : Fin 2, Fin 2 => siteW 0 p.1 p.2 := rfl
  rw [h]
  decide

theorem hsidxinj_W (n : ℕ) : Function.Injective (sidxW n) := by
  have h : sidxW n = sidxW 0 := rfl
  rw [h]
  decide

theorem completedAt_zero_W : completedAt scoord sstep 0 = (∅ : Finset (Fin 4)) := by decide

/-- The coefficients `cwit t / (n+1)`, nonzero at every `n`. -/
noncomputable def cfW : ℕ → Fin 4 → ℝ := fun n t => cwit t / ((n : ℝ) + 1)

theorem cfW_ne_zero (n : ℕ) (t : Fin 4) : cfW n t ≠ 0 := by
  have h1 : cwit t ≠ 0 := by
    show (t.val : ℝ) + 1 ≠ 0
    positivity
  have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  exact div_ne_zero h1 h2

theorem cfdesign_eq (n : ℕ) :
    (3 * (2 : ℝ) ^ 4) ^ 2 *
        ∑ i : Fin 3, (∑ t ∈ completedAt scoord sstep (i : ℕ), cfW n t ^ 2) ^ 2
      = ((3 * (2 : ℝ) ^ 4) ^ 2 *
          ∑ i : Fin 3, (∑ t ∈ completedAt scoord sstep (i : ℕ), cwit t ^ 2) ^ 2)
        * (1 / ((n : ℝ) + 1)) ^ 4 := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hinner : ∀ i : Fin 3,
      (∑ t ∈ completedAt scoord sstep (i : ℕ), cfW n t ^ 2) ^ 2
        = (∑ t ∈ completedAt scoord sstep (i : ℕ), cwit t ^ 2) ^ 2
          * (1 / ((n : ℝ) + 1)) ^ 4 := by
    intro i
    have h1 : ∑ t ∈ completedAt scoord sstep (i : ℕ), cfW n t ^ 2
        = (∑ t ∈ completedAt scoord sstep (i : ℕ), cwit t ^ 2) * (1 / ((n : ℝ) + 1)) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      show (cwit t / ((n : ℝ) + 1)) ^ 2 = _
      field_simp
    rw [h1]; ring
  rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.sum_mul]
  ring

theorem cfdesign : Tendsto (fun n : ℕ => (3 * (2 : ℝ) ^ 4) ^ 2 *
    ∑ i : Fin 3, (∑ t ∈ completedAt scoord sstep (i : ℕ), cfW n t ^ 2) ^ 2) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 4) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 4
  have h := hb.const_mul ((3 * (2 : ℝ) ^ 4) ^ 2 *
    ∑ i : Fin 3, (∑ t ∈ completedAt scoord sstep (i : ℕ), cwit t ^ 2) ^ 2)
  simpa using h.congr fun n => (cfdesign_eq n).symm

/-- Every hypothesis of `lindeberg_rowDiff_multiKernel_of_basis` holds at the kernel
`Alg.multiKernel walPsi rhoW lamW`, with two components and coefficients `1` and `2`, `j = 2`,
`B₀ = 2`, and design coefficients nonzero at every `n`. -/
theorem lindeberg_multiKernel_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |rowDiff P (fun _ => ξ) (fun _ => scoord)
              (fun _ => Alg.multiKernel walPsi rhoW lamW) cfW (fun _ => sstep)
              (fun _ => 3) n i ω|},
            (rowDiff P (fun _ => ξ) (fun _ => scoord)
              (fun _ => Alg.multiKernel walPsi rhoW lamW) cfW (fun _ => sstep)
              (fun _ => 3) n i ω) ^ 2 ∂P) atTop (𝓝 0))
    ∧ rhoW 0 1 ≠ rhoW 1 1
    ∧ lamW 0 ≠ lamW 1
    ∧ (∀ n : ℕ, ∀ t : Fin 4, cfW n t ≠ 0) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) wal
  have hlaw : ∀ v : ℕ × ℕ, P.map (ξ v) = wal := fun v => (hlawξ v).map_eq
  have hbs : IsBasisSystem P ξ walPsi (Set.univ : Set (Fin 2)) 2 :=
    Step2.isBasisSystem_of_law hmeasξ measurable_walPsi hindepξ hlaw abs_walPsi_le
      (fun r _ => integral_walPsi r) integral_walPsi_mul
  have hrho : ∀ (γ : Fin 2) (i : Fin 2), rhoW γ i ∈ (Set.univ : Set (Fin 2)) :=
    fun _ _ => Set.mem_univ _
  have hint : ∀ (n : ℕ) (t : Fin 4),
      Integrable (degenTerm ξ scoord (Alg.multiKernel walPsi rhoW lamW) t) P := fun _ t =>
    (Alg.memLp_degenTerm_multiKernel hbs scoord t rhoW lamW).integrable one_le_two
  have hdeg : ∀ (n : ℕ) (t : Fin 4) (e' : Set (Fin 2)), e' ≠ Set.univ →
      P[degenTerm ξ scoord (Alg.multiKernel walPsi rhoW lamW) t |
        latentSigma ξ (scoord t '' e')] =ᵐ[P] 0 := fun _ t e' hne =>
    Alg.condExp_degenTerm_multiKernel_eq_zero hbs (scoord_injective t) hrho e' hne
  have hbd : ∀ t : Fin 4, ∀ᵐ ω ∂P,
      |degenTerm ξ scoord (Alg.multiKernel walPsi rhoW lamW) t ω| ≤ 16 := by
    intro t
    refine Filter.Eventually.of_forall fun ω => ?_
    show |∑ γ : Fin 2, lamW γ * Step2.prodKernel walPsi (rhoW γ)
      (latentTuple ξ scoord t ω)| ≤ 16
    have hlamb : ∀ γ : Fin 2, |lamW γ| ≤ 2 := by
      intro γ
      fin_cases γ <;> · show |((_ : Fin 2) : ℝ) + 1| ≤ 2; norm_num
    calc |∑ γ : Fin 2, lamW γ * Step2.prodKernel walPsi (rhoW γ)
            (latentTuple ξ scoord t ω)|
        ≤ ∑ γ : Fin 2, |lamW γ * Step2.prodKernel walPsi (rhoW γ)
            (latentTuple ξ scoord t ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _γ : Fin 2, (2 : ℝ) * (max (2 : ℝ) 1 ^ Fintype.card (Fin 2)) := by
          refine Finset.sum_le_sum fun γ _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hlamb γ) (Step2.abs_prodKernel_le abs_walPsi_le _ _)
            (abs_nonneg _) (by norm_num)
      _ ≤ 16 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hgm : Measurable (Alg.multiKernel walPsi rhoW lamW) :=
    Alg.measurable_multiKernel measurable_walPsi rhoW lamW
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, rhoW_ne, ?_, fun n t => cfW_ne_zero n t⟩
  · exact lindeberg_rowDiff_multiKernel_of_basis (P := P) (ψ := walPsi)
      (Rpos := (Set.univ : Set (Fin 2))) (B₀ := 2) (ρ := rhoW) (lam := lamW)
      (U := fun _ => ξ) (coord := fun _ => scoord) (cf := cfW) (stp := fun _ => sstep)
      (kk := fun _ => 3) (Equiv.refl (Fin 2)) (Idx := fun _ _ => Fin 2) (site := siteW)
      (sidx := sidxW) (fun _ => hbs) hrho hsiteinj_W hcoordsite_W hsidxinj_W hint hdeg
      (fun n i => Step45.measurable_degenDiff (c := cfW n) (step := sstep) hmeasξ (i : ℕ))
      (fun n i => Step45.integrable_pow_four_degenDiff (c := cfW n) (step := sstep)
        (by norm_num) hmeasξ hindepξ hgm (hint n) (hdeg n) hbd (i : ℕ))
      cfdesign
  · show ((0 : Fin 2) : ℝ) + 1 ≠ ((1 : Fin 2) : ℝ) + 1
    norm_num
end Witness
end CLT
end Multiway
