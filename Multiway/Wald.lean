import Multiway.Sqrt
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The Wald lemma

This file proves a reusable Wald lemma: given a central limit theorem for a restricted deviation
(taken as a hypothesis) and a consistent variance estimator, the restricted variance estimate is
positive definite with probability tending to one and the Wald statistic converges in distribution
to `χ²_r`. It is used in Theorems 7(b), 9(c), 11(c) and 12(b) of the paper. The limit `χ²_r` is
written as the law of `‖Z‖²` with `Z ~ N(0, I_r)`, and convergence in probability of a matrix is
convergence in probability of `ω ↦ frobNorm (A n ω - Σ)`.

## Main results

* `waldStat`: the Wald statistic `𝟙{A ≻ 0} x'A⁻¹x`.
* `waldStat_smul`: invariance under `(A, x) ↦ (aA, √a x)` for `a > 0`.
* `wald_of_clt`: the Wald lemma with a deterministic limit `Σ ≻ 0`.
* `wald_of_clt_rateAgnostic`: the version with a random normalizer `𝒱_n`, via Lemma SM.B.14.
* `wald_of_clt_witness`: a model satisfying all hypotheses of `wald_of_clt`.
-/

namespace Multiway

namespace Wald

open Filter Finset MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Frobenius norm as a norm on a Euclidean space

The definitions are in `Multiway/Sqrt.lean` and are re-exported under the `Wald` namespace. -/

export Multiway (matVec matVec_apply matVec_add matVec_sub matVec_smul matVec_sum
  frobSq_nonneg frobNorm_nonneg sq_frobNorm norm_matVec dist_matVec)


/-! ### The Wald statistic -/

open Classical in
/-- **The Wald statistic** `𝒲 = 𝟙{A ≻ 0} x'A⁻¹x`, with `A = 𝓡V̂𝓡'` and `x = 𝓡θ̂ − 𝓡θ`;
it is zero off the event `A ≻ 0`. -/
noncomputable def waldStat (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  if A.PosDef then x ⬝ᵥ A⁻¹ *ᵥ x else 0

open Classical in
theorem waldStat_of_not_posDef {A : Matrix ι ι ℝ} (h : ¬ A.PosDef) (x : EuclideanSpace ℝ ι) :
    waldStat A x = 0 := by simp [waldStat, h]

open Classical in
theorem waldStat_of_posDef {A : Matrix ι ι ℝ} (h : A.PosDef) (x : EuclideanSpace ℝ ι) :
    waldStat A x = x ⬝ᵥ A⁻¹ *ᵥ x := by simp [waldStat, h]

omit [Fintype ι] [DecidableEq ι] in
/-- Positive definiteness is invariant under a positive scaling. -/
theorem posDef_smul_iff {a : ℝ} (ha : 0 < a) (A : Matrix ι ι ℝ) :
    (a • A).PosDef ↔ A.PosDef := by
  refine ⟨fun hc => ?_, fun hc => hc.smul ha⟩
  have h := hc.smul (inv_pos.mpr ha)
  rwa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h

/-- The Wald statistic is invariant under `(V̂, θ̂ − θ) ↦ (aV̂, √a(θ̂ − θ))` for `a > 0`. -/
theorem waldStat_smul {a : ℝ} (ha : 0 < a) (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    waldStat (a • A) (Real.sqrt a • x) = waldStat A x := by
  by_cases hA : A.PosDef
  · have hsm : (a • A).PosDef := hA.smul ha
    have hinv : (a • A)⁻¹ = a⁻¹ • A⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hA)]
    rw [waldStat_of_posDef hsm, waldStat_of_posDef hA, hinv]
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    simp only [WithLp.ofLp_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    field_simp
    rw [Real.sq_sqrt ha.le]
  · have hsm : ¬ (a • A).PosDef := fun hc => hA ((posDef_smul_iff ha A).mp hc)
    rw [waldStat_of_not_posDef hsm, waldStat_of_not_posDef hA]

/-! ### The Wald statistic as a squared norm

Off the event `Σ̂ ≻ 0` the inverse square root vanishes, so the identity `waldStat_eq_sq_norm`
holds in every realization. -/

/-- `Σ̂^{-1/2} = 0` whenever `Σ̂` is not positive definite. If `Σ̂` is not positive
semidefinite then `CFC.sqrt Σ̂ = 0`, and if it is positive semidefinite but singular then so is
its square root. -/
theorem inv_sqrtPD_eq_zero_of_not_posDef {A : Matrix ι ι ℝ} (h : ¬ A.PosDef) :
    (sqrtPD A)⁻¹ = 0 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  refine Matrix.nonsing_inv_apply_not_isUnit _ fun hu => ?_
  rw [← Matrix.isUnit_iff_isUnit_det] at hu
  by_cases hps : A.PosSemidef
  · refine h (hps.posDef_iff_isUnit.mpr ?_)
    rw [← sqrtPD_mul_self hps]
    exact hu.mul hu
  · rw [sqrtPD, CFC.sqrt_of_not_nonneg fun hn => hps (Matrix.nonneg_iff_posSemidef.mp hn)] at hu
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_zero] at hu
    exact not_isUnit_zero hu

/-- The studentizing matrix `T := Σ̂^{-1/2}Σ^{1/2}` of Lemma SM.B.14, with `Σ̂ := A` and
`Σ := C`. Off the event `A ≻ 0` it is the zero matrix, by `inv_sqrtPD_eq_zero_of_not_posDef`. -/
noncomputable def studentizerMat (A C : Matrix ι ι ℝ) : Matrix ι ι ℝ := (sqrtPD A)⁻¹ * sqrtPD C

/-- In every realization `𝒲 = ‖T(Σ^{-1/2}x)‖²` with `T = Σ̂^{-1/2}Σ^{1/2}`. On the event `Σ̂ ≻ 0`
this holds because `TΣ^{-1/2} = Σ̂^{-1/2}`, and off it both sides are zero. -/
theorem studentizer_comp_invSqrt (A : Matrix ι ι ℝ) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) :
    toEuclideanCLM (𝕜 := ℝ) (studentizerMat A C) (toEuclideanCLM (𝕜 := ℝ) ((sqrtPD C)⁻¹) x)
      = toEuclideanCLM (𝕜 := ℝ) ((sqrtPD A)⁻¹) x := by
  have e : studentizerMat A C * (sqrtPD C)⁻¹ = (sqrtPD A)⁻¹ := by
    rw [studentizerMat, Matrix.mul_assoc, sqrtPD_mul_inv hC, Matrix.mul_one]
  rw [← e, map_mul]
  rfl

theorem waldStat_eq_sq_norm (A : Matrix ι ι ℝ) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    (x : EuclideanSpace ℝ ι) :
    waldStat A x
      = ‖toEuclideanCLM (𝕜 := ℝ) (studentizerMat A C)
          (toEuclideanCLM (𝕜 := ℝ) ((sqrtPD C)⁻¹) x)‖ ^ 2 := by
  rw [studentizer_comp_invSqrt A hC]
  by_cases hA : A.PosDef
  · rw [waldStat_of_posDef hA, ← real_inner_self_eq_norm_sq, Matrix.inner_toEuclideanCLM]
    have hS : ((sqrtPD A)⁻¹).PosDef := inv_sqrtPD_posDef hA
    simp only [Matrix.ofLp_toEuclideanCLM]
    rw [← dotProduct_transpose_mul_self ((sqrtPD A)⁻¹) (WithLp.ofLp x),
      transpose_eq_self hS.isHermitian, inv_sqrtPD_mul_self hA]
  · rw [waldStat_of_not_posDef hA, inv_sqrtPD_eq_zero_of_not_posDef hA]
    simp

/-! ### The spectral norm is at most the Frobenius norm -/

theorem norm_toEuclideanCLM_apply_le (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ‖toEuclideanCLM (𝕜 := ℝ) M x‖ ≤ frobNorm M * ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, frobNorm,
    ← Real.sqrt_mul (frobSq_nonneg M)]
  refine Real.sqrt_le_sqrt ?_
  have key : ∀ i : ι, ‖(toEuclideanCLM (𝕜 := ℝ) M x).ofLp i‖ ^ 2
      ≤ (∑ j, M i j ^ 2) * ∑ j, ‖(WithLp.ofLp x) j‖ ^ 2 := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun j => M i j) (fun j => (WithLp.ofLp x) j)
    have e : (toEuclideanCLM (𝕜 := ℝ) M x).ofLp i = ∑ j, M i j * (WithLp.ofLp x) j := by
      rw [Matrix.ofLp_toEuclideanCLM]
      simp [Matrix.mulVec, dotProduct]
    rw [e, Real.norm_eq_abs, sq_abs]
    refine h.trans_eq ?_
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  calc ∑ i, ‖(toEuclideanCLM (𝕜 := ℝ) M x).ofLp i‖ ^ 2
      ≤ ∑ _i : ι, ((∑ j, M _i j ^ 2) * ∑ j, ‖(WithLp.ofLp x) j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => key i
    _ = frobSq M * ∑ j, ‖(WithLp.ofLp x) j‖ ^ 2 := by rw [← Finset.sum_mul]; rfl

/-- `‖M‖ ≤ ‖M‖_F`: the spectral norm is dominated by the Frobenius norm. -/
theorem opNorm_le_frobNorm (M : Matrix ι ι ℝ) : ‖M‖ ≤ frobNorm M := by
  rw [Matrix.cstar_norm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ (frobNorm_nonneg M) (norm_toEuclideanCLM_apply_le M)

/-! ### The event `Σ̂ ≻ 0`, quantitatively -/

/-- A Hermitian matrix within spectral distance `t < 1` of the identity is positive definite,
since `‖I − 𝒦‖ ≤ t` gives `(1−t)I ⪯ 𝒦`. -/
theorem posDef_of_norm_sub_one_le {K : Matrix ι ι ℝ} (hK : K.IsHermitian) {t : ℝ}
    (ht : ‖K - 1‖ ≤ t) (ht1 : t < 1) : K.PosDef := by
  have hlower : (1 - t) • (1 : Matrix ι ι ℝ) ≤ K := by
    have hn : ‖(1 : Matrix ι ι ℝ) - K‖ ≤ t := by rw [norm_sub_rev]; exact ht
    have hh1 : ((1 : Matrix ι ι ℝ) - K).IsHermitian :=
      Matrix.IsHermitian.sub Matrix.isHermitian_one hK
    have h := le_smul_one_of_norm_le hh1 hn
    rw [Matrix.le_iff] at h ⊢
    have e : K - (1 - t) • (1 : Matrix ι ι ℝ) = t • (1 : Matrix ι ι ℝ) - (1 - K) := by module
    rw [e]; exact h
  exact posDef_of_le (Matrix.PosDef.one.smul (by linarith : (0 : ℝ) < 1 - t)) hlower

/-- With `𝒦 = Σ^{-1/2}Σ̂Σ^{-1/2}` and `ϑ = ‖𝒦 − I‖`, if
`ϑ ≤ t ≤ 1/2` then `Σ̂ ≻ 0` and the studentizing matrix `T = Σ̂^{-1/2}Σ^{1/2}` satisfies
`‖T − I‖_F² ≤ 3rt`, by Lemma SM.B.14. -/
theorem posDef_and_frobSq_studentizer_le_of_norm {C A : Matrix ι ι ℝ} (hC : C.PosDef)
    (hA : A.IsHermitian) {t : ℝ} (ht : ‖(sqrtPD C)⁻¹ * A * (sqrtPD C)⁻¹ - 1‖ ≤ t)
    (ht2 : t ≤ 1 / 2) :
    A.PosDef ∧ frobSq (studentizerMat A C - 1) ≤ 3 * Fintype.card ι * t := by
  set S : Matrix ι ι ℝ := (sqrtPD C)⁻¹ with hSdef
  have hSh : Sᴴ = S := (inv_sqrtPD_posDef hC).isHermitian.eq
  have hKherm : (S * A * S).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul (A := A) S hA
    rwa [hSh] at h
  have hK : (S * A * S).PosDef := posDef_of_norm_sub_one_le hKherm ht (by linarith)
  have hsqrtinj : Function.Injective (sqrtPD C).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (sqrtPD_posDef hC).isUnit
  have hAeq : (sqrtPD C)ᴴ * (S * A * S) * sqrtPD C = A := by
    rw [(sqrtPD_posDef hC).isHermitian.eq, hSdef]
    have e : sqrtPD C * ((sqrtPD C)⁻¹ * A * (sqrtPD C)⁻¹) * sqrtPD C
        = (sqrtPD C * (sqrtPD C)⁻¹) * A * ((sqrtPD C)⁻¹ * sqrtPD C) := by
      simp only [Matrix.mul_assoc]
    rw [e, sqrtPD_mul_inv hC, sqrtPD_inv_mul hC, Matrix.one_mul, Matrix.mul_one]
  have hApd : A.PosDef := by
    have h := hK.conjTranspose_mul_mul_same (B := sqrtPD C) hsqrtinj
    rwa [hAeq] at h
  exact ⟨hApd, frobSq_sqrt_sub_one_le hC hApd ht ht2⟩

/-- The same statement with the hypothesis on the Frobenius distance from `Σ`, via
`𝒦 − I = Σ^{-1/2}(Σ̂ − Σ)Σ^{-1/2}` and `opNorm_le_frobNorm`. -/
theorem posDef_and_frobSq_studentizer_le {C A : Matrix ι ι ℝ} (hC : C.PosDef)
    (hA : A.IsHermitian) (hsmall : ‖(sqrtPD C)⁻¹‖ ^ 2 * frobNorm (A - C) ≤ 1 / 2) :
    A.PosDef ∧ frobSq (studentizerMat A C - 1)
      ≤ 3 * Fintype.card ι * (‖(sqrtPD C)⁻¹‖ ^ 2 * frobNorm (A - C)) := by
  set S : Matrix ι ι ℝ := (sqrtPD C)⁻¹ with hSdef
  have hSCS : S * C * S = 1 :=
    inv_conj_eq_one (sqrtPD_mul_self hC.posSemidef) (sqrtPD_inv_mul hC) (sqrtPD_mul_inv hC)
  have hKsub : S * A * S - 1 = S * (A - C) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hSCS]
  have hnorm : ‖S * A * S - 1‖ ≤ ‖S‖ ^ 2 * frobNorm (A - C) := by
    rw [hKsub]
    calc ‖S * (A - C) * S‖ ≤ ‖S * (A - C)‖ * ‖S‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖S‖ * ‖A - C‖) * ‖S‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (‖S‖ * frobNorm (A - C)) * ‖S‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (opNorm_le_frobNorm _) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖S‖ ^ 2 * frobNorm (A - C) := by ring
  exact posDef_and_frobSq_studentizer_le_of_norm hC hA hnorm hsmall

/-! ### Measurability

If `Σ̂_n` is a random matrix then so is the studentizing matrix `T_n = Σ̂_n^{-1/2}Σ^{1/2}`, by
`CFC.measurable_sqrt` and the continuity of `Matrix.det` and `Matrix.adjugate`. -/

/-- The matrix inverse is measurable. `Matrix.inv` is `Ring.inverse A.det • A.adjugate`, and over
a field `Ring.inverse` is `Inv.inv`, so this is the measurability of `det`, of `adjugate` and of
real inversion. -/
theorem measurable_matrix_inv : Measurable fun M : Matrix ι ι ℝ => M⁻¹ := by
  have hdet : Measurable fun M : Matrix ι ι ℝ => M.det := (continuous_id.matrix_det).measurable
  have hadj : Measurable fun M : Matrix ι ι ℝ => M.adjugate :=
    (continuous_id.matrix_adjugate).measurable
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hdet.inv.mul hadj.eval_matrix

/-- The positive definite square root is measurable, by `CFC.measurable_sqrt`. -/
theorem measurable_sqrtPD : Measurable fun M : Matrix ι ι ℝ => sqrtPD M := CFC.measurable_sqrt

omit [DecidableEq ι] in
/-- Matrix multiplication of two measurable matrix-valued maps is measurable. -/
theorem measurable_matrix_mul {α : Type*} [MeasurableSpace α] {f g : α → Matrix ι ι ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a * g a := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => hf.eval_matrix.mul hg.eval_matrix

/-- The studentizing matrix is measurable in both its arguments. -/
theorem measurable_studentizerMat_comp {α : Type*} [MeasurableSpace α] {f g : α → Matrix ι ι ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => studentizerMat (f a) (g a) :=
  measurable_matrix_mul (measurable_matrix_inv.comp (measurable_sqrtPD.comp hf))
    (measurable_sqrtPD.comp hg)

/-- The studentizing matrix is measurable in its first argument. -/
theorem measurable_studentizerMat (C : Matrix ι ι ℝ) :
    Measurable fun M : Matrix ι ι ℝ => studentizerMat M C :=
  measurable_studentizerMat_comp measurable_id measurable_const

/-- `EuclideanSpace ℝ (ι × ι)` read back as a matrix; the inverse of `matVec`. -/
def unvecMat (b : EuclideanSpace ℝ (ι × ι)) : Matrix ι ι ℝ := Matrix.of fun i j => b (i, j)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem unvecMat_matVec (M : Matrix ι ι ℝ) : unvecMat (matVec M) = M := rfl

omit [Fintype ι] [DecidableEq ι] in
@[fun_prop]
theorem continuous_unvecMat : Continuous (unvecMat : EuclideanSpace ℝ (ι × ι) → Matrix ι ι ℝ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (i, j)).comp (EuclideanSpace.equiv (ι × ι) ℝ).continuous

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_matVec : Continuous (matVec : Matrix ι ι ℝ → EuclideanSpace ℝ (ι × ι)) :=
  (EuclideanSpace.equiv (ι × ι) ℝ).symm.continuous.comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)

omit [DecidableEq ι] in
theorem measurable_matVec : Measurable (matVec : Matrix ι ι ℝ → EuclideanSpace ℝ (ι × ι)) :=
  continuous_matVec.measurable

/-- The continuous map `(x, T) ↦ Tx`, with the matrix viewed as a vector of
`EuclideanSpace ℝ (ι × ι)` so that Slutsky's theorem applies. -/
noncomputable def waldVec (q : EuclideanSpace ℝ ι × EuclideanSpace ℝ (ι × ι)) :
    EuclideanSpace ℝ ι :=
  toEuclideanCLM (𝕜 := ℝ) (unvecMat q.2) q.1

theorem continuous_waldVec : Continuous (waldVec (ι := ι)) := by
  unfold waldVec
  fun_prop

theorem waldVec_mk (x : EuclideanSpace ℝ ι) (b : EuclideanSpace ℝ (ι × ι)) :
    waldVec (x, b) = toEuclideanCLM (𝕜 := ℝ) (unvecMat b) x := rfl

theorem waldVec_apply (x : EuclideanSpace ℝ ι) (T : Matrix ι ι ℝ) :
    waldVec (x, matVec T) = toEuclideanCLM (𝕜 := ℝ) T x := by
  rw [waldVec_mk, unvecMat_matVec]

theorem sqrtPD_eq_cfcSqrt (A : Matrix ι ι ℝ) : sqrtPD A = CFC.sqrt A := rfl

/-! ### The `ε`–`δ` form of the deterministic bound

One `δ` controls both positive definiteness and the studentizer. -/

/-- Given `ε > 0` there is a `δ > 0` such that every Hermitian `Σ̂` within Frobenius distance `δ`
of `Σ ≻ 0` is positive definite and has `‖Σ̂^{-1/2}Σ^{1/2} − I‖_F < ε`. -/
theorem exists_delta_studentizer {Sg : Matrix ι ι ℝ} (hSg : Sg.PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ A : Matrix ι ι ℝ, A.IsHermitian → frobNorm (A - Sg) < δ →
      A.PosDef ∧ frobNorm (studentizerMat A Sg - 1) < ε := by
  set κ₀ : ℝ := ‖(sqrtPD Sg)⁻¹‖ ^ 2 with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by positivity
  set κ : ℝ := κ₀ + 1 with hκ
  have hκ0 : 0 < κ := by positivity
  set c : ℝ := 3 * (Fintype.card ι : ℝ) + 1 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨min (1 / (2 * κ)) (ε ^ 2 / (c * κ)), lt_min (by positivity) (by positivity), ?_⟩
  intro A hAh hlt
  set f : ℝ := frobNorm (A - Sg) with hf
  have hf0 : 0 ≤ f := frobNorm_nonneg _
  have hd1 : f < 1 / (2 * κ) := lt_of_lt_of_le hlt (min_le_left _ _)
  have hd2 : f < ε ^ 2 / (c * κ) := lt_of_lt_of_le hlt (min_le_right _ _)
  have hmono : κ₀ * f ≤ κ * f := mul_le_mul_of_nonneg_right (by linarith) hf0
  have hhalf : κ₀ * f ≤ 1 / 2 := by
    have h1 : κ * f < κ * (1 / (2 * κ)) := mul_lt_mul_of_pos_left hd1 hκ0
    have h2 : κ * (1 / (2 * κ)) = 1 / 2 := by field_simp
    linarith
  obtain ⟨hpd, hfs⟩ := posDef_and_frobSq_studentizer_le hSg hAh hhalf
  refine ⟨hpd, ?_⟩
  have hkey : c * (κ * f) < ε ^ 2 := by
    have h1 : κ * f < κ * (ε ^ 2 / (c * κ)) := mul_lt_mul_of_pos_left hd2 hκ0
    have h2 : c * (κ * (ε ^ 2 / (c * κ))) = ε ^ 2 := by field_simp
    have h3 : c * (κ * f) < c * (κ * (ε ^ 2 / (c * κ))) := mul_lt_mul_of_pos_left h1 hc0
    linarith
  have hcompare : 3 * (Fintype.card ι : ℝ) * (κ₀ * f) ≤ c * (κ * f) :=
    mul_le_mul (by linarith) hmono (by positivity) hc0.le
  have hlt2 : frobSq (studentizerMat A Sg - 1) < ε ^ 2 := by linarith
  rw [frobNorm]
  calc Real.sqrt (frobSq (studentizerMat A Sg - 1))
      < Real.sqrt (ε ^ 2) := by
        exact Real.sqrt_lt_sqrt (frobSq_nonneg _) hlt2
    _ = ε := Real.sqrt_sq hε.le

/-- The version with a moving comparison matrix: one `δ` works for every positive definite `𝒱`,
because the hypothesis is on the ratio `𝒦 = 𝒱^{-1/2}𝒱̂𝒱^{-1/2}` rather than on `𝒱̂ − 𝒱`. -/
theorem exists_delta_studentizer_ratio {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ C A : Matrix ι ι ℝ, C.PosDef → A.IsHermitian →
      frobNorm ((sqrtPD C)⁻¹ * A * (sqrtPD C)⁻¹ - 1) < δ →
      A.PosDef ∧ frobNorm (studentizerMat A C - 1) < ε := by
  set c : ℝ := 3 * (Fintype.card ι : ℝ) + 1 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨min (1 / 2) (ε ^ 2 / c), lt_min (by norm_num) (by positivity), ?_⟩
  intro C A hC hA hlt
  set t : ℝ := frobNorm ((sqrtPD C)⁻¹ * A * (sqrtPD C)⁻¹ - 1) with htdef
  have ht0 : 0 ≤ t := frobNorm_nonneg _
  have hnorm : ‖(sqrtPD C)⁻¹ * A * (sqrtPD C)⁻¹ - 1‖ ≤ t := opNorm_le_frobNorm _
  have ht2 : t ≤ 1 / 2 := le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _))
  obtain ⟨hpd, hfs⟩ := posDef_and_frobSq_studentizer_le_of_norm hC hA hnorm ht2
  refine ⟨hpd, ?_⟩
  have hlt2 : frobSq (studentizerMat A C - 1) < ε ^ 2 := by
    have h1 : 3 * (Fintype.card ι : ℝ) * t ≤ c * t :=
      mul_le_mul_of_nonneg_right (by linarith) ht0
    have h2 : c * t < c * (ε ^ 2 / c) :=
      mul_lt_mul_of_pos_left (lt_of_lt_of_le hlt (min_le_right _ _)) hc0
    have h3 : c * (ε ^ 2 / c) = ε ^ 2 := by field_simp
    linarith
  rw [frobNorm]
  calc Real.sqrt (frobSq (studentizerMat A C - 1))
      < Real.sqrt (ε ^ 2) := Real.sqrt_lt_sqrt (frobSq_nonneg _) hlt2
    _ = ε := Real.sqrt_sq hε.le

/-! ### Transferring a limit law to another probability space

`TendstoInDistribution` depends on the limiting random variable only through its law, so a limit
stated for a variable on one probability space also holds for any variable with the same law on
another space. -/

theorem tendstoInDistribution_congr_law {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Ωa : Type*} {mΩa : MeasurableSpace Ωa} {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    {Ωb : Type*} {mΩb : MeasurableSpace Ωb} {Pb : Measure Ωb} [IsProbabilityMeasure Pb]
    {X : ℕ → Ω → E} {Za : Ωa → E} {Zb : Ωb → E}
    (h : TendstoInDistribution X atTop Za (fun _ => P) Pa)
    (hb : AEMeasurable Zb Pb) (heq : Pa.map Za = Pb.map Zb) :
    TendstoInDistribution X atTop Zb (fun _ => P) Pb := by
  refine ⟨h.forall_aemeasurable, hb, ?_⟩
  convert h.tendsto using 4
  exact congrArg _ (Subtype.ext heq.symm)

/-! ### The Slutsky core -/

section Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

set_option maxHeartbeats 1000000 in
/-- Slutsky's theorem for the studentized deviation. If `w_n ⟶^d N(0, I_r)` and `‖T_n − I_r‖_F ⟶^p 0`, then
`T_n w_n ⟶^d N(0, I_r)`. -/
theorem studentizedTendsto_of_studentizer
    {w : ℕ → Ω → EuclideanSpace ℝ ι} {T : ℕ → Ω → Matrix ι ι ℝ} {G : Ω' → EuclideanSpace ℝ ι}
    (hw : TendstoInDistribution w atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 1)
    (hTmeas : ∀ n, Measurable (T n))
    (hT : TendstoInMeasure P (fun n ω => frobNorm (T n ω - 1)) atTop (fun _ => 0)) :
    TendstoInDistribution (fun n ω => toEuclideanCLM (𝕜 := ℝ) (T n ω) (w n ω)) atTop
      (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (fun _ => P) (multivariateGaussian 0 1) := by
  rw [tendstoInMeasure_iff_dist] at hT
  have hY : TendstoInMeasure P (fun n ω => matVec (T n ω)) atTop
      (fun _ => matVec (1 : Matrix ι ι ℝ)) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine (hT ε hε).congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, dist_matVec, Real.dist_eq, sub_zero,
      abs_of_nonneg (frobNorm_nonneg _)]
  have hYm : ∀ n, AEMeasurable (fun ω => matVec (T n ω)) P :=
    fun n => (measurable_matVec.comp (hTmeas n)).aemeasurable
  have hslut := hw.continuous_comp_prodMk_of_tendstoInMeasure_const continuous_waldVec hY hYm
  have he1 : (fun n ω => waldVec (w n ω, matVec (T n ω)))
      = fun n ω => toEuclideanCLM (𝕜 := ℝ) (T n ω) (w n ω) := by
    funext n ω; exact waldVec_apply _ _
  have he2 : (fun ω' => waldVec (G ω', matVec (1 : Matrix ι ι ℝ))) = G := by
    funext ω'
    rw [waldVec_apply, map_one, one_apply_eq_self]
  rw [he1, he2] at hslut
  refine tendstoInDistribution_congr_law hslut (by fun_prop) ?_
  rw [hG, Measure.map_id]

/-- The Wald statistic converges in distribution to `χ²_r`, by the continuous mapping theorem
applied to `studentizedTendsto_of_studentizer` with `z ↦ ‖z‖²`. -/
theorem waldTendsto_of_studentizer
    {w : ℕ → Ω → EuclideanSpace ℝ ι} {T : ℕ → Ω → Matrix ι ι ℝ} {G : Ω' → EuclideanSpace ℝ ι}
    (hw : TendstoInDistribution w atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 1)
    (hTmeas : ∀ n, Measurable (T n))
    (hT : TendstoInMeasure P (fun n ω => frobNorm (T n ω - 1)) atTop (fun _ => 0)) :
    TendstoInDistribution (fun n ω => ‖toEuclideanCLM (𝕜 := ℝ) (T n ω) (w n ω)‖ ^ 2) atTop
      (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P) (multivariateGaussian 0 1) :=
  (studentizedTendsto_of_studentizer hw hG hTmeas hT).continuous_comp
    (g := fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (by fun_prop)

/-! ### The main lemma -/

/-- **The Wald lemma.** Let `A n` be Hermitian and measurable with `A n ⟶^p Sg ≻ 0` in
Frobenius norm, and let `u n ⟶^d N(0, Sg)` (the hypothesis `hCLT`). Then `P(A n ≻ 0) → 1` and
`waldStat (A n) (u n) ⟶^d χ²_r`. With `A n = 𝓡(a_n V̂_n)𝓡'` and `u n = √a_n 𝓡(θ̂_n − θ)` this is
the common shape of Theorems 7(b), 9(c) and 12(b); `a_n` cancels by `waldStat_smul`. -/
theorem wald_of_clt
    {Sg : Matrix ι ι ℝ} (hSg : Sg.PosDef)
    {A : ℕ → Ω → Matrix ι ι ℝ} (hAherm : ∀ n ω, (A n ω).IsHermitian)
    (hAmeas : ∀ n, Measurable (A n))
    (hA : TendstoInMeasure P (fun n ω => frobNorm (A n ω - Sg)) atTop (fun _ => 0))
    {u : ℕ → Ω → EuclideanSpace ℝ ι} {G : Ω' → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution u atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 Sg) :
    Tendsto (fun n => P {ω | (A n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution (fun n ω => waldStat (A n ω) (u n ω)) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P) (multivariateGaussian 0 1) := by
  rw [tendstoInMeasure_iff_dist] at hA
  have hAd : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => P {ω | δ ≤ frobNorm (A n ω - Sg)}) atTop (𝓝 0) := by
    intro δ hδ
    refine (hA δ hδ).congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (frobNorm_nonneg _)]
  set T : ℕ → Ω → Matrix ι ι ℝ := fun n ω => studentizerMat (A n ω) Sg with hTdef
  have hTmeas : ∀ n, Measurable (T n) := fun n => (measurable_studentizerMat Sg).comp (hAmeas n)
  have hTlim : TendstoInMeasure P (fun n ω => frobNorm (T n ω - 1)) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    obtain ⟨δ, hδ, hkey⟩ := exists_delta_studentizer hSg hε
    have hsub : ∀ n, {ω | ε ≤ dist (frobNorm (T n ω - 1)) ((fun _ : Ω => (0 : ℝ)) ω)}
        ⊆ {ω | δ ≤ frobNorm (A n ω - Sg)} := by
      intro n ω hω
      simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero,
        abs_of_nonneg (frobNorm_nonneg _)] at hω ⊢
      by_contra hcon
      rw [not_le] at hcon
      exact absurd (hkey (A n ω) (hAherm n ω) hcon).2 (not_lt.mpr hω)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hAd δ hδ)
      (fun _ => zero_le) (fun n => measure_mono (hsub n))
  refine ⟨?_, ?_⟩
  · obtain ⟨δ, hδ, hkey⟩ := exists_delta_studentizer hSg one_pos
    have hsub : ∀ n, {ω | ¬ (A n ω).PosDef} ⊆ {ω | δ ≤ frobNorm (A n ω - Sg)} := by
      intro n ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      by_contra hcon
      rw [not_le] at hcon
      exact hω (hkey (A n ω) (hAherm n ω) hcon).1
    have hc : Tendsto (fun n => P {ω | ¬ (A n ω).PosDef}) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hAd δ hδ)
        (fun _ => zero_le) (fun n => measure_mono (hsub n))
    have hlow : Tendsto (fun n => 1 - P {ω | ¬ (A n ω).PosDef}) atTop (𝓝 1) := by
      have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) hc
        (Or.inl ENNReal.one_ne_top)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
      (fun n => prob_le_one)
    refine tsub_le_iff_right.mpr ?_
    have hu : (Set.univ : Set Ω) = {ω | (A n ω).PosDef} ∪ {ω | ¬ (A n ω).PosDef} := by
      ext ω; simp [em]
    have h1 : P (Set.univ : Set Ω) ≤ P {ω | (A n ω).PosDef} + P {ω | ¬ (A n ω).PosDef} := by
      rw [hu]; exact measure_union_le _ _
    simpa using h1
  · have hstat : ∀ n ω, waldStat (A n ω) (u n ω)
        = ‖toEuclideanCLM (𝕜 := ℝ) (T n ω)
            (toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) (u n ω))‖ ^ 2 :=
      fun n ω => waldStat_eq_sq_norm (A n ω) hSg (u n ω)
    have hwlim : TendstoInDistribution
        (fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) (u n ω)) atTop
        (fun ω' => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) (G ω')) (fun _ => P) P' :=
      hCLT.continuous_comp (ContinuousLinearMap.continuous _)
    have hGmap : P'.map (fun ω' => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) (G ω'))
        = multivariateGaussian 0 1 := by
      have hGm : AEMeasurable G P' := hCLT.aemeasurable_limit
      have h1 : P'.map (fun ω' => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) (G ω'))
          = (P'.map G).map (fun x : EuclideanSpace ℝ ι =>
              toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) x) :=
        (AEMeasurable.map_map_of_aemeasurable (by fun_prop) hGm).symm
      rw [h1, hG, multivariateGaussian_zero_one, multivariateGaussian,
        Measure.map_map (by fun_prop) (by fun_prop)]
      have he : ((fun x : EuclideanSpace ℝ ι => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) x) ∘
          fun x : EuclideanSpace ℝ ι =>
            (0 : EuclideanSpace ℝ ι) + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sg) x) = id := by
        funext x
        simp only [Function.comp_apply, zero_add, id_eq, ← sqrtPD_eq_cfcSqrt]
        show (toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) * toEuclideanCLM (𝕜 := ℝ) (sqrtPD Sg)) x = x
        rw [← map_mul, sqrtPD_inv_mul hSg, map_one]
        rfl
      rw [he, Measure.map_id]
    have hmain := waldTendsto_of_studentizer hwlim hGmap hTmeas hTlim
    have heq : (fun n ω => waldStat (A n ω) (u n ω))
        = fun n ω => ‖toEuclideanCLM (𝕜 := ℝ) (T n ω)
            (toEuclideanCLM (𝕜 := ℝ) ((sqrtPD Sg)⁻¹) (u n ω))‖ ^ 2 := by
      funext n ω; exact hstat n ω
    rw [heq]
    exact hmain

/-- **The rate-agnostic Wald lemma** (Theorem 11(c)). If
`𝒱_n^{-1/2}𝒱̂_n𝒱_n^{-1/2} ⟶^p I_r` and `𝒱_n^{-1/2}𝓡_n(β̂ − β) ⟶^d N(0, I_r)`, then
`P(𝒱̂_n ≻ 0) → 1`, `𝟙{𝒱̂_n ≻ 0}𝒱̂_n^{-1/2}𝓡_n(β̂ − β) ⟶^d N(0, I_r)` and `𝒲 ⟶^d χ²_r`. The
normalizer `𝒱_n` is random and need not converge. -/
theorem wald_of_clt_rateAgnostic
    {V : ℕ → Ω → Matrix ι ι ℝ} (hV : ∀ n ω, (V n ω).PosDef) (hVmeas : ∀ n, Measurable (V n))
    {Vh : ℕ → Ω → Matrix ι ι ℝ} (hVhherm : ∀ n ω, (Vh n ω).IsHermitian)
    (hVhmeas : ∀ n, Measurable (Vh n))
    (hK : TendstoInMeasure P
      (fun n ω => frobNorm ((sqrtPD (V n ω))⁻¹ * Vh n ω * (sqrtPD (V n ω))⁻¹ - 1)) atTop
      (fun _ => 0))
    {x : ℕ → Ω → EuclideanSpace ℝ ι} {G : Ω' → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution
      (fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (V n ω))⁻¹) (x n ω)) atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 1) :
    Tendsto (fun n => P {ω | (Vh n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (Vh n ω))⁻¹) (x n ω)) atTop
          (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (fun _ => P) (multivariateGaussian 0 1)
      ∧ TendstoInDistribution (fun n ω => waldStat (Vh n ω) (x n ω)) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P) (multivariateGaussian 0 1) := by
  rw [tendstoInMeasure_iff_dist] at hK
  have hKd : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω |
      δ ≤ frobNorm ((sqrtPD (V n ω))⁻¹ * Vh n ω * (sqrtPD (V n ω))⁻¹ - 1)}) atTop (𝓝 0) := by
    intro δ hδ
    refine (hK δ hδ).congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (frobNorm_nonneg _)]
  set T : ℕ → Ω → Matrix ι ι ℝ := fun n ω => studentizerMat (Vh n ω) (V n ω) with hTdef
  have hTmeas : ∀ n, Measurable (T n) :=
    fun n => measurable_studentizerMat_comp (hVhmeas n) (hVmeas n)
  have hTlim : TendstoInMeasure P (fun n ω => frobNorm (T n ω - 1)) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    obtain ⟨δ, hδ, hkey⟩ := exists_delta_studentizer_ratio (ι := ι) hε
    have hsub : ∀ n, {ω | ε ≤ dist (frobNorm (T n ω - 1)) ((fun _ : Ω => (0 : ℝ)) ω)}
        ⊆ {ω | δ ≤ frobNorm ((sqrtPD (V n ω))⁻¹ * Vh n ω * (sqrtPD (V n ω))⁻¹ - 1)} := by
      intro n ω hω
      simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero,
        abs_of_nonneg (frobNorm_nonneg _)] at hω ⊢
      by_contra hcon
      rw [not_le] at hcon
      exact absurd (hkey (V n ω) (Vh n ω) (hV n ω) (hVhherm n ω) hcon).2 (not_lt.mpr hω)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hKd δ hδ)
      (fun _ => zero_le) (fun n => measure_mono (hsub n))
  have hvec := studentizedTendsto_of_studentizer hCLT hG hTmeas hTlim
  have hid : ∀ n ω, toEuclideanCLM (𝕜 := ℝ) (T n ω)
      (toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (V n ω))⁻¹) (x n ω))
      = toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (Vh n ω))⁻¹) (x n ω) :=
    fun n ω => studentizer_comp_invSqrt (Vh n ω) (hV n ω) (x n ω)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨δ, hδ, hkey⟩ := exists_delta_studentizer_ratio (ι := ι) one_pos
    have hsub : ∀ n, {ω | ¬ (Vh n ω).PosDef}
        ⊆ {ω | δ ≤ frobNorm ((sqrtPD (V n ω))⁻¹ * Vh n ω * (sqrtPD (V n ω))⁻¹ - 1)} := by
      intro n ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      by_contra hcon
      rw [not_le] at hcon
      exact hω (hkey (V n ω) (Vh n ω) (hV n ω) (hVhherm n ω) hcon).1
    have hc : Tendsto (fun n => P {ω | ¬ (Vh n ω).PosDef}) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hKd δ hδ)
        (fun _ => zero_le) (fun n => measure_mono (hsub n))
    have hlow : Tendsto (fun n => 1 - P {ω | ¬ (Vh n ω).PosDef}) atTop (𝓝 1) := by
      have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) hc
        (Or.inl ENNReal.one_ne_top)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
      (fun n => prob_le_one)
    refine tsub_le_iff_right.mpr ?_
    have hu : (Set.univ : Set Ω) = {ω | (Vh n ω).PosDef} ∪ {ω | ¬ (Vh n ω).PosDef} := by
      ext ω; simp [em]
    have h1 : P (Set.univ : Set Ω) ≤ P {ω | (Vh n ω).PosDef} + P {ω | ¬ (Vh n ω).PosDef} := by
      rw [hu]; exact measure_union_le _ _
    simpa using h1
  · have heq : (fun n ω => toEuclideanCLM (𝕜 := ℝ) (T n ω)
        (toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (V n ω))⁻¹) (x n ω)))
        = fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (Vh n ω))⁻¹) (x n ω) := by
      funext n ω; exact hid n ω
    rw [heq] at hvec
    exact hvec
  · have hmain := waldTendsto_of_studentizer hCLT hG hTmeas hTlim
    have heq : (fun n ω => waldStat (Vh n ω) (x n ω))
        = fun n ω => ‖toEuclideanCLM (𝕜 := ℝ) (T n ω)
            (toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (V n ω))⁻¹) (x n ω))‖ ^ 2 := by
      funext n ω
      exact waldStat_eq_sq_norm (Vh n ω) (hV n ω) (x n ω)
    rw [heq]
    exact hmain

end Probability

/-! ### A model for the Wald lemma

The hypotheses of `wald_of_clt` hold with `Σ = I_r`, the constant sequence `Σ̂_n = I_r` and the
identity on `(EuclideanSpace ℝ ι, N(0, I_r))`. At `Σ̂ = I_r` the Wald
statistic is `‖x‖²` (`waldStat_one`). -/

theorem waldStat_one (x : EuclideanSpace ℝ ι) : waldStat (1 : Matrix ι ι ℝ) x = ‖x‖ ^ 2 := by
  rw [waldStat_of_posDef Matrix.PosDef.one, inv_one, ← Matrix.inner_toEuclideanCLM,
    map_one, one_apply_eq_self]
  exact real_inner_self_eq_norm_sq x

/-- The hypotheses of `wald_of_clt` hold for an explicit model, and its conclusions follow. -/
theorem wald_of_clt_witness :
    Tendsto (fun _ : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
        {_x : EuclideanSpace ℝ ι | (1 : Matrix ι ι ℝ).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun (_ : ℕ) (y : EuclideanSpace ℝ ι) => waldStat (1 : Matrix ι ι ℝ) y) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2)
          (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
          (multivariateGaussian 0 1) := by
  refine wald_of_clt (P := multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) (Sg := 1) Matrix.PosDef.one
    (A := fun _ _ => (1 : Matrix ι ι ℝ)) (fun _ _ => Matrix.isHermitian_one)
    (fun _ => measurable_const) ?_ (u := fun _ => id) (G := id)
    (tendstoInDistribution_const aemeasurable_id) ?_
  · intro ε hε
    have hz : frobNorm ((1 : Matrix ι ι ℝ) - 1) = 0 := by
      simp [frobNorm, frobSq]
    have hset : {y : EuclideanSpace ℝ ι |
        ε ≤ edist (frobNorm ((1 : Matrix ι ι ℝ) - 1)) ((fun _ => (0 : ℝ)) y)} = ∅ := by
      ext y
      simp only [hz, edist_self, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    simp only [hset, measure_empty]
    exact tendsto_const_nhds
  · exact Measure.map_id
