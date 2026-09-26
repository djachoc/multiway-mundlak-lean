import Multiway.Restricted
import Multiway.Concentration
import Multiway.Sharing
import Multiway.Wald
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Rate-agnostic inference under multiway clustering

This file formalizes parts (a) and (b) of Theorem 11 of the paper (rate-agnostic inference
under multiway clustering) together with Lemma SM.B.13 (the infeasible union meat), whose
convergence statement is the input to part (a). Part (c) is
`Multiway.Wald.wald_of_clt_rateAgnostic`. Eigenvalue bounds are carried in Loewner form,
`c • I ≤ Ω_n` and `Ω ≤ κ • I`, so `λ_min` and `λ_max` are never formed.

## Main results

* `rateAgnostic_a`, `rateAgnostic_b`: Theorem 11(a) and (b).
* `infeasibleMeat_condVar_le_of_regime3`: the conditional variance bound of Lemma SM.B.13.
* `infeasibleMeat_tendstoInProb_of_regime3`: `‖𝓜̃_n - Ω_n‖_F / λ_min(Ω_n) → 0` in probability.
* `perturb_tendstoInProb_of_accum`: `‖𝓜̂_CGM - 𝓜̃_n‖_F / λ_min(Ω_n) → 0` in probability.
* `tendstoInMeasure_zero_of_condExp_le`: convergence in probability from a conditional
  first-moment bound by a random majorant that converges in probability.
-/

namespace Multiway
namespace RateAgnostic

open Filter Finset Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

/-! ### The Frobenius norm against the spectral norm -/

section Frobenius

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype γ] [DecidableEq γ]

omit [DecidableEq α] [DecidableEq β] in
/-- The squared Frobenius norm read down the columns. -/
theorem rectFrobSq_eq_sum_col (F : Matrix α β ℝ) :
    rectFrobSq F = ∑ j : β, ∑ i : α, F i j ^ 2 := by
  rw [rectFrobSq]
  exact Finset.sum_comm

omit [DecidableEq α] [DecidableEq β] in
/-- `‖Py‖² ≤ ‖P‖²‖y‖²`, written in coordinates: `Matrix.l2_opNorm_mulVec` with both sides
squared. -/
theorem sum_sq_mulVec_le (P : Matrix α γ ℝ) (y : γ → ℝ) :
    ∑ i : α, (P *ᵥ y) i ^ 2 ≤ ‖P‖ ^ 2 * ∑ k : γ, y k ^ 2 := by
  have h : ‖(EuclideanSpace.equiv α ℝ).symm (P *ᵥ y)‖
      ≤ ‖P‖ * ‖(EuclideanSpace.equiv γ ℝ).symm y‖ :=
    Matrix.l2_opNorm_mulVec P ((EuclideanSpace.equiv γ ℝ).symm y)
  have hl : ∑ i : α, (P *ᵥ y) i ^ 2 = ‖(EuclideanSpace.equiv α ℝ).symm (P *ᵥ y)‖ ^ 2 := by
    rw [← dot_self_eq]
    simp [dotProduct, sq]
  have hr : ∑ k : γ, y k ^ 2 = ‖(EuclideanSpace.equiv γ ℝ).symm y‖ ^ 2 := by
    rw [← dot_self_eq]
    simp [dotProduct, sq]
  rw [hl, hr]
  have hnn : (0 : ℝ) ≤ ‖(EuclideanSpace.equiv α ℝ).symm (P *ᵥ y)‖ := norm_nonneg _
  nlinarith [mul_self_le_mul_self hnn h]

omit [DecidableEq α] [DecidableEq β] in
/-- `‖PM‖_F ≤ ‖P‖‖M‖_F`, squared, where `‖P‖` is the l2 operator norm. -/
theorem rectFrobSq_mul_left_le (P : Matrix α γ ℝ) (M : Matrix γ β ℝ) :
    rectFrobSq (P * M) ≤ ‖P‖ ^ 2 * rectFrobSq M := by
  rw [rectFrobSq_eq_sum_col, rectFrobSq_eq_sum_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ∀ i : α, (P * M) i j = (P *ᵥ fun k : γ => M k j) i := by
    intro i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  calc ∑ i : α, ((P * M) i j) ^ 2 = ∑ i : α, ((P *ᵥ fun k : γ => M k j) i) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [h1 i]
    _ ≤ ‖P‖ ^ 2 * ∑ k : γ, (M k j) ^ 2 := sum_sq_mulVec_le P _

omit [DecidableEq α] in
/-- `‖MQ‖_F ≤ ‖Q‖‖M‖_F`, squared; obtained from `rectFrobSq_mul_left_le` by transposition. -/
theorem rectFrobSq_mul_right_le (M : Matrix α γ ℝ) (Q : Matrix γ β ℝ) :
    rectFrobSq (M * Q) ≤ ‖Q‖ ^ 2 * rectFrobSq M := by
  have ht : rectFrobSq (M * Q) = rectFrobSq (Qᵀ * Mᵀ) := by
    rw [← Matrix.transpose_mul, rectFrobSq_transpose]
  have hQ : ‖Qᵀ‖ = ‖Q‖ := by
    rw [← conjTranspose_eq_transpose]
    exact Matrix.l2_opNorm_conjTranspose Q
  rw [ht, ← hQ, ← rectFrobSq_transpose M]
  exact rectFrobSq_mul_left_le Qᵀ Mᵀ

/-- The vectorization of a rectangular matrix, used to transfer the triangle inequality to
`rectFrobNorm`. -/
noncomputable def rectVec (F : Matrix α β ℝ) : EuclideanSpace ℝ (α × β) :=
  (EuclideanSpace.equiv (α × β) ℝ).symm fun p => F p.1 p.2

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] theorem rectVec_apply (F : Matrix α β ℝ) (p : α × β) : rectVec F p = F p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem rectVec_sub (X Y : Matrix α β ℝ) : rectVec (X - Y) = rectVec X - rectVec Y := by
  ext p; simp

omit [DecidableEq α] [DecidableEq β] in
/-- The Euclidean norm of `rectVec F` is `‖F‖_F`. -/
theorem norm_rectVec (F : Matrix α β ℝ) : ‖rectVec F‖ = rectFrobNorm F := by
  rw [EuclideanSpace.norm_eq, rectFrobNorm, rectFrobSq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show ‖(rectVec F).ofLp (i, j)‖ = ‖F i j‖ from rfl, Real.norm_eq_abs, sq_abs]

omit [DecidableEq α] [DecidableEq β] in
/-- The triangle inequality for `‖·‖_F` in three-point form:
`‖X - Z‖_F ≤ ‖X - Y‖_F + ‖Y - Z‖_F`. -/
theorem rectFrobNorm_sub_le (X Y Z : Matrix α β ℝ) :
    rectFrobNorm (X - Z) ≤ rectFrobNorm (X - Y) + rectFrobNorm (Y - Z) := by
  rw [← norm_rectVec, ← norm_rectVec, ← norm_rectVec, rectVec_sub, rectVec_sub, rectVec_sub]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- `‖A'EA‖_F ≤ ‖A‖²‖E‖_F` for square `E` and rectangular `A`. -/
theorem rectFrobNorm_conj_le (A : Matrix α β ℝ) (E : Matrix α α ℝ) :
    rectFrobNorm (Aᵀ * E * A) ≤ ‖A‖ ^ 2 * rectFrobNorm E := by
  have hA : ‖Aᵀ‖ = ‖A‖ := by
    rw [← conjTranspose_eq_transpose]
    exact Matrix.l2_opNorm_conjTranspose A
  have h1 : rectFrobSq (Aᵀ * E * A) ≤ ‖A‖ ^ 2 * (‖A‖ ^ 2 * rectFrobSq E) := by
    calc rectFrobSq (Aᵀ * E * A) ≤ ‖A‖ ^ 2 * rectFrobSq (Aᵀ * E) :=
          rectFrobSq_mul_right_le _ _
      _ ≤ ‖A‖ ^ 2 * (‖A‖ ^ 2 * rectFrobSq E) := by
          have := rectFrobSq_mul_left_le Aᵀ E
          rw [hA] at this
          exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have h2 : rectFrobNorm (Aᵀ * E * A) ≤ Real.sqrt (‖A‖ ^ 2 * (‖A‖ ^ 2 * rectFrobSq E)) := by
    rw [rectFrobNorm]
    exact Real.sqrt_le_sqrt h1
  refine h2.trans (le_of_eq ?_)
  have h3 : ‖A‖ ^ 2 * (‖A‖ ^ 2 * rectFrobSq E) = (‖A‖ ^ 2) ^ 2 * rectFrobSq E := by ring
  rw [h3, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), rectFrobNorm]

end Frobenius

/-! ### Theorem 11(a), the deterministic bounds -/

section PartADeterministic

variable {κ r : Type*} [Fintype κ] [DecidableEq κ] [Fintype r] [DecidableEq r]

omit [DecidableEq κ] [Fintype r] [DecidableEq r] in
/-- On a square matrix `frobNorm` and `rectFrobNorm` agree definitionally. -/
theorem frobNorm_eq_rectFrobNorm (M : Matrix κ κ ℝ) : frobNorm M = rectFrobNorm M := rfl

omit [Fintype r] [DecidableEq r] in
/-- `G_n` at `A = I_K` is `Ω_n^{-1/2}`. -/
theorem restrictedStd_one (Om : Matrix κ κ ℝ) : restrictedStd Om 1 = (sqrtPD Om)⁻¹ := by
  simp [restrictedStd]

omit [Fintype r] [DecidableEq r] in
/-- `‖Ω_n^{-1/2}‖² ≤ 1/λ_min(Ω_n)`: the restricted standardization bound at `A = I_K`. -/
theorem sq_opNorm_inv_sqrtPD_le {Om : Matrix κ κ ℝ} (hOm : Om.PosDef) {c : ℝ} (hc : 0 < c)
    (hcOm : c • (1 : Matrix κ κ ℝ) ≤ Om) : ‖(sqrtPD Om)⁻¹‖ ^ 2 ≤ c⁻¹ := by
  have hinj : Function.Injective (1 : Matrix κ κ ℝ).mulVec := by
    intro a b hab
    simpa [Matrix.one_mulVec] using hab
  have h := sq_l2_opNorm_restrictedStd_le hOm hinj hc hcOm
  rwa [restrictedStd_one] at h

omit [Fintype r] [DecidableEq r] in
/-- Theorem 11(a), first claim, deterministically:
`‖Ω_n^{-1/2}E_nΩ_n^{-1/2}‖_F ≤ ‖E_n‖_F/λ_min(Ω_n)` with `E_n = 𝓜̃_n - Ω_n`. -/
theorem rectFrobNorm_standardized_le {Om : Matrix κ κ ℝ} (hOm : Om.PosDef) {c : ℝ} (hc : 0 < c)
    (hcOm : c • (1 : Matrix κ κ ℝ) ≤ Om) (Mt : Matrix κ κ ℝ) :
    rectFrobNorm ((sqrtPD Om)⁻¹ * (Mt - Om) * (sqrtPD Om)⁻¹)
      ≤ rectFrobNorm (Mt - Om) / c := by
  have hsym : ((sqrtPD Om)⁻¹ : Matrix κ κ ℝ)ᵀ = (sqrtPD Om)⁻¹ :=
    transpose_eq_self (sqrtPD_posDef hOm).inv.isHermitian
  have h1 := rectFrobNorm_conj_le ((sqrtPD Om)⁻¹) (Mt - Om)
  rw [hsym] at h1
  refine h1.trans ?_
  calc ‖(sqrtPD Om)⁻¹‖ ^ 2 * rectFrobNorm (Mt - Om)
      ≤ c⁻¹ * rectFrobNorm (Mt - Om) :=
        mul_le_mul_of_nonneg_right (sq_opNorm_inv_sqrtPD_le hOm hc hcOm) (rectFrobNorm_nonneg _)
    _ = rectFrobNorm (Mt - Om) / c := by rw [inv_mul_eq_div]

omit [DecidableEq κ] in
/-- `𝒱_n^{-1/2}𝒱̃_n𝒱_n^{-1/2} - I_r = G_n'E_nG_n`, for `𝒱_n = A'Ω_nA`, `𝒱̃_n = A'𝓜̃_nA` and
`G_n = restrictedStd Om A`. -/
theorem ratio_sub_one_eq {Om : Matrix κ κ ℝ} (hOm : Om.PosDef) {A : Matrix κ r ℝ}
    (hA : Function.Injective A.mulVec) (Mt : Matrix κ κ ℝ) :
    (sqrtPD (Aᵀ * Om * A))⁻¹ * (Aᵀ * Mt * A) * (sqrtPD (Aᵀ * Om * A))⁻¹ - 1
      = (restrictedStd Om A)ᵀ * (Mt - Om) * restrictedStd Om A := by
  set V := Aᵀ * Om * A with hVdef
  have hV : V.PosDef := posDef_restricted hOm hA
  set S := sqrtPD V with hSdef
  have hSi : ((S⁻¹)ᵀ : Matrix r r ℝ) = S⁻¹ :=
    transpose_eq_self (sqrtPD_posDef hV).inv.isHermitian
  have hGt : (restrictedStd Om A)ᵀ = S⁻¹ * Aᵀ := by
    rw [restrictedStd, Matrix.transpose_mul, hSi]
  have hone : S⁻¹ * V * S⁻¹ = 1 :=
    inv_conj_eq_one (sqrtPD_mul_self hV.posSemidef) (sqrtPD_inv_mul hV) (sqrtPD_mul_inv hV)
  rw [hGt, restrictedStd]
  have hexp : S⁻¹ * Aᵀ * (Mt - Om) * (A * S⁻¹)
      = S⁻¹ * (Aᵀ * Mt * A) * S⁻¹ - S⁻¹ * V * S⁻¹ := by
    rw [hVdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  rw [hexp, hone]

/-- Theorem 11(a), second claim, deterministically:
`‖𝒱_n^{-1/2}𝒱̃_n𝒱_n^{-1/2} - I_r‖_F ≤ ‖E_n‖_F/λ_min(Ω_n)`. -/
theorem rectFrobNorm_ratio_sub_one_le {Om : Matrix κ κ ℝ} (hOm : Om.PosDef) {A : Matrix κ r ℝ}
    (hA : Function.Injective A.mulVec) {c : ℝ} (hc : 0 < c)
    (hcOm : c • (1 : Matrix κ κ ℝ) ≤ Om) (Mt : Matrix κ κ ℝ) :
    rectFrobNorm ((sqrtPD (Aᵀ * Om * A))⁻¹ * (Aᵀ * Mt * A) * (sqrtPD (Aᵀ * Om * A))⁻¹ - 1)
      ≤ rectFrobNorm (Mt - Om) / c := by
  rw [ratio_sub_one_eq hOm hA Mt]
  refine (rectFrobNorm_conj_le (restrictedStd Om A) (Mt - Om)).trans ?_
  calc ‖restrictedStd Om A‖ ^ 2 * rectFrobNorm (Mt - Om)
      ≤ c⁻¹ * rectFrobNorm (Mt - Om) :=
        mul_le_mul_of_nonneg_right (sq_l2_opNorm_restrictedStd_le hOm hA hc hcOm)
          (rectFrobNorm_nonneg _)
    _ = rectFrobNorm (Mt - Om) / c := by rw [inv_mul_eq_div]

end PartADeterministic

/-! ### Theorem 11(a) -/

section PartA

variable {κ r : Type*} [Fintype κ] [DecidableEq κ] [Fintype r] [DecidableEq r]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Convergence in probability to zero passes to a nonnegative dominated sequence. -/
theorem tendstoInMeasure_zero_of_le {f g : ℕ → Ω → ℝ} (hnn : ∀ n ω, 0 ≤ f n ω)
    (hle : ∀ n ω, f n ω ≤ g n ω)
    (hg : TendstoInMeasure P g atTop (fun _ => 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε)
    (fun _ => zero_le) (fun n => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  rw [abs_of_nonneg (hnn n ω)] at hω
  exact hω.trans ((hle n ω).trans (le_abs_self _))

/-- **Theorem 11(a).** If `‖𝓜̃_n - Ω_n‖_F/λ_min(Ω_n) → 0` in probability, then
`‖Ω_n^{-1/2}(𝓜̃_n - Ω_n)Ω_n^{-1/2}‖_F → 0` and `‖𝒱_n^{-1/2}𝒱̃_n𝒱_n^{-1/2} - I_r‖_F → 0` in
probability. Here `c n ω` is a lower Loewner bound for `Ω_n`. -/
theorem rateAgnostic_a
    {Om : ℕ → Ω → Matrix κ κ ℝ} (hOm : ∀ n ω, (Om n ω).PosDef)
    {c : ℕ → Ω → ℝ} (hc : ∀ n ω, 0 < c n ω)
    (hcOm : ∀ n ω, c n ω • (1 : Matrix κ κ ℝ) ≤ Om n ω)
    {Mt : ℕ → Ω → Matrix κ κ ℝ}
    (hE : TendstoInMeasure P (fun n ω => rectFrobNorm (Mt n ω - Om n ω) / c n ω) atTop
      (fun _ => 0))
    {A : ℕ → Ω → Matrix κ r ℝ} (hA : ∀ n ω, Function.Injective (A n ω).mulVec) :
    TendstoInMeasure P
        (fun n ω => rectFrobNorm ((sqrtPD (Om n ω))⁻¹ * (Mt n ω - Om n ω) * (sqrtPD (Om n ω))⁻¹))
        atTop (fun _ => 0)
      ∧ TendstoInMeasure P
        (fun n ω => rectFrobNorm ((sqrtPD ((A n ω)ᵀ * Om n ω * A n ω))⁻¹
            * ((A n ω)ᵀ * Mt n ω * A n ω) * (sqrtPD ((A n ω)ᵀ * Om n ω * A n ω))⁻¹ - 1))
        atTop (fun _ => 0) := by
  refine ⟨tendstoInMeasure_zero_of_le (fun _ _ => rectFrobNorm_nonneg _) (fun n ω => ?_) hE,
    tendstoInMeasure_zero_of_le (fun _ _ => rectFrobNorm_nonneg _) (fun n ω => ?_) hE⟩
  · exact rectFrobNorm_standardized_le (hOm n ω) (hc n ω) (hcOm n ω) (Mt n ω)
  · exact rectFrobNorm_ratio_sub_one_le (hOm n ω) (hA n ω) (hc n ω) (hcOm n ω) (Mt n ω)

/-- Convergence in probability to zero is closed under addition. -/
theorem tendstoInMeasure_zero_add {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure P f atTop (fun _ => 0))
    (hg : TendstoInMeasure P g atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => f n ω + g n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hf hg ⊢
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  have hsum : Tendsto (fun n => P {ω | ε / 2 ≤ dist (f n ω) ((fun _ => (0 : ℝ)) ω)}
      + P {ω | ε / 2 ≤ dist (g n ω) ((fun _ => (0 : ℝ)) ω)}) atTop (𝓝 0) := by
    simpa using (hf (ε / 2) hhalf).add (hg (ε / 2) hhalf)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, Set.mem_union] at hω ⊢
  rcases le_or_gt (ε / 2) |f n ω| with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith [abs_add_le (f n ω) (g n ω)])

/-- **Theorem 11(b).** If in addition `‖𝓜̂_CGM - 𝓜̃_n‖_F/λ_min(Ω_n) → 0` in probability, then
the two conclusions of part (a) hold with `𝓜̂_CGM` in place of `𝓜̃_n`, and
`P(𝒱̂_n ≻ 0) → 1`. -/
theorem rateAgnostic_b [IsProbabilityMeasure P]
    {Om : ℕ → Ω → Matrix κ κ ℝ} (hOm : ∀ n ω, (Om n ω).PosDef)
    {cn : ℕ → Ω → ℝ} (hc : ∀ n ω, 0 < cn n ω)
    (hcOm : ∀ n ω, cn n ω • (1 : Matrix κ κ ℝ) ≤ Om n ω)
    {Mt Mh : ℕ → Ω → Matrix κ κ ℝ}
    (hE : TendstoInMeasure P (fun n ω => rectFrobNorm (Mt n ω - Om n ω) / cn n ω) atTop
      (fun _ => 0))
    (hperturb : TendstoInMeasure P (fun n ω => rectFrobNorm (Mh n ω - Mt n ω) / cn n ω) atTop
      (fun _ => 0))
    {A : ℕ → Ω → Matrix κ r ℝ} (hA : ∀ n ω, Function.Injective (A n ω).mulVec)
    (hHerm : ∀ n ω, ((A n ω)ᵀ * Mh n ω * A n ω).IsHermitian) :
    TendstoInMeasure P
        (fun n ω => rectFrobNorm ((sqrtPD (Om n ω))⁻¹ * (Mh n ω - Om n ω) * (sqrtPD (Om n ω))⁻¹))
        atTop (fun _ => 0)
      ∧ TendstoInMeasure P
        (fun n ω => rectFrobNorm ((sqrtPD ((A n ω)ᵀ * Om n ω * A n ω))⁻¹
            * ((A n ω)ᵀ * Mh n ω * A n ω) * (sqrtPD ((A n ω)ᵀ * Om n ω * A n ω))⁻¹ - 1))
        atTop (fun _ => 0)
      ∧ Tendsto (fun n => P {ω | ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}) atTop (𝓝 1) := by
  -- part (a) and the triangle inequality
  have hEh : TendstoInMeasure P (fun n ω => rectFrobNorm (Mh n ω - Om n ω) / cn n ω) atTop
      (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_le
      (fun n ω => div_nonneg (rectFrobNorm_nonneg _) (hc n ω).le) (fun n ω => ?_)
      (tendstoInMeasure_zero_add hperturb hE)
    rw [← add_div]
    exact div_le_div_of_nonneg_right (rectFrobNorm_sub_le _ (Mt n ω) _) (hc n ω).le
  obtain ⟨h1, h2⟩ := rateAgnostic_a hOm hc hcOm hEh hA
  refine ⟨h1, h2, ?_⟩
  -- `𝒱̂_n ≻ 0` once the standardized difference has spectral norm below one
  obtain ⟨δ, hδ, hkey⟩ := Wald.exists_delta_studentizer_ratio (ι := r) one_pos
  rw [tendstoInMeasure_iff_dist] at h2
  have hbad : Tendsto (fun n => P {ω | ¬ ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h2 δ hδ)
      (fun _ => zero_le) (fun n => measure_mono ?_)
    intro ω hω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg (rectFrobNorm_nonneg _)] at hω ⊢
    by_contra hcon
    rw [not_le] at hcon
    exact hω (hkey ((A n ω)ᵀ * Om n ω * A n ω) ((A n ω)ᵀ * Mh n ω * A n ω)
      (posDef_restricted (hOm n ω) (hA n ω)) (hHerm n ω) hcon).1
  have hlow : Tendsto (fun n => 1 - P {ω | ¬ ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}) atTop (𝓝 1) := by
    have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) hbad
      (Or.inl ENNReal.one_ne_top)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun _ => prob_le_one)
  refine tsub_le_iff_right.mpr ?_
  have hu : (Set.univ : Set Ω) = {ω | ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}
      ∪ {ω | ¬ ((A n ω)ᵀ * Mh n ω * A n ω).PosDef} := by
    ext ω; simp [em]
  have h1' : P (Set.univ : Set Ω) ≤ P {ω | ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}
      + P {ω | ¬ ((A n ω)ᵀ * Mh n ω * A n ω).PosDef} := by
    rw [hu]; exact measure_union_le _ _
  simpa using h1'

end PartA

/-! ### Conditional-expectation tools

The conditional variance of a finite sum as a double sum, the fourth-moment bound
`|E[ν₁ν₂ν₃ν₄ ∣ 𝒟]| ≤ C` from the pointwise Young inequality, and a conditional Markov
inequality. -/

section Conditional

-- `𝒟` precedes the ambient `mΩ`, so that `mΩ` is the instance used by synthesis.
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The square of a sum over a `Finset`, expanded as a double sum. -/
theorem sq_finsetSum_eq_double_sum {J : Type*} (S : Finset J) (ζ : J → Ω → ℝ) :
    (fun ω => (∑ p ∈ S, ζ p ω) ^ 2) = ∑ p ∈ S, ∑ q ∈ S, (fun ω => ζ p ω * ζ q ω) := by
  funext ω
  simp only [Finset.sum_apply]
  rw [sq, Finset.sum_mul_sum]

/-- The conditional second moment of a finite sum is the double sum of the conditional
second moments of pairs of summands. For centered summands this is
`Var[(𝓜̃_n)_{kl} ∣ 𝒟] = ∑_{o₁∼o₂}∑_{o₃∼o₄} Cov(ξ_{o₁o₂},ξ_{o₃o₄} ∣ 𝒟)`. -/
theorem condExp_sq_sum_eq {J : Type*} (S : Finset J) (ζ : J → Ω → ℝ)
    (hint : ∀ p ∈ S, ∀ q ∈ S, Integrable (fun ω => ζ p ω * ζ q ω) μ) :
    μ[fun ω => (∑ p ∈ S, ζ p ω) ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ p ∈ S, ∑ q ∈ S, (μ[fun ω => ζ p ω * ζ q ω | 𝒟]) ω := by
  classical
  rw [sq_finsetSum_eq_double_sum S ζ]
  have h1 := condExp_finsetSum (μ := μ) (s := S)
    (f := fun p : J => ∑ q ∈ S, (fun ω => ζ p ω * ζ q ω))
    (fun p hp => integrable_finsetSum' _ fun q hq => hint p hp q hq) 𝒟
  have h2 : ∀ᵐ ω ∂μ, ∀ p ∈ S,
      (μ[∑ q ∈ S, (fun ω => ζ p ω * ζ q ω) | 𝒟]) ω
        = ∑ q ∈ S, (μ[fun ω => ζ p ω * ζ q ω | 𝒟]) ω := by
    rw [Filter.eventually_all_finset]
    intro p hp
    filter_upwards [condExp_finsetSum (μ := μ) (s := S)
      (f := fun q : J => (fun ω => ζ p ω * ζ q ω)) (fun q hq => hint p hp q hq) 𝒟] with ω hω
    rw [hω, Finset.sum_apply]
  filter_upwards [h1, h2] with ω e1 e2
  rw [e1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun p hp => e2 p hp

/-- If each of `a, b, d, e` has conditional fourth moment at most `C`, then
`|E[abde ∣ 𝒟]| ≤ C`. The proof uses the pointwise inequality `4|abde| ≤ a⁴ + b⁴ + d⁴ + e⁴`
and monotonicity of `condExp`, without a conditional Hölder inequality. -/
theorem abs_condExp_prod_four_le {a b d e : Ω → ℝ} {Cm : ℝ}
    (hprod : Integrable (fun ω => a ω * b ω * (d ω * e ω)) μ)
    (ha : Integrable (fun ω => a ω ^ 4) μ) (hb : Integrable (fun ω => b ω ^ 4) μ)
    (hd : Integrable (fun ω => d ω ^ 4) μ) (he : Integrable (fun ω => e ω ^ 4) μ)
    (hma : ∀ᵐ ω ∂μ, (μ[fun ω => a ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hmb : ∀ᵐ ω ∂μ, (μ[fun ω => b ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hmd : ∀ᵐ ω ∂μ, (μ[fun ω => d ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hme : ∀ᵐ ω ∂μ, (μ[fun ω => e ω ^ 4 | 𝒟]) ω ≤ Cm) :
    ∀ᵐ ω ∂μ, |(μ[fun ω => a ω * b ω * (d ω * e ω) | 𝒟]) ω| ≤ Cm := by
  have hg : Integrable ((fun ω => a ω ^ 4) + (fun ω => b ω ^ 4) + (fun ω => d ω ^ 4)
      + (fun ω => e ω ^ 4) : Ω → ℝ) μ := ((ha.add hb).add hd).add he
  have hf4 : Integrable ((4 : ℝ) • (fun ω => a ω * b ω * (d ω * e ω)) : Ω → ℝ) μ :=
    hprod.smul (4 : ℝ)
  -- the pointwise bound `4|abde| ≤ a⁴+b⁴+d⁴+e⁴`, in both directions
  have hup : ((4 : ℝ) • (fun ω => a ω * b ω * (d ω * e ω)) : Ω → ℝ)
      ≤ᵐ[μ] ((fun ω => a ω ^ 4) + (fun ω => b ω ^ 4) + (fun ω => d ω ^ 4)
        + (fun ω => e ω ^ 4) : Ω → ℝ) := by
    filter_upwards with ω
    show 4 * (a ω * b ω * (d ω * e ω)) ≤ a ω ^ 4 + b ω ^ 4 + d ω ^ 4 + e ω ^ 4
    nlinarith [sq_nonneg (a ω * b ω - d ω * e ω), sq_nonneg (a ω ^ 2 - b ω ^ 2),
      sq_nonneg (d ω ^ 2 - e ω ^ 2)]
  have hlo : (-((fun ω => a ω ^ 4) + (fun ω => b ω ^ 4) + (fun ω => d ω ^ 4)
        + (fun ω => e ω ^ 4)) : Ω → ℝ)
      ≤ᵐ[μ] ((4 : ℝ) • (fun ω => a ω * b ω * (d ω * e ω)) : Ω → ℝ) := by
    filter_upwards with ω
    show -(a ω ^ 4 + b ω ^ 4 + d ω ^ 4 + e ω ^ 4) ≤ 4 * (a ω * b ω * (d ω * e ω))
    nlinarith [sq_nonneg (a ω * b ω + d ω * e ω), sq_nonneg (a ω ^ 2 - b ω ^ 2),
      sq_nonneg (d ω ^ 2 - e ω ^ 2)]
  have s1 := condExp_add (μ := μ) ha hb 𝒟
  have s2 := condExp_add (μ := μ) (ha.add hb) hd 𝒟
  have s3 := condExp_add (μ := μ) ((ha.add hb).add hd) he 𝒟
  have hmono1 := condExp_mono (μ := μ) (m := 𝒟) hf4 hg hup
  have hmono2 := condExp_mono (μ := μ) (m := 𝒟) hg.neg hf4 hlo
  have hneg := condExp_neg (μ := μ) ((fun ω => a ω ^ 4) + (fun ω => b ω ^ 4)
    + (fun ω => d ω ^ 4) + (fun ω => e ω ^ 4) : Ω → ℝ) 𝒟
  have hsmul := condExp_smul (μ := μ) (4 : ℝ) (fun ω => a ω * b ω * (d ω * e ω)) 𝒟
  filter_upwards [s1, s2, s3, hmono1, hmono2, hneg, hsmul, hma, hmb, hmd, hme]
    with ω e1 e2 e3 m1 m2 en es ea eb ed ee
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 m1 m2 en es
  rw [abs_le]
  constructor <;> linarith

/-- A conditional Markov inequality for the second moment:
`P(ε ≤ |X| ∣ 𝒟) ≤ ε^{-2} E[X² ∣ 𝒟]`, with the conditional probability written as the
conditional expectation of the indicator. -/
theorem condMarkov_sq {X : Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hX : Integrable (fun ω => X ω ^ 2) μ)
    (hind : Integrable (Set.indicator {ω | ε ≤ |X ω|} (fun _ => (1 : ℝ))) μ) :
    (μ[Set.indicator {ω | ε ≤ |X ω|} (fun _ => (1 : ℝ)) | 𝒟])
      ≤ᵐ[μ] fun ω => ε⁻¹ ^ 2 * (μ[fun ω => X ω ^ 2 | 𝒟]) ω := by
  have hle : Set.indicator {ω | ε ≤ |X ω|} (fun _ => (1 : ℝ))
      ≤ᵐ[μ] ((ε⁻¹ ^ 2 : ℝ) • fun ω => X ω ^ 2) := by
    filter_upwards with ω
    show Set.indicator {ω | ε ≤ |X ω|} (fun _ => (1 : ℝ)) ω ≤ ε⁻¹ ^ 2 * X ω ^ 2
    by_cases hω : ω ∈ {ω | ε ≤ |X ω|}
    · rw [Set.indicator_of_mem hω]
      have hx : ε ≤ |X ω| := hω
      have h1 : ε ^ 2 ≤ X ω ^ 2 := by
        have := mul_self_le_mul_self hε.le hx
        nlinarith [sq_abs (X ω)]
      rw [inv_pow]
      calc (1 : ℝ) = (ε ^ 2)⁻¹ * ε ^ 2 := (inv_mul_cancel₀ (by positivity)).symm
        _ ≤ (ε ^ 2)⁻¹ * X ω ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    · rw [Set.indicator_of_notMem hω]
      positivity
  have hmono := condExp_mono (μ := μ) (m := 𝒟) hind (hX.smul ((ε⁻¹ : ℝ) ^ 2)) hle
  have hsm := condExp_smul (μ := μ) ((ε⁻¹ : ℝ) ^ 2) (fun ω => X ω ^ 2) 𝒟
  filter_upwards [hmono, hsm] with ω e1 e2
  refine e1.trans (le_of_eq ?_)
  rw [e2]; rfl

end Conditional

/-! ### Counting the nonvanishing covariances

Deterministic bookkeeping that turns `Multiway.Sharing.card_linkedQuads_le` into a bound on a
double sum over pairs of linked pairs. -/

section Counting

open Sharing

variable {O D L : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)

/-- Pairs of linked pairs whose four observations form a quadruple of `𝓛_n`. -/
noncomputable def crossPairs : Finset ((O × O) × (O × O)) :=
  ((linkedPairs c dims) ×ˢ (linkedPairs c dims)).filter
    (fun pq => (pq.1.1, pq.1.2, pq.2.1, pq.2.2) ∈ linkedQuads c dims)

omit [DecidableEq D] in
/-- `#{(p,q) : p,q linked, the quadruple in 𝓛_n} ≤ |𝓛_n| ≤ 4n(D_n+1)³`, by injection into
`𝓛_n`. -/
theorem card_crossPairs_le :
    (crossPairs c dims).card ≤ 4 * (Fintype.card O * (maxDegree c dims + 1) ^ 3) := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn
    (fun pq : (O × O) × (O × O) => (pq.1.1, pq.1.2, pq.2.1, pq.2.2)) ?_ ?_)
    (card_linkedQuads_le c dims)
  · intro pq hpq
    exact (Finset.mem_filter.mp hpq).2
  · rintro ⟨⟨a, b⟩, ⟨u, v⟩⟩ - ⟨⟨a', b'⟩, ⟨u', v'⟩⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [h1, h2, h3, h4]

omit [DecidableEq D] in
/-- A kernel on pairs of linked pairs that vanishes off `𝓛_n` and is bounded by `κ` on it has
double sum at most `4κn(D_n+1)³`. -/
theorem abs_double_sum_le (F : (O × O) → (O × O) → ℝ) {kap : ℝ} (hkap : 0 ≤ kap)
    (hzero : ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims → F p q = 0)
    (hbd : ∀ p q, |F p q| ≤ kap) :
    |∑ p ∈ linkedPairs c dims, ∑ q ∈ linkedPairs c dims, F p q|
      ≤ kap * (4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3)) := by
  classical
  have hflat : ∑ p ∈ linkedPairs c dims, ∑ q ∈ linkedPairs c dims, F p q
      = ∑ pq ∈ (linkedPairs c dims) ×ˢ (linkedPairs c dims), F pq.1 pq.2 :=
    (Finset.sum_product' _ _ _).symm
  have hrestrict : ∑ pq ∈ (linkedPairs c dims) ×ˢ (linkedPairs c dims), F pq.1 pq.2
      = ∑ pq ∈ crossPairs c dims, F pq.1 pq.2 := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro pq hpq hnot
    have hmem := Finset.mem_product.mp hpq
    refine hzero pq.1 hmem.1 pq.2 hmem.2 fun hq => hnot ?_
    exact Finset.mem_filter.mpr ⟨hpq, hq⟩
  rw [hflat, hrestrict]
  have hcard : ((crossPairs c dims).card : ℝ)
      ≤ 4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3) := by
    have := card_crossPairs_le c dims
    have hc : ((crossPairs c dims).card : ℝ)
        ≤ ((4 * (Fintype.card O * (maxDegree c dims + 1) ^ 3) : ℕ) : ℝ) := by exact_mod_cast this
    refine hc.trans (le_of_eq ?_)
    push_cast
    ring
  calc |∑ pq ∈ crossPairs c dims, F pq.1 pq.2|
      ≤ ∑ pq ∈ crossPairs c dims, |F pq.1 pq.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _pq ∈ crossPairs c dims, kap := Finset.sum_le_sum fun pq _ => hbd _ _
    _ = ((crossPairs c dims).card : ℝ) * kap := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3)) * kap :=
        mul_le_mul_of_nonneg_right hcard hkap
    _ = kap * (4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3)) := mul_comm _ _

omit [DecidableEq D] in
/-- At `κ = 2B⁴C`, the bound `4κn(D_n+1)³` of `abs_double_sum_le` is at most
`64B⁴C·δ_n·λ_min(Ω_n)²`, using `(D_n+1)³ ≤ 8D_n³` and `nD_n³ = δ_nλ_min(Ω_n)²`. -/
theorem counting_bound_eq_delta {B Cm lmin : ℝ} (hC : 0 ≤ Cm) (hl : 0 < lmin) :
    (2 * B ^ 4 * Cm) * (4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3))
      ≤ 64 * B ^ 4 * Cm * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) lmin * lmin ^ 2 := by
  have hD : (1 : ℝ) ≤ (maxDegree c dims : ℝ) := by
    exact_mod_cast one_le_maxDegree c dims
  have hcube : ((maxDegree c dims : ℝ) + 1) ^ 3 ≤ 8 * (maxDegree c dims : ℝ) ^ 3 := by
    nlinarith [hD, sq_nonneg ((maxDegree c dims : ℝ) - 1)]
  have hn : (0 : ℝ) ≤ (Fintype.card O : ℝ) := Nat.cast_nonneg _
  have hrhs : 64 * B ^ 4 * Cm
      * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) lmin * lmin ^ 2
      = 64 * B ^ 4 * Cm * ((Fintype.card O : ℝ) * (maxDegree c dims : ℝ) ^ 3) := by
    rw [deltaSeq]
    field_simp
  rw [hrhs]
  have hBC : (0 : ℝ) ≤ B ^ 4 * Cm := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcube hn, hBC]

end Counting

/-! ### Quadratic-form bounds for kernels on the sharing graph

For a kernel supported on the sharing graph with bounded entries, `quadForm_le_of_graphSupported`
gives the Loewner bound `A ⪯ κ(D_n+1)I` directly from `|x_ox_{o'}| ≤ (x_o²+x_{o'}²)/2` and the
row count, without a spectral decomposition. -/

section GraphQuadForm

open Sharing

variable {O D L : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)

omit [DecidableEq O] [DecidableEq D] in
/-- Summing an indicator of the sharing graph over the second index counts the closed
neighbourhood of the first. The real-valued form of `Multiway.Sharing.sum_ite_closedNbhd`. -/
theorem sum_ite_linked_right (o : O) (t : ℝ) :
    (∑ o' : O, if Linked c dims o o' then t else 0)
      = ((closedNbhd c dims o).card : ℝ) * t := by
  rw [← Finset.sum_filter]
  simp [closedNbhd]

omit [DecidableEq O] [DecidableEq D] in
/-- Summing an indicator of the sharing graph over the first index counts the closed
neighbourhood of the second; this uses the symmetry of the sharing graph. -/
theorem sum_ite_linked_left (o' : O) (t : ℝ) :
    (∑ o : O, if Linked c dims o o' then t else 0)
      = ((closedNbhd c dims o').card : ℝ) * t := by
  rw [← sum_ite_linked_right c dims o' t]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases h : Linked c dims o o'
  · rw [ite_eq_left h, ite_eq_left (linked_symm h)]
  · rw [ite_eq_right h, ite_eq_right fun hc => h (linked_symm hc)]

omit [DecidableEq D] in
/-- For a kernel `A` supported on the sharing graph with entries bounded by `κ`,
`x'Ax ≤ κ(D_n+1)‖x‖²`. At `A = Ω` and `κ = C^{1/2}` this is `Ω ⪯ C^{1/2}(D_n+1)I`; at
`A = 𝒮h` and `κ = 1` it bounds the spectral norm of the sharing matrix by `D_n+1`. -/
theorem quadForm_le_of_graphSupported (A : Matrix O O ℝ) {kap : ℝ} (hkap : 0 ≤ kap)
    (hb : ∀ o o', |A o o'| ≤ kap)
    (hz : ∀ o o', ¬ Linked c dims o o' → A o o' = 0) (x : O → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ kap * ((maxDegree c dims : ℝ) + 1) * (x ⬝ᵥ x) := by
  classical
  have hdot : x ⬝ᵥ (A *ᵥ x) = ∑ o : O, ∑ o' : O, x o * (A o o' * x o') := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun o _ => by rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  -- the Young step, term by term
  have hterm : ∀ o o' : O, x o * (A o o' * x o')
      ≤ (if Linked c dims o o' then kap * (x o ^ 2) / 2 else 0)
        + (if Linked c dims o o' then kap * (x o' ^ 2) / 2 else 0) := by
    intro o o'
    by_cases h : Linked c dims o o'
    · rw [ite_eq_left h, ite_eq_left h]
      have h1 : |A o o'| ≤ kap := hb o o'
      have h2 : x o * (A o o' * x o') ≤ |A o o'| * (|x o| * |x o'|) := by
        calc x o * (A o o' * x o') ≤ |x o * (A o o' * x o')| := le_abs_self _
          _ = |A o o'| * (|x o| * |x o'|) := by
              rw [abs_mul, abs_mul]; ring
      have h3 : |x o| * |x o'| ≤ (x o ^ 2 + x o' ^ 2) / 2 := by
        nlinarith [sq_nonneg (|x o| - |x o'|), sq_abs (x o), sq_abs (x o')]
      nlinarith [abs_nonneg (A o o'), abs_nonneg (x o), abs_nonneg (x o'),
        mul_nonneg (abs_nonneg (x o)) (abs_nonneg (x o'))]
    · rw [ite_eq_right h, ite_eq_right h, hz o o' h]
      simp
  -- the two sums, one per index
  have hD : ∀ o : O, ((closedNbhd c dims o).card : ℝ) ≤ (maxDegree c dims : ℝ) + 1 := by
    intro o
    have := card_closedNbhd_le c dims o
    exact_mod_cast this
  have hS1 : ∑ o : O, ∑ o' : O, (if Linked c dims o o' then kap * (x o ^ 2) / 2 else 0)
      ≤ ((maxDegree c dims : ℝ) + 1) * (kap * (x ⬝ᵥ x) / 2) := by
    have hrow : ∀ o : O, (∑ o' : O, if Linked c dims o o' then kap * (x o ^ 2) / 2 else 0)
        ≤ ((maxDegree c dims : ℝ) + 1) * (kap * (x o ^ 2) / 2) := by
      intro o
      rw [sum_ite_linked_right c dims o]
      exact mul_le_mul_of_nonneg_right (hD o) (by positivity)
    calc ∑ o : O, ∑ o' : O, (if Linked c dims o o' then kap * (x o ^ 2) / 2 else 0)
        ≤ ∑ o : O, ((maxDegree c dims : ℝ) + 1) * (kap * (x o ^ 2) / 2) :=
          Finset.sum_le_sum fun o _ => hrow o
      _ = ((maxDegree c dims : ℝ) + 1) * (kap * (x ⬝ᵥ x) / 2) := by
          rw [← Finset.mul_sum, dotProduct]
          congr 1
          rw [← Finset.sum_div, ← Finset.mul_sum]
          congr 2
          exact Finset.sum_congr rfl fun o _ => by rw [sq]
  have hS2 : ∑ o : O, ∑ o' : O, (if Linked c dims o o' then kap * (x o' ^ 2) / 2 else 0)
      ≤ ((maxDegree c dims : ℝ) + 1) * (kap * (x ⬝ᵥ x) / 2) := by
    have hswap : ∑ o : O, ∑ o' : O, (if Linked c dims o o' then kap * (x o' ^ 2) / 2 else 0)
        = ∑ o' : O, ∑ o : O, (if Linked c dims o o' then kap * (x o' ^ 2) / 2 else 0) :=
      Finset.sum_comm
    rw [hswap]
    have hcol : ∀ o' : O, (∑ o : O, if Linked c dims o o' then kap * (x o' ^ 2) / 2 else 0)
        ≤ ((maxDegree c dims : ℝ) + 1) * (kap * (x o' ^ 2) / 2) := by
      intro o'
      rw [sum_ite_linked_left c dims o']
      exact mul_le_mul_of_nonneg_right (hD o') (by positivity)
    calc ∑ o' : O, ∑ o : O, (if Linked c dims o o' then kap * (x o' ^ 2) / 2 else 0)
        ≤ ∑ o' : O, ((maxDegree c dims : ℝ) + 1) * (kap * (x o' ^ 2) / 2) :=
          Finset.sum_le_sum fun o' _ => hcol o'
      _ = ((maxDegree c dims : ℝ) + 1) * (kap * (x ⬝ᵥ x) / 2) := by
          rw [← Finset.mul_sum, dotProduct]
          congr 1
          rw [← Finset.sum_div, ← Finset.mul_sum]
          congr 2
          exact Finset.sum_congr rfl fun o _ => by rw [sq]
  have hsplit : ∑ o : O, ∑ o' : O, x o * (A o o' * x o')
      ≤ (∑ o : O, ∑ o' : O, (if Linked c dims o o' then kap * (x o ^ 2) / 2 else 0))
        + ∑ o : O, ∑ o' : O, (if Linked c dims o o' then kap * (x o' ^ 2) / 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun o _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun o' _ => hterm o o'
  rw [hdot]
  linarith [hsplit, hS1, hS2]

omit [DecidableEq D] in
/-- `Ω ⪯ C^{1/2}(D_n+1)I`, the Loewner form of the first bound of Lemma SM.B.11(d), as
consumed by `trace_conj_proj_le`. -/
theorem le_smul_one_of_graphSupported {A : Matrix O O ℝ} (hA : A.IsHermitian) {kap : ℝ}
    (hkap : 0 ≤ kap) (hb : ∀ o o', |A o o'| ≤ kap)
    (hz : ∀ o o', ¬ Linked c dims o o' → A o o' = 0) :
    A ≤ (kap * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ) := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.sub (by simp [Matrix.IsHermitian]) hA
  · intro x
    have hmv : ((kap * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ)) *ᵥ x
        = (kap * ((maxDegree c dims : ℝ) + 1)) • x := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 : star x ⬝ᵥ (((kap * ((maxDegree c dims : ℝ) + 1)) • (1 : Matrix O O ℝ) - A) *ᵥ x)
        = kap * ((maxDegree c dims : ℝ) + 1) * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, hmv, dotProduct_smul, smul_eq_mul, star_trivial]
    rw [h1]
    linarith [quadForm_le_of_graphSupported c dims A hkap hb hz x]

end GraphQuadForm

/-! ### The trace bound `tr(ΠΩΠ) ≤ (d_{[Δ]}+K)λ_max(Ω)`

`Π` is an orthogonal projector of rank `d_{[Δ]}+K`, as in Lemma SM.B.6; only its symmetry,
idempotence and trace are used. `Multiway/ResidualBridge.lean` supplies these for
`hatMatrix S x`. -/

section TraceBound

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- For a symmetric idempotent `Π` of trace `ρ` and any `Ω ⪯ κI`, `tr(ΠΩΠ) ≤ κρ`, since
`ΠΩΠ ⪯ Π(κI)Π = κΠ`. This gives `E[‖ϖ‖² ∣ 𝒟] = tr(ΠΩΠ) ≤ (d_{[Δ]}+K)λ_max(Ω)`. -/
theorem trace_conj_proj_le {Pr : Matrix κ κ ℝ} (hPr : Pr.IsHermitian) (hPP : Pr * Pr = Pr)
    {Om : Matrix κ κ ℝ} {kap rho : ℝ} (hOm : Om ≤ kap • (1 : Matrix κ κ ℝ))
    (htr : Pr.trace = rho) : (Pr * Om * Pr).trace ≤ kap * rho := by
  have h0 : (kap • (1 : Matrix κ κ ℝ) - Om).PosSemidef := Matrix.le_iff.mp hOm
  have hc := h0.conjTranspose_mul_mul_same Pr
  have hPt : (Pr : Matrix κ κ ℝ)ᴴ = Pr := by
    rw [conjTranspose_eq_transpose]; exact transpose_eq_self hPr
  rw [hPt] at hc
  have hexp : Pr * (kap • (1 : Matrix κ κ ℝ) - Om) * Pr = kap • Pr - Pr * Om * Pr := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPP]
  rw [hexp] at hc
  have hle : Pr * Om * Pr ≤ kap • Pr := Matrix.le_iff.mpr hc
  have htrle := trace_le_of_le hle
  rwa [Matrix.trace_smul, htr, smul_eq_mul] at htrle

end TraceBound

/-! ### Lemma SM.B.13, first claim

`E[‖𝓜̃_n - Ω_n‖_F² ∣ 𝒟] ≤ 64K²B⁴C δ_n λ_min(Ω_n)²`. The theorems below take the vanishing
condition `hzero`, the covariance bound `hbd` and the centering as hypotheses;
`infeasibleMeat_condVar_le_of_regime3` is the form with all of them discharged. -/

section InfeasibleMeat

open Sharing

variable {O D L κ : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable [Fintype κ] [DecidableEq κ] {Ω : Type*}

/-- `𝓜̃_n := ∑_{o∼o'} x̃_ox̃_{o'}'ν_oν_{o'}`, the infeasible union meat. -/
def unionMeat (c : D → O → L) (dims : Finset D) (xt : O → κ → Ω → ℝ) (nu : O → Ω → ℝ)
    (ω : Ω) : Matrix κ κ ℝ :=
  Matrix.of fun k l => ∑ p ∈ linkedPairs c dims, xt p.1 k ω * xt p.2 l ω * (nu p.1 ω * nu p.2 ω)

/-- `Ω_n = X̃'ΩX̃`, written as a sum over linked pairs. At the kernel `condOmegaKernel 𝒟 P nu`
this is `E[𝓜̃_n ∣ 𝒟]`, by `condExp_unionMeat_eq_scoreVar`. -/
def scoreVar (c : D → O → L) (dims : Finset D) (xt : O → κ → Ω → ℝ) (Om : O → O → Ω → ℝ)
    (ω : Ω) : Matrix κ κ ℝ :=
  Matrix.of fun k l => ∑ p ∈ linkedPairs c dims, xt p.1 k ω * xt p.2 l ω * Om p.1 p.2 ω

/-- `ξ_{oo'} - E[ξ_{oo'} ∣ 𝒟] = x̃_{ok}x̃_{o'l}(ν_oν_{o'} - Ω_{oo'})`, the centered summand. -/
def centeredSummand (xt : O → κ → Ω → ℝ) (nu : O → Ω → ℝ) (Om : O → O → Ω → ℝ)
    (k l : κ) (p : O × O) (ω : Ω) : ℝ :=
  xt p.1 k ω * xt p.2 l ω * (nu p.1 ω * nu p.2 ω - Om p.1 p.2 ω)

omit [DecidableEq O] [DecidableEq D] [Fintype κ] [DecidableEq κ] in
/-- The `(k,l)` entry of `𝓜̃_n - Ω_n` is the sum of the centered summands. -/
theorem unionMeat_sub_apply (c : D → O → L) (dims : Finset D) (xt : O → κ → Ω → ℝ)
    (nu : O → Ω → ℝ) (Om : O → O → Ω → ℝ) (k l : κ) (ω : Ω) :
    (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l
      = ∑ p ∈ linkedPairs c dims, centeredSummand xt nu Om k l p ω := by
  rw [Matrix.sub_apply, unionMeat, scoreVar]
  show (∑ p ∈ linkedPairs c dims, xt p.1 k ω * xt p.2 l ω * (nu p.1 ω * nu p.2 ω))
      - (∑ p ∈ linkedPairs c dims, xt p.1 k ω * xt p.2 l ω * Om p.1 p.2 ω) = _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [centeredSummand]; ring

-- `𝒟` precedes the ambient `mΩ`, as elsewhere in this package.
variable (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [DecidableEq D] [Fintype κ] [DecidableEq κ] in
/-- `Var[(𝓜̃_n)_{kl} ∣ 𝒟] ≤ 4κn(D_n+1)³` under a per-quadruple covariance bound `κ`, from the
double-sum expansion, the vanishing off `𝓛_n`, the bound on `𝓛_n` and Lemma SM.B.11(c). -/
theorem condExp_sq_entry_le (c : D → O → L) (dims : Finset D) {xt : O → κ → Ω → ℝ}
    {nu : O → Ω → ℝ} {Om : O → O → Ω → ℝ} (k l : κ) {kap : ℝ} (hkap : 0 ≤ kap)
    (hint : ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      Integrable (fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω) μ)
    (hzero : ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims →
      (μ[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) =ᵐ[μ] 0)
    (hbd : ∀ p q : O × O, ∀ᵐ ω ∂μ,
      |(μ[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) ω| ≤ kap) :
    ∀ᵐ ω ∂μ, (μ[fun ω =>
        ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2 | 𝒟]) ω
      ≤ kap * (4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3)) := by
  classical
  have hfun : (fun ω => ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2)
      = fun ω => (∑ p ∈ linkedPairs c dims, centeredSummand xt nu Om k l p ω) ^ 2 := by
    funext ω; rw [unionMeat_sub_apply]
  rw [hfun]
  have hall : ∀ᵐ ω ∂μ, ∀ p q : O × O,
      |(μ[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) ω| ≤ kap :=
    ae_all_iff.2 fun p => ae_all_iff.2 fun q => hbd p q
  have hzall : ∀ᵐ ω ∂μ, ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims →
      (μ[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) ω = 0 := by
    rw [Filter.eventually_all_finset]
    intro p hp
    rw [Filter.eventually_all_finset]
    intro q hq
    by_cases hmem : (p.1, p.2, q.1, q.2) ∈ linkedQuads c dims
    · filter_upwards with ω hcon; exact absurd hmem hcon
    · filter_upwards [hzero p hp q hq hmem] with ω hω _
      simpa using hω
  filter_upwards [condExp_sq_sum_eq 𝒟 (linkedPairs c dims)
    (fun p ω => centeredSummand xt nu Om k l p ω) hint, hall, hzall] with ω e1 e2 e3
  rw [e1]
  refine le_trans (le_abs_self _) ?_
  exact abs_double_sum_le c dims
    (fun p q => (μ[fun ω => centeredSummand xt nu Om k l p ω
      * centeredSummand xt nu Om k l q ω | 𝒟]) ω) hkap
    (fun p hp q hq hnm => e3 p hp q hq hnm) (fun p q => e2 p q)

omit [DecidableEq D] [DecidableEq κ] in
/-- `E[‖𝓜̃_n - Ω_n‖_F² ∣ 𝒟] ≤ 4K²κn(D_n+1)³` under a per-quadruple covariance bound `κ`,
by summing the entrywise bound over the `K²` entries. -/
theorem condExp_frobSq_unionMeat_sub_le (c : D → O → L) (dims : Finset D)
    {xt : O → κ → Ω → ℝ} {nu : O → Ω → ℝ} {Om : O → O → Ω → ℝ} {kap : ℝ} (hkap : 0 ≤ kap)
    (hint : ∀ k l : κ, ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      Integrable (fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω) μ)
    (hzero : ∀ k l : κ, ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims →
      (μ[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) =ᵐ[μ] 0)
    (hbd : ∀ k l : κ, ∀ p q : O × O, ∀ᵐ ω ∂μ,
      |(μ[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) ω| ≤ kap) :
    ∀ᵐ ω ∂μ, (μ[fun ω => frobSq (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) | 𝒟]) ω
      ≤ (Fintype.card κ : ℝ) ^ 2
        * (kap * (4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3))) := by
  classical
  set Vb : ℝ := kap * (4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3)) with hVb
  -- each squared entry is integrable, as a finite sum of the products in `hint`
  have hentry : ∀ k l : κ, Integrable (fun ω =>
      ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2) μ := by
    intro k l
    have hfun : (fun ω => ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2)
        = ∑ p ∈ linkedPairs c dims, ∑ q ∈ linkedPairs c dims,
            (fun ω => centeredSummand xt nu Om k l p ω * centeredSummand xt nu Om k l q ω) := by
      rw [← sq_finsetSum_eq_double_sum (linkedPairs c dims)
        (fun p ω => centeredSummand xt nu Om k l p ω)]
      funext ω; rw [unionMeat_sub_apply]
    rw [hfun]
    exact integrable_finsetSum' _ fun p hp =>
      integrable_finsetSum' _ fun q hq => hint k l p hp q hq
  have hfrob : (fun ω => frobSq (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω))
      = ∑ k : κ, ∑ l : κ,
        (fun ω => ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2) := by
    funext ω
    simp only [Finset.sum_apply]
    rfl
  rw [hfrob]
  have h1 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset κ))
    (f := fun k : κ => ∑ l : κ, (fun ω =>
      ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2))
    (fun k _ => integrable_finsetSum' _ fun l _ => hentry k l) 𝒟
  have h2 : ∀ᵐ ω ∂μ, ∀ k : κ,
      (μ[∑ l : κ, (fun ω =>
        ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2) | 𝒟]) ω
        = ∑ l : κ, (μ[fun ω =>
            ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2 | 𝒟]) ω := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset κ))
      (fun l _ => hentry k l) 𝒟] with ω hω
    rw [hω, Finset.sum_apply]
  have h3 : ∀ᵐ ω ∂μ, ∀ k l : κ,
      (μ[fun ω => ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2 | 𝒟]) ω
        ≤ Vb :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun l =>
      condExp_sq_entry_le 𝒟 c dims k l hkap (hint k l) (hzero k l) (hbd k l)
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, Finset.sum_apply]
  calc ∑ k : κ, (μ[∑ l : κ, (fun ω =>
        ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2) | 𝒟]) ω
      = ∑ k : κ, ∑ l : κ, (μ[fun ω =>
          ((unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) k l) ^ 2 | 𝒟]) ω :=
        Finset.sum_congr rfl fun k _ => e2 k
    _ ≤ ∑ _k : κ, ∑ _l : κ, Vb :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => e3 k l
    _ = (Fintype.card κ : ℝ) ^ 2 * Vb := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

omit [DecidableEq D] [DecidableEq κ] in
/-- **Lemma SM.B.13, first claim.** `E[‖𝓜̃_n - Ω_n‖_F² ∣ 𝒟] ≤ 64K²B⁴C δ_n λ_min(Ω_n)²`,
given the per-quadruple bound `hbd : |Cov(ξ_{o₁o₂},ξ_{o₃o₄} ∣ 𝒟)| ≤ 2B⁴C`. See
`abs_condExp_centeredSummand_mul_le` and `infeasibleMeat_condVar_le_of_regime3` for the
discharge of `hbd`, `hzero` and `hint`. -/
theorem infeasibleMeat_condVar_le (c : D → O → L) (dims : Finset D)
    {xt : O → κ → Ω → ℝ} {nu : O → Ω → ℝ} {Om : O → O → Ω → ℝ} {B Cm lmin : ℝ}
    (hC : 0 ≤ Cm) (hl : 0 < lmin)
    (hint : ∀ k l : κ, ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      Integrable (fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω) μ)
    (hzero : ∀ k l : κ, ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims →
      (μ[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) =ᵐ[μ] 0)
    (hbd : ∀ k l : κ, ∀ p q : O × O, ∀ᵐ ω ∂μ,
      |(μ[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) ω| ≤ 2 * B ^ 4 * Cm) :
    ∀ᵐ ω ∂μ, (μ[fun ω => frobSq (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) | 𝒟]) ω
      ≤ 64 * (Fintype.card κ : ℝ) ^ 2 * B ^ 4 * Cm
        * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) lmin * lmin ^ 2 := by
  have hkap : (0 : ℝ) ≤ 2 * B ^ 4 * Cm := by positivity
  filter_upwards [condExp_frobSq_unionMeat_sub_le 𝒟 c dims hkap hint hzero hbd] with ω hω
  refine hω.trans ?_
  have hstep := counting_bound_eq_delta c dims (B := B) hC hl
  have hK : (0 : ℝ) ≤ (Fintype.card κ : ℝ) ^ 2 := by positivity
  calc (Fintype.card κ : ℝ) ^ 2
        * ((2 * B ^ 4 * Cm) * (4 * ((Fintype.card O : ℝ) * ((maxDegree c dims : ℝ) + 1) ^ 3)))
      ≤ (Fintype.card κ : ℝ) ^ 2
        * (64 * B ^ 4 * Cm * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) lmin
          * lmin ^ 2) := mul_le_mul_of_nonneg_left hstep hK
    _ = 64 * (Fintype.card κ : ℝ) ^ 2 * B ^ 4 * Cm
        * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) lmin * lmin ^ 2 := by ring

end InfeasibleMeat

/-! ### Satisfiability of the hypotheses

Each theorem below applies a main result of this file with every hypothesis discharged in a
concrete model, showing that the hypotheses are jointly satisfiable. The model for
`infeasibleMeat_condVar_le` has every centered summand identically zero. -/

section Witness

open Sharing

/-- The identically-zero sequence converges to zero in probability. -/
theorem tendstoInMeasure_const_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) :
    TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hz : ∀ n : ℕ, P {ω : Ω | ε ≤ dist ((fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) n ω)
      ((fun _ => (0 : ℝ)) ω)} = 0 := by
    intro n
    convert measure_empty (μ := P)
    ext ω
    simp [not_le.mpr hε]
  have heq : (fun n : ℕ => P {ω : Ω | ε ≤ dist ((fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) n ω)
      ((fun _ => (0 : ℝ)) ω)}) = fun _ => 0 := funext hz
  rw [heq]
  exact tendsto_const_nhds

/-- The one-dimensional identity design is positive definite and its own lower Loewner bound. -/
theorem witness_one_posDef : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := Matrix.PosDef.one

theorem witness_one_le : (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) ≤ 1 := by
  rw [one_smul]

theorem witness_one_injective : Function.Injective (1 : Matrix (Fin 1) (Fin 1) ℝ).mulVec := by
  intro a b hab
  simpa [Matrix.one_mulVec] using hab

/-- The hypotheses of `rateAgnostic_a` hold on the model `Ω_n = 𝓜̃_n = 𝓡_n = I_1`,
`λ_min = 1`, over the one-point probability space. -/
theorem rateAgnostic_a_witness :
    TendstoInMeasure (Measure.dirac ())
        (fun (_ : ℕ) (_ : Unit) => rectFrobNorm
          ((sqrtPD (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ * ((1 : Matrix (Fin 1) (Fin 1) ℝ) - 1)
            * (sqrtPD (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹)) atTop (fun _ => 0)
      ∧ TendstoInMeasure (Measure.dirac ())
        (fun (_ : ℕ) (_ : Unit) => rectFrobNorm
          ((sqrtPD ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 * 1))⁻¹
            * ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 * 1)
            * (sqrtPD ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 * 1))⁻¹ - 1)) atTop (fun _ => 0) := by
  refine rateAgnostic_a (P := Measure.dirac ()) (Om := fun _ _ => 1) (c := fun _ _ => 1)
    (Mt := fun _ _ => 1) (A := fun _ _ => 1) (fun _ _ => witness_one_posDef)
    (fun _ _ => one_pos) (fun _ _ => witness_one_le) ?_ (fun _ _ => witness_one_injective)
  have hfun : (fun (_ : ℕ) (_ : Unit) =>
      rectFrobNorm ((1 : Matrix (Fin 1) (Fin 1) ℝ) - 1) / 1) = fun _ _ => (0 : ℝ) := by
    funext n ω
    simp [rectFrobNorm, rectFrobSq]
  rw [hfun]
  exact tendstoInMeasure_const_zero _

/-- The hypotheses of `rateAgnostic_b` hold on the same model with `𝓜̂_CGM = 𝓜̃_n = Ω_n`. -/
theorem rateAgnostic_b_witness :
    TendstoInMeasure (Measure.dirac ())
        (fun (_ : ℕ) (_ : Unit) => rectFrobNorm
          ((sqrtPD (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ * ((1 : Matrix (Fin 1) (Fin 1) ℝ) - 1)
            * (sqrtPD (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹)) atTop (fun _ => 0)
      ∧ TendstoInMeasure (Measure.dirac ())
        (fun (_ : ℕ) (_ : Unit) => rectFrobNorm
          ((sqrtPD ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 * 1))⁻¹
            * ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 * 1)
            * (sqrtPD ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 * 1))⁻¹ - 1)) atTop (fun _ => 0)
      ∧ Tendsto (fun _ : ℕ => (Measure.dirac ())
          {_ω : Unit | ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 * 1).PosDef}) atTop (𝓝 1) := by
  have hfun : (fun (_ : ℕ) (_ : Unit) =>
      rectFrobNorm ((1 : Matrix (Fin 1) (Fin 1) ℝ) - 1) / 1) = fun _ _ => (0 : ℝ) := by
    funext n ω
    simp [rectFrobNorm, rectFrobSq]
  refine rateAgnostic_b (P := Measure.dirac ()) (Om := fun _ _ => 1) (cn := fun _ _ => 1)
    (Mt := fun _ _ => 1) (Mh := fun _ _ => 1) (A := fun _ _ => 1)
    (fun _ _ => witness_one_posDef) (fun _ _ => one_pos) (fun _ _ => witness_one_le)
    ?_ ?_ (fun _ _ => witness_one_injective) (fun _ _ => ?_)
  · rw [hfun]; exact tendstoInMeasure_const_zero _
  · rw [hfun]; exact tendstoInMeasure_const_zero _
  · simp

/-- The hypotheses of `infeasibleMeat_condVar_le` hold on the two-observation sharing graph of
`Multiway/Sharing.lean`, with `x̃ ≡ 1`, `ν ≡ 0`, `Ω ≡ 0`, `B = C = λ = 1`, `𝒟 = ⊥` and the
one-point probability space. -/
theorem infeasibleMeat_condVar_le_witness :
    ∀ᵐ ω ∂(Measure.dirac ()),
      ((Measure.dirac ())[fun ω : Unit => frobSq
        (unionMeat witC witDims (fun (_ : WitO) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
            (fun _ _ => (0 : ℝ)) ω
          - scoreVar witC witDims (fun (_ : WitO) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
            (fun _ _ _ => (0 : ℝ)) ω) | ⊥]) ω
        ≤ 64 * (Fintype.card (Fin 1) : ℝ) ^ 2 * (1 : ℝ) ^ 4 * 1
          * deltaSeq (Fintype.card WitO : ℝ) (maxDegree witC witDims : ℝ) 1 * (1 : ℝ) ^ 2 := by
  have hz : ∀ (k l : Fin 1) (p q : WitO × WitO),
      (fun ω : Unit => centeredSummand (fun (_ : WitO) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
          (fun _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) k l p ω
        * centeredSummand (fun (_ : WitO) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
          (fun _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) k l q ω) = (0 : Unit → ℝ) := by
    intro k l p q
    funext ω
    simp [centeredSummand]
  refine infeasibleMeat_condVar_le (⊥ : MeasurableSpace Unit) (μ := Measure.dirac ())
    witC witDims (B := 1) (Cm := 1) (lmin := 1) zero_le_one one_pos ?_ ?_ ?_
  · intro k l p _ q _
    rw [hz k l p q]
    exact integrable_zero _ _ _
  · intro k l p _ q _ _
    rw [hz k l p q, condExp_zero]
  · intro k l p q
    rw [hz k l p q, condExp_zero]
    filter_upwards with ω
    norm_num

end Witness

/-! ### Vector and Frobenius norms

`l2Norm` is the Euclidean norm of an observation-indexed vector, written as the square root of a
sum of squares. The Frobenius facts are the triangle inequality over a `Finset` sum and the norm
of a scaled outer product. -/

/-- `‖u‖`, the Euclidean norm of an observation-indexed vector. -/
noncomputable def l2Norm {O : Type*} [Fintype O] (u : O → ℝ) : ℝ :=
  Real.sqrt (∑ o : O, u o ^ 2)

theorem l2Norm_nonneg {O : Type*} [Fintype O] (u : O → ℝ) : 0 ≤ l2Norm u := Real.sqrt_nonneg _

theorem sq_l2Norm {O : Type*} [Fintype O] (u : O → ℝ) : l2Norm u ^ 2 = ∑ o : O, u o ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

section FrobSum

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem rectVec_add (X Y : Matrix α β ℝ) : rectVec (X + Y) = rectVec X + rectVec Y := by
  ext p; simp

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem rectVec_sum {ι : Type*} (S : Finset ι) (F : ι → Matrix α β ℝ) :
    rectVec (∑ p ∈ S, F p) = ∑ p ∈ S, rectVec (F p) := by
  classical
  induction S using Finset.induction with
  | empty => ext p; simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, rectVec_add, ih]

omit [DecidableEq α] [DecidableEq β] in
/-- The triangle inequality for `‖·‖_F` over a `Finset` sum. -/
theorem rectFrobNorm_sum_le {ι : Type*} (S : Finset ι) (F : ι → Matrix α β ℝ) :
    rectFrobNorm (∑ p ∈ S, F p) ≤ ∑ p ∈ S, rectFrobNorm (F p) := by
  rw [← norm_rectVec, rectVec_sum]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => norm_rectVec _))

end FrobSum

section Outer

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- `‖ab't‖_F² = ‖a‖²‖b‖²t²`. -/
theorem rectFrobSq_outer (a b : κ → ℝ) (t : ℝ) :
    rectFrobSq (Matrix.of fun k l : κ => a k * b l * t)
      = (∑ k : κ, a k ^ 2) * ((∑ l : κ, b l ^ 2) * t ^ 2) := by
  have h1 : ∀ k : κ, (∑ l : κ, (a k * b l * t) ^ 2)
      = a k ^ 2 * ((∑ l : κ, b l ^ 2) * t ^ 2) := by
    intro k
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  calc rectFrobSq (Matrix.of fun k l : κ => a k * b l * t)
      = ∑ k : κ, ∑ l : κ, (a k * b l * t) ^ 2 := rfl
    _ = ∑ k : κ, a k ^ 2 * ((∑ l : κ, b l ^ 2) * t ^ 2) := Finset.sum_congr rfl fun k _ => h1 k
    _ = (∑ k : κ, a k ^ 2) * ((∑ l : κ, b l ^ 2) * t ^ 2) :=
        (Finset.sum_mul Finset.univ (fun k : κ => a k ^ 2) ((∑ l : κ, b l ^ 2) * t ^ 2)).symm

omit [DecidableEq κ] in
/-- For rows with `∑_k x̃_{ok}² ≤ B²`, `‖x̃_ox̃_{o'}'t‖_F ≤ B²|t|`. The hypothesis `_hB` is
not used in the proof. -/
theorem rectFrobNorm_outer_le {a b : κ → ℝ} {B : ℝ} (_hB : 0 ≤ B)
    (ha : ∑ k : κ, a k ^ 2 ≤ B ^ 2) (hb : ∑ k : κ, b k ^ 2 ≤ B ^ 2) (t : ℝ) :
    rectFrobNorm (Matrix.of fun k l : κ => a k * b l * t) ≤ B ^ 2 * |t| := by
  have hle : (∑ k : κ, a k ^ 2) * ((∑ l : κ, b l ^ 2) * t ^ 2) ≤ (B ^ 2 * |t|) ^ 2 := by
    have h1 : (∑ k : κ, a k ^ 2) * ((∑ l : κ, b l ^ 2) * t ^ 2)
        ≤ B ^ 2 * ((∑ l : κ, b l ^ 2) * t ^ 2) :=
      mul_le_mul_of_nonneg_right ha
        (by positivity)
    have h2 : B ^ 2 * ((∑ l : κ, b l ^ 2) * t ^ 2) ≤ B ^ 2 * (B ^ 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (sq_nonneg _)) (sq_nonneg _)
    have h3 : B ^ 2 * (B ^ 2 * t ^ 2) = (B ^ 2 * |t|) ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    linarith
  rw [rectFrobNorm, rectFrobSq_outer]
  exact (Real.sqrt_le_sqrt hle).trans (le_of_eq (Real.sqrt_sq (by positivity)))

end Outer

/-! ### The bilinear graph bound `∑_{o∼o'}|u_o||v_{o'}| ≤ (D_n+1)‖u‖‖v‖`

Proved by Cauchy–Schwarz over `linkedPairs`, using the row count `#N(o) ≤ D_n+1` on the first
index and the column count on the second, without forming the sharing matrix or its
eigenvalues. -/

section GraphBilinear

open Sharing

variable {O D L : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable (c : D → O → L) (dims : Finset D)

omit [DecidableEq O] [DecidableEq D] in
/-- A sum over the linked pairs, written as an indicator double sum. -/
theorem sum_linkedPairs_eq (F : O × O → ℝ) :
    ∑ p ∈ linkedPairs c dims, F p
      = ∑ o : O, ∑ o' : O, (if Linked c dims o o' then F (o, o') else 0) := by
  rw [linkedPairs, Finset.sum_filter, Fintype.sum_prod_type]

omit [DecidableEq D] in
/-- `∑_{o∼o'} u_o² ≤ (D_n+1)‖u‖²`, by the row count. -/
theorem sum_linkedPairs_fst_sq_le (u : O → ℝ) :
    ∑ p ∈ linkedPairs c dims, u p.1 ^ 2
      ≤ ((maxDegree c dims : ℝ) + 1) * ∑ o : O, u o ^ 2 := by
  rw [sum_linkedPairs_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun o _ => ?_
  rw [sum_ite_linked_right c dims o (u o ^ 2)]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact_mod_cast card_closedNbhd_le c dims o

omit [DecidableEq D] in
/-- `∑_{o∼o'} v_{o'}² ≤ (D_n+1)‖v‖²`, by the column count, using the symmetry of the sharing
graph. -/
theorem sum_linkedPairs_snd_sq_le (v : O → ℝ) :
    ∑ p ∈ linkedPairs c dims, v p.2 ^ 2
      ≤ ((maxDegree c dims : ℝ) + 1) * ∑ o : O, v o ^ 2 := by
  rw [sum_linkedPairs_eq, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun o' _ => ?_
  rw [sum_ite_linked_left c dims o' (v o' ^ 2)]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact_mod_cast card_closedNbhd_le c dims o'

omit [DecidableEq D] in
/-- `∑_{o∼o'}|u_o||v_{o'}| ≤ (D_n+1)‖u‖‖v‖`. -/
theorem sum_linked_abs_mul_le (u v : O → ℝ) :
    ∑ p ∈ linkedPairs c dims, |u p.1| * |v p.2|
      ≤ ((maxDegree c dims : ℝ) + 1) * (l2Norm u * l2Norm v) := by
  have hD : (0 : ℝ) ≤ (maxDegree c dims : ℝ) + 1 := by positivity
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (linkedPairs c dims)
    (fun p : O × O => |u p.1|) (fun p : O × O => |v p.2|)
  have h1 : ∑ p ∈ linkedPairs c dims, |u p.1| ^ 2 = ∑ p ∈ linkedPairs c dims, u p.1 ^ 2 :=
    Finset.sum_congr rfl fun p _ => sq_abs _
  have h2 : ∑ p ∈ linkedPairs c dims, |v p.2| ^ 2 = ∑ p ∈ linkedPairs c dims, v p.2 ^ 2 :=
    Finset.sum_congr rfl fun p _ => sq_abs _
  rw [h1, h2] at hcs
  refine hcs.trans ?_
  have hu : Real.sqrt (∑ p ∈ linkedPairs c dims, u p.1 ^ 2)
      ≤ Real.sqrt ((maxDegree c dims : ℝ) + 1) * l2Norm u := by
    rw [l2Norm, ← Real.sqrt_mul hD]
    exact Real.sqrt_le_sqrt (sum_linkedPairs_fst_sq_le c dims u)
  have hv : Real.sqrt (∑ p ∈ linkedPairs c dims, v p.2 ^ 2)
      ≤ Real.sqrt ((maxDegree c dims : ℝ) + 1) * l2Norm v := by
    rw [l2Norm, ← Real.sqrt_mul hD]
    exact Real.sqrt_le_sqrt (sum_linkedPairs_snd_sq_le c dims v)
  have hmul := mul_le_mul hu hv (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (l2Norm_nonneg u))
  refine hmul.trans (le_of_eq ?_)
  have hsq : Real.sqrt ((maxDegree c dims : ℝ) + 1) * Real.sqrt ((maxDegree c dims : ℝ) + 1)
      = (maxDegree c dims : ℝ) + 1 := Real.mul_self_sqrt hD
  calc Real.sqrt ((maxDegree c dims : ℝ) + 1) * l2Norm u
        * (Real.sqrt ((maxDegree c dims : ℝ) + 1) * l2Norm v)
      = (Real.sqrt ((maxDegree c dims : ℝ) + 1) * Real.sqrt ((maxDegree c dims : ℝ) + 1))
          * (l2Norm u * l2Norm v) := by ring
    _ = ((maxDegree c dims : ℝ) + 1) * (l2Norm u * l2Norm v) := by rw [hsq]

omit [DecidableEq D] in
/-- The three-term bound
`∑_{o∼o'}(|u_o||w_{o'}| + |w_o||u_{o'}| + |w_o||w_{o'}|) ≤ (D_n+1)(2‖u‖‖w‖ + ‖w‖²)`. -/
theorem sum_linked_perturb_le (u w : O → ℝ) :
    ∑ p ∈ linkedPairs c dims,
        (|u p.1| * |w p.2| + |w p.1| * |u p.2| + |w p.1| * |w p.2|)
      ≤ ((maxDegree c dims : ℝ) + 1) * (2 * l2Norm u * l2Norm w + l2Norm w ^ 2) := by
  have h1 := sum_linked_abs_mul_le c dims u w
  have h2 := sum_linked_abs_mul_le c dims w u
  have h3 := sum_linked_abs_mul_le c dims w w
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  nlinarith [h1, h2, h3, sq_l2Norm w]

end GraphBilinear

/-! ### The deterministic perturbation bound of Theorem 11(b)

With `ν̂ = ν - ϖ`, `‖𝓜̂_CGM - 𝓜̃_n‖_F ≤ B²(D_n+1)(2‖ν‖‖ϖ‖ + ‖ϖ‖²)` holds in every sample when
`sup_o‖x̃_o‖ ≤ B`; this is `rectFrobNorm_unionMeat_perturb_le`. -/

section Perturb

open Sharing

variable {O D L κ : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable [Fintype κ] [DecidableEq κ] {Ω : Type*}

omit [DecidableEq O] [DecidableEq D] [Fintype κ] [DecidableEq κ] in
/-- `𝓜̂_CGM - 𝓜̃_n = ∑_{o∼o'} x̃_ox̃_{o'}'(ν̂_oν̂_{o'} - ν_oν_{o'})`. -/
theorem unionMeat_sub_unionMeat_eq_sum (c : D → O → L) (dims : Finset D)
    (xt : O → κ → Ω → ℝ) (nuh nu : O → Ω → ℝ) (ω : Ω) :
    unionMeat c dims xt nuh ω - unionMeat c dims xt nu ω
      = ∑ p ∈ linkedPairs c dims, Matrix.of (fun k l : κ =>
          xt p.1 k ω * xt p.2 l ω * (nuh p.1 ω * nuh p.2 ω - nu p.1 ω * nu p.2 ω)) := by
  ext k l
  simp only [Matrix.sub_apply, Matrix.sum_apply, unionMeat, Matrix.of_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

private theorem abs_add_three (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| := by
  have h1 := abs_add_le (x + y) z
  have h2 := abs_add_le x y
  linarith

omit [DecidableEq D] [DecidableEq κ] in
/-- `‖𝓜̂_CGM - 𝓜̃_n‖_F ≤ B²(D_n+1)(2‖ν‖‖ϖ‖ + ‖ϖ‖²)`, from the entrywise expansion
`ν̂_oν̂_{o'} - ν_oν_{o'} = -ν_oϖ_{o'} - ϖ_oν_{o'} + ϖ_oϖ_{o'}`, the outer-product bound
`‖x̃_ox̃_{o'}'‖_F ≤ B²`, and the bilinear graph bound. -/
theorem rectFrobNorm_unionMeat_perturb_le (c : D → O → L) (dims : Finset D)
    (xt : O → κ → Ω → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hxt : ∀ (o : O) (ω' : Ω), ∑ k : κ, xt o k ω' ^ 2 ≤ B ^ 2)
    (nu vp : O → Ω → ℝ) (ω : Ω) :
    rectFrobNorm (unionMeat c dims xt (fun o ω' => nu o ω' - vp o ω') ω
        - unionMeat c dims xt nu ω)
      ≤ B ^ 2 * ((maxDegree c dims : ℝ) + 1)
          * (2 * l2Norm (fun o => nu o ω) * l2Norm (fun o => vp o ω)
            + l2Norm (fun o => vp o ω) ^ 2) := by
  rw [unionMeat_sub_unionMeat_eq_sum]
  refine (rectFrobNorm_sum_le _ _).trans ?_
  have hterm : ∀ p ∈ linkedPairs c dims,
      rectFrobNorm (Matrix.of (fun k l : κ => xt p.1 k ω * xt p.2 l ω *
          ((nu p.1 ω - vp p.1 ω) * (nu p.2 ω - vp p.2 ω) - nu p.1 ω * nu p.2 ω)))
        ≤ B ^ 2 * (|nu p.1 ω| * |vp p.2 ω| + |vp p.1 ω| * |nu p.2 ω|
            + |vp p.1 ω| * |vp p.2 ω|) := by
    intro p _
    refine (rectFrobNorm_outer_le hB (hxt p.1 ω) (hxt p.2 ω) _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg B)
    have he : (nu p.1 ω - vp p.1 ω) * (nu p.2 ω - vp p.2 ω) - nu p.1 ω * nu p.2 ω
        = -(nu p.1 ω * vp p.2 ω) + -(vp p.1 ω * nu p.2 ω) + vp p.1 ω * vp p.2 ω := by ring
    rw [he]
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_neg, abs_neg, abs_mul, abs_mul, abs_mul]
  calc ∑ p ∈ linkedPairs c dims, rectFrobNorm (Matrix.of (fun k l : κ =>
          xt p.1 k ω * xt p.2 l ω *
            ((nu p.1 ω - vp p.1 ω) * (nu p.2 ω - vp p.2 ω) - nu p.1 ω * nu p.2 ω)))
      ≤ ∑ p ∈ linkedPairs c dims, B ^ 2 * (|nu p.1 ω| * |vp p.2 ω|
          + |vp p.1 ω| * |nu p.2 ω| + |vp p.1 ω| * |vp p.2 ω|) := Finset.sum_le_sum hterm
    _ = B ^ 2 * ∑ p ∈ linkedPairs c dims, (|nu p.1 ω| * |vp p.2 ω|
          + |vp p.1 ω| * |nu p.2 ω| + |vp p.1 ω| * |vp p.2 ω|) := by rw [Finset.mul_sum]
    _ ≤ B ^ 2 * (((maxDegree c dims : ℝ) + 1)
          * (2 * l2Norm (fun o => nu o ω) * l2Norm (fun o => vp o ω)
            + l2Norm (fun o => vp o ω) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (sum_linked_perturb_le c dims (fun o => nu o ω) (fun o => vp o ω)) (sq_nonneg B)
    _ = B ^ 2 * ((maxDegree c dims : ℝ) + 1)
          * (2 * l2Norm (fun o => nu o ω) * l2Norm (fun o => vp o ω)
            + l2Norm (fun o => vp o ω) ^ 2) := by ring

end Perturb

/-! ## From conditional to unconditional convergence

`tendstoInMeasure_zero_of_condExp_le` turns a conditional first-moment bound by a random
majorant `ρ_n` that converges in probability to zero into convergence in probability. The
bounded-convergence step it uses, `tendsto_integral_of_tendstoInMeasure_le_one`, rests on the
elementary bound `∫Y_n ≤ η + P(Y_n ≥ η)` for `0 ≤ Y_n ≤ 1`. -/

section Bridge

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A conditional Markov inequality for the first moment: for `X ≥ 0`, the pointwise bound
`𝟙{ε ≤ X} ≤ ε⁻¹X` passed through the conditional expectation. -/
theorem condMarkov_abs {X : Ω → ℝ} {ε : ℝ} (hε : 0 < ε) (hX0 : ∀ ω, 0 ≤ X ω)
    (hX : Integrable X P)
    (hind : Integrable (Set.indicator {ω | ε ≤ X ω} (fun _ => (1 : ℝ))) P) :
    (P[Set.indicator {ω | ε ≤ X ω} (fun _ => (1 : ℝ)) | 𝒟])
      ≤ᵐ[P] fun ω => ε⁻¹ * (P[X | 𝒟]) ω := by
  have hle : Set.indicator {ω | ε ≤ X ω} (fun _ => (1 : ℝ)) ≤ᵐ[P] ((ε⁻¹ : ℝ) • X) := by
    filter_upwards with ω
    show Set.indicator {ω | ε ≤ X ω} (fun _ => (1 : ℝ)) ω ≤ ε⁻¹ * X ω
    by_cases hω : ω ∈ {ω | ε ≤ X ω}
    · rw [Set.indicator_of_mem hω]
      have hx : ε ≤ X ω := hω
      calc (1 : ℝ) = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
        _ ≤ ε⁻¹ * X ω := mul_le_mul_of_nonneg_left hx (by positivity)
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (by positivity) (hX0 ω)
  have hmono := condExp_mono (μ := P) (m := 𝒟) hind (hX.smul ((ε⁻¹ : ℝ))) hle
  have hsm := condExp_smul (μ := P) ((ε⁻¹ : ℝ)) X 𝒟
  filter_upwards [hmono, hsm] with ω e1 e2
  refine e1.trans (le_of_eq ?_)
  rw [e2]; rfl

/-- Scaling by a real constant preserves convergence in probability to zero. -/
theorem tendstoInMeasure_zero_const_mul {f : ℕ → Ω → ℝ} (a : ℝ)
    (hf : TendstoInMeasure P f atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => a * f n ω) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  rcases eq_or_ne a 0 with rfl | ha
  · have hz : ∀ n : ℕ, P {ω | ε ≤ dist ((0 : ℝ) * f n ω) ((fun _ => (0 : ℝ)) ω)} = 0 := by
      intro n
      convert measure_empty (μ := P)
      ext ω
      simp [not_le.mpr hε]
    have heq : (fun n : ℕ => P {ω | ε ≤ dist ((0 : ℝ) * f n ω) ((fun _ => (0 : ℝ)) ω)})
        = fun _ => 0 := funext hz
    rw [heq]
    exact tendsto_const_nhds
  · have hA : 0 < |a| := abs_pos.mpr ha
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hf (ε / |a|) (by positivity)) (fun _ => zero_le) (fun n => measure_mono ?_)
    intro ω hω
    have hω' : ε ≤ dist (a * f n ω) ((fun _ => (0 : ℝ)) ω) := hω
    show ε / |a| ≤ dist (f n ω) ((fun _ => (0 : ℝ)) ω)
    rw [Real.dist_eq, sub_zero] at hω' ⊢
    rw [abs_mul] at hω'
    rw [div_le_iff₀ hA]
    linarith

/-- A deterministic null sequence converges in probability to zero. -/
theorem tendstoInMeasure_zero_of_tendsto_const {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0)) :
    TendstoInMeasure P (fun n (_ : Ω) => b n) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hnull : ∀ᶠ n in atTop, P {ω : Ω | ε ≤ dist (b n) ((fun _ => (0 : ℝ)) ω)} = 0 := by
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.mp hb ε hε] with n hn
    convert measure_empty (μ := P)
    ext ω
    have hlt : |b n| < ε := by simpa [Real.norm_eq_abs] using hn
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hmem
    have hm' : ε ≤ dist (b n) ((fun _ => (0 : ℝ)) ω) := hmem
    rw [Real.dist_eq, sub_zero] at hm'
    linarith
  exact Tendsto.congr' (hnull.mono fun n hn => hn.symm) tendsto_const_nhds

/-- Bounded convergence for convergence in probability: if `0 ≤ Y_n ≤ 1` and `Y_n → 0` in
probability, then `∫Y_n → 0`. The proof uses `∫Y_n ≤ η + P(Y_n ≥ η)`. -/
theorem tendsto_integral_of_tendstoInMeasure_le_one [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} (hmeas : ∀ n, Measurable (Y n))
    (h0 : ∀ n ω, 0 ≤ Y n ω) (h1 : ∀ n ω, Y n ω ≤ 1)
    (hY : TendstoInMeasure P Y atTop (fun _ => (0 : ℝ))) :
    Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop (𝓝 0) := by
  have hint : ∀ n, Integrable (Y n) P := fun n =>
    Integrable.mono' (integrable_const (1 : ℝ)) (hmeas n).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 n ω)]; exact h1 n ω)
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hη0 : (0 : ℝ) < ε / 3 := by positivity
  rw [tendstoInMeasure_iff_dist] at hY
  have hset : ∀ n : ℕ, {ω | ε / 3 ≤ dist (Y n ω) ((fun _ => (0 : ℝ)) ω)}
      = {ω | ε / 3 ≤ Y n ω} := by
    intro n
    ext ω
    show (ε / 3 ≤ dist (Y n ω) ((fun _ => (0 : ℝ)) ω)) ↔ (ε / 3 ≤ Y n ω)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (h0 n ω)]
  have hbound : ∀ n : ℕ, ∫ ω, Y n ω ∂P ≤ ε / 3 + (P {ω | ε / 3 ≤ Y n ω}).toReal := by
    intro n
    have hs : MeasurableSet {ω | ε / 3 ≤ Y n ω} := measurableSet_le measurable_const (hmeas n)
    have hgi : Integrable (fun ω => ε / 3
        + Set.indicator {ω | ε / 3 ≤ Y n ω} (fun _ => (1 : ℝ)) ω) P :=
      (integrable_const (ε / 3)).add ((integrable_const (1 : ℝ)).indicator hs)
    have hptw : ∀ ω, Y n ω ≤ ε / 3
        + Set.indicator {ω | ε / 3 ≤ Y n ω} (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases hω : ω ∈ {ω | ε / 3 ≤ Y n ω}
      · rw [Set.indicator_of_mem hω]
        linarith [h1 n ω]
      · rw [Set.indicator_of_notMem hω]
        have hnot : ¬ (ε / 3 ≤ Y n ω) := hω
        linarith [not_le.mp hnot]
    refine (integral_mono (hint n) hgi (fun ω => hptw ω)).trans (le_of_eq ?_)
    rw [integral_add (integrable_const (ε / 3)) ((integrable_const (1 : ℝ)).indicator hs),
      integral_const, integral_indicator_const (1 : ℝ) hs]
    simp [measureReal_def]
  have hev := (ENNReal.tendsto_nhds_zero.mp (hY (ε / 3) hη0)) (ENNReal.ofReal (ε / 3))
    (by simpa using hη0)
  filter_upwards [hev] with n hn
  rw [hset n] at hn
  have h2 : (P {ω | ε / 3 ≤ Y n ω}).toReal ≤ ε / 3 :=
    ENNReal.toReal_le_of_le_ofReal hη0.le hn
  have h3 : 0 ≤ ∫ ω, Y n ω ∂P := integral_nonneg (fun ω => h0 n ω)
  rw [Real.norm_eq_abs, abs_of_nonneg h3]
  linarith [hbound n]

/-- A nonnegative `Z_n` whose conditional first moment given `𝒟` is dominated by a random
`ρ_n` that converges in probability to zero itself converges in probability to zero. -/
theorem tendstoInMeasure_zero_of_condExp_le [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)] {Z ρ : ℕ → Ω → ℝ}
    (hZmeas : ∀ n, Measurable (Z n)) (hZ0 : ∀ n ω, 0 ≤ Z n ω)
    (hZint : ∀ n, Integrable (Z n) P)
    (hρmeas : ∀ n, Measurable (ρ n)) (hρ0 : ∀ n ω, 0 ≤ ρ n ω)
    (hle : ∀ n, (P[Z n | 𝒟]) ≤ᵐ[P] ρ n)
    (hρ : TendstoInMeasure P ρ atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hεinv : (0 : ℝ) ≤ ε⁻¹ := by positivity
  set Y : ℕ → Ω → ℝ := fun n ω => min 1 (ε⁻¹ * ρ n ω) with hYdef
  have hYmeas : ∀ n, Measurable (Y n) := fun n =>
    measurable_const.min (measurable_const.mul (hρmeas n))
  have hY0 : ∀ n ω, 0 ≤ Y n ω := fun n ω =>
    le_min zero_le_one (mul_nonneg hεinv (hρ0 n ω))
  have hY1 : ∀ n ω, Y n ω ≤ 1 := fun n ω => min_le_left _ _
  have hYint : ∀ n, Integrable (Y n) P := fun n =>
    Integrable.mono' (integrable_const (1 : ℝ)) (hYmeas n).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hY0 n ω)]; exact hY1 n ω)
  have hYtend : TendstoInMeasure P Y atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_zero_of_le hY0 (fun n ω => min_le_right _ _)
      (tendstoInMeasure_zero_const_mul ε⁻¹ hρ)
  have hIY := tendsto_integral_of_tendstoInMeasure_le_one hYmeas hY0 hY1 hYtend
  have hmeasA : ∀ n, MeasurableSet {ω | ε ≤ Z n ω} := fun n =>
    measurableSet_le measurable_const (hZmeas n)
  have hindint : ∀ n, Integrable (Set.indicator {ω | ε ≤ Z n ω} (fun _ => (1 : ℝ))) P :=
    fun n => (integrable_const (1 : ℝ)).indicator (hmeasA n)
  have hkey : ∀ n, (P[Set.indicator {ω | ε ≤ Z n ω} (fun _ => (1 : ℝ)) | 𝒟]) ≤ᵐ[P] Y n := by
    intro n
    have hone : Set.indicator {ω | ε ≤ Z n ω} (fun _ => (1 : ℝ)) ≤ᵐ[P] fun _ => (1 : ℝ) := by
      filter_upwards with ω
      show Set.indicator {ω | ε ≤ Z n ω} (fun _ => (1 : ℝ)) ω ≤ 1
      by_cases hω : ω ∈ {ω | ε ≤ Z n ω}
      · rw [Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem hω]; exact zero_le_one
    have hb1 := condExp_mono (μ := P) (m := 𝒟) (hindint n) (integrable_const (1 : ℝ)) hone
    rw [condExp_const hm (1 : ℝ)] at hb1
    have hm1 := condMarkov_abs 𝒟 hε (hZ0 n) (hZint n) (hindint n)
    filter_upwards [hb1, hm1, hle n] with ω e1 e3 e4
    refine le_min e1 (e3.trans ?_)
    exact mul_le_mul_of_nonneg_left e4 hεinv
  have hPle : ∀ n, P {ω | ε ≤ Z n ω} ≤ ENNReal.ofReal (∫ ω, Y n ω ∂P) := by
    intro n
    have h1 : (P {ω | ε ≤ Z n ω}).toReal
        = ∫ ω, (P[Set.indicator {ω | ε ≤ Z n ω} (fun _ => (1 : ℝ)) | 𝒟]) ω ∂P := by
      rw [integral_condExp hm, integral_indicator_const (1 : ℝ) (hmeasA n)]
      simp [measureReal_def]
    have h2 : ∫ ω, (P[Set.indicator {ω | ε ≤ Z n ω} (fun _ => (1 : ℝ)) | 𝒟]) ω ∂P
        ≤ ∫ ω, Y n ω ∂P := integral_mono_ae integrable_condExp (hYint n) (hkey n)
    have h3 : (P {ω | ε ≤ Z n ω}).toReal ≤ ∫ ω, Y n ω ∂P := by rw [h1]; exact h2
    rw [← ENNReal.ofReal_toReal (measure_ne_top P {ω | ε ≤ Z n ω})]
    exact ENNReal.ofReal_le_ofReal h3
  have hfin : Tendsto (fun n => ENNReal.ofReal (∫ ω, Y n ω ∂P)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hIY
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfin
    (fun _ => zero_le) (fun n => ?_)
  refine le_trans (measure_mono ?_) (hPle n)
  intro ω hω
  have hω' : ε ≤ dist (Z n ω) ((fun _ => (0 : ℝ)) ω) := hω
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hZ0 n ω)] at hω'
  exact hω'

/-- The same passage from a conditional second-moment bound. -/
theorem tendstoInMeasure_zero_of_condExp_sq_le [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)] {Z ρ : ℕ → Ω → ℝ}
    (hZmeas : ∀ n, Measurable (Z n)) (hZ0 : ∀ n ω, 0 ≤ Z n ω)
    (hZint : ∀ n, Integrable (fun ω => Z n ω ^ 2) P)
    (hρmeas : ∀ n, Measurable (ρ n)) (hρ0 : ∀ n ω, 0 ≤ ρ n ω)
    (hle : ∀ n, (P[fun ω => Z n ω ^ 2 | 𝒟]) ≤ᵐ[P] ρ n)
    (hρ : TendstoInMeasure P ρ atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  have hsq : TendstoInMeasure P (fun n ω => Z n ω ^ 2) atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_zero_of_condExp_le 𝒟 hm (fun n => (hZmeas n).pow_const 2)
      (fun n ω => sq_nonneg _) hZint hρmeas hρ0 hle hρ
  rw [tendstoInMeasure_iff_dist] at hsq ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hsq (ε ^ 2) (by positivity)) (fun _ => zero_le) (fun n => measure_mono ?_)
  intro ω hω
  have hω' : ε ≤ dist (Z n ω) ((fun _ => (0 : ℝ)) ω) := hω
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hZ0 n ω)] at hω'
  show ε ^ 2 ≤ dist (Z n ω ^ 2) ((fun _ => (0 : ℝ)) ω)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]
  nlinarith [hZ0 n ω, hε.le]

end Bridge

/-! ## Lemma SM.B.13, second claim

`infeasibleMeat_tendstoInProb` proves `‖𝓜̃_n - Ω_n‖_F/λ_min(Ω_n) ⟶^p 0` over a sequence of
designs whose observation, cluster and coefficient types vary with the index. The key step,
`condExp_sq_div`, pulls the `𝒟`-measurable random divisor `λ_min(Ω_n)^{-2}` out of the
conditional expectation; this is legitimate because the first claim's bound
`64K²B⁴Cδ_nλ_min(Ω_n)²` equals `64K²B⁴C·nD_n³` and so does not depend on `λ_min`. The
integrability hypothesis `hdivint` is removed in `infeasibleMeat_tendstoInProb_nodiv`. -/

section MeatLimit

open Sharing

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Pulling a `𝒟`-measurable random divisor out of a conditional second moment:
`E[(F/λ)² ∣ 𝒟] = E[F² ∣ 𝒟]/λ²`. -/
theorem condExp_sq_div [IsProbabilityMeasure P] {F lam : Ω → ℝ}
    (hlam : Measurable[𝒟] lam)
    (hFint : Integrable (fun ω => F ω ^ 2) P)
    (hint : Integrable (fun ω => (F ω / lam ω) ^ 2) P) :
    (P[fun ω => (F ω / lam ω) ^ 2 | 𝒟])
      =ᵐ[P] fun ω => (P[fun ω => F ω ^ 2 | 𝒟]) ω / lam ω ^ 2 := by
  have hfm : StronglyMeasurable[𝒟] (fun ω => (lam ω ^ 2)⁻¹) :=
    ((hlam.pow_const 2).inv).stronglyMeasurable
  have hfg : ((fun ω => (lam ω ^ 2)⁻¹) * fun ω => F ω ^ 2) = fun ω => (F ω / lam ω) ^ 2 := by
    funext ω
    show (lam ω ^ 2)⁻¹ * F ω ^ 2 = (F ω / lam ω) ^ 2
    rw [div_pow, div_eq_inv_mul]
  have h := condExp_mul_of_stronglyMeasurable_left (m := 𝒟) (μ := P) hfm
    (by rw [hfg]; exact hint) hFint
  rw [hfg] at h
  filter_upwards [h] with ω hω
  rw [hω, Pi.mul_apply, div_eq_inv_mul]

variable {O D L κ : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable [Fintype κ] [DecidableEq κ]

omit [DecidableEq O] [DecidableEq D] [DecidableEq κ] in
/-- The squared Frobenius norm `‖·‖_F²` of the union-meat difference equals `frobSq`. -/
theorem sq_rectFrobNorm_unionMeat_sub (c : D → O → L) (dims : Finset D)
    (xt : O → κ → Ω → ℝ) (nu : O → Ω → ℝ) (Om : O → O → Ω → ℝ) :
    (fun ω => rectFrobNorm (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) ^ 2)
      = fun ω => frobSq (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) := by
  funext ω
  rw [rectFrobNorm, Real.sq_sqrt (rectFrobSq_nonneg _)]
  rfl

omit [DecidableEq D] [DecidableEq κ] in
/-- The first claim of Lemma SM.B.13 divided through by the random `λ_min(Ω_n)`:
`E[(‖𝓜̃_n - Ω_n‖_F/λ_min(Ω_n))² ∣ 𝒟] ≤ 64K²B⁴Cδ_n`, with `δ_n = nD_n³/λ²`. -/
theorem condExp_sq_ratio_unionMeat_le [IsProbabilityMeasure P] (c : D → O → L) (dims : Finset D)
    {xt : O → κ → Ω → ℝ} {nu : O → Ω → ℝ} {Om : O → O → Ω → ℝ} {B Cm : ℝ} (hC : 0 ≤ Cm)
    {lam : Ω → ℝ} (hlamM : Measurable[𝒟] lam) (hlam0 : ∀ ω, 0 < lam ω)
    (hFint : Integrable (fun ω =>
      frobSq (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω)) P)
    (hdivint : Integrable (fun ω =>
      (rectFrobNorm (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) / lam ω) ^ 2) P)
    (hint : ∀ k l : κ, ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      Integrable (fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω) P)
    (hzero : ∀ k l : κ, ∀ p ∈ linkedPairs c dims, ∀ q ∈ linkedPairs c dims,
      (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims →
      (P[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) =ᵐ[P] 0)
    (hbd : ∀ k l : κ, ∀ p q : O × O, ∀ᵐ ω ∂P,
      |(P[fun ω => centeredSummand xt nu Om k l p ω
        * centeredSummand xt nu Om k l q ω | 𝒟]) ω| ≤ 2 * B ^ 4 * Cm) :
    (P[fun ω =>
        (rectFrobNorm (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) / lam ω) ^ 2 | 𝒟])
      ≤ᵐ[P] fun ω => 64 * (Fintype.card κ : ℝ) ^ 2 * B ^ 4 * Cm
          * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) (lam ω) := by
  have h1 := infeasibleMeat_condVar_le 𝒟 c dims (B := B) (Cm := Cm) (lmin := 1) hC one_pos
    hint hzero hbd
  have h2 := condExp_sq_div 𝒟 hlamM
    (by rw [sq_rectFrobNorm_unionMeat_sub]; exact hFint) hdivint
  rw [sq_rectFrobNorm_unionMeat_sub] at h2
  filter_upwards [h1, h2] with ω e1 e2
  rw [e2]
  have hl2 : (0 : ℝ) < lam ω ^ 2 := pow_pos (hlam0 ω) 2
  have e1' : (P[fun ω => frobSq (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) | 𝒟]) ω
      ≤ 64 * (Fintype.card κ : ℝ) ^ 2 * B ^ 4 * Cm
        * ((Fintype.card O : ℝ) * (maxDegree c dims : ℝ) ^ 3) := by
    simpa [deltaSeq] using e1
  calc (P[fun ω => frobSq (unionMeat c dims xt nu ω - scoreVar c dims xt Om ω) | 𝒟]) ω
        / lam ω ^ 2
      ≤ (64 * (Fintype.card κ : ℝ) ^ 2 * B ^ 4 * Cm
          * ((Fintype.card O : ℝ) * (maxDegree c dims : ℝ) ^ 3)) / lam ω ^ 2 := by
        gcongr
    _ = 64 * (Fintype.card κ : ℝ) ^ 2 * B ^ 4 * Cm
          * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) (lam ω) := by
        rw [deltaSeq]; ring

end MeatLimit

section MeatSequence

open Sharing

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Lemma SM.B.13, second claim.** `‖𝓜̃_n - Ω_n‖_F/λ_min(Ω_n) ⟶^p 0`, given `δ_n ⟶^p 0`
(`hdelta`), the hypotheses of the first claim (`hint`, `hzero`, `hbd`), and measurability and
integrability conditions (`hFmeas`, `hFint`, `hdivint`). -/
theorem infeasibleMeat_tendstoInProb [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)]
    {O D L κ : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, DecidableEq (L j)] [∀ j, Fintype (κ j)]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j))
    (xt : ∀ j, O j → κ j → Ω → ℝ) (nu : ∀ j, O j → Ω → ℝ) (Om : ∀ j, O j → O j → Ω → ℝ)
    {B Cm : ℝ} (hC : 0 ≤ Cm)
    {lam : ℕ → Ω → ℝ} (hlamM : ∀ j, Measurable[𝒟] (lam j)) (hlam0 : ∀ j ω, 0 < lam j ω)
    (hFmeas : ∀ j, Measurable (fun ω =>
      rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (Om j) ω)))
    (hFint : ∀ j, Integrable (fun ω =>
      frobSq (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (Om j) ω)) P)
    (hdivint : ∀ j, Integrable (fun ω =>
      (rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (Om j) ω) / lam j ω) ^ 2) P)
    (hint : ∀ j, ∀ k l : κ j, ∀ p ∈ linkedPairs (c j) (dims j),
      ∀ q ∈ linkedPairs (c j) (dims j),
      Integrable (fun ω => centeredSummand (xt j) (nu j) (Om j) k l p ω
        * centeredSummand (xt j) (nu j) (Om j) k l q ω) P)
    (hzero : ∀ j, ∀ k l : κ j, ∀ p ∈ linkedPairs (c j) (dims j),
      ∀ q ∈ linkedPairs (c j) (dims j),
      (p.1, p.2, q.1, q.2) ∉ linkedQuads (c j) (dims j) →
      (P[fun ω => centeredSummand (xt j) (nu j) (Om j) k l p ω
        * centeredSummand (xt j) (nu j) (Om j) k l q ω | 𝒟]) =ᵐ[P] 0)
    (hbd : ∀ j, ∀ k l : κ j, ∀ p q : O j × O j, ∀ᵐ ω ∂P,
      |(P[fun ω => centeredSummand (xt j) (nu j) (Om j) k l p ω
        * centeredSummand (xt j) (nu j) (Om j) k l q ω | 𝒟]) ω| ≤ 2 * B ^ 4 * Cm)
    (hdelta : TendstoInMeasure P (fun j ω => 64 * (Fintype.card (κ j) : ℝ) ^ 2 * B ^ 4 * Cm
        * deltaSeq (Fintype.card (O j) : ℝ) (maxDegree (c j) (dims j) : ℝ) (lam j ω))
        atTop (fun _ => 0)) :
    TendstoInMeasure P (fun j ω =>
        rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
          - scoreVar (c j) (dims j) (xt j) (Om j) ω) / lam j ω) atTop (fun _ => 0) := by
  have hlamΩ : ∀ j, Measurable (lam j) := fun j => (hlamM j).mono hm le_rfl
  refine tendstoInMeasure_zero_of_condExp_sq_le 𝒟 hm
    (fun j => (hFmeas j).div (hlamΩ j))
    (fun j ω => div_nonneg (rectFrobNorm_nonneg _) (hlam0 j ω).le)
    hdivint (fun j => ?_) (fun j ω => ?_) (fun j => ?_) hdelta
  · simp only [deltaSeq]
    exact measurable_const.mul (measurable_const.div ((hlamΩ j).pow_const 2))
  · refine mul_nonneg (mul_nonneg (by positivity) hC) ?_
    rw [deltaSeq]
    positivity
  · exact condExp_sq_ratio_unionMeat_le 𝒟 (c j) (dims j) hC (hlamM j) (hlam0 j)
      (hFint j) (hdivint j) (hint j) (hzero j) (hbd j)

end MeatSequence

/-! ## The perturbation from fixed-effects residuals

`perturb_tendstoInProb` proves `‖𝓜̂_CGM - 𝓜̃_n‖_F/λ_min(Ω_n) ⟶^p 0` over a sequence of designs,
combining the deterministic perturbation bound, a conditional Young inequality
`2XY ≤ tX² + t⁻¹Y²` with deterministic `t = (b/a)^{1/2}` (valid for `a, b > 0`), the pull-out
of the random divisor, and the conditional Markov passage. It takes as hypotheses the two
conditional second-moment bounds `hnu`, `hvp` and the rate condition `hrate`;
`perturb_tendstoInProb_of_accum` discharges `hrate` from the accumulation assumption, and
`perturb_tendstoInProb_of_moments` also discharges `hnu` and `hvp`. -/

section PerturbSequence

open Sharing

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Conditional Young inequality: from `E[X² ∣ 𝒟] ≤ a` and `E[Y² ∣ 𝒟] ≤ b` with real
`a, b > 0`, `E[2XY + Y² ∣ 𝒟] ≤ 2(ab)^{1/2} + b`. -/
theorem condExp_two_mul_add_sq_le [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hXint : Integrable (fun ω => X ω ^ 2) P) (hYint : Integrable (fun ω => Y ω ^ 2) P)
    (hmix : Integrable (fun ω => 2 * X ω * Y ω + Y ω ^ 2) P)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hXa : (P[fun ω => X ω ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => a)
    (hYb : (P[fun ω => Y ω ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => b) :
    (P[fun ω => 2 * X ω * Y ω + Y ω ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => 2 * Real.sqrt (a * b) + b := by
  obtain ⟨sa, hsa0, hsa⟩ : ∃ sa : ℝ, 0 < sa ∧ sa ^ 2 = a :=
    ⟨Real.sqrt a, Real.sqrt_pos.mpr ha, Real.sq_sqrt ha.le⟩
  obtain ⟨sb, hsb0, hsb⟩ : ∃ sb : ℝ, 0 < sb ∧ sb ^ 2 = b :=
    ⟨Real.sqrt b, Real.sqrt_pos.mpr hb, Real.sq_sqrt hb.le⟩
  have ht0 : 0 < sb / sa := div_pos hsb0 hsa0
  have hptw : (fun ω => 2 * X ω * Y ω + Y ω ^ 2)
      ≤ᵐ[P] (((sb / sa) • (fun ω => X ω ^ 2)) + ((sb / sa)⁻¹ • (fun ω => Y ω ^ 2))
        + (fun ω => Y ω ^ 2) : Ω → ℝ) := by
    filter_upwards with ω
    show 2 * X ω * Y ω + Y ω ^ 2
        ≤ (sb / sa) * X ω ^ 2 + (sb / sa)⁻¹ * Y ω ^ 2 + Y ω ^ 2
    have hkey : (sb / sa) * (X ω - Y ω / (sb / sa)) ^ 2
        = (sb / sa) * X ω ^ 2 + (sb / sa)⁻¹ * Y ω ^ 2 - 2 * X ω * Y ω := by
      field_simp
      ring
    have hnn : 0 ≤ (sb / sa) * (X ω - Y ω / (sb / sa)) ^ 2 :=
      mul_nonneg ht0.le (sq_nonneg _)
    linarith
  have hmaj : Integrable (((sb / sa) • (fun ω => X ω ^ 2)) + ((sb / sa)⁻¹ • (fun ω => Y ω ^ 2))
      + (fun ω => Y ω ^ 2) : Ω → ℝ) P :=
    ((hXint.smul (sb / sa)).add (hYint.smul (sb / sa)⁻¹)).add hYint
  have hmono := condExp_mono (μ := P) (m := 𝒟) hmix hmaj hptw
  have s1 := condExp_add (μ := P)
    ((hXint.smul (sb / sa)).add (hYint.smul (sb / sa)⁻¹)) hYint 𝒟
  have s2 := condExp_add (μ := P) (hXint.smul (sb / sa)) (hYint.smul (sb / sa)⁻¹) 𝒟
  have s3 := condExp_smul (μ := P) (sb / sa) (fun ω => X ω ^ 2) 𝒟
  have s4 := condExp_smul (μ := P) (sb / sa)⁻¹ (fun ω => Y ω ^ 2) 𝒟
  have hsqrtmul : Real.sqrt (a * b) = sa * sb := by
    rw [← hsa, ← hsb, ← mul_pow]
    exact Real.sqrt_sq (by positivity)
  have halg : (sb / sa) * a + (sb / sa)⁻¹ * b + b = 2 * Real.sqrt (a * b) + b := by
    rw [hsqrtmul, ← hsa, ← hsb]
    field_simp
    ring
  filter_upwards [hmono, s1, s2, s3, s4, hXa, hYb] with ω m1 e1 e2 e3 e4 gX gY
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
  rw [e1, e2, e3, e4] at m1
  have gX' : (P[fun ω => X ω ^ 2 | 𝒟]) ω ≤ a := gX
  have gY' : (P[fun ω => Y ω ^ 2 | 𝒟]) ω ≤ b := gY
  have p1 : (sb / sa) * (P[fun ω => X ω ^ 2 | 𝒟]) ω ≤ (sb / sa) * a :=
    mul_le_mul_of_nonneg_left gX' ht0.le
  have p2 : (sb / sa)⁻¹ * (P[fun ω => Y ω ^ 2 | 𝒟]) ω ≤ (sb / sa)⁻¹ * b :=
    mul_le_mul_of_nonneg_left gY' (inv_pos.mpr ht0).le
  show (P[fun ω => 2 * X ω * Y ω + Y ω ^ 2 | 𝒟]) ω ≤ 2 * Real.sqrt (a * b) + b
  linarith

/-! ### The rate arithmetic

`rate_le_of_sharing_e` bounds the majorant at one index, `tendstoInMeasure_zero_sqrt` shows that
convergence in probability to zero survives the square root, and `rate_tendstoInProb_of_accum`
supplies the rate hypothesis `hrate` of `perturb_tendstoInProb`. -/

/-- The rate arithmetic at one index. With `a_n = C^{1/2}n` and `b_n = C^{1/2}(d_{[Δ]}+K)(D_n+1)`,
the majorant `B²(D_n+1)λ_min(Ω_n)^{-1}(2(a_nb_n)^{1/2} + b_n)` is at most
`c₁(δ_nd_{[Δ]})^{1/2} + c₂δ_nd_{[Δ]}` with `c₁ = (32B⁴C(1+K))^{1/2}` and `c₂ = 8B⁴C(1+K)`,
using `D_n ≥ 1`, `d_{[Δ]} ≥ 1` and `he`, the bound `D_n²/λ_min(Ω_n) ≤ 2B²C^{1/2}δ_n` of
Lemma SM.B.11(e). The square-root inequality is proved by squaring both sides. -/
theorem rate_le_of_sharing_e {B Csq Kr nR dd Dn lmin : ℝ}
    (hCsq : 0 ≤ Csq) (hK0 : 0 ≤ Kr) (hn0 : 0 ≤ nR) (hdd : 1 ≤ dd) (hD : 1 ≤ Dn)
    (hlmin : 0 < lmin)
    (he : Dn ^ 2 / lmin ≤ 2 * B ^ 2 * Csq * deltaSeq nR Dn lmin) :
    B ^ 2 * (Dn + 1) / lmin
        * (2 * Real.sqrt (Csq * nR * (Csq * (dd + Kr) * (Dn + 1)))
            + Csq * (dd + Kr) * (Dn + 1))
      ≤ Real.sqrt (32 * B ^ 4 * Csq ^ 2 * (1 + Kr))
            * Real.sqrt (deltaSeq nR Dn lmin * dd)
        + 8 * B ^ 4 * Csq ^ 2 * (1 + Kr) * (deltaSeq nR Dn lmin * dd) := by
  have ht : (0 : ℝ) ≤ Dn - 1 := by linarith
  have hd0 : (0 : ℝ) ≤ dd := by linarith
  have hlne : lmin ≠ 0 := hlmin.ne'
  have hdel0 : (0 : ℝ) ≤ deltaSeq nR Dn lmin := by
    rw [deltaSeq]
    exact div_nonneg (mul_nonneg hn0 (pow_nonneg (by linarith) 3)) (sq_nonneg _)
  have hdK : dd + Kr ≤ (1 + Kr) * dd := by nlinarith
  have hT0 : (0 : ℝ) ≤ B ^ 2 * (Dn + 1) / lmin :=
    div_nonneg (mul_nonneg (sq_nonneg B) (by linarith)) hlmin.le
  have h8 : (Dn + 1) ^ 3 ≤ 8 * Dn ^ 3 := by
    nlinarith [ht, mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
  have h4 : (Dn + 1) ^ 2 ≤ 4 * Dn ^ 2 := by nlinarith [ht, mul_nonneg ht ht]
  have hp1 : 2 * (B ^ 2 * (Dn + 1) / lmin)
        * Real.sqrt (Csq * nR * (Csq * (dd + Kr) * (Dn + 1)))
      ≤ Real.sqrt (32 * B ^ 4 * Csq ^ 2 * (1 + Kr))
          * Real.sqrt (deltaSeq nR Dn lmin * dd) := by
    have hc1nn : (0 : ℝ) ≤ 32 * B ^ 4 * Csq ^ 2 * (1 + Kr) :=
      mul_nonneg (by positivity) (by linarith)
    have hLeq : 2 * (B ^ 2 * (Dn + 1) / lmin)
          * Real.sqrt (Csq * nR * (Csq * (dd + Kr) * (Dn + 1)))
        = Real.sqrt ((2 * (B ^ 2 * (Dn + 1) / lmin)) ^ 2
            * (Csq * nR * (Csq * (dd + Kr) * (Dn + 1)))) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
    have hReq : Real.sqrt (32 * B ^ 4 * Csq ^ 2 * (1 + Kr))
          * Real.sqrt (deltaSeq nR Dn lmin * dd)
        = Real.sqrt ((32 * B ^ 4 * Csq ^ 2 * (1 + Kr)) * (deltaSeq nR Dn lmin * dd)) :=
      (Real.sqrt_mul hc1nn _).symm
    rw [hLeq, hReq]
    refine Real.sqrt_le_sqrt ?_
    have hPQ : 4 * B ^ 4 * Csq ^ 2 * nR * ((dd + Kr) * (Dn + 1) ^ 3)
        ≤ 4 * B ^ 4 * Csq ^ 2 * nR * ((1 + Kr) * dd * (8 * Dn ^ 3)) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hn0)
      exact mul_le_mul hdK h8 (pow_nonneg (by linarith) 3)
        (mul_nonneg (by linarith) hd0)
    have heq1 : (2 * (B ^ 2 * (Dn + 1) / lmin)) ^ 2
          * (Csq * nR * (Csq * (dd + Kr) * (Dn + 1)))
        = (4 * B ^ 4 * Csq ^ 2 * nR * ((dd + Kr) * (Dn + 1) ^ 3)) / lmin ^ 2 := by
      field_simp
      ring
    have heq2 : 32 * B ^ 4 * Csq ^ 2 * (1 + Kr) * (deltaSeq nR Dn lmin * dd)
        = (4 * B ^ 4 * Csq ^ 2 * nR * ((1 + Kr) * dd * (8 * Dn ^ 3))) / lmin ^ 2 := by
      rw [deltaSeq]
      field_simp
      ring
    rw [heq1, heq2, ← sub_nonneg, ← sub_div]
    exact div_nonneg (by linarith) (by positivity)
  have hp2 : B ^ 2 * (Dn + 1) / lmin * (Csq * (dd + Kr) * (Dn + 1))
      ≤ 8 * B ^ 4 * Csq ^ 2 * (1 + Kr) * (deltaSeq nR Dn lmin * dd) := by
    have hdiv : (Dn + 1) ^ 2 / lmin ≤ 4 * (Dn ^ 2 / lmin) := by
      rw [← sub_nonneg]
      have hrw : 4 * (Dn ^ 2 / lmin) - (Dn + 1) ^ 2 / lmin
          = (4 * Dn ^ 2 - (Dn + 1) ^ 2) / lmin := by ring
      rw [hrw]
      exact div_nonneg (by linarith) hlmin.le
    have hstep : (Dn + 1) ^ 2 / lmin ≤ 8 * B ^ 2 * Csq * deltaSeq nR Dn lmin := by
      linarith
    have hcoef : (0 : ℝ) ≤ B ^ 2 * Csq * (dd + Kr) :=
      mul_nonneg (mul_nonneg (sq_nonneg B) hCsq) (by linarith)
    have hid : B ^ 2 * (Dn + 1) / lmin * (Csq * (dd + Kr) * (Dn + 1))
        = B ^ 2 * Csq * (dd + Kr) * ((Dn + 1) ^ 2 / lmin) := by ring
    rw [hid]
    calc B ^ 2 * Csq * (dd + Kr) * ((Dn + 1) ^ 2 / lmin)
        ≤ B ^ 2 * Csq * (dd + Kr) * (8 * B ^ 2 * Csq * deltaSeq nR Dn lmin) :=
          mul_le_mul_of_nonneg_left hstep hcoef
      _ = 8 * B ^ 4 * Csq ^ 2 * ((dd + Kr) * deltaSeq nR Dn lmin) := by ring
      _ ≤ 8 * B ^ 4 * Csq ^ 2 * ((1 + Kr) * dd * deltaSeq nR Dn lmin) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdK hdel0) (by positivity)
      _ = 8 * B ^ 4 * Csq ^ 2 * (1 + Kr) * (deltaSeq nR Dn lmin * dd) := by ring
  have hsplit : B ^ 2 * (Dn + 1) / lmin
        * (2 * Real.sqrt (Csq * nR * (Csq * (dd + Kr) * (Dn + 1)))
          + Csq * (dd + Kr) * (Dn + 1))
      = 2 * (B ^ 2 * (Dn + 1) / lmin)
          * Real.sqrt (Csq * nR * (Csq * (dd + Kr) * (Dn + 1)))
        + B ^ 2 * (Dn + 1) / lmin * (Csq * (dd + Kr) * (Dn + 1)) := by ring
  rw [hsplit]
  linarith

/-- Convergence in probability to zero is preserved by the square root, since
`ε ≤ X^{1/2}` implies `ε² ≤ X`. -/
theorem tendstoInMeasure_zero_sqrt {f : ℕ → Ω → ℝ} (hnn : ∀ n ω, 0 ≤ f n ω)
    (hf : TendstoInMeasure P f atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => Real.sqrt (f n ω)) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hf (ε ^ 2) (by positivity)) (fun _ => zero_le) (fun n => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hω
  rw [abs_of_nonneg (hnn n ω)]
  have h1 : ε ^ 2 ≤ Real.sqrt (f n ω) ^ 2 := by nlinarith [Real.sqrt_nonneg (f n ω)]
  rwa [Real.sq_sqrt (hnn n ω)] at h1

/-- The rate hypothesis `hrate` of `perturb_tendstoInProb`, at `a_n = C^{1/2}n` and
`b_n = C^{1/2}(d_{[Δ]}+K)(D_n+1)`, derived from the accumulation condition `δ_nd_{[Δ]} ⟶^p 0`
and the bound `hsharing` of Lemma SM.B.11(e) (proved in `Multiway.Sharing`). -/
theorem rate_tendstoInProb_of_accum
    {O D L : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, DecidableEq (L j)]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j))
    {lam : ℕ → Ω → ℝ} (hlam0 : ∀ j ω, 0 < lam j ω)
    {B Csq Kr : ℝ} (hCsq : 0 ≤ Csq) (hK0 : 0 ≤ Kr)
    {nR dd : ℕ → ℝ} (hn0 : ∀ j, 0 ≤ nR j) (hdd : ∀ j, 1 ≤ dd j)
    {a b : ℕ → ℝ}
    (hadef : ∀ j, a j = Csq * nR j)
    (hbdef : ∀ j, b j = Csq * (dd j + Kr) * ((maxDegree (c j) (dims j) : ℝ) + 1))
    (hsharing : ∀ (j : ℕ) (ω : Ω), ((maxDegree (c j) (dims j) : ℝ)) ^ 2 / lam j ω
      ≤ 2 * B ^ 2 * Csq * deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω))
    (hacc : TendstoInMeasure P
      (fun j ω => deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω) * dd j)
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun j ω =>
        B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
          * (2 * Real.sqrt (a j * b j) + b j)) atTop (fun _ => (0 : ℝ)) := by
  have hD1 : ∀ j, (1 : ℝ) ≤ ((maxDegree (c j) (dims j) : ℕ) : ℝ) := fun j => by
    exact_mod_cast one_le_maxDegree (c j) (dims j)
  have hdel0 : ∀ (j : ℕ) (ω : Ω),
      (0 : ℝ) ≤ deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω) := by
    intro j ω
    rw [deltaSeq]
    exact div_nonneg (mul_nonneg (hn0 j) (pow_nonneg (by linarith [hD1 j]) 3)) (sq_nonneg _)
  have hY0 : ∀ (j : ℕ) (ω : Ω),
      (0 : ℝ) ≤ deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω) * dd j :=
    fun j ω => mul_nonneg (hdel0 j ω) (by linarith [hdd j])
  refine tendstoInMeasure_zero_of_le (f := fun j ω =>
      B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
        * (2 * Real.sqrt (a j * b j) + b j))
    (g := fun j ω => Real.sqrt (32 * B ^ 4 * Csq ^ 2 * (1 + Kr))
        * Real.sqrt (deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω) * dd j)
      + 8 * B ^ 4 * Csq ^ 2 * (1 + Kr)
        * (deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω) * dd j))
    (fun j ω => ?_) (fun j ω => ?_) ?_
  · have hb0 : (0 : ℝ) ≤ b j := by
      rw [hbdef j]
      exact mul_nonneg (mul_nonneg hCsq (by linarith [hdd j])) (by linarith [hD1 j])
    have hT0 : (0 : ℝ) ≤ B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω :=
      div_nonneg (mul_nonneg (sq_nonneg B) (by linarith [hD1 j])) (hlam0 j ω).le
    have : (0 : ℝ) ≤ 2 * Real.sqrt (a j * b j) + b j := by
      have := Real.sqrt_nonneg (a j * b j)
      linarith
    exact mul_nonneg hT0 this
  · rw [hadef j, hbdef j]
    exact rate_le_of_sharing_e hCsq hK0 (hn0 j) (hdd j) (hD1 j) (hlam0 j ω) (hsharing j ω)
  · exact tendstoInMeasure_zero_add
      (tendstoInMeasure_zero_const_mul _ (tendstoInMeasure_zero_sqrt hY0 hacc))
      (tendstoInMeasure_zero_const_mul _ hacc)

/-- **Theorem 11(b), perturbation step.** `‖𝓜̂_CGM - 𝓜̃_n‖_F/λ_min(Ω_n) ⟶^p 0`, where
`𝓜̂_CGM` is `unionMeat` at the fixed-effects residual `ν̂_FE = ν - ϖ` and `𝓜̃_n` is
`unionMeat` at `ν`. -/
theorem perturb_tendstoInProb [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)]
    {O D L κ : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, DecidableEq (L j)] [∀ j, Fintype (κ j)]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j))
    (xt : ∀ j, O j → κ j → Ω → ℝ) (nu vp : ∀ j, O j → Ω → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hxt : ∀ (j : ℕ) (o : O j) (ω : Ω), ∑ k : κ j, xt j o k ω ^ 2 ≤ B ^ 2)
    {lam : ℕ → Ω → ℝ} (hlamM : ∀ j, Measurable[𝒟] (lam j)) (hlam0 : ∀ j ω, 0 < lam j ω)
    {a b : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hnumeas : ∀ (j : ℕ) (o : O j), Measurable (nu j o))
    (hvpmeas : ∀ (j : ℕ) (o : O j), Measurable (vp j o))
    (hnuint : ∀ j, Integrable (fun ω => l2Norm (fun o => nu j o ω) ^ 2) P)
    (hvpint : ∀ j, Integrable (fun ω => l2Norm (fun o => vp j o ω) ^ 2) P)
    (hmajint : ∀ j, Integrable (fun ω =>
        B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
          * (2 * l2Norm (fun o => nu j o ω) * l2Norm (fun o => vp j o ω)
            + l2Norm (fun o => vp j o ω) ^ 2)) P)
    (hnu : ∀ j, (P[fun ω => l2Norm (fun o => nu j o ω) ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => a j)
    (hvp : ∀ j, (P[fun ω => l2Norm (fun o => vp j o ω) ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => b j)
    (hrate : TendstoInMeasure P (fun j ω =>
        B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
          * (2 * Real.sqrt (a j * b j) + b j)) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun j ω =>
        rectFrobNorm (unionMeat (c j) (dims j) (xt j) (fun o ω => nu j o ω - vp j o ω) ω
          - unionMeat (c j) (dims j) (xt j) (nu j) ω) / lam j ω) atTop (fun _ => 0) := by
  have hlamΩ : ∀ j, Measurable (lam j) := fun j => (hlamM j).mono hm le_rfl
  have hX : ∀ j, Measurable (fun ω => l2Norm (fun o => nu j o ω)) := fun j =>
    (Finset.measurable_sum _ fun o _ => (hnumeas j o).pow_const 2).sqrt
  have hY : ∀ j, Measurable (fun ω => l2Norm (fun o => vp j o ω)) := fun j =>
    (Finset.measurable_sum _ fun o _ => (hvpmeas j o).pow_const 2).sqrt
  have hWmeas : ∀ j, Measurable (fun ω => 2 * l2Norm (fun o => nu j o ω)
      * l2Norm (fun o => vp j o ω) + l2Norm (fun o => vp j o ω) ^ 2) := fun j =>
    ((measurable_const.mul (hX j)).mul (hY j)).add ((hY j).pow_const 2)
  have hg : ∀ j, Measurable (fun ω => B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω) :=
    fun j => measurable_const.div (hlamΩ j)
  have hgD : ∀ j, StronglyMeasurable[𝒟]
      (fun ω => B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω) := fun j =>
    (measurable_const.div (hlamM j)).stronglyMeasurable
  have hg0 : ∀ (j : ℕ) (ω : Ω),
      0 ≤ B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω := fun j ω =>
    div_nonneg (by positivity) (hlam0 j ω).le
  have hW0 : ∀ (j : ℕ) (ω : Ω), 0 ≤ 2 * l2Norm (fun o => nu j o ω)
      * l2Norm (fun o => vp j o ω) + l2Norm (fun o => vp j o ω) ^ 2 := by
    intro j ω
    have h1 := l2Norm_nonneg (fun o => nu j o ω)
    have h2 := l2Norm_nonneg (fun o => vp j o ω)
    positivity
  have hWint : ∀ j, Integrable (fun ω => 2 * l2Norm (fun o => nu j o ω)
      * l2Norm (fun o => vp j o ω) + l2Norm (fun o => vp j o ω) ^ 2) P := by
    intro j
    refine Integrable.mono' ((hnuint j).add ((hvpint j).add (hvpint j)))
      (hWmeas j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 j ω)]
    show 2 * l2Norm (fun o => nu j o ω) * l2Norm (fun o => vp j o ω)
        + l2Norm (fun o => vp j o ω) ^ 2
      ≤ l2Norm (fun o => nu j o ω) ^ 2
        + (l2Norm (fun o => vp j o ω) ^ 2 + l2Norm (fun o => vp j o ω) ^ 2)
    nlinarith [sq_nonneg (l2Norm (fun o => nu j o ω) - l2Norm (fun o => vp j o ω))]
  have hle : ∀ j, (P[fun ω => B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
        * (2 * l2Norm (fun o => nu j o ω) * l2Norm (fun o => vp j o ω)
          + l2Norm (fun o => vp j o ω) ^ 2) | 𝒟])
      ≤ᵐ[P] fun ω => B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
        * (2 * Real.sqrt (a j * b j) + b j) := by
    intro j
    have hmul := condExp_mul_of_stronglyMeasurable_left (m := 𝒟) (μ := P) (hgD j)
      (g := fun ω => 2 * l2Norm (fun o => nu j o ω) * l2Norm (fun o => vp j o ω)
        + l2Norm (fun o => vp j o ω) ^ 2) (hmajint j) (hWint j)
    have hcs := condExp_two_mul_add_sq_le 𝒟 (hnuint j) (hvpint j) (hWint j) (ha j) (hb j)
      (hnu j) (hvp j)
    filter_upwards [hmul, hcs] with ω e1 e2
    calc (P[fun ω => B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
          * (2 * l2Norm (fun o => nu j o ω) * l2Norm (fun o => vp j o ω)
            + l2Norm (fun o => vp j o ω) ^ 2) | 𝒟]) ω
        = B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
          * (P[fun ω => 2 * l2Norm (fun o => nu j o ω) * l2Norm (fun o => vp j o ω)
            + l2Norm (fun o => vp j o ω) ^ 2 | 𝒟]) ω := e1
      _ ≤ B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
          * (2 * Real.sqrt (a j * b j) + b j) := mul_le_mul_of_nonneg_left e2 (hg0 j ω)
  refine tendstoInMeasure_zero_of_le
    (fun j ω => div_nonneg (rectFrobNorm_nonneg _) (hlam0 j ω).le) (fun j ω => ?_)
    (tendstoInMeasure_zero_of_condExp_le 𝒟 hm (fun j => (hg j).mul (hWmeas j))
      (fun j ω => mul_nonneg (hg0 j ω) (hW0 j ω)) hmajint
      (fun j => (hg j).mul measurable_const)
      (fun j ω => mul_nonneg (hg0 j ω) (add_nonneg (by positivity) (hb j).le)) hle hrate)
  have hd := rectFrobNorm_unionMeat_perturb_le (c j) (dims j) (xt j) hB (hxt j) (nu j) (vp j) ω
  rw [div_le_iff₀ (hlam0 j ω)]
  have hlne : lam j ω ≠ 0 := (hlam0 j ω).ne'
  refine hd.trans (le_of_eq ?_)
  simp only [Pi.mul_apply]
  field_simp

/-- `perturb_tendstoInProb` with `hrate` discharged, at `a_n = C^{1/2}n` and
`b_n = C^{1/2}(d_{[Δ]}+K)(D_n+1)`, whose positivity follows from `C > 0`, `n > 0` and
`d_{[Δ]} ≥ 1`. The remaining hypotheses are the conditional second-moment bounds `hnu`, `hvp`,
Lemma SM.B.11(e) (`hsharing`) and the accumulation condition `hacc`. -/
theorem perturb_tendstoInProb_of_accum [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)]
    {O D L κ : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, DecidableEq (L j)] [∀ j, Fintype (κ j)]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j))
    (xt : ∀ j, O j → κ j → Ω → ℝ) (nu vp : ∀ j, O j → Ω → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hxt : ∀ (j : ℕ) (o : O j) (ω : Ω), ∑ k : κ j, xt j o k ω ^ 2 ≤ B ^ 2)
    {lam : ℕ → Ω → ℝ} (hlamM : ∀ j, Measurable[𝒟] (lam j)) (hlam0 : ∀ j ω, 0 < lam j ω)
    {Csq Kr : ℝ} (hCsq : 0 < Csq) (hK0 : 0 ≤ Kr)
    {nR dd : ℕ → ℝ} (hn : ∀ j, 0 < nR j) (hdd : ∀ j, 1 ≤ dd j)
    {a b : ℕ → ℝ}
    (hadef : ∀ j, a j = Csq * nR j)
    (hbdef : ∀ j, b j = Csq * (dd j + Kr) * ((maxDegree (c j) (dims j) : ℝ) + 1))
    (hnumeas : ∀ (j : ℕ) (o : O j), Measurable (nu j o))
    (hvpmeas : ∀ (j : ℕ) (o : O j), Measurable (vp j o))
    (hnuint : ∀ j, Integrable (fun ω => l2Norm (fun o => nu j o ω) ^ 2) P)
    (hvpint : ∀ j, Integrable (fun ω => l2Norm (fun o => vp j o ω) ^ 2) P)
    (hmajint : ∀ j, Integrable (fun ω =>
        B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
          * (2 * l2Norm (fun o => nu j o ω) * l2Norm (fun o => vp j o ω)
            + l2Norm (fun o => vp j o ω) ^ 2)) P)
    (hnu : ∀ j, (P[fun ω => l2Norm (fun o => nu j o ω) ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => a j)
    (hvp : ∀ j, (P[fun ω => l2Norm (fun o => vp j o ω) ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => b j)
    (hsharing : ∀ (j : ℕ) (ω : Ω), ((maxDegree (c j) (dims j) : ℝ)) ^ 2 / lam j ω
      ≤ 2 * B ^ 2 * Csq * deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω))
    (hacc : TendstoInMeasure P
      (fun j ω => deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω) * dd j)
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun j ω =>
        rectFrobNorm (unionMeat (c j) (dims j) (xt j) (fun o ω => nu j o ω - vp j o ω) ω
          - unionMeat (c j) (dims j) (xt j) (nu j) ω) / lam j ω) atTop (fun _ => 0) := by
  have hD1 : ∀ j, (1 : ℝ) ≤ ((maxDegree (c j) (dims j) : ℕ) : ℝ) := fun j => by
    exact_mod_cast one_le_maxDegree (c j) (dims j)
  refine perturb_tendstoInProb 𝒟 hm c dims xt nu vp hB hxt hlamM hlam0
    (a := a) (b := b) (fun j => ?_) (fun j => ?_) hnumeas hvpmeas hnuint hvpint hmajint hnu hvp
    (rate_tendstoInProb_of_accum c dims hlam0 hCsq.le hK0 (fun j => (hn j).le) hdd
      hadef hbdef hsharing hacc)
  · rw [hadef j]
    exact mul_pos hCsq (hn j)
  · rw [hbdef j]
    exact mul_pos (mul_pos hCsq (by linarith [hdd j])) (by linarith [hD1 j])

end PerturbSequence

/-! ## Witnesses for the sequence theorems

The witness design grows with `j`: `O j = Fin (j+1)` observations, one maintained dimension, and
each observation in its own cluster, so the sharing graph is the diagonal and `D_j = 1`. The
witness for `perturb_tendstoInProb` takes `ν ≡ 1` and `ϖ ≡ 1`, so `𝓜̃_n ≠ 0`. -/

section SeqWitness

open Sharing

/-- The `j`-th design of the sequence witness: `j+1` observations, one maintained dimension,
each observation its own cluster. -/
def seqC (j : ℕ) : Fin 1 → Fin (j + 1) → Fin (j + 1) := fun _ o => o

def seqDims (_j : ℕ) : Finset (Fin 1) := Finset.univ

theorem seqLinked_iff (j : ℕ) (o o' : Fin (j + 1)) :
    Linked (seqC j) (seqDims j) o o' ↔ o = o' := by
  constructor
  · rintro ⟨d, -, h⟩; exact h
  · intro h; exact ⟨0, Finset.mem_univ _, h⟩

/-- The witness graph has no open edges, so `D_j = max{1,0} = 1`. -/
theorem seq_maxDegree (j : ℕ) : maxDegree (seqC j) (seqDims j) = 1 := by
  have h0 : (Finset.univ.sup fun o : Fin (j + 1) =>
      (openNbhd (seqC j) (seqDims j) o).card) = 0 := by
    refine (Finset.sup_eq_bot_iff _ _).mpr ?_
    intro o _
    show (openNbhd (seqC j) (seqDims j) o).card = 0
    rw [Finset.card_eq_zero]
    ext o'
    simp only [mem_openNbhd, Finset.notMem_empty, iff_false, not_and]
    intro hne hlink
    exact hne ((seqLinked_iff j o o').mp hlink).symm
  rw [maxDegree, h0]
  rfl

private theorem seq_meat_zero (j : ℕ) (ω : Unit) :
    unionMeat (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
      - scoreVar (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
        (fun _ _ _ => (0 : ℝ)) ω = 0 := by
  ext k l
  simp [unionMeat, scoreVar]

/-- The hypotheses of `infeasibleMeat_tendstoInProb` are satisfiable, on the growing design
with `λ_j = j+1`, so that `δ_j = 1/(j+1) → 0`. -/
theorem infeasibleMeat_tendstoInProb_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (j : ℕ) (ω : Unit) =>
        rectFrobNorm (unionMeat (seqC j) (seqDims j)
            (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
          - scoreVar (seqC j) (seqDims j)
            (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
            (fun _ _ _ => (0 : ℝ)) ω) / ((j : ℝ) + 1))
      atTop (fun _ => 0) := by
  have hF : ∀ (j : ℕ) (ω : Unit),
      rectFrobNorm (unionMeat (seqC j) (seqDims j)
          (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
        - scoreVar (seqC j) (seqDims j)
          (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
          (fun _ _ _ => (0 : ℝ)) ω) = 0 := by
    intro j ω
    rw [seq_meat_zero j ω]
    simp [rectFrobNorm, rectFrobSq]
  have hcs : ∀ (j : ℕ) (k l : Fin 1) (p q : Fin (j + 1) × Fin (j + 1)),
      (fun ω : Unit => centeredSummand (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
          (fun _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) k l p ω
        * centeredSummand (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
          (fun _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) k l q ω) = (0 : Unit → ℝ) := by
    intro j k l p q
    funext ω
    simp [centeredSummand]
  refine infeasibleMeat_tendstoInProb (⊥ : MeasurableSpace Unit) (P := Measure.dirac ())
    bot_le (O := fun j => Fin (j + 1)) (D := fun _ => Fin 1) (L := fun j => Fin (j + 1))
    (κ := fun _ => Fin 1) seqC seqDims
    (fun _ => fun _ _ _ => (1 : ℝ)) (fun _ => fun _ _ => (0 : ℝ))
    (fun _ => fun _ _ _ => (0 : ℝ)) (B := 1) (Cm := 1) zero_le_one
    (lam := fun j _ => ((j : ℝ) + 1)) (fun _ => measurable_const)
    (fun j _ => by positivity) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    have he : (fun ω : Unit => rectFrobNorm (unionMeat (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
      - scoreVar (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
        (fun _ _ _ => (0 : ℝ)) ω)) = fun _ => (0 : ℝ) := funext (hF j)
    rw [he]
    exact measurable_const
  · intro j
    have he : (fun ω : Unit => frobSq (unionMeat (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
      - scoreVar (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
        (fun _ _ _ => (0 : ℝ)) ω)) = fun _ => (0 : ℝ) := by
      funext ω
      rw [seq_meat_zero j ω]
      simp [frobSq]
    rw [he]
    exact integrable_zero _ _ _
  · intro j
    have he : (fun ω : Unit => (rectFrobNorm (unionMeat (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
      - scoreVar (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
        (fun _ _ _ => (0 : ℝ)) ω) / ((j : ℝ) + 1)) ^ 2) = fun _ => (0 : ℝ) := by
      funext ω
      rw [hF j ω]
      simp
    rw [he]
    exact integrable_zero _ _ _
  · intro j k l p _ q _
    rw [hcs j k l p q]
    exact integrable_zero _ _ _
  · intro j k l p _ q _ _
    rw [hcs j k l p q, condExp_zero]
  · intro j k l p q
    rw [hcs j k l p q, condExp_zero]
    filter_upwards with ω
    norm_num
  · have hfun : (fun (j : ℕ) (_ : Unit) => 64 * (Fintype.card (Fin 1) : ℝ) ^ 2 * (1 : ℝ) ^ 4 * 1
        * deltaSeq (Fintype.card (Fin (j + 1)) : ℝ) (maxDegree (seqC j) (seqDims j) : ℝ)
          ((j : ℝ) + 1)) = fun (j : ℕ) (_ : Unit) => 64 * (1 / ((j : ℝ) + 1)) := by
      funext j ω
      rw [seq_maxDegree j, deltaSeq]
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      field_simp
    rw [hfun]
    refine tendstoInMeasure_zero_of_tendsto_const ?_
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (64 : ℝ)

private theorem seq_l2Norm_one (j : ℕ) :
    l2Norm (fun _ : Fin (j + 1) => (1 : ℝ)) ^ 2 = (j : ℝ) + 1 := by
  rw [sq_l2Norm]
  simp

/-- The hypotheses of `perturb_tendstoInProb` are satisfiable, on the growing design with
`ν ≡ 1`, `ϖ ≡ 1` and `λ_j = (j+1)²`; here `𝓜̃_n ≠ 0`. -/
theorem perturb_tendstoInProb_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (j : ℕ) (ω : Unit) =>
        rectFrobNorm (unionMeat (seqC j) (seqDims j)
            (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
            (fun (_o : Fin (j + 1)) (_ω : Unit) => (1 : ℝ) - (1 : ℝ)) ω
          - unionMeat (seqC j) (seqDims j)
            (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
            (fun _ _ => (1 : ℝ)) ω) / (((j : ℝ) + 1) ^ 2)) atTop (fun _ => 0) := by
  refine perturb_tendstoInProb (⊥ : MeasurableSpace Unit) (P := Measure.dirac ())
    bot_le (O := fun j => Fin (j + 1)) (D := fun _ => Fin 1) (L := fun j => Fin (j + 1))
    (κ := fun _ => Fin 1) seqC seqDims
    (fun _ => fun _ _ _ => (1 : ℝ)) (fun _ => fun _ _ => (1 : ℝ))
    (fun _ => fun _ _ => (1 : ℝ)) (B := 1) zero_le_one (fun j o ω => by simp)
    (lam := fun j _ => (((j : ℝ) + 1) ^ 2)) (fun _ => measurable_const)
    (fun j _ => by positivity) (a := fun j => (j : ℝ) + 1) (b := fun j => (j : ℝ) + 1)
    (fun j => by positivity) (fun j => by positivity)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    (fun j => integrable_const _) (fun j => integrable_const _)
    (fun j => integrable_const _) (fun j => ?_) (fun j => ?_) ?_
  · rw [condExp_const bot_le]
    filter_upwards with ω
    exact le_of_eq (seq_l2Norm_one j)
  · rw [condExp_const bot_le]
    filter_upwards with ω
    exact le_of_eq (seq_l2Norm_one j)
  · have hfun : (fun (j : ℕ) (_ : Unit) =>
        (1 : ℝ) ^ 2 * ((maxDegree (seqC j) (seqDims j) : ℝ) + 1) / (((j : ℝ) + 1) ^ 2)
          * (2 * Real.sqrt (((j : ℝ) + 1) * ((j : ℝ) + 1)) + ((j : ℝ) + 1)))
        = fun (j : ℕ) (_ : Unit) => 6 * (1 / ((j : ℝ) + 1)) := by
      funext j ω
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      rw [seq_maxDegree j, Real.sqrt_mul_self (by positivity)]
      push_cast
      field_simp
      ring
    rw [hfun]
    refine tendstoInMeasure_zero_of_tendsto_const ?_
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (6 : ℝ)

private theorem seq_l2Norm_inv (j : ℕ) :
    l2Norm (fun _ : Fin (j + 1) => (((j : ℝ) + 1)⁻¹)) ^ 2 = ((j : ℝ) + 1)⁻¹ := by
  have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
  rw [sq_l2Norm]
  simp
  field_simp

/-- The hypotheses of `perturb_tendstoInProb_of_accum` are jointly satisfiable, on the growing
design with `ν ≡ 1`, `ϖ ≡ (j+1)^{-1}`, `C^{1/2} = B = 1`, `K = 0`, `d_{[Δ]} = 1` and
`λ_j = j+1`, giving `δ_j = (j+1)^{-1} → 0`. Here `ν̂_FE = ν - ϖ` differs from both `0` and `ν`,
and `hnu` holds with equality. -/
theorem perturb_tendstoInProb_of_accum_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (j : ℕ) (ω : Unit) =>
        rectFrobNorm (unionMeat (seqC j) (seqDims j)
            (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
            (fun (_o : Fin (j + 1)) (_ω : Unit) => (1 : ℝ) - ((j : ℝ) + 1)⁻¹) ω
          - unionMeat (seqC j) (seqDims j)
            (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
            (fun _ _ => (1 : ℝ)) ω) / ((j : ℝ) + 1)) atTop (fun _ => 0) := by
  refine perturb_tendstoInProb_of_accum (⊥ : MeasurableSpace Unit) (P := Measure.dirac ())
    bot_le (O := fun j => Fin (j + 1)) (D := fun _ => Fin 1) (L := fun j => Fin (j + 1))
    (κ := fun _ => Fin 1) seqC seqDims
    (fun _ => fun _ _ _ => (1 : ℝ)) (fun _ => fun _ _ => (1 : ℝ))
    (fun j => fun _ _ => ((j : ℝ) + 1)⁻¹) (B := 1) zero_le_one (fun j o ω => by simp)
    (lam := fun j _ => ((j : ℝ) + 1)) (fun _ => measurable_const)
    (fun j _ => by positivity) (Csq := 1) (Kr := 0) one_pos le_rfl
    (nR := fun j => (j : ℝ) + 1) (dd := fun _ => 1) (fun j => by positivity) (fun _ => le_rfl)
    (a := fun j => (j : ℝ) + 1) (b := fun _ => 2) (fun j => by ring) (fun j => ?_)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    (fun j => integrable_const _) (fun j => integrable_const _)
    (fun j => integrable_const _) (fun j => ?_) (fun j => ?_) (fun j ω => ?_) ?_
  · rw [seq_maxDegree j]
    norm_num
  · rw [condExp_const bot_le]
    filter_upwards with ω
    exact le_of_eq (seq_l2Norm_one j)
  · rw [condExp_const bot_le]
    filter_upwards with ω
    rw [seq_l2Norm_inv j]
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  · have hm : ((maxDegree (seqC j) (seqDims j) : ℕ) : ℝ) = 1 := by
      rw [seq_maxDegree j]
      norm_num
    have hd : deltaSeq ((j : ℝ) + 1) ((maxDegree (seqC j) (seqDims j) : ℝ)) ((j : ℝ) + 1)
        = ((j : ℝ) + 1)⁻¹ := by
      rw [deltaSeq, hm]
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    have hinv : (0 : ℝ) ≤ ((j : ℝ) + 1)⁻¹ := by positivity
    rw [hd, hm]
    norm_num
    linarith
  · have hfun : (fun (j : ℕ) (_ : Unit) =>
        deltaSeq ((j : ℝ) + 1) ((maxDegree (seqC j) (seqDims j) : ℝ)) ((j : ℝ) + 1) * 1)
        = fun (j : ℕ) (_ : Unit) => 1 / ((j : ℝ) + 1) := by
      funext j ω
      have hm : ((maxDegree (seqC j) (seqDims j) : ℕ) : ℝ) = 1 := by
        rw [seq_maxDegree j]
        norm_num
      rw [deltaSeq, hm]
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hfun]
    refine tendstoInMeasure_zero_of_tendsto_const ?_
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

end SeqWitness

/-! ## Regime 3: centering and the four-fold covariance

Under the dependence assumption (Regime 3) and exogeneity, this section proves the centering
`E[𝓜̃_n ∣ 𝒟] = Ω_n` of Lemma SM.B.11(a) and the hypotheses `hzero`, `hbd`, `hint` of
Lemma SM.B.13. The four-fold vanishing concerns conditional independence of the two blocks
`{o₁,o₂}` and `{o₃,o₄}`, read off the separation `(o₁,o₂,o₃,o₄) ∉ 𝓛_n`; `hdims` (`J ≥ 1`)
makes the sharing relation reflexive, so the blocks are disjoint.

## Main results

* `condExp_unionMeat_eq_scoreVar`: the centering `E[𝓜̃_n ∣ 𝒟] = Ω_n`.
* `condExp_centeredSummand_mul_eq_zero`: vanishing of the covariance off `𝓛_n`.
* `abs_condExp_centeredSummand_mul_le`: the per-quadruple bound `|Cov| ≤ 2B⁴C`.
* `integrable_centeredSummand_mul`: integrability of products of centered summands.
* `infeasibleMeat_condVar_le_of_regime3`: all four combined into the first claim. -/

section CondOmegaKernel

variable {O Ω : Type*}

/-- The conditional covariance kernel `Ω_{oo'} := E[ν_oν_{o'} ∣ 𝒟]`, in the shape `scoreVar`
consumes; `scoreVar c dims xt (condOmegaKernel 𝒟 P nu)` is `Ω_n = X̃'ΩX̃` restricted to the
sharing graph. -/
noncomputable def condOmegaKernel (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (nu : O → Ω → ℝ) : O → O → Ω → ℝ :=
  fun o o' => P[nu o * nu o' | 𝒟]

end CondOmegaKernel

/-! ### Consequences of the moment assumption -/

section Moments

open MeasureTheory
open scoped ENNReal

variable {O Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `4⁻¹ + 4⁻¹ = 2⁻¹` in `ℝ≥0∞`: the Hölder triple `MemLp.mul` needs to send `ν ∈ L⁴` to
`ν_oν_{o'} ∈ L²`. -/
instance holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
    ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩

/-- Under the moment assumption every product of two disturbances is in `L²`; this supplies the
`hprod` hypothesis below. -/
theorem memLp_two_mul_of_memLp_four {nu : O → Ω → ℝ} (hL4 : ∀ o, MemLp (nu o) 4 P) (o o' : O) :
    MemLp (nu o * nu o') 2 P :=
  (hL4 o).mul (hL4 o')

end Moments

/-! ### The conditional covariance of two products

The identity `E[(U - E[U ∣ 𝒟])(V - E[V ∣ 𝒟]) ∣ 𝒟] = E[UV ∣ 𝒟] - E[U ∣ 𝒟]E[V ∣ 𝒟]`, which
needs no independence, and its vanishing under conditional independence. -/

section Generic

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {h𝒟 : 𝒟 ≤ mΩ}
variable {P : Measure Ω} [IsFiniteMeasure P]

omit [StandardBorelSpace Ω] [IsFiniteMeasure P] in
/-- The centered product of two `L²` variables is integrable. -/
theorem integrable_centered_mul {U V : Ω → ℝ} (hUm : MemLp U 2 P) (hVm : MemLp V 2 P) :
    Integrable ((U - P[U | 𝒟]) * (V - P[V | 𝒟])) P := by
  have ham : MemLp (P[U | 𝒟]) 2 P := MemLp.condExp (m := 𝒟) one_le_two hUm
  have hbm : MemLp (P[V | 𝒟]) 2 P := MemLp.condExp (m := 𝒟) one_le_two hVm
  exact (hUm.sub ham).integrable_mul (hVm.sub hbm)

omit [StandardBorelSpace Ω] in
include h𝒟 in
/-- `Cov(U,V ∣ 𝒟) = E[UV ∣ 𝒟] - E[U ∣ 𝒟]E[V ∣ 𝒟]`, by pulling the `𝒟`-measurable conditional
means out of the cross terms. -/
theorem condExp_centered_mul_eq {U V : Ω → ℝ} (hUm : MemLp U 2 P) (hVm : MemLp V 2 P) :
    P[(U - P[U | 𝒟]) * (V - P[V | 𝒟]) | 𝒟] =ᵐ[P] P[U * V | 𝒟] - P[U | 𝒟] * P[V | 𝒟] := by
  have ham : MemLp (P[U | 𝒟]) 2 P := MemLp.condExp (m := 𝒟) one_le_two hUm
  have hbm : MemLp (P[V | 𝒟]) 2 P := MemLp.condExp (m := 𝒟) one_le_two hVm
  have hUi : Integrable U P := hUm.integrable one_le_two
  have hVi : Integrable V P := hVm.integrable one_le_two
  have hUV : Integrable (U * V) P := hUm.integrable_mul hVm
  have hbU : Integrable (P[V | 𝒟] * U) P := hbm.integrable_mul hUm
  have haV : Integrable (P[U | 𝒟] * V) P := ham.integrable_mul hVm
  have hab : Integrable (P[U | 𝒟] * P[V | 𝒟]) P := ham.integrable_mul hbm
  have e2 : P[P[V | 𝒟] * U | 𝒟] =ᵐ[P] P[V | 𝒟] * P[U | 𝒟] :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp hbU hUi
  have e3 : P[P[U | 𝒟] * V | 𝒟] =ᵐ[P] P[U | 𝒟] * P[V | 𝒟] :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp haV hVi
  have e4 : P[P[U | 𝒟] * P[V | 𝒟] | 𝒟] = P[U | 𝒟] * P[V | 𝒟] :=
    condExp_of_stronglyMeasurable h𝒟
      (stronglyMeasurable_condExp.mul stronglyMeasurable_condExp) hab
  have hZeq : (U - P[U | 𝒟]) * (V - P[V | 𝒟])
      = U * V - P[V | 𝒟] * U - P[U | 𝒟] * V + P[U | 𝒟] * P[V | 𝒟] := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hZeq]
  have k1 : P[U * V - P[V | 𝒟] * U - P[U | 𝒟] * V + P[U | 𝒟] * P[V | 𝒟] | 𝒟]
      =ᵐ[P] P[U * V - P[V | 𝒟] * U - P[U | 𝒟] * V | 𝒟] + P[P[U | 𝒟] * P[V | 𝒟] | 𝒟] :=
    condExp_add ((hUV.sub hbU).sub haV) hab 𝒟
  have k2 : P[U * V - P[V | 𝒟] * U - P[U | 𝒟] * V | 𝒟]
      =ᵐ[P] P[U * V - P[V | 𝒟] * U | 𝒟] - P[P[U | 𝒟] * V | 𝒟] :=
    condExp_sub (hUV.sub hbU) haV 𝒟
  have k3 : P[U * V - P[V | 𝒟] * U | 𝒟] =ᵐ[P] P[U * V | 𝒟] - P[P[V | 𝒟] * U | 𝒟] :=
    condExp_sub hUV hbU 𝒟
  filter_upwards [k1, k2, k3, e2, e3] with ω m1 m2 m3 f2 f3
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at m1 m2 m3 f2 f3 ⊢
  rw [m1, m2, m3, f2, f3, e4]
  simp only [Pi.mul_apply]
  ring

/-- `Cov(U,V ∣ 𝒟) = 0` for conditionally independent `U` and `V`, by the conditional product
rule of `Multiway.Sharing`. -/
theorem condExp_centered_mul_eq_zero {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V)
    (hUm : MemLp U 2 P) (hVm : MemLp V 2 P) (hind : CondIndepFun 𝒟 h𝒟 U V P) :
    P[(U - P[U | 𝒟]) * (V - P[V | 𝒟]) | 𝒟] =ᵐ[P] 0 := by
  filter_upwards [condExp_centered_mul_eq (h𝒟 := h𝒟) hUm hVm,
    Sharing.condExp_mul_of_condIndepFun hU hV (hUm.integrable one_le_two)
      (hVm.integrable one_le_two) (hUm.integrable_mul hVm) hind] with ω h1 h2
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply] at h1 h2 ⊢
  rw [h1, h2]
  ring

end Generic

/-! ### The centering `E[𝓜̃_n ∣ 𝒟] = Ω_n` -/

section Centering

open MeasureTheory ProbabilityTheory MeasurableSpace Sharing

variable {O D L κ : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable [Fintype κ] [DecidableEq κ]
variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {h𝒟 : 𝒟 ≤ mΩ}
variable {P : Measure Ω} [IsFiniteMeasure P]
variable {c : D → O → L} {dims : Finset D} {nu : O → Ω → ℝ}

omit [DecidableEq D] [Fintype κ] [DecidableEq κ] in
/-- **Lemma SM.B.11(a).** `E[𝓜̃_n ∣ 𝒟] = Ω_n` entrywise, under the dependence assumption
(Regime 3, `hreg`), exogeneity (`hexog`), bounded regressors (`hB`) and `J ≥ 1` (`hdims`).
Off the sharing graph `Ω_{oo'} = 0` by `Multiway.Sharing.condCov_eq_zero_of_not_linked`, and
the finitely many null sets are intersected in `hzae`. -/
theorem condExp_unionMeat_eq_scoreVar (hdims : dims.Nonempty)
    (hreg : Regime3 𝒟 h𝒟 c dims nu P) (hmeas : ∀ o, Measurable (nu o))
    (hL2 : ∀ o, MemLp (nu o) 2 P) (hexog : ∀ o, P[nu o | 𝒟] =ᵐ[P] 0)
    {xt : O → κ → Ω → ℝ} {B : ℝ}
    (hxt : ∀ o k, StronglyMeasurable[𝒟] (xt o k)) (hB : ∀ o k ω, |xt o k ω| ≤ B) (k l : κ) :
    P[fun ω => unionMeat c dims xt nu ω k l | 𝒟]
      =ᵐ[P] fun ω => scoreVar c dims xt (condOmegaKernel 𝒟 P nu) ω k l := by
  classical
  have hz : ∀ o o', ¬ Linked c dims o o' → P[nu o * nu o' | 𝒟] =ᵐ[P] 0 :=
    fun o o' hsep => condCov_eq_zero_of_not_linked hdims hreg hmeas hL2 hexog hsep
  have hint : ∀ o o', Integrable (nu o * nu o') P :=
    fun o o' => (hL2 o).integrable_mul (hL2 o')
  have hmain := condExp_meat_eq_scoreVar (𝒟 := 𝒟) (c := c) (dims := dims) h𝒟 hxt hB hint hz k l
  have hzae : ∀ᵐ ω ∂P, ∀ o o' : O, ¬ Linked c dims o o' → (P[nu o * nu o' | 𝒟]) ω = 0 := by
    rw [ae_all_iff]; intro o; rw [ae_all_iff]; intro o'
    by_cases h : Linked c dims o o'
    · exact Filter.Eventually.of_forall fun ω hcon => absurd h hcon
    · filter_upwards [hz o o' h] with ω hω _; exact hω
  have hfun : (fun ω => unionMeat c dims xt nu ω k l)
      = fun ω => ∑ p ∈ linkedPairs c dims,
          xt p.1 k ω * xt p.2 l ω * (nu p.1 ω * nu p.2 ω) := by
    funext ω; rw [unionMeat]; rfl
  rw [hfun]
  filter_upwards [hmain, hzae] with ω h1 h2
  rw [h1]
  show _ = ∑ p ∈ linkedPairs c dims, xt p.1 k ω * xt p.2 l ω * (P[nu p.1 * nu p.2 | 𝒟]) ω
  exact sum_eq_sum_over_linkedPairs c dims (fun o o' => (P[nu o * nu o' | 𝒟]) ω)
    (fun o o' => xt o k ω * xt o' l ω) (fun o o' h => h2 o o' h)

end Centering

/-! ### The four-fold covariance off `𝓛_n` -/

section FourFold

open MeasureTheory ProbabilityTheory MeasurableSpace Sharing

variable {O D L κ : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable [Fintype κ] [DecidableEq κ]
variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {h𝒟 : 𝒟 ≤ mΩ}
variable {P : Measure Ω} [IsFiniteMeasure P]
variable {c : D → O → L} {dims : Finset D} {nu : O → Ω → ℝ}

omit [DecidableEq O] [DecidableEq D] [Fintype κ] [DecidableEq κ] [StandardBorelSpace Ω]
  [IsFiniteMeasure P] in
/-- On a pair of linked pairs, `(o₁,o₂,o₃,o₄) ∉ 𝓛_n` means all four cross-links fail. -/
theorem not_linked_of_not_mem_linkedQuads {p q : O × O}
    (hp : p ∈ linkedPairs c dims) (hq : q ∈ linkedPairs c dims)
    (hnm : (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims) :
    ¬ Linked c dims p.1 q.1 ∧ ¬ Linked c dims p.1 q.2 ∧
      ¬ Linked c dims p.2 q.1 ∧ ¬ Linked c dims p.2 q.2 := by
  classical
  have hpl : Linked c dims p.1 p.2 := (Finset.mem_filter.1 hp).2
  have hql : Linked c dims q.1 q.2 := (Finset.mem_filter.1 hq).2
  by_contra hcon
  refine hnm (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpl, hql, ?_⟩)
  by_cases h1 : Linked c dims p.1 q.1
  · exact Or.inl h1
  by_cases h2 : Linked c dims p.1 q.2
  · exact Or.inr (Or.inl h2)
  by_cases h3 : Linked c dims p.2 q.1
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : Linked c dims p.2 q.2
  · exact Or.inr (Or.inr (Or.inr h4))
  exact absurd ⟨h1, h2, h3, h4⟩ hcon

omit [DecidableEq D] [Fintype κ] [DecidableEq κ] in
/-- Regime 3 at the blocks `{o₁,o₂}` and `{o₃,o₄}`: off `𝓛_n` the products `ξ_{o₁o₂}` and
`ξ_{o₃o₄}` are conditionally independent given `𝒟`. Disjointness of the blocks follows from the
separation and reflexivity of `∼`, which holds when `dims.Nonempty`. -/
theorem condIndepFun_prod_of_not_mem_linkedQuads (hdims : dims.Nonempty)
    (hreg : Regime3 𝒟 h𝒟 c dims nu P) {p q : O × O}
    (hp : p ∈ linkedPairs c dims) (hq : q ∈ linkedPairs c dims)
    (hnm : (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims) :
    CondIndepFun 𝒟 h𝒟 (nu p.1 * nu p.2) (nu q.1 * nu q.2) P := by
  classical
  obtain ⟨h11, h12, h21, h22⟩ := not_linked_of_not_mem_linkedQuads hp hq hnm
  have hsep : ∀ o ∈ ({p.1, p.2} : Finset O), ∀ o' ∈ ({q.1, q.2} : Finset O),
      ¬ Linked c dims o o' := by
    intro o ho o' ho'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ho ho'
    rcases ho with rfl | rfl <;> rcases ho' with rfl | rfl
    exacts [h11, h12, h21, h22]
  have hrefl : ∀ o : O, Linked c dims o o := fun o => ⟨hdims.choose, hdims.choose_spec, rfl⟩
  have hdisj : Disjoint ({p.1, p.2} : Finset O) ({q.1, q.2} : Finset O) := by
    rw [Finset.disjoint_left]
    intro o ho ho'
    exact hsep o ho o ho' (hrefl o)
  have hci := hreg {p.1, p.2} {q.1, q.2} hdisj hsep
  have hle : ∀ (S : Finset O) (r s : O), r ∈ S → s ∈ S →
      MeasurableSpace.comap (nu r * nu s) inferInstance
        ≤ ⨆ o ∈ (S : Set O), MeasurableSpace.comap (nu o) inferInstance := by
    intro S r s hr hs
    have hmem : ∀ t ∈ S, Measurable[⨆ o ∈ (S : Set O),
        MeasurableSpace.comap (nu o) inferInstance] (nu t) := by
      intro t ht
      refine (comap_measurable (nu t)).mono ?_ le_rfl
      exact le_iSup₂ (f := fun (o : O) (_ : o ∈ (S : Set O)) =>
        MeasurableSpace.comap (nu o) inferInstance) t (by simpa using ht)
    exact ((hmem r hr).mul (hmem s hs)).comap_le
  refine (condIndepFun_iff_condIndep 𝒟 h𝒟 (nu p.1 * nu p.2) (nu q.1 * nu q.2) P).2
    (condIndep_of_condIndep_of_le_left (condIndep_of_condIndep_of_le_right hci ?_) ?_)
  · exact hle {q.1, q.2} q.1 q.2 (by simp) (by simp)
  · exact hle {p.1, p.2} p.1 p.2 (by simp) (by simp)

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype κ] [DecidableEq κ]
  [StandardBorelSpace Ω] [IsFiniteMeasure P] in
/-- `|x̃_{o₁k}x̃_{o₂l}x̃_{o₃k}x̃_{o₄l}| ≤ B⁴` under the bound `|x̃_{ok}| ≤ B`. -/
theorem norm_weight_le {xt : O → κ → Ω → ℝ} {B : ℝ} (hB : ∀ o k ω, |xt o k ω| ≤ B)
    (k l : κ) (p q : O × O) (ω : Ω) :
    ‖(xt p.1 k * xt p.2 l * (xt q.1 k * xt q.2 l)) ω‖ ≤ B ^ 4 := by
  simp only [Pi.mul_apply]
  have h0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hB p.1 k ω)
  calc ‖xt p.1 k ω * xt p.2 l ω * (xt q.1 k ω * xt q.2 l ω)‖
      = |xt p.1 k ω| * |xt p.2 l ω| * (|xt q.1 k ω| * |xt q.2 l ω|) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    _ ≤ B * B * (B * B) :=
        mul_le_mul (mul_le_mul (hB _ _ _) (hB _ _ _) (abs_nonneg _) h0)
          (mul_le_mul (hB _ _ _) (hB _ _ _) (abs_nonneg _) h0)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg h0 h0)
    _ = B ^ 4 := by ring

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype κ] [DecidableEq κ]
  [StandardBorelSpace Ω] [IsFiniteMeasure P] in
/-- `ξ̄_{o₁o₂}ξ̄_{o₃o₄} = (x̃_{o₁k}x̃_{o₂l}x̃_{o₃k}x̃_{o₄l})(ν_{o₁}ν_{o₂} - Ω_{o₁o₂})(ν_{o₃}ν_{o₄} -
Ω_{o₃o₄})`, with the `𝒟`-measurable weight as a single factor. -/
theorem centeredSummand_mul_eq (xt : O → κ → Ω → ℝ) (k l : κ) (p q : O × O) :
    (fun ω => centeredSummand xt nu (condOmegaKernel 𝒟 P nu) k l p ω
        * centeredSummand xt nu (condOmegaKernel 𝒟 P nu) k l q ω)
      = (xt p.1 k * xt p.2 l * (xt q.1 k * xt q.2 l))
        * ((nu p.1 * nu p.2 - P[nu p.1 * nu p.2 | 𝒟])
            * (nu q.1 * nu q.2 - P[nu q.1 * nu q.2 | 𝒟])) := by
  funext ω
  simp only [centeredSummand, condOmegaKernel, Pi.mul_apply, Pi.sub_apply]
  ring

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype κ] [DecidableEq κ]
  [StandardBorelSpace Ω] [IsFiniteMeasure P] in
include h𝒟 in
/-- The product of two centered summands is integrable, from `ν_oν_{o'} ∈ L²` and the
boundedness of `x̃`. -/
theorem integrable_centeredSummand_mul {xt : O → κ → Ω → ℝ} {B : ℝ}
    (hxt : ∀ o k, StronglyMeasurable[𝒟] (xt o k)) (hB : ∀ o k ω, |xt o k ω| ≤ B)
    (hprod : ∀ o o', MemLp (nu o * nu o') 2 P) (k l : κ) (p q : O × O) :
    Integrable (fun ω => centeredSummand xt nu (condOmegaKernel 𝒟 P nu) k l p ω
      * centeredSummand xt nu (condOmegaKernel 𝒟 P nu) k l q ω) P := by
  rw [centeredSummand_mul_eq (𝒟 := 𝒟) (P := P) xt k l p q]
  exact (integrable_centered_mul (𝒟 := 𝒟) (hprod p.1 p.2) (hprod q.1 q.2)).bdd_mul
    ((((hxt p.1 k).mul (hxt p.2 l)).mul
      ((hxt q.1 k).mul (hxt q.2 l))).mono h𝒟).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => norm_weight_le hB k l p q ω)

omit [DecidableEq D] [Fintype κ] [DecidableEq κ] in
/-- The conditional covariance of two centered summands vanishes off `𝓛_n`: the separation
gives conditional independence of the two blocks under Regime 3, and the `𝒟`-measurable
weight comes out by pull-out. -/
theorem condExp_centeredSummand_mul_eq_zero (hdims : dims.Nonempty)
    (hreg : Regime3 𝒟 h𝒟 c dims nu P) (hmeas : ∀ o, Measurable (nu o))
    (hprod : ∀ o o', MemLp (nu o * nu o') 2 P) {xt : O → κ → Ω → ℝ} {B : ℝ}
    (hxt : ∀ o k, StronglyMeasurable[𝒟] (xt o k)) (hB : ∀ o k ω, |xt o k ω| ≤ B)
    (k l : κ) {p q : O × O} (hp : p ∈ linkedPairs c dims) (hq : q ∈ linkedPairs c dims)
    (hnm : (p.1, p.2, q.1, q.2) ∉ linkedQuads c dims) :
    P[fun ω => centeredSummand xt nu (condOmegaKernel 𝒟 P nu) k l p ω
        * centeredSummand xt nu (condOmegaKernel 𝒟 P nu) k l q ω | 𝒟] =ᵐ[P] 0 := by
  have hZ0 := condExp_centered_mul_eq_zero ((hmeas p.1).mul (hmeas p.2))
    ((hmeas q.1).mul (hmeas q.2)) (hprod p.1 p.2) (hprod q.1 q.2)
    (condIndepFun_prod_of_not_mem_linkedQuads hdims hreg hp hq hnm)
  have hZi := integrable_centered_mul (𝒟 := 𝒟) (hprod p.1 p.2) (hprod q.1 q.2)
  have hWZ := integrable_centeredSummand_mul (h𝒟 := h𝒟) hxt hB hprod k l p q
  rw [centeredSummand_mul_eq (𝒟 := 𝒟) (P := P) xt k l p q] at hWZ ⊢
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (((hxt p.1 k).mul (hxt p.2 l)).mul ((hxt q.1 k).mul (hxt q.2 l))) hWZ hZi
  filter_upwards [hpull, hZ0] with ω g1 g2
  simp only [Pi.mul_apply, Pi.zero_apply] at g1 g2 ⊢
  rw [g1, g2]
  ring

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype κ] [DecidableEq κ]
  [StandardBorelSpace Ω] in
include h𝒟 in
/-- The conditional covariance bound `|Cov(ξ_{o₁o₂},ξ_{o₃o₄} ∣ 𝒟)| ≤ 2B⁴C`. By
`condExp_centered_mul_eq` the covariance is `E[ν_{o₁}ν_{o₂}ν_{o₃}ν_{o₄} ∣ 𝒟] - Ω_{o₁o₂}Ω_{o₃o₄}`;
the first term is bounded by `abs_condExp_prod_four_le` and the second by `hOmbd` twice. -/
theorem abs_condExp_centeredSummand_mul_le {xt : O → κ → Ω → ℝ} {B Cm Csq : ℝ}
    (hxt : ∀ o k, StronglyMeasurable[𝒟] (xt o k)) (hB : ∀ o k ω, |xt o k ω| ≤ B)
    (hprod : ∀ o o', MemLp (nu o * nu o') 2 P)
    (hmom : ∀ o, ∀ᵐ ω ∂P, (P[fun ω => nu o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hOmbd : ∀ o o', ∀ᵐ ω ∂P, |(P[nu o * nu o' | 𝒟]) ω| ≤ Csq) (hCsq : Csq ^ 2 ≤ Cm)
    (k l : κ) (p q : O × O) :
    ∀ᵐ ω ∂P, |(P[fun ω => centeredSummand xt nu (condOmegaKernel 𝒟 P nu) k l p ω
        * centeredSummand xt nu (condOmegaKernel 𝒟 P nu) k l q ω | 𝒟]) ω| ≤ 2 * B ^ 4 * Cm := by
  have hpow : ∀ o : O, Integrable (fun ω => nu o ω ^ 4) P := by
    intro o
    refine ((hprod o o).integrable_mul (hprod o o)).congr ?_
    filter_upwards with ω
    simp only [Pi.mul_apply]
    ring
  have hfour : Integrable (fun ω => nu p.1 ω * nu p.2 ω * (nu q.1 ω * nu q.2 ω)) P :=
    (hprod p.1 p.2).integrable_mul (hprod q.1 q.2)
  have habs := abs_condExp_prod_four_le 𝒟 hfour (hpow p.1) (hpow p.2) (hpow q.1) (hpow q.2)
    (hmom p.1) (hmom p.2) (hmom q.1) (hmom q.2)
  have hid := condExp_centered_mul_eq (h𝒟 := h𝒟) (hprod p.1 p.2) (hprod q.1 q.2)
  have hZi := integrable_centered_mul (𝒟 := 𝒟) (hprod p.1 p.2) (hprod q.1 q.2)
  have hWZ := integrable_centeredSummand_mul (h𝒟 := h𝒟) hxt hB hprod k l p q
  rw [centeredSummand_mul_eq (𝒟 := 𝒟) (P := P) xt k l p q] at hWZ ⊢
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (((hxt p.1 k).mul (hxt p.2 l)).mul ((hxt q.1 k).mul (hxt q.2 l))) hWZ hZi
  have hCm : (0 : ℝ) ≤ Cm := le_trans (sq_nonneg Csq) hCsq
  filter_upwards [hpull, hid, habs, hOmbd p.1 p.2, hOmbd q.1 q.2] with ω g1 g2 g3 g4 g5
  simp only [Pi.mul_apply, Pi.sub_apply] at g1 g2 ⊢
  rw [g1, g2, abs_mul]
  have hCsq0 : (0 : ℝ) ≤ Csq := le_trans (abs_nonneg _) g4
  have hab : |(P[nu p.1 * nu p.2 | 𝒟]) ω * (P[nu q.1 * nu q.2 | 𝒟]) ω| ≤ Cm := by
    rw [abs_mul]
    calc |(P[nu p.1 * nu p.2 | 𝒟]) ω| * |(P[nu q.1 * nu q.2 | 𝒟]) ω|
        ≤ Csq * Csq := mul_le_mul g4 g5 (abs_nonneg _) hCsq0
      _ = Csq ^ 2 := by ring
      _ ≤ Cm := hCsq
  have hsub : |(P[fun ω => nu p.1 ω * nu p.2 ω * (nu q.1 ω * nu q.2 ω) | 𝒟]) ω
      - (P[nu p.1 * nu p.2 | 𝒟]) ω * (P[nu q.1 * nu q.2 | 𝒟]) ω| ≤ 2 * Cm := by
    refine le_trans (abs_sub _ _) ?_
    linarith
  have hw : |(xt p.1 k * xt p.2 l * (xt q.1 k * xt q.2 l)) ω| ≤ B ^ 4 := by
    simpa [Real.norm_eq_abs] using norm_weight_le hB k l p q ω
  calc |(xt p.1 k * xt p.2 l * (xt q.1 k * xt q.2 l)) ω|
        * |(P[fun ω => nu p.1 ω * nu p.2 ω * (nu q.1 ω * nu q.2 ω) | 𝒟]) ω
            - (P[nu p.1 * nu p.2 | 𝒟]) ω * (P[nu q.1 * nu q.2 | 𝒟]) ω|
      ≤ B ^ 4 * (2 * Cm) := mul_le_mul hw hsub (abs_nonneg _) (by positivity)
    _ = 2 * B ^ 4 * Cm := by ring

omit [DecidableEq D] [DecidableEq κ] in
/-- **Lemma SM.B.13**, first claim, under the dependence assumption (Regime 3) and the moment
assumption. The hypotheses `hint`, `hzero` and `hbd` of `infeasibleMeat_condVar_le` are supplied
by `integrable_centeredSummand_mul`, `condExp_centeredSummand_mul_eq_zero` and
`abs_condExp_centeredSummand_mul_le`, with `Ω_n = E[𝓜̃_n ∣ 𝒟]` by `condExp_unionMeat_eq_scoreVar`. -/
theorem infeasibleMeat_condVar_le_of_regime3 (hdims : dims.Nonempty)
    (hreg : Regime3 𝒟 h𝒟 c dims nu P) (hmeas : ∀ o, Measurable (nu o))
    (hprod : ∀ o o', MemLp (nu o * nu o') 2 P) {xt : O → κ → Ω → ℝ} {B Cm Csq lmin : ℝ}
    (hl : 0 < lmin)
    (hxt : ∀ o k, StronglyMeasurable[𝒟] (xt o k)) (hB : ∀ o k ω, |xt o k ω| ≤ B)
    (hmom : ∀ o, ∀ᵐ ω ∂P, (P[fun ω => nu o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hOmbd : ∀ o o', ∀ᵐ ω ∂P, |(P[nu o * nu o' | 𝒟]) ω| ≤ Csq) (hCsq : Csq ^ 2 ≤ Cm) :
    ∀ᵐ ω ∂P, (P[fun ω => frobSq (unionMeat c dims xt nu ω
        - scoreVar c dims xt (condOmegaKernel 𝒟 P nu) ω) | 𝒟]) ω
      ≤ 64 * (Fintype.card κ : ℝ) ^ 2 * B ^ 4 * Cm
        * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) lmin * lmin ^ 2 :=
  infeasibleMeat_condVar_le 𝒟 c dims (le_trans (sq_nonneg Csq) hCsq) hl
    (fun k l p _ q _ => integrable_centeredSummand_mul (h𝒟 := h𝒟) hxt hB hprod k l p q)
    (fun k l _p hp _q hq hnm =>
      condExp_centeredSummand_mul_eq_zero hdims hreg hmeas hprod hxt hB k l hp hq hnm)
    (fun k l p q => abs_condExp_centeredSummand_mul_le (h𝒟 := h𝒟) hxt hB hprod hmom hOmbd
      hCsq k l p q)

end FourFold

/-! ### Examples on a Gaussian model

Two observations under a product of two standard Gaussians, `ν_o` the `o`-th coordinate, each
observation in its own cluster. Here `Ω_{oo} = 1` and `Ω_n = 13` at weights `x̃ = 2, 3`, and the
centered summands are almost surely non-zero, so the conclusions are not trivial identities. -/

section RegimeWitness

open MeasureTheory ProbabilityTheory MeasurableSpace Sharing

/-- `ν_o ∈ L⁴` in the Gaussian example model. -/
theorem witGNu_memLp_four (o : WitO) : MemLp (witGNu o) 4 witGP := by
  have h : MemLp (id : ℝ → ℝ) 4 (witGP.map (fun ω : WitGΩ => ω o)) := by
    rw [witGP_map_eval o]; exact memLp_id_gaussianReal' 4 (by simp)
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_pi_apply o).aemeasurable).1 h

theorem witG_prod (o o' : WitO) : MemLp (witGNu o * witGNu o') 2 witGP :=
  memLp_two_mul_of_memLp_four witGNu_memLp_four o o'

theorem witG_mem_linkedPairs (o : WitO) : (o, o) ∈ linkedPairs witC2 witDims :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨0, Finset.mem_univ 0, rfl⟩⟩

/-- `(0,0,1,1) ∉ 𝓛_n` in the example model: both pairs are linked, and every cross-link is
`0 ∼ 1`, which fails. -/
theorem witG_not_mem_linkedQuads :
    ((0 : WitO), (0 : WitO), (1 : WitO), (1 : WitO)) ∉ linkedQuads witC2 witDims := by
  intro h
  obtain ⟨-, -, hcross⟩ := (Finset.mem_filter.1 h).2
  rcases hcross with h1 | h1 | h1 | h1 <;> exact witNotLinked h1

theorem witGXt_bound (o : WitO) (k : Fin 1) (ω : WitGΩ) : |witGXt o k ω| ≤ 3 := by
  unfold witGXt; split <;> norm_num

/-- `Ω_{oo} = E[ν_o² ∣ 𝒟] = 1` in the example model. -/
theorem witG_condOmega_diag_eq_one (o : WitO) :
    witGP[witGNu o * witGNu o | (⊥ : MeasurableSpace WitGΩ)] =ᵐ[witGP] fun _ => 1 := by
  rw [condExp_bot]
  have h : ∫ x, witGNu o x * witGNu o x ∂witGP = 1 := witGNu_sq_integral o
  simp only [Pi.mul_apply]
  rw [h]

/-- The centered summand `ξ̄_{oo} = x̃_{ok}x̃_{ol}(ν_o² - 1)` is almost surely non-zero, since
`gaussianReal 0 1 ≪ volume` and `{x : x² = 1}` is finite. -/
theorem witG_centered_ne_zero (o : WitO) :
    ∀ᵐ ω ∂witGP, witGNu o ω * witGNu o ω - 1 ≠ 0 := by
  have hmeasS : MeasurableSet {x : ℝ | x * x - 1 = 0} := by
    have hfun : {x : ℝ | x * x - 1 = 0} = (fun x : ℝ => x * x - 1) ⁻¹' {0} := rfl
    rw [hfun]
    exact ((measurable_id.mul measurable_id).sub measurable_const)
      (measurableSet_singleton 0)
  have hsub : {x : ℝ | x * x - 1 = 0} ⊆ ({-1, 1} : Set ℝ) := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    have h : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h1 | h1
    · right; exact sub_eq_zero.1 h1
    · left; linarith
  have hvol : (MeasureTheory.volume : Measure ℝ) ({-1, 1} : Set ℝ) = 0 :=
    ((Set.finite_singleton (1 : ℝ)).insert (-1)).measure_zero _
  have hnull : gaussianReal 0 1 {x : ℝ | x * x - 1 = 0} = 0 :=
    measure_mono_null hsub (gaussianReal_absolutelyContinuous 0 (by norm_num) hvol)
  rw [ae_iff]
  have hpre : {ω : WitGΩ | ¬ (witGNu o ω * witGNu o ω - 1 ≠ 0)}
      = (fun ω : WitGΩ => ω o) ⁻¹' {x : ℝ | x * x - 1 = 0} := by
    ext ω; simp [witGNu]
  rw [hpre, ← Measure.map_apply (measurable_pi_apply o) hmeasS, witGP_map_eval o, hnull]

/-- Example for `condExp_centeredSummand_mul_eq_zero`: the quadruple `(0,0,1,1)` lies outside
`𝓛_n` while both pairs are linked. -/
theorem witness_condExp_centeredSummand_mul_eq_zero :
    witGP[fun ω =>
        centeredSummand witGXt witGNu (condOmegaKernel ⊥ witGP witGNu) 0 0
            ((0 : WitO), (0 : WitO)) ω
          * centeredSummand witGXt witGNu (condOmegaKernel ⊥ witGP witGNu) 0 0
            ((1 : WitO), (1 : WitO)) ω | (⊥ : MeasurableSpace WitGΩ)] =ᵐ[witGP] 0 :=
  condExp_centeredSummand_mul_eq_zero (h𝒟 := bot_le) Finset.univ_nonempty witG_regime3
    witGNu_measurable witG_prod (B := 3) (fun _ _ => stronglyMeasurable_const) witGXt_bound
    0 0 (witG_mem_linkedPairs 0) (witG_mem_linkedPairs 1) witG_not_mem_linkedQuads

/-- Example for `condExp_unionMeat_eq_scoreVar`. -/
theorem witness_condExp_unionMeat_eq_scoreVar :
    witGP[fun ω => unionMeat witC2 witDims witGXt witGNu ω 0 0
        | (⊥ : MeasurableSpace WitGΩ)]
      =ᵐ[witGP] fun ω =>
        scoreVar witC2 witDims witGXt (condOmegaKernel ⊥ witGP witGNu) ω 0 0 :=
  condExp_unionMeat_eq_scoreVar (h𝒟 := bot_le) Finset.univ_nonempty witG_regime3
    witGNu_measurable witGNu_memLp witG_exog (B := 3)
    (fun _ _ => stronglyMeasurable_const) witGXt_bound 0 0

/-- The linked pairs of the example model are the two diagonal pairs. -/
theorem witG_linkedPairs :
    linkedPairs witC2 witDims = {((0 : WitO), (0 : WitO)), ((1 : WitO), (1 : WitO))} := by
  decide

/-- `Ω_n = 4Ω_{00} + 9Ω_{11} = 13` in the example model. -/
theorem witness_scoreVar_eq_thirteen :
    (fun ω => scoreVar witC2 witDims witGXt (condOmegaKernel ⊥ witGP witGNu) ω 0 0)
      =ᵐ[witGP] fun _ => 13 := by
  filter_upwards [witG_condOmega_diag_eq_one 0, witG_condOmega_diag_eq_one 1] with ω h0 h1
  simp only [scoreVar, Matrix.of_apply]
  rw [witG_linkedPairs, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [condOmegaKernel]
  rw [h0, h1]
  unfold witGXt
  norm_num

end RegimeWitness

/-! ### Lemma SM.B.13, second claim, under Regime 3 -/

section MeatSequenceRegime3

open MeasureTheory ProbabilityTheory MeasurableSpace Sharing

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace Ω] {P : Measure Ω}

/-- **Lemma SM.B.13**, second claim, under Regime 3: `infeasibleMeat_tendstoInProb` with `hint`,
`hzero` and `hbd` supplied, at `Ω_n := scoreVar (c j) (dims j) (xt j) (condOmegaKernel 𝒟 P (nu j))`.
See `infeasibleMeat_tendstoInProb_of_regime3_nodiv` for a form without `hOmbd` and `hdivint`. -/
theorem infeasibleMeat_tendstoInProb_of_regime3 [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)]
    {O D L κ : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, DecidableEq (L j)] [∀ j, Fintype (κ j)]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j))
    (xt : ∀ j, O j → κ j → Ω → ℝ) (nu : ∀ j, O j → Ω → ℝ) {B Cm Csq : ℝ}
    {lam : ℕ → Ω → ℝ} (hlamM : ∀ j, Measurable[𝒟] (lam j)) (hlam0 : ∀ j ω, 0 < lam j ω)
    (hFmeas : ∀ j, Measurable (fun ω =>
      rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (condOmegaKernel 𝒟 P (nu j)) ω)))
    (hFint : ∀ j, Integrable (fun ω =>
      frobSq (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (condOmegaKernel 𝒟 P (nu j)) ω)) P)
    (hdivint : ∀ j, Integrable (fun ω =>
      (rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (condOmegaKernel 𝒟 P (nu j)) ω) / lam j ω) ^ 2) P)
    (hdims : ∀ j, (dims j).Nonempty)
    (hreg : ∀ j, Regime3 𝒟 hm (c j) (dims j) (nu j) P)
    (hmeas : ∀ j o, Measurable (nu j o))
    (hprod : ∀ j o o', MemLp (nu j o * nu j o') 2 P)
    (hxt : ∀ j o k, StronglyMeasurable[𝒟] (xt j o k))
    (hB : ∀ j o k ω, |xt j o k ω| ≤ B)
    (hmom : ∀ j o, ∀ᵐ ω ∂P, (P[fun ω => nu j o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hOmbd : ∀ j o o', ∀ᵐ ω ∂P, |(P[nu j o * nu j o' | 𝒟]) ω| ≤ Csq) (hCsq : Csq ^ 2 ≤ Cm)
    (hdelta : TendstoInMeasure P (fun j ω => 64 * (Fintype.card (κ j) : ℝ) ^ 2 * B ^ 4 * Cm
        * deltaSeq (Fintype.card (O j) : ℝ) (maxDegree (c j) (dims j) : ℝ) (lam j ω))
        atTop (fun _ => 0)) :
    TendstoInMeasure P (fun j ω =>
        rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
          - scoreVar (c j) (dims j) (xt j) (condOmegaKernel 𝒟 P (nu j)) ω) / lam j ω)
      atTop (fun _ => 0) :=
  infeasibleMeat_tendstoInProb 𝒟 hm c dims xt nu (fun j => condOmegaKernel 𝒟 P (nu j))
    (le_trans (sq_nonneg Csq) hCsq) hlamM hlam0 hFmeas hFint hdivint
    (fun j k l p _ q _ =>
      integrable_centeredSummand_mul (h𝒟 := hm) (hxt j) (hB j) (hprod j) k l p q)
    (fun j k l _p hp _q hq hnm =>
      condExp_centeredSummand_mul_eq_zero (hdims j) (hreg j) (hmeas j) (hprod j) (hxt j)
        (hB j) k l hp hq hnm)
    (fun j k l p q => abs_condExp_centeredSummand_mul_le (h𝒟 := hm) (hxt j) (hB j) (hprod j)
      (hmom j) (hOmbd j) hCsq k l p q)
    hdelta

end MeatSequenceRegime3

/-! ## Moment bounds and removal of the integrability side condition

This part derives `hOmbd` (`|Ω_{oo'}| ≤ C^{1/2}`), `hnu` (`E[‖ν‖² ∣ 𝒟] ≤ C^{1/2}n`) and `hvp`
(`E[‖ϖ‖² ∣ 𝒟] ≤ C^{1/2}(d+K)(D_n+1)`) from the moment assumption, using conditional Jensen for
the square (`Integrable.norm_condExp_rpow_le`), and removes the integrability hypothesis
`hdivint` by multiplying the divisor into the indicator in the conditional Chebyshev step. -/

/-! ### Conditional Jensen for the square, and `hOmbd` -/

section MomentBound

variable {O Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Conditional Jensen for the square. -/
theorem sq_condExp_le_condExp_sq {X : Ω → ℝ} (hint : Integrable (fun ω => X ω ^ 2) P) :
    ∀ᵐ ω ∂P, (P[X | 𝒟]) ω ^ 2 ≤ (P[fun ω => X ω ^ 2 | 𝒟]) ω := by
  have hfun : (fun ω => ‖X ω‖ ^ (2 : ℝ)) = fun ω => X ω ^ 2 := by
    funext ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have h := Integrable.norm_condExp_rpow_le (m := 𝒟) (μ := P) (f := X) (p := 2) one_le_two
    (by rw [hfun]; exact hint)
  rw [hfun] at h
  filter_upwards [h] with ω hω
  have : ‖(P[X | 𝒟]) ω‖ ^ (2 : ℝ) ≤ (P[fun ω => X ω ^ 2 | 𝒟]) ω := hω
  rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
    sq_abs] at this

/-- The fourth power `ν_o^4` is integrable when `ν_oν_o ∈ L²`. -/
theorem integrable_pow_four {nu : O → Ω → ℝ} (hprod : ∀ o o', MemLp (nu o * nu o') 2 P)
    (o : O) : Integrable (fun ω => nu o ω ^ 4) P := by
  refine ((hprod o o).integrable_mul (hprod o o)).congr ?_
  filter_upwards with ω
  simp only [Pi.mul_apply]
  ring

/-- `|Ω_{oo'}| = |E[ν_oν_{o'} ∣ 𝒟]| ≤ C^{1/2}` from `E[ν_o^4 ∣ 𝒟] ≤ C`. -/
theorem abs_condOmega_le_sqrt {nu : O → Ω → ℝ} {Cm : ℝ}
    (hprod : ∀ o o', MemLp (nu o * nu o') 2 P)
    (hmom : ∀ o, ∀ᵐ ω ∂P, (P[fun ω => nu o ω ^ 4 | 𝒟]) ω ≤ Cm) (o o' : O) :
    ∀ᵐ ω ∂P, |(P[nu o * nu o' | 𝒟]) ω| ≤ Real.sqrt Cm := by
  have h4o := integrable_pow_four hprod o
  have h4o' := integrable_pow_four hprod o'
  have hsqint : Integrable (fun ω => (nu o * nu o') ω ^ 2) P := (hprod o o').integrable_sq
  have hjen := sq_condExp_le_condExp_sq (𝒟 := 𝒟) hsqint
  have hptw : (fun ω => (nu o * nu o') ω ^ 2)
      ≤ᵐ[P] fun ω => (nu o ω ^ 4 + nu o' ω ^ 4) / 2 := by
    filter_upwards with ω
    simp only [Pi.mul_apply]
    nlinarith [sq_nonneg (nu o ω ^ 2 - nu o' ω ^ 2), sq_nonneg (nu o ω * nu o' ω)]
  have hmaj : Integrable (fun ω => (nu o ω ^ 4 + nu o' ω ^ 4) / 2) P :=
    (h4o.add h4o').div_const 2
  have hmono := condExp_mono (μ := P) (m := 𝒟) hsqint hmaj hptw
  have hadd : (P[fun ω => (nu o ω ^ 4 + nu o' ω ^ 4) / 2 | 𝒟])
      =ᵐ[P] fun ω => ((P[fun ω => nu o ω ^ 4 | 𝒟]) ω + (P[fun ω => nu o' ω ^ 4 | 𝒟]) ω) / 2 := by
    have e1 : (fun ω => (nu o ω ^ 4 + nu o' ω ^ 4) / 2)
        = (2 : ℝ)⁻¹ • ((fun ω => nu o ω ^ 4) + fun ω => nu o' ω ^ 4) := by
      funext ω; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    rw [e1]
    filter_upwards [condExp_smul (μ := P) (2 : ℝ)⁻¹
      ((fun ω => nu o ω ^ 4) + fun ω => nu o' ω ^ 4) 𝒟,
      condExp_add (μ := P) h4o h4o' 𝒟] with ω g1 g2
    rw [g1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [g2]
    simp only [Pi.add_apply]
    ring
  filter_upwards [hjen, hmono, hadd, hmom o, hmom o'] with ω j1 m1 a1 c1 c2
  have hle : (P[nu o * nu o' | 𝒟]) ω ^ 2 ≤ Cm := by
    rw [a1] at m1
    linarith
  calc |(P[nu o * nu o' | 𝒟]) ω| = Real.sqrt ((P[nu o * nu o' | 𝒟]) ω ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt Cm := Real.sqrt_le_sqrt hle

end MomentBound

/-! ### The bound `E[‖ν‖² ∣ 𝒟] = tr(Ω) ≤ C^{1/2}n` -/

section NuBound

variable {O Ω : Type*} [Fintype O] {𝒟 mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsFiniteMeasure P]

/-- `E[‖ν‖² ∣ 𝒟] = tr(Ω) ≤ C^{1/2}n`. -/
theorem condExp_sq_l2Norm_le {nu : O → Ω → ℝ} {Cm : ℝ}
    (hprod : ∀ o o', MemLp (nu o * nu o') 2 P)
    (hmom : ∀ o, ∀ᵐ ω ∂P, (P[fun ω => nu o ω ^ 4 | 𝒟]) ω ≤ Cm) :
    (P[fun ω => l2Norm (fun o => nu o ω) ^ 2 | 𝒟])
      ≤ᵐ[P] fun _ => (Fintype.card O : ℝ) * Real.sqrt Cm := by
  classical
  have hsqfun : ∀ o : O, (nu o * nu o) = fun ω => nu o ω ^ 2 := by
    intro o; funext ω; simp only [Pi.mul_apply]; ring
  have hsqint : ∀ o : O, Integrable (fun ω => nu o ω ^ 2) P := by
    intro o
    rw [← hsqfun o]
    exact (hprod o o).integrable one_le_two
  have hfun : (fun ω => l2Norm (fun o => nu o ω) ^ 2)
      = ∑ o : O, fun ω => nu o ω ^ 2 := by
    funext ω
    rw [sq_l2Norm]
    rw [Finset.sum_apply]
  have hsum := condExp_finsetSum (μ := P) (s := (Finset.univ : Finset O))
    (f := fun o => fun ω => nu o ω ^ 2) (fun o _ => hsqint o) 𝒟
  have hdiag : ∀ o : O, ∀ᵐ ω ∂P, (P[fun ω => nu o ω ^ 2 | 𝒟]) ω ≤ Real.sqrt Cm := by
    intro o
    filter_upwards [abs_condOmega_le_sqrt (𝒟 := 𝒟) hprod hmom o o] with ω hω
    rw [hsqfun o] at hω
    exact le_trans (le_abs_self _) hω
  rw [hfun]
  have hall : ∀ᵐ ω ∂P, ∀ o : O, (P[fun ω => nu o ω ^ 2 | 𝒟]) ω ≤ Real.sqrt Cm := by
    rw [ae_all_iff]; exact hdiag
  filter_upwards [hsum, hall] with ω e1 e2
  rw [e1, Finset.sum_apply]
  calc ∑ o : O, (P[fun ω => nu o ω ^ 2 | 𝒟]) ω
      ≤ ∑ _o : O, Real.sqrt Cm := Finset.sum_le_sum fun o _ => e2 o
    _ = (Fintype.card O : ℝ) * Real.sqrt Cm := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end NuBound

/-! ### The bound `E[‖ϖ‖² ∣ 𝒟] = tr(ΠΩΠ) ≤ (d_{[Δ]}+K)λ_max(Ω)`

`Π` enters only through its symmetry, idempotence and trace. -/

section ProjBoundDet

variable {O : Type*} [Fintype O] [DecidableEq O]

omit [DecidableEq O] in
/-- `‖Πx‖² = x'Πx` for a symmetric idempotent `Π`, written as a double sum. -/
theorem sq_l2Norm_mulVec_proj (A : Matrix O O ℝ) (hH : A.IsHermitian) (hI : A * A = A)
    (x : O → ℝ) :
    l2Norm (A *ᵥ x) ^ 2 = ∑ o : O, ∑ o' : O, A o o' * (x o * x o') := by
  have hAt : Aᵀ = A := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hH
  have hdd : ∀ u : O → ℝ, l2Norm u ^ 2 = u ⬝ᵥ u := by
    intro u
    rw [sq_l2Norm, dotProduct]
    exact Finset.sum_congr rfl fun o _ => by rw [sq]
  rw [hdd]
  have h1 : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hAt, hI]
    exact dotProduct_comm _ _
  rw [h1, dotProduct]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun o' _ => by ring

/-- `∑_{o,o'} Π_{oo'}Ω_{oo'} = tr(ΠΩΠ) ≤ κ·tr(Π)` for a symmetric idempotent `Π` and a
symmetric `Ω ⪯ κI`. -/
theorem double_sum_le_of_proj {A Om : Matrix O O ℝ} (hA : A.IsHermitian) (hAA : A * A = A)
    (hOmH : Om.IsHermitian) {kap rho : ℝ} (hOm : Om ≤ kap • (1 : Matrix O O ℝ))
    (htr : A.trace = rho) :
    ∑ o : O, ∑ o' : O, A o o' * Om o o' ≤ kap * rho := by
  have hsym : ∀ o o' : O, Om o' o = Om o o' := by
    intro o o'
    have h := congrFun (congrFun hOmH o) o'
    simpa [Matrix.conjTranspose_apply] using h
  have h1 : ∑ o : O, ∑ o' : O, A o o' * Om o o' = (A * Om).trace := by
    rw [Matrix.trace]
    refine (Finset.sum_congr rfl fun o _ => ?_).symm
    rw [Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun o' _ => by rw [hsym o o']
  have h2 : (A * Om).trace = (A * Om * A).trace := by
    calc (A * Om).trace = (Om * (A * A)).trace := by rw [hAA, Matrix.trace_mul_comm]
      _ = ((Om * A) * A).trace := by rw [Matrix.mul_assoc]
      _ = (A * (Om * A)).trace := Matrix.trace_mul_comm _ _
      _ = (A * Om * A).trace := by rw [Matrix.mul_assoc]
  rw [h1, h2]
  exact trace_conj_proj_le hA hAA hOm htr

omit [DecidableEq O] in
/-- The entries of an orthogonal projector are bounded by one, since `Π_{oo'}² ≤ Π_{oo} = ∑_k Π_{ok}²`
and `Π_{oo}² ≤ Π_{oo}`. -/
theorem abs_entry_le_one_of_proj {A : Matrix O O ℝ} (hA : A.IsHermitian) (hAA : A * A = A)
    (o o' : O) : |A o o'| ≤ 1 := by
  have hsym : ∀ p q : O, A q p = A p q := by
    intro p q
    have h := congrFun (congrFun hA p) q
    simpa [Matrix.conjTranspose_apply] using h
  have hdiag : ∀ p : O, A p p = ∑ k : O, A p k ^ 2 := by
    intro p
    have h := congrFun (congrFun hAA p) p
    rw [Matrix.mul_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by rw [hsym p k, sq]
  have hge : ∀ p q : O, A p q ^ 2 ≤ A p p := by
    intro p q
    rw [hdiag p]
    exact Finset.single_le_sum (f := fun k => A p k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ q)
  have hle1 : A o o ≤ 1 := by
    have h := hge o o
    nlinarith [hge o o]
  have h2 : A o o' ^ 2 ≤ 1 := le_trans (hge o o') hle1
  rw [abs_le]
  constructor <;> nlinarith [h2]

end ProjBoundDet

section ProjBound

open Sharing

variable {O D L Ω : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {𝒟 mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
variable (c : D → O → L) (dims : Finset D)

omit [DecidableEq D] in
/-- `E[‖ϖ‖² ∣ 𝒟] = tr(ΠΩΠ) ≤ C^{1/2}(D_n+1)tr(Π)` at `ϖ = Πν`. The hypothesis `hz` is the
vanishing of `Ω_{oo'}` off the sharing graph (Lemma SM.B.11(a), `condCov_eq_zero_of_not_linked`). -/
theorem condExp_sq_l2Norm_proj_le {nu : O → Ω → ℝ} {Cm rho : ℝ} (hle𝒟 : 𝒟 ≤ mΩ)
    {Pr : Ω → Matrix O O ℝ}
    (hPrm : ∀ o o', StronglyMeasurable[𝒟] (fun ω => Pr ω o o'))
    (hPrH : ∀ ω, (Pr ω).IsHermitian) (hPrI : ∀ ω, Pr ω * Pr ω = Pr ω)
    (hPrtr : ∀ ω, (Pr ω).trace = rho)
    (hprod : ∀ o o', MemLp (nu o * nu o') 2 P)
    (hmom : ∀ o, ∀ᵐ ω ∂P, (P[fun ω => nu o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hz : ∀ o o', ¬ Linked c dims o o' → P[nu o * nu o' | 𝒟] =ᵐ[P] 0) :
    (P[fun ω => l2Norm (fun o => (Pr ω *ᵥ fun o' => nu o' ω) o) ^ 2 | 𝒟])
      ≤ᵐ[P] fun _ => Real.sqrt Cm * ((maxDegree c dims : ℝ) + 1) * rho := by
  classical
  have hint : ∀ o o', Integrable (nu o * nu o') P :=
    fun o o' => (hprod o o').integrable one_le_two
  have hwint : ∀ p : O × O, Integrable ((fun ω => Pr ω p.1 p.2) * (nu p.1 * nu p.2)) P := by
    intro p
    refine (hint p.1 p.2).bdd_mul (c := (1 : ℝ))
      ((hPrm p.1 p.2).mono hle𝒟).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    exact abs_entry_le_one_of_proj (hPrH ω) (hPrI ω) p.1 p.2
  have hfun : (fun ω => l2Norm (fun o => (Pr ω *ᵥ fun o' => nu o' ω) o) ^ 2)
      = ∑ p ∈ (Finset.univ : Finset (O × O)),
          ((fun ω => Pr ω p.1 p.2) * (nu p.1 * nu p.2)) := by
    funext ω
    rw [Finset.sum_apply, sq_l2Norm_mulVec_proj (Pr ω) (hPrH ω) (hPrI ω) (fun o => nu o ω),
      Fintype.sum_prod_type]
    rfl
  have hsum := condExp_finsetSum (μ := P) (s := (Finset.univ : Finset (O × O)))
    (f := fun p : O × O => ((fun ω => Pr ω p.1 p.2) * (nu p.1 * nu p.2)))
    (fun p _ => hwint p) 𝒟
  have hpull : ∀ᵐ ω ∂P, ∀ p : O × O,
      (P[(fun ω => Pr ω p.1 p.2) * (nu p.1 * nu p.2) | 𝒟]) ω
        = Pr ω p.1 p.2 * (P[nu p.1 * nu p.2 | 𝒟]) ω := by
    rw [ae_all_iff]
    intro p
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hPrm p.1 p.2) (hwint p)
      (hint p.1 p.2)] with ω hω
    rw [hω]; rfl
  have hbd : ∀ᵐ ω ∂P, ∀ o o' : O, |(P[nu o * nu o' | 𝒟]) ω| ≤ Real.sqrt Cm := by
    rw [ae_all_iff]; intro o; rw [ae_all_iff]; intro o'
    exact abs_condOmega_le_sqrt hprod hmom o o'
  have hzero : ∀ᵐ ω ∂P, ∀ o o' : O, ¬ Linked c dims o o' → (P[nu o * nu o' | 𝒟]) ω = 0 := by
    rw [ae_all_iff]; intro o; rw [ae_all_iff]; intro o'
    by_cases h : Linked c dims o o'
    · exact Filter.Eventually.of_forall fun ω hcon => absurd h hcon
    · filter_upwards [hz o o' h] with ω hω _; exact hω
  rw [hfun]
  filter_upwards [hsum, hpull, hbd, hzero] with ω e1 e2 e3 e4
  rw [e1, Finset.sum_apply, Finset.sum_congr rfl (fun p _ => e2 p)]
  set Om : Matrix O O ℝ := Matrix.of fun o o' => (P[nu o * nu o' | 𝒟]) ω with hOmdef
  have hOmH : Om.IsHermitian := by
    ext o o'
    simp only [hOmdef, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [mul_comm (nu o') (nu o)]
  have hOmle := le_smul_one_of_graphSupported c dims hOmH (Real.sqrt_nonneg Cm)
    (fun o o' => e3 o o') (fun o o' h => e4 o o' h)
  have hmain := double_sum_le_of_proj (hPrH ω) (hPrI ω) hOmH hOmle (hPrtr ω)
  rw [Fintype.sum_prod_type]
  exact hmain

end ProjBound

/-! ### Conditional Chebyshev with the divisor inside the indicator -/

section DivBridge

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Conditional Markov step with the random divisor multiplied into the indicator, so no
integrability of `(F/λ)²` is needed. -/
theorem condExp_indicator_div_le [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ) {F lam : Ω → ℝ}
    {sig ep : ℝ} (hep : 0 < ep) (_hF0 : ∀ ω, 0 ≤ F ω) (hFmeas : Measurable F)
    (hlamM : Measurable[𝒟] lam) (hlam0 : ∀ ω, 0 < lam ω)
    (hFint : Integrable (fun ω => F ω ^ 2) P)
    (hle : (P[fun ω => F ω ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => sig) :
    (P[Set.indicator {ω | ep ≤ F ω / lam ω} (fun _ => (1 : ℝ)) | 𝒟])
      ≤ᵐ[P] fun ω => sig / (ep ^ 2 * lam ω ^ 2) := by
  classical
  have hlamΩ : Measurable lam := hlamM.mono hm le_rfl
  set A : Set Ω := {ω | ep ≤ F ω / lam ω} with hA
  have hmeasA : MeasurableSet A := measurableSet_le measurable_const (hFmeas.div hlamΩ)
  set ind : Ω → ℝ := Set.indicator A (fun _ => (1 : ℝ)) with hind
  have hind0 : ∀ ω, 0 ≤ ind ω := by
    intro ω
    by_cases h : ω ∈ A
    · rw [hind, Set.indicator_of_mem h]; exact zero_le_one
    · rw [hind, Set.indicator_of_notMem h]
  have hindint : Integrable ind P := (integrable_const (1 : ℝ)).indicator hmeasA
  -- the truncated multiplier, one for each `S : ℕ`
  have hstep : ∀ S : ℕ, ∀ᵐ ω ∂P,
      ep ^ 2 * min (lam ω ^ 2) (S : ℝ) * (P[ind | 𝒟]) ω ≤ sig := by
    intro S
    have hwm : StronglyMeasurable[𝒟] (fun ω => ep ^ 2 * min (lam ω ^ 2) (S : ℝ)) :=
      (measurable_const.mul ((hlamM.pow_const 2).min measurable_const)).stronglyMeasurable
    have hwb : ∀ ω, |ep ^ 2 * min (lam ω ^ 2) (S : ℝ)| ≤ ep ^ 2 * S := by
      intro ω
      have h1 : 0 ≤ min (lam ω ^ 2) (S : ℝ) := le_min (sq_nonneg _) (Nat.cast_nonneg S)
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    have hwgint : Integrable ((fun ω => ep ^ 2 * min (lam ω ^ 2) (S : ℝ)) * ind) P := by
      refine hindint.bdd_mul (c := ep ^ 2 * S) (hwm.mono hm).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      exact hwb ω
    have hptw : ((fun ω => ep ^ 2 * min (lam ω ^ 2) (S : ℝ)) * ind)
        ≤ᵐ[P] fun ω => F ω ^ 2 := by
      filter_upwards with ω
      show ep ^ 2 * min (lam ω ^ 2) (S : ℝ) * ind ω ≤ F ω ^ 2
      by_cases h : ω ∈ A
      · rw [hind, Set.indicator_of_mem h, mul_one]
        have hx : ep ≤ F ω / lam ω := h
        have hFl : ep * lam ω ≤ F ω := by
          rw [le_div_iff₀ (hlam0 ω)] at hx
          exact hx
        have h1 : ep ^ 2 * lam ω ^ 2 ≤ F ω ^ 2 := by
          have h2 : 0 ≤ ep * lam ω := mul_nonneg hep.le (hlam0 ω).le
          nlinarith [hFl, h2]
        have h3 : min (lam ω ^ 2) (S : ℝ) ≤ lam ω ^ 2 := min_le_left _ _
        nlinarith [h1, h3, sq_nonneg ep]
      · rw [hind, Set.indicator_of_notMem h, mul_zero]
        exact sq_nonneg _
    have hmono := condExp_mono (μ := P) (m := 𝒟) hwgint hFint hptw
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝒟) (μ := P) hwm hwgint hindint
    filter_upwards [hmono, hpull, hle] with ω m1 p1 l1
    rw [p1] at m1
    exact le_trans m1 l1
  have hall : ∀ᵐ ω ∂P, ∀ S : ℕ,
      ep ^ 2 * min (lam ω ^ 2) (S : ℝ) * (P[ind | 𝒟]) ω ≤ sig := by
    rw [ae_all_iff]; exact hstep
  filter_upwards [hall] with ω hω
  have hS := hω ⌈lam ω ^ 2⌉₊
  rw [min_eq_left (Nat.le_ceil _)] at hS
  rw [le_div_iff₀ (mul_pos (pow_pos hep 2) (pow_pos (hlam0 ω) 2))]
  calc (P[ind | 𝒟]) ω * (ep ^ 2 * lam ω ^ 2)
      = ep ^ 2 * lam ω ^ 2 * (P[ind | 𝒟]) ω := by ring
    _ ≤ sig := hS

/-- Convergence in probability to zero from a conditional second-moment bound with a random
divisor, without integrability of the ratio. -/
theorem tendstoInMeasure_zero_of_condExp_sq_div_le [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)] {F lam : ℕ → Ω → ℝ} {sig : ℕ → ℝ}
    (hFmeas : ∀ n, Measurable (F n)) (hF0 : ∀ n ω, 0 ≤ F n ω)
    (hFint : ∀ n, Integrable (fun ω => F n ω ^ 2) P)
    (hlamM : ∀ n, Measurable[𝒟] (lam n)) (hlam0 : ∀ n ω, 0 < lam n ω)
    (hsig0 : ∀ n, 0 ≤ sig n)
    (hle : ∀ n, (P[fun ω => F n ω ^ 2 | 𝒟]) ≤ᵐ[P] fun _ => sig n)
    (hrho : TendstoInMeasure P (fun n ω => sig n / lam n ω ^ 2) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => F n ω / lam n ω) atTop (fun _ => 0) := by
  classical
  have hlamΩ : ∀ n, Measurable (lam n) := fun n => (hlamM n).mono hm le_rfl
  rw [tendstoInMeasure_iff_dist]
  intro ep hep
  have hep2 : (0 : ℝ) < ep ^ 2 := pow_pos hep 2
  set rho : ℕ → Ω → ℝ := fun n ω => sig n / lam n ω ^ 2 with hrhodef
  have hrho0 : ∀ n ω, 0 ≤ rho n ω := fun n ω =>
    div_nonneg (hsig0 n) (sq_nonneg _)
  have hrhomeas : ∀ n, Measurable (rho n) := fun n =>
    measurable_const.div ((hlamΩ n).pow_const 2)
  set Y : ℕ → Ω → ℝ := fun n ω => min 1 ((ep ^ 2)⁻¹ * rho n ω) with hYdef
  have hYmeas : ∀ n, Measurable (Y n) := fun n =>
    measurable_const.min (measurable_const.mul (hrhomeas n))
  have hY0 : ∀ n ω, 0 ≤ Y n ω := fun n ω =>
    le_min zero_le_one (mul_nonneg (by positivity) (hrho0 n ω))
  have hY1 : ∀ n ω, Y n ω ≤ 1 := fun n ω => min_le_left _ _
  have hYint : ∀ n, Integrable (Y n) P := fun n =>
    Integrable.mono' (integrable_const (1 : ℝ)) (hYmeas n).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hY0 n ω)]; exact hY1 n ω)
  have hYtend : TendstoInMeasure P Y atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_zero_of_le hY0 (fun n ω => min_le_right _ _)
      (tendstoInMeasure_zero_const_mul (ep ^ 2)⁻¹ hrho)
  have hIY := tendsto_integral_of_tendstoInMeasure_le_one hYmeas hY0 hY1 hYtend
  have hmeasA : ∀ n, MeasurableSet {ω | ep ≤ F n ω / lam n ω} := fun n =>
    measurableSet_le measurable_const ((hFmeas n).div (hlamΩ n))
  have hindint : ∀ n, Integrable
      (Set.indicator {ω | ep ≤ F n ω / lam n ω} (fun _ => (1 : ℝ))) P :=
    fun n => (integrable_const (1 : ℝ)).indicator (hmeasA n)
  have hkey : ∀ n, (P[Set.indicator {ω | ep ≤ F n ω / lam n ω} (fun _ => (1 : ℝ)) | 𝒟])
      ≤ᵐ[P] Y n := by
    intro n
    have hone : Set.indicator {ω | ep ≤ F n ω / lam n ω} (fun _ => (1 : ℝ))
        ≤ᵐ[P] fun _ => (1 : ℝ) := by
      filter_upwards with ω
      show Set.indicator {ω | ep ≤ F n ω / lam n ω} (fun _ => (1 : ℝ)) ω ≤ 1
      by_cases hω : ω ∈ {ω | ep ≤ F n ω / lam n ω}
      · rw [Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem hω]; exact zero_le_one
    have hb1 := condExp_mono (μ := P) (m := 𝒟) (hindint n) (integrable_const (1 : ℝ)) hone
    rw [condExp_const hm (1 : ℝ)] at hb1
    have hm1 := condExp_indicator_div_le 𝒟 hm hep (hF0 n) (hFmeas n) (hlamM n) (hlam0 n)
      (hFint n) (hle n)
    filter_upwards [hb1, hm1] with ω e1 e3
    refine le_min e1 (e3.trans (le_of_eq ?_))
    rw [hrhodef]
    field_simp
  have hPle : ∀ n, P {ω | ep ≤ F n ω / lam n ω} ≤ ENNReal.ofReal (∫ ω, Y n ω ∂P) := by
    intro n
    have h1 : (P {ω | ep ≤ F n ω / lam n ω}).toReal
        = ∫ ω, (P[Set.indicator {ω | ep ≤ F n ω / lam n ω} (fun _ => (1 : ℝ)) | 𝒟]) ω ∂P := by
      rw [integral_condExp hm, integral_indicator_const (1 : ℝ) (hmeasA n)]
      simp [measureReal_def]
    have h2 : ∫ ω, (P[Set.indicator {ω | ep ≤ F n ω / lam n ω} (fun _ => (1 : ℝ)) | 𝒟]) ω ∂P
        ≤ ∫ ω, Y n ω ∂P := integral_mono_ae integrable_condExp (hYint n) (hkey n)
    have h3 : (P {ω | ep ≤ F n ω / lam n ω}).toReal ≤ ∫ ω, Y n ω ∂P := by rw [h1]; exact h2
    rw [← ENNReal.ofReal_toReal (measure_ne_top P {ω | ep ≤ F n ω / lam n ω})]
    exact ENNReal.ofReal_le_ofReal h3
  have hfin : Tendsto (fun n => ENNReal.ofReal (∫ ω, Y n ω ∂P)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hIY
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfin
    (fun _ => zero_le) (fun n => ?_)
  refine le_trans (measure_mono ?_) (hPle n)
  intro ω hω
  have hω' : ep ≤ dist (F n ω / lam n ω) ((fun _ => (0 : ℝ)) ω) := hω
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (hF0 n ω) (hlam0 n ω).le)] at hω'
  exact hω'

section DivBridgeSeq

open Sharing

variable {O D L κ : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, DecidableEq (L j)] [∀ j, Fintype (κ j)]

/-- **Lemma SM.B.13**, second claim, without the hypothesis `hdivint`. -/
theorem infeasibleMeat_tendstoInProb_nodiv [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j))
    (xt : ∀ j, O j → κ j → Ω → ℝ) (nu : ∀ j, O j → Ω → ℝ) (Om : ∀ j, O j → O j → Ω → ℝ)
    {B Cm : ℝ} (hC : 0 ≤ Cm)
    {lam : ℕ → Ω → ℝ} (hlamM : ∀ j, Measurable[𝒟] (lam j)) (hlam0 : ∀ j ω, 0 < lam j ω)
    (hFmeas : ∀ j, Measurable (fun ω =>
      rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (Om j) ω)))
    (hFint : ∀ j, Integrable (fun ω =>
      frobSq (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (Om j) ω)) P)
    (hint : ∀ j, ∀ k l : κ j, ∀ p ∈ linkedPairs (c j) (dims j),
      ∀ q ∈ linkedPairs (c j) (dims j),
      Integrable (fun ω => centeredSummand (xt j) (nu j) (Om j) k l p ω
        * centeredSummand (xt j) (nu j) (Om j) k l q ω) P)
    (hzero : ∀ j, ∀ k l : κ j, ∀ p ∈ linkedPairs (c j) (dims j),
      ∀ q ∈ linkedPairs (c j) (dims j),
      (p.1, p.2, q.1, q.2) ∉ linkedQuads (c j) (dims j) →
      (P[fun ω => centeredSummand (xt j) (nu j) (Om j) k l p ω
        * centeredSummand (xt j) (nu j) (Om j) k l q ω | 𝒟]) =ᵐ[P] 0)
    (hbd : ∀ j, ∀ k l : κ j, ∀ p q : O j × O j, ∀ᵐ ω ∂P,
      |(P[fun ω => centeredSummand (xt j) (nu j) (Om j) k l p ω
        * centeredSummand (xt j) (nu j) (Om j) k l q ω | 𝒟]) ω| ≤ 2 * B ^ 4 * Cm)
    (hdelta : TendstoInMeasure P (fun j ω => 64 * (Fintype.card (κ j) : ℝ) ^ 2 * B ^ 4 * Cm
        * deltaSeq (Fintype.card (O j) : ℝ) (maxDegree (c j) (dims j) : ℝ) (lam j ω))
        atTop (fun _ => 0)) :
    TendstoInMeasure P (fun j ω =>
        rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
          - scoreVar (c j) (dims j) (xt j) (Om j) ω) / lam j ω) atTop (fun _ => 0) := by
  set sig : ℕ → ℝ := fun j => 64 * (Fintype.card (κ j) : ℝ) ^ 2 * B ^ 4 * Cm
    * ((Fintype.card (O j) : ℝ) * (maxDegree (c j) (dims j) : ℝ) ^ 3) with hsigdef
  have hrho : TendstoInMeasure P (fun j ω => sig j / lam j ω ^ 2) atTop (fun _ => 0) := by
    have hfun : (fun j ω => sig j / lam j ω ^ 2)
        = fun j ω => 64 * (Fintype.card (κ j) : ℝ) ^ 2 * B ^ 4 * Cm
          * deltaSeq (Fintype.card (O j) : ℝ) (maxDegree (c j) (dims j) : ℝ) (lam j ω) := by
      funext j ω
      rw [hsigdef, deltaSeq]
      ring
    rw [hfun]
    exact hdelta
  refine tendstoInMeasure_zero_of_condExp_sq_div_le 𝒟 hm hFmeas
    (fun j ω => rectFrobNorm_nonneg _) (fun j => ?_) hlamM hlam0 (fun j => ?_) (fun j => ?_) hrho
  · rw [sq_rectFrobNorm_unionMeat_sub]
    exact hFint j
  · rw [hsigdef]
    have h1 : (0 : ℝ) ≤ (Fintype.card (O j) : ℝ) * (maxDegree (c j) (dims j) : ℝ) ^ 3 := by
      positivity
    have h2 : (0 : ℝ) ≤ 64 * (Fintype.card (κ j) : ℝ) ^ 2 * B ^ 4 * Cm := by positivity
    exact mul_nonneg h2 h1
  · rw [sq_rectFrobNorm_unionMeat_sub]
    have h1 := infeasibleMeat_condVar_le 𝒟 (c j) (dims j) (B := B) (Cm := Cm) (lmin := 1)
      hC one_pos (hint j) (hzero j) (hbd j)
    filter_upwards [h1] with ω e1
    rw [hsigdef]
    simpa [deltaSeq] using e1

end DivBridgeSeq

end DivBridge

/-! ### Consequences for the main statements -/

section Consumers

open MeasureTheory ProbabilityTheory MeasurableSpace Sharing

variable {O D L κ : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable [Fintype κ] [DecidableEq κ]
variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {h𝒟 : 𝒟 ≤ mΩ}
variable {P : Measure Ω} [IsFiniteMeasure P]
variable {c : D → O → L} {dims : Finset D} {nu : O → Ω → ℝ}

omit [DecidableEq D] [DecidableEq κ] in
/-- **Lemma SM.B.13**, first claim, with `hOmbd` derived from the moment assumption. -/
theorem infeasibleMeat_condVar_le_of_moments (hdims : dims.Nonempty)
    (hreg : Regime3 𝒟 h𝒟 c dims nu P) (hmeas : ∀ o, Measurable (nu o))
    (hprod : ∀ o o', MemLp (nu o * nu o') 2 P) {xt : O → κ → Ω → ℝ} {B Cm lmin : ℝ}
    (hCm : 0 ≤ Cm) (hl : 0 < lmin)
    (hxt : ∀ o k, StronglyMeasurable[𝒟] (xt o k)) (hB : ∀ o k ω, |xt o k ω| ≤ B)
    (hmom : ∀ o, ∀ᵐ ω ∂P, (P[fun ω => nu o ω ^ 4 | 𝒟]) ω ≤ Cm) :
    ∀ᵐ ω ∂P, (P[fun ω => frobSq (unionMeat c dims xt nu ω
        - scoreVar c dims xt (condOmegaKernel 𝒟 P nu) ω) | 𝒟]) ω
      ≤ 64 * (Fintype.card κ : ℝ) ^ 2 * B ^ 4 * Cm
        * deltaSeq (Fintype.card O : ℝ) (maxDegree c dims : ℝ) lmin * lmin ^ 2 :=
  infeasibleMeat_condVar_le_of_regime3 (h𝒟 := h𝒟) hdims hreg hmeas hprod hl hxt hB hmom
    (abs_condOmega_le_sqrt hprod hmom) (le_of_eq (Real.sq_sqrt hCm))

end Consumers

section ConsumerSeq

open MeasureTheory ProbabilityTheory MeasurableSpace Sharing

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace Ω] {P : Measure Ω}

/-- **Lemma SM.B.13**, second claim, under Regime 3 and the moment assumption, without `hOmbd`
and `hdivint`. -/
theorem infeasibleMeat_tendstoInProb_of_regime3_nodiv [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)]
    {O D L κ : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, DecidableEq (L j)] [∀ j, Fintype (κ j)]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j))
    (xt : ∀ j, O j → κ j → Ω → ℝ) (nu : ∀ j, O j → Ω → ℝ) {B Cm : ℝ} (hCm : 0 ≤ Cm)
    {lam : ℕ → Ω → ℝ} (hlamM : ∀ j, Measurable[𝒟] (lam j)) (hlam0 : ∀ j ω, 0 < lam j ω)
    (hFmeas : ∀ j, Measurable (fun ω =>
      rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (condOmegaKernel 𝒟 P (nu j)) ω)))
    (hFint : ∀ j, Integrable (fun ω =>
      frobSq (unionMeat (c j) (dims j) (xt j) (nu j) ω
        - scoreVar (c j) (dims j) (xt j) (condOmegaKernel 𝒟 P (nu j)) ω)) P)
    (hdims : ∀ j, (dims j).Nonempty)
    (hreg : ∀ j, Regime3 𝒟 hm (c j) (dims j) (nu j) P)
    (hmeas : ∀ j o, Measurable (nu j o))
    (hprod : ∀ j o o', MemLp (nu j o * nu j o') 2 P)
    (hxt : ∀ j o k, StronglyMeasurable[𝒟] (xt j o k))
    (hB : ∀ j o k ω, |xt j o k ω| ≤ B)
    (hmom : ∀ j o, ∀ᵐ ω ∂P, (P[fun ω => nu j o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hdelta : TendstoInMeasure P (fun j ω => 64 * (Fintype.card (κ j) : ℝ) ^ 2 * B ^ 4 * Cm
        * deltaSeq (Fintype.card (O j) : ℝ) (maxDegree (c j) (dims j) : ℝ) (lam j ω))
        atTop (fun _ => 0)) :
    TendstoInMeasure P (fun j ω =>
        rectFrobNorm (unionMeat (c j) (dims j) (xt j) (nu j) ω
          - scoreVar (c j) (dims j) (xt j) (condOmegaKernel 𝒟 P (nu j)) ω) / lam j ω)
      atTop (fun _ => 0) :=
  infeasibleMeat_tendstoInProb_nodiv 𝒟 hm c dims xt nu
    (fun j => condOmegaKernel 𝒟 P (nu j)) hCm hlamM hlam0 hFmeas hFint
    (fun j k l p _ q _ =>
      integrable_centeredSummand_mul (h𝒟 := hm) (hxt j) (hB j) (hprod j) k l p q)
    (fun j k l _p hp _q hq hnm =>
      condExp_centeredSummand_mul_eq_zero (hdims j) (hreg j) (hmeas j) (hprod j) (hxt j)
        (hB j) k l hp hq hnm)
    (fun j k l p q => abs_condExp_centeredSummand_mul_le (h𝒟 := hm) (hxt j) (hB j) (hprod j)
      (hmom j) (abs_condOmega_le_sqrt (hprod j) (hmom j)) (le_of_eq (Real.sq_sqrt hCm)) k l p q)
    hdelta

end ConsumerSeq

section ConsumerPerturb

open Sharing

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The perturbation hypothesis `hperturb` of Theorem 11(b) at `ϖ := Πν`, with `hnu` and `hvp`
derived from the moment assumption (`hmom`), the sharing-graph vanishing `hz`, and the symmetry,
idempotence, trace and `𝒟`-measurability of `Π`. -/
theorem perturb_tendstoInProb_of_moments [IsProbabilityMeasure P] (hm : 𝒟 ≤ mΩ)
    [SigmaFinite (P.trim hm)]
    {O D L κ : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    [∀ j, DecidableEq (D j)] [∀ j, DecidableEq (L j)] [∀ j, Fintype (κ j)]
    (c : ∀ j, D j → O j → L j) (dims : ∀ j, Finset (D j))
    (xt : ∀ j, O j → κ j → Ω → ℝ) (nu : ∀ j, O j → Ω → ℝ)
    (Pr : ∀ j, Ω → Matrix (O j) (O j) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hxt : ∀ (j : ℕ) (o : O j) (ω : Ω), ∑ k : κ j, xt j o k ω ^ 2 ≤ B ^ 2)
    {lam : ℕ → Ω → ℝ} (hlamM : ∀ j, Measurable[𝒟] (lam j)) (hlam0 : ∀ j ω, 0 < lam j ω)
    {Cm Kr : ℝ} (hCm : 0 < Cm) (hK0 : 0 ≤ Kr)
    {nR dd : ℕ → ℝ} (hn : ∀ j, 0 < nR j) (hdd : ∀ j, 1 ≤ dd j)
    (hnR : ∀ j, (Fintype.card (O j) : ℝ) = nR j)
    (hPrm : ∀ j o o', StronglyMeasurable[𝒟] (fun ω => Pr j ω o o'))
    (hPrH : ∀ j ω, (Pr j ω).IsHermitian) (hPrI : ∀ j ω, Pr j ω * Pr j ω = Pr j ω)
    (hPrtr : ∀ j ω, (Pr j ω).trace = dd j + Kr)
    (hnumeas : ∀ (j : ℕ) (o : O j), Measurable (nu j o))
    (hvpmeas : ∀ (j : ℕ) (o : O j),
      Measurable fun ω => (Pr j ω *ᵥ fun o' => nu j o' ω) o)
    (hnuint : ∀ j, Integrable (fun ω => l2Norm (fun o => nu j o ω) ^ 2) P)
    (hvpint : ∀ j, Integrable (fun ω =>
      l2Norm (fun o => (Pr j ω *ᵥ fun o' => nu j o' ω) o) ^ 2) P)
    (hmajint : ∀ j, Integrable (fun ω =>
        B ^ 2 * ((maxDegree (c j) (dims j) : ℝ) + 1) / lam j ω
          * (2 * l2Norm (fun o => nu j o ω)
              * l2Norm (fun o => (Pr j ω *ᵥ fun o' => nu j o' ω) o)
            + l2Norm (fun o => (Pr j ω *ᵥ fun o' => nu j o' ω) o) ^ 2)) P)
    (hprod : ∀ j o o', MemLp (nu j o * nu j o') 2 P)
    (hmom : ∀ j o, ∀ᵐ ω ∂P, (P[fun ω => nu j o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (hz : ∀ j o o', ¬ Linked (c j) (dims j) o o' → P[nu j o * nu j o' | 𝒟] =ᵐ[P] 0)
    (hsharing : ∀ (j : ℕ) (ω : Ω), ((maxDegree (c j) (dims j) : ℝ)) ^ 2 / lam j ω
      ≤ 2 * B ^ 2 * Real.sqrt Cm * deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω))
    (hacc : TendstoInMeasure P
      (fun j ω => deltaSeq (nR j) ((maxDegree (c j) (dims j) : ℝ)) (lam j ω) * dd j)
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun j ω =>
        rectFrobNorm (unionMeat (c j) (dims j) (xt j)
            (fun o ω => nu j o ω - (Pr j ω *ᵥ fun o' => nu j o' ω) o) ω
          - unionMeat (c j) (dims j) (xt j) (nu j) ω) / lam j ω) atTop (fun _ => 0) := by
  have hsC : (0 : ℝ) < Real.sqrt Cm := Real.sqrt_pos.mpr hCm
  refine perturb_tendstoInProb_of_accum 𝒟 hm c dims xt nu
    (fun j o ω => (Pr j ω *ᵥ fun o' => nu j o' ω) o) hB hxt hlamM hlam0 hsC hK0 hn hdd
    (a := fun j => Real.sqrt Cm * nR j)
    (b := fun j => Real.sqrt Cm * (dd j + Kr) * ((maxDegree (c j) (dims j) : ℝ) + 1))
    (fun _ => rfl) (fun _ => rfl) hnumeas hvpmeas hnuint hvpint hmajint (fun j => ?_)
    (fun j => ?_) hsharing hacc
  · filter_upwards [condExp_sq_l2Norm_le (𝒟 := 𝒟) (hprod j) (hmom j)] with ω hω
    rw [← hnR j]
    calc (P[fun ω => l2Norm (fun o => nu j o ω) ^ 2 | 𝒟]) ω
        ≤ (Fintype.card (O j) : ℝ) * Real.sqrt Cm := hω
      _ = Real.sqrt Cm * (Fintype.card (O j) : ℝ) := mul_comm _ _
  · filter_upwards [condExp_sq_l2Norm_proj_le (c j) (dims j) hm (hPrm j) (hPrH j) (hPrI j)
      (hPrtr j) (hprod j) (hmom j) (hz j)] with ω hω
    calc (P[fun ω => l2Norm (fun o => (Pr j ω *ᵥ fun o' => nu j o' ω) o) ^ 2 | 𝒟]) ω
        ≤ Real.sqrt Cm * ((maxDegree (c j) (dims j) : ℝ) + 1) * (dd j + Kr) := hω
      _ = Real.sqrt Cm * (dd j + Kr) * ((maxDegree (c j) (dims j) : ℝ) + 1) := by ring

end ConsumerPerturb

/-! ### Examples on a two-point model

`Ω = Bool` under the fair coin with `𝒟 = ⊥`, so `ν` is random and not `𝒟`-measurable. All three
bounds are attained: `Ω_{01} = 1 = C^{1/2}`, `E[‖ν‖² ∣ 𝒟] = 2 = nC^{1/2}`, and
`E[‖Πν‖² ∣ 𝒟] = 2 = C^{1/2}(D_n+1)tr(Π)` at `Π = ½J`. -/

section MomentWitness

open Sharing
open scoped ENNReal

/-- `Ω = Bool` under the fair-coin law, with `𝒟 = ⊥`. -/
noncomputable def wmP : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure wmP := by
  constructor
  rw [wmP, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ MeasurableSet.univ,
    Measure.dirac_apply' _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, smul_eq_mul]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- One fair sign, shared by both observations. -/
def wmNu : Fin 2 → Bool → ℝ := fun _ ω => if ω then 1 else -1

/-- Both observations in one cluster of one maintained dimension. -/
def wmC : Fin 1 → Fin 2 → Fin 1 := fun _ _ => 0

def wmDims : Finset (Fin 1) := Finset.univ

theorem wmNu_mul (o o' : Fin 2) : wmNu o * wmNu o' = fun _ => (1 : ℝ) := by
  funext ω
  cases ω <;> simp [wmNu]

theorem wmNu_pow_four (o : Fin 2) : (fun ω => wmNu o ω ^ 4) = fun _ => (1 : ℝ) := by
  funext ω
  cases ω <;> norm_num [wmNu]

theorem wmLinked (o o' : Fin 2) : Linked wmC wmDims o o' :=
  ⟨0, by simp [wmDims], rfl⟩

theorem wm_prod (o o' : Fin 2) : MemLp (wmNu o * wmNu o') 2 wmP := by
  rw [wmNu_mul]
  exact memLp_const 1

theorem wm_mom (o : Fin 2) :
    ∀ᵐ ω ∂wmP, (wmP[fun ω => wmNu o ω ^ 4 | ⊥]) ω ≤ 1 := by
  rw [wmNu_pow_four o, condExp_const bot_le]
  filter_upwards with ω
  exact le_rfl

theorem wm_nu_nondegenerate : (wmP[wmNu 0 * wmNu 1 | ⊥]) = fun _ => (1 : ℝ) := by
  rw [wmNu_mul, condExp_const bot_le]

/-- Example for `abs_condOmega_le_sqrt`, at which the bound is attained. -/
theorem abs_condOmega_le_sqrt_witness :
    (∀ᵐ ω ∂wmP, |(wmP[wmNu 0 * wmNu 1 | ⊥]) ω| ≤ Real.sqrt 1)
      ∧ (wmP[wmNu 0 * wmNu 1 | ⊥]) = fun _ => (1 : ℝ) := by
  exact ⟨abs_condOmega_le_sqrt wm_prod wm_mom 0 1, wm_nu_nondegenerate⟩

theorem wm_l2Norm_sq : (fun ω => l2Norm (fun o => wmNu o ω) ^ 2) = fun _ => (2 : ℝ) := by
  funext ω
  rw [sq_l2Norm]
  cases ω <;> norm_num [wmNu, Fin.sum_univ_two]

/-- Example for `condExp_sq_l2Norm_le`, at which the bound is attained. -/
theorem condExp_sq_l2Norm_le_witness :
    ((wmP[fun ω => l2Norm (fun o => wmNu o ω) ^ 2 | ⊥])
        ≤ᵐ[wmP] fun _ => (Fintype.card (Fin 2) : ℝ) * Real.sqrt 1)
      ∧ ((wmP[fun ω => l2Norm (fun o => wmNu o ω) ^ 2 | ⊥]) = fun _ => (2 : ℝ))
      ∧ (Fintype.card (Fin 2) : ℝ) * Real.sqrt 1 = 2 := by
  refine ⟨condExp_sq_l2Norm_le wm_prod wm_mom, ?_, by norm_num⟩
  rw [wm_l2Norm_sq, condExp_const bot_le]

/-- `Π = ½J`, the orthogonal projector onto the constant vectors of `ℝ²`. -/
noncomputable def wmPr : Bool → Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ => Matrix.of fun _ _ => (1 / 2 : ℝ)

theorem wmPr_isHermitian (ω : Bool) : (wmPr ω).IsHermitian := by
  ext i j
  simp [wmPr, Matrix.conjTranspose_apply]

theorem wmPr_idem (ω : Bool) : wmPr ω * wmPr ω = wmPr ω := by
  ext i j
  simp [wmPr, Matrix.mul_apply]

theorem wmPr_trace (ω : Bool) : (wmPr ω).trace = 1 := by
  simp [wmPr, Matrix.trace, Matrix.diag]

theorem wm_maxDegree : maxDegree wmC wmDims = 1 := by decide

theorem wm_proj_l2Norm_sq :
    (fun ω => l2Norm (fun o => (wmPr ω *ᵥ fun o' => wmNu o' ω) o) ^ 2) = fun _ => (2 : ℝ) := by
  funext ω
  rw [sq_l2Norm]
  cases ω <;>
    norm_num [wmNu, wmPr, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Example for `condExp_sq_l2Norm_proj_le`, at which the bound is attained. -/
theorem condExp_sq_l2Norm_proj_le_witness :
    ((wmP[fun ω => l2Norm (fun o => (wmPr ω *ᵥ fun o' => wmNu o' ω) o) ^ 2 | ⊥])
        ≤ᵐ[wmP] fun _ => Real.sqrt 1 * ((maxDegree wmC wmDims : ℝ) + 1) * 1)
      ∧ ((wmP[fun ω => l2Norm (fun o => (wmPr ω *ᵥ fun o' => wmNu o' ω) o) ^ 2 | ⊥])
          = fun _ => (2 : ℝ))
      ∧ Real.sqrt 1 * ((maxDegree wmC wmDims : ℝ) + 1) * 1 = 2 := by
  refine ⟨condExp_sq_l2Norm_proj_le wmC wmDims (bot_le) (fun o o' => stronglyMeasurable_const)
    wmPr_isHermitian wmPr_idem wmPr_trace wm_prod wm_mom
    (fun o o' h => absurd (wmLinked o o') h), ?_, ?_⟩
  · rw [wm_proj_l2Norm_sq, condExp_const bot_le]
  · rw [wm_maxDegree]
    norm_num

end MomentWitness

/-! ### An example for the second claim without `hdivint`

Further examples, with non-vanishing centered summands, are in `Multiway/PerturbWitness.lean`
and `Multiway/ClusterShock.lean`. -/

section NoDivWitness

open Sharing

/-- Example for `infeasibleMeat_tendstoInProb_nodiv` on a growing design. -/
theorem infeasibleMeat_tendstoInProb_nodiv_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (j : ℕ) (ω : Unit) =>
        rectFrobNorm (unionMeat (seqC j) (seqDims j)
            (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
          - scoreVar (seqC j) (seqDims j)
            (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
            (fun _ _ _ => (0 : ℝ)) ω) / ((j : ℝ) + 1))
      atTop (fun _ => 0) := by
  have hF : ∀ (j : ℕ) (ω : Unit),
      rectFrobNorm (unionMeat (seqC j) (seqDims j)
          (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
        - scoreVar (seqC j) (seqDims j)
          (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
          (fun _ _ _ => (0 : ℝ)) ω) = 0 := by
    intro j ω
    rw [seq_meat_zero j ω]
    simp [rectFrobNorm, rectFrobSq]
  have hcs : ∀ (j : ℕ) (k l : Fin 1) (p q : Fin (j + 1) × Fin (j + 1)),
      (fun ω : Unit => centeredSummand (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
          (fun _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) k l p ω
        * centeredSummand (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
          (fun _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) k l q ω) = (0 : Unit → ℝ) := by
    intro j k l p q
    funext ω
    simp [centeredSummand]
  refine infeasibleMeat_tendstoInProb_nodiv (⊥ : MeasurableSpace Unit) (P := Measure.dirac ())
    bot_le (O := fun j => Fin (j + 1)) (D := fun _ => Fin 1) (L := fun j => Fin (j + 1))
    (κ := fun _ => Fin 1) seqC seqDims
    (fun _ => fun _ _ _ => (1 : ℝ)) (fun _ => fun _ _ => (0 : ℝ))
    (fun _ => fun _ _ _ => (0 : ℝ)) (B := 1) (Cm := 1) zero_le_one
    (lam := fun j _ => ((j : ℝ) + 1)) (fun _ => measurable_const)
    (fun j _ => by positivity) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    have he : (fun ω : Unit => rectFrobNorm (unionMeat (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
      - scoreVar (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
        (fun _ _ _ => (0 : ℝ)) ω)) = fun _ => (0 : ℝ) := funext (hF j)
    rw [he]
    exact measurable_const
  · intro j
    have he : (fun ω : Unit => frobSq (unionMeat (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ω
      - scoreVar (seqC j) (seqDims j)
        (fun (_ : Fin (j + 1)) (_ : Fin 1) (_ : Unit) => (1 : ℝ))
        (fun _ _ _ => (0 : ℝ)) ω)) = fun _ => (0 : ℝ) := by
      funext ω
      rw [seq_meat_zero j ω]
      simp [frobSq]
    rw [he]
    exact integrable_zero _ _ _
  · intro j k l p _ q _
    rw [hcs j k l p q]
    exact integrable_zero _ _ _
  · intro j k l p _ q _ _
    rw [hcs j k l p q, condExp_zero]
  · intro j k l p q
    rw [hcs j k l p q, condExp_zero]
    filter_upwards with ω
    norm_num
  · have hfun : (fun (j : ℕ) (_ : Unit) => 64 * (Fintype.card (Fin 1) : ℝ) ^ 2 * (1 : ℝ) ^ 4 * 1
        * deltaSeq (Fintype.card (Fin (j + 1)) : ℝ) (maxDegree (seqC j) (seqDims j) : ℝ)
          ((j : ℝ) + 1)) = fun (j : ℕ) (_ : Unit) => 64 * (1 / ((j : ℝ) + 1)) := by
      funext j ω
      rw [seq_maxDegree j, deltaSeq]
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      field_simp
    rw [hfun]
    refine tendstoInMeasure_zero_of_tendsto_const ?_
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (64 : ℝ)

end NoDivWitness

/-! ## Theorem 11 with almost-everywhere matrix hypotheses

When `Ω_n` is built from `E[ν_oν_{o'} ∣ 𝒟]`, its properties hold only almost everywhere. The
statements below carry the hypotheses on `Ω_n` as `∀ᵐ ω` rather than `∀ ω`, with the same
conclusions as `rateAgnostic_a` and `rateAgnostic_b`; the positivity `hc` stays pointwise. -/

section AlmostEverywhere

variable {κ r : Type*} [Fintype κ] [DecidableEq κ] [Fintype r] [DecidableEq r]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `tendstoInMeasure_zero_of_le` with the domination holding only almost everywhere. -/
theorem tendstoInMeasure_zero_of_le_ae {f g : ℕ → Ω → ℝ} (hnn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ f n ω)
    (hle : ∀ n, ∀ᵐ ω ∂P, f n ω ≤ g n ω)
    (hg : TendstoInMeasure P g atTop (fun _ => 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε)
    (fun _ => zero_le) (fun n => measure_mono_ae ?_)
  filter_upwards [hnn n, hle n] with ω h0 h1
  intro hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  rw [abs_of_nonneg h0] at hω
  exact hω.trans (h1.trans (le_abs_self _))

/-- **Theorem 11(a)**, with `Ω_n ≻ 0`, the variance floor and the full column rank of `A` holding
only almost everywhere. The conclusions are those of `rateAgnostic_a`. -/
theorem rateAgnostic_a_ae
    {Om : ℕ → Ω → Matrix κ κ ℝ} (hOm : ∀ n, ∀ᵐ ω ∂P, (Om n ω).PosDef)
    {c : ℕ → Ω → ℝ} (hc : ∀ n ω, 0 < c n ω)
    (hcOm : ∀ n, ∀ᵐ ω ∂P, c n ω • (1 : Matrix κ κ ℝ) ≤ Om n ω)
    {Mt : ℕ → Ω → Matrix κ κ ℝ}
    (hE : TendstoInMeasure P (fun n ω => rectFrobNorm (Mt n ω - Om n ω) / c n ω) atTop
      (fun _ => 0))
    {A : ℕ → Ω → Matrix κ r ℝ} (hA : ∀ n, ∀ᵐ ω ∂P, Function.Injective (A n ω).mulVec) :
    TendstoInMeasure P
        (fun n ω => rectFrobNorm ((sqrtPD (Om n ω))⁻¹ * (Mt n ω - Om n ω) * (sqrtPD (Om n ω))⁻¹))
        atTop (fun _ => 0)
      ∧ TendstoInMeasure P
        (fun n ω => rectFrobNorm ((sqrtPD ((A n ω)ᵀ * Om n ω * A n ω))⁻¹
            * ((A n ω)ᵀ * Mt n ω * A n ω) * (sqrtPD ((A n ω)ᵀ * Om n ω * A n ω))⁻¹ - 1))
        atTop (fun _ => 0) := by
  constructor
  · refine tendstoInMeasure_zero_of_le_ae
      (fun _ => Filter.Eventually.of_forall fun _ => rectFrobNorm_nonneg _) (fun n => ?_) hE
    filter_upwards [hOm n, hcOm n] with ω h1 h2
    exact rectFrobNorm_standardized_le h1 (hc n ω) h2 (Mt n ω)
  · refine tendstoInMeasure_zero_of_le_ae
      (fun _ => Filter.Eventually.of_forall fun _ => rectFrobNorm_nonneg _) (fun n => ?_) hE
    filter_upwards [hOm n, hcOm n, hA n] with ω h1 h2 h3
    exact rectFrobNorm_ratio_sub_one_le h1 h3 (hc n ω) h2 (Mt n ω)

/-- **Theorem 11(b)**, with the four matrix hypotheses holding only almost everywhere. The
conclusions are those of `rateAgnostic_b`. -/
theorem rateAgnostic_b_ae [IsProbabilityMeasure P]
    {Om : ℕ → Ω → Matrix κ κ ℝ} (hOm : ∀ n, ∀ᵐ ω ∂P, (Om n ω).PosDef)
    {cn : ℕ → Ω → ℝ} (hc : ∀ n ω, 0 < cn n ω)
    (hcOm : ∀ n, ∀ᵐ ω ∂P, cn n ω • (1 : Matrix κ κ ℝ) ≤ Om n ω)
    {Mt Mh : ℕ → Ω → Matrix κ κ ℝ}
    (hE : TendstoInMeasure P (fun n ω => rectFrobNorm (Mt n ω - Om n ω) / cn n ω) atTop
      (fun _ => 0))
    (hperturb : TendstoInMeasure P (fun n ω => rectFrobNorm (Mh n ω - Mt n ω) / cn n ω) atTop
      (fun _ => 0))
    {A : ℕ → Ω → Matrix κ r ℝ} (hA : ∀ n, ∀ᵐ ω ∂P, Function.Injective (A n ω).mulVec)
    (hHerm : ∀ n, ∀ᵐ ω ∂P, ((A n ω)ᵀ * Mh n ω * A n ω).IsHermitian) :
    TendstoInMeasure P
        (fun n ω => rectFrobNorm ((sqrtPD (Om n ω))⁻¹ * (Mh n ω - Om n ω) * (sqrtPD (Om n ω))⁻¹))
        atTop (fun _ => 0)
      ∧ TendstoInMeasure P
        (fun n ω => rectFrobNorm ((sqrtPD ((A n ω)ᵀ * Om n ω * A n ω))⁻¹
            * ((A n ω)ᵀ * Mh n ω * A n ω) * (sqrtPD ((A n ω)ᵀ * Om n ω * A n ω))⁻¹ - 1))
        atTop (fun _ => 0)
      ∧ Tendsto (fun n => P {ω | ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}) atTop (𝓝 1) := by
  have hEh : TendstoInMeasure P (fun n ω => rectFrobNorm (Mh n ω - Om n ω) / cn n ω) atTop
      (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_le_ae
      (fun n => Filter.Eventually.of_forall fun ω =>
        div_nonneg (rectFrobNorm_nonneg _) (hc n ω).le)
      (fun n => Filter.Eventually.of_forall fun ω => ?_)
      (tendstoInMeasure_zero_add hperturb hE)
    rw [← add_div]
    exact div_le_div_of_nonneg_right (rectFrobNorm_sub_le _ (Mt n ω) _) (hc n ω).le
  obtain ⟨h1, h2⟩ := rateAgnostic_a_ae hOm hc hcOm hEh hA
  refine ⟨h1, h2, ?_⟩
  obtain ⟨δ, hδ, hkey⟩ := Wald.exists_delta_studentizer_ratio (ι := r) one_pos
  rw [tendstoInMeasure_iff_dist] at h2
  have hbad : Tendsto (fun n => P {ω | ¬ ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h2 δ hδ)
      (fun _ => zero_le) (fun n => measure_mono_ae ?_)
    filter_upwards [hOm n, hA n, hHerm n] with ω g1 g2 g3
    intro hω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg (rectFrobNorm_nonneg _)] at hω ⊢
    by_contra hcon
    rw [not_le] at hcon
    exact hω (hkey ((A n ω)ᵀ * Om n ω * A n ω) ((A n ω)ᵀ * Mh n ω * A n ω)
      (posDef_restricted g1 g2) g3 hcon).1
  have hlow : Tendsto (fun n => 1 - P {ω | ¬ ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}) atTop
      (𝓝 1) := by
    have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) hbad
      (Or.inl ENNReal.one_ne_top)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun _ => prob_le_one)
  refine tsub_le_iff_right.mpr ?_
  have hu : (Set.univ : Set Ω) = {ω | ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}
      ∪ {ω | ¬ ((A n ω)ᵀ * Mh n ω * A n ω).PosDef} := by
    ext ω; simp [em]
  have h1' : P (Set.univ : Set Ω) ≤ P {ω | ((A n ω)ᵀ * Mh n ω * A n ω).PosDef}
      + P {ω | ¬ ((A n ω)ᵀ * Mh n ω * A n ω).PosDef} := by
    rw [hu]; exact measure_union_le _ _
  simpa using h1'

end AlmostEverywhere

end RateAgnostic
end Multiway
