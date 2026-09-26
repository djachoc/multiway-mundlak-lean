import Multiway.Sqrt
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Restricted standardization

This file formalizes Lemma SM.B.12 of the paper (restricted standardization): if `Ω* ≻ 0` is
`K × K` and `A ∈ ℝ^{K×r}` has full column rank, then `A'Ω*A ≻ 0`, and
`G := A(A'Ω*A)^{-1/2}` satisfies `G'Ω*G = I_r` and `‖G‖² ≤ λ_min(Ω*)^{-1}`.

The bound on `‖G‖` is stated for any `c > 0` with `c • I ⪯ Ω*`, in the form `‖G‖² ≤ c⁻¹`;
taking `c = λ_min(Ω*)` recovers the eigenvalue form. Full column rank is expressed as
injectivity of `b ↦ Ab`, and `‖·‖` is the l2 operator norm.

## Main results

* `restrictedStd`: the standardizer `G = A(A'Ω*A)^{-1/2}`.
* `posDef_restricted`: `A'Ω*A` is positive definite.
* `transpose_mul_mul_restrictedStd`: `G'Ω*G = I_r`.
* `sq_l2_opNorm_restrictedStd_le`: `‖G‖² ≤ c⁻¹`.
-/

namespace Multiway

open scoped MatrixOrder Matrix.Norms.L2Operator

open Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-! ### Preliminaries -/

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
/-- Over `ℝ` the conjugate transpose is the transpose. -/
theorem conjTranspose_eq_transpose (A : Matrix m n ℝ) : Aᴴ = Aᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]


omit [DecidableEq m] in
/-- An l2 operator norm bound from a bound on vectors, via
`ContinuousLinearMap.opNorm_le_bound` and `Matrix.l2_opNorm_def`. -/
theorem l2_opNorm_le_of_mulVec_le {G : Matrix m n ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : n → ℝ, ‖(EuclideanSpace.equiv m ℝ).symm (G *ᵥ x)‖
      ≤ C * ‖(EuclideanSpace.equiv n ℝ).symm x‖) : ‖G‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC fun x => h x

/-! ### The restricted standardizer -/

/-- The restricted standardizer `G := A(A'Ω*A)^{-1/2}`. -/
noncomputable def restrictedStd (Om : Matrix m m ℝ) (A : Matrix m n ℝ) : Matrix m n ℝ :=
  A * (sqrtPD (Aᵀ * Om * A))⁻¹

omit [DecidableEq m] [DecidableEq n] in
/-- **Lemma SM.B.12, first part.** If `Ω* ≻ 0` and `A` has full column rank, then
`A'Ω*A ≻ 0`. -/
theorem posDef_restricted {Om : Matrix m m ℝ} (hOm : Om.PosDef) {A : Matrix m n ℝ}
    (hA : Function.Injective A.mulVec) : (Aᵀ * Om * A).PosDef := by
  have h := hOm.conjTranspose_mul_mul_same (B := A) hA
  rwa [conjTranspose_eq_transpose] at h

omit [DecidableEq m] in
/-- `G'Ω*G = I_r`. -/
theorem transpose_mul_mul_restrictedStd {Om : Matrix m m ℝ} (hOm : Om.PosDef)
    {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) :
    (restrictedStd Om A)ᵀ * Om * restrictedStd Om A = 1 := by
  set V := Aᵀ * Om * A with hVdef
  have hV : V.PosDef := posDef_restricted hOm hA
  set S := sqrtPD V with hSdef
  have hSi : ((S⁻¹)ᵀ : Matrix n n ℝ) = S⁻¹ := transpose_eq_self (sqrtPD_posDef hV).inv.isHermitian
  have hGt : (restrictedStd Om A)ᵀ = S⁻¹ * Aᵀ := by
    rw [restrictedStd, Matrix.transpose_mul, hSi]
  rw [hGt, restrictedStd]
  have e : S⁻¹ * Aᵀ * Om * (A * S⁻¹) = S⁻¹ * (Aᵀ * Om * A) * S⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e, ← hVdef]
  exact inv_conj_eq_one (sqrtPD_mul_self hV.posSemidef) (sqrtPD_inv_mul hV) (sqrtPD_mul_inv hV)

/-- **Lemma SM.B.12, second part.** `‖A(A'Ω*A)^{-1/2}‖² ≤ c⁻¹` for any `c > 0` with
`c • I ⪯ Ω*`. -/
theorem sq_l2_opNorm_restrictedStd_le {Om : Matrix m m ℝ} (hOm : Om.PosDef)
    {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) {c : ℝ} (hc : 0 < c)
    (hcOm : c • (1 : Matrix m m ℝ) ≤ Om) : ‖restrictedStd Om A‖ ^ 2 ≤ c⁻¹ := by
  have hci : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
  set G := restrictedStd Om A with hGdef
  have hGOG : Gᵀ * Om * G = 1 := transpose_mul_mul_restrictedStd hOm hA
  -- `c‖Gb‖² ≤ (Gb)'Ω*(Gb) = b'G'Ω*Gb = ‖b‖²`
  have key : ∀ b : n → ℝ, (G *ᵥ b) ⬝ᵥ (G *ᵥ b) ≤ c⁻¹ * (b ⬝ᵥ b) := by
    intro b
    have h1 := le_dotProduct_mulVec_of_smul_one_le hcOm (G *ᵥ b)
    rw [dotProduct_mulVec_conj, hGOG, Matrix.one_mulVec] at h1
    rw [← le_div_iff₀' hc] at h1
    rwa [div_eq_inv_mul] at h1
  -- the same inequality between Euclidean norms
  have hnorm : ∀ b : n → ℝ, ‖(EuclideanSpace.equiv m ℝ).symm (G *ᵥ b)‖
      ≤ Real.sqrt c⁻¹ * ‖(EuclideanSpace.equiv n ℝ).symm b‖ := by
    intro b
    have h2 := key b
    rw [dot_self_eq, dot_self_eq] at h2
    have h3 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hci.le, Real.sqrt_sq (norm_nonneg _)] at h3
  have hG : ‖G‖ ≤ Real.sqrt c⁻¹ :=
    l2_opNorm_le_of_mulVec_le (Real.sqrt_nonneg _) hnorm
  calc ‖G‖ ^ 2 ≤ Real.sqrt c⁻¹ ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hG 2
    _ = c⁻¹ := Real.sq_sqrt hci.le

end Multiway
