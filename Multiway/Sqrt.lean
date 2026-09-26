import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Chebyshev

/-!
# Matrix square roots

This file formalizes Lemma SM.B.14 of the paper (matrix square roots): for symmetric positive
definite `Σ`, `Σ̂` with `𝒦 := Σ^{-1/2} Σ̂ Σ^{-1/2}` and `ϑ := ‖𝒦 - I_r‖ ≤ 1/2`, the matrix
`T := Σ̂^{-1/2} Σ^{1/2}` satisfies `‖T - I_r‖_F ≤ (3rϑ)^{1/2}`. It also collects the Loewner-order,
trace and Frobenius-norm facts about real matrices used elsewhere in the library.

## Notation

* `sqrtPD A` is the positive definite square root `A^{1/2}`, defined through `CFC.sqrt`.
* `‖·‖` is the l2 operator (spectral) norm, `open scoped Matrix.Norms.L2Operator`.
* `frobNorm M` is the Frobenius norm `‖M‖_F`, defined entrywise so that it can be used
  alongside the spectral norm.

## Main results

* `frobSq_sqrt_sub_one_le`: `‖T - I‖_F² ≤ 3rt` for any bound `t ≤ 1/2` on `‖𝒦 - I‖`.
* `frobNorm_sqrt_sub_one_le`: Lemma SM.B.14.
* `inv_le_of_smul_one_le`, `smul_one_le_inv_of_le_smul_one`: inversion reverses the Loewner
  order against a scalar matrix.
* `frobNorm_add_le`: the triangle inequality for `frobNorm`.
-/

namespace Multiway

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The positive definite square root -/

/-- `A^{1/2}`: the positive definite square root of a positive definite `A`, defined as
`CFC.sqrt` through the continuous functional calculus on real matrices. -/
noncomputable def sqrtPD (A : Matrix n n ℝ) : Matrix n n ℝ := CFC.sqrt A

/-- `A^{1/2}` is positive semidefinite. -/
theorem sqrtPD_posSemidef {A : Matrix n n ℝ} : (sqrtPD A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)

/-- `A^{1/2} A^{1/2} = A`. -/
theorem sqrtPD_mul_self {A : Matrix n n ℝ} (hA : A.PosSemidef) : sqrtPD A * sqrtPD A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

/-- `A^{1/2}` is positive definite when `A` is. -/
theorem sqrtPD_posDef {A : Matrix n n ℝ} (hA : A.PosDef) : (sqrtPD A).PosDef := by
  rw [sqrtPD_posSemidef.posDef_iff_isUnit]
  have h2 : IsUnit A := hA.isUnit
  rw [← sqrtPD_mul_self hA.posSemidef] at h2
  exact isUnit_of_mul_isUnit_left h2

/-- A positive definite matrix is nonsingular. -/
theorem isUnit_det_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef) : IsUnit A.det :=
  isUnit_iff_ne_zero.mpr hA.det_pos.ne'

/-- `A^{1/2} A^{-1/2} = I`. -/
theorem sqrtPD_mul_inv {A : Matrix n n ℝ} (hA : A.PosDef) : sqrtPD A * (sqrtPD A)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef (sqrtPD_posDef hA))

/-- `A^{-1/2} A^{1/2} = I`. -/
theorem sqrtPD_inv_mul {A : Matrix n n ℝ} (hA : A.PosDef) : (sqrtPD A)⁻¹ * sqrtPD A = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef (sqrtPD_posDef hA))

/-- `A^{-1/2}` is positive definite. -/
theorem inv_sqrtPD_posDef {A : Matrix n n ℝ} (hA : A.PosDef) : ((sqrtPD A)⁻¹).PosDef :=
  (sqrtPD_posDef hA).inv

/-- `A^{-1/2} A^{-1/2} = A^{-1}`. -/
theorem inv_sqrtPD_mul_self {A : Matrix n n ℝ} (hA : A.PosDef) :
    (sqrtPD A)⁻¹ * (sqrtPD A)⁻¹ = A⁻¹ := by
  rw [← Matrix.mul_inv_rev, sqrtPD_mul_self hA.posSemidef]

omit [Fintype n] [DecidableEq n] in
/-- Over `ℝ`, Hermitian means symmetric. -/
theorem transpose_eq_self {M : Matrix n n ℝ} (hM : M.IsHermitian) : Mᵀ = M := by
  ext i j
  have := congrFun (congrFun hM i) j
  simpa [Matrix.conjTranspose_apply] using this

section Algebra

variable {S A : Matrix n n ℝ}

/-- `S^{-1} (S S) S^{-1} = I`. -/
theorem inv_conj_eq_one (h : S * S = A) (hl : S⁻¹ * S = 1) (hr : S * S⁻¹ = 1) :
    S⁻¹ * A * S⁻¹ = 1 := by
  have e : S⁻¹ * A * S⁻¹ = (S⁻¹ * S) * (S * S⁻¹) := by rw [← h]; simp [Matrix.mul_assoc]
  rw [e, hl, hr, Matrix.one_mul]

/-- `S^{-1} (A A) S^{-1} = A` when `S S = A`. -/
theorem inv_conj_sq (h : S * S = A) (hl : S⁻¹ * S = 1) (hr : S * S⁻¹ = 1) :
    S⁻¹ * (A * A) * S⁻¹ = A := by
  have e : S⁻¹ * (A * A) * S⁻¹ = (S⁻¹ * S) * ((S * S) * (S * S⁻¹)) := by
    rw [← h]; simp [Matrix.mul_assoc]
  rw [e, hl, hr, Matrix.one_mul, Matrix.mul_one, h]

end Algebra

/-! ### The Loewner order -/

omit [Fintype n] [DecidableEq n] in
/-- If `A` is positive definite and `A ⪯ B`, then `B` is positive definite. -/
theorem posDef_of_le {A B : Matrix n n ℝ} (hA : A.PosDef) (hAB : A ≤ B) : B.PosDef := by
  have h := Matrix.le_iff.mp hAB
  have e : B = A + (B - A) := by abel
  rw [e]
  exact hA.add_posSemidef h

omit [Fintype n] [DecidableEq n] in
/-- Scalar multiplication is monotone for the Loewner order: `0 ≤ a` and `A ⪯ B` give
`aA ⪯ aB`. -/
theorem loewner_smul_le_smul {A B : Matrix n n ℝ} {a : ℝ} (ha : 0 ≤ a) (h : A ≤ B) :
    a • A ≤ a • B := by
  rw [Matrix.le_iff] at h ⊢
  have e : a • B - a • A = a • (B - A) := by rw [smul_sub]
  rw [e]
  exact h.smul ha

/-! #### Congruence by rectangular matrices -/

omit [DecidableEq n] in
/-- Congruence preserves the Loewner order, with `S` rectangular: `A ⪯ B` gives
`SᴴAS ⪯ SᴴBS`, a bound between `m × m` matrices. -/
theorem conjTranspose_mul_mul_le {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix n n ℝ} (h : A ≤ B) (S : Matrix n m ℝ) :
    Sᴴ * A * S ≤ Sᴴ * B * S := by
  rw [Matrix.le_iff]
  have e : Sᴴ * B * S - Sᴴ * A * S = Sᴴ * (B - A) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [e]
  exact (Matrix.le_iff.mp h).conjTranspose_mul_mul_same S

omit [DecidableEq n] in
/-- Congruence in the form `A ⪯ B ⟹ S A Sᵀ ⪯ S B Sᵀ` for `S : Matrix m n ℝ`; over `ℝ`
this is `conjTranspose_mul_mul_le` at `Sᵀ`. -/
theorem mul_mul_transpose_le {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix n n ℝ} (h : A ≤ B) (S : Matrix m n ℝ) :
    S * A * Sᵀ ≤ S * B * Sᵀ := by
  have hS : (Sᵀ)ᴴ = S := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  simpa [hS] using conjTranspose_mul_mul_le h Sᵀ

/-- If `a I ⪯ M` with `a > 0` and `M` positive definite, then `M^{-1} ⪯ a^{-1} I`. The proof
is the identity `a^{-1}I - M^{-1} = a^{-1} M^{-1/2}(M - aI)M^{-1/2}`, whose right-hand side is
a congruence of a positive semidefinite matrix. Mathlib's `CStarAlgebra.inv_le_inv` states this
for `ℂ`-algebras. -/
theorem inv_le_of_smul_one_le {M : Matrix n n ℝ} (hM : M.PosDef) {a : ℝ} (ha : 0 < a)
    (h : a • (1 : Matrix n n ℝ) ≤ M) : M⁻¹ ≤ a⁻¹ • (1 : Matrix n n ℝ) := by
  set S := (sqrtPD M)⁻¹ with hSdef
  have hSh : Sᴴ = S := (inv_sqrtPD_posDef hM).isHermitian.eq
  have hSS : S * S = M⁻¹ := inv_sqrtPD_mul_self hM
  have hSMS : S * M * S = 1 :=
    inv_conj_eq_one (sqrtPD_mul_self hM.posSemidef) (sqrtPD_inv_mul hM) (sqrtPD_mul_inv hM)
  have key : (Sᴴ * (M - a • (1 : Matrix n n ℝ)) * S).PosSemidef :=
    (Matrix.le_iff.mp h).conjTranspose_mul_mul_same S
  rw [hSh] at key
  have e : S * (M - a • (1 : Matrix n n ℝ)) * S = 1 - a • M⁻¹ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hSMS, hSS]
  rw [e] at key
  rw [Matrix.le_iff]
  have e2 : a⁻¹ • (1 : Matrix n n ℝ) - M⁻¹ = a⁻¹ • ((1 : Matrix n n ℝ) - a • M⁻¹) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [e2]
  exact key.smul (le_of_lt (inv_pos.mpr ha))

/-- The other half of operator inversion reversing the Loewner order: if `M ⪯ a I` with `a > 0`
and `M` positive definite, then `a^{-1} I ⪯ M^{-1}`. The proof is the same identity
`M^{-1} - a^{-1}I = a^{-1} M^{-1/2}(aI - M)M^{-1/2}` read the other way. -/
theorem smul_one_le_inv_of_le_smul_one {M : Matrix n n ℝ} (hM : M.PosDef) {a : ℝ} (ha : 0 < a)
    (h : M ≤ a • (1 : Matrix n n ℝ)) : a⁻¹ • (1 : Matrix n n ℝ) ≤ M⁻¹ := by
  set S := (sqrtPD M)⁻¹ with hSdef
  have hSh : Sᴴ = S := (inv_sqrtPD_posDef hM).isHermitian.eq
  have hSS : S * S = M⁻¹ := inv_sqrtPD_mul_self hM
  have hSMS : S * M * S = 1 :=
    inv_conj_eq_one (sqrtPD_mul_self hM.posSemidef) (sqrtPD_inv_mul hM) (sqrtPD_mul_inv hM)
  have key : (Sᴴ * (a • (1 : Matrix n n ℝ) - M) * S).PosSemidef :=
    (Matrix.le_iff.mp h).conjTranspose_mul_mul_same S
  rw [hSh] at key
  have e : S * (a • (1 : Matrix n n ℝ) - M) * S = a • M⁻¹ - 1 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hSMS, hSS]
  rw [e] at key
  rw [Matrix.le_iff]
  have e2 : M⁻¹ - a⁻¹ • (1 : Matrix n n ℝ) = a⁻¹ • (a • M⁻¹ - (1 : Matrix n n ℝ)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [e2]
  exact key.smul (le_of_lt (inv_pos.mpr ha))

/-- Operator arithmetic–geometric mean inequality: `(2c) I ⪯ A + c² A^{-1}` for every real
`c`. The proof is `A + c²A^{-1} - (2c)I = A^{-1/2}(A - cI)'(A - cI)A^{-1/2}`. -/
theorem two_mul_smul_one_le {A : Matrix n n ℝ} (hA : A.PosDef) (c : ℝ) :
    (2 * c) • (1 : Matrix n n ℝ) ≤ A + c ^ 2 • A⁻¹ := by
  set S := (sqrtPD A)⁻¹ with hSdef
  have hSh : Sᴴ = S := (inv_sqrtPD_posDef hA).isHermitian.eq
  have hSS : S * S = A⁻¹ := inv_sqrtPD_mul_self hA
  have hSAS : S * A * S = 1 :=
    inv_conj_eq_one (sqrtPD_mul_self hA.posSemidef) (sqrtPD_inv_mul hA) (sqrtPD_mul_inv hA)
  have hSA2S : S * (A * A) * S = A :=
    inv_conj_sq (sqrtPD_mul_self hA.posSemidef) (sqrtPD_inv_mul hA) (sqrtPD_mul_inv hA)
  set D := A - c • (1 : Matrix n n ℝ) with hDdef
  have hDh : Dᴴ = D := by
    rw [hDdef, Matrix.conjTranspose_sub, hA.isHermitian.eq]
    simp
  have key : (Sᴴ * (Dᴴ * D) * S).PosSemidef :=
    (Matrix.posSemidef_conjTranspose_mul_self D).conjTranspose_mul_mul_same S
  rw [hSh, hDh] at key
  have hDD : D * D = A * A - (2 * c) • A + c ^ 2 • (1 : Matrix n n ℝ) := by
    rw [hDdef]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
    module
  have e : S * (D * D) * S = A + c ^ 2 • A⁻¹ - (2 * c) • (1 : Matrix n n ℝ) := by
    rw [hDD]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hSA2S, hSAS, hSS]
    module
  rw [e] at key
  exact Matrix.le_iff.mpr key

/-! ### The Loewner order as a quadratic-form inequality -/

/-- `b I ⪯ H` says `b‖x‖² ≤ x'Hx` for every `x`. -/
theorem le_dotProduct_mulVec_of_smul_one_le {H : Matrix n n ℝ} {b : ℝ}
    (h : b • (1 : Matrix n n ℝ) ≤ H) (x : n → ℝ) : b * (x ⬝ᵥ x) ≤ x ⬝ᵥ (H *ᵥ x) := by
  have hpsd := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, star_trivial] at hpsd
  linarith

/-- `H ⪯ b I` says `x'Hx ≤ b‖x‖²` for every `x`. -/
theorem dotProduct_mulVec_le_of_le_smul_one {H : Matrix n n ℝ} {b : ℝ}
    (h : H ≤ b • (1 : Matrix n n ℝ)) (x : n → ℝ) : x ⬝ᵥ (H *ᵥ x) ≤ b * (x ⬝ᵥ x) := by
  have hpsd := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, star_trivial] at hpsd
  linarith

omit [DecidableEq n] in
/-- `x'(T'T)x = ‖Tx‖²`. -/
theorem dotProduct_transpose_mul_self (T : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((Tᵀ * T) *ᵥ x) = (T *ᵥ x) ⬝ᵥ (T *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_transpose]

omit [DecidableEq n] in
/-- `(Gb)'Ω(Gb) = b'(G'ΩG)b` for a rectangular `G : Matrix m n ℝ` and an arbitrary square
`Ω : Matrix m m ℝ`. -/
theorem dotProduct_mulVec_conj {m : Type*} [Fintype m]
    (G : Matrix m n ℝ) (Om : Matrix m m ℝ) (b : n → ℝ) :
    (G *ᵥ b) ⬝ᵥ (Om *ᵥ (G *ᵥ b)) = b ⬝ᵥ ((Gᵀ * Om * G) *ᵥ b) := by
  have e : (Gᵀ * Om * G) *ᵥ b = Gᵀ *ᵥ (Om *ᵥ (G *ᵥ b)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [e]
  conv_rhs => rw [dotProduct_mulVec, Matrix.vecMul_transpose]

omit [DecidableEq n] in
/-- `v'(X'X)v = ‖Xv‖²` for a rectangular `X`. This is the case `Ω = I` of
`dotProduct_mulVec_conj`, stated without a `DecidableEq m` instance. -/
theorem dotProduct_transpose_mul_self_rect {m : Type*} [Fintype m]
    (X : Matrix m n ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((Xᵀ * X) *ᵥ v) = (X *ᵥ v) ⬝ᵥ (X *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_transpose]

/-- An eigenvector of a Hermitian matrix, read as a plain function, is nonzero. -/
theorem eigenvectorBasis_ne_zero {H : Matrix n n ℝ} (hH : H.IsHermitian) (i : n) :
    (⇑(hH.eigenvectorBasis i) : n → ℝ) ≠ 0 := by
  simpa using hH.eigenvectorBasis.orthonormal.ne_zero i

/-- If `H ⪯ b I`, then every eigenvalue satisfies `λ_i(H) ≤ b`. -/
theorem eigenvalues_le_of_le_smul_one {H : Matrix n n ℝ} (hH : H.IsHermitian) {b : ℝ}
    (h : H ≤ b • (1 : Matrix n n ℝ)) (i : n) : hH.eigenvalues i ≤ b := by
  set v : n → ℝ := ⇑(hH.eigenvectorBasis i) with hvdef
  have hvne : v ≠ 0 := by rw [hvdef]; exact eigenvectorBasis_ne_zero hH i
  have hvv : 0 < v ⬝ᵥ v := by simpa using Matrix.dotProduct_star_self_pos_iff.mpr hvne
  have hmul : H *ᵥ v = hH.eigenvalues i • v := hH.mulVec_eigenvectorBasis i
  have h1 := dotProduct_mulVec_le_of_le_smul_one h v
  rw [hmul, dotProduct_smul, smul_eq_mul] at h1
  nlinarith

/-! ### Traces -/

omit [DecidableEq n] in
/-- The trace is monotone for the Loewner order. -/
theorem trace_le_of_le {A B : Matrix n n ℝ} (h : A ≤ B) : A.trace ≤ B.trace := by
  have := (Matrix.le_iff.mp h).trace_nonneg
  rw [Matrix.trace_sub] at this
  linarith

/-- `tr(c I) = c r`. -/
theorem trace_smul_one (c : ℝ) : ((c • (1 : Matrix n n ℝ)).trace) = c * Fintype.card n := by
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]

/-! ### The Frobenius norm -/

/-- The squared Frobenius norm `‖M‖_F²`, written out entrywise. -/
def frobSq (M : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

/-- The Frobenius norm `‖M‖_F`. -/
noncomputable def frobNorm (M : Matrix n n ℝ) : ℝ := Real.sqrt (frobSq M)

omit [DecidableEq n] in
/-- `‖M‖_F² = tr(M'M)`. -/
theorem frobSq_eq_trace (M : Matrix n n ℝ) : frobSq M = (Mᵀ * M).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [frobSq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq n] in
/-- `tr(N²) ≤ ‖N‖_F²` for a real square matrix, the gap being `‖N - N'‖_F²/2`. -/
theorem trace_mul_self_le_frobSq (N : Matrix n n ℝ) : (N * N).trace ≤ frobSq N := by
  have hL : (N * N).trace = ∑ i, ∑ j, N i j * N j i := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]
  have hcomm : ∑ i, ∑ j, N j i ^ 2 = frobSq N := by
    rw [frobSq, Finset.sum_comm]
  rw [hL]
  have step : ∑ i, ∑ j, N i j * N j i
      ≤ ∑ i, ∑ j, ((N i j ^ 2 + N j i ^ 2) * (1 / 2 : ℝ)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    nlinarith [sq_nonneg (N i j - N j i)]
  refine step.trans_eq ?_
  simp only [← Finset.sum_mul, Finset.sum_add_distrib]
  rw [hcomm, frobSq]
  ring

omit [DecidableEq n] in
/-- Cauchy–Schwarz on the diagonal: `tr(M)² ≤ r ‖M‖_F²`. -/
theorem sq_trace_le (M : Matrix n n ℝ) : M.trace ^ 2 ≤ Fintype.card n * frobSq M := by
  have h1 : M.trace ^ 2 ≤ (Fintype.card n : ℝ) * ∑ i, M i i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset n)) (f := fun i => M i i)
    simpa [Matrix.trace, Matrix.diag_apply] using this
  refine h1.trans ?_
  have h2 : ∑ i, M i i ^ 2 ≤ frobSq M := by
    rw [frobSq]
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.single_le_sum (f := fun j => M i j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)

/-- `‖M - I‖_F² = ‖M‖_F² - 2 tr(M) + r`. -/
theorem frobSq_sub_one (M : Matrix n n ℝ) :
    frobSq (M - 1) = frobSq M - 2 * M.trace + Fintype.card n := by
  have hone : ∀ i j : n, (1 : Matrix n n ℝ) i j = if i = j then 1 else 0 := fun i j => rfl
  simp only [frobSq, Matrix.sub_apply, hone]
  have expand : ∀ i : n, ∑ j, (M i j - (if i = j then (1:ℝ) else 0)) ^ 2
      = (∑ j, M i j ^ 2) - 2 * M i i + 1 := by
    intro i
    have h : ∀ j : n, (M i j - (if i = j then (1:ℝ) else 0)) ^ 2
        = M i j ^ 2 - 2 * (if i = j then M i j else 0) + (if i = j then (1:ℝ) else 0) := by
      intro j
      by_cases hij : i = j
      · simp [hij]; ring
      · simp [hij]
    rw [Finset.sum_congr rfl fun j _ => h j]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  rw [Finset.sum_congr rfl fun i _ => expand i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Matrix.trace, Matrix.diag_apply]

/-! ### The spectral norm bounds the Loewner order -/

omit [DecidableEq n] in
/-- The dot product of a real vector with itself is its squared Euclidean norm. -/
theorem dot_self_eq (x : n → ℝ) : x ⬝ᵥ x = ‖(EuclideanSpace.equiv n ℝ).symm x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Cauchy–Schwarz for the spectral norm: `x'Hx ≤ ‖H‖ ‖x‖²`. -/
theorem dot_mulVec_le (H : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (H *ᵥ x) ≤ ‖H‖ * ‖(EuclideanSpace.equiv n ℝ).symm x‖ ^ 2 := by
  set y : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm x with hy
  have h1 : x ⬝ᵥ (H *ᵥ x) = ⟪y, (EuclideanSpace.equiv n ℝ).symm (H *ᵥ x)⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [hy, dotProduct_comm]
  rw [h1]
  calc ⟪y, (EuclideanSpace.equiv n ℝ).symm (H *ᵥ x)⟫
      ≤ ‖y‖ * ‖(EuclideanSpace.equiv n ℝ).symm (H *ᵥ x)‖ := real_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖H‖ * ‖y‖) := by
        gcongr
        exact Matrix.l2_opNorm_mulVec H y
    _ = ‖H‖ * ‖y‖ ^ 2 := by ring

/-- The spectral norm bounds the Loewner order: a Hermitian `H` with `‖H‖ ≤ b` satisfies
`H ⪯ b I`. -/
theorem le_smul_one_of_norm_le {H : Matrix n n ℝ} (hH : H.IsHermitian) {b : ℝ}
    (hb : ‖H‖ ≤ b) : H ≤ b • (1 : Matrix n n ℝ) := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.sub ?_ hH
    simp [Matrix.IsHermitian]
  · intro x
    have hmv : (b • (1 : Matrix n n ℝ)) *ᵥ x = b • x := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 : star x ⬝ᵥ ((b • (1 : Matrix n n ℝ) - H) *ᵥ x)
        = b * (x ⬝ᵥ x) - x ⬝ᵥ (H *ᵥ x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, hmv, dotProduct_smul, smul_eq_mul,
        star_trivial]
    rw [h1, dot_self_eq]
    have h2 := dot_mulVec_le H x
    have h3 : ‖H‖ * ‖(EuclideanSpace.equiv n ℝ).symm x‖ ^ 2
        ≤ b * ‖(EuclideanSpace.equiv n ℝ).symm x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    linarith

/-! ### Eigenvalues of a matrix similar to a symmetric positive definite one -/

/-- Suppose `T = S^{-1} W S` with `W` symmetric positive definite, so that the eigenvalues
`μ_i` of `T` are those of `W`. If `b I ⪯ T'T`, that is `‖Tv‖ ≥ √b ‖v‖` for every `v`, then every
`μ_i` is at least `√b`. -/
theorem sqrt_le_eigenvalues_of_similar {T S W : Matrix n n ℝ}
    (hSinj : Function.Injective (S⁻¹).mulVec) (hSmi : S * S⁻¹ = 1) (hW : W.PosDef)
    (hsim : S⁻¹ * W * S = T) {b : ℝ}
    (hTT : b • (1 : Matrix n n ℝ) ≤ Tᵀ * T) (i : n) :
    Real.sqrt b ≤ hW.1.eigenvalues i := by
  have hmupos : 0 < hW.1.eigenvalues i := hW.eigenvalues_pos i
  set v : n → ℝ := ⇑(hW.1.eigenvectorBasis i) with hvdef
  have hvne : v ≠ 0 := by rw [hvdef]; exact eigenvectorBasis_ne_zero hW.1 i
  have hWv : W *ᵥ v = hW.1.eigenvalues i • v := hW.1.mulVec_eigenvectorBasis i
  -- `S⁻¹ v` is an eigenvector of `T` for the same eigenvalue, and it is nonzero
  have hune : (S⁻¹ *ᵥ v) ≠ 0 := by
    intro h
    refine hvne (hSinj ?_)
    show S⁻¹ *ᵥ v = S⁻¹ *ᵥ (0 : n → ℝ)
    rw [Matrix.mulVec_zero]
    exact h
  have huu : 0 < (S⁻¹ *ᵥ v) ⬝ᵥ (S⁻¹ *ᵥ v) := by
    simpa using Matrix.dotProduct_star_self_pos_iff.mpr hune
  have hTS : T * S⁻¹ = S⁻¹ * W := by
    rw [← hsim]
    have e : S⁻¹ * W * S * S⁻¹ = S⁻¹ * W * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
    rw [e, hSmi, Matrix.mul_one]
  have hTu : T *ᵥ (S⁻¹ *ᵥ v) = hW.1.eigenvalues i • (S⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hTS, ← Matrix.mulVec_mulVec, hWv, Matrix.mulVec_smul]
  -- `|μ| ‖v‖ = ‖Tv‖ ≥ √b ‖v‖`
  have hq := le_dotProduct_mulVec_of_smul_one_le hTT (S⁻¹ *ᵥ v)
  rw [dotProduct_transpose_mul_self, hTu, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul] at hq
  have hb2 : b ≤ hW.1.eigenvalues i ^ 2 := by nlinarith
  calc Real.sqrt b ≤ Real.sqrt (hW.1.eigenvalues i ^ 2) := Real.sqrt_le_sqrt hb2
    _ = hW.1.eigenvalues i := Real.sqrt_sq hmupos.le

/-! ### A scalar estimate -/

/-- `r/(1-ϑ) - 2r/√(1+ϑ) + r ≤ 3rϑ` for `0 ≤ ϑ ≤ 1/2`, via `ϑ/(1-ϑ) ≤ 2ϑ` and
`(1+ϑ)^{-1/2} ≥ 1 - ϑ/2`. -/
theorem scalar_bound {r t s : ℝ} (hr : 0 ≤ r) (h0 : 0 ≤ t) (h2 : t ≤ 1 / 2)
    (hs0 : 0 < s) (hs2 : s ^ 2 = 1 + t) :
    r / (1 - t) - 2 * (r / s) + r ≤ 3 * r * t := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hu2 : ((1 - t / 2) * s) ^ 2 ≤ 1 := by
    have e : ((1 - t / 2) * s) ^ 2 = (1 - t / 2) ^ 2 * s ^ 2 := by ring
    rw [e, hs2]
    nlinarith [mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ 3 - t)]
  have hu0 : 0 ≤ (1 - t / 2) * s := by nlinarith
  have hinv : 1 - t / 2 ≤ 1 / s := by
    rw [le_div_iff₀ hs0]
    nlinarith [hu2, hu0]
  have hA : r * (1 - t / 2) ≤ r / s := by
    have h7 := mul_le_mul_of_nonneg_left hinv hr
    rwa [mul_one_div] at h7
  have hB : r / (1 - t) ≤ r * (1 + 2 * t) := by
    rw [div_le_iff₀ h1t]
    nlinarith [mul_nonneg (mul_nonneg hr h0) (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]
  nlinarith [hA, hB]

/-! ### The main lemma -/

/-- Lemma SM.B.14 in squared form, with `ϑ` replaced by any upper bound `t ≤ 1/2` for
`‖𝒦 - I‖`: with `𝒦 := Σ^{-1/2} Σ̂ Σ^{-1/2}` and `T := Σ̂^{-1/2} Σ^{1/2}`,
`‖T - I‖_F² ≤ 3rt`. -/
theorem frobSq_sqrt_sub_one_le {Sg Sh : Matrix n n ℝ} (hg : Sg.PosDef) (hh : Sh.PosDef)
    {t : ℝ} (ht : ‖(sqrtPD Sg)⁻¹ * Sh * (sqrtPD Sg)⁻¹ - 1‖ ≤ t) (ht2 : t ≤ 1 / 2) :
    frobSq ((sqrtPD Sh)⁻¹ * sqrtPD Sg - 1) ≤ 3 * Fintype.card n * t := by
  have ht0 : 0 ≤ t := le_trans (norm_nonneg _) ht
  have hr0 : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hb : (0 : ℝ) < 1 + t := by linarith
  set P := sqrtPD Sg with hPdef
  set Q := sqrtPD Sh with hQdef
  have hP : P.PosDef := sqrtPD_posDef hg
  have hQ : Q.PosDef := sqrtPD_posDef hh
  have hPi : (P⁻¹).PosDef := hP.inv
  have hQi : (Q⁻¹).PosDef := hQ.inv
  have hQQ : Q * Q = Sh := sqrtPD_mul_self hh.posSemidef
  have hQiQi : Q⁻¹ * Q⁻¹ = Sh⁻¹ := inv_sqrtPD_mul_self hh
  have hPim : P⁻¹ * P = 1 := sqrtPD_inv_mul hg
  have hShmi : Sh * Sh⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hh)
  set K := P⁻¹ * Sh * P⁻¹ with hKdef
  set T := Q⁻¹ * P with hTdef
  -- `K` is positive definite
  have hPiinj : Function.Injective (P⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hPi.isUnit
  have hK : K.PosDef := by
    have h := hh.conjTranspose_mul_mul_same (B := P⁻¹) hPiinj
    rwa [hPi.isHermitian.eq] at h
  -- `‖𝒦 - I‖ ≤ t` as the Loewner bounds `(1-t)I ⪯ 𝒦 ⪯ (1+t)I`
  have hKh : (K - 1).IsHermitian := Matrix.IsHermitian.sub hK.isHermitian Matrix.isHermitian_one
  have hupper : K ≤ (1 + t) • (1 : Matrix n n ℝ) := by
    have h := le_smul_one_of_norm_le hKh ht
    rw [Matrix.le_iff] at h ⊢
    have e : (1 + t) • (1 : Matrix n n ℝ) - K = t • (1 : Matrix n n ℝ) - (K - 1) := by module
    rw [e]; exact h
  have hlower : (1 - t) • (1 : Matrix n n ℝ) ≤ K := by
    have hn : ‖(1 : Matrix n n ℝ) - K‖ ≤ t := by rw [norm_sub_rev]; exact ht
    have hh1 : ((1 : Matrix n n ℝ) - K).IsHermitian :=
      Matrix.IsHermitian.sub Matrix.isHermitian_one hK.isHermitian
    have h := le_smul_one_of_norm_le hh1 hn
    rw [Matrix.le_iff] at h ⊢
    have e : K - (1 - t) • (1 : Matrix n n ℝ) = t • (1 : Matrix n n ℝ) - (1 - K) := by module
    rw [e]; exact h
  -- `T'T = 𝒦⁻¹`, so the `s_i²` lie in `[(1+t)⁻¹, (1-t)⁻¹]`
  have hTt : Tᵀ = P * Q⁻¹ := by
    rw [hTdef, Matrix.transpose_mul, transpose_eq_self hP.isHermitian,
      transpose_eq_self hQi.isHermitian]
  have hKinv : K⁻¹ = P * Sh⁻¹ * P := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hKdef]
    have e1 : P⁻¹ * Sh * P⁻¹ * (P * Sh⁻¹ * P) = P⁻¹ * Sh * (P⁻¹ * P) * Sh⁻¹ * P := by
      simp only [Matrix.mul_assoc]
    rw [e1, hPim, Matrix.mul_one]
    have e2 : P⁻¹ * Sh * Sh⁻¹ * P = P⁻¹ * (Sh * Sh⁻¹) * P := by simp only [Matrix.mul_assoc]
    rw [e2, hShmi, Matrix.mul_one, hPim]
  have hTT : Tᵀ * T = K⁻¹ := by
    rw [hTt, hTdef, hKinv]
    have e : P * Q⁻¹ * (Q⁻¹ * P) = P * (Q⁻¹ * Q⁻¹) * P := by simp only [Matrix.mul_assoc]
    rw [e, hQiQi]
  have hTTpd : (Tᵀ * T).PosDef := by rw [hTT]; exact hK.inv
  have hTTupper : Tᵀ * T ≤ (1 - t)⁻¹ • (1 : Matrix n n ℝ) := by
    rw [hTT]; exact inv_le_of_smul_one_le hK h1t hlower
  have hTTlower : (1 + t)⁻¹ • (1 : Matrix n n ℝ) ≤ Tᵀ * T := by
    rw [hTT]; exact smul_one_le_inv_of_le_smul_one hK hb hupper
  -- `tr(T'T) = ∑_i s_i² ≤ r/(1-t)`
  have hfrobT : frobSq T = ∑ i, hTTpd.1.eigenvalues i := by
    rw [frobSq_eq_trace]
    simpa using hTTpd.1.trace_eq_sum_eigenvalues
  have hsum1 : ∑ i, hTTpd.1.eigenvalues i ≤ (Fintype.card n : ℝ) * (1 - t)⁻¹ := by
    refine (Finset.sum_le_sum fun i _ =>
      eigenvalues_le_of_le_smul_one hTTpd.1 hTTupper i).trans_eq ?_
    simp [Finset.card_univ]
  -- `T` is similar to `W := Σ̂^{-1/4} Σ^{1/2} Σ̂^{-1/4}`, so `μ_i ≥ (1+t)^{-1/2}`
  set S := sqrtPD Q with hSdef
  have hS : S.PosDef := sqrtPD_posDef hQ
  have hSi : (S⁻¹).PosDef := hS.inv
  have hSS : S * S = Q := sqrtPD_mul_self hQ.posSemidef
  have hSiSi : S⁻¹ * S⁻¹ = Q⁻¹ := inv_sqrtPD_mul_self hQ
  have hSim : S⁻¹ * S = 1 := sqrtPD_inv_mul hQ
  have hSmi : S * S⁻¹ = 1 := sqrtPD_mul_inv hQ
  have hSiinj : Function.Injective (S⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hSi.isUnit
  set W := S⁻¹ * P * S⁻¹ with hWdef
  have hW : W.PosDef := by
    have h := hP.conjTranspose_mul_mul_same (B := S⁻¹) hSiinj
    rw [hSi.isHermitian.eq] at h
    rwa [hWdef]
  have hsim : S⁻¹ * W * S = T := by
    rw [hWdef, hTdef]
    have e : S⁻¹ * (S⁻¹ * P * S⁻¹) * S = (S⁻¹ * S⁻¹) * P * (S⁻¹ * S) := by
      simp only [Matrix.mul_assoc]
    rw [e, hSiSi, hSim, Matrix.mul_one]
  -- `tr(T) = tr(W) = ∑_i μ_i`
  have htrTW : T.trace = W.trace := by
    rw [← hsim, Matrix.trace_mul_comm (S⁻¹ * W) S]
    have e : S * (S⁻¹ * W) = (S * S⁻¹) * W := by simp only [Matrix.mul_assoc]
    rw [e, hSmi, Matrix.one_mul]
  have htrW : W.trace = ∑ i, hW.1.eigenvalues i := by
    simpa using hW.1.trace_eq_sum_eigenvalues
  have hsum2 : (Fintype.card n : ℝ) * (Real.sqrt (1 + t))⁻¹ ≤ ∑ i, hW.1.eigenvalues i := by
    have hstep : ∀ i : n, Real.sqrt ((1 + t)⁻¹) ≤ hW.1.eigenvalues i := fun i =>
      sqrt_le_eigenvalues_of_similar hSiinj hSmi hW hsim hTTlower i
    have h1 : (Fintype.card n : ℝ) * Real.sqrt ((1 + t)⁻¹) ≤ ∑ i, hW.1.eigenvalues i := by
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => hstep i)
      simp [Finset.card_univ]
    rwa [Real.sqrt_inv] at h1
  -- the decomposition and the two scalar estimates
  have hs0 : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr hb
  have hs2 : Real.sqrt (1 + t) ^ 2 = 1 + t := Real.sq_sqrt hb.le
  have hsc := scalar_bound (r := (Fintype.card n : ℝ)) hr0 ht0 ht2 hs0 hs2
  have e1 : (Fintype.card n : ℝ) * (1 - t)⁻¹ = (Fintype.card n : ℝ) / (1 - t) :=
    (div_eq_mul_inv _ _).symm
  have e2 : (Fintype.card n : ℝ) * (Real.sqrt (1 + t))⁻¹
      = (Fintype.card n : ℝ) / Real.sqrt (1 + t) := (div_eq_mul_inv _ _).symm
  rw [frobSq_sub_one, hfrobT, htrTW, htrW]
  linarith [hsum1, hsum2, hsc, e1, e2]

/-- **Lemma SM.B.14.** `‖T - I‖_F ≤ (3rϑ)^{1/2}` with `ϑ = ‖𝒦 - I‖ ≤ 1/2`. -/
theorem frobNorm_sqrt_sub_one_le {Sg Sh : Matrix n n ℝ} (hg : Sg.PosDef) (hh : Sh.PosDef)
    (ht : ‖(sqrtPD Sg)⁻¹ * Sh * (sqrtPD Sg)⁻¹ - 1‖ ≤ 1 / 2) :
    frobNorm ((sqrtPD Sh)⁻¹ * sqrtPD Sg - 1)
      ≤ Real.sqrt (3 * Fintype.card n * ‖(sqrtPD Sg)⁻¹ * Sh * (sqrtPD Sg)⁻¹ - 1‖) := by
  rw [frobNorm]
  exact Real.sqrt_le_sqrt (frobSq_sqrt_sub_one_le hg hh le_rfl ht)

/-! ### The Frobenius norm is a norm

A matrix is read as a vector of `EuclideanSpace ℝ (n × n)`, whose norm equals `frobNorm`, so
the norm laws for `frobNorm` follow from Mathlib. -/

/-- A matrix read as a vector of `EuclideanSpace ℝ (n × n)`. -/
noncomputable def matVec (M : Matrix n n ℝ) : EuclideanSpace ℝ (n × n) :=
  (EuclideanSpace.equiv (n × n) ℝ).symm fun p => M p.1 p.2

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matVec_apply (M : Matrix n n ℝ) (p : n × n) : matVec M p = M p.1 p.2 := rfl

omit [Fintype n] [DecidableEq n] in
theorem matVec_add (A B : Matrix n n ℝ) : matVec (A + B) = matVec A + matVec B := by
  ext p; simp

omit [Fintype n] [DecidableEq n] in
theorem matVec_sub (A B : Matrix n n ℝ) : matVec (A - B) = matVec A - matVec B := by
  ext p; simp

omit [Fintype n] [DecidableEq n] in
theorem matVec_smul (r : ℝ) (A : Matrix n n ℝ) : matVec (r • A) = r • matVec A := by
  ext p; simp

omit [Fintype n] [DecidableEq n] in
theorem matVec_sum {α : Type*} (s : Finset α) (f : α → Matrix n n ℝ) :
    matVec (∑ i ∈ s, f i) = ∑ i ∈ s, matVec (f i) := by
  classical
  induction s using Finset.induction with
  | empty => ext p; simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, matVec_add, ih]

omit [DecidableEq n] in
theorem frobSq_nonneg (M : Matrix n n ℝ) : 0 ≤ frobSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq n] in
theorem frobNorm_nonneg (M : Matrix n n ℝ) : 0 ≤ frobNorm M := Real.sqrt_nonneg _

omit [DecidableEq n] in
theorem sq_frobNorm (M : Matrix n n ℝ) : frobNorm M ^ 2 = frobSq M :=
  Real.sq_sqrt (frobSq_nonneg M)

omit [DecidableEq n] in
/-- The Euclidean norm of `matVec M` is the Frobenius norm of `M`. -/
theorem norm_matVec (M : Matrix n n ℝ) : ‖matVec M‖ = frobNorm M := by
  rw [EuclideanSpace.norm_eq, frobNorm, frobSq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show ‖(matVec M).ofLp (i, j)‖ = ‖M i j‖ from rfl, Real.norm_eq_abs, sq_abs]

omit [DecidableEq n] in
theorem dist_matVec (A B : Matrix n n ℝ) : dist (matVec A) (matVec B) = frobNorm (A - B) := by
  rw [dist_eq_norm, ← matVec_sub, norm_matVec]

omit [DecidableEq n] in
theorem frobNorm_zero : frobNorm (0 : Matrix n n ℝ) = 0 := by
  rw [frobNorm, show frobSq (0 : Matrix n n ℝ) = 0 by simp [frobSq], Real.sqrt_zero]

omit [DecidableEq n] in
theorem frobNorm_add_le (A B : Matrix n n ℝ) :
    frobNorm (A + B) ≤ frobNorm A + frobNorm B := by
  rw [← norm_matVec, ← norm_matVec A, ← norm_matVec B, matVec_add]
  exact norm_add_le _ _

omit [DecidableEq n] in
theorem frobNorm_sub_le (A B : Matrix n n ℝ) :
    frobNorm (A - B) ≤ frobNorm A + frobNorm B := by
  rw [← norm_matVec, ← norm_matVec A, ← norm_matVec B, matVec_sub]
  exact norm_sub_le _ _

omit [DecidableEq n] in
theorem frobNorm_smul (r : ℝ) (A : Matrix n n ℝ) :
    frobNorm (r • A) = |r| * frobNorm A := by
  rw [← norm_matVec, ← norm_matVec A, matVec_smul, norm_smul, Real.norm_eq_abs]

omit [DecidableEq n] in
theorem frobNorm_sum_le {α : Type*} (s : Finset α) (f : α → Matrix n n ℝ) :
    frobNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, frobNorm (f i) := by
  rw [← norm_matVec, matVec_sum]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_matVec _)

omit [DecidableEq n] in
theorem frobNorm_mono {A B : Matrix n n ℝ} (h : frobSq A ≤ frobSq B) :
    frobNorm A ≤ frobNorm B := Real.sqrt_le_sqrt h

omit [DecidableEq n] in
theorem frobSq_neg (A : Matrix n n ℝ) : frobSq (-A) = frobSq A := by
  simp [frobSq]

omit [DecidableEq n] in
theorem frobNorm_neg (A : Matrix n n ℝ) : frobNorm (-A) = frobNorm A := by
  rw [frobNorm, frobNorm, frobSq_neg]

omit [DecidableEq n] in
theorem frobSq_transpose (A : Matrix n n ℝ) : frobSq Aᵀ = frobSq A := by
  rw [frobSq, frobSq, Finset.sum_comm]
  rfl

omit [DecidableEq n] in
theorem frobNorm_transpose (A : Matrix n n ℝ) : frobNorm Aᵀ = frobNorm A := by
  rw [frobNorm, frobNorm, frobSq_transpose]

omit [DecidableEq n] in
theorem frobSq_eq_frobNorm_sq (A : Matrix n n ℝ) : frobSq A = frobNorm A ^ 2 :=
  (sq_frobNorm A).symm


end Multiway
