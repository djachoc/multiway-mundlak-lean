import Multiway.Incremental
import Multiway.OrthoSum
import Multiway.Leverage
import Multiway.DimensionWise
import Multiway.ProjBridge
import Multiway.Sqrt
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Computation of the joint within transformation

This file formalizes Proposition SM.E.1 of the paper (Computation of the joint within
transformation), clause by clause. Clauses (a), (c) and (d) are projector and least-squares
algebra over a finite-dimensional real inner product space `E`; clause (b), a statement about the
entries of `P_[Δ]`, is formalized on `EuclideanSpace ℝ O`. The convergence `Γ_k → Q_[Δ]Γ_0` of
clause (c) (Halperin's alternating projection theorem) is not formalized. In clause (c) the
smallest nonzero singular value `σ⁺_min(Δ)` enters through the hypothesis
`σ⁺_min(Δ)‖u‖ ≤ ‖Δ'u‖` for `u ∈ col(Δ)`; in clause (d) `σ_min(X̃)` and `‖X̃‖` enter through
`σ‖v‖ ≤ ‖X̃v‖` and `‖X̃v‖ ≤ b‖v‖`.

## Main results

* `within_deletedSpace`, `finrank_deletedSpace`: deleting a singleton category (clause (a)).
* `starProjection_joint`, `jointProjMat_diag`: the closed form after absorbing one dimension (b).
* `sweep_iterate_sub`, `frobSq_starProjection_le`, `sweepList_eq_orthogonal`: the alternating
  scheme and its error bound (c).
* `norm_beta_perturbed_le`, `norm_nu_perturbed_le`: the tolerance bounds (d).
-/

namespace Multiway

open Submodule LinearMap

open scoped RealInnerProductSpace

/-! ## Splitting a subspace along a subspace of it

Let `T ≤ S`. Then `T ⊔ (S ⊓ Tᗮ) = S`, the projector onto `S ⊓ Tᗮ` agrees with the projector onto
`S` on `Tᗮ`, and the dimensions subtract. -/

section Split

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {S T : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
/-- `T` and `S ⊓ Tᗮ` are orthogonal for every `S`. -/
theorem isOrtho_inf_orthogonal (S T : Submodule ℝ E) : T ⟂ (S ⊓ Tᗮ) :=
  (Submodule.isOrtho_iff_le.mpr inf_le_right).symm

/-- `𝒮 = T ⊕ (𝒮 ∩ Tᗮ)` for a subspace `T ≤ 𝒮`. -/
theorem sup_inf_orthogonal_eq (hTS : T ≤ S) : T ⊔ (S ⊓ Tᗮ) = S := by
  refine le_antisymm (sup_le hTS inf_le_left) fun x hx => ?_
  have hsplit : T.starProjection x + Tᗮ.starProjection x = x :=
    T.starProjection_add_starProjection_orthogonal x
  refine hsplit ▸ Submodule.add_mem_sup (T.starProjection_apply_mem x) ?_
  refine Submodule.mem_inf.mpr ⟨?_, Tᗮ.starProjection_apply_mem x⟩
  rw [Submodule.starProjection_orthogonal_val]
  exact Submodule.sub_mem _ hx (hTS (T.starProjection_apply_mem x))

/-- On `Tᗮ` the projector onto `S ⊓ Tᗮ` is the projector onto `S`, so the projector of the reduced
design is the restriction of the original one. -/
theorem starProjection_inf_orthogonal_eq (hTS : T ≤ S) {x : E} (hx : x ∈ Tᗮ) :
    (S ⊓ Tᗮ).starProjection x = S.starProjection x := by
  have hsup : T ⊔ (S ⊓ Tᗮ) = S := sup_inf_orthogonal_eq hTS
  have h := starProjection_add_of_isOrtho (isOrtho_inf_orthogonal S T) x
  simp only [hsup] at h
  rwa [(Submodule.starProjection_apply_eq_zero_iff T).mpr hx, zero_add] at h

/-- `dim(S ⊓ Tᗮ) + dim T = dim S` whenever `T ≤ S`. -/
theorem finrank_inf_orthogonal_add (hTS : T ≤ S) :
    Module.finrank ℝ (S ⊓ Tᗮ : Submodule ℝ E) + Module.finrank ℝ T = Module.finrank ℝ S := by
  have hbot : T ⊓ (S ⊓ Tᗮ) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_left T inf_le_right)
      (le_of_eq (Submodule.inf_orthogonal_eq_bot T)))
  have h := Submodule.finrank_sup_add_finrank_inf_eq T (S ⊓ Tᗮ)
  rw [sup_inf_orthogonal_eq hTS, hbot, finrank_bot, add_zero] at h
  omega

end Split

/-! ## Clause (a): deleting a singleton category -/

section Singleton

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {S : Submodule ℝ E} {e : E}

/-- If `e_o ∈ 𝒮` then `Q_[Δ]e_o = 0`. -/
theorem starProjection_orthogonal_singleton (he : e ∈ S) : Sᗮ.starProjection e = 0 := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr he,
    sub_self]

/-- The `o`-th row of `Q_[Δ]` vanishes: `⟪e_o, Q_[Δ]x⟫ = 0`. In particular `x̃_o = 0` and
`(Q_[Δ]y)_o = 0`. -/
theorem inner_singleton_starProjection_orthogonal (he : e ∈ S) (x : E) :
    ⟪e, Sᗮ.starProjection x⟫ = 0 := by
  rw [← Submodule.inner_starProjection_left_eq_right Sᗮ e x,
    starProjection_orthogonal_singleton he, inner_zero_left]

/-- The `o`-th row of `P_[Δ]` is `e_o'`, so `z_o = x_o`. -/
theorem inner_singleton_starProjection (he : e ∈ S) (x : E) :
    ⟪e, S.starProjection x⟫ = ⟪e, x⟫ := by
  rw [← Submodule.inner_starProjection_left_eq_right S e x,
    Submodule.starProjection_eq_self_iff.mpr he]

variable {ι : Type*} {x : ι → E}

/-- The residual maker of `[Δ, X]` annihilates `e_o ∈ 𝒮`: `Re_o = 0`. -/
theorem residualMaker_singleton (he : e ∈ S) : residualMaker S x e = 0 :=
  residualMaker_apply_of_mem_fixedEffects he

/-- `R_{oo} = 0`. -/
theorem inner_residualMaker_singleton (he : e ∈ S) : ⟪e, residualMaker S x e⟫ = 0 := by
  rw [residualMaker_singleton (x := x) he, inner_zero_right]

/-! ### The reduced design -/

/-- The fixed-effect space of the reduced design, `𝒮 ∩ e_o^⊥`, inside the original ambient
space. -/
noncomputable def deletedSpace (S : Submodule ℝ E) (e : E) : Submodule ℝ E := S ⊓ (ℝ ∙ e)ᗮ

/-- Restriction to `𝒪 ∖ {o}` inside the original ambient space. It is the component of `u`
orthogonal to `e_o`, which is `u - u_o e_o` when `⟪e, e⟫ = 1`. -/
noncomputable def deleteObs (e : E) (u : E) : E := u - ⟪e, u⟫ • e

omit [FiniteDimensional ℝ E] in
theorem deleteObs_mem_orthogonal (he : ⟪e, e⟫ = 1) (u : E) : deleteObs e u ∈ (ℝ ∙ e)ᗮ := by
  refine Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ?_
  rw [deleteObs, inner_sub_right, real_inner_smul_right, he, mul_one, sub_self]

omit [FiniteDimensional ℝ E] in
theorem span_singleton_le (he : e ∈ S) : (ℝ ∙ e) ≤ S :=
  (Submodule.span_singleton_le_iff_mem e S).mpr he

/-- The joint within transformation of the reduced design, applied to the restricted column,
is the original `Q_[Δ]u`, so the residual maker of the reduced design is `Q_[Δ]` with row and
column `o` deleted. -/
theorem within_deletedSpace (he : e ∈ S) (hee : ⟪e, e⟫ = 1) (u : E) :
    deleteObs e u - (deletedSpace S e).starProjection (deleteObs e u)
      = u - S.starProjection u := by
  have hmem := deleteObs_mem_orthogonal (e := e) hee u
  have hproj : (deletedSpace S e).starProjection (deleteObs e u)
      = S.starProjection (deleteObs e u) :=
    starProjection_inf_orthogonal_eq (span_singleton_le he) hmem
  rw [deletedSpace] at hproj
  rw [deletedSpace, hproj, deleteObs, map_sub, map_smul,
    Submodule.starProjection_eq_self_iff.mpr he]
  abel

/-- Inner products of within-transformed columns (`X̃'X̃`, `X̃'Q_[Δ]y`) are unchanged by
deleting the singleton observation. -/
theorem inner_within_deletedSpace (he : e ∈ S) (hee : ⟪e, e⟫ = 1) (u v : E) :
    ⟪deleteObs e u - (deletedSpace S e).starProjection (deleteObs e u),
        deleteObs e v - (deletedSpace S e).starProjection (deleteObs e v)⟫
      = ⟪Sᗮ.starProjection u, Sᗮ.starProjection v⟫ := by
  rw [within_deletedSpace he hee u, within_deletedSpace he hee v,
    Submodule.starProjection_orthogonal_val, Submodule.starProjection_orthogonal_val]

/-- Deleting the singleton observation reduces `d_[Δ]` by one. -/
theorem finrank_deletedSpace (he : e ∈ S) (hne : e ≠ 0) :
    Module.finrank ℝ (deletedSpace S e) + 1 = Module.finrank ℝ S := by
  have h := finrank_inf_orthogonal_add (span_singleton_le he)
  rwa [finrank_span_singleton hne] at h

/-- Deleting the singleton observation reduces `n` by one. -/
theorem finrank_orthogonal_singleton (hne : e ≠ 0) :
    Module.finrank ℝ ((ℝ ∙ e)ᗮ : Submodule ℝ E) + 1 = Module.finrank ℝ E := by
  have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ e)
  rw [finrank_span_singleton hne] at h
  omega

end Singleton

/-! ## Clause (b): the closed form once one dimension is absorbed

The matrix `Δ_{m*}` is represented by its index map `f : O → L`, with `P_{m*} = proj f` the projector onto
`𝒮_{m*} = fibreSpace f`; `Δ_{-m*}` is a matrix `Dr` with column space `𝒮_{-m*}`. The reduced
spectral decomposition `W'W = U_pD_pU_p'` (with `U_p'U_p = I_p`, `D_p ≻ 0`) is a hypothesis
`hspec`, and `D_p^{-1/2}` is the inverse of `sqrtPD`. -/

section Absorbed

open Finset Matrix

variable {O : Type*} [Fintype O] [DecidableEq O]

/-! ### A symmetric idempotent matrix is the orthogonal projector onto its column space -/

/-- `col(A)`, as a subspace of `EuclideanSpace ℝ O`. -/
noncomputable def colSpace {J : Type*} [Fintype J] [DecidableEq J] (A : Matrix O J ℝ) :
    Submodule ℝ (EuclideanSpace ℝ O) := LinearMap.range (Matrix.toEuclideanLin A)

omit [Fintype O] [DecidableEq O] in
theorem mem_colSpace {J : Type*} [Fintype J] [DecidableEq J] (A : Matrix O J ℝ)
    (x : EuclideanSpace ℝ J) : Matrix.toEuclideanLin A x ∈ colSpace A :=
  LinearMap.mem_range_self _ x

omit [Fintype O] [DecidableEq O] in
/-- `toEuclideanLin (AB) = toEuclideanLin A ∘ toEuclideanLin B`. -/
theorem toEuclideanLin_mul {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (A : Matrix O J ℝ) (B : Matrix J K ℝ) (x : EuclideanSpace ℝ K) :
    Matrix.toEuclideanLin (A * B) x = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
  show WithLp.toLp 2 ((A * B) *ᵥ WithLp.ofLp x) = _
  rw [← Matrix.mulVec_mulVec]
  rfl

/-- A symmetric matrix is self-adjoint as an operator on `EuclideanSpace ℝ O`. -/
theorem inner_toEuclideanLin_symm {A : Matrix O O ℝ} (hsymm : Aᵀ = A)
    (x y : EuclideanSpace ℝ O) :
    ⟪Matrix.toEuclideanLin A x, y⟫ = ⟪x, Matrix.toEuclideanLin A y⟫ := by
  have hco : ∀ (z : EuclideanSpace ℝ O) (o : O),
      Matrix.toEuclideanLin A z o = ∑ o' : O, A o o' * z o' := fun _ _ => rfl
  simp only [inner_euclidean, hco, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  have hs : A o' o = A o o' := by
    have h := congrFun (congrFun hsymm o) o'
    simpa [Matrix.transpose_apply] using h
  rw [hs]
  ring

/-- A symmetric idempotent matrix is the orthogonal projector onto its column space. -/
theorem starProjection_colSpace {A : Matrix O O ℝ} (hsymm : Aᵀ = A) (hidem : A * A = A)
    (x : EuclideanSpace ℝ O) :
    (colSpace A).starProjection x = Matrix.toEuclideanLin A x := by
  have hAA : ∀ z : EuclideanSpace ℝ O,
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin A z) = Matrix.toEuclideanLin A z := by
    intro z
    rw [← toEuclideanLin_mul, hidem]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (mem_colSpace A x) ?_
  rintro _ ⟨y, rfl⟩
  rw [inner_sub_left, ← inner_toEuclideanLin_symm hsymm (Matrix.toEuclideanLin A x) y, hAA,
    inner_toEuclideanLin_symm hsymm x y, sub_self]

/-! ### The reduced spectral factor `V := WU_pD_p^{-1/2}` -/

section Spectral

variable {J Rk : Type*} [Fintype J] [DecidableEq J] [Fintype Rk] [DecidableEq Rk]
variable {W : Matrix O J ℝ} {Up : Matrix J Rk ℝ} {Dp : Matrix Rk Rk ℝ}

/-- `V := WU_pD_p^{-1/2}`. -/
noncomputable def specFactor (W : Matrix O J ℝ) (Up : Matrix J Rk ℝ) (Dp : Matrix Rk Rk ℝ) :
    Matrix O Rk ℝ := W * Up * (sqrtPD Dp)⁻¹

/-- `P_W = VV'`. -/
noncomputable def specProj (W : Matrix O J ℝ) (Up : Matrix J Rk ℝ) (Dp : Matrix Rk Rk ℝ) :
    Matrix O O ℝ := specFactor W Up Dp * (specFactor W Up Dp)ᵀ

/-- `D_p^{-1/2}` is symmetric. -/
theorem transpose_inv_sqrtPD (hD : Dp.PosDef) : ((sqrtPD Dp)⁻¹)ᵀ = (sqrtPD Dp)⁻¹ :=
  transpose_eq_self (inv_sqrtPD_posDef hD).isHermitian

omit [DecidableEq O] [DecidableEq J] in
/-- `V'V = D_p^{-1/2}U_p'W'WU_pD_p^{-1/2} = I_p`. -/
theorem specFactor_transpose_mul_self (hD : Dp.PosDef) (hU : Upᵀ * Up = 1)
    (hspec : Wᵀ * W = Up * Dp * Upᵀ) :
    (specFactor W Up Dp)ᵀ * specFactor W Up Dp = 1 := by
  have hmid : (specFactor W Up Dp)ᵀ * specFactor W Up Dp
      = (sqrtPD Dp)⁻¹ * (Upᵀ * (Wᵀ * W) * Up) * (sqrtPD Dp)⁻¹ := by
    simp only [specFactor, Matrix.transpose_mul, transpose_inv_sqrtPD hD, Matrix.mul_assoc]
  have h1 : Upᵀ * (Up * Dp * Upᵀ) * Up = Dp := by
    calc Upᵀ * (Up * Dp * Upᵀ) * Up = Upᵀ * Up * Dp * (Upᵀ * Up) := by
          simp only [Matrix.mul_assoc]
      _ = Dp := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  rw [hmid, hspec, h1]
  exact inv_conj_eq_one (sqrtPD_mul_self hD.posSemidef) (sqrtPD_inv_mul hD) (sqrtPD_mul_inv hD)

omit [DecidableEq O] in
/-- `WU_pU_p' = W`, from `(I - U_pU_p')W'W(I - U_pU_p') = 0` and
`Matrix.conjTranspose_mul_self_eq_zero`. -/
theorem mul_eigenvectors_eq_self (hU : Upᵀ * Up = 1) (hspec : Wᵀ * W = Up * Dp * Upᵀ) :
    W * Up * Upᵀ = W := by
  have key : ∀ N : Matrix J J ℝ, Nᵀ = N → N * Up = 0 → W * N = 0 := by
    intro N hNsym hNU
    have hz : (W * N)ᴴ * (W * N) = 0 := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hNsym]
      calc N * Wᵀ * (W * N) = N * (Wᵀ * W) * N := by simp only [Matrix.mul_assoc]
        _ = N * (Up * Dp * Upᵀ) * N := by rw [hspec]
        _ = N * Up * Dp * (Upᵀ * N) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hNU, Matrix.zero_mul, Matrix.zero_mul]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hz
  have hNsym : ((1 : Matrix J J ℝ) - Up * Upᵀ)ᵀ = (1 : Matrix J J ℝ) - Up * Upᵀ := by
    simp [Matrix.transpose_sub, Matrix.transpose_mul]
  have hNU : ((1 : Matrix J J ℝ) - Up * Upᵀ) * Up = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have hWN := key _ hNsym hNU
  rw [Matrix.mul_sub, Matrix.mul_one] at hWN
  rw [Matrix.mul_assoc]
  exact (sub_eq_zero.mp hWN).symm

omit [DecidableEq O] [DecidableEq J] in
/-- `V'W = D_p^{1/2}U_p'`. -/
theorem specFactor_transpose_mul (hD : Dp.PosDef) (hU : Upᵀ * Up = 1)
    (hspec : Wᵀ * W = Up * Dp * Upᵀ) :
    (specFactor W Up Dp)ᵀ * W = sqrtPD Dp * Upᵀ := by
  have h : (specFactor W Up Dp)ᵀ * W = (sqrtPD Dp)⁻¹ * (Upᵀ * (Wᵀ * W)) := by
    simp only [specFactor, Matrix.transpose_mul, transpose_inv_sqrtPD hD, Matrix.mul_assoc]
  rw [h, hspec]
  calc (sqrtPD Dp)⁻¹ * (Upᵀ * (Up * Dp * Upᵀ))
      = (sqrtPD Dp)⁻¹ * (Upᵀ * Up * Dp) * Upᵀ := by simp only [Matrix.mul_assoc]
    _ = (sqrtPD Dp)⁻¹ * Dp * Upᵀ := by rw [hU, Matrix.one_mul]
    _ = sqrtPD Dp * Upᵀ := by
        have h1 : (sqrtPD Dp)⁻¹ * (sqrtPD Dp * sqrtPD Dp) = sqrtPD Dp := by
          rw [← Matrix.mul_assoc, sqrtPD_inv_mul hD, Matrix.one_mul]
        rw [sqrtPD_mul_self hD.posSemidef] at h1
        rw [h1]

omit [Fintype O] [DecidableEq O] [DecidableEq J] in
/-- `VV'` is symmetric. -/
theorem specProj_transpose (W : Matrix O J ℝ) (Up : Matrix J Rk ℝ) (Dp : Matrix Rk Rk ℝ) :
    (specProj W Up Dp)ᵀ = specProj W Up Dp := by
  rw [specProj, Matrix.transpose_mul, Matrix.transpose_transpose]

omit [DecidableEq O] [DecidableEq J] in
/-- `VV'` is idempotent, from `V'V = I_p`. -/
theorem specProj_mul_self (hD : Dp.PosDef) (hU : Upᵀ * Up = 1)
    (hspec : Wᵀ * W = Up * Dp * Upᵀ) :
    specProj W Up Dp * specProj W Up Dp = specProj W Up Dp := by
  calc specProj W Up Dp * specProj W Up Dp
      = specFactor W Up Dp * ((specFactor W Up Dp)ᵀ * specFactor W Up Dp)
          * (specFactor W Up Dp)ᵀ := by
        simp only [specProj, Matrix.mul_assoc]
    _ = specProj W Up Dp := by
        rw [specFactor_transpose_mul_self hD hU hspec, Matrix.mul_one, specProj]

omit [DecidableEq O] in
/-- `VV'W = W`: `VV'` fixes `col(W)`. -/
theorem specProj_mul_eq_self (hD : Dp.PosDef) (hU : Upᵀ * Up = 1)
    (hspec : Wᵀ * W = Up * Dp * Upᵀ) : specProj W Up Dp * W = W := by
  have h1 : specProj W Up Dp * W = specFactor W Up Dp * ((specFactor W Up Dp)ᵀ * W) := by
    rw [specProj, Matrix.mul_assoc]
  rw [h1, specFactor_transpose_mul hD hU hspec, specFactor]
  calc W * Up * (sqrtPD Dp)⁻¹ * (sqrtPD Dp * Upᵀ)
      = W * Up * ((sqrtPD Dp)⁻¹ * sqrtPD Dp) * Upᵀ := by simp only [Matrix.mul_assoc]
    _ = W * Up * Upᵀ := by rw [sqrtPD_inv_mul hD, Matrix.mul_one]
    _ = W := mul_eigenvectors_eq_self hU hspec

/-- `col(VV') = col(W)`. One inclusion holds because `V = W(U_pD_p^{-1/2})`, the other because
`VV'W = W`. -/
theorem colSpace_specProj (hD : Dp.PosDef) (hU : Upᵀ * Up = 1)
    (hspec : Wᵀ * W = Up * Dp * Upᵀ) : colSpace (specProj W Up Dp) = colSpace W := by
  have hfac : specProj W Up Dp
      = W * ((Up * (sqrtPD Dp)⁻¹) * (specFactor W Up Dp)ᵀ) := by
    simp only [specProj, specFactor, Matrix.mul_assoc]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [hfac, toEuclideanLin_mul]
    exact mem_colSpace W _
  · rintro _ ⟨y, rfl⟩
    have hfix : Matrix.toEuclideanLin W y
        = Matrix.toEuclideanLin (specProj W Up Dp) (Matrix.toEuclideanLin W y) := by
      rw [← toEuclideanLin_mul, specProj_mul_eq_self hD hU hspec]
    have hmem : Matrix.toEuclideanLin (specProj W Up Dp) (Matrix.toEuclideanLin W y)
        ∈ colSpace (specProj W Up Dp) := mem_colSpace _ _
    rwa [← hfix] at hmem

/-- `VV' = W(W'W)^{+}W' = P_W`: `VV'` is the orthogonal projector onto `col(W)`. -/
theorem starProjection_colSpace_specFactor (hD : Dp.PosDef) (hU : Upᵀ * Up = 1)
    (hspec : Wᵀ * W = Up * Dp * Upᵀ) (x : EuclideanSpace ℝ O) :
    (colSpace W).starProjection x = Matrix.toEuclideanLin (specProj W Up Dp) x := by
  have h : colSpace W = colSpace (specProj W Up Dp) := (colSpace_specProj hD hU hspec).symm
  simp only [h]
  exact starProjection_colSpace (specProj_transpose W Up Dp) (specProj_mul_self hD hU hspec) x

end Spectral

/-! ### Absorbing dimension `m*` -/

section Absorb

variable {L : Type*} [DecidableEq L]
variable {J Rk : Type*} [Fintype J] [DecidableEq J] [Fintype Rk] [DecidableEq Rk]

/-- `Q_{m*} = I_n - P_{m*}` as an operator, with `P_{m*}` the matrix `proj f`. -/
theorem starProjection_orthogonal_fibreSpace (f : O → L) (x : EuclideanSpace ℝ O) :
    (fibreSpace f)ᗮ.starProjection x = Matrix.toEuclideanLin (1 - proj f) x := by
  rw [Submodule.starProjection_orthogonal_val, starProjection_fibreSpace_mulVec]
  ext o
  show x o - _ = _
  simp

/-- `W := Q_{m*}Δ_{-m*}`. -/
noncomputable def absorbedBlock (f : O → L) (Dr : Matrix O J ℝ) : Matrix O J ℝ :=
  (1 - proj f) * Dr

/-- `col(W) = Q_{m*}𝒮_{-m*}`. -/
theorem colSpace_absorbedBlock (f : O → L) (Dr : Matrix O J ℝ) :
    colSpace (absorbedBlock f Dr)
      = (colSpace Dr).map
          (((fibreSpace f)ᗮ.starProjection :
            EuclideanSpace ℝ O →ₗ[ℝ] EuclideanSpace ℝ O)) := by
  have hmap : (((fibreSpace f)ᗮ.starProjection :
        EuclideanSpace ℝ O →ₗ[ℝ] EuclideanSpace ℝ O)).comp (Matrix.toEuclideanLin Dr)
      = Matrix.toEuclideanLin (absorbedBlock f Dr) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, absorbedBlock, toEuclideanLin_mul]
    exact starProjection_orthogonal_fibreSpace f _
  rw [colSpace, colSpace, ← hmap, LinearMap.range_comp]

variable {f : O → L} {Dr : Matrix O J ℝ} {Up : Matrix J Rk ℝ} {Dp : Matrix Rk Rk ℝ}

/-- `rank(W) + dim 𝒮_{m*} = d_[Δ]`, that is `rank(W) = d_[Δ] - N_{m*}` when every category
of dimension `m*` is realized. -/
theorem finrank_colSpace_absorbedBlock (f : O → L) (Dr : Matrix O J ℝ) :
    Module.finrank ℝ (colSpace (absorbedBlock f Dr)) + Module.finrank ℝ (fibreSpace f)
      = Module.finrank ℝ
          ((fibreSpace f ⊔ colSpace Dr : Submodule ℝ (EuclideanSpace ℝ O))) := by
  have hle : fibreSpace f ≤ fibreSpace f ⊔ colSpace Dr := le_sup_left
  have hS : fibreSpace f ⊔ colSpace Dr = fibreSpace f ⊔ colSpace Dr := rfl
  have h := finrank_inf_orthogonal_add hle
  rw [inf_orthogonal_eq_map_starProjection_orthogonal hS, ← colSpace_absorbedBlock] at h
  exact h

/-- `P_[Δ] = P_{m*} + VV'`, from Lemma SM.B.1 (Incremental projector) at `m = m*`. -/
theorem starProjection_joint (hD : Dp.PosDef) (hU : Upᵀ * Up = 1)
    (hspec : (absorbedBlock f Dr)ᵀ * (absorbedBlock f Dr) = Up * Dp * Upᵀ)
    (x : EuclideanSpace ℝ O) :
    (fibreSpace f ⊔ colSpace Dr).starProjection x
      = Matrix.toEuclideanLin (proj f + specProj (absorbedBlock f Dr) Up Dp) x := by
  have hinc := DFunLike.congr_fun
    (incrementalProjector_eq_starProjection (S := fibreSpace f ⊔ colSpace Dr)
      (T := fibreSpace f) (U := colSpace Dr) rfl) x
  have hcol : (colSpace Dr).map
      (((fibreSpace f)ᗮ.starProjection : EuclideanSpace ℝ O →ₗ[ℝ] EuclideanSpace ℝ O))
      = colSpace (absorbedBlock f Dr) := (colSpace_absorbedBlock f Dr).symm
  simp only [hcol] at hinc
  have hinc' : (fibreSpace f ⊔ colSpace Dr).starProjection x - (fibreSpace f).starProjection x
      = (colSpace (absorbedBlock f Dr)).starProjection x := hinc
  have hW := starProjection_colSpace_specFactor (W := absorbedBlock f Dr) hD hU hspec x
  have hm : (fibreSpace f).starProjection x = Matrix.toEuclideanLin (proj f) x :=
    starProjection_fibreSpace f x
  have hsum : Matrix.toEuclideanLin (proj f + specProj (absorbedBlock f Dr) Up Dp) x
      = Matrix.toEuclideanLin (proj f) x
        + Matrix.toEuclideanLin (specProj (absorbedBlock f Dr) Up Dp) x := by
    rw [map_add]; rfl
  rw [hsum, ← hm, ← hW, ← hinc']
  abel

/-- `Q_[Δ] = Q_{m*} - VV'`. -/
theorem starProjection_orthogonal_joint (hD : Dp.PosDef) (hU : Upᵀ * Up = 1)
    (hspec : (absorbedBlock f Dr)ᵀ * (absorbedBlock f Dr) = Up * Dp * Upᵀ)
    (x : EuclideanSpace ℝ O) :
    (fibreSpace f ⊔ colSpace Dr)ᗮ.starProjection x
      = (fibreSpace f)ᗮ.starProjection x
        - Matrix.toEuclideanLin (specProj (absorbedBlock f Dr) Up Dp) x := by
  have hsum : Matrix.toEuclideanLin (proj f + specProj (absorbedBlock f Dr) Up Dp) x
      = Matrix.toEuclideanLin (proj f) x
        + Matrix.toEuclideanLin (specProj (absorbedBlock f Dr) Up Dp) x := by
    rw [map_add]; rfl
  have hm : (fibreSpace f).starProjection x = Matrix.toEuclideanLin (proj f) x :=
    starProjection_fibreSpace f x
  rw [Submodule.starProjection_orthogonal_val, starProjection_joint hD hU hspec x, hsum,
    Submodule.starProjection_orthogonal_val, hm]
  abel

omit [DecidableEq O] [DecidableEq Rk] in
/-- `(P_[Δ])_{oo} = 1/T^{(m*)}_{i_{m*}(o)} + ‖v_o‖²`, with `v_o'` the `o`-th row of `V`. -/
theorem jointProjMat_diag (f : O → L) (V : Matrix O Rk ℝ) (o : O) :
    (proj f + V * Vᵀ) o o = (margCount f (f o) : ℝ)⁻¹ + ∑ k : Rk, V o k ^ 2 := by
  simp [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

end Absorb

end Absorbed

/-! ## Clause (c): the alternating scheme

`Γ_k := (Q_M ⋯ Q_1)^k Γ_0`, columnwise. One sweep is `sweepList P l` at `l = [1, …, M]`, and
`Γ_k` is `sweepIter P l k`. -/

section Alternating

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {D : Type*}

/-- One sweep: `sweepList P [1, …, M] = Q_M ⋯ Q_1`, the residual makers applied in list
order. -/
noncomputable def sweepList (P : D → Submodule ℝ E) : List D → (E →ₗ[ℝ] E)
  | [] => LinearMap.id
  | m :: l => (sweepList P l).comp (((P m)ᗮ.starProjection : E →ₗ[ℝ] E))

@[simp] theorem sweepList_nil (P : D → Submodule ℝ E) (x : E) : sweepList P [] x = x := rfl

@[simp] theorem sweepList_cons (P : D → Submodule ℝ E) (m : D) (l : List D) (x : E) :
    sweepList P (m :: l) x = sweepList P l ((P m)ᗮ.starProjection x) := rfl

/-- `Γ_k := (Q_M ⋯ Q_1)^k Γ_0`, columnwise. -/
noncomputable def sweepIter (P : D → Submodule ℝ E) (l : List D) (k : ℕ) (x : E) : E :=
  (fun y => sweepList P l y)^[k] x

@[simp] theorem sweepIter_zero (P : D → Submodule ℝ E) (l : List D) (x : E) :
    sweepIter P l 0 x = x := rfl

theorem sweepIter_succ (P : D → Submodule ℝ E) (l : List D) (k : ℕ) (x : E) :
    sweepIter P l (k + 1) x = sweepIter P l k (sweepList P l x) :=
  Function.iterate_succ_apply _ k x

section Annihilate

variable {S : Submodule ℝ E} {P : D → Submodule ℝ E}

/-- Since `𝒮_m ⊆ 𝒮`, `Q_[Δ]P_m = 0`. -/
theorem orthogonal_comp_starProjection {V : Submodule ℝ E} (hVS : V ≤ S) (x : E) :
    Sᗮ.starProjection (V.starProjection x) = 0 := by
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_eq_self_iff.mpr (hVS (V.starProjection_apply_mem x)), sub_self]

/-- `Q_[Δ]Q_m = Q_[Δ]` for every `m`. -/
theorem orthogonal_comp_orthogonal {V : Submodule ℝ E} (hVS : V ≤ S) (x : E) :
    Sᗮ.starProjection (Vᗮ.starProjection x) = Sᗮ.starProjection x := by
  rw [Submodule.starProjection_orthogonal_val (K := V), map_sub,
    orthogonal_comp_starProjection hVS, sub_zero]

/-- `Q_[Δ]` is unchanged by a complete sweep. -/
theorem orthogonal_comp_sweepList (hPS : ∀ m, P m ≤ S) (l : List D) (x : E) :
    Sᗮ.starProjection (sweepList P l x) = Sᗮ.starProjection x := by
  induction l generalizing x with
  | nil => rfl
  | cons m t ih => rw [sweepList_cons, ih, orthogonal_comp_orthogonal (hPS m)]

/-- `Q_[Δ]Γ_k = Q_[Δ]Γ_0`. -/
theorem orthogonal_sweep_iterate (hPS : ∀ m, P m ≤ S) (l : List D) (k : ℕ) (x : E) :
    Sᗮ.starProjection (sweepIter P l k x) = Sᗮ.starProjection x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [sweepIter_succ, ih, orthogonal_comp_sweepList hPS]

/-- `Γ_k - Q_[Δ]Γ_0 = Γ_k - Q_[Δ]Γ_k = P_[Δ]Γ_k`. -/
theorem sweep_iterate_sub (hPS : ∀ m, P m ≤ S) (l : List D) (k : ℕ) (x : E) :
    sweepIter P l k x - Sᗮ.starProjection x = S.starProjection (sweepIter P l k x) := by
  rw [← orthogonal_sweep_iterate hPS l k x, Submodule.starProjection_orthogonal_val, sub_sub_cancel]

end Annihilate

/-! ### The error bound

`‖Γ_k - Q_[Δ]Γ_0‖_F = ‖P_[Δ]Γ_k‖_F ≤ ‖Δ'Γ_k‖_F / σ⁺_min(Δ)`. The hypothesis `hσ` is the
property of `σ⁺_min(Δ)` that the proof uses, and `hker` is `Δ'Q_[Δ] = 0`. -/

section Bound

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {S : Submodule ℝ E} {Dt : E →ₗ[ℝ] G} {σ : ℝ}

/-- The bound, columnwise: `σ⁺_min(Δ)‖P_[Δ]v‖ ≤ ‖Δ'v‖`. -/
theorem norm_starProjection_le (hker : ∀ z ∈ Sᗮ, Dt z = 0) (hσ : ∀ u ∈ S, σ * ‖u‖ ≤ ‖Dt u‖)
    (v : E) : σ * ‖S.starProjection v‖ ≤ ‖Dt v‖ := by
  have hsplit : S.starProjection v + Sᗮ.starProjection v = v :=
    S.starProjection_add_starProjection_orthogonal v
  have hDt : Dt v = Dt (S.starProjection v) := by
    conv_lhs => rw [← hsplit]
    rw [map_add, hker _ (Sᗮ.starProjection_apply_mem v), add_zero]
  rw [hDt]
  exact hσ _ (S.starProjection_apply_mem v)

/-- The Frobenius error bound, squared: `σ⁺_min(Δ)²‖P_[Δ]Γ‖_F² ≤ ‖Δ'Γ‖_F²`, the norms being
sums over the columns of `Γ`. -/
theorem frobSq_starProjection_le (hσ0 : 0 ≤ σ) (hker : ∀ z ∈ Sᗮ, Dt z = 0)
    (hσ : ∀ u ∈ S, σ * ‖u‖ ≤ ‖Dt u‖) {ι : Type*} [Fintype ι] (Γ : ι → E) :
    σ ^ 2 * ∑ i, ‖S.starProjection (Γ i)‖ ^ 2 ≤ ∑ i, ‖Dt (Γ i)‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_starProjection_le hker hσ (Γ i)
  have h0 : 0 ≤ σ * ‖S.starProjection (Γ i)‖ := mul_nonneg hσ0 (norm_nonneg _)
  have hsq := mul_self_le_mul_self h0 h
  calc σ ^ 2 * ‖S.starProjection (Γ i)‖ ^ 2
      = (σ * ‖S.starProjection (Γ i)‖) * (σ * ‖S.starProjection (Γ i)‖) := by ring
    _ ≤ ‖Dt (Γ i)‖ * ‖Dt (Γ i)‖ := hsq
    _ = ‖Dt (Γ i)‖ ^ 2 := by ring

end Bound

/-! ### One sweep suffices under pairwise orthogonality -/

section OneSweep

omit [FiniteDimensional ℝ E] in
/-- A list sum of differences, used to collect `∑_{ℓ∈l}P_ℓQ_m = |l|P_0` in the induction
below. -/
theorem list_sum_map_sub_const {V : Type*} [AddCommGroup V] [Module ℝ V] (l : List D)
    (g : D → V) (c : V) :
    (l.map (fun m => g m - c)).sum = (l.map g).sum - (l.length : ℝ) • c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel

variable {C₀ : Submodule ℝ E} {P : D → Submodule ℝ E}

/-- If `P_mP_ℓ = P_0` for `m ≠ ℓ` and `P_mP_0 = P_0`, then
`∏_{m≤k}(I_n - P_m) = I_n - ∑_{m≤k}P_m + (k-1)P_0` for `k ≥ 1`. -/
theorem sweepList_apply_of_pairwise (hconst : ∀ m, C₀ ≤ P m)
    (hpair : ∀ m ℓ, m ≠ ℓ → ∀ x : E,
      (P m).starProjection ((P ℓ).starProjection x) = C₀.starProjection x) :
    ∀ {l : List D}, l.Nodup → l ≠ [] → ∀ x : E,
      sweepList P l x
        = x - (l.map fun m => (P m).starProjection x).sum
          + ((l.length : ℝ) - 1) • C₀.starProjection x := by
  intro l
  induction l with
  | nil => intro _ hne; exact absurd rfl hne
  | cons m t ih =>
      intro hnd _ x
      have hmt : m ∉ t := (List.nodup_cons.mp hnd).1
      have htnd : t.Nodup := (List.nodup_cons.mp hnd).2
      rcases eq_or_ne t ([] : List D) with rfl | htne
      · simp [Submodule.starProjection_orthogonal_val]
      · -- `P_0Q_m = 0`, since `P_0P_m = P_0`.
        have hle : ∀ y : E, C₀.starProjection ((P m).starProjection y) = C₀.starProjection y :=
          fun y => DFunLike.congr_fun
            (Submodule.starProjection_comp_starProjection_of_le (hconst m)) y
        have hC0 : C₀.starProjection ((P m)ᗮ.starProjection x) = 0 := by
          rw [Submodule.starProjection_orthogonal_val (K := P m), map_sub, hle x, sub_self]
        -- `P_ℓQ_m = P_ℓ - P_0` for every `ℓ ∈ t`, since `ℓ ≠ m`.
        have hmap : (t.map fun ℓ => (P ℓ).starProjection ((P m)ᗮ.starProjection x))
            = t.map fun ℓ => (P ℓ).starProjection x - C₀.starProjection x := by
          refine List.map_congr_left fun ℓ hℓ => ?_
          have hne' : ℓ ≠ m := fun h => hmt (h ▸ hℓ)
          rw [Submodule.starProjection_orthogonal_val (K := P m), map_sub, hpair ℓ m hne' x]
        rw [sweepList_cons, ih htnd htne, hmap, hC0, smul_zero, add_zero,
          list_sum_map_sub_const, Submodule.starProjection_orthogonal_val (K := P m),
          List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [sub_smul, one_smul, add_smul, one_smul]
        abel

variable [Fintype D] [Nonempty D]

/-- Under pairwise orthogonality one sweep suffices. By Proposition 1 (Dimension-wise Mundlak
equivalence), `Γ_1 = Q_[Δ]Γ_0`. -/
theorem sweepList_eq_orthogonal (hconst : ∀ m, C₀ ≤ P m)
    (hpair : ∀ m ℓ, m ≠ ℓ → ∀ x : E,
      (P m).starProjection ((P ℓ).starProjection x) = C₀.starProjection x)
    {l : List D} (hnd : l.Nodup) (hfull : ∀ m : D, m ∈ l) (x : E) :
    sweepList P l x = (⨆ m, P m)ᗮ.starProjection x := by
  classical
  have hne : l ≠ [] := by
    intro h
    exact absurd (hfull (Classical.arbitrary D)) (by simp [h])
  have huniv : l.toFinset = (Finset.univ : Finset D) :=
    Finset.eq_univ_iff_forall.mpr fun m => List.mem_toFinset.mpr (hfull m)
  have hsum : (l.map fun m => (P m).starProjection x).sum
      = ∑ m, (P m).starProjection x := by
    rw [← List.sum_toFinset _ hnd, huniv]
  have hlen : (l.length : ℝ) = (Fintype.card D : ℝ) := by
    rw [← List.toFinset_card_of_nodup hnd, huniv, Finset.card_univ]
  rw [sweepList_apply_of_pairwise hconst hpair hnd hne x, hsum, hlen,
    Submodule.starProjection_orthogonal_val, starProjection_iSup_eq hconst hpair x]
  abel

end OneSweep

end Alternating

/-! ## Clause (d): the tolerance bounds

`A : F →ₗ[ℝ] E` is `X̃` with `F` the coefficient space, `A + Ep` is `X̃_τ`, and `ep` is `e`. The
scalar `σ` is `σ_min(X̃)`, entering through `σ‖v‖ ≤ ‖X̃v‖`; `b` is `‖X̃‖`, entering through
`‖X̃v‖ ≤ b‖v‖`; and `τ` bounds `‖E‖` and `‖e‖`. -/

section Tolerance

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A norm bound on a linear map is a norm bound on its adjoint. -/
theorem norm_adjoint_le {A : F →ₗ[ℝ] E} {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ v, ‖A v‖ ≤ c * ‖v‖)
    (w : E) : ‖LinearMap.adjoint A w‖ ≤ c * ‖w‖ := by
  set z : F := LinearMap.adjoint A w with hz
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0, norm_zero]
    exact mul_nonneg hc0 (norm_nonneg w)
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr h0
    have hkey : ‖z‖ * ‖z‖ ≤ c * ‖w‖ * ‖z‖ := by
      have h1 : (‖z‖ : ℝ) * ‖z‖ = ⟪w, A z⟫ := by
        rw [← LinearMap.adjoint_inner_left A z w, ← hz, real_inner_self_eq_norm_mul_norm]
      have h2 : ⟪w, A z⟫ ≤ ‖w‖ * ‖A z‖ := real_inner_le_norm w (A z)
      have h3 : ‖w‖ * ‖A z‖ ≤ ‖w‖ * (c * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hc z) (norm_nonneg w)
      calc ‖z‖ * ‖z‖ = ⟪w, A z⟫ := h1
        _ ≤ ‖w‖ * ‖A z‖ := h2
        _ ≤ ‖w‖ * (c * ‖z‖) := h3
        _ = c * ‖w‖ * ‖z‖ := by ring
    exact le_of_mul_le_mul_right (by linarith [hkey]) hzpos

variable {A Ep : F →ₗ[ℝ] E} {σ b τ : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- `σ_min(X̃_τ) ≥ σ_min(X̃) - τ`, from `‖(A + E)v‖ ≥ ‖Av‖ - ‖Ev‖`. -/
theorem norm_perturbed_lower (hA : ∀ v, σ * ‖v‖ ≤ ‖A v‖) (hEp : ∀ v, ‖Ep v‖ ≤ τ * ‖v‖) (v : F) :
    (σ - τ) * ‖v‖ ≤ ‖(A + Ep) v‖ := by
  have hsum : (A + Ep) v = A v + Ep v := rfl
  have htri : ‖A v‖ ≤ ‖A v + Ep v‖ + ‖Ep v‖ := by
    have := norm_sub_le (A v + Ep v) (Ep v)
    simpa using this
  rw [hsum]
  have h1 := hA v
  have h2 := hEp v
  nlinarith [htri, h1, h2]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The companion upper bound `‖X̃_τ‖ ≤ ‖X̃‖ + τ`. -/
theorem norm_perturbed_upper (hb : ∀ v, ‖A v‖ ≤ b * ‖v‖) (hEp : ∀ v, ‖Ep v‖ ≤ τ * ‖v‖) (v : F) :
    ‖(A + Ep) v‖ ≤ (b + τ) * ‖v‖ := by
  have hsum : (A + Ep) v = A v + Ep v := rfl
  rw [hsum]
  calc ‖A v + Ep v‖ ≤ ‖A v‖ + ‖Ep v‖ := norm_add_le _ _
    _ ≤ b * ‖v‖ + τ * ‖v‖ := add_le_add (hb v) (hEp v)
    _ = (b + τ) * ‖v‖ := by ring

/-- `X̃_τ'X̃_τ ≻ 0`: the perturbed Gram form is positive at every nonzero vector. -/
theorem inner_adjoint_perturbed_pos (hA : ∀ v, σ * ‖v‖ ≤ ‖A v‖) (hEp : ∀ v, ‖Ep v‖ ≤ τ * ‖v‖)
    (hστ : τ < σ) {v : F} (hv : v ≠ 0) :
    0 < ⟪LinearMap.adjoint (A + Ep) ((A + Ep) v), v⟫ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlow := norm_perturbed_lower hA hEp v
  have hpos : 0 < ‖(A + Ep) v‖ := lt_of_lt_of_le (by nlinarith) hlow
  rw [LinearMap.adjoint_inner_left (A + Ep) v ((A + Ep) v), real_inner_self_eq_norm_mul_norm]
  exact mul_pos hpos hpos

/-- `‖X̃_τ'X̃_τ d‖ ≥ (σ_min(X̃) - τ)²‖d‖`, the form of `‖(X̃_τ'X̃_τ)^{-1}‖ ≤ (σ_min(X̃) - τ)^{-2}`
used below. -/
theorem norm_adjoint_perturbed_lower (hA : ∀ v, σ * ‖v‖ ≤ ‖A v‖) (hEp : ∀ v, ‖Ep v‖ ≤ τ * ‖v‖)
    (hστ : τ < σ) (d : F) :
    (σ - τ) ^ 2 * ‖d‖ ≤ ‖LinearMap.adjoint (A + Ep) ((A + Ep) d)‖ := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have hlow := norm_perturbed_lower hA hEp d
    have hσpos : 0 < σ - τ := by linarith
    have hinner : ⟪LinearMap.adjoint (A + Ep) ((A + Ep) d), d⟫ = ‖(A + Ep) d‖ * ‖(A + Ep) d‖ := by
      rw [LinearMap.adjoint_inner_left (A + Ep) d ((A + Ep) d), real_inner_self_eq_norm_mul_norm]
    have hCS : ⟪LinearMap.adjoint (A + Ep) ((A + Ep) d), d⟫
        ≤ ‖LinearMap.adjoint (A + Ep) ((A + Ep) d)‖ * ‖d‖ :=
      real_inner_le_norm _ _
    have hsq0 : (σ - τ) * ‖d‖ * ((σ - τ) * ‖d‖) ≤ ‖(A + Ep) d‖ * ‖(A + Ep) d‖ :=
      mul_self_le_mul_self (by positivity) hlow
    have hsq : (σ - τ) ^ 2 * ‖d‖ * ‖d‖ ≤ ‖LinearMap.adjoint (A + Ep) ((A + Ep) d)‖ * ‖d‖ := by
      nlinarith [hinner, hCS, hsq0]
    exact le_of_mul_le_mul_right hsq hdpos

variable {yt ep ν : E} {β βτ : F}

/-- The normal equations: `X̃_τ'X̃_τ(β̂_τ - β̂_JM) = -X̃_τ'Eβ̂_JM + E'ν̂_FE + X̃_τ'e`, given
`X̃'ν̂_FE = 0` (Theorem 3(a)). -/
theorem adjoint_perturbed_normal (hmodel : yt = A β + ν)
    (hscore : LinearMap.adjoint A ν = 0)
    (hnormal : LinearMap.adjoint (A + Ep) ((A + Ep) βτ)
      = LinearMap.adjoint (A + Ep) (yt + ep)) :
    LinearMap.adjoint (A + Ep) ((A + Ep) (βτ - β))
      = -LinearMap.adjoint (A + Ep) (Ep β) + LinearMap.adjoint Ep ν
        + LinearMap.adjoint (A + Ep) ep := by
  have hadd : LinearMap.adjoint (A + Ep) = LinearMap.adjoint A + LinearMap.adjoint Ep :=
    map_add _ _ _
  have hyt : yt = (A + Ep) β - Ep β + ν := by
    rw [hmodel]
    have : (A + Ep) β = A β + Ep β := rfl
    rw [this]; abel
  have hν : LinearMap.adjoint (A + Ep) ν = LinearMap.adjoint Ep ν := by
    rw [hadd]
    show LinearMap.adjoint A ν + LinearMap.adjoint Ep ν = _
    rw [hscore, zero_add]
  have hsub : (A + Ep) (βτ - β) = (A + Ep) βτ - (A + Ep) β := map_sub _ _ _
  rw [hsub, map_sub, hnormal, hyt]
  rw [map_add, map_add, map_sub, hν]
  abel

/-- The bound on `β̂_τ - β̂_JM`, valid in every sample. -/
theorem norm_beta_perturbed_le (hb0 : 0 ≤ b) (hτ0 : 0 ≤ τ) (hστ : τ < σ)
    (hA : ∀ v, σ * ‖v‖ ≤ ‖A v‖) (hb : ∀ v, ‖A v‖ ≤ b * ‖v‖)
    (hEp : ∀ v, ‖Ep v‖ ≤ τ * ‖v‖) (hep : ‖ep‖ ≤ τ)
    (hmodel : yt = A β + ν) (hscore : LinearMap.adjoint A ν = 0)
    (hnormal : LinearMap.adjoint (A + Ep) ((A + Ep) βτ)
      = LinearMap.adjoint (A + Ep) (yt + ep)) :
    ‖βτ - β‖ ≤ τ * (‖ν‖ + (b + τ) * (1 + ‖β‖)) / (σ - τ) ^ 2 := by
  have hσpos : 0 < σ - τ := by linarith
  have hsqpos : 0 < (σ - τ) ^ 2 := by positivity
  have hbτ0 : 0 ≤ b + τ := by linarith
  have hlow := norm_adjoint_perturbed_lower hA hEp hστ (βτ - β)
  have hid := adjoint_perturbed_normal hmodel hscore hnormal
  -- bound the three terms
  have hupper := norm_perturbed_upper (A := A) (Ep := Ep) (b := b) (τ := τ) hb hEp
  have t1 : ‖LinearMap.adjoint (A + Ep) (Ep β)‖ ≤ (b + τ) * (τ * ‖β‖) :=
    le_trans (norm_adjoint_le hbτ0 hupper (Ep β))
      (mul_le_mul_of_nonneg_left (hEp β) hbτ0)
  have t2 : ‖LinearMap.adjoint Ep ν‖ ≤ τ * ‖ν‖ := norm_adjoint_le hτ0 hEp ν
  have t3 : ‖LinearMap.adjoint (A + Ep) ep‖ ≤ (b + τ) * τ :=
    le_trans (norm_adjoint_le hbτ0 hupper ep) (mul_le_mul_of_nonneg_left hep hbτ0)
  have htri : ‖LinearMap.adjoint (A + Ep) ((A + Ep) (βτ - β))‖
      ≤ ‖LinearMap.adjoint (A + Ep) (Ep β)‖ + ‖LinearMap.adjoint Ep ν‖
        + ‖LinearMap.adjoint (A + Ep) ep‖ := by
    rw [hid]
    calc ‖-LinearMap.adjoint (A + Ep) (Ep β) + LinearMap.adjoint Ep ν
            + LinearMap.adjoint (A + Ep) ep‖
        ≤ ‖-LinearMap.adjoint (A + Ep) (Ep β) + LinearMap.adjoint Ep ν‖
            + ‖LinearMap.adjoint (A + Ep) ep‖ := norm_add_le _ _
      _ ≤ ‖-LinearMap.adjoint (A + Ep) (Ep β)‖ + ‖LinearMap.adjoint Ep ν‖
            + ‖LinearMap.adjoint (A + Ep) ep‖ := by
            have := norm_add_le (-LinearMap.adjoint (A + Ep) (Ep β)) (LinearMap.adjoint Ep ν)
            linarith
      _ = _ := by rw [norm_neg]
  rw [le_div_iff₀ hsqpos]
  nlinarith [hlow, htri, t1, t2, t3]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The bound on `ν̂_τ - ν̂_FE`, from `ν̂_τ - ν̂_FE = e - Eβ̂_JM - X̃_τ(β̂_τ - β̂_JM)`. -/
theorem norm_nu_perturbed_le (hb0 : 0 ≤ b) (hτ0 : 0 ≤ τ)
    (hb : ∀ v, ‖A v‖ ≤ b * ‖v‖) (hEp : ∀ v, ‖Ep v‖ ≤ τ * ‖v‖) (hep : ‖ep‖ ≤ τ)
    (hmodel : yt = A β + ν) :
    ‖(yt + ep - (A + Ep) βτ) - ν‖ ≤ τ * (1 + ‖β‖) + (b + τ) * ‖βτ - β‖ := by
  have hbτ0 : 0 ≤ b + τ := by linarith
  have hupper := norm_perturbed_upper (A := A) (Ep := Ep) (b := b) (τ := τ) hb hEp
  have hkey : (yt + ep - (A + Ep) βτ) - ν = ep - Ep β - (A + Ep) (βτ - β) := by
    have h1 : (A + Ep) (βτ - β) = (A + Ep) βτ - (A + Ep) β := map_sub _ _ _
    have h2 : (A + Ep) β = A β + Ep β := rfl
    rw [h1, h2, hmodel]
    abel
  rw [hkey]
  have htri : ‖ep - Ep β - (A + Ep) (βτ - β)‖
      ≤ ‖ep‖ + ‖Ep β‖ + ‖(A + Ep) (βτ - β)‖ := by
    calc ‖ep - Ep β - (A + Ep) (βτ - β)‖
        ≤ ‖ep - Ep β‖ + ‖(A + Ep) (βτ - β)‖ := norm_sub_le _ _
      _ ≤ (‖ep‖ + ‖Ep β‖) + ‖(A + Ep) (βτ - β)‖ := by
          linarith [norm_sub_le ep (Ep β)]
      _ = ‖ep‖ + ‖Ep β‖ + ‖(A + Ep) (βτ - β)‖ := by ring
  have h1 := hEp β
  have h2 := hupper (βτ - β)
  nlinarith [htri, h1, h2, hep]

end Tolerance

end Multiway
