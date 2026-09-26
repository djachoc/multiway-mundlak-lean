import Multiway.LeverageCond
import Multiway.GroupCompute
import Multiway.ProjBridge
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The residual maker as a matrix

This file represents the residual maker `R` of Lemma SM.B.6 (residual representation and exact
leverage identity) as a matrix on `ℝⁿ = EuclideanSpace ℝ O`. The matrix `R` is symmetric and idempotent, every
row of `R` sums to zero over every cell of a maintained fixed-effect dimension (`RΔ_m = 0`), and
`tr(R) = n - d_[Δ] - K`. The hat matrix `Π = I_n - R`
is the orthogonal projector onto `col([Δ, X])`, of trace `d_[Δ] + K`.

## Notation

* `fixedEffectSpace c dims` is `𝒮 = col(Δ)`, the supremum of the fibre spaces `col(Δ_m)`.
* `residualMatrix S x` is `R` and `hatMatrix S x` is `Π`.
* `cellVec t` is the indicator vector `ι_t` of a set of observations.

## Main results

* `opMatrix`: the matrix of an operator on `EuclideanSpace ℝ O`, with `opMatrix_mulVec`.
* `residualMatrix_isSymm`, `residualMatrix_mul_self`, `residualMatrix_cell_sum_eq_zero`,
  `residualMatrix_trace`: the properties of `R`.
* `hatMatrix_isHermitian`, `hatMatrix_mul_self`, `hatMatrix_trace`: the properties of `Π`.
-/

namespace Multiway
namespace ResidualBridge

open Finset Matrix
open scoped RealInnerProductSpace

/-! ## The matrix of an operator on `EuclideanSpace ℝ O` -/

section OpMatrix

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- The matrix of an operator on `EuclideanSpace ℝ O`, with entries `R_{oo'} = (R e_{o'})_o` in
the standard basis. -/
noncomputable def opMatrix (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O) :
    Matrix O O ℝ :=
  Matrix.of fun o o' => LeverageCond.opEntry R o o'

omit [Fintype O] in
@[simp] theorem opMatrix_apply (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O) (o o' : O) :
    opMatrix R o o' = LeverageCond.opEntry R o o' := rfl

/-- The matrix acts by `Matrix.mulVec` as the operator acts. -/
theorem opMatrix_mulVec (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O)
    (z : EuclideanSpace ℝ O) :
    opMatrix R *ᵥ WithLp.ofLp z = WithLp.ofLp (R z) := by
  funext o
  exact (LeverageCond.apply_eq_sum_opEntry R z o).symm

/-- `opMatrix R` is the matrix whose `Matrix.toEuclideanLin` is `R`. -/
theorem toEuclideanLin_opMatrix (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O) :
    Matrix.toEuclideanLin (opMatrix R)
      = (R : EuclideanSpace ℝ O →ₗ[ℝ] EuclideanSpace ℝ O) :=
  LinearMap.ext fun z => congrArg (WithLp.toLp 2) (opMatrix_mulVec R z)

/-- The matrix determines the operator. -/
theorem opMatrix_injective {R R' : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (h : opMatrix R = opMatrix R') (z : EuclideanSpace ℝ O) : R z = R' z := by
  have h1 : WithLp.ofLp (R z) = WithLp.ofLp (R' z) := by
    rw [← opMatrix_mulVec, ← opMatrix_mulVec, h]
  exact congrArg (WithLp.toLp 2) h1

/-- The matrix of a self-adjoint operator is symmetric. -/
theorem opMatrix_isSymm {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫) : (opMatrix R).IsSymm := by
  show (opMatrix R)ᵀ = opMatrix R
  refine Matrix.ext fun o o' => ?_
  exact (LeverageCond.opEntry_comm hsym o o').symm

/-- The matrix of a composition is the product of the matrices. -/
theorem opMatrix_mul_of_comp (R R' : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O) :
    opMatrix R * opMatrix R' = opMatrix (R.comp R') := by
  refine eq_of_toEuclideanLin_eq fun z => ?_
  have h1 : (opMatrix R * opMatrix R') *ᵥ WithLp.ofLp z
      = WithLp.ofLp (R (R' z)) := by
    rw [← Matrix.mulVec_mulVec, opMatrix_mulVec, opMatrix_mulVec]
  rw [h1, opMatrix_mulVec]
  rfl

/-- The trace of the matrix is the trace of the operator. -/
theorem opMatrix_trace (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O) :
    (opMatrix R).trace
      = LinearMap.trace ℝ (EuclideanSpace ℝ O)
          (R : EuclideanSpace ℝ O →ₗ[ℝ] EuclideanSpace ℝ O) := by
  have h : Matrix.toLin (EuclideanSpace.basisFun O ℝ).toBasis
      (EuclideanSpace.basisFun O ℝ).toBasis (opMatrix R)
      = (R : EuclideanSpace ℝ O →ₗ[ℝ] EuclideanSpace ℝ O) := toEuclideanLin_opMatrix R
  rw [← h, Matrix.trace_toLin_eq]

/-! ### Row sums over a set of observations -/

/-- `ι_t`, the indicator vector of a set of observations; for a cell `t` it is a column of
`Δ_F`. -/
noncomputable def cellVec (t : Finset O) : EuclideanSpace ℝ O :=
  WithLp.toLp 2 fun o => if o ∈ t then (1 : ℝ) else 0

omit [Fintype O] in
@[simp] theorem cellVec_apply (t : Finset O) (o : O) :
    cellVec t o = if o ∈ t then (1 : ℝ) else 0 := rfl

/-- `(Rι_t)_o = ∑_{o' ∈ t} R_{oo'}`, so a row sum over a set is the operator evaluated at the
set's indicator. -/
theorem sum_row_opMatrix (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O) (t : Finset O)
    (o : O) : ∑ o' ∈ t, opMatrix R o o' = R (cellVec t) o := by
  rw [LeverageCond.apply_eq_sum_opEntry R (cellVec t) o]
  simp only [opMatrix_apply, cellVec_apply, mul_ite, mul_one, mul_zero]
  rw [sum_indicator]

end OpMatrix

/-! ## The residual maker as a matrix -/

section Residual

variable {O : Type*} [Fintype O] [DecidableEq O] {ι : Type*}

/-- The residual maker `R` as a matrix. -/
noncomputable def residualMatrix (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : Matrix O O ℝ :=
  opMatrix (residualMaker S x)

@[simp] theorem residualMatrix_apply (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) (o o' : O) :
    residualMatrix S x o o' = LeverageCond.opEntry (residualMaker S x) o o' := rfl

/-- `R` acts on `ℝⁿ` as the orthogonal projector onto `col([Δ, X])ᗮ`. -/
theorem residualMatrix_mulVec (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) (z : EuclideanSpace ℝ O) :
    residualMatrix S x *ᵥ WithLp.ofLp z = WithLp.ofLp (residualMaker S x z) :=
  opMatrix_mulVec _ z

/-- `R` is symmetric. -/
theorem residualMatrix_isSymm (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : (residualMatrix S x).IsSymm :=
  opMatrix_isSymm (inner_residualMaker_left_eq_right S x)

/-- `Rᵀ = R`. -/
theorem residualMatrix_transpose (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : (residualMatrix S x)ᵀ = residualMatrix S x :=
  residualMatrix_isSymm S x

/-- `R` is Hermitian. -/
theorem residualMatrix_isHermitian (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : (residualMatrix S x).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (residualMatrix_isSymm S x)

/-- `R² = R`. -/
theorem residualMatrix_mul_self (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) :
    residualMatrix S x * residualMatrix S x = residualMatrix S x := by
  have hop : ∀ u : EuclideanSpace ℝ O,
      residualMaker S x (residualMaker S x u) = residualMaker S x u := by
    intro u
    have h := residualMaker_isIdempotentElem S x
    have h' := congrArg
      (fun T : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O => T u) h
    simpa using h'
  refine eq_of_toEuclideanLin_eq fun z => ?_
  have h1 : (residualMatrix S x * residualMatrix S x) *ᵥ WithLp.ofLp z
      = WithLp.ofLp (residualMaker S x z) := by
    rw [← Matrix.mulVec_mulVec, residualMatrix_mulVec, residualMatrix_mulVec, hop]
  rw [h1, residualMatrix_mulVec]

/-! ### Vectors fixed and annihilated by `R`

`R` fixes `col([Δ, X])ᗮ` pointwise and annihilates every matrix whose columns lie in
`col([Δ, X])`. -/

omit [DecidableEq O] in
/-- A vector orthogonal to `𝒮` and to every regressor column lies in `col([Δ, X])ᗮ`. -/
theorem mem_orthogonal_fittedSpace {S : Submodule ℝ (EuclideanSpace ℝ O)}
    {x : ι → EuclideanSpace ℝ O} {v : EuclideanSpace ℝ O}
    (hS : ∀ w ∈ S, ⟪w, v⟫ = 0) (hx : ∀ k, ⟪x k, v⟫ = 0) :
    v ∈ (fittedSpace S x)ᗮ := by
  rw [fittedSpace, regressorSpace, ← Submodule.inf_orthogonal]
  refine Submodule.mem_inf.mpr ⟨(Submodule.mem_orthogonal _ _).mpr hS, ?_⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hx k
  | zero => simp
  | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [real_inner_smul_left, ha, mul_zero]

/-- If `v ⊥ col([Δ, X])` then `Rv = v`. -/
theorem residualMatrix_mulVec_of_mem_orthogonal (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) {v : EuclideanSpace ℝ O} (hv : v ∈ (fittedSpace S x)ᗮ) :
    residualMatrix S x *ᵥ WithLp.ofLp v = WithLp.ofLp v := by
  rw [residualMatrix_mulVec, residualMaker, Submodule.starProjection_eq_self_iff.mpr hv]

/-- If `v ⊥ 𝒮` and `v ⊥ x_k` for every `k`, then `Rv = v`. -/
theorem residualMatrix_mulVec_of_orthogonal (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) {v : EuclideanSpace ℝ O}
    (hS : ∀ w ∈ S, ⟪w, v⟫ = 0) (hx : ∀ k, ⟪x k, v⟫ = 0) :
    residualMatrix S x *ᵥ WithLp.ofLp v = WithLp.ofLp v :=
  residualMatrix_mulVec_of_mem_orthogonal S x (mem_orthogonal_fittedSpace hS hx)

/-- `R` annihilates every vector of `col([Δ, X])`. -/
theorem residualMatrix_mulVec_eq_zero (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) {v : EuclideanSpace ℝ O} (hv : v ∈ fittedSpace S x) :
    residualMatrix S x *ᵥ WithLp.ofLp v = 0 := by
  rw [residualMatrix_mulVec, residualMaker_apply_eq_zero hv]
  rfl

/-- `RA = 0` for every matrix `A` whose columns lie in `col([Δ, X])`. -/
theorem residualMatrix_mul_eq_zero {K : Type*} (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) (A : Matrix O K ℝ)
    (hA : ∀ k, (WithLp.toLp 2 fun o => A o k : EuclideanSpace ℝ O) ∈ fittedSpace S x) :
    residualMatrix S x * A = 0 := by
  ext o k
  have h1 : residualMatrix S x *ᵥ (fun o' => A o' k) = 0 :=
    residualMatrix_mulVec_eq_zero S x (hA k)
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun h1 o

/-- `tr(R) = n - d_[Δ] - K`. -/
theorem residualMatrix_trace [Fintype ι] (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) (hX : LinearIndependent ℝ (withinRegressor S x)) :
    (residualMatrix S x).trace
      = (Fintype.card O : ℝ) - (Module.finrank ℝ S : ℝ) - (Fintype.card ι : ℝ) := by
  rw [residualMatrix, opMatrix_trace, trace_residualMaker S x hX, finrank_euclideanSpace]

/-! ### The hat matrix `Π = I_n - R` -/

/-- `Π = I_n - R`, the orthogonal projector onto `col([Δ, X])`, of rank `d_[Δ] + K`. -/
noncomputable def hatMatrix (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : Matrix O O ℝ :=
  1 - residualMatrix S x

theorem hatMatrix_eq_one_sub (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : hatMatrix S x = 1 - residualMatrix S x := rfl

theorem hatMatrix_transpose (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : (hatMatrix S x)ᵀ = hatMatrix S x := by
  rw [hatMatrix, Matrix.transpose_sub, Matrix.transpose_one, residualMatrix_transpose]

theorem hatMatrix_isSymm (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : (hatMatrix S x).IsSymm :=
  hatMatrix_transpose S x

theorem hatMatrix_isHermitian (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : (hatMatrix S x).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (hatMatrix_isSymm S x)

theorem hatMatrix_mul_self (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) : hatMatrix S x * hatMatrix S x = hatMatrix S x := by
  have hexp : hatMatrix S x * hatMatrix S x
      = 1 - residualMatrix S x - residualMatrix S x
        + residualMatrix S x * residualMatrix S x := by
    simp only [hatMatrix, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hexp, residualMatrix_mul_self, hatMatrix]
  abel

/-- `tr(Π) = d_[Δ] + K`. -/
theorem hatMatrix_trace [Fintype ι] (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) (hX : LinearIndependent ℝ (withinRegressor S x)) :
    (hatMatrix S x).trace = (Module.finrank ℝ S : ℝ) + (Fintype.card ι : ℝ) := by
  rw [hatMatrix, Matrix.trace_sub, Matrix.trace_one, residualMatrix_trace S x hX]
  ring

end Residual

/-! ## Row sums of `R` over cells -/

section FixedEffects

variable {O D L : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {ι : Type*}

/-- The joint fixed-effects space `𝒮 = col(Δ) = col([Δ_1, …, Δ_M])`, the supremum of the column
spaces of the maintained dimensions; `d_[Δ]` is its `Module.finrank`. -/
noncomputable def fixedEffectSpace (c : D → O → L) (dims : Finset D) :
    Submodule ℝ (EuclideanSpace ℝ O) :=
  ⨆ m ∈ dims, fibreSpace (c m)

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
theorem fibreSpace_le_fixedEffectSpace (c : D → O → L) (dims : Finset D) {m : D}
    (hm : m ∈ dims) : fibreSpace (c m) ≤ fixedEffectSpace c dims :=
  le_iSup₂ (f := fun m (_ : m ∈ dims) => fibreSpace (c m)) m hm

/-- The indicator of a level-`{m}` cell, the fibre of `i_m` over `i_m(o₀)`, is a column of
`Δ_m`. -/
theorem cellVec_cellOf_singleton (c : D → O → L) (m : D) (o₀ : O) :
    cellVec (cellOf c ({m} : Finset D) o₀) = fibreIndicator (c m) (c m o₀) := by
  have hiff : ∀ o : O, o ∈ cellOf c ({m} : Finset D) o₀ ↔ c m o = c m o₀ := by
    intro o
    rw [mem_cellOf]
    constructor
    · intro h; exact h m (Finset.mem_singleton_self m)
    · intro h j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      exact h
  ext o
  rw [cellVec_apply, fibreIndicator_apply]
  exact if_congr (hiff o) rfl rfl

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
/-- Every column of `Δ_m` lies in `col(Δ)`, for `m` a maintained dimension. -/
theorem fibreIndicator_mem_fixedEffectSpace (c : D → O → L) (dims : Finset D) {m : D}
    (hm : m ∈ dims) (a : L) :
    fibreIndicator (c m) a ∈ fixedEffectSpace c dims :=
  fibreSpace_le_fixedEffectSpace c dims hm (Submodule.subset_span ⟨a, rfl⟩)

/-- `RΔ_m = 0`, that is, every row of `R` sums to zero over every level-`{m}` cell. -/
theorem residualMatrix_cell_sum_eq_zero (c : D → O → L) (dims : Finset D)
    (x : ι → EuclideanSpace ℝ O) {m : D} (hm : m ∈ dims) :
    ∀ t ∈ cells c ({m} : Finset D), ∀ o : O,
      ∑ o' ∈ t, residualMatrix (fixedEffectSpace c dims) x o o' = 0 := by
  intro t ht o
  obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 ht
  have hzero : residualMaker (fixedEffectSpace c dims) x (fibreIndicator (c m) (c m o₀)) = 0 :=
    residualMaker_apply_of_mem_fixedEffects
      (fibreIndicator_mem_fixedEffectSpace c dims hm (c m o₀))
  calc ∑ o' ∈ cellOf c ({m} : Finset D) o₀,
        residualMatrix (fixedEffectSpace c dims) x o o'
      = residualMaker (fixedEffectSpace c dims) x
          (cellVec (cellOf c ({m} : Finset D) o₀)) o := sum_row_opMatrix _ _ _
    _ = residualMaker (fixedEffectSpace c dims) x (fibreIndicator (c m) (c m o₀)) o := by
        rw [cellVec_cellOf_singleton]
    _ = (0 : EuclideanSpace ℝ O) o := by rw [hzero]
    _ = 0 := rfl

/-- `RΔ_m = 0` for every maintained dimension `m`. -/
theorem residualMatrix_cell_sum_eq_zero_dims (c : D → O → L) (dims : Finset D)
    (x : ι → EuclideanSpace ℝ O) :
    ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ o : O,
      ∑ o' ∈ t, residualMatrix (fixedEffectSpace c dims) x o o' = 0 :=
  fun _ hm => residualMatrix_cell_sum_eq_zero c dims x hm

/-- Proposition SM.E.2(c) for the residual maker, `T_{{m}}(R) = -tr(R)`. Both hypotheses of
`GroupCompute.superAgg_residual_singleton` are verified for `R`. -/
theorem superAgg_residualMatrix_singleton (c : D → O → L) (dims : Finset D)
    (x : ι → EuclideanSpace ℝ O) {m : D} (hm : m ∈ dims) :
    superAgg c ({m} : Finset D)
        (fun o o' => residualMatrix (fixedEffectSpace c dims) x o o')
      = -(residualMatrix (fixedEffectSpace c dims) x).trace :=
  superAgg_residual_singleton c m (residualMatrix_cell_sum_eq_zero c dims x hm)

end FixedEffects

/-! ## An example

Two observations, one fixed-effect dimension with a single category, and no regressors. Then
`𝒮 = span(ι_n)`, `d_[Δ] = 1`, `K = 0`, `n = 2`, `tr(R) = 1`, and `T_{{0}}(R) = -1`. -/

section Witness

/-- The index map of the example, with two observations and one category. -/
def witC : Fin 1 → Fin 2 → Unit := fun _ _ => ()

/-- No regressors: `K = 0`. -/
def witX : Fin 0 → EuclideanSpace ℝ (Fin 2) := Fin.elim0

theorem witX_linearIndependent :
    LinearIndependent ℝ
      (withinRegressor (fixedEffectSpace witC ({0} : Finset (Fin 1))) witX) :=
  linearIndependent_empty_type

/-- With one dimension that has a single category, `col(Δ) = col(ι_n)`. -/
theorem witFixedEffectSpace :
    fixedEffectSpace witC ({0} : Finset (Fin 1)) = constSpace (Fin 2) := by
  have h : fixedEffectSpace witC ({0} : Finset (Fin 1))
      = fibreSpace (fun _ : Fin 2 => (() : Unit)) := by
    rw [fixedEffectSpace]
    refine le_antisymm (iSup₂_le fun m _ => le_of_eq ?_) ?_
    · rfl
    · exact le_iSup₂ (f := fun m (_ : m ∈ ({0} : Finset (Fin 1))) => fibreSpace (witC m))
        (0 : Fin 1) (Finset.mem_singleton_self 0)
  rw [h, fibreSpace_unit]

/-- `d_[Δ] = 1`. -/
theorem witFinrank : Module.finrank ℝ (constSpace (Fin 2)) = 1 := by
  have hne : constVec (Fin 2) ≠ 0 := by
    intro hc
    have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hc
    simp at h1
  exact finrank_span_singleton hne

/-- `tr(R) = n - d_[Δ] - K = 2 - 1 - 0 = 1`. -/
theorem witness_trace :
    (residualMatrix (fixedEffectSpace witC ({0} : Finset (Fin 1))) witX).trace = 1 := by
  rw [residualMatrix_trace _ _ witX_linearIndependent, witFixedEffectSpace, witFinrank]
  norm_num

/-- `T_{{0}}(R) = -tr(R) = -1` on the example. -/
theorem witness_superAgg :
    superAgg witC ({0} : Finset (Fin 1))
        (fun o o' =>
          residualMatrix (fixedEffectSpace witC ({0} : Finset (Fin 1))) witX o o')
      = -1 := by
  rw [superAgg_residualMatrix_singleton witC ({0} : Finset (Fin 1)) witX
        (Finset.mem_singleton_self 0), witness_trace]

/-- Symmetry, idempotence and `RΔ_m = 0` on the example. -/
theorem witness_properties :
    (residualMatrix (fixedEffectSpace witC ({0} : Finset (Fin 1))) witX).IsSymm
      ∧ residualMatrix (fixedEffectSpace witC ({0} : Finset (Fin 1))) witX
          * residualMatrix (fixedEffectSpace witC ({0} : Finset (Fin 1))) witX
        = residualMatrix (fixedEffectSpace witC ({0} : Finset (Fin 1))) witX
      ∧ (∀ t ∈ cells witC ({0} : Finset (Fin 1)), ∀ o : Fin 2,
          ∑ o' ∈ t,
            residualMatrix (fixedEffectSpace witC ({0} : Finset (Fin 1))) witX o o' = 0) :=
  ⟨residualMatrix_isSymm _ _, residualMatrix_mul_self _ _,
    residualMatrix_cell_sum_eq_zero witC ({0} : Finset (Fin 1)) witX
      (Finset.mem_singleton_self 0)⟩

end Witness

end ResidualBridge
end Multiway
