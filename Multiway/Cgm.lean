import Multiway.InclusionExclusion
import Multiway.GroupCompute
import Multiway.Concentration
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# The multiway cluster-robust estimator under absorbed clustering

This file formalizes clauses (a) and (b) of Lemma SM.B.8 of the paper. Clause (a): the
multiway meat formed from the idiosyncratic scores has conditional expectation `𝓜_n`.
Clause (b), at `J = 1`: `E[𝓜̂_CGM | 𝒟] = σ²_ε[∑_o x̃_o x̃_o' R_oo + Ξ_n]` with
`Ξ_n := X̃'(R ∘ (Sh - I))X̃`, and the finite-sample bound
`‖Ξ_n‖ ≤ B²[√((d_[Δ]-N_m) G^{(m)}_max n) + √(K G^{(m)}_max n) + d_[Δ] + K]` in the `l2`
operator norm. The limit `‖Ξ_n‖/n → 0` is in `Multiway/CgmLimit.lean`.

The residual-maker `R` is an abstract symmetric idempotent matrix, the conditional moments
`E[v_o v_{o'} | 𝒟]` enter as the hypothesis `hcross`, and the within regressors summing to
zero over each cluster enters as `hXcl`. `Multiway/ResidualBridge.lean` supplies the
properties of `R` for `residualMatrix S`.

## Main results

* `meat_eq_linkedPairs`: Lemma SM.B.7 applied entrywise, reducing the meat to a pair sum.
* `condExp_meat_idiosyncratic`: clause (a).
* `condExp_meatCGM`: the identity of clause (b).
* `xiMat_opNorm_le`: the norm bound of clause (b).
-/

namespace Multiway
namespace Cgm

open Finset MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

variable {O K D L : Type*}

/-! ## The inclusion–exclusion step

The identity holds for each `ω`. -/

section Meat

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- Lemma SM.B.7 at each entry and each `ω`. The multiway meat equals the
sum over linked pairs `∑_{o∼o'} x̃_{oa} x̃_{o'b} v_o v_{o'}`. -/
theorem meat_eq_linkedPairs {Ω : Type*} (c : D → O → L) (dims : Finset D)
    (X : O → K → Ω → ℝ) (v : O → Ω → ℝ) (a b : K) (ω : Ω) :
    ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) *
          ∑ g ∈ cells c A, (∑ o ∈ g, X o a ω * v o ω) * (∑ o' ∈ g, X o' b ω * v o' ω)
      = ∑ o : O, ∑ o' : O,
          (if Linked c dims o o' then X o a ω * X o' b ω * (v o ω * v o' ω) else 0) :=
  multiway_meat_inclusion_exclusion_entry c dims (fun o k => X o k ω) (fun o => v o ω) a b

end Meat

/-! ## The conditional step

The conditional expectation passes through the double sum over linked pairs and pulls out the
`𝒟`-measurable regressors, leaving the pair moment `E[v_o v_{o'} | 𝒟]`. -/

section Engine

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
-- `𝒟` precedes `mΩ` so that `mΩ` is used for instance synthesis.
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
/-- The indicator of a link is a constant of `ω`, so the coefficient of a pair is
`𝒟`-measurable whenever the regressors are. -/
theorem stronglyMeasurable_pairCoeff {c : D → O → L} {dims : Finset D}
    {X : O → K → Ω → ℝ} {a b : K} (hX : ∀ o k, StronglyMeasurable[𝒟] (X o k)) (o o' : O) :
    StronglyMeasurable[𝒟]
      (fun ω => if Linked c dims o o' then X o a ω * X o' b ω else 0) := by
  by_cases h : Linked c dims o o'
  · have hfun : (fun ω => if Linked c dims o o' then X o a ω * X o' b ω else 0)
        = fun ω => X o a ω * X o' b ω := funext fun ω => by simp [h]
    rw [hfun]
    exact (hX o a).mul (hX o' b)
  · have hfun : (fun ω => if Linked c dims o o' then X o a ω * X o' b ω else 0)
        = fun _ : Ω => (0 : ℝ) := funext fun ω => by simp [h]
    rw [hfun]
    exact stronglyMeasurable_const

omit [DecidableEq O] [DecidableEq D] in
/-- `E[∑_{o∼o'} x̃_{oa} x̃_{o'b} v_o v_{o'} | 𝒟]` is obtained from the pair sum by replacing
each product `v_o v_{o'}` by its conditional expectation `S_{oo'}`, for an arbitrary `S`. -/
theorem condExp_linkedPairs {c : D → O → L} {dims : Finset D}
    {X : O → K → Ω → ℝ} {v : O → Ω → ℝ} {S : O → O → Ω → ℝ} {a b : K}
    (hX : ∀ o k, StronglyMeasurable[𝒟] (X o k))
    (hint : ∀ o o', Integrable (fun ω => v o ω * v o' ω) μ)
    (hint' : ∀ o o', Integrable
      (fun ω => (if Linked c dims o o' then X o a ω * X o' b ω else 0) * (v o ω * v o' ω)) μ)
    (hcross : ∀ o o', μ[fun ω => v o ω * v o' ω | 𝒟] =ᵐ[μ] S o o') :
    μ[fun ω => ∑ o : O, ∑ o' : O,
        (if Linked c dims o o' then X o a ω * X o' b ω * (v o ω * v o' ω) else 0) | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, ∑ o' : O,
        (if Linked c dims o o' then X o a ω * X o' b ω * S o o' ω else 0) := by
  classical
  have hrw : (fun ω => ∑ o : O, ∑ o' : O,
        (if Linked c dims o o' then X o a ω * X o' b ω * (v o ω * v o' ω) else 0))
      = ∑ o : O, ∑ o' : O,
          (fun ω => (if Linked c dims o o' then X o a ω * X o' b ω else 0)
            * (v o ω * v o' ω)) := by
    funext ω
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
    by_cases h : Linked c dims o o' <;> simp [h, mul_assoc]
  rw [hrw]
  have h1 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
    (f := fun o : O => ∑ o' : O,
      (fun ω => (if Linked c dims o o' then X o a ω * X o' b ω else 0) * (v o ω * v o' ω)))
    (fun o _ => integrable_finsetSum' _ fun o' _ => hint' o o') 𝒟
  have h2 : ∀ᵐ ω ∂μ, ∀ o : O,
      μ[∑ o' : O, (fun ω => (if Linked c dims o o' then X o a ω * X o' b ω else 0)
            * (v o ω * v o' ω)) | 𝒟] ω
        = ∑ o' : O, μ[fun ω => (if Linked c dims o o' then X o a ω * X o' b ω else 0)
            * (v o ω * v o' ω) | 𝒟] ω := by
    refine ae_all_iff.2 fun o => ?_
    filter_upwards [condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
      (fun o' _ => hint' o o') 𝒟] with ω hω
    rw [hω, Finset.sum_apply]
  have h3 : ∀ᵐ ω ∂μ, ∀ q : O × O,
      μ[fun ω => (if Linked c dims q.1 q.2 then X q.1 a ω * X q.2 b ω else 0)
          * (v q.1 ω * v q.2 ω) | 𝒟] ω
        = (if Linked c dims q.1 q.2 then X q.1 a ω * X q.2 b ω else 0) * S q.1 q.2 ω := by
    refine ae_all_iff.2 fun q => ?_
    filter_upwards [condExp_mul_of_stronglyMeasurable_left
        (stronglyMeasurable_pairCoeff 𝒟 (c := c) (dims := dims) (a := a) (b := b) hX q.1 q.2)
        (hint' q.1 q.2) (hint q.1 q.2), hcross q.1 q.2] with ω ha hb
    have ha' : μ[fun ω => (if Linked c dims q.1 q.2 then X q.1 a ω * X q.2 b ω else 0)
          * (v q.1 ω * v q.2 ω) | 𝒟] ω
        = (if Linked c dims q.1 q.2 then X q.1 a ω * X q.2 b ω else 0)
          * μ[fun ω => v q.1 ω * v q.2 ω | 𝒟] ω := ha
    rw [ha', hb]
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, Finset.sum_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [e2 o]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [e3 (o, o')]
  by_cases h : Linked c dims o o' <;> simp [h, mul_assoc]

end Engine

/-! ## Clause (a) -/

section ClauseA

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] in
/-- Every observation is linked to itself as soon as at least one dimension is maintained. -/
theorem linked_self {c : D → O → L} {dims : Finset D} (hdims : dims.Nonempty) (o : O) :
    Linked c dims o o := by
  obtain ⟨j, hj⟩ := hdims
  exact ⟨j, hj, rfl⟩

/-- **Lemma SM.B.8(a).** `E[∑_{∅≠A}(-1)^{|A|+1} ∑_{g∈𝒢_A} s_g s_g' | 𝒟] = 𝓜_n` with
`s_g = ∑_{o∈g} x̃_o ε_o`, stated at entry `(a,b)`. The hypothesis `hcross` is
`E[ε_o ε_{o'} | 𝒟] = 𝟙{o = o'} σ²_ε(o)`. -/
theorem condExp_meat_idiosyncratic {c : D → O → L} {dims : Finset D}
    {X : O → K → Ω → ℝ} {eps : O → Ω → ℝ} {sig : O → Ω → ℝ} {a b : K}
    (hdims : dims.Nonempty)
    (hX : ∀ o k, StronglyMeasurable[𝒟] (X o k))
    (hint : ∀ o o', Integrable (fun ω => eps o ω * eps o' ω) μ)
    (hint' : ∀ o o', Integrable
      (fun ω => (if Linked c dims o o' then X o a ω * X o' b ω else 0)
        * (eps o ω * eps o' ω)) μ)
    (hcross : ∀ o o', μ[fun ω => eps o ω * eps o' ω | 𝒟]
      =ᵐ[μ] fun ω => if o = o' then sig o ω else 0) :
    μ[fun ω => ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) *
          ∑ g ∈ cells c A,
            (∑ o ∈ g, X o a ω * eps o ω) * (∑ o' ∈ g, X o' b ω * eps o' ω) | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, X o a ω * X o b ω * sig o ω := by
  classical
  -- reduce the meat to the linked-pair sum
  have hie : (fun ω => ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) *
          ∑ g ∈ cells c A,
            (∑ o ∈ g, X o a ω * eps o ω) * (∑ o' ∈ g, X o' b ω * eps o' ω))
      = fun ω => ∑ o : O, ∑ o' : O,
          (if Linked c dims o o' then X o a ω * X o' b ω * (eps o ω * eps o' ω) else 0) :=
    funext fun ω => meat_eq_linkedPairs c dims X eps a b ω
  rw [hie]
  filter_upwards [condExp_linkedPairs 𝒟 (S := fun o o' ω => if o = o' then sig o ω else 0)
    hX hint hint' hcross] with ω hω
  rw [hω]
  -- only diagonal pairs contribute
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_eq_single o]
  · simp [linked_self hdims o]
  · intro o' _ hne
    by_cases h : Linked c dims o o' <;> simp [h, Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ o) h

end ClauseA

/-! ## The operator norm against the Frobenius norm

The main result is the Gram bound `‖Y'Y‖ ≤ ‖Y‖²_F`. -/

section OpNorm

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/-- `‖My‖² ≤ ‖M‖²_F ‖y‖²`, by the Cauchy–Schwarz inequality applied to each row of `M`. -/
theorem sum_sq_mulVec_le_rectFrobSq (M : Matrix α β ℝ) (y : β → ℝ) :
    ∑ i : α, (M *ᵥ y) i ^ 2 ≤ rectFrobSq M * ∑ k : β, y k ^ 2 := by
  rw [rectFrobSq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : (M *ᵥ y) i = ∑ k : β, M i k * y k := rfl
  rw [h]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => M i k) y

omit [DecidableEq α] in
/-- The `l2` operator norm is bounded by the rectangular Frobenius norm, `‖M‖ ≤ ‖M‖_F`. -/
theorem l2_opNorm_le_rectFrobNorm (M : Matrix α β ℝ) : ‖M‖ ≤ rectFrobNorm M := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (rectFrobNorm_nonneg M) fun y => ?_
  have hval : ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := α) (n := β)).trans
        LinearMap.toContinuousLinearMap) M y
      = (EuclideanSpace.equiv α ℝ).symm (M *ᵥ ((EuclideanSpace.equiv β ℝ) y)) := rfl
  rw [hval]
  have hl : ‖(EuclideanSpace.equiv α ℝ).symm (M *ᵥ ((EuclideanSpace.equiv β ℝ) y))‖ ^ 2
      = ∑ i : α, (M *ᵥ ((EuclideanSpace.equiv β ℝ) y)) i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  have hr : ‖y‖ ^ 2 = ∑ k : β, ((EuclideanSpace.equiv β ℝ) y) k ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  have hkey : ‖(EuclideanSpace.equiv α ℝ).symm (M *ᵥ ((EuclideanSpace.equiv β ℝ) y))‖ ^ 2
      ≤ (rectFrobNorm M * ‖y‖) ^ 2 := by
    rw [hl, mul_pow, rectFrobNorm_sq, hr]
    exact sum_sq_mulVec_le_rectFrobSq M _
  have h1 : (0 : ℝ) ≤ rectFrobNorm M * ‖y‖ :=
    mul_nonneg (rectFrobNorm_nonneg M) (norm_nonneg y)
  nlinarith [norm_nonneg ((EuclideanSpace.equiv α ℝ).symm
    (M *ᵥ ((EuclideanSpace.equiv β ℝ) y))), hkey, h1]

omit [DecidableEq α] in
/-- The Gram bound: `‖Y'Y‖ ≤ ‖Y‖²_F = tr(Y'Y)`. -/
theorem l2_opNorm_transpose_mul_self_le (Y : Matrix α β ℝ) :
    ‖Yᵀ * Y‖ ≤ rectFrobSq Y := by
  have hc : Yᵀ = Yᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial Y).symm
  rw [hc, Matrix.l2_opNorm_conjTranspose_mul_self, ← rectFrobNorm_sq, sq]
  exact mul_le_mul (l2_opNorm_le_rectFrobNorm Y) (l2_opNorm_le_rectFrobNorm Y)
    (norm_nonneg Y) (rectFrobNorm_nonneg Y)

end OpNorm

/-! ## Clause (b), the deterministic part

The lemmas below are norm and trace inequalities for the fixed matrix `Ξ_n`. -/

section Deterministic

variable {N : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [Fintype N] [DecidableEq N]

/-- The cluster indicator `D_j := diag(𝟙{i_m(o) = j})`. -/
def dmat (i : O → N) (j : N) : Matrix O O ℝ :=
  Matrix.diagonal fun o => if i o = j then 1 else 0

/-- The block-diagonal part `bd_m(·)` along the clusters of dimension `m`. -/
def blockPart (i : O → N) (M : Matrix O O ℝ) : Matrix O O ℝ :=
  Matrix.of fun o o' => if i o = i o' then M o o' else 0

/-- The size `T^{(m)}_j` of cluster `j` of dimension `m`. -/
def clusterCard (i : O → N) (j : N) : ℕ := (Finset.univ.filter fun o : O => i o = j).card

omit [Fintype O] [DecidableEq O] [Fintype N] in
@[simp] theorem blockPart_apply (i : O → N) (M : Matrix O O ℝ) (o o' : O) :
    blockPart i M o o' = if i o = i o' then M o o' else 0 := rfl

omit [Fintype O] [DecidableEq O] [Fintype N] in
theorem blockPart_add (i : O → N) (M M' : Matrix O O ℝ) :
    blockPart i (M + M') = blockPart i M + blockPart i M' := by
  ext o o'
  by_cases h : i o = i o' <;> simp [h]

/-- `∑_j D_j Ξ D_j = bd_m(Ξ)`: the block-diagonal part is the sum of the cluster blocks. -/
theorem sum_dmat_conj (i : O → N) (M : Matrix O O ℝ) :
    ∑ j : N, dmat i j * M * dmat i j = blockPart i M := by
  classical
  ext o o'
  rw [Matrix.sum_apply]
  have hterm : ∀ j : N, (dmat i j * M * dmat i j) o o'
      = (if i o = j then (1 : ℝ) else 0) * M o o' * (if i o' = j then (1 : ℝ) else 0) := by
    intro j
    rw [dmat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_eq_single (i o)]
  · by_cases h : i o = i o'
    · simp [h]
    · have h' : ¬ i o' = i o := fun hc => h hc.symm
      simp [h, h']
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ (i o)) h

omit [Fintype K] [DecidableEq K] [Fintype N] in
/-- `(A D_j X̃)'(A D_j X̃) = X̃'D_j A D_j X̃` for a symmetric idempotent `A`. -/
theorem gram_cluster_eq (i : O → N) (j : N) (x : Matrix O K ℝ) {A : Matrix O O ℝ}
    (hsym : Aᵀ = A) (hidem : A * A = A) :
    (A * dmat i j * x)ᵀ * (A * dmat i j * x) = xᵀ * (dmat i j * A * dmat i j) * x := by
  have hD : (dmat i j)ᵀ = dmat i j := Matrix.diagonal_transpose _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hsym, hD]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc A A, hidem]

omit [Fintype K] [DecidableEq K] in
/-- `X̃'bd_m(A)X̃ = ∑_j (A D_j X̃)'(A D_j X̃)`, a sum of Gram matrices. -/
theorem xT_blockPart_eq_sum_gram (i : O → N) (x : Matrix O K ℝ) {A : Matrix O O ℝ}
    (hsym : Aᵀ = A) (hidem : A * A = A) :
    xᵀ * blockPart i A * x = ∑ j : N, (A * dmat i j * x)ᵀ * (A * dmat i j * x) := by
  rw [← sum_dmat_conj i A, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun j _ => (gram_cluster_eq i j x hsym hidem).symm

omit [DecidableEq O] [DecidableEq K] [Fintype N] [DecidableEq N] in
/-- `tr(X̃'ΞX̃) = tr(Ξ X̃X̃')`, trace cyclicity. -/
theorem trace_conj_eq_trace_mul_gram (x : Matrix O K ℝ) (M : Matrix O O ℝ) :
    (xᵀ * M * x).trace = (M * (x * xᵀ)).trace := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

omit [DecidableEq K] in
/-- `∑_j tr(X̃'D_jAD_jX̃) = tr(A bd_m(X̃X̃'))`. -/
theorem sum_rectFrobSq_cluster_eq_trace (i : O → N) (x : Matrix O K ℝ) {A : Matrix O O ℝ}
    (hsym : Aᵀ = A) (hidem : A * A = A) :
    ∑ j : N, rectFrobSq (A * dmat i j * x) = (blockPart i A * (x * xᵀ)).trace := by
  have h : ∀ j : N, rectFrobSq (A * dmat i j * x)
      = (dmat i j * A * dmat i j * (x * xᵀ)).trace := by
    intro j
    rw [rectFrobSq_eq_trace, gram_cluster_eq i j x hsym hidem, trace_conj_eq_trace_mul_gram]
  rw [Finset.sum_congr rfl fun j _ => h j, ← Matrix.trace_sum, ← Matrix.sum_mul, sum_dmat_conj]

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
/-- `tr(MG) = ∑_{o,o'} M_{oo'}G_{o'o}`. -/
theorem trace_mul_eq_sum (M G : Matrix O O ℝ) :
    (M * G).trace = ∑ o : O, ∑ o' : O, M o o' * G o' o := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
/-- `tr(A'B) = ∑_{o,o'} A_{oo'}B_{oo'}`, the Frobenius inner product. -/
theorem trace_transpose_mul_eq_sum (A B : Matrix O O ℝ) :
    (Aᵀ * B).trace = ∑ o : O, ∑ o' : O, A o o' * B o o' := by
  rw [trace_mul_eq_sum]
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

omit [DecidableEq O] [Fintype N] in
/-- The block-diagonal part may be moved from one factor to the other under the trace, when
the other factor is symmetric. -/
theorem trace_blockPart_mul_comm (i : O → N) (A G : Matrix O O ℝ) (hG : Gᵀ = G) :
    (blockPart i A * G).trace = (Aᵀ * blockPart i G).trace := by
  rw [trace_mul_eq_sum, trace_transpose_mul_eq_sum]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  have hGs : G o' o = G o o' := by
    have := congrFun (congrFun hG o) o'
    simpa [Matrix.transpose_apply] using this
  by_cases h : i o = i o' <;> simp [h, hGs]

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
/-- `‖A‖²_F = tr(A)` for a symmetric idempotent `A`. -/
theorem rectFrobSq_of_symmProj {A : Matrix O O ℝ} (hsym : Aᵀ = A) (hidem : A * A = A) :
    rectFrobSq A = A.trace := by
  rw [rectFrobSq_eq_trace, hsym, hidem]

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
/-- The diagonal of a symmetric idempotent matrix is nonnegative, since `A_oo = ∑_{o'} A²_{oo'}`. -/
theorem diag_nonneg_of_symmProj {A : Matrix O O ℝ} (hsym : Aᵀ = A) (hidem : A * A = A)
    (o : O) : 0 ≤ A o o := by
  have h : A o o = ∑ o' : O, A o o' * A o o' := by
    conv_lhs => rw [← hidem]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun o' _ => ?_
    have := congrFun (congrFun hsym o) o'
    simp only [Matrix.transpose_apply] at this
    rw [this]
  rw [h]
  exact Finset.sum_nonneg fun o' _ => mul_self_nonneg _

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
/-- Hence `tr(A) ≥ 0` for a symmetric idempotent `A`. -/
theorem trace_nonneg_of_symmProj {A : Matrix O O ℝ} (hsym : Aᵀ = A) (hidem : A * A = A) :
    0 ≤ A.trace :=
  Finset.sum_nonneg fun o _ => diag_nonneg_of_symmProj hsym hidem o

/-! ### The counting step, `∑_j T^{(m)2}_j ≤ G^{(m)}_max n` -/

omit [DecidableEq O] in
theorem sum_pairs_sameCluster (i : O → N) :
    ∑ o : O, ∑ o' : O, (if i o = i o' then (1 : ℝ) else 0)
      = ∑ j : N, ((clusterCard i j : ℝ)) * ((clusterCard i j : ℝ)) := by
  classical
  have hinner : ∀ o : O, ∑ o' : O, (if i o = i o' then (1 : ℝ) else 0)
      = (clusterCard i (i o) : ℝ) := by
    intro o
    have hc : ∀ o' : O, (if i o = i o' then (1 : ℝ) else 0)
        = (if i o' = i o then (1 : ℝ) else 0) := by
      intro o'
      by_cases h : i o = i o'
      · simp [h]
      · have h' : ¬ i o' = i o := fun hc => h hc.symm
        simp [h, h']
    rw [Finset.sum_congr rfl fun o' _ => hc o', Finset.sum_boole, clusterCard]
  rw [Finset.sum_congr rfl fun o _ => hinner o,
    ← Finset.sum_fiberwise (Finset.univ : Finset O) i (fun o => (clusterCard i (i o) : ℝ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcong : ∀ o ∈ (Finset.univ : Finset O).filter (fun o => i o = j),
      (clusterCard i (i o) : ℝ) = (clusterCard i j : ℝ) := by
    intro o ho
    rw [(Finset.mem_filter.1 ho).2]
  rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul]
  rfl

omit [DecidableEq O] in
theorem sum_clusterCard (i : O → N) : ∑ j : N, (clusterCard i j : ℝ) = (Fintype.card O : ℝ) := by
  classical
  have h := Finset.sum_fiberwise (Finset.univ : Finset O) i (fun _ : O => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  simpa [clusterCard, Finset.card_univ] using h

omit [DecidableEq O] in
/-- `∑_j T^{(m)2}_j ≤ G^{(m)}_max n`. -/
theorem sum_clusterCard_sq_le (i : O → N) {Gmax : ℝ}
    (hG : ∀ j : N, (clusterCard i j : ℝ) ≤ Gmax) :
    ∑ j : N, ((clusterCard i j : ℝ)) * ((clusterCard i j : ℝ))
      ≤ Gmax * (Fintype.card O : ℝ) := by
  have h1 : ∑ j : N, ((clusterCard i j : ℝ)) * ((clusterCard i j : ℝ))
      ≤ ∑ j : N, Gmax * (clusterCard i j : ℝ) :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hG j) (Nat.cast_nonneg _)
  rw [← Finset.mul_sum, sum_clusterCard] at h1
  exact h1

/-! ### `‖bd_m(X̃X̃')‖_F ≤ B²√(G^{(m)}_max n)` -/

omit [DecidableEq O] [DecidableEq K] in
theorem rectFrobSq_blockPart_gram_le (i : O → N) (x : Matrix O K ℝ) {B Gmax : ℝ}
    (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j : N, (clusterCard i j : ℝ) ≤ Gmax) :
    rectFrobSq (blockPart i (x * xᵀ)) ≤ B ^ 4 * (Gmax * (Fintype.card O : ℝ)) := by
  have hentry : ∀ o o' : O, ((x * xᵀ) o o') ^ 2 ≤ B ^ 4 := by
    intro o o'
    have hcs : ((x * xᵀ) o o') ^ 2 ≤ (∑ k : K, x o k ^ 2) * ∑ k : K, x o' k ^ 2 := by
      have h : (x * xᵀ) o o' = ∑ k : K, x o k * x o' k := by
        simp [Matrix.mul_apply, Matrix.transpose_apply]
      rw [h]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => x o k) (fun k => x o' k)
    have h2 : (∑ k : K, x o k ^ 2) * ∑ k : K, x o' k ^ 2 ≤ B ^ 2 * B ^ 2 :=
      mul_le_mul (hB o) (hB o') (Finset.sum_nonneg fun k _ => sq_nonneg _) (sq_nonneg B)
    calc ((x * xᵀ) o o') ^ 2 ≤ (∑ k : K, x o k ^ 2) * ∑ k : K, x o' k ^ 2 := hcs
      _ ≤ B ^ 2 * B ^ 2 := h2
      _ = B ^ 4 := by ring
  have hstep : rectFrobSq (blockPart i (x * xᵀ))
      ≤ ∑ o : O, ∑ o' : O, B ^ 4 * (if i o = i o' then (1 : ℝ) else 0) := by
    rw [rectFrobSq]
    refine Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ => ?_
    by_cases h : i o = i o'
    · simpa [h] using hentry o o'
    · simp [h]
  calc rectFrobSq (blockPart i (x * xᵀ))
      ≤ ∑ o : O, ∑ o' : O, B ^ 4 * (if i o = i o' then (1 : ℝ) else 0) := hstep
    _ = B ^ 4 * ∑ o : O, ∑ o' : O, (if i o = i o' then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun o _ => (Finset.mul_sum _ _ _).symm
    _ = B ^ 4 * ∑ j : N, ((clusterCard i j : ℝ)) * ((clusterCard i j : ℝ)) := by
        rw [sum_pairs_sameCluster]
    _ ≤ B ^ 4 * (Gmax * (Fintype.card O : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_clusterCard_sq_le i hG) (by positivity)

/-! ### The bound for a symmetric idempotent matrix

The bound holds for an arbitrary symmetric idempotent `A`; it is applied at `A^{(m)}` and at `Λ`. -/

theorem opNorm_xT_blockPart_le (i : O → N) (x : Matrix O K ℝ) {A : Matrix O O ℝ}
    (hsym : Aᵀ = A) (hidem : A * A = A) {B Gmax : ℝ}
    (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j : N, (clusterCard i j : ℝ) ≤ Gmax) :
    ‖xᵀ * blockPart i A * x‖
      ≤ B ^ 2 * Real.sqrt (A.trace * (Gmax * (Fintype.card O : ℝ))) := by
  have hGn : 0 ≤ Gmax * (Fintype.card O : ℝ) := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset N) with hN | hN
    · have : (Fintype.card O : ℝ) = 0 := by
        rw [← sum_clusterCard i, hN, Finset.sum_empty]
      rw [this, mul_zero]
    · obtain ⟨j, -⟩ := hN
      have h0 : (0 : ℝ) ≤ Gmax := le_trans (Nat.cast_nonneg _) (hG j)
      exact mul_nonneg h0 (Nat.cast_nonneg _)
  -- the norm of a sum of Gram matrices is at most its trace
  have hsum : ‖xᵀ * blockPart i A * x‖ ≤ ∑ j : N, rectFrobSq (A * dmat i j * x) := by
    rw [xT_blockPart_eq_sum_gram i x hsym hidem]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    exact l2_opNorm_transpose_mul_self_le _
  -- `∑_j tr(X̃'D_jA D_jX̃) = tr(A bd_m(X̃X̃')) ≤ ‖A‖_F ‖bd_m(X̃X̃')‖_F`
  have hGsym : (x * xᵀ)ᵀ = x * xᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have htr : ∑ j : N, rectFrobSq (A * dmat i j * x)
      = (Aᵀ * blockPart i (x * xᵀ)).trace := by
    rw [sum_rectFrobSq_cluster_eq_trace i x hsym hidem,
      trace_blockPart_mul_comm i A (x * xᵀ) hGsym]
  have hcs : (Aᵀ * blockPart i (x * xᵀ)).trace
      ≤ rectFrobNorm A * rectFrobNorm (blockPart i (x * xᵀ)) :=
    le_trans (le_abs_self _) (abs_trace_transpose_mul_le A (blockPart i (x * xᵀ)))
  -- `‖A‖_F = √tr(A)` and `‖bd_m(X̃X̃')‖_F ≤ B²√(G_max n)`
  have hA : rectFrobNorm A = Real.sqrt A.trace := by
    rw [rectFrobNorm, rectFrobSq_of_symmProj hsym hidem]
  have hbd : rectFrobNorm (blockPart i (x * xᵀ))
      ≤ B ^ 2 * Real.sqrt (Gmax * (Fintype.card O : ℝ)) := by
    have h := rectFrobSq_blockPart_gram_le i x hB hG
    have h1 : rectFrobNorm (blockPart i (x * xᵀ))
        ≤ Real.sqrt (B ^ 4 * (Gmax * (Fintype.card O : ℝ))) := by
      rw [rectFrobNorm]
      exact Real.sqrt_le_sqrt h
    refine h1.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), show B ^ 4 = (B ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  calc ‖xᵀ * blockPart i A * x‖
      ≤ ∑ j : N, rectFrobSq (A * dmat i j * x) := hsum
    _ = (Aᵀ * blockPart i (x * xᵀ)).trace := htr
    _ ≤ rectFrobNorm A * rectFrobNorm (blockPart i (x * xᵀ)) := hcs
    _ ≤ Real.sqrt A.trace * (B ^ 2 * Real.sqrt (Gmax * (Fintype.card O : ℝ))) := by
        rw [hA]
        exact mul_le_mul_of_nonneg_left hbd (Real.sqrt_nonneg _)
    _ = B ^ 2 * Real.sqrt (A.trace * (Gmax * (Fintype.card O : ℝ))) := by
        rw [Real.sqrt_mul (trace_nonneg_of_symmProj hsym hidem)]
        ring

/-! ### The diagonal term, `‖∑_o Π_{oo} x̃_o x̃_o'‖ ≤ B² tr(Π)` -/

omit [Fintype N] [DecidableEq N] in
theorem opNorm_xT_diagonal_le (x : Matrix O K ℝ) (d : O → ℝ) (hd : ∀ o : O, 0 ≤ d o)
    {B : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2) :
    ‖xᵀ * Matrix.diagonal d * x‖ ≤ B ^ 2 * ∑ o : O, d o := by
  set Y : Matrix O K ℝ := Matrix.of fun o k => Real.sqrt (d o) * x o k with hY
  have hfac : Yᵀ * Y = xᵀ * Matrix.diagonal d * x := by
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Matrix.mul_diagonal]
    simp only [hY, Matrix.transpose_apply, Matrix.of_apply]
    have hs : Real.sqrt (d o) * Real.sqrt (d o) = d o := Real.mul_self_sqrt (hd o)
    calc Real.sqrt (d o) * x o a * (Real.sqrt (d o) * x o b)
        = (Real.sqrt (d o) * Real.sqrt (d o)) * (x o a * x o b) := by ring
      _ = x o a * d o * x o b := by rw [hs]; ring
  have hfrob : rectFrobSq Y ≤ B ^ 2 * ∑ o : O, d o := by
    have hrw : rectFrobSq Y = ∑ o : O, d o * ∑ k : K, x o k ^ 2 := by
      rw [rectFrobSq]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hs : Real.sqrt (d o) * Real.sqrt (d o) = d o := Real.mul_self_sqrt (hd o)
      simp only [hY, Matrix.of_apply]
      calc (Real.sqrt (d o) * x o k) ^ 2
          = (Real.sqrt (d o) * Real.sqrt (d o)) * x o k ^ 2 := by ring
        _ = d o * x o k ^ 2 := by rw [hs]
    rw [hrw, Finset.mul_sum]
    exact Finset.sum_le_sum fun o _ => by
      rw [mul_comm (B ^ 2) (d o)]
      exact mul_le_mul_of_nonneg_left (hB o) (hd o)
  rw [← hfac]
  exact (l2_opNorm_transpose_mul_self_le Y).trans hfrob

end Deterministic

/-! ## `Ξ_n := X̃'(R ∘ (𝒮h - I))X̃`

The product `R ∘ (𝒮h - I)` is `Matrix.hadamard`, with its `⊙` notation scoped to `Matrix`. -/

section Xi

variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq D] [DecidableEq L]

/-- `𝒮h`, the sharing matrix of the maintained dimensions: `(𝒮h)_{oo'} = 𝟙{o ∼ o'}`. -/
def linkMat (c : D → O → L) (dims : Finset D) : Matrix O O ℝ :=
  Matrix.of fun o o' => if Linked c dims o o' then 1 else 0

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
@[simp] theorem linkMat_apply (c : D → O → L) (dims : Finset D) (o o' : O) :
    linkMat c dims o o' = if Linked c dims o o' then 1 else 0 := rfl

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
/-- For a single maintained dimension this is `shMat`, since sharing some maintained dimension
and sharing every one of them coincide for a singleton. -/
theorem linkMat_singleton (c : D → O → L) (m : D) : linkMat c {m} = shMat c {m} := by
  ext o o'
  have hiff : Linked c {m} o o' ↔ SameOn c {m} o o' := by
    constructor
    · rintro ⟨j, hj, hcj⟩ k hk
      rw [Finset.mem_singleton] at hj hk
      subst hj; subst hk; exact hcj
    · intro h
      exact ⟨m, Finset.mem_singleton_self m, h m (Finset.mem_singleton_self m)⟩
  by_cases h : Linked c {m} o o'
  · simp [shMat, h, hiff.1 h]
  · have h' : ¬ SameOn c {m} o o' := fun hc => h (hiff.2 hc)
    simp [shMat, h, h']

/-- `Ξ_n := X̃'(R ∘ (𝒮h - I))X̃`. -/
def xiMat (c : D → O → L) (dims : Finset D) (R : Matrix O O ℝ) (x : Matrix O K ℝ) :
    Matrix K K ℝ :=
  xᵀ * (R ⊙ (linkMat c dims - 1)) * x

omit [DecidableEq O] [Fintype K] [DecidableEq D] [DecidableEq L] in
/-- `(X̃'ΞX̃)_{ab} = ∑_{o,o'} x̃_{oa} Ξ_{oo'} x̃_{o'b}`. -/
theorem transpose_mul_mul_apply (x : Matrix O K ℝ) (M : Matrix O O ℝ) (a b : K) :
    (xᵀ * M * x) a b = ∑ o : O, ∑ o' : O, x o a * (M o o' * x o' b) := by
  rw [Matrix.mul_apply]
  have h : ∀ o' : O, (xᵀ * M) a o' * x o' b = ∑ o : O, x o a * (M o o' * x o' b) := by
    intro o'
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun o _ => by
      rw [Matrix.transpose_apply]; ring
  rw [Finset.sum_congr rfl fun o' _ => h o']
  exact Finset.sum_comm

omit [Fintype K] [DecidableEq D] in
/-- The linked-pair sum splits into its diagonal and off-diagonal pairs. The identity is
deterministic. -/
theorem linkedPairs_split (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (R : Matrix O O ℝ) (x : Matrix O K ℝ) (a b : K) :
    ∑ o : O, ∑ o' : O, (if Linked c dims o o' then x o a * x o' b * R o o' else 0)
      = (∑ o : O, x o a * x o b * R o o) + xiMat c dims R x a b := by
  classical
  have hdiag : (∑ o : O, x o a * x o b * R o o)
      = ∑ o : O, ∑ o' : O, (if o = o' then x o a * x o' b * R o o' else 0) := by
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_eq_single o]
    · simp
    · intro o' _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ o) h
  rw [hdiag, xiMat, transpose_mul_mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o' _ => ?_
  have hlinkSelf : Linked c dims o o := linked_self hdims o
  by_cases hoo : o = o'
  · subst hoo
    simp [hlinkSelf]
  · by_cases h : Linked c dims o o'
    · simp [h, hoo]
      ring
    · simp [h, hoo]

end Xi

/-! ## Clause (b): the identity and the bound -/

section ClauseB

variable {N : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [Fintype N] [DecidableEq N] [DecidableEq D] [DecidableEq L]

omit [Fintype O] [Fintype N] [DecidableEq D] in
/-- The inner matrix of `Ξ_n = -∑_j X̃'D_jΠD_jX̃ + ∑_o Π_{oo} x̃_o x̃_o'`. Off the diagonal
`R_{oo'} = -Π_{oo'}` by `hPi : Π = I - R`; on the diagonal the sharing indicator and the
identity cancel. -/
theorem hadamard_linkOff_eq (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    {R Pi : Matrix O O ℝ} (hPi : Pi = 1 - R) :
    R ⊙ (linkMat c dims - 1) = -(blockPart i Pi) + Matrix.diagonal (fun o => Pi o o) := by
  classical
  ext o o'
  by_cases hoo : o = o'
  · subst hoo
    have h1 : Linked c dims o o := linked_self hdims o
    simp [h1]
  · have hR : R o o' = -Pi o o' := by
      rw [hPi]
      simp [hoo]
    by_cases h : Linked c dims o o'
    · have hi : i o = i o' := (hlink o o').1 h
      simp [h, hoo, hi, hR]
    · have hi : ¬ i o = i o' := fun hc => h ((hlink o o').2 hc)
      simp [h, hoo, hi]

omit [Fintype K] [DecidableEq K] [Fintype N] [DecidableEq D] in
/-- The split of `Ξ_n` into its block-diagonal and diagonal terms. -/
theorem xiMat_eq (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    {R Pi : Matrix O O ℝ} (hPi : Pi = 1 - R) (x : Matrix O K ℝ) :
    xiMat c dims R x
      = -(xᵀ * blockPart i Pi * x) + xᵀ * Matrix.diagonal (fun o => Pi o o) * x := by
  rw [xiMat, hadamard_linkOff_eq c hdims i hlink hPi, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_neg, Matrix.neg_mul]

omit [DecidableEq D] in
/-- **Lemma SM.B.8(b), the norm bound.**
`‖Ξ_n‖ ≤ B²[√((d_[Δ]-N_m)G^{(m)}_max n) + √(K G^{(m)}_max n) + d_[Δ] + K]` in the `l2`
operator norm, where `Π = P_m + A^{(m)} + Λ` (`hdecomp`) with `A^{(m)}` and `Λ` symmetric
idempotent of traces `d_[Δ] - N_m` and `K`, and `tr(Π) = d_[Δ] + K`. -/
theorem xiMat_opNorm_le (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    (x : Matrix O K ℝ) {R Pi Pm A Lam : Matrix O O ℝ}
    (hPi : Pi = 1 - R) (hdecomp : Pi = Pm + A + Lam)
    (hPm : ∀ o o' : O,
      Pm o o' = if i o = i o' then ((clusterCard i (i o) : ℝ))⁻¹ else 0)
    (hAsym : Aᵀ = A) (hAidem : A * A = A)
    (hLsym : Lamᵀ = Lam) (hLidem : Lam * Lam = Lam)
    (hXcl : ∀ (j : N) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O => i o = j), x o k = 0)
    {B Gmax : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j : N, (clusterCard i j : ℝ) ≤ Gmax) :
    ‖xiMat c dims R x‖
      ≤ B ^ 2 * (Real.sqrt (A.trace * (Gmax * (Fintype.card O : ℝ)))
          + Real.sqrt (Lam.trace * (Gmax * (Fintype.card O : ℝ))) + Pi.trace) := by
  classical
  -- `P_m` is constant on each cluster block, so `X̃'D_jP_mD_jX̃ = 0`
  have hPmBlock : blockPart i Pm = Pm := by
    ext o o'
    by_cases h : i o = i o' <;> simp [hPm o o', h]
  have hzero : xᵀ * blockPart i Pm * x = 0 := by
    ext a b
    rw [hPmBlock, transpose_mul_mul_apply]
    have hterm : ∀ o : O, ∑ o' : O, x o a * (Pm o o' * x o' b) = 0 := by
      intro o
      have hin : ∑ o' : O, x o a * (Pm o o' * x o' b)
          = x o a * ((clusterCard i (i o) : ℝ))⁻¹
            * ∑ o' ∈ Finset.univ.filter (fun o' : O => i o' = i o), x o' b := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun o' _ => ?_
        rw [hPm o o']
        split_ifs with h1 h2 h2
        · ring
        · exact absurd h1.symm h2
        · exact absurd h2.symm h1
        · ring
      rw [hin, hXcl (i o) b, mul_zero]
    simp only [Matrix.zero_apply]
    exact Finset.sum_eq_zero fun o _ => hterm o
  -- `bd_m(Π)` splits and the `P_m` piece drops out
  have hsplit : xᵀ * blockPart i Pi * x
      = xᵀ * blockPart i A * x + xᵀ * blockPart i Lam * x := by
    rw [hdecomp, blockPart_add, blockPart_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.add_mul, hzero, zero_add]
  -- `Π_{oo} ≥ 0` for every `o`
  have hAdiag : ∀ o : O, 0 ≤ A o o := diag_nonneg_of_symmProj hAsym hAidem
  have hLdiag : ∀ o : O, 0 ≤ Lam o o := diag_nonneg_of_symmProj hLsym hLidem
  have hPidiag : ∀ o : O, 0 ≤ Pi o o := by
    intro o
    have hPmd : (0 : ℝ) ≤ Pm o o := by
      rw [hPm o o]
      simp
    have : Pi o o = Pm o o + A o o + Lam o o := by rw [hdecomp]; simp
    rw [this]
    have := hAdiag o
    have := hLdiag o
    linarith
  rw [xiMat_eq c hdims i hlink hPi x, hsplit]
  have hnorm : ‖-(xᵀ * blockPart i A * x + xᵀ * blockPart i Lam * x)
        + xᵀ * Matrix.diagonal (fun o => Pi o o) * x‖
      ≤ (‖xᵀ * blockPart i A * x‖ + ‖xᵀ * blockPart i Lam * x‖)
        + ‖xᵀ * Matrix.diagonal (fun o => Pi o o) * x‖ := by
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    rw [norm_neg]
    exact norm_add_le _ _
  refine hnorm.trans ?_
  have h1 := opNorm_xT_blockPart_le i x hAsym hAidem hB hG
  have h2 := opNorm_xT_blockPart_le i x hLsym hLidem hB hG
  have h3 := opNorm_xT_diagonal_le x (fun o => Pi o o) hPidiag hB
  have htr : ∑ o : O, Pi o o = Pi.trace := rfl
  rw [htr] at h3
  linarith

end ClauseB

/-! ## Clause (b): the conditional expectation -/

section ClauseBCond

variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq D] [DecidableEq L]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [Fintype K] in
/-- **Lemma SM.B.8(b), the identity**, entry by entry:
`E[𝓜̂_CGM | 𝒟] = σ²_ε[∑_o x̃_o x̃_o' R_oo + Ξ_n]`. The hypothesis `hcross` is
`E[ν̂_{FE,o} ν̂_{FE,o'} | 𝒟] = σ²_ε R_{oo'}`. -/
theorem condExp_meatCGM {c : D → O → L} {dims : Finset D}
    {X : O → K → Ω → ℝ} {nuh : O → Ω → ℝ} {R : O → O → Ω → ℝ} {s : Ω → ℝ} {a b : K}
    (hdims : dims.Nonempty)
    (hX : ∀ o k, StronglyMeasurable[𝒟] (X o k))
    (hint : ∀ o o', Integrable (fun ω => nuh o ω * nuh o' ω) μ)
    (hint' : ∀ o o', Integrable
      (fun ω => (if Linked c dims o o' then X o a ω * X o' b ω else 0)
        * (nuh o ω * nuh o' ω)) μ)
    (hcross : ∀ o o', μ[fun ω => nuh o ω * nuh o' ω | 𝒟]
      =ᵐ[μ] fun ω => s ω * R o o' ω) :
    μ[fun ω => ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) *
          ∑ g ∈ cells c A,
            (∑ o ∈ g, X o a ω * nuh o ω) * (∑ o' ∈ g, X o' b ω * nuh o' ω) | 𝒟]
      =ᵐ[μ] fun ω => s ω * ((∑ o : O, X o a ω * X o b ω * R o o ω)
          + xiMat c dims (Matrix.of fun o o' => R o o' ω)
              (Matrix.of fun o k => X o k ω) a b) := by
  classical
  have hie : (fun ω => ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) *
          ∑ g ∈ cells c A,
            (∑ o ∈ g, X o a ω * nuh o ω) * (∑ o' ∈ g, X o' b ω * nuh o' ω))
      = fun ω => ∑ o : O, ∑ o' : O,
          (if Linked c dims o o' then X o a ω * X o' b ω * (nuh o ω * nuh o' ω) else 0) :=
    funext fun ω => meat_eq_linkedPairs c dims X nuh a b ω
  rw [hie]
  filter_upwards [condExp_linkedPairs 𝒟 (S := fun o o' ω => s ω * R o o' ω)
    hX hint hint' hcross] with ω hω
  rw [hω]
  have hfac : ∀ o o' : O,
      (if Linked c dims o o' then X o a ω * X o' b ω * (s ω * R o o' ω) else 0)
        = s ω * (if Linked c dims o o' then X o a ω * X o' b ω * R o o' ω else 0) := by
    intro o o'
    by_cases h : Linked c dims o o'
    · simp [h]
      ring
    · simp [h]
  rw [Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => hfac o o']
  simp only [← Finset.mul_sum]
  have hsplit := linkedPairs_split c hdims (Matrix.of fun o o' => R o o' ω)
    (Matrix.of fun o k => X o k ω) a b
  simp only [Matrix.of_apply] at hsplit
  rw [hsplit]

end ClauseBCond

/-! ## Examples

Each theorem below applies a main result of this file to an explicit model on which its
hypotheses hold. -/

section Witness

/-- The design of the example for `xiMat_opNorm_le`, with two observations in one cluster of
dimension `m` and within regressors `+1` and `-1`, which sum to zero over the cluster. -/
def witnessX : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun o _ => if o = 0 then 1 else -1

/-- The `P_m` of the example for `xiMat_opNorm_le`. There is one cluster of size `2`, so every
entry of the block is `1/2`. -/
noncomputable def witnessPm : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1 / 2

/-- An example for `condExp_meat_idiosyncratic`: `Ω = Unit`, `μ = dirac ()`, `𝒟 = ⊥`, one
observation, one coefficient, one maintained dimension, `x̃ ≡ 1` and `ε ≡ 1`; both sides
equal `1`. -/
theorem condExp_meat_idiosyncratic_witness :
    (Measure.dirac ())[fun _ : Unit =>
        ∑ A ∈ (({0} : Finset (Fin 1))).powerset.filter (fun A => A.Nonempty),
          (-1 : ℝ) ^ (A.card + 1) *
            ∑ g ∈ cells (show Fin 1 → Fin 1 → Fin 1 from fun _ _ => 0) A,
              (∑ _o ∈ g, (1 : ℝ) * 1) * (∑ _o' ∈ g, (1 : ℝ) * 1)
        | (⊥ : MeasurableSpace Unit)]
      =ᵐ[Measure.dirac ()] fun _ : Unit => ∑ _o : Fin 1, (1 : ℝ) * 1 * 1 := by
  refine condExp_meat_idiosyncratic (⊥ : MeasurableSpace Unit)
    (c := show Fin 1 → Fin 1 → Fin 1 from fun _ _ => 0) (dims := ({0} : Finset (Fin 1)))
    (X := fun _ _ _ => (1 : ℝ)) (eps := fun _ _ => (1 : ℝ)) (sig := fun _ _ => (1 : ℝ))
    (a := 0) (b := 0) (Finset.singleton_nonempty 0)
    (fun _ _ => stronglyMeasurable_const) (fun _ _ => integrable_const _)
    (fun _ _ => integrable_const _) ?_
  intro o o'
  have h2 : (fun _ : Unit => if o = o' then (1 : ℝ) else 0) = fun _ : Unit => (1 : ℝ) := by
    funext _
    rw [Subsingleton.elim o o']
    simp
  have h1 : (fun _ : Unit => (1 : ℝ) * 1) = fun _ : Unit => (1 : ℝ) := by norm_num
  rw [h1, h2, condExp_const bot_le]

/-- An example for `xiMat_opNorm_le`: two observations in a single cluster, `K = 1`,
`X̃ = (1,-1)'`, `P_m = (1/2)ιι'`, `Π = P_m`, `R = I - P_m`, `B = 1`, `G^{(m)}_max = 2`, and
`A^{(m)} = Λ = 0`. In this example `R` and `Ξ_n` are nonzero. -/
theorem xiMat_opNorm_le_witness :
    ‖xiMat (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1)) (1 - witnessPm) witnessX‖
      ≤ (1 : ℝ) ^ 2 *
          (Real.sqrt ((0 : Matrix (Fin 2) (Fin 2) ℝ).trace
              * (2 * (Fintype.card (Fin 2) : ℝ)))
            + Real.sqrt ((0 : Matrix (Fin 2) (Fin 2) ℝ).trace
              * (2 * (Fintype.card (Fin 2) : ℝ)))
            + witnessPm.trace) := by
  have hcard : clusterCard (fun _ : Fin 2 => (0 : Fin 1)) 0 = 2 := by
    simp [clusterCard]
  refine xiMat_opNorm_le (fun _ _ => (0 : Fin 1)) (Finset.singleton_nonempty 0)
    (fun _ => (0 : Fin 1)) ?_ witnessX (Pm := witnessPm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun o o' => ⟨fun _ => rfl, fun _ => ⟨0, Finset.mem_singleton_self 0, rfl⟩⟩
  · exact (sub_sub_cancel _ _).symm
  · rw [add_zero, add_zero]
  · intro o o'
    rw [witnessPm]
    simp only [Matrix.of_apply, hcard]
    norm_num
  · simp
  · simp
  · simp
  · simp
  · intro j k
    have hfil : (Finset.univ.filter fun o : Fin 2 => (0 : Fin 1) = j)
        = (Finset.univ : Finset (Fin 2)) := by
      refine Finset.filter_true_of_mem fun o _ => ?_
      exact Subsingleton.elim _ _
    rw [hfil, Fin.sum_univ_two]
    simp [witnessX]
  · intro o
    rw [Fin.sum_univ_one]
    fin_cases o <;> norm_num [witnessX]
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hj, hcard]
    norm_num

end Witness

end Cgm
end Multiway
