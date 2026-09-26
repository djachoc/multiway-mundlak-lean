import Multiway.GroupCompute
import Multiway.Wald
import Multiway.Sequence
import Multiway.Plugin
import Multiway.CLT
import Multiway.PiHat
import Multiway.SteinCluster
import Mathlib.Data.Finset.Powerset

/-!
# Feasible inference for the diagnostic coefficient

This file formalizes Theorem 12 of the paper (feasible inference for the diagnostic
coefficient) together with Theorem 6 (asymptotic normality of the diagnostic coefficient).
Clause (c) is an exact identity for the mean of the union meat; clause (a) is the consistency
`Υ̂ - Υ_n ⟶^p 0`, assembled from the deterministic bounds of Steps 1–4 over a sequence of designs;
clause (b) is the Wald limit, obtained from `wald_of_clt`.

## Main results

* `piinf_c`: clause (c), both equalities.
* `piinf_a`, `piinf_a_of_step1`, `piinf_a_of_regime1_full`: clause (a).
* `piinf_wald`, `piinf_wald_of_meat`, `piinf_wald_of_meat_restricted`: clause (b).

## Notation

* `ieMeat`, `dimMeat`, `upsilonN` are `n²/N_*` times `Υ̂`, `Υ̂^dim` and `Υ_n`.
* `cellScore z v t` is the cell score `ĝ^{(A)}_t`, and `Multiway.cells c A` the level-`A` cells.
* `Eu o o'` is the second moment of `(u_o, u_{o'})`; `frobNorm` is the Frobenius norm.
-/

namespace Multiway

namespace PiInf

open Finset Matrix

variable {O D L K : Type*}

/-! ## §0 Squared lengths and outer products

`vecSqNorm` is the squared Euclidean length on `ℝ^q`, used so that no `Real.sqrt` is carried
through the Cauchy--Schwarz steps. -/

section Vec

variable [Fintype K] [DecidableEq K]

/-- `‖a‖²` for `a ∈ ℝ^K`. -/
def vecSqNorm (a : K → ℝ) : ℝ := ∑ k, a k ^ 2

omit [DecidableEq K] in
theorem vecSqNorm_nonneg (a : K → ℝ) : 0 ≤ vecSqNorm a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq K] in
theorem vecSqNorm_mul_right (r : ℝ) (a : K → ℝ) :
    vecSqNorm (fun k => a k * r) = vecSqNorm a * r ^ 2 := by
  simp only [vecSqNorm, mul_pow, ← Finset.sum_mul]

omit [DecidableEq K] in
/-- `‖ab'‖_F² = ‖a‖²‖b‖²`. -/
theorem frobSq_vecMulVec (a b : K → ℝ) :
    frobSq (Matrix.vecMulVec a b) = vecSqNorm a * vecSqNorm b := by
  simp only [frobSq, Matrix.vecMulVec_apply, mul_pow, vecSqNorm]
  rw [Finset.sum_mul_sum]

omit [DecidableEq K] in
/-- `‖ab'‖_F = ‖a‖‖b‖`. -/
theorem frobNorm_vecMulVec (a b : K → ℝ) :
    frobNorm (Matrix.vecMulVec a b) = Real.sqrt (vecSqNorm a) * Real.sqrt (vecSqNorm b) := by
  rw [frobNorm, frobSq_vecMulVec, Real.sqrt_mul (vecSqNorm_nonneg a)]

omit [DecidableEq K] in
/-- At one cell, `‖aa' + ab' + ba'‖_F ≤ ‖a‖² + 2‖a‖‖b‖`. -/
theorem frobNorm_outer_three_le (a b : K → ℝ) :
    frobNorm (Matrix.vecMulVec a a + Matrix.vecMulVec a b + Matrix.vecMulVec b a)
      ≤ vecSqNorm a + 2 * (Real.sqrt (vecSqNorm a) * Real.sqrt (vecSqNorm b)) := by
  have h1 : frobNorm (Matrix.vecMulVec a a + Matrix.vecMulVec a b + Matrix.vecMulVec b a)
      ≤ frobNorm (Matrix.vecMulVec a a + Matrix.vecMulVec a b)
        + frobNorm (Matrix.vecMulVec b a) := frobNorm_add_le _ _
  have h2 : frobNorm (Matrix.vecMulVec a a + Matrix.vecMulVec a b)
      ≤ frobNorm (Matrix.vecMulVec a a) + frobNorm (Matrix.vecMulVec a b) := frobNorm_add_le _ _
  have h3 : frobNorm (Matrix.vecMulVec a a) = vecSqNorm a := by
    rw [frobNorm_vecMulVec, Real.mul_self_sqrt (vecSqNorm_nonneg a)]
  have h4 : frobNorm (Matrix.vecMulVec a b)
      = Real.sqrt (vecSqNorm a) * Real.sqrt (vecSqNorm b) := frobNorm_vecMulVec a b
  have h5 : frobNorm (Matrix.vecMulVec b a)
      = Real.sqrt (vecSqNorm a) * Real.sqrt (vecSqNorm b) := by
    rw [frobNorm_vecMulVec, mul_comm]
  linarith

omit [DecidableEq K] in
/-- `‖z̃_o z̃_{o'}'‖_F ≤ B²` whenever `‖z̃_o‖ ≤ B` and `‖z̃_{o'}‖ ≤ B`. -/
theorem frobNorm_vecMulVec_le {a b : K → ℝ} {B : ℝ} (ha : vecSqNorm a ≤ B ^ 2)
    (hb : vecSqNorm b ≤ B ^ 2) : frobNorm (Matrix.vecMulVec a b) ≤ B ^ 2 := by
  rw [frobNorm, frobSq_vecMulVec]
  have h : vecSqNorm a * vecSqNorm b ≤ B ^ 2 * B ^ 2 :=
    mul_le_mul ha hb (vecSqNorm_nonneg b) (sq_nonneg B)
  calc Real.sqrt (vecSqNorm a * vecSqNorm b) ≤ Real.sqrt (B ^ 2 * B ^ 2) := Real.sqrt_le_sqrt h
    _ = B ^ 2 := Real.sqrt_mul_self (sq_nonneg B)

end Vec


/-! ## §1 Cauchy--Schwarz inside a cell

Steps 1, 2 and 4 each bound a sum over the cells of a fixed level by the cell size times a sum
over the observations, via Cauchy--Schwarz inside the cell and `Multiway.sum_over_cells`. -/

section Cells

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

omit [Fintype O] [DecidableEq O] in
/-- Cauchy--Schwarz inside one cell: `(∑_{o ∈ t}|v_o|)² ≤ #t ∑_{o ∈ t} v_o²`. -/
theorem sq_sum_abs_le (t : Finset O) (v : O → ℝ) :
    (∑ o ∈ t, |v o|) ^ 2 ≤ (t.card : ℝ) * ∑ o ∈ t, v o ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := t) (f := fun o => |v o|)
  simpa [sq_abs] using h

/-- **Step 4's cell bound.** With every level-`F` cell holding at most `b` observations,
`∑_{t ∈ 𝒯_F}(∑_{o ∈ t}|v_o|)² ≤ b ∑_o v_o²`. -/
theorem sum_cells_sq_abs_le (c : D → O → L) (F : Finset D) (v : O → ℝ) {b : ℝ}
    (hb : ∀ t ∈ cells c F, (t.card : ℝ) ≤ b) :
    ∑ t ∈ cells c F, (∑ o ∈ t, |v o|) ^ 2 ≤ b * ∑ o : O, v o ^ 2 := by
  have hstep : ∀ t ∈ cells c F, (∑ o ∈ t, |v o|) ^ 2 ≤ b * ∑ o ∈ t, v o ^ 2 := by
    intro t ht
    refine (sq_sum_abs_le t v).trans ?_
    exact mul_le_mul_of_nonneg_right (hb t ht) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine (Finset.sum_le_sum hstep).trans_eq ?_
  rw [← Finset.mul_sum, sum_over_cells c F fun o => v o ^ 2]

/-- `Δ_FΔ_F' ⪯ G_max I`, as a quadratic-form inequality:
`x'Δ_FΔ_F'x = ∑_t(∑_{o ∈ t}x_o)² ≤ G_max‖x‖²` when every level-`F` cell holds at most `G_max`
observations. -/
theorem shareQuad_le (c : D → O → L) (F : Finset D) (x : O → ℝ) {g : ℝ}
    (hg : ∀ t ∈ cells c F, (t.card : ℝ) ≤ g) :
    ∑ o : O, ∑ o' : O, (if SameOn c F o o' then x o * x o' else 0) ≤ g * ∑ o : O, x o ^ 2 := by
  rw [← sum_cells_pair c F fun o o' => x o * x o']
  have hstep : ∀ t ∈ cells c F, (∑ o ∈ t, ∑ o' ∈ t, x o * x o') ≤ g * ∑ o ∈ t, x o ^ 2 := by
    intro t ht
    have hsq : (∑ o ∈ t, ∑ o' ∈ t, x o * x o') = (∑ o ∈ t, x o) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
    rw [hsq]
    exact (sq_sum_le_card_mul_sum_sq (s := t) (f := x)).trans
      (mul_le_mul_of_nonneg_right (hg t ht) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  refine (Finset.sum_le_sum hstep).trans_eq ?_
  rw [← Finset.mul_sum, sum_over_cells c F fun o => x o ^ 2]

variable [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
/-- With every level-`F` cell holding at most `b` observations,
`∑_{t ∈ 𝒯_F} ‖∑_{o ∈ t} a_o‖² ≤ b ∑_o ‖a_o‖²`. -/
theorem sum_cells_vecSqNorm_le (c : D → O → L) (F : Finset D) (a : O → K → ℝ) {b : ℝ}
    (hb : ∀ t ∈ cells c F, (t.card : ℝ) ≤ b) :
    ∑ t ∈ cells c F, vecSqNorm (fun k => ∑ o ∈ t, a o k) ≤ b * ∑ o : O, vecSqNorm (a o) := by
  have hstep : ∀ t ∈ cells c F, vecSqNorm (fun k => ∑ o ∈ t, a o k)
      ≤ b * ∑ o ∈ t, vecSqNorm (a o) := by
    intro t ht
    have h1 : vecSqNorm (fun k => ∑ o ∈ t, a o k) ≤ (t.card : ℝ) * ∑ o ∈ t, vecSqNorm (a o) := by
      have hk : ∀ k : K, (∑ o ∈ t, a o k) ^ 2 ≤ (t.card : ℝ) * ∑ o ∈ t, a o k ^ 2 :=
        fun k => sq_sum_le_card_mul_sum_sq (s := t) (f := fun o => a o k)
      calc vecSqNorm (fun k => ∑ o ∈ t, a o k) = ∑ k, (∑ o ∈ t, a o k) ^ 2 := rfl
        _ ≤ ∑ k : K, (t.card : ℝ) * ∑ o ∈ t, a o k ^ 2 :=
            Finset.sum_le_sum fun k _ => hk k
        _ = (t.card : ℝ) * ∑ o ∈ t, vecSqNorm (a o) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            rfl
    refine h1.trans (mul_le_mul_of_nonneg_right (hb t ht) ?_)
    exact Finset.sum_nonneg fun _ _ => vecSqNorm_nonneg _
  refine (Finset.sum_le_sum hstep).trans_eq ?_
  rw [← Finset.mul_sum, sum_over_cells c F fun o => vecSqNorm (a o)]

omit [DecidableEq K] in
/-- **Step 1's bound on the cross-cell aggregates.** At `F = {m,m'}`,
`∑_{j,j'}‖ζ^{(mm')}_{jj'}‖² ≤ B²c^{(2)}_max n`. -/
theorem step1_zeta_bound (c : D → O → L) (F : Finset D) (z : O → K → ℝ) {B b : ℝ}
    (hz : ∀ o, vecSqNorm (z o) ≤ B ^ 2) (hb0 : 0 ≤ b)
    (hb : ∀ t ∈ cells c F, (t.card : ℝ) ≤ b) :
    ∑ t ∈ cells c F, vecSqNorm (fun k => ∑ o ∈ t, z o k)
      ≤ b * ((Fintype.card O : ℝ) * B ^ 2) := by
  refine (sum_cells_vecSqNorm_le c F z hb).trans (mul_le_mul_of_nonneg_left ?_ hb0)
  calc ∑ o : O, vecSqNorm (z o) ≤ ∑ _o : O, B ^ 2 := Finset.sum_le_sum fun o _ => hz o
    _ = (Fintype.card O : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

end Cells

/-! ## §2 The cell scores and the three meats

The inclusion--exclusion meat, the dimension-wise meat, and the pairwise form they both
collapse to. -/

section Meats

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]

/-- `ĝ^{(A)}_t := ∑_{o ⊙ A = t} z̃_o û_o`, the cell score. -/
def cellScore (z : O → K → ℝ) (v : O → ℝ) (t : Finset O) : K → ℝ := fun k => ∑ o ∈ t, z o k * v o

omit [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K] in
theorem cellScore_eq (z : O → K → ℝ) (v : O → ℝ) (t : Finset O) :
    cellScore z v t = fun k => ∑ o ∈ t, z o k * v o := rfl

/-- `(n²/N_*) Υ̂`, the inclusion--exclusion meat. -/
noncomputable def ieMeat (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (v : O → ℝ) :
    Matrix K K ℝ :=
  ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty), (-1 : ℝ) ^ (A.card + 1) •
    ∑ t ∈ cells c A, Matrix.vecMulVec (cellScore z v t) (cellScore z v t)

/-- `(n²/N_*) Υ̂^dim := ∑_m ∑_j ĝ^{(m)}_j ĝ^{(m)′}_j`, the sum of the `|A| = 1` terms. -/
noncomputable def dimMeat (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (v : O → ℝ) :
    Matrix K K ℝ :=
  ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
    Matrix.vecMulVec (cellScore z v t) (cellScore z v t)

/-- `∑_{o,o'} w(o,o') v_o v_{o'} z̃_o z̃_{o'}'`, the pairwise form of Step 3. -/
noncomputable def pairForm (z : O → K → ℝ) (v : O → ℝ) (w : O → O → ℝ) : Matrix K K ℝ :=
  ∑ o : O, ∑ o' : O, (w o o' * (v o * v o')) • Matrix.vecMulVec (z o) (z o')

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
theorem pairForm_sub (z : O → K → ℝ) (v : O → ℝ) (w₁ w₂ : O → O → ℝ) :
    pairForm z v w₁ - pairForm z v w₂ = pairForm z v (fun o o' => w₁ o o' - w₂ o o') := by
  simp only [pairForm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [← sub_smul, sub_mul]

omit [DecidableEq K] in
/-- **Step 3, first identity.** `(n²/N_*)Υ̂ = ∑_{o,o'} 𝟙{E(o,o') ≠ ∅} s_o s_{o'}'`, by
Lemma SM.B.7 at the `M` fixed-effect dimensions. -/
theorem ieMeat_eq_pairForm (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (v : O → ℝ) :
    ieMeat c dims z v
      = pairForm z v (fun o o' => if Linked c dims o o' then (1 : ℝ) else 0) := by
  simp only [ieMeat, cellScore_eq]
  rw [multiway_meat_inclusion_exclusion c dims z v, pairForm]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  by_cases h : Linked c dims o o' <;> simp [h]

omit [Fintype K] [DecidableEq K] in
/-- **Step 3, second identity.** `(n²/N_*)Υ̂^dim = ∑_{o,o'} #E(o,o') s_o s_{o'}'`, since
`∑_m 𝟙{i_m(o) = i_m(o')} = #E(o,o')`. -/
theorem dimMeat_eq_pairForm (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (v : O → ℝ) :
    dimMeat c dims z v = pairForm z v (fun o o' => ((sharedDims c dims o o').card : ℝ)) := by
  classical
  ext a b
  simp only [dimMeat, pairForm, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  have hcell : ∀ m : D,
      ∑ t ∈ cells c ({m} : Finset D), cellScore z v t a * cellScore z v t b
        = ∑ o : O, ∑ o' : O,
            if SameOn c ({m} : Finset D) o o' then (z o a * v o) * (z o' b * v o') else 0 :=
    fun m => sum_cells_mul (c := c) (A := ({m} : Finset D)) (fun o => z o a * v o)
      (fun o' => z o' b * v o')
  rw [Finset.sum_congr rfl fun m _ => hcell m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o' _ => ?_
  have hsplit : ∀ m : D,
      (if SameOn c ({m} : Finset D) o o' then (z o a * v o) * (z o' b * v o') else 0)
        = ((z o a * v o) * (z o' b * v o')) *
            (if SameOn c ({m} : Finset D) o o' then (1 : ℝ) else 0) := by
    intro m
    by_cases h : SameOn c ({m} : Finset D) o o' <;> simp [h]
  rw [Finset.sum_congr rfl fun m _ => hsplit m, ← Finset.mul_sum]
  have hcount : ∑ m ∈ dims, (if SameOn c ({m} : Finset D) o o' then (1 : ℝ) else 0)
      = ((sharedDims c dims o o').card : ℝ) := by
    rw [Finset.sum_boole, sharedDims]
    congr 2
    refine Finset.filter_congr fun m _ => ?_
    constructor
    · intro h; exact h m (Finset.mem_singleton_self m)
    · intro h j hj; rw [Finset.mem_singleton.1 hj]; exact h
  rw [hcount]
  ring

omit [DecidableEq K] in
/-- **Step 3.** `(n²/N_*)(Υ̂^dim - Υ̂) = ∑_{o,o'}(#E(o,o') - 1)_+ s_o s_{o'}'`. -/
theorem dimMeat_sub_ieMeat (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (v : O → ℝ) :
    dimMeat c dims z v - ieMeat c dims z v
      = pairForm z v (fun o o' => (((sharedDims c dims o o').card - 1 : ℕ) : ℝ)) := by
  rw [dimMeat_eq_pairForm, ieMeat_eq_pairForm, pairForm_sub]
  congr 1
  funext o o'
  by_cases h : Linked c dims o o'
  · have hne : (sharedDims c dims o o').Nonempty := by
      obtain ⟨j, hj, hcj⟩ := h
      exact ⟨j, Finset.mem_filter.2 ⟨hj, hcj⟩⟩
    have h1 : 1 ≤ (sharedDims c dims o o').card := Finset.card_pos.2 hne
    have hind : (if Linked c dims o o' then (1 : ℝ) else 0) = 1 := by simp [h]
    rw [hind, Nat.cast_sub h1, Nat.cast_one]
  · have he : sharedDims c dims o o' = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      exact h ⟨j, (Finset.mem_filter.1 hj).1, (Finset.mem_filter.1 hj).2⟩
    have hind : (if Linked c dims o o' then (1 : ℝ) else 0) = 0 := by simp [h]
    rw [hind, he]
    simp

omit [DecidableEq K] in
/-- **Step 2's Cauchy--Schwarz bound.**
`∑_{m,j}‖ĝ^{(m)}_j - g^{(m)}_j‖² ≤ B²MG_max‖w‖²`, where `w` is the vector whose cell aggregates
are bounded (`w = P_{C_1}u` in Step 2). -/
theorem step2_score_diff_bound (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (w : O → ℝ)
    {B b : ℝ} (hz : ∀ o, vecSqNorm (z o) ≤ B ^ 2) (hb0 : 0 ≤ b)
    (hb : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), (t.card : ℝ) ≤ b) :
    ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D), vecSqNorm (cellScore z w t)
      ≤ (dims.card : ℝ) * (b * (B ^ 2 * ∑ o : O, w o ^ 2)) := by
  have hone : ∀ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D), vecSqNorm (cellScore z w t)
      ≤ b * (B ^ 2 * ∑ o : O, w o ^ 2) := by
    intro m hm
    have h1 : ∑ t ∈ cells c ({m} : Finset D), vecSqNorm (cellScore z w t)
        ≤ b * ∑ o : O, vecSqNorm (fun k => z o k * w o) :=
      sum_cells_vecSqNorm_le c ({m} : Finset D) (fun o k => z o k * w o) (hb m hm)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hb0)
    calc ∑ o : O, vecSqNorm (fun k => z o k * w o)
        = ∑ o : O, vecSqNorm (z o) * w o ^ 2 :=
          Finset.sum_congr rfl fun o _ => vecSqNorm_mul_right (w o) (z o)
      _ ≤ ∑ o : O, B ^ 2 * w o ^ 2 := by
          refine Finset.sum_le_sum fun o _ => ?_
          exact mul_le_mul_of_nonneg_right (hz o) (sq_nonneg _)
      _ = B ^ 2 * ∑ o : O, w o ^ 2 := by rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hone).trans_eq ?_
  rw [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq D] [DecidableEq K] in
/-- **Step 2's closing inequality.** With `S_d := ∑_{m,j}‖ĝ^{(m)}_j - g^{(m)}_j‖²` and
`S_g := ∑_{m,j}‖g^{(m)}_j‖²`, in every realization
`‖Υ̂^dim(v) - Υ̂^dim(u)‖_F ≤ S_d + 2√(S_dS_g)`. -/
theorem frobNorm_dimMeat_sub_dimMeat_le (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (v u : O → ℝ) :
    frobNorm (dimMeat c dims z v - dimMeat c dims z u)
      ≤ (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            vecSqNorm (cellScore z (fun o => v o - u o) t))
        + 2 * Real.sqrt
            ((∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
                vecSqNorm (cellScore z (fun o => v o - u o) t))
              * ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
                  vecSqNorm (cellScore z u t)) := by
  classical
  have hFdnn : ∀ t : Finset O, 0 ≤ vecSqNorm (cellScore z (fun o => v o - u o) t) :=
    fun t => vecSqNorm_nonneg _
  have hFgnn : ∀ t : Finset O, 0 ≤ vecSqNorm (cellScore z u t) := fun t => vecSqNorm_nonneg _
  -- the algebraic identity `ĝĝ' - gg' = dd' + dg' + gd'`, cell by cell
  have hmat : ∀ t : Finset O,
      Matrix.vecMulVec (cellScore z v t) (cellScore z v t)
          - Matrix.vecMulVec (cellScore z u t) (cellScore z u t)
        = Matrix.vecMulVec (cellScore z (fun o => v o - u o) t)
              (cellScore z (fun o => v o - u o) t)
          + Matrix.vecMulVec (cellScore z (fun o => v o - u o) t) (cellScore z u t)
          + Matrix.vecMulVec (cellScore z u t) (cellScore z (fun o => v o - u o) t) := by
    intro t
    ext a b
    have hs : ∀ k : K, (∑ o ∈ t, z o k * (v o - u o))
        = (∑ o ∈ t, z o k * v o) - ∑ o ∈ t, z o k * u o := by
      intro k
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun o _ => by ring
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply, cellScore, hs]
    ring
  have hsub : dimMeat c dims z v - dimMeat c dims z u
      = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
          (Matrix.vecMulVec (cellScore z (fun o => v o - u o) t)
              (cellScore z (fun o => v o - u o) t)
            + Matrix.vecMulVec (cellScore z (fun o => v o - u o) t) (cellScore z u t)
            + Matrix.vecMulVec (cellScore z u t) (cellScore z (fun o => v o - u o) t)) := by
    rw [dimMeat, dimMeat, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => hmat t
  -- the triangle inequality inside one cell
  have hterm : ∀ t : Finset O,
      frobNorm (Matrix.vecMulVec (cellScore z (fun o => v o - u o) t)
              (cellScore z (fun o => v o - u o) t)
            + Matrix.vecMulVec (cellScore z (fun o => v o - u o) t) (cellScore z u t)
            + Matrix.vecMulVec (cellScore z u t) (cellScore z (fun o => v o - u o) t))
        ≤ vecSqNorm (cellScore z (fun o => v o - u o) t)
          + 2 * (Real.sqrt (vecSqNorm (cellScore z (fun o => v o - u o) t))
              * Real.sqrt (vecSqNorm (cellScore z u t))) := by
    intro t
    exact frobNorm_outer_three_le (cellScore z (fun o => v o - u o) t) (cellScore z u t)
  -- the Cauchy--Schwarz inequality, inside each dimension's cells and then across dimensions
  have hcs : ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
        (Real.sqrt (vecSqNorm (cellScore z (fun o => v o - u o) t))
          * Real.sqrt (vecSqNorm (cellScore z u t)))
      ≤ Real.sqrt (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            vecSqNorm (cellScore z (fun o => v o - u o) t))
        * Real.sqrt (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            vecSqNorm (cellScore z u t)) := by
    refine (Finset.sum_le_sum fun m _ => Real.sum_sqrt_mul_sqrt_le _ hFdnn hFgnn).trans ?_
    exact Real.sum_sqrt_mul_sqrt_le _
      (fun m => Finset.sum_nonneg fun t _ => hFdnn t)
      (fun m => Finset.sum_nonneg fun t _ => hFgnn t)
  have hsplit : ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
        (vecSqNorm (cellScore z (fun o => v o - u o) t)
          + 2 * (Real.sqrt (vecSqNorm (cellScore z (fun o => v o - u o) t))
              * Real.sqrt (vecSqNorm (cellScore z u t))))
      = (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            vecSqNorm (cellScore z (fun o => v o - u o) t))
        + 2 * ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            (Real.sqrt (vecSqNorm (cellScore z (fun o => v o - u o) t))
              * Real.sqrt (vecSqNorm (cellScore z u t))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hSdnn : (0 : ℝ) ≤ ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
      vecSqNorm (cellScore z (fun o => v o - u o) t) :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun t _ => hFdnn t
  rw [hsub]
  refine le_trans (frobNorm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun m _ =>
    (frobNorm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => hterm t)) ?_
  rw [hsplit, Real.sqrt_mul hSdnn]
  linarith [hcs]

end Meats

/-! ## §3 Step 4: the bound on `D`

Since `(k-1)_+ ≤ C(k,2)`, `‖D‖ ≤ (N_*B²/n²)C(M,2)c^{(2)}_max‖û‖²`. -/

section Step4

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]

/-- `(k-1)_+ ≤ C(k,2)` for every `k ≥ 0`, with `(k-1)_+` the truncated subtraction in `ℕ`. -/
theorem sub_one_le_choose_two (k : ℕ) : k - 1 ≤ k.choose 2 := by
  cases k with
  | zero => simp
  | succ j =>
      rw [Nat.add_sub_cancel, Nat.choose_succ_succ, Nat.choose_one_right]
      exact Nat.le_add_right _ _

omit [Fintype O] [DecidableEq O] in
/-- The level-two subsets of `dims` contained in `E(o,o')` are exactly the level-two subsets of
`E(o,o')`, so their number is `C(#E(o,o'),2)`. -/
theorem card_filter_powersetCard_two (c : D → O → L) (dims : Finset D) (o o' : O) :
    ((Finset.powersetCard 2 dims).filter (fun e => e ⊆ sharedDims c dims o o')).card
      = (sharedDims c dims o o').card.choose 2 := by
  classical
  have hsub : sharedDims c dims o o' ⊆ dims := Finset.filter_subset _ _
  have hset : (Finset.powersetCard 2 dims).filter (fun e => e ⊆ sharedDims c dims o o')
      = Finset.powersetCard 2 (sharedDims c dims o o') := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hE⟩; exact ⟨hE, hcard⟩
    · rintro ⟨hE, hcard⟩; exact ⟨⟨hE.trans hsub, hcard⟩, hE⟩
  rw [hset, Finset.card_powersetCard]

/-- **Step 4's counting step.** `(#E(o,o') - 1)_+ ≤ ∑_{|e|=2}𝟙{o ⊙ e = o' ⊙ e}`. -/
theorem step4_weight_le (c : D → O → L) (dims : Finset D) (o o' : O) :
    (((sharedDims c dims o o').card - 1 : ℕ) : ℝ)
      ≤ ∑ e ∈ Finset.powersetCard 2 dims, (if SameOn c e o o' then (1 : ℝ) else 0) := by
  classical
  have hsum : ∑ e ∈ Finset.powersetCard 2 dims, (if SameOn c e o o' then (1 : ℝ) else 0)
      = (((Finset.powersetCard 2 dims).filter
            (fun e => e ⊆ sharedDims c dims o o')).card : ℝ) := by
    rw [Finset.sum_boole]
    congr 2
    exact Finset.filter_congr fun e he =>
      sameOn_iff_subset (c := c) (dims := dims) (Finset.mem_powersetCard.1 he).1
  rw [hsum, card_filter_powersetCard_two c dims o o']
  exact_mod_cast sub_one_le_choose_two _

omit [DecidableEq O] [DecidableEq K] in
/-- The triangle inequality applied to the pairwise form, with `‖z̃_o z̃_{o'}'‖_F ≤ B²`. -/
theorem frobNorm_pairForm_le (z : O → K → ℝ) (v : O → ℝ) (w : O → O → ℝ) {B : ℝ}
    (hz : ∀ o, vecSqNorm (z o) ≤ B ^ 2) :
    frobNorm (pairForm z v w) ≤ B ^ 2 * ∑ o : O, ∑ o' : O, |w o o'| * (|v o| * |v o'|) := by
  have hterm : ∀ o o' : O,
      frobNorm ((w o o' * (v o * v o')) • Matrix.vecMulVec (z o) (z o'))
        ≤ B ^ 2 * (|w o o'| * (|v o| * |v o'|)) := by
    intro o o'
    rw [frobNorm_smul]
    have h1 : frobNorm (Matrix.vecMulVec (z o) (z o')) ≤ B ^ 2 :=
      frobNorm_vecMulVec_le (hz o) (hz o')
    have h2 : |w o o' * (v o * v o')| = |w o o'| * (|v o| * |v o'|) := by
      rw [abs_mul, abs_mul]
    rw [h2, mul_comm (B ^ 2)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  calc frobNorm (pairForm z v w)
      ≤ ∑ o : O, frobNorm (∑ o' : O, (w o o' * (v o * v o')) • Matrix.vecMulVec (z o) (z o')) :=
        frobNorm_sum_le _ _
    _ ≤ ∑ o : O, ∑ o' : O, B ^ 2 * (|w o o'| * (|v o| * |v o'|)) := by
        refine Finset.sum_le_sum fun o _ => ?_
        exact (frobNorm_sum_le _ _).trans (Finset.sum_le_sum fun o' _ => hterm o o')
    _ = B ^ 2 * ∑ o : O, ∑ o' : O, |w o o'| * (|v o| * |v o'|) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun o _ => (Finset.mul_sum _ _ _).symm

omit [DecidableEq K] in
/-- **Step 4.** In every realization, `‖Υ̂^dim - Υ̂‖_F ≤ B² C(M,2) c^{(2)}_max ‖û‖²`, where `b`
bounds the size of a level-two cell. -/
theorem step4_bound (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (v : O → ℝ) {B b : ℝ}
    (hz : ∀ o, vecSqNorm (z o) ≤ B ^ 2)
    (hb : ∀ e ∈ Finset.powersetCard 2 dims, ∀ t ∈ cells c e, (t.card : ℝ) ≤ b) :
    frobNorm (dimMeat c dims z v - ieMeat c dims z v)
      ≤ B ^ 2 * (((Finset.powersetCard 2 dims).card : ℝ) * (b * ∑ o : O, v o ^ 2)) := by
  classical
  rw [dimMeat_sub_ieMeat]
  refine (frobNorm_pairForm_le z v _ hz).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg B))
  have hw : ∀ o o' : O,
      |(((sharedDims c dims o o').card - 1 : ℕ) : ℝ)| * (|v o| * |v o'|)
        ≤ ∑ e ∈ Finset.powersetCard 2 dims,
            (if SameOn c e o o' then |v o| * |v o'| else 0) := by
    intro o o'
    rw [abs_of_nonneg (by positivity)]
    have hsum : ∑ e ∈ Finset.powersetCard 2 dims,
        (if SameOn c e o o' then |v o| * |v o'| else 0)
          = (∑ e ∈ Finset.powersetCard 2 dims, (if SameOn c e o o' then (1 : ℝ) else 0))
              * (|v o| * |v o'|) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h : SameOn c e o o' <;> simp [h]
    rw [hsum]
    exact mul_le_mul_of_nonneg_right (step4_weight_le c dims o o') (by positivity)
  calc ∑ o : O, ∑ o' : O,
        |(((sharedDims c dims o o').card - 1 : ℕ) : ℝ)| * (|v o| * |v o'|)
      ≤ ∑ o : O, ∑ o' : O, ∑ e ∈ Finset.powersetCard 2 dims,
          (if SameOn c e o o' then |v o| * |v o'| else 0) :=
        Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ => hw o o'
    _ = ∑ e ∈ Finset.powersetCard 2 dims, ∑ t ∈ cells c e, (∑ o ∈ t, |v o|) ^ 2 := by
        have hswap : ∀ o : O, ∑ o' : O, ∑ e ∈ Finset.powersetCard 2 dims,
            (if SameOn c e o o' then |v o| * |v o'| else 0)
              = ∑ e ∈ Finset.powersetCard 2 dims, ∑ o' : O,
                  (if SameOn c e o o' then |v o| * |v o'| else 0) :=
          fun o => Finset.sum_comm
        rw [Finset.sum_congr rfl fun o _ => hswap o, Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← sum_cells_pair c e (fun o o' => |v o| * |v o'|)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [pow_two, Finset.sum_mul_sum]
    _ ≤ ∑ _e ∈ Finset.powersetCard 2 dims, b * ∑ o : O, v o ^ 2 :=
        Finset.sum_le_sum fun e he => sum_cells_sq_abs_le c e v (hb e he)
    _ = ((Finset.powersetCard 2 dims).card : ℝ) * (b * ∑ o : O, v o ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Step4

/-! ## §4 Clause (c)

The second moment `Eu(o,o') = ∑_m ς²_m𝟙{i_m(o)=i_m(o')} + 𝟙{o=o'}σ²_ε(o)` enters as the
hypothesis `hEu`. -/

section ClauseC

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]

/-- `∑_{o ∈ t} z̃_o`, the category aggregate `z^{(m)}_j` at a level-`{m}` cell. -/
def cellVec (z : O → K → ℝ) (t : Finset O) : K → ℝ := fun k => ∑ o ∈ t, z o k

/-- The inclusion--exclusion meat with the second moment `Eu(o,o')` in place of `u_o u_{o'}`;
this is `(n²/N_*)` times the mean of the union meat. -/
noncomputable def ieMeatKer (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (Eu : O → O → ℝ) : Matrix K K ℝ :=
  ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty), (-1 : ℝ) ^ (A.card + 1) •
    ∑ t ∈ cells c A, ∑ o ∈ t, ∑ o' ∈ t, Eu o o' • Matrix.vecMulVec (z o) (z o')

/-- `∑_{o,o'} Eu(o,o') z̃_o z̃_{o'}'`, which is `(n²/N_*)` times the variance of the score. -/
noncomputable def condVarScore (z : O → K → ℝ) (Eu : O → O → ℝ) : Matrix K K ℝ :=
  ∑ o : O, ∑ o' : O, Eu o o' • Matrix.vecMulVec (z o) (z o')

/-- `(n²/N_*) Υ_n = ∑_m ς²_m ∑_j z^{(m)}_j z^{(m)′}_j`. -/
noncomputable def upsilonN (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (vr : D → ℝ) :
    Matrix K K ℝ :=
  ∑ m ∈ dims, (vr m ^ 2) • ∑ t ∈ cells c ({m} : Finset D),
    Matrix.vecMulVec (cellVec z t) (cellVec z t)

omit [Fintype K] [DecidableEq K] in
/-- Lemma SM.B.7 for an arbitrary pair kernel `Eu(o,o')` in place of the rank-one weight
`v_o v_{o'}`. -/
theorem ieMeatKer_eq_pairKer (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (Eu : O → O → ℝ) :
    ieMeatKer c dims z Eu
      = ∑ o : O, ∑ o' : O,
          (if Linked c dims o o' then Eu o o' else 0) • Matrix.vecMulVec (z o) (z o') := by
  classical
  ext a b
  simp only [ieMeatKer, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  have hcells : ∀ A : Finset D,
      ∑ t ∈ cells c A, ∑ o ∈ t, ∑ o' ∈ t, Eu o o' * (z o a * z o' b)
        = ∑ o : O, ∑ o' : O, if SameOn c A o o' then Eu o o' * (z o a * z o' b) else 0 :=
    fun A => sum_cells_pair c A fun o o' => Eu o o' * (z o a * z o' b)
  rw [Finset.sum_congr rfl fun A _ => by rw [hcells A]]
  have hpush : ∀ A : Finset D,
      (-1 : ℝ) ^ (A.card + 1) *
          (∑ o : O, ∑ o' : O, if SameOn c A o o' then Eu o o' * (z o a * z o' b) else 0)
        = ∑ o : O, ∑ o' : O, (Eu o o' * (z o a * z o' b)) *
            ((-1 : ℝ) ^ (A.card + 1) * (if SameOn c A o o' then (1 : ℝ) else 0)) := by
    intro A
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun o' _ => ?_
    by_cases h : SameOn c A o o'
    · have h1 : (if SameOn c A o o' then Eu o o' * (z o a * z o' b) else 0)
          = Eu o o' * (z o a * z o' b) := by simp [h]
      have h2 : (if SameOn c A o o' then (1 : ℝ) else 0) = 1 := by simp [h]
      rw [h1, h2]; ring
    · have h1 : (if SameOn c A o o' then Eu o o' * (z o a * z o' b) else 0) = 0 := by simp [h]
      have h2 : (if SameOn c A o o' then (1 : ℝ) else 0) = 0 := by simp [h]
      rw [h1, h2]; ring
  rw [Finset.sum_congr rfl fun A _ => hpush A, Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [← Finset.mul_sum, weight_eq (c := c) (dims := dims) o o']
  by_cases h : Linked c dims o o' <;> simp [h]

omit [Fintype K] [DecidableEq K] in
/-- **Theorem 12(c).** Given the second-moment identity `hEu`,
(i) the mean of the union meat equals `(N_*/n²)` times the variance of the score, and
(ii) that variance is `Υ_n + ∑_o z̃_o z̃_o' σ²_ε(o)`. The hypothesis `hdims` (`M ≥ 1`) is
needed: at `dims = ∅` no pair is linked while the diagonal of `Eu` does not vanish. -/
theorem piinf_c (c : D → O → L) (dims : Finset D) (hdims : dims.Nonempty) (z : O → K → ℝ)
    (Eu : O → O → ℝ) (vr : D → ℝ) (sg : O → ℝ)
    (hEu : ∀ o o', Eu o o'
      = (∑ m ∈ dims, vr m ^ 2 * (if c m o = c m o' then (1 : ℝ) else 0))
        + (if o = o' then sg o ^ 2 else 0)) :
    ieMeatKer c dims z Eu = condVarScore z Eu
      ∧ condVarScore z Eu
          = upsilonN c dims z vr + ∑ o : O, (sg o ^ 2) • Matrix.vecMulVec (z o) (z o) := by
  classical
  refine ⟨?_, ?_⟩
  · -- (i): `Eu` vanishes off the linked pairs
    rw [ieMeatKer_eq_pairKer, condVarScore]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
    by_cases h : Linked c dims o o'
    · simp [h]
    · have hzero : Eu o o' = 0 := by
        rw [hEu o o']
        have h1 : ∀ m ∈ dims, vr m ^ 2 * (if c m o = c m o' then (1 : ℝ) else 0) = 0 := by
          intro m hm
          have hne : ¬ c m o = c m o' := fun hc => h ⟨m, hm, hc⟩
          simp [hne]
        have h2 : ¬ o = o' := by
          rintro rfl
          obtain ⟨m, hm⟩ := hdims
          exact h ⟨m, hm, rfl⟩
        rw [Finset.sum_congr rfl h1]
        simp [h2]
      simp [h, hzero]
  · -- (ii): the category part is `Υ_n`, the idiosyncratic part is the diagonal
    ext a b
    simp only [condVarScore, upsilonN, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul]
    have hexp : ∀ o o' : O, Eu o o' * (z o a * z o' b)
        = (∑ m ∈ dims, vr m ^ 2 * ((if SameOn c ({m} : Finset D) o o' then (1 : ℝ) else 0)
              * (z o a * z o' b)))
          + (if o = o' then sg o ^ 2 * (z o a * z o' b) else 0) := by
      intro o o'
      rw [hEu o o', add_mul, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hs : (if SameOn c ({m} : Finset D) o o' then (1 : ℝ) else 0)
            = (if c m o = c m o' then (1 : ℝ) else 0) := by
          by_cases h : c m o = c m o'
          · have : SameOn c ({m} : Finset D) o o' := by
              intro j hj; rw [Finset.mem_singleton.1 hj]; exact h
            simp [this, h]
          · have hno : ¬ SameOn c ({m} : Finset D) o o' :=
              fun hc => h (hc m (Finset.mem_singleton_self m))
            simp [hno, h]
        rw [hs]; ring
      · by_cases h : o = o' <;> simp [h]
    rw [Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => hexp o o']
    simp only [Finset.sum_add_distrib]
    congr 1
    · -- the category part
      have hcat : ∀ m : D, (∑ o : O, ∑ o' : O,
          vr m ^ 2 * ((if SameOn c ({m} : Finset D) o o' then (1 : ℝ) else 0)
            * (z o a * z o' b)))
            = vr m ^ 2 * ∑ t ∈ cells c ({m} : Finset D), cellVec z t a * cellVec z t b := by
        intro m
        simp only [cellVec]
        rw [sum_cells_mul (c := c) (A := ({m} : Finset D)) (fun o => z o a) (fun o' => z o' b),
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun o' _ => ?_
        by_cases h : SameOn c ({m} : Finset D) o o' <;> simp [h]
      calc (∑ o : O, ∑ o' : O, ∑ m ∈ dims,
              vr m ^ 2 * ((if SameOn c ({m} : Finset D) o o' then (1 : ℝ) else 0)
                * (z o a * z o' b)))
          = ∑ m ∈ dims, ∑ o : O, ∑ o' : O,
              vr m ^ 2 * ((if SameOn c ({m} : Finset D) o o' then (1 : ℝ) else 0)
                * (z o a * z o' b)) := by
            rw [Finset.sum_congr rfl fun o _ => Finset.sum_comm, Finset.sum_comm]
        _ = ∑ m ∈ dims, vr m ^ 2 *
              ∑ t ∈ cells c ({m} : Finset D), cellVec z t a * cellVec z t b :=
            Finset.sum_congr rfl fun m _ => hcat m
    · -- the idiosyncratic part
      refine Finset.sum_congr rfl fun o _ => ?_
      simp

end ClauseC

/-! ## §5 Clause (a)'s final assembly, and clause (b) -/

section Probability

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

section Assembly

variable [Fintype K] [DecidableEq K]

omit [DecidableEq K] [IsProbabilityMeasure P] in
/-- **The last sentence of Step 4.** From `hstep2` (`Υ̂^dim - Υ_n ⟶^p 0`) and `hstep4`
(`D ⟶^p 0`), the triangle inequality gives `Υ̂ - Υ_n ⟶^p 0`. -/
theorem piinf_a_of_steps {Ups : ℕ → Matrix K K ℝ} {Ud Uh : ℕ → Ω → Matrix K K ℝ}
    (hstep2 : TendstoInMeasure P (fun n ω => frobNorm (Ud n ω - Ups n)) atTop (fun _ => 0))
    (hstep4 : TendstoInMeasure P (fun n ω => frobNorm (Ud n ω - Uh n ω)) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => frobNorm (Uh n ω - Ups n)) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hstep2 hstep4 ⊢
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  have hsub : ∀ n : ℕ,
      {ω | ε ≤ dist (frobNorm (Uh n ω - Ups n)) ((fun _ : Ω => (0 : ℝ)) ω)}
        ⊆ {ω | ε / 2 ≤ dist (frobNorm (Ud n ω - Ups n)) ((fun _ : Ω => (0 : ℝ)) ω)}
          ∪ {ω | ε / 2 ≤ dist (frobNorm (Ud n ω - Uh n ω)) ((fun _ : Ω => (0 : ℝ)) ω)} := by
    intro n ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg (Wald.frobNorm_nonneg _)] at hω ⊢
    by_contra hc
    rw [not_or, not_le, not_le] at hc
    obtain ⟨h1, h2⟩ := hc
    have hdec : Uh n ω - Ups n = (Ud n ω - Ups n) - (Ud n ω - Uh n ω) := by abel
    have hle : frobNorm (Uh n ω - Ups n)
        ≤ frobNorm (Ud n ω - Ups n) + frobNorm (Ud n ω - Uh n ω) := by
      rw [hdec]; exact frobNorm_sub_le _ _
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
    (fun n => (measure_mono (hsub n)).trans (measure_union_le _ _))
  have h := (hstep2 (ε / 2) hhalf).add (hstep4 (ε / 2) hhalf)
  simpa using h

end Assembly

/-! ## §5b The `O_p` bounds of Steps 2 and 4

Both statements have the shape `o(1) × O_p(1) = o_p(1)`
(`Sequence.tendstoInProb_zero_of_bddInProb_mul`), over a family of designs indexed by `n` on a
single probability space. A nonnegative scaling `a n` stands for `N_*/n²`; then `step4Rate` is
`N_*B²C(M,2)c^{(2)}_max/n` and `step2Rate` is `N_*MB²G²_max/n²`, and the rate conditions
`N_* c^{(2)}_max = o(n)` and `N_* G²_max = o(n²)` say that these tend to zero. -/

section OpWrappers

open scoped ENNReal

-- The family index types `Dn On Ln Kn` vary with `n`.
variable {Dn On Ln Kn : ℕ → Type*}
  [∀ n, Fintype (On n)] [∀ n, DecidableEq (On n)]
  [∀ n, Fintype (Kn n)] [∀ n, DecidableEq (Kn n)]
  [∀ n, DecidableEq (Dn n)] [∀ n, DecidableEq (Ln n)]

/-- `a_n · n · B² · #{e : |e| = 2} · c^{(2)}_max`, the deterministic factor of Step 4's `O_p`
bound. -/
def step4Rate (B a nObs pairs cmax : ℝ) : ℝ := a * (nObs * (B ^ 2 * (pairs * cmax)))

/-- `a_n · M · G_max · B² · G_max`, the deterministic factor of Step 2's `O_p` bound. -/
def step2Rate (B a M G : ℝ) : ℝ := a * (M * (G * (B ^ 2 * G)))

omit [IsProbabilityMeasure P] in
/-- **Domination for `O_p(1)`.** If `|Z_n| ≤ |W_n|` almost everywhere and `W_n = O_p(1)`, then
`Z_n = O_p(1)`. -/
theorem bddInProb_of_abs_le {Z W : ℕ → Ω → ℝ}
    (hle : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ |W n ω|) (hW : Sequence.BddInProb P W) :
    Sequence.BddInProb P Z := by
  intro δ hδ
  obtain ⟨C, hC0, hCb⟩ := hW δ hδ
  refine ⟨C, hC0, fun n => ?_⟩
  refine le_trans (measure_mono_ae ?_) (hCb n)
  filter_upwards [hle n] with ω hω hmem
  have h1 : C ≤ |Z n ω| := hmem
  show C ≤ |W n ω|
  exact h1.trans hω

omit [IsProbabilityMeasure P] [∀ n, DecidableEq (On n)] in
/-- `‖û‖²/n = O_p(1)`, from `‖û‖² ≤ ‖u‖²` (`hproj`), a uniform first-moment bound on `‖u‖²/n`
(`hmom`), and Markov's inequality. -/
theorem residSq_div_card_bddInProb (u v : ∀ n, Ω → On n → ℝ)
    (hcard : ∀ n, 0 < (Fintype.card (On n) : ℝ))
    (hproj : ∀ n, ∀ᵐ ω ∂P, ∑ o : On n, v n ω o ^ 2 ≤ ∑ o : On n, u n ω o ^ 2)
    (hmeas : ∀ n, AEMeasurable
      (fun ω => (∑ o : On n, u n ω o ^ 2) / (Fintype.card (On n) : ℝ)) P)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmom : ∀ n, ∫⁻ ω, ‖(∑ o : On n, u n ω o ^ 2) / (Fintype.card (On n) : ℝ)‖ₑ ∂P ≤ C) :
    Sequence.BddInProb P
      (fun n ω => (∑ o : On n, v n ω o ^ 2) / (Fintype.card (On n) : ℝ)) := by
  refine bddInProb_of_abs_le (fun n => ?_) (Sequence.bddInProb_of_lintegral_le hmeas hC hmom)
  filter_upwards [hproj n] with ω hω
  have h1 : (0 : ℝ) ≤ ∑ o : On n, v n ω o ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ o : On n, u n ω o ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [abs_of_nonneg (div_nonneg h1 (hcard n).le), abs_of_nonneg (div_nonneg h2 (hcard n).le),
    div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hω (inv_nonneg.mpr (hcard n).le)

omit [IsProbabilityMeasure P] [∀ n, DecidableEq (Kn n)] in
/-- **Step 4's closing sentence.** If `‖û‖²/n = O_p(1)` and `N_* c^{(2)}_max = o(n)` (read
through `step4Rate`), then `a_n‖Υ̂^dim - Υ̂‖_F ⟶^p 0`. The hypothesis `hb0` requires the cell
bound to be nonnegative. -/
theorem step4_tendstoInProb
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, Ω → On n → Kn n → ℝ) (v : ∀ n, Ω → On n → ℝ)
    {a b : ℕ → ℝ} {B : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (hcard : ∀ n, 0 < (Fintype.card (On n) : ℝ))
    (hz : ∀ n, ∀ᵐ ω ∂P, ∀ o, vecSqNorm (z n ω o) ≤ B ^ 2)
    (hb : ∀ n, ∀ e ∈ Finset.powersetCard 2 (dims n), ∀ t ∈ cells (c n) e, (t.card : ℝ) ≤ b n)
    (hu : Sequence.BddInProb P
      (fun n ω => (∑ o : On n, v n ω o ^ 2) / (Fintype.card (On n) : ℝ)))
    (hrate : Tendsto (fun n => step4Rate B (a n) (Fintype.card (On n) : ℝ)
      (((Finset.powersetCard 2 (dims n)).card : ℝ)) (b n)) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω => a n * frobNorm (dimMeat (c n) (dims n) (z n ω) (v n ω)
        - ieMeat (c n) (dims n) (z n ω) (v n ω))) atTop (fun _ => 0) := by
  refine Sequence.tendstoInProb_zero_of_bddInProb_mul
    (k := fun n => step4Rate B (a n) (Fintype.card (On n) : ℝ)
      (((Finset.powersetCard 2 (dims n)).card : ℝ)) (b n))
    (fun n => ?_) (fun n => ?_) hu hrate
  · exact mul_nonneg (ha0 n) (mul_nonneg (hcard n).le
      (mul_nonneg (sq_nonneg B) (mul_nonneg (Nat.cast_nonneg _) (hb0 n))))
  · filter_upwards [hz n] with ω hzω
    have hfs := step4_bound (c n) (dims n) (z n ω) (v n ω) hzω (hb n)
    have hSnn : (0 : ℝ) ≤ ∑ o : On n, v n ω o ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hne : (Fintype.card (On n) : ℝ) ≠ 0 := (hcard n).ne'
    rw [abs_of_nonneg (mul_nonneg (ha0 n) (frobNorm_nonneg _)),
      abs_of_nonneg (div_nonneg hSnn (hcard n).le)]
    have hkey : step4Rate B (a n) (Fintype.card (On n) : ℝ)
          (((Finset.powersetCard 2 (dims n)).card : ℝ)) (b n)
          * ((∑ o : On n, v n ω o ^ 2) / (Fintype.card (On n) : ℝ))
        = a n * (B ^ 2 * ((((Finset.powersetCard 2 (dims n)).card : ℝ))
            * (b n * ∑ o : On n, v n ω o ^ 2))) := by
      simp only [step4Rate]
      field_simp
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hfs (ha0 n)

omit [IsProbabilityMeasure P] [∀ n, DecidableEq (Kn n)] in
/-- **Step 2's displayed limit.** If `‖w‖²/G_max = O_p(1)` (`hproj`, with `w = P_{C_1}u`) and
`N_* G²_max = o(n²)` (read through `step2Rate`), then
`a_n∑_{m,j}‖ĝ^{(m)}_j - g^{(m)}_j‖² ⟶^p 0`. -/
theorem step2_tendstoInProb
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, Ω → On n → Kn n → ℝ) (w : ∀ n, Ω → On n → ℝ)
    {a G : ℕ → ℝ} {B : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hG : ∀ n, 0 < G n)
    (hz : ∀ n, ∀ᵐ ω ∂P, ∀ o, vecSqNorm (z n ω o) ≤ B ^ 2)
    (hcell : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)), (t.card : ℝ) ≤ G n)
    (hproj : Sequence.BddInProb P (fun n ω => (∑ o : On n, w n ω o ^ 2) / G n))
    (hrate : Tendsto (fun n => step2Rate B (a n) ((dims n).card : ℝ) (G n)) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω => a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
        vecSqNorm (cellScore (z n ω) (w n ω) t)) atTop (fun _ => 0) := by
  refine Sequence.tendstoInProb_zero_of_bddInProb_mul
    (k := fun n => step2Rate B (a n) ((dims n).card : ℝ) (G n))
    (fun n => ?_) (fun n => ?_) hproj hrate
  · exact mul_nonneg (ha0 n) (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (hG n).le (mul_nonneg (sq_nonneg B) (hG n).le)))
  · filter_upwards [hz n] with ω hzω
    have hfs := step2_score_diff_bound (c n) (dims n) (z n ω) (w n ω) hzω (hG n).le (hcell n)
    have hSnn : (0 : ℝ) ≤ ∑ o : On n, w n ω o ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hLnn : (0 : ℝ) ≤ ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
        vecSqNorm (cellScore (z n ω) (w n ω) t) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => vecSqNorm_nonneg _
    have hne : G n ≠ 0 := (hG n).ne'
    rw [abs_of_nonneg (mul_nonneg (ha0 n) hLnn), abs_of_nonneg (div_nonneg hSnn (hG n).le)]
    have hkey : step2Rate B (a n) ((dims n).card : ℝ) (G n)
          * ((∑ o : On n, w n ω o ^ 2) / G n)
        = a n * (((dims n).card : ℝ) * (G n * (B ^ 2 * ∑ o : On n, w n ω o ^ 2))) := by
      simp only [step2Rate]
      field_simp
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hfs (ha0 n)

/-! ### §5c Clause (a), chained

The two inputs of `piinf_a_of_steps` are supplied: `step4_smul_tendstoInProb` rescales Step 4's
limit, and `step2_assembly_tendstoInProb` combines Step 2's limit with the two outputs of Step 1,
`hstep1` and `hscore`, through the product rule `Sequence.tendstoInProb_zero_of_le_sqrt_mul`. -/

section Chained

variable [Fintype K] [DecidableEq K]

omit [IsProbabilityMeasure P] [DecidableEq K] [∀ n, DecidableEq (Kn n)] in
/-- `step4_tendstoInProb` in the form `‖a_n•Υ̂^dim - a_n•Υ̂‖_F ⟶^p 0`, using `a_n ≥ 0`. -/
theorem step4_smul_tendstoInProb
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, Ω → On n → K → ℝ) (v : ∀ n, Ω → On n → ℝ)
    {a b : ℕ → ℝ} {B : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (hcard : ∀ n, 0 < (Fintype.card (On n) : ℝ))
    (hz : ∀ n, ∀ᵐ ω ∂P, ∀ o, vecSqNorm (z n ω o) ≤ B ^ 2)
    (hb : ∀ n, ∀ e ∈ Finset.powersetCard 2 (dims n), ∀ t ∈ cells (c n) e, (t.card : ℝ) ≤ b n)
    (hu : Sequence.BddInProb P
      (fun n ω => (∑ o : On n, v n ω o ^ 2) / (Fintype.card (On n) : ℝ)))
    (hrate : Tendsto (fun n => step4Rate B (a n) (Fintype.card (On n) : ℝ)
      (((Finset.powersetCard 2 (dims n)).card : ℝ)) (b n)) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (v n ω)
        - a n • ieMeat (c n) (dims n) (z n ω) (v n ω))) atTop (fun _ => 0) := by
  have hfun : (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (v n ω)
        - a n • ieMeat (c n) (dims n) (z n ω) (v n ω)))
      = fun n ω => a n * frobNorm (dimMeat (c n) (dims n) (z n ω) (v n ω)
        - ieMeat (c n) (dims n) (z n ω) (v n ω)) := by
    funext n ω
    rw [← smul_sub, frobNorm_smul, abs_of_nonneg (ha0 n)]
  rw [hfun]
  exact step4_tendstoInProb (Kn := fun _ => K) c dims z v ha0 hb0 hcard hz hb hu hrate

omit [IsProbabilityMeasure P] [DecidableEq K] [∀ n, DecidableEq (Kn n)] in
/-- **Step 2: `Υ̂^dim - Υ_n ⟶^p 0`.** Combines `frobNorm_dimMeat_sub_dimMeat_le`, the
limit of `step2_tendstoInProb`, `S_g = O_p(1)` (`hscore`) and Step 1's conclusion (`hstep1`).
Here `u` is the disturbance and `v` the residual. -/
theorem step2_assembly_tendstoInProb
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, Ω → On n → K → ℝ) (v u : ∀ n, Ω → On n → ℝ)
    {Ups : ℕ → Matrix K K ℝ} {a G : ℕ → ℝ} {B : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hG : ∀ n, 0 < G n)
    (hz : ∀ n, ∀ᵐ ω ∂P, ∀ o, vecSqNorm (z n ω o) ≤ B ^ 2)
    (hcell : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)), (t.card : ℝ) ≤ G n)
    (hproj : Sequence.BddInProb P
      (fun n ω => (∑ o : On n, (v n ω o - u n ω o) ^ 2) / G n))
    (hrate : Tendsto (fun n => step2Rate B (a n) ((dims n).card : ℝ) (G n)) atTop (𝓝 0))
    (hscore : Sequence.BddInProb P
      (fun n ω => a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
        vecSqNorm (cellScore (z n ω) (u n ω) t)))
    (hstep1 : TendstoInMeasure P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n))
      atTop (fun _ => 0)) :
    TendstoInMeasure P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (v n ω) - Ups n))
      atTop (fun _ => 0) := by
  have hSnn : ∀ (n : ℕ) (ω : Ω), (0 : ℝ) ≤ ∑ m ∈ dims n,
      ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
        vecSqNorm (cellScore (z n ω) (fun o => v n ω o - u n ω o) t) :=
    fun n ω => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => vecSqNorm_nonneg _
  have hGnn : ∀ (n : ℕ) (ω : Ω), (0 : ℝ) ≤ ∑ m ∈ dims n,
      ∑ t ∈ cells (c n) ({m} : Finset (Dn n)), vecSqNorm (cellScore (z n ω) (u n ω) t) :=
    fun n ω => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => vecSqNorm_nonneg _
  -- `S_d ⟶^p 0`, the displayed limit of Step 2
  have hS : TendstoInMeasure P
      (fun n ω => a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
        vecSqNorm (cellScore (z n ω) (fun o => v n ω o - u n ω o) t)) atTop (fun _ => 0) :=
    step2_tendstoInProb (Kn := fun _ => K) c dims z (fun n ω o => v n ω o - u n ω o)
      ha0 hG hz hcell hproj hrate
  -- the cross term `2√(S_dS_g)`
  have hcross : TendstoInMeasure P
      (fun n ω => 2 * Real.sqrt
        ((a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
            vecSqNorm (cellScore (z n ω) (fun o => v n ω o - u n ω o) t))
          * (a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
              vecSqNorm (cellScore (z n ω) (u n ω) t)))) atTop (fun _ => 0) := by
    refine Sequence.tendstoInProb_zero_of_le_sqrt_mul (κ := 2) (by norm_num)
      (fun n => Filter.Eventually.of_forall fun ω => mul_nonneg (ha0 n) (hSnn n ω))
      (fun n => Filter.Eventually.of_forall fun ω => ?_) hS hscore
    rw [abs_of_nonneg (by positivity)]
  -- the first half of the triangle inequality
  have hdiff : TendstoInMeasure P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (v n ω)
        - a n • dimMeat (c n) (dims n) (z n ω) (u n ω))) atTop (fun _ => 0) := by
    refine Sequence.tendstoInProb_zero_of_abs_le_add
      (fun n => Filter.Eventually.of_forall fun ω => ?_) hS hcross
    rw [abs_of_nonneg (frobNorm_nonneg _), abs_of_nonneg (mul_nonneg (ha0 n) (hSnn n ω)),
      abs_of_nonneg (by positivity)]
    have hsm : a n • dimMeat (c n) (dims n) (z n ω) (v n ω)
        - a n • dimMeat (c n) (dims n) (z n ω) (u n ω)
        = a n • (dimMeat (c n) (dims n) (z n ω) (v n ω)
            - dimMeat (c n) (dims n) (z n ω) (u n ω)) := (smul_sub _ _ _).symm
    rw [hsm, frobNorm_smul, abs_of_nonneg (ha0 n)]
    have hdet := frobNorm_dimMeat_sub_dimMeat_le (c n) (dims n) (z n ω) (v n ω) (u n ω)
    have hsqrt : Real.sqrt
        ((a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
            vecSqNorm (cellScore (z n ω) (fun o => v n ω o - u n ω o) t))
          * (a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
              vecSqNorm (cellScore (z n ω) (u n ω) t)))
        = a n * Real.sqrt
            ((∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
                vecSqNorm (cellScore (z n ω) (fun o => v n ω o - u n ω o) t))
              * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
                  vecSqNorm (cellScore (z n ω) (u n ω) t)) := by
      have h1 : ∀ x y : ℝ, (a n * x) * (a n * y) = a n ^ 2 * (x * y) := fun x y => by ring
      rw [h1, Real.sqrt_mul (sq_nonneg (a n)), Real.sqrt_sq (ha0 n)]
    rw [hsqrt]
    nlinarith [hdet, ha0 n, Real.sqrt_nonneg
      ((∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
          vecSqNorm (cellScore (z n ω) (fun o => v n ω o - u n ω o) t))
        * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
            vecSqNorm (cellScore (z n ω) (u n ω) t))]
  -- the second half is `hstep1`
  refine Sequence.tendstoInProb_zero_of_abs_le_add
    (fun n => Filter.Eventually.of_forall fun ω => ?_) hdiff hstep1
  rw [abs_of_nonneg (frobNorm_nonneg _), abs_of_nonneg (frobNorm_nonneg _),
    abs_of_nonneg (frobNorm_nonneg _)]
  have hdec : a n • dimMeat (c n) (dims n) (z n ω) (v n ω) - Ups n
      = (a n • dimMeat (c n) (dims n) (z n ω) (v n ω)
          - a n • dimMeat (c n) (dims n) (z n ω) (u n ω))
        + (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n) := by abel
  rw [hdec]
  exact frobNorm_add_le _ _

omit [IsProbabilityMeasure P] [DecidableEq K] [∀ n, DecidableEq (Kn n)] in
/-- **Theorem 12(a): `Υ̂ - Υ_n ⟶^p 0`.** `piinf_a_of_steps` with both inputs supplied, at
`Υ̂^dim := a_n•dimMeat` and `Υ̂ := a_n•ieMeat`. The remaining hypotheses are Step 1's outputs
`hstep1` and `hscore`, the bound `hproj` on `‖P_{C_1}u‖²`, and `hresid` (`‖û‖²/n = O_p(1)`). -/
theorem piinf_a
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, Ω → On n → K → ℝ) (v u : ∀ n, Ω → On n → ℝ)
    {Ups : ℕ → Matrix K K ℝ} {a b G : ℕ → ℝ} {B : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (hG : ∀ n, 0 < G n)
    (hcard : ∀ n, 0 < (Fintype.card (On n) : ℝ))
    (hz : ∀ n, ∀ᵐ ω ∂P, ∀ o, vecSqNorm (z n ω o) ≤ B ^ 2)
    (hb : ∀ n, ∀ e ∈ Finset.powersetCard 2 (dims n), ∀ t ∈ cells (c n) e, (t.card : ℝ) ≤ b n)
    (hcell : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)), (t.card : ℝ) ≤ G n)
    (hresid : Sequence.BddInProb P
      (fun n ω => (∑ o : On n, v n ω o ^ 2) / (Fintype.card (On n) : ℝ)))
    (hrate4 : Tendsto (fun n => step4Rate B (a n) (Fintype.card (On n) : ℝ)
      (((Finset.powersetCard 2 (dims n)).card : ℝ)) (b n)) atTop (𝓝 0))
    (hproj : Sequence.BddInProb P
      (fun n ω => (∑ o : On n, (v n ω o - u n ω o) ^ 2) / G n))
    (hrate2 : Tendsto (fun n => step2Rate B (a n) ((dims n).card : ℝ) (G n)) atTop (𝓝 0))
    (hscore : Sequence.BddInProb P
      (fun n ω => a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
        vecSqNorm (cellScore (z n ω) (u n ω) t)))
    (hstep1 : TendstoInMeasure P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n))
      atTop (fun _ => 0)) :
    TendstoInMeasure P
      (fun n ω => frobNorm (a n • ieMeat (c n) (dims n) (z n ω) (v n ω) - Ups n))
      atTop (fun _ => 0) :=
  piinf_a_of_steps
    (step2_assembly_tendstoInProb c dims z v u ha0 hG hz hcell hproj hrate2 hscore hstep1)
    (step4_smul_tendstoInProb c dims z v ha0 hb0 hcard hz hb hresid hrate4)

end Chained

end OpWrappers

section ClauseB

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 12(b), Step 6.** With `a_n = N_*`, the Wald statistic for `𝓡π = 𝓡π₀` converges in
distribution to `χ²_r`, given:

* `Vp n ω`, the restricted variance estimator `𝓡V̂_π𝓡'`, Hermitian and measurable;
* `ha`, clause (a) restricted through `𝓡`: `𝓡(N_*V̂_π)𝓡' ⟶^p Sg`;
* `hCLT`, the restricted central limit theorem, and `hSg`, positive definiteness of its limit;
* `x n ω = 𝓡(π̂ - π)`. -/
theorem piinf_wald
    {Ns : ℕ → ℝ} (hNs : ∀ n, 0 < Ns n)
    {Sg : Matrix ι ι ℝ} (hSg : Sg.PosDef)
    {Vp : ℕ → Ω → Matrix ι ι ℝ} (hVherm : ∀ n ω, (Vp n ω).IsHermitian)
    (hVmeas : ∀ n, Measurable (Vp n))
    (ha : TendstoInMeasure P (fun n ω => frobNorm (Ns n • Vp n ω - Sg)) atTop (fun _ => 0))
    {x : ℕ → Ω → EuclideanSpace ℝ ι} {G : Ω' → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution (fun n ω => Real.sqrt (Ns n) • x n ω) atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 Sg) :
    Tendsto (fun n => P {ω | (Vp n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution (fun n ω => Wald.waldStat (Vp n ω) (x n ω)) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P) (multivariateGaussian 0 1) := by
  obtain ⟨h1, h2⟩ := Wald.wald_of_clt (P := P) (P' := P') hSg
    (A := fun n ω => Ns n • Vp n ω)
    (fun n ω => (hVherm n ω).smul (IsSelfAdjoint.all (Ns n)))
    (fun n => (hVmeas n).const_smul (Ns n)) ha
    (u := fun n ω => Real.sqrt (Ns n) • x n ω) hCLT hG
  constructor
  · refine h1.congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact Wald.posDef_smul_iff (hNs n) (Vp n ω)
  · have heq : (fun n ω => Wald.waldStat (Ns n • Vp n ω) (Real.sqrt (Ns n) • x n ω))
        = fun n ω => Wald.waldStat (Vp n ω) (x n ω) := by
      funext n ω
      exact Wald.waldStat_smul (hNs n) (Vp n ω) (x n ω)
    rw [heq] at h2
    exact h2

/-- **Theorem 12(b) from clause (a), at `Ψ̂ = I` and `𝓡 = I_q`.** The hypothesis `ha` of
`piinf_wald` is derived from `‖Υ̂ - Υ_n‖_F ⟶^p 0` and the deterministic limit `hlim : Υ_n → Υ`.
The central limit theorem `hCLT` remains a hypothesis. -/
theorem piinf_wald_of_meat
    {Ns : ℕ → ℝ} (hNs : ∀ n, 0 < Ns n)
    {Sg : Matrix ι ι ℝ} (hSg : Sg.PosDef)
    {Uh : ℕ → Ω → Matrix ι ι ℝ} (hHerm : ∀ n ω, (Uh n ω).IsHermitian)
    (hmeas : ∀ n, Measurable (Uh n))
    {Ups : ℕ → Matrix ι ι ℝ}
    (ha0 : TendstoInMeasure P (fun n ω => frobNorm (Uh n ω - Ups n)) atTop (fun _ => 0))
    (hlim : Tendsto (fun n => frobNorm (Ups n - Sg)) atTop (𝓝 0))
    {x : ℕ → Ω → EuclideanSpace ℝ ι} {G : Ω' → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution (fun n ω => Real.sqrt (Ns n) • x n ω) atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 Sg) :
    Tendsto (fun n => P {ω | ((Ns n)⁻¹ • Uh n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution (fun n ω => Wald.waldStat ((Ns n)⁻¹ • Uh n ω) (x n ω)) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P) (multivariateGaussian 0 1) := by
  refine piinf_wald hNs hSg (Vp := fun n ω => (Ns n)⁻¹ • Uh n ω)
    (fun n ω => (hHerm n ω).smul (IsSelfAdjoint.all ((Ns n)⁻¹)))
    (fun n => (hmeas n).const_smul ((Ns n)⁻¹)) ?_ hCLT hG
  have hfun : (fun n ω => frobNorm (Ns n • ((Ns n)⁻¹ • Uh n ω) - Sg))
      = fun n ω => frobNorm (Uh n ω - Sg) := by
    funext n ω
    rw [smul_smul, mul_inv_cancel₀ (hNs n).ne', one_smul]
  rw [hfun]
  have hdet : TendstoInMeasure P (fun n (_ : Ω) => frobNorm (Ups n - Sg)) atTop (fun _ => 0) :=
    Sequence.tendstoInProb_zero_of_abs_le_const
      (fun n => Filter.Eventually.of_forall fun _ =>
        le_of_eq (abs_of_nonneg (frobNorm_nonneg _))) hlim
  refine Sequence.tendstoInProb_zero_of_abs_le_add
    (fun n => Filter.Eventually.of_forall fun ω => ?_) ha0 hdet
  rw [abs_of_nonneg (frobNorm_nonneg _), abs_of_nonneg (frobNorm_nonneg _),
    abs_of_nonneg (frobNorm_nonneg _)]
  have hdec : Uh n ω - Sg = (Uh n ω - Ups n) + (Ups n - Sg) := by abel
  rw [hdec]
  exact frobNorm_add_le _ _

/-- **Theorem 12(b) from clause (a), for `V̂_π = N_*^{-1}Ψ̂_n^{-1}Υ̂Ψ̂_n^{-1}` restricted through
`𝓡`.** Here `Uh` is `Υ̂`, `Ups` is `Υ_n`, `Gn` is `Ψ̂_n^{-1}`, `Rm` is `𝓡` and `Sg` is
`𝓡Ψ⁻¹ΥΨ⁻¹𝓡'`. The hypotheses `hLg` and `hLr` bound `‖Ψ̂_n^{-1}‖_F` and `‖𝓡‖_F` uniformly, and
`hdet` is the deterministic limit `𝓡Ψ̂_n^{-1}Υ_nΨ̂_n^{-1}𝓡' → 𝓡Ψ⁻¹ΥΨ⁻¹𝓡'`. The matrices `Ψ̂_n`
are deterministic, i.e. the statement holds along a realization of `(X,𝒪)`. -/
theorem piinf_wald_of_meat_restricted
    {Kq : ℕ → Type*} [∀ n, Fintype (Kq n)]
    (Uh : ∀ n, Ω → Matrix (Kq n) (Kq n) ℝ) (Ups : ∀ n, Matrix (Kq n) (Kq n) ℝ)
    (Gn : ∀ n, Matrix (Kq n) (Kq n) ℝ) (Rm : ∀ n, Matrix ι (Kq n) ℝ)
    {Ns : ℕ → ℝ} (hNs : ∀ n, 0 < Ns n)
    {Sg : Matrix ι ι ℝ} (hSg : Sg.PosDef)
    (hVherm : ∀ n ω, ((Ns n)⁻¹ • (Rm n * (Gn n * Uh n ω * Gn n) * (Rm n)ᵀ)).IsHermitian)
    (hVmeas : ∀ n, Measurable fun ω => (Ns n)⁻¹ • (Rm n * (Gn n * Uh n ω * Gn n) * (Rm n)ᵀ))
    {Lg Lr : ℝ} (hLg0 : 0 ≤ Lg) (hLr0 : 0 ≤ Lr)
    (hLg : ∀ n, frobNorm (Gn n) ≤ Lg) (hLr : ∀ n, rectFrobNorm (Rm n) ≤ Lr)
    (hdet : Tendsto (fun n => frobNorm (Rm n * (Gn n * Ups n * Gn n) * (Rm n)ᵀ - Sg))
      atTop (𝓝 0))
    (ha0 : TendstoInMeasure P (fun n ω => frobNorm (Uh n ω - Ups n)) atTop (fun _ => 0))
    {x : ℕ → Ω → EuclideanSpace ℝ ι} {G : Ω' → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution (fun n ω => Real.sqrt (Ns n) • x n ω) atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 Sg) :
    Tendsto (fun n => P {ω | ((Ns n)⁻¹ • (Rm n * (Gn n * Uh n ω * Gn n) * (Rm n)ᵀ)).PosDef})
        atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => Wald.waldStat ((Ns n)⁻¹ • (Rm n * (Gn n * Uh n ω * Gn n) * (Rm n)ᵀ))
            (x n ω)) atTop (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P)
          (multivariateGaussian 0 1) := by
  refine piinf_wald hNs hSg
    (Vp := fun n ω => (Ns n)⁻¹ • (Rm n * (Gn n * Uh n ω * Gn n) * (Rm n)ᵀ))
    hVherm hVmeas ?_ hCLT hG
  have hfun : (fun n ω => frobNorm (Ns n • ((Ns n)⁻¹
        • (Rm n * (Gn n * Uh n ω * Gn n) * (Rm n)ᵀ)) - Sg))
      = fun n ω => frobNorm (Rm n * (Gn n * Uh n ω * Gn n) * (Rm n)ᵀ - Sg) := by
    funext n ω
    rw [smul_smul, mul_inv_cancel₀ (hNs n).ne', one_smul]
  rw [hfun]
  exact Plugin.tendstoInProb_restricted_of_meat Uh Ups Gn Rm Sg hLg0 hLr0 hLg hLr hdet ha0

end ClauseB

end Probability

/-! ## §6 Witnesses

Each witness applies the result it concerns to an explicit model, showing that its hypotheses are
jointly satisfiable. -/

section Witnesses

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

/-- The witness model: every observation in one category of every dimension, with
`c^{(2)}_max = G_max = 1`. -/
def wIndex (M : ℕ) : Fin M → Fin 1 → Fin 1 := fun _ _ => 0

/-- Unit scores `z̃_o ≡ 1`, so `B = 1`. -/
def wScore : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

/-- Unit residuals `û_o ≡ 1`. -/
def wResid : Fin 1 → ℝ := fun _ => 1

/-- `step4_bound` at two fixed-effect dimensions and one observation, where it holds with
equality `1 ≤ 1`. -/
theorem step4_bound_witness :
    frobNorm (dimMeat (wIndex 2) Finset.univ wScore wResid
        - ieMeat (wIndex 2) Finset.univ wScore wResid)
      ≤ (1 : ℝ) ^ 2 * (((Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))).card : ℝ)
          * (1 * ∑ o : Fin 1, wResid o ^ 2)) := by
  refine step4_bound (wIndex 2) Finset.univ wScore wResid (B := 1) (b := 1)
    (fun o => ?_) (fun e _ t _ => ?_)
  · simp [vecSqNorm, wScore]
  · have h : t.card ≤ 1 := by simpa using Finset.card_le_univ t
    exact_mod_cast h

/-- The second moments of the clause-(c) witness: `ς²_m = 1` and `σ²_ε(o) = 1`, in the shape of
`hEu`. -/
def wEu : Fin 1 → Fin 1 → ℝ := fun o o' =>
  (∑ m ∈ (Finset.univ : Finset (Fin 1)),
      (1 : ℝ) ^ 2 * (if wIndex 1 m o = wIndex 1 m o' then (1 : ℝ) else 0))
    + (if o = o' then (1 : ℝ) ^ 2 else 0)

/-- `piinf_c` on a model with one dimension, one observation, one coefficient and unit
variances. -/
theorem piinf_c_witness :
    ieMeatKer (wIndex 1) Finset.univ wScore wEu = condVarScore wScore wEu
      ∧ condVarScore wScore wEu
          = upsilonN (wIndex 1) Finset.univ wScore (fun _ => (1 : ℝ))
            + ∑ o : Fin 1, ((1 : ℝ) ^ 2) • Matrix.vecMulVec (wScore o) (wScore o) :=
  piinf_c (wIndex 1) Finset.univ ⟨0, Finset.mem_univ 0⟩ wScore wEu (fun _ => (1 : ℝ))
    (fun _ => (1 : ℝ)) (fun _ _ => rfl)

/-- `piinf_wald` with `N_* ≡ 1`, `Σ = I_r`, `𝓡V̂_π𝓡' ≡ I_r`, and the identity on
`(EuclideanSpace ℝ ι, N(0,I_r))` as the deviation. -/
theorem piinf_wald_witness {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Tendsto (fun _ : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
        {_x : EuclideanSpace ℝ ι | (1 : Matrix ι ι ℝ).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun (_ : ℕ) (y : EuclideanSpace ℝ ι) => Wald.waldStat (1 : Matrix ι ι ℝ) y) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2)
          (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
          (multivariateGaussian 0 1) := by
  refine piinf_wald (P := multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) (Ns := fun _ => (1 : ℝ))
    (fun _ => one_pos) (Sg := 1) Matrix.PosDef.one (Vp := fun _ _ => (1 : Matrix ι ι ℝ))
    (fun _ _ => Matrix.isHermitian_one) (fun _ => measurable_const) ?_
    (x := fun _ => id) (G := id) ?_ Measure.map_id
  · intro ε hε
    have hz : frobNorm ((1 : ℝ) • (1 : Matrix ι ι ℝ) - 1) = 0 := by
      simp [frobNorm, frobSq]
    have hset : {y : EuclideanSpace ℝ ι |
        ε ≤ edist (frobNorm ((1 : ℝ) • (1 : Matrix ι ι ℝ) - 1)) ((fun _ => (0 : ℝ)) y)}
          = (∅ : Set (EuclideanSpace ℝ ι)) := by
      ext y
      simp only [hz, edist_self, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    simp only [hset, measure_empty]
    exact tendsto_const_nhds
  · have h : TendstoInDistribution (fun (_ : ℕ) (ω : EuclideanSpace ℝ ι) => ω) atTop id
        (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
        (multivariateGaussian 0 1) := tendstoInDistribution_const aemeasurable_id
    simpa using h

/-- `‖I₁‖_F = 1`. -/
theorem frobNorm_one_fin_one : frobNorm (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  simp [frobNorm, frobSq, Matrix.one_apply]

/-- `piinf_wald_of_meat` with `Υ̂ = Υ_n = (1 + (n+1)^{-1})I₁` and `Υ = I₁`, so that
`‖Υ_n - Υ‖_F = (n+1)^{-1}`, `N_* ≡ 1`, and the identity on `(EuclideanSpace ℝ (Fin 1), N(0,1))`
as the deviation. -/
theorem piinf_wald_of_meat_witness :
    Tendsto (fun n : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
        {_y : EuclideanSpace ℝ (Fin 1) |
          ((1 : ℝ)⁻¹ • ((1 + ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ))).PosDef})
        atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun (n : ℕ) (y : EuclideanSpace ℝ (Fin 1)) =>
            Wald.waldStat ((1 : ℝ)⁻¹ • ((1 + ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
              y)
          atTop (fun z : EuclideanSpace ℝ (Fin 1) => ‖z‖ ^ 2)
          (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
          (multivariateGaussian 0 1) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hups : ∀ n : ℕ, frobNorm ((1 + ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
      - (1 : Matrix (Fin 1) (Fin 1) ℝ)) = ((n : ℝ) + 1)⁻¹ := by
    intro n
    have hsm : (1 + ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
        - (1 : Matrix (Fin 1) (Fin 1) ℝ)
        = (((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [add_smul, one_smul]
      abel
    rw [hsm, frobNorm_smul, frobNorm_one_fin_one, mul_one, abs_of_nonneg (by positivity)]
  refine piinf_wald_of_meat (P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1) (Ns := fun _ => (1 : ℝ))
    (fun _ => one_pos) (Sg := 1) Matrix.PosDef.one
    (Uh := fun n _ => (1 + ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (fun _ _ => Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)) (fun _ => measurable_const)
    (Ups := fun n => (1 + ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) ?_
    (hbase.congr fun n => (hups n).symm) (x := fun _ => id) (G := id) ?_ Measure.map_id
  · refine Sequence.tendstoInProb_zero_of_abs_le_const (b := fun _ => 0)
      (fun n => Filter.Eventually.of_forall fun _ => ?_) tendsto_const_nhds
    rw [sub_self, frobNorm_zero, abs_zero]
  · have h : TendstoInDistribution
        (fun (_ : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) => ω) atTop id
        (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
        (multivariateGaussian 0 1) := tendstoInDistribution_const aemeasurable_id
    simpa using h

/-- Every `1 × 1` real matrix is Hermitian. -/
theorem isHermitian_fin_one (M : Matrix (Fin 1) (Fin 1) ℝ) : M.IsHermitian := by
  show Mᴴ = M
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.conjTranspose_apply]

/-- The witness value `Ψ̂_n^{-1} = 2I₂`. -/
noncomputable def wPsiInv : Matrix (Fin 2) (Fin 2) ℝ := (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The witness value of `𝓡`: the `1 × 2` selector of the first coordinate. -/
def wRestrict : Matrix (Fin 1) (Fin 2) ℝ := Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0

/-- `𝓡Ψ̂⁻¹(tI₂)Ψ̂⁻¹𝓡' = 4tI₁` on the witness model. -/
theorem wRestrict_conj (t : ℝ) :
    wRestrict * (wPsiInv * (t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * wPsiInv) * wRestrictᵀ
      = (4 * t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [wRestrict, wPsiInv, Matrix.mul_apply]
  ring

theorem frobNorm_wPsiInv : frobNorm wPsiInv = Real.sqrt 8 := by
  rw [frobNorm]
  congr 1
  simp [frobSq, wPsiInv, Matrix.one_apply]
  norm_num

theorem rectFrobNorm_wRestrict : rectFrobNorm wRestrict = 1 := by
  rw [rectFrobNorm]
  have h : rectFrobSq wRestrict = 1 := by
    simp [rectFrobSq, wRestrict]
  rw [h, Real.sqrt_one]

/-- `piinf_wald_of_meat_restricted` with `Ψ̂_n^{-1} = 2I₂`, `𝓡` the `1 × 2` selector,
`Υ̂ = Υ_n = ((1 + (n+1)^{-1})/4)I₂` and `Σ = I₁`, so that the restricted limit is approached at
rate `(n+1)^{-1}`. -/
theorem piinf_wald_of_meat_restricted_witness :
    Tendsto (fun n : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
        {_y : EuclideanSpace ℝ (Fin 1) |
          ((1 : ℝ)⁻¹ • (wRestrict * (wPsiInv
              * ((((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
              * wPsiInv) * wRestrictᵀ)).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun (n : ℕ) (y : EuclideanSpace ℝ (Fin 1)) =>
            Wald.waldStat ((1 : ℝ)⁻¹ • (wRestrict * (wPsiInv
              * ((((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
              * wPsiInv) * wRestrictᵀ)) y)
          atTop (fun z : EuclideanSpace ℝ (Fin 1) => ‖z‖ ^ 2)
          (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
          (multivariateGaussian 0 1) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hconj : ∀ n : ℕ, wRestrict * (wPsiInv
      * ((((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * wPsiInv)
      * wRestrictᵀ
      = ((1 : ℝ) + ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    intro n
    rw [wRestrict_conj]
    congr 1
    ring
  have hdet : ∀ n : ℕ, frobNorm (wRestrict * (wPsiInv
      * ((((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * wPsiInv)
      * wRestrictᵀ - (1 : Matrix (Fin 1) (Fin 1) ℝ)) = ((n : ℝ) + 1)⁻¹ := by
    intro n
    rw [hconj n]
    have hsm : ((1 : ℝ) + ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
        - (1 : Matrix (Fin 1) (Fin 1) ℝ)
        = (((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [add_smul, one_smul]
      abel
    rw [hsm, frobNorm_smul, frobNorm_one_fin_one, mul_one, abs_of_nonneg (by positivity)]
  refine piinf_wald_of_meat_restricted (P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (Kq := fun _ => Fin 2)
    (Uh := fun n _ => (((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (Ups := fun n => (((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (Gn := fun _ => wPsiInv) (Rm := fun _ => wRestrict) (Ns := fun _ => (1 : ℝ))
    (fun _ => one_pos) (Sg := 1) Matrix.PosDef.one
    (fun _ _ => (isHermitian_fin_one _).smul (IsSelfAdjoint.all _))
    (fun _ => measurable_const)
    (Lg := Real.sqrt 8) (Lr := 1) (Real.sqrt_nonneg 8) zero_le_one
    (fun _ => le_of_eq frobNorm_wPsiInv) (fun _ => le_of_eq rectFrobNorm_wRestrict)
    (hbase.congr fun n => (hdet n).symm) ?_ (x := fun _ => id) (G := id) ?_ Measure.map_id
  · refine Sequence.tendstoInProb_zero_of_abs_le_const (b := fun _ => 0)
      (fun n => Filter.Eventually.of_forall fun _ => ?_) tendsto_const_nhds
    rw [sub_self, frobNorm_zero, abs_zero]
  · have h : TendstoInDistribution
        (fun (_ : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) => ω) atTop id
        (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
        (multivariateGaussian 0 1) := tendstoInDistribution_const aemeasurable_id
    simpa using h

/-! ### §6b Witnesses for §5b on a growing family of designs

At index `n` the model has `n+1` observations, `M = 2` dimensions with one category each, unit
scores and unit residuals, so `c^{(2)}_max = G_max = n+1`; the scaling is `a_n = (n+1)^{-3}` and
`P` is a point mass. The quantities sent to zero are `(n+1)^{-1}` and `2(n+1)^{-1}`. -/

section SeqWitness

open scoped ENNReal

/-- The witness family: `n+1` observations at index `n`, two fixed-effect dimensions and one
category in each. -/
def seqIndex (n : ℕ) : Fin 2 → Fin (n + 1) → Fin 1 := fun _ _ => 0

/-- Unit scores on the witness family, so `B = 1`. -/
def seqScore (n : ℕ) : Fin (n + 1) → Fin 1 → ℝ := fun _ _ => 1

/-- Unit residuals on the witness family, so `‖û‖² = n+1`. -/
def seqResid (n : ℕ) : Fin (n + 1) → ℝ := fun _ => 1

theorem seq_card (n : ℕ) : (Fintype.card (Fin (n + 1)) : ℝ) = (n : ℝ) + 1 := by
  simp

theorem seq_residSq (n : ℕ) : (∑ o : Fin (n + 1), seqResid n o ^ 2) = (n : ℝ) + 1 := by
  simp [seqResid]

/-- On the witness family, `‖û‖²/n = O_p(1)`, obtained from `residSq_div_card_bddInProb`. -/
theorem seq_bddInProb :
    Sequence.BddInProb (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => (∑ o : Fin (n + 1), seqResid n o ^ 2)
        / (Fintype.card (Fin (n + 1)) : ℝ)) := by
  have hone : ∀ n : ℕ, (∑ o : Fin (n + 1), seqResid n o ^ 2)
      / (Fintype.card (Fin (n + 1)) : ℝ) = 1 := by
    intro n
    rw [seq_residSq, seq_card]
    exact div_self (by positivity)
  refine residSq_div_card_bddInProb (P := Measure.dirac (0 : ℝ))
    (On := fun n => Fin (n + 1)) (fun n _ => seqResid n) (fun n _ => seqResid n)
    (fun n => ?_) (fun n => ?_) (fun n => ?_) (C := 1) ENNReal.one_ne_top (fun n => ?_)
  · rw [seq_card]; positivity
  · exact Filter.Eventually.of_forall fun _ => le_rfl
  · simp only [hone]
    exact measurable_const.aemeasurable
  · simp only [hone]
    rw [lintegral_const]
    simp

/-- On the witness family, `‖(n²/N_*)D‖_F = (n+1)²`. -/
theorem seq_meat_diff_frobNorm (n : ℕ) :
    frobNorm (dimMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n)
        - ieMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n))
      = ((n : ℝ) + 1) ^ 2 := by
  have hw : ∀ o o' : Fin (n + 1),
      (((sharedDims (seqIndex n) (Finset.univ : Finset (Fin 2)) o o').card - 1 : ℕ) : ℝ)
        = 1 := by
    intro o o'
    have hs : sharedDims (seqIndex n) (Finset.univ : Finset (Fin 2)) o o' = Finset.univ := by
      rw [sharedDims]
      exact Finset.filter_true_of_mem fun m _ => rfl
    rw [hs]
    simp
  have hentry : pairForm (seqScore n) (seqResid n)
      (fun o o' => (((sharedDims (seqIndex n) (Finset.univ : Finset (Fin 2)) o o').card
        - 1 : ℕ) : ℝ)) 0 0 = ((n : ℝ) + 1) ^ 2 := by
    simp only [pairForm, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, hw, seqScore, seqResid, mul_one]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [dimMeat_sub_ieMeat]
  simp only [frobNorm, frobSq, Fin.sum_univ_one, hentry]
  exact Real.sqrt_sq (by positivity)

/-- On the witness family, the score-difference sum of Step 2 equals `2(n+1)²`. -/
theorem seq_step2_value (n : ℕ) :
    (∑ m ∈ (Finset.univ : Finset (Fin 2)),
        ∑ t ∈ cells (seqIndex n) ({m} : Finset (Fin 2)),
          vecSqNorm (cellScore (seqScore n) (seqResid n) t))
      = 2 * ((n : ℝ) + 1) ^ 2 := by
  have hone : ∀ m : Fin 2,
      (∑ t ∈ cells (seqIndex n) ({m} : Finset (Fin 2)),
        vecSqNorm (cellScore (seqScore n) (seqResid n) t)) = ((n : ℝ) + 1) ^ 2 := by
    intro m
    have hv : ∀ t : Finset (Fin (n + 1)),
        vecSqNorm (cellScore (seqScore n) (seqResid n) t)
          = (∑ _o ∈ t, (1 : ℝ)) * (∑ _o' ∈ t, (1 : ℝ)) := by
      intro t
      simp only [vecSqNorm, cellScore, seqScore, seqResid, Fin.sum_univ_one, mul_one, pow_two]
    rw [Finset.sum_congr rfl fun t _ => hv t,
      sum_cells_mul (c := seqIndex n) (A := ({m} : Finset (Fin 2)))
        (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))]
    have hsame : ∀ o o' : Fin (n + 1), SameOn (seqIndex n) ({m} : Finset (Fin 2)) o o' :=
      fun _ _ _ _ => rfl
    have hstep : ∀ o o' : Fin (n + 1),
        (if SameOn (seqIndex n) ({m} : Finset (Fin 2)) o o' then (1 : ℝ) * 1 else 0) = 1 :=
      fun o o' => by simp [hsame o o']
    rw [Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => hstep o o']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun m _ => hone m]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- `step4_tendstoInProb` on the witness family, where the sequence is `(n+1)^{-1}`. -/
theorem step4_tendstoInProb_witness :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => (((n : ℝ) + 1) ^ 3)⁻¹ *
        frobNorm (dimMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n)
          - ieMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n)))
      atTop (fun _ => 0) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine step4_tendstoInProb (P := Measure.dirac (0 : ℝ))
    (Dn := fun _ => Fin 2) (On := fun n => Fin (n + 1)) (Ln := fun _ => Fin 1)
    (Kn := fun _ => Fin 1)
    (fun n => seqIndex n) (fun _ => Finset.univ) (fun n _ => seqScore n)
    (fun n _ => seqResid n)
    (a := fun n => (((n : ℝ) + 1) ^ 3)⁻¹)
    (b := fun n => (Fintype.card (Fin (n + 1)) : ℝ)) (B := 1)
    (fun _ => by positivity) (fun _ => by positivity) ?_ ?_ ?_ seq_bddInProb ?_
  · intro n; rw [seq_card]; positivity
  · exact fun _ => Filter.Eventually.of_forall fun _ _ => by simp [vecSqNorm, seqScore]
  · intro n e _ t _
    exact_mod_cast Finset.card_le_univ t
  · refine hbase.congr fun n => ?_
    have hp : ((Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))).card : ℝ) = 1 := by
      simp [Finset.card_powersetCard]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [step4Rate, seq_card, hp]
    field_simp

/-- `step2_tendstoInProb` on the witness family, where the sequence is `2(n+1)^{-1}`. -/
theorem step2_tendstoInProb_witness :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => (((n : ℝ) + 1) ^ 3)⁻¹ *
        ∑ m ∈ (Finset.univ : Finset (Fin 2)),
          ∑ t ∈ cells (seqIndex n) ({m} : Finset (Fin 2)),
            vecSqNorm (cellScore (seqScore n) (seqResid n) t))
      atTop (fun _ => 0) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine step2_tendstoInProb (P := Measure.dirac (0 : ℝ))
    (Dn := fun _ => Fin 2) (On := fun n => Fin (n + 1)) (Ln := fun _ => Fin 1)
    (Kn := fun _ => Fin 1)
    (fun n => seqIndex n) (fun _ => Finset.univ) (fun n _ => seqScore n)
    (fun n _ => seqResid n)
    (a := fun n => (((n : ℝ) + 1) ^ 3)⁻¹)
    (G := fun n => (Fintype.card (Fin (n + 1)) : ℝ)) (B := 1)
    (fun _ => by positivity) ?_ ?_ ?_ seq_bddInProb ?_
  · intro n; rw [seq_card]; positivity
  · exact fun _ => Filter.Eventually.of_forall fun _ _ => by simp [vecSqNorm, seqScore]
  · intro n m _ t _
    exact_mod_cast Finset.card_le_univ t
  · have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using hbase.const_mul 2
    refine h2.congr fun n => ?_
    have hc2 : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [step2Rate, seq_card, hc2]
    field_simp

/-! ### §6c Witnesses for §5c on the same family

The disturbance is `u ≡ 0` and the residual `û ≡ 1`, so `Υ_n = 0` and Step 1's outputs hold
trivially. The quantities sent to zero are `2(n+1)^{-1}` and `(n+1)^{-1}`. -/

/-- The disturbance `u ≡ 0` of the witness model. -/
def seqZero (n : ℕ) : Fin (n + 1) → ℝ := fun _ => 0

/-- With `u ≡ 0` the dimension-wise meat vanishes. -/
theorem seq_zero_dimMeat (n : ℕ) :
    dimMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqZero n) = 0 := by
  ext i j
  simp [dimMeat, Matrix.sum_apply, Matrix.vecMulVec_apply, cellScore, seqZero]

/-- On the witness family, `‖(n²/N_*)Υ̂^dim‖_F = 2(n+1)²`. -/
theorem seq_dimMeat_frobNorm (n : ℕ) :
    frobNorm (dimMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n))
      = 2 * ((n : ℝ) + 1) ^ 2 := by
  have hentry : dimMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n)
      (seqResid n) 0 0 = 2 * ((n : ℝ) + 1) ^ 2 := by
    rw [← seq_step2_value n]
    simp only [dimMeat, Matrix.sum_apply, Matrix.vecMulVec_apply, vecSqNorm, Fin.sum_univ_one,
      pow_two]
  simp only [frobNorm, frobSq, Fin.sum_univ_one, hentry]
  exact Real.sqrt_sq (by positivity)

/-- On the witness family, `‖(n²/N_*)Υ̂‖_F = (n+1)²`. -/
theorem seq_ieMeat_frobNorm (n : ℕ) :
    frobNorm (ieMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n))
      = ((n : ℝ) + 1) ^ 2 := by
  have hw : ∀ o o' : Fin (n + 1),
      (if Linked (seqIndex n) (Finset.univ : Finset (Fin 2)) o o' then (1 : ℝ) else 0) = 1 :=
    fun o o' => by
      have h : Linked (seqIndex n) (Finset.univ : Finset (Fin 2)) o o' :=
        ⟨0, Finset.mem_univ 0, rfl⟩
      simp [h]
  have hentry : ieMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n)
      (seqResid n) 0 0 = ((n : ℝ) + 1) ^ 2 := by
    rw [ieMeat_eq_pairForm]
    simp only [pairForm, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, hw, seqScore, seqResid, mul_one]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  simp only [frobNorm, frobSq, Fin.sum_univ_one, hentry]
  exact Real.sqrt_sq (by positivity)

/-- `‖P_{C_1}u‖² = O_p(G_max)` on the witness model. -/
theorem seq_hproj :
    Sequence.BddInProb (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => (∑ o : Fin (n + 1), (seqResid n o - seqZero n o) ^ 2)
        / (Fintype.card (Fin (n + 1)) : ℝ)) := by
  refine Sequence.bddInProb_of_abs_le_const (M := 1)
    (fun n => Filter.Eventually.of_forall fun ω => ?_)
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : (∑ o : Fin (n + 1), (seqResid n o - seqZero n o) ^ 2) = (n : ℝ) + 1 := by
    simp [seqResid, seqZero]
  rw [h1, seq_card, div_self hne]
  norm_num

/-- `N_*n^{-2}∑_{m,j}‖g^{(m)}_j‖² = O_p(1)` on the witness model, where it is `0`. -/
theorem seq_hscore :
    Sequence.BddInProb (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => (((n : ℝ) + 1) ^ 3)⁻¹ *
        ∑ m ∈ (Finset.univ : Finset (Fin 2)),
          ∑ t ∈ cells (seqIndex n) ({m} : Finset (Fin 2)),
            vecSqNorm (cellScore (seqScore n) (seqZero n) t)) := by
  refine Sequence.bddInProb_of_abs_le_const (M := 0)
    (fun n => Filter.Eventually.of_forall fun ω => ?_)
  have h0 : (∑ m ∈ (Finset.univ : Finset (Fin 2)),
      ∑ t ∈ cells (seqIndex n) ({m} : Finset (Fin 2)),
        vecSqNorm (cellScore (seqScore n) (seqZero n) t)) = 0 := by
    simp [cellScore, vecSqNorm, seqZero]
  rw [h0, mul_zero, abs_zero]

/-- `N_*n^{-2}∑_{m,j}g^{(m)}_jg^{(m)′}_j - Υ_n ⟶^p 0` on the witness model, where both terms
vanish. -/
theorem seq_hstep1 :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => frobNorm ((((n : ℝ) + 1) ^ 3)⁻¹ •
        dimMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqZero n)
        - (0 : Matrix (Fin 1) (Fin 1) ℝ))) atTop (fun _ => (0 : ℝ)) := by
  refine Sequence.tendstoInProb_zero_of_abs_le_const (b := fun _ => 0)
    (fun n => Filter.Eventually.of_forall fun ω => ?_) tendsto_const_nhds
  rw [seq_zero_dimMeat n, smul_zero, sub_zero, frobNorm_zero, abs_zero]

/-- `step2_assembly_tendstoInProb` on the witness family, where the sequence is
`2(n+1)^{-1}`. -/
theorem step2_assembly_tendstoInProb_witness :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => frobNorm ((((n : ℝ) + 1) ^ 3)⁻¹ •
          dimMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n)
        - (0 : Matrix (Fin 1) (Fin 1) ℝ))) atTop (fun _ => (0 : ℝ)) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine step2_assembly_tendstoInProb (P := Measure.dirac (0 : ℝ)) (K := Fin 1)
    (Dn := fun _ => Fin 2) (On := fun n => Fin (n + 1)) (Ln := fun _ => Fin 1)
    (fun n => seqIndex n) (fun _ => Finset.univ) (fun n _ => seqScore n)
    (fun n _ => seqResid n) (fun n _ => seqZero n)
    (Ups := fun _ => 0) (a := fun n => (((n : ℝ) + 1) ^ 3)⁻¹)
    (G := fun n => (Fintype.card (Fin (n + 1)) : ℝ)) (B := 1)
    (fun _ => by positivity) ?_ ?_ ?_ seq_hproj ?_ seq_hscore seq_hstep1
  · intro n; rw [seq_card]; positivity
  · exact fun _ => Filter.Eventually.of_forall fun _ _ => by simp [vecSqNorm, seqScore]
  · intro n m _ t _
    exact_mod_cast Finset.card_le_univ t
  · have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using hbase.const_mul 2
    refine h2.congr fun n => ?_
    have hc2 : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [step2Rate, seq_card, hc2]
    field_simp

/-- `piinf_a` on the witness family, where the sequence is `(n+1)^{-1}`. -/
theorem piinf_a_witness :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => frobNorm ((((n : ℝ) + 1) ^ 3)⁻¹ •
          ieMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n)
        - (0 : Matrix (Fin 1) (Fin 1) ℝ))) atTop (fun _ => (0 : ℝ)) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine piinf_a (P := Measure.dirac (0 : ℝ)) (K := Fin 1)
    (Dn := fun _ => Fin 2) (On := fun n => Fin (n + 1)) (Ln := fun _ => Fin 1)
    (fun n => seqIndex n) (fun _ => Finset.univ) (fun n _ => seqScore n)
    (fun n _ => seqResid n) (fun n _ => seqZero n)
    (Ups := fun _ => 0) (a := fun n => (((n : ℝ) + 1) ^ 3)⁻¹)
    (b := fun n => (Fintype.card (Fin (n + 1)) : ℝ))
    (G := fun n => (Fintype.card (Fin (n + 1)) : ℝ)) (B := 1)
    (fun _ => by positivity) (fun n => by rw [seq_card]; positivity) ?_ ?_ ?_ ?_ ?_
    seq_bddInProb ?_ seq_hproj ?_ seq_hscore seq_hstep1
  · intro n; rw [seq_card]; positivity
  · intro n; rw [seq_card]; positivity
  · exact fun _ => Filter.Eventually.of_forall fun _ _ => by simp [vecSqNorm, seqScore]
  · intro n e _ t _
    exact_mod_cast Finset.card_le_univ t
  · intro n m _ t _
    exact_mod_cast Finset.card_le_univ t
  · refine hbase.congr fun n => ?_
    have hp : ((Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))).card : ℝ) = 1 := by
      simp [Finset.card_powersetCard]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [step4Rate, seq_card, hp]
    field_simp
  · have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using hbase.const_mul 2
    refine h2.congr fun n => ?_
    have hc2 : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [step2Rate, seq_card, hc2]
    field_simp

end SeqWitness

end Witnesses

/-! ## §7 Theorem 6: asymptotic normality of the diagnostic coefficient

Along a realization of `(X,𝒪)`, `pi_clt` gives `√N_*(π̂ - π) ⟶^d Ψ⁻¹Z` with `Z ∼ N(0,Υ)`, and
`pi_clt_std` gives `√N_*(π̂ - π) ⟶^d N(0, Ψ⁻¹ΥΨ⁻¹)` under the quadratic-form identity `hsand`.
The proof splits the score as `Z̃'u = Ğ_n + Z̃'ε` (`score_decomposition`), shows
`√N_* n⁻¹Z̃'ε ⟶^p 0` (`tendstoInProb_score_eps`), applies the Lindeberg–Feller theorem to the
category term by Cramér–Wold (`score_clt_gen`), and passes through `Ψ_n⁻¹` by Slutsky.
`pi_clt_unconditional_of_frozen` removes the conditioning given `hfreeze`, and
`piinf_wald_of_meat_of_pi_clt` discharges the central limit hypothesis of Theorem 12(b).
Condition (ii) enters as `hA : A_n → Ψ⁻¹` for a left inverse `A_n` of `n⁻¹Z̃'Z̃`, and the
variances are carried per category as `vr n j`. -/

section PiCLT

open MeasureTheory Filter ProbabilityTheory
open scoped Topology RealInnerProductSpace ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Generalized scalar Lindeberg CLT: arbitrary finite index type per `n`, arbitrary scale. -/
theorem scalar_clt_gen {J : ℕ → Type*} [∀ n, Fintype (J n)]
    (a : ℕ → ℝ) (w : ∀ n, J n → ℝ) (e : ∀ n, J n → Ω → ℝ) (vr : ∀ n, J n → ℝ) (C σ2 : ℝ)
    (hmeas : ∀ n j, Measurable (e n j))
    (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n j, ∫ ω, e n j ω ∂P = 0)
    (hL2 : ∀ n j, MemLp (e n j) 2 P)
    (hint4 : ∀ n j, Integrable (fun ω => e n j ω ^ 4) P)
    (hvar : ∀ n j, Var[e n j; P] = vr n j)
    (hmom : ∀ n j, ∫ ω, e n j ω ^ 4 ∂P ≤ C)
    (hσ2 : 0 < σ2)
    (hSn : Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, w n j ^ 2 * vr n j) atTop (𝓝 σ2))
    (hlin4 : Tendsto (fun n : ℕ => a n ^ 4 * ∑ j, w n j ^ 4) atTop (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) ω => a n * ∑ j, w n j * e n j ω) atTop
      (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 σ2.toNNReal) := by
  classical
  set σ : ℝ := Real.sqrt σ2 with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hσ2
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt hσ2.le
  set q : (n : ℕ) → Fin (Fintype.card (J n)) → J n := fun n i => (Fintype.equivFin (J n)).symm i
    with hq
  have hsum : ∀ (n : ℕ) (f : J n → ℝ), ∑ i : Fin (Fintype.card (J n)), f (q n i) = ∑ j, f j :=
    fun n f => Equiv.sum_comp _ f
  set c : (n : ℕ) → Fin (Fintype.card (J n)) → ℝ := fun n i => σ⁻¹ * a n * w n (q n i) with hc
  set A : (n : ℕ) → Fin (Fintype.card (J n)) → Ω → ℝ :=
    fun n i ω => c n i * e n (q n i) ω with hA
  have hc2 : ∀ (n : ℕ) (i : Fin (Fintype.card (J n))),
      c n i ^ 2 = σ2⁻¹ * (a n ^ 2 * w n (q n i) ^ 2) := by
    intro n i
    simp only [hc, mul_pow, inv_pow, hσsq]
    ring
  have hc4 : ∀ (n : ℕ) (i : Fin (Fintype.card (J n))),
      c n i ^ 4 = (σ2 ^ 2)⁻¹ * (a n ^ 4 * w n (q n i) ^ 4) := by
    intro n i
    have h : c n i ^ 4 = (c n i ^ 2) ^ 2 := by ring
    rw [h, hc2]
    ring
  have hmeasA : ∀ (n : ℕ) (i : Fin (Fintype.card (J n))), Measurable (A n i) := fun n i =>
    (hmeas n (q n i)).const_mul _
  have hindepA : ∀ n : ℕ, iIndepFun (A n) P := by
    intro n
    have h1 : iIndepFun (fun i : Fin (Fintype.card (J n)) => e n (q n i)) P :=
      (hindep n).precomp (Equiv.injective _)
    exact h1.comp _ (fun i => measurable_const_mul (c n i))
  have hL2A : ∀ (n : ℕ) (i : Fin (Fintype.card (J n))), MemLp (A n i) 2 P := fun n i =>
    (hL2 n (q n i)).const_mul _
  have hmeanA : ∀ (n : ℕ) (i : Fin (Fintype.card (J n))), ∫ ω, A n i ω ∂P = 0 := by
    intro n i
    simp only [hA, integral_const_mul, hmean, mul_zero]
  have hvarA : ∀ n : ℕ,
      ∑ i, Var[A n i; P] = σ2⁻¹ * (a n ^ 2 * ∑ j, w n j ^ 2 * vr n j) := by
    intro n
    have h1 : ∀ i : Fin (Fintype.card (J n)),
        Var[A n i; P] = σ2⁻¹ * a n ^ 2 * (w n (q n i) ^ 2 * vr n (q n i)) := by
      intro i
      rw [hA, variance_const_mul, hvar, hc2]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum,
      hsum n (fun j => w n j ^ 2 * vr n j)]
    ring
  have hvarlim : Tendsto (fun n : ℕ => ∑ i, Var[A n i; P]) atTop (𝓝 1) := by
    have := hSn.const_mul σ2⁻¹
    rw [inv_mul_cancel₀ (ne_of_gt hσ2)] at this
    exact this.congr (fun n => (hvarA n).symm)
  have hint4A : ∀ (n : ℕ) (i : Fin (Fintype.card (J n))),
      Integrable (fun ω => A n i ω ^ 4) P := by
    intro n i
    simpa [hA, mul_pow] using (hint4 n (q n i)).const_mul (c n i ^ 4)
  have hA4 : ∀ (n : ℕ) (i : Fin (Fintype.card (J n))),
      ∫ ω, A n i ω ^ 4 ∂P = c n i ^ 4 * ∫ ω, e n (q n i) ω ^ 4 ∂P := by
    intro n i
    simp [hA, mul_pow, integral_const_mul]
  have hlinA : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => ∑ i, ∫ ω in {ω | δ < |A n i ω|}, A n i ω ^ 2 ∂P) atTop (𝓝 0) := by
    intro δ hδ
    have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
    have hterm : ∀ (n : ℕ) (i : Fin (Fintype.card (J n))),
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
        (a n ^ 4 * ∑ j, w n j ^ 4)) atTop (𝓝 0))
    · refine (Finset.sum_le_sum fun i _ => hterm n i).trans (le_of_eq ?_)
      have h3 : ∀ i : Fin (Fintype.card (J n)), (δ ^ 2)⁻¹ * (c n i ^ 4 * C)
          = ((δ ^ 2)⁻¹ * C * (σ2 ^ 2)⁻¹ * a n ^ 4) * w n (q n i) ^ 4 := by
        intro i
        rw [hc4]
        ring
      rw [Finset.sum_congr rfl (fun i _ => h3 i), ← Finset.mul_sum,
        hsum n (fun j => w n j ^ 4)]
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
  have T3 := CLT.tendstoInDistribution_of_law_eq T2 aemeasurable_id hlaw
  have hrow : ∀ (n : ℕ) (ω : Ω), σ * ∑ i, A n i ω = a n * ∑ j, w n j * e n j ω := by
    intro n ω
    have h1 : ∀ i : Fin (Fintype.card (J n)),
        A n i ω = σ⁻¹ * (a n * (w n (q n i) * e n (q n i) ω)) := by
      intro i; rw [hA, hc]; ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum, ← mul_assoc,
      mul_inv_cancel₀ hσpos.ne', one_mul, ← Finset.mul_sum,
      hsum n (fun j => w n j * e n j ω)]
  refine T3.congr (fun n => ?_) (by rfl)
  filter_upwards with ω
  exact hrow n ω


/-- Generalized vector CLT by Cramer--Wold. -/
theorem score_clt_gen {K : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    (a : ℕ → ℝ) (z : ∀ n, J n → EuclideanSpace ℝ (Fin K))
    (e : ∀ n, J n → Ω → ℝ) (vr : ∀ n, J n → ℝ) (C : ℝ)
    (Ups : Matrix (Fin K) (Fin K) ℝ) (hUps : Ups.PosDef)
    (hmeas : ∀ n j, Measurable (e n j))
    (hindep : ∀ n, iIndepFun (e n) P)
    (hmean : ∀ n j, ∫ ω, e n j ω ∂P = 0)
    (hL2 : ∀ n j, MemLp (e n j) 2 P)
    (hint4 : ∀ n j, Integrable (fun ω => e n j ω ^ 4) P)
    (hvar : ∀ n j, Var[e n j; P] = vr n j)
    (hmom : ∀ n j, ∫ ω, e n j ω ^ 4 ∂P ≤ C)
    (hSn : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪z n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hlin4 : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 4 * ∑ j, ⟪z n j, t⟫ ^ 4) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => a n • ∑ j, e n j ω • z n j) atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Ups) := by
  have hmeasW : ∀ n : ℕ, Measurable (fun ω => a n • ∑ j, e n j ω • z n j) := by
    intro n
    have hterm : ∀ j : J n, Measurable (fun ω => e n j ω • z n j) := by
      intro j
      have h := hmeas n j
      fun_prop
    exact (Finset.measurable_sum _ (fun j _ => hterm j)).const_smul (a n)
  have hproj : ∀ (n : ℕ) (ω : Ω) (t : EuclideanSpace ℝ (Fin K)),
      ⟪a n • ∑ j, e n j ω • z n j, t⟫ = a n * ∑ j, ⟪z n j, t⟫ * e n j ω := by
    intro n ω t
    rw [real_inner_smul_left, sum_inner]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [real_inner_smul_left]; ring)
  refine TendstoInDistribution.of_inner (by fun_prop) (fun n => (hmeasW n).aemeasurable) ?_
  intro t
  by_cases ht : t = 0
  · subst ht
    simpa using
      (CLT.tendstoInDistribution_zero (P := P)
        (μ'' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin K)) Ups))
  · have hσ2 : 0 < t ⬝ᵥ (Ups *ᵥ t) := CLT.dotProduct_mulVec_pos_of_posDef hUps ht
    have T := scalar_clt_gen (P := P) a (fun n j => ⟪z n j, t⟫) e vr C _ hmeas hindep hmean
      hL2 hint4 hvar hmom hσ2 (hSn t) (hlin4 t)
    have hlaw : (multivariateGaussian 0 Ups).map (fun x => ⟪x, t⟫)
        = (gaussianReal 0 (t ⬝ᵥ (Ups *ᵥ t)).toNNReal).map (id : ℝ → ℝ) := by
      rw [Measure.map_id, CLT.map_inner_multivariateGaussian hUps.posSemidef t]
    have T2 := CLT.tendstoInDistribution_of_law_eq T (by fun_prop) hlaw
    refine T2.congr (fun n => ?_) (by rfl)
    filter_upwards with ω
    exact (hproj n ω t).symm


/-- Markov's inequality on the second moment, for a normed-space-valued array. -/
theorem tendstoInProb_zero_of_lintegral_enorm_sq_le {E : Type*} [NormedAddCommGroup E]
    {Y : ℕ → Ω → E} (hmeas : ∀ n, AEMeasurable (fun ω => ‖Y n ω‖ₑ ^ 2) P)
    {c : ℕ → ℝ≥0∞} (hle : ∀ n, ∫⁻ ω, ‖Y n ω‖ₑ ^ 2 ∂P ≤ c n) (hc : Tendsto c atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop (fun _ => (0 : E)) := by
  rw [tendstoInMeasure_iff_enorm]
  intro ε hε hεtop
  have hε2 : (0 : ℝ≥0∞) < ε ^ 2 := by positivity
  have hε2top : ε ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hεtop
  have hstep : ∀ n, P {ω | ε ≤ ‖Y n ω - (fun _ => (0 : E)) ω‖ₑ} ≤ c n / ε ^ 2 := by
    intro n
    have hsub : {ω | ε ≤ ‖Y n ω - (fun _ => (0 : E)) ω‖ₑ} ⊆ {ω | ε ^ 2 ≤ ‖Y n ω‖ₑ ^ 2} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, sub_zero] at hω ⊢
      gcongr
    refine (measure_mono hsub).trans ?_
    exact le_trans (meas_ge_le_lintegral_div (hmeas n) hε2.ne' hε2top)
      (ENNReal.div_le_div_right (hle n) _)
  have hdiv : Tendsto (fun n => c n / ε ^ 2) atTop (𝓝 0) := by
    simp_rw [div_eq_mul_inv]
    have h := ENNReal.Tendsto.mul_const hc (Or.inr (ENNReal.inv_ne_top.mpr hε2.ne'))
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
    (fun n => zero_le) hstep

/-- `‖x‖² = ∑ₖ xₖ²`. -/
theorem euclidean_norm_sq {K : ℕ} (x : EuclideanSpace ℝ (Fin K)) : ‖x‖ ^ 2 = ∑ k, x k ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)]
  exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs]

/-- `E‖∑ₒ εₒ z̃ₒ‖² = ∑ₒ ‖z̃ₒ‖² σ²_ε(o)`, the trace of `Var(Z̃'ε) = ∑ₒ z̃ₒz̃ₒ' σ²_ε(o)`. -/
theorem integral_norm_sq_score {K : ℕ} {O : Type*} [Fintype O]
    (zt : O → EuclideanSpace ℝ (Fin K)) (eps : O → Ω → ℝ) (sev : O → ℝ)
    (hindep : iIndepFun eps P) (hL2 : ∀ o, MemLp (eps o) 2 P)
    (hmean : ∀ o, ∫ ω, eps o ω ∂P = 0) (hvar : ∀ o, Var[eps o; P] = sev o) :
    ∫ ω, ‖∑ o, eps o ω • zt o‖ ^ 2 ∂P = ∑ o, ‖zt o‖ ^ 2 * sev o := by
  classical
  set Y : Fin K → O → Ω → ℝ := fun k o ω => zt o k * eps o ω with hY
  have hcoord : ∀ (ω : Ω) (k : Fin K),
      (∑ o, eps o ω • zt o) k = ∑ o, Y k o ω := by
    intro ω k
    rw [CLT.euclideanSum_apply]
    exact Finset.sum_congr rfl fun o _ => by simp [hY, mul_comm]
  have hYL2 : ∀ (k : Fin K), ∀ o ∈ (Finset.univ : Finset O), MemLp (Y k o) 2 P :=
    fun k o _ => (hL2 o).const_mul _
  have hYindep : ∀ (k : Fin K),
      Set.Pairwise (↑(Finset.univ : Finset O)) fun o o' => IndepFun (Y k o) (Y k o') P := by
    intro k o _ o' _ hne
    exact ((hindep.indepFun hne).comp (measurable_const_mul _) (measurable_const_mul _))
  have hSumL2 : ∀ k : Fin K, MemLp (fun ω => ∑ o, Y k o ω) 2 P := by
    intro k
    have := memLp_finsetSum (Finset.univ : Finset O) (fun o _ => hYL2 k o (Finset.mem_univ o))
    simpa using this
  have hSumMean : ∀ k : Fin K, ∫ ω, (∑ o, Y k o ω) ∂P = 0 := by
    intro k
    rw [integral_finsetSum _ (fun o _ => ((hL2 o).const_mul (zt o k)).integrable (by norm_num))]
    refine Finset.sum_eq_zero fun o _ => ?_
    simp [integral_const_mul, hmean o]
  have hSumVar : ∀ k : Fin K, Var[fun ω => ∑ o, Y k o ω; P] = ∑ o, zt o k ^ 2 * sev o := by
    intro k
    have hfun : (fun ω => ∑ o, Y k o ω) = ∑ o, Y k o := by
      funext ω; rw [Finset.sum_apply]
    rw [hfun, IndepFun.variance_sum (hYL2 k) (hYindep k)]
    exact Finset.sum_congr rfl fun o _ => by rw [hY, variance_const_mul, hvar]
  have hsq : ∀ k : Fin K, ∫ ω, (∑ o, Y k o ω) ^ 2 ∂P = ∑ o, zt o k ^ 2 * sev o := by
    intro k
    have h : Var[fun ω => ∑ o, Y k o ω; P] = ∫ ω, (∑ o, Y k o ω) ^ 2 ∂P := by
      rw [variance_eq_integral (hSumL2 k).aemeasurable]
      simp only [hSumMean k, sub_zero]
    rw [← h, hSumVar k]
  calc ∫ ω, ‖∑ o, eps o ω • zt o‖ ^ 2 ∂P
      = ∫ ω, ∑ k, (∑ o, Y k o ω) ^ 2 ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show ‖∑ o, eps o ω • zt o‖ ^ 2 = ∑ k, (∑ o, Y k o ω) ^ 2
        rw [euclidean_norm_sq]
        exact Finset.sum_congr rfl fun k _ => by rw [hcoord ω k]
    _ = ∑ k, ∫ ω, (∑ o, Y k o ω) ^ 2 ∂P :=
        integral_finsetSum _ (fun k _ => (hSumL2 k).integrable_sq)
    _ = ∑ k, ∑ o, zt o k ^ 2 * sev o := Finset.sum_congr rfl fun k _ => hsq k
    _ = ∑ o, ‖zt o‖ ^ 2 * sev o := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun o _ => by rw [euclidean_norm_sq, Finset.sum_mul]


/-- Integrability of the squared norm of the score, by the same coordinate decomposition. -/
theorem integrable_norm_sq_score {K : ℕ} {O : Type*} [Fintype O]
    (zt : O → EuclideanSpace ℝ (Fin K)) (eps : O → Ω → ℝ) (hL2 : ∀ o, MemLp (eps o) 2 P) :
    Integrable (fun ω => ‖∑ o, eps o ω • zt o‖ ^ 2) P := by
  classical
  set Y : Fin K → O → Ω → ℝ := fun k o ω => zt o k * eps o ω with hY
  have hcoord : ∀ (ω : Ω) (k : Fin K), (∑ o, eps o ω • zt o) k = ∑ o, Y k o ω := by
    intro ω k
    rw [CLT.euclideanSum_apply]
    exact Finset.sum_congr rfl fun o _ => by simp [hY, mul_comm]
  have hSumL2 : ∀ k : Fin K, MemLp (fun ω => ∑ o, Y k o ω) 2 P := by
    intro k
    have := memLp_finsetSum (Finset.univ : Finset O)
      (fun o (_ : o ∈ (Finset.univ : Finset O)) => (hL2 o).const_mul (zt o k))
    simpa using this
  have hint : Integrable (fun ω => ∑ k, (∑ o, Y k o ω) ^ 2) P := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin K))
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin K))) => (hSumL2 k).integrable_sq)
    simpa using this
  refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
  show ∑ k, (∑ o, Y k o ω) ^ 2 = ‖∑ o, eps o ω • zt o‖ ^ 2
  rw [euclidean_norm_sq]
  exact Finset.sum_congr rfl fun k _ => by rw [hcoord ω k]

/-- `√N_* n⁻¹ Z̃'ε ⟶^p 0`, by Chebyshev's inequality, since the variance is `O(N_*/n) → 0`. -/
theorem tendstoInProb_score_eps {K : ℕ} {O : ℕ → Type*} [∀ n, Fintype (O n)]
    (a : ℕ → ℝ) (zt : ∀ n, O n → EuclideanSpace ℝ (Fin K)) (eps : ∀ n, O n → Ω → ℝ)
    (sev : ∀ n, O n → ℝ) (B Cs : ℝ)
    (hmeas : ∀ n o, Measurable (eps n o))
    (hindep : ∀ n, iIndepFun (eps n) P)
    (hL2 : ∀ n o, MemLp (eps n o) 2 P)
    (hmean : ∀ n o, ∫ ω, eps n o ω ∂P = 0)
    (hvar : ∀ n o, Var[eps n o; P] = sev n o)
    (hzt : ∀ n o, ‖zt n o‖ ^ 2 ≤ B ^ 2)
    (hsev0 : ∀ n o, 0 ≤ sev n o) (hsev : ∀ n o, sev n o ≤ Cs)
    (hi : Tendsto (fun n : ℕ => a n ^ 2 * (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => a n • ∑ o, eps n o ω • zt n o) atTop (fun _ => 0) := by
  classical
  refine tendstoInProb_zero_of_lintegral_enorm_sq_le (P := P)
    (c := fun n => ENNReal.ofReal (a n ^ 2 * (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs)))
    (fun n => ?_) (fun n => ?_) ?_
  · have hm : Measurable (fun ω => a n • ∑ o, eps n o ω • zt n o) :=
      (Finset.measurable_sum _ (fun o _ => (hmeas n o).smul_const (zt n o))).const_smul (a n)
    exact (hm.enorm.pow_const 2).aemeasurable
  · have hint : Integrable (fun ω => ‖∑ o, eps n o ω • zt n o‖ ^ 2) P :=
      integrable_norm_sq_score (P := P) (zt n) (eps n) (hL2 n)
    have hval : ∫ ω, ‖∑ o, eps n o ω • zt n o‖ ^ 2 ∂P = ∑ o, ‖zt n o‖ ^ 2 * sev n o :=
      integral_norm_sq_score (P := P) (zt n) (eps n) (sev n) (hindep n) (hL2 n) (hmean n) (hvar n)
    have hptwise : ∀ ω, ‖a n • ∑ o, eps n o ω • zt n o‖ₑ ^ 2
        = ENNReal.ofReal (a n ^ 2 * ‖∑ o, eps n o ω • zt n o‖ ^ 2) := by
      intro ω
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs]
    rw [lintegral_congr hptwise,
      ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul (a n ^ 2))
        (Filter.Eventually.of_forall fun ω => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul, hval]
    have hb : ∑ o, ‖zt n o‖ ^ 2 * sev n o ≤ (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs) := by
      have hterm : ∀ o ∈ (Finset.univ : Finset (O n)),
          ‖zt n o‖ ^ 2 * sev n o ≤ B ^ 2 * Cs := by
        intro o _
        have h1 : ‖zt n o‖ ^ 2 * sev n o ≤ B ^ 2 * sev n o :=
          mul_le_mul_of_nonneg_right (hzt n o) (hsev0 n o)
        have h2 : B ^ 2 * sev n o ≤ B ^ 2 * Cs :=
          mul_le_mul_of_nonneg_left (hsev n o) (sq_nonneg B)
        linarith
      calc ∑ o, ‖zt n o‖ ^ 2 * sev n o ≤ ∑ _o : O n, B ^ 2 * Cs := Finset.sum_le_sum hterm
        _ = (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_left hb (sq_nonneg (a n))
    linarith [this]
  · simpa using ENNReal.tendsto_ofReal hi


/-- The score limit: `√N_* n⁻¹ Z̃'u = √N_* n⁻¹ Ğ_n + √N_* n⁻¹ Z̃'ε ⟶^d N(0, Υ)`. -/
theorem pi_score_clt {K : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    {O : ℕ → Type*} [∀ n, Fintype (O n)]
    (a : ℕ → ℝ)
    (zc : ∀ n, J n → EuclideanSpace ℝ (Fin K)) (zt : ∀ n, O n → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, J n → Ω → ℝ) (eps : ∀ n, O n → Ω → ℝ)
    (vr : ∀ n, J n → ℝ) (sev : ∀ n, O n → ℝ) (C B Cs : ℝ)
    (Ups : Matrix (Fin K) (Fin K) ℝ) (hUps : Ups.PosDef)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hindepη : ∀ n, iIndepFun (etab n) P)
    (hmeanη : ∀ n j, ∫ ω, etab n j ω ∂P = 0) (hL2η : ∀ n j, MemLp (etab n j) 2 P)
    (hint4η : ∀ n j, Integrable (fun ω => etab n j ω ^ 4) P)
    (hvarη : ∀ n j, Var[etab n j; P] = vr n j)
    (hmomη : ∀ n j, ∫ ω, etab n j ω ^ 4 ∂P ≤ C)
    (hmeasε : ∀ n o, Measurable (eps n o)) (hindepε : ∀ n, iIndepFun (eps n) P)
    (hL2ε : ∀ n o, MemLp (eps n o) 2 P) (hmeanε : ∀ n o, ∫ ω, eps n o ω ∂P = 0)
    (hvarε : ∀ n o, Var[eps n o; P] = sev n o)
    (hzt : ∀ n o, ‖zt n o‖ ^ 2 ≤ B ^ 2)
    (hsev0 : ∀ n o, 0 ≤ sev n o) (hsev : ∀ n o, sev n o ≤ Cs)
    (hi : Tendsto (fun n : ℕ => a n ^ 2 * (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hlin4 : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 4 * ∑ j, ⟪zc n j, t⟫ ^ 4) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => a n • ((∑ j, etab n j ω • zc n j) + (∑ o, eps n o ω • zt n o)))
      atTop (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Ups) := by
  classical
  have hG := score_clt_gen (P := P) a zc etab vr C Ups hUps hmeasη hindepη hmeanη hL2η hint4η
    hvarη hmomη hiii hlin4
  have hE := tendstoInProb_score_eps (P := P) a zt eps sev B Cs hmeasε hindepε hL2ε hmeanε
    hvarε hzt hsev0 hsev hi
  refine tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (n : ℕ) ω => a n • ∑ j, etab n j ω • zc n j) _ _ hG ?_ ?_
  · have hfun : ((fun (n : ℕ) ω => a n • ((∑ j, etab n j ω • zc n j)
        + (∑ o, eps n o ω • zt n o))) - fun (n : ℕ) ω => a n • ∑ j, etab n j ω • zc n j)
        = fun (n : ℕ) ω => a n • ∑ o, eps n o ω • zt n o := by
      funext n ω
      simp [smul_add]
    rw [hfun]
    exact hE
  · intro n
    refine Measurable.aemeasurable ?_
    have h1 : Measurable (fun ω => ∑ j, etab n j ω • zc n j) :=
      Finset.measurable_sum _ (fun j _ => (hmeasη n j).smul_const (zc n j))
    have h2 : Measurable (fun ω => ∑ o, eps n o ω • zt n o) :=
      Finset.measurable_sum _ (fun o _ => (hmeasε n o).smul_const (zt n o))
    exact (h1.add h2).const_smul (a n)


/-- Slutsky through `Ψ_n⁻¹`, in adjoint form. -/
theorem tendstoInDistribution_apply_of_solve {K : ℕ}
    {W : ℕ → Ω → EuclideanSpace ℝ (Fin K)} {Ups : Matrix (Fin K) (Fin K) ℝ}
    (hW : TendstoInDistribution W atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Ups))
    {A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))}
    {Ainf : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)}
    (hA : Tendsto A atTop (𝓝 Ainf))
    {dev : ℕ → Ω → EuclideanSpace ℝ (Fin K)} (hdevmeas : ∀ n, AEMeasurable (dev n) P)
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω, dev n ω = A n (W n ω)) :
    TendstoInDistribution dev atTop (fun z => Ainf z) (fun _ => P)
      (multivariateGaussian 0 Ups) := by
  refine TendstoInDistribution.of_inner (by fun_prop) hdevmeas ?_
  intro t
  have hY : TendstoInMeasure P
      (fun (n : ℕ) (_ : Ω) => (ContinuousLinearMap.adjoint (A n)) t) atTop
      (fun _ => (ContinuousLinearMap.adjoint Ainf) t) :=
    CLT.tendstoInMeasure_of_tendsto_const (CLT.tendsto_adjoint_apply hA t)
  have hSl := hW.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) => ⟪p.1, p.2⟫)
    (by fun_prop) hY (fun n => aemeasurable_const)
  refine CLT.tendstoInDistribution_of_eventually_ae_eq
    (hSl.congr (fun _ => Filter.EventuallyEq.rfl) ?_)
    (fun n => (Continuous.measurable (by fun_prop :
      Continuous fun x : EuclideanSpace ℝ (Fin K) => ⟪x, t⟫)).comp_aemeasurable (hdevmeas n)) ?_
  · filter_upwards with z
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rfl
  · filter_upwards [hsolve] with n hn
    filter_upwards with ω
    rw [hn ω, ← ContinuousLinearMap.adjoint_inner_right]


/-- `⟪x, e_k⟫ = x_k`. -/
theorem inner_single_one {K : ℕ} (x : EuclideanSpace ℝ (Fin K)) (k : Fin K) :
    ⟪x, EuclideanSpace.single k (1 : ℝ)⟫ = x k := by
  simp [PiLp.inner_apply]

/-- Condition (iii), read at the `K` coordinate directions and with the variances bounded away
from zero, bounds `a_n^2 ∑_j ‖z_j‖^2`. -/
theorem bddUnder_scaled_sumSq {K : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    (a : ℕ → ℝ) (zc : ∀ n, J n → EuclideanSpace ℝ (Fin K)) (vr : ∀ n, J n → ℝ)
    (v0 : ℝ) (hv0 : 0 < v0) (hvr : ∀ n j, v0 ≤ vr n j)
    (Ups : Matrix (Fin K) (Fin K) ℝ)
    (hiii : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t)))) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ᶠ n : ℕ in atTop, a n ^ 2 * ∑ j, ‖zc n j‖ ^ 2 ≤ T := by
  classical
  set ek : Fin K → EuclideanSpace ℝ (Fin K) := fun k => EuclideanSpace.single k (1 : ℝ) with hek
  have hF : ∀ n : ℕ, a n ^ 2 * ∑ j, ‖zc n j‖ ^ 2
      = ∑ k, a n ^ 2 * ∑ j, ⟪zc n j, ek k⟫ ^ 2 := by
    intro n
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by
      rw [euclidean_norm_sq]
      exact Finset.sum_congr rfl fun k _ => by rw [hek, inner_single_one]
  have hle : ∀ (n : ℕ) (k : Fin K), a n ^ 2 * ∑ j, ⟪zc n j, ek k⟫ ^ 2
      ≤ v0⁻¹ * (a n ^ 2 * ∑ j, ⟪zc n j, ek k⟫ ^ 2 * vr n j) := by
    intro n k
    have h1 : v0 * ∑ j, ⟪zc n j, ek k⟫ ^ 2 ≤ ∑ j, ⟪zc n j, ek k⟫ ^ 2 * vr n j := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hvr n j) (sq_nonneg _)
    have h2 : ∑ j, ⟪zc n j, ek k⟫ ^ 2 ≤ v0⁻¹ * ∑ j, ⟪zc n j, ek k⟫ ^ 2 * vr n j := by
      calc ∑ j, ⟪zc n j, ek k⟫ ^ 2 = v0⁻¹ * (v0 * ∑ j, ⟪zc n j, ek k⟫ ^ 2) := by
            field_simp
        _ ≤ v0⁻¹ * ∑ j, ⟪zc n j, ek k⟫ ^ 2 * vr n j :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    calc a n ^ 2 * ∑ j, ⟪zc n j, ek k⟫ ^ 2
        ≤ a n ^ 2 * (v0⁻¹ * ∑ j, ⟪zc n j, ek k⟫ ^ 2 * vr n j) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = v0⁻¹ * (a n ^ 2 * ∑ j, ⟪zc n j, ek k⟫ ^ 2 * vr n j) := by ring
  set L : ℝ := ∑ k, v0⁻¹ * (ek k ⬝ᵥ (Ups *ᵥ ek k)) with hL
  have hlim : Tendsto
      (fun n : ℕ => ∑ k, v0⁻¹ * (a n ^ 2 * ∑ j, ⟪zc n j, ek k⟫ ^ 2 * vr n j)) atTop (𝓝 L) :=
    tendsto_finsetSum _ (fun k _ => ((hiii (ek k)).const_mul v0⁻¹))
  refine ⟨max 0 (L + 1), le_max_left _ _, ?_⟩
  filter_upwards [hlim.eventually (eventually_lt_nhds (by linarith : L < L + 1))] with n hn
  calc a n ^ 2 * ∑ j, ‖zc n j‖ ^ 2 = ∑ k, a n ^ 2 * ∑ j, ⟪zc n j, ek k⟫ ^ 2 := hF n
    _ ≤ ∑ k, v0⁻¹ * (a n ^ 2 * ∑ j, ⟪zc n j, ek k⟫ ^ 2 * vr n j) :=
        Finset.sum_le_sum fun k _ => hle n k
    _ ≤ max 0 (L + 1) := le_trans hn.le (le_max_right _ _)

/-- Condition (iv), as the fourth-moment Lindeberg input. -/
theorem lin4_of_cond_iv {K : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    (a : ℕ → ℝ) (zc : ∀ n, J n → EuclideanSpace ℝ (Fin K)) (vr : ∀ n, J n → ℝ)
    (mx : ℕ → ℝ) (v0 : ℝ) (hv0 : 0 < v0) (hvr : ∀ n j, v0 ≤ vr n j)
    (Ups : Matrix (Fin K) (Fin K) ℝ)
    (hiii : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ n, 0 ≤ mx n) (hmx : ∀ n j, ‖zc n j‖ ^ 2 ≤ mx n)
    (hmxsum : ∀ n, mx n ≤ ∑ j, ‖zc n j‖ ^ 2)
    (hiv : Tendsto (fun n : ℕ => mx n / ∑ j, ‖zc n j‖ ^ 2) atTop (𝓝 0))
    (t : EuclideanSpace ℝ (Fin K)) :
    Tendsto (fun n : ℕ => a n ^ 4 * ∑ j, ⟪zc n j, t⟫ ^ 4) atTop (𝓝 0) := by
  classical
  obtain ⟨T, hT0, hT⟩ := bddUnder_scaled_sumSq a zc vr v0 hv0 hvr Ups hiii
  have hneg : Tendsto (fun n : ℕ => a n ^ 2 * mx n) atTop (𝓝 0) := by
    have hbound : ∀ᶠ n : ℕ in atTop,
        a n ^ 2 * mx n ≤ (mx n / ∑ j, ‖zc n j‖ ^ 2) * T := by
      filter_upwards [hT] with n hn
      rcases eq_or_lt_of_le (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg ‖zc n j‖) : (0 : ℝ) ≤ ∑ j, ‖zc n j‖ ^ 2) with h0 | h0
      · have hmz : mx n = 0 := le_antisymm (h0 ▸ hmxsum n) (hmx0 n)
        simp [hmz, ← h0]
      · have hkey : a n ^ 2 * mx n
            = (mx n / ∑ j, ‖zc n j‖ ^ 2) * (a n ^ 2 * ∑ j, ‖zc n j‖ ^ 2) := by
          field_simp
        rw [hkey]
        exact mul_le_mul_of_nonneg_left hn (div_nonneg (hmx0 n) h0.le)
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun n => mul_nonneg (sq_nonneg _) (hmx0 n)) hbound ?_
    simpa using hiv.mul_const T
  have hcs : ∀ (n : ℕ) (j : J n), ⟪zc n j, t⟫ ^ 2 ≤ ‖zc n j‖ ^ 2 * ‖t‖ ^ 2 := by
    intro n j
    have h := abs_real_inner_le_norm (zc n j) t
    nlinarith [sq_abs (⟪zc n j, t⟫ : ℝ), abs_nonneg (⟪zc n j, t⟫ : ℝ),
      norm_nonneg (zc n j), norm_nonneg t]
  have hstep : ∀ n : ℕ, a n ^ 4 * ∑ j, ⟪zc n j, t⟫ ^ 4
      ≤ (a n ^ 2 * mx n) * (‖t‖ ^ 2 * (a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2)) := by
    intro n
    have hterm : ∀ j ∈ (Finset.univ : Finset (J n)),
        ⟪zc n j, t⟫ ^ 4 ≤ (mx n * ‖t‖ ^ 2) * ⟪zc n j, t⟫ ^ 2 := by
      intro j _
      have h2 : ‖zc n j‖ ^ 2 * ‖t‖ ^ 2 ≤ mx n * ‖t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hmx n j) (sq_nonneg _)
      have h4 : ⟪zc n j, t⟫ ^ 4 = ⟪zc n j, t⟫ ^ 2 * ⟪zc n j, t⟫ ^ 2 := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_right ((hcs n j).trans h2) (sq_nonneg _)
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    calc a n ^ 4 * ∑ j, ⟪zc n j, t⟫ ^ 4
        ≤ a n ^ 4 * ((mx n * ‖t‖ ^ 2) * ∑ j, ⟪zc n j, t⟫ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (a n ^ 2 * mx n) * (‖t‖ ^ 2 * (a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2)) := by ring
  have hQ : ∀ n : ℕ,
      a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 ≤ ‖t‖ ^ 2 * (a n ^ 2 * ∑ j, ‖zc n j‖ ^ 2) := by
    intro n
    have hterm : ∀ j ∈ (Finset.univ : Finset (J n)),
        ⟪zc n j, t⟫ ^ 2 ≤ ‖t‖ ^ 2 * ‖zc n j‖ ^ 2 := by
      intro j _
      have := hcs n j
      nlinarith [this]
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    calc a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 ≤ a n ^ 2 * (‖t‖ ^ 2 * ∑ j, ‖zc n j‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = ‖t‖ ^ 2 * (a n ^ 2 * ∑ j, ‖zc n j‖ ^ 2) := by ring
  have hgoal : ∀ᶠ n : ℕ in atTop,
      a n ^ 4 * ∑ j, ⟪zc n j, t⟫ ^ 4 ≤ (a n ^ 2 * mx n) * (‖t‖ ^ 2 * (‖t‖ ^ 2 * T)) := by
    filter_upwards [hT] with n hn
    refine (hstep n).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) (hmx0 n))
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact (hQ n).trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _))
  refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by positivity)) hgoal ?_
  have h : Tendsto (fun n : ℕ => (a n ^ 2 * mx n) * (‖t‖ ^ 2 * (‖t‖ ^ 2 * T))) atTop
      (𝓝 (0 * (‖t‖ ^ 2 * (‖t‖ ^ 2 * T)))) := hneg.mul_const _
  simpa using h


/-- **Theorem 6**, along a realization of `(X, 𝒪)`. -/
theorem pi_clt {K : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    {O : ℕ → Type*} [∀ n, Fintype (O n)]
    (a Ns : ℕ → ℝ) (mx : ℕ → ℝ)
    (zc : ∀ n, J n → EuclideanSpace ℝ (Fin K)) (zt : ∀ n, O n → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, J n → Ω → ℝ) (eps : ∀ n, O n → Ω → ℝ)
    (vr : ∀ n, J n → ℝ) (sev : ∀ n, O n → ℝ) (C B Cs v0 : ℝ)
    (Ups : Matrix (Fin K) (Fin K) ℝ) (hUps : Ups.PosDef)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hindepη : ∀ n, iIndepFun (etab n) P)
    (hmeanη : ∀ n j, ∫ ω, etab n j ω ∂P = 0) (hL2η : ∀ n j, MemLp (etab n j) 2 P)
    (hint4η : ∀ n j, Integrable (fun ω => etab n j ω ^ 4) P)
    (hvarη : ∀ n j, Var[etab n j; P] = vr n j)
    (hmomη : ∀ n j, ∫ ω, etab n j ω ^ 4 ∂P ≤ C)
    (hv0 : 0 < v0) (hvr : ∀ n j, v0 ≤ vr n j)
    (hmeasε : ∀ n o, Measurable (eps n o)) (hindepε : ∀ n, iIndepFun (eps n) P)
    (hL2ε : ∀ n o, MemLp (eps n o) 2 P) (hmeanε : ∀ n o, ∫ ω, eps n o ω ∂P = 0)
    (hvarε : ∀ n o, Var[eps n o; P] = sev n o)
    (hsev0 : ∀ n o, 0 ≤ sev n o) (hsev : ∀ n o, sev n o ≤ Cs)
    (hzt : ∀ n o, ‖zt n o‖ ^ 2 ≤ B ^ 2)
    (hi : Tendsto (fun n : ℕ => a n ^ 2 * (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ n, 0 ≤ mx n) (hmx : ∀ n j, ‖zc n j‖ ^ 2 ≤ mx n)
    (hmxsum : ∀ n, mx n ≤ ∑ j, ‖zc n j‖ ^ 2)
    (hiv : Tendsto (fun n : ℕ => mx n / ∑ j, ‖zc n j‖ ^ 2) atTop (𝓝 0))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hA : Tendsto A atTop (𝓝 Psiinv))
    (pih : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (pi0 : EuclideanSpace ℝ (Fin K))
    (hpimeas : ∀ n, AEMeasurable (pih n) P)
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω, Real.sqrt (Ns n) • (pih n ω - pi0)
      = A n (a n • ((∑ j, etab n j ω • zc n j) + (∑ o, eps n o ω • zt n o)))) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (Ns n) • (pih n ω - pi0)) atTop
      (fun z => Psiinv z) (fun _ => P) (multivariateGaussian 0 Ups) := by
  have hlin4 := lin4_of_cond_iv a zc vr mx v0 hv0 hvr Ups hiii hmx0 hmx hmxsum hiv
  have hW := pi_score_clt (P := P) a zc zt etab eps vr sev C B Cs Ups hUps hmeasη hindepη
    hmeanη hL2η hint4η hvarη hmomη hmeasε hindepε hL2ε hmeanε hvarε hzt hsev0 hsev hi hiii hlin4
  exact tendstoInDistribution_apply_of_solve (P := P) hW hA
    (fun n => (hpimeas n).sub_const pi0 |>.const_smul (Real.sqrt (Ns n))) hsolve


section Wiring

variable {K : ℕ}

/-- `(Z̃'Z̃)(π̂ - π) = Z̃'u`, Lemma SM.B.4 with the inverse cleared. -/
theorem gram_mulVec_piHat_sub {O : Type*} [Fintype O] [DecidableEq O]
    {Mn : Matrix O O ℝ} {Xm Zm : Matrix O (Fin K) ℝ} {iota y u : O → ℝ}
    {b p beta pi0 : Fin K → ℝ} {s : ℝ}
    (hM : PiHat.IsAnnihilator Mn Xm iota)
    (hfit : PiHat.IsOLSFit Xm Zm iota y b p s)
    (hPD : ((Mn * Zm)ᵀ * (Mn * Zm)).PosDef)
    (hmodel : y = Xm *ᵥ beta + Zm *ᵥ pi0 + u) :
    ((Mn * Zm)ᵀ * (Mn * Zm)) *ᵥ (p - pi0) = (Mn * Zm)ᵀ *ᵥ u := by
  have hdet : IsUnit (((Mn * Zm)ᵀ * (Mn * Zm)).det) := Ne.isUnit hPD.det_pos.ne'
  rw [PiHat.piHat_sub_eq hM hfit hPD hmodel, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- `Z̃'v = ∑ₒ vₒ z̃ₒ`. -/
theorem transpose_mulVec_eq_sum {O : Type*} [Fintype O]
    (Zt : Matrix O (Fin K) ℝ) (v : O → ℝ) :
    (WithLp.toLp 2 (Ztᵀ *ᵥ v) : EuclideanSpace ℝ (Fin K))
      = ∑ o, v o • (WithLp.toLp 2 (fun k => Zt o k) : EuclideanSpace ℝ (Fin K)) := by
  ext k
  rw [CLT.euclideanSum_apply]
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- `Z̃'u = Ğ_n + Z̃'ε`, from `u_o = ∑_{m} η̆^{(m)}_{i_m(o)} + ε_o` and
`z^{(m)}_j = ∑_{o : i_m(o) = j} z̃_o`. -/
theorem score_decomposition {O J : Type*} [Fintype O] [Fintype J] [DecidableEq J]
    (mem : J → O → Prop) [∀ j o, Decidable (mem j o)]
    (zt : O → EuclideanSpace ℝ (Fin K)) (etab : J → ℝ) (eps : O → ℝ) (u : O → ℝ)
    (hu : ∀ o, u o = (∑ j ∈ Finset.univ.filter (fun j => mem j o), etab j) + eps o) :
    ∑ o, u o • zt o
      = (∑ j, etab j • (∑ o ∈ Finset.univ.filter (fun o => mem j o), zt o))
        + ∑ o, eps o • zt o := by
  classical
  have hsplit : ∑ o, u o • zt o
      = (∑ o, (∑ j ∈ Finset.univ.filter (fun j => mem j o), etab j) • zt o)
        + ∑ o, eps o • zt o := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun o _ => by rw [hu o, add_smul]
  rw [hsplit]
  congr 1
  have hinner : ∀ o : O, (∑ j ∈ Finset.univ.filter (fun j => mem j o), etab j) • zt o
      = ∑ j ∈ Finset.univ.filter (fun j => mem j o), etab j • zt o := by
    intro o
    rw [Finset.sum_smul]
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => hinner o]
  rw [Finset.sum_comm' (s := (Finset.univ : Finset O))
    (t := fun o => Finset.univ.filter (fun j => mem j o))
    (t' := (Finset.univ : Finset J)) (s' := fun j => Finset.univ.filter (fun o => mem j o))
    (f := fun o j => etab j • zt o) (by simp)]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.smul_sum]

/-- The solved form `hsolve` of `pi_clt`, derived from Lemma SM.B.4. -/
theorem solvedForm_of_piHat {O : Type*} [Fintype O] [DecidableEq O]
    {Mn : Matrix O O ℝ} {Xm Zm : Matrix O (Fin K) ℝ} {iota y u : O → ℝ}
    {b p beta pi0 : Fin K → ℝ} {s nn sN : ℝ}
    (hM : PiHat.IsAnnihilator Mn Xm iota)
    (hfit : PiHat.IsOLSFit Xm Zm iota y b p s)
    (hPD : ((Mn * Zm)ᵀ * (Mn * Zm)).PosDef)
    (hmodel : y = Xm *ᵥ beta + Zm *ᵥ pi0 + u)
    (A : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hAsolve : ∀ x : EuclideanSpace ℝ (Fin K),
      A (nn⁻¹ • (WithLp.toLp 2 (((Mn * Zm)ᵀ * (Mn * Zm)) *ᵥ WithLp.ofLp x))) = x) :
    sN • ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin K)) - WithLp.toLp 2 pi0)
      = A ((nn⁻¹ * sN) •
          ∑ o, u o • (WithLp.toLp 2 (fun k => (Mn * Zm) o k) : EuclideanSpace ℝ (Fin K))) := by
  have hkey := hAsolve (sN • ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin K)) - WithLp.toLp 2 pi0))
  rw [← hkey]
  congr 1
  have hof : (WithLp.ofLp (sN • ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin K))
      - WithLp.toLp 2 pi0)) : Fin K → ℝ) = sN • (p - pi0) := rfl
  rw [hof, Matrix.mulVec_smul, gram_mulVec_piHat_sub hM hfit hPD hmodel,
    ← transpose_mulVec_eq_sum (Mn * Zm) u]
  have : (WithLp.toLp 2 (sN • ((Mn * Zm)ᵀ *ᵥ u)) : EuclideanSpace ℝ (Fin K))
      = sN • WithLp.toLp 2 ((Mn * Zm)ᵀ *ᵥ u) := rfl
  rw [this, smul_smul]

end Wiring


section Deconditioning

open CLTMartingale.CondD

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Theorem 6**, unconditional form, given the conditional-law hypothesis `hfreeze`. -/
theorem pi_clt_unconditional_of_frozen {K : ℕ}
    (𝒟 : MeasurableSpace Ω) (h𝒟 : 𝒟 ≤ mΩ) (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (Ns : ℕ → ℝ) (pi0 : EuclideanSpace ℝ (Fin K))
    {pih : ℕ → Ω → EuclideanSpace ℝ (Fin K)}
    (hY : ∀ n : ℕ, AEMeasurable (fun ω => Real.sqrt (Ns n) • (pih n ω - pi0)) P)
    (Ups : Matrix (Fin K) (Fin K) ℝ)
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} (Q : Ω → @Measure Ω₀ mΩ₀)
    [∀ ω, IsProbabilityMeasure (Q ω)]
    (pih₀ : Ω → ℕ → Ω₀ → EuclideanSpace ℝ (Fin K))
    (hfreeze : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin K)),
      condCharFunD 𝒟 P (fun ω => Real.sqrt (Ns n) • (pih n ω - pi0)) t
        =ᵐ[P] fun ω => charFun (@Measure.map Ω₀ (EuclideanSpace ℝ (Fin K)) mΩ₀ _
          (fun ω₀ => Real.sqrt (Ns n) • (pih₀ ω n ω₀ - pi0)) (Q ω)) t)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mΩ₀)
      (fun (n : ℕ) (ω₀ : Ω₀) => Real.sqrt (Ns n) • (pih₀ ω n ω₀ - pi0)) atTop
      (fun z => Psiinv z) (fun _ => Q ω) (multivariateGaussian 0 Ups)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun (n : ℕ) ω => Real.sqrt (Ns n) • (pih n ω - pi0)) atTop
      (fun z => Psiinv z) (fun _ => P) (multivariateGaussian 0 Ups) := by
  have hZ : AEMeasurable (fun z : EuclideanSpace ℝ (Fin K) => Psiinv z)
      (multivariateGaussian 0 Ups) := Psiinv.continuous.measurable.aemeasurable
  refine tendstoInDistribution_of_deconditioning 𝒟 h𝒟 P
    (CLT.tendstoInMeasure_trivialDesign P) hY hZ ?_
  intro t ns hns _
  have hcond := CLT.tendsto_condCharFunD_of_frozen 𝒟 P
    (fun n ω => Real.sqrt (Ns n) • (pih n ω - pi0)) Q
    (fun ω n ω₀ => Real.sqrt (Ns n) • (pih₀ ω n ω₀ - pi0)) (multivariateGaussian 0 Ups)
    (fun z => Psiinv z) hfreeze hfrozen t
  filter_upwards [hcond] with ω hω
  exact hω.comp hns

end Deconditioning



/-- Slutsky through `Ψ_n⁻¹`, with the sandwich as the limit covariance. -/
theorem tendstoInDistribution_apply_of_solve_std {K : ℕ}
    {W : ℕ → Ω → EuclideanSpace ℝ (Fin K)} {Ups Sg : Matrix (Fin K) (Fin K) ℝ}
    (hUps : Ups.PosSemidef) (hSg : Sg.PosSemidef)
    (hW : TendstoInDistribution W atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Ups))
    {A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))}
    {Ainf : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)}
    (hA : Tendsto A atTop (𝓝 Ainf))
    (hsand : ∀ t : EuclideanSpace ℝ (Fin K),
      (ContinuousLinearMap.adjoint Ainf t) ⬝ᵥ (Ups *ᵥ (ContinuousLinearMap.adjoint Ainf t))
        = t ⬝ᵥ (Sg *ᵥ t))
    {dev : ℕ → Ω → EuclideanSpace ℝ (Fin K)} (hdevmeas : ∀ n, AEMeasurable (dev n) P)
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω, dev n ω = A n (W n ω)) :
    TendstoInDistribution dev atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Sg) := by
  refine TendstoInDistribution.of_inner (by fun_prop) hdevmeas ?_
  intro t
  have hY : TendstoInMeasure P
      (fun (n : ℕ) (_ : Ω) => (ContinuousLinearMap.adjoint (A n)) t) atTop
      (fun _ => (ContinuousLinearMap.adjoint Ainf) t) :=
    CLT.tendstoInMeasure_of_tendsto_const (CLT.tendsto_adjoint_apply hA t)
  have hSl := hW.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) => ⟪p.1, p.2⟫)
    (by fun_prop) hY (fun n => aemeasurable_const)
  have hlaw : (multivariateGaussian 0 Sg).map (fun x : EuclideanSpace ℝ (Fin K) => ⟪x, t⟫)
      = (multivariateGaussian 0 Ups).map
          (fun x : EuclideanSpace ℝ (Fin K) => ⟪x, (ContinuousLinearMap.adjoint Ainf) t⟫) := by
    rw [CLT.map_inner_multivariateGaussian hSg t,
      CLT.map_inner_multivariateGaussian hUps ((ContinuousLinearMap.adjoint Ainf) t), hsand t]
  have hSl2 := CLT.tendstoInDistribution_of_law_eq hSl (by fun_prop) hlaw
  refine CLT.tendstoInDistribution_of_eventually_ae_eq hSl2
    (fun n => (Continuous.measurable (by fun_prop :
      Continuous fun x : EuclideanSpace ℝ (Fin K) => ⟪x, t⟫)).comp_aemeasurable (hdevmeas n)) ?_
  filter_upwards [hsolve] with n hn
  filter_upwards with ω
  rw [hn ω, ← ContinuousLinearMap.adjoint_inner_right]

/-- **Theorem 6** in standard form: the limit is `N(0, Ψ⁻¹ΥΨ⁻¹)`. -/
theorem pi_clt_std {K : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    {O : ℕ → Type*} [∀ n, Fintype (O n)]
    (a Ns : ℕ → ℝ) (mx : ℕ → ℝ)
    (zc : ∀ n, J n → EuclideanSpace ℝ (Fin K)) (zt : ∀ n, O n → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, J n → Ω → ℝ) (eps : ∀ n, O n → Ω → ℝ)
    (vr : ∀ n, J n → ℝ) (sev : ∀ n, O n → ℝ) (C B Cs v0 : ℝ)
    (Ups Sg : Matrix (Fin K) (Fin K) ℝ) (hUps : Ups.PosDef) (hSg : Sg.PosSemidef)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hindepη : ∀ n, iIndepFun (etab n) P)
    (hmeanη : ∀ n j, ∫ ω, etab n j ω ∂P = 0) (hL2η : ∀ n j, MemLp (etab n j) 2 P)
    (hint4η : ∀ n j, Integrable (fun ω => etab n j ω ^ 4) P)
    (hvarη : ∀ n j, Var[etab n j; P] = vr n j)
    (hmomη : ∀ n j, ∫ ω, etab n j ω ^ 4 ∂P ≤ C)
    (hv0 : 0 < v0) (hvr : ∀ n j, v0 ≤ vr n j)
    (hmeasε : ∀ n o, Measurable (eps n o)) (hindepε : ∀ n, iIndepFun (eps n) P)
    (hL2ε : ∀ n o, MemLp (eps n o) 2 P) (hmeanε : ∀ n o, ∫ ω, eps n o ω ∂P = 0)
    (hvarε : ∀ n o, Var[eps n o; P] = sev n o)
    (hsev0 : ∀ n o, 0 ≤ sev n o) (hsev : ∀ n o, sev n o ≤ Cs)
    (hzt : ∀ n o, ‖zt n o‖ ^ 2 ≤ B ^ 2)
    (hi : Tendsto (fun n : ℕ => a n ^ 2 * (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ n, 0 ≤ mx n) (hmx : ∀ n j, ‖zc n j‖ ^ 2 ≤ mx n)
    (hmxsum : ∀ n, mx n ≤ ∑ j, ‖zc n j‖ ^ 2)
    (hiv : Tendsto (fun n : ℕ => mx n / ∑ j, ‖zc n j‖ ^ 2) atTop (𝓝 0))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (hA : Tendsto A atTop (𝓝 Psiinv))
    (hsand : ∀ t : EuclideanSpace ℝ (Fin K),
      (ContinuousLinearMap.adjoint Psiinv t) ⬝ᵥ (Ups *ᵥ (ContinuousLinearMap.adjoint Psiinv t))
        = t ⬝ᵥ (Sg *ᵥ t))
    (pih : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (pi0 : EuclideanSpace ℝ (Fin K))
    (hpimeas : ∀ n, AEMeasurable (pih n) P)
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω, Real.sqrt (Ns n) • (pih n ω - pi0)
      = A n (a n • ((∑ j, etab n j ω • zc n j) + (∑ o, eps n o ω • zt n o)))) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (Ns n) • (pih n ω - pi0)) atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Sg) := by
  have hlin4 := lin4_of_cond_iv a zc vr mx v0 hv0 hvr Ups hiii hmx0 hmx hmxsum hiv
  have hW := pi_score_clt (P := P) a zc zt etab eps vr sev C B Cs Ups hUps hmeasη hindepη
    hmeanη hL2η hint4η hvarη hmomη hmeasε hindepε hL2ε hmeanε hvarε hzt hsev0 hsev hi hiii hlin4
  exact tendstoInDistribution_apply_of_solve_std (P := P) hUps.posSemidef hSg hW hA hsand
    (fun n => (hpimeas n).sub_const pi0 |>.const_smul (Real.sqrt (Ns n))) hsolve

/-- **Theorem 12(b)** with its central limit theorem supplied by Theorem 6. -/
theorem piinf_wald_of_meat_of_pi_clt {K : ℕ}
    {Ns : ℕ → ℝ} (hNs : ∀ n, 0 < Ns n)
    {Sg : Matrix (Fin K) (Fin K) ℝ} (hSgPD : Sg.PosDef)
    {Uh : ℕ → Ω → Matrix (Fin K) (Fin K) ℝ} (hHerm : ∀ n ω, (Uh n ω).IsHermitian)
    (hUmeas : ∀ n, Measurable (Uh n))
    {Upn : ℕ → Matrix (Fin K) (Fin K) ℝ}
    (ha0 : TendstoInMeasure P (fun n ω => frobNorm (Uh n ω - Upn n)) atTop (fun _ => 0))
    (hlim : Tendsto (fun n => frobNorm (Upn n - Sg)) atTop (𝓝 0))
    {pih : ℕ → Ω → EuclideanSpace ℝ (Fin K)} {pi0 : EuclideanSpace ℝ (Fin K)}
    (hCLT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (Ns n) • (pih n ω - pi0)) atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Sg)) :
    Tendsto (fun n => P {ω | ((Ns n)⁻¹ • Uh n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => Wald.waldStat ((Ns n)⁻¹ • Uh n ω) (pih n ω - pi0)) atTop
          (fun z : EuclideanSpace ℝ (Fin K) => ‖z‖ ^ 2) (fun _ => P)
          (multivariateGaussian 0 1) :=
  piinf_wald_of_meat (P := P) (P' := multivariateGaussian 0 Sg) hNs hSgPD hHerm hUmeas ha0 hlim
    hCLT Measure.map_id

namespace PiWitness

open scoped ENNReal

/-- The category index of design `n`: `N_* = (n+1)^2` categories. -/
abbrev wJ (n : ℕ) : Type := Fin ((n + 1) ^ 2)

/-- The observations of design `n`: `(n+1)^3` of them, so that `N_*/n = 1/(n+1) → 0`. -/
abbrev wO (n : ℕ) : Type := Fin ((n + 1) ^ 3)

/-- `N_*` as a real. -/
noncomputable def wNs (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2

/-- `√N_*/n = (n+1)/(n+1)^3`. -/
noncomputable def wa (n : ℕ) : ℝ := (((n : ℝ) + 1) ^ 2)⁻¹

/-- `max_j ‖z_j‖^2`. -/
noncomputable def wmx (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2

/-- The category weight `z^{(m)}_j`, of length `n+1`. -/
noncomputable def wzc (n : ℕ) (_ : wJ n) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 fun _ => ((n : ℝ) + 1)

/-- The observation row `z̃_o`, of unit length. -/
noncomputable def wzt (n : ℕ) (_ : wO n) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 fun _ => (1 : ℝ)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `η̆^{(m)}_j` at design `n`: the `(2n, j)` slot of one i.i.d. Rademacher family. -/
noncomputable def weta (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (j : wJ n) : Ω → ℝ := ξ (2 * n, j.val)

/-- `ε_o` at design `n`: the `(2n+1, o)` slot of the same family. -/
noncomputable def weps (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (o : wO n) : Ω → ℝ := ξ (2 * n + 1, o.val)

/-- `π̂_n`, defined by the solved form of Lemma SM.B.4 at `Ψ̂_n = I`. -/
noncomputable def wpih (ξ : ℕ × ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin 1) :=
  (Real.sqrt (wNs n))⁻¹ •
    (wa n • ((∑ j, weta ξ n j ω • wzc n j) + (∑ o, weps ξ n o ω • wzt n o)))

theorem sqrt_wNs (n : ℕ) : Real.sqrt (wNs n) = (n : ℝ) + 1 := by
  rw [wNs, Real.sqrt_sq (by positivity)]

theorem norm_sq_wzc (n : ℕ) (j : wJ n) : ‖wzc n j‖ ^ 2 = ((n : ℝ) + 1) ^ 2 := by
  rw [euclidean_norm_sq]; simp [wzc]

theorem norm_sq_wzt (n : ℕ) (o : wO n) : ‖wzt n o‖ ^ 2 = 1 := by
  rw [euclidean_norm_sq]; simp [wzt]

theorem inner_wzc (n : ℕ) (j : wJ n) (t : EuclideanSpace ℝ (Fin 1)) :
    ⟪wzc n j, t⟫ = ((n : ℝ) + 1) * t 0 := by
  simp [wzc, PiLp.inner_apply, mul_comm]

theorem sum_norm_sq_wzc (n : ℕ) : ∑ j, ‖wzc n j‖ ^ 2 = ((n : ℝ) + 1) ^ 4 := by
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => norm_sq_wzc n j, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Condition (iii) holds exactly at every `n`, with limit `Υ = 1 ≻ 0`. -/
theorem upsilon_witness (t : EuclideanSpace ℝ (Fin 1)) (n : ℕ) :
    wa n ^ 2 * ∑ j, ⟪wzc n j, t⟫ ^ 2 * (1 : ℝ) = t 0 ^ 2 := by
  have hterm : ∀ j : wJ n, ⟪wzc n j, t⟫ ^ 2 * (1 : ℝ) = (((n : ℝ) + 1) * t 0) ^ 2 := by
    intro j; rw [inner_wzc n j t, mul_one]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, wa]
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem dotProduct_one_witness (t : EuclideanSpace ℝ (Fin 1)) :
    (t : EuclideanSpace ℝ (Fin 1)) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ t) = t 0 ^ 2 := by
  rw [Matrix.one_mulVec]
  simp only [dotProduct, Fin.sum_univ_one]
  ring

/-- `1/(n+1) → 0`. -/
theorem tendsto_inv_succ : Tendsto (fun n : ℕ => (((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  simpa [Pi.inv_def] using h.inv_tendsto_atTop

/-- `pi_clt` on an explicit sequence of designs. -/
theorem pi_clt_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt (wNs n) • (wpih ξ n ω - (0 : EuclideanSpace ℝ (Fin 1))))
        atTop (fun z => (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) z) (fun _ => P)
        (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
    ∧ (∀ n : ℕ, Fintype.card (wJ n) = (n + 1) ^ 2 ∧ Fintype.card (wO n) = (n + 1) ^ 3)
    ∧ (∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin 1)),
        wa n ^ 2 * ∑ j, ⟪wzc n j, t⟫ ^ 2 * (1 : ℝ) = t 0 ^ 2)
    ∧ (∀ n : ℕ, wmx n / ∑ j, ‖wzc n j‖ ^ 2 = (((n : ℝ) + 1) ^ 2)⁻¹)
    ∧ (∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin 1)),
        Var[fun ω => wa n * ∑ j, ⟪wzc n j, t⟫ * ξ (2 * n, j.val) ω; P] = t 0 ^ 2) := by
  classical
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ :=
    exists_iid (ℕ × ℕ) CLT.Witness.rade
  have hmeasη : ∀ (n : ℕ) (j : wJ n), Measurable (weta ξ n j) := fun n j => hmeasξ _
  have hmeasε : ∀ (n : ℕ) (o : wO n), Measurable (weps ξ n o) := fun n o => hmeasξ _
  have hindepη : ∀ n : ℕ, iIndepFun (weta ξ n) P := fun n =>
    hindepξ.precomp (g := fun j : wJ n => (2 * n, j.val))
      (fun a b hab => Fin.val_injective (congrArg Prod.snd hab))
  have hindepε : ∀ n : ℕ, iIndepFun (weps ξ n) P := fun n =>
    hindepξ.precomp (g := fun o : wO n => (2 * n + 1, o.val))
      (fun a b hab => Fin.val_injective (congrArg Prod.snd hab))
  have hmeanη : ∀ (n : ℕ) (j : wJ n), ∫ ω, weta ξ n j ω ∂P = 0 := by
    intro n j
    show ∫ ω, ξ (2 * n, j.val) ω ∂P = 0
    rw [(hlawξ (2 * n, j.val)).integral_eq, CLT.Witness.integral_id_rade]
  have hmeanε : ∀ (n : ℕ) (o : wO n), ∫ ω, weps ξ n o ω ∂P = 0 := by
    intro n o
    show ∫ ω, ξ (2 * n + 1, o.val) ω ∂P = 0
    rw [(hlawξ (2 * n + 1, o.val)).integral_eq, CLT.Witness.integral_id_rade]
  have hL2η : ∀ (n : ℕ) (j : wJ n), MemLp (weta ξ n j) 2 P := fun n j =>
    (hlawξ (2 * n, j.val)).memLp CLT.Witness.memLp_id_rade
  have hL2ε : ∀ (n : ℕ) (o : wO n), MemLp (weps ξ n o) 2 P := fun n o =>
    (hlawξ (2 * n + 1, o.val)).memLp CLT.Witness.memLp_id_rade
  have hint4η : ∀ (n : ℕ) (j : wJ n), Integrable (fun ω => weta ξ n j ω ^ 4) P := fun n j =>
    (hlawξ (2 * n, j.val)).integrable_fun_comp CLT.Witness.integrable_pow4_rade
  have hvarη : ∀ (n : ℕ) (j : wJ n), Var[weta ξ n j; P] = 1 := by
    intro n j
    show Var[ξ (2 * n, j.val); P] = 1
    rw [(hlawξ (2 * n, j.val)).variance_eq, CLT.Witness.variance_id_rade]
  have hvarε : ∀ (n : ℕ) (o : wO n), Var[weps ξ n o; P] = 1 := by
    intro n o
    show Var[ξ (2 * n + 1, o.val); P] = 1
    rw [(hlawξ (2 * n + 1, o.val)).variance_eq, CLT.Witness.variance_id_rade]
  have hmomη : ∀ (n : ℕ) (j : wJ n), ∫ ω, weta ξ n j ω ^ 4 ∂P ≤ 1 := by
    intro n j
    show ∫ ω, ξ (2 * n, j.val) ω ^ 4 ∂P ≤ 1
    have h : ∫ ω, ξ (2 * n, j.val) ω ^ 4 ∂P = ∫ x, x ^ 4 ∂CLT.Witness.rade := by
      simpa [Function.comp_def] using
        (hlawξ (2 * n, j.val)).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [h, CLT.Witness.integral_pow4_rade]
  -- the four conditions of the theorem, on this design
  have hi : Tendsto
      (fun n : ℕ => wa n ^ 2 * (Fintype.card (wO n) : ℝ) * ((1 : ℝ) ^ 2 * 1)) atTop (𝓝 0) := by
    refine tendsto_inv_succ.congr fun n => ?_
    rw [wa, Fintype.card_fin]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  have hiv : Tendsto (fun n : ℕ => wmx n / ∑ j, ‖wzc n j‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_inv_succ.pow 2
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at h
    refine h.congr fun n => ?_
    rw [wmx, sum_norm_sq_wzc]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω,
      Real.sqrt (wNs n) • (wpih ξ n ω - (0 : EuclideanSpace ℝ (Fin 1)))
        = (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))
            (wa n • ((∑ j, weta ξ n j ω • wzc n j) + (∑ o, weps ξ n o ω • wzt n o))) := by
    filter_upwards with n ω
    have hne : Real.sqrt (wNs n) ≠ 0 := by rw [sqrt_wNs]; positivity
    rw [sub_zero, wpih, smul_smul, mul_inv_cancel₀ hne, one_smul]
    rfl
  have hpimeas : ∀ n : ℕ, AEMeasurable (wpih ξ n) P := by
    intro n
    refine Measurable.aemeasurable ?_
    have h1 : Measurable fun ω => ∑ j, weta ξ n j ω • wzc n j :=
      Finset.measurable_sum _ fun j _ => (hmeasη n j).smul_const (wzc n j)
    have h2 : Measurable fun ω => ∑ o, weps ξ n o ω • wzt n o :=
      Finset.measurable_sum _ fun o _ => (hmeasε n o).smul_const (wzt n o)
    exact ((h1.add h2).const_smul (wa n)).const_smul ((Real.sqrt (wNs n))⁻¹)
  refine ⟨Ω, mΩ, P, hprobξ, ξ, ?_, ?_, fun n t => upsilon_witness t n, ?_, ?_⟩
  · refine pi_clt (P := P) wa wNs wmx wzc wzt (weta ξ) (weps ξ) (fun _ _ => 1) (fun _ _ => 1)
      1 1 1 1 1 Matrix.PosDef.one hmeasη hindepη hmeanη hL2η hint4η hvarη hmomη
      zero_lt_one (fun _ _ => le_refl 1) hmeasε hindepε hL2ε hmeanε hvarε
      (fun _ _ => zero_le_one) (fun _ _ => le_refl 1)
      (fun n o => by rw [norm_sq_wzt]; norm_num) hi ?_
      (fun n => by rw [wmx]; positivity) (fun n j => by rw [norm_sq_wzc, wmx])
      (fun n => ?_) hiv (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) tendsto_const_nhds
      (wpih ξ) 0 hpimeas hsolve
    · intro t
      rw [dotProduct_one_witness t]
      exact tendsto_const_nhds.congr fun n => (upsilon_witness t n).symm
    · rw [wmx, sum_norm_sq_wzc]
      have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [h0]
      calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 2 * 1 := by ring
        _ ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) + 1)]
        _ = ((n : ℝ) + 1) ^ 4 := by ring
  · exact fun n => ⟨Fintype.card_fin _, Fintype.card_fin _⟩
  · intro n
    rw [wmx, sum_norm_sq_wzc]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · intro n t
    have hfun : (fun ω => ∑ j, ⟪wzc n j, t⟫ * ξ (2 * n, j.val) ω)
        = ∑ j, fun ω => ⟪wzc n j, t⟫ * weta ξ n j ω := by
      funext ω; rw [Finset.sum_apply]; rfl
    have hL2' : ∀ j ∈ (Finset.univ : Finset (wJ n)),
        MemLp (fun ω => ⟪wzc n j, t⟫ * weta ξ n j ω) 2 P := fun j _ => (hL2η n j).const_mul _
    have hindep' : Set.Pairwise (↑(Finset.univ : Finset (wJ n)))
        fun j j' => IndepFun (fun ω => ⟪wzc n j, t⟫ * weta ξ n j ω)
          (fun ω => ⟪wzc n j', t⟫ * weta ξ n j' ω) P := by
      intro j _ j' _ hne
      exact (((hindepη n).indepFun hne).comp (measurable_const_mul _) (measurable_const_mul _))
    rw [variance_const_mul, hfun, IndepFun.variance_sum hL2' hindep',
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [variance_const_mul, hvarη n j, mul_one]]
    simpa using upsilon_witness t n

end PiWitness
end PiCLT


/-! ## §8 The `O_p` inputs of clause (a) from the second moments

`piinf_a_of_step1` is clause (a) with `hproj`, `hresid` and `hscore` derived rather than assumed,
leaving `hstep1`. The inputs are the second-moment identity `hEu` (as in `piinf_c`), with
`omegaU` the kernel `Ω_u`, and a symmetric idempotent matrix `Pim` with `tr(Pim) ≤ R` standing
for `P_{C_1}`.

* `proj_bddInProb`: `‖P_{C_1}u‖² = O_p(G_max)`, via `tr(PΩ_u) ≤ g·tr(P)`.
* `residSq_bddInProb_of_omega`: `‖û‖² = O_p(n)`.
* `hscore_of_hstep1`: `hscore` follows from `hstep1` and a bound on `tr(Υ_n)`. -/
section Step1Inputs

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

/-! ### §8a Facts about `O_p(1)`

`bddInProb_of_tendstoInProb` shows `Z_n ⟶^p 0 ⟹ Z_n = O_p(1)` for a.e.-measurable `Z_n`. -/
section OpFacts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- A nonnegative null sequence is bounded, with an explicit bound. -/
theorem exists_forall_le_of_tendsto_zero {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hf : Tendsto f atTop (𝓝 (0 : ℝ))) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, f n ≤ C := by
  have h1 : ∀ᶠ n in atTop, f n < 1 := hf.eventually_lt tendsto_const_nhds zero_lt_one
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h1
  have hs : (0 : ℝ) ≤ ∑ i ∈ Finset.range N, f i := Finset.sum_nonneg fun i _ => hf0 i
  refine ⟨1 + ∑ i ∈ Finset.range N, f i, by linarith, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have := (hN n hn).le
    linarith
  · have hn' : n < N := Nat.lt_of_not_le hn
    have h3 : f n ≤ ∑ i ∈ Finset.range N, f i :=
      Finset.single_le_sum (f := f) (fun i _ => hf0 i) (Finset.mem_range.2 hn')
    linarith

/-- For an a.e.-measurable real random variable, `P(|Y| ≥ k) ≤ δ` for some `k`, by continuity
from above. -/
theorem exists_tail_bound (Y : Ω → ℝ) (hY : AEMeasurable Y P) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ P {ω | C ≤ |Y ω|} ≤ δ := by
  set s : ℕ → Set Ω := fun k => {ω | ((k : ℕ) : ℝ) ≤ |Y ω|} with hsdef
  have hmeasS : ∀ k, NullMeasurableSet (s k) P := fun k =>
    nullMeasurableSet_le aemeasurable_const hY.abs
  have hanti : Antitone s := by
    intro i j hij ω hω
    have h1 : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    exact le_trans h1 hω
  have hinter : (⋂ k, s k) = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := exists_nat_gt |Y ω|
    exact ⟨k, not_le.2 hk⟩
  have hlim := tendsto_measure_iInter_atTop (μ := P) hmeasS hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  have hev : ∀ᶠ k in atTop, (P ∘ s) k < δ := hlim.eventually_lt tendsto_const_nhds hδ
  obtain ⟨k, hk⟩ := hev.exists
  exact ⟨(k : ℝ), Nat.cast_nonneg k, hk.le⟩

/-- If `Z_n ⟶^p 0` and each `Z_n` is a.e.-measurable, then `Z_n = O_p(1)`. -/
theorem bddInProb_of_tendstoInProb {Z : ℕ → Ω → ℝ}
    (hmeas : ∀ n, AEMeasurable (Z n) P)
    (hZ : TendstoInMeasure P Z atTop (fun _ => (0 : ℝ))) :
    Sequence.BddInProb P Z := by
  rw [tendstoInMeasure_iff_dist] at hZ
  intro δ hδ
  have h1 := hZ 1 one_pos
  have h2 : ∀ᶠ n in atTop,
      P {ω | (1 : ℝ) ≤ dist (Z n ω) ((fun _ : Ω => (0 : ℝ)) ω)} < δ :=
    h1.eventually_lt tendsto_const_nhds hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h2
  choose Cc hCc0 hCcb using fun n : ℕ => exists_tail_bound (P := P) (Z n) (hmeas n) hδ
  have hs : (0 : ℝ) ≤ ∑ i ∈ Finset.range N, Cc i := Finset.sum_nonneg fun i _ => hCc0 i
  refine ⟨1 + ∑ i ∈ Finset.range N, Cc i, by linarith, fun n => ?_⟩
  by_cases hn : N ≤ n
  · refine le_trans (measure_mono ?_) (hN n hn).le
    intro ω hω
    have h3 : 1 + ∑ i ∈ Finset.range N, Cc i ≤ |Z n ω| := hω
    show (1 : ℝ) ≤ dist (Z n ω) ((fun _ : Ω => (0 : ℝ)) ω)
    rw [Real.dist_eq, sub_zero]
    linarith
  · have hn' : n < N := Nat.lt_of_not_le hn
    refine le_trans (measure_mono ?_) (hCcb n)
    intro ω hω
    have h3 : 1 + ∑ i ∈ Finset.range N, Cc i ≤ |Z n ω| := hω
    have h5 : Cc n ≤ ∑ i ∈ Finset.range N, Cc i :=
      Finset.single_le_sum (f := Cc) (fun i _ => hCc0 i) (Finset.mem_range.2 hn')
    show Cc n ≤ |Z n ω|
    linarith

omit [IsProbabilityMeasure P] in
/-- `|W_n| ≤ |Z_n| + c` with `Z_n = O_p(1)` gives `W_n = O_p(1)`. -/
theorem bddInProb_of_abs_le_add_const {W Z : ℕ → Ω → ℝ} {cst : ℝ}
    (hle : ∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ |Z n ω| + cst) (hZ : Sequence.BddInProb P Z) :
    Sequence.BddInProb P W := by
  intro δ hδ
  obtain ⟨C, hC0, hCb⟩ := hZ δ hδ
  refine ⟨C + |cst|, by positivity, fun n => ?_⟩
  refine le_trans (measure_mono_ae ?_) (hCb n)
  filter_upwards [hle n] with ω hω hmem
  have h1 : C + |cst| ≤ |W n ω| := hmem
  have h2 : cst ≤ |cst| := le_abs_self cst
  show C ≤ |Z n ω|
  linarith

end OpFacts

/-! ### §8b The trace of the dimension-wise meat -/
section Trace

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable [Fintype K] [DecidableEq K]

omit [DecidableEq D] [DecidableEq K] in
/-- `tr(Υ̂^dim) = ∑_{m,j}‖ĝ^{(m)}_j‖²`. -/
theorem trace_dimMeat (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (v : O → ℝ) :
    (dimMeat c dims z v).trace
      = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D), vecSqNorm (cellScore z v t) := by
  simp only [Matrix.trace, Matrix.diag_apply, dimMeat, Matrix.sum_apply,
    Matrix.vecMulVec_apply, vecSqNorm, pow_two]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_comm

end Trace

section TraceNorm

variable [Fintype K]

/-- `|tr(M)| ≤ √r ‖M‖_F`. -/
theorem abs_trace_le (M : Matrix K K ℝ) :
    |M.trace| ≤ Real.sqrt (Fintype.card K) * frobNorm M := by
  have h := sq_trace_le M
  have h1 : |M.trace| = Real.sqrt (M.trace ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [h1]
  calc Real.sqrt (M.trace ^ 2) ≤ Real.sqrt ((Fintype.card K : ℝ) * frobSq M) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt (Fintype.card K) * frobNorm M := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), frobNorm]

end TraceNorm

/-! ### §8c `hscore` from `hstep1`

Taking traces of Step 1's conclusion gives `N_*n^{-2}∑_{m,j}‖g^{(m)}_j‖² - tr(Υ_n) ⟶^p 0`, and
`tr(Υ_n) = O(1)` by condition (iii) of Theorem 6. -/
section Score

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Dn On Ln : ℕ → Type*}
  [∀ n, Fintype (On n)] [∀ n, DecidableEq (On n)]
  [∀ n, DecidableEq (Dn n)] [∀ n, DecidableEq (Ln n)]
variable [Fintype K] [DecidableEq K]

/-- From `‖a_n•Υ̂^dim(u) - Υ_n‖_F ⟶^p 0` and `|tr(Υ_n)| ≤ Cb`,
`a_n∑_{m,j}‖g^{(m)}_j‖² = O_p(1)`. -/
theorem hscore_of_hstep1
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, Ω → On n → K → ℝ) (u : ∀ n, Ω → On n → ℝ)
    {Ups : ℕ → Matrix K K ℝ} {a : ℕ → ℝ} {Cb : ℝ}
    (hmeas : ∀ n, AEMeasurable (fun ω =>
      frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n)) P)
    (hUps : ∀ n, |(Ups n).trace| ≤ Cb)
    (hstep1 : TendstoInMeasure P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n))
      atTop (fun _ => 0)) :
    Sequence.BddInProb P
      (fun n ω => a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
        vecSqNorm (cellScore (z n ω) (u n ω) t)) := by
  have hZ : Sequence.BddInProb P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n)) :=
    bddInProb_of_tendstoInProb hmeas hstep1
  have hZ' := Sequence.bddInProb_const_mul (P := P) (Real.sqrt (Fintype.card K)) hZ
  refine bddInProb_of_abs_le_add_const (cst := Cb)
    (fun n => Filter.Eventually.of_forall fun ω => ?_) hZ'
  have htr : a n * ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
      vecSqNorm (cellScore (z n ω) (u n ω) t)
      = (a n • dimMeat (c n) (dims n) (z n ω) (u n ω)).trace := by
    rw [Matrix.trace_smul, smul_eq_mul, trace_dimMeat]
  have hdec : (a n • dimMeat (c n) (dims n) (z n ω) (u n ω)).trace
      = (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n).trace + (Ups n).trace := by
    rw [Matrix.trace_sub]; ring
  have hb := abs_trace_le (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n)
  have hnn : (0 : ℝ) ≤ Real.sqrt (Fintype.card K) *
      frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n) :=
    mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg _)
  rw [htr, hdec, abs_of_nonneg hnn]
  calc |(a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n).trace + (Ups n).trace|
      ≤ |(a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n).trace| + |(Ups n).trace| :=
        abs_add_le _ _
    _ ≤ Real.sqrt (Fintype.card K) *
          frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n) + Cb :=
        add_le_add hb (hUps n)

end Score

/-! ### §8d `Ω_u ⪯ (Mς̄²G_max + σ̄²)I` as a quadratic form -/
section Omega

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] in
/-- `o ⊙ {m} = o' ⊙ {m}` is `i_m(o) = i_m(o')`. -/
theorem sameOn_singleton (c : D → O → L) (m : D) (o o' : O) :
    SameOn c ({m} : Finset D) o o' ↔ c m o = c m o' := by
  constructor
  · intro h; exact h m (Finset.mem_singleton_self m)
  · intro h j hj; rw [Finset.mem_singleton.1 hj]; exact h

/-- `x'Δ_FΔ_F'x ≥ 0`. -/
theorem shareQuad_nonneg (c : D → O → L) (F : Finset D) (x : O → ℝ) :
    0 ≤ ∑ o : O, ∑ o' : O, (if SameOn c F o o' then x o * x o' else 0) := by
  rw [← sum_cells_pair c F fun o o' => x o * x o']
  refine Finset.sum_nonneg fun t _ => ?_
  have hsq : (∑ o ∈ t, ∑ o' ∈ t, x o * x o') = (∑ o ∈ t, x o) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
  rw [hsq]
  positivity

/-- `Ω_u = ∑_m ς²_mΔ_mΔ_m' + diag(σ²_ε(o))`, as a kernel on pairs. -/
def omegaU (c : D → O → L) (dims : Finset D) (vr : D → ℝ) (sg : O → ℝ) : O → O → ℝ :=
  fun o o' => (∑ m ∈ dims, vr m ^ 2 * (if c m o = c m o' then (1 : ℝ) else 0))
    + (if o = o' then sg o ^ 2 else 0)

/-- `Ω_u(o,o) = ∑_m ς²_m + σ²_ε(o)`. -/
theorem omegaU_diag (c : D → O → L) (dims : Finset D) (vr : D → ℝ) (sg : O → ℝ) (o : O) :
    omegaU c dims vr sg o o = (∑ m ∈ dims, vr m ^ 2) + sg o ^ 2 := by
  simp [omegaU]

/-- `x'Ω_ux ≤ (M̄ς̄²G_max + σ̄²)‖x‖²`, from `shareQuad_le` at each singleton level `{m}`. -/
theorem omegaU_quad_le (c : D → O → L) (dims : Finset D) (vr : D → ℝ) (sg : O → ℝ)
    (x : O → ℝ) {G Cvr Csg Mbar : ℝ}
    (hcell : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), (t.card : ℝ) ≤ G)
    (hG : 0 ≤ G) (hvr : ∀ m, vr m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ o, sg o ^ 2 ≤ Csg)
    (hM : ((dims).card : ℝ) ≤ Mbar) :
    ∑ o : O, ∑ o' : O, omegaU c dims vr sg o o' * (x o * x o')
      ≤ (Mbar * (Cvr * G) + Csg) * ∑ o : O, x o ^ 2 := by
  classical
  have hxnn : (0 : ℝ) ≤ ∑ o : O, x o ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsplit : ∀ o o' : O, omegaU c dims vr sg o o' * (x o * x o')
      = (∑ m ∈ dims, vr m ^ 2 * (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0))
        + (if o = o' then sg o ^ 2 * (x o * x o') else 0) := by
    intro o o'
    simp only [omegaU, add_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      by_cases h : c m o = c m o'
      · have h2 : SameOn c ({m} : Finset D) o o' := (sameOn_singleton c m o o').2 h
        simp [h, h2]
      · have h2 : ¬ SameOn c ({m} : Finset D) o o' :=
          fun hc => h ((sameOn_singleton c m o o').1 hc)
        simp [h, h2]
    · by_cases h : o = o' <;> simp [h]
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) =>
    Finset.sum_congr rfl fun o' (_ : o' ∈ Finset.univ) => hsplit o o']
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hT2 : (∑ o : O, ∑ o' : O, (if o = o' then sg o ^ 2 * (x o * x o') else 0))
      = ∑ o : O, sg o ^ 2 * x o ^ 2 := by
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_ite_eq (Finset.univ : Finset O) o (fun o' => sg o ^ 2 * (x o * x o'))]
    simp [pow_two]
  have hT2le : (∑ o : O, sg o ^ 2 * x o ^ 2) ≤ Csg * ∑ o : O, x o ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_right (hsg o) (sq_nonneg _)
  have hswap : ∀ o : O, (∑ o' : O, ∑ m ∈ dims,
      vr m ^ 2 * (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0))
      = ∑ m ∈ dims, ∑ o' : O,
        vr m ^ 2 * (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0) :=
    fun o => Finset.sum_comm
  have hT1 : (∑ o : O, ∑ o' : O, ∑ m ∈ dims,
      vr m ^ 2 * (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0))
      = ∑ m ∈ dims, vr m ^ 2 * (∑ o : O, ∑ o' : O,
          (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0)) := by
    rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => hswap o, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun o _ => by rw [Finset.mul_sum]
  have hT1le : (∑ m ∈ dims, vr m ^ 2 * (∑ o : O, ∑ o' : O,
      (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0)))
      ≤ Mbar * (Cvr * (G * ∑ o : O, x o ^ 2)) := by
    have hterm : ∀ m ∈ dims, vr m ^ 2 * (∑ o : O, ∑ o' : O,
        (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0))
        ≤ Cvr * (G * ∑ o : O, x o ^ 2) := by
      intro m hm
      have hnn := shareQuad_nonneg c ({m} : Finset D) x
      have hle := shareQuad_le c ({m} : Finset D) x (g := G) (fun t ht => hcell m hm t ht)
      calc vr m ^ 2 * (∑ o : O, ∑ o' : O,
            (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0))
          ≤ Cvr * (∑ o : O, ∑ o' : O,
            (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0)) :=
            mul_le_mul_of_nonneg_right (hvr m) hnn
        _ ≤ Cvr * (G * ∑ o : O, x o ^ 2) := mul_le_mul_of_nonneg_left hle hCvr
    calc (∑ m ∈ dims, vr m ^ 2 * (∑ o : O, ∑ o' : O,
          (if SameOn c ({m} : Finset D) o o' then x o * x o' else 0)))
        ≤ ∑ _m ∈ dims, Cvr * (G * ∑ o : O, x o ^ 2) := Finset.sum_le_sum hterm
      _ = ((dims.card : ℝ)) * (Cvr * (G * ∑ o : O, x o ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Mbar * (Cvr * (G * ∑ o : O, x o ^ 2)) :=
          mul_le_mul_of_nonneg_right hM (mul_nonneg hCvr (mul_nonneg hG hxnn))
  rw [hT1, hT2]
  have hid : Mbar * (Cvr * (G * ∑ o : O, x o ^ 2)) + Csg * ∑ o : O, x o ^ 2
      = (Mbar * (Cvr * G) + Csg) * ∑ o : O, x o ^ 2 := by ring
  linarith [hT1le, hT2le, hid]

end Omega

/-! ### §8e `tr(PΩ) ≤ g·tr(P)`

For `P` symmetric and idempotent, `tr(PΩ) = ∑_p (P_{p·})'Ω(P_{p·})`, so `x'Ωx ≤ g‖x‖²` gives
`tr(PΩ) ≤ g∑_p‖P_{p·}‖² = g·tr(P)`. Also `‖u - Pu‖² = ‖u‖² - ‖Pu‖²`. -/
section Projector

variable [Fintype O] [DecidableEq O]

omit [Fintype O] in
/-- `Pᵀ = P` read at a pair of indices. -/
theorem symm_apply_of_transpose {Pim : Matrix O O ℝ} (hsym : Pimᵀ = Pim) (p q : O) :
    Pim p q = Pim q p := by
  have h := congrFun (congrFun hsym q) p
  simpa [Matrix.transpose_apply] using h

/-- `∑_{p,o}P_{po}² = tr(P)` for `P` symmetric idempotent. -/
theorem sum_sq_row_eq_trace {Pim : Matrix O O ℝ} (hsym : Pimᵀ = Pim)
    (hidem : Pim * Pim = Pim) :
    ∑ p : O, ∑ o : O, (Pim p o) ^ 2 = Pim.trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : ∑ o : O, (Pim p o) ^ 2 = ∑ o : O, Pim p o * Pim o p := by
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [pow_two, symm_apply_of_transpose hsym p o]
  rw [h1]
  have h2 : (Pim * Pim) p p = ∑ o : O, Pim p o * Pim o p := Matrix.mul_apply
  rw [← h2, hidem]

/-- `tr(PΩ) ≤ g·tr(P) ≤ g·R` for `P` symmetric idempotent and `x'Ωx ≤ g‖x‖²`. -/
theorem trace_quad_le {Pim : Matrix O O ℝ} (hsym : Pimᵀ = Pim) (hidem : Pim * Pim = Pim)
    (Ker : O → O → ℝ) {g R : ℝ} (hg : 0 ≤ g)
    (hquad : ∀ x : O → ℝ, ∑ o : O, ∑ o' : O, Ker o o' * (x o * x o') ≤ g * ∑ o : O, x o ^ 2)
    (htr : Pim.trace ≤ R) :
    ∑ o : O, ∑ o' : O, Pim o o' * Ker o o' ≤ g * R := by
  have hexp : ∀ o o' : O, Pim o o' * Ker o o'
      = ∑ p : O, Ker o o' * (Pim p o * Pim p o') := by
    intro o o'
    have h1 : Pim o o' = ∑ p : O, Pim o p * Pim p o' := by
      have h := Matrix.mul_apply (M := Pim) (N := Pim) (i := o) (k := o')
      rw [hidem] at h
      exact h
    rw [h1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [symm_apply_of_transpose hsym o p]
    ring
  have hswap : ∀ o : O, (∑ o' : O, ∑ p : O, Ker o o' * (Pim p o * Pim p o'))
      = ∑ p : O, ∑ o' : O, Ker o o' * (Pim p o * Pim p o') := fun o => Finset.sum_comm
  have hkey : ∑ o : O, ∑ o' : O, Pim o o' * Ker o o'
      = ∑ p : O, ∑ o : O, ∑ o' : O, Ker o o' * (Pim p o * Pim p o') := by
    rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) =>
      Finset.sum_congr rfl fun o' (_ : o' ∈ Finset.univ) => hexp o o']
    rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => hswap o]
    exact Finset.sum_comm
  rw [hkey]
  calc ∑ p : O, ∑ o : O, ∑ o' : O, Ker o o' * (Pim p o * Pim p o')
      ≤ ∑ _p : O, g * ∑ o : O, (Pim _p o) ^ 2 :=
        Finset.sum_le_sum fun p _ => hquad (fun o => Pim p o)
    _ = g * ∑ p : O, ∑ o : O, (Pim p o) ^ 2 := by rw [Finset.mul_sum]
    _ = g * Pim.trace := by rw [sum_sq_row_eq_trace hsym hidem]
    _ ≤ g * R := mul_le_mul_of_nonneg_left htr hg

/-- `‖Pu‖² = ∑_{p,q}P_{pq}u_pu_q` for `P` symmetric idempotent. -/
theorem sum_sq_mulVec {Pim : Matrix O O ℝ} (hsym : Pimᵀ = Pim) (hidem : Pim * Pim = Pim)
    (y : O → ℝ) :
    ∑ o : O, (Pim.mulVec y o) ^ 2 = ∑ p : O, ∑ q : O, Pim p q * (y p * y q) := by
  have hstep : ∀ o : O, (Pim.mulVec y o) ^ 2
      = ∑ p : O, ∑ q : O, (Pim o p * y p) * (Pim o q * y q) := by
    intro o
    have hmv : Pim.mulVec y o = ∑ p : O, Pim o p * y p := by
      simp [Matrix.mulVec, dotProduct]
    rw [hmv, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => hstep o, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : ∑ o : O, (Pim o p * y p) * (Pim o q * y q)
      = (∑ o : O, Pim p o * Pim o q) * (y p * y q) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [symm_apply_of_transpose hsym o p]
    ring
  rw [h1]
  have h2 : (Pim * Pim) p q = ∑ o : O, Pim p o * Pim o q := Matrix.mul_apply
  rw [← h2, hidem]

/-- `‖u - Pu‖² = ‖u‖² - ‖Pu‖²` for `P` symmetric idempotent. -/
theorem sum_sq_sub_mulVec {Pim : Matrix O O ℝ} (hsym : Pimᵀ = Pim) (hidem : Pim * Pim = Pim)
    (y : O → ℝ) :
    ∑ o : O, (y o - Pim.mulVec y o) ^ 2
      = (∑ o : O, y o ^ 2) - ∑ o : O, (Pim.mulVec y o) ^ 2 := by
  have hmv : ∀ o : O, Pim.mulVec y o = ∑ p : O, Pim o p * y p := by
    intro o; simp [Matrix.mulVec, dotProduct]
  have hcross : ∑ o : O, y o * Pim.mulVec y o = ∑ o : O, (Pim.mulVec y o) ^ 2 := by
    have hL : ∑ o : O, y o * Pim.mulVec y o = ∑ o : O, ∑ p : O, Pim o p * (y o * y p) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [hmv o, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hL, sum_sq_mulVec hsym hidem y]
  have hexp : ∀ o : O, (y o - Pim.mulVec y o) ^ 2
      = y o ^ 2 - 2 * (y o * Pim.mulVec y o) + (Pim.mulVec y o) ^ 2 := fun o => by ring
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => hexp o]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcross]
  ring

end Projector

/-! ### §8f The two `O_p` bounds

`E‖P_{C_1}u‖² = tr(PΩ_u) ≤ (M̄ς̄²G_max + σ̄²)R` and `E‖u‖² = tr(Ω_u) ≤ n(M̄ς̄² + σ̄²)`, followed
by Markov's inequality. -/
section ProjMoment

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

section Single

variable [Fintype O] [DecidableEq O]

/-- `E[‖Pu‖²] = ∑_{p,q}P_{pq}Ω_u(p,q)`. `hint` is integrability of each product `u_pu_q`. -/
theorem integral_sum_sq_mulVec {Pim : Matrix O O ℝ} (hsym : Pimᵀ = Pim)
    (hidem : Pim * Pim = Pim) (u : Ω → O → ℝ) (Ker : O → O → ℝ)
    (hint : ∀ p q, Integrable (fun ω => u ω p * u ω q) P)
    (hEu : ∀ p q, ∫ ω, u ω p * u ω q ∂P = Ker p q) :
    ∫ ω, (∑ o : O, (Pim.mulVec (u ω) o) ^ 2) ∂P = ∑ p : O, ∑ q : O, Pim p q * Ker p q := by
  have hstep : ∀ ω, (∑ o : O, (Pim.mulVec (u ω) o) ^ 2)
      = ∑ p : O, ∑ q : O, Pim p q * (u ω p * u ω q) :=
    fun ω => sum_sq_mulVec hsym hidem (u ω)
  simp_rw [hstep]
  have hinner : ∀ p : O, ∫ ω, (∑ q : O, Pim p q * (u ω p * u ω q)) ∂P
      = ∑ q : O, Pim p q * Ker p q := by
    intro p
    have h := MeasureTheory.integral_finsetSum (μ := P) (s := (Finset.univ : Finset O))
      (f := fun q ω => Pim p q * (u ω p * u ω q))
      (fun q _ => (hint p q).const_mul (Pim p q))
    rw [h]
    exact Finset.sum_congr rfl fun q _ => by rw [integral_const_mul, hEu p q]
  have houter := MeasureTheory.integral_finsetSum (μ := P) (s := (Finset.univ : Finset O))
    (f := fun p ω => ∑ q : O, Pim p q * (u ω p * u ω q))
    (fun p _ => MeasureTheory.integrable_finsetSum _
      (fun q _ => (hint p q).const_mul (Pim p q)))
  rw [houter]
  exact Finset.sum_congr rfl fun p _ => hinner p

end Single

variable {Dn On Ln : ℕ → Type*}
  [∀ n, Fintype (On n)] [∀ n, DecidableEq (On n)]
  [∀ n, DecidableEq (Dn n)] [∀ n, DecidableEq (Ln n)]

/-- `‖P_{C_1}u‖² = O_p(G_max)`. Here `hsym`, `hidem` and `htr` say that `Pim` is symmetric,
idempotent and of trace at most `R`; `hw` is `û = u - Pim u`; `hEu` is the second-moment identity;
`hcell` bounds the category sizes by `G_max ≥ 1`; `hvr` and `hsg` bound the variances. -/
theorem proj_bddInProb
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (u v : ∀ n, Ω → On n → ℝ) (Pim : ∀ n, Matrix (On n) (On n) ℝ)
    (vr : ∀ n, Dn n → ℝ) (sg : ∀ n, On n → ℝ)
    {G : ℕ → ℝ} {R Cvr Csg Mbar : ℝ}
    (hsym : ∀ n, (Pim n)ᵀ = Pim n) (hidem : ∀ n, Pim n * Pim n = Pim n)
    (htr : ∀ n, (Pim n).trace ≤ R) (hR : 0 ≤ R)
    (hw : ∀ n ω o, v n ω o - u n ω o = -((Pim n).mulVec (u n ω) o))
    (hint : ∀ n p q, Integrable (fun ω => u n ω p * u n ω q) P)
    (hEu : ∀ n p q, ∫ ω, u n ω p * u n ω q ∂P = omegaU (c n) (dims n) (vr n) (sg n) p q)
    (hcell : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)), (t.card : ℝ) ≤ G n)
    (hG : ∀ n, 1 ≤ G n)
    (hvr : ∀ n m, vr n m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ n o, sg n o ^ 2 ≤ Csg) (hCsg : 0 ≤ Csg)
    (hM : ∀ n, ((dims n).card : ℝ) ≤ Mbar) (hMbar : 0 ≤ Mbar) :
    Sequence.BddInProb P (fun n ω => (∑ o : On n, (v n ω o - u n ω o) ^ 2) / G n) := by
  have hGpos : ∀ n, (0 : ℝ) < G n := fun n => lt_of_lt_of_le zero_lt_one (hG n)
  have hfun : (fun (n : ℕ) (ω : Ω) => (∑ o : On n, (v n ω o - u n ω o) ^ 2) / G n)
      = fun (n : ℕ) (ω : Ω) => (∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2) / G n := by
    funext n ω
    congr 1
    exact Finset.sum_congr rfl fun o _ => by rw [hw n ω o]; ring
  rw [hfun]
  have hnum : ∀ n, Integrable
      (fun ω => ∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2) P := by
    intro n
    have h1 : (fun ω => ∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2)
        = fun ω => ∑ p : On n, ∑ q : On n, (Pim n) p q * (u n ω p * u n ω q) :=
      funext fun ω => sum_sq_mulVec (hsym n) (hidem n) (u n ω)
    rw [h1]
    exact MeasureTheory.integrable_finsetSum _ fun p _ =>
      MeasureTheory.integrable_finsetSum _ fun q _ => (hint n p q).const_mul _
  have hintg : ∀ n, Integrable
      (fun ω => (∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2) / G n) P :=
    fun n => (hnum n).div_const _
  have hmean : ∀ n, ∫ ω, (∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2) / G n ∂P
      ≤ R * (Mbar * Cvr + Csg) := by
    intro n
    rw [integral_div, integral_sum_sq_mulVec (P := P) (hsym n) (hidem n) (u n) _
      (hint n) (hEu n)]
    have hgnn : (0 : ℝ) ≤ Mbar * (Cvr * G n) + Csg :=
      add_nonneg (mul_nonneg hMbar (mul_nonneg hCvr (hGpos n).le)) hCsg
    have hq := trace_quad_le (hsym n) (hidem n)
      (omegaU (c n) (dims n) (vr n) (sg n)) (g := Mbar * (Cvr * G n) + Csg) (R := R) hgnn
      (fun x => omegaU_quad_le (c n) (dims n) (vr n) (sg n) x (hcell n) (hGpos n).le
        (hvr n) hCvr (hsg n) (hM n)) (htr n)
    have hdiv : (Mbar * (Cvr * G n) + Csg) * R / G n ≤ R * (Mbar * Cvr + Csg) := by
      rw [div_le_iff₀ (hGpos n)]
      have key : 0 ≤ Csg * R * (G n - 1) :=
        mul_nonneg (mul_nonneg hCsg hR) (by linarith [hG n])
      nlinarith [key]
    calc (∑ p : On n, ∑ q : On n, (Pim n) p q * omegaU (c n) (dims n) (vr n) (sg n) p q) / G n
        ≤ ((Mbar * (Cvr * G n) + Csg) * R) / G n :=
          div_le_div_of_nonneg_right hq (hGpos n).le
      _ ≤ R * (Mbar * Cvr + Csg) := hdiv
  refine Sequence.bddInProb_of_lintegral_le (fun n => (hintg n).aemeasurable)
    (M := ENNReal.ofReal (R * (Mbar * Cvr + Csg))) ENNReal.ofReal_ne_top (fun n => ?_)
  have hnn : 0 ≤ᵐ[P] fun ω => (∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2) / G n :=
    Filter.Eventually.of_forall fun ω =>
      div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hGpos n).le
  have hae : ∀ᵐ ω ∂P, ‖(∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2) / G n‖ₑ
      = ENNReal.ofReal ((∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2) / G n) := by
    filter_upwards with ω
    rw [Real.enorm_eq_ofReal
      (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hGpos n).le)]
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal (hintg n) hnn]
  exact ENNReal.ofReal_le_ofReal (hmean n)

/-- `‖û‖²/n = O_p(1)`, from `û = u - Pim u`, `tr(Ω_u) ≤ Cn` and Markov's inequality. -/
theorem residSq_bddInProb_of_omega
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (u v : ∀ n, Ω → On n → ℝ) (Pim : ∀ n, Matrix (On n) (On n) ℝ)
    (vr : ∀ n, Dn n → ℝ) (sg : ∀ n, On n → ℝ)
    {Cvr Csg Mbar : ℝ}
    (hsym : ∀ n, (Pim n)ᵀ = Pim n) (hidem : ∀ n, Pim n * Pim n = Pim n)
    (hw : ∀ n ω o, v n ω o - u n ω o = -((Pim n).mulVec (u n ω) o))
    (hint : ∀ n p q, Integrable (fun ω => u n ω p * u n ω q) P)
    (hEu : ∀ n p q, ∫ ω, u n ω p * u n ω q ∂P = omegaU (c n) (dims n) (vr n) (sg n) p q)
    (hcard : ∀ n, 0 < (Fintype.card (On n) : ℝ))
    (hvr : ∀ n m, vr n m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ n o, sg n o ^ 2 ≤ Csg)
    (hM : ∀ n, ((dims n).card : ℝ) ≤ Mbar) :
    Sequence.BddInProb P
      (fun n ω => (∑ o : On n, v n ω o ^ 2) / (Fintype.card (On n) : ℝ)) := by
  have hdom : ∀ n, ∀ᵐ ω ∂P, ∑ o : On n, v n ω o ^ 2 ≤ ∑ o : On n, u n ω o ^ 2 := by
    intro n
    refine Filter.Eventually.of_forall fun ω => ?_
    have hv : ∀ o : On n, v n ω o = u n ω o - (Pim n).mulVec (u n ω) o := by
      intro o
      have := hw n ω o
      linarith
    rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => by rw [hv o],
      sum_sq_sub_mulVec (hsym n) (hidem n)]
    have : (0 : ℝ) ≤ ∑ o : On n, ((Pim n).mulVec (u n ω) o) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hnum : ∀ n, Integrable (fun ω => ∑ o : On n, u n ω o ^ 2) P := by
    intro n
    have h1 : (fun ω => ∑ o : On n, u n ω o ^ 2)
        = fun ω => ∑ o : On n, u n ω o * u n ω o := by
      funext ω
      exact Finset.sum_congr rfl fun o _ => by rw [pow_two]
    rw [h1]
    exact MeasureTheory.integrable_finsetSum _ fun o _ => hint n o o
  have hintg : ∀ n, Integrable
      (fun ω => (∑ o : On n, u n ω o ^ 2) / (Fintype.card (On n) : ℝ)) P :=
    fun n => (hnum n).div_const _
  have hmean : ∀ n, ∫ ω, (∑ o : On n, u n ω o ^ 2) / (Fintype.card (On n) : ℝ) ∂P
      ≤ Mbar * Cvr + Csg := by
    intro n
    have hsum : ∫ ω, (∑ o : On n, u n ω o ^ 2) ∂P
        = ∑ o : On n, omegaU (c n) (dims n) (vr n) (sg n) o o := by
      have h1 : (fun ω => ∑ o : On n, u n ω o ^ 2)
          = fun ω => ∑ o : On n, u n ω o * u n ω o := by
        funext ω
        exact Finset.sum_congr rfl fun o _ => by rw [pow_two]
      rw [h1, MeasureTheory.integral_finsetSum (μ := P) (s := (Finset.univ : Finset (On n)))
        (f := fun o ω => u n ω o * u n ω o) (fun o _ => hint n o o)]
      exact Finset.sum_congr rfl fun o _ => hEu n o o
    rw [integral_div, hsum, div_le_iff₀ (hcard n)]
    have hterm : ∀ o : On n, omegaU (c n) (dims n) (vr n) (sg n) o o ≤ Mbar * Cvr + Csg := by
      intro o
      rw [omegaU_diag]
      have h1 : (∑ m ∈ dims n, vr n m ^ 2) ≤ ((dims n).card : ℝ) * Cvr := by
        calc (∑ m ∈ dims n, vr n m ^ 2) ≤ ∑ _m ∈ dims n, Cvr :=
              Finset.sum_le_sum fun m _ => hvr n m
          _ = ((dims n).card : ℝ) * Cvr := by rw [Finset.sum_const, nsmul_eq_mul]
      have h2 : ((dims n).card : ℝ) * Cvr ≤ Mbar * Cvr :=
        mul_le_mul_of_nonneg_right (hM n) hCvr
      linarith [hsg n o]
    calc (∑ o : On n, omegaU (c n) (dims n) (vr n) (sg n) o o)
        ≤ ∑ _o : On n, (Mbar * Cvr + Csg) := Finset.sum_le_sum fun o _ => hterm o
      _ = (Fintype.card (On n) : ℝ) * (Mbar * Cvr + Csg) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Mbar * Cvr + Csg) * (Fintype.card (On n) : ℝ) := by ring
  refine residSq_div_card_bddInProb (P := P) u v hcard hdom
    (fun n => (hintg n).aemeasurable)
    (C := ENNReal.ofReal (Mbar * Cvr + Csg)) ENNReal.ofReal_ne_top (fun n => ?_)
  have hnn : 0 ≤ᵐ[P] fun ω => (∑ o : On n, u n ω o ^ 2) / (Fintype.card (On n) : ℝ) :=
    Filter.Eventually.of_forall fun ω =>
      div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hcard n).le
  have hae : ∀ᵐ ω ∂P, ‖(∑ o : On n, u n ω o ^ 2) / (Fintype.card (On n) : ℝ)‖ₑ
      = ENNReal.ofReal ((∑ o : On n, u n ω o ^ 2) / (Fintype.card (On n) : ℝ)) := by
    filter_upwards with ω
    rw [Real.enorm_eq_ofReal
      (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hcard n).le)]
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal (hintg n) hnn]
  exact ENNReal.ofReal_le_ofReal (hmean n)

end ProjMoment

/-! ### §8g Clause (a) given Step 1 -/
section Chain

variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Dn On Ln : ℕ → Type*}
  [∀ n, Fintype (On n)] [∀ n, DecidableEq (On n)]
  [∀ n, DecidableEq (Dn n)] [∀ n, DecidableEq (Ln n)]
variable [Fintype K] [DecidableEq K]

/-- **Theorem 12(a)** given Step 1's conclusion `hstep1`, with `hproj`, `hresid` and `hscore`
supplied by `proj_bddInProb`, `residSq_bddInProb_of_omega` and `hscore_of_hstep1`. -/
theorem piinf_a_of_step1
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, Ω → On n → K → ℝ) (v u : ∀ n, Ω → On n → ℝ)
    (Pim : ∀ n, Matrix (On n) (On n) ℝ) (vr : ∀ n, Dn n → ℝ) (sg : ∀ n, On n → ℝ)
    {Ups : ℕ → Matrix K K ℝ} {a b G : ℕ → ℝ} {B R Cvr Csg Mbar Cb : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (hG : ∀ n, 1 ≤ G n)
    (hcard : ∀ n, 0 < (Fintype.card (On n) : ℝ))
    (hz : ∀ n, ∀ᵐ ω ∂P, ∀ o, vecSqNorm (z n ω o) ≤ B ^ 2)
    (hb : ∀ n, ∀ e ∈ Finset.powersetCard 2 (dims n), ∀ t ∈ cells (c n) e, (t.card : ℝ) ≤ b n)
    (hcell : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)), (t.card : ℝ) ≤ G n)
    (hrate4 : Tendsto (fun n => step4Rate B (a n) (Fintype.card (On n) : ℝ)
      (((Finset.powersetCard 2 (dims n)).card : ℝ)) (b n)) atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => step2Rate B (a n) ((dims n).card : ℝ) (G n)) atTop (𝓝 0))
    (hsym : ∀ n, (Pim n)ᵀ = Pim n) (hidem : ∀ n, Pim n * Pim n = Pim n)
    (htr : ∀ n, (Pim n).trace ≤ R) (hR : 0 ≤ R)
    (hw : ∀ n ω o, v n ω o - u n ω o = -((Pim n).mulVec (u n ω) o))
    (hint : ∀ n p q, Integrable (fun ω => u n ω p * u n ω q) P)
    (hEu : ∀ n p q, ∫ ω, u n ω p * u n ω q ∂P = omegaU (c n) (dims n) (vr n) (sg n) p q)
    (hvr : ∀ n m, vr n m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ n o, sg n o ^ 2 ≤ Csg) (hCsg : 0 ≤ Csg)
    (hM : ∀ n, ((dims n).card : ℝ) ≤ Mbar) (hMbar : 0 ≤ Mbar)
    (hmeas : ∀ n, AEMeasurable (fun ω =>
      frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n)) P)
    (hUps : ∀ n, |(Ups n).trace| ≤ Cb)
    (hstep1 : TendstoInMeasure P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n ω) (u n ω) - Ups n))
      atTop (fun _ => 0)) :
    TendstoInMeasure P
      (fun n ω => frobNorm (a n • ieMeat (c n) (dims n) (z n ω) (v n ω) - Ups n))
      atTop (fun _ => 0) :=
  piinf_a c dims z v u ha0 hb0 (fun n => lt_of_lt_of_le zero_lt_one (hG n)) hcard hz hb hcell
    (residSq_bddInProb_of_omega c dims u v Pim vr sg hsym hidem hw hint hEu hcard hvr hCvr
      hsg hM)
    hrate4
    (proj_bddInProb c dims u v Pim vr sg hsym hidem htr hR hw hint hEu hcell hG hvr hCvr
      hsg hCsg hM hMbar)
    hrate2
    (hscore_of_hstep1 c dims z u hmeas hUps hstep1) hstep1

end Chain

end Step1Inputs

/-! ### §8h Witness for `piinf_a_of_step1`

The growing design of §6b with `u ≡ 1`, `P_{C_1}` the projector on the first coordinate, and
`û = (0,1,…,1)`; `P` is a point mass. The quantity sent to zero is `n²/(n+1)³`. -/
section Step1Witness

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

/-- The witness projector on the first coordinate, of trace one. -/
noncomputable def seqPim (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then (1 : ℝ) else 0)

/-- The witness residual `û = u - P_{C_1}u = (0,1,…,1)` at `u ≡ 1`. -/
def seqResid1 (n : ℕ) : Fin (n + 1) → ℝ := fun o => if o = 0 then 0 else 1

/-- The witness category variances: `1` on the first dimension and `0` on the second. -/
def seqVr : Fin 2 → ℝ := fun m => if m = 0 then 1 else 0

/-- The witness idiosyncratic variances, all zero. -/
def seqSg (n : ℕ) : Fin (n + 1) → ℝ := fun _ => 0

theorem seqPim_transpose (n : ℕ) : (seqPim n)ᵀ = seqPim n := by
  rw [seqPim, Matrix.diagonal_transpose]

theorem seqPim_idem (n : ℕ) : seqPim n * seqPim n = seqPim n := by
  rw [seqPim, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = 0 <;> simp [h]

theorem seqPim_trace (n : ℕ) : (seqPim n).trace = 1 := by
  rw [seqPim, Matrix.trace_diagonal]
  simp

theorem seqPim_mulVec (n : ℕ) (o : Fin (n + 1)) :
    (seqPim n).mulVec (seqResid n) o = if o = 0 then (1 : ℝ) else 0 := by
  rw [seqPim, Matrix.mulVec_diagonal]
  by_cases h : o = 0 <;> simp [h, seqResid]

theorem seq_hw (n : ℕ) (o : Fin (n + 1)) :
    seqResid1 n o - seqResid n o = -((seqPim n).mulVec (seqResid n) o) := by
  rw [seqPim_mulVec]
  by_cases h : o = 0 <;> simp [h, seqResid1, seqResid]

/-- On the witness model `Ω_u ≡ 1`. -/
theorem seq_omegaU (n : ℕ) (p q : Fin (n + 1)) :
    omegaU (seqIndex n) (Finset.univ : Finset (Fin 2)) seqVr (seqSg n) p q = 1 := by
  simp [omegaU, seqIndex, seqVr, seqSg]

theorem seq_sum_resid1 (n : ℕ) : ∑ o : Fin (n + 1), seqResid1 n o = (n : ℝ) := by
  have h1 : ∀ o : Fin (n + 1), seqResid1 n o = 1 - (if o = 0 then (1 : ℝ) else 0) := by
    intro o
    by_cases h : o = 0 <;> simp [h, seqResid1]
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => h1 o, Finset.sum_sub_distrib]
  simp

/-- On the witness model `‖P_{C_1}u‖² = 1`. -/
theorem seq_projSq (n : ℕ) :
    ∑ o : Fin (n + 1), (seqResid1 n o - seqResid n o) ^ 2 = 1 := by
  have h1 : ∀ o : Fin (n + 1), (seqResid1 n o - seqResid n o) ^ 2
      = (if o = 0 then (1 : ℝ) else 0) := by
    intro o
    by_cases h : o = 0 <;> simp [h, seqResid1, seqResid]
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => h1 o]
  simp

/-- On the witness model `‖û‖² = n`. -/
theorem seq_residSq1 (n : ℕ) : ∑ o : Fin (n + 1), seqResid1 n o ^ 2 = (n : ℝ) := by
  have h1 : ∀ o : Fin (n + 1), seqResid1 n o ^ 2 = seqResid1 n o := by
    intro o
    by_cases h : o = 0 <;> simp [h, seqResid1]
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => h1 o, seq_sum_resid1]

/-- On the witness model `‖(n²/N_*)Υ̂(û)‖_F = n²`. -/
theorem seq_ieMeat1_frobNorm (n : ℕ) :
    frobNorm (ieMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid1 n))
      = (n : ℝ) ^ 2 := by
  have hw : ∀ o o' : Fin (n + 1),
      (if Linked (seqIndex n) (Finset.univ : Finset (Fin 2)) o o' then (1 : ℝ) else 0) = 1 :=
    fun o o' => by
      have h : Linked (seqIndex n) (Finset.univ : Finset (Fin 2)) o o' :=
        ⟨0, Finset.mem_univ 0, rfl⟩
      simp [h]
  have hentry : ieMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n)
      (seqResid1 n) 0 0 = (n : ℝ) ^ 2 := by
    rw [ieMeat_eq_pairForm]
    simp only [pairForm, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, hw, seqScore, mul_one, one_mul]
    have hsq : ∑ o : Fin (n + 1), ∑ o' : Fin (n + 1), seqResid1 n o * seqResid1 n o'
        = (∑ o : Fin (n + 1), seqResid1 n o) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
    rw [hsq, seq_sum_resid1]
  simp only [frobNorm, frobSq, Fin.sum_univ_one, hentry]
  exact Real.sqrt_sq (by positivity)

/-- `hstep1` on the witness model, where the quantity sent to zero is `2/(n+1)`. -/
theorem seq_hstep1_one :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => frobNorm ((((n : ℝ) + 1) ^ 3)⁻¹ •
        dimMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid n)
        - (0 : Matrix (Fin 1) (Fin 1) ℝ))) atTop (fun _ => (0 : ℝ)) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using hbase.const_mul 2
  refine Sequence.tendstoInProb_zero_of_abs_le_const
    (b := fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹)
    (fun n => Filter.Eventually.of_forall fun ω => ?_) h2
  rw [sub_zero, frobNorm_smul, seq_dimMeat_frobNorm]
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((n : ℝ) + 1) ^ 3)⁻¹)]
  rw [abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (((n : ℝ) + 1) ^ 3)⁻¹ * (2 * ((n : ℝ) + 1) ^ 2))]
  have heq : (((n : ℝ) + 1) ^ 3)⁻¹ * (2 * ((n : ℝ) + 1) ^ 2) = 2 * ((n : ℝ) + 1)⁻¹ := by
    field_simp
  rw [heq]

/-- `piinf_a_of_step1` on the witness family, where the sequence is `n²/(n+1)³`. -/
theorem piinf_a_of_step1_witness :
    TendstoInMeasure (Measure.dirac (0 : ℝ))
      (fun (n : ℕ) (_ : ℝ) => frobNorm ((((n : ℝ) + 1) ^ 3)⁻¹ •
          ieMeat (seqIndex n) (Finset.univ : Finset (Fin 2)) (seqScore n) (seqResid1 n)
        - (0 : Matrix (Fin 1) (Fin 1) ℝ))) atTop (fun _ => (0 : ℝ)) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine piinf_a_of_step1 (P := Measure.dirac (0 : ℝ)) (K := Fin 1)
    (Dn := fun _ => Fin 2) (On := fun n => Fin (n + 1)) (Ln := fun _ => Fin 1)
    (fun n => seqIndex n) (fun _ => Finset.univ) (fun n _ => seqScore n)
    (fun n _ => seqResid1 n) (fun n _ => seqResid n) (fun n => seqPim n)
    (fun _ => seqVr) (fun n => seqSg n)
    (Ups := fun _ => 0) (a := fun n => (((n : ℝ) + 1) ^ 3)⁻¹)
    (b := fun n => (Fintype.card (Fin (n + 1)) : ℝ))
    (G := fun n => (Fintype.card (Fin (n + 1)) : ℝ)) (B := 1) (R := 1)
    (Cvr := 1) (Csg := 0) (Mbar := 2) (Cb := 0)
    (fun _ => by positivity) (fun n => by rw [seq_card]; positivity)
    (fun n => by rw [seq_card]; linarith [Nat.cast_nonneg (α := ℝ) n])
    (fun n => by rw [seq_card]; positivity)
    (fun _ => Filter.Eventually.of_forall fun _ _ => by simp [vecSqNorm, seqScore])
    (fun n e _ t _ => by exact_mod_cast Finset.card_le_univ t)
    (fun n m _ t _ => by exact_mod_cast Finset.card_le_univ t)
    ?_ ?_ seqPim_transpose seqPim_idem (fun n => le_of_eq (seqPim_trace n)) zero_le_one
    (fun n _ o => seq_hw n o) (fun n p q => integrable_const _)
    (fun n p q => ?_)
    (fun n m => by by_cases h : m = 0 <;> simp [seqVr, h]) zero_le_one
    (fun n o => by simp [seqSg]) le_rfl
    (fun n => by simp) (by norm_num)
    (fun n => aemeasurable_const) (fun n => by simp)
    seq_hstep1_one
  · refine hbase.congr fun n => ?_
    have hp : ((Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))).card : ℝ) = 1 := by
      simp [Finset.card_powersetCard]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [step4Rate, seq_card, hp]
    field_simp
  · have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using hbase.const_mul 2
    refine h2.congr fun n => ?_
    have hc2 : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [step2Rate, seq_card, hc2]
    field_simp
  · rw [seq_omegaU]
    simp [seqResid]

end Step1Witness

/-! ## §9 Step 1

`step1_tendstoInProb` proves `hstep1` under the Regime-1 model of Theorem 6: `u = ∑_{m'}Δ_{m'}η̆^{(m')} + ε`,
with the category effects and the idiosyncratic disturbances forming a centred independent array
with variances `ς²_{m'}` and `σ²_ε(o)` and bounded fourth moments. `piinf_a_of_regime1` is
clause (a) with `hstep1` supplied.

Writing `Υ̂^dim(u) - Υ_n = (Lead - Υ_n) + Cross + Rem` with
`Lead := ∑_{m,j} z^{(m)}_jz^{(m)′}_jη̆^{(m)2}_j` and `Rem := ∑_{m,j}r^{(m)}_jr^{(m)′}_j`, in every
realization (`frobNorm_r1_decomp_le`)
`‖a_n•Υ̂^dim(u) - a_n•Υ_n‖_F ≤ ‖a_n•Lead - a_n•Υ_n‖_F + a_nS_R + 2√((a_nS_R)(a_nS_L))`.
The leading term is controlled by its second moment (`integral_frobSq_r1Lead_le`), the remainder
by its first (`integral_r1RemSum_le`), and `a_nS_L` has mean `a_n tr(Υ_n)` (`integral_r1LeadSum`).

The disturbance array is indexed by `(D × Finset O) ⊕ O`: a site `Sum.inl (m, t)` for each
category effect, with the category represented by its level-`{m}` cell `t`, and a site `Sum.inr o`
for each `ε_o`. The cross-level aggregates are bounded through `sum_cells_inter`: the
level-`A ∪ A'` cells are exactly the nonempty intersections of a level-`A` cell with a level-`A'`
cell. -/
section CellsPair
open Finset

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- The cell of `o` at a union of levels is the intersection of its cells at each. -/
theorem cellOf_union (c : D → O → L) (A A' : Finset D) (o : O) :
    cellOf c (A ∪ A') o = cellOf c A o ∩ cellOf c A' o := by
  ext o'
  simp only [Finset.mem_inter, mem_cellOf, SameOn]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Finset.mem_union_left _ hj),
      fun j hj => h j (Finset.mem_union_right _ hj)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Finset.mem_union.1 hj with hj' | hj'
    · exact h1 j hj'
    · exact h2 j hj'

/-- A member of a cell determines it. -/
theorem eq_cellOf_of_mem {c : D → O → L} {A : Finset D} {t : Finset O} (ht : t ∈ cells c A)
    {o : O} (ho : o ∈ t) : t = cellOf c A o := by
  obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 ht
  exact (cellOf_eq_iff.2 (by simpa using ho)).symm

/-- A nonempty intersection of a level-`A` cell with a level-`A'` cell is a level-`A ∪ A'`
cell. -/
theorem inter_mem_cells_union {c : D → O → L} {A A' : Finset D} {t t' : Finset O}
    (ht : t ∈ cells c A) (ht' : t' ∈ cells c A') {o : O} (ho : o ∈ t ∩ t') :
    t ∩ t' ∈ cells c (A ∪ A') := by
  obtain ⟨ho1, ho2⟩ := Finset.mem_inter.1 ho
  rw [eq_cellOf_of_mem ht ho1, eq_cellOf_of_mem ht' ho2, ← cellOf_union]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ o)

/-- The level-`A ∪ A'` cells are exactly the nonempty intersections of a level-`A` cell with a
level-`A'` cell, one to one; hence summing a function that vanishes on `∅` over pairs of cells
equals summing it over the cells of the joint level. -/
theorem sum_cells_inter (c : D -> O -> L) (A A' : Finset D) (f : Finset O -> ℝ)
    (hf : f (EmptyCollection.emptyCollection) = 0) :
    (Finset.sum (cells c A) (fun t => Finset.sum (cells c A') (fun t' => f (t ∩ t'))))
      = Finset.sum (cells c (A ∪ A')) f := by
  classical
  set PHI : O -> Finset O × Finset O := fun o => (cellOf c A o, cellOf c A' o) with hPHI
  set PSI : Finset O × Finset O -> Finset O := fun p => p.1 ∩ p.2 with hPSI
  have hsub : Finset.image PHI Finset.univ ⊆ (cells c A) ×ˢ (cells c A') := by
    intro p hp
    obtain ⟨o, -, rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ o),
      Finset.mem_image_of_mem _ (Finset.mem_univ o)⟩
  have hzero : ∀ p ∈ (cells c A) ×ˢ (cells c A'),
      p ∉ Finset.image PHI Finset.univ -> f (PSI p) = 0 := by
    intro p hp hnp
    have hpe : PSI p = EmptyCollection.emptyCollection := by
      by_contra hne
      obtain ⟨o, ho⟩ := Finset.nonempty_iff_ne_empty.2 hne
      obtain ⟨ho1, ho2⟩ := Finset.mem_inter.1 ho
      refine hnp (Finset.mem_image.2 ⟨o, Finset.mem_univ o, ?_⟩)
      have h1 : p.1 = cellOf c A o := eq_cellOf_of_mem (Finset.mem_product.1 hp).1 ho1
      have h2 : p.2 = cellOf c A' o := eq_cellOf_of_mem (Finset.mem_product.1 hp).2 ho2
      exact Prod.ext h1.symm h2.symm
    rw [hpe, hf]
  have hinj : ∀ p ∈ Finset.image PHI Finset.univ, ∀ q ∈ Finset.image PHI Finset.univ,
      PSI p = PSI q -> p = q := by
    intro p hp q hq hpq
    obtain ⟨o, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨o', -, rfl⟩ := Finset.mem_image.1 hq
    have h : cellOf c (A ∪ A') o = cellOf c (A ∪ A') o' := by
      rw [cellOf_union, cellOf_union]; exact hpq
    have hs : SameOn c (A ∪ A') o o' := cellOf_eq_iff.1 h
    have hA : cellOf c A o = cellOf c A o' :=
      cellOf_eq_iff.2 (fun j hj => hs j (Finset.mem_union_left _ hj))
    have hA' : cellOf c A' o = cellOf c A' o' :=
      cellOf_eq_iff.2 (fun j hj => hs j (Finset.mem_union_right _ hj))
    exact Prod.ext hA hA'
  have hprod : (Finset.sum (cells c A) (fun t => Finset.sum (cells c A') (fun t' => f (t ∩ t'))))
      = Finset.sum ((cells c A) ×ˢ (cells c A')) (fun p => f (PSI p)) := by
    rw [Finset.sum_product]
  rw [hprod, ← Finset.sum_subset hsub hzero, ← Finset.sum_image hinj]
  congr 1
  rw [Finset.image_image]
  refine Finset.image_congr ?_
  intro o _
  simp only [hPSI, hPHI, Function.comp_apply]
  exact (cellOf_union c A A' o).symm

end CellsPair

section Regime1
open Finset

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- The bound `∑_{j,j'}‖ζ^{(mm')}_{jj'}‖² ≤ B²c^{(2)}_max n` over the pair of levels
`({m},{m'})`. -/
theorem step1_zeta_pair_bound [Fintype K] [DecidableEq K]
    (c : D → O → L) (A A' : Finset D) (z : O → K → ℝ) {B b : ℝ}
    (hz : ∀ o, vecSqNorm (z o) ≤ B ^ 2) (hb0 : 0 ≤ b)
    (hb : ∀ t ∈ cells c (A ∪ A'), (t.card : ℝ) ≤ b) :
    ∑ t ∈ cells c A, ∑ t' ∈ cells c A', vecSqNorm (cellVec z (t ∩ t'))
      ≤ b * ((Fintype.card O : ℝ) * B ^ 2) := by
  have hf : vecSqNorm (cellVec z (∅ : Finset O)) = 0 := by
    simp [vecSqNorm, cellVec]
  rw [sum_cells_inter c A A' (fun s => vecSqNorm (cellVec z s)) hf]
  exact step1_zeta_bound c (A ∪ A') z hz hb0 hb

/-- Each observation of `t` lies in exactly one level-`A'` cell, so the intersections of `t`
with the level-`A'` cells partition `t`. -/
theorem sum_inter_cells (c : D → O → L) (A' : Finset D) (t : Finset O) (h : O → ℝ) :
    ∑ t' ∈ cells c A', ∑ o ∈ t ∩ t', h o = ∑ o ∈ t, h o := by
  classical
  have hstep : ∀ t' : Finset O, ∑ o ∈ t ∩ t', h o
      = ∑ o ∈ t', (if o ∈ t then h o else 0) := by
    intro t'
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun t' _ => hstep t',
    sum_over_cells c A' (fun o => if o ∈ t then h o else 0)]
  simp [Finset.sum_ite_mem]

/-- The sites carrying a Regime-1 remainder: the category effects of the dimensions in `E`, and
the idiosyncratic disturbances of the observations in `t`. -/
def r1Sites (c : D → O → L) (E : Finset D) (t : Finset O) : Finset ((D × Finset O) ⊕ O) :=
  (E.biUnion fun m' => (cells c ({m'} : Finset D)).image (Prod.mk m')).disjSum t

/-- A sum over `r1Sites` written out. -/
theorem sum_r1Sites (c : D → O → L) (E : Finset D) (t : Finset O)
    (F : ((D × Finset O) ⊕ O) → ℝ) :
    ∑ i ∈ r1Sites c E t, F i
      = (∑ m' ∈ E, ∑ t' ∈ cells c ({m'} : Finset D), F (Sum.inl (m', t')))
        + ∑ o ∈ t, F (Sum.inr o) := by
  classical
  rw [r1Sites, Finset.sum_disjSum]
  congr 1
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun m' _ => ?_
    refine Finset.sum_image ?_
    intro x _ y _ hxy
    exact (Prod.mk.injEq m' x m' y ▸ hxy).2
  · intro m₁ _ m₂ _ hne
    refine Finset.disjoint_left.2 ?_
    intro p hp1 hp2
    obtain ⟨t₁, -, rfl⟩ := Finset.mem_image.1 hp1
    obtain ⟨t₂, -, h2⟩ := Finset.mem_image.1 hp2
    exact hne ((Prod.mk.injEq m₂ t₂ m₁ t₁ ▸ h2).1).symm

end Regime1

section Regime1b
open Finset

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]

/-- The Regime-1 disturbance in a single realization,
`u_o = ∑_{m ∈ dims} η̆^{(m)}_{j_m(o)} + ε_o`. -/
def r1Dist (c : D → O → L) (dims : Finset D) (X : ((D × Finset O) ⊕ O) → ℝ) (o : O) : ℝ :=
  (∑ m ∈ dims, X (Sum.inl (m, cellOf c ({m} : Finset D) o))) + X (Sum.inr o)

/-- The coefficients of `r^{(m)}_t` in coordinate `k`: `ζ^{(mm')}_{tt'} = ∑_{o ∈ t ∩ t'} z̃_o`
at a category site, and `z̃_o` at an observation site. -/
def r1Coef (z : O → K → ℝ) (t : Finset O) (k : K) : ((D × Finset O) ⊕ O) → ℝ :=
  Sum.elim (fun p => cellVec z (t ∩ p.2) k) (fun o => z o k)

/-- The remainder `r^{(m)}_t`, as a linear form in the disturbance array. -/
def r1Rem (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (m : D) (t : Finset O)
    (X : ((D × Finset O) ⊕ O) → ℝ) : K → ℝ :=
  fun k => ∑ i ∈ r1Sites c (dims.erase m) t, r1Coef z t k i * X i

omit [Fintype K] [DecidableEq K] in
/-- Step 1's decomposition `g^{(m)}_j = z^{(m)}_jη̆^{(m)}_j + r^{(m)}_j`. -/
theorem cellScore_r1Dist (c : D -> O -> L) (dims : Finset D) (z : O -> K -> ℝ)
    (X : ((D × Finset O) ⊕ O) -> ℝ) {m : D} (hm : m ∈ dims) {t : Finset O}
    (ht : t ∈ cells c ({m} : Finset D)) :
    cellScore z (r1Dist c dims X) t
      = fun k => cellVec z t k * X (Sum.inl (m, t)) + r1Rem c dims z m t X k := by
  classical
  funext k
  have hexp : ∑ o ∈ t, z o k * r1Dist c dims X o
      = (∑ o ∈ t, ∑ m' ∈ dims, z o k * X (Sum.inl (m', cellOf c ({m'} : Finset D) o)))
        + ∑ o ∈ t, z o k * X (Sum.inr o) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun o _ => by rw [r1Dist, mul_add, Finset.mul_sum]
  have key1 : ∑ o ∈ t, z o k * X (Sum.inl (m, cellOf c ({m} : Finset D) o))
      = cellVec z t k * X (Sum.inl (m, t)) := by
    have hc : ∀ o ∈ t, z o k * X (Sum.inl (m, cellOf c ({m} : Finset D) o))
        = z o k * X (Sum.inl (m, t)) := by
      intro o ho
      rw [← eq_cellOf_of_mem ht ho]
    rw [Finset.sum_congr rfl hc, ← Finset.sum_mul]
    rfl
  have key2 : ∀ m' : D, ∑ o ∈ t, z o k * X (Sum.inl (m', cellOf c ({m'} : Finset D) o))
      = ∑ t' ∈ cells c ({m'} : Finset D), cellVec z (t ∩ t') k * X (Sum.inl (m', t')) := by
    intro m'
    rw [← sum_inter_cells c ({m'} : Finset D) t
      (fun o => z o k * X (Sum.inl (m', cellOf c ({m'} : Finset D) o)))]
    refine Finset.sum_congr rfl fun t' ht' => ?_
    have hin : ∀ o ∈ t ∩ t', z o k * X (Sum.inl (m', cellOf c ({m'} : Finset D) o))
        = z o k * X (Sum.inl (m', t')) := by
      intro o ho
      rw [← eq_cellOf_of_mem ht' (Finset.mem_inter.1 ho).2]
    rw [Finset.sum_congr rfl hin, ← Finset.sum_mul]
    rfl
  have hsplit : ∑ m' ∈ dims, (∑ o ∈ t, z o k * X (Sum.inl (m', cellOf c ({m'} : Finset D) o)))
      = (∑ o ∈ t, z o k * X (Sum.inl (m, cellOf c ({m} : Finset D) o)))
        + ∑ m' ∈ dims.erase m, ∑ o ∈ t, z o k * X (Sum.inl (m', cellOf c ({m'} : Finset D) o)) :=
    (Finset.add_sum_erase dims _ hm).symm
  have hrem : r1Rem c dims z m t X k
      = (∑ m' ∈ dims.erase m, ∑ t' ∈ cells c ({m'} : Finset D),
          cellVec z (t ∩ t') k * X (Sum.inl (m', t'))) + ∑ o ∈ t, z o k * X (Sum.inr o) := by
    rw [r1Rem, sum_r1Sites]
    simp only [r1Coef, Sum.elim_inl, Sum.elim_inr]
  show ∑ o ∈ t, z o k * r1Dist c dims X o = _
  rw [hexp, Finset.sum_comm, hsplit, key1, hrem,
    Finset.sum_congr rfl (fun m' (_ : m' ∈ dims.erase m) => key2 m')]
  ring

end Regime1b

section IndepMoments
open Finset MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Orthogonality of independent summands. -/
theorem variance_sum_of_iIndepFun {ι : Type*} (X : ι → Ω → ℝ) (hX : iIndepFun X P)
    (g : ι → ℝ → ℝ) (hg : ∀ i, Measurable (g i)) (s : Finset ι)
    (hmem : ∀ i ∈ s, MemLp (fun ω => g i (X i ω)) 2 P) :
    variance (fun ω => ∑ i ∈ s, g i (X i ω)) P
      = ∑ i ∈ s, variance (fun ω => g i (X i ω)) P := by
  have hpair : (s : Set ι).Pairwise fun i j =>
      IndepFun (fun ω => g i (X i ω)) (fun ω => g j (X j ω)) P :=
    fun i _ j _ hij => (hX.indepFun hij).comp (hg i) (hg j)
  have h := ProbabilityTheory.IndepFun.variance_sum (X := fun i ω => g i (X i ω)) hmem hpair
  have hfun : (∑ i ∈ s, fun ω => g i (X i ω)) = fun ω => ∑ i ∈ s, g i (X i ω) := by
    funext ω
    simp [Finset.sum_apply]
  rw [← hfun]
  exact h

/-- The second moment of a linear form in an independent centred array. -/
theorem integral_sq_linear_indep {ι : Type*} (X : ι → Ω → ℝ) (hX : iIndepFun X P)
    (hmem : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (s : Finset ι) (coef : ι → ℝ) :
    ∫ ω, (∑ i ∈ s, coef i * X i ω) ^ 2 ∂P = ∑ i ∈ s, coef i ^ 2 * ∫ ω, (X i ω) ^ 2 ∂P := by
  have hmemc : ∀ i, MemLp (fun ω => coef i * X i ω) 2 P := fun i => (hmem i).const_mul _
  have hZmem : MemLp (fun ω => ∑ i ∈ s, coef i * X i ω) 2 P :=
    memLp_finsetSum s fun i _ => hmemc i
  have hZmean : ∫ ω, (∑ i ∈ s, coef i * X i ω) ∂P = 0 := by
    rw [integral_finsetSum _ fun i _ => ((hmemc i).integrable one_le_two)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, hmean i, mul_zero]
  rw [← variance_of_integral_eq_zero hZmem.aemeasurable hZmean,
    variance_sum_of_iIndepFun X hX (fun i x => coef i * x)
      (fun i => measurable_const.mul measurable_id) s (fun i _ => hmemc i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [variance_const_mul, variance_of_integral_eq_zero (hmem i).aemeasurable (hmean i)]

/-- The second moment of the centred sum of squares of an independent array. -/
theorem integral_sq_sub_sq_indep {ι : Type*} (X : ι → Ω → ℝ) (hX : iIndepFun X P)
    (s : Finset ι) (coef : ι → ℝ)
    (hmem : ∀ i ∈ s, MemLp (fun ω => (X i ω) ^ 2) 2 P) :
    ∫ ω, (∑ i ∈ s, coef i * (X i ω) ^ 2 - ∑ i ∈ s, coef i * ∫ x, (X i x) ^ 2 ∂P) ^ 2 ∂P
      ≤ ∑ i ∈ s, coef i ^ 2 * ∫ ω, (X i ω) ^ 4 ∂P := by
  have hmemc : ∀ i ∈ s, MemLp (fun ω => coef i * (X i ω) ^ 2) 2 P :=
    fun i hi => (hmem i hi).const_mul _
  have hYmem : MemLp (fun ω => ∑ i ∈ s, coef i * (X i ω) ^ 2) 2 P :=
    memLp_finsetSum s hmemc
  have hYmean : ∫ ω, (∑ i ∈ s, coef i * (X i ω) ^ 2) ∂P
      = ∑ i ∈ s, coef i * ∫ x, (X i x) ^ 2 ∂P := by
    rw [integral_finsetSum _ fun i hi => ((hmemc i hi).integrable one_le_two)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hvar : ∫ ω, (∑ i ∈ s, coef i * (X i ω) ^ 2
        - ∑ i ∈ s, coef i * ∫ x, (X i x) ^ 2 ∂P) ^ 2 ∂P
      = variance (fun ω => ∑ i ∈ s, coef i * (X i ω) ^ 2) P := by
    rw [variance_eq_integral hYmem.aemeasurable, hYmean]
  rw [hvar, variance_sum_of_iIndepFun X hX (fun i x => coef i * x ^ 2)
    (fun i => measurable_const.mul (measurable_id.pow_const 2)) s hmemc]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [variance_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hle : variance (fun ω => (X i ω) ^ 2) P ≤ ∫ ω, ((X i ω) ^ 2) ^ 2 ∂P := by
    rw [variance_eq_sub (hmem i hi)]
    have : (0 : ℝ) ≤ (∫ ω, (X i ω) ^ 2 ∂P) ^ 2 := sq_nonneg _
    simp only [Pi.pow_apply]
    linarith
  calc variance (fun ω => (X i ω) ^ 2) P ≤ ∫ ω, ((X i ω) ^ 2) ^ 2 ∂P := hle
    _ = ∫ ω, (X i ω) ^ 4 ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        ring

end IndepMoments

section OuterSub
open Finset

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]

/-- The cell-by-cell bound for `FF' - LL' = RR' + RL' + LR'`, at a general pair of cell
arrays `F` and `L` with `R = F - L`. -/
theorem frobNorm_sum_outer_sub_le (c : D → O → L) (dims : Finset D)
    (F Lv : D → Finset O → K → ℝ) :
    frobNorm (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
        (Matrix.vecMulVec (F m t) (F m t) - Matrix.vecMulVec (Lv m t) (Lv m t)))
      ≤ (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            vecSqNorm (fun k => F m t k - Lv m t k))
        + 2 * Real.sqrt
            ((∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
                vecSqNorm (fun k => F m t k - Lv m t k))
              * ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D), vecSqNorm (Lv m t)) := by
  classical
  have hFdnn : ∀ (m : D) (t : Finset O), 0 ≤ vecSqNorm (fun k => F m t k - Lv m t k) :=
    fun _ _ => vecSqNorm_nonneg _
  have hFgnn : ∀ (m : D) (t : Finset O), 0 ≤ vecSqNorm (Lv m t) := fun _ _ => vecSqNorm_nonneg _
  have hmat : ∀ (m : D) (t : Finset O),
      Matrix.vecMulVec (F m t) (F m t) - Matrix.vecMulVec (Lv m t) (Lv m t)
        = Matrix.vecMulVec (fun k => F m t k - Lv m t k) (fun k => F m t k - Lv m t k)
          + Matrix.vecMulVec (fun k => F m t k - Lv m t k) (Lv m t)
          + Matrix.vecMulVec (Lv m t) (fun k => F m t k - Lv m t k) := by
    intro m t
    ext p q
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
    ring
  have hterm : ∀ (m : D) (t : Finset O),
      frobNorm (Matrix.vecMulVec (F m t) (F m t) - Matrix.vecMulVec (Lv m t) (Lv m t))
        ≤ vecSqNorm (fun k => F m t k - Lv m t k)
          + 2 * (Real.sqrt (vecSqNorm (fun k => F m t k - Lv m t k))
              * Real.sqrt (vecSqNorm (Lv m t))) := by
    intro m t
    rw [hmat m t]
    exact frobNorm_outer_three_le (fun k => F m t k - Lv m t k) (Lv m t)
  have hcs : ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
        (Real.sqrt (vecSqNorm (fun k => F m t k - Lv m t k))
          * Real.sqrt (vecSqNorm (Lv m t)))
      ≤ Real.sqrt (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            vecSqNorm (fun k => F m t k - Lv m t k))
        * Real.sqrt (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D), vecSqNorm (Lv m t)) := by
    refine (Finset.sum_le_sum fun m _ =>
      Real.sum_sqrt_mul_sqrt_le _ (fun t => hFdnn m t) (fun t => hFgnn m t)).trans ?_
    exact Real.sum_sqrt_mul_sqrt_le _
      (fun m => Finset.sum_nonneg fun t _ => hFdnn m t)
      (fun m => Finset.sum_nonneg fun t _ => hFgnn m t)
  have hsplit : ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
        (vecSqNorm (fun k => F m t k - Lv m t k)
          + 2 * (Real.sqrt (vecSqNorm (fun k => F m t k - Lv m t k))
              * Real.sqrt (vecSqNorm (Lv m t))))
      = (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            vecSqNorm (fun k => F m t k - Lv m t k))
        + 2 * ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            (Real.sqrt (vecSqNorm (fun k => F m t k - Lv m t k))
              * Real.sqrt (vecSqNorm (Lv m t))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hSdnn : (0 : ℝ) ≤ ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
      vecSqNorm (fun k => F m t k - Lv m t k) :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun t _ => hFdnn m t
  refine le_trans (frobNorm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun m _ =>
    (frobNorm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => hterm m t)) ?_
  rw [hsplit, Real.sqrt_mul hSdnn]
  linarith [hcs]

end OuterSub

section LeadDef
open Finset

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]

/-- The leading vector of Step 1, `z^{(m)}_j η̆^{(m)}_j`. -/
def r1LeadVec (z : O → K → ℝ) (m : D) (t : Finset O) (X : ((D × Finset O) ⊕ O) → ℝ) : K → ℝ :=
  fun k => cellVec z t k * X (Sum.inl (m, t))

/-- `∑_{m,j} z^{(m)}_j z^{(m)′}_j η̆^{(m)2}_j`, the leading part of `Υ̂^dim(u)`. -/
noncomputable def r1Lead (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → ℝ) : Matrix K K ℝ :=
  ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
    Matrix.vecMulVec (r1LeadVec z m t X) (r1LeadVec z m t X)

/-- `∑_{m,j}‖r^{(m)}_j‖²`. -/
noncomputable def r1RemSum (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → ℝ) : ℝ :=
  ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D), vecSqNorm (r1Rem c dims z m t X)

/-- `∑_{m,j}‖z^{(m)}_j η̆^{(m)}_j‖²`. -/
noncomputable def r1LeadSum (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → ℝ) : ℝ :=
  ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
    vecSqNorm (cellVec z t) * X (Sum.inl (m, t)) ^ 2

theorem r1RemSum_nonneg (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → ℝ) : 0 ≤ r1RemSum c dims z X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => vecSqNorm_nonneg _

theorem r1LeadSum_nonneg (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → ℝ) : 0 ≤ r1LeadSum c dims z X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (vecSqNorm_nonneg _) (sq_nonneg _)

/-- Step 1's deterministic decomposition bound. -/
theorem frobNorm_r1_decomp_le (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (vr : D → ℝ)
    (X : ((D × Finset O) ⊕ O) → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    frobNorm (a • dimMeat c dims z (r1Dist c dims X) - a • upsilonN c dims z vr)
      ≤ frobNorm (a • r1Lead c dims z X - a • upsilonN c dims z vr)
        + (a * r1RemSum c dims z X
           + 2 * Real.sqrt ((a * r1RemSum c dims z X) * (a * r1LeadSum c dims z X))) := by
  classical
  have halg : a • dimMeat c dims z (r1Dist c dims X) - a • upsilonN c dims z vr
      = (a • r1Lead c dims z X - a • upsilonN c dims z vr)
        + a • (dimMeat c dims z (r1Dist c dims X) - r1Lead c dims z X) := by
    rw [smul_sub]
    abel
  have hdiff : dimMeat c dims z (r1Dist c dims X) - r1Lead c dims z X
      = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
          (Matrix.vecMulVec (cellScore z (r1Dist c dims X) t)
              (cellScore z (r1Dist c dims X) t)
            - Matrix.vecMulVec (r1LeadVec z m t X) (r1LeadVec z m t X)) := by
    rw [dimMeat, r1Lead, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_sub_distrib]
  have hbase := frobNorm_sum_outer_sub_le c dims
    (fun m t => cellScore z (r1Dist c dims X) t) (fun m t => r1LeadVec z m t X)
  have hrem : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D),
      vecSqNorm (fun k => cellScore z (r1Dist c dims X) t k - r1LeadVec z m t X k)
        = vecSqNorm (r1Rem c dims z m t X) := by
    intro m hm t ht
    have h := congrFun (cellScore_r1Dist c dims z X hm ht)
    refine congrArg vecSqNorm ?_
    funext k
    rw [h k, r1LeadVec]
    ring
  have hRS : (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
      vecSqNorm (fun k => cellScore z (r1Dist c dims X) t k - r1LeadVec z m t X k))
      = r1RemSum c dims z X :=
    Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun t ht => hrem m hm t ht
  have hLS : (∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
      vecSqNorm (r1LeadVec z m t X)) = r1LeadSum c dims z X := by
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun t _ => ?_
    exact vecSqNorm_mul_right (X (Sum.inl (m, t))) (cellVec z t)
  rw [hRS, hLS] at hbase
  have hsqrt : Real.sqrt ((a * r1RemSum c dims z X) * (a * r1LeadSum c dims z X))
      = a * Real.sqrt (r1RemSum c dims z X * r1LeadSum c dims z X) := by
    have h : (a * r1RemSum c dims z X) * (a * r1LeadSum c dims z X)
        = a ^ 2 * (r1RemSum c dims z X * r1LeadSum c dims z X) := by ring
    rw [h, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  rw [halg]
  refine (frobNorm_add_le _ _).trans (add_le_add (le_refl _) ?_)
  rw [frobNorm_smul, abs_of_nonneg ha, hsqrt, hdiff]
  refine le_trans (mul_le_mul_of_nonneg_left hbase ha) (le_of_eq ?_)
  ring

end LeadDef

section R1Moments
open Finset MeasureTheory ProbabilityTheory

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]
variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `‖r^{(m)}_j‖²` is integrable, being a finite sum of squares of `L²` linear forms. -/
theorem integrable_vecSqNorm_r1Rem (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hmem : ∀ i, MemLp (X i) 2 P) (m : D) (t : Finset O) :
    Integrable (fun ω => vecSqNorm (r1Rem c dims z m t (fun i => X i ω))) P := by
  have hterm : ∀ k : K, Integrable
      (fun ω => (∑ i ∈ r1Sites c (dims.erase m) t, r1Coef z t k i * X i ω) ^ 2) P := by
    intro k
    exact MemLp.integrable_sq
      (memLp_finsetSum _ fun i _ => (hmem i).const_mul (r1Coef z t k i))
  exact integrable_finset_sum _ fun k _ => hterm k

/-- `E‖r^{(m)}_j‖²`, the trace of `E[r^{(m)}_jr^{(m)′}_j]`. -/
theorem integral_vecSqNorm_r1Rem (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hX : iIndepFun X P) (hmem : ∀ i, MemLp (X i) 2 P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (m : D) (t : Finset O) :
    ∫ ω, vecSqNorm (r1Rem c dims z m t (fun i => X i ω)) ∂P
      = (∑ m' ∈ dims.erase m, ∑ t' ∈ cells c ({m'} : Finset D),
            vecSqNorm (cellVec z (t ∩ t')) * ∫ ω, (X (Sum.inl (m', t')) ω) ^ 2 ∂P)
        + ∑ o ∈ t, vecSqNorm (z o) * ∫ ω, (X (Sum.inr o) ω) ^ 2 ∂P := by
  classical
  have hterm : ∀ k : K, Integrable
      (fun ω => (∑ i ∈ r1Sites c (dims.erase m) t, r1Coef z t k i * X i ω) ^ 2) P := by
    intro k
    exact MemLp.integrable_sq
      (memLp_finsetSum _ fun i _ => (hmem i).const_mul (r1Coef z t k i))
  have hsplit : ∫ ω, vecSqNorm (r1Rem c dims z m t (fun i => X i ω)) ∂P
      = ∑ k : K, ∫ ω, (∑ i ∈ r1Sites c (dims.erase m) t, r1Coef z t k i * X i ω) ^ 2 ∂P :=
    integral_finsetSum _ fun k _ => hterm k
  have hk : ∀ k : K,
      ∫ ω, (∑ i ∈ r1Sites c (dims.erase m) t, r1Coef z t k i * X i ω) ^ 2 ∂P
        = ∑ i ∈ r1Sites c (dims.erase m) t,
            r1Coef z t k i ^ 2 * ∫ ω, (X i ω) ^ 2 ∂P :=
    fun k => integral_sq_linear_indep X hX hmem hmean _ (r1Coef z t k)
  rw [hsplit, Finset.sum_congr rfl fun k (_ : k ∈ (Finset.univ : Finset K)) => hk k,
    Finset.sum_comm]
  have hi : ∀ i ∈ r1Sites c (dims.erase m) t,
      (∑ k : K, r1Coef z t k i ^ 2 * ∫ ω, (X i ω) ^ 2 ∂P)
        = (∑ k : K, r1Coef z t k i ^ 2) * ∫ ω, (X i ω) ^ 2 ∂P :=
    fun i _ => (Finset.sum_mul _ _ _).symm
  rw [Finset.sum_congr rfl hi, sum_r1Sites]
  simp only [r1Coef, Sum.elim_inl, Sum.elim_inr]
  rfl

end R1Moments

section R1RemBound
open Finset MeasureTheory ProbabilityTheory

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]
variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [Fintype K] [DecidableEq K] [IsProbabilityMeasure P] in
/-- `{m} ∪ {m'}` is a two-element subset of `dims`. -/
theorem union_pair_mem_powersetCard {c : D → O → L} {dims : Finset D} {m m' : D}
    (hm : m ∈ dims) (hm' : m' ∈ dims.erase m) :
    (({m} : Finset D) ∪ ({m'} : Finset D)) ∈ Finset.powersetCard 2 dims := by
  have hne : m ≠ m' := fun h => (Finset.mem_erase.1 hm').1 h.symm
  have hu : ({m} : Finset D) ∪ ({m'} : Finset D) = {m, m'} := by
    rw [Finset.singleton_union]
  rw [hu, Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · refine Finset.insert_subset_iff.2 ⟨hm, ?_⟩
    simpa using (Finset.mem_erase.1 hm').2
  · rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- `E‖r^{(m)}_j‖²` summed over the categories of one dimension. -/
theorem sum_cells_integral_vecSqNorm_r1Rem_le
    (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hX : iIndepFun X P) (hmem : ∀ i, MemLp (X i) 2 P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (vr : D → ℝ) (sg : O → ℝ)
    (hvarEta : ∀ m' ∈ dims, ∀ t' ∈ cells c ({m'} : Finset D),
      ∫ ω, (X (Sum.inl (m', t')) ω) ^ 2 ∂P = vr m' ^ 2)
    (hvarEps : ∀ o, ∫ ω, (X (Sum.inr o) ω) ^ 2 ∂P = sg o ^ 2)
    {B b Cvr Csg Mbar : ℝ}
    (hz : ∀ o, vecSqNorm (z o) ≤ B ^ 2) (hb0 : 0 ≤ b)
    (hb : ∀ e ∈ Finset.powersetCard 2 dims, ∀ t ∈ cells c e, (t.card : ℝ) ≤ b)
    (hvr : ∀ m, vr m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ o, sg o ^ 2 ≤ Csg) (hCsg : 0 ≤ Csg)
    (hM : ((dims.card : ℕ) : ℝ) ≤ Mbar) {m : D} (hm : m ∈ dims) :
    ∑ t ∈ cells c ({m} : Finset D),
        ∫ ω, vecSqNorm (r1Rem c dims z m t (fun i => X i ω)) ∂P
      ≤ Mbar * (Cvr * (b * ((Fintype.card O : ℝ) * B ^ 2)))
        + Csg * ((Fintype.card O : ℝ) * B ^ 2) := by
  classical
  have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
  have hn0 : (0 : ℝ) ≤ (Fintype.card O : ℝ) := Nat.cast_nonneg _
  have hid : ∀ t ∈ cells c ({m} : Finset D),
      ∫ ω, vecSqNorm (r1Rem c dims z m t (fun i => X i ω)) ∂P
        = (∑ m' ∈ dims.erase m, ∑ t' ∈ cells c ({m'} : Finset D),
              vecSqNorm (cellVec z (t ∩ t')) * vr m' ^ 2)
          + ∑ o ∈ t, vecSqNorm (z o) * sg o ^ 2 := by
    intro t _
    rw [integral_vecSqNorm_r1Rem c dims z X hX hmem hmean m t]
    congr 1
    · refine Finset.sum_congr rfl fun m' hm' => Finset.sum_congr rfl fun t' ht' => ?_
      rw [hvarEta m' (Finset.mem_of_mem_erase hm') t' ht']
    · exact Finset.sum_congr rfl fun o _ => by rw [hvarEps o]
  rw [Finset.sum_congr rfl hid, Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · rw [Finset.sum_comm]
    have hstep : ∀ m' ∈ dims.erase m,
        (∑ t ∈ cells c ({m} : Finset D), ∑ t' ∈ cells c ({m'} : Finset D),
            vecSqNorm (cellVec z (t ∩ t')) * vr m' ^ 2)
          ≤ Cvr * (b * ((Fintype.card O : ℝ) * B ^ 2)) := by
      intro m' hm'
      have hbp : ∀ t ∈ cells c (({m} : Finset D) ∪ ({m'} : Finset D)), (t.card : ℝ) ≤ b :=
        hb _ (union_pair_mem_powersetCard (c := c) hm hm')
      have hzeta := step1_zeta_pair_bound c ({m} : Finset D) ({m'} : Finset D) z hz hb0 hbp
      have hfac : (∑ t ∈ cells c ({m} : Finset D), ∑ t' ∈ cells c ({m'} : Finset D),
            vecSqNorm (cellVec z (t ∩ t')) * vr m' ^ 2)
          = (∑ t ∈ cells c ({m} : Finset D), ∑ t' ∈ cells c ({m'} : Finset D),
              vecSqNorm (cellVec z (t ∩ t'))) * vr m' ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun t _ => (Finset.sum_mul _ _ _).symm
      rw [hfac]
      have hnn : (0 : ℝ) ≤ ∑ t ∈ cells c ({m} : Finset D), ∑ t' ∈ cells c ({m'} : Finset D),
          vecSqNorm (cellVec z (t ∩ t')) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => vecSqNorm_nonneg _
      calc (∑ t ∈ cells c ({m} : Finset D), ∑ t' ∈ cells c ({m'} : Finset D),
            vecSqNorm (cellVec z (t ∩ t'))) * vr m' ^ 2
          ≤ (b * ((Fintype.card O : ℝ) * B ^ 2)) * Cvr :=
            mul_le_mul hzeta (hvr m') (sq_nonneg _) (mul_nonneg hb0 (mul_nonneg hn0 hB2))
        _ = Cvr * (b * ((Fintype.card O : ℝ) * B ^ 2)) := by ring
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCvr (mul_nonneg hb0 (mul_nonneg hn0 hB2)))
    exact le_trans (Nat.cast_le.2 (Finset.card_erase_le)) hM
  · rw [sum_over_cells c ({m} : Finset D) fun o => vecSqNorm (z o) * sg o ^ 2]
    calc ∑ o : O, vecSqNorm (z o) * sg o ^ 2
        ≤ ∑ _o : O, B ^ 2 * Csg :=
          Finset.sum_le_sum fun o _ =>
            mul_le_mul (hz o) (hsg o) (sq_nonneg _) hB2
      _ = Csg * ((Fintype.card O : ℝ) * B ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          ring

end R1RemBound

section R1Total
open Finset MeasureTheory ProbabilityTheory

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]
variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `a_n · M · (M · Cvr · c^{(2)}_max + Csg) · n · B²`, the majorant of Step 1's remainder. -/
def step1RemRate (B a nObs M cmax Cvr Csg : ℝ) : ℝ :=
  a * (M * (M * (Cvr * (cmax * (nObs * B ^ 2))) + Csg * (nObs * B ^ 2)))

/-- `a_n∑_{m,j}E‖r^{(m)}_j‖² ≤ step1RemRate`, i.e.
`(N_*/n²)∑_{m,j}E‖r^{(m)}_j‖² ≤ CN_*c^{(2)}_max/n + CN_*/n`. -/
theorem integral_r1RemSum_le (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hX : iIndepFun X P) (hmem : ∀ i, MemLp (X i) 2 P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (vr : D → ℝ) (sg : O → ℝ)
    (hvarEta : ∀ m' ∈ dims, ∀ t' ∈ cells c ({m'} : Finset D),
      ∫ ω, (X (Sum.inl (m', t')) ω) ^ 2 ∂P = vr m' ^ 2)
    (hvarEps : ∀ o, ∫ ω, (X (Sum.inr o) ω) ^ 2 ∂P = sg o ^ 2)
    {B b Cvr Csg Mbar : ℝ}
    (hz : ∀ o, vecSqNorm (z o) ≤ B ^ 2) (hb0 : 0 ≤ b)
    (hb : ∀ e ∈ Finset.powersetCard 2 dims, ∀ t ∈ cells c e, (t.card : ℝ) ≤ b)
    (hvr : ∀ m, vr m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ o, sg o ^ 2 ≤ Csg) (hCsg : 0 ≤ Csg)
    (hM : ((dims.card : ℕ) : ℝ) ≤ Mbar) (hMbar : 0 ≤ Mbar) :
    ∫ ω, r1RemSum c dims z (fun i => X i ω) ∂P
      ≤ Mbar * (Mbar * (Cvr * (b * ((Fintype.card O : ℝ) * B ^ 2)))
          + Csg * ((Fintype.card O : ℝ) * B ^ 2)) := by
  classical
  have hint : ∀ m : D, ∀ t : Finset O,
      Integrable (fun ω => vecSqNorm (r1Rem c dims z m t (fun i => X i ω))) P :=
    fun m t => integrable_vecSqNorm_r1Rem c dims z X hmem m t
  have hsplit : ∫ ω, r1RemSum c dims z (fun i => X i ω) ∂P
      = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
          ∫ ω, vecSqNorm (r1Rem c dims z m t (fun i => X i ω)) ∂P := by
    have hdef : ∀ ω, r1RemSum c dims z (fun i => X i ω)
        = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
            vecSqNorm (r1Rem c dims z m t (fun i => X i ω)) := fun _ => rfl
    simp only [hdef]
    rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun t _ => hint m t]
    exact Finset.sum_congr rfl fun m _ => integral_finsetSum _ fun t _ => hint m t
  rw [hsplit]
  have hper : ∀ m ∈ dims, (∑ t ∈ cells c ({m} : Finset D),
      ∫ ω, vecSqNorm (r1Rem c dims z m t (fun i => X i ω)) ∂P)
      ≤ Mbar * (Cvr * (b * ((Fintype.card O : ℝ) * B ^ 2)))
        + Csg * ((Fintype.card O : ℝ) * B ^ 2) :=
    fun m hm => sum_cells_integral_vecSqNorm_r1Rem_le c dims z X hX hmem hmean vr sg
      hvarEta hvarEps hz hb0 hb hvr hCvr hsg hCsg hM hm
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right hM ?_
  have hn0 : (0 : ℝ) ≤ (Fintype.card O : ℝ) := Nat.cast_nonneg _
  have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
  have h1 : (0 : ℝ) ≤ Mbar * (Cvr * (b * ((Fintype.card O : ℝ) * B ^ 2))) :=
    mul_nonneg hMbar (mul_nonneg hCvr (mul_nonneg hb0 (mul_nonneg hn0 hB2)))
  have h2 : (0 : ℝ) ≤ Csg * ((Fintype.card O : ℝ) * B ^ 2) :=
    mul_nonneg hCsg (mul_nonneg hn0 hB2)
  linarith

end R1Total

section R1LeadBound
open Finset MeasureTheory ProbabilityTheory

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]
variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The coefficient of `η̆^{(m)2}_j` in entry `(p,q)` of the leading part. -/
def r1LeadCoef (z : O → K → ℝ) (p q : K) : ((D × Finset O) ⊕ O) → ℝ :=
  Sum.elim (fun w => cellVec z w.2 p * cellVec z w.2 q) (fun _ => 0)

theorem r1Lead_apply (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → ℝ) (p q : K) :
    (r1Lead c dims z X) p q
      = ∑ i ∈ r1Sites c dims (∅ : Finset O), r1LeadCoef z p q i * (X i) ^ 2 := by
  rw [sum_r1Sites]
  simp only [r1LeadCoef, Sum.elim_inl, Finset.sum_empty, add_zero]
  simp only [r1Lead, Matrix.sum_apply, Matrix.vecMulVec_apply, r1LeadVec]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun t _ => by ring

theorem upsilonN_apply_sites (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (vr : D → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ)
    (hvarEta : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D),
      ∫ ω, (X (Sum.inl (m, t)) ω) ^ 2 ∂P = vr m ^ 2) (p q : K) :
    (upsilonN c dims z vr) p q
      = ∑ i ∈ r1Sites c dims (∅ : Finset O),
          r1LeadCoef z p q i * ∫ ω, (X i ω) ^ 2 ∂P := by
  rw [sum_r1Sites]
  simp only [r1LeadCoef, Sum.elim_inl, Finset.sum_empty, add_zero]
  simp only [upsilonN, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t ht => by rw [hvarEta m hm t ht]; ring

/-- The entrywise-variance bound for the leading part of Step 1. -/
theorem integral_frobSq_r1Lead_le (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (vr : D → ℝ) (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hX : iIndepFun X P)
    (hmem4 : ∀ i, MemLp (fun ω => (X i ω) ^ 2) 2 P)
    (hvarEta : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D),
      ∫ ω, (X (Sum.inl (m, t)) ω) ^ 2 ∂P = vr m ^ 2)
    {C4 a : ℝ} (hfour : ∀ i, ∫ ω, (X i ω) ^ 4 ∂P ≤ C4) :
    ∫ ω, frobSq (a • r1Lead c dims z (fun i => X i ω) - a • upsilonN c dims z vr) ∂P
      ≤ a ^ 2 * (C4 * ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
          (vecSqNorm (cellVec z t)) ^ 2) := by
  classical
  set S : Finset ((D × Finset O) ⊕ O) := r1Sites c dims (∅ : Finset O) with hS
  set E : Ω → K → K → ℝ := fun ω p q =>
    (∑ i ∈ S, r1LeadCoef z p q i * (X i ω) ^ 2)
      - ∑ i ∈ S, r1LeadCoef z p q i * ∫ x, (X i x) ^ 2 ∂P with hE
  have hmemE : ∀ p q : K, MemLp (fun ω => E ω p q) 2 P := by
    intro p q
    exact (memLp_finsetSum _ fun i _ => (hmem4 i).const_mul (r1LeadCoef z p q i)).sub
      (memLp_const _)
  have hintE : ∀ p q : K, Integrable (fun ω => a ^ 2 * (E ω p q) ^ 2) P :=
    fun p q => ((hmemE p q).integrable_sq).const_mul _
  have hpt : ∀ ω, frobSq (a • r1Lead c dims z (fun i => X i ω) - a • upsilonN c dims z vr)
      = ∑ p : K, ∑ q : K, a ^ 2 * (E ω p q) ^ 2 := by
    intro ω
    simp only [frobSq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [r1Lead_apply, upsilonN_apply_sites c dims z vr X hvarEta]
    simp only [hE]
    ring
  have hbound : ∀ p q : K, ∫ ω, (E ω p q) ^ 2 ∂P
      ≤ C4 * ∑ i ∈ S, (r1LeadCoef z p q i) ^ 2 := by
    intro p q
    refine (integral_sq_sub_sq_indep X hX S (r1LeadCoef z p q)
      (fun i _ => hmem4 i)).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [mul_comm C4]
      exact mul_le_mul_of_nonneg_left (hfour i) (sq_nonneg _)
  have hsum : ∫ ω, frobSq (a • r1Lead c dims z (fun i => X i ω)
        - a • upsilonN c dims z vr) ∂P
      = ∑ p : K, ∑ q : K, a ^ 2 * ∫ ω, (E ω p q) ^ 2 ∂P := by
    simp only [hpt]
    rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hintE p q]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum _ fun q _ => hintE p q]
    exact Finset.sum_congr rfl fun q _ => integral_const_mul _ _
  rw [hsum]
  have hstep : ∑ p : K, ∑ q : K, a ^ 2 * ∫ ω, (E ω p q) ^ 2 ∂P
      ≤ ∑ p : K, ∑ q : K, a ^ 2 * (C4 * ∑ i ∈ S, (r1LeadCoef z p q i) ^ 2) := by
    refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
    exact mul_le_mul_of_nonneg_left (hbound p q) (sq_nonneg a)
  refine hstep.trans ?_
  have hcollect : ∑ p : K, ∑ q : K, a ^ 2 * (C4 * ∑ i ∈ S, (r1LeadCoef z p q i) ^ 2)
      = a ^ 2 * (C4 * ∑ i ∈ S, ∑ p : K, ∑ q : K, (r1LeadCoef z p q i) ^ 2) := by
    simp only [Finset.mul_sum]
    calc (∑ p : K, ∑ q : K, ∑ i ∈ S, a ^ 2 * (C4 * (r1LeadCoef z p q i) ^ 2))
        = ∑ p : K, ∑ i ∈ S, ∑ q : K, a ^ 2 * (C4 * (r1LeadCoef z p q i) ^ 2) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ i ∈ S, ∑ p : K, ∑ q : K, a ^ 2 * (C4 * (r1LeadCoef z p q i) ^ 2) := Finset.sum_comm
  rw [hcollect]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sq_nonneg a)
  refine congrArg (fun x => C4 * x) ?_
  rw [hS, sum_r1Sites]
  simp only [r1LeadCoef, Sum.elim_inl, Finset.sum_empty, add_zero]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun t _ => ?_
  rw [vecSqNorm, pow_two, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

end R1LeadBound

section R1Aux
open Finset MeasureTheory ProbabilityTheory

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]
variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `tr(Υ_n) = ∑_m ς²_m ∑_j ‖z^{(m)}_j‖²`. -/
theorem trace_upsilonN (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (vr : D → ℝ) :
    (upsilonN c dims z vr).trace
      = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D), vecSqNorm (cellVec z t) * vr m ^ 2 := by
  classical
  simp only [Matrix.trace, Matrix.diag, upsilonN, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [vecSqNorm, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem integrable_r1LeadSum (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hmem : ∀ i, MemLp (X i) 2 P) :
    Integrable (fun ω => r1LeadSum c dims z (fun i => X i ω)) P := by
  have hdef : ∀ ω, r1LeadSum c dims z (fun i => X i ω)
      = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
          vecSqNorm (cellVec z t) * (X (Sum.inl (m, t)) ω) ^ 2 := fun _ => rfl
  simp only [hdef]
  exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun t _ =>
    ((hmem (Sum.inl (m, t))).integrable_sq).const_mul _

theorem integrable_r1RemSum (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hmem : ∀ i, MemLp (X i) 2 P) :
    Integrable (fun ω => r1RemSum c dims z (fun i => X i ω)) P := by
  have hdef : ∀ ω, r1RemSum c dims z (fun i => X i ω)
      = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
          vecSqNorm (r1Rem c dims z m t (fun i => X i ω)) := fun _ => rfl
  simp only [hdef]
  exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun t _ =>
    integrable_vecSqNorm_r1Rem c dims z X hmem m t

/-- `E[∑_{m,j}‖z^{(m)}_jη̆^{(m)}_j‖²] = tr(Υ_n)`. -/
theorem integral_r1LeadSum (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (vr : D → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hmem : ∀ i, MemLp (X i) 2 P)
    (hvarEta : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D),
      ∫ ω, (X (Sum.inl (m, t)) ω) ^ 2 ∂P = vr m ^ 2) :
    ∫ ω, r1LeadSum c dims z (fun i => X i ω) ∂P = (upsilonN c dims z vr).trace := by
  classical
  have hdef : ∀ ω, r1LeadSum c dims z (fun i => X i ω)
      = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
          vecSqNorm (cellVec z t) * (X (Sum.inl (m, t)) ω) ^ 2 := fun _ => rfl
  simp only [hdef]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun t _ =>
    ((hmem (Sum.inl (m, t))).integrable_sq).const_mul _, trace_upsilonN]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_finsetSum _ fun t _ => ((hmem (Sum.inl (m, t))).integrable_sq).const_mul _]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [integral_const_mul, hvarEta m hm t ht]

theorem integrable_frobSq_r1Lead (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (vr : D → ℝ) (X : ((D × Finset O) ⊕ O) → Ω → ℝ)
    (hmem4 : ∀ i, MemLp (fun ω => (X i ω) ^ 2) 2 P) (a : ℝ) :
    Integrable (fun ω =>
      frobSq (a • r1Lead c dims z (fun i => X i ω) - a • upsilonN c dims z vr)) P := by
  classical
  have hdef : ∀ ω, frobSq (a • r1Lead c dims z (fun i => X i ω) - a • upsilonN c dims z vr)
      = ∑ p : K, ∑ q : K,
          (a * (r1Lead c dims z (fun i => X i ω)) p q - a * (upsilonN c dims z vr) p q) ^ 2 := by
    intro ω
    simp only [frobSq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [hdef]
  refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => ?_
  have hmemF : MemLp (fun ω =>
      a * (r1Lead c dims z (fun i => X i ω)) p q - a * (upsilonN c dims z vr) p q) 2 P := by
    have h1 : MemLp (fun ω => a * (r1Lead c dims z (fun i => X i ω)) p q) 2 P := by
      have : ∀ ω, a * (r1Lead c dims z (fun i => X i ω)) p q
          = ∑ i ∈ r1Sites c dims (∅ : Finset O),
              (a * r1LeadCoef z p q i) * (X i ω) ^ 2 := by
        intro ω
        rw [r1Lead_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [this]
      exact memLp_finsetSum _ fun i _ => (hmem4 i).const_mul _
    exact h1.sub (memLp_const _)
  exact hmemF.integrable_sq

end R1Aux

section Step1Seq
open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Dn On Ln : ℕ → Type*}
  [∀ n, Fintype (On n)] [∀ n, DecidableEq (On n)]
  [∀ n, DecidableEq (Dn n)] [∀ n, DecidableEq (Ln n)]
variable [Fintype K] [DecidableEq K]

/-- **Step 1** of the proof of Theorem 12. -/
theorem step1_tendstoInProb
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, On n → K → ℝ) (vr : ∀ n, Dn n → ℝ) (sg : ∀ n, On n → ℝ)
    (X : ∀ n, ((Dn n × Finset (On n)) ⊕ On n) → Ω → ℝ)
    {a b : ℕ → ℝ} {B Cvr Csg Mbar C4 A : ℝ}
    (ha0 : ∀ n, 0 ≤ a n)
    (hX : ∀ n, iIndepFun (X n) P)
    (hmem : ∀ n i, MemLp (X n i) 2 P)
    (hmem4 : ∀ n i, MemLp (fun ω => (X n i ω) ^ 2) 2 P)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hvarEta : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)),
      ∫ ω, (X n (Sum.inl (m, t)) ω) ^ 2 ∂P = vr n m ^ 2)
    (hvarEps : ∀ n o, ∫ ω, (X n (Sum.inr o) ω) ^ 2 ∂P = sg n o ^ 2)
    (hfour : ∀ n i, ∫ ω, (X n i ω) ^ 4 ∂P ≤ C4)
    (hz : ∀ n o, vecSqNorm (z n o) ≤ B ^ 2) (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ n, ∀ e ∈ Finset.powersetCard 2 (dims n), ∀ t ∈ cells (c n) e, (t.card : ℝ) ≤ b n)
    (hvr : ∀ n m, vr n m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ n o, sg n o ^ 2 ≤ Csg) (hCsg : 0 ≤ Csg)
    (hM : ∀ n, (((dims n).card : ℕ) : ℝ) ≤ Mbar) (hMbar : 0 ≤ Mbar)
    (hA : ∀ n, a n * (upsilonN (c n) (dims n) (z n) (vr n)).trace ≤ A)
    (hrem : Tendsto (fun n => step1RemRate B (a n) (Fintype.card (On n) : ℝ) Mbar (b n) Cvr Csg)
      atTop (𝓝 0))
    (hlead : Tendsto (fun n => (a n) ^ 2 * (C4 *
        ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
          (vecSqNorm (cellVec (z n) t)) ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω => frobNorm (a n • dimMeat (c n) (dims n) (z n)
          (r1Dist (c n) (dims n) (fun i => X n i ω))
        - a n • upsilonN (c n) (dims n) (z n) (vr n))) atTop (fun _ => 0) := by
  classical
  have hleadsq : TendstoInMeasure P
      (fun n ω => frobSq (a n • r1Lead (c n) (dims n) (z n) (fun i => X n i ω)
        - a n • upsilonN (c n) (dims n) (z n) (vr n))) atTop (fun _ => 0) := by
    refine Sequence.tendstoInProb_zero_of_integral_abs_le
      (fun n => integrable_frobSq_r1Lead (c n) (dims n) (z n) (vr n) (X n) (hmem4 n) (a n))
      (fun n => ?_) hlead
    have hnn : ∀ ω, |frobSq (a n • r1Lead (c n) (dims n) (z n) (fun i => X n i ω)
        - a n • upsilonN (c n) (dims n) (z n) (vr n))|
          = frobSq (a n • r1Lead (c n) (dims n) (z n) (fun i => X n i ω)
            - a n • upsilonN (c n) (dims n) (z n) (vr n)) :=
      fun ω => abs_of_nonneg (frobSq_nonneg _)
    simp only [hnn]
    exact integral_frobSq_r1Lead_le (c n) (dims n) (z n) (vr n) (X n) (hX n) (hmem4 n)
      (hvarEta n) (hfour n)
  have hleadp : TendstoInMeasure P
      (fun n ω => frobNorm (a n • r1Lead (c n) (dims n) (z n) (fun i => X n i ω)
        - a n • upsilonN (c n) (dims n) (z n) (vr n))) atTop (fun _ => 0) :=
    Sequence.tendstoInProb_sqrt_zero hleadsq
  have hremp : TendstoInMeasure P
      (fun n ω => a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω))
      atTop (fun _ => 0) := by
    refine Sequence.tendstoInProb_zero_of_integral_abs_le
      (fun n => (integrable_r1RemSum (c n) (dims n) (z n) (X n) (hmem n)).const_mul _)
      (fun n => ?_) hrem
    have hnn : ∀ ω, |a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω)|
        = a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω) :=
      fun ω => abs_of_nonneg (mul_nonneg (ha0 n) (r1RemSum_nonneg _ _ _ _))
    simp only [hnn, integral_const_mul, step1RemRate]
    refine mul_le_mul_of_nonneg_left ?_ (ha0 n)
    exact (integral_r1RemSum_le (c n) (dims n) (z n) (X n) (hX n) (hmem n) (hmean n)
      (vr n) (sg n) (hvarEta n) (hvarEps n) (hz n) (hb0 n) (hb n) (hvr n) hCvr (hsg n) hCsg
      (hM n) hMbar).trans (le_of_eq (by ring))
  have hleadop : Sequence.BddInProb P
      (fun n ω => a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω)) := by
    have hint : ∀ n, Integrable
        (fun ω => a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω)) P :=
      fun n => (integrable_r1LeadSum (c n) (dims n) (z n) (X n) (hmem n)).const_mul _
    refine Sequence.bddInProb_of_lintegral_le (fun n => (hint n).aemeasurable)
      (M := ENNReal.ofReal A) ENNReal.ofReal_ne_top (fun n => ?_)
    have h1 : ENNReal.ofReal (∫ ω, ‖a n * r1LeadSum (c n) (dims n) (z n)
          (fun i => X n i ω)‖ ∂P)
        = ∫⁻ ω, ‖a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω)‖ₑ ∂P :=
      ofReal_integral_norm_eq_lintegral_enorm (hint n)
    rw [← h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hnn : ∀ ω, ‖a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω)‖
        = a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω) :=
      fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (mul_nonneg (ha0 n) (r1LeadSum_nonneg _ _ _ _))
    simp only [hnn, integral_const_mul]
    rw [integral_r1LeadSum (c n) (dims n) (z n) (vr n) (X n) (hmem n) (hvarEta n)]
    exact hA n
  have hcross : TendstoInMeasure P
      (fun n ω => 2 * Real.sqrt ((a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω))
        * (a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω)))) atTop (fun _ => 0) := by
    refine Sequence.tendstoInProb_zero_of_le_sqrt_mul (κ := 2) (by norm_num)
      (fun n => Filter.Eventually.of_forall fun ω =>
        mul_nonneg (ha0 n) (r1RemSum_nonneg _ _ _ _))
      (fun n => Filter.Eventually.of_forall fun ω => ?_) hremp hleadop
    exact le_of_eq (abs_of_nonneg (by positivity))
  have hbr : TendstoInMeasure P
      (fun n ω => a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω)
        + 2 * Real.sqrt ((a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω))
          * (a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω))))
      atTop (fun _ => 0) := by
    refine Sequence.tendstoInProb_zero_of_abs_le_add
      (fun n => Filter.Eventually.of_forall fun ω => ?_) hremp hcross
    have h1 : (0 : ℝ) ≤ a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω) :=
      mul_nonneg (ha0 n) (r1RemSum_nonneg _ _ _ _)
    have h2 : (0 : ℝ) ≤ 2 * Real.sqrt ((a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω))
        * (a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω))) := by positivity
    rw [abs_of_nonneg (by linarith), abs_of_nonneg h1, abs_of_nonneg h2]
  refine Sequence.tendstoInProb_zero_of_abs_le_add
    (fun n => Filter.Eventually.of_forall fun ω => ?_) hleadp hbr
  have hdec := frobNorm_r1_decomp_le (c n) (dims n) (z n) (vr n) (fun i => X n i ω) (ha0 n)
  have h1 : (0 : ℝ) ≤ frobNorm (a n • r1Lead (c n) (dims n) (z n) (fun i => X n i ω)
      - a n • upsilonN (c n) (dims n) (z n) (vr n)) := frobNorm_nonneg _
  have h2 : (0 : ℝ) ≤ a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω)
      + 2 * Real.sqrt ((a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω))
        * (a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω))) := by
    have hq1 : (0 : ℝ) ≤ a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω) :=
      mul_nonneg (ha0 n) (r1RemSum_nonneg _ _ _ _)
    have hq2 : (0 : ℝ) ≤ Real.sqrt ((a n * r1RemSum (c n) (dims n) (z n) (fun i => X n i ω))
        * (a n * r1LeadSum (c n) (dims n) (z n) (fun i => X n i ω))) := Real.sqrt_nonneg _
    linarith
  rw [abs_of_nonneg (frobNorm_nonneg _), abs_of_nonneg h1, abs_of_nonneg h2]
  exact hdec

end Step1Seq

section R1Meas
open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω}

/-- `Finset.aemeasurable_sum`, in applied form. -/
theorem aemeasurable_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, AEMeasurable (f i) P) : AEMeasurable (fun ω => ∑ i ∈ s, f i ω) P := by
  have h := Finset.aemeasurable_sum s hf
  have he : (∑ i ∈ s, f i) = fun ω => ∑ i ∈ s, f i ω := by
    funext ω
    simp [Finset.sum_apply]
  rwa [he] at h

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]

theorem trace_upsilonN_nonneg (c : D → O → L) (dims : Finset D) (z : O → K → ℝ) (vr : D → ℝ) :
    0 ≤ (upsilonN c dims z vr).trace := by
  rw [trace_upsilonN]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (vecSqNorm_nonneg _) (sq_nonneg _)

/-- The quantity in `hstep1` is measurable. -/
theorem aemeasurable_frobNorm_dimMeat_r1Dist (c : D → O → L) (dims : Finset D) (z : O → K → ℝ)
    (vr : D → ℝ) (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hXm : ∀ i, AEMeasurable (X i) P) (a : ℝ) :
    AEMeasurable (fun ω => frobNorm (a • dimMeat c dims z (r1Dist c dims (fun i => X i ω))
      - a • upsilonN c dims z vr)) P := by
  classical
  have hu : ∀ o : O, AEMeasurable (fun ω => r1Dist c dims (fun i => X i ω) o) P := by
    intro o
    have h1 : AEMeasurable
        (fun ω => ∑ m ∈ dims, X (Sum.inl (m, cellOf c ({m} : Finset D) o)) ω) P :=
      aemeasurable_finsetSum _ fun m _ => hXm _
    exact h1.add (hXm _)
  have hcs : ∀ (t : Finset O) (k : K),
      AEMeasurable (fun ω => cellScore z (r1Dist c dims (fun i => X i ω)) t k) P := by
    intro t k
    have h1 : AEMeasurable
        (fun ω => ∑ o ∈ t, z o k * r1Dist c dims (fun i => X i ω) o) P :=
      aemeasurable_finsetSum _ fun o _ => ((hu o).const_mul (z o k))
    exact h1
  have hentry : ∀ p q : K, AEMeasurable (fun ω =>
      (a * (dimMeat c dims z (r1Dist c dims (fun i => X i ω))) p q
        - a * (upsilonN c dims z vr) p q) ^ 2) P := by
    intro p q
    have hd : AEMeasurable
        (fun ω => (dimMeat c dims z (r1Dist c dims (fun i => X i ω))) p q) P := by
      have hrw : ∀ ω, (dimMeat c dims z (r1Dist c dims (fun i => X i ω))) p q
          = ∑ m ∈ dims, ∑ t ∈ cells c ({m} : Finset D),
              cellScore z (r1Dist c dims (fun i => X i ω)) t p
                * cellScore z (r1Dist c dims (fun i => X i ω)) t q := by
        intro ω
        simp only [dimMeat, Matrix.sum_apply, Matrix.vecMulVec_apply]
      simp only [hrw]
      exact aemeasurable_finsetSum _ fun m _ =>
        aemeasurable_finsetSum _ fun t _ => (hcs t p).mul (hcs t q)
    exact ((hd.const_mul a).sub_const _).pow_const 2
  have hdef : (fun ω => frobNorm (a • dimMeat c dims z (r1Dist c dims (fun i => X i ω))
      - a • upsilonN c dims z vr))
      = fun ω => Real.sqrt (∑ p : K, ∑ q : K,
          (a * (dimMeat c dims z (r1Dist c dims (fun i => X i ω))) p q
            - a * (upsilonN c dims z vr) p q) ^ 2) := by
    funext ω
    simp only [frobNorm, frobSq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hdef]
  exact Real.continuous_sqrt.measurable.comp_aemeasurable
    (aemeasurable_finsetSum _ fun p _ => aemeasurable_finsetSum _ fun q _ => hentry p q)

end R1Meas

section R1Chain
open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Dn On Ln : ℕ → Type*}
  [∀ n, Fintype (On n)] [∀ n, DecidableEq (On n)]
  [∀ n, DecidableEq (Dn n)] [∀ n, DecidableEq (Ln n)]
variable [Fintype K] [DecidableEq K]

/-- **Theorem 12(a)** with Step 1 supplied. -/
theorem piinf_a_of_regime1
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, On n → K → ℝ) (v : ∀ n, Ω → On n → ℝ)
    (Pim : ∀ n, Matrix (On n) (On n) ℝ) (vr : ∀ n, Dn n → ℝ) (sg : ∀ n, On n → ℝ)
    (X : ∀ n, ((Dn n × Finset (On n)) ⊕ On n) → Ω → ℝ)
    {a b G : ℕ → ℝ} {B R Cvr Csg Mbar C4 A : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (hG : ∀ n, 1 ≤ G n)
    (hcard : ∀ n, 0 < (Fintype.card (On n) : ℝ))
    (hX : ∀ n, iIndepFun (X n) P)
    (hmem : ∀ n i, MemLp (X n i) 2 P)
    (hmem4 : ∀ n i, MemLp (fun ω => (X n i ω) ^ 2) 2 P)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hvarEta : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)),
      ∫ ω, (X n (Sum.inl (m, t)) ω) ^ 2 ∂P = vr n m ^ 2)
    (hvarEps : ∀ n o, ∫ ω, (X n (Sum.inr o) ω) ^ 2 ∂P = sg n o ^ 2)
    (hfour : ∀ n i, ∫ ω, (X n i ω) ^ 4 ∂P ≤ C4)
    (hz : ∀ n o, vecSqNorm (z n o) ≤ B ^ 2)
    (hb : ∀ n, ∀ e ∈ Finset.powersetCard 2 (dims n), ∀ t ∈ cells (c n) e, (t.card : ℝ) ≤ b n)
    (hcell : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)), (t.card : ℝ) ≤ G n)
    (hrate4 : Tendsto (fun n => step4Rate B (a n) (Fintype.card (On n) : ℝ)
      (((Finset.powersetCard 2 (dims n)).card : ℝ)) (b n)) atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => step2Rate B (a n) ((dims n).card : ℝ) (G n)) atTop (𝓝 0))
    (hrem : Tendsto (fun n => step1RemRate B (a n) (Fintype.card (On n) : ℝ) Mbar (b n) Cvr Csg)
      atTop (𝓝 0))
    (hlead : Tendsto (fun n => (a n) ^ 2 * (C4 *
        ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
          (vecSqNorm (cellVec (z n) t)) ^ 2)) atTop (𝓝 0))
    (hsym : ∀ n, (Pim n).transpose = Pim n) (hidem : ∀ n, Pim n * Pim n = Pim n)
    (htr : ∀ n, (Pim n).trace ≤ R) (hR : 0 ≤ R)
    (hw : ∀ n ω o, v n ω o - r1Dist (c n) (dims n) (fun i => X n i ω) o
      = -((Pim n).mulVec (r1Dist (c n) (dims n) (fun i => X n i ω)) o))
    (hint : ∀ n p q, Integrable (fun ω => r1Dist (c n) (dims n) (fun i => X n i ω) p
      * r1Dist (c n) (dims n) (fun i => X n i ω) q) P)
    (hEu : ∀ n p q, ∫ ω, r1Dist (c n) (dims n) (fun i => X n i ω) p
      * r1Dist (c n) (dims n) (fun i => X n i ω) q ∂P
        = omegaU (c n) (dims n) (vr n) (sg n) p q)
    (hvr : ∀ n m, vr n m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ n o, sg n o ^ 2 ≤ Csg) (hCsg : 0 ≤ Csg)
    (hM : ∀ n, (((dims n).card : ℕ) : ℝ) ≤ Mbar) (hMbar : 0 ≤ Mbar)
    (hA : ∀ n, a n * (upsilonN (c n) (dims n) (z n) (vr n)).trace ≤ A) :
    TendstoInMeasure P
      (fun n ω => frobNorm (a n • ieMeat (c n) (dims n) (z n) (v n ω)
        - a n • upsilonN (c n) (dims n) (z n) (vr n))) atTop (fun _ => 0) := by
  classical
  have hXm : ∀ n i, AEMeasurable (X n i) P :=
    fun n i => (hmem n i).aestronglyMeasurable.aemeasurable
  have hUps : ∀ n, |(a n • upsilonN (c n) (dims n) (z n) (vr n)).trace| ≤ A := by
    intro n
    rw [Matrix.trace_smul, smul_eq_mul,
      abs_of_nonneg (mul_nonneg (ha0 n) (trace_upsilonN_nonneg _ _ _ _))]
    exact hA n
  have hmeas : ∀ n, AEMeasurable (fun ω => frobNorm (a n • dimMeat (c n) (dims n) (z n)
      (r1Dist (c n) (dims n) (fun i => X n i ω))
      - a n • upsilonN (c n) (dims n) (z n) (vr n))) P :=
    fun n => aemeasurable_frobNorm_dimMeat_r1Dist (c n) (dims n) (z n) (vr n) (X n)
      (hXm n) (a n)
  exact piinf_a_of_step1 c dims (fun n _ => z n) v
    (fun n ω => r1Dist (c n) (dims n) (fun i => X n i ω)) Pim vr sg
    ha0 hb0 hG hcard (fun n => Filter.Eventually.of_forall fun ω => hz n) hb hcell
    hrate4 hrate2 hsym hidem htr hR hw hint hEu hvr hCvr hsg hCsg
    (fun n => hM n) hMbar hmeas hUps
    (step1_tendstoInProb c dims z vr sg X ha0 hX hmem hmem4 hmean hvarEta hvarEps hfour
      hz hb0 hb hvr hCvr hsg hCsg hM hMbar hA hrem hlead)

end R1Chain

namespace Step1Model
open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- The witness design: an `(n+1) × (n+1)` grid of observations. -/
abbrev wO (n : ℕ) : Type := Fin (n + 1) × Fin (n + 1)

/-- Two fixed-effect dimensions, the row index and the column index. -/
def wC (n : ℕ) : Fin 2 → wO n → Fin (n + 1) := fun d o => if d = 0 then o.1 else o.2

/-- A single regressor, identically one, so `B = 1`. -/
def wZ (n : ℕ) : wO n → Fin 1 → ℝ := fun _ _ => 1

/-- `a_n = N_*/n² = (n+1)/((n+1)²)²`. -/
noncomputable def wA (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 3

theorem wA_nonneg (n : ℕ) : 0 ≤ wA n := by
  rw [wA]
  positivity

theorem wCard (n : ℕ) : (Fintype.card (wO n) : ℝ) = ((n : ℝ) + 1) ^ 2 := by
  simp [wO, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Every level-`{d}` cell is a row or a column, with `n+1` observations. -/
theorem wCell_card (n : ℕ) (d : Fin 2) {t : Finset (wO n)}
    (ht : t ∈ cells (wC n) ({d} : Finset (Fin 2))) : t.card = n + 1 := by
  classical
  obtain ⟨o, -, rfl⟩ := Finset.mem_image.1 ht
  have hset : ∀ (dd : Fin 2) (oo : wO n), cellOf (wC n) ({dd} : Finset (Fin 2)) oo
      = Finset.univ.filter (fun o' : wO n => wC n dd o' = wC n dd oo) := by
    intro dd oo
    ext o'
    simp only [mem_cellOf, Finset.mem_filter, Finset.mem_univ, true_and, SameOn,
      Finset.mem_singleton]
    exact ⟨fun h => h dd rfl, fun h j hj => by subst hj; exact h⟩
  have key : ∀ (dd : Fin 2), ∀ (oo : wO n),
      (Finset.univ.filter (fun o' : wO n => wC n dd o' = wC n dd oo)).card = n + 1 := by
    rw [Fin.forall_fin_two]
    constructor
    · intro oo
      have he : (Finset.univ.filter (fun o' : wO n => wC n 0 o' = wC n 0 oo))
          = ({oo.1} : Finset (Fin (n + 1))) ×ˢ (Finset.univ : Finset (Fin (n + 1))) := by
        ext o'
        simp only [wC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton, and_true, if_pos rfl]
        exact ⟨fun h => h, fun h => h⟩
      rw [he, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
        one_mul]
    · intro oo
      have he : (Finset.univ.filter (fun o' : wO n => wC n 1 o' = wC n 1 oo))
          = (Finset.univ : Finset (Fin (n + 1))) ×ˢ ({oo.2} : Finset (Fin (n + 1))) := by
        ext o'
        simp only [wC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton]
        norm_num
      rw [he, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
        mul_one]
  rw [hset d o]
  exact key d o

/-- Every level-`{0,1}` cell is a single observation, so `c^{(2)}_max = 1`. -/
theorem wPair_card (n : ℕ) {e : Finset (Fin 2)}
    (he : e ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))) {t : Finset (wO n)}
    (ht : t ∈ cells (wC n) e) : t.card = 1 := by
  classical
  have heu : e = (Finset.univ : Finset (Fin 2)) := by
    have hc := (Finset.mem_powersetCard.1 he).2
    exact Finset.eq_univ_of_card e (by simpa using hc)
  subst heu
  obtain ⟨o, -, rfl⟩ := Finset.mem_image.1 ht
  have hset : cellOf (wC n) (Finset.univ : Finset (Fin 2)) o = ({o} : Finset (wO n)) := by
    ext o'
    simp only [mem_cellOf, SameOn, Finset.mem_univ, forall_true_left, Finset.mem_singleton,
      forall_const]
    constructor
    · intro h
      have h0 := h 0
      have h1 := h 1
      simp only [wC] at h0 h1
      norm_num at h0 h1
      exact Prod.ext h0 h1
    · intro h j
      rw [h]
  rw [hset, Finset.card_singleton]

theorem wSumCard (n : ℕ) (F : Finset (Fin 2)) :
    ∑ t ∈ cells (wC n) F, ((t.card : ℕ) : ℝ) = ((n : ℝ) + 1) ^ 2 := by
  classical
  have h : ∀ t : Finset (wO n), ((t.card : ℕ) : ℝ) = ∑ _o ∈ t, (1 : ℝ) := by
    intro t
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun t _ => h t, sum_over_cells (wC n) F (fun _ => (1 : ℝ)),
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  exact wCard n

theorem wVecSq (n : ℕ) (t : Finset (wO n)) :
    vecSqNorm (cellVec (wZ n) t) = ((t.card : ℕ) : ℝ) ^ 2 := by
  have hc : ∀ k : Fin 1, cellVec (wZ n) t k = ((t.card : ℕ) : ℝ) := by
    intro k
    rw [cellVec]
    simp [wZ, Finset.sum_const, nsmul_eq_mul]
  simp [vecSqNorm, hc]

theorem wSumVecSq (n : ℕ) (d : Fin 2) :
    ∑ t ∈ cells (wC n) ({d} : Finset (Fin 2)), vecSqNorm (cellVec (wZ n) t)
      = ((n : ℝ) + 1) ^ 3 := by
  classical
  have hstep : ∀ t ∈ cells (wC n) ({d} : Finset (Fin 2)),
      vecSqNorm (cellVec (wZ n) t) = ((n : ℝ) + 1) * ((t.card : ℕ) : ℝ) := by
    intro t ht
    rw [wVecSq, wCell_card n d ht]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, wSumCard]
  ring

theorem wSumVecSq4 (n : ℕ) (d : Fin 2) :
    ∑ t ∈ cells (wC n) ({d} : Finset (Fin 2)), (vecSqNorm (cellVec (wZ n) t)) ^ 2
      = ((n : ℝ) + 1) ^ 5 := by
  classical
  have hstep : ∀ t ∈ cells (wC n) ({d} : Finset (Fin 2)),
      (vecSqNorm (cellVec (wZ n) t)) ^ 2 = ((n : ℝ) + 1) ^ 3 * ((t.card : ℕ) : ℝ) := by
    intro t ht
    rw [wVecSq, wCell_card n d ht]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, wSumCard]
  ring

theorem wTrace (n : ℕ) :
    (upsilonN (wC n) (Finset.univ : Finset (Fin 2)) (wZ n) (fun _ => (1 : ℝ))).trace
      = 2 * ((n : ℝ) + 1) ^ 3 := by
  classical
  rw [trace_upsilonN]
  have hstep : ∀ d ∈ (Finset.univ : Finset (Fin 2)),
      (∑ t ∈ cells (wC n) ({d} : Finset (Fin 2)),
        vecSqNorm (cellVec (wZ n) t) * (1 : ℝ) ^ 2) = ((n : ℝ) + 1) ^ 3 := by
    intro d _
    simpa using wSumVecSq n d
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

/-- `a_n tr(Υ_n) = 2` at every index. -/
theorem wA_trace (n : ℕ) :
    wA n * (upsilonN (wC n) (Finset.univ : Finset (Fin 2)) (wZ n) (fun _ => (1 : ℝ))).trace
      = 2 := by
  rw [wTrace, wA]
  have h : ((n : ℝ) + 1) ^ 3 ≠ 0 := by positivity
  field_simp

theorem wRemRate (n : ℕ) :
    step1RemRate 1 (wA n) (Fintype.card (wO n) : ℝ) 2 1 1 1 = 6 / ((n : ℝ) + 1) := by
  rw [step1RemRate, wCard, wA]
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem wLeadRate (n : ℕ) :
    (wA n) ^ 2 * (1 * ∑ m ∈ (Finset.univ : Finset (Fin 2)),
        ∑ t ∈ cells (wC n) ({m} : Finset (Fin 2)), (vecSqNorm (cellVec (wZ n) t)) ^ 2)
      = 2 / ((n : ℝ) + 1) := by
  classical
  have hstep : ∀ d ∈ (Finset.univ : Finset (Fin 2)),
      (∑ t ∈ cells (wC n) ({d} : Finset (Fin 2)), (vecSqNorm (cellVec (wZ n) t)) ^ 2)
        = ((n : ℝ) + 1) ^ 5 := fun d _ => wSumVecSq4 n d
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, wA]
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_const_div : ∀ k : ℝ,
    Tendsto (fun n : ℕ => k / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  intro k
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := h.const_mul k
  simpa [mul_one_div, div_eq_mul_inv] using this

end Step1Model

namespace Step1Model

open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
theorem integral_sq_rade : ∫ x, x ^ 2 ∂CLT.Witness.rade = 1 := by
  rw [CLT.Witness.integral_rade (f := fun x : ℝ => x ^ 2) (by fun_prop)]
  norm_num

theorem wVecSqNorm_z (n : ℕ) (o : wO n) : vecSqNorm (wZ n o) = 1 := by
  simp [vecSqNorm, wZ]

/-- `step1_tendstoInProb` on a balanced two-way grid with i.i.d. Rademacher disturbances. -/
theorem step1_witness :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Measure Om) (_ : IsProbabilityMeasure P)
      (X : ∀ n, ((Fin 2 × Finset (wO n)) ⊕ wO n) → Om → ℝ),
      TendstoInMeasure P
        (fun n ω => frobNorm (wA n • dimMeat (wC n) (Finset.univ : Finset (Fin 2)) (wZ n)
            (r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω))
          - wA n • upsilonN (wC n) (Finset.univ : Finset (Fin 2)) (wZ n) (fun _ => (1 : ℝ))))
        atTop (fun _ => 0)
      ∧ (∀ n, wA n
          * (upsilonN (wC n) (Finset.univ : Finset (Fin 2)) (wZ n) (fun _ => (1 : ℝ))).trace = 2)
      ∧ (∀ n, (Fintype.card (wO n) : ℝ) = ((n : ℝ) + 1) ^ 2)
      ∧ (∀ n, ∀ d : Fin 2, ∀ t ∈ cells (wC n) ({d} : Finset (Fin 2)), t.card = n + 1)
      ∧ (∀ n, ∀ e ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)),
          ∀ t ∈ cells (wC n) e, t.card = 1) := by
  classical
  obtain ⟨Om, mOm, P, xi, hmeasx, hlawx, hindepx, hprobx⟩ :=
    exists_iid (Σ n : ℕ, ((Fin 2 × Finset (wO n)) ⊕ wO n)) CLT.Witness.rade
  refine ⟨Om, mOm, P, hprobx, fun n i => xi ⟨n, i⟩, ?_, wA_trace, wCard,
    fun n d t ht => wCell_card n d ht, fun n e he t ht => wPair_card n he ht⟩
  have hmean : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      ∫ ω, xi ⟨n, i⟩ ω ∂P = 0 := by
    intro n i
    rw [(hlawx ⟨n, i⟩).integral_eq, CLT.Witness.integral_id_rade]
  have hmem : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n), MemLp (xi ⟨n, i⟩) 2 P :=
    fun n i => (hlawx ⟨n, i⟩).memLp CLT.Witness.memLp_id_rade
  have hint4 : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      Integrable (fun ω => (xi ⟨n, i⟩ ω) ^ 4) P :=
    fun n i => (hlawx ⟨n, i⟩).integrable_fun_comp CLT.Witness.integrable_pow4_rade
  have hmem4 : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      MemLp (fun ω => (xi ⟨n, i⟩ ω) ^ 2) 2 P := by
    intro n i
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    refine (hint4 n i).congr ?_
    filter_upwards with ω
    show (xi ⟨n, i⟩ ω) ^ 4 = ((xi ⟨n, i⟩ ω) ^ 2) ^ 2
    ring
  have hsq : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      ∫ ω, (xi ⟨n, i⟩ ω) ^ 2 ∂P = 1 := by
    intro n i
    have h := (hlawx ⟨n, i⟩).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [show (∫ ω, (xi ⟨n, i⟩ ω) ^ 2 ∂P) = ∫ ω, ((fun x : ℝ => x ^ 2) ∘ (xi ⟨n, i⟩)) ω ∂P from rfl,
      h, integral_sq_rade]
  have hfour : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      ∫ ω, (xi ⟨n, i⟩ ω) ^ 4 ∂P ≤ 1 := by
    intro n i
    have h := (hlawx ⟨n, i⟩).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [show (∫ ω, (xi ⟨n, i⟩ ω) ^ 4 ∂P) = ∫ ω, ((fun x : ℝ => x ^ 4) ∘ (xi ⟨n, i⟩)) ω ∂P from rfl,
      h, CLT.Witness.integral_pow4_rade]
  have hrem : Tendsto (fun n : ℕ => step1RemRate 1 (wA n) (Fintype.card (wO n) : ℝ) 2 1 1 1)
      atTop (𝓝 0) := by
    have he : (fun n : ℕ => step1RemRate 1 (wA n) (Fintype.card (wO n) : ℝ) 2 1 1 1)
        = fun n : ℕ => 6 / ((n : ℝ) + 1) := funext wRemRate
    rw [he]
    exact tendsto_const_div 6
  have hlead : Tendsto (fun n : ℕ => (wA n) ^ 2 * (1 *
      ∑ m ∈ (Finset.univ : Finset (Fin 2)),
        ∑ t ∈ cells (wC n) ({m} : Finset (Fin 2)),
          (vecSqNorm (cellVec (wZ n) t)) ^ 2)) atTop (𝓝 0) := by
    have he : (fun n : ℕ => (wA n) ^ 2 * (1 *
        ∑ m ∈ (Finset.univ : Finset (Fin 2)),
          ∑ t ∈ cells (wC n) ({m} : Finset (Fin 2)),
            (vecSqNorm (cellVec (wZ n) t)) ^ 2))
        = fun n : ℕ => 2 / ((n : ℝ) + 1) := funext wLeadRate
    rw [he]
    exact tendsto_const_div 2
  exact step1_tendstoInProb (K := Fin 1) wC (fun _ => Finset.univ) wZ
    (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) (fun n i => xi ⟨n, i⟩)
    (B := 1) (Cvr := 1) (Csg := 1) (Mbar := 2) (C4 := 1) (A := 2) (b := fun _ => 1)
    wA_nonneg
    (fun n => hindepx.precomp (g := fun i => (⟨n, i⟩ : Σ n : ℕ, _)) sigma_mk_injective)
    hmem hmem4 hmean
    (fun n m _ t _ => by rw [hsq n (Sum.inl (m, t))]; norm_num)
    (fun n o => by rw [hsq n (Sum.inr o)]; norm_num)
    hfour
    (fun n o => by rw [wVecSqNorm_z]; norm_num)
    (fun _ => zero_le_one)
    (fun n e he t ht => by rw [wPair_card n he ht]; norm_num)
    (fun _ _ => by norm_num) zero_le_one
    (fun _ _ => by norm_num) zero_le_one
    (fun _ => by simp) (by norm_num)
    (fun n => le_of_eq (wA_trace n)) hrem hlead

end Step1Model

/-! ## §10 Theorem 6 restricted through a rectangular `𝓡`

For `s ∈ ℝ^r`, `⟪s, √N_*𝓡(π̂-π)⟫ = ⟪𝓡's, √N_*(π̂-π)⟫`, so the restricted limit follows from
Cramér--Wold in the single direction `t := 𝓡's`, whose scalar limit has variance
`s'(𝓡Ψ⁻¹ΥΨ⁻¹𝓡')s`. No theorem on linear images of multivariate Gaussians is needed.

* `tendstoInDistribution_apply_of_solve_rect`: Slutsky through a rectangular limit map.
* `pi_clt_std_rect`: the limit law of any `dev_n = A_n(score_n)` with `A_n` rectangular.
* `pi_clt_std_restricted`: `√N_* 𝓡(π̂ - π) ⟶^d N(0, Sg)` for a fixed `𝓡`, with `Sg` fixed by
  `hsand`. -/
section Rect
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `‖(A_n)† t - A† t‖ → 0` between two Euclidean spaces of different dimension. -/
theorem tendsto_adjoint_apply_rect {Kq r : ℕ}
    {A : ℕ → (EuclideanSpace ℝ (Fin Kq) →L[ℝ] EuclideanSpace ℝ (Fin r))}
    {Ainf : EuclideanSpace ℝ (Fin Kq) →L[ℝ] EuclideanSpace ℝ (Fin r)}
    (hA : Tendsto A atTop (𝓝 Ainf)) (t : EuclideanSpace ℝ (Fin r)) :
    Tendsto (fun n => (ContinuousLinearMap.adjoint (A n)) t) atTop
      (𝓝 ((ContinuousLinearMap.adjoint Ainf) t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (?_ : Tendsto (fun n => ‖A n - Ainf‖ * ‖t‖) atTop (𝓝 0))
  · have h : (ContinuousLinearMap.adjoint (A n)) t - (ContinuousLinearMap.adjoint Ainf) t
        = (ContinuousLinearMap.adjoint (A n - Ainf)) t := by
      rw [map_sub]; rfl
    rw [h]
    refine (ContinuousLinearMap.le_opNorm _ t).trans ?_
    exact mul_le_mul_of_nonneg_right
      (le_of_eq (LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _)) (norm_nonneg t)
  · have h0 : Tendsto (fun n => ‖A n - Ainf‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hA
    simpa using h0.mul_const ‖t‖

/-- Slutsky through a rectangular limit map. -/
theorem tendstoInDistribution_apply_of_solve_rect {Kq r : ℕ}
    {W : ℕ → Ω → EuclideanSpace ℝ (Fin Kq)} {Ups : Matrix (Fin Kq) (Fin Kq) ℝ}
    {Sg : Matrix (Fin r) (Fin r) ℝ}
    (hUps : Ups.PosSemidef) (hSg : Sg.PosSemidef)
    (hW : TendstoInDistribution W atTop
      (id : EuclideanSpace ℝ (Fin Kq) → EuclideanSpace ℝ (Fin Kq)) (fun _ => P)
      (multivariateGaussian 0 Ups))
    {A : ℕ → (EuclideanSpace ℝ (Fin Kq) →L[ℝ] EuclideanSpace ℝ (Fin r))}
    {Ainf : EuclideanSpace ℝ (Fin Kq) →L[ℝ] EuclideanSpace ℝ (Fin r)}
    (hA : Tendsto A atTop (𝓝 Ainf))
    (hsand : ∀ t : EuclideanSpace ℝ (Fin r),
      (ContinuousLinearMap.adjoint Ainf t) ⬝ᵥ (Ups *ᵥ (ContinuousLinearMap.adjoint Ainf t))
        = t ⬝ᵥ (Sg *ᵥ t))
    {dev : ℕ → Ω → EuclideanSpace ℝ (Fin r)} (hdevmeas : ∀ n, AEMeasurable (dev n) P)
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω, dev n ω = A n (W n ω)) :
    TendstoInDistribution dev atTop
      (id : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r)) (fun _ => P)
      (multivariateGaussian 0 Sg) := by
  refine TendstoInDistribution.of_inner (by fun_prop) hdevmeas ?_
  intro t
  have hY : TendstoInMeasure P
      (fun (n : ℕ) (_ : Ω) => (ContinuousLinearMap.adjoint (A n)) t) atTop
      (fun _ => (ContinuousLinearMap.adjoint Ainf) t) :=
    CLT.tendstoInMeasure_of_tendsto_const (tendsto_adjoint_apply_rect hA t)
  have hSl := hW.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : EuclideanSpace ℝ (Fin Kq) × EuclideanSpace ℝ (Fin Kq) => ⟪p.1, p.2⟫)
    (by fun_prop) hY (fun n => aemeasurable_const)
  have hlaw : (multivariateGaussian 0 Sg).map (fun x : EuclideanSpace ℝ (Fin r) => ⟪x, t⟫)
      = (multivariateGaussian 0 Ups).map
          (fun x : EuclideanSpace ℝ (Fin Kq) => ⟪x, (ContinuousLinearMap.adjoint Ainf) t⟫) := by
    rw [CLT.map_inner_multivariateGaussian hSg t,
      CLT.map_inner_multivariateGaussian hUps ((ContinuousLinearMap.adjoint Ainf) t), hsand t]
  have hSl2 := CLT.tendstoInDistribution_of_law_eq hSl (by fun_prop) hlaw
  refine CLT.tendstoInDistribution_of_eventually_ae_eq hSl2
    (fun n => (Continuous.measurable (by fun_prop :
      Continuous fun x : EuclideanSpace ℝ (Fin r) => ⟪x, t⟫)).comp_aemeasurable (hdevmeas n)) ?_
  filter_upwards [hsolve] with n hn
  filter_upwards with ω
  rw [hn ω, ← ContinuousLinearMap.adjoint_inner_right]

/-- The rectangular face of `pi_clt_std`. -/
theorem pi_clt_std_rect {K r : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    {O : ℕ → Type*} [∀ n, Fintype (O n)]
    (a Ns : ℕ → ℝ) (mx : ℕ → ℝ)
    (zc : ∀ n, J n → EuclideanSpace ℝ (Fin K)) (zt : ∀ n, O n → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, J n → Ω → ℝ) (eps : ∀ n, O n → Ω → ℝ)
    (vr : ∀ n, J n → ℝ) (sev : ∀ n, O n → ℝ) (C B Cs v0 : ℝ)
    (Ups : Matrix (Fin K) (Fin K) ℝ) (Sg : Matrix (Fin r) (Fin r) ℝ)
    (hUps : Ups.PosDef) (hSg : Sg.PosSemidef)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hindepη : ∀ n, iIndepFun (etab n) P)
    (hmeanη : ∀ n j, ∫ ω, etab n j ω ∂P = 0) (hL2η : ∀ n j, MemLp (etab n j) 2 P)
    (hint4η : ∀ n j, Integrable (fun ω => etab n j ω ^ 4) P)
    (hvarη : ∀ n j, Var[etab n j; P] = vr n j)
    (hmomη : ∀ n j, ∫ ω, etab n j ω ^ 4 ∂P ≤ C)
    (hv0 : 0 < v0) (hvr : ∀ n j, v0 ≤ vr n j)
    (hmeasε : ∀ n o, Measurable (eps n o)) (hindepε : ∀ n, iIndepFun (eps n) P)
    (hL2ε : ∀ n o, MemLp (eps n o) 2 P) (hmeanε : ∀ n o, ∫ ω, eps n o ω ∂P = 0)
    (hvarε : ∀ n o, Var[eps n o; P] = sev n o)
    (hsev0 : ∀ n o, 0 ≤ sev n o) (hsev : ∀ n o, sev n o ≤ Cs)
    (hzt : ∀ n o, ‖zt n o‖ ^ 2 ≤ B ^ 2)
    (hi : Tendsto (fun n : ℕ => a n ^ 2 * (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ n, 0 ≤ mx n) (hmx : ∀ n j, ‖zc n j‖ ^ 2 ≤ mx n)
    (hmxsum : ∀ n, mx n ≤ ∑ j, ‖zc n j‖ ^ 2)
    (hiv : Tendsto (fun n : ℕ => mx n / ∑ j, ‖zc n j‖ ^ 2) atTop (𝓝 0))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin r)))
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (hA : Tendsto A atTop (𝓝 Psiinv))
    (hsand : ∀ t : EuclideanSpace ℝ (Fin r),
      (ContinuousLinearMap.adjoint Psiinv t) ⬝ᵥ (Ups *ᵥ (ContinuousLinearMap.adjoint Psiinv t))
        = t ⬝ᵥ (Sg *ᵥ t))
    (dev : ℕ → Ω → EuclideanSpace ℝ (Fin r)) (hdevmeas : ∀ n, AEMeasurable (dev n) P)
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω, dev n ω
      = A n (a n • ((∑ j, etab n j ω • zc n j) + (∑ o, eps n o ω • zt n o)))) :
    TendstoInDistribution dev atTop
      (id : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r)) (fun _ => P)
      (multivariateGaussian 0 Sg) := by
  have hlin4 := lin4_of_cond_iv a zc vr mx v0 hv0 hvr Ups hiii hmx0 hmx hmxsum hiv
  have hW := pi_score_clt (P := P) a zc zt etab eps vr sev C B Cs Ups hUps hmeasη hindepη
    hmeanη hL2η hint4η hvarη hmomη hmeasε hindepε hL2ε hmeanε hvarε hzt hsev0 hsev hi hiii hlin4
  exact tendstoInDistribution_apply_of_solve_rect (P := P) hUps.posSemidef hSg hW hA hsand
    hdevmeas hsolve

end Rect

section Rect2
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Left composition by a fixed operator is continuous in the operator norm. -/
theorem tendsto_comp_const_left {K r : ℕ}
    (Rm : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin r))
    {A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))}
    {Ainf : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)}
    (hA : Tendsto A atTop (𝓝 Ainf)) :
    Tendsto (fun n => Rm.comp (A n)) atTop (𝓝 (Rm.comp Ainf)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (?_ : Tendsto (fun n => ‖Rm‖ * ‖A n - Ainf‖) atTop (𝓝 0))
  · have h : Rm.comp (A n) - Rm.comp Ainf = Rm.comp (A n - Ainf) := by
      ext x
      simp [ContinuousLinearMap.comp_apply]
    rw [h]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  · have h0 : Tendsto (fun n => ‖A n - Ainf‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hA
    simpa using h0.const_mul ‖Rm‖

/-- **Theorem 6** restricted through a fixed `𝓡`. -/
theorem pi_clt_std_restricted {K r : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    {O : ℕ → Type*} [∀ n, Fintype (O n)]
    (a Ns : ℕ → ℝ) (mx : ℕ → ℝ)
    (zc : ∀ n, J n → EuclideanSpace ℝ (Fin K)) (zt : ∀ n, O n → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, J n → Ω → ℝ) (eps : ∀ n, O n → Ω → ℝ)
    (vr : ∀ n, J n → ℝ) (sev : ∀ n, O n → ℝ) (C B Cs v0 : ℝ)
    (Ups : Matrix (Fin K) (Fin K) ℝ) (Sg : Matrix (Fin r) (Fin r) ℝ)
    (hUps : Ups.PosDef) (hSg : Sg.PosSemidef)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hindepη : ∀ n, iIndepFun (etab n) P)
    (hmeanη : ∀ n j, ∫ ω, etab n j ω ∂P = 0) (hL2η : ∀ n j, MemLp (etab n j) 2 P)
    (hint4η : ∀ n j, Integrable (fun ω => etab n j ω ^ 4) P)
    (hvarη : ∀ n j, Var[etab n j; P] = vr n j)
    (hmomη : ∀ n j, ∫ ω, etab n j ω ^ 4 ∂P ≤ C)
    (hv0 : 0 < v0) (hvr : ∀ n j, v0 ≤ vr n j)
    (hmeasε : ∀ n o, Measurable (eps n o)) (hindepε : ∀ n, iIndepFun (eps n) P)
    (hL2ε : ∀ n o, MemLp (eps n o) 2 P) (hmeanε : ∀ n o, ∫ ω, eps n o ω ∂P = 0)
    (hvarε : ∀ n o, Var[eps n o; P] = sev n o)
    (hsev0 : ∀ n o, 0 ≤ sev n o) (hsev : ∀ n o, sev n o ≤ Cs)
    (hzt : ∀ n o, ‖zt n o‖ ^ 2 ≤ B ^ 2)
    (hi : Tendsto (fun n : ℕ => a n ^ 2 * (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ n, 0 ≤ mx n) (hmx : ∀ n j, ‖zc n j‖ ^ 2 ≤ mx n)
    (hmxsum : ∀ n, mx n ≤ ∑ j, ‖zc n j‖ ^ 2)
    (hiv : Tendsto (fun n : ℕ => mx n / ∑ j, ‖zc n j‖ ^ 2) atTop (𝓝 0))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (Rm : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (hA : Tendsto A atTop (𝓝 Psiinv))
    (hsand : ∀ t : EuclideanSpace ℝ (Fin r),
      (ContinuousLinearMap.adjoint (Rm.comp Psiinv) t)
          ⬝ᵥ (Ups *ᵥ (ContinuousLinearMap.adjoint (Rm.comp Psiinv) t))
        = t ⬝ᵥ (Sg *ᵥ t))
    (pih : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (pi0 : EuclideanSpace ℝ (Fin K))
    (hpimeas : ∀ n, AEMeasurable (pih n) P)
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω, Real.sqrt (Ns n) • (pih n ω - pi0)
      = A n (a n • ((∑ j, etab n j ω • zc n j) + (∑ o, eps n o ω • zt n o)))) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (Ns n) • Rm (pih n ω - pi0)) atTop
      (id : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r)) (fun _ => P)
      (multivariateGaussian 0 Sg) := by
  refine pi_clt_std_rect a Ns mx zc zt etab eps vr sev C B Cs v0 Ups Sg hUps hSg
    hmeasη hindepη hmeanη hL2η hint4η hvarη hmomη hv0 hvr hmeasε hindepε hL2ε hmeanε hvarε
    hsev0 hsev hzt hi hiii hmx0 hmx hmxsum hiv
    (fun n => Rm.comp (A n)) (Rm.comp Psiinv) (tendsto_comp_const_left Rm hA) hsand
    (fun n ω => Real.sqrt (Ns n) • Rm (pih n ω - pi0)) ?_ ?_
  · intro n
    have hm : Measurable (fun x : EuclideanSpace ℝ (Fin K) => Real.sqrt (Ns n) • Rm x) := by
      fun_prop
    exact hm.comp_aemeasurable ((hpimeas n).sub_const pi0)
  · filter_upwards [hsolve] with n hn
    intro ω
    rw [← map_smul Rm, hn ω]
    rfl

end Rect2


/-! ## §11 The second moments, the rectangular bridge, and the unconditional limit

* §11a: `integral_r1Dist_mul` proves the second-moment identity
  `E[u_ou_{o'}] = ∑_m ς²_m 𝟙{i_m(o)=i_m(o')} + 𝟙{o=o'}σ²_ε(o)` under the Regime-1 model, by
  polarizing `integral_sq_linear_indep`; `piinf_a_of_regime1_full` is clause (a) with `hEu`
  and `hint` supplied.
* §11b: `matCLM` turns a matrix into a continuous linear map and `adjoint_matCLM` identifies the
  adjoint of `𝓡` with `𝓡'`; `piinf_wald_restricted_closed` is clause (b) at a rectangular `𝓡`
  with the central limit theorem supplied by `pi_clt_std_restricted`.
* §11c: `pi_clt_unconditional_of_design` and `pi_clt_std_unconditional_of_design` are Theorem 6
  unconditionally, for a `𝒟`-measurable design on a standard Borel space.
* §11d: `piinf_c_of_regime1` is clause (c) with `hEu` supplied, and `tendsto_ringInverse_of_psi`
  derives `hA` from `Ψ_n → Ψ ≻ 0`. -/

section PiEleven
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

variable {Ω : Type*} {mOm : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

section Polar
variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- Polarized form of `integral_sq_linear_indep`. -/
theorem integral_mul_linear_indep {ι : Type*} (X : ι → Ω → ℝ) (hX : iIndepFun X P)
    (hmem : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (s : Finset ι) (f g : ι → ℝ) :
    ∫ ω, (∑ i ∈ s, f i * X i ω) * (∑ i ∈ s, g i * X i ω) ∂P
      = ∑ i ∈ s, f i * g i * ∫ ω, (X i ω) ^ 2 ∂P := by
  classical
  have hmemS : ∀ h : ι → ℝ, MemLp (fun ω => ∑ i ∈ s, h i * X i ω) 2 P :=
    fun h => memLp_finsetSum s (fun i _ => (hmem i).const_mul (h i))
  have hpt : ∀ ω, (∑ i ∈ s, f i * X i ω) * (∑ i ∈ s, g i * X i ω)
      = ((∑ i ∈ s, (f i + g i) * X i ω) ^ 2
          - (∑ i ∈ s, (f i - g i) * X i ω) ^ 2) / 4 := by
    intro ω
    have h1 : ∑ i ∈ s, (f i + g i) * X i ω
        = (∑ i ∈ s, f i * X i ω) + (∑ i ∈ s, g i * X i ω) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i ∈ s, (f i - g i) * X i ω
        = (∑ i ∈ s, f i * X i ω) - (∑ i ∈ s, g i * X i ω) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
    integral_sub (hmemS _).integrable_sq (hmemS _).integrable_sq,
    integral_sq_linear_indep X hX hmem hmean s (fun i => f i + g i),
    integral_sq_linear_indep X hX hmem hmean s (fun i => f i - g i),
    ← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

end Polar

section Rep
variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `cellOf c A p` is a level-`A` cell. -/
theorem cellOf_mem_cells (c : D → O → L) (A : Finset D) (p : O) :
    cellOf c A p ∈ cells c A :=
  Finset.mem_image.2 ⟨p, Finset.mem_univ p, rfl⟩

/-- The coefficient vector of `u_p` in the disturbance array. -/
def r1CoefO (c : D → O → L) (p : O) : ((D × Finset O) ⊕ O) → ℝ :=
  Sum.elim (fun q => if q.2 = cellOf c ({q.1} : Finset D) p then (1 : ℝ) else 0)
    (fun o => if o = p then (1 : ℝ) else 0)

/-- `u_p` is the linear form with coefficients `r1CoefO c p` over the full site set. -/
theorem r1Dist_eq_linear (c : D → O → L) (dims : Finset D)
    (X : ((D × Finset O) ⊕ O) → ℝ) (p : O) :
    r1Dist c dims X p
      = ∑ i ∈ r1Sites c dims (Finset.univ : Finset O), r1CoefO c p i * X i := by
  classical
  rw [sum_r1Sites]
  have h1 : ∀ m' ∈ dims, (∑ t' ∈ cells c ({m'} : Finset D),
      r1CoefO c p (Sum.inl (m', t')) * X (Sum.inl (m', t')))
      = X (Sum.inl (m', cellOf c ({m'} : Finset D) p)) := by
    intro m' _
    rw [Finset.sum_eq_single (cellOf c ({m'} : Finset D) p)]
    · simp [r1CoefO]
    · intro b _ hb; simp [r1CoefO, hb]
    · intro h; exact absurd (cellOf_mem_cells c ({m'} : Finset D) p) h
  have h2 : (∑ o : O, r1CoefO c p (Sum.inr o) * X (Sum.inr o)) = X (Sum.inr p) := by
    rw [Finset.sum_eq_single p]
    · simp [r1CoefO]
    · intro b _ hb; simp [r1CoefO, hb]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [Finset.sum_congr rfl h1, h2]
  rfl

end Rep

section Eu
variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- **Step 5's second-moment identity** under the Regime-1 model. -/
theorem integral_r1Dist_mul (c : D → O → L) (dims : Finset D)
    (vr : D → ℝ) (sg : O → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hX : iIndepFun X P)
    (hmem : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hvarEta : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D),
      ∫ ω, (X (Sum.inl (m, t)) ω) ^ 2 ∂P = vr m ^ 2)
    (hvarEps : ∀ o, ∫ ω, (X (Sum.inr o) ω) ^ 2 ∂P = sg o ^ 2)
    (p q : O) :
    ∫ ω, r1Dist c dims (fun i => X i ω) p * r1Dist c dims (fun i => X i ω) q ∂P
      = omegaU c dims vr sg p q := by
  classical
  have hrw : ∀ ω, r1Dist c dims (fun i => X i ω) p * r1Dist c dims (fun i => X i ω) q
      = (∑ i ∈ r1Sites c dims (Finset.univ : Finset O), r1CoefO c p i * X i ω)
        * (∑ i ∈ r1Sites c dims (Finset.univ : Finset O), r1CoefO c q i * X i ω) := by
    intro ω
    rw [r1Dist_eq_linear c dims (fun i => X i ω) p, r1Dist_eq_linear c dims (fun i => X i ω) q]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
    integral_mul_linear_indep X hX hmem hmean _ (r1CoefO c p) (r1CoefO c q), sum_r1Sites]
  have hI : ∀ m' ∈ dims, (∑ t' ∈ cells c ({m'} : Finset D),
      r1CoefO c p (Sum.inl (m', t')) * r1CoefO c q (Sum.inl (m', t'))
        * ∫ ω, (X (Sum.inl (m', t')) ω) ^ 2 ∂P)
      = vr m' ^ 2 * (if c m' p = c m' q then (1 : ℝ) else 0) := by
    intro m' hm'
    rw [Finset.sum_eq_single (cellOf c ({m'} : Finset D) p)]
    · rw [hvarEta m' hm' _ (cellOf_mem_cells c ({m'} : Finset D) p)]
      by_cases h : c m' p = c m' q
      · have hc : cellOf c ({m'} : Finset D) p = cellOf c ({m'} : Finset D) q :=
          cellOf_eq_iff.2 ((sameOn_singleton c m' p q).2 h)
        simp [r1CoefO, hc, h]
      · have hc : ¬ (cellOf c ({m'} : Finset D) p = cellOf c ({m'} : Finset D) q) := by
          intro hc'; exact h ((sameOn_singleton c m' p q).1 (cellOf_eq_iff.1 hc'))
        simp [r1CoefO, hc, h]
    · intro b _ hb; simp [r1CoefO, hb]
    · intro h; exact absurd (cellOf_mem_cells c ({m'} : Finset D) p) h
  have hE : (∑ o : O, r1CoefO c p (Sum.inr o) * r1CoefO c q (Sum.inr o)
      * ∫ ω, (X (Sum.inr o) ω) ^ 2 ∂P) = if p = q then sg p ^ 2 else 0 := by
    rw [Finset.sum_eq_single p]
    · rw [hvarEps p]
      by_cases h : p = q <;> simp [r1CoefO, h]
    · intro b _ hb; simp [r1CoefO, hb]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [Finset.sum_congr rfl hI, hE]
  rfl

end Eu

section EuInt
variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `u_p` is square integrable. -/
theorem memLp_r1Dist (c : D → O → L) (dims : Finset D)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hmem : ∀ i, MemLp (X i) 2 P) (p : O) :
    MemLp (fun ω => r1Dist c dims (fun i => X i ω) p) 2 P := by
  classical
  have hrw : (fun ω => r1Dist c dims (fun i => X i ω) p)
      = fun ω => ∑ i ∈ r1Sites c dims (Finset.univ : Finset O), r1CoefO c p i * X i ω := by
    funext ω
    exact r1Dist_eq_linear c dims (fun i => X i ω) p
  rw [hrw]
  exact memLp_finsetSum _ (fun i _ => (hmem i).const_mul _)

/-- `u_pu_q` is integrable. -/
theorem integrable_r1Dist_mul (c : D → O → L) (dims : Finset D)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hmem : ∀ i, MemLp (X i) 2 P) (p q : O) :
    Integrable (fun ω => r1Dist c dims (fun i => X i ω) p
      * r1Dist c dims (fun i => X i ω) q) P :=
  (memLp_r1Dist c dims X hmem p).integrable_mul (memLp_r1Dist c dims X hmem q)

end EuInt

section Chain1
variable {Dn On Ln : ℕ → Type*}
  [∀ n, Fintype (On n)] [∀ n, DecidableEq (On n)]
  [∀ n, DecidableEq (Dn n)] [∀ n, DecidableEq (Ln n)]
variable [Fintype K] [DecidableEq K]

/-- **Theorem 12(a)** with Step 1 and the second-moment identity both supplied. -/
theorem piinf_a_of_regime1_full
    (c : ∀ n, Dn n → On n → Ln n) (dims : ∀ n, Finset (Dn n))
    (z : ∀ n, On n → K → ℝ) (v : ∀ n, Ω → On n → ℝ)
    (Pim : ∀ n, Matrix (On n) (On n) ℝ) (vr : ∀ n, Dn n → ℝ) (sg : ∀ n, On n → ℝ)
    (X : ∀ n, ((Dn n × Finset (On n)) ⊕ On n) → Ω → ℝ)
    {a b G : ℕ → ℝ} {B R Cvr Csg Mbar C4 A : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (hG : ∀ n, 1 ≤ G n)
    (hcard : ∀ n, 0 < (Fintype.card (On n) : ℝ))
    (hX : ∀ n, iIndepFun (X n) P)
    (hmem : ∀ n i, MemLp (X n i) 2 P)
    (hmem4 : ∀ n i, MemLp (fun ω => (X n i ω) ^ 2) 2 P)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hvarEta : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)),
      ∫ ω, (X n (Sum.inl (m, t)) ω) ^ 2 ∂P = vr n m ^ 2)
    (hvarEps : ∀ n o, ∫ ω, (X n (Sum.inr o) ω) ^ 2 ∂P = sg n o ^ 2)
    (hfour : ∀ n i, ∫ ω, (X n i ω) ^ 4 ∂P ≤ C4)
    (hz : ∀ n o, vecSqNorm (z n o) ≤ B ^ 2)
    (hb : ∀ n, ∀ e ∈ Finset.powersetCard 2 (dims n), ∀ t ∈ cells (c n) e, (t.card : ℝ) ≤ b n)
    (hcell : ∀ n, ∀ m ∈ dims n, ∀ t ∈ cells (c n) ({m} : Finset (Dn n)), (t.card : ℝ) ≤ G n)
    (hrate4 : Tendsto (fun n => step4Rate B (a n) (Fintype.card (On n) : ℝ)
      (((Finset.powersetCard 2 (dims n)).card : ℝ)) (b n)) atTop (𝓝 0))
    (hrate2 : Tendsto (fun n => step2Rate B (a n) ((dims n).card : ℝ) (G n)) atTop (𝓝 0))
    (hrem : Tendsto (fun n => step1RemRate B (a n) (Fintype.card (On n) : ℝ) Mbar (b n) Cvr Csg)
      atTop (𝓝 0))
    (hlead : Tendsto (fun n => (a n) ^ 2 * (C4 *
        ∑ m ∈ dims n, ∑ t ∈ cells (c n) ({m} : Finset (Dn n)),
          (vecSqNorm (cellVec (z n) t)) ^ 2)) atTop (𝓝 0))
    (hsym : ∀ n, (Pim n).transpose = Pim n) (hidem : ∀ n, Pim n * Pim n = Pim n)
    (htr : ∀ n, (Pim n).trace ≤ R) (hR : 0 ≤ R)
    (hw : ∀ n ω o, v n ω o - r1Dist (c n) (dims n) (fun i => X n i ω) o
      = -((Pim n).mulVec (r1Dist (c n) (dims n) (fun i => X n i ω)) o))
    (hvr : ∀ n m, vr n m ^ 2 ≤ Cvr) (hCvr : 0 ≤ Cvr)
    (hsg : ∀ n o, sg n o ^ 2 ≤ Csg) (hCsg : 0 ≤ Csg)
    (hM : ∀ n, (((dims n).card : ℕ) : ℝ) ≤ Mbar) (hMbar : 0 ≤ Mbar)
    (hA : ∀ n, a n * (upsilonN (c n) (dims n) (z n) (vr n)).trace ≤ A) :
    TendstoInMeasure P
      (fun n ω => frobNorm (a n • ieMeat (c n) (dims n) (z n) (v n ω)
        - a n • upsilonN (c n) (dims n) (z n) (vr n))) atTop (fun _ => 0) := by
  classical
  exact piinf_a_of_regime1 c dims z v Pim vr sg X ha0 hb0 hG hcard hX hmem hmem4 hmean
    hvarEta hvarEps hfour hz hb hcell hrate4 hrate2 hrem hlead hsym hidem htr hR hw
    (fun n p q => integrable_r1Dist_mul (c n) (dims n) (X n) (hmem n) p q)
    (fun n p q => integral_r1Dist_mul (c n) (dims n) (vr n) (sg n) (X n) (hX n) (hmem n)
      (hmean n) (hvarEta n) (hvarEps n) p q)
    hvr hCvr hsg hCsg hM hMbar hA

end Chain1

namespace Step5Witness
open Finset MeasureTheory ProbabilityTheory Filter Step1Model
open scoped Topology ENNReal

/-- The second-moment identity on the growing Rademacher model of §9. -/
theorem eu_witness :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Measure Om) (_ : IsProbabilityMeasure P)
      (X : ∀ n, ((Fin 2 × Finset (wO n)) ⊕ wO n) → Om → ℝ),
      (∀ n p q, ∫ ω, r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω) p
            * r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω) q ∂P
          = omegaU (wC n) (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
              (fun _ => (1 : ℝ)) p q)
      ∧ (∀ n (p : wO n), ∫ ω, r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω) p
            * r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω) p ∂P = 3)
      ∧ (∫ ω, r1Dist (wC 1) (Finset.univ : Finset (Fin 2)) (fun i => X 1 i ω) (0, 0)
            * r1Dist (wC 1) (Finset.univ : Finset (Fin 2)) (fun i => X 1 i ω) (0, 1) ∂P = 1)
      ∧ (∫ ω, r1Dist (wC 1) (Finset.univ : Finset (Fin 2)) (fun i => X 1 i ω) (0, 0)
            * r1Dist (wC 1) (Finset.univ : Finset (Fin 2)) (fun i => X 1 i ω) (1, 1) ∂P = 0) := by
  classical
  obtain ⟨Om, mOm, P, xi, hmeasx, hlawx, hindepx, hprobx⟩ :=
    exists_iid (Σ n : ℕ, ((Fin 2 × Finset (wO n)) ⊕ wO n)) CLT.Witness.rade
  have hmean : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      ∫ ω, xi ⟨n, i⟩ ω ∂P = 0 := by
    intro n i
    rw [(hlawx ⟨n, i⟩).integral_eq, CLT.Witness.integral_id_rade]
  have hmem : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n), MemLp (xi ⟨n, i⟩) 2 P :=
    fun n i => (hlawx ⟨n, i⟩).memLp CLT.Witness.memLp_id_rade
  have hsq : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      ∫ ω, (xi ⟨n, i⟩ ω) ^ 2 ∂P = 1 := by
    intro n i
    have h := (hlawx ⟨n, i⟩).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [show (∫ ω, (xi ⟨n, i⟩ ω) ^ 2 ∂P) = ∫ ω, ((fun x : ℝ => x ^ 2) ∘ (xi ⟨n, i⟩)) ω ∂P from rfl,
      h, integral_sq_rade]
  have hkey : ∀ (n : ℕ) (p q : wO n),
      ∫ ω, r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => xi ⟨n, i⟩ ω) p
          * r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => xi ⟨n, i⟩ ω) q ∂P
        = omegaU (wC n) (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)) p q := by
    intro n p q
    refine integral_r1Dist_mul (wC n) (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
      (fun _ => (1 : ℝ)) (fun i => xi ⟨n, i⟩)
      (hindepx.precomp (g := fun i => (⟨n, i⟩ : Σ n : ℕ, _)) sigma_mk_injective)
      (hmem n) (hmean n) (fun m _ t _ => ?_) (fun o => ?_) p q
    · rw [hsq n (Sum.inl (m, t))]; norm_num
    · rw [hsq n (Sum.inr o)]; norm_num
  refine ⟨Om, mOm, P, hprobx, fun n i => xi ⟨n, i⟩, hkey, fun n p => ?_, ?_, ?_⟩
  · rw [hkey n p p]
    simp [omegaU]
    norm_num
  · rw [hkey 1 (0, 0) (0, 1)]
    simp [omegaU, wC]
  · rw [hkey 1 (0, 0) (1, 1)]
    simp [omegaU, wC]

end Step5Witness

section Bridge
open Matrix
open scoped RealInnerProductSpace

/-- A rectangular matrix `𝓡` as a continuous linear map between Euclidean spaces. -/
noncomputable def matCLM {K r : ℕ} (Rmat : Matrix (Fin r) (Fin K) ℝ) :
    EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Rmat)

theorem matCLM_apply {K r : ℕ} (Rmat : Matrix (Fin r) (Fin K) ℝ)
    (x : EuclideanSpace ℝ (Fin K)) :
    matCLM Rmat x = (WithLp.toLp 2 (Rmat *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin r)) := rfl

/-- The adjoint of `𝓡` is `𝓡'`. -/
theorem adjoint_matCLM {K r : ℕ} (Rmat : Matrix (Fin r) (Fin K) ℝ) :
    ContinuousLinearMap.adjoint (matCLM Rmat) = matCLM Rmatᵀ := by
  have h : (Matrix.toEuclideanLin Rmatᵀ) = LinearMap.adjoint (Matrix.toEuclideanLin Rmat) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
  rw [matCLM, matCLM, h, LinearMap.adjoint_toContinuousLinearMap]

end Bridge

section RestrictedWald
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- **Theorem 12(b)** at a rectangular `𝓡`, with the central limit theorem in the output shape of
`pi_clt_std_restricted`. -/
theorem piinf_wald_of_meat_restricted_of_pi_clt {K r : ℕ}
    (Uh : ℕ → Ω → Matrix (Fin K) (Fin K) ℝ) (Ups : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (Gn : ℕ → Matrix (Fin K) (Fin K) ℝ) (Rmat : Matrix (Fin r) (Fin K) ℝ)
    {Ns : ℕ → ℝ} (hNs : ∀ n, 0 < Ns n)
    {Sg : Matrix (Fin r) (Fin r) ℝ} (hSg : Sg.PosDef)
    (hVherm : ∀ n ω, ((Ns n)⁻¹ • (Rmat * (Gn n * Uh n ω * Gn n) * Rmatᵀ)).IsHermitian)
    (hVmeas : ∀ n, Measurable fun ω => (Ns n)⁻¹ • (Rmat * (Gn n * Uh n ω * Gn n) * Rmatᵀ))
    {Lg Lr : ℝ} (hLg0 : 0 ≤ Lg) (hLr0 : 0 ≤ Lr)
    (hLg : ∀ n, frobNorm (Gn n) ≤ Lg) (hLr : rectFrobNorm Rmat ≤ Lr)
    (hdet : Tendsto (fun n => frobNorm (Rmat * (Gn n * Ups n * Gn n) * Rmatᵀ - Sg))
      atTop (𝓝 0))
    (ha0 : TendstoInMeasure P (fun n ω => frobNorm (Uh n ω - Ups n)) atTop (fun _ => 0))
    {pih : ℕ → Ω → EuclideanSpace ℝ (Fin K)} {pi0 : EuclideanSpace ℝ (Fin K)}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (Ns n) • matCLM Rmat (pih n ω - pi0)) atTop
      (id : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r)) (fun _ => P)
      (multivariateGaussian 0 Sg)) :
    Tendsto (fun n => P {ω | ((Ns n)⁻¹ • (Rmat * (Gn n * Uh n ω * Gn n) * Rmatᵀ)).PosDef})
        atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => Wald.waldStat ((Ns n)⁻¹ • (Rmat * (Gn n * Uh n ω * Gn n) * Rmatᵀ))
            (matCLM Rmat (pih n ω - pi0))) atTop
          (fun z : EuclideanSpace ℝ (Fin r) => ‖z‖ ^ 2) (fun _ => P)
          (multivariateGaussian 0 1) :=
  piinf_wald_of_meat_restricted (Kq := fun _ => Fin K) (P := P)
    (P' := multivariateGaussian 0 Sg) Uh Ups Gn (fun _ => Rmat) hNs hSg
    hVherm hVmeas hLg0 hLr0 hLg (fun _ => hLr) hdet ha0
    (x := fun n ω => matCLM Rmat (pih n ω - pi0)) hCLT Measure.map_id

end RestrictedWald

section RestrictedClosed
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

/-- **Theorem 12(b)** at a rectangular `𝓡`, with the central limit theorem supplied by
`pi_clt_std_restricted`. -/
theorem piinf_wald_restricted_closed {K r : ℕ} {J : ℕ → Type*} [∀ n, Fintype (J n)]
    {O : ℕ → Type*} [∀ n, Fintype (O n)]
    (a Ns : ℕ → ℝ) (mx : ℕ → ℝ)
    (zc : ∀ n, J n → EuclideanSpace ℝ (Fin K)) (zt : ∀ n, O n → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, J n → Ω → ℝ) (eps : ∀ n, O n → Ω → ℝ)
    (vr : ∀ n, J n → ℝ) (sev : ∀ n, O n → ℝ) (C B Cs v0 : ℝ)
    (Ups : Matrix (Fin K) (Fin K) ℝ) (Sg : Matrix (Fin r) (Fin r) ℝ)
    (hUps : Ups.PosDef) (hSgPD : Sg.PosDef)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hindepη : ∀ n, iIndepFun (etab n) P)
    (hmeanη : ∀ n j, ∫ ω, etab n j ω ∂P = 0) (hL2η : ∀ n j, MemLp (etab n j) 2 P)
    (hint4η : ∀ n j, Integrable (fun ω => etab n j ω ^ 4) P)
    (hvarη : ∀ n j, Var[etab n j; P] = vr n j)
    (hmomη : ∀ n j, ∫ ω, etab n j ω ^ 4 ∂P ≤ C)
    (hv0 : 0 < v0) (hvr : ∀ n j, v0 ≤ vr n j)
    (hmeasε : ∀ n o, Measurable (eps n o)) (hindepε : ∀ n, iIndepFun (eps n) P)
    (hL2ε : ∀ n o, MemLp (eps n o) 2 P) (hmeanε : ∀ n o, ∫ ω, eps n o ω ∂P = 0)
    (hvarε : ∀ n o, Var[eps n o; P] = sev n o)
    (hsev0 : ∀ n o, 0 ≤ sev n o) (hsev : ∀ n o, sev n o ≤ Cs)
    (hzt : ∀ n o, ‖zt n o‖ ^ 2 ≤ B ^ 2)
    (hi : Tendsto (fun n : ℕ => a n ^ 2 * (Fintype.card (O n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => a n ^ 2 * ∑ j, ⟪zc n j, t⟫ ^ 2 * vr n j) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ n, 0 ≤ mx n) (hmx : ∀ n j, ‖zc n j‖ ^ 2 ≤ mx n)
    (hmxsum : ∀ n, mx n ≤ ∑ j, ‖zc n j‖ ^ 2)
    (hiv : Tendsto (fun n : ℕ => mx n / ∑ j, ‖zc n j‖ ^ 2) atTop (𝓝 0))
    (A : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)))
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (Rmat : Matrix (Fin r) (Fin K) ℝ)
    (hA : Tendsto A atTop (𝓝 Psiinv))
    (hsand : ∀ t : EuclideanSpace ℝ (Fin r),
      (ContinuousLinearMap.adjoint ((matCLM Rmat).comp Psiinv) t)
          ⬝ᵥ (Ups *ᵥ (ContinuousLinearMap.adjoint ((matCLM Rmat).comp Psiinv) t))
        = t ⬝ᵥ (Sg *ᵥ t))
    (pih : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (pi0 : EuclideanSpace ℝ (Fin K))
    (hpimeas : ∀ n, AEMeasurable (pih n) P)
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω, Real.sqrt (Ns n) • (pih n ω - pi0)
      = A n (a n • ((∑ j, etab n j ω • zc n j) + (∑ o, eps n o ω • zt n o))))
    (Uh : ℕ → Ω → Matrix (Fin K) (Fin K) ℝ) (Upn : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (Gn : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (hNs : ∀ n, 0 < Ns n)
    (hVherm : ∀ n ω, ((Ns n)⁻¹ • (Rmat * (Gn n * Uh n ω * Gn n) * Rmatᵀ)).IsHermitian)
    (hVmeas : ∀ n, Measurable fun ω => (Ns n)⁻¹ • (Rmat * (Gn n * Uh n ω * Gn n) * Rmatᵀ))
    {Lg Lr : ℝ} (hLg0 : 0 ≤ Lg) (hLr0 : 0 ≤ Lr)
    (hLg : ∀ n, frobNorm (Gn n) ≤ Lg) (hLr : rectFrobNorm Rmat ≤ Lr)
    (hdet : Tendsto (fun n => frobNorm (Rmat * (Gn n * Upn n * Gn n) * Rmatᵀ - Sg))
      atTop (𝓝 0))
    (ha0 : TendstoInMeasure P (fun n ω => frobNorm (Uh n ω - Upn n)) atTop (fun _ => 0)) :
    Tendsto (fun n => P {ω | ((Ns n)⁻¹ • (Rmat * (Gn n * Uh n ω * Gn n) * Rmatᵀ)).PosDef})
        atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => Wald.waldStat ((Ns n)⁻¹ • (Rmat * (Gn n * Uh n ω * Gn n) * Rmatᵀ))
            (matCLM Rmat (pih n ω - pi0))) atTop
          (fun z : EuclideanSpace ℝ (Fin r) => ‖z‖ ^ 2) (fun _ => P)
          (multivariateGaussian 0 1) :=
  piinf_wald_of_meat_restricted_of_pi_clt Uh Upn Gn Rmat hNs hSgPD hVherm hVmeas
    hLg0 hLr0 hLg hLr hdet ha0
    (pi_clt_std_restricted a Ns mx zc zt etab eps vr sev C B Cs v0 Ups Sg hUps hSgPD.posSemidef
      hmeasη hindepη hmeanη hL2η hint4η hvarη hmomη hv0 hvr hmeasε hindepε hL2ε hmeanε hvarε
      hsev0 hsev hzt hi hiii hmx0 hmx hmxsum hiv A Psiinv (matCLM Rmat) hA hsand pih pi0
      hpimeas hsolve)

end RestrictedClosed

section DesignDecond
open CLTMartingale.CondD Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

variable {Om : Type*} {𝒟 : MeasurableSpace Om} [mOm2 : MeasurableSpace Om] [StandardBorelSpace Om]

/-- **Theorem 6**, unconditional, for a `𝒟`-measurable design. -/
theorem pi_clt_unconditional_of_design {K : ℕ}
    (h𝒟 : 𝒟 ≤ mOm2) (P : Measure Om) [IsProbabilityMeasure P]
    [∀ ω : Om, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Ns : ℕ → ℝ) (pi0 : EuclideanSpace ℝ (Fin K))
    (Ups : Matrix (Fin K) (Fin K) ℝ)
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    {γ : Type*} [MeasurableSpace γ] [MeasurableEq γ]
    {D : ℕ → Om → γ} (hD : ∀ n, Measurable[𝒟] (D n))
    {F : ℕ → γ → Om → EuclideanSpace ℝ (Fin K)}
    (hF : ∀ n, Measurable (Function.uncurry (F n)))
    {pih : ℕ → Om → EuclideanSpace ℝ (Fin K)}
    (hpi : ∀ n ω, Real.sqrt (Ns n) • (pih n ω - pi0) = F n (D n ω) ω)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mOm2)
      (fun (n : ℕ) (y : Om) => F n (D n ω) y) atTop
      (fun z => Psiinv z) (fun _ => condExpKernel P 𝒟 ω) (multivariateGaussian 0 Ups)) :
    TendstoInDistribution (m := fun _ : ℕ => mOm2)
      (fun (n : ℕ) ω => Real.sqrt (Ns n) • (pih n ω - pi0)) atTop
      (fun z => Psiinv z) (fun _ => P) (multivariateGaussian 0 Ups) :=
  tendstoInDistribution_of_design (E := EuclideanSpace ℝ (Fin K)) h𝒟 P hD hF hpi
    Psiinv.continuous.measurable.aemeasurable hfrozen

/-- **Theorem 6** in standard form, unconditional, for a `𝒟`-measurable design. -/
theorem pi_clt_std_unconditional_of_design {K : ℕ}
    (h𝒟 : 𝒟 ≤ mOm2) (P : Measure Om) [IsProbabilityMeasure P]
    [∀ ω : Om, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Ns : ℕ → ℝ) (pi0 : EuclideanSpace ℝ (Fin K))
    (Sg : Matrix (Fin K) (Fin K) ℝ)
    {γ : Type*} [MeasurableSpace γ] [MeasurableEq γ]
    {D : ℕ → Om → γ} (hD : ∀ n, Measurable[𝒟] (D n))
    {F : ℕ → γ → Om → EuclideanSpace ℝ (Fin K)}
    (hF : ∀ n, Measurable (Function.uncurry (F n)))
    {pih : ℕ → Om → EuclideanSpace ℝ (Fin K)}
    (hpi : ∀ n ω, Real.sqrt (Ns n) • (pih n ω - pi0) = F n (D n ω) ω)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mOm2)
      (fun (n : ℕ) (y : Om) => F n (D n ω) y) atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
      (fun _ => condExpKernel P 𝒟 ω) (multivariateGaussian 0 Sg)) :
    TendstoInDistribution (m := fun _ : ℕ => mOm2)
      (fun (n : ℕ) ω => Real.sqrt (Ns n) • (pih n ω - pi0)) atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Sg) :=
  tendstoInDistribution_of_design (E := EuclideanSpace ℝ (Fin K)) h𝒟 P hD hF hpi
    aemeasurable_id hfrozen

end DesignDecond

namespace RectWitness
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- A rectangular restriction, `r = 1 < 2 = K`: the first coordinate. -/
def wR : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

/-- The identity on the unrestricted space, standing for `Ψ⁻¹`. -/
noncomputable abbrev wPsi : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))

/-- The `𝓡`-specific hypotheses of the rectangular chain are jointly satisfiable at `r < K`. -/
theorem rect_bridge_witness :
    (ContinuousLinearMap.adjoint (matCLM wR) = matCLM wRᵀ)
      ∧ (∀ t : EuclideanSpace ℝ (Fin 1),
          (ContinuousLinearMap.adjoint ((matCLM wR).comp wPsi) t)
              ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
                (ContinuousLinearMap.adjoint ((matCLM wR).comp wPsi) t))
            = t ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ t))
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef
      ∧ ∃ x : EuclideanSpace ℝ (Fin 2), x ≠ 0 ∧ matCLM wR x = 0 := by
  refine ⟨adjoint_matCLM wR, ?_, Matrix.PosDef.one, ?_⟩
  · intro t
    have hcomp : (matCLM wR).comp wPsi = matCLM wR := ContinuousLinearMap.comp_id _
    rw [hcomp, adjoint_matCLM]
    have hval : ∀ i : Fin 2, (matCLM wRᵀ t : EuclideanSpace ℝ (Fin 2)) i
        = if i = 0 then t 0 else 0 := by
      intro i
      rw [matCLM_apply]
      fin_cases i <;> simp [wR, Matrix.mulVec, dotProduct]
    simp only [Matrix.one_mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_one, hval]
    norm_num
  · refine ⟨WithLp.toLp 2 ![0, 1], ?_, ?_⟩
    · intro h
      have := congrFun (congrArg WithLp.ofLp h) 1
      simp at this
    · rw [matCLM_apply]
      ext i
      fin_cases i
      simp [wR, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end RectWitness


section CondTwo
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

/-- Condition (ii) of Theorem 6, `Ψ_n → Ψ ≻ 0`, gives the hypothesis `hA` of `pi_clt`. -/
theorem tendsto_ringInverse_of_psi {K : ℕ}
    {Psi : ℕ → (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))}
    {Psilim : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)}
    (hPsi : Tendsto Psi atTop (𝓝 Psilim))
    (hpd : ∀ a : EuclideanSpace ℝ (Fin K), a ≠ 0 → 0 < ⟪a, Psilim a⟫) :
    Tendsto (fun n => Ring.inverse (Psi n)) atTop (𝓝 (Ring.inverse Psilim)) :=
  CLT.tendsto_inverse hPsi (CLT.isUnit_of_inner_pos hpd)

end CondTwo

section ClauseCRegime1
open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]

/-- **Theorem 12(c)** under the Regime-1 model, with the second-moment identity supplied. -/
theorem piinf_c_of_regime1 (c : D → O → L) (dims : Finset D) (hdims : dims.Nonempty)
    (z : O → K → ℝ) (vr : D → ℝ) (sg : O → ℝ)
    (X : ((D × Finset O) ⊕ O) → Ω → ℝ) (hX : iIndepFun X P)
    (hmem : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hvarEta : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D),
      ∫ ω, (X (Sum.inl (m, t)) ω) ^ 2 ∂P = vr m ^ 2)
    (hvarEps : ∀ o, ∫ ω, (X (Sum.inr o) ω) ^ 2 ∂P = sg o ^ 2) :
    ieMeatKer c dims z (fun o o' => ∫ ω, r1Dist c dims (fun i => X i ω) o
        * r1Dist c dims (fun i => X i ω) o' ∂P)
        = condVarScore z (fun o o' => ∫ ω, r1Dist c dims (fun i => X i ω) o
            * r1Dist c dims (fun i => X i ω) o' ∂P)
      ∧ condVarScore z (fun o o' => ∫ ω, r1Dist c dims (fun i => X i ω) o
            * r1Dist c dims (fun i => X i ω) o' ∂P)
          = upsilonN c dims z vr + ∑ o : O, (sg o ^ 2) • Matrix.vecMulVec (z o) (z o) :=
  piinf_c c dims hdims z _ vr sg
    (fun o o' => integral_r1Dist_mul c dims vr sg X hX hmem hmean hvarEta hvarEps o o')

end ClauseCRegime1

end PiEleven

/-! ## §12 End-to-end witnesses

* `piinf_a_regime1_full_witness`: `piinf_a_of_regime1_full` on the balanced two-way grid
  `Fin(n+1) × Fin(n+1)` with an i.i.d. Rademacher array and the demeaning projector
  `P_n = N_n^{-1}J`, where `a_n tr(Υ_n) = 2` at every index.
* `piinf_wald_restricted_closed_witness`: `piinf_wald_restricted_closed` at `K = 2`, `r = 1`,
  with `(n+1)²·2` categories, `(n+1)³` observations, `Υ = I₂`, `Ψ̂^{-1} = 2I₂`, `𝓡 = (1  0)` and
  a random meat estimator with `‖Υ̂_n - Υ_n‖_F = (n+1)^{-1}√2/4`. -/

section PiTwelve
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace Step1Model

/-- The demeaning projector `P_n = N_n^{-1}J` on the grid of design `n`. -/
noncomputable def wPi (n : ℕ) : Matrix (wO n) (wO n) ℝ :=
  Matrix.of fun _ _ => (((n : ℝ) + 1) ^ 2)⁻¹

theorem card_univ_wO (n : ℕ) :
    ((Finset.univ : Finset (wO n)).card : ℝ) = ((n : ℝ) + 1) ^ 2 := by
  rw [Finset.card_univ]
  exact wCard n

theorem wPi_transpose (n : ℕ) : (wPi n).transpose = wPi n := by
  ext i j
  rfl

theorem wPi_idem (n : ℕ) : wPi n * wPi n = wPi n := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [wPi, Matrix.of_apply]
  rw [Finset.sum_const, nsmul_eq_mul, card_univ_wO]
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem wPi_trace (n : ℕ) : (wPi n).trace = 1 := by
  show (∑ i : wO n, wPi n i i) = 1
  simp only [wPi, Matrix.of_apply]
  rw [Finset.sum_const, nsmul_eq_mul, card_univ_wO]
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- `P_n ≠ 0`. -/
theorem wPi_ne_zero (n : ℕ) : wPi n ≠ 0 := by
  intro h
  have h0 : ((((n : ℝ) + 1) ^ 2)⁻¹) = 0 := by
    have := congrFun (congrFun h ((0 : Fin (n + 1)), (0 : Fin (n + 1))))
      ((0 : Fin (n + 1)), (0 : Fin (n + 1)))
    simpa [wPi] using this
  have hne : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  exact hne (inv_eq_zero.1 h0)

/-- The residualized disturbance `ṽ = (I - P_n)u`. -/
noncomputable def wResid (n : ℕ) (u : wO n → ℝ) : wO n → ℝ :=
  fun o => u o - ((wPi n).mulVec u) o

theorem wRate4 (n : ℕ) :
    step4Rate 1 (wA n) (Fintype.card (wO n) : ℝ)
      (((Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))).card : ℝ)) 1
      = 1 / ((n : ℝ) + 1) := by
  have hp : ((Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))).card : ℝ) = 1 := by
    simp
  rw [step4Rate, wCard, wA, hp]
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem wRate2 (n : ℕ) :
    step2Rate 1 (wA n) (((Finset.univ : Finset (Fin 2)).card : ℝ)) ((n : ℝ) + 1)
      = 2 / ((n : ℝ) + 1) := by
  rw [step2Rate, wA]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- `piinf_a_of_regime1_full` on the balanced two-way grid. -/
theorem piinf_a_regime1_full_witness :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Measure Om) (_ : IsProbabilityMeasure P)
      (X : ∀ n, ((Fin 2 × Finset (wO n)) ⊕ wO n) → Om → ℝ),
      TendstoInMeasure P
        (fun n ω => frobNorm
          (wA n • ieMeat (wC n) (Finset.univ : Finset (Fin 2)) (wZ n)
              (wResid n (r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω)))
            - wA n • upsilonN (wC n) (Finset.univ : Finset (Fin 2)) (wZ n) (fun _ => (1 : ℝ))))
        atTop (fun _ => 0)
      ∧ (∀ n, wA n
          * (upsilonN (wC n) (Finset.univ : Finset (Fin 2)) (wZ n) (fun _ => (1 : ℝ))).trace = 2)
      ∧ (∀ n, (Fintype.card (wO n) : ℝ) = ((n : ℝ) + 1) ^ 2)
      ∧ (∀ n, ∀ d : Fin 2, ∀ t ∈ cells (wC n) ({d} : Finset (Fin 2)), t.card = n + 1)
      ∧ (∀ n, ∀ e ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)),
          ∀ t ∈ cells (wC n) e, t.card = 1)
      ∧ (∀ n, (wPi n).trace = 1 ∧ wPi n ≠ 0)
      ∧ (∀ n p q, ∫ ω, r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω) p
            * r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω) q ∂P
          = omegaU (wC n) (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
              (fun _ => (1 : ℝ)) p q)
      ∧ (∀ n (p : wO n), ∫ ω, r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω) p
            * r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => X n i ω) p ∂P = 3)
      ∧ (∫ ω, r1Dist (wC 1) (Finset.univ : Finset (Fin 2)) (fun i => X 1 i ω) (0, 0)
            * r1Dist (wC 1) (Finset.univ : Finset (Fin 2)) (fun i => X 1 i ω) (0, 1) ∂P = 1)
      ∧ (∫ ω, r1Dist (wC 1) (Finset.univ : Finset (Fin 2)) (fun i => X 1 i ω) (0, 0)
            * r1Dist (wC 1) (Finset.univ : Finset (Fin 2)) (fun i => X 1 i ω) (1, 1) ∂P = 0) := by
  classical
  obtain ⟨Om, mOm, P, xi, hmeasx, hlawx, hindepx, hprobx⟩ :=
    exists_iid (Σ n : ℕ, ((Fin 2 × Finset (wO n)) ⊕ wO n)) CLT.Witness.rade
  have hmean : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      ∫ ω, xi ⟨n, i⟩ ω ∂P = 0 := by
    intro n i
    rw [(hlawx ⟨n, i⟩).integral_eq, CLT.Witness.integral_id_rade]
  have hmem : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n), MemLp (xi ⟨n, i⟩) 2 P :=
    fun n i => (hlawx ⟨n, i⟩).memLp CLT.Witness.memLp_id_rade
  have hint4 : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      Integrable (fun ω => (xi ⟨n, i⟩ ω) ^ 4) P :=
    fun n i => (hlawx ⟨n, i⟩).integrable_fun_comp CLT.Witness.integrable_pow4_rade
  have hmem4 : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      MemLp (fun ω => (xi ⟨n, i⟩ ω) ^ 2) 2 P := by
    intro n i
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    refine (hint4 n i).congr ?_
    filter_upwards with ω
    show (xi ⟨n, i⟩ ω) ^ 4 = ((xi ⟨n, i⟩ ω) ^ 2) ^ 2
    ring
  have hsq : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      ∫ ω, (xi ⟨n, i⟩ ω) ^ 2 ∂P = 1 := by
    intro n i
    have h := (hlawx ⟨n, i⟩).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [show (∫ ω, (xi ⟨n, i⟩ ω) ^ 2 ∂P) = ∫ ω, ((fun x : ℝ => x ^ 2) ∘ (xi ⟨n, i⟩)) ω ∂P from rfl,
      h, integral_sq_rade]
  have hfour : ∀ (n : ℕ) (i : (Fin 2 × Finset (wO n)) ⊕ wO n),
      ∫ ω, (xi ⟨n, i⟩ ω) ^ 4 ∂P ≤ 1 := by
    intro n i
    have h := (hlawx ⟨n, i⟩).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [show (∫ ω, (xi ⟨n, i⟩ ω) ^ 4 ∂P) = ∫ ω, ((fun x : ℝ => x ^ 4) ∘ (xi ⟨n, i⟩)) ω ∂P from rfl,
      h, CLT.Witness.integral_pow4_rade]
  have hindep : ∀ n : ℕ, iIndepFun (fun i : (Fin 2 × Finset (wO n)) ⊕ wO n => xi ⟨n, i⟩) P :=
    fun n => hindepx.precomp (g := fun i => (⟨n, i⟩ : Σ n : ℕ, _)) sigma_mk_injective
  have hkey : ∀ (n : ℕ) (p q : wO n),
      ∫ ω, r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => xi ⟨n, i⟩ ω) p
          * r1Dist (wC n) (Finset.univ : Finset (Fin 2)) (fun i => xi ⟨n, i⟩ ω) q ∂P
        = omegaU (wC n) (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)) p q := by
    intro n p q
    refine integral_r1Dist_mul (wC n) (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
      (fun _ => (1 : ℝ)) (fun i => xi ⟨n, i⟩) (hindep n) (hmem n) (hmean n)
      (fun m _ t _ => ?_) (fun o => ?_) p q
    · rw [hsq n (Sum.inl (m, t))]; norm_num
    · rw [hsq n (Sum.inr o)]; norm_num
  have hrem : Tendsto (fun n : ℕ => step1RemRate 1 (wA n) (Fintype.card (wO n) : ℝ) 2 1 1 1)
      atTop (𝓝 0) := by
    have he : (fun n : ℕ => step1RemRate 1 (wA n) (Fintype.card (wO n) : ℝ) 2 1 1 1)
        = fun n : ℕ => 6 / ((n : ℝ) + 1) := funext wRemRate
    rw [he]
    exact tendsto_const_div 6
  have hlead : Tendsto (fun n : ℕ => (wA n) ^ 2 * (1 *
      ∑ m ∈ (Finset.univ : Finset (Fin 2)),
        ∑ t ∈ cells (wC n) ({m} : Finset (Fin 2)),
          (vecSqNorm (cellVec (wZ n) t)) ^ 2)) atTop (𝓝 0) := by
    have he : (fun n : ℕ => (wA n) ^ 2 * (1 *
        ∑ m ∈ (Finset.univ : Finset (Fin 2)),
          ∑ t ∈ cells (wC n) ({m} : Finset (Fin 2)),
            (vecSqNorm (cellVec (wZ n) t)) ^ 2))
        = fun n : ℕ => 2 / ((n : ℝ) + 1) := funext wLeadRate
    rw [he]
    exact tendsto_const_div 2
  have hrate4 : Tendsto (fun n : ℕ => step4Rate 1 (wA n) (Fintype.card (wO n) : ℝ)
      (((Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))).card : ℝ)) 1) atTop (𝓝 0) := by
    have he : (fun n : ℕ => step4Rate 1 (wA n) (Fintype.card (wO n) : ℝ)
        (((Finset.powersetCard 2 (Finset.univ : Finset (Fin 2))).card : ℝ)) 1)
        = fun n : ℕ => 1 / ((n : ℝ) + 1) := funext wRate4
    rw [he]
    exact tendsto_const_div 1
  have hrate2 : Tendsto (fun n : ℕ => step2Rate 1 (wA n)
      (((Finset.univ : Finset (Fin 2)).card : ℝ)) ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have he : (fun n : ℕ => step2Rate 1 (wA n)
        (((Finset.univ : Finset (Fin 2)).card : ℝ)) ((n : ℝ) + 1))
        = fun n : ℕ => 2 / ((n : ℝ) + 1) := funext wRate2
    rw [he]
    exact tendsto_const_div 2
  refine ⟨Om, mOm, P, hprobx, fun n i => xi ⟨n, i⟩, ?_, wA_trace, wCard,
    fun n d t ht => wCell_card n d ht, fun n e he t ht => wPair_card n he ht,
    fun n => ⟨wPi_trace n, wPi_ne_zero n⟩, hkey, ?_, ?_, ?_⟩
  · exact piinf_a_of_regime1_full (P := P) (K := Fin 1) wC (fun _ => Finset.univ) wZ
      (fun n ω => wResid n (r1Dist (wC n) (Finset.univ : Finset (Fin 2))
        (fun i => xi ⟨n, i⟩ ω)))
      wPi (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) (fun n i => xi ⟨n, i⟩)
      (B := 1) (R := 1) (Cvr := 1) (Csg := 1) (Mbar := 2) (C4 := 1) (A := 2)
      (a := wA) (b := fun _ => 1) (G := fun n => (n : ℝ) + 1)
      wA_nonneg (fun _ => zero_le_one)
      (fun n => by have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
      (fun n => by rw [wCard]; positivity)
      hindep hmem hmem4 hmean
      (fun n m _ t _ => by rw [hsq n (Sum.inl (m, t))]; norm_num)
      (fun n o => by rw [hsq n (Sum.inr o)]; norm_num)
      hfour
      (fun n o => by rw [wVecSqNorm_z]; norm_num)
      (fun n e he t ht => by rw [wPair_card n he ht]; norm_num)
      (fun n m _ t ht => by rw [wCell_card n m ht]; push_cast; exact le_rfl)
      hrate4 hrate2 hrem hlead
      wPi_transpose wPi_idem (fun n => le_of_eq (wPi_trace n)) zero_le_one
      (fun n ω o => by simp [wResid])
      (fun _ _ => by norm_num) zero_le_one
      (fun _ _ => by norm_num) zero_le_one
      (fun _ => by simp) (by norm_num)
      (fun n => le_of_eq (wA_trace n))
  · intro n p
    rw [hkey n p p]
    simp [omegaU]
    norm_num
  · rw [hkey 1 (0, 0) (0, 1)]
    simp [omegaU, wC]
  · rw [hkey 1 (0, 0) (1, 1)]
    simp [omegaU, wC]

end Step1Model

namespace RectDesign

theorem frobNorm_one_fin_two : frobNorm (1 : Matrix (Fin 2) (Fin 2) ℝ) = Real.sqrt 2 := by
  rw [frobNorm]
  congr 1
  simp [frobSq, Matrix.one_apply]

/-- The category index of design `n` at `K = 2`: `(n+1)²` categories along each coordinate
direction. -/
abbrev rJ (n : ℕ) : Type := Fin ((n + 1) ^ 2) × Fin 2

/-- The observations of design `n`. -/
abbrev rO (n : ℕ) : Type := Fin ((n + 1) ^ 3)

/-- `N_*` as a real. -/
noncomputable def rNs (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2

/-- `√N_*/n`. -/
noncomputable def ra (n : ℕ) : ℝ := (((n : ℝ) + 1) ^ 2)⁻¹

/-- `max_j ‖z_j‖²`. -/
noncomputable def rmx (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2

/-- The category weight, of length `n+1` along coordinate `j.2`. -/
noncomputable def rzc (n : ℕ) (j : rJ n) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun k => if k = j.2 then ((n : ℝ) + 1) else 0)

/-- The observation row, the all-ones vector of `ℝ²`. -/
noncomputable def rzt (n : ℕ) (_ : rO n) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

theorem sqrt_rNs (n : ℕ) : Real.sqrt (rNs n) = (n : ℝ) + 1 := by
  rw [rNs, Real.sqrt_sq (by positivity)]

theorem inner_rzc (n : ℕ) (j : rJ n) (t : EuclideanSpace ℝ (Fin 2)) :
    ⟪rzc n j, t⟫ = ((n : ℝ) + 1) * t j.2 := by
  simp [rzc, PiLp.inner_apply, mul_comm]

theorem norm_sq_rzc (n : ℕ) (j : rJ n) : ‖rzc n j‖ ^ 2 = ((n : ℝ) + 1) ^ 2 := by
  rw [euclidean_norm_sq, Finset.sum_eq_single j.2]
  · simp [rzc]
  · intro b _ hb; simp [rzc, hb]
  · intro h; exact absurd (Finset.mem_univ j.2) h

theorem norm_sq_rzt (n : ℕ) (o : rO n) : ‖rzt n o‖ ^ 2 = 2 := by
  rw [euclidean_norm_sq]
  simp [rzt]

theorem sum_inner_sq_rzc (n : ℕ) (t : EuclideanSpace ℝ (Fin 2)) :
    ∑ j : rJ n, ⟪rzc n j, t⟫ ^ 2 * (1 : ℝ) = ((n : ℝ) + 1) ^ 4 * (t 0 ^ 2 + t 1 ^ 2) := by
  have h : ∀ j : rJ n, ⟪rzc n j, t⟫ ^ 2 * (1 : ℝ) = (((n : ℝ) + 1) * t j.2) ^ 2 := by
    intro j; rw [inner_rzc, mul_one]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h j, Fintype.sum_prod_type]
  have hd : ∀ _i : Fin ((n + 1) ^ 2), (∑ d : Fin 2, (((n : ℝ) + 1) * t d) ^ 2)
      = ((n : ℝ) + 1) ^ 2 * (t 0 ^ 2 + t 1 ^ 2) := by
    intro _i
    rw [Fin.sum_univ_two]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hd i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem sum_norm_sq_rzc (n : ℕ) : ∑ j : rJ n, ‖rzc n j‖ ^ 2 = 2 * ((n : ℝ) + 1) ^ 4 := by
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => norm_sq_rzc n j, Finset.sum_const,
    Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Condition (iii) holds exactly at every `n`, with limit `Υ = I₂ ≻ 0`. -/
theorem upsilon_exact (n : ℕ) (t : EuclideanSpace ℝ (Fin 2)) :
    ra n ^ 2 * ∑ j : rJ n, ⟪rzc n j, t⟫ ^ 2 * (1 : ℝ) = t 0 ^ 2 + t 1 ^ 2 := by
  rw [sum_inner_sq_rzc, ra]
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem dotProduct_one_fin_two (t : EuclideanSpace ℝ (Fin 2)) :
    (t : EuclideanSpace ℝ (Fin 2)) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ t)
      = t 0 ^ 2 + t 1 ^ 2 := by
  rw [Matrix.one_mulVec]
  simp only [dotProduct, Fin.sum_univ_two]
  ring

/-- `matCLM 𝓡` is not injective. -/
theorem matCLM_wRestrict_not_injective :
    ∃ x : EuclideanSpace ℝ (Fin 2), x ≠ 0 ∧ matCLM wRestrict x = 0 := by
  refine ⟨WithLp.toLp 2 ![0, 1], ?_, ?_⟩
  · intro h
    have := congrFun (congrArg WithLp.ofLp h) 1
    simp at this
  · rw [matCLM_apply]
    ext i
    fin_cases i
    simp [wRestrict, Matrix.mulVec, dotProduct]

/-- The sandwich identity at `Ψ⁻¹ = I₂`, `Υ = I₂`, `𝓡 = (1  0)`, with `Σ = (1)`. -/
theorem rsand (t : EuclideanSpace ℝ (Fin 1)) :
    (ContinuousLinearMap.adjoint ((matCLM wRestrict).comp
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))) t)
        ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (ContinuousLinearMap.adjoint
          ((matCLM wRestrict).comp (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))) t))
      = t ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ t) := by
  have hcomp : (matCLM wRestrict).comp (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
      = matCLM wRestrict := ContinuousLinearMap.comp_id _
  rw [hcomp, adjoint_matCLM]
  have hval : ∀ i : Fin 2, (matCLM wRestrictᵀ t : EuclideanSpace ℝ (Fin 2)) i
      = if i = 0 then t 0 else 0 := by
    intro i
    rw [matCLM_apply]
    fin_cases i <;> simp [wRestrict, Matrix.mulVec, dotProduct]
  simp only [Matrix.one_mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_one, hval]
  norm_num

variable {Om : Type*}

/-- The category disturbance of design `n`. -/
noncomputable def reta (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ) (n : ℕ) (j : rJ n) : Om → ℝ :=
  xi ⟨n, Sum.inl j⟩

/-- The idiosyncratic disturbance of design `n`. -/
noncomputable def reps (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ) (n : ℕ) (o : rO n) : Om → ℝ :=
  xi ⟨n, Sum.inr o⟩

/-- `π̂_n`, from the solved form of Lemma SM.B.4 at `Ψ̂_n = I₂`. -/
noncomputable def rpih (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ) (n : ℕ) (ω : Om) :
    EuclideanSpace ℝ (Fin 2) :=
  (Real.sqrt (rNs n))⁻¹ •
    (ra n • ((∑ j, reta xi n j ω • rzc n j) + (∑ o, reps xi n o ω • rzt n o)))

/-- A random `±1` sign, read off the disturbance array. -/
noncomputable def rsgn (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ) (ω : Om) : ℝ :=
  if 0 ≤ xi ⟨0, Sum.inr (0 : rO 0)⟩ ω then 1 else -1

/-- The estimated meat `Υ̂_n`, random at every index. -/
noncomputable def rUh (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ) (n : ℕ) (ω : Om) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ((((1 : ℝ) + ((n : ℝ) + 1)⁻¹ * (1 + rsgn xi ω)) / 4)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The population meat `Υ_n`. -/
noncomputable def rUps (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem abs_rsgn (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ) (ω : Om) : |rsgn xi ω| = 1 := by
  unfold rsgn
  split <;> norm_num

theorem measurable_rsgn [MeasurableSpace Om] (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ)
    (h : Measurable (xi ⟨0, Sum.inr (0 : rO 0)⟩)) : Measurable (rsgn xi) := by
  unfold rsgn
  exact Measurable.ite (measurableSet_le measurable_const h) measurable_const measurable_const

theorem rUh_sub_rUps (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ) (n : ℕ) (ω : Om) :
    rUh xi n ω - rUps n
      = ((((n : ℝ) + 1)⁻¹ * rsgn xi ω) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [rUh, rUps, ← sub_smul]
  congr 1
  ring

/-- `‖Υ̂_n - Υ_n‖_F = (n+1)^{-1}√2/4`. -/
theorem frobNorm_rUh_sub (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ) (n : ℕ) (ω : Om) :
    frobNorm (rUh xi n ω - rUps n) = (((n : ℝ) + 1)⁻¹ / 4) * Real.sqrt 2 := by
  rw [rUh_sub_rUps, frobNorm_smul, frobNorm_one_fin_two]
  congr 1
  rw [abs_div, abs_mul, abs_rsgn, mul_one,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)]
  norm_num

/-- `‖𝓡Ψ̂^{-1}Υ_nΨ̂^{-1}𝓡' - Σ‖_F = (n+1)^{-1}`. -/
theorem frobNorm_rdet (n : ℕ) :
    frobNorm (wRestrict * (wPsiInv * rUps n * wPsiInv) * wRestrictᵀ
      - (1 : Matrix (Fin 1) (Fin 1) ℝ)) = ((n : ℝ) + 1)⁻¹ := by
  rw [rUps, wRestrict_conj]
  have hsm : (4 * (((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
      - (1 : Matrix (Fin 1) (Fin 1) ℝ)
      = (((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [show (4 * (((1 : ℝ) + ((n : ℝ) + 1)⁻¹) / 4)) = 1 + ((n : ℝ) + 1)⁻¹ by ring,
      add_smul, one_smul]
    abel
  rw [hsm, frobNorm_smul, frobNorm_one_fin_one, mul_one,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)]

/-- `piinf_wald_restricted_closed` at `K = 2`, `r = 1`. -/
theorem piinf_wald_restricted_closed_witness :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Measure Om) (_ : IsProbabilityMeasure P)
      (xi : (Σ n : ℕ, (rJ n ⊕ rO n)) → Om → ℝ),
      (Tendsto (fun n => P {ω | ((rNs n)⁻¹ • (wRestrict * (wPsiInv * rUh xi n ω * wPsiInv)
            * wRestrictᵀ)).PosDef}) atTop (𝓝 1)
        ∧ TendstoInDistribution
            (fun n ω => Wald.waldStat ((rNs n)⁻¹ • (wRestrict
                * (wPsiInv * rUh xi n ω * wPsiInv) * wRestrictᵀ))
              (matCLM wRestrict (rpih xi n ω - (0 : EuclideanSpace ℝ (Fin 2))))) atTop
            (fun z : EuclideanSpace ℝ (Fin 1) => ‖z‖ ^ 2) (fun _ => P)
            (multivariateGaussian 0 1))
      ∧ (∀ n : ℕ, Fintype.card (rJ n) = (n + 1) ^ 2 * 2 ∧ Fintype.card (rO n) = (n + 1) ^ 3)
      ∧ (∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin 2)),
          ra n ^ 2 * ∑ j : rJ n, ⟪rzc n j, t⟫ ^ 2 * (1 : ℝ) = t 0 ^ 2 + t 1 ^ 2)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef
      ∧ (∃ x : EuclideanSpace ℝ (Fin 2), x ≠ 0 ∧ matCLM wRestrict x = 0)
      ∧ (∀ (n : ℕ) (ω : Om), frobNorm (rUh xi n ω - rUps n)
          = (((n : ℝ) + 1)⁻¹ / 4) * Real.sqrt 2)
      ∧ (∀ n : ℕ, frobNorm (wRestrict * (wPsiInv * rUps n * wPsiInv) * wRestrictᵀ
          - (1 : Matrix (Fin 1) (Fin 1) ℝ)) = ((n : ℝ) + 1)⁻¹)
      ∧ (∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin 2)),
          Var[fun ω => ra n * ∑ j : rJ n, ⟪rzc n j, t⟫ * reta xi n j ω; P]
            = t 0 ^ 2 + t 1 ^ 2) := by
  classical
  obtain ⟨Om, mOm, P, xi, hmeasx, hlawx, hindepx, hprobx⟩ :=
    exists_iid (Σ n : ℕ, (rJ n ⊕ rO n)) CLT.Witness.rade
  have hmeasη : ∀ (n : ℕ) (j : rJ n), Measurable (reta xi n j) := fun n j => hmeasx _
  have hmeasε : ∀ (n : ℕ) (o : rO n), Measurable (reps xi n o) := fun n o => hmeasx _
  have hinjl : ∀ n : ℕ, Function.Injective
      (fun j : rJ n => (⟨n, Sum.inl j⟩ : Σ n : ℕ, (rJ n ⊕ rO n))) := by
    intro n a b hab
    simpa using hab
  have hinjr : ∀ n : ℕ, Function.Injective
      (fun o : rO n => (⟨n, Sum.inr o⟩ : Σ n : ℕ, (rJ n ⊕ rO n))) := by
    intro n a b hab
    simpa using hab
  have hindepη : ∀ n : ℕ, iIndepFun (reta xi n) P := fun n =>
    hindepx.precomp (g := fun j : rJ n => (⟨n, Sum.inl j⟩ : Σ n : ℕ, (rJ n ⊕ rO n))) (hinjl n)
  have hindepε : ∀ n : ℕ, iIndepFun (reps xi n) P := fun n =>
    hindepx.precomp (g := fun o : rO n => (⟨n, Sum.inr o⟩ : Σ n : ℕ, (rJ n ⊕ rO n))) (hinjr n)
  have hmeanη : ∀ (n : ℕ) (j : rJ n), ∫ ω, reta xi n j ω ∂P = 0 := by
    intro n j
    show ∫ ω, xi ⟨n, Sum.inl j⟩ ω ∂P = 0
    rw [(hlawx ⟨n, Sum.inl j⟩).integral_eq, CLT.Witness.integral_id_rade]
  have hmeanε : ∀ (n : ℕ) (o : rO n), ∫ ω, reps xi n o ω ∂P = 0 := by
    intro n o
    show ∫ ω, xi ⟨n, Sum.inr o⟩ ω ∂P = 0
    rw [(hlawx ⟨n, Sum.inr o⟩).integral_eq, CLT.Witness.integral_id_rade]
  have hL2η : ∀ (n : ℕ) (j : rJ n), MemLp (reta xi n j) 2 P := fun n j =>
    (hlawx ⟨n, Sum.inl j⟩).memLp CLT.Witness.memLp_id_rade
  have hL2ε : ∀ (n : ℕ) (o : rO n), MemLp (reps xi n o) 2 P := fun n o =>
    (hlawx ⟨n, Sum.inr o⟩).memLp CLT.Witness.memLp_id_rade
  have hint4η : ∀ (n : ℕ) (j : rJ n), Integrable (fun ω => reta xi n j ω ^ 4) P := fun n j =>
    (hlawx ⟨n, Sum.inl j⟩).integrable_fun_comp CLT.Witness.integrable_pow4_rade
  have hvarη : ∀ (n : ℕ) (j : rJ n), Var[reta xi n j; P] = 1 := by
    intro n j
    show Var[xi ⟨n, Sum.inl j⟩; P] = 1
    rw [(hlawx ⟨n, Sum.inl j⟩).variance_eq, CLT.Witness.variance_id_rade]
  have hvarε : ∀ (n : ℕ) (o : rO n), Var[reps xi n o; P] = 1 := by
    intro n o
    show Var[xi ⟨n, Sum.inr o⟩; P] = 1
    rw [(hlawx ⟨n, Sum.inr o⟩).variance_eq, CLT.Witness.variance_id_rade]
  have hmomη : ∀ (n : ℕ) (j : rJ n), ∫ ω, reta xi n j ω ^ 4 ∂P ≤ 1 := by
    intro n j
    show ∫ ω, xi ⟨n, Sum.inl j⟩ ω ^ 4 ∂P ≤ 1
    have h : ∫ ω, xi ⟨n, Sum.inl j⟩ ω ^ 4 ∂P = ∫ x, x ^ 4 ∂CLT.Witness.rade := by
      simpa [Function.comp_def] using
        (hlawx ⟨n, Sum.inl j⟩).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [h, CLT.Witness.integral_pow4_rade]
  have hi : Tendsto (fun n : ℕ => ra n ^ 2 * (Fintype.card (rO n) : ℝ) * ((2 : ℝ) ^ 2 * 1))
      atTop (𝓝 0) := by
    have h := PiWitness.tendsto_inv_succ.const_mul (4 : ℝ)
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [ra, Fintype.card_fin]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hiv : Tendsto (fun n : ℕ => rmx n / ∑ j : rJ n, ‖rzc n j‖ ^ 2) atTop (𝓝 0) := by
    have h := (PiWitness.tendsto_inv_succ.pow 2).const_mul (2⁻¹ : ℝ)
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, mul_zero] at h
    refine h.congr fun n => ?_
    rw [rmx, sum_norm_sq_rzc]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hsolve : ∀ᶠ n : ℕ in atTop, ∀ ω,
      Real.sqrt (rNs n) • (rpih xi n ω - (0 : EuclideanSpace ℝ (Fin 2)))
        = (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
            (ra n • ((∑ j, reta xi n j ω • rzc n j) + (∑ o, reps xi n o ω • rzt n o))) := by
    filter_upwards with n ω
    have hne : Real.sqrt (rNs n) ≠ 0 := by rw [sqrt_rNs]; positivity
    rw [sub_zero, rpih, smul_smul, mul_inv_cancel₀ hne, one_smul]
    rfl
  have hpimeas : ∀ n : ℕ, AEMeasurable (rpih xi n) P := by
    intro n
    refine Measurable.aemeasurable ?_
    have h1 : Measurable fun ω => ∑ j, reta xi n j ω • rzc n j :=
      Finset.measurable_sum _ fun j _ => (hmeasη n j).smul_const (rzc n j)
    have h2 : Measurable fun ω => ∑ o, reps xi n o ω • rzt n o :=
      Finset.measurable_sum _ fun o _ => (hmeasε n o).smul_const (rzt n o)
    exact ((h1.add h2).const_smul (ra n)).const_smul ((Real.sqrt (rNs n))⁻¹)
  have hVmeas : ∀ n : ℕ, Measurable fun ω => (rNs n)⁻¹ •
      (wRestrict * (wPsiInv * rUh xi n ω * wPsiInv) * wRestrictᵀ) := by
    intro n
    have hs : Measurable (rsgn xi) := measurable_rsgn xi (hmeasx _)
    have hfun : (fun ω => (rNs n)⁻¹
          • (wRestrict * (wPsiInv * rUh xi n ω * wPsiInv) * wRestrictᵀ))
        = fun ω => ((rNs n)⁻¹ * (4 * (((1 : ℝ) + ((n : ℝ) + 1)⁻¹ * (1 + rsgn xi ω)) / 4)))
            • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      funext ω
      rw [rUh, wRestrict_conj, smul_smul]
    rw [hfun]
    fun_prop
  have ha0 : TendstoInMeasure P (fun n ω => frobNorm (rUh xi n ω - rUps n)) atTop
      (fun _ => 0) := by
    refine Sequence.tendstoInProb_zero_of_abs_le_const
      (b := fun n : ℕ => (((n : ℝ) + 1)⁻¹ / 4) * Real.sqrt 2)
      (fun n => Filter.Eventually.of_forall fun ω => ?_) ?_
    · rw [frobNorm_rUh_sub, abs_of_nonneg (by positivity)]
    · have h := (PiWitness.tendsto_inv_succ.div_const 4).mul_const (Real.sqrt 2)
      simpa using h
  have hdet : Tendsto (fun n : ℕ => frobNorm (wRestrict * (wPsiInv * rUps n * wPsiInv)
      * wRestrictᵀ - (1 : Matrix (Fin 1) (Fin 1) ℝ))) atTop (𝓝 0) :=
    PiWitness.tendsto_inv_succ.congr fun n => (frobNorm_rdet n).symm
  refine ⟨Om, mOm, P, hprobx, xi, ?_, ?_, fun n t => upsilon_exact n t, Matrix.PosDef.one,
    matCLM_wRestrict_not_injective, fun n ω => frobNorm_rUh_sub xi n ω, frobNorm_rdet, ?_⟩
  · exact piinf_wald_restricted_closed (P := P) ra rNs rmx rzc rzt (reta xi) (reps xi)
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) 1 2 1 1
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      Matrix.PosDef.one Matrix.PosDef.one
      hmeasη hindepη hmeanη hL2η hint4η hvarη hmomη
      zero_lt_one (fun _ _ => le_refl 1)
      hmeasε hindepε hL2ε hmeanε hvarε (fun _ _ => zero_le_one) (fun _ _ => le_refl 1)
      (fun n o => by rw [norm_sq_rzt]; norm_num) hi
      (fun t => by
        rw [dotProduct_one_fin_two t]
        exact tendsto_const_nhds.congr fun n => (upsilon_exact n t).symm)
      (fun n => by rw [rmx]; positivity)
      (fun n j => by rw [norm_sq_rzc, rmx])
      (fun n => by
        rw [rmx, sum_norm_sq_rzc]
        have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
        calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 2 * 1 := by ring
          _ ≤ ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) ^ 2) :=
              mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
          _ = 2 * ((n : ℝ) + 1) ^ 4 := by ring)
      hiv
      (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) wRestrict
      tendsto_const_nhds rsand
      (rpih xi) 0 hpimeas hsolve
      (rUh xi) rUps (fun _ => wPsiInv) (fun n => by rw [rNs]; positivity)
      (fun _ _ => (isHermitian_fin_one _).smul (IsSelfAdjoint.all _)) hVmeas
      (Lg := Real.sqrt 8) (Lr := 1) (Real.sqrt_nonneg 8) zero_le_one
      (fun _ => le_of_eq frobNorm_wPsiInv) (le_of_eq rectFrobNorm_wRestrict)
      hdet ha0
  · exact fun n => ⟨by simp [Fintype.card_prod, Fintype.card_fin], Fintype.card_fin _⟩
  · intro n t
    have hfun : (fun ω => ∑ j : rJ n, ⟪rzc n j, t⟫ * reta xi n j ω)
        = ∑ j : rJ n, fun ω => ⟪rzc n j, t⟫ * reta xi n j ω := by
      funext ω; rw [Finset.sum_apply]
    have hL2' : ∀ j ∈ (Finset.univ : Finset (rJ n)),
        MemLp (fun ω => ⟪rzc n j, t⟫ * reta xi n j ω) 2 P := fun j _ => (hL2η n j).const_mul _
    have hindep' : Set.Pairwise (↑(Finset.univ : Finset (rJ n)))
        fun j j' => IndepFun (fun ω => ⟪rzc n j, t⟫ * reta xi n j ω)
          (fun ω => ⟪rzc n j', t⟫ * reta xi n j' ω) P := by
      intro j _ j' _ hne
      exact (((hindepη n).indepFun hne).comp (measurable_const_mul _) (measurable_const_mul _))
    rw [variance_const_mul, hfun, IndepFun.variance_sum hL2' hindep',
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [variance_const_mul, hvarη n j, mul_one]]
    simpa using upsilon_exact n t

end RectDesign

end PiTwelve

/-! ## §13 Removing the conditioning

`pi_clt_unconditional_of_design_closed` is Theorem 6 with a `𝒟`-measurable random design: every
hypothesis of `pi_clt` is read under the regular conditional law `ℙ_ω := condExpKernel P 𝒟 ω` at
`P`-almost every `ω`, and the conclusion holds under `P`. The design is frozen by
`ae_ae_eq_pi_design`, and the frozen statistic is passed to
`pi_clt_unconditional_of_frozen_stat`. `piinf_wald_unconditional_of_design_closed` is the
corresponding form of Theorem 12(b) at `𝓡 = I_K`. The limits `Υ`, `Ψ⁻¹` and `π₀` are
deterministic.

The witness runs on the product space `Bool × ((ℕ × ℕ) → Bool)` of `Multiway.SteinCluster`, where
`𝒟` is a proper sub-σ-field and `ℙ_ω ≠ P`, with the category weights multiplied by the sign of
the design coin. -/

section PiThirteen
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

section DesignDecondClosed

open CLTMartingale.CondD

variable {Om : Type*} {𝒟 : MeasurableSpace Om} [mOm2 : MeasurableSpace Om]
  [StandardBorelSpace Om]

/-- Removing the conditioning, given the statistic's a.e. equality with its frozen form.
`hfrz` is required only eventually in `n`, and `hWm` is full measurability. -/
theorem pi_clt_unconditional_of_frozen_stat {K : ℕ}
    (h𝒟 : 𝒟 ≤ mOm2) (P : Measure Om) [IsProbabilityMeasure P]
    [∀ ω : Om, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    {W : ℕ → Om → EuclideanSpace ℝ (Fin K)} (hWm : ∀ n, Measurable (W n))
    {Wfr : Om → ℕ → Om → EuclideanSpace ℝ (Fin K)}
    (hfrz : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, W n =ᵐ[condExpKernel P 𝒟 ω] Wfr ω n)
    (Ups : Matrix (Fin K) (Fin K) ℝ)
    {Z : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)} (hZ : Measurable Z)
    (hfrozen : ∀ᵐ ω ∂P, TendstoInDistribution (m := fun _ : ℕ => mOm2) (Wfr ω) atTop
      Z (fun _ => condExpKernel P 𝒟 ω) (multivariateGaussian 0 Ups)) :
    TendstoInDistribution (m := fun _ : ℕ => mOm2) W atTop Z (fun _ => P)
      (multivariateGaussian 0 Ups) := by
  refine tendstoInDistribution_of_tendsto_condCharFunD h𝒟 P
    (fun n => (hWm n).aemeasurable) hZ.aemeasurable fun t => ?_
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, condCharFunD 𝒟 P (W n) t ω
      = charFun (@Measure.map Om (EuclideanSpace ℝ (Fin K)) mOm2 _ (W n)
          (condExpKernel P 𝒟 ω)) t :=
    ae_all_iff.2 fun n => condCharFunD_eq_charFun_condExpKernel h𝒟 P (hWm n) t
  filter_upwards [hall, hfrz, hfrozen] with ω hω hfr hcl
  have h : Tendsto (fun n : ℕ => charFun
      (@Measure.map Om (EuclideanSpace ℝ (Fin K)) mOm2 _ (Wfr ω n)
        (condExpKernel P 𝒟 ω)) t) atTop
      (𝓝 (charFun ((multivariateGaussian 0 Ups).map Z) t)) := hcl.tendsto_charFun t
  refine Tendsto.congr' ?_ h
  filter_upwards [hfr] with n hn
  show charFun (@Measure.map Om (EuclideanSpace ℝ (Fin K)) mOm2 _ (Wfr ω n)
    (condExpKernel P 𝒟 ω)) t = condCharFunD 𝒟 P (W n) t ω
  rw [hω n, Measure.map_congr hn]

/-- Freezing the design of Theorem 6: under `ℙ_ω` the category weights, the observation rows,
the scale `a_n` and `Ψ̂_n` are a.e. constant. Vectors are frozen whole and `Ψ̂_n` entry by
entry. -/
theorem ae_ae_eq_pi_design {K : ℕ} {Jc : ℕ → Type*} [∀ n, Fintype (Jc n)]
    {Ob : ℕ → Type*} [∀ n, Fintype (Ob n)]
    (h𝒟 : 𝒟 ≤ mOm2) (P : Measure Om) [IsFiniteMeasure P]
    {aa : ℕ → Om → ℝ}
    {zc : ∀ n, Jc n → Om → EuclideanSpace ℝ (Fin K)}
    {zt : ∀ n, Ob n → Om → EuclideanSpace ℝ (Fin K)}
    {Amat : ℕ → Om → Matrix (Fin K) (Fin K) ℝ}
    (haD : ∀ n, Measurable[𝒟] (aa n))
    (hzcD : ∀ n j, Measurable[𝒟] (zc n j))
    (hztD : ∀ n o, Measurable[𝒟] (zt n o))
    (hAD : ∀ n p q, Measurable[𝒟] fun ω => Amat n ω p q) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      aa n y = aa n ω ∧ (∀ j, zc n j y = zc n j ω) ∧ (∀ o, zt n o y = zt n o ω)
        ∧ Amat n y = Amat n ω := by
  refine ae_all_iff.2 fun n => ?_
  have h1 : ∀ᵐ ω ∂P, ∀ᵐ y ∂(condExpKernel P 𝒟 ω), aa n y = aa n ω :=
    ae_ae_eq_condExpKernel h𝒟 P (haD n)
  have h2 : ∀ᵐ ω ∂P, ∀ j : Jc n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω), zc n j y = zc n j ω :=
    ae_all_iff.2 fun j => ae_ae_eq_condExpKernel h𝒟 P (hzcD n j)
  have h3 : ∀ᵐ ω ∂P, ∀ o : Ob n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω), zt n o y = zt n o ω :=
    ae_all_iff.2 fun o => ae_ae_eq_condExpKernel h𝒟 P (hztD n o)
  have h4 : ∀ᵐ ω ∂P, ∀ p : Fin K × Fin K, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Amat n y p.1 p.2 = Amat n ω p.1 p.2 :=
    ae_all_iff.2 fun p => ae_ae_eq_condExpKernel h𝒟 P (hAD n p.1 p.2)
  filter_upwards [h1, h2, h3, h4] with ω hω1 hω2 hω3 hω4
  filter_upwards [hω1, ae_all_iff.2 hω2, ae_all_iff.2 hω3, ae_all_iff.2 hω4]
    with y hy1 hy2 hy3 hy4
  exact ⟨hy1, hy2, hy3, Matrix.ext fun p q => hy4 (p, q)⟩

/-- `√s • ((π₀ + (√s)⁻¹ • v) - π₀) = v`. -/
theorem sqrt_smul_solved {K : ℕ} {s : ℝ} (hs : 0 < s)
    (pi0 v : EuclideanSpace ℝ (Fin K)) :
    Real.sqrt s • ((pi0 + (Real.sqrt s)⁻¹ • v) - pi0) = v := by
  rw [add_sub_cancel_left, smul_inv_smul₀ (ne_of_gt (Real.sqrt_pos.2 hs))]

/-- **Theorem 6** under the full measure, with the design random: `a_n`, `N_*`, `max_j‖z_j‖²`,
`z^{(m)}_j`, `z̃_o` and `Ψ̂_n` are `𝒟`-measurable, every hypothesis of `pi_clt` holds under `ℙ_ω`
for `P`-a.e. `ω`, and the conclusion holds under `P`. The limits `Υ` and `Ψ⁻¹`, the value `π₀`
and the constants are deterministic. -/
theorem pi_clt_unconditional_of_design_closed {K : ℕ}
    {Jc : ℕ → Type*} [∀ n, Fintype (Jc n)] {Ob : ℕ → Type*} [∀ n, Fintype (Ob n)]
    (h𝒟 : 𝒟 ≤ mOm2) (P : Measure Om) [IsProbabilityMeasure P]
    [∀ ω : Om, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (aa Ns mx : ℕ → Om → ℝ)
    (zc : ∀ n, Jc n → Om → EuclideanSpace ℝ (Fin K))
    (zt : ∀ n, Ob n → Om → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, Jc n → Om → ℝ) (eps : ∀ n, Ob n → Om → ℝ)
    (vr : ∀ n, Jc n → Om → ℝ) (sev : ∀ n, Ob n → Om → ℝ) (C B Cs v0 : ℝ)
    (Ups : Matrix (Fin K) (Fin K) ℝ) (hUps : Ups.PosDef)
    (Amat : ℕ → Om → Matrix (Fin K) (Fin K) ℝ)
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (pih : ℕ → Om → EuclideanSpace ℝ (Fin K)) (pi0 : EuclideanSpace ℝ (Fin K))
    (haD : ∀ n, Measurable[𝒟] (aa n))
    (hzcD : ∀ n j, Measurable[𝒟] (zc n j)) (hztD : ∀ n o, Measurable[𝒟] (zt n o))
    (hAD : ∀ n p q, Measurable[𝒟] fun ω => Amat n ω p q)
    (hNs : ∀ n ω, 0 < Ns n ω)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hmeasε : ∀ n o, Measurable (eps n o))
    (hWm : ∀ n, Measurable fun y => Real.sqrt (Ns n y) • (pih n y - pi0))
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ y, Real.sqrt (Ns n y) • (pih n y - pi0)
      = matCLM (Amat n y) (aa n y •
          ((∑ j, etab n j y • zc n j y) + (∑ o, eps n o y • zt n o y))))
    (hindepη : ∀ᵐ ω ∂P, ∀ n, iIndepFun (etab n) (condExpKernel P 𝒟 ω))
    (hmeanη : ∀ᵐ ω ∂P, ∀ n j, ∫ y, etab n j y ∂(condExpKernel P 𝒟 ω) = 0)
    (hL2η : ∀ᵐ ω ∂P, ∀ n j, MemLp (etab n j) 2 (condExpKernel P 𝒟 ω))
    (hint4η : ∀ᵐ ω ∂P, ∀ n j, Integrable (fun y => etab n j y ^ 4) (condExpKernel P 𝒟 ω))
    (hvarη : ∀ᵐ ω ∂P, ∀ n j, Var[etab n j; condExpKernel P 𝒟 ω] = vr n j ω)
    (hmomη : ∀ᵐ ω ∂P, ∀ n j, ∫ y, etab n j y ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C)
    (hv0 : 0 < v0) (hvr : ∀ᵐ ω ∂P, ∀ n j, v0 ≤ vr n j ω)
    (hindepε : ∀ᵐ ω ∂P, ∀ n, iIndepFun (eps n) (condExpKernel P 𝒟 ω))
    (hL2ε : ∀ᵐ ω ∂P, ∀ n o, MemLp (eps n o) 2 (condExpKernel P 𝒟 ω))
    (hmeanε : ∀ᵐ ω ∂P, ∀ n o, ∫ y, eps n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hvarε : ∀ᵐ ω ∂P, ∀ n o, Var[eps n o; condExpKernel P 𝒟 ω] = sev n o ω)
    (hsev0 : ∀ᵐ ω ∂P, ∀ n o, 0 ≤ sev n o ω) (hsev : ∀ᵐ ω ∂P, ∀ n o, sev n o ω ≤ Cs)
    (hzt : ∀ᵐ ω ∂P, ∀ n o, ‖zt n o ω‖ ^ 2 ≤ B ^ 2)
    (hi : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
        aa n ω ^ 2 * (Fintype.card (Ob n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ᵐ ω ∂P, ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => aa n ω ^ 2 * ∑ j, ⟪zc n j ω, t⟫ ^ 2 * vr n j ω) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ᵐ ω ∂P, ∀ n, 0 ≤ mx n ω)
    (hmx : ∀ᵐ ω ∂P, ∀ n j, ‖zc n j ω‖ ^ 2 ≤ mx n ω)
    (hmxsum : ∀ᵐ ω ∂P, ∀ n, mx n ω ≤ ∑ j, ‖zc n j ω‖ ^ 2)
    (hiv : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => mx n ω / ∑ j, ‖zc n j ω‖ ^ 2) atTop (𝓝 0))
    (hA : ∀ᵐ ω ∂P, Tendsto (fun n => matCLM (Amat n ω)) atTop (𝓝 Psiinv)) :
    TendstoInDistribution (m := fun _ : ℕ => mOm2)
      (fun (n : ℕ) y => Real.sqrt (Ns n y) • (pih n y - pi0)) atTop
      (fun z => Psiinv z) (fun _ => P) (multivariateGaussian 0 Ups) := by
  classical
  refine pi_clt_unconditional_of_frozen_stat h𝒟 P hWm
    (Wfr := fun ω n y => Real.sqrt (Ns n ω) •
      ((pi0 + (Real.sqrt (Ns n ω))⁻¹ • matCLM (Amat n ω) (aa n ω •
          ((∑ j, etab n j y • zc n j ω) + (∑ o, eps n o y • zt n o ω)))) - pi0))
    ?_ Ups (Psiinv.continuous.measurable) ?_
  · filter_upwards [ae_ae_eq_pi_design h𝒟 P haD hzcD hztD hAD] with ω hω
    filter_upwards [hsolve] with n hn
    filter_upwards [hω n] with y hy
    have h1 : (∑ j, etab n j y • zc n j y) = ∑ j, etab n j y • zc n j ω :=
      Finset.sum_congr rfl fun j _ => by rw [hy.2.1 j]
    have h2 : (∑ o, eps n o y • zt n o y) = ∑ o, eps n o y • zt n o ω :=
      Finset.sum_congr rfl fun o _ => by rw [hy.2.2.1 o]
    show Real.sqrt (Ns n y) • (pih n y - pi0) = _
    rw [hn y, sqrt_smul_solved (hNs n ω), h1, h2, hy.1, hy.2.2.2]
  · filter_upwards [hindepη, hmeanη, hL2η, hint4η, hvarη, hmomη, hvr, hindepε, hL2ε, hmeanε,
      hvarε, hsev0, hsev, hzt, hi, hiii, hmx0, hmx, hmxsum, hiv, hA]
      with ω h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
    refine pi_clt (P := condExpKernel P 𝒟 ω) (fun n => aa n ω) (fun n => Ns n ω)
      (fun n => mx n ω) (fun n j => zc n j ω) (fun n o => zt n o ω) etab eps
      (fun n j => vr n j ω) (fun n o => sev n o ω) C B Cs v0 Ups hUps
      hmeasη h1 h2 h3 h4 h5 h6 hv0 h7 hmeasε h8 h9 h10 h11 h12 h13 h14 h15 h16
      h17 h18 h19 h20 (fun n => matCLM (Amat n ω)) Psiinv h21
      (fun n y => pi0 + (Real.sqrt (Ns n ω))⁻¹ • matCLM (Amat n ω) (aa n ω •
          ((∑ j, etab n j y • zc n j ω) + (∑ o, eps n o y • zt n o ω)))) pi0 ?_ ?_
    · intro n
      refine Measurable.aemeasurable ?_
      have hs1 : Measurable fun y : Om => ∑ j, etab n j y • zc n j ω :=
        Finset.measurable_sum _ fun j _ => (hmeasη n j).smul_const (zc n j ω)
      have hs2 : Measurable fun y : Om => ∑ o, eps n o y • zt n o ω :=
        Finset.measurable_sum _ fun o _ => (hmeasε n o).smul_const (zt n o ω)
      exact measurable_const.add
        ((((matCLM (Amat n ω)).continuous.measurable).comp
          ((hs1.add hs2).const_smul (aa n ω))).const_smul ((Real.sqrt (Ns n ω))⁻¹))
    · exact Filter.Eventually.of_forall fun n y => sqrt_smul_solved (hNs n ω) _ _

/-- **Theorem 6** in standard form, unconditional, with the design random. -/
theorem pi_clt_std_unconditional_of_design_closed {K : ℕ}
    {Jc : ℕ → Type*} [∀ n, Fintype (Jc n)] {Ob : ℕ → Type*} [∀ n, Fintype (Ob n)]
    (h𝒟 : 𝒟 ≤ mOm2) (P : Measure Om) [IsProbabilityMeasure P]
    [∀ ω : Om, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (aa mx : ℕ → Om → ℝ) (NS : ℕ → Om → ℝ)
    (zc : ∀ n, Jc n → Om → EuclideanSpace ℝ (Fin K))
    (zt : ∀ n, Ob n → Om → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, Jc n → Om → ℝ) (eps : ∀ n, Ob n → Om → ℝ)
    (vr : ∀ n, Jc n → Om → ℝ) (sev : ∀ n, Ob n → Om → ℝ) (C B Cs v0 : ℝ)
    (Ups Sg : Matrix (Fin K) (Fin K) ℝ) (hUps : Ups.PosDef) (hSg : Sg.PosSemidef)
    (Amat : ℕ → Om → Matrix (Fin K) (Fin K) ℝ)
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (pih : ℕ → Om → EuclideanSpace ℝ (Fin K)) (pi0 : EuclideanSpace ℝ (Fin K))
    (haD : ∀ n, Measurable[𝒟] (aa n))
    (hzcD : ∀ n j, Measurable[𝒟] (zc n j)) (hztD : ∀ n o, Measurable[𝒟] (zt n o))
    (hAD : ∀ n p q, Measurable[𝒟] fun ω => Amat n ω p q)
    (hNS : ∀ n ω, 0 < NS n ω)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hmeasε : ∀ n o, Measurable (eps n o))
    (hWm : ∀ n, Measurable fun y => Real.sqrt (NS n y) • (pih n y - pi0))
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ y, Real.sqrt (NS n y) • (pih n y - pi0)
      = matCLM (Amat n y) (aa n y •
          ((∑ j, etab n j y • zc n j y) + (∑ o, eps n o y • zt n o y))))
    (hindepη : ∀ᵐ ω ∂P, ∀ n, iIndepFun (etab n) (condExpKernel P 𝒟 ω))
    (hmeanη : ∀ᵐ ω ∂P, ∀ n j, ∫ y, etab n j y ∂(condExpKernel P 𝒟 ω) = 0)
    (hL2η : ∀ᵐ ω ∂P, ∀ n j, MemLp (etab n j) 2 (condExpKernel P 𝒟 ω))
    (hint4η : ∀ᵐ ω ∂P, ∀ n j, Integrable (fun y => etab n j y ^ 4) (condExpKernel P 𝒟 ω))
    (hvarη : ∀ᵐ ω ∂P, ∀ n j, Var[etab n j; condExpKernel P 𝒟 ω] = vr n j ω)
    (hmomη : ∀ᵐ ω ∂P, ∀ n j, ∫ y, etab n j y ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C)
    (hv0 : 0 < v0) (hvr : ∀ᵐ ω ∂P, ∀ n j, v0 ≤ vr n j ω)
    (hindepε : ∀ᵐ ω ∂P, ∀ n, iIndepFun (eps n) (condExpKernel P 𝒟 ω))
    (hL2ε : ∀ᵐ ω ∂P, ∀ n o, MemLp (eps n o) 2 (condExpKernel P 𝒟 ω))
    (hmeanε : ∀ᵐ ω ∂P, ∀ n o, ∫ y, eps n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hvarε : ∀ᵐ ω ∂P, ∀ n o, Var[eps n o; condExpKernel P 𝒟 ω] = sev n o ω)
    (hsev0 : ∀ᵐ ω ∂P, ∀ n o, 0 ≤ sev n o ω) (hsev : ∀ᵐ ω ∂P, ∀ n o, sev n o ω ≤ Cs)
    (hzt : ∀ᵐ ω ∂P, ∀ n o, ‖zt n o ω‖ ^ 2 ≤ B ^ 2)
    (hi : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
        aa n ω ^ 2 * (Fintype.card (Ob n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ᵐ ω ∂P, ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => aa n ω ^ 2 * ∑ j, ⟪zc n j ω, t⟫ ^ 2 * vr n j ω) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ᵐ ω ∂P, ∀ n, 0 ≤ mx n ω)
    (hmx : ∀ᵐ ω ∂P, ∀ n j, ‖zc n j ω‖ ^ 2 ≤ mx n ω)
    (hmxsum : ∀ᵐ ω ∂P, ∀ n, mx n ω ≤ ∑ j, ‖zc n j ω‖ ^ 2)
    (hiv : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => mx n ω / ∑ j, ‖zc n j ω‖ ^ 2) atTop (𝓝 0))
    (hA : ∀ᵐ ω ∂P, Tendsto (fun n => matCLM (Amat n ω)) atTop (𝓝 Psiinv))
    (hsand : ∀ t : EuclideanSpace ℝ (Fin K),
      (ContinuousLinearMap.adjoint Psiinv t)
          ⬝ᵥ (Ups *ᵥ (ContinuousLinearMap.adjoint Psiinv t))
        = t ⬝ᵥ (Sg *ᵥ t)) :
    TendstoInDistribution (m := fun _ : ℕ => mOm2)
      (fun (n : ℕ) y => Real.sqrt (NS n y) • (pih n y - pi0)) atTop
      (id : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (fun _ => P)
      (multivariateGaussian 0 Sg) := by
  classical
  refine pi_clt_unconditional_of_frozen_stat h𝒟 P hWm
    (Wfr := fun ω n y => Real.sqrt (NS n ω) •
      ((pi0 + (Real.sqrt (NS n ω))⁻¹ • matCLM (Amat n ω) (aa n ω •
          ((∑ j, etab n j y • zc n j ω) + (∑ o, eps n o y • zt n o ω)))) - pi0))
    ?_ Sg measurable_id ?_
  · filter_upwards [ae_ae_eq_pi_design h𝒟 P haD hzcD hztD hAD] with ω hω
    filter_upwards [hsolve] with n hn
    filter_upwards [hω n] with y hy
    have h1 : (∑ j, etab n j y • zc n j y) = ∑ j, etab n j y • zc n j ω :=
      Finset.sum_congr rfl fun j _ => by rw [hy.2.1 j]
    have h2 : (∑ o, eps n o y • zt n o y) = ∑ o, eps n o y • zt n o ω :=
      Finset.sum_congr rfl fun o _ => by rw [hy.2.2.1 o]
    show Real.sqrt (NS n y) • (pih n y - pi0) = _
    rw [hn y, sqrt_smul_solved (hNS n ω), h1, h2, hy.1, hy.2.2.2]
  · filter_upwards [hindepη, hmeanη, hL2η, hint4η, hvarη, hmomη, hvr, hindepε, hL2ε, hmeanε,
      hvarε, hsev0, hsev, hzt, hi, hiii, hmx0, hmx, hmxsum, hiv, hA]
      with ω h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
    refine pi_clt_std (P := condExpKernel P 𝒟 ω) (fun n => aa n ω) (fun n => NS n ω)
      (fun n => mx n ω) (fun n j => zc n j ω) (fun n o => zt n o ω) etab eps
      (fun n j => vr n j ω) (fun n o => sev n o ω) C B Cs v0 Ups Sg hUps hSg
      hmeasη h1 h2 h3 h4 h5 h6 hv0 h7 hmeasε h8 h9 h10 h11 h12 h13 h14 h15 h16
      h17 h18 h19 h20 (fun n => matCLM (Amat n ω)) Psiinv h21 hsand
      (fun n y => pi0 + (Real.sqrt (NS n ω))⁻¹ • matCLM (Amat n ω) (aa n ω •
          ((∑ j, etab n j y • zc n j ω) + (∑ o, eps n o y • zt n o ω)))) pi0 ?_ ?_
    · intro n
      refine Measurable.aemeasurable ?_
      have hs1 : Measurable fun y : Om => ∑ j, etab n j y • zc n j ω :=
        Finset.measurable_sum _ fun j _ => (hmeasη n j).smul_const (zc n j ω)
      have hs2 : Measurable fun y : Om => ∑ o, eps n o y • zt n o ω :=
        Finset.measurable_sum _ fun o _ => (hmeasε n o).smul_const (zt n o ω)
      exact measurable_const.add
        ((((matCLM (Amat n ω)).continuous.measurable).comp
          ((hs1.add hs2).const_smul (aa n ω))).const_smul ((Real.sqrt (NS n ω))⁻¹))
    · exact Filter.Eventually.of_forall fun n y => sqrt_smul_solved (hNS n ω) _ _

/-- **Theorem 12(b)**, unconditional, with the design random; its central limit theorem is
`pi_clt_std_unconditional_of_design_closed`. -/
theorem piinf_wald_unconditional_of_design_closed {K : ℕ}
    {Jc : ℕ → Type*} [∀ n, Fintype (Jc n)] {Ob : ℕ → Type*} [∀ n, Fintype (Ob n)]
    (h𝒟 : 𝒟 ≤ mOm2) (P : Measure Om) [IsProbabilityMeasure P]
    [∀ ω : Om, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (aa mx : ℕ → Om → ℝ) (Nsd : ℕ → ℝ)
    (zc : ∀ n, Jc n → Om → EuclideanSpace ℝ (Fin K))
    (zt : ∀ n, Ob n → Om → EuclideanSpace ℝ (Fin K))
    (etab : ∀ n, Jc n → Om → ℝ) (eps : ∀ n, Ob n → Om → ℝ)
    (vr : ∀ n, Jc n → Om → ℝ) (sev : ∀ n, Ob n → Om → ℝ) (C B Cs v0 : ℝ)
    (Ups Sg : Matrix (Fin K) (Fin K) ℝ) (hUps : Ups.PosDef) (hSgPD : Sg.PosDef)
    (Amat : ℕ → Om → Matrix (Fin K) (Fin K) ℝ)
    (Psiinv : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
    (pih : ℕ → Om → EuclideanSpace ℝ (Fin K)) (pi0 : EuclideanSpace ℝ (Fin K))
    (haD : ∀ n, Measurable[𝒟] (aa n))
    (hzcD : ∀ n j, Measurable[𝒟] (zc n j)) (hztD : ∀ n o, Measurable[𝒟] (zt n o))
    (hAD : ∀ n p q, Measurable[𝒟] fun ω => Amat n ω p q)
    (hNsd : ∀ n, 0 < Nsd n)
    (hmeasη : ∀ n j, Measurable (etab n j)) (hmeasε : ∀ n o, Measurable (eps n o))
    (hWm : ∀ n, Measurable fun y => Real.sqrt (Nsd n) • (pih n y - pi0))
    (hsolve : ∀ᶠ n : ℕ in atTop, ∀ y, Real.sqrt (Nsd n) • (pih n y - pi0)
      = matCLM (Amat n y) (aa n y •
          ((∑ j, etab n j y • zc n j y) + (∑ o, eps n o y • zt n o y))))
    (hindepη : ∀ᵐ ω ∂P, ∀ n, iIndepFun (etab n) (condExpKernel P 𝒟 ω))
    (hmeanη : ∀ᵐ ω ∂P, ∀ n j, ∫ y, etab n j y ∂(condExpKernel P 𝒟 ω) = 0)
    (hL2η : ∀ᵐ ω ∂P, ∀ n j, MemLp (etab n j) 2 (condExpKernel P 𝒟 ω))
    (hint4η : ∀ᵐ ω ∂P, ∀ n j, Integrable (fun y => etab n j y ^ 4) (condExpKernel P 𝒟 ω))
    (hvarη : ∀ᵐ ω ∂P, ∀ n j, Var[etab n j; condExpKernel P 𝒟 ω] = vr n j ω)
    (hmomη : ∀ᵐ ω ∂P, ∀ n j, ∫ y, etab n j y ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C)
    (hv0 : 0 < v0) (hvr : ∀ᵐ ω ∂P, ∀ n j, v0 ≤ vr n j ω)
    (hindepε : ∀ᵐ ω ∂P, ∀ n, iIndepFun (eps n) (condExpKernel P 𝒟 ω))
    (hL2ε : ∀ᵐ ω ∂P, ∀ n o, MemLp (eps n o) 2 (condExpKernel P 𝒟 ω))
    (hmeanε : ∀ᵐ ω ∂P, ∀ n o, ∫ y, eps n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hvarε : ∀ᵐ ω ∂P, ∀ n o, Var[eps n o; condExpKernel P 𝒟 ω] = sev n o ω)
    (hsev0 : ∀ᵐ ω ∂P, ∀ n o, 0 ≤ sev n o ω) (hsev : ∀ᵐ ω ∂P, ∀ n o, sev n o ω ≤ Cs)
    (hzt : ∀ᵐ ω ∂P, ∀ n o, ‖zt n o ω‖ ^ 2 ≤ B ^ 2)
    (hi : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
        aa n ω ^ 2 * (Fintype.card (Ob n) : ℝ) * (B ^ 2 * Cs)) atTop (𝓝 0))
    (hiii : ∀ᵐ ω ∂P, ∀ t : EuclideanSpace ℝ (Fin K),
      Tendsto (fun n : ℕ => aa n ω ^ 2 * ∑ j, ⟪zc n j ω, t⟫ ^ 2 * vr n j ω) atTop
        (𝓝 (t ⬝ᵥ (Ups *ᵥ t))))
    (hmx0 : ∀ᵐ ω ∂P, ∀ n, 0 ≤ mx n ω)
    (hmx : ∀ᵐ ω ∂P, ∀ n j, ‖zc n j ω‖ ^ 2 ≤ mx n ω)
    (hmxsum : ∀ᵐ ω ∂P, ∀ n, mx n ω ≤ ∑ j, ‖zc n j ω‖ ^ 2)
    (hiv : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => mx n ω / ∑ j, ‖zc n j ω‖ ^ 2) atTop (𝓝 0))
    (hA : ∀ᵐ ω ∂P, Tendsto (fun n => matCLM (Amat n ω)) atTop (𝓝 Psiinv))
    (hsand : ∀ t : EuclideanSpace ℝ (Fin K),
      (ContinuousLinearMap.adjoint Psiinv t)
          ⬝ᵥ (Ups *ᵥ (ContinuousLinearMap.adjoint Psiinv t))
        = t ⬝ᵥ (Sg *ᵥ t))
    (Uh : ℕ → Om → Matrix (Fin K) (Fin K) ℝ) (Upn : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (hHerm : ∀ n ω, (Uh n ω).IsHermitian) (hUmeas : ∀ n, Measurable (Uh n))
    (ha0 : TendstoInMeasure P (fun n ω => frobNorm (Uh n ω - Upn n)) atTop (fun _ => 0))
    (hlim : Tendsto (fun n => frobNorm (Upn n - Sg)) atTop (𝓝 0)) :
    Tendsto (fun n => P {ω | ((Nsd n)⁻¹ • Uh n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => Wald.waldStat ((Nsd n)⁻¹ • Uh n ω) (pih n ω - pi0)) atTop
          (fun z : EuclideanSpace ℝ (Fin K) => ‖z‖ ^ 2) (fun _ => P)
          (multivariateGaussian 0 1) :=
  piinf_wald_of_meat_of_pi_clt (P := P) hNsd hSgPD hHerm hUmeas ha0 hlim
    (pi_clt_std_unconditional_of_design_closed h𝒟 P aa mx (fun n _ => Nsd n) zc zt etab eps
      vr sev C B Cs v0 Ups Sg hUps hSgPD.posSemidef Amat Psiinv pih pi0 haD hzcD hztD hAD
      (fun n _ => hNsd n) hmeasη hmeasε hWm hsolve hindepη hmeanη hL2η hint4η hvarη hmomη
      hv0 hvr hindepε hL2ε hmeanε hvarε hsev0 hsev hzt hi hiii hmx0 hmx hmxsum hiv hA hsand)

end DesignDecondClosed

section PiDesignWitness

namespace PiDesignWitness

open Multiway.SteinCluster.FrozenDesignWitness
open Multiway.PiInf.PiWitness
open scoped RealInnerProductSpace

/-- Transfer of an independent family along `map snd = P1`. -/
theorem iIndepFun_of_snd {ι : Type*} {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]
    {μ : Measure Aw} (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1)
    {F : ∀ i, Cw → γ i} (hF : ∀ i, Measurable (F i)) (h : iIndepFun F P1) :
    iIndepFun (fun i (y : Aw) => F i y.2) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  have hmeas : MeasurableSet (⋂ i ∈ S, F i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi => (hF i) (hs i hi)
  have hpre : (⋂ i ∈ S, (fun y : Aw => F i y.2) ⁻¹' sets i)
      = Prod.snd ⁻¹' (⋂ i ∈ S, F i ⁻¹' sets i) := by
    ext y
    simp only [Set.mem_iInter, Set.mem_preimage]
  rw [hpre, ← Measure.map_apply measurable_snd hmeas, hmap,
    h.measure_inter_preimage_eq_mul S hs]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [show ((fun y : Aw => F i y.2) ⁻¹' sets i) = Prod.snd ⁻¹' (F i ⁻¹' sets i) from rfl,
    ← Measure.map_apply measurable_snd ((hF i) (hs i hi)), hmap]

theorem abs_sgnA (y : Aw) : |sgnA y| = 1 := by
  by_cases h : y.1 <;> simp [sgnA, h]

theorem meas_sgnA' : Measurable sgnA := meas_sgnA.mono Dw_le le_rfl

/-- The category weight, with its sign read off the design coin. -/
noncomputable def pzc (n : ℕ) (j : wJ n) (y : Aw) : EuclideanSpace ℝ (Fin 1) :=
  sgnA y • wzc n j

/-- The observation row, with the same sign. -/
noncomputable def pzt (n : ℕ) (o : wO n) (y : Aw) : EuclideanSpace ℝ (Fin 1) :=
  sgnA y • wzt n o

/-- The category effect: the `(2n, j)` coin. -/
noncomputable def peta (n : ℕ) (j : wJ n) (y : Aw) : ℝ := coinSign (2 * n, j.val) y.2

/-- The idiosyncratic error: the `(2n+1, o)` coin. -/
noncomputable def peps (n : ℕ) (o : wO n) (y : Aw) : ℝ := coinSign (2 * n + 1, o.val) y.2

/-- `Ψ̂_n = I` at every index. -/
noncomputable def pAmat (_ : ℕ) (_ : Aw) : Matrix (Fin 1) (Fin 1) ℝ := 1

/-- `π̂_n`, by the solved form of Lemma SM.B.4 at the random design. -/
noncomputable def ppih (n : ℕ) (y : Aw) : EuclideanSpace ℝ (Fin 1) :=
  (0 : EuclideanSpace ℝ (Fin 1)) + (Real.sqrt (wNs n))⁻¹ •
    matCLM (pAmat n y) (wa n •
      ((∑ j, peta n j y • pzc n j y) + (∑ o, peps n o y • pzt n o y)))

theorem meas_peta (n : ℕ) (j : wJ n) : Measurable (peta n j) :=
  (meas_coinSign (2 * n, j.val)).comp measurable_snd

theorem meas_peps (n : ℕ) (o : wO n) : Measurable (peps n o) :=
  (meas_coinSign (2 * n + 1, o.val)).comp measurable_snd

theorem peta_pow_four (n : ℕ) (j : wJ n) (y : Aw) : peta n j y ^ 4 = 1 :=
  coinSign_pow_four (2 * n, j.val) y.2

theorem peps_pow_four (n : ℕ) (o : wO n) (y : Aw) : peps n o y ^ 4 = 1 :=
  coinSign_pow_four (2 * n + 1, o.val) y.2

theorem peta_sq (n : ℕ) (j : wJ n) (y : Aw) : peta n j y * peta n j y = 1 :=
  coinSign_sq (2 * n, j.val) y.2

theorem peps_sq (n : ℕ) (o : wO n) (y : Aw) : peps n o y * peps n o y = 1 :=
  coinSign_sq (2 * n + 1, o.val) y.2

theorem abs_peta (n : ℕ) (j : wJ n) (y : Aw) : |peta n j y| ≤ 1 :=
  abs_coinSign_le (2 * n, j.val) y.2

theorem abs_peps (n : ℕ) (o : wO n) (y : Aw) : |peps n o y| ≤ 1 :=
  abs_coinSign_le (2 * n + 1, o.val) y.2

theorem smul_pzc (n : ℕ) (j : wJ n) (y : Aw) :
    peta n j y • pzc n j y = (peta n j y * sgnA y) • wzc n j := by
  rw [pzc, smul_smul]

theorem smul_pzt (n : ℕ) (o : wO n) (y : Aw) :
    peps n o y • pzt n o y = (peps n o y * sgnA y) • wzt n o := by
  rw [pzt, smul_smul]

theorem meas_ppih (n : ℕ) : Measurable (ppih n) := by
  have h1 : Measurable fun y : Aw => ∑ j, peta n j y • pzc n j y := by
    refine Finset.measurable_sum _ fun j _ => ?_
    have he : (fun y : Aw => peta n j y • pzc n j y)
        = fun y => (peta n j y * sgnA y) • wzc n j := funext fun y => smul_pzc n j y
    rw [he]
    exact ((meas_peta n j).mul meas_sgnA').smul_const _
  have h2 : Measurable fun y : Aw => ∑ o, peps n o y • pzt n o y := by
    refine Finset.measurable_sum _ fun o _ => ?_
    have he : (fun y : Aw => peps n o y • pzt n o y)
        = fun y => (peps n o y * sgnA y) • wzt n o := funext fun y => smul_pzt n o y
    rw [he]
    exact ((meas_peps n o).mul meas_sgnA').smul_const _
  exact measurable_const.add
    (((matCLM (1 : Matrix (Fin 1) (Fin 1) ℝ)).continuous.measurable.comp
      ((h1.add h2).const_smul (wa n))).const_smul ((Real.sqrt (wNs n))⁻¹))

theorem inner_pzc_sq (n : ℕ) (j : wJ n) (y : Aw) (t : EuclideanSpace ℝ (Fin 1)) :
    ⟪pzc n j y, t⟫ ^ 2 = ⟪wzc n j, t⟫ ^ 2 := by
  rw [pzc, real_inner_smul_left, mul_pow, show sgnA y ^ 2 = 1 by rw [sq]; exact sgnA_mul y,
    one_mul]

theorem norm_pzc_sq (n : ℕ) (j : wJ n) (y : Aw) : ‖pzc n j y‖ ^ 2 = ‖wzc n j‖ ^ 2 := by
  rw [pzc, norm_smul, Real.norm_eq_abs, abs_sgnA, one_mul]

theorem norm_pzt_sq (n : ℕ) (o : wO n) (y : Aw) : ‖pzt n o y‖ ^ 2 = ‖wzt n o‖ ^ 2 := by
  rw [pzt, norm_smul, Real.norm_eq_abs, abs_sgnA, one_mul]

/-- `MemLp` at exponent `2` for a coin sign under any probability measure on `Aw`. -/
theorem memLp_of_bound {μ : Measure Aw} [IsProbabilityMeasure μ] {f : Aw → ℝ}
    (hf : Measurable f) (hb : ∀ y, |f y| ≤ 1) : MemLp f 2 μ :=
  (memLp_top_of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb y)).mono_exponent
    le_top

theorem variance_of_sq {μ : Measure Aw} [IsProbabilityMeasure μ] {f : Aw → ℝ}
    (hf : MemLp f 2 μ) (h0 : ∫ y, f y ∂μ = 0) (h1 : ∀ y, f y * f y = 1) :
    Var[f; μ] = 1 := by
  rw [ProbabilityTheory.variance_eq_sub hf, h0]
  have he : (fun y => f y ^ 2) = fun _ => (1 : ℝ) := by
    funext y; rw [sq]; exact h1 y
  simp [he]

theorem indep_peta (n : ℕ) : iIndepFun (fun j : wJ n => coinSign (2 * n, j.val)) P1 :=
  indep_coinSign.precomp (g := fun j : wJ n => (2 * n, j.val))
    (fun _ _ hab => Fin.val_injective (congrArg Prod.snd hab))

theorem indep_peps (n : ℕ) : iIndepFun (fun o : wO n => coinSign (2 * n + 1, o.val)) P1 :=
  indep_coinSign.precomp (g := fun o : wO n => (2 * n + 1, o.val))
    (fun _ _ hab => Fin.val_injective (congrArg Prod.snd hab))

theorem integral_peta {μ : Measure Aw} (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1)
    (n : ℕ) (j : wJ n) : ∫ y, peta n j y ∂μ = 0 :=
  (integral_of_snd hmap (meas_coinSign (2 * n, j.val))).trans
    (integral_coinSign (2 * n, j.val))

theorem integral_peps {μ : Measure Aw} (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1)
    (n : ℕ) (o : wO n) : ∫ y, peps n o y ∂μ = 0 :=
  (integral_of_snd hmap (meas_coinSign (2 * n + 1, o.val))).trans
    (integral_coinSign (2 * n + 1, o.val))

theorem hi_witness : Tendsto
    (fun n : ℕ => wa n ^ 2 * (Fintype.card (wO n) : ℝ) * ((1 : ℝ) ^ 2 * 1)) atTop (𝓝 0) := by
  refine tendsto_inv_succ.congr fun n => ?_
  rw [wa, Fintype.card_fin]
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem hiv_witness : Tendsto (fun n : ℕ => wmx n / ∑ j, ‖wzc n j‖ ^ 2) atTop (𝓝 0) := by
  have h := tendsto_inv_succ.pow 2
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at h
  refine h.congr fun n => ?_
  rw [wmx, sum_norm_sq_wzc]
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem hmxsum_witness (n : ℕ) : wmx n ≤ ∑ j, ‖wzc n j‖ ^ 2 := by
  rw [wmx, sum_norm_sq_wzc]
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [h0]
  calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 2 * 1 := by ring
    _ ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) + 1)]
    _ = ((n : ℝ) + 1) ^ 4 := by ring

/-- The deconditioned Theorem 6 on a non-trivial `𝒟`. -/
theorem pi_clt_unconditional_of_design_closed_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (j : wJ n) (y : Aw),
        pzc n j y = (if y.1 then (1 : ℝ) else -1) • wzc n j)
    ∧ (∀ᵐ ω ∂Pw, ∀ (n : ℕ) (j : wJ n),
        Var[peta n j; condExpKernel Pw Dw ω] = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) y => Real.sqrt (wNs n) • (ppih n y - (0 : EuclideanSpace ℝ (Fin 1))))
        atTop (fun z => (matCLM (1 : Matrix (Fin 1) (Fin 1) ℝ)) z) (fun _ => Pw)
        (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  classical
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ _ => rfl, ?_, ?_⟩
  · filter_upwards [map_snd_condExpKernel] with ω hω n j
    exact variance_of_sq (memLp_of_bound (meas_peta n j) (abs_peta n j))
      (integral_peta hω n j) (peta_sq n j)
  · refine pi_clt_unconditional_of_design_closed (𝒟 := Dw) (Jc := wJ) (Ob := wO)
      Dw_le Pw (fun n _ => wa n) (fun n _ => wNs n) (fun n _ => wmx n) pzc pzt peta peps
      (fun _ _ _ => 1) (fun _ _ _ => 1) 1 1 1 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)
      Matrix.PosDef.one pAmat (matCLM (1 : Matrix (Fin 1) (Fin 1) ℝ)) ppih 0
      (fun _ => measurable_const)
      (fun n j => meas_sgnA.smul_const (wzc n j)) (fun n o => meas_sgnA.smul_const (wzt n o))
      (fun _ _ _ => measurable_const)
      (fun n _ => by rw [wNs]; positivity) meas_peta meas_peps
      (fun n => ((meas_ppih n).sub_const 0).const_smul (Real.sqrt (wNs n)))
      (Filter.Eventually.of_forall fun n y =>
        sqrt_smul_solved (by rw [wNs]; positivity :
          (0 : ℝ) < wNs n) (0 : EuclideanSpace ℝ (Fin 1)) _)
      ?_ ?_ ?_ ?_ ?_ ?_ zero_lt_one (Filter.Eventually.of_forall fun _ _ _ => le_refl 1)
      ?_ ?_ ?_ ?_ (Filter.Eventually.of_forall fun _ _ _ => zero_le_one)
      (Filter.Eventually.of_forall fun _ _ _ => le_refl 1) ?_
      (Filter.Eventually.of_forall fun _ => hi_witness) ?_
      (Filter.Eventually.of_forall fun _ n => by rw [wmx]; positivity) ?_ ?_ ?_
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
    · filter_upwards [map_snd_condExpKernel] with ω hω n
      exact iIndepFun_of_snd hω (fun j : wJ n => meas_coinSign (2 * n, j.val)) (indep_peta n)
    · filter_upwards [map_snd_condExpKernel] with ω hω n j
      exact integral_peta hω n j
    · exact Filter.Eventually.of_forall fun _ n j =>
        memLp_of_bound (meas_peta n j) (abs_peta n j)
    · refine Filter.Eventually.of_forall fun ω n j => ?_
      have he : (fun y : Aw => peta n j y ^ 4) = fun _ => (1 : ℝ) :=
        funext fun y => peta_pow_four n j y
      rw [he]
      exact integrable_const 1
    · filter_upwards [map_snd_condExpKernel] with ω hω n j
      exact variance_of_sq (memLp_of_bound (meas_peta n j) (abs_peta n j))
        (integral_peta hω n j) (peta_sq n j)
    · refine Filter.Eventually.of_forall fun ω n j => ?_
      have he : (fun y : Aw => peta n j y ^ 4) = fun _ => (1 : ℝ) :=
        funext fun y => peta_pow_four n j y
      rw [he]
      simp
    · filter_upwards [map_snd_condExpKernel] with ω hω n
      exact iIndepFun_of_snd hω (fun o : wO n => meas_coinSign (2 * n + 1, o.val))
        (indep_peps n)
    · exact Filter.Eventually.of_forall fun _ n o =>
        memLp_of_bound (meas_peps n o) (abs_peps n o)
    · filter_upwards [map_snd_condExpKernel] with ω hω n o
      exact integral_peps hω n o
    · filter_upwards [map_snd_condExpKernel] with ω hω n o
      exact variance_of_sq (memLp_of_bound (meas_peps n o) (abs_peps n o))
        (integral_peps hω n o) (peps_sq n o)
    · refine Filter.Eventually.of_forall fun ω n o => ?_
      rw [norm_pzt_sq, norm_sq_wzt]
      norm_num
    · refine Filter.Eventually.of_forall fun ω t => ?_
      rw [dotProduct_one_witness t]
      refine tendsto_const_nhds.congr fun n => ?_
      have hterm : ∀ j : wJ n, ⟪pzc n j ω, t⟫ ^ 2 * (1 : ℝ) = ⟪wzc n j, t⟫ ^ 2 * (1 : ℝ) :=
        fun j => by rw [inner_pzc_sq]
      rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j]
      exact (upsilon_witness t n).symm
    · refine Filter.Eventually.of_forall fun ω n j => ?_
      rw [norm_pzc_sq, norm_sq_wzc, wmx]
    · exact Filter.Eventually.of_forall fun ω n => by
        simpa only [norm_pzc_sq] using hmxsum_witness n
    · refine Filter.Eventually.of_forall fun ω => ?_
      simpa only [norm_pzc_sq] using hiv_witness

end PiDesignWitness

end PiDesignWitness

end PiThirteen


end PiInf

end Multiway
