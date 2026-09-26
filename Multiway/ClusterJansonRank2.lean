/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Multiway.ClusterJansonB

/-!
# A rank-2 witness on a non-trivial `𝒟`

This file exhibits a design satisfying every hypothesis of the vector form of Theorem 5(a)
(`ClusterJanson.cltcluster_a_general_betaJM_janson_unconditional_vector_of_dep`) at `r = 2`,
on the proper sub-σ-field `Dw`, with a random `𝒟`-measurable design, a non-transitive `J = 2`
sharing relation, and a restricted variance `𝒱_n` that is not a multiple of the identity.

## The design

`N_n = 2(n+3)` observations indexed by `Fin (n+3) × Fin 2`; observation `(o, j)` carries the
`j`-th regressor alone at level `w_j` (`w_0 = 1`, `w_1 = 2`). Hence
`X̃_n'X̃_n = diag(n+3, 4(n+3))`, `𝓡_n = I_2`, `Ω_n = I` and
`𝒱_n = diag((n+3)^{-1}, (4(n+3))^{-1})`. The dependency graph is `pathG` on the first index,
so `D_n = 5`, `λ_min(Ω_n) = n+3` and `δ_n = 250/(n+3) → 0`. The disturbances are fair signs.

## Main results

* `rk2_restrictedVar_ne_smul_one`: `𝒱_n` is not a multiple of the identity.
* `cltcluster_a_general_betaJM_janson_unconditional_vector_rank2_witness`: the witness.
-/

namespace Multiway.ClusterJanson

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators MatrixOrder
open Matrix
open Causalean.Mathlib.Probability.SteinMethod
open Multiway.SteinCluster
open Multiway.SteinCluster.FrozenDesignWitness

namespace Rank2Witness

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-! ### The design and its Gram matrix -/

/-- the two regressor levels, `w_0 = 1` and `w_1 = 2` -/
noncomputable def rk2w : Fin 2 → ℝ := fun k => if k = 0 then 1 else 2

theorem rk2w_ne_zero (k : Fin 2) : rk2w k ≠ 0 := by
  fin_cases k <;> norm_num [rk2w]

theorem one_le_rk2w_sq (k : Fin 2) : (1 : ℝ) ≤ (rk2w k) ^ 2 := by
  fin_cases k <;> norm_num [rk2w]

theorem rk2w_sq_le_four (k : Fin 2) : (rk2w k) ^ 2 ≤ 2 ^ 2 := by
  fin_cases k <;> norm_num [rk2w]

/-- `X̃_n`: observation `(o, j)` carries the `j`-th regressor alone, at level `w_j`. -/
noncomputable def rk2Xt (n : ℕ) : Matrix (Fin (n + 3) × Fin 2) (Fin 2) ℝ :=
  fun p k => if p.2 = k then rk2w k else 0

/-- the diagonal of the Gram matrix, `(n+3)w_k²` -/
noncomputable def rk2d (n : ℕ) : Fin 2 → ℝ := fun k => ((n : ℝ) + 3) * (rk2w k) ^ 2

theorem rk2d_pos (n : ℕ) (k : Fin 2) : 0 < rk2d n k := by
  have h1 := one_le_rk2w_sq k
  have h2 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have : (0 : ℝ) < (rk2w k) ^ 2 := by linarith
  exact mul_pos h2 this

theorem rk2d_ne_zero (n : ℕ) (k : Fin 2) : rk2d n k ≠ 0 := ne_of_gt (rk2d_pos n k)

theorem rk2d_zero (n : ℕ) : rk2d n 0 = (n : ℝ) + 3 := by
  simp [rk2d, rk2w]

theorem rk2d_one (n : ℕ) : rk2d n 1 = ((n : ℝ) + 3) * 4 := by
  norm_num [rk2d, rk2w]

/-- `X̃_n'X̃_n = diag((n+3)w_0², (n+3)w_1²)`. -/
theorem rk2Gram (n : ℕ) : (rk2Xt n)ᵀ * rk2Xt n = Matrix.diagonal (rk2d n) := by
  classical
  ext k k'
  show ∑ p : Fin (n + 3) × Fin 2, rk2Xt n p k * rk2Xt n p k'
      = Matrix.diagonal (rk2d n) k k'
  rw [Fintype.sum_prod_type]
  have hinner : ∀ o : Fin (n + 3),
      (∑ j : Fin 2, rk2Xt n (o, j) k * rk2Xt n (o, j) k')
        = if k = k' then (rk2w k) ^ 2 else 0 := by
    intro o
    rw [Finset.sum_eq_single k]
    · by_cases hkk : k = k'
      · subst hkk; simp [rk2Xt, sq]
      · simp [rk2Xt, hkk]
    · intro j _ hj
      simp [rk2Xt, hj]
    · intro h
      exact absurd (Finset.mem_univ k) h
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Matrix.diagonal_apply]
  by_cases hkk : k = k'
  · subst hkk
    have e1 : (if k = k then (rk2w k) ^ 2 else (0 : ℝ)) = (rk2w k) ^ 2 := by simp
    have e2 : (if k = k then rk2d n k else (0 : ℝ)) = rk2d n k := by simp
    rw [e1, e2, rk2d]
    push_cast
    ring
  · rw [ite_eq_right hkk, ite_eq_right hkk, mul_zero]

theorem rk2_scoreVar (n : ℕ) :
    scoreVar (rk2Xt n) (1 : Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ)
      = Matrix.diagonal (rk2d n) := by
  rw [scoreVar, Matrix.mul_one, rk2Gram]

/-- The inverse of a diagonal matrix with nonvanishing diagonal, by exhibiting the right
inverse. -/
theorem inv_diagonal_of_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℝ}
    (hd : ∀ k, d k ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun k => (d k)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun k => d k * (d k)⁻¹) = fun _ : ι => (1 : ℝ) :=
    funext fun k => mul_inv_cancel₀ (hd k)
  show Matrix.diagonal (fun k => d k * (d k)⁻¹) = 1
  rw [h]
  exact Matrix.diagonal_one

theorem rk2_scoreMap (n : ℕ) :
    scoreMap (rk2Xt n) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.diagonal (fun k => (rk2d n k)⁻¹) := by
  rw [scoreMap, Matrix.transpose_one, Matrix.mul_one, rk2Gram,
    inv_diagonal_of_ne_zero (rk2d_ne_zero n)]

/-- `𝒱_n = (X̃_n'X̃_n)^{-1} = diag((n+3)^{-1}, (4(n+3))^{-1})`. -/
theorem rk2_restrictedVar (n : ℕ) :
    restrictedVar (rk2Xt n) (1 : Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.diagonal (fun k => (rk2d n k)⁻¹) := by
  rw [restrictedVar, rk2_scoreMap, rk2_scoreVar, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  show (rk2d n k)⁻¹ * rk2d n k * (rk2d n k)⁻¹ = (rk2d n k)⁻¹
  rw [inv_mul_cancel₀ (rk2d_ne_zero n k), one_mul]

/-- `𝒱_n` is not a multiple of the identity, so the standardization mixes the two
coordinates. -/
theorem rk2_restrictedVar_ne_smul_one (n : ℕ) (c : ℝ) :
    restrictedVar (rk2Xt n) (1 : Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ)
      ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  rw [rk2_restrictedVar] at h
  have h00 : (rk2d n 0)⁻¹ = c := by
    have := congrFun (congrFun h 0) 0
    simpa [Matrix.diagonal_apply, Matrix.one_apply] using this
  have h11 : (rk2d n 1)⁻¹ = c := by
    have := congrFun (congrFun h 1) 1
    simpa [Matrix.diagonal_apply, Matrix.one_apply] using this
  rw [rk2d_zero] at h00
  rw [rk2d_one] at h11
  have hpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have hne : ((n : ℝ) + 3) ≠ 0 := ne_of_gt hpos
  have e1 : c * ((n : ℝ) + 3) = 1 := by rw [← h00]; field_simp
  have e2 : c * (((n : ℝ) + 3) * 4) = 1 := by rw [← h11]; field_simp
  have e3 : (c * ((n : ℝ) + 3)) * 4 = 1 := by rw [← e2]; ring
  rw [e1] at e3
  norm_num at e3

theorem rk2_hfloor (n : ℕ) :
    ((n : ℝ) + 3) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      ≤ scoreVar (rk2Xt n) (1 : Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ) := by
  classical
  rw [rk2_scoreVar, Matrix.le_iff]
  have hsmul : ((n : ℝ) + 3) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.diagonal (fun _ : Fin 2 => (n : ℝ) + 3) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hdiff : Matrix.diagonal (rk2d n) - ((n : ℝ) + 3) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.diagonal (fun k => rk2d n k - ((n : ℝ) + 3)) := by
    rw [hsmul]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hdiff]
  refine Matrix.PosSemidef.diagonal ?_
  rw [Pi.le_def]
  intro k
  have h1 := one_le_rk2w_sq k
  have h2 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have h3 : ((n : ℝ) + 3) * 1 ≤ ((n : ℝ) + 3) * (rk2w k) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 h2.le
  show (0 : ℝ) ≤ rk2d n k - ((n : ℝ) + 3)
  simp only [rk2d]
  linarith

theorem rk2_hA (n : ℕ) :
    Function.Injective (scoreMap (rk2Xt n) (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec := by
  refine Matrix.mulVec_injective_of_isUnit ?_
  rw [rk2_scoreMap, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  refine isUnit_iff_ne_zero.mpr ?_
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  exact inv_ne_zero (rk2d_ne_zero n k)

theorem rk2_row_dot (n : ℕ) (p : Fin (n + 3) × Fin 2) :
    (fun k => rk2Xt n p k) ⬝ᵥ (fun k => rk2Xt n p k) = (rk2w p.2) ^ 2 := by
  classical
  show ∑ k : Fin 2, rk2Xt n p k * rk2Xt n p k = (rk2w p.2) ^ 2
  rw [Finset.sum_eq_single p.2]
  · simp [rk2Xt, sq]
  · intro j _ hj
    simp [rk2Xt, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ p.2) h

/-! ### The disturbances on the product coin space -/

/-- the coin index of observation `(o, j)` at sample size `n` -/
def rk2Idx (n : ℕ) (p : Fin (n + 3) × Fin 2) : ℕ × ℕ := (n, 2 * p.1.val + p.2.val)

theorem rk2Idx_injective (n : ℕ) : Function.Injective (rk2Idx n) := by
  intro p q h
  have h2 : 2 * p.1.val + p.2.val = 2 * q.1.val + q.2.val := congrArg Prod.snd h
  have hp2 := p.2.isLt
  have hq2 := q.2.isLt
  have h1 : p.1.val = q.1.val := by omega
  have h3 : p.2.val = q.2.val := by omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h3)

noncomputable def rk2vSign (n : ℕ) (p : Fin (n + 3) × Fin 2) (z : Cw) : ℝ :=
  coinSign (rk2Idx n p) z

noncomputable def rk2uSign (n : ℕ) (p : Fin (n + 3) × Fin 2) (y : Aw) : ℝ :=
  rk2vSign n p y.2

theorem meas_rk2vSign (n : ℕ) (p : Fin (n + 3) × Fin 2) : Measurable (rk2vSign n p) :=
  meas_coinSign (rk2Idx n p)

theorem meas_rk2uSign (n : ℕ) (p : Fin (n + 3) × Fin 2) : Measurable (rk2uSign n p) :=
  (meas_rk2vSign n p).comp measurable_snd

theorem abs_rk2vSign_le (n : ℕ) (p : Fin (n + 3) × Fin 2) (z : Cw) : |rk2vSign n p z| ≤ 1 :=
  abs_coinSign_le (rk2Idx n p) z

theorem indep_rk2vSign (n : ℕ) : iIndepFun (rk2vSign n) P1 :=
  indep_coinSign.precomp (g := rk2Idx n) (rk2Idx_injective n)

theorem integral_rk2vSign (n : ℕ) (p : Fin (n + 3) × Fin 2) :
    ∫ z, rk2vSign n p z ∂P1 = 0 :=
  integral_coinSign (rk2Idx n p)

theorem integral_rk2vSign_mul (n : ℕ) (p q : Fin (n + 3) × Fin 2) :
    ∫ z, rk2vSign n p z * rk2vSign n q z ∂P1
      = (1 : Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ) p q := by
  have h : (∫ z, rk2vSign n p z * rk2vSign n q z ∂P1)
      = if (rk2Idx n p = rk2Idx n q) then (1 : ℝ) else 0 :=
    integral_coinSign_mul (rk2Idx n p) (rk2Idx n q)
  rw [h, Matrix.one_apply]
  by_cases hh : p = q
  · subst hh; simp
  · have hne : ¬ (rk2Idx n p = rk2Idx n q) := fun hc => hh (rk2Idx_injective n hc)
    rw [ite_eq_right hne, ite_eq_right hh]

/-! ### The `J = 2` dependency graph on the product index set -/

/-- The `pathG` neighbourhood of `o` has at most three members. -/
theorem card_pathFilter_le (n : ℕ) (o : Fin (n + 3)) :
    (Finset.univ.filter (fun o' : Fin (n + 3) => pathG (n + 3) o o')).card ≤ 3 := by
  classical
  have hsub : (Finset.univ.filter (fun o' : Fin (n + 3) => pathG (n + 3) o o')) ⊆
      ((Finset.univ.filter (fun o' : Fin (n + 3) => o'.val = o.val))
        ∪ (Finset.univ.filter (fun o' : Fin (n + 3) => o'.val + 1 = o.val)))
      ∪ (Finset.univ.filter (fun o' : Fin (n + 3) => o.val + 1 = o'.val)) := by
    intro j hj
    have hG : pathG (n + 3) o j := (Finset.mem_filter.mp hj).2
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

/-- the dependency graph under `ℙ_ω`: `(o, j) ∼ (o', j')` iff `|o − o'| ≤ 1` -/
noncomputable def rk2Dep {μ : Measure Aw} [IsProbabilityMeasure μ]
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1) (n : ℕ) :
    DepGraph (rk2uSign n) μ where
  G := fun p q => pathG (n + 3) p.1 q.1
  decG := fun _ _ => inferInstance
  refl := fun _ => Or.inl rfl
  symm := fun p q h => by unfold pathG at h ⊢; omega
  meas := meas_rk2uSign n
  indep := by
    intro A Bs h
    have hdisj : Disjoint A Bs := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact h a ha a hb (Or.inl rfl)
    have hP1 : IndepFun
        (fun z : Cw => fun k : ↥A => rk2vSign n (k : Fin (n + 3) × Fin 2) z)
        (fun z : Cw => fun k : ↥Bs => rk2vSign n (k : Fin (n + 3) × Fin 2) z) P1 :=
      (indep_rk2vSign n).indepFun_finset A Bs hdisj (meas_rk2vSign n)
    exact indepFun_of_snd
      (F := fun z : Cw => fun k : ↥A => rk2vSign n (k : Fin (n + 3) × Fin 2) z)
      (G := fun z : Cw => fun k : ↥Bs => rk2vSign n (k : Fin (n + 3) × Fin 2) z) hmap
      (Measurable.of_eval fun k : ↥A => meas_rk2vSign n (k : Fin (n + 3) × Fin 2))
      (Measurable.of_eval fun k : ↥Bs => meas_rk2vSign n (k : Fin (n + 3) × Fin 2)) hP1

/-- Every closed neighbourhood has at most `3 × 2 = 6` members, so `D_n = 5` serves. -/
theorem rk2Dep_nbhd_card {μ : Measure Aw} [IsProbabilityMeasure μ]
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1) (n : ℕ) (p : Fin (n + 3) × Fin 2) :
    ((rk2Dep hmap n).nbhd p).card ≤ 6 := by
  classical
  have hsub : (rk2Dep hmap n).nbhd p ⊆
      (Finset.univ.filter (fun o' : Fin (n + 3) => pathG (n + 3) p.1 o'))
        ×ˢ (Finset.univ : Finset (Fin 2)) := by
    intro q hq
    have hG : pathG (n + 3) p.1 q.1 := (rk2Dep hmap n).mem_nbhd_iff.mp hq
    simp [Finset.mem_product, Finset.mem_filter, hG]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have := card_pathFilter_le n p.1
  omega

/-! ### The random design, the estimator and the rate -/

/-- the design at index `n`, with the sign of the design coin: `𝒟`-measurable and non-constant -/
noncomputable def rk2gXt (n : ℕ) (y : Aw) : Matrix (Fin (n + 3) × Fin 2) (Fin 2) ℝ :=
  sgnA y • rk2Xt n

/-- the conditional second-moment matrix of the disturbances -/
noncomputable def rk2Om (n : ℕ) (_ : Aw) :
    Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ := 1

noncomputable def rk2Bhat (n : ℕ) (y : Aw) : Fin 2 → ℝ :=
  ((rk2gXt n y)ᵀ * rk2gXt n y)⁻¹ *ᵥ ((rk2gXt n y)ᵀ *ᵥ (fun p => rk2uSign n p y))

theorem rk2_hXtD (n : ℕ) (p : Fin (n + 3) × Fin 2) (k : Fin 2) :
    Measurable[Dw] fun y => rk2gXt n y p k := by
  have h : (fun y : Aw => rk2gXt n y p k) = fun y => sgnA y * rk2Xt n p k := rfl
  rw [h]
  exact meas_sgnA.mul_const _

theorem rk2_card (n : ℕ) : Fintype.card (Fin (n + 3) × Fin 2) = (n + 3) * 2 := by
  simp [Fintype.card_prod]

/-- `δ_n = 2(n+3)·5³/(n+3)² = 250/(n+3) → 0`, the accumulation-rate condition. -/
theorem tendsto_rk2_accumRate :
    Tendsto (fun n : ℕ => accumRate ((n + 3) * 2) 5 ((n : ℝ) + 3)) atTop (𝓝 0) := by
  have hacc : ∀ n : ℕ, accumRate ((n + 3) * 2) 5 ((n : ℝ) + 3) = 250 / ((n : ℝ) + 3) := by
    intro n
    unfold accumRate
    have hc : (((n + 3) * 2 : ℕ) : ℝ) = ((n : ℝ) + 3) * 2 := by push_cast; ring
    have h5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
    rw [hc, h5]
    have hne : ((n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  simp only [hacc]
  have hd : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa using (tendsto_const_nhds (x := (250 : ℝ)) (f := atTop (α := ℕ))).div_atTop hd

end Rank2Witness

/-! ### The witness -/

section Rank2

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.SteinCluster.FrozenDesignWitness
open Multiway.ClusterJanson.Rank2Witness

/-- **Rank-2 witness for Theorem 5(a).** The design coin is fair; `𝒟` is a proper sub-σ-field;
`ℙ_ω ≠ P`; the design `±X̃_n` is random; the sharing relation is not transitive; the restriction
dimension is `2`; `𝒱_n` is not a multiple of the identity for any `n`, `ω` and scalar; and
`𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_2)` under `P`. -/
theorem cltcluster_a_general_betaJM_janson_unconditional_vector_rank2_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), rk2gXt n y = (if y.1 then (1 : ℝ) else -1) • rk2Xt n)
    ∧ (∀ n : ℕ, ∃ a b c : Fin (n + 3),
        pathG (n + 3) a b ∧ pathG (n + 3) b c ∧ ¬ pathG (n + 3) a c)
    ∧ Fintype.card (Fin 2) = 2
    ∧ (∀ (n : ℕ) (y : Aw) (c : ℝ),
        restrictedVar (rk2gXt n y) (rk2Om n y) (1 : Matrix (Fin 2) (Fin 2) ℝ)
          ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) =>
          restrictedStat (rk2gXt n y) (rk2Om n y) (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (rk2Bhat n y - (0 : Fin 2 → ℝ)))
        atTop (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (fun _ => Pw)
        (stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ => rfl, pathG_not_transitive,
    Fintype.card_fin 2, ?_, ?_⟩
  · intro n y c
    rw [show rk2gXt n y = sgnA y • rk2Xt n from rfl,
      show rk2Om n y = (1 : Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ) from rfl,
      restrictedVar_smul (sgnA_mul y)]
    exact rk2_restrictedVar_ne_smul_one n c
  · let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
    refine cltcluster_a_general_betaJM_janson_unconditional_vector_of_dep
      (O := fun n => Fin (n + 3) × Fin 2)
      Dw_le Pw rk2gXt rk2Om (fun _ => 1) rk2uSign rk2Bhat (fun _ => 0)
      rk2_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
      (fun n _ => (n : ℝ) + 3) (fun _ _ => 5) 2 1 (by norm_num) zero_le_one
      (fun n p y => abs_rk2vSign_le n p y.2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [map_snd_condExpKernel] with ω hω
      exact ⟨fun n => rk2Dep hω n, fun n p => rk2Dep_nbhd_card hω n p⟩
    · refine Filter.Eventually.of_forall fun ω n => ?_
      rw [show rk2gXt n ω = sgnA ω • rk2Xt n from rfl, scoreMap_smul (sgnA_mul ω)]
      exact rk2_hA n
    · exact Filter.Eventually.of_forall fun _ n => by positivity
    · refine Filter.Eventually.of_forall fun ω n => ?_
      rw [show rk2gXt n ω = sgnA ω • rk2Xt n from rfl, scoreVar_smul (sgnA_mul ω),
        show rk2Om n ω = (1 : Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ) from rfl]
      exact rk2_hfloor n
    · filter_upwards [map_snd_condExpKernel] with ω hω
      intro n p q
      exact (integral_of_snd hω ((meas_rk2vSign n p).mul (meas_rk2vSign n q))).trans
        (integral_rk2vSign_mul n p q)
    · filter_upwards [map_snd_condExpKernel] with ω hω
      intro n p
      exact (integral_of_snd hω (meas_rk2vSign n p)).trans (integral_rk2vSign n p)
    · refine Filter.Eventually.of_forall fun ω n p => ?_
      have h : (fun k => rk2gXt n ω p k) ⬝ᵥ (fun k => rk2gXt n ω p k)
          = (rk2w p.2) ^ 2 := by
        have he : (fun k => rk2gXt n ω p k) = fun k => sgnA ω * rk2Xt n p k := rfl
        rw [he]
        show ∑ k : Fin 2, (sgnA ω * rk2Xt n p k) * (sgnA ω * rk2Xt n p k) = _
        have hre : ∀ k : Fin 2, (sgnA ω * rk2Xt n p k) * (sgnA ω * rk2Xt n p k)
            = rk2Xt n p k * rk2Xt n p k := by
          intro k
          have := sgnA_mul ω
          nlinarith [this]
        simp only [hre]
        exact rk2_row_dot n p
      rw [h]
      exact rk2w_sq_le_four p.2
    · exact Filter.Eventually.of_forall fun _ _ => by norm_num
    · refine Filter.Eventually.of_forall fun _ n => ?_
      rw [rk2_card n]
      omega
    · refine Filter.Eventually.of_forall fun _ => ?_
      have hc : ∀ n : ℕ, Fintype.card (Fin (n + 3) × Fin 2) = (n + 3) * 2 := rk2_card
      simpa [hc] using tendsto_rk2_accumRate

end Rank2

end Multiway.ClusterJanson
