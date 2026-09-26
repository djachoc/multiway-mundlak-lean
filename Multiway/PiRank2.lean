import Multiway.PiInf

/-!
# A `K = 2` example for the deconditioned Theorems 6 and 12(b)

This file builds a two-dimensional example satisfying every hypothesis of
`pi_clt_unconditional_of_design_closed` (the deconditioned form of Theorem 6) and of
`piinf_wald_unconditional_of_design_closed` (the deconditioned Wald statement of Theorem 12(b)),
and derives both conclusions through those theorems.

The design has `(n+1)²` categories in each of the directions `(1,0)` and `(1,1)`, with weight
length `s_n = (n+1) + (n+1)^{-1}`, so condition (iii) holds with `Υ_n = (1 + (n+1)^{-2})²Υ` and
`Υ = ((2,1),(1,1))`. With `Ψ` the `2 × 2` Hilbert matrix, `Ψ⁻¹ = ((4,−6),(−6,12))` and the
sandwich `Ψ⁻¹ΥΨ⁻¹ = ((20,−36),(−36,72))`; none of these is a multiple of the identity. The design
and `Ψ̂_n` depend on a fair coin measurable with respect to a proper sub-σ-field `Dw`, and `Ψ̂_n`
converges to `Ψ⁻¹` without being equal to it.

## Main results

* `pi_clt_unconditional_of_design_closed_rank2_witness`: the deconditioned limit law at `K = 2`.
* `piinf_wald_unconditional_of_design_closed_rank2_witness`: the deconditioned Wald limit at
  `K = 2`.
-/

namespace Multiway
namespace PiInf
namespace PiRank2Witness

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal RealInnerProductSpace
open Multiway.SteinCluster.FrozenDesignWitness
open Multiway.PiInf.PiWitness
open Multiway.PiInf.PiDesignWitness

/-! ### Two-dimensional vectors -/

theorem inner_fin_two (b a : EuclideanSpace ℝ (Fin 2)) : ⟪b, a⟫ = b 0 * a 0 + b 1 * a 1 := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The vector `(a, b)` of `ℝ²`. -/
noncomputable def qvecOf (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then a else b)

theorem qvecOf_zero (a b : ℝ) : qvecOf a b 0 = a := by
  show (if (0 : Fin 2) = 0 then a else b) = a
  simp

theorem qvecOf_one (a b : ℝ) : qvecOf a b 1 = b := by
  show (if (1 : Fin 2) = 0 then a else b) = b
  simp

/-- The two directions `qdir 0 = (1,0)` and `qdir 1 = (1,1)`, neither proportional nor
orthogonal. -/
noncomputable def qdir (d : Fin 2) : EuclideanSpace ℝ (Fin 2) := qvecOf 1 (d.val : ℝ)

theorem inner_qdir (d : Fin 2) (t : EuclideanSpace ℝ (Fin 2)) :
    ⟪qdir d, t⟫ = t 0 + (d.val : ℝ) * t 1 := by
  rw [inner_fin_two, qdir, qvecOf_zero, qvecOf_one, one_mul]

theorem norm_sq_qdir (d : Fin 2) : ‖qdir d‖ ^ 2 = 1 + (d.val : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_fin_two, qdir, qvecOf_zero, qvecOf_one]
  ring

theorem sgnA_true {y : Aw} (h : y.1 = true) : sgnA y = 1 := by simp [sgnA, h]

theorem sgnA_false {y : Aw} (h : y.1 = false) : sgnA y = -1 := by simp [sgnA, h]

theorem sgnA_ne_zero (y : Aw) : sgnA y ≠ 0 := by
  intro h
  have := abs_sgnA y
  rw [h] at this
  norm_num at this

theorem inv_succ_pos (n : ℕ) : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity

theorem inv_succ_le_one (n : ℕ) : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h := (div_le_one hpos).2 hge
  simpa [one_div] using h

/-! ### The matrices `Υ`, `Ψ`, `Ψ⁻¹` and the sandwich -/

/-- `Υ = ((2,1),(1,1))`: the limit of `a_n²∑_j z_jz_j'ς²_j` on this design. -/
def Ups2 : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]

/-- `Ψ = ((1,1/2),(1/2,1/3))`, the `2 × 2` Hilbert matrix. -/
noncomputable def Psi2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1 / 3]

/-- `Ψ⁻¹ = ((4,−6),(−6,12))`. -/
def Psi2inv : Matrix (Fin 2) (Fin 2) ℝ := !![4, -6; -6, 12]

/-- `Ψ⁻¹ΥΨ⁻¹ = ((20,−36),(−36,72))`, the variance of the limit law. -/
def Sand2 : Matrix (Fin 2) (Fin 2) ℝ := !![20, -36; -36, 72]

theorem Ups2_apply_01 : Ups2 0 1 = 1 := rfl

theorem Psi2_apply_01 : Psi2 0 1 = 1 / 2 := rfl

theorem Psi2inv_apply_00 : Psi2inv 0 0 = 4 := rfl

theorem Psi2inv_apply_01 : Psi2inv 0 1 = -6 := rfl

theorem Sand2_apply_01 : Sand2 0 1 = -36 := rfl

/-- A matrix with a nonzero `(0,1)` entry is not a multiple of the identity. -/
theorem ne_smul_one_of_offDiag {M : Matrix (Fin 2) (Fin 2) ℝ} (h : M 0 1 ≠ 0) (c : ℝ) :
    M ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro hM
  have hval := congrFun (congrFun hM 0) 1
  rw [Matrix.smul_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), smul_zero] at hval
  exact h hval

/-- `Υ` is not a multiple of the identity. -/
theorem Ups2_ne_smul_one (c : ℝ) : Ups2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ne_smul_one_of_offDiag (by rw [Ups2_apply_01]; norm_num) c

/-- `Ψ` is not a multiple of the identity. -/
theorem Psi2_ne_smul_one (c : ℝ) : Psi2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ne_smul_one_of_offDiag (by rw [Psi2_apply_01]; norm_num) c

/-- `Ψ⁻¹` is not a multiple of the identity. -/
theorem Psi2inv_ne_smul_one (c : ℝ) : Psi2inv ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ne_smul_one_of_offDiag (by rw [Psi2inv_apply_01]; norm_num) c

/-- The sandwich `Ψ⁻¹ΥΨ⁻¹` is not a multiple of the identity. -/
theorem Sand2_ne_smul_one (c : ℝ) : Sand2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ne_smul_one_of_offDiag (by rw [Sand2_apply_01]; norm_num) c

/-- `Ψ⁻¹` is a two-sided inverse of `Ψ`. -/
theorem Psi2_mul_Psi2inv : Psi2 * Psi2inv = 1 := by
  rw [Psi2, Psi2inv, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

theorem Psi2inv_mul_Psi2 : Psi2inv * Psi2 = 1 := by
  rw [Psi2, Psi2inv, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

/-- The sandwich `Ψ⁻¹ΥΨ⁻¹` equals `Sand2`. -/
theorem Psi2inv_sandwich : Psi2inv * Ups2 * Psi2inv = Sand2 := by
  rw [Psi2inv, Ups2, Matrix.mul_fin_two, Matrix.mul_fin_two, Sand2]
  norm_num

theorem Psi2inv_symm : Psi2invᵀ = Psi2inv := by
  rw [Psi2inv]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply]

theorem dotProduct_Ups2 (t : EuclideanSpace ℝ (Fin 2)) :
    (t : EuclideanSpace ℝ (Fin 2)) ⬝ᵥ (Ups2 *ᵥ t) = t 0 ^ 2 + (t 0 + t 1) ^ 2 := by
  simp [Ups2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem Ups2_posDef : Ups2.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · show Ups2ᴴ = Ups2
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Ups2, Matrix.conjTranspose_apply]
  · intro x hx
    have hval : star x ⬝ᵥ (Ups2 *ᵥ x) = x 0 ^ 2 + (x 0 + x 1) ^ 2 := by
      simp [Ups2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, star]
      ring
    rw [hval]
    rcases eq_or_ne (x 1) 0 with h1 | h1
    · have h0 : x 0 ≠ 0 := by
        intro h
        refine hx (funext fun i => ?_)
        fin_cases i
        · simpa using h
        · simpa using h1
      have hpos : 0 < x 0 * x 0 := mul_self_pos.2 h0
      rw [h1]
      nlinarith
    · rcases eq_or_ne (x 0) 0 with h0 | h0
      · have hpos : 0 < x 1 * x 1 := mul_self_pos.2 h1
        rw [h0]
        nlinarith
      · have hpos : 0 < x 0 * x 0 := mul_self_pos.2 h0
        nlinarith [sq_nonneg (x 0 + x 1)]

theorem dotProduct_Sand2 (t : EuclideanSpace ℝ (Fin 2)) :
    (t : EuclideanSpace ℝ (Fin 2)) ⬝ᵥ (Sand2 *ᵥ t)
      = 20 * t 0 ^ 2 - 72 * t 0 * t 1 + 72 * t 1 ^ 2 := by
  simp [Sand2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The sandwich is positive definite. -/
theorem Sand2_posDef : Sand2.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · show Sand2ᴴ = Sand2
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Sand2, Matrix.conjTranspose_apply]
  · intro x hx
    have hval : star x ⬝ᵥ (Sand2 *ᵥ x) = 20 * x 0 ^ 2 - 72 * x 0 * x 1 + 72 * x 1 ^ 2 := by
      simp [Sand2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, star]
      ring
    rw [hval]
    rcases eq_or_ne (x 1) 0 with h1 | h1
    · have h0 : x 0 ≠ 0 := by
        intro h
        refine hx (funext fun i => ?_)
        fin_cases i
        · simpa using h
        · simpa using h1
      have hpos : 0 < x 0 * x 0 := mul_self_pos.2 h0
      rw [h1]
      nlinarith
    · have hpos : 0 < x 1 * x 1 := mul_self_pos.2 h1
      nlinarith [sq_nonneg (x 0 - 2 * x 1), sq_nonneg (x 0 - x 1)]

/-- The limit map mixes the coordinates: `matCLM Ψ⁻¹` sends `(0,1)` to a vector whose first
coordinate is `−6`. -/
theorem matCLM_Psi2inv_mixes :
    (matCLM Psi2inv (WithLp.toLp 2 ![(0 : ℝ), 1])) 0 = -6 := by
  rw [matCLM_apply]
  simp [Psi2inv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem matCLM_smul_apply (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (v : EuclideanSpace ℝ (Fin 2)) : matCLM (c • A) v = c • matCLM A v := by
  rw [matCLM_apply, matCLM_apply, Matrix.smul_mulVec]
  rfl

theorem matCLM_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    matCLM (c • A) = c • matCLM A := by
  refine ContinuousLinearMap.ext fun v => ?_
  show matCLM (c • A) v = c • matCLM A v
  exact matCLM_smul_apply c A v

/-! ### The design

There are `(n+1)²` categories in each of the two directions, with weight length
`s_n = (n+1) + (n+1)^{-1}`. -/

/-- The category index of design `n` at `K = 2`. -/
abbrev qJ (n : ℕ) : Type := Fin ((n + 1) ^ 2) × Fin 2

/-- The weight length `s_n = (n+1) + (n+1)^{-1}`. -/
noncomputable def qscale (n : ℕ) : ℝ := ((n : ℝ) + 1) + ((n : ℝ) + 1)⁻¹

theorem qscale_pos (n : ℕ) : 0 < qscale n := by
  rw [qscale]; positivity

theorem qscale_ne (n : ℕ) : qscale n ≠ 0 := ne_of_gt (qscale_pos n)

/-- The category weight: length `s_n`, pointing along `qdir j.2`. -/
noncomputable def qzc (n : ℕ) (j : qJ n) : EuclideanSpace ℝ (Fin 2) := qscale n • qdir j.2

/-- The observation row, the all-ones vector `(1,1)`. -/
noncomputable def qzt (n : ℕ) (_ : wO n) : EuclideanSpace ℝ (Fin 2) := qdir 1

/-- `max_j‖z_j‖²`, attained in direction `1`. -/
noncomputable def qmx (n : ℕ) : ℝ := 2 * qscale n ^ 2

theorem inner_qzc (n : ℕ) (j : qJ n) (t : EuclideanSpace ℝ (Fin 2)) :
    ⟪qzc n j, t⟫ = qscale n * (t 0 + (j.2.val : ℝ) * t 1) := by
  rw [qzc, real_inner_smul_left, inner_qdir]

theorem norm_sq_qzc (n : ℕ) (j : qJ n) :
    ‖qzc n j‖ ^ 2 = qscale n ^ 2 * (1 + (j.2.val : ℝ) ^ 2) := by
  rw [qzc, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sq_qdir]

theorem norm_sq_qzt (n : ℕ) (o : wO n) : ‖qzt n o‖ ^ 2 = 2 := by
  rw [qzt, norm_sq_qdir]
  norm_num

theorem sum_inner_sq_qzc (n : ℕ) (t : EuclideanSpace ℝ (Fin 2)) :
    ∑ j : qJ n, ⟪qzc n j, t⟫ ^ 2 * (1 : ℝ)
      = ((n : ℝ) + 1) ^ 2 * qscale n ^ 2 * (t 0 ^ 2 + (t 0 + t 1) ^ 2) := by
  have h : ∀ j : qJ n, ⟪qzc n j, t⟫ ^ 2 * (1 : ℝ)
      = (qscale n * (t 0 + (j.2.val : ℝ) * t 1)) ^ 2 := by
    intro j; rw [inner_qzc, mul_one]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h j, Fintype.sum_prod_type]
  have hd : ∀ _i : Fin ((n + 1) ^ 2),
      (∑ d : Fin 2, (qscale n * (t 0 + (d.val : ℝ) * t 1)) ^ 2)
        = qscale n ^ 2 * (t 0 ^ 2 + (t 0 + t 1) ^ 2) := by
    intro _i
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hd i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem sum_norm_sq_qzc (n : ℕ) :
    ∑ j : qJ n, ‖qzc n j‖ ^ 2 = 3 * ((n : ℝ) + 1) ^ 2 * qscale n ^ 2 := by
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => norm_sq_qzc n j,
    Fintype.sum_prod_type]
  have hd : ∀ _i : Fin ((n + 1) ^ 2),
      (∑ d : Fin 2, qscale n ^ 2 * (1 + (d.val : ℝ) ^ 2)) = 3 * qscale n ^ 2 := by
    intro _i
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hd i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem norm_sq_qzc_le (n : ℕ) (j : qJ n) : ‖qzc n j‖ ^ 2 ≤ qmx n := by
  rw [norm_sq_qzc, qmx]
  have hlt := j.2.isLt
  have h : (j.2.val : ℝ) ≤ 1 := by
    have : j.2.val ≤ 1 := by omega
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ (j.2.val : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ qscale n ^ 2 := sq_nonneg _
  have hd2 : (j.2.val : ℝ) ^ 2 ≤ 1 := by nlinarith
  calc qscale n ^ 2 * (1 + (j.2.val : ℝ) ^ 2)
      ≤ qscale n ^ 2 * (1 + 1) := mul_le_mul_of_nonneg_left (by linarith) hp
    _ = 2 * qscale n ^ 2 := by ring

theorem qmx_le_sum (n : ℕ) : qmx n ≤ ∑ j : qJ n, ‖qzc n j‖ ^ 2 := by
  rw [qmx, sum_norm_sq_qzc]
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hq : (0 : ℝ) ≤ qscale n ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ 3 * ((n : ℝ) + 1) ^ 2 - 2)]

/-- Condition (iii) at index `n`: `Υ_n = (1 + (n+1)^{-2})²Υ`. -/
theorem upsilon_value2 (t : EuclideanSpace ℝ (Fin 2)) (n : ℕ) :
    wa n ^ 2 * ∑ j : qJ n, ⟪qzc n j, t⟫ ^ 2 * (1 : ℝ)
      = (1 + (((n : ℝ) + 1)⁻¹) ^ 2) ^ 2 * (t 0 ^ 2 + (t 0 + t 1) ^ 2) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hss : (((n : ℝ) + 1)⁻¹) ^ 2 * ((n : ℝ) + 1) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hne, one_pow]
  have hkey : ((n : ℝ) + 1)⁻¹ * qscale n = 1 + (((n : ℝ) + 1)⁻¹) ^ 2 := by
    rw [qscale, mul_add, inv_mul_cancel₀ hne, sq]
  rw [sum_inner_sq_qzc, wa, ← hkey, ← inv_pow]
  linear_combination ((((n : ℝ) + 1)⁻¹) ^ 2 * qscale n ^ 2
    * (t 0 ^ 2 + (t 0 + t 1) ^ 2)) * hss

/-- Condition (iii): `Υ_n` converges to `Υ`. -/
theorem tendsto_upsilon2 (t : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n : ℕ => wa n ^ 2 * ∑ j : qJ n, ⟪qzc n j, t⟫ ^ 2 * (1 : ℝ)) atTop
      (𝓝 (t 0 ^ 2 + (t 0 + t 1) ^ 2)) := by
  have h0 := tendsto_inv_succ.pow 2
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at h0
  have h1 : Tendsto (fun n : ℕ => 1 + (((n : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 1) := by
    have h := h0.const_add (1 : ℝ)
    rw [add_zero] at h
    exact h
  have h2 := (h1.pow 2).mul_const (t 0 ^ 2 + (t 0 + t 1) ^ 2)
  rw [one_pow, one_mul] at h2
  exact h2.congr fun n => (upsilon_value2 t n).symm

theorem qhi : Tendsto (fun n : ℕ => wa n ^ 2 * (Fintype.card (wO n) : ℝ)
    * (Real.sqrt 2 ^ 2 * 1)) atTop (𝓝 0) := by
  have h := tendsto_inv_succ.const_mul (2 : ℝ)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [wa, Fintype.card_fin, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem qhiv : Tendsto (fun n : ℕ => qmx n / ∑ j : qJ n, ‖qzc n j‖ ^ 2) atTop (𝓝 0) := by
  have h0 := tendsto_inv_succ.pow 2
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at h0
  have h := h0.const_mul ((2 : ℝ) / 3)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  have key : qmx n / ∑ j : qJ n, ‖qzc n j‖ ^ 2 = 2 / 3 * (((n : ℝ) + 1)⁻¹) ^ 2 := by
    rw [qmx, sum_norm_sq_qzc]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hss : (((n : ℝ) + 1)⁻¹) ^ 2 * ((n : ℝ) + 1) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hne, one_pow]
    have hs2 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have hq2 : (0 : ℝ) < qscale n ^ 2 := pow_pos (qscale_pos n) 2
    have hd : (3 : ℝ) * ((n : ℝ) + 1) ^ 2 * qscale n ^ 2 ≠ 0 :=
      ne_of_gt (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) hs2) hq2)
    rw [div_eq_iff hd]
    linear_combination (-2 * qscale n ^ 2) * hss
  rw [key]

/-! ### The random design and the estimator `Ψ̂_n` -/

/-- The category weight, with its sign read off the design coin. -/
noncomputable def pzc2 (n : ℕ) (j : qJ n) (y : Aw) : EuclideanSpace ℝ (Fin 2) :=
  sgnA y • qzc n j

/-- The observation row, with the same sign. -/
noncomputable def pzt2 (n : ℕ) (o : wO n) (y : Aw) : EuclideanSpace ℝ (Fin 2) :=
  sgnA y • qzt n o

/-- The category effect: the `(2n, 2j+d)` coin, one per `(category, direction)` pair. -/
noncomputable def peta2 (n : ℕ) (j : qJ n) (y : Aw) : ℝ :=
  coinSign (2 * n, 2 * j.1.val + j.2.val) y.2

/-- `Ψ̂_n(y) = (1 + sgnA(y)/(2(n+1)))·Ψ⁻¹`, a `𝒟`-measurable estimator of `Ψ⁻¹`. -/
noncomputable def qAmat (n : ℕ) (y : Aw) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 + sgnA y * ((n : ℝ) + 1)⁻¹ / 2) • Psi2inv

theorem qAmat_apply (n : ℕ) (y : Aw) (p q : Fin 2) :
    qAmat n y p q = (1 + sgnA y * ((n : ℝ) + 1)⁻¹ / 2) * Psi2inv p q := rfl

theorem qAmat_coef_pos (n : ℕ) (y : Aw) : 0 < 1 + sgnA y * ((n : ℝ) + 1)⁻¹ / 2 := by
  have hb := abs_le.1 (le_of_eq (abs_sgnA y))
  have hinv := inv_succ_pos n
  have hle := inv_succ_le_one n
  nlinarith [mul_nonneg (by linarith [hb.1] : (0 : ℝ) ≤ sgnA y + 1) (le_of_lt hinv)]

/-- `Ψ̂_n` is not a multiple of the identity, at any `n` and any `y`. -/
theorem qAmat_ne_smul_one (n : ℕ) (y : Aw) (c : ℝ) :
    qAmat n y ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ne_smul_one_of_offDiag ?_ c
  rw [qAmat_apply, Psi2inv_apply_01]
  have := qAmat_coef_pos n y
  nlinarith

/-- `Ψ̂_n` is never equal to its limit `Ψ⁻¹`. -/
theorem qAmat_ne_Psi2inv (n : ℕ) (y : Aw) : qAmat n y ≠ Psi2inv := by
  intro h
  have hval := congrFun (congrFun h 0) 0
  rw [qAmat_apply, Psi2inv_apply_00] at hval
  have h2 : sgnA y * ((n : ℝ) + 1)⁻¹ = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact sgnA_ne_zero y h3
  · exact absurd h3 (ne_of_gt (inv_succ_pos n))

/-- `Ψ̂_n` takes different values on the two halves of `𝒟`. -/
theorem qAmat_ne_of_fst (n : ℕ) (y y' : Aw) (hy : y.1 = true) (hy' : y'.1 = false) :
    qAmat n y ≠ qAmat n y' := by
  intro h
  have hval := congrFun (congrFun h 0) 0
  rw [qAmat_apply, qAmat_apply, Psi2inv_apply_00, sgnA_true hy, sgnA_false hy'] at hval
  have hinv := inv_succ_pos n
  nlinarith

theorem matCLM_qAmat (n : ℕ) (y : Aw) :
    matCLM (qAmat n y) = (1 + sgnA y * ((n : ℝ) + 1)⁻¹ / 2) • matCLM Psi2inv := by
  rw [qAmat, matCLM_smul]

/-- `Ψ̂_n` converges to `Ψ⁻¹`. -/
theorem tendsto_qAmat (y : Aw) :
    Tendsto (fun n : ℕ => matCLM (qAmat n y)) atTop (𝓝 (matCLM Psi2inv)) := by
  have hc : Tendsto (fun n : ℕ => 1 + sgnA y * ((n : ℝ) + 1)⁻¹ / 2) atTop (𝓝 1) := by
    have h := (tendsto_inv_succ.const_mul (sgnA y)).div_const 2
    rw [mul_zero, zero_div] at h
    have h2 := h.const_add (1 : ℝ)
    rw [add_zero] at h2
    exact h2
  have h2 := hc.smul_const (matCLM Psi2inv)
  rw [one_smul] at h2
  exact h2.congr fun n => (matCLM_qAmat n y).symm

theorem measD_qAmat (n : ℕ) (p q : Fin 2) : Measurable[Dw] fun ω => qAmat n ω p q := by
  have h : (fun ω : Aw => qAmat n ω p q)
      = fun ω => (1 + sgnA ω * ((n : ℝ) + 1)⁻¹ / 2) * Psi2inv p q :=
    funext fun ω => qAmat_apply n ω p q
  rw [h]
  exact (((meas_sgnA.mul_const _).div_const 2).const_add 1).mul_const _

/-- `π̂_n`, by the solved form of Lemma SM.B.4 at the random design. -/
noncomputable def qpih (n : ℕ) (y : Aw) : EuclideanSpace ℝ (Fin 2) :=
  (0 : EuclideanSpace ℝ (Fin 2)) + (Real.sqrt (wNs n))⁻¹ •
    matCLM (qAmat n y) (wa n •
      ((∑ j, peta2 n j y • pzc2 n j y) + (∑ o, peps n o y • pzt2 n o y)))

theorem qJ_inj (n : ℕ) :
    Function.Injective (fun j : qJ n => ((2 * n, 2 * j.1.val + j.2.val) : ℕ × ℕ)) := by
  intro a b hab
  have h : 2 * a.1.val + a.2.val = 2 * b.1.val + b.2.val := congrArg Prod.snd hab
  have ha := a.2.isLt
  have hb := b.2.isLt
  have h1 : a.1 = b.1 := Fin.ext (by omega)
  have h2 : a.2 = b.2 := Fin.ext (by omega)
  exact Prod.ext h1 h2

theorem meas_peta2 (n : ℕ) (j : qJ n) : Measurable (peta2 n j) :=
  (meas_coinSign (2 * n, 2 * j.1.val + j.2.val)).comp measurable_snd

theorem peta2_pow_four (n : ℕ) (j : qJ n) (y : Aw) : peta2 n j y ^ 4 = 1 :=
  coinSign_pow_four (2 * n, 2 * j.1.val + j.2.val) y.2

theorem peta2_sq (n : ℕ) (j : qJ n) (y : Aw) : peta2 n j y * peta2 n j y = 1 :=
  coinSign_sq (2 * n, 2 * j.1.val + j.2.val) y.2

theorem abs_peta2 (n : ℕ) (j : qJ n) (y : Aw) : |peta2 n j y| ≤ 1 :=
  abs_coinSign_le (2 * n, 2 * j.1.val + j.2.val) y.2

theorem indep_peta2 (n : ℕ) :
    iIndepFun (fun j : qJ n => coinSign (2 * n, 2 * j.1.val + j.2.val)) P1 :=
  indep_coinSign.precomp (g := fun j : qJ n => (2 * n, 2 * j.1.val + j.2.val)) (qJ_inj n)

theorem integral_peta2 {μ : Measure Aw} (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1)
    (n : ℕ) (j : qJ n) : ∫ y, peta2 n j y ∂μ = 0 :=
  (integral_of_snd hmap (meas_coinSign (2 * n, 2 * j.1.val + j.2.val))).trans
    (integral_coinSign (2 * n, 2 * j.1.val + j.2.val))

theorem smul_pzc2 (n : ℕ) (j : qJ n) (y : Aw) :
    peta2 n j y • pzc2 n j y = (peta2 n j y * sgnA y) • qzc n j := by
  rw [pzc2, smul_smul]

theorem smul_pzt2 (n : ℕ) (o : wO n) (y : Aw) :
    peps n o y • pzt2 n o y = (peps n o y * sgnA y) • qzt n o := by
  rw [pzt2, smul_smul]

theorem inner_pzc2_sq (n : ℕ) (j : qJ n) (y : Aw) (t : EuclideanSpace ℝ (Fin 2)) :
    ⟪pzc2 n j y, t⟫ ^ 2 = ⟪qzc n j, t⟫ ^ 2 := by
  rw [pzc2, real_inner_smul_left, mul_pow, show sgnA y ^ 2 = 1 by rw [sq]; exact sgnA_mul y,
    one_mul]

theorem norm_pzc2_sq (n : ℕ) (j : qJ n) (y : Aw) : ‖pzc2 n j y‖ ^ 2 = ‖qzc n j‖ ^ 2 := by
  rw [pzc2, norm_smul, Real.norm_eq_abs, abs_sgnA, one_mul]

theorem norm_pzt2_sq (n : ℕ) (o : wO n) (y : Aw) : ‖pzt2 n o y‖ ^ 2 = ‖qzt n o‖ ^ 2 := by
  rw [pzt2, norm_smul, Real.norm_eq_abs, abs_sgnA, one_mul]

theorem meas_qscore (n : ℕ) : Measurable fun y : Aw =>
    wa n • ((∑ j, peta2 n j y • pzc2 n j y) + (∑ o, peps n o y • pzt2 n o y)) := by
  have h1 : Measurable fun y : Aw => ∑ j, peta2 n j y • pzc2 n j y := by
    refine Finset.measurable_sum _ fun j _ => ?_
    have he : (fun y : Aw => peta2 n j y • pzc2 n j y)
        = fun y => (peta2 n j y * sgnA y) • qzc n j := funext fun y => smul_pzc2 n j y
    rw [he]
    exact ((meas_peta2 n j).mul meas_sgnA').smul_const _
  have h2 : Measurable fun y : Aw => ∑ o, peps n o y • pzt2 n o y := by
    refine Finset.measurable_sum _ fun o _ => ?_
    have he : (fun y : Aw => peps n o y • pzt2 n o y)
        = fun y => (peps n o y * sgnA y) • qzt n o := funext fun y => smul_pzt2 n o y
    rw [he]
    exact ((meas_peps n o).mul meas_sgnA').smul_const _
  exact (h1.add h2).const_smul (wa n)

theorem meas_qpih (n : ℕ) : Measurable (qpih n) := by
  have hv := meas_qscore n
  have hk : qpih n
      = fun y => (0 : EuclideanSpace ℝ (Fin 2)) + (Real.sqrt (wNs n))⁻¹ •
          ((1 + sgnA y * ((n : ℝ) + 1)⁻¹ / 2) •
            matCLM Psi2inv (wa n • ((∑ j, peta2 n j y • pzc2 n j y)
              + (∑ o, peps n o y • pzt2 n o y)))) := by
    funext y
    rw [qpih, matCLM_qAmat]
    rfl
  have hm1 : Measurable fun y : Aw => 1 + sgnA y * ((n : ℝ) + 1)⁻¹ / 2 :=
    ((meas_sgnA'.mul_const _).div_const 2).const_add 1
  have hm2 : Measurable fun y : Aw =>
      matCLM Psi2inv (wa n • ((∑ j, peta2 n j y • pzc2 n j y)
        + (∑ o, peps n o y • pzt2 n o y))) :=
    (matCLM Psi2inv).continuous.measurable.comp hv
  rw [hk]
  exact measurable_const.add ((hm1.smul hm2).const_smul ((Real.sqrt (wNs n))⁻¹))

/-! ### The remaining hypotheses

The lemmas below prove the hypotheses of `pi_clt_unconditional_of_design_closed` that do not
concern the matrices. Both results below use them. -/

theorem qkernel_prob (ω : Aw) : IsProbabilityMeasure (condExpKernel Pw Dw ω) := inferInstance

theorem qhindepEta : ∀ᵐ ω ∂Pw, ∀ n : ℕ, iIndepFun (peta2 n) (condExpKernel Pw Dw ω) := by
  filter_upwards [map_snd_condExpKernel] with ω hω n
  exact iIndepFun_of_snd hω
    (fun j : qJ n => meas_coinSign (2 * n, 2 * j.1.val + j.2.val)) (indep_peta2 n)

theorem qhmeanEta : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (j : qJ n),
    ∫ y, peta2 n j y ∂(condExpKernel Pw Dw ω) = 0 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n j
  exact integral_peta2 hω n j

theorem qhL2Eta : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (j : qJ n),
    MemLp (peta2 n j) 2 (condExpKernel Pw Dw ω) := by
  refine Filter.Eventually.of_forall fun ω n j => ?_
  have := qkernel_prob ω
  exact memLp_of_bound (meas_peta2 n j) (abs_peta2 n j)

theorem qhint4Eta : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (j : qJ n),
    Integrable (fun y => peta2 n j y ^ 4) (condExpKernel Pw Dw ω) := by
  refine Filter.Eventually.of_forall fun ω n j => ?_
  have := qkernel_prob ω
  have he : (fun y : Aw => peta2 n j y ^ 4) = fun _ => (1 : ℝ) :=
    funext fun y => peta2_pow_four n j y
  rw [he]
  exact integrable_const 1

/-- The conditional variance of every category effect under `ℙ_ω` is `1`. -/
theorem qhvarEta : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (j : qJ n),
    Var[peta2 n j; condExpKernel Pw Dw ω] = 1 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n j
  have := qkernel_prob ω
  exact variance_of_sq (memLp_of_bound (meas_peta2 n j) (abs_peta2 n j))
    (integral_peta2 hω n j) (peta2_sq n j)

theorem qhmomEta : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (j : qJ n),
    ∫ y, peta2 n j y ^ 4 ∂(condExpKernel Pw Dw ω) ≤ 1 := by
  refine Filter.Eventually.of_forall fun ω n j => ?_
  have := qkernel_prob ω
  have he : (fun y : Aw => peta2 n j y ^ 4) = fun _ => (1 : ℝ) :=
    funext fun y => peta2_pow_four n j y
  rw [he]
  simp

theorem qhindepEps : ∀ᵐ ω ∂Pw, ∀ n : ℕ, iIndepFun (peps n) (condExpKernel Pw Dw ω) := by
  filter_upwards [map_snd_condExpKernel] with ω hω n
  exact iIndepFun_of_snd hω (fun o : wO n => meas_coinSign (2 * n + 1, o.val)) (indep_peps n)

theorem qhL2Eps : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (o : wO n),
    MemLp (peps n o) 2 (condExpKernel Pw Dw ω) := by
  refine Filter.Eventually.of_forall fun ω n o => ?_
  have := qkernel_prob ω
  exact memLp_of_bound (meas_peps n o) (abs_peps n o)

theorem qhmeanEps : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (o : wO n),
    ∫ y, peps n o y ∂(condExpKernel Pw Dw ω) = 0 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n o
  exact integral_peps hω n o

theorem qhvarEps : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (o : wO n),
    Var[peps n o; condExpKernel Pw Dw ω] = 1 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n o
  have := qkernel_prob ω
  exact variance_of_sq (memLp_of_bound (meas_peps n o) (abs_peps n o))
    (integral_peps hω n o) (peps_sq n o)

theorem qhztBound : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (o : wO n),
    ‖pzt2 n o ω‖ ^ 2 ≤ Real.sqrt 2 ^ 2 := by
  refine Filter.Eventually.of_forall fun ω n o => ?_
  rw [norm_pzt2_sq, norm_sq_qzt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Condition (iii) at the random design. -/
theorem qhiiiDesign : ∀ᵐ ω ∂Pw, ∀ t : EuclideanSpace ℝ (Fin 2),
    Tendsto (fun n : ℕ => wa n ^ 2 * ∑ j : qJ n, ⟪pzc2 n j ω, t⟫ ^ 2 * (1 : ℝ)) atTop
      (𝓝 (t ⬝ᵥ (Ups2 *ᵥ t))) := by
  refine Filter.Eventually.of_forall fun ω t => ?_
  rw [dotProduct_Ups2 t]
  refine (tendsto_upsilon2 t).congr fun n => ?_
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [inner_pzc2_sq]

theorem qhmxBound : ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (j : qJ n), ‖pzc2 n j ω‖ ^ 2 ≤ qmx n :=
  Filter.Eventually.of_forall fun ω n j => by
    simpa only [norm_pzc2_sq] using norm_sq_qzc_le n j

theorem qhmxsumBound : ∀ᵐ ω ∂Pw, ∀ n : ℕ, qmx n ≤ ∑ j : qJ n, ‖pzc2 n j ω‖ ^ 2 :=
  Filter.Eventually.of_forall fun ω n => by
    simpa only [norm_pzc2_sq] using qmx_le_sum n

theorem qhivDesign : ∀ᵐ ω ∂Pw,
    Tendsto (fun n : ℕ => qmx n / ∑ j : qJ n, ‖pzc2 n j ω‖ ^ 2) atTop (𝓝 0) := by
  refine Filter.Eventually.of_forall fun ω => ?_
  simpa only [norm_pzc2_sq] using qhiv

/-! ### The deconditioned limit law -/

/-- The deconditioned limit law at `K = 2`, derived from
`pi_clt_unconditional_of_design_closed`. -/
theorem pi_clt_rank2_deconditioned :
    TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
      (fun (n : ℕ) y => Real.sqrt (wNs n) • (qpih n y - (0 : EuclideanSpace ℝ (Fin 2))))
      atTop (fun z => (matCLM Psi2inv) z) (fun _ => Pw)
      (multivariateGaussian 0 Ups2) := by
  classical
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  exact pi_clt_unconditional_of_design_closed (𝒟 := Dw) (Jc := qJ) (Ob := wO)
    Dw_le Pw (fun n _ => wa n) (fun n _ => wNs n) (fun n _ => qmx n) pzc2 pzt2 peta2 peps
    (fun _ _ _ => 1) (fun _ _ _ => 1) 1 (Real.sqrt 2) 1 1 Ups2
    Ups2_posDef qAmat (matCLM Psi2inv) qpih 0
    (fun _ => measurable_const)
    (fun n j => meas_sgnA.smul_const (qzc n j)) (fun n o => meas_sgnA.smul_const (qzt n o))
    measD_qAmat
    (fun n _ => by rw [wNs]; positivity) meas_peta2 meas_peps
    (fun n => ((meas_qpih n).sub_const 0).const_smul (Real.sqrt (wNs n)))
    (Filter.Eventually.of_forall fun n y =>
      sqrt_smul_solved (by rw [wNs]; positivity : (0 : ℝ) < wNs n)
        (0 : EuclideanSpace ℝ (Fin 2)) _)
    qhindepEta qhmeanEta qhL2Eta qhint4Eta qhvarEta qhmomEta
    zero_lt_one (Filter.Eventually.of_forall fun _ _ _ => le_refl 1)
    qhindepEps qhL2Eps qhmeanEps qhvarEps
    (Filter.Eventually.of_forall fun _ _ _ => zero_le_one)
    (Filter.Eventually.of_forall fun _ _ _ => le_refl 1) qhztBound
    (Filter.Eventually.of_forall fun _ => qhi) qhiiiDesign
    (Filter.Eventually.of_forall fun _ n => by rw [qmx]; positivity)
    qhmxBound qhmxsumBound qhivDesign
    (Filter.Eventually.of_forall fun ω => tendsto_qAmat ω)

/-- **Theorem 6, deconditioned, at `K = 2`.** On this design all hypotheses of
`pi_clt_unconditional_of_design_closed` hold with `Dw` a proper sub-σ-field and `ℙ_ω ≠ P`;
`Υ`, `Ψ`, `Ψ⁻¹` and `Ψ⁻¹ΥΨ⁻¹` are not multiples of the identity; `Ψ̂_n` is random and converges
to `Ψ⁻¹` without reaching it; `Υ_n` converges to `Υ` without reaching it; and the limit law
holds. -/
theorem pi_clt_unconditional_of_design_closed_rank2_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (j : qJ n) (y : Aw),
        pzc2 n j y = (if y.1 then (1 : ℝ) else -1) • qzc n j)
    ∧ (∀ᵐ ω ∂Pw, ∀ (n : ℕ) (j : qJ n),
        Var[peta2 n j; condExpKernel Pw Dw ω] = 1)
    ∧ Ups2.PosDef
    ∧ (∀ c : ℝ, Ups2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ Psi2 * Psi2inv = 1
    ∧ Psi2inv * Psi2 = 1
    ∧ (∀ c : ℝ, Psi2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ c : ℝ, Psi2inv ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ Psi2inv * Ups2 * Psi2inv = Sand2
    ∧ (∀ c : ℝ, Sand2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (matCLM Psi2inv (WithLp.toLp 2 ![(0 : ℝ), 1])) 0 = -6
    ∧ (∀ (n : ℕ) (y y' : Aw), y.1 = true → y'.1 = false → qAmat n y ≠ qAmat n y')
    ∧ (∀ (n : ℕ) (y : Aw), qAmat n y ≠ Psi2inv)
    ∧ (∀ (n : ℕ) (y : Aw) (c : ℝ), qAmat n y ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin 2)),
        wa n ^ 2 * ∑ j : qJ n, ⟪qzc n j, t⟫ ^ 2 * (1 : ℝ)
          = (1 + (((n : ℝ) + 1)⁻¹) ^ 2) ^ 2 * (t ⬝ᵥ (Ups2 *ᵥ t)))
    ∧ (∀ t : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun n : ℕ => wa n ^ 2 * ∑ j : qJ n, ⟪qzc n j, t⟫ ^ 2 * (1 : ℝ)) atTop
          (𝓝 (t ⬝ᵥ (Ups2 *ᵥ t))))
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) y => Real.sqrt (wNs n) • (qpih n y - (0 : EuclideanSpace ℝ (Fin 2))))
        atTop (fun z => (matCLM Psi2inv) z) (fun _ => Pw)
        (multivariateGaussian 0 Ups2) := by
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ _ => rfl, qhvarEta, Ups2_posDef,
    Ups2_ne_smul_one, Psi2_mul_Psi2inv, Psi2inv_mul_Psi2, Psi2_ne_smul_one, Psi2inv_ne_smul_one,
    Psi2inv_sandwich, Sand2_ne_smul_one, matCLM_Psi2inv_mixes, qAmat_ne_of_fst,
    qAmat_ne_Psi2inv, qAmat_ne_smul_one, ?_, ?_, pi_clt_rank2_deconditioned⟩
  · intro n t
    rw [dotProduct_Ups2]
    exact upsilon_value2 t n
  · intro t
    rw [dotProduct_Ups2]
    exact tendsto_upsilon2 t

/-! ### The deconditioned Wald statement

`piinf_wald_unconditional_of_design_closed` is instantiated on the same design. Its hypothesis
`hsand` forces `Σ = Ψ⁻¹ΥΨ⁻¹ = Sand2`. The estimated meat satisfies
`‖Υ̂_n − Υ_n‖_F = (n+1)^{-1}√2` and `‖Υ_n − Σ‖_F = 3(n+1)^{-1}√2`. -/

/-- The estimated meat `Υ̂_n`, random through the design coin. -/
noncomputable def qUh (n : ℕ) (y : Aw) : Matrix (Fin 2) (Fin 2) ℝ :=
  Sand2 + ((3 + sgnA y) * ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The population meat `Υ_n`. -/
noncomputable def qUpn (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Sand2 + (3 * ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem qUh_apply (n : ℕ) (y : Aw) (i j : Fin 2) :
    qUh n y i j
      = Sand2 i j + (3 + sgnA y) * ((n : ℝ) + 1)⁻¹ * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  simp only [qUh, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem qUh_herm (n : ℕ) (y : Aw) : (qUh n y).IsHermitian := by
  show (qUh n y)ᴴ = qUh n y
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.conjTranspose_apply, qUh_apply, Sand2, Matrix.one_apply]

theorem meas_qUh (n : ℕ) : Measurable (qUh n) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have h : (fun y : Aw => qUh n y i j)
      = fun y => Sand2 i j
          + (3 + sgnA y) * ((n : ℝ) + 1)⁻¹ * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j :=
    funext fun y => qUh_apply n y i j
  rw [h]
  exact (((meas_sgnA'.const_add 3).mul_const _).mul_const _).const_add _

/-- `‖Υ̂_n − Υ_n‖_F = (n+1)^{-1}√2`, nonzero at every `n` and every `y`. -/
theorem frobNorm_qUh_sub (n : ℕ) (y : Aw) :
    frobNorm (qUh n y - qUpn n) = ((n : ℝ) + 1)⁻¹ * Real.sqrt 2 := by
  have h : qUh n y - qUpn n
      = (sgnA y * ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [qUh, qUpn, add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    ring
  rw [h, frobNorm_smul, RectDesign.frobNorm_one_fin_two, abs_mul, abs_sgnA, one_mul,
    abs_of_nonneg (le_of_lt (inv_succ_pos n))]

/-- `‖Υ_n − Σ‖_F = 3(n+1)^{-1}√2`, nonzero at every `n`. -/
theorem frobNorm_qUpn_sub (n : ℕ) :
    frobNorm (qUpn n - Sand2) = 3 * ((n : ℝ) + 1)⁻¹ * Real.sqrt 2 := by
  have h : qUpn n - Sand2 = (3 * ((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [qUpn, add_sub_cancel_left]
  rw [h, frobNorm_smul, RectDesign.frobNorm_one_fin_two,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * ((n : ℝ) + 1)⁻¹)]

/-- `Υ̂_n` takes different values on the two halves of `𝒟`. -/
theorem qUh_ne_of_fst (n : ℕ) (y y' : Aw) (hy : y.1 = true) (hy' : y'.1 = false) :
    qUh n y ≠ qUh n y' := by
  intro h
  have hval := congrFun (congrFun h 0) 0
  rw [qUh_apply, qUh_apply, sgnA_true hy, sgnA_false hy',
    Matrix.one_apply_eq (0 : Fin 2)] at hval
  have hinv := inv_succ_pos n
  nlinarith

/-- The sandwich identity `hsand` holds at `Σ = Ψ⁻¹ΥΨ⁻¹`. -/
theorem qhsand (t : EuclideanSpace ℝ (Fin 2)) :
    (ContinuousLinearMap.adjoint (matCLM Psi2inv) t)
        ⬝ᵥ (Ups2 *ᵥ (ContinuousLinearMap.adjoint (matCLM Psi2inv) t))
      = t ⬝ᵥ (Sand2 *ᵥ t) := by
  have h0 : (matCLM Psi2inv t) 0 = 4 * t 0 - 6 * t 1 := by
    rw [matCLM_apply]
    show (Psi2inv *ᵥ (WithLp.ofLp t)) 0 = _
    simp only [Psi2inv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have h1 : (matCLM Psi2inv t) 1 = -6 * t 0 + 12 * t 1 := by
    rw [matCLM_apply]
    show (Psi2inv *ᵥ (WithLp.ofLp t)) 1 = _
    simp only [Psi2inv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [adjoint_matCLM, Psi2inv_symm, dotProduct_Ups2, dotProduct_Sand2, h0, h1]
  ring

theorem qha0 : TendstoInMeasure Pw (fun n y => frobNorm (qUh n y - qUpn n)) atTop
    (fun _ => 0) := by
  refine Sequence.tendstoInProb_zero_of_abs_le_const
    (b := fun n : ℕ => ((n : ℝ) + 1)⁻¹ * Real.sqrt 2)
    (fun n => Filter.Eventually.of_forall fun y => ?_) ?_
  · rw [frobNorm_qUh_sub, abs_of_nonneg (by positivity)]
  · have h := PiWitness.tendsto_inv_succ.mul_const (Real.sqrt 2)
    simpa using h

theorem qhlim : Tendsto (fun n => frobNorm (qUpn n - Sand2)) atTop (𝓝 0) := by
  have h := (PiWitness.tendsto_inv_succ.const_mul (3 : ℝ)).mul_const (Real.sqrt 2)
  rw [mul_zero, zero_mul] at h
  exact h.congr fun n => (frobNorm_qUpn_sub n).symm

/-- **Theorem 12(b), deconditioned, at `K = 2`.** All hypotheses of
`piinf_wald_unconditional_of_design_closed` hold on this design with the non-diagonal
`Σ = Ψ⁻¹ΥΨ⁻¹ = ((20,−36),(−36,72))`, and the Wald limit follows. -/
theorem piinf_wald_unconditional_of_design_closed_rank2_witness :
    Sand2.PosDef
    ∧ (∀ c : ℝ, Sand2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ (n : ℕ) (y : Aw), frobNorm (qUh n y - qUpn n) = ((n : ℝ) + 1)⁻¹ * Real.sqrt 2)
    ∧ (∀ n : ℕ, frobNorm (qUpn n - Sand2) = 3 * ((n : ℝ) + 1)⁻¹ * Real.sqrt 2)
    ∧ (∀ (n : ℕ) (y y' : Aw), y.1 = true → y'.1 = false → qUh n y ≠ qUh n y')
    ∧ Tendsto (fun n => Pw {y : Aw | ((wNs n)⁻¹ • qUh n y).PosDef}) atTop (𝓝 1)
    ∧ TendstoInDistribution
        (fun n y => Wald.waldStat ((wNs n)⁻¹ • qUh n y)
          (qpih n y - (0 : EuclideanSpace ℝ (Fin 2)))) atTop
        (fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖ ^ 2) (fun _ => Pw)
        (multivariateGaussian 0 1) := by
  classical
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  obtain ⟨hpd, hwald⟩ :=
    piinf_wald_unconditional_of_design_closed (𝒟 := Dw) (Jc := qJ) (Ob := wO)
      Dw_le Pw (fun n _ => wa n) (fun n _ => qmx n) wNs pzc2 pzt2 peta2 peps
      (fun _ _ _ => 1) (fun _ _ _ => 1) 1 (Real.sqrt 2) 1 1 Ups2 Sand2
      Ups2_posDef Sand2_posDef qAmat (matCLM Psi2inv) qpih 0
      (fun _ => measurable_const)
      (fun n j => meas_sgnA.smul_const (qzc n j)) (fun n o => meas_sgnA.smul_const (qzt n o))
      measD_qAmat
      (fun n => by rw [wNs]; positivity) meas_peta2 meas_peps
      (fun n => ((meas_qpih n).sub_const 0).const_smul (Real.sqrt (wNs n)))
      (Filter.Eventually.of_forall fun n y =>
        sqrt_smul_solved (by rw [wNs]; positivity : (0 : ℝ) < wNs n)
          (0 : EuclideanSpace ℝ (Fin 2)) _)
      qhindepEta qhmeanEta qhL2Eta qhint4Eta qhvarEta qhmomEta
      zero_lt_one (Filter.Eventually.of_forall fun _ _ _ => le_refl 1)
      qhindepEps qhL2Eps qhmeanEps qhvarEps
      (Filter.Eventually.of_forall fun _ _ _ => zero_le_one)
      (Filter.Eventually.of_forall fun _ _ _ => le_refl 1) qhztBound
      (Filter.Eventually.of_forall fun _ => qhi) qhiiiDesign
      (Filter.Eventually.of_forall fun _ n => by rw [qmx]; positivity)
      qhmxBound qhmxsumBound qhivDesign
      (Filter.Eventually.of_forall fun ω => tendsto_qAmat ω)
      qhsand qUh qUpn qUh_herm meas_qUh qha0 qhlim
  exact ⟨Sand2_posDef, Sand2_ne_smul_one, frobNorm_qUh_sub, frobNorm_qUpn_sub,
    qUh_ne_of_fst, hpd, hwald⟩

end PiRank2Witness
end PiInf
end Multiway
