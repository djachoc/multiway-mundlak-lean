import Multiway.CLT

/-!
# Theorem 4(a) at `K = 2`

The hypotheses of Theorem 4(a) of the paper (asymptotic normality of the joint-projection
Mundlak estimator) hold at `K = 2` on the following design, with a limit map that mixes the two
coordinates. The observations are `Fin n`, the fixed-effect space is spanned by
the indicator `d_n` of the first observation, and the regressors are `v_n(o) = 1{o ≠ 0}` and the
ramp `r_n(o) = o/n`. The Gram limit is the `2 × 2` Hilbert matrix
`H = ((1, 1/2), (1/2, 1/3))`, the errors are i.i.d. Rademacher so `S = H`, and
`H⁻¹ = ((4, −6), (−6, 12))`. None of `S`, `H`, `H⁻¹` is a multiple of the identity.

## Main results

* `clt_a_rank2_witness`: the hypotheses of `clt_a` are jointly satisfiable at `K = 2`.
* `clt_b_rank2_witness`: the same for `clt_b`.
* `clt_a_rank2_unconditional_witness`: the unconditional form of the limit law at `K = 2`.
-/

namespace Multiway
namespace CLT
namespace Rank2Witness

open Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Matrix ENNReal
open Multiway.CLT.Witness

/-! ### The `2 × 2` operator algebra

Operators on `ℝ²` are written as linear combinations of the four matrix units, which reduces a
limit in the operator norm to four scalar limits. -/

/-- The matrix unit `E_{ij}` as a continuous linear map on `ℝ²`. -/
noncomputable def blk (i j : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).smulRight (EuclideanSpace.single i (1 : ℝ))

theorem blk_apply (i j : Fin 2) (v : EuclideanSpace ℝ (Fin 2)) (k : Fin 2) :
    (blk i j v) k = if k = i then v j else 0 := by
  show (⟪EuclideanSpace.single j (1 : ℝ), v⟫ •
    (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) k = _
  rw [PiLp.smul_apply, EuclideanSpace.single_apply, EuclideanSpace.inner_single_left]
  by_cases h : k = i <;> simp [h]

/-- The operator with matrix `(a b; c d)`. -/
noncomputable def op2 (a b c d : ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  a • blk 0 0 + b • blk 0 1 + c • blk 1 0 + d • blk 1 1

theorem op2_zero (a b c d : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (op2 a b c d v) 0 = a * v 0 + b * v 1 := by
  show ((a • blk 0 0 + b • blk 0 1 + c • blk 1 0 + d • blk 1 1) v) 0 = _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, blk_apply]
  norm_num

theorem op2_one (a b c d : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (op2 a b c d v) 1 = c * v 0 + d * v 1 := by
  show ((a • blk 0 0 + b • blk 0 1 + c • blk 1 0 + d • blk 1 1) v) 1 = _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, blk_apply]
  norm_num

theorem eq_of_coords {x y : EuclideanSpace ℝ (Fin 2)} (h0 : x 0 = y 0) (h1 : x 1 = y 1) :
    x = y := by
  ext k
  fin_cases k
  · exact h0
  · exact h1

theorem eq_zero_of_coords {x : EuclideanSpace ℝ (Fin 2)} (h0 : x 0 = 0) (h1 : x 1 = 0) :
    x = 0 := by
  refine eq_of_coords ?_ ?_ <;> simpa using ‹_›

theorem inner_fin_two (b a : EuclideanSpace ℝ (Fin 2)) : ⟪b, a⟫ = b 0 * a 0 + b 1 * a 1 := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, mul_comm]

theorem inner_op2 (a b c d : ℝ) (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, op2 a b c d v⟫ = u 0 * (a * v 0 + b * v 1) + u 1 * (c * v 0 + d * v 1) := by
  rw [inner_fin_two, op2_zero, op2_one]

theorem smul_op2 (r a b c d : ℝ) : r • op2 a b c d = op2 (r * a) (r * b) (r * c) (r * d) := by
  unfold op2
  module

theorem op2_mul (a b c d a' b' c' d' : ℝ) :
    op2 a b c d * op2 a' b' c' d'
      = op2 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  refine ContinuousLinearMap.ext fun v => eq_of_coords ?_ ?_
  · rw [ContinuousLinearMap.mul_apply, op2_zero, op2_zero, op2_one, op2_zero]
    ring
  · rw [ContinuousLinearMap.mul_apply, op2_one, op2_zero, op2_one, op2_one]
    ring

theorem op2_id :
    op2 1 0 0 1 = (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  refine ContinuousLinearMap.ext fun v => eq_of_coords ?_ ?_
  · rw [op2_zero]; simp
  · rw [op2_one]; simp

/-- Four scalar limits give one operator-norm limit. -/
theorem tendsto_op2 {a b c d : ℕ → ℝ} {A B C D : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hc : Tendsto c atTop (𝓝 C)) (hd : Tendsto d atTop (𝓝 D)) :
    Tendsto (fun n => op2 (a n) (b n) (c n) (d n)) atTop (𝓝 (op2 A B C D)) := by
  simp only [op2]
  exact (((ha.smul_const _).add (hb.smul_const _)).add (hc.smul_const _)).add (hd.smul_const _)

/-! ### The design -/

/-- The second regressor column: the ramp `r_n(o) = o/n`. It vanishes at the first
observation, so it is orthogonal to `d_n` and no projection formula is needed. -/
noncomputable def rvec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun o => (o.val : ℝ) / (n : ℝ)

theorem rvec_apply (n : ℕ) (o : Fin n) : rvec n o = (o.val : ℝ) / (n : ℝ) := rfl

/-- `X_n : ℝ² → ℝⁿ`, `a ↦ a_0v_n + a_1r_n`. -/
noncomputable def X2 (n : ℕ) : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun a := a 0 • xvec n + a 1 • rvec n
  map_add' a b := by
    simp only [PiLp.add_apply, add_smul]
    abel
  map_smul' r a := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

theorem X2_apply (n : ℕ) (a : EuclideanSpace ℝ (Fin 2)) (o : Fin n) :
    (X2 n a) o = a 0 * (if o.val = 0 then (0 : ℝ) else 1) + a 1 * ((o.val : ℝ) / (n : ℝ)) := by
  show (a 0 • xvec n + a 1 • rvec n) o = _
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, xvec_apply, rvec_apply]
  simp

theorem rvec_mem_orth (n : ℕ) : rvec n ∈ (ℝ ∙ dvec n)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp only [dvec, rvec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_eq_zero fun o _ => ?_
  by_cases h : o.val = 0 <;> simp [h]

/-- `Q_[Δ]X = X` on this design. -/
theorem jointWithin_X2 (n : ℕ) (a : EuclideanSpace ℝ (Fin 2)) :
    jointWithin (⨆ m, feSpace n m) (X2 n a) = X2 n a := by
  rw [iSup_feSpace, jointWithin_apply, (Submodule.starProjection_apply_eq_zero_iff _).2, sub_zero]
  show (a 0 • xvec n + a 1 • rvec n) ∈ (ℝ ∙ dvec n)ᗮ
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (xvec_mem_orth n))
    (Submodule.smul_mem _ _ (rvec_mem_orth n))

/-- The within rows, read through `⟪·,t⟫`: `x̃_o = (1{o ≠ 0}, o/n)`. -/
theorem inner_withinRow_rank2 (n : ℕ) (o : Fin n) (t : EuclideanSpace ℝ (Fin 2)) :
    ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫
      = t 0 * (if o.val = 0 then (0 : ℝ) else 1) + t 1 * ((o.val : ℝ) / (n : ℝ)) := by
  rw [real_inner_comm, inner_withinRow, jointWithin_X2, X2_apply]

/-- The design is identified for `n ≥ 3`. -/
theorem identified_rank2 {n : ℕ} (hn : 3 ≤ n) : Identified (⨆ m, feSpace n m) (X2 n) := by
  intro a ha
  rw [iSup_feSpace, Submodule.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ := ha
  have hn0 : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z ⟨1, by omega⟩) hc
  have h2 := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z ⟨2, by omega⟩) hc
  simp only [PiLp.smul_apply, smul_eq_mul, X2_apply] at h1 h2
  rw [show dvec n ⟨1, by omega⟩ = 0 from by simp [dvec]] at h1
  rw [show dvec n ⟨2, by omega⟩ = 0 from by simp [dvec]] at h2
  norm_num at h1 h2
  have ha1 : a 1 = 0 := by
    have hkey : a 1 * (n : ℝ)⁻¹ = 0 := by
      rw [div_eq_mul_inv] at h2
      linear_combination h1 - h2
    rcases mul_eq_zero.1 hkey with h | h
    · exact h
    · exact absurd (inv_eq_zero.1 h) hn0
  have ha0 : a 0 = 0 := by
    rw [ha1] at h1
    linarith
  exact eq_zero_of_coords ha0 ha1

/-! ### The Gram entries -/

theorem sum_range_cast (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_sq_cast (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `(X̃'X̃)_{00} = ⟪v_n, v_n⟫ = n − 1`. -/
noncomputable def g00 (n : ℕ) : ℝ := ((n - 1 : ℕ) : ℝ)

/-- `(X̃'X̃)_{01} = ⟪v_n, r_n⟫ = n^{-1}·n(n−1)/2`. -/
noncomputable def g01 (n : ℕ) : ℝ := (n : ℝ)⁻¹ * ((n : ℝ) * ((n : ℝ) - 1) / 2)

/-- `(X̃'X̃)_{11} = ⟪r_n, r_n⟫ = n^{-2}·n(n−1)(2n−1)/6`. -/
noncomputable def g11 (n : ℕ) : ℝ :=
  ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6)

theorem sum_rvec (n : ℕ) : ∑ o : Fin n, ((o.val : ℝ) / (n : ℝ)) = g01 n := by
  simp only [div_eq_inv_mul, ← Finset.mul_sum, g01]
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) n, sum_range_cast]
  ring

theorem sum_rvec_sq (n : ℕ) : ∑ o : Fin n, ((o.val : ℝ) / (n : ℝ)) ^ 2 = g11 n := by
  have h : ∀ o : Fin n, ((o.val : ℝ) / (n : ℝ)) ^ 2 = ((n : ℝ)⁻¹) ^ 2 * (o.val : ℝ) ^ 2 := by
    intro o; rw [div_pow]; ring
  rw [Finset.sum_congr rfl fun o _ => h o, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => (i : ℝ) ^ 2) n, sum_range_sq_cast, g11]

theorem inner_xvec_self' (n : ℕ) : ⟪xvec n, xvec n⟫ = g00 n := inner_xvec_self n

theorem inner_xvec_rvec (n : ℕ) : ⟪xvec n, rvec n⟫ = g01 n := by
  simp only [xvec, rvec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h : ∀ o : Fin n,
      ((o.val : ℝ) / (n : ℝ)) * (if o.val = 0 then (0 : ℝ) else 1)
        = (o.val : ℝ) / (n : ℝ) := by
    intro o
    by_cases h : o.val = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun o _ => h o, sum_rvec]

theorem inner_rvec_xvec (n : ℕ) : ⟪rvec n, xvec n⟫ = g01 n := by
  rw [real_inner_comm]
  exact inner_xvec_rvec n

theorem inner_rvec_self (n : ℕ) : ⟪rvec n, rvec n⟫ = g11 n := by
  simp only [rvec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h : ∀ o : Fin n, ((o.val : ℝ) / (n : ℝ)) * ((o.val : ℝ) / (n : ℝ))
      = ((o.val : ℝ) / (n : ℝ)) ^ 2 := by intro o; ring
  rw [Finset.sum_congr rfl fun o _ => h o, sum_rvec_sq]

/-- The Gram operator `X̃'X̃`; its off-diagonal entry `g01 n = (n−1)/2` is nonzero. -/
theorem gramCLM_rank2 (n : ℕ) :
    gramCLM (⨆ m, feSpace n m) (X2 n) = op2 (g00 n) (g01 n) (g01 n) (g11 n) := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [gramCLM_apply]
  refine ext_inner_left ℝ fun b => ?_
  rw [gram, inner_score, jointWithin_X2, inner_op2]
  show ⟪(b 0 • xvec n + b 1 • rvec n : EuclideanSpace ℝ (Fin n)),
    (a 0 • xvec n + a 1 • rvec n : EuclideanSpace ℝ (Fin n))⟫ = _
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [inner_xvec_self', inner_xvec_rvec, inner_rvec_xvec, inner_rvec_self]
  ring

/-! ### The scalar limits -/

theorem tendsto_ginv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhds_zero_nat

theorem g00_div {n : ℕ} (hn : 1 ≤ n) : (n : ℝ)⁻¹ * g00 n = 1 - (n : ℝ)⁻¹ := by
  have hn0 : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    push_cast [Nat.cast_sub hn]; ring
  rw [g00, hc]
  field_simp

theorem g01_div {n : ℕ} (hn : 1 ≤ n) : (n : ℝ)⁻¹ * g01 n = (1 - (n : ℝ)⁻¹) / 2 := by
  have hn0 : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [g01]
  field_simp

theorem g11_div {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ)⁻¹ * g11 n = (1 - (n : ℝ)⁻¹) * (2 - (n : ℝ)⁻¹) / 6 := by
  have hn0 : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [g11]
  field_simp

theorem tendsto_one_sub_ginv :
    Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop (𝓝 ((1 : ℝ) - 0)) :=
  tendsto_const_nhds.sub tendsto_ginv

theorem tendsto_g00 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g00 n) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    have := tendsto_one_sub_ginv
    rwa [sub_zero] at this
  refine Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn using (g00_div hn).symm

theorem tendsto_g01 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g01 n) atTop (𝓝 (1 / 2)) := by
  have h : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) / 2) atTop (𝓝 ((1 : ℝ) / 2)) := by
    have h0 := tendsto_one_sub_ginv.div_const (2 : ℝ)
    rwa [sub_zero] at h0
  refine Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn using (g01_div hn).symm

theorem tendsto_g11 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g11 n) atTop (𝓝 (1 / 3)) := by
  have h : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) * (2 - (n : ℝ)⁻¹) / 6) atTop
      (𝓝 ((1 : ℝ) / 3)) := by
    have h0 : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) * (2 - (n : ℝ)⁻¹) / 6) atTop
        (𝓝 (((1 : ℝ) - 0) * ((2 : ℝ) - 0) / 6)) :=
      (tendsto_one_sub_ginv.mul (tendsto_const_nhds.sub tendsto_ginv)).div_const 6
    rwa [show ((1 : ℝ) - 0) * ((2 : ℝ) - 0) / 6 = (1 : ℝ) / 3 by norm_num] at h0
  refine Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn using (g11_div hn).symm

/-! ### The limit matrices `H`, `S` and `H⁻¹` -/

/-- `H = ((1, 1/2), (1/2, 1/3))`, the `2 × 2` Hilbert matrix as an operator. -/
noncomputable def H2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  op2 1 (1 / 2) (1 / 2) (1 / 3)

/-- `H⁻¹ = ((4, −6), (−6, 12))`. -/
noncomputable def Hinv2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  op2 4 (-6) (-6) 12

/-- `S`, equal to `H` on this design because the errors are homoskedastic with unit variance. -/
noncomputable def Smat2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![1, 1 / 2], ![1 / 2, 1 / 3]]

theorem Smat2_apply_01 : Smat2 0 1 = 1 / 2 := rfl

theorem H2_mul_Hinv2 : H2 * Hinv2 = 1 := by
  rw [H2, Hinv2, op2_mul]
  norm_num
  exact op2_id

theorem Hinv2_mul_H2 : Hinv2 * H2 = 1 := by
  rw [H2, Hinv2, op2_mul]
  norm_num
  exact op2_id

theorem dotProduct_Smat2 (t : EuclideanSpace ℝ (Fin 2)) :
    t ⬝ᵥ (Smat2 *ᵥ t) = (t 0) ^ 2 + t 0 * t 1 + (t 1) ^ 2 / 3 := by
  simp [Smat2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem Smat2_posDef : Smat2.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · show Smat2ᴴ = Smat2
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Smat2, Matrix.conjTranspose_apply]
  · intro x hx
    have hval : star x ⬝ᵥ (Smat2 *ᵥ x) = (x 0) ^ 2 + x 0 * x 1 + (x 1) ^ 2 / 3 := by
      simp [Smat2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, star]
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
      nlinarith [sq_nonneg (x 0 + x 1 / 2)]

/-- `S` is not a multiple of the identity. -/
theorem Smat2_ne_smul_one (c : ℝ) : Smat2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have hval := congrFun (congrFun h 0) 1
  rw [Smat2_apply_01] at hval
  norm_num [Matrix.one_apply] at hval

theorem op2_ne_smul_one {a b c d : ℝ} (hb : b ≠ 0) (r : ℝ) :
    op2 a b c d ≠ r • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  intro h
  have hval := congrArg
    (fun f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) =>
      (f (EuclideanSpace.single 1 (1 : ℝ))) 0) h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, PiLp.smul_apply,
    smul_eq_mul, op2_zero, EuclideanSpace.single_apply] at hval
  norm_num at hval
  exact hb hval

/-- `H` is not a multiple of the identity. -/
theorem H2_ne_smul_one (c : ℝ) :
    H2 ≠ c • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  op2_ne_smul_one (by norm_num) c

/-- `H⁻¹` is not a multiple of the identity. -/
theorem Hinv2_ne_smul_one (c : ℝ) :
    Hinv2 ≠ c • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  op2_ne_smul_one (by norm_num) c

theorem hHpos_rank2 (a : EuclideanSpace ℝ (Fin 2)) (ha : a ≠ 0) : 0 < ⟪a, H2 a⟫ := by
  rw [H2, inner_op2]
  rcases eq_or_ne (a 1) 0 with h1 | h1
  · have h0 : a 0 ≠ 0 := fun h => ha (eq_zero_of_coords h h1)
    have hpos : 0 < a 0 * a 0 := mul_self_pos.2 h0
    rw [h1]
    nlinarith
  · have hpos : 0 < a 1 * a 1 := mul_self_pos.2 h1
    nlinarith [sq_nonneg (a 0 + a 1 / 2)]

/-- `Ring.inverse H = ((4, −6), (−6, 12))`. -/
theorem ringInverse_H2 : Ring.inverse H2 = Hinv2 := by
  have hu : IsUnit H2 := isUnit_of_inner_pos hHpos_rank2
  calc Ring.inverse H2 = Ring.inverse H2 * 1 := by rw [mul_one]
    _ = Ring.inverse H2 * (H2 * Hinv2) := by rw [H2_mul_Hinv2]
    _ = Ring.inverse H2 * H2 * Hinv2 := by rw [mul_assoc]
    _ = 1 * Hinv2 := by rw [Ring.inverse_mul_cancel _ hu]
    _ = Hinv2 := one_mul _

/-- The Gram limit `n^{-1}X̃'X̃ → H`. -/
theorem hHlim_rank2 :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n)) atTop (𝓝 H2) := by
  have hfun : ∀ n : ℕ, (n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n)
      = op2 ((n : ℝ)⁻¹ * g00 n) ((n : ℝ)⁻¹ * g01 n) ((n : ℝ)⁻¹ * g01 n)
        ((n : ℝ)⁻¹ * g11 n) := by
    intro n
    rw [gramCLM_rank2, smul_op2]
  refine Tendsto.congr (fun n => (hfun n).symm) ?_
  have h := tendsto_op2 tendsto_g00 tendsto_g01 tendsto_g01 tendsto_g11
  rw [H2]
  exact h

/-! ### The score variance and fourth-moment conditions -/

theorem sum_inner_sq_rank2 (n : ℕ) (t : EuclideanSpace ℝ (Fin 2)) :
    ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫ ^ 2 * (1 : ℝ)
      = (t 0) ^ 2 * g00 n + 2 * t 0 * t 1 * g01 n + (t 1) ^ 2 * g11 n := by
  have hterm : ∀ o : Fin n,
      ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫ ^ 2 * (1 : ℝ)
        = (t 0) ^ 2 * (if o.val = 0 then (0 : ℝ) else 1)
          + 2 * t 0 * t 1 * ((o.val : ℝ) / (n : ℝ))
          + (t 1) ^ 2 * ((o.val : ℝ) / (n : ℝ)) ^ 2 := by
    intro o
    rw [inner_withinRow_rank2]
    by_cases h : o.val = 0
    · have hz : ((o.val : ℝ) / (n : ℝ)) = 0 := by rw [h]; simp
      rw [hz]
      simp [h]
    · simp only [h, if_false]
      ring
  rw [Finset.sum_congr rfl fun o _ => hterm o, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, sum_ite_fin n 1, sum_rvec,
    sum_rvec_sq, g00]
  ring

theorem hSn_rank2 (t : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫ ^ 2 * (1 : ℝ)) atTop
      (𝓝 (t ⬝ᵥ (Smat2 *ᵥ t))) := by
  have hfun : ∀ n : ℕ, (n : ℝ)⁻¹ *
      ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫ ^ 2 * (1 : ℝ)
      = (t 0) ^ 2 * ((n : ℝ)⁻¹ * g00 n) + 2 * t 0 * t 1 * ((n : ℝ)⁻¹ * g01 n)
        + (t 1) ^ 2 * ((n : ℝ)⁻¹ * g11 n) := by
    intro n
    rw [sum_inner_sq_rank2]
    ring
  refine Tendsto.congr (fun n => (hfun n).symm) ?_
  have h := ((tendsto_g00.const_mul ((t 0) ^ 2)).add
    (tendsto_g01.const_mul (2 * t 0 * t 1))).add (tendsto_g11.const_mul ((t 1) ^ 2))
  rw [dotProduct_Smat2]
  have heq : (t 0) ^ 2 * 1 + 2 * t 0 * t 1 * (1 / 2) + (t 1) ^ 2 * (1 / 3)
      = (t 0) ^ 2 + t 0 * t 1 + (t 1) ^ 2 / 3 := by ring
  rw [← heq]
  exact h

theorem abs_inner_withinRow_le (n : ℕ) (o : Fin n) (t : EuclideanSpace ℝ (Fin 2)) :
    |⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫| ≤ |t 0| + |t 1| := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) o.isLt
    exact_mod_cast hn
  have h1 : |(if o.val = 0 then (0 : ℝ) else 1)| ≤ 1 := by
    by_cases h : o.val = 0 <;> simp [h]
  have h2 : |(o.val : ℝ) / (n : ℝ)| ≤ 1 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (o.val : ℝ)),
      abs_of_nonneg hnpos.le, div_le_one hnpos]
    exact_mod_cast o.isLt.le
  rw [inner_withinRow_rank2]
  calc |t 0 * (if o.val = 0 then (0 : ℝ) else 1) + t 1 * ((o.val : ℝ) / (n : ℝ))|
      ≤ |t 0 * (if o.val = 0 then (0 : ℝ) else 1)| + |t 1 * ((o.val : ℝ) / (n : ℝ))| :=
        abs_add_le _ _
    _ = |t 0| * |(if o.val = 0 then (0 : ℝ) else 1)| + |t 1| * |(o.val : ℝ) / (n : ℝ)| := by
        rw [abs_mul, abs_mul]
    _ ≤ |t 0| * 1 + |t 1| * 1 := by
        have a1 : |t 0| * |(if o.val = 0 then (0 : ℝ) else 1)| ≤ |t 0| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        have a2 : |t 1| * |(o.val : ℝ) / (n : ℝ)| ≤ |t 1| * 1 :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        linarith
    _ = |t 0| + |t 1| := by ring

theorem pow_four_le_of_abs_le {x B : ℝ} (h : |x| ≤ B) : x ^ 4 ≤ B ^ 4 := by
  have hB : (0 : ℝ) ≤ B := (abs_nonneg x).trans h
  have h2 : x ^ 2 ≤ B ^ 2 := by
    have hsq := sq_abs x
    nlinarith [abs_nonneg x]
  calc x ^ 4 = x ^ 2 * x ^ 2 := by ring
    _ ≤ B ^ 2 * B ^ 2 := mul_self_le_mul_self (sq_nonneg x) h2
    _ = B ^ 4 := by ring

/-- The fourth-moment condition, from the bound `|x̃_o't| ≤ |t_0| + |t_1|`. -/
theorem hlin4_rank2 (t : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ *
        ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫ ^ 4) atTop (𝓝 0) := by
  set c : ℝ := |t 0| + |t 1| with hc
  have hc0 : (0 : ℝ) ≤ c := by positivity
  refine squeeze_zero (g := fun n : ℕ => (n : ℝ)⁻¹ * c ^ 4) (fun n => ?_) (fun n => ?_) ?_
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun o _ => by positivity)
  · have hsum : ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫ ^ 4
        ≤ (n : ℝ) * c ^ 4 := by
      calc ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫ ^ 4
          ≤ ∑ _o : Fin n, c ^ 4 :=
            Finset.sum_le_sum fun o _ => pow_four_le_of_abs_le (abs_inner_withinRow_le n o t)
        _ = (n : ℝ) * c ^ 4 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases eq_or_ne (n : ℝ) 0 with hn0 | hn0
    · simp [hn0]
    · calc ((n : ℝ) ^ 2)⁻¹ * ∑ o : Fin n, ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫ ^ 4
          ≤ ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) * c ^ 4) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (n : ℝ)⁻¹ * c ^ 4 := by field_simp
  · simpa using tendsto_ginv.mul_const (c ^ 4)

/-! ### The inverse Gram operators

`A n` and its limit are taken to be `Ring.inverse`, as in `clt_a_of_gram_limit`. -/

theorem hAsolve_rank2 :
    ∀ᶠ n : ℕ in atTop, ∀ a : EuclideanSpace ℝ (Fin 2),
      Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n))
        ((n : ℝ)⁻¹ • gram (⨆ m, feSpace n m) (X2 n) a) = a := by
  filter_upwards [eventually_ge_atTop 3, eventually_ne_atTop 0] with n hn hn0 a
  have hu : IsUnit ((n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n)) :=
    isUnit_smul (isUnit_gramCLM _ _ (identified_rank2 hn))
      (inv_ne_zero (Nat.cast_ne_zero.2 hn0))
  have hmul := Ring.inverse_mul_cancel _ hu
  calc Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n))
          ((n : ℝ)⁻¹ • gram (⨆ m, feSpace n m) (X2 n) a)
      = (Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n)) *
          ((n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n))) a := rfl
    _ = a := by rw [hmul]; rfl

theorem hAlim_rank2 :
    Tendsto (fun n : ℕ => Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n))) atTop
      (𝓝 (Ring.inverse H2)) :=
  tendsto_inverse hHlim_rank2 (isUnit_of_inner_pos hHpos_rank2)

/-! ### The model and the estimator -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The observed outcome, at `K = 2`. -/
noncomputable def yW2 (ξ : ℕ × ℕ → Ω → ℝ) (β : EuclideanSpace ℝ (Fin 2)) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin n) := X2 n β + (∑ m, feW n m) + nuW ξ n ω

/-- The estimator `β̂_n = β + (X̃'X̃)^{-1}X̃'ν`, constructed from the score. -/
noncomputable def bW2 (ξ : ℕ × ℕ → Ω → ℝ) (β : EuclideanSpace ℝ (Fin 2)) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin 2) :=
  β + Ring.inverse (gramCLM (⨆ m, feSpace n m) (X2 n))
      (score (⨆ m, feSpace n m) (X2 n) (nuW ξ n ω))

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem isMFESlope_bW2 (ξ : ℕ × ℕ → Ω → ℝ) (β : EuclideanSpace ℝ (Fin 2)) {n : ℕ} (hn : 3 ≤ n)
    (ω : Ω) : IsMFESlope (⨆ m, feSpace n m) (X2 n) (yW2 ξ β n ω) (bW2 ξ β n ω) := by
  have hu : IsUnit (gramCLM (⨆ m, feSpace n m) (X2 n)) :=
    isUnit_gramCLM _ _ (identified_rank2 hn)
  refine isMFESlope_of_gram_sub_eq_score (s := ∑ m, feW n m) (v := nuW ξ n ω) rfl
    (Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m (feW_mem n m)) ?_
  have hsub : bW2 ξ β n ω - β
      = Ring.inverse (gramCLM (⨆ m, feSpace n m) (X2 n))
          (score (⨆ m, feSpace n m) (X2 n) (nuW ξ n ω)) := by
    simp [bW2]
  rw [hsub]
  have hmul := Ring.mul_inverse_cancel _ hu
  calc gram (⨆ m, feSpace n m) (X2 n)
        (Ring.inverse (gramCLM (⨆ m, feSpace n m) (X2 n))
          (score (⨆ m, feSpace n m) (X2 n) (nuW ξ n ω)))
      = (gramCLM (⨆ m, feSpace n m) (X2 n) *
          Ring.inverse (gramCLM (⨆ m, feSpace n m) (X2 n)))
            (score (⨆ m, feSpace n m) (X2 n) (nuW ξ n ω)) := rfl
    _ = score (⨆ m, feSpace n m) (X2 n) (nuW ξ n ω) := by rw [hmul]; rfl

theorem measurable_bW2 {ξ : ℕ × ℕ → Ω → ℝ} (hξ : ∀ i, Measurable (ξ i))
    (β : EuclideanSpace ℝ (Fin 2)) (n : ℕ) : Measurable (bW2 ξ β n) := by
  have h : Measurable fun ω => score (⨆ m, feSpace n m) (X2 n) (nuW ξ n ω) := by
    refine measurable_score _ _ fun o => ?_
    simp only [nuW_apply]
    exact ((hξ (0, 0)).mul_const _).add (hξ (n, o.val))
  exact (((Ring.inverse (gramCLM (⨆ m, feSpace n m) (X2 n))).continuous.measurable).comp
    h).const_add β

/-! ### Examples -/

/-- **Theorem 4(a) at `K = 2`.** On this design `β̂_n` is both a joint-projection Mundlak slope
and a multiway fixed-effects slope, `√n(β̂_n − β)` converges in distribution to
`H⁻¹ N(0, S)` with `H⁻¹ = ((4, −6), (−6, 12))`, `S` is positive definite, and none of `S`, `H`,
`H⁻¹` is a multiple of the identity. -/
theorem clt_a_rank2_witness (β : EuclideanSpace ℝ (Fin 2)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (X2 n))
          (X2 n) (yW2 ξ β n ω) (bW2 ξ β n ω))
    ∧ (∀ᶠ n : ℕ in atTop, ∀ ω,
        IsMFESlope (⨆ m, feSpace n m) (X2 n) (yW2 ξ β n ω) (bW2 ξ β n ω))
    ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bW2 ξ β n ω - β)) atTop
        (fun z => Hinv2 z) (fun _ => P) (multivariateGaussian 0 Smat2)
    ∧ Smat2.PosDef
    ∧ (∀ c : ℝ, Smat2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ c : ℝ, H2 ≠ c • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
    ∧ (∀ c : ℝ, Hinv2 ≠ c • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hmeas : ∀ (n : ℕ) (o : Fin n), Measurable (errW ξ n o) := fun n o => hmeasξ _
  have hindep : ∀ n : ℕ, iIndepFun (errW ξ n) P := fun n =>
    hindepξ.precomp (g := fun o : Fin n => (n, o.val))
      (fun a b hab => Fin.val_injective (congrArg Prod.snd hab))
  have hmean : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ∂P = 0 := by
    intro n o
    show ∫ ω, ξ (n, o.val) ω ∂P = 0
    rw [(hlawξ (n, o.val)).integral_eq, integral_id_rade]
  have hL2 : ∀ (n : ℕ) (o : Fin n), MemLp (errW ξ n o) 2 P := fun n o =>
    (hlawξ (n, o.val)).memLp memLp_id_rade
  have hint4 : ∀ (n : ℕ) (o : Fin n), Integrable (fun ω => errW ξ n o ω ^ 4) P := fun n o =>
    (hlawξ (n, o.val)).integrable_fun_comp integrable_pow4_rade
  have hvar : ∀ (n : ℕ) (o : Fin n), Var[errW ξ n o; P] = 1 := by
    intro n o
    show Var[ξ (n, o.val); P] = 1
    rw [(hlawξ (n, o.val)).variance_eq, variance_id_rade]
  have hmom : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ^ 4 ∂P ≤ 1 := by
    intro n o
    show ∫ ω, ξ (n, o.val) ω ^ 4 ∂P ≤ 1
    have h : ∫ ω, ξ (n, o.val) ω ^ 4 ∂P = ∫ x, x ^ 4 ∂rade := by
      simpa [Function.comp_def] using
        (hlawξ (n, o.val)).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [h, integral_pow4_rade]
  have hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, feSpace n m) (X2 n) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact identified_rank2 hn
  have hMFE : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsMFESlope (⨆ m, feSpace n m) (X2 n) (yW2 ξ β n ω) (bW2 ξ β n ω) := by
    filter_upwards [eventually_ge_atTop 3] with n hn ω
    exact isMFESlope_bW2 ξ β hn ω
  have hJM : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (X2 n))
        (X2 n) (yW2 ξ β n ω) (bW2 ξ β n ω) := by
    filter_upwards [hid, hMFE] with n hidn hMFEn ω
    exact (jm_equiv hidn (dvec_mem n) _ _).mpr (hMFEn ω)
  refine ⟨Ω, mΩ, P, hprobξ, ξ, hJM, hMFE, ?_, Smat2_posDef, Smat2_ne_smul_one,
    H2_ne_smul_one, Hinv2_ne_smul_one⟩
  rw [← ringInverse_H2]
  exact (clt_a (O := fun n => Fin n) (fun n => Fintype.card_fin n) feSpace X2 β
    feW (fun n m => feW_mem n m) (nuW ξ) (yW2 ξ β) (fun n ω => rfl)
    (aaW ξ) (fun n m ω => aaW_mem ξ n m ω) (errW ξ) (fun _ _ => 1) 1
    (fun n ω => rfl) hmeas hindep hmean hL2 hint4 hvar hmom
    Smat2 Smat2_posDef hSn_rank2 hlin4_rank2
    (fun n => Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n)))
    (Ring.inverse H2) hAsolve_rank2 hAlim_rank2
    dvec dvec_mem hid (bW2 ξ β) (bW2 ξ β)
    (fun n => (measurable_bW2 hmeasξ β n).aemeasurable)
    (fun n => (measurable_bW2 hmeasξ β n).aemeasurable) hJM hMFE).1

/-- **Theorem 4(b) at `K = 2`.** The same design, through `clt_b`; the directional limits `hdir`
are obtained from `scalar_clt`. -/
theorem clt_b_rank2_witness (β : EuclideanSpace ℝ (Fin 2)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      (∀ᶠ n : ℕ in atTop, ∀ ω, IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (X2 n))
          (X2 n) (yW2 ξ β n ω) (bW2 ξ β n ω))
    ∧ TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bW2 ξ β n ω - β)) atTop
        (fun z => Hinv2 z) (fun _ => P) (multivariateGaussian 0 Smat2) := by
  obtain ⟨Ω, mΩ, P, ξ, hmeasξ, hlawξ, hindepξ, hprobξ⟩ := exists_iid (ℕ × ℕ) rade
  have hmeas : ∀ (n : ℕ) (o : Fin n), Measurable (errW ξ n o) := fun n o => hmeasξ _
  have hindep : ∀ n : ℕ, iIndepFun (errW ξ n) P := fun n =>
    hindepξ.precomp (g := fun o : Fin n => (n, o.val))
      (fun a b hab => Fin.val_injective (congrArg Prod.snd hab))
  have hmean : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ∂P = 0 := by
    intro n o
    show ∫ ω, ξ (n, o.val) ω ∂P = 0
    rw [(hlawξ (n, o.val)).integral_eq, integral_id_rade]
  have hL2 : ∀ (n : ℕ) (o : Fin n), MemLp (errW ξ n o) 2 P := fun n o =>
    (hlawξ (n, o.val)).memLp memLp_id_rade
  have hint4 : ∀ (n : ℕ) (o : Fin n), Integrable (fun ω => errW ξ n o ω ^ 4) P := fun n o =>
    (hlawξ (n, o.val)).integrable_fun_comp integrable_pow4_rade
  have hvar : ∀ (n : ℕ) (o : Fin n), Var[errW ξ n o; P] = 1 := by
    intro n o
    show Var[ξ (n, o.val); P] = 1
    rw [(hlawξ (n, o.val)).variance_eq, variance_id_rade]
  have hmom : ∀ (n : ℕ) (o : Fin n), ∫ ω, errW ξ n o ω ^ 4 ∂P ≤ 1 := by
    intro n o
    show ∫ ω, ξ (n, o.val) ω ^ 4 ∂P ≤ 1
    have h : ∫ ω, ξ (n, o.val) ω ^ 4 ∂P = ∫ x, x ^ 4 ∂rade := by
      simpa [Function.comp_def] using
        (hlawξ (n, o.val)).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    rw [h, integral_pow4_rade]
  have hid : ∀ᶠ n : ℕ in atTop, Identified (⨆ m, feSpace n m) (X2 n) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact identified_rank2 hn
  have hMFE : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsMFESlope (⨆ m, feSpace n m) (X2 n) (yW2 ξ β n ω) (bW2 ξ β n ω) := by
    filter_upwards [eventually_ge_atTop 3] with n hn ω
    exact isMFESlope_bW2 ξ β hn ω
  have hJM : ∀ᶠ n : ℕ in atTop, ∀ ω,
      IsAugSlope (jmControls (dvec n) (⨆ m, feSpace n m) (X2 n))
        (X2 n) (yW2 ξ β n ω) (bW2 ξ β n ω) := by
    filter_upwards [hid, hMFE] with n hidn hMFEn ω
    exact (jm_equiv hidn (dvec_mem n) _ _).mpr (hMFEn ω)
  have hnumeas : ∀ (n : ℕ) (o : Fin n), Measurable fun ω => nuW ξ n ω o := by
    intro n o
    simp only [nuW_apply]
    exact ((hmeasξ (0, 0)).mul_const _).add (hmeasξ (n, o.val))
  have hdir : ∀ t : EuclideanSpace ℝ (Fin 2), t ≠ 0 →
      TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
          ⟪score (⨆ m, feSpace n m) (X2 n) (nuW ξ n ω), t⟫) atTop
        (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 (t ⬝ᵥ (Smat2 *ᵥ t)).toNNReal) := by
    intro t ht
    have hs2 : 0 < t ⬝ᵥ (Smat2 *ᵥ t) := dotProduct_mulVec_pos_of_posDef Smat2_posDef ht
    have T := scalar_clt (P := P) (O := fun n => Fin n) (fun n => Fintype.card_fin n)
      (fun n o => ⟪withinRow (⨆ m, feSpace n m) (X2 n) o, t⟫) (errW ξ) (fun _ _ => (1 : ℝ))
      1 _ hmeas hindep hmean hL2 hint4 hvar hmom hs2 (hSn_rank2 t) (hlin4_rank2 t)
    refine T.congr (fun n => ?_) (by rfl)
    filter_upwards with ω
    rw [inner_score_eq_sum (feSpace n) (X2 n) (aaW ξ n) (fun m ω => aaW_mem ξ n m ω)
      (errW ξ n) (nuW ξ n) (fun ω => rfl) t ω]
  refine ⟨Ω, mΩ, P, hprobξ, ξ, hJM, ?_⟩
  rw [← ringInverse_H2]
  exact (clt_b (O := fun n => Fin n) feSpace X2 β feW (fun n m => feW_mem n m)
    (nuW ξ) (yW2 ξ β) (fun n ω => rfl) hnumeas Smat2 Smat2_posDef hdir
    (fun n => Ring.inverse ((n : ℝ)⁻¹ • gramCLM (⨆ m, feSpace n m) (X2 n)))
    (Ring.inverse H2) hAsolve_rank2 hAlim_rank2
    dvec dvec_mem hid (bW2 ξ β) (bW2 ξ β)
    (fun n => (measurable_bW2 hmeasξ β n).aemeasurable)
    (fun n => (measurable_bW2 hmeasξ β n).aemeasurable) hJM hMFE).1

/-! ### The unconditional form at `K = 2`

The design σ-field is `⊥`, and the limit law is transferred through
`clt_a_unconditional_of_frozen`. -/

/-- The unconditional limit law of Theorem 4(a) at `K = 2`, obtained from `clt_a_rank2_witness`
and `condCharFunD_bot`, together with the non-degeneracy of `S`, `H` and `H⁻¹`. -/
theorem clt_a_rank2_unconditional_witness (β : EuclideanSpace ℝ (Fin 2)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ × ℕ → Ω → ℝ),
      TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (bW2 ξ β n ω - β)) atTop
        (fun z => Hinv2 z) (fun _ => P) (multivariateGaussian 0 Smat2)
    ∧ Smat2.PosDef
    ∧ (∀ c : ℝ, Smat2 ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ c : ℝ, H2 ≠ c • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
    ∧ (∀ c : ℝ, Hinv2 ≠ c • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) := by
  obtain ⟨Ω, mΩ, P, hP, ξ, _, _, hclt, hSpd, hSne, hHne, hHinvne⟩ := clt_a_rank2_witness β
  refine ⟨Ω, mΩ, P, hP, ξ, ?_, hSpd, hSne, hHne, hHinvne⟩
  exact clt_a_unconditional_of_frozen ⊥ bot_le P β hclt.forall_aemeasurable Smat2 Hinv2
    (fun _ => P) (fun _ n ω => bW2 ξ β n ω)
    (fun n t => by rw [condCharFunD_bot P (hclt.forall_aemeasurable n) t])
    (Filter.Eventually.of_forall fun _ => hclt)

end Rank2Witness
end CLT
end Multiway
