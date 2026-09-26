import Multiway.Quadform
import Multiway.LeverageCond
import Multiway.Wald
import Multiway.Cgm
import Multiway.Sequence
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The heteroskedasticity-robust variance estimator

This file formalizes Theorem 7 of the paper (the heteroskedasticity-robust estimator) and
Lemma SM.B.8(c) (the multiway cluster-robust estimator under absorbed clustering, variance
bounds). The residual maker `R` is an abstract symmetric idempotent matrix, `𝓜̂_W` is treated
entry by entry through a `𝒟`-measurable weight `w`, and the conditional moment identities of the
errors enter as hypotheses in the shape of `Multiway.Quadform`.

## Main results

* `abs_condExp_meatW_sub_le`, `condExp_meatW_var_le`: conditional bias and fluctuation bounds.
* `tendstoInProb_meatW_sub`: `n^{-1}𝓜̂_W - S_n →ᵖ 0` over a sequence of designs.
* `tendstoInProb_nVhat`: `nV̂_W →ᵖ H^{-1}SH^{-1}`.
* `vhat_wald`, `vhat_wald_of_nVhat`: Theorem 7(b), with the central limit theorem as a
  hypothesis; the second derives the variance limit from Theorem 7(a).
* `cgm_meat_var_le`, `cgm_diag_var_le`: Lemma SM.B.8(c).
-/

namespace Multiway
namespace Vhat

open Filter Finset MeasureTheory ProbabilityTheory

open scoped Matrix Topology

/-! ## The Frobenius norm under conjugation by a symmetric idempotent matrix

`‖RAR‖_F ≤ ‖A‖_F` for symmetric idempotent `R`, from `‖A‖²_F = ‖RA‖²_F + ‖(I-R)A‖²_F`. -/

section Frobenius

variable {O : Type*} [Fintype O] [DecidableEq O]

omit [DecidableEq O] in
/-- `tr(A'SA) = ‖SA‖²_F` for a symmetric idempotent `S`. -/
theorem trace_conj_eq_rectFrobSq {S : Matrix O O ℝ} (hsym : Sᵀ = S) (hidem : S * S = S)
    (A : Matrix O O ℝ) : (Aᵀ * S * A).trace = rectFrobSq (S * A) := by
  rw [rectFrobSq_eq_trace, Matrix.transpose_mul, hsym]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc S S A, hidem]

omit [Fintype O] in
/-- `I - S` is symmetric idempotent whenever `S` is. -/
theorem one_sub_symm {S : Matrix O O ℝ} (hsym : Sᵀ = S) : ((1 : Matrix O O ℝ) - S)ᵀ = 1 - S := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, hsym]

theorem one_sub_idem {S : Matrix O O ℝ} (hidem : S * S = S) :
    ((1 : Matrix O O ℝ) - S) * (1 - S) = 1 - S := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one, hidem, sub_self, sub_zero]

/-- `‖RA‖_F ≤ ‖A‖_F` for a symmetric idempotent `R`. -/
theorem rectFrobSq_mul_left_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    (A : Matrix O O ℝ) : rectFrobSq (R * A) ≤ rectFrobSq A := by
  have hone : (Aᵀ * 1 * A).trace = rectFrobSq A := by
    rw [trace_conj_eq_rectFrobSq (S := (1 : Matrix O O ℝ)) Matrix.transpose_one
      (Matrix.one_mul _) A, Matrix.one_mul]
  have hsplit : (Aᵀ * 1 * A).trace
      = (Aᵀ * R * A).trace + (Aᵀ * ((1 : Matrix O O ℝ) - R) * A).trace := by
    rw [← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.mul_add]
    congr 2
    simp
  have h1 : (Aᵀ * R * A).trace = rectFrobSq (R * A) := trace_conj_eq_rectFrobSq hsym hidem A
  have h2 : (Aᵀ * ((1 : Matrix O O ℝ) - R) * A).trace = rectFrobSq (((1 : Matrix O O ℝ) - R) * A) :=
    trace_conj_eq_rectFrobSq (one_sub_symm hsym) (one_sub_idem hidem) A
  have h3 : 0 ≤ rectFrobSq (((1 : Matrix O O ℝ) - R) * A) := rectFrobSq_nonneg _
  rw [hone] at hsplit
  rw [h1, h2] at hsplit
  linarith

/-- The same on the right, by transposition. -/
theorem rectFrobSq_mul_right_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    (A : Matrix O O ℝ) : rectFrobSq (A * R) ≤ rectFrobSq A := by
  have h : rectFrobSq (A * R) = rectFrobSq (R * Aᵀ) := by
    rw [← rectFrobSq_transpose (A * R), Matrix.transpose_mul, hsym]
  rw [h, ← rectFrobSq_transpose A]
  exact rectFrobSq_mul_left_le hsym hidem _

/-- `‖RAR‖_F ≤ ‖A‖_F` for a symmetric idempotent `R`. -/
theorem rectFrobSq_conj_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    (A : Matrix O O ℝ) : rectFrobSq (R * A * R) ≤ rectFrobSq A :=
  (rectFrobSq_mul_right_le hsym hidem (R * A)).trans (rectFrobSq_mul_left_le hsym hidem A)

omit [DecidableEq O] in
theorem rectFrobSq_smul (c : ℝ) (A : Matrix O O ℝ) :
    rectFrobSq (c • A) = c ^ 2 * rectFrobSq A := by
  rw [rectFrobSq, rectFrobSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Matrix.smul_apply, smul_eq_mul, mul_pow]

theorem rectFrobSq_diagonal (d : O → ℝ) :
    rectFrobSq (Matrix.diagonal d) = ∑ o : O, d o ^ 2 := by
  rw [rectFrobSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne' _ hj]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h

end Frobenius

/-! ## The leverage entries

`∑_{o'} R²_{oo'} = R_oo`, `R_oo ∈ [0,1]` and `∑_{o'≠o} R²_{oo'} = R_oo(1-R_oo)`, from symmetry
and idempotence. -/

section Entries

variable {O : Type*} [Fintype O] [DecidableEq O] {R : Matrix O O ℝ}

omit [DecidableEq O] in
/-- `∑_{o'} R²_{oo'} = (R²)_{oo} = R_oo`. -/
theorem sum_sq_row (hsym : Rᵀ = R) (hidem : R * R = R) (o : O) :
    ∑ o' : O, R o o' ^ 2 = R o o := by
  have hentry : ∀ o' : O, R o' o = R o o' := fun o' => by
    have := congrFun (congrFun hsym o) o'
    simpa using this
  have h : (R * R) o o = ∑ o' : O, R o o' ^ 2 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun o' _ => by rw [hentry o', sq]
  rw [← h, hidem]

omit [DecidableEq O] in
theorem diag_nonneg (hsym : Rᵀ = R) (hidem : R * R = R) (o : O) : 0 ≤ R o o := by
  rw [← sum_sq_row hsym hidem o]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq O] in
/-- `R_oo ≤ 1`: the diagonal entry dominates its own square. -/
theorem diag_le_one (hsym : Rᵀ = R) (hidem : R * R = R) (o : O) : R o o ≤ 1 := by
  have hterm : R o o ^ 2 ≤ ∑ o' : O, R o o' ^ 2 :=
    Finset.single_le_sum (f := fun o' : O => R o o' ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ o)
  rw [sum_sq_row hsym hidem o] at hterm
  nlinarith [diag_nonneg hsym hidem o]

omit [DecidableEq O] in
/-- `|R_{oo'}| ≤ 1`: every entry is dominated by its row sum of squares, which is `R_oo ≤ 1`. -/
theorem abs_entry_le_one (hsym : Rᵀ = R) (hidem : R * R = R) (o o' : O) : |R o o'| ≤ 1 := by
  have hterm : R o o' ^ 2 ≤ ∑ o'' : O, R o o'' ^ 2 :=
    Finset.single_le_sum (f := fun o'' : O => R o o'' ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ o')
  rw [sum_sq_row hsym hidem o] at hterm
  have h1 : R o o' ^ 2 ≤ 1 := hterm.trans (diag_le_one hsym hidem o)
  nlinarith [abs_nonneg (R o o'), sq_abs (R o o')]

/-- `∑_{o'≠o} R²_{oo'} = R_oo(1-R_oo)`. -/
theorem sum_erase_sq_row (hsym : Rᵀ = R) (hidem : R * R = R) (o : O) :
    ∑ o' ∈ Finset.univ.erase o, R o o' ^ 2 = R o o * (1 - R o o) := by
  have h := Finset.sum_erase_add (Finset.univ : Finset O) (fun o' : O => R o o' ^ 2)
    (Finset.mem_univ o)
  rw [sum_sq_row hsym hidem o] at h
  nlinarith [h]

end Entries

/-! ## Theorem 7(a): the conditional bias

`E[ν̂²_{FE,o}|𝒟] = ∑_{o'} R²_{oo'}σ²_ε(o')`, the bound
`|E[ν̂²_{FE,o}|𝒟] - σ²_ε(o)| ≤ 3σ̄²(1-R_oo)`, and its sum against `x̃_{oj}x̃_{ok}` with
`∑_o(1-R_oo) = d_[Δ]+K`. -/

section Bias

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The residual `ν̂_{FE,o} = (Rε)_o = ∑_{o'} R_{oo'}ε_{o'}`. -/
def feResidual (R : Matrix O O ℝ) (eps : O → Ω → ℝ) (o : O) (ω : Ω) : ℝ :=
  ∑ o' : O, R o o' * eps o' ω

theorem feResidual_one (eps : O → Ω → ℝ) (o : O) (ω : Ω) :
    feResidual (1 : Matrix O O ℝ) eps o ω = eps o ω := by
  rw [feResidual, Finset.sum_eq_single o]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro o' _ ho'
    rw [Matrix.one_apply_ne' ho', zero_mul]
  · intro h; exact absurd (Finset.mem_univ o) h

omit [DecidableEq O] in
theorem integrable_feResidual_sq (R : Matrix O O ℝ) {eps : O → Ω → ℝ}
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ) (o : O) :
    Integrable (fun ω => feResidual R eps o ω ^ 2) μ := by
  have hrw : (fun ω => feResidual R eps o ω ^ 2)
      = ∑ o' : O, ∑ o'' : O, (fun ω => (R o o' * R o o'') * (eps o' ω * eps o'' ω)) :=
    LeverageCond.sq_sum_eq_double_sum (fun o' (_ : Ω) => R o o') eps
  rw [hrw]
  exact integrable_finsetSum' _ fun o' _ =>
    integrable_finsetSum' _ fun o'' _ => (hint o' o'').const_mul _

/-- `E[ν̂²_{FE,o}|𝒟] = ∑_{o'} R²_{oo'}σ²_ε(o')`. Neither symmetry nor idempotence of `R` is
used. -/
theorem condExp_feResidual_sq (R : Matrix O O ℝ) {eps sig : O → Ω → ℝ}
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0) (o : O) :
    μ[fun ω => feResidual R eps o ω ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ o' : O, R o o' ^ 2 * sig o' ω :=
  LeverageCond.condExp_sq_linearCombination 𝒟 (c := fun o' (_ : Ω) => R o o') (eps := eps)
    (fun _ => stronglyMeasurable_const) hint (fun o' o'' => (hint o' o'').const_mul _) hcross

/-- `|E[ν̂²_{FE,o}|𝒟] - σ²_ε(o)| ≤ σ²_ε(o)(1-R_oo) + 2σ̄²(1-R_oo) ≤ 3σ̄²(1-R_oo)`. -/
theorem abs_condExp_feResidual_sq_sub_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    {eps sig : O → Ω → ℝ} {sbar : ℝ}
    (hsig0 : ∀ o ω, 0 ≤ sig o ω) (hsigB : ∀ o ω, sig o ω ≤ sbar)
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0) (o : O) :
    ∀ᵐ ω ∂μ, |μ[fun ω => feResidual R eps o ω ^ 2 | 𝒟] ω - sig o ω|
      ≤ 3 * sbar * (1 - R o o) := by
  filter_upwards [condExp_feResidual_sq 𝒟 R hint hcross o] with ω hω
  rw [hω]
  -- use `∑_{o'} R²_{oo'} = R_oo`
  rw [LeverageCond.sum_sq_split (sum_sq_row hsym hidem o) (fun o' => sig o' ω) o]
  set d : ℝ := R o o with hd
  set E : ℝ := ∑ o' ∈ Finset.univ.erase o, R o o' ^ 2 * (sig o' ω - sig o ω) with hE
  have hd0 : 0 ≤ d := diag_nonneg hsym hidem o
  have hd1 : d ≤ 1 := diag_le_one hsym hidem o
  have hsb : 0 ≤ sbar := le_trans (hsig0 o ω) (hsigB o ω)
  have hmass : ∑ o' ∈ Finset.univ.erase o, R o o' ^ 2 = d * (1 - d) :=
    sum_erase_sq_row hsym hidem o
  have hupper : E ≤ 2 * sbar * (d * (1 - d)) := by
    have hstep : E ≤ ∑ o' ∈ Finset.univ.erase o, R o o' ^ 2 * (2 * sbar) := by
      refine Finset.sum_le_sum fun o' _ => ?_
      have : sig o' ω - sig o ω ≤ 2 * sbar := by
        have := hsigB o' ω; have := hsig0 o ω; linarith
      exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
    rw [← Finset.sum_mul, hmass] at hstep
    linarith
  have hlower : -(2 * sbar * (d * (1 - d))) ≤ E := by
    have hstep : ∑ o' ∈ Finset.univ.erase o, R o o' ^ 2 * (-(2 * sbar)) ≤ E := by
      refine Finset.sum_le_sum fun o' _ => ?_
      have : -(2 * sbar) ≤ sig o' ω - sig o ω := by
        have := hsig0 o' ω; have := hsigB o ω; linarith
      exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
    rw [← Finset.sum_mul, hmass] at hstep
    linarith
  have hso : sig o ω ≤ sbar := hsigB o ω
  have hso0 : 0 ≤ sig o ω := hsig0 o ω
  have h1d : (0 : ℝ) ≤ 1 - d := by linarith
  have hp1 : 0 ≤ sbar * (1 - d) := mul_nonneg hsb h1d
  have hp2 : 0 ≤ (1 - d) * sig o ω := mul_nonneg h1d hso0
  have hp3 : (1 - d) * sig o ω ≤ (1 - d) * sbar := mul_le_mul_of_nonneg_left hso h1d
  have hp4 : 2 * sbar * (d * (1 - d)) ≤ 2 * sbar * (1 - d) := by
    have h2s : (0 : ℝ) ≤ 2 * sbar := by linarith
    nlinarith [mul_nonneg h2s h1d]
  have hgoal : d * sig o ω + E - sig o ω = E - (1 - d) * sig o ω := by ring
  rw [abs_le, hgoal]
  constructor
  · linarith
  · linarith

omit [DecidableEq O] in
/-- `E[𝓜̂_W|𝒟]` entry by entry: the `𝒟`-measurable weight comes out by the pull-out
property. -/
theorem condExp_meatW (R : Matrix O O ℝ) {eps w : O → Ω → ℝ}
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hintw : ∀ o, Integrable (fun ω => w o ω * feResidual R eps o ω ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * feResidual R eps o ω ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, w o ω * μ[fun ω => feResidual R eps o ω ^ 2 | 𝒟] ω :=
  Quadform.condExp_sum_mul 𝒟 (Finset.univ : Finset O) hw
    (fun o => integrable_feResidual_sq (μ := μ) R hint o) hintw

/-- **Theorem 7(a), conditional bias.** `|E[𝓜̂_W|𝒟] - 𝓜_n| ≤ 3σ̄²B²(d_[Δ]+K)` entry by entry,
with `𝓜_n = ∑_o x̃_ox̃_o'σ²_ε(o)`. The hypothesis `htr` is `∑_o(1-R_oo) = d_[Δ]+K` and `hB`
bounds the weights. -/
theorem abs_condExp_meatW_sub_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    {eps sig w : O → Ω → ℝ} {sbar B2 dK : ℝ}
    (hsig0 : ∀ o ω, 0 ≤ sig o ω) (hsigB : ∀ o ω, sig o ω ≤ sbar)
    (hB : ∀ o ω, |w o ω| ≤ B2)
    (htr : ∑ o : O, (1 - R o o) = dK)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hintw : ∀ o, Integrable (fun ω => w o ω * feResidual R eps o ω ^ 2) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0) :
    ∀ᵐ ω ∂μ, |μ[fun ω => ∑ o : O, w o ω * feResidual R eps o ω ^ 2 | 𝒟] ω
        - ∑ o : O, w o ω * sig o ω| ≤ 3 * sbar * B2 * dK := by
  have hall : ∀ᵐ ω ∂μ, ∀ o : O,
      |μ[fun ω => feResidual R eps o ω ^ 2 | 𝒟] ω - sig o ω| ≤ 3 * sbar * (1 - R o o) :=
    ae_all_iff.2 fun o =>
      abs_condExp_feResidual_sq_sub_le 𝒟 hsym hidem hsig0 hsigB hint hcross o
  filter_upwards [condExp_meatW 𝒟 R hw hint hintw, hall] with ω hmean hbias
  rw [hmean, ← Finset.sum_sub_distrib]
  have hterm : ∀ o : O,
      |w o ω * μ[fun ω => feResidual R eps o ω ^ 2 | 𝒟] ω - w o ω * sig o ω|
        ≤ B2 * (3 * sbar * (1 - R o o)) := by
    intro o
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (hB o ω) (hbias o) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hB o ω))
  calc |∑ o : O, (w o ω * μ[fun ω => feResidual R eps o ω ^ 2 | 𝒟] ω - w o ω * sig o ω)|
      ≤ ∑ o : O, |w o ω * μ[fun ω => feResidual R eps o ω ^ 2 | 𝒟] ω - w o ω * sig o ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ o : O, B2 * (3 * sbar * (1 - R o o)) := Finset.sum_le_sum fun o _ => hterm o
    _ = 3 * sbar * B2 * dK := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, htr]; ring

end Bias

/-! ## Theorem 7(a): the conditional fluctuation

Entry `(j,k)` of `𝓜̂_W` is `ε'RA_{jk}Rε` with `A_{jk} = diag(x̃_{oj}x̃_{ok})`, and Lemma SM.C.5
gives `Var(n^{-1}(𝓜̂_W)_{jk}|𝒟) ≤ 3CB⁴/n`. -/

section Fluctuation

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The matrix `c · RA_{jk}R`, with the normalizer `c` (in the theorem, `n^{-1}`) carried
inside. -/
def meatMat (c : ℝ) (R : Matrix O O ℝ) (w : O → Ω → ℝ) (ω : Ω) : Matrix O O ℝ :=
  c • (R * Matrix.diagonal (fun o => w o ω) * R)

theorem meatMat_apply (c : ℝ) (R : Matrix O O ℝ) (w : O → Ω → ℝ) (ω : Ω) (o₁ o₂ : O) :
    meatMat c R w ω o₁ o₂ = c * ∑ o : O, R o₁ o * w o ω * R o o₂ := by
  rw [meatMat, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun o _ => by rw [Matrix.mul_diagonal]

/-- `ε'(cRA_{jk}R)ε = c ∑_o x̃_{oj}x̃_{ok} ν̂²_{FE,o}` in every realization. -/
theorem quadForm_meatMat {R : Matrix O O ℝ} (hsym : Rᵀ = R) (c : ℝ) (w eps : O → Ω → ℝ)
    (ω : Ω) :
    Quadform.quadForm (meatMat c R w) eps ω
      = c * ∑ o : O, w o ω * feResidual R eps o ω ^ 2 := by
  have hsymm : ∀ o o' : O, R o' o = R o o' := fun o o' => by
    have := congrFun (congrFun hsym o) o'
    simpa using this
  rw [Quadform.quadForm_apply, Fintype.sum_prod_type]
  have hstep : ∀ o₁ : O, ∑ o₂ : O, meatMat c R w ω o₁ o₂ * (eps o₁ ω * eps o₂ ω)
      = ∑ o₂ : O, ∑ o : O,
          (R o₁ o * eps o₁ ω) * (c * w o ω * (R o o₂ * eps o₂ ω)) := by
    intro o₁
    refine Finset.sum_congr rfl fun o₂ _ => ?_
    rw [meatMat_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun o _ => by ring
  calc ∑ o₁ : O, ∑ o₂ : O, meatMat c R w ω o₁ o₂ * (eps o₁ ω * eps o₂ ω)
      = ∑ o₁ : O, ∑ o₂ : O, ∑ o : O,
          (R o₁ o * eps o₁ ω) * (c * w o ω * (R o o₂ * eps o₂ ω)) :=
        Finset.sum_congr rfl fun o₁ _ => hstep o₁
    _ = ∑ o₁ : O, ∑ o : O, ∑ o₂ : O,
          (R o₁ o * eps o₁ ω) * (c * w o ω * (R o o₂ * eps o₂ ω)) :=
        Finset.sum_congr rfl fun o₁ _ => Finset.sum_comm
    _ = ∑ o : O, ∑ o₁ : O, ∑ o₂ : O,
          (R o₁ o * eps o₁ ω) * (c * w o ω * (R o o₂ * eps o₂ ω)) := Finset.sum_comm
    _ = c * ∑ o : O, w o ω * feResidual R eps o ω ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun o _ => ?_
        have hinner : ∀ o₁ : O, ∑ o₂ : O,
            (R o₁ o * eps o₁ ω) * (c * w o ω * (R o o₂ * eps o₂ ω))
            = (R o₁ o * eps o₁ ω) * (c * w o ω * ∑ o₂ : O, R o o₂ * eps o₂ ω) := by
          intro o₁
          rw [Finset.mul_sum, Finset.mul_sum]
        have hrow : ∑ o₁ : O, R o₁ o * eps o₁ ω = feResidual R eps o ω := by
          rw [feResidual]
          exact Finset.sum_congr rfl fun o₁ _ => by rw [hsymm o o₁]
        calc ∑ o₁ : O, ∑ o₂ : O,
              (R o₁ o * eps o₁ ω) * (c * w o ω * (R o o₂ * eps o₂ ω))
            = ∑ o₁ : O, (R o₁ o * eps o₁ ω) * (c * w o ω * ∑ o₂ : O, R o o₂ * eps o₂ ω) :=
              Finset.sum_congr rfl fun o₁ _ => hinner o₁
          _ = (∑ o₁ : O, R o₁ o * eps o₁ ω) * (c * w o ω * ∑ o₂ : O, R o o₂ * eps o₂ ω) :=
              (Finset.sum_mul _ _ _).symm
          _ = c * (w o ω * feResidual R eps o ω ^ 2) := by
              rw [hrow]
              show feResidual R eps o ω * (c * w o ω * feResidual R eps o ω) = _
              ring

/-- Every entry of `cRA_{jk}R` is bounded. -/
theorem abs_meatMat_apply_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    {w : O → Ω → ℝ} {B2 : ℝ} (hB : ∀ o ω, |w o ω| ≤ B2) (c : ℝ) (o₁ o₂ : O) (ω : Ω) :
    |meatMat c R w ω o₁ o₂| ≤ |c| * (Fintype.card O * B2) := by
  have hB0 : 0 ≤ B2 := le_trans (abs_nonneg _) (hB o₁ ω)
  rw [meatMat_apply, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  calc |∑ o : O, R o₁ o * w o ω * R o o₂|
      ≤ ∑ o : O, |R o₁ o * w o ω * R o o₂| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _o : O, B2 := by
        refine Finset.sum_le_sum fun o _ => ?_
        rw [abs_mul, abs_mul]
        have h1 : |R o₁ o| ≤ 1 := abs_entry_le_one hsym hidem o₁ o
        have h2 : |R o o₂| ≤ 1 := abs_entry_le_one hsym hidem o o₂
        have h3 : |w o ω| ≤ B2 := hB o ω
        calc |R o₁ o| * |w o ω| * |R o o₂|
            ≤ 1 * B2 * 1 :=
              mul_le_mul (mul_le_mul h1 h3 (abs_nonneg _) zero_le_one) h2 (abs_nonneg _)
                (by linarith)
          _ = B2 := by ring
    _ = Fintype.card O * B2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `‖cRA_{jk}R‖²_F ≤ c²‖A_{jk}‖²_F ≤ c²B⁴n`. -/
theorem rectFrobSq_meatMat_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    {w : O → Ω → ℝ} {B2 : ℝ} (hB : ∀ o ω, |w o ω| ≤ B2) (c : ℝ) (ω : Ω) :
    rectFrobSq (meatMat c R w ω) ≤ c ^ 2 * (B2 ^ 2 * Fintype.card O) := by
  rw [meatMat, rectFrobSq_smul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  refine (rectFrobSq_conj_le hsym hidem _).trans ?_
  rw [rectFrobSq_diagonal]
  calc ∑ o : O, w o ω ^ 2 ≤ ∑ _o : O, B2 ^ 2 := by
        refine Finset.sum_le_sum fun o _ => ?_
        have := hB o ω
        nlinarith [abs_nonneg (w o ω), sq_abs (w o ω)]
    _ = B2 ^ 2 * Fintype.card O := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ### Lemma SM.C.5 with bounded coefficients -/

theorem integrable_bdd_mul {f g : Ω → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f μ)
    (hb : ∀ ω, |f ω| ≤ B) (hg : Integrable g μ) : Integrable (fun ω => f ω * g ω) μ :=
  hg.bdd_mul hf (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)

/-- Lemma SM.C.5 with a deterministic Frobenius bound:
`E[(ε'Wε)²|𝒟] - (E[ε'Wε|𝒟])² ≤ 3CF` whenever `‖W‖²_F ≤ F` in every realization. -/
theorem condExp_quadForm_le_const [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ)
    {W : Ω → Matrix O O ℝ} {eps sig : O → Ω → ℝ} {C Bw F : ℝ} (hC : 0 ≤ C) (hBw : 0 ≤ Bw)
    (hW : ∀ o o', StronglyMeasurable[𝒟] fun ω => W ω o o')
    (hWb : ∀ o o' ω, |W ω o o'| ≤ Bw)
    (hFr : ∀ ω, rectFrobSq (W ω) ≤ F)
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hvar : ∀ o, μ[fun ω => eps o ω * eps o ω | 𝒟] =ᵐ[μ] sig o)
    (hcross : ∀ o o', o ≠ o' → μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0)
    (hfour : ∀ o, μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ≤ᵐ[μ] fun _ => C)
    (hpair : ∀ o o', o ≠ o' →
      μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
        =ᵐ[μ] fun ω => sig o ω * sig o' ω)
    (hmixed : ∀ a o o' : O, o ≠ o' →
      μ[fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0)
    (hquad : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0) :
    (fun ω => μ[fun ω => Quadform.quadForm W eps ω ^ 2 | 𝒟] ω
        - μ[Quadform.quadForm W eps | 𝒟] ω ^ 2)
      ≤ᵐ[μ] fun _ => 3 * C * F := by
  have hmeas : ∀ o o', AEStronglyMeasurable (fun ω => W ω o o') μ :=
    fun o o' => ((hW o o').mono h𝒟).aestronglyMeasurable
  have hiW2 : ∀ p : O × O,
      Integrable (fun ω => W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω)) μ :=
    fun p => integrable_bdd_mul (hmeas p.1 p.2) (fun ω => hWb p.1 p.2 ω) (hi2 p)
  have hiW4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
        * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))) μ := by
    intro r
    have hprod : ∀ ω, |W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2| ≤ Bw * Bw := by
      intro ω
      rw [abs_mul]
      exact mul_le_mul (hWb _ _ ω) (hWb _ _ ω) (abs_nonneg _) hBw
    have := integrable_bdd_mul (μ := μ)
      ((hmeas r.1.1 r.1.2).mul (hmeas r.2.1 r.2.2)) hprod (hi4 r)
    simpa [mul_assoc] using this
  have hmain := Quadform.condExp_quadForm_sq_sub_sq_condExp_le 𝒟 h𝒟 hC hW hi2 hiW2 hi4 hiW4
    hvar hcross hfour hpair hmixed hquad
  filter_upwards [hmain] with ω hω
  refine hω.trans ?_
  exact mul_le_mul_of_nonneg_left (hFr ω) (by linarith)

/-- **Theorem 7(a), conditional fluctuation.** The conditional variance of `c(𝓜̂_W)_{jk}` is
at most `3Cc²B⁴n`, written as `E[Q²|𝒟] - (E[Q|𝒟])²`. -/
theorem condExp_meatW_var_le [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ)
    {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    {eps sig w : O → Ω → ℝ} {C B2 c : ℝ} (hC : 0 ≤ C) (hB0 : 0 ≤ B2)
    (hB : ∀ o ω, |w o ω| ≤ B2)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hvar : ∀ o, μ[fun ω => eps o ω * eps o ω | 𝒟] =ᵐ[μ] sig o)
    (hcross : ∀ o o', o ≠ o' → μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0)
    (hfour : ∀ o, μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ≤ᵐ[μ] fun _ => C)
    (hpair : ∀ o o', o ≠ o' →
      μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
        =ᵐ[μ] fun ω => sig o ω * sig o' ω)
    (hmixed : ∀ a o o' : O, o ≠ o' →
      μ[fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0)
    (hquad : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0) :
    (fun ω => μ[fun ω => (c * ∑ o : O, w o ω * feResidual R eps o ω ^ 2) ^ 2 | 𝒟] ω
        - μ[fun ω => c * ∑ o : O, w o ω * feResidual R eps o ω ^ 2 | 𝒟] ω ^ 2)
      ≤ᵐ[μ] fun _ => 3 * C * (c ^ 2 * (B2 ^ 2 * Fintype.card O)) := by
  have hfun : Quadform.quadForm (meatMat c R w) eps
      = fun ω => c * ∑ o : O, w o ω * feResidual R eps o ω ^ 2 :=
    funext fun ω => quadForm_meatMat hsym c w eps ω
  have hWm : ∀ o₁ o₂, StronglyMeasurable[𝒟] fun ω => meatMat c R w ω o₁ o₂ := by
    intro o₁ o₂
    have hrw : (fun ω => meatMat c R w ω o₁ o₂)
        = fun ω => c * ∑ o : O, R o₁ o * w o ω * R o o₂ :=
      funext fun ω => meatMat_apply c R w ω o₁ o₂
    rw [hrw]
    have hsum : StronglyMeasurable[𝒟] fun ω => ∑ o : O, R o₁ o * w o ω * R o o₂ := by
      have hsplit : (fun ω => ∑ o : O, R o₁ o * w o ω * R o o₂)
          = ∑ o : O, fun ω => R o₁ o * w o ω * R o o₂ := by
        funext ω; simp only [Finset.sum_apply]
      rw [hsplit]
      exact Finset.stronglyMeasurable_sum _ fun o _ =>
        ((hw o).const_mul (R o₁ o)).mul_const (R o o₂)
    exact hsum.const_mul c
  have hres := condExp_quadForm_le_const 𝒟 h𝒟 (W := meatMat c R w) (eps := eps) (sig := sig)
    (Bw := |c| * (Fintype.card O * B2)) hC
    (mul_nonneg (abs_nonneg c) (mul_nonneg (by positivity) hB0)) hWm
    (abs_meatMat_apply_le hsym hidem hB c)
    (rectFrobSq_meatMat_le hsym hidem hB c) hi2 hi4 hvar hcross hfour hpair hmixed hquad
  rw [hfun] at hres
  exact hres

/-- The fluctuation bound at `c = n^{-1}`: `Var(n^{-1}(𝓜̂_W)_{jk}|𝒟) ≤ 3CB⁴/n`. -/
theorem condExp_meatW_var_le_normalized [IsFiniteMeasure μ] [Nonempty O] (h𝒟 : 𝒟 ≤ mΩ)
    {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    {eps sig w : O → Ω → ℝ} {C B2 : ℝ} (hC : 0 ≤ C) (hB0 : 0 ≤ B2)
    (hB : ∀ o ω, |w o ω| ≤ B2)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hvar : ∀ o, μ[fun ω => eps o ω * eps o ω | 𝒟] =ᵐ[μ] sig o)
    (hcross : ∀ o o', o ≠ o' → μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0)
    (hfour : ∀ o, μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ≤ᵐ[μ] fun _ => C)
    (hpair : ∀ o o', o ≠ o' →
      μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
        =ᵐ[μ] fun ω => sig o ω * sig o' ω)
    (hmixed : ∀ a o o' : O, o ≠ o' →
      μ[fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0)
    (hquad : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0) :
    (fun ω => μ[fun ω =>
          ((Fintype.card O : ℝ)⁻¹ * ∑ o : O, w o ω * feResidual R eps o ω ^ 2) ^ 2 | 𝒟] ω
        - μ[fun ω =>
            (Fintype.card O : ℝ)⁻¹ * ∑ o : O, w o ω * feResidual R eps o ω ^ 2 | 𝒟] ω ^ 2)
      ≤ᵐ[μ] fun _ => 3 * C * B2 ^ 2 / Fintype.card O := by
  have hn : (0 : ℝ) < Fintype.card O := by
    exact_mod_cast Fintype.card_pos
  have hres := condExp_meatW_var_le 𝒟 h𝒟 hsym hidem (c := (Fintype.card O : ℝ)⁻¹) hC hB0 hB hw
    hi2 hi4 hvar hcross hfour hpair hmixed hquad
  refine hres.mono fun ω hω => hω.trans (le_of_eq ?_)
  field_simp

/-- **Lemma SM.B.8(c), second claim.** Every entry of `s∑_o x̃_ox̃_o'ε²_o` has conditional
variance at most `3Cs²B⁴n`; at `s = n^{-1}` this is `3CB⁴/n`. It is the `R = I` instance of
`condExp_meatW_var_le`. -/
theorem cgm_diag_var_le [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ)
    {eps sig w : O → Ω → ℝ} {C B2 s : ℝ} (hC : 0 ≤ C) (hB0 : 0 ≤ B2)
    (hB : ∀ o ω, |w o ω| ≤ B2)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hvar : ∀ o, μ[fun ω => eps o ω * eps o ω | 𝒟] =ᵐ[μ] sig o)
    (hcross : ∀ o o', o ≠ o' → μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0)
    (hfour : ∀ o, μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ≤ᵐ[μ] fun _ => C)
    (hpair : ∀ o o', o ≠ o' →
      μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
        =ᵐ[μ] fun ω => sig o ω * sig o' ω)
    (hmixed : ∀ a o o' : O, o ≠ o' →
      μ[fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0)
    (hquad : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0) :
    (fun ω => μ[fun ω => (s * ∑ o : O, w o ω * eps o ω ^ 2) ^ 2 | 𝒟] ω
        - μ[fun ω => s * ∑ o : O, w o ω * eps o ω ^ 2 | 𝒟] ω ^ 2)
      ≤ᵐ[μ] fun _ => 3 * C * (s ^ 2 * (B2 ^ 2 * Fintype.card O)) := by
  have hres := condExp_meatW_var_le 𝒟 h𝒟 (R := (1 : Matrix O O ℝ)) Matrix.transpose_one
    (Matrix.one_mul _) (c := s) hC hB0 hB hw hi2 hi4 hvar hcross hfour hpair hmixed hquad
  simp only [feResidual_one] at hres
  exact hres

end Fluctuation

/-! ## Theorem 7(b)

The Wald statistic `[√n 𝓡(β̂_JM - β)]'[𝓡(nV̂_W)𝓡']^{-1}[√n 𝓡(β̂_JM - β)]` converges to `χ²_r`,
by `Multiway.Wald.wald_of_clt`. The central limit theorem is a hypothesis, stated already
restricted through `𝓡`. -/

section WaldClause

open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]

/-- The restricted deviation `𝓡(β̂ - β)`. -/
noncomputable def restrictVec (Rm : Matrix ι K ℝ) (v : EuclideanSpace ℝ K) :
    EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm (Rm *ᵥ (WithLp.ofLp v))

omit [Fintype ι] [DecidableEq ι] [DecidableEq K] in
@[simp] theorem restrictVec_apply (Rm : Matrix ι K ℝ) (v : EuclideanSpace ℝ K) (i : ι) :
    restrictVec Rm v i = ∑ j : K, Rm i j * v j := by
  rw [restrictVec]
  rfl

theorem restrictVec_one (v : EuclideanSpace ℝ ι) : restrictVec (1 : Matrix ι ι ℝ) v = v := by
  ext i
  rw [restrictVec_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro j _ hj
    rw [Matrix.one_apply_ne' hj, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [DecidableEq ι] [DecidableEq K] in
/-- `𝓡C𝓡' ≻ 0` from `C ≻ 0` and `𝓡` of full row rank, the latter as
`Function.Injective 𝓡.vecMul`. -/
theorem posDef_restrict {Rm : Matrix ι K ℝ} {C : Matrix K K ℝ} (hC : C.PosDef)
    (hRank : Function.Injective Rm.vecMul) : (Rm * C * Rmᵀ).PosDef := by
  have h := hC.mul_mul_conjTranspose_same hRank
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

omit [Fintype ι] [DecidableEq ι] [DecidableEq K] in
/-- Measurability of the restricted, normalized variance estimate, from measurability of
`V̂_n`. -/
theorem measurable_smul_restrict {Ω : Type*} [MeasurableSpace Ω] (a : ℝ) (Rm : Matrix ι K ℝ)
    {f : Ω → Matrix K K ℝ} (hf : Measurable f) :
    Measurable fun ω => a • (Rm * f ω * Rmᵀ) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have hrw : (fun ω => (a • (Rm * f ω * Rmᵀ)) i j)
      = fun ω => a * ∑ k : K, (∑ l : K, Rm i l * f ω l k) * Rmᵀ k j := by
    funext ω
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  rw [hrw]
  refine Measurable.const_mul ?_ a
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (Finset.measurable_sum _ fun l _ =>
    (hf.eval_matrix (i := l) (j := k)).const_mul (Rm i l)).mul_const (Rmᵀ k j)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [DecidableEq K] in
/-- **Theorem 7(b)**, with the variance limit as a hypothesis. `P(𝓡V̂_W𝓡' ≻ 0) → 1` and
`𝒲(𝓡, V̂_W; β̂_JM) ⟶ᵈ χ²_r`. The central limit theorem is the hypothesis `hCLT`, in restricted
form, and `hVhlim` is the restricted variance limit; `vhat_wald_of_nVhat` derives the latter.
The normalizer is a positive sequence `a_n` (the paper's `a_n = n`). -/
theorem vhat_wald
    {Rm : Matrix ι K ℝ} {C : Matrix K K ℝ} (hC : C.PosDef)
    (hRank : Function.Injective Rm.vecMul)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {Vh : ℕ → Ω → Matrix K K ℝ}
    (hVhherm : ∀ n ω, (Rm * Vh n ω * Rmᵀ).IsHermitian)
    (hVhmeas : ∀ n, Measurable (Vh n))
    (hVhlim : TendstoInMeasure P
      (fun n ω => frobNorm (a n • (Rm * Vh n ω * Rmᵀ) - Rm * C * Rmᵀ)) atTop (fun _ => 0))
    {dev : ℕ → Ω → EuclideanSpace ℝ K} {G : Ω' → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution
      (fun n ω => Real.sqrt (a n) • restrictVec Rm (dev n ω)) atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 (Rm * C * Rmᵀ)) :
    Tendsto (fun n => P {ω | (Rm * Vh n ω * Rmᵀ).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => Wald.waldStat (Rm * Vh n ω * Rmᵀ) (restrictVec Rm (dev n ω))) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P) (multivariateGaussian 0 1) := by
  obtain ⟨hevent, hchi⟩ := Wald.wald_of_clt (P := P) (P' := P') (Sg := Rm * C * Rmᵀ)
    (posDef_restrict hC hRank)
    (A := fun n ω => a n • (Rm * Vh n ω * Rmᵀ))
    (fun n ω => (hVhherm n ω).smul (IsSelfAdjoint.all (a n)))
    (fun n => measurable_smul_restrict (a n) Rm (hVhmeas n)) hVhlim
    (u := fun n ω => Real.sqrt (a n) • restrictVec Rm (dev n ω)) (G := G) hCLT hG
  constructor
  · refine hevent.congr fun n => ?_
    congr 1
    ext ω
    exact Wald.posDef_smul_iff (ha n) _
  · have heq : (fun n ω => Wald.waldStat (a n • (Rm * Vh n ω * Rmᵀ))
        (Real.sqrt (a n) • restrictVec Rm (dev n ω)))
        = fun n ω => Wald.waldStat (Rm * Vh n ω * Rmᵀ) (restrictVec Rm (dev n ω)) := by
      funext n ω
      exact Wald.waldStat_smul (ha n) _ _
    rwa [heq] at hchi

end WaldClause

/-! ## Lemma SM.B.8(c)

Entry `(a,b)` of the multiway meat is `ε'Wε` with `W_{oo'} = x̃_{oa}x̃_{o'b}𝟙{o ∼ o'}`, and
`‖W‖²_F ≤ B⁴ J G_max n` by the union bound `𝟙{o ∼ o'} ≤ ∑_{j≤J} 𝟙{o ∼_{j} o'}`. -/

section CgmC

variable {O K D L : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `W_{oo'} = s x̃_{oa}x̃_{o'b}𝟙{o ∼ o'}`, with the normalizer `s` carried inside. -/
def linkWeightMat (c : D → O → L) (dims : Finset D) (X : O → K → Ω → ℝ) (a b : K) (s : ℝ)
    (ω : Ω) : Matrix O O ℝ :=
  Matrix.of fun o o' => s * (if Linked c dims o o' then X o a ω * X o' b ω else 0)

omit [Fintype O] [DecidableEq O] [DecidableEq D] in
theorem linkWeightMat_apply (c : D → O → L) (dims : Finset D) (X : O → K → Ω → ℝ) (a b : K)
    (s : ℝ) (ω : Ω) (o o' : O) :
    linkWeightMat c dims X a b s ω o o'
      = s * (if Linked c dims o o' then X o a ω * X o' b ω else 0) := rfl

/-- `s` times entry `(a,b)` of the multiway meat is the quadratic form `ε'Wε` with
`W = linkWeightMat` (Lemma SM.B.7). -/
theorem quadForm_linkWeightMat (c : D → O → L) (dims : Finset D) (X : O → K → Ω → ℝ)
    (eps : O → Ω → ℝ) (a b : K) (s : ℝ) (ω : Ω) :
    Quadform.quadForm (linkWeightMat c dims X a b s) eps ω
      = s * ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
          (-1 : ℝ) ^ (A.card + 1) *
            ∑ g ∈ cells c A,
              (∑ o ∈ g, X o a ω * eps o ω) * (∑ o' ∈ g, X o' b ω * eps o' ω) := by
  rw [Cgm.meat_eq_linkedPairs c dims X eps a b ω, Quadform.quadForm_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [linkWeightMat_apply]
  by_cases h : Linked c dims o o'
  · simp only [h, ite_true]
    ring
  · simp only [h, ite_false]
    ring

omit [DecidableEq O] [DecidableEq D] in
/-- The number of sharing pairs is at most `J G_max n`, where `hG` bounds every level-`{j}`
cell by `G_max`. -/
theorem sum_linked_le {c : D → O → L} {dims : Finset D} {Gmax : ℝ}
    (hG : ∀ j ∈ dims, ∀ o : O,
      (((Finset.univ : Finset O).filter (fun o' => c j o = c j o')).card : ℝ) ≤ Gmax) :
    ∑ o : O, ∑ o' : O, (if Linked c dims o o' then (1 : ℝ) else 0)
      ≤ (dims.card : ℝ) * Gmax * Fintype.card O := by
  classical
  have hpt : ∀ o o' : O, (if Linked c dims o o' then (1 : ℝ) else 0)
      ≤ ∑ j ∈ dims, (if c j o = c j o' then (1 : ℝ) else 0) := by
    intro o o'
    by_cases h : Linked c dims o o'
    · obtain ⟨j, hj, hcj⟩ := id h
      simp only [h, ite_true]
      refine le_trans (le_of_eq ?_)
        (Finset.single_le_sum (f := fun j : D => if c j o = c j o' then (1 : ℝ) else 0)
          (fun _ _ => by positivity) hj)
      simp only [hcj, ite_true]
    · simp only [h, ite_false]
      exact Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ o : O, ∑ o' : O, (if Linked c dims o o' then (1 : ℝ) else 0)
      ≤ ∑ o : O, ∑ o' : O, ∑ j ∈ dims, (if c j o = c j o' then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ => hpt o o'
    _ = ∑ o : O, ∑ j ∈ dims, ∑ o' : O, (if c j o = c j o' then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun o _ => Finset.sum_comm
    _ ≤ ∑ _o : O, ∑ _j ∈ dims, Gmax := by
        refine Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun j hj => ?_
        rw [Finset.sum_boole]
        exact hG j hj o
    _ = (dims.card : ℝ) * Gmax * Fintype.card O := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
        ring

omit [DecidableEq O] [DecidableEq D] in
/-- `‖W‖²_F ≤ s²B⁴ J G_max n`. -/
theorem rectFrobSq_linkWeightMat_le {c : D → O → L} {dims : Finset D} {X : O → K → Ω → ℝ}
    {a b : K} {B2 Gmax : ℝ}
    (hX : ∀ o o' ω, |X o a ω * X o' b ω| ≤ B2)
    (hG : ∀ j ∈ dims, ∀ o : O,
      (((Finset.univ : Finset O).filter (fun o' => c j o = c j o')).card : ℝ) ≤ Gmax)
    (s : ℝ) (ω : Ω) :
    rectFrobSq (linkWeightMat c dims X a b s ω)
      ≤ s ^ 2 * B2 ^ 2 * ((dims.card : ℝ) * Gmax * Fintype.card O) := by
  have hstep : rectFrobSq (linkWeightMat c dims X a b s ω)
      ≤ ∑ o : O, ∑ o' : O,
          s ^ 2 * B2 ^ 2 * (if Linked c dims o o' then (1 : ℝ) else 0) := by
    rw [rectFrobSq]
    refine Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ => ?_
    rw [linkWeightMat_apply]
    by_cases h : Linked c dims o o'
    · simp only [h, ite_true]
      rw [mul_pow]
      have hsq : (X o a ω * X o' b ω) ^ 2 ≤ B2 ^ 2 := by
        have := hX o o' ω
        nlinarith [abs_nonneg (X o a ω * X o' b ω), sq_abs (X o a ω * X o' b ω)]
      calc s ^ 2 * (X o a ω * X o' b ω) ^ 2
          ≤ s ^ 2 * B2 ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg s)
        _ = s ^ 2 * B2 ^ 2 * 1 := by ring
    · simp only [h, ite_false, mul_zero]
      norm_num
  refine hstep.trans ?_
  have hfac : ∑ o : O, ∑ o' : O,
      s ^ 2 * B2 ^ 2 * (if Linked c dims o o' then (1 : ℝ) else 0)
      = s ^ 2 * B2 ^ 2 * ∑ o : O, ∑ o' : O,
          (if Linked c dims o o' then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun o _ => (Finset.mul_sum _ _ _).symm
  rw [hfac]
  refine mul_le_mul_of_nonneg_left (sum_linked_le hG) ?_
  positivity

/-- **Lemma SM.B.8(c), first claim.** Conditionally on `𝒟`, `s` times entry `(a,b)` of the
multiway meat has variance at most `3C s² B⁴ J G_max n`; at `s = n^{-1}` this is
`3CB⁴ J G_max/n`. -/
theorem cgm_meat_var_le [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ)
    {c : D → O → L} {dims : Finset D} {X : O → K → Ω → ℝ} {eps sig : O → Ω → ℝ} {a b : K}
    {C B2 Gmax s : ℝ} (hC : 0 ≤ C) (hB0 : 0 ≤ B2)
    (hX : ∀ o o' ω, |X o a ω * X o' b ω| ≤ B2)
    (hG : ∀ j ∈ dims, ∀ o : O,
      (((Finset.univ : Finset O).filter (fun o' => c j o = c j o')).card : ℝ) ≤ Gmax)
    (hXm : ∀ o k, StronglyMeasurable[𝒟] (X o k))
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hvar : ∀ o, μ[fun ω => eps o ω * eps o ω | 𝒟] =ᵐ[μ] sig o)
    (hcross : ∀ o o', o ≠ o' → μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0)
    (hfour : ∀ o, μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ≤ᵐ[μ] fun _ => C)
    (hpair : ∀ o o', o ≠ o' →
      μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
        =ᵐ[μ] fun ω => sig o ω * sig o' ω)
    (hmixed : ∀ a' o o' : O, o ≠ o' →
      μ[fun ω => eps a' ω * eps a' ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0)
    (hquad : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0) :
    (fun ω => μ[fun ω => (s * ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
            (-1 : ℝ) ^ (A.card + 1) *
              ∑ g ∈ cells c A,
                (∑ o ∈ g, X o a ω * eps o ω) * (∑ o' ∈ g, X o' b ω * eps o' ω)) ^ 2 | 𝒟] ω
        - μ[fun ω => s * ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
            (-1 : ℝ) ^ (A.card + 1) *
              ∑ g ∈ cells c A,
                (∑ o ∈ g, X o a ω * eps o ω) * (∑ o' ∈ g, X o' b ω * eps o' ω) | 𝒟] ω ^ 2)
      ≤ᵐ[μ] fun _ =>
        3 * C * (s ^ 2 * B2 ^ 2 * ((dims.card : ℝ) * Gmax * Fintype.card O)) := by
  classical
  have hfun : Quadform.quadForm (linkWeightMat c dims X a b s) eps
      = fun ω => s * ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
          (-1 : ℝ) ^ (A.card + 1) *
            ∑ g ∈ cells c A,
              (∑ o ∈ g, X o a ω * eps o ω) * (∑ o' ∈ g, X o' b ω * eps o' ω) :=
    funext fun ω => quadForm_linkWeightMat c dims X eps a b s ω
  have hWm : ∀ o o', StronglyMeasurable[𝒟]
      fun ω => linkWeightMat c dims X a b s ω o o' := by
    intro o o'
    have hrw : (fun ω => linkWeightMat c dims X a b s ω o o')
        = fun ω => s * (if Linked c dims o o' then X o a ω * X o' b ω else 0) :=
      funext fun ω => linkWeightMat_apply c dims X a b s ω o o'
    rw [hrw]
    exact (Cgm.stronglyMeasurable_pairCoeff 𝒟 (c := c) (dims := dims) (a := a) (b := b)
      hXm o o').const_mul s
  have hWb : ∀ o o' ω, |linkWeightMat c dims X a b s ω o o'| ≤ |s| * B2 := by
    intro o o' ω
    rw [linkWeightMat_apply, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
    by_cases h : Linked c dims o o'
    · simp only [h, ite_true]
      exact hX o o' ω
    · simp only [h, ite_false, abs_zero]
      exact hB0
  have hres := condExp_quadForm_le_const 𝒟 h𝒟 (W := linkWeightMat c dims X a b s)
    (eps := eps) (sig := sig) (Bw := |s| * B2) hC (by positivity) hWm hWb
    (rectFrobSq_linkWeightMat_le hX hG s) hi2 hi4 hvar hcross hfour hpair hmixed hquad
  rw [hfun] at hres
  exact hres

end CgmC

/-! ## Non-vacuity

The conditional clauses are instantiated on the one-point model of `Multiway.Quadform`, and
Theorem 7(b) on a Gaussian model. -/

section Witnesses

open Matrix

/-- `abs_condExp_meatW_sub_le` on the model `Ω = Unit`, `μ = dirac ()`, `𝒟 = ⊥`, `R = I`,
`ε_o = 𝟙{o = o₀}`, `σ²_ε(o) = 𝟙{o = o₀}`, `σ̄² = 1`, `w ≡ 1`. -/
theorem abs_condExp_meatW_sub_le_witness {O : Type*} [Fintype O] [DecidableEq O] (o₀ : O) :
    ∀ᵐ u ∂(Measure.dirac ()),
      |(Measure.dirac ())[fun u : Unit => ∑ o : O,
            (1 : ℝ) * feResidual (1 : Matrix O O ℝ) (Quadform.witnessEps o₀) o u ^ 2
            | (⊥ : MeasurableSpace Unit)] u
        - ∑ o : O, (1 : ℝ) * (if o = o₀ then (1 : ℝ) else 0)|
      ≤ 3 * 1 * 1 * 0 := by
  refine abs_condExp_meatW_sub_le (⊥ : MeasurableSpace Unit) (R := (1 : Matrix O O ℝ))
    Matrix.transpose_one (Matrix.one_mul _)
    (eps := Quadform.witnessEps o₀) (sig := fun o _ => if o = o₀ then (1 : ℝ) else 0)
    (w := fun _ _ => (1 : ℝ)) (sbar := 1) (B2 := 1) (dK := 0)
    (fun o _ => by by_cases h : o = o₀ <;> simp [h])
    (fun o _ => by by_cases h : o = o₀ <;> simp [h])
    (fun _ _ => by norm_num)
    ?_ (fun _ => stronglyMeasurable_const)
    (fun _ _ => Quadform.integrable_unit _) (fun _ => Quadform.integrable_unit _) ?_
  · simp
  · intro o' o''
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    by_cases h : o' = o''
    · subst h
      show Quadform.witnessEps o₀ o' u * Quadform.witnessEps o₀ o' u = _
      rw [Quadform.witnessEps_mul_self o₀ o' u]
      simp
    · show Quadform.witnessEps o₀ o' u * Quadform.witnessEps o₀ o'' u = _
      rw [Quadform.witnessEps_mul_eq_zero o₀ h u]
      simp [h]

/-- `condExp_meatW_var_le` on the same model, with `C = 1`, `B² = 1` and `c = 1`. -/
theorem condExp_meatW_var_le_witness {O : Type*} [Fintype O] [DecidableEq O] (o₀ : O) :
    (fun u : Unit => (Measure.dirac ())[fun u : Unit =>
          ((1 : ℝ) * ∑ o : O, (1 : ℝ) *
            feResidual (1 : Matrix O O ℝ) (Quadform.witnessEps o₀) o u ^ 2) ^ 2
          | (⊥ : MeasurableSpace Unit)] u
        - (Measure.dirac ())[fun u : Unit =>
            (1 : ℝ) * ∑ o : O, (1 : ℝ) *
              feResidual (1 : Matrix O O ℝ) (Quadform.witnessEps o₀) o u ^ 2
            | (⊥ : MeasurableSpace Unit)] u ^ 2)
      ≤ᵐ[Measure.dirac ()] fun _ : Unit =>
        3 * (1 : ℝ) * ((1 : ℝ) ^ 2 * ((1 : ℝ) ^ 2 * Fintype.card O)) := by
  refine condExp_meatW_var_le (⊥ : MeasurableSpace Unit) bot_le (R := (1 : Matrix O O ℝ))
    Matrix.transpose_one (Matrix.one_mul _)
    (eps := Quadform.witnessEps o₀) (sig := fun o _ => if o = o₀ then (1 : ℝ) else 0)
    (w := fun _ _ => (1 : ℝ)) (C := 1) (B2 := 1) (c := 1) zero_le_one zero_le_one
    (fun _ _ => by norm_num) (fun _ => stronglyMeasurable_const)
    (fun _ => Quadform.integrable_unit _) (fun _ => Quadform.integrable_unit _) ?_ ?_ ?_ ?_ ?_ ?_
  · intro o
    rw [Quadform.condExp_unit]
    exact Filter.Eventually.of_forall fun u => Quadform.witnessEps_mul_self o₀ o u
  · intro o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o' u = (0 : ℝ)
    exact Quadform.witnessEps_mul_eq_zero o₀ h u
  · intro o
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o u
        * (Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o u) ≤ (1 : ℝ)
    rw [Quadform.witnessEps_mul_self o₀ o u]
    by_cases h : o = o₀ <;> simp [h]
  · intro o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o u
        * (Quadform.witnessEps o₀ o' u * Quadform.witnessEps o₀ o' u)
        = (if o = o₀ then (1 : ℝ) else 0) * (if o' = o₀ then (1 : ℝ) else 0)
    rw [Quadform.witnessEps_mul_self o₀ o u, Quadform.witnessEps_mul_self o₀ o' u]
  · intro a o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ a u * Quadform.witnessEps o₀ a u
        * (Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o' u) = (0 : ℝ)
    rw [Quadform.witnessEps_mul_eq_zero o₀ h u, mul_zero]
  · intro p q hp _ _ _
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ p.1 u * Quadform.witnessEps o₀ p.2 u
        * (Quadform.witnessEps o₀ q.1 u * Quadform.witnessEps o₀ q.2 u) = (0 : ℝ)
    rw [Quadform.witnessEps_mul_eq_zero o₀ hp u, zero_mul]

/-- `cgm_meat_var_le` on the same model, with a single dimension whose clustering map is
constant, `X ≡ 1`, `s = 1`, `B² = 1`, `G_max = n`. -/
theorem cgm_meat_var_le_witness {O : Type*} [Fintype O] [DecidableEq O] (o₀ : O) :
    (fun u : Unit => (Measure.dirac ())[fun u : Unit =>
          ((1 : ℝ) * ∑ A ∈ ({0} : Finset (Fin 1)).powerset.filter (fun A => A.Nonempty),
            (-1 : ℝ) ^ (A.card + 1) *
              ∑ g ∈ cells (fun _ _ => (0 : Fin 1)) A,
                (∑ o ∈ g, (1 : ℝ) * Quadform.witnessEps o₀ o u) *
                  (∑ o' ∈ g, (1 : ℝ) * Quadform.witnessEps o₀ o' u)) ^ 2
          | (⊥ : MeasurableSpace Unit)] u
        - (Measure.dirac ())[fun u : Unit =>
            (1 : ℝ) * ∑ A ∈ ({0} : Finset (Fin 1)).powerset.filter (fun A => A.Nonempty),
              (-1 : ℝ) ^ (A.card + 1) *
                ∑ g ∈ cells (fun _ _ => (0 : Fin 1)) A,
                  (∑ o ∈ g, (1 : ℝ) * Quadform.witnessEps o₀ o u) *
                    (∑ o' ∈ g, (1 : ℝ) * Quadform.witnessEps o₀ o' u)
            | (⊥ : MeasurableSpace Unit)] u ^ 2)
      ≤ᵐ[Measure.dirac ()] fun _ : Unit =>
        3 * (1 : ℝ) * ((1 : ℝ) ^ 2 * (1 : ℝ) ^ 2 *
          ((({0} : Finset (Fin 1)).card : ℝ) * (Fintype.card O : ℝ) * Fintype.card O)) := by
  refine cgm_meat_var_le (⊥ : MeasurableSpace Unit) bot_le
    (c := fun _ _ => (0 : Fin 1)) (dims := ({0} : Finset (Fin 1)))
    (X := fun _ _ _ => (1 : ℝ)) (eps := Quadform.witnessEps o₀)
    (sig := fun o _ => if o = o₀ then (1 : ℝ) else 0) (a := 0) (b := 0)
    (C := 1) (B2 := 1) (Gmax := (Fintype.card O : ℝ)) (s := 1)
    zero_le_one zero_le_one (fun _ _ _ => by norm_num) ?_
    (fun _ _ => stronglyMeasurable_const)
    (fun _ => Quadform.integrable_unit _) (fun _ => Quadform.integrable_unit _) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j _ o
    refine le_trans ?_ (le_refl (Fintype.card O : ℝ))
    exact_mod_cast Finset.card_filter_le _ _
  · intro o
    rw [Quadform.condExp_unit]
    exact Filter.Eventually.of_forall fun u => Quadform.witnessEps_mul_self o₀ o u
  · intro o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o' u = (0 : ℝ)
    exact Quadform.witnessEps_mul_eq_zero o₀ h u
  · intro o
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o u
        * (Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o u) ≤ (1 : ℝ)
    rw [Quadform.witnessEps_mul_self o₀ o u]
    by_cases h : o = o₀ <;> simp [h]
  · intro o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o u
        * (Quadform.witnessEps o₀ o' u * Quadform.witnessEps o₀ o' u)
        = (if o = o₀ then (1 : ℝ) else 0) * (if o' = o₀ then (1 : ℝ) else 0)
    rw [Quadform.witnessEps_mul_self o₀ o u, Quadform.witnessEps_mul_self o₀ o' u]
  · intro a o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ a u * Quadform.witnessEps o₀ a u
        * (Quadform.witnessEps o₀ o u * Quadform.witnessEps o₀ o' u) = (0 : ℝ)
    rw [Quadform.witnessEps_mul_eq_zero o₀ h u, mul_zero]
  · intro p q hp _ _ _
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps o₀ p.1 u * Quadform.witnessEps o₀ p.2 u
        * (Quadform.witnessEps o₀ q.1 u * Quadform.witnessEps o₀ q.2 u) = (0 : ℝ)
    rw [Quadform.witnessEps_mul_eq_zero o₀ hp u, zero_mul]

/-- `vhat_wald` with `𝓡 = I_r`, `H^{-1}SH^{-1} = I_r`, `V̂_n = I_r`, `a_n = 1`, and the
identity on `(EuclideanSpace ℝ ι, N(0, I_r))` as the Gaussian deviation. -/
theorem vhat_wald_witness {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Tendsto (fun _ : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
        {_x : EuclideanSpace ℝ ι |
          ((1 : Matrix ι ι ℝ) * 1 * (1 : Matrix ι ι ℝ)ᵀ).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun (_ : ℕ) (y : EuclideanSpace ℝ ι) =>
            Wald.waldStat ((1 : Matrix ι ι ℝ) * 1 * (1 : Matrix ι ι ℝ)ᵀ)
              (restrictVec 1 y)) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2)
          (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
          (multivariateGaussian 0 1) := by
  have hone : (1 : Matrix ι ι ℝ) * 1 * (1 : Matrix ι ι ℝ)ᵀ = 1 := by
    rw [Matrix.transpose_one, Matrix.one_mul, Matrix.one_mul]
  refine vhat_wald (P := multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
    (Rm := (1 : Matrix ι ι ℝ)) (C := (1 : Matrix ι ι ℝ)) Matrix.PosDef.one ?_
    (a := fun _ => (1 : ℝ)) (fun _ => one_pos)
    (Vh := fun _ _ => (1 : Matrix ι ι ℝ)) (fun _ _ => by rw [hone]; exact Matrix.isHermitian_one)
    (fun _ => measurable_const) ?_
    (dev := fun _ => id) (G := id) ?_ ?_
  · intro v v' h
    simpa [Matrix.vecMul_one] using h
  · intro ε hε
    have hz : frobNorm ((1 : ℝ) • ((1 : Matrix ι ι ℝ) * 1 * (1 : Matrix ι ι ℝ)ᵀ)
        - (1 : Matrix ι ι ℝ) * 1 * (1 : Matrix ι ι ℝ)ᵀ) = 0 := by
      rw [one_smul, sub_self]
      simp [frobNorm, frobSq]
    have hset : {y : EuclideanSpace ℝ ι |
        ε ≤ edist (frobNorm ((1 : ℝ) • ((1 : Matrix ι ι ℝ) * 1 * (1 : Matrix ι ι ℝ)ᵀ)
            - (1 : Matrix ι ι ℝ) * 1 * (1 : Matrix ι ι ℝ)ᵀ)) ((fun _ => (0 : ℝ)) y)} = ∅ := by
      ext y
      simp only [hz, edist_self, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    simp only [hset, measure_empty]
    exact tendsto_const_nhds
  · have hfun : (fun (_ : ℕ) (y : EuclideanSpace ℝ ι) =>
        Real.sqrt (1 : ℝ) • restrictVec (1 : Matrix ι ι ℝ) (id y))
        = fun (_ : ℕ) => (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
      funext n y
      rw [Real.sqrt_one, one_smul, restrictVec_one]
    rw [hfun]
    exact tendstoInDistribution_const aemeasurable_id
  · rw [Measure.map_id, hone]

end Witnesses

/-! ## Theorem 7(a): the limit in probability

Over a sequence of designs with observation types `O j`, the conditional bias and fluctuation
bounds give `n^{-1}(𝓜̂_W)_{jk} - (S_n)_{jk} →ᵖ 0`, through
`(Q-A)² ≤ 2(Q - E[Q|𝒟])² + 2(E[Q|𝒟] - A)²`, the tower property and Markov's inequality at order
two. The hypothesis `hn` states `n → ∞`, and `hdK` states `(d_[Δ]+K)/n → 0`. The result is
stated entry by entry; `tendstoInProb_frobNorm_of_entries` assembles the matrix limit. -/

section Asymptotic

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `Z_j →ᵖ 0` from `Z_j² →ᵖ 0`. -/
theorem tendstoInProb_zero_of_sq {Z : ℕ → Ω → ℝ}
    (h : TendstoInMeasure P (fun j ω => Z j ω ^ 2) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h (ε ^ 2) (by positivity)) (fun j => zero_le) (fun j => measure_mono fun ω hω => ?_)
  have h1 : ε ≤ |Z j ω| := by
    have h2 : ε ≤ dist (Z j ω) ((fun _ => (0 : ℝ)) ω) := hω
    rwa [Real.dist_eq, sub_zero] at h2
  show ε ^ 2 ≤ dist ((fun j ω => Z j ω ^ 2) j ω) ((fun _ => (0 : ℝ)) ω)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (Z j ω), abs_nonneg (Z j ω)]

/-- Markov's inequality at order two: `E[Z_j²] → 0` gives `Z_j →ᵖ 0`. -/
theorem tendstoInProb_zero_of_integral_sq_le {Z : ℕ → Ω → ℝ}
    (hint : ∀ j, Integrable (fun ω => Z j ω ^ 2) P) {c : ℕ → ℝ}
    (hle : ∀ j, ∫ ω, Z j ω ^ 2 ∂P ≤ c j) (hc : Tendsto c atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_sq (P := P) ?_
  refine Sequence.tendstoInProb_zero_of_integral_abs_le hint (fun j => ?_) hc
  have habs : ∀ ω, |Z j ω ^ 2| = Z j ω ^ 2 := fun ω => abs_of_nonneg (sq_nonneg _)
  simp only [habs]
  exact hle j

/-- Convergence in probability from a conditional bias bound `b_j` and a conditional variance
bound `v_j`, both tending to `0`. The centering `A_j` need only be measurable. -/
theorem tendstoInProb_of_bias_condVar [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    {Q A : ℕ → Ω → ℝ} {b v : ℕ → ℝ}
    (hQ : ∀ j, MemLp (Q j) 2 P) (hA : ∀ j, AEStronglyMeasurable (A j) P)
    (hbias : ∀ j, ∀ᵐ ω ∂P, |(P[Q j | 𝒟]) ω - A j ω| ≤ b j)
    (hvar : ∀ j, (fun ω => (P[fun ω => Q j ω ^ 2 | 𝒟]) ω - (P[Q j | 𝒟]) ω ^ 2)
      ≤ᵐ[P] fun _ => v j)
    (hb : Tendsto b atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 0)) :
    TendstoInMeasure P (fun j ω => Q j ω - A j ω) atTop (fun _ => (0 : ℝ)) := by
  have hmL2 : ∀ j, MemLp (P[Q j | 𝒟]) 2 P := fun j => (hQ j).condExp one_le_two
  have hdiff : ∀ j, Integrable (fun ω => (Q j ω - (P[Q j | 𝒟]) ω) ^ 2) P :=
    fun j => ((hQ j).sub (hmL2 j)).integrable_sq
  have hcen : ∀ j, ∫ ω, (Q j ω - (P[Q j | 𝒟]) ω) ^ 2 ∂P ≤ v j := by
    intro j
    have hcv : ∫ ω, (ProbabilityTheory.condVar 𝒟 (Q j) P) ω ∂P
        = ∫ ω, (Q j ω - (P[Q j | 𝒟]) ω) ^ 2 ∂P := integral_condExp h𝒟
    have hle : ProbabilityTheory.condVar 𝒟 (Q j) P ≤ᵐ[P] fun _ => v j := by
      filter_upwards [ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp h𝒟 (hQ j),
        hvar j] with ω h1 h2
      have h1' : ProbabilityTheory.condVar 𝒟 (Q j) P ω
          = (P[fun ω => Q j ω ^ 2 | 𝒟]) ω - (P[Q j | 𝒟]) ω ^ 2 := h1
      rw [h1']
      exact h2
    have h3 : ∫ ω, (ProbabilityTheory.condVar 𝒟 (Q j) P) ω ∂P ≤ ∫ _ω, v j ∂P :=
      integral_mono_ae ProbabilityTheory.integrable_condVar (integrable_const _) hle
    rw [hcv] at h3
    simpa using h3
  have hQAmeas : ∀ j, AEStronglyMeasurable (fun ω => (Q j ω - A j ω) ^ 2) P := by
    intro j
    have h := (hQ j).aestronglyMeasurable.sub (hA j)
    refine (h.mul h).congr (Filter.Eventually.of_forall fun ω => ?_)
    show (Q j ω - A j ω) * (Q j ω - A j ω) = (Q j ω - A j ω) ^ 2
    ring
  have hbnd : ∀ j, ∀ᵐ ω ∂P, (Q j ω - A j ω) ^ 2
      ≤ 2 * (Q j ω - (P[Q j | 𝒟]) ω) ^ 2 + 2 * b j ^ 2 := by
    intro j
    filter_upwards [hbias j] with ω hω
    have h2 : ((P[Q j | 𝒟]) ω - A j ω) ^ 2 ≤ b j ^ 2 := by
      nlinarith [abs_nonneg ((P[Q j | 𝒟]) ω - A j ω), sq_abs ((P[Q j | 𝒟]) ω - A j ω), hω]
    nlinarith [sq_nonneg ((Q j ω - (P[Q j | 𝒟]) ω) - ((P[Q j | 𝒟]) ω - A j ω)), h2]
  have hboundint : ∀ j, Integrable
      (fun ω => 2 * (Q j ω - (P[Q j | 𝒟]) ω) ^ 2 + 2 * b j ^ 2) P :=
    fun j => ((hdiff j).const_mul 2).add (integrable_const _)
  have hQAint : ∀ j, Integrable (fun ω => (Q j ω - A j ω) ^ 2) P := by
    intro j
    refine Integrable.mono' (hboundint j) (hQAmeas j) ?_
    filter_upwards [hbnd j] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  have hQAle : ∀ j, ∫ ω, (Q j ω - A j ω) ^ 2 ∂P ≤ 2 * v j + 2 * b j ^ 2 := by
    intro j
    have h1 : ∫ ω, (Q j ω - A j ω) ^ 2 ∂P
        ≤ ∫ ω, (2 * (Q j ω - (P[Q j | 𝒟]) ω) ^ 2 + 2 * b j ^ 2) ∂P :=
      integral_mono_ae (hQAint j) (hboundint j) (hbnd j)
    have h2 : ∫ ω, (2 * (Q j ω - (P[Q j | 𝒟]) ω) ^ 2 + 2 * b j ^ 2) ∂P
        = 2 * ∫ ω, (Q j ω - (P[Q j | 𝒟]) ω) ^ 2 ∂P + 2 * b j ^ 2 := by
      rw [integral_add ((hdiff j).const_mul 2) (integrable_const _), integral_const_mul]
      simp
    rw [h2] at h1
    have h3 := hcen j
    linarith
  have hlim : Tendsto (fun j => 2 * v j + 2 * b j ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => 2 * v j) atTop (𝓝 0) := by simpa using hv.const_mul 2
    have h2 : Tendsto (fun j => 2 * b j ^ 2) atTop (𝓝 0) := by
      simpa using (hb.pow 2).const_mul 2
    simpa using h1.add h2
  exact tendstoInProb_zero_of_integral_sq_le hQAint hQAle hlim

end Asymptotic

/-! ### The two pieces §8 needs that §4 builds inline -/

section MeatMeasurable

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω)

/-- Entry `(o₁,o₂)` of `cRA_{jk}R` is `𝒟`-measurable. -/
theorem stronglyMeasurable_meatMat_apply {w : O → Ω → ℝ}
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o)) (R : Matrix O O ℝ) (c : ℝ) (o₁ o₂ : O) :
    StronglyMeasurable[𝒟] fun ω => meatMat c R w ω o₁ o₂ := by
  have hrw : (fun ω => meatMat c R w ω o₁ o₂)
      = fun ω => c * ∑ o : O, R o₁ o * w o ω * R o o₂ :=
    funext fun ω => meatMat_apply c R w ω o₁ o₂
  rw [hrw]
  have hsum : StronglyMeasurable[𝒟] fun ω => ∑ o : O, R o₁ o * w o ω * R o o₂ := by
    have hsplit : (fun ω => ∑ o : O, R o₁ o * w o ω * R o o₂)
        = ∑ o : O, fun ω => R o₁ o * w o ω * R o o₂ := by
      funext ω; simp only [Finset.sum_apply]
    rw [hsplit]
    exact Finset.stronglyMeasurable_sum _ fun o _ =>
      ((hw o).const_mul (R o₁ o)).mul_const (R o o₂)
  exact hsum.const_mul c

end MeatMeasurable

section QuadIntegrable

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [DecidableEq O] in
/-- `ε'Wε ∈ L²` for bounded, measurable entries of `W` and integrable four-fold products
of `ε`. -/
theorem memLp_two_quadForm {W : Ω → Matrix O O ℝ} {eps : O → Ω → ℝ} {Bw : ℝ} (hBw : 0 ≤ Bw)
    (hW : ∀ o o', AEStronglyMeasurable (fun ω => W ω o o') μ)
    (hWb : ∀ o o' ω, |W ω o o'| ≤ Bw)
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ) :
    MemLp (Quadform.quadForm W eps) 2 μ := by
  have hiW2 : ∀ p : O × O, Integrable (fun ω => W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω)) μ :=
    fun p => integrable_bdd_mul (hW p.1 p.2) (fun ω => hWb p.1 p.2 ω) (hi2 p)
  have hint : Integrable (Quadform.quadForm W eps) μ := by
    have hrw : Quadform.quadForm W eps
        = ∑ p : O × O, fun ω => W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω) := by
      funext ω
      rw [Quadform.quadForm_apply]
      simp only [Finset.sum_apply]
    rw [hrw]
    exact integrable_finsetSum' _ fun p _ => hiW2 p
  have hiW4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
        * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))) μ := by
    intro r
    have hprod : ∀ ω, |W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2| ≤ Bw * Bw := by
      intro ω
      rw [abs_mul]
      exact mul_le_mul (hWb _ _ ω) (hWb _ _ ω) (abs_nonneg _) hBw
    have h := integrable_bdd_mul (μ := μ) ((hW r.1.1 r.1.2).mul (hW r.2.1 r.2.2)) hprod (hi4 r)
    simpa [mul_assoc] using h
  have hsq : Integrable (fun ω => Quadform.quadForm W eps ω ^ 2) μ := by
    have hrw : (fun ω => Quadform.quadForm W eps ω ^ 2)
        = ∑ p : O × O, ∑ q : O × O, fun ω => W ω p.1 p.2 * W ω q.1 q.2
            * (eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω)) := by
      funext ω
      simp only [Finset.sum_apply]
      rw [Quadform.quadForm_apply, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hrw]
    exact integrable_finsetSum' _ fun p _ => integrable_finsetSum' _ fun q _ => hiW4 (p, q)
  exact (memLp_two_iff_integrable_sq hint.aestronglyMeasurable).2 hsq

end QuadIntegrable

/-! ### The limit over a sequence of designs -/

section MeatLimit

variable {O : ℕ → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Theorem 7(a), limit in probability.** `n^{-1}(𝓜̂_W)_{jk} - (S_n)_{jk} →ᵖ 0` entry by
entry, over a sequence of designs whose observation type `O j` varies with `j`. The hypotheses
are those of the bias and fluctuation bounds at each `j`, together with `hdK`
(`(d_[Δ]+K)/n → 0`), `hn` (`n → ∞`) and `hcard` (`n > 0`). -/
theorem tendstoInProb_meatW_sub [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    {R : ∀ j, Matrix (O j) (O j) ℝ}
    (hsym : ∀ j, (R j)ᵀ = R j) (hidem : ∀ j, R j * R j = R j)
    {eps sig w : ∀ j, O j → Ω → ℝ} {sbar B2 C : ℝ} {dK : ℕ → ℝ}
    (hC : 0 ≤ C) (hB0 : 0 ≤ B2)
    (hsig0 : ∀ j (o : O j) ω, 0 ≤ sig j o ω) (hsigB : ∀ j (o : O j) ω, sig j o ω ≤ sbar)
    (hB : ∀ j (o : O j) ω, |w j o ω| ≤ B2)
    (hw : ∀ j (o : O j), StronglyMeasurable[𝒟] (w j o))
    (htr : ∀ j, ∑ o : O j, (1 - R j o o) = dK j)
    (hcard : ∀ j, 0 < (Fintype.card (O j) : ℝ))
    (hi2 : ∀ j (p : O j × O j), Integrable (fun ω => eps j p.1 ω * eps j p.2 ω) P)
    (hi4 : ∀ j (r : (O j × O j) × (O j × O j)),
      Integrable (fun ω => eps j r.1.1 ω * eps j r.1.2 ω
        * (eps j r.2.1 ω * eps j r.2.2 ω)) P)
    (hcross : ∀ j (o' o'' : O j), P[fun ω => eps j o' ω * eps j o'' ω | 𝒟]
      =ᵐ[P] fun ω => if o' = o'' then sig j o' ω else 0)
    (hfour : ∀ j (o : O j),
      P[fun ω => eps j o ω * eps j o ω * (eps j o ω * eps j o ω) | 𝒟] ≤ᵐ[P] fun _ => C)
    (hpair : ∀ j (o o' : O j), o ≠ o' →
      P[fun ω => eps j o ω * eps j o ω * (eps j o' ω * eps j o' ω) | 𝒟]
        =ᵐ[P] fun ω => sig j o ω * sig j o' ω)
    (hmixed : ∀ j (a o o' : O j), o ≠ o' →
      P[fun ω => eps j a ω * eps j a ω * (eps j o ω * eps j o' ω) | 𝒟] =ᵐ[P] 0)
    (hquad : ∀ j (p q : O j × O j), p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      P[fun ω => eps j p.1 ω * eps j p.2 ω * (eps j q.1 ω * eps j q.2 ω) | 𝒟] =ᵐ[P] 0)
    (hdK : Tendsto (fun j => dK j / (Fintype.card (O j) : ℝ)) atTop (𝓝 0))
    (hn : Tendsto (fun j => ((Fintype.card (O j) : ℝ))⁻¹) atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun j ω => ((Fintype.card (O j) : ℝ))⁻¹
            * ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2
          - ((Fintype.card (O j) : ℝ))⁻¹ * ∑ o : O j, w j o ω * sig j o ω)
      atTop (fun _ => (0 : ℝ)) := by
  have hc0 : ∀ j, (0 : ℝ) ≤ ((Fintype.card (O j) : ℝ))⁻¹ :=
    fun j => le_of_lt (inv_pos.2 (hcard j))
  have hint : ∀ j (o' o'' : O j), Integrable (fun ω => eps j o' ω * eps j o'' ω) P :=
    fun j o' o'' => hi2 j (o', o'')
  have hvarj : ∀ j (o : O j), P[fun ω => eps j o ω * eps j o ω | 𝒟] =ᵐ[P] sig j o := by
    intro j o
    filter_upwards [hcross j o o] with ω hω
    simpa using hω
  have hcrossj : ∀ j (o o' : O j), o ≠ o' →
      P[fun ω => eps j o ω * eps j o' ω | 𝒟] =ᵐ[P] 0 := by
    intro j o o' h
    filter_upwards [hcross j o o'] with ω hω
    simpa [h] using hω
  have hintw : ∀ j (o : O j),
      Integrable (fun ω => w j o ω * feResidual (R j) (eps j) o ω ^ 2) P := fun j o =>
    integrable_bdd_mul (((hw j o).mono h𝒟).aestronglyMeasurable) (fun ω => hB j o ω)
      (integrable_feResidual_sq (μ := P) (R j) (hint j) o)
  -- the statistic is in `L²`
  have hQmem : ∀ j, MemLp (fun ω => ((Fintype.card (O j) : ℝ))⁻¹
      * ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2) 2 P := by
    intro j
    have hfun : (fun ω => ((Fintype.card (O j) : ℝ))⁻¹
          * ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2)
        = Quadform.quadForm (meatMat ((Fintype.card (O j) : ℝ))⁻¹ (R j) (w j)) (eps j) :=
      funext fun ω => (quadForm_meatMat (hsym j) _ (w j) (eps j) ω).symm
    rw [hfun]
    refine memLp_two_quadForm
      (Bw := |((Fintype.card (O j) : ℝ))⁻¹| * ((Fintype.card (O j) : ℝ) * B2))
      (mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hB0)) ?_
      (abs_meatMat_apply_le (hsym j) (hidem j) (hB j) _) (hi2 j) (hi4 j)
    intro o o'
    exact ((stronglyMeasurable_meatMat_apply 𝒟 (hw j) (R j) _ o o').mono h𝒟).aestronglyMeasurable
  -- the centering is measurable
  have hAmeas : ∀ j, AEStronglyMeasurable (fun ω => ((Fintype.card (O j) : ℝ))⁻¹
      * ∑ o : O j, w j o ω * sig j o ω) P := by
    intro j
    have hsm : StronglyMeasurable[𝒟] fun ω => ((Fintype.card (O j) : ℝ))⁻¹
        * ∑ o : O j, w j o ω * (P[fun ω => eps j o ω * eps j o ω | 𝒟]) ω := by
      refine StronglyMeasurable.const_mul ?_ _
      have hsplit : (fun ω => ∑ o : O j, w j o ω
            * (P[fun ω => eps j o ω * eps j o ω | 𝒟]) ω)
          = ∑ o : O j, fun ω => w j o ω * (P[fun ω => eps j o ω * eps j o ω | 𝒟]) ω := by
        funext ω; simp only [Finset.sum_apply]
      rw [hsplit]
      exact Finset.stronglyMeasurable_sum _ fun o _ =>
        (hw j o).mul stronglyMeasurable_condExp
    refine ((hsm.mono h𝒟).aestronglyMeasurable).congr ?_
    have hall : ∀ᵐ ω ∂P, ∀ o : O j,
        (P[fun ω => eps j o ω * eps j o ω | 𝒟]) ω = sig j o ω :=
      ae_all_iff.2 fun o => hvarj j o
    filter_upwards [hall] with ω hω
    have hsum : ∑ o : O j, w j o ω * (P[fun ω => eps j o ω * eps j o ω | 𝒟]) ω
        = ∑ o : O j, w j o ω * sig j o ω :=
      Finset.sum_congr rfl fun o _ => by rw [hω o]
    rw [hsum]
  -- the bias bound, normalized
  have hbias : ∀ j, ∀ᵐ ω ∂P, |(P[fun ω => ((Fintype.card (O j) : ℝ))⁻¹
        * ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2 | 𝒟]) ω
        - ((Fintype.card (O j) : ℝ))⁻¹ * ∑ o : O j, w j o ω * sig j o ω|
      ≤ 3 * sbar * B2 * dK j * ((Fintype.card (O j) : ℝ))⁻¹ := by
    intro j
    have hfs := abs_condExp_meatW_sub_le 𝒟 (hsym j) (hidem j) (hsig0 j) (hsigB j) (hB j)
      (htr j) (hw j) (hint j) (hintw j) (hcross j)
    have hsm : P[fun ω => ((Fintype.card (O j) : ℝ))⁻¹
          * ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2 | 𝒟]
        =ᵐ[P] fun ω => ((Fintype.card (O j) : ℝ))⁻¹
          * (P[fun ω => ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2 | 𝒟]) ω := by
      have h := condExp_smul (μ := P) ((Fintype.card (O j) : ℝ))⁻¹
        (fun ω => ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2) 𝒟
      have hfe : ((Fintype.card (O j) : ℝ))⁻¹
            • (fun ω => ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2)
          = fun ω => ((Fintype.card (O j) : ℝ))⁻¹
            * ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2 := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul]
      rw [hfe] at h
      filter_upwards [h] with ω hω
      simpa only [Pi.smul_apply, smul_eq_mul] using hω
    filter_upwards [hfs, hsm] with ω h1 h2
    rw [h2]
    set Mv : ℝ := (P[fun ω => ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2 | 𝒟]) ω
      with hMv
    set Sv : ℝ := ∑ o : O j, w j o ω * sig j o ω with hSv
    have habs : |((Fintype.card (O j) : ℝ))⁻¹ * Mv - ((Fintype.card (O j) : ℝ))⁻¹ * Sv|
        = ((Fintype.card (O j) : ℝ))⁻¹ * |Mv - Sv| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (hc0 j)]
    rw [habs]
    calc ((Fintype.card (O j) : ℝ))⁻¹ * |Mv - Sv|
        ≤ ((Fintype.card (O j) : ℝ))⁻¹ * (3 * sbar * B2 * dK j) :=
          mul_le_mul_of_nonneg_left h1 (hc0 j)
      _ = 3 * sbar * B2 * dK j * ((Fintype.card (O j) : ℝ))⁻¹ := by ring
  -- the fluctuation bound at `c = n⁻¹`
  have hvarb : ∀ j, (fun ω => (P[fun ω => (((Fintype.card (O j) : ℝ))⁻¹
          * ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2) ^ 2 | 𝒟]) ω
        - (P[fun ω => ((Fintype.card (O j) : ℝ))⁻¹
          * ∑ o : O j, w j o ω * feResidual (R j) (eps j) o ω ^ 2 | 𝒟]) ω ^ 2)
      ≤ᵐ[P] fun _ => 3 * C * ((((Fintype.card (O j) : ℝ))⁻¹) ^ 2
        * (B2 ^ 2 * (Fintype.card (O j) : ℝ))) := fun j =>
    condExp_meatW_var_le 𝒟 h𝒟 (hsym j) (hidem j) hC hB0 (hB j) (hw j) (hi2 j) (hi4 j)
      (hvarj j) (hcrossj j) (hfour j) (hpair j) (hmixed j) (hquad j)
  have hbt : Tendsto (fun j => 3 * sbar * B2 * dK j * ((Fintype.card (O j) : ℝ))⁻¹)
      atTop (𝓝 0) := by
    have heq : ∀ j, 3 * sbar * B2 * dK j * ((Fintype.card (O j) : ℝ))⁻¹
        = 3 * sbar * B2 * (dK j / (Fintype.card (O j) : ℝ)) := by
      intro j; rw [div_eq_mul_inv]; ring
    simp only [heq]
    simpa using hdK.const_mul (3 * sbar * B2)
  have hvt : Tendsto (fun j => 3 * C * ((((Fintype.card (O j) : ℝ))⁻¹) ^ 2
      * (B2 ^ 2 * (Fintype.card (O j) : ℝ)))) atTop (𝓝 0) := by
    have heq : ∀ j, 3 * C * ((((Fintype.card (O j) : ℝ))⁻¹) ^ 2
        * (B2 ^ 2 * (Fintype.card (O j) : ℝ)))
        = 3 * C * B2 ^ 2 * ((Fintype.card (O j) : ℝ))⁻¹ := by
      intro j
      have hne : ((Fintype.card (O j) : ℝ)) ≠ 0 := (hcard j).ne'
      field_simp
    simp only [heq]
    simpa using hn.const_mul (3 * C * B2 ^ 2)
  exact tendstoInProb_of_bias_condVar 𝒟 h𝒟 hQmem hAmeas hbias hvarb hbt hvt

end MeatLimit

/-! ### Non-vacuity of the limit in probability -/

section AsymptoticWitness

/-- `tendstoInProb_meatW_sub` on a growing family of one-point models: `𝒪_j = {0,…,j}`,
`Ω = Unit`, `P = dirac ()`, `𝒟 = ⊥`, `R = I`, `ε_o = 𝟙{o = 0}`, `σ²_ε(o) = 𝟙{o = 0}`,
`σ̄² = 1`, `w ≡ 1`, `B² = 1`, `C = 1`. -/
theorem tendstoInProb_meatW_sub_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (j : ℕ) (u : Unit) =>
        ((Fintype.card (Fin (j + 1)) : ℝ))⁻¹
            * ∑ o : Fin (j + 1), (1 : ℝ)
              * feResidual (1 : Matrix (Fin (j + 1)) (Fin (j + 1)) ℝ)
                  (Quadform.witnessEps (0 : Fin (j + 1))) o u ^ 2
          - ((Fintype.card (Fin (j + 1)) : ℝ))⁻¹
            * ∑ o : Fin (j + 1), (1 : ℝ) * (if o = (0 : Fin (j + 1)) then (1 : ℝ) else 0))
      atTop (fun _ => (0 : ℝ)) := by
  have hcardR : ∀ j : ℕ, (Fintype.card (Fin (j + 1)) : ℝ) = (j : ℝ) + 1 := by
    intro j
    rw [Fintype.card_fin]
    push_cast
    ring
  have hpos : ∀ j : ℕ, 0 < (Fintype.card (Fin (j + 1)) : ℝ) := by
    intro j
    rw [hcardR j]
    positivity
  have hgrow : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    refine Filter.tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hinv : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) := hgrow.inv_tendsto_atTop
  refine tendstoInProb_meatW_sub (O := fun j => Fin (j + 1)) (⊥ : MeasurableSpace Unit) bot_le
    (R := fun _ => 1) (fun _ => Matrix.transpose_one) (fun _ => Matrix.one_mul _)
    (eps := fun j => Quadform.witnessEps (0 : Fin (j + 1)))
    (sig := fun _ o _ => if o = 0 then (1 : ℝ) else 0) (w := fun _ _ _ => (1 : ℝ))
    (sbar := 1) (B2 := 1) (C := 1) (dK := fun _ => 0) zero_le_one zero_le_one
    (fun _ o _ => by by_cases h : o = 0 <;> simp [h])
    (fun _ o _ => by by_cases h : o = 0 <;> simp [h])
    (fun _ _ _ => by norm_num) (fun _ _ => stronglyMeasurable_const) ?_ hpos
    (fun _ _ => Quadform.integrable_unit _) (fun _ _ => Quadform.integrable_unit _)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    simp
  · intro j o' o''
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    by_cases h : o' = o''
    · subst h
      show Quadform.witnessEps (0 : Fin (j + 1)) o' u
          * Quadform.witnessEps (0 : Fin (j + 1)) o' u = _
      rw [Quadform.witnessEps_mul_self (0 : Fin (j + 1)) o' u]
      simp
    · show Quadform.witnessEps (0 : Fin (j + 1)) o' u
          * Quadform.witnessEps (0 : Fin (j + 1)) o'' u = _
      rw [Quadform.witnessEps_mul_eq_zero (0 : Fin (j + 1)) h u]
      simp [h]
  · intro j o
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps (0 : Fin (j + 1)) o u * Quadform.witnessEps (0 : Fin (j + 1)) o u
        * (Quadform.witnessEps (0 : Fin (j + 1)) o u
          * Quadform.witnessEps (0 : Fin (j + 1)) o u) ≤ (1 : ℝ)
    rw [Quadform.witnessEps_mul_self (0 : Fin (j + 1)) o u]
    by_cases h : o = 0 <;> simp [h]
  · intro j o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps (0 : Fin (j + 1)) o u * Quadform.witnessEps (0 : Fin (j + 1)) o u
        * (Quadform.witnessEps (0 : Fin (j + 1)) o' u
          * Quadform.witnessEps (0 : Fin (j + 1)) o' u)
        = (if o = 0 then (1 : ℝ) else 0) * (if o' = 0 then (1 : ℝ) else 0)
    rw [Quadform.witnessEps_mul_self (0 : Fin (j + 1)) o u,
      Quadform.witnessEps_mul_self (0 : Fin (j + 1)) o' u]
  · intro j a o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps (0 : Fin (j + 1)) a u * Quadform.witnessEps (0 : Fin (j + 1)) a u
        * (Quadform.witnessEps (0 : Fin (j + 1)) o u
          * Quadform.witnessEps (0 : Fin (j + 1)) o' u) = (0 : ℝ)
    rw [Quadform.witnessEps_mul_eq_zero (0 : Fin (j + 1)) h u, mul_zero]
  · intro j p q hp _ _ _
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps (0 : Fin (j + 1)) p.1 u * Quadform.witnessEps (0 : Fin (j + 1)) p.2 u
        * (Quadform.witnessEps (0 : Fin (j + 1)) q.1 u
          * Quadform.witnessEps (0 : Fin (j + 1)) q.2 u) = (0 : ℝ)
    rw [Quadform.witnessEps_mul_eq_zero (0 : Fin (j + 1)) hp u, zero_mul]
  · simp
  · refine hinv.congr fun j => ?_
    rw [hcardR j]

end AsymptoticWitness

/-! ## Theorem 7(a): `nV̂_W ⟶ᵖ H^{-1}SH^{-1}`

With `V̂_W := (X̃'X̃)^{-1}𝓜̂_W(X̃'X̃)^{-1}`, the limit follows by continuous mapping through
`(n^{-1}X̃'X̃)^{-1}`, from `n^{-1}X̃'X̃ →ᵖ H ≻ 0`, `n^{-1}𝓜̂_W - S_n →ᵖ 0` and `S_n →ᵖ S`. The
matrix `X̃'X̃` is never assumed invertible (`Matrix.inv` is total), and the sample size is a
positive sequence `N`. Continuity of inversion is used on `Matrix K K ℝ` with the `ℓ²` operator
norm, scoped to one section; statements are in `frobNorm`.
-/

section ContinuousMapping

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Convergence in probability to a constant -/

/-- `u_n ⟶ᵖ a` if and only if `d(u_n, a) ⟶ᵖ 0`. -/
theorem tendstoInProb_const_iff_dist {E : Type*} [PseudoMetricSpace E]
    {u : ℕ → Ω → E} {a : E} :
    TendstoInMeasure P u atTop (fun _ => a)
      ↔ TendstoInMeasure P (fun n ω => dist (u n ω) a) atTop (fun _ => (0 : ℝ)) := by
  have hset : ∀ (n : ℕ) (ε : ℝ),
      {ω | ε ≤ dist (dist (u n ω) a) (0 : ℝ)} = {ω | ε ≤ dist (u n ω) a} := by
    intro n ε
    ext ω
    simp [abs_of_nonneg dist_nonneg]
  rw [tendstoInMeasure_iff_dist, tendstoInMeasure_iff_dist]
  constructor <;> intro h ε hε
  · simpa only [hset] using h ε hε
  · simpa only [hset] using h ε hε

/-- Continuous mapping in probability, two arguments, constant limits. -/
theorem tendstoInProb_comp₂ {E F Z : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [PseudoMetricSpace Z] {u : ℕ → Ω → E} {v : ℕ → Ω → F} {a : E} {b : F} {g : E → F → Z}
    (hg : ContinuousAt (fun p : E × F => g p.1 p.2) (a, b))
    (hu : TendstoInMeasure P u atTop (fun _ => a))
    (hv : TendstoInMeasure P v atTop (fun _ => b)) :
    TendstoInMeasure P (fun n ω => g (u n ω) (v n ω)) atTop (fun _ => g a b) := by
  rw [tendstoInMeasure_iff_dist] at hu hv ⊢
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.1 hg ε hε
  have hmono : ∀ n : ℕ, P {ω | ε ≤ dist (g (u n ω) (v n ω)) (g a b)}
      ≤ P {ω | δ ≤ dist (u n ω) a} + P {ω | δ ≤ dist (v n ω) b} := by
    intro n
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    replace hω : ε ≤ dist (g (u n ω) (v n ω)) (g a b) := hω
    by_cases h1 : δ ≤ dist (u n ω) a
    · exact Or.inl h1
    by_cases h2 : δ ≤ dist (v n ω) b
    · exact Or.inr h2
    replace h1 : dist (u n ω) a < δ := not_le.1 h1
    replace h2 : dist (v n ω) b < δ := not_le.1 h2
    exfalso
    have hd : dist ((u n ω, v n ω)) (a, b) < δ := by
      rw [Prod.dist_eq]
      exact max_lt h1 h2
    exact absurd (hδ hd) (not_lt.2 hω)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n => zero_le) hmono
  simpa using (hu δ hδpos).add (hv δ hδpos)

/-- A nonnegative sequence dominated by a fixed multiple of a null sequence is null. -/
theorem tendstoInProb_zero_of_le_const_mul {u v : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 < c)
    (hu0 : ∀ n ω, 0 ≤ u n ω) (hle : ∀ n ω, u n ω ≤ c * v n ω)
    (hv : TendstoInMeasure P v atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P u atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hv ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hv (ε / c) (by positivity)) (fun n => zero_le) (fun n => measure_mono fun ω hω => ?_)
  replace hω : ε ≤ dist (u n ω) (0 : ℝ) := hω
  show ε / c ≤ dist (v n ω) (0 : ℝ)
  rw [Real.dist_eq, sub_zero] at hω ⊢
  rw [abs_of_nonneg (hu0 n ω)] at hω
  have h1 : ε ≤ c * v n ω := le_trans hω (hle n ω)
  have h2 : ε / c ≤ v n ω := (div_le_iff₀ hc).2 (by linarith)
  exact le_trans h2 (le_abs_self _)

/-- Convergence in probability is preserved under eventual equality. -/
theorem tendstoInProb_congr_eventually {E : Type*} [PseudoMetricSpace E]
    {u v : ℕ → Ω → E} {a : E} (h : ∀ᶠ n in atTop, u n = v n)
    (hu : TendstoInMeasure P u atTop (fun _ => a)) :
    TendstoInMeasure P v atTop (fun _ => a) := by
  rw [tendstoInMeasure_iff_dist] at hu ⊢
  intro ε hε
  refine (hu ε hε).congr' ?_
  filter_upwards [h] with n hn
  rw [hn]

theorem tendstoInProb_zero_add {v w : ℕ → Ω → ℝ}
    (hv : TendstoInMeasure P v atTop (fun _ => (0 : ℝ)))
    (hw : TendstoInMeasure P w atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => v n ω + w n ω) atTop (fun _ => (0 : ℝ)) := by
  have h := tendstoInProb_comp₂ (g := fun x y : ℝ => x + y) continuous_add.continuousAt hv hw
  simpa using h

theorem tendstoInProb_zero_of_le_add {u v w : ℕ → Ω → ℝ} (hu0 : ∀ n ω, 0 ≤ u n ω)
    (hle : ∀ n ω, u n ω ≤ v n ω + w n ω)
    (hv : TendstoInMeasure P v atTop (fun _ => (0 : ℝ)))
    (hw : TendstoInMeasure P w atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P u atTop (fun _ => (0 : ℝ)) :=
  tendstoInProb_zero_of_le_const_mul one_pos hu0
    (fun n ω => by rw [one_mul]; exact hle n ω) (tendstoInProb_zero_add hv hw)

theorem tendstoInProb_zero_const :
    TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hset : {ω : Ω | ε ≤ dist (0 : ℝ) 0} = (∅ : Set Ω) := by
    ext ω
    constructor
    · intro hc
      rw [dist_self] at hc
      exact absurd hc (not_le.2 hε)
    · exact fun hc => hc.elim
  simp only [hset, measure_empty]
  exact tendsto_const_nhds

/-- `u_n ⟶ᵖ 0` implies `|u_n| ⟶ᵖ 0`. -/
theorem tendstoInProb_abs {u : ℕ → Ω → ℝ}
    (hu : TendstoInMeasure P u atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => |u n ω|) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hu ⊢
  intro ε hε
  refine (hu ε hε).congr fun n => ?_
  congr 1
  ext ω
  simp

theorem tendstoInProb_zero_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℕ → Ω → ℝ}
    (h : ∀ i ∈ s, TendstoInMeasure P (f i) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ s, f i n ω) atTop (fun _ => (0 : ℝ)) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using tendstoInProb_zero_const (P := P)
  | insert a s ha ih =>
      have h1 : TendstoInMeasure P (f a) atTop (fun _ => (0 : ℝ)) :=
        h a (Finset.mem_insert_self a s)
      have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      have heq : (fun (n : ℕ) (ω : Ω) => ∑ i ∈ insert a s, f i n ω)
          = fun (n : ℕ) (ω : Ω) => f a n ω + ∑ i ∈ s, f i n ω := by
        funext n ω
        rw [Finset.sum_insert ha]
      rw [heq]
      exact tendstoInProb_zero_add h1 h2

/-- A deterministic limit is a limit in probability. -/
theorem tendstoInProb_of_tendsto [IsFiniteMeasure P] {a : ℕ → ℝ} {c : ℝ}
    (h : Tendsto a atTop (𝓝 c)) :
    TendstoInMeasure P (fun n (_ : Ω) => a n) atTop (fun _ => c) :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (Filter.Eventually.of_forall fun _ => h)

/-! ### From entrywise limits to the matrix limit

`‖A‖_F ≤ ∑_{a,b}|A_{ab}|` and a union bound. -/

section Entries

variable {K : Type*} [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
theorem frobNorm_le_sum_abs (A : Matrix K K ℝ) : frobNorm A ≤ ∑ a : K, ∑ b : K, |A a b| := by
  have hnn : (0 : ℝ) ≤ ∑ a : K, ∑ b : K, |A a b| :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _
  have hsq : frobSq A ≤ (∑ a : K, ∑ b : K, |A a b|) ^ 2 := by
    have h1 : frobSq A = ∑ p : K × K, |A p.1 p.2| ^ 2 := by
      rw [frobSq, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (sq_abs _).symm
    have h2 : (∑ a : K, ∑ b : K, |A a b|) = ∑ p : K × K, |A p.1 p.2| :=
      (Fintype.sum_prod_type (fun p : K × K => |A p.1 p.2|)).symm
    rw [h1, h2]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun p _ => abs_nonneg _
  have h := Real.sqrt_le_sqrt hsq
  rwa [show Real.sqrt (frobSq A) = frobNorm A from rfl, Real.sqrt_sq hnn] at h

omit [DecidableEq K] in
/-- Entrywise convergence in probability implies convergence in `‖·‖_F`. -/
theorem tendstoInProb_frobNorm_of_entries {M N : ℕ → Ω → Matrix K K ℝ}
    (h : ∀ a b : K, TendstoInMeasure P (fun n ω => M n ω a b - N n ω a b)
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => frobNorm (M n ω - N n ω)) atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_le_const_mul
    (v := fun n ω => ∑ a : K, ∑ b : K, |M n ω a b - N n ω a b|) one_pos
    (fun n ω => frobNorm_nonneg _) (fun n ω => ?_) ?_
  · rw [one_mul]
    refine le_trans (frobNorm_le_sum_abs _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [Matrix.sub_apply]
  · exact tendstoInProb_zero_finsetSum _ fun a _ =>
      tendstoInProb_zero_finsetSum _ fun b _ => tendstoInProb_abs (h a b)

end Entries

/-! ### Frobenius and `ℓ²` operator norms, and continuity of inversion

`Matrix.Norms.L2Operator` makes `Matrix K K ℝ` a complete normed ring, so
`NormedRing.inverse_continuousAt` applies; `‖A‖ ≤ ‖A‖_F ≤ √K‖A‖` converts to and from
`frobNorm`. -/

section MatrixNorms

open scoped Matrix.Norms.L2Operator

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `‖A‖ ≤ ‖A‖_F`. -/
theorem l2_opNorm_le_frobNorm (A : Matrix K K ℝ) : ‖A‖ ≤ frobNorm A := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (frobNorm_nonneg A) fun x => ?_
  have hx : ‖x‖ ^ 2 = ∑ j : K, (x.ofLp j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  have hy : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ^ 2
      = ∑ i : K, (∑ j : K, A i j * x.ofLp j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) x).ofLp i = ∑ j : K, A i j * x.ofLp j from rfl,
      Real.norm_eq_abs, sq_abs]
  have hsum : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ^ 2 ≤ (frobNorm A * ‖x‖) ^ 2 := by
    rw [hy, mul_pow, sq_frobNorm, hx, frobSq, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x.ofLp j)
  have hnn : 0 ≤ frobNorm A * ‖x‖ := mul_nonneg (frobNorm_nonneg A) (norm_nonneg x)
  have h := Real.sqrt_le_sqrt hsum
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at h

/-- `‖A‖_F ≤ √(card K)‖A‖`: the columns are the images of the standard basis. -/
theorem frobNorm_le_sqrt_card_mul_l2_opNorm (A : Matrix K K ℝ) :
    frobNorm A ≤ Real.sqrt (Fintype.card K) * ‖A‖ := by
  have hcol : ∀ j : K, ∑ i : K, (A i j) ^ 2 ≤ ‖A‖ ^ 2 := by
    intro j
    have hb := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℝ))
    rw [show ((EuclideanSpace.single j (1 : ℝ)) : EuclideanSpace ℝ K).ofLp = Pi.single j (1 : ℝ)
      from rfl] at hb
    have hmv : A.mulVec (Pi.single j (1 : ℝ)) = fun i => A i j := by
      funext i; simp [Matrix.mulVec_single]
    rw [hmv] at hb
    have hone : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
    rw [hone, mul_one] at hb
    have hnorm : ‖(EuclideanSpace.equiv K ℝ).symm (fun i => A i j)‖ ^ 2
        = ∑ i : K, (A i j) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]; rfl
    calc ∑ i : K, (A i j) ^ 2 = ‖(EuclideanSpace.equiv K ℝ).symm (fun i => A i j)‖ ^ 2 :=
          hnorm.symm
      _ ≤ ‖A‖ ^ 2 := by
          nlinarith [norm_nonneg ((EuclideanSpace.equiv K ℝ).symm (fun i => A i j)),
            norm_nonneg A]
  have hfs : frobSq A ≤ (Fintype.card K : ℝ) * ‖A‖ ^ 2 := by
    rw [frobSq, Finset.sum_comm]
    calc ∑ j : K, ∑ i : K, (A i j) ^ 2 ≤ ∑ _j : K, ‖A‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = (Fintype.card K : ℝ) * ‖A‖ ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnn : 0 ≤ Real.sqrt (Fintype.card K) * ‖A‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg A)
  have hsq : frobNorm A ^ 2 ≤ (Real.sqrt (Fintype.card K) * ‖A‖) ^ 2 := by
    rw [sq_frobNorm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hfs
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (frobNorm_nonneg A), Real.sqrt_sq hnn] at h

/-- `(G,M) ↦ G^{-1}MG^{-1}` is continuous at an invertible `G`. -/
theorem continuousAt_conj_inverse {H : Matrix K K ℝ} (hH : IsUnit H) (S : Matrix K K ℝ) :
    ContinuousAt (fun p : Matrix K K ℝ × Matrix K K ℝ =>
      Ring.inverse p.1 * p.2 * Ring.inverse p.1) (H, S) := by
  obtain ⟨u, rfl⟩ := hH
  have h1 : ContinuousAt (fun p : Matrix K K ℝ × Matrix K K ℝ => Ring.inverse p.1)
      (((u : Matrix K K ℝ)), S) := by
    have h := ContinuousAt.comp (x := ((u : Matrix K K ℝ), S))
      (NormedRing.inverse_continuousAt u) continuousAt_fst
    simpa [Function.comp_def] using h
  exact (h1.mul continuousAt_snd).mul h1

/-- `G_n ⟶ᵖ H` invertible and `M_n ⟶ᵖ S` give `G_n^{-1}M_nG_n^{-1} ⟶ᵖ H^{-1}SH^{-1}` in
`‖·‖_F`. `G_n` need not be invertible. -/
theorem tendstoInProb_conj_inverse {G M : ℕ → Ω → Matrix K K ℝ} {H S : Matrix K K ℝ}
    (hH : IsUnit H)
    (hG : TendstoInMeasure P (fun n ω => frobNorm (G n ω - H)) atTop (fun _ => (0 : ℝ)))
    (hM : TendstoInMeasure P (fun n ω => frobNorm (M n ω - S)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P
      (fun n ω => frobNorm ((G n ω)⁻¹ * M n ω * (G n ω)⁻¹ - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  have hGn : TendstoInMeasure P G atTop (fun _ => H) := by
    rw [tendstoInProb_const_iff_dist]
    refine tendstoInProb_zero_of_le_const_mul one_pos (fun n ω => dist_nonneg)
      (fun n ω => ?_) hG
    rw [one_mul, dist_eq_norm]
    exact l2_opNorm_le_frobNorm _
  have hMn : TendstoInMeasure P M atTop (fun _ => S) := by
    rw [tendstoInProb_const_iff_dist]
    refine tendstoInProb_zero_of_le_const_mul one_pos (fun n ω => dist_nonneg)
      (fun n ω => ?_) hM
    rw [one_mul, dist_eq_norm]
    exact l2_opNorm_le_frobNorm _
  have hcomp := tendstoInProb_comp₂ (g := fun x y : Matrix K K ℝ =>
    Ring.inverse x * y * Ring.inverse x) (continuousAt_conj_inverse hH S) hGn hMn
  rw [tendstoInProb_const_iff_dist] at hcomp
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  refine tendstoInProb_zero_of_le_const_mul (c := Real.sqrt (Fintype.card K) + 1)
    (by positivity) (fun n ω => frobNorm_nonneg _) (fun n ω => ?_) hcomp
  rw [dist_eq_norm]
  have h1 := frobNorm_le_sqrt_card_mul_l2_opNorm
    (Ring.inverse (G n ω) * M n ω * Ring.inverse (G n ω)
      - Ring.inverse H * S * Ring.inverse H)
  nlinarith [norm_nonneg (Ring.inverse (G n ω) * M n ω * Ring.inverse (G n ω)
    - Ring.inverse H * S * Ring.inverse H)]

end MatrixNorms

/-! ### The normalization

`nV̂_W = (n^{-1}X̃'X̃)^{-1}(n^{-1}𝓜̂_W)(n^{-1}X̃'X̃)^{-1}` for `n ≠ 0`. -/

section Normalization

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `(cA)^{-1} = c^{-1}A^{-1}` for `c ≠ 0`, with no invertibility hypothesis on `A`. -/
theorem inv_smul_of_ne_zero {c : ℝ} (hc : c ≠ 0) (A : Matrix K K ℝ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, Matrix.nonsing_inv_mul A h]
  · have hdet0 : A.det = 0 := by rwa [isUnit_iff_ne_zero, not_not] at h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, smul_zero,
      Matrix.nonsing_inv_apply_not_isUnit]
    rw [Matrix.det_smul, hdet0, mul_zero, isUnit_iff_ne_zero]
    simp

theorem conj_inv_smul {c : ℝ} (hc : c ≠ 0) (Gr Mh : Matrix K K ℝ) :
    (c • Gr)⁻¹ * (c • Mh) * (c • Gr)⁻¹ = c⁻¹ • (Gr⁻¹ * Mh * Gr⁻¹) := by
  rw [inv_smul_of_ne_zero hc, smul_mul_smul_comm, smul_mul_smul_comm,
    show c⁻¹ * c * c⁻¹ = c⁻¹ by field_simp]

end Normalization

/-! ### `nV̂_W ⟶ᵖ H^{-1}SH^{-1}` -/

section NVhat

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Theorem 7(a).** `N_n(X̃'X̃)^{-1}𝓜̂_W(X̃'X̃)^{-1} →ᵖ H^{-1}SH^{-1}`. Here `Gr` is `X̃'X̃`,
`Mh` is `𝓜̂_W` and `Sn` is `S_n`, all unnormalized; `hH`, `hG` give `N_n^{-1}X̃'X̃ →ᵖ H ≻ 0`,
`hM` gives `N_n^{-1}𝓜̂_W - S_n →ᵖ 0`, and `hS` gives `S_n →ᵖ S`. -/
theorem tendstoInProb_nVhat {Gr Mh Sn : ℕ → Ω → Matrix K K ℝ} {H S : Matrix K K ℝ}
    {N : ℕ → ℝ} (hN : ∀ n, 0 < N n) (hH : H.PosDef)
    (hG : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Gr n ω - H))
      atTop (fun _ => (0 : ℝ)))
    (hM : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Mh n ω - Sn n ω))
      atTop (fun _ => (0 : ℝ)))
    (hS : TendstoInMeasure P (fun n ω => frobNorm (Sn n ω - S)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P
      (fun n ω => frobNorm (N n • ((Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹) - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  have hHu : IsUnit H :=
    H.isUnit_iff_isUnit_det.2 (isUnit_iff_ne_zero.2 hH.det_pos.ne')
  have hMS : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Mh n ω - S))
      atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInProb_zero_of_le_add (fun n ω => frobNorm_nonneg _) (fun n ω => ?_) hM hS
    have hsplit : (N n)⁻¹ • Mh n ω - S
        = ((N n)⁻¹ • Mh n ω - Sn n ω) + (Sn n ω - S) := by abel
    rw [hsplit]
    exact frobNorm_add_le _ _
  have hconj := tendstoInProb_conj_inverse (G := fun n ω => (N n)⁻¹ • Gr n ω)
    (M := fun n ω => (N n)⁻¹ • Mh n ω) hHu hG hMS
  refine tendstoInProb_congr_eventually (Filter.Eventually.of_forall fun n => ?_) hconj
  funext ω
  rw [conj_inv_smul (inv_ne_zero (hN n).ne'), inv_inv]

end NVhat

/-! ### Non-vacuity

With `K = 1` over a one-point space: `N_j = j+1`, `X̃'X̃ = [j+1]`, `H = [1]`,
`S_n = [1 + (j+1)^{-1}]`, `𝓜̂_W = [(j+1)(1 + (j+1)^{-1})]`, `S = [1]`. Both `‖S_n - S‖_F` and
`‖nV̂_W - H^{-1}SH^{-1}‖_F` equal `(j+1)^{-1} > 0`. -/

section NVhatWitness

theorem frobNorm_scalar (r : ℝ) :
    frobNorm ((Matrix.of fun _ _ => r : Matrix (Fin 1) (Fin 1) ℝ)) = |r| := by
  simp [frobNorm, frobSq, Real.sqrt_sq_eq_abs]

theorem tendstoInProb_nVhat_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (n : ℕ) (_ : Unit) => frobNorm (((n : ℝ) + 1) •
          (((Matrix.of fun _ _ => (n : ℝ) + 1) : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
              * ((Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹))
                  : Matrix (Fin 1) (Fin 1) ℝ)
              * ((Matrix.of fun _ _ => (n : ℝ) + 1) : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)
            - (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_nVhat (P := Measure.dirac ()) (H := 1) (S := 1)
    (N := fun n : ℕ => (n : ℝ) + 1)
    (Sn := fun (n : ℕ) (_ : Unit) => (Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹))
    (fun n => by positivity) Matrix.PosDef.one ?_ ?_ ?_
  · refine tendstoInProb_of_tendsto ?_
    have hval : ∀ n : ℕ, frobNorm ((((n : ℝ) + 1)⁻¹ • (Matrix.of fun _ _ => (n : ℝ) + 1) - 1 :
        Matrix (Fin 1) (Fin 1) ℝ)) = 0 := by
      intro n
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      have heq : ((((n : ℝ) + 1)⁻¹ • (Matrix.of fun _ _ => (n : ℝ) + 1) - 1 :
          Matrix (Fin 1) (Fin 1) ℝ)) = Matrix.of fun _ _ => (0 : ℝ) := by
        ext i j
        fin_cases i; fin_cases j; simp [inv_mul_cancel₀ hne]
      rw [heq, frobNorm_scalar]
      simp
    simp only [hval]
    exact tendsto_const_nhds
  · refine tendstoInProb_of_tendsto ?_
    have hval : ∀ n : ℕ, frobNorm ((((n : ℝ) + 1)⁻¹
        • (Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹))
        - (Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) : Matrix (Fin 1) (Fin 1) ℝ)) = 0 := by
      intro n
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      have heq : ((((n : ℝ) + 1)⁻¹
          • (Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹))
          - (Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) : Matrix (Fin 1) (Fin 1) ℝ))
          = Matrix.of fun _ _ => (0 : ℝ) := by
        ext i j
        fin_cases i; fin_cases j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
          inv_mul_cancel_left₀ hne, sub_self]
      rw [heq, frobNorm_scalar]
      simp
    simp only [hval]
    exact tendsto_const_nhds
  · refine tendstoInProb_of_tendsto ?_
    have hval : ∀ n : ℕ, frobNorm (((Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) - 1 :
        Matrix (Fin 1) (Fin 1) ℝ)) = ((n : ℝ) + 1)⁻¹ := by
      intro n
      have heq : (((Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) - 1 :
          Matrix (Fin 1) (Fin 1) ℝ)) = Matrix.of fun _ _ => ((n : ℝ) + 1)⁻¹ := by
        ext i j
        fin_cases i; fin_cases j; simp
      rw [heq, frobNorm_scalar, abs_of_nonneg (by positivity)]
    simp only [hval]
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => ?_
    rw [one_div]

end NVhatWitness

end ContinuousMapping

/-! ## Theorem 7(b) with the variance limit derived

The restricted limit `𝓡(nV̂_W)𝓡' ⟶ᵖ 𝓡H^{-1}SH^{-1}𝓡'` follows from `nV̂_W ⟶ᵖ H^{-1}SH^{-1}`
and the inequality `‖𝓡B𝓡'‖_F ≤ ‖𝓡‖²_F‖B‖_F` for a rectangular `𝓡`. This gives
`vhat_wald_of_nVhat`.
-/

section RestrictedLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Congruence by a rectangular matrix

The factor `𝓡` is measured by `rectFrobSq`, which agrees definitionally with `frobNorm` squared
on square matrices. -/

section RectCongruence

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Submultiplicativity of the rectangular Frobenius norm, squared. -/
theorem rectFrobSq_mul_le_mul (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    rectFrobSq (A * B) ≤ rectFrobSq A * rectFrobSq B := by
  have hstep : ∀ (i : α) (k : γ), ((A * B) i k) ^ 2
      ≤ (∑ j : β, A i j ^ 2) * (∑ j : β, B j k ^ 2) := by
    intro i k
    have h : (A * B) i k = ∑ j : β, A i j * B j k := by
      simp only [Matrix.mul_apply]
    rw [h]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hsum : rectFrobSq (A * B)
      ≤ ∑ i : α, ∑ k : γ, (∑ j : β, A i j ^ 2) * (∑ j : β, B j k ^ 2) := by
    rw [rectFrobSq]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hstep i k
  have hfact : ∑ i : α, ∑ k : γ, (∑ j : β, A i j ^ 2) * (∑ j : β, B j k ^ 2)
      = (∑ i : α, ∑ j : β, A i j ^ 2) * (∑ k : γ, ∑ j : β, B j k ^ 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hB : ∑ k : γ, ∑ j : β, B j k ^ 2 = rectFrobSq B := by
    rw [rectFrobSq]
    exact Finset.sum_comm
  rw [hfact, hB] at hsum
  exact hsum

end RectCongruence

section RectConj

variable {ι K : Type*} [Fintype ι] [Fintype K]

/-- `‖𝓡B𝓡'‖_F ≤ ‖𝓡‖²_F‖B‖_F` for a rectangular `𝓡`. -/
theorem frobNorm_conj_rect_le (Rm : Matrix ι K ℝ) (B : Matrix K K ℝ) :
    frobNorm (Rm * B * Rmᵀ) ≤ rectFrobSq Rm * frobNorm B := by
  have hsq : rectFrobSq (Rm * B * Rmᵀ) ≤ rectFrobSq Rm ^ 2 * rectFrobSq B := by
    have h1 : rectFrobSq (Rm * B * Rmᵀ) ≤ rectFrobSq (Rm * B) * rectFrobSq (Rmᵀ) :=
      rectFrobSq_mul_le_mul _ _
    rw [rectFrobSq_transpose] at h1
    calc rectFrobSq (Rm * B * Rmᵀ) ≤ rectFrobSq (Rm * B) * rectFrobSq Rm := h1
      _ ≤ rectFrobSq Rm * rectFrobSq B * rectFrobSq Rm :=
          mul_le_mul_of_nonneg_right (rectFrobSq_mul_le_mul _ _) (rectFrobSq_nonneg Rm)
      _ = rectFrobSq Rm ^ 2 * rectFrobSq B := by ring
  have hfn : frobNorm (Rm * B * Rmᵀ) = Real.sqrt (rectFrobSq (Rm * B * Rmᵀ)) := rfl
  have hfb : frobNorm B = Real.sqrt (rectFrobSq B) := rfl
  rw [hfn, hfb]
  calc Real.sqrt (rectFrobSq (Rm * B * Rmᵀ))
      ≤ Real.sqrt (rectFrobSq Rm ^ 2 * rectFrobSq B) := Real.sqrt_le_sqrt hsq
    _ = rectFrobSq Rm * Real.sqrt (rectFrobSq B) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (rectFrobSq_nonneg Rm)]

omit [Fintype ι] in
/-- `a(𝓡B𝓡') = 𝓡(aB)𝓡'`. -/
theorem smul_conj_rect (a : ℝ) (Rm : Matrix ι K ℝ) (B : Matrix K K ℝ) :
    a • (Rm * B * Rmᵀ) = Rm * (a • B) * Rmᵀ := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype ι] in
/-- `𝓡B𝓡'` is Hermitian whenever `B` is symmetric. -/
theorem isHermitian_conj_rect {Rm : Matrix ι K ℝ} {B : Matrix K K ℝ} (hB : Bᵀ = B) :
    (Rm * B * Rmᵀ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hB, Matrix.mul_assoc]

end RectConj

/-! ### The restricted limit, and Theorem 7(b) -/

section ConjInv

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `(X̃'X̃)^{-1}𝓜̂_W(X̃'X̃)^{-1}` is symmetric whenever `X̃'X̃` and `𝓜̂_W` are. -/
theorem transpose_conj_inv {Gr Mh : Matrix K K ℝ} (hG : Grᵀ = Gr) (hM : Mhᵀ = Mh) :
    (Gr⁻¹ * Mh * Gr⁻¹)ᵀ = Gr⁻¹ * Mh * Gr⁻¹ := by
  have hinv : (Gr⁻¹)ᵀ = Gr⁻¹ := by rw [Matrix.transpose_nonsing_inv, hG]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hinv, hM, Matrix.mul_assoc]

/-- `ω ↦ f(ω)^{-1}g(ω)f(ω)^{-1}` is measurable; `Matrix.inv` is total,
so no invertibility is needed. -/
theorem measurable_conj_inv {f g : Ω → Matrix K K ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun ω => (f ω)⁻¹ * g ω * (f ω)⁻¹ :=
  Wald.measurable_matrix_mul
    (Wald.measurable_matrix_mul (Wald.measurable_matrix_inv.comp hf) hg)
    (Wald.measurable_matrix_inv.comp hf)

/-- `H^{-1}SH^{-1} ≻ 0` from `H ≻ 0` and `S ≻ 0`. -/
theorem posDef_conj_inv {H S : Matrix K K ℝ} (hH : H.PosDef) (hS : S.PosDef) :
    (H⁻¹ * S * H⁻¹).PosDef := by
  have hinj : Function.Injective (H⁻¹).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 hH.isUnit)
  have hsymm : Hᵀ = H := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hH.isHermitian.eq
  have hinvsymm : (H⁻¹)ᴴ = H⁻¹ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_nonsing_inv, hsymm]
  have h := hS.mul_mul_conjTranspose_same hinj
  rwa [hinvsymm] at h

end ConjInv

section Restricted

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]

omit [DecidableEq ι] [DecidableEq K] in
/-- `𝓡(·)𝓡'` preserves convergence in probability to a constant. -/
theorem tendstoInProb_conj_rect {X : ℕ → Ω → Matrix K K ℝ} {C : Matrix K K ℝ}
    (Rm : Matrix ι K ℝ)
    (h : TendstoInMeasure P (fun n ω => frobNorm (X n ω - C)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω => frobNorm (Rm * X n ω * Rmᵀ - Rm * C * Rmᵀ)) atTop
      (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_le_const_mul (c := rectFrobSq Rm + 1)
    (by linarith [rectFrobSq_nonneg Rm]) (fun n ω => frobNorm_nonneg _) (fun n ω => ?_) h
  have hsplit : Rm * X n ω * Rmᵀ - Rm * C * Rmᵀ = Rm * (X n ω - C) * Rmᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hsplit]
  refine (frobNorm_conj_rect_le Rm _).trans ?_
  nlinarith [frobNorm_nonneg (X n ω - C), rectFrobSq_nonneg Rm]

omit [DecidableEq ι] in
/-- `𝓡(nV̂_W)𝓡' ⟶ᵖ 𝓡H^{-1}SH^{-1}𝓡'`, under the hypotheses of `tendstoInProb_nVhat`. -/
theorem tendstoInProb_restricted_nVhat
    {Gr Mh Sn : ℕ → Ω → Matrix K K ℝ} {H S : Matrix K K ℝ} {N : ℕ → ℝ}
    (Rm : Matrix ι K ℝ) (hN : ∀ n, 0 < N n) (hH : H.PosDef)
    (hG : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Gr n ω - H))
      atTop (fun _ => (0 : ℝ)))
    (hM : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Mh n ω - Sn n ω))
      atTop (fun _ => (0 : ℝ)))
    (hS : TendstoInMeasure P (fun n ω => frobNorm (Sn n ω - S)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P
      (fun n ω => frobNorm (N n • (Rm * ((Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹) * Rmᵀ)
        - Rm * (H⁻¹ * S * H⁻¹) * Rmᵀ))
      atTop (fun _ => (0 : ℝ)) := by
  have hlim := tendstoInProb_conj_rect (P := P) Rm (tendstoInProb_nVhat hN hH hG hM hS)
  have heq : (fun n ω => frobNorm (N n • (Rm * ((Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹) * Rmᵀ)
        - Rm * (H⁻¹ * S * H⁻¹) * Rmᵀ))
      = fun n ω => frobNorm (Rm * (N n • ((Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹)) * Rmᵀ
        - Rm * (H⁻¹ * S * H⁻¹) * Rmᵀ) := by
    funext n ω
    rw [smul_conj_rect]
  rw [heq]
  exact hlim

variable [IsProbabilityMeasure P]
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Theorem 7(b).** `P(𝓡V̂_W𝓡' ≻ 0) → 1` and `𝒲(𝓡, V̂_W; β̂_JM) ⟶ᵈ χ²_r`, with
`V̂_W = (X̃'X̃)^{-1}𝓜̂_W(X̃'X̃)^{-1}` and the restricted variance limit derived from Theorem 7(a).

`hRank` is full row rank of `𝓡`; `hH`, `hG` give `n^{-1}X̃'X̃ →ᵖ H ≻ 0`; `hSpd`, `hS` give
`S_n →ᵖ S ≻ 0`; `hM` is `n^{-1}𝓜̂_W - S_n →ᵖ 0` (`tendstoInProb_meatW_sub`); `hCLT`, `hGg` are
the central limit theorem through `𝓡`. `hN` makes the sample size positive, `hGrsymm`,
`hMhsymm` state symmetry of `X̃'X̃` and `𝓜̂_W`, and `hGrmeas`, `hMhmeas` their measurability. -/
theorem vhat_wald_of_nVhat
    {Rm : Matrix ι K ℝ} (hRank : Function.Injective Rm.vecMul)
    {H S : Matrix K K ℝ} (hH : H.PosDef) (hSpd : S.PosDef)
    {N : ℕ → ℝ} (hN : ∀ n, 0 < N n)
    {Gr Mh Sn : ℕ → Ω → Matrix K K ℝ}
    (hGrsymm : ∀ n ω, (Gr n ω)ᵀ = Gr n ω) (hMhsymm : ∀ n ω, (Mh n ω)ᵀ = Mh n ω)
    (hGrmeas : ∀ n, Measurable (Gr n)) (hMhmeas : ∀ n, Measurable (Mh n))
    (hG : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Gr n ω - H))
      atTop (fun _ => (0 : ℝ)))
    (hM : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Mh n ω - Sn n ω))
      atTop (fun _ => (0 : ℝ)))
    (hS : TendstoInMeasure P (fun n ω => frobNorm (Sn n ω - S)) atTop (fun _ => (0 : ℝ)))
    {dev : ℕ → Ω → EuclideanSpace ℝ K} {Gg : Ω' → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution
      (fun n ω => Real.sqrt (N n) • restrictVec Rm (dev n ω)) atTop Gg (fun _ => P) P')
    (hGg : P'.map Gg = multivariateGaussian 0 (Rm * (H⁻¹ * S * H⁻¹) * Rmᵀ)) :
    Tendsto (fun n => P {ω |
        (Rm * ((Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹) * Rmᵀ).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => Wald.waldStat (Rm * ((Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹) * Rmᵀ)
            (restrictVec Rm (dev n ω))) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P) (multivariateGaussian 0 1) :=
  vhat_wald (posDef_conj_inv hH hSpd) hRank hN
    (Vh := fun n ω => (Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹)
    (fun n ω => isHermitian_conj_rect (transpose_conj_inv (hGrsymm n ω) (hMhsymm n ω)))
    (fun n => measurable_conj_inv (hGrmeas n) (hMhmeas n))
    (tendstoInProb_restricted_nVhat Rm hN hH hG hM hS) hCLT hGg

end Restricted

/-! ### Non-vacuity

One regressor (`K = ι = Fin 1`, `𝓡 = I₁`) over `Ω = ℝ¹` under `N(0, 1)`, with `N_n = n + 1`,
`X̃'X̃ = [n+1]`, `H = [1]`, `S_n = [1 + (n+1)^{-1}]`, `S = [1]`,
`𝓜̂_W = [(n+1)(1 + (n+1)^{-1})]` and `β̂ − β = (n+1)^{-1/2}ω`, so that `√N_n 𝓡(β̂ − β) = ω`. The
restricted variance estimate is `[1 + (n+1)^{-1}] ≻ 0` at every index, so the Wald statistic is
`ω²/(1 + (n+1)^{-1})`. -/

section WaldOfNVhatWitness

/-- The witness's bread `X̃'X̃ = [n+1]`, constant in `ω`. -/
noncomputable def wGr (n : ℕ) (_ω : EuclideanSpace ℝ (Fin 1)) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of fun _ _ => (n : ℝ) + 1

/-- The witness's meat `𝓜̂_W = [(n+1)(1 + (n+1)^{-1})]`, constant in `ω`. -/
noncomputable def wMh (n : ℕ) (_ω : EuclideanSpace ℝ (Fin 1)) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹)

/-- The witness's `S_n = [1 + (n+1)^{-1}]`, which converges to `S = [1]` without ever equalling
it. -/
noncomputable def wSn (n : ℕ) (_ω : EuclideanSpace ℝ (Fin 1)) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹

/-- The witness's deviation `β̂ − β = (n+1)^{-1/2}ω`, so that `√N_n(β̂ − β) = ω ~ N(0,1)`. -/
noncomputable def wDev (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  (Real.sqrt ((n : ℝ) + 1))⁻¹ • ω

/-- `‖S_n − S‖_F = (n+1)^{-1} > 0` at every index. -/
theorem frobNorm_wSn_sub (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) :
    frobNorm (wSn n ω - 1) = ((n : ℝ) + 1)⁻¹ := by
  have heq : (wSn n ω - 1 : Matrix (Fin 1) (Fin 1) ℝ)
      = Matrix.of fun _ _ => ((n : ℝ) + 1)⁻¹ := by
    ext i j
    fin_cases i; fin_cases j
    simp [wSn]
  rw [heq, frobNorm_scalar, abs_of_nonneg (by positivity)]

/-- The restricted variance estimate of the witness is `𝓡(N_nV̂_W)𝓡' = [1 + (n+1)^{-1}]`. -/
theorem wVhat_restricted (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) :
    ((n : ℝ) + 1) • ((1 : Matrix (Fin 1) (Fin 1) ℝ)
        * ((wGr n ω)⁻¹ * wMh n ω * (wGr n ω)⁻¹) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)
      = Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹ := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hinv : (wGr n ω)⁻¹ = Matrix.of fun _ _ => ((n : ℝ) + 1)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i; fin_cases j
    simp [wGr, Matrix.mul_apply, mul_inv_cancel₀ hne]
  rw [hinv, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  fin_cases i; fin_cases j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul, wMh,
    Finset.univ_unique, Finset.sum_singleton]
  field_simp

/-- `vhat_wald_of_nVhat` on the witness model. -/
theorem vhat_wald_of_nVhat_witness :
    Tendsto (fun n : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
        {ω | ((1 : Matrix (Fin 1) (Fin 1) ℝ) * ((wGr n ω)⁻¹ * wMh n ω * (wGr n ω)⁻¹)
          * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
            Wald.waldStat ((1 : Matrix (Fin 1) (Fin 1) ℝ)
                * ((wGr n ω)⁻¹ * wMh n ω * (wGr n ω)⁻¹)
                * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)
              (restrictVec 1 (wDev n ω))) atTop
          (fun z : EuclideanSpace ℝ (Fin 1) => ‖z‖ ^ 2)
          (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
          (multivariateGaussian 0 1) := by
  have hCeq : ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [inv_one, Matrix.one_mul, Matrix.one_mul]
  have hrank : Function.Injective (1 : Matrix (Fin 1) (Fin 1) ℝ).vecMul := by
    intro v v' h
    simpa [Matrix.vecMul_one] using h
  have hGrsymm : ∀ (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)), (wGr n ω)ᵀ = wGr n ω := by
    intro n ω; ext i j; fin_cases i; fin_cases j; simp [wGr]
  have hMhsymm : ∀ (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)), (wMh n ω)ᵀ = wMh n ω := by
    intro n ω; ext i j; fin_cases i; fin_cases j; simp [wMh]
  have hGw : TendstoInMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
      (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        frobNorm ((((n : ℝ) + 1)⁻¹ • wGr n ω - 1 : Matrix (Fin 1) (Fin 1) ℝ)))
      atTop (fun _ => (0 : ℝ)) := by
    have hfun : (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        frobNorm ((((n : ℝ) + 1)⁻¹ • wGr n ω - 1 : Matrix (Fin 1) (Fin 1) ℝ)))
        = fun (_ : ℕ) (_ : EuclideanSpace ℝ (Fin 1)) => (0 : ℝ) := by
      funext n ω
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      have heq : ((((n : ℝ) + 1)⁻¹ • wGr n ω - 1 : Matrix (Fin 1) (Fin 1) ℝ))
          = Matrix.of fun _ _ => (0 : ℝ) := by
        ext i j
        fin_cases i; fin_cases j
        simp [wGr, inv_mul_cancel₀ hne]
      rw [heq, frobNorm_scalar]
      simp
    rw [hfun]
    exact tendstoInProb_of_tendsto (a := fun _ => (0 : ℝ)) (c := 0) tendsto_const_nhds
  have hMw : TendstoInMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
      (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        frobNorm ((((n : ℝ) + 1)⁻¹ • wMh n ω - wSn n ω : Matrix (Fin 1) (Fin 1) ℝ)))
      atTop (fun _ => (0 : ℝ)) := by
    have hfun : (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        frobNorm ((((n : ℝ) + 1)⁻¹ • wMh n ω - wSn n ω : Matrix (Fin 1) (Fin 1) ℝ)))
        = fun (_ : ℕ) (_ : EuclideanSpace ℝ (Fin 1)) => (0 : ℝ) := by
      funext n ω
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      have heq : ((((n : ℝ) + 1)⁻¹ • wMh n ω - wSn n ω : Matrix (Fin 1) (Fin 1) ℝ))
          = Matrix.of fun _ _ => (0 : ℝ) := by
        ext i j
        fin_cases i; fin_cases j
        simp [wMh, wSn, inv_mul_cancel_left₀ hne]
      rw [heq, frobNorm_scalar]
      simp
    rw [hfun]
    exact tendstoInProb_of_tendsto (a := fun _ => (0 : ℝ)) (c := 0) tendsto_const_nhds
  have hSw : TendstoInMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
      (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        frobNorm ((wSn n ω - 1 : Matrix (Fin 1) (Fin 1) ℝ)))
      atTop (fun _ => (0 : ℝ)) := by
    have hfun : (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        frobNorm ((wSn n ω - 1 : Matrix (Fin 1) (Fin 1) ℝ)))
        = fun (n : ℕ) (_ : EuclideanSpace ℝ (Fin 1)) => ((n : ℝ) + 1)⁻¹ := by
      funext n ω
      exact frobNorm_wSn_sub n ω
    rw [hfun]
    refine tendstoInProb_of_tendsto (a := fun n : ℕ => ((n : ℝ) + 1)⁻¹) (c := 0) ?_
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => ?_
    rw [one_div]
  have hCLTw : TendstoInDistribution
      (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        Real.sqrt ((n : ℝ) + 1) • restrictVec (1 : Matrix (Fin 1) (Fin 1) ℝ) (wDev n ω))
      atTop (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
      (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
    have hfun : (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        Real.sqrt ((n : ℝ) + 1) • restrictVec (1 : Matrix (Fin 1) (Fin 1) ℝ) (wDev n ω))
        = fun (_ : ℕ) => (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) := by
      funext n ω
      have hne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
      simp only [wDev, restrictVec_one, smul_smul, mul_inv_cancel₀ hne, one_smul]
      rfl
    rw [hfun]
    exact tendstoInDistribution_const aemeasurable_id
  have hGgw : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1).map id
      = multivariateGaussian 0 ((1 : Matrix (Fin 1) (Fin 1) ℝ)
          * ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)
          * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) := by
    rw [Measure.map_id, hCeq, Matrix.transpose_one, Matrix.one_mul, Matrix.one_mul]
  exact vhat_wald_of_nVhat (P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (Rm := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (H := 1) (S := 1)
    (N := fun n : ℕ => (n : ℝ) + 1) (Gr := wGr) (Mh := wMh) (Sn := wSn)
    (dev := wDev) (Gg := id)
    hrank Matrix.PosDef.one Matrix.PosDef.one (fun n => by positivity) hGrsymm hMhsymm
    (fun _ => measurable_const) (fun _ => measurable_const) hGw hMw hSw hCLTw hGgw

end WaldOfNVhatWitness

end RestrictedLimit

end Vhat
end Multiway
