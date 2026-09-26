import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Residual representation and the residual maker `R`

The first part of this file formalizes the first sentence of Lemma SM.B.6 (residual
representation and exact leverage identity): under the model `y = Xβ + Δα + ν` and the rank
condition `X'Q_[Δ]X ≻ 0`, the residual maker `R` is symmetric and idempotent with `RΔ = 0`,
`tr(R) = n - d_[Δ] - K`, and `ν̂_FE = Rν`. The conditional clauses of the lemma are in
`Multiway.LeverageCond`. The second part formalizes Proposition SM.D.2 (sufficient conditions
for Assumption 3(iv)).

## Notation

* `E` is `ℝⁿ`, `S` is `𝒮 = col(Δ)`, and the regressors are a family `x : ι → E`.
* `fittedSpace S x` is `col([Δ, X])` and `withinRegressor S x` gives the columns of `Q_[Δ]X`.
* `residualMaker S x` is `R`, the orthogonal projector onto `col([Δ, X])ᗮ`.

## Main results

* `residualMaker_isSelfAdjoint`, `residualMaker_isIdempotentElem`,
  `residualMaker_apply_of_mem_fixedEffects`, `trace_residualMaker`: the properties of `R`.
* `feResidual_eq_residualMaker_apply`: `ν̂_FE = Rν`.
* `SuffLeverage.leverage_clause_a`, `SuffLeverage.leverage_clause_b`: Proposition SM.D.2.
-/

namespace Multiway

open scoped RealInnerProductSpace

open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*}

/-! ### Definitions -/

/-- `col(X)`, the span of the `K` regressor columns. -/
def regressorSpace (x : ι → E) : Submodule ℝ E := Submodule.span ℝ (Set.range x)

/-- `col([Δ, X])`, the column space of the fixed-effect dummies together with the
regressors. -/
def fittedSpace (S : Submodule ℝ E) (x : ι → E) : Submodule ℝ E := S ⊔ regressorSpace x

/-- The columns of the joint within transformation `X̃ = Q_[Δ]X`. -/
noncomputable def withinRegressor (S : Submodule ℝ E) (x : ι → E) (k : ι) : E :=
  Sᗮ.starProjection (x k)

/-- The residual maker `R = Q_[Δ] - Λ`, as the orthogonal projector onto `col([Δ, X])ᗮ`. -/
noncomputable def residualMaker (S : Submodule ℝ E) (x : ι → E) : E →L[ℝ] E :=
  (fittedSpace S x)ᗮ.starProjection

variable {S : Submodule ℝ E} {x : ι → E}

omit [FiniteDimensional ℝ E] in
theorem mem_fittedSpace_of_mem {v : E} (h : v ∈ S) : v ∈ fittedSpace S x :=
  Submodule.mem_sup_left h

omit [FiniteDimensional ℝ E] in
theorem regressor_mem_fittedSpace (k : ι) : x k ∈ fittedSpace S x :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)

/-- `R = I - P`, with `P` the orthogonal projector onto `col([Δ, X])`. -/
theorem residualMaker_eq_id_sub (S : Submodule ℝ E) (x : ι → E) :
    residualMaker S x = ContinuousLinearMap.id ℝ E - (fittedSpace S x).starProjection :=
  Submodule.starProjection_orthogonal _

/-! ### Symmetry and idempotence -/

/-- `R` is self-adjoint. -/
theorem residualMaker_isSelfAdjoint (S : Submodule ℝ E) (x : ι → E) :
    IsSelfAdjoint (residualMaker S x) :=
  isSelfAdjoint_starProjection _

/-- Symmetry of `R` in the form `⟪Ru, v⟫ = ⟪u, Rv⟫`. -/
theorem inner_residualMaker_left_eq_right (S : Submodule ℝ E) (x : ι → E) (u v : E) :
    ⟪residualMaker S x u, v⟫ = ⟪u, residualMaker S x v⟫ :=
  Submodule.inner_starProjection_left_eq_right _ u v

/-- `R² = R`. -/
theorem residualMaker_isIdempotentElem (S : Submodule ℝ E) (x : ι → E) :
    IsIdempotentElem (residualMaker S x) :=
  Submodule.isIdempotentElem_starProjection _

/-! ### `RΔ = 0` -/

theorem residualMaker_apply_eq_zero {v : E} (hv : v ∈ fittedSpace S x) :
    residualMaker S x v = 0 := by
  rw [residualMaker, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_eq_self_iff.mpr hv, sub_self]

/-- `RΔ = 0`: `R` annihilates the joint fixed-effects space `𝒮`. -/
theorem residualMaker_apply_of_mem_fixedEffects {v : E} (hv : v ∈ S) :
    residualMaker S x v = 0 :=
  residualMaker_apply_eq_zero (mem_fittedSpace_of_mem hv)

/-- `RX = 0`. -/
theorem residualMaker_apply_regressor (k : ι) : residualMaker S x (x k) = 0 :=
  residualMaker_apply_eq_zero (regressor_mem_fittedSpace k)

/-! ### `tr(R) = n - d_[Δ] - K` -/

/-- Under the rank condition, `rank([Δ, X]) = d_[Δ] + K`. -/
theorem finrank_fittedSpace [Fintype ι] (S : Submodule ℝ E) (x : ι → E)
    (hX : LinearIndependent ℝ (withinRegressor S x)) :
    finrank ℝ (fittedSpace S x) = finrank ℝ S + Fintype.card ι := by
  set W : Submodule ℝ E := Submodule.span ℝ (Set.range (withinRegressor S x)) with hW
  have hWS : W ≤ Sᗮ := by
    rw [hW, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.starProjection_apply_mem _ _
  have hsplit : fittedSpace S x = S ⊔ W := by
    refine le_antisymm ?_ ?_
    · rw [fittedSpace, sup_le_iff]
      refine ⟨le_sup_left, ?_⟩
      rw [regressorSpace, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hk : x k = S.starProjection (x k) + withinRegressor S x k := by
        rw [withinRegressor, Submodule.starProjection_orthogonal_val]
        abel
      exact Submodule.mem_sup.2 ⟨_, S.starProjection_apply_mem _, _,
        Submodule.subset_span ⟨k, rfl⟩, hk.symm⟩
    · rw [sup_le_iff]
      refine ⟨le_sup_left, ?_⟩
      rw [hW, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hk : withinRegressor S x k = x k - S.starProjection (x k) :=
        Submodule.starProjection_orthogonal_val _
      rw [SetLike.mem_coe, hk]
      exact Submodule.sub_mem _ (regressor_mem_fittedSpace k)
        (mem_fittedSpace_of_mem (S.starProjection_apply_mem _))
  have hinf : S ⊓ W = ⊥ := by
    refine le_bot_iff.mp ?_
    calc S ⊓ W ≤ S ⊓ Sᗮ := inf_le_inf_left S hWS
      _ = ⊥ := S.inf_orthogonal_eq_bot
  have hcard : finrank ℝ W = Fintype.card ι := by
    rw [hW]; exact finrank_span_eq_card hX
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S W
  rw [hinf, finrank_bot, add_zero, hcard] at hsum
  rw [hsplit, hsum]

/-- `R` is a linear projection onto `col([Δ, X])ᗮ`. -/
theorem isProj_residualMaker (S : Submodule ℝ E) (x : ι → E) :
    LinearMap.IsProj (fittedSpace S x)ᗮ (residualMaker S x : E →ₗ[ℝ] E) where
  map_mem v := Submodule.starProjection_apply_mem _ v
  map_id _ hv := Submodule.starProjection_eq_self_iff.mpr hv

/-- Under the rank condition, `tr(R) = n - d_[Δ] - K`. -/
theorem trace_residualMaker [Fintype ι] (S : Submodule ℝ E) (x : ι → E)
    (hX : LinearIndependent ℝ (withinRegressor S x)) :
    LinearMap.trace ℝ E (residualMaker S x : E →ₗ[ℝ] E)
      = (finrank ℝ E : ℝ) - (finrank ℝ S : ℝ) - (Fintype.card ι : ℝ) := by
  have hrank := finrank_fittedSpace S x hX
  have horth := (fittedSpace S x).finrank_add_finrank_orthogonal
  have hnat : finrank ℝ (fittedSpace S x)ᗮ + (finrank ℝ S + Fintype.card ι) = finrank ℝ E := by
    omega
  have hreal : (finrank ℝ (fittedSpace S x)ᗮ : ℝ) + ((finrank ℝ S : ℝ) + (Fintype.card ι : ℝ))
      = (finrank ℝ E : ℝ) := by exact_mod_cast hnat
  rw [(isProj_residualMaker S x).trace]
  linarith

/-! ### `ν̂_FE = Rν` -/

/-- Under the model `y = Xβ + Δα + ν`, the residual maker sees only the disturbance:
`Ry = Rν`. -/
theorem residualMaker_apply_model [Fintype ι] {y a ν : E} {β : ι → ℝ} (ha : a ∈ S)
    (hy : y = (∑ k, β k • x k) + a + ν) :
    residualMaker S x y = residualMaker S x ν := by
  have hX : residualMaker S x (∑ k, β k • x k) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun k _ => by
      rw [map_smul, residualMaker_apply_regressor, smul_zero]
  rw [hy, map_add, map_add, hX, residualMaker_apply_of_mem_fixedEffects ha, zero_add, zero_add]

/-- The fixed-effects residual `ν̂_FE := Q_[Δ](y - Xβ̂)` equals `Ry`, for any `β̂` solving the
within normal equations `X'Q_[Δ](y - Xβ̂) = 0`. -/
theorem withinResidual_eq_residualMaker [Fintype ι] {y : E} {b : ι → ℝ}
    (hb : ∀ k, ⟪withinRegressor S x k, y - ∑ j, b j • x j⟫ = 0) :
    Sᗮ.starProjection (y - ∑ j, b j • x j) = residualMaker S x y := by
  set u : E := y - ∑ j, b j • x j with hu
  set r : E := Sᗮ.starProjection u with hr
  have hrS : r ∈ Sᗮ := Submodule.starProjection_apply_mem _ _
  have hrX : ∀ k, ⟪x k, r⟫ = 0 := by
    intro k
    rw [hr, ← Submodule.inner_starProjection_left_eq_right]
    exact hb k
  have hrP : r ∈ (fittedSpace S x)ᗮ := by
    rw [fittedSpace, ← Submodule.inf_orthogonal]
    refine ⟨hrS, (Submodule.mem_orthogonal _ _).2 fun v hv => ?_⟩
    rw [regressorSpace] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨k, rfl⟩ := hv; exact hrX k
    | zero => simp
    | add v w _ _ hv hw => rw [inner_add_left, hv, hw, add_zero]
    | smul c v _ hv => rw [real_inner_smul_left, hv, mul_zero]
  have hyr : y - r ∈ fittedSpace S x := by
    have hsplit : y - r = (∑ j, b j • x j) + S.starProjection u := by
      rw [hr, Submodule.starProjection_orthogonal_val, hu]
      abel
    rw [hsplit]
    exact Submodule.add_mem _
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (regressor_mem_fittedSpace j))
      (mem_fittedSpace_of_mem (S.starProjection_apply_mem _))
  refine (Submodule.eq_starProjection_of_mem_orthogonal' hrP
    (Submodule.le_orthogonal_orthogonal _ hyr) (by abel)).symm

/-- **Lemma SM.B.6**, last clause of the first sentence: under the model, the fixed-effects
residual is `ν̂_FE = Rν`. -/
theorem feResidual_eq_residualMaker_apply [Fintype ι] {y a ν : E} {β b : ι → ℝ} (ha : a ∈ S)
    (hy : y = (∑ k, β k • x k) + a + ν)
    (hb : ∀ k, ⟪withinRegressor S x k, y - ∑ j, b j • x j⟫ = 0) :
    Sᗮ.starProjection (y - ∑ j, b j • x j) = residualMaker S x ν :=
  (withinResidual_eq_residualMaker hb).trans (residualMaker_apply_model ha hy)

/-! ## Proposition SM.D.2: sufficient conditions for Assumption 3(iv)

Suppose `sup_o ‖x_o‖ ≤ C` almost surely and `n⁻¹ tr(X'Q_[Δ]X) ⟶^p tr(H) > 0`. Then the
leverage ratio `max_o ‖x̃_o‖² / ∑_o ‖x̃_o‖²` tends to `0` in probability: (a) if `M = 1`, and the
ratio is then `O_p(1/n)`; (b) for general `M`, if `max_o (P_[Δ])_{oo} → 0`.

The designs form a sequence on one probability space `(Ω, P)` with observation type `O n`;
`X n` is the regressor matrix, `Pm n` a symmetric idempotent matrix playing the role of
`P_[Δ]`, and `⟶^p` is `TendstoInMeasure`. The ratio uses Lean's convention `x / 0 = 0`, and
the hypotheses that depend on the design are required eventually in `n`. In clause (a) the
one-way category-average projector `avgProj i` is proved to be the orthogonal projector onto
the vectors constant on categories.

## Main results

* `tendstoInProb_leverageRatio`: the convergence step shared by both clauses.
* `leverage_clause_a`, `leverage_clause_a_bigO`, `leverage_clause_b`: the two clauses.
* `leverage_clause_a_witness`, `leverage_clause_b_witness`: models of the hypotheses.
-/

namespace SuffLeverage

open Filter MeasureTheory
open scoped Topology ENNReal Matrix

open Filter MeasureTheory
open scoped Topology ENNReal Matrix

/-! ### The leverage ratio -/

section Objects

variable {O : Type*} [Fintype O] {ι : Type*} [Fintype ι]

/-- `‖x̃_o‖²`, the squared Euclidean norm of the `o`-th row of the within matrix `X̃`. -/
def rowNormSq (Xt : Matrix O ι ℝ) (o : O) : ℝ := ∑ j, (Xt o j) ^ 2

/-- `max_{o∈𝒪} ‖x̃_o‖²`. -/
noncomputable def maxRowNormSq (Xt : Matrix O ι ℝ) : ℝ := ⨆ o : O, rowNormSq Xt o

/-- `∑_{o∈𝒪} ‖x̃_o‖²`. -/
def sumRowNormSq (Xt : Matrix O ι ℝ) : ℝ := ∑ o, rowNormSq Xt o

/-- The leverage ratio `max_o ‖x̃_o‖² / ∑_o ‖x̃_o‖²`. -/
noncomputable def leverageRatio (Xt : Matrix O ι ℝ) : ℝ :=
  maxRowNormSq Xt / sumRowNormSq Xt

omit [Fintype O] in
theorem rowNormSq_nonneg (Xt : Matrix O ι ℝ) (o : O) : 0 ≤ rowNormSq Xt o :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem le_maxRowNormSq (Xt : Matrix O ι ℝ) (o : O) : rowNormSq Xt o ≤ maxRowNormSq Xt :=
  le_ciSup (Set.finite_range _).bddAbove o

omit [Fintype O] in
theorem maxRowNormSq_le {Xt : Matrix O ι ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ o, rowNormSq Xt o ≤ b) : maxRowNormSq Xt ≤ b := by
  rcases isEmpty_or_nonempty O with _ | _
  · simpa [maxRowNormSq] using hb
  · exact ciSup_le h

theorem maxRowNormSq_nonneg (Xt : Matrix O ι ℝ) : 0 ≤ maxRowNormSq Xt := by
  rcases isEmpty_or_nonempty O with _ | hN
  · simp [maxRowNormSq]
  · exact le_trans (rowNormSq_nonneg Xt (Classical.arbitrary O)) (le_maxRowNormSq Xt _)

theorem sumRowNormSq_nonneg (Xt : Matrix O ι ℝ) : 0 ≤ sumRowNormSq Xt :=
  Finset.sum_nonneg fun o _ => rowNormSq_nonneg Xt o

theorem leverageRatio_nonneg (Xt : Matrix O ι ℝ) : 0 ≤ leverageRatio Xt :=
  div_nonneg (maxRowNormSq_nonneg Xt) (sumRowNormSq_nonneg Xt)

/-- `∑_o ‖x̃_o‖² = tr(X̃'X̃)`. -/
theorem sumRowNormSq_eq_trace [DecidableEq ι] (Xt : Matrix O ι ℝ) :
    sumRowNormSq Xt = (Xtᵀ * Xt).trace := by
  rw [Matrix.trace, sumRowNormSq]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, rowNormSq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun j _ => by ring

/-- `X̃'X̃ = X'QX` for `Q` symmetric and idempotent, so that `∑_o ‖x̃_o‖² = tr(X'Q_[Δ]X)`. -/
theorem sumRowNormSq_within_eq_trace [DecidableEq O] [DecidableEq ι]
    (Q : Matrix O O ℝ) (X : Matrix O ι ℝ) (hsymm : Qᵀ = Q) (hidem : Q * Q = Q) :
    sumRowNormSq (Q * X) = (Xᵀ * Q * X).trace := by
  rw [sumRowNormSq_eq_trace, Matrix.transpose_mul, hsymm, ← Matrix.mul_assoc,
    Matrix.mul_assoc Xᵀ Q Q, hidem]

theorem compl_transpose {O : Type*} [DecidableEq O] {Pm : Matrix O O ℝ} (h : Pmᵀ = Pm) :
    ((1 : Matrix O O ℝ) - Pm)ᵀ = (1 : Matrix O O ℝ) - Pm := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, h]

theorem compl_mul_self {O : Type*} [Fintype O] [DecidableEq O] {Pm : Matrix O O ℝ}
    (h : Pm * Pm = Pm) :
    ((1 : Matrix O O ℝ) - Pm) * ((1 : Matrix O O ℝ) - Pm) = (1 : Matrix O O ℝ) - Pm := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one, h]
  abel

/-- `∑_o ‖x̃_o‖² = n · (n⁻¹ tr(X'Q_[Δ]X))`. -/
theorem sumRowNormSq_eq_card_mul {O' : Type*} [Fintype O'] [DecidableEq O'] [DecidableEq ι]
    {Pm : Matrix O' O' ℝ} (X : Matrix O' ι ℝ) (hsymm : Pmᵀ = Pm) (hidem : Pm * Pm = Pm)
    {r : ℝ} (hr : r ≠ 0) :
    sumRowNormSq (((1 : Matrix O' O' ℝ) - Pm) * X)
      = r * (r⁻¹ * ((Xᵀ * ((1 : Matrix O' O' ℝ) - Pm) * X)).trace) := by
  rw [sumRowNormSq_within_eq_trace _ _ (compl_transpose hsymm) (compl_mul_self hidem)]
  field_simp

end Objects

/-! ### The convergence step shared by both clauses -/

section Skeleton

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A deterministic `o(n)` bound on `max_o ‖x̃_o‖²`, together with `n⁻¹ ∑_o ‖x̃_o‖² ⟶^p t > 0`,
gives convergence of the leverage ratio to `0` in probability. -/
theorem tendstoInProb_leverageRatio
    {O : ℕ → Type*} [∀ n, Fintype (O n)] {ι : Type*} [Fintype ι]
    {Xt : ∀ n, Ω → Matrix (O n) ι ℝ} {b : ℕ → ℝ} {T : ℕ → Ω → ℝ} {t : ℝ} (ht : 0 < t)
    (hb0 : ∀ n, 0 ≤ b n)
    (hnum : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ∀ o, rowNormSq (Xt n ω) o ≤ b n)
    (hb : Tendsto (fun n => b n / n) atTop (𝓝 0))
    (hden : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, sumRowNormSq (Xt n ω) = (n : ℝ) * T n ω)
    (hT : TendstoInMeasure P T atTop (fun _ => t)) :
    TendstoInMeasure P (fun n ω => leverageRatio (Xt n ω)) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hhalf : (0 : ℝ) < t / 2 := by linarith
  have hTsmall : ∀ᶠ n in atTop, P {ω | t / 2 ≤ dist (T n ω) t} ≤ δ := by
    have := (tendstoInMeasure_iff_dist.mp hT) (t / 2) hhalf
    exact (ENNReal.tendsto_nhds_zero.mp this) δ hδ
  have hbsmall : ∀ᶠ n in atTop, b n / n < ε * t / 2 := by
    refine Filter.Tendsto.eventually_lt_const ?_ hb
    positivity
  have hn1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast hn
  filter_upwards [hTsmall, hbsmall, hn1, hnum, hden] with n hTn hbn hn hnum' hden'
  refine le_trans (measure_mono_ae ?_) hTn
  filter_upwards [hnum', hden'] with ω hrow hsum hmem
  have hmem' : ε ≤ leverageRatio (Xt n ω) := by
    have : ε ≤ |leverageRatio (Xt n ω)| := by
      simpa [Real.dist_eq] using (hmem : ε ≤ dist (leverageRatio (Xt n ω)) 0)
    rwa [abs_of_nonneg (leverageRatio_nonneg _)] at this
  show t / 2 ≤ dist (T n ω) t
  rw [Real.dist_eq]
  by_contra hcon
  rw [not_le] at hcon
  have hTlow : t / 2 < T n ω := by
    have h1 : |T n ω - t| < t / 2 := hcon
    have h2 := abs_lt.mp h1
    linarith [h2.1]
  have hpos : 0 < sumRowNormSq (Xt n ω) := by
    rw [hsum]; nlinarith
  have hmax : maxRowNormSq (Xt n ω) ≤ b n := maxRowNormSq_le (hb0 n) hrow
  have hlt : leverageRatio (Xt n ω) < ε := by
    have hbn' : b n < ε * t / 2 * n := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < (n:ℝ))] at hbn
      linarith
    have hs : ε * t / 2 * n < ε * sumRowNormSq (Xt n ω) := by
      rw [hsum]
      have : t / 2 * (n : ℝ) < T n ω * (n : ℝ) :=
        mul_lt_mul_of_pos_right hTlow (by linarith)
      nlinarith
    calc leverageRatio (Xt n ω) ≤ b n / sumRowNormSq (Xt n ω) := by
          unfold leverageRatio; gcongr
      _ < ε := by rw [div_lt_iff₀ hpos]; linarith
  linarith

end Skeleton

/-! ### Clause (b): the Cauchy--Schwarz leverage bound -/

section ClauseB

variable {O : Type*} [Fintype O] [DecidableEq O] {ι : Type*} [Fintype ι]

omit [DecidableEq O] in
/-- `∑_{o'} P_{oo'}² = P_{oo}` for a symmetric idempotent `P`. -/
theorem sum_sq_row_eq_diag {Pm : Matrix O O ℝ} (hsymm : Pmᵀ = Pm) (hidem : Pm * Pm = Pm)
    (o : O) : ∑ o' : O, (Pm o o') ^ 2 = Pm o o := by
  have h : (Pm * Pm) o o = Pm o o := by rw [hidem]
  rw [Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun o' _ => ?_
  have : Pm o' o = Pm o o' := by
    have := congrFun (congrFun hsymm o) o'
    simpa [Matrix.transpose_apply] using this
  rw [this]; ring

/-- If `sup_o ‖x_o‖ ≤ C` and `(P_[Δ])_{oo} ≤ mx` for every `o`, then
`‖x̃_o‖² ≤ 2KC²(1 + n·mx)`. -/
theorem rowNormSq_within_le_of_diag {Pm : Matrix O O ℝ} {X : Matrix O ι ℝ} {C mx : ℝ}
    (hsymm : Pmᵀ = Pm) (hidem : Pm * Pm = Pm)
    (hX : ∀ o, rowNormSq X o ≤ C ^ 2) (hd : ∀ o, Pm o o ≤ mx) (o : O) :
    rowNormSq ((1 - Pm) * X) o
      ≤ 2 * (Fintype.card ι : ℝ) * C ^ 2 * (1 + (Fintype.card O : ℝ) * mx) := by
  have hcol : ∀ j : ι, ∑ o' : O, (X o' j) ^ 2 ≤ (Fintype.card O : ℝ) * C ^ 2 := by
    intro j
    calc ∑ o' : O, (X o' j) ^ 2 ≤ ∑ _o' : O, C ^ 2 := by
          refine Finset.sum_le_sum fun o' _ => le_trans ?_ (hX o')
          exact Finset.single_le_sum (f := fun k => (X o' k) ^ 2)
            (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ = (Fintype.card O : ℝ) * C ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hproj : ∀ j : ι, ((Pm * X) o j) ^ 2 ≤ mx * ((Fintype.card O : ℝ) * C ^ 2) := by
    intro j
    have hcs : ((Pm * X) o j) ^ 2
        ≤ (∑ o' : O, (Pm o o') ^ 2) * (∑ o' : O, (X o' j) ^ 2) := by
      rw [Matrix.mul_apply]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun o' => Pm o o') (fun o' => X o' j)
    rw [sum_sq_row_eq_diag hsymm hidem o] at hcs
    refine hcs.trans (mul_le_mul (hd o) (hcol j) (Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_)
    have h0 : (0:ℝ) ≤ ∑ o' : O, (Pm o o') ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [sum_sq_row_eq_diag hsymm hidem o] at h0
    exact le_trans h0 (hd o)
  have hentry : ∀ j : ι, ((((1 : Matrix O O ℝ) - Pm) * X) o j) ^ 2
      ≤ 2 * C ^ 2 + 2 * (mx * ((Fintype.card O : ℝ) * C ^ 2)) := by
    intro j
    have hsplit : (((1 : Matrix O O ℝ) - Pm) * X) o j = X o j - (Pm * X) o j := by
      rw [Matrix.sub_mul, Matrix.sub_apply, Matrix.one_mul]
    have h1 : (X o j) ^ 2 ≤ C ^ 2 :=
      le_trans (Finset.single_le_sum (f := fun k => (X o k) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)) (hX o)
    have h2 := hproj j
    rw [hsplit]
    nlinarith [sq_nonneg (X o j + (Pm * X) o j)]
  calc rowNormSq ((1 - Pm) * X) o
      ≤ ∑ _j : ι, (2 * C ^ 2 + 2 * (mx * ((Fintype.card O : ℝ) * C ^ 2))) :=
        Finset.sum_le_sum fun j _ => hentry j
    _ = 2 * (Fintype.card ι : ℝ) * C ^ 2 * (1 + (Fintype.card O : ℝ) * mx) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

end ClauseB

/-! ### Clause (a): the one-way category-average projector `P₁` -/

section ClauseA

variable {O : Type*} [Fintype O] [DecidableEq O] {N : Type*} [DecidableEq N]
variable {ι : Type*} [Fintype ι]

/-- The category fibre `{o' ∈ 𝒪 : i_1(o') = c}` of the single fixed-effect dimension. -/
def fibre (i : O → N) (c : N) : Finset O := Finset.univ.filter (fun p => i p = c)

omit [DecidableEq O] in
theorem self_mem_fibre (i : O → N) (o : O) : o ∈ fibre i (i o) := by simp [fibre]

omit [DecidableEq O] in
theorem fibre_card_pos (i : O → N) (o : O) : 0 < (fibre i (i o)).card :=
  Finset.card_pos.mpr ⟨o, self_mem_fibre i o⟩

omit [DecidableEq O] in
theorem fibre_congr {i : O → N} {o o' : O} (h : i o = i o') : fibre i (i o) = fibre i (i o') := by
  rw [h]

/-- `P_1`, the category-average projector of a one-way design: it replaces each column of a
matrix by its category averages. -/
noncomputable def avgProj (i : O → N) : Matrix O O ℝ :=
  fun o o' => if i o' = i o then ((fibre i (i o)).card : ℝ)⁻¹ else 0

omit [DecidableEq O] [Fintype ι] in
theorem avgProj_mul_apply (i : O → N) (V : Matrix O ι ℝ) (o : O) (j : ι) :
    (avgProj i * V) o j
      = ((fibre i (i o)).card : ℝ)⁻¹ * ∑ o' ∈ fibre i (i o), V o' j := by
  rw [Matrix.mul_apply, Finset.mul_sum, fibre, Finset.sum_filter]
  exact Finset.sum_congr rfl fun o' _ => by by_cases h : i o' = i o <;> simp [avgProj, h, fibre]

omit [DecidableEq O] [Fintype ι] in
/-- `|(P_1 x_{·j})_o| ≤ max_{o'} |x_{o'j}|`. -/
theorem abs_avgProj_mul_le (i : O → N) (V : Matrix O ι ℝ) {c : ℝ} (_hc : 0 ≤ c) (j : ι)
    (h : ∀ o', |V o' j| ≤ c) (o : O) : |(avgProj i * V) o j| ≤ c := by
  have hcard : (0 : ℝ) < ((fibre i (i o)).card : ℝ) := by
    exact_mod_cast fibre_card_pos i o
  rw [avgProj_mul_apply, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hcard))]
  have hsum : |∑ o' ∈ fibre i (i o), V o' j| ≤ ((fibre i (i o)).card : ℝ) * c := by
    calc |∑ o' ∈ fibre i (i o), V o' j| ≤ ∑ o' ∈ fibre i (i o), |V o' j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _o' ∈ fibre i (i o), c := Finset.sum_le_sum fun o' _ => h o'
      _ = ((fibre i (i o)).card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ((fibre i (i o)).card : ℝ)⁻¹ * |∑ o' ∈ fibre i (i o), V o' j|
      ≤ ((fibre i (i o)).card : ℝ)⁻¹ * (((fibre i (i o)).card : ℝ) * c) := by
        exact mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hcard))
    _ = c := by field_simp

omit [DecidableEq O] in
/-- `P_1` is symmetric. -/
theorem avgProj_transpose (i : O → N) : (avgProj i)ᵀ = avgProj i := by
  ext o o'
  by_cases h : i o = i o'
  · simp [Matrix.transpose_apply, avgProj, h]
  · have h' : ¬ i o' = i o := fun hc => h hc.symm
    simp [Matrix.transpose_apply, avgProj, h, h']

/-- `P_1` is idempotent. -/
theorem avgProj_mul_self (i : O → N) : avgProj i * avgProj i = avgProj i := by
  ext o o''
  rw [Matrix.mul_apply]
  by_cases h : i o'' = i o
  · have hcard : (0 : ℝ) < ((fibre i (i o)).card : ℝ) := by exact_mod_cast fibre_card_pos i o
    have hterm : ∀ o' ∈ Finset.univ,
        avgProj i o o' * avgProj i o' o''
          = if o' ∈ fibre i (i o) then ((fibre i (i o)).card : ℝ)⁻¹
              * ((fibre i (i o)).card : ℝ)⁻¹ else 0 := by
      intro o' _
      by_cases h1 : i o' = i o
      · have h2 : i o'' = i o' := by rw [h, h1]
        have h3 : fibre i (i o') = fibre i (i o) := by rw [h1]
        simp [avgProj, h1, h2, fibre, Finset.mem_filter]
      · simp [avgProj, fibre, Finset.mem_filter, h1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    simp only [avgProj, h, reduceIte]
    field_simp
  · have hterm : ∀ o' ∈ Finset.univ, avgProj i o o' * avgProj i o' o'' = (0 : ℝ) := by
      intro o' _
      by_cases h1 : i o' = i o
      · have h2 : ¬ i o'' = i o' := by rw [h1]; exact h
        simp [avgProj, h2]
      · simp [avgProj, h1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero]
    simp only [avgProj, h, reduceIte]

omit [DecidableEq O] [Fintype ι] in
/-- `col(P_1) ⊆ 𝒮_1`: the image of `P_1` is constant on categories. -/
theorem avgProj_mul_constant_on_fibre (i : O → N) (V : Matrix O ι ℝ) {o o' : O}
    (h : i o = i o') (j : ι) : (avgProj i * V) o j = (avgProj i * V) o' j := by
  rw [avgProj_mul_apply, avgProj_mul_apply, fibre_congr h]

omit [DecidableEq O] [Fintype ι] in
/-- `P_1Δ_1 = Δ_1`: `P_1` fixes every vector that is constant on categories. -/
theorem avgProj_mul_of_constant_on_fibre (i : O → N) (V : Matrix O ι ℝ) (j : ι)
    (h : ∀ o o' : O, i o = i o' → V o j = V o' j) (o : O) :
    (avgProj i * V) o j = V o j := by
  have hcard : (0 : ℝ) < ((fibre i (i o)).card : ℝ) := by exact_mod_cast fibre_card_pos i o
  rw [avgProj_mul_apply]
  have hconst : ∑ o' ∈ fibre i (i o), V o' j = ((fibre i (i o)).card : ℝ) * V o j := by
    have hpt : ∀ o' ∈ fibre i (i o), V o' j = V o j := by
      intro o' ho'
      rw [fibre, Finset.mem_filter] at ho'
      exact h o' o ho'.2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  field_simp

/-- At `M = 1`, `max_o ‖x̃_o‖² ≤ 4KC²`, a constant in `n`. -/
theorem rowNormSq_within_avgProj_le (i : O → N) (X : Matrix O ι ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hX : ∀ o, rowNormSq X o ≤ C ^ 2) (o : O) :
    rowNormSq (((1 : Matrix O O ℝ) - avgProj i) * X) o ≤ 4 * (Fintype.card ι : ℝ) * C ^ 2 := by
  have hcolbd : ∀ (j : ι) (o' : O), |X o' j| ≤ C := by
    intro j o'
    have h1 : (X o' j) ^ 2 ≤ C ^ 2 :=
      le_trans (Finset.single_le_sum (f := fun k => (X o' k) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)) (hX o')
    exact abs_le.mpr (abs_le_of_sq_le_sq' h1 hC)
  have hentry : ∀ j : ι, ((((1 : Matrix O O ℝ) - avgProj i) * X) o j) ^ 2 ≤ 4 * C ^ 2 := by
    intro j
    have hsplit : ((((1 : Matrix O O ℝ) - avgProj i) * X) o j)
        = X o j - (avgProj i * X) o j := by
      rw [Matrix.sub_mul, Matrix.sub_apply, Matrix.one_mul]
    have h1 : |X o j| ≤ C := hcolbd j o
    have h2 : |(avgProj i * X) o j| ≤ C := abs_avgProj_mul_le i X hC j (hcolbd j) o
    rw [hsplit]
    have h3 : |X o j - (avgProj i * X) o j| ≤ 2 * C := by
      calc |X o j - (avgProj i * X) o j| ≤ |X o j| + |(avgProj i * X) o j| := abs_sub _ _
        _ ≤ C + C := add_le_add h1 h2
        _ = 2 * C := by ring
    nlinarith [abs_nonneg (X o j - (avgProj i * X) o j),
      sq_abs (X o j - (avgProj i * X) o j)]
  calc rowNormSq (((1 : Matrix O O ℝ) - avgProj i) * X) o ≤ ∑ _j : ι, 4 * C ^ 2 :=
        Finset.sum_le_sum fun j _ => hentry j
    _ = 4 * (Fintype.card ι : ℝ) * C ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

end ClauseA

/-! ### Convergence in probability is closed under finite sums -/

section InProbSum

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A constant sequence converges in probability to that constant. -/
theorem tendstoInProb_const (a : ℝ) :
    TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => a) atTop (fun _ => a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hnull : ∀ n : ℕ, P {ω | ε ≤ dist ((fun (_ : ℕ) (_ : Ω) => a) n ω) a} = 0 := by
    intro n
    convert measure_empty (μ := P)
    ext ω
    simp only [Set.mem_ofPred_eq, dist_self, Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  have heq : (fun n : ℕ => P {ω | ε ≤ dist ((fun (_ : ℕ) (_ : Ω) => a) n ω) a})
      = fun _ : ℕ => (0 : ℝ≥0∞) := funext hnull
  rw [heq]
  exact tendsto_const_nhds

/-- Convergence in probability is closed under addition. -/
theorem tendstoInProb_add {Z W : ℕ → Ω → ℝ} {a c : ℝ}
    (hZ : TendstoInMeasure P Z atTop (fun _ => a))
    (hW : TendstoInMeasure P W atTop (fun _ => c)) :
    TendstoInMeasure P (fun n ω => Z n ω + W n ω) atTop (fun _ => a + c) := by
  rw [tendstoInMeasure_iff_dist] at hZ hW ⊢
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  have hsum : Tendsto (fun n => P {ω | ε / 2 ≤ dist (Z n ω) a}
      + P {ω | ε / 2 ≤ dist (W n ω) c}) atTop (𝓝 0) := by
    simpa using (hZ (ε / 2) hhalf).add (hW (ε / 2) hhalf)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  refine le_trans (measure_mono (fun ω hω => ?_)) (measure_union_le _ _)
  simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  have h1 : |Z n ω + W n ω - (a + c)| ≤ |Z n ω - a| + |W n ω - c| := by
    have : Z n ω + W n ω - (a + c) = (Z n ω - a) + (W n ω - c) := by ring
    rw [this]; exact abs_add_le _ _
  linarith [hcon.1, hcon.2]

/-- Convergence in probability is closed under a `Finset` sum. -/
theorem tendstoInProb_finsetSum {α : Type*} (s : Finset α) {Z : α → ℕ → Ω → ℝ} {c : α → ℝ}
    (h : ∀ a ∈ s, TendstoInMeasure P (Z a) atTop (fun _ => c a)) :
    TendstoInMeasure P (fun n ω => ∑ a ∈ s, Z a n ω) atTop (fun _ => ∑ a ∈ s, c a) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using tendstoInProb_const (P := P) (0 : ℝ)
  | insert a s ha ih =>
      have hmem : ∀ b ∈ s, TendstoInMeasure P (Z b) atTop (fun _ => c b) :=
        fun b hb => h b (Finset.mem_insert_of_mem hb)
      have hA : TendstoInMeasure P (Z a) atTop (fun _ => c a) := h a (Finset.mem_insert_self a s)
      have := tendstoInProb_add hA (ih hmem)
      simpa [Finset.sum_insert ha] using this

/-- Entrywise convergence in probability of the diagonal gives convergence of the trace. -/
theorem tendstoInProb_trace {ι : Type*} [Fintype ι] {A : ℕ → Ω → Matrix ι ι ℝ}
    {H : Matrix ι ι ℝ} (h : ∀ j, TendstoInMeasure P (fun n ω => A n ω j j) atTop (fun _ => H j j)) :
    TendstoInMeasure P (fun n ω => (A n ω).trace) atTop (fun _ => H.trace) := by
  simpa [Matrix.trace, Matrix.diag] using
    tendstoInProb_finsetSum (P := P) (Finset.univ : Finset ι)
      (Z := fun j n ω => A n ω j j) (c := fun j => H j j) (fun j _ => h j)

end InProbSum

/-! ### The `O_p(1/n)` half of clause (a) -/

section BigO

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `max_o ‖x̃_o‖² / ∑_o ‖x̃_o‖² = O_p(1/n)`, in the eventual form: there is `c` such that the
bound holds with high probability for all sufficiently large `n`. -/
theorem bigO_leverageRatio
    {O : ℕ → Type*} [∀ n, Fintype (O n)] {ι : Type*} [Fintype ι]
    {Xt : ∀ n, Ω → Matrix (O n) ι ℝ} {b t : ℝ} {T : ℕ → Ω → ℝ} (ht : 0 < t) (hb0 : 0 ≤ b)
    (hnum : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ∀ o, rowNormSq (Xt n ω) o ≤ b)
    (hden : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, sumRowNormSq (Xt n ω) = (n : ℝ) * T n ω)
    (hT : TendstoInMeasure P T atTop (fun _ => t)) :
    ∀ δ : ℝ≥0∞, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      P {ω | c ≤ (n : ℝ) * leverageRatio (Xt n ω)} ≤ δ := by
  intro δ hδ
  refine ⟨2 * b / t + 1, by positivity, ?_⟩
  have hhalf : (0 : ℝ) < t / 2 := by linarith
  have hTsmall : ∀ᶠ n in atTop, P {ω | t / 2 ≤ dist (T n ω) t} ≤ δ :=
    (ENNReal.tendsto_nhds_zero.mp ((tendstoInMeasure_iff_dist.mp hT) (t / 2) hhalf)) δ hδ
  have hn1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast hn
  filter_upwards [hTsmall, hn1, hnum, hden] with n hTn hn hrow hsum
  refine le_trans (measure_mono_ae ?_) hTn
  filter_upwards [hrow, hsum] with ω hrow' hsum' hmem
  show t / 2 ≤ dist (T n ω) t
  rw [Real.dist_eq]
  by_contra hcon
  rw [not_le] at hcon
  have hTlow : t / 2 < T n ω := by
    have h2 := abs_lt.mp (hcon : |T n ω - t| < t / 2)
    linarith [h2.1]
  have hpos : 0 < sumRowNormSq (Xt n ω) := by rw [hsum']; nlinarith
  have hmax : maxRowNormSq (Xt n ω) ≤ b := maxRowNormSq_le hb0 hrow'
  have hle : (n : ℝ) * leverageRatio (Xt n ω) ≤ b / T n ω := by
    have h1 : leverageRatio (Xt n ω) ≤ b / sumRowNormSq (Xt n ω) := by
      unfold leverageRatio; gcongr
    have h2 : (n : ℝ) * leverageRatio (Xt n ω) ≤ (n : ℝ) * (b / sumRowNormSq (Xt n ω)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have hnz : (n : ℝ) ≠ 0 := by linarith
    have h3 : (n : ℝ) * (b / sumRowNormSq (Xt n ω)) = b / T n ω := by
      rw [hsum']
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hbt : b / T n ω < 2 * b / t + 1 := by
    rcases eq_or_lt_of_le hb0 with hb | hb
    · rw [← hb]
      have : (0:ℝ) / T n ω = 0 := by simp
      rw [this]
      positivity
    · have h1 : b / T n ω < b / (t / 2) := by
        apply div_lt_div_of_pos_left hb (by linarith) hTlow
      have h2 : b / (t / 2) = 2 * b / t := by field_simp
      linarith
  have hmem' : 2 * b / t + 1 ≤ (n : ℝ) * leverageRatio (Xt n ω) := hmem
  linarith

end BigO

/-! ### Proposition SM.D.2 -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {ι : Type*} [Fintype ι]

/-- **Proposition SM.D.2(b).** For general `M`, the leverage ratio tends to `0` in probability
whenever `max_o (P_[Δ])_{oo} → 0`. -/
theorem leverage_clause_b [DecidableEq ι]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Pm : ∀ n, Ω → Matrix (O n) (O n) ℝ} {X : ∀ n, Ω → Matrix (O n) ι ℝ}
    {C trH : ℝ} {mx : ℕ → ℝ} (htrH : 0 < trH) (hmx0 : ∀ n, 0 ≤ mx n)
    (hsymm : ∀ n ω, (Pm n ω)ᵀ = Pm n ω) (hidem : ∀ n ω, Pm n ω * Pm n ω = Pm n ω)
    (hcard : ∀ᶠ n : ℕ in atTop, (Fintype.card (O n) : ℝ) = (n : ℝ))
    (hbdd : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P, ∀ o, rowNormSq (X n ω) o ≤ C ^ 2)
    (hdiag : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P, ∀ o, Pm n ω o o ≤ mx n)
    (hmx : Tendsto mx atTop (𝓝 0))
    (htr : TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹
        * ((X n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * X n ω).trace)
      atTop (fun _ => trH)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => leverageRatio (((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * X n ω))
      atTop (fun _ => (0 : ℝ)) := by
  have hK0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hn1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn; exact_mod_cast hn
  refine tendstoInProb_leverageRatio
    (b := fun n => 2 * (Fintype.card ι : ℝ) * C ^ 2 * (1 + (n : ℝ) * mx n))
    (T := fun (n : ℕ) ω => (n : ℝ)⁻¹
      * ((X n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - Pm n ω) * X n ω).trace)
    htrH (fun n => by
      have h1 : (0 : ℝ) ≤ (n : ℝ) * mx n := mul_nonneg (Nat.cast_nonneg n) (hmx0 n)
      exact mul_nonneg (by positivity) (by linarith)) ?_ ?_ ?_ htr
  · filter_upwards [hbdd, hdiag, hcard] with n hb hd hc
    filter_upwards [hb, hd] with ω hb' hd'
    intro o
    have := rowNormSq_within_le_of_diag (hsymm n ω) (hidem n ω) hb' hd' o
    rwa [hc] at this
  · have hlim : Tendsto (fun n : ℕ => 2 * (Fintype.card ι : ℝ) * C ^ 2 / (n : ℝ)
        + 2 * (Fintype.card ι : ℝ) * C ^ 2 * mx n) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 2 * (Fintype.card ι : ℝ) * C ^ 2 / (n : ℝ))
          atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
      have h2 : Tendsto (fun n : ℕ => 2 * (Fintype.card ι : ℝ) * C ^ 2 * mx n)
          atTop (𝓝 0) := by
        simpa using hmx.const_mul (2 * (Fintype.card ι : ℝ) * C ^ 2)
      simpa using h1.add h2
    refine hlim.congr' ?_
    filter_upwards [hn1] with n hn
    have hnz : (n : ℝ) ≠ 0 := by linarith
    field_simp
  · filter_upwards [hn1] with n hn
    have hnz : (n : ℝ) ≠ 0 := by linarith
    filter_upwards with ω
    exact sumRowNormSq_eq_card_mul (X n ω) (hsymm n ω) (hidem n ω) hnz

/-- **Proposition SM.D.2(a).** At `M = 1`, the leverage ratio tends to `0` in probability. -/
theorem leverage_clause_a [DecidableEq ι]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {N : ℕ → Type*} [∀ n, DecidableEq (N n)]
    {idx : ∀ n, Ω → O n → N n} {X : ∀ n, Ω → Matrix (O n) ι ℝ}
    {C trH : ℝ} (hC : 0 ≤ C) (htrH : 0 < trH)
    (hbdd : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P, ∀ o, rowNormSq (X n ω) o ≤ C ^ 2)
    (htr : TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹
        * ((X n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - avgProj (idx n ω)) * X n ω).trace)
      atTop (fun _ => trH)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => leverageRatio (((1 : Matrix (O n) (O n) ℝ) - avgProj (idx n ω)) * X n ω))
      atTop (fun _ => (0 : ℝ)) := by
  have hn1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn; exact_mod_cast hn
  refine tendstoInProb_leverageRatio (b := fun _ => 4 * (Fintype.card ι : ℝ) * C ^ 2)
    (T := fun (n : ℕ) ω => (n : ℝ)⁻¹
      * ((X n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - avgProj (idx n ω)) * X n ω).trace)
    htrH (fun n => by positivity) ?_ ?_ ?_ htr
  · filter_upwards [hbdd] with n hb
    filter_upwards [hb] with ω hb'
    exact fun o => rowNormSq_within_avgProj_le (idx n ω) (X n ω) hC hb' o
  · exact tendsto_const_div_atTop_nhds_zero_nat _
  · filter_upwards [hn1] with n hn
    have hnz : (n : ℝ) ≠ 0 := by linarith
    filter_upwards with ω
    exact sumRowNormSq_eq_card_mul (X n ω)
      (avgProj_transpose (idx n ω)) (avgProj_mul_self (idx n ω)) hnz

/-- **Proposition SM.D.2(a)**, second sentence: at `M = 1`, the leverage ratio is `O_p(1/n)`. -/
theorem leverage_clause_a_bigO [DecidableEq ι]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {N : ℕ → Type*} [∀ n, DecidableEq (N n)]
    {idx : ∀ n, Ω → O n → N n} {X : ∀ n, Ω → Matrix (O n) ι ℝ}
    {C trH : ℝ} (hC : 0 ≤ C) (htrH : 0 < trH)
    (hbdd : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P, ∀ o, rowNormSq (X n ω) o ≤ C ^ 2)
    (htr : TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹
        * ((X n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - avgProj (idx n ω)) * X n ω).trace)
      atTop (fun _ => trH)) :
    ∀ δ : ℝ≥0∞, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      P {ω | c ≤ (n : ℝ)
        * leverageRatio (((1 : Matrix (O n) (O n) ℝ) - avgProj (idx n ω)) * X n ω)} ≤ δ := by
  have hn1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn; exact_mod_cast hn
  refine bigO_leverageRatio (b := 4 * (Fintype.card ι : ℝ) * C ^ 2)
    (T := fun (n : ℕ) ω => (n : ℝ)⁻¹
      * ((X n ω)ᵀ * ((1 : Matrix (O n) (O n) ℝ) - avgProj (idx n ω)) * X n ω).trace)
    htrH (by positivity) ?_ ?_ htr
  · filter_upwards [hbdd] with n hb
    filter_upwards [hb] with ω hb'
    exact fun o => rowNormSq_within_avgProj_le (idx n ω) (X n ω) hC hb' o
  · filter_upwards [hn1] with n hn
    have hnz : (n : ℝ) ≠ 0 := by linarith
    filter_upwards with ω
    exact sumRowNormSq_eq_card_mul (X n ω)
      (avgProj_transpose (idx n ω)) (avgProj_mul_self (idx n ω)) hnz

end Main

/-! ### Witnesses -/

section Witness

/-- A sequence eventually equal to a constant converges to it in probability. -/
theorem tendstoInProb_of_eventually_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℕ → Ω → ℝ} {a : ℝ} (h : ∀ᶠ n : ℕ in atTop, ∀ ω, Z n ω = a) :
    TendstoInMeasure P Z atTop (fun _ => a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  filter_upwards [h] with n hn
  have hempty : {ω | ε ≤ dist (Z n ω) a} = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, hn ω, dist_self]
    exact hε
  rw [hempty, measure_empty]
  exact zero_le

/-- The witness design for clause (a): `2n` observations in one category and one regressor
taking the values `±1` in balanced pairs, so that the within transformation is the identity. -/
noncomputable def witnessX (n : ℕ) : Unit → Matrix (Fin n × Fin 2) (Fin 1) ℝ :=
  fun _ o _ => if o.2 = 0 then 1 else -1

/-- The single category of the witness design. -/
def witnessIdx (n : ℕ) : Unit → (Fin n × Fin 2) → Fin 1 := fun _ _ => 0

theorem witness_rowNormSq (n : ℕ) (o : Fin n × Fin 2) :
    rowNormSq (witnessX n ()) o = 1 := by
  simp only [rowNormSq, witnessX, Fin.sum_univ_one]
  by_cases h : o.2 = 0 <;> simp [h]

theorem witness_sum_zero (n : ℕ) : ∑ o : Fin n × Fin 2, witnessX n () o 0 = 0 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [witnessX, Fin.sum_univ_two]

theorem witness_avgProj_mul (n : ℕ) :
    avgProj (witnessIdx n ()) * witnessX n () = 0 := by
  ext o j
  rw [avgProj_mul_apply]
  have hfib : fibre (witnessIdx n ()) (witnessIdx n () o) = Finset.univ := by
    ext o'; simp [fibre, witnessIdx]
  have hj : j = 0 := Subsingleton.elim _ _
  rw [hfib, hj, ← Finset.sum_coe_sort]
  simp [witness_sum_zero n, Finset.sum_attach Finset.univ (fun o' => witnessX n () o' 0)]

theorem witness_within (n : ℕ) :
    ((1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) - avgProj (witnessIdx n ()))
      * witnessX n () = witnessX n () := by
  rw [Matrix.sub_mul, Matrix.one_mul, witness_avgProj_mul, sub_zero]

theorem witness_sumRowNormSq (n : ℕ) : sumRowNormSq (witnessX n ()) = 2 * (n : ℝ) := by
  rw [sumRowNormSq]
  simp only [witness_rowNormSq]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  push_cast; ring

/-- A model of the hypotheses of `leverage_clause_a`, with `tr(H) = 2`. -/
theorem leverage_clause_a_witness :
    TendstoInMeasure (Measure.dirac ()) (fun (n : ℕ) (ω : Unit) =>
      leverageRatio (((1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
        - avgProj (witnessIdx n ω)) * witnessX n ω)) atTop (fun _ => (0 : ℝ)) := by
  refine leverage_clause_a (C := 1) (trH := 2) zero_le_one (by norm_num)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω o => ?_) ?_
  · cases ω; simp [witness_rowNormSq]
  · refine tendstoInProb_of_eventually_eq ?_
    filter_upwards [eventually_ge_atTop 1] with n hn ω
    cases ω
    have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 : ((witnessX n ())ᵀ * ((1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
        - avgProj (witnessIdx n ())) * witnessX n ()).trace
        = sumRowNormSq (((1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
          - avgProj (witnessIdx n ())) * witnessX n ()) := by
      rw [sumRowNormSq_within_eq_trace _ _
        (compl_transpose (avgProj_transpose (witnessIdx n ())))
        (compl_mul_self (avgProj_mul_self (witnessIdx n ())))]
    rw [h1, witness_within, witness_sumRowNormSq]
    field_simp

/-- On the clause (a) witness the leverage ratio equals `1/(2n)` for every `n ≥ 1`. -/
theorem leverage_clause_a_witness_ratio {n : ℕ} (hn : 1 ≤ n) :
    leverageRatio (((1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
      - avgProj (witnessIdx n ())) * witnessX n ()) = 1 / (2 * (n : ℝ)) := by
  have : Nonempty (Fin n × Fin 2) := ⟨⟨⟨0, by omega⟩, 0⟩⟩
  rw [witness_within, leverageRatio, witness_sumRowNormSq, maxRowNormSq]
  simp only [witness_rowNormSq, ciSup_const]

/-- The witness design for clause (b): `n` observations, one regressor equal to `1`, and
`P_[Δ] = 0`. -/
noncomputable def witnessXb (n : ℕ) : Unit → Matrix (Fin n) (Fin 1) ℝ := fun _ _ _ => 1

theorem witnessXb_rowNormSq (n : ℕ) (o : Fin n) : rowNormSq (witnessXb n ()) o = 1 := by
  simp [rowNormSq, witnessXb]

theorem witnessXb_sumRowNormSq (n : ℕ) : sumRowNormSq (witnessXb n ()) = (n : ℝ) := by
  rw [sumRowNormSq]
  simp only [witnessXb_rowNormSq]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin, mul_one]

/-- A model of the hypotheses of `leverage_clause_b`, with `tr(H) = 1`. -/
theorem leverage_clause_b_witness :
    TendstoInMeasure (Measure.dirac ()) (fun (n : ℕ) (ω : Unit) =>
      leverageRatio (((1 : Matrix (Fin n) (Fin n) ℝ) - (0 : Matrix (Fin n) (Fin n) ℝ))
        * witnessXb n ω)) atTop (fun _ => (0 : ℝ)) := by
  refine leverage_clause_b (C := 1) (trH := 1) (mx := fun _ => 0) (by norm_num)
    (fun _ => le_refl 0) (fun n ω => Matrix.transpose_zero) (fun n ω => by simp)
    (Filter.Eventually.of_forall fun n => by simp)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω o => ?_)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω o => le_refl 0)
    tendsto_const_nhds ?_
  · cases ω; simp [witnessXb_rowNormSq]
  · refine tendstoInProb_of_eventually_eq ?_
    filter_upwards [eventually_ge_atTop 1] with n hn ω
    cases ω
    have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 : ((witnessXb n ())ᵀ * ((1 : Matrix (Fin n) (Fin n) ℝ)
        - (0 : Matrix (Fin n) (Fin n) ℝ)) * witnessXb n ()).trace
        = sumRowNormSq (((1 : Matrix (Fin n) (Fin n) ℝ)
          - (0 : Matrix (Fin n) (Fin n) ℝ)) * witnessXb n ()) := by
      rw [sumRowNormSq_within_eq_trace _ _ (compl_transpose Matrix.transpose_zero)
        (compl_mul_self (by simp))]
    rw [h1, sub_zero, Matrix.one_mul, witnessXb_sumRowNormSq]
    field_simp

/-- On the clause (b) witness the leverage ratio equals `1/n` for every `n ≥ 1`. -/
theorem leverage_clause_b_witness_ratio {n : ℕ} (hn : 1 ≤ n) :
    leverageRatio (((1 : Matrix (Fin n) (Fin n) ℝ) - (0 : Matrix (Fin n) (Fin n) ℝ))
      * witnessXb n ()) = 1 / (n : ℝ) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [sub_zero, Matrix.one_mul, leverageRatio, witnessXb_sumRowNormSq, maxRowNormSq]
  simp only [witnessXb_rowNormSq, ciSup_const]

end Witness

end SuffLeverage

end Multiway
