import Multiway.Leverage
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Conditional leverage identities and the exact leverage correction

This file formalizes the conditional clauses of Lemma SM.B.6 (residual representation and exact
leverage identity) and Proposition SM.D.4 (exact leverage correction). Under the Regime 1
dependence assumption, `Rν = Rε`, `E[ν̂²_{FE,o} | 𝒟] = ∑_{o'} R²_{oo'} σ²_ε(o')`
`= R_oo σ²_ε(o) + ∑_{o'≠o} R²_{oo'}(σ²_ε(o') - σ²_ε(o))`, and under homoskedasticity
`E[M̂_W | 𝒟] = σ²_ε ∑_o x̃_o x̃_o' R_oo`. The probabilistic input enters
through the hypothesis `hcross`, `E[ε_o ε_{o'} | 𝒟] = 𝟙{o = o'} σ²_ε(o)`, and `R` is a
deterministic operator.

## Notation

* `O` is the support and `EuclideanSpace ℝ O` is `ℝⁿ`;
* `opEntry R o o'` is `R_{oo'}`, and `R (epsv ω) o` is `ν̂_{FE,o}`;
* `sig o` is the variance `σ²_ε(o)`, and `w o` is an entry of `x̃_o x̃_o'`, so the estimators
  `M̂_W` and `M̂^{LC}` are treated entry by entry.

## Main results

* `residualMaker_apply_of_regimeOne`: `Rν = Rε`, an identity in every realization.
* `sum_opEntry_sq`: `∑_{o'} R²_{oo'} = R_oo` for self-adjoint idempotent `R`.
* `condExp_feResidual_sq`, `condExp_feResidual_sq_leverage`, `condExp_meatW`: Lemma SM.B.6.
* `condExp_meatLC_sub_meat`, `condExp_meatLC_of_homoskedastic`: Proposition SM.D.4(a) and (b).
-/

namespace Multiway
namespace LeverageCond

open MeasureTheory

open scoped RealInnerProductSpace

/-! ## The identity `Rν = Rε` -/

section RegimeOne

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} {S : Submodule ℝ E} {x : ι → E}

/-- **Lemma SM.B.6**, first clause: if `ν = ∑_m Δ_m a^{(m)} + ε` with each `a m` in the joint
fixed-effects space `𝒮`, then `Rν = Rε`. -/
theorem residualMaker_apply_of_regimeOne {D : Type*} {dims : Finset D} {a : D → E} {ν ε : E}
    (ha : ∀ m ∈ dims, a m ∈ S) (hν : ν = (∑ m ∈ dims, a m) + ε) :
    residualMaker S x ν = residualMaker S x ε := by
  rw [hν, map_add, map_sum,
    Finset.sum_eq_zero fun m hm => residualMaker_apply_of_mem_fixedEffects (ha m hm), zero_add]

/-- `Rν = Rε` pointwise in `ω`, for a random disturbance. -/
theorem residualMaker_apply_of_regimeOne_pointwise {D Ω : Type*} {dims : Finset D}
    {a : D → Ω → E} {ν ε : Ω → E}
    (ha : ∀ m ∈ dims, ∀ ω, a m ω ∈ S) (hν : ∀ ω, ν ω = (∑ m ∈ dims, a m ω) + ε ω) (ω : Ω) :
    residualMaker S x (ν ω) = residualMaker S x (ε ω) :=
  residualMaker_apply_of_regimeOne (fun m hm => ha m hm ω) (hν ω)

/-- Under the model and the Regime 1 decomposition, the fixed-effects residual sees only the
idiosyncratic component: `ν̂_FE = Rε`. -/
theorem feResidual_eq_residualMaker_idiosyncratic [Fintype ι] {D : Type*} {dims : Finset D}
    {a : D → E} {y c ν ε : E} {β b : ι → ℝ} (hc : c ∈ S)
    (hy : y = (∑ k, β k • x k) + c + ν)
    (hb : ∀ k, ⟪withinRegressor S x k, y - ∑ j, b j • x j⟫ = 0)
    (ha : ∀ m ∈ dims, a m ∈ S) (hν : ν = (∑ m ∈ dims, a m) + ε) :
    Sᗮ.starProjection (y - ∑ j, b j • x j) = residualMaker S x ε :=
  (feResidual_eq_residualMaker_apply hc hy hb).trans (residualMaker_apply_of_regimeOne ha hν)

end RegimeOne

/-! ## The entries `R_{oo'}`, and `∑_{o'} R²_{oo'} = R_oo` -/

section Entries

variable {O : Type*} [Fintype O] [DecidableEq O]

omit [DecidableEq O] in
/-- The inner product of `EuclideanSpace ℝ O` written coordinatewise. -/
theorem inner_eucl (z z' : EuclideanSpace ℝ O) : ⟪z, z'⟫ = ∑ o : O, z o * z' o := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun o _ => mul_comm _ _

omit [Fintype O] [DecidableEq O] in
/-- A `Finset` sum of vectors of `EuclideanSpace ℝ O` is evaluated coordinatewise. -/
theorem euclSum_apply {κ : Type*} (s : Finset κ) (F : κ → EuclideanSpace ℝ O) (o : O) :
    (∑ i ∈ s, F i) o = ∑ i ∈ s, (F i) o :=
  map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (β := fun _ : O => ℝ) o) F s

/-- A coordinate of a vector is an inner product against a standard basis vector. -/
theorem coord_eq_inner_single (z : EuclideanSpace ℝ O) (o : O) :
    z o = ⟪z, EuclideanSpace.single o (1 : ℝ)⟫ := by
  rw [EuclideanSpace.inner_single_right]
  simp

/-- Every vector is the combination of the standard basis vectors given by its coordinates. -/
theorem eq_sum_single (z : EuclideanSpace ℝ O) :
    z = ∑ o' : O, z o' • EuclideanSpace.single o' (1 : ℝ) := by
  ext o
  rw [euclSum_apply]
  simp

/-- The entry `R_{oo'}` of an operator on `EuclideanSpace ℝ O`: the `o`-th coordinate of its
value at the `o'`-th standard basis vector. -/
noncomputable def opEntry (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O) (o o' : O) : ℝ :=
  R (EuclideanSpace.single o' (1 : ℝ)) o

/-- `R_{oo'} = ⟪R e_{o'}, e_o⟫`, the form the symmetry step uses. -/
theorem opEntry_eq_inner (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O) (o o' : O) :
    opEntry R o o' = ⟪R (EuclideanSpace.single o' (1 : ℝ)), EuclideanSpace.single o (1 : ℝ)⟫ :=
  coord_eq_inner_single _ _

/-- `ν̂_{FE,o} = ∑_{o'} R_{oo'} ε_{o'}`: the coordinate expansion of a continuous linear map on
`EuclideanSpace ℝ O`. -/
theorem apply_eq_sum_opEntry (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O)
    (z : EuclideanSpace ℝ O) (o : O) : R z o = ∑ o' : O, opEntry R o o' * z o' := by
  conv_lhs => rw [eq_sum_single z]
  rw [map_sum, euclSum_apply]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [map_smul, PiLp.smul_apply, smul_eq_mul, opEntry, mul_comm]

/-- Symmetry of `R` read on the entries: `R_{oo'}` is the `o'`-th coordinate of `R e_o`. -/
theorem opEntry_comm {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫) (o o' : O) :
    opEntry R o o' = R (EuclideanSpace.single o (1 : ℝ)) o' := by
  rw [opEntry_eq_inner, hsym, real_inner_comm, ← coord_eq_inner_single]

/-- `∑_{o'} R²_{oo'} = (R²)_{oo} = R_{oo}`, from self-adjointness and idempotence. -/
theorem sum_opEntry_sq {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u) (o : O) :
    ∑ o' : O, opEntry R o o' ^ 2 = opEntry R o o := by
  have hstep : ∀ o' : O, opEntry R o o' ^ 2
      = R (EuclideanSpace.single o (1 : ℝ)) o' * R (EuclideanSpace.single o (1 : ℝ)) o' := by
    intro o'
    rw [opEntry_comm hsym o o', sq]
  calc ∑ o' : O, opEntry R o o' ^ 2
      = ∑ o' : O, R (EuclideanSpace.single o (1 : ℝ)) o'
          * R (EuclideanSpace.single o (1 : ℝ)) o' := Finset.sum_congr rfl fun o' _ => hstep o'
    _ = ⟪R (EuclideanSpace.single o (1 : ℝ)), R (EuclideanSpace.single o (1 : ℝ))⟫ :=
        (inner_eucl _ _).symm
    _ = ⟪EuclideanSpace.single o (1 : ℝ), R (R (EuclideanSpace.single o (1 : ℝ)))⟫ := hsym _ _
    _ = ⟪EuclideanSpace.single o (1 : ℝ), R (EuclideanSpace.single o (1 : ℝ))⟫ := by rw [hidem]
    _ = ⟪R (EuclideanSpace.single o (1 : ℝ)), EuclideanSpace.single o (1 : ℝ)⟫ :=
        real_inner_comm _ _
    _ = opEntry R o o := (coord_eq_inner_single _ _).symm

/-- `∑_{o'} R²_{oo'} = R_{oo}` for the residual maker. -/
theorem sum_opEntry_sq_residualMaker {ι : Type*} (S : Submodule ℝ (EuclideanSpace ℝ O))
    (x : ι → EuclideanSpace ℝ O) (o : O) :
    ∑ o' : O, opEntry (residualMaker S x) o o' ^ 2 = opEntry (residualMaker S x) o o :=
  sum_opEntry_sq (inner_residualMaker_left_eq_right S x)
    (fun u => by
      have h := residualMaker_isIdempotentElem S x
      have h' := congrArg
        (fun T : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O => T u) h
      simpa using h') o

/-- If the squared entries of a row sum to `d`, a weighted row sum splits into its diagonal
part and the deviations of the weights from the diagonal one. -/
theorem sum_sq_split {a : O → ℝ} {d : ℝ} (ha : ∑ o' : O, a o' ^ 2 = d) (t : O → ℝ) (o : O) :
    ∑ o' : O, a o' ^ 2 * t o'
      = d * t o + ∑ o' ∈ Finset.univ.erase o, a o' ^ 2 * (t o' - t o) := by
  have herase : ∑ o' ∈ Finset.univ.erase o, a o' ^ 2 * (t o' - t o)
      = ∑ o' : O, a o' ^ 2 * (t o' - t o) := Finset.sum_erase _ (by simp)
  rw [herase]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ha]
  ring

end Entries

/-! ## Conditional moments of the residuals -/

section Conditional

variable {O : Type*} [Fintype O] [DecidableEq O]
-- `𝒟` is declared before the ambient `mΩ`, so that `mΩ` is found by instance synthesis.
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [DecidableEq O] in
/-- The square of a linear combination, expanded into the double sum the conditional
expectation is taken over term by term. -/
theorem sq_sum_eq_double_sum (c eps : O → Ω → ℝ) :
    (fun ω => (∑ o' : O, c o' ω * eps o' ω) ^ 2)
      = ∑ o' : O, ∑ o'' : O,
          (fun ω => (c o' ω * c o'' ω) * (eps o' ω * eps o'' ω)) := by
  funext ω
  simp only [Finset.sum_apply]
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun o' _ => Finset.sum_congr rfl fun o'' _ => by ring

/-- `E[(∑_{o'} c_{o'} ε_{o'})² | 𝒟] = ∑_{o'} c²_{o'} σ²_ε(o')` for arbitrary `𝒟`-measurable
coefficients, given `hcross`: `E[ε_{o'} ε_{o''} | 𝒟] = 𝟙{o' = o''} σ²_ε(o')`. -/
theorem condExp_sq_linearCombination {c eps sig : O → Ω → ℝ}
    (hc : ∀ o', StronglyMeasurable[𝒟] (c o'))
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hint' : ∀ o' o'', Integrable (fun ω => (c o' ω * c o'' ω) * (eps o' ω * eps o'' ω)) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0) :
    μ[fun ω => (∑ o' : O, c o' ω * eps o' ω) ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ o' : O, c o' ω ^ 2 * sig o' ω := by
  classical
  rw [sq_sum_eq_double_sum c eps]
  have h1 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
    (f := fun o' : O => ∑ o'' : O, (fun ω => (c o' ω * c o'' ω) * (eps o' ω * eps o'' ω)))
    (fun o' _ => integrable_finsetSum' _ fun o'' _ => hint' o' o'') 𝒟
  have h2 : ∀ᵐ ω ∂μ, ∀ o' : O,
      μ[∑ o'' : O, (fun ω => (c o' ω * c o'' ω) * (eps o' ω * eps o'' ω)) | 𝒟] ω
        = ∑ o'' : O, μ[fun ω => (c o' ω * c o'' ω) * (eps o' ω * eps o'' ω) | 𝒟] ω := by
    refine ae_all_iff.2 fun o' => ?_
    filter_upwards [condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
      (fun o'' _ => hint' o' o'') 𝒟] with ω hω
    rw [hω, Finset.sum_apply]
  have hpull : ∀ o' o'' : O,
      μ[fun ω => (c o' ω * c o'' ω) * (eps o' ω * eps o'' ω) | 𝒟]
        =ᵐ[μ] fun ω => (c o' ω * c o'' ω) * μ[fun ω => eps o' ω * eps o'' ω | 𝒟] ω :=
    fun o' o'' =>
      condExp_mul_of_stronglyMeasurable_left ((hc o').mul (hc o'')) (hint' o' o'') (hint o' o'')
  have h3 : ∀ᵐ ω ∂μ, ∀ q : O × O,
      μ[fun ω => (c q.1 ω * c q.2 ω) * (eps q.1 ω * eps q.2 ω) | 𝒟] ω
        = (c q.1 ω * c q.2 ω) * (if q.1 = q.2 then sig q.1 ω else 0) := by
    refine ae_all_iff.2 fun q => ?_
    filter_upwards [hpull q.1 q.2, hcross q.1 q.2] with ω ha hb
    rw [ha, hb]
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, Finset.sum_apply]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [e2 o']
  have hterm : ∀ o'' ∈ (Finset.univ : Finset O),
      μ[fun ω => (c o' ω * c o'' ω) * (eps o' ω * eps o'' ω) | 𝒟] ω
        = (c o' ω * c o'' ω) * (if o' = o'' then sig o' ω else 0) :=
    fun o'' _ => e3 (o', o'')
  rw [Finset.sum_congr rfl hterm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- The square of a residual coordinate is integrable as soon as the products `ε_{o'} ε_{o''}`
are: it is a finite combination of them with constant coefficients. -/
theorem integrable_feResidual_sq (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O)
    {epsv : Ω → EuclideanSpace ℝ O}
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ) (o : O) :
    Integrable (fun ω => R (epsv ω) o ^ 2) μ := by
  have hrw : (fun ω => R (epsv ω) o ^ 2)
      = ∑ o' : O, ∑ o'' : O,
          (fun ω => (opEntry R o o' * opEntry R o o'') * (epsv ω o' * epsv ω o'')) := by
    simp only [apply_eq_sum_opEntry]
    exact sq_sum_eq_double_sum (fun o' _ => opEntry R o o') (fun o' ω => epsv ω o')
  rw [hrw]
  exact integrable_finsetSum' _ fun o' _ =>
    integrable_finsetSum' _ fun o'' _ => (hint o' o'').const_mul _

/-- **Lemma SM.B.6**, first form: `E[ν̂²_{FE,o} | 𝒟] = ∑_{o'} R²_{oo'} σ²_ε(o')`. -/
theorem condExp_feResidual_sq (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O)
    {epsv : Ω → EuclideanSpace ℝ O} {sig : O → Ω → ℝ}
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hcross : ∀ o' o'', μ[fun ω => epsv ω o' * epsv ω o'' | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0) (o : O) :
    μ[fun ω => R (epsv ω) o ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ o' : O, opEntry R o o' ^ 2 * sig o' ω := by
  simp only [apply_eq_sum_opEntry]
  exact condExp_sq_linearCombination 𝒟 (c := fun o' _ => opEntry R o o')
    (eps := fun o' ω => epsv ω o') (fun _ => stronglyMeasurable_const) hint
    (fun o' o'' => (hint o' o'').const_mul _) hcross

/-- **Lemma SM.B.6**, second form:
`E[ν̂²_{FE,o} | 𝒟] = R_oo σ²_ε(o) + ∑_{o'≠o} R²_{oo'}(σ²_ε(o') - σ²_ε(o))`. -/
theorem condExp_feResidual_sq_leverage {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    {epsv : Ω → EuclideanSpace ℝ O} {sig : O → Ω → ℝ}
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hcross : ∀ o' o'', μ[fun ω => epsv ω o' * epsv ω o'' | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0) (o : O) :
    μ[fun ω => R (epsv ω) o ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => opEntry R o o * sig o ω
        + ∑ o' ∈ Finset.univ.erase o, opEntry R o o' ^ 2 * (sig o' ω - sig o ω) := by
  filter_upwards [condExp_feResidual_sq 𝒟 R hint hcross o] with ω hω
  rw [hω]
  exact sum_sq_split (sum_opEntry_sq hsym hidem o) (fun o' => sig o' ω) o

/-- `E[∑_o w_o ν̂²_{FE,o} | 𝒟] = ∑_o w_o ∑_{o'} R²_{oo'} σ²_ε(o')` for an arbitrary
`𝒟`-measurable weight `w_o`. At `w_o = x̃_{oj} x̃_{ok}` this is entry `(j,k)` of `M̂_W`, and at
`w_o = x̃_{oj} x̃_{ok}/R_oo` entry `(j,k)` of `M̂^{LC}`. -/
theorem condExp_weighted_feResidual_sq (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O)
    {epsv : Ω → EuclideanSpace ℝ O} {sig w : O → Ω → ℝ}
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hcross : ∀ o' o'', μ[fun ω => epsv ω o' * epsv ω o'' | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0)
    (hintw : ∀ o, Integrable (fun ω => w o ω * R (epsv ω) o ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * R (epsv ω) o ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, w o ω * ∑ o' : O, opEntry R o o' ^ 2 * sig o' ω := by
  have hrw : (fun ω => ∑ o : O, w o ω * R (epsv ω) o ^ 2)
      = ∑ o : O, (fun ω => w o ω * R (epsv ω) o ^ 2) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hrw]
  have h1 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
    (fun o _ => hintw o) 𝒟
  have h2 : ∀ᵐ ω ∂μ, ∀ o : O, μ[fun ω => w o ω * R (epsv ω) o ^ 2 | 𝒟] ω
      = w o ω * μ[fun ω => R (epsv ω) o ^ 2 | 𝒟] ω :=
    ae_all_iff.2 fun o => condExp_mul_of_stronglyMeasurable_left (hw o) (hintw o)
      (integrable_feResidual_sq R hint o)
  have h3 : ∀ᵐ ω ∂μ, ∀ o : O, μ[fun ω => R (epsv ω) o ^ 2 | 𝒟] ω
      = ∑ o' : O, opEntry R o o' ^ 2 * sig o' ω :=
    ae_all_iff.2 fun o => condExp_feResidual_sq 𝒟 R hint hcross o
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun o _ => by rw [e2 o, e3 o]

/-- **Lemma SM.B.6**, homoskedastic case: with `σ²_ε(o) ≡ σ²_ε`,
`E[M̂_W | 𝒟] = σ²_ε ∑_o x̃_o x̃_o' R_oo`, entry by entry. -/
theorem condExp_meatW {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    {epsv : Ω → EuclideanSpace ℝ O} {sig w : O → Ω → ℝ} {s : Ω → ℝ}
    (hhom : ∀ o ω, sig o ω = s ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hcross : ∀ o' o'', μ[fun ω => epsv ω o' * epsv ω o'' | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0)
    (hintw : ∀ o, Integrable (fun ω => w o ω * R (epsv ω) o ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * R (epsv ω) o ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => s ω * ∑ o : O, w o ω * opEntry R o o := by
  filter_upwards [condExp_weighted_feResidual_sq 𝒟 R hw hint hcross hintw] with ω hω
  rw [hω, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hterm : ∀ o' ∈ (Finset.univ : Finset O),
      opEntry R o o' ^ 2 * sig o' ω = opEntry R o o' ^ 2 * s ω :=
    fun o' _ => by rw [hhom o' ω]
  have hinner : ∑ o' : O, opEntry R o o' ^ 2 * sig o' ω = s ω * opEntry R o o := by
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_opEntry_sq hsym hidem o, mul_comm]
  rw [hinner]
  ring

/-- **Proposition SM.D.4(a).** If `R_oo > 0` for every `o`, then
`E[M̂^{LC} | 𝒟] - M_n = ∑_o x̃_o x̃_o' R_oo^{-1} ∑_{o'≠o} R²_{oo'}(σ²_ε(o') - σ²_ε(o))`,
with `M_n = ∑_o x̃_o x̃_o' σ²_ε(o)`. -/
theorem condExp_meatLC_sub_meat {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    (hRpos : ∀ o : O, 0 < opEntry R o o)
    {epsv : Ω → EuclideanSpace ℝ O} {sig w : O → Ω → ℝ}
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hcross : ∀ o' o'', μ[fun ω => epsv ω o' * epsv ω o'' | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0)
    (hintw : ∀ o, Integrable (fun ω => w o ω / opEntry R o o * R (epsv ω) o ^ 2) μ) :
    (fun ω => μ[fun ω => ∑ o : O, w o ω * (R (epsv ω) o ^ 2 / opEntry R o o) | 𝒟] ω
        - ∑ o : O, w o ω * sig o ω)
      =ᵐ[μ] fun ω => ∑ o : O, w o ω / opEntry R o o
          * ∑ o' ∈ Finset.univ.erase o, opEntry R o o' ^ 2 * (sig o' ω - sig o ω) := by
  have hdiv : (fun ω => ∑ o : O, w o ω * (R (epsv ω) o ^ 2 / opEntry R o o))
      = fun ω => ∑ o : O, w o ω / opEntry R o o * R (epsv ω) o ^ 2 := by
    funext ω
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [mul_div_assoc']
    ring
  rw [hdiv]
  filter_upwards [condExp_weighted_feResidual_sq 𝒟 R
    (w := fun o ω => w o ω / opEntry R o o)
    (fun o => (hw o).div stronglyMeasurable_const) hint hcross hintw] with ω hω
  rw [hω, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hcancel : w o ω / opEntry R o o * (opEntry R o o * sig o ω) = w o ω * sig o ω := by
    rw [← mul_assoc, div_mul_cancel₀ _ (hRpos o).ne']
  rw [sum_sq_split (sum_opEntry_sq hsym hidem o) (fun o' => sig o' ω) o, mul_add, hcancel]
  ring

/-- **Proposition SM.D.4(b).** Under homoskedasticity `E[M̂^{LC} | 𝒟] = M_n`: the
leverage-corrected estimator is conditionally unbiased for the score variance. -/
theorem condExp_meatLC_of_homoskedastic {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    (hRpos : ∀ o : O, 0 < opEntry R o o)
    {epsv : Ω → EuclideanSpace ℝ O} {sig w : O → Ω → ℝ} {s : Ω → ℝ}
    (hhom : ∀ o ω, sig o ω = s ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hcross : ∀ o' o'', μ[fun ω => epsv ω o' * epsv ω o'' | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0)
    (hintw : ∀ o, Integrable (fun ω => w o ω / opEntry R o o * R (epsv ω) o ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * (R (epsv ω) o ^ 2 / opEntry R o o) | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, w o ω * sig o ω := by
  filter_upwards [condExp_meatLC_sub_meat 𝒟 hsym hidem hRpos hw hint hcross hintw] with ω hω
  have hzero : ∑ o : O, w o ω / opEntry R o o
      * ∑ o' ∈ Finset.univ.erase o, opEntry R o o' ^ 2 * (sig o' ω - sig o ω) = 0 := by
    refine Finset.sum_eq_zero fun o _ => ?_
    have : ∑ o' ∈ Finset.univ.erase o, opEntry R o o' ^ 2 * (sig o' ω - sig o ω) = 0 := by
      refine Finset.sum_eq_zero fun o' _ => ?_
      rw [hhom o' ω, hhom o ω, sub_self, mul_zero]
    rw [this, mul_zero]
  rw [hzero] at hω
  linarith [hω]

end Conditional

/-! ## Satisfiability of the hypotheses

Concrete models satisfying every hypothesis of the two claims of Proposition SM.D.4. -/

section Witness

open scoped RealInnerProductSpace

/-- The disturbance of both models: the standard basis vector at `o₀`, constant in `ω`. -/
theorem witness_cross {O : Type*} [Fintype O] [DecidableEq O] (o₀ : O) (o' o'' : O) :
    (Measure.dirac ())[fun _ : Unit =>
        (EuclideanSpace.single o₀ (1 : ℝ)) o' * (EuclideanSpace.single o₀ (1 : ℝ)) o''
        | (⊥ : MeasurableSpace Unit)]
      =ᵐ[Measure.dirac ()] fun _ : Unit =>
        if o' = o'' then (if o' = o₀ then (1 : ℝ) else 0) else 0 := by
  have hconst : (fun _ : Unit =>
      (EuclideanSpace.single o₀ (1 : ℝ)) o' * (EuclideanSpace.single o₀ (1 : ℝ)) o'')
      = fun _ : Unit => (if o' = o'' then (if o' = o₀ then (1 : ℝ) else 0) else 0) := by
    funext _
    by_cases h : o' = o''
    · subst h
      by_cases h2 : o' = o₀ <;> simp [h2]
    · have hmul : (if o' = o₀ then (1 : ℝ) else 0) * (if o'' = o₀ then (1 : ℝ) else 0) = 0 := by
        by_cases h2 : o' = o₀
        · by_cases h3 : o'' = o₀
          · exact absurd (h2.trans h3.symm) h
          · simp [h3]
        · simp [h2]
      simpa [h] using hmul
  rw [hconst, condExp_const bot_le]

/-- A model for `condExp_meatLC_sub_meat`: `Ω = Unit`, `μ = dirac ()`, `𝒟 = ⊥`, `R = id`,
`ε ≡ e_{o₀}`, `w ≡ 1`, with the heteroskedastic variance profile `σ²_ε(o) = 𝟙{o = o₀}`. -/
theorem condExp_meatLC_sub_meat_witness {O : Type*} [Fintype O] [DecidableEq O] (o₀ : O) :
    (fun ω : Unit => (Measure.dirac ())[fun _ : Unit => ∑ o : O, (1 : ℝ) *
          ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ O)) (EuclideanSpace.single o₀ (1 : ℝ)) o
            ^ 2 / opEntry (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ O)) o o)
          | (⊥ : MeasurableSpace Unit)] ω
        - ∑ o : O, (1 : ℝ) * (if o = o₀ then (1 : ℝ) else 0))
      =ᵐ[Measure.dirac ()] fun _ : Unit => ∑ o : O,
          (1 : ℝ) / opEntry (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ O)) o o
            * ∑ o' ∈ Finset.univ.erase o,
                opEntry (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ O)) o o' ^ 2
                  * ((if o' = o₀ then (1 : ℝ) else 0) - (if o = o₀ then (1 : ℝ) else 0)) := by
  have hdiag : ∀ o : O,
      opEntry (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ O)) o o = 1 := by
    intro o
    simp [opEntry]
  exact condExp_meatLC_sub_meat (⊥ : MeasurableSpace Unit)
    (R := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ O))
    (fun _ _ => rfl) (fun _ => rfl) (fun o => by rw [hdiag o]; exact one_pos)
    (epsv := fun _ => EuclideanSpace.single o₀ (1 : ℝ))
    (sig := fun o _ => if o = o₀ then (1 : ℝ) else 0) (w := fun _ _ => (1 : ℝ))
    (fun _ => stronglyMeasurable_const) (fun _ _ => integrable_const _)
    (fun o' o'' => witness_cross o₀ o' o'') (fun _ => integrable_const _)

/-- A model for `condExp_meatLC_of_homoskedastic`: the same construction at `O = Fin 1`, with
unit variance. -/
theorem condExp_meatLC_of_homoskedastic_witness :
    (Measure.dirac ())[fun _ : Unit => ∑ o : Fin 1, (1 : ℝ) *
        ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))
            (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) o ^ 2
          / opEntry (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) o o)
        | (⊥ : MeasurableSpace Unit)]
      =ᵐ[Measure.dirac ()] fun _ : Unit =>
        ∑ o : Fin 1, (1 : ℝ) * (if o = (0 : Fin 1) then (1 : ℝ) else 0) := by
  have hdiag : ∀ o : Fin 1,
      opEntry (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) o o = 1 := by
    intro o
    simp [opEntry]
  exact condExp_meatLC_of_homoskedastic (⊥ : MeasurableSpace Unit)
    (R := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))
    (fun _ _ => rfl) (fun _ => rfl) (fun o => by rw [hdiag o]; exact one_pos)
    (epsv := fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    (sig := fun o _ => if o = (0 : Fin 1) then (1 : ℝ) else 0) (w := fun _ _ => (1 : ℝ))
    (s := fun _ => (1 : ℝ)) (fun o _ => by simp [Subsingleton.elim o (0 : Fin 1)])
    (fun _ => stronglyMeasurable_const) (fun _ _ => integrable_const _)
    (fun o' o'' => witness_cross (0 : Fin 1) o' o'') (fun _ => integrable_const _)

end Witness

end LeverageCond
end Multiway
