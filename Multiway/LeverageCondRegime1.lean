import Multiway.LeverageCond
import Multiway.CondIndep
import Mathlib.Probability.CondVar

/-!
# Leverage identity and leverage correction under Regime 1

This file formalizes clauses (ii) and (iii) of Lemma SM.B.6 (Residual representation and exact
leverage identity) and Proposition SM.D.4 (Exact leverage correction) under Regime 1 of the
dependence assumption: the innovations `ε_o` are mutually conditionally independent given `𝒟`,
with conditional mean zero and conditional variances `σ²_ε(o)`. The conditional cross-moment
identity `E[ε_o ε_{o'} | 𝒟] = 𝟙{o = o'} σ²_ε(o)`, taken as the hypothesis `hcross` in
`Multiway.LeverageCond`, is derived here. The residual-maker entries `R_{oo'}` may be arbitrary
`𝒟`-measurable random variables satisfying `ν̂_{FE,o} = ∑_{o'} R_{oo'} ε_{o'}` (`hres`) and
`∑_{o'} R²_{oo'} = R_{oo}` (`hrow`); a deterministic operator is a special case.

## Main results

* `condExp_cross_of_regimeOne`: the conditional cross moments under Regime 1.
* `condExp_meatLC_sub_meat_regimeOne`, `condExp_meatLC_of_homoskedastic_regimeOne`:
  Proposition SM.D.4 at a fixed design, without `hcross`.
* `randomDesign_of_opEntry`: a fixed self-adjoint idempotent operator is a random design.
* `prop_lc_a_random_regimeOne`, `prop_lc_b_random_regimeOne`: Proposition SM.D.4 at a random
  design under Regime 1.
-/

namespace Multiway
namespace LeverageCondRegime1

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace

/-! ### The diagonal: `E[ε_o² | 𝒟]` is the conditional variance -/

section Diagonal

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `E[X | 𝒟] = 0` then `E[X² | 𝒟] = Var(X | 𝒟)`. -/
theorem condExp_mul_self_eq_condVar {X : Ω → ℝ} (hX0 : μ[X | 𝒟] =ᵐ[μ] 0) :
    μ[fun ω => X ω * X ω | 𝒟] =ᵐ[μ] Var[X ; μ | 𝒟] := by
  have hdef : Var[X ; μ | 𝒟] = μ[(X - μ[X | 𝒟]) ^ 2 | 𝒟] := rfl
  rw [hdef]
  refine condExp_congr_ae ?_
  filter_upwards [hX0] with ω hω
  show X ω * X ω = (X ω - (μ[X | 𝒟]) ω) ^ 2
  rw [show (μ[X | 𝒟]) ω = 0 from hω]
  ring

end Diagonal

/-! ### Conditional cross moments under Regime 1 -/

section Cross

variable {O : Type*} [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Under Regime 1 (the innovations mutually conditionally independent given `𝒟`, with
conditional mean zero and conditional variances `σ²_ε(o)`),
`E[ε_{o'} ε_{o''} | 𝒟] = 𝟙{o' = o''} σ²_ε(o')`. -/
theorem condExp_cross_of_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    {eps sig : O → Ω → ℝ}
    (hmeas : ∀ o, Measurable[mΩ] (eps o))
    (hindep : iCondIndepFun 𝒟 h𝒟 eps μ)
    (hint₁ : ∀ o, Integrable (eps o) μ)
    (hint₂ : ∀ o o', Integrable (fun ω => eps o ω * eps o' ω) μ)
    (hmean : ∀ o, μ[eps o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[eps o ; μ | 𝒟] =ᵐ[μ] sig o) (o o' : O) :
    μ[fun ω => eps o ω * eps o' ω | 𝒟]
      =ᵐ[μ] fun ω => if o = o' then sig o ω else 0 := by
  classical
  by_cases h : o = o'
  · subst h
    filter_upwards [(condExp_mul_self_eq_condVar 𝒟 (hmean o)).trans (hvar o)] with ω hω
    simpa using hω
  · have hz := CondIndep.condExp_mul_eq_zero_of_condIndepFun 𝒟 (hmeas o) (hmeas o')
      (hindep.condIndepFun h) (hint₁ o) (hint₁ o') (hint₂ o o') (hmean o')
    filter_upwards [hz] with ω hω
    simpa [h] using hω

end Cross

/-! ### Leverage identity and leverage correction under Regime 1

Each theorem is the corresponding theorem of `Multiway.LeverageCond` applied to
`condExp_cross_of_regimeOne`. -/

section Siblings

open LeverageCond

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable {epsv : Ω → EuclideanSpace ℝ O} {sig w : O → Ω → ℝ}

/-- **Lemma SM.B.6 (ii), first form, under Regime 1.**
`E[ν̂²_{FE,o} | 𝒟] = ∑_{o'} R²_{oo'} σ²_ε(o')`. -/
theorem condExp_feResidual_sq_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O)
    (hmeas : ∀ o, Measurable[mΩ] fun ω => epsv ω o)
    (hindep : iCondIndepFun 𝒟 h𝒟 (fun (o : O) (ω : Ω) => epsv ω o) μ)
    (hint₁ : ∀ o, Integrable (fun ω => epsv ω o) μ)
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hmean : ∀ o, μ[fun ω => epsv ω o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[fun ω => epsv ω o ; μ | 𝒟] =ᵐ[μ] sig o) (o : O) :
    μ[fun ω => R (epsv ω) o ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ o' : O, opEntry R o o' ^ 2 * sig o' ω :=
  condExp_feResidual_sq 𝒟 R hint
    (condExp_cross_of_regimeOne 𝒟 hmeas hindep hint₁ hint hmean hvar) o

/-- **Lemma SM.B.6 (ii), second form, under Regime 1.**
`E[ν̂²_{FE,o} | 𝒟] = R_oo σ²_ε(o) + ∑_{o'≠o} R²_{oo'}(σ²_ε(o') - σ²_ε(o))`. -/
theorem condExp_feResidual_sq_leverage_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    (hmeas : ∀ o, Measurable[mΩ] fun ω => epsv ω o)
    (hindep : iCondIndepFun 𝒟 h𝒟 (fun (o : O) (ω : Ω) => epsv ω o) μ)
    (hint₁ : ∀ o, Integrable (fun ω => epsv ω o) μ)
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hmean : ∀ o, μ[fun ω => epsv ω o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[fun ω => epsv ω o ; μ | 𝒟] =ᵐ[μ] sig o) (o : O) :
    μ[fun ω => R (epsv ω) o ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => opEntry R o o * sig o ω
        + ∑ o' ∈ Finset.univ.erase o, opEntry R o o' ^ 2 * (sig o' ω - sig o ω) :=
  condExp_feResidual_sq_leverage 𝒟 hsym hidem hint
    (condExp_cross_of_regimeOne 𝒟 hmeas hindep hint₁ hint hmean hvar) o

/-- The weighted conditional residual variance under Regime 1. -/
theorem condExp_weighted_feResidual_sq_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} (R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hmeas : ∀ o, Measurable[mΩ] fun ω => epsv ω o)
    (hindep : iCondIndepFun 𝒟 h𝒟 (fun (o : O) (ω : Ω) => epsv ω o) μ)
    (hint₁ : ∀ o, Integrable (fun ω => epsv ω o) μ)
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hmean : ∀ o, μ[fun ω => epsv ω o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[fun ω => epsv ω o ; μ | 𝒟] =ᵐ[μ] sig o)
    (hintw : ∀ o, Integrable (fun ω => w o ω * R (epsv ω) o ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * R (epsv ω) o ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, w o ω * ∑ o' : O, opEntry R o o' ^ 2 * sig o' ω :=
  condExp_weighted_feResidual_sq 𝒟 R hw hint
    (condExp_cross_of_regimeOne 𝒟 hmeas hindep hint₁ hint hmean hvar) hintw

/-- **Lemma SM.B.6 (iii) under Regime 1.** `E[M̂_W | 𝒟] = σ²_ε ∑_o x̃_o x̃_o' R_oo`, entry by
entry. -/
theorem condExp_meatW_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O} {s : Ω → ℝ}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    (hhom : ∀ o ω, sig o ω = s ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hmeas : ∀ o, Measurable[mΩ] fun ω => epsv ω o)
    (hindep : iCondIndepFun 𝒟 h𝒟 (fun (o : O) (ω : Ω) => epsv ω o) μ)
    (hint₁ : ∀ o, Integrable (fun ω => epsv ω o) μ)
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hmean : ∀ o, μ[fun ω => epsv ω o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[fun ω => epsv ω o ; μ | 𝒟] =ᵐ[μ] sig o)
    (hintw : ∀ o, Integrable (fun ω => w o ω * R (epsv ω) o ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * R (epsv ω) o ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => s ω * ∑ o : O, w o ω * opEntry R o o :=
  condExp_meatW 𝒟 hsym hidem hhom hw hint
    (condExp_cross_of_regimeOne 𝒟 hmeas hindep hint₁ hint hmean hvar) hintw

/-- **Proposition SM.D.4 (a) under Regime 1.**
`E[M̂^{LC} | 𝒟] - M_n = ∑_o x̃_o x̃_o' R_oo^{-1} ∑_{o'≠o} R²_{oo'}(σ²_ε(o') - σ²_ε(o))`. -/
theorem condExp_meatLC_sub_meat_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    (hRpos : ∀ o : O, 0 < opEntry R o o)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hmeas : ∀ o, Measurable[mΩ] fun ω => epsv ω o)
    (hindep : iCondIndepFun 𝒟 h𝒟 (fun (o : O) (ω : Ω) => epsv ω o) μ)
    (hint₁ : ∀ o, Integrable (fun ω => epsv ω o) μ)
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hmean : ∀ o, μ[fun ω => epsv ω o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[fun ω => epsv ω o ; μ | 𝒟] =ᵐ[μ] sig o)
    (hintw : ∀ o, Integrable (fun ω => w o ω / opEntry R o o * R (epsv ω) o ^ 2) μ) :
    (fun ω => μ[fun ω => ∑ o : O, w o ω * (R (epsv ω) o ^ 2 / opEntry R o o) | 𝒟] ω
        - ∑ o : O, w o ω * sig o ω)
      =ᵐ[μ] fun ω => ∑ o : O, w o ω / opEntry R o o
          * ∑ o' ∈ Finset.univ.erase o, opEntry R o o' ^ 2 * (sig o' ω - sig o ω) :=
  condExp_meatLC_sub_meat 𝒟 hsym hidem hRpos hw hint
    (condExp_cross_of_regimeOne 𝒟 hmeas hindep hint₁ hint hmean hvar) hintw

/-- **Proposition SM.D.4 (b) under Regime 1.** `E[M̂^{LC} | 𝒟] = M_n` when
`σ²_ε(o) ≡ σ²_ε`. -/
theorem condExp_meatLC_of_homoskedastic_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O} {s : Ω → ℝ}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    (hRpos : ∀ o : O, 0 < opEntry R o o)
    (hhom : ∀ o ω, sig o ω = s ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hmeas : ∀ o, Measurable[mΩ] fun ω => epsv ω o)
    (hindep : iCondIndepFun 𝒟 h𝒟 (fun (o : O) (ω : Ω) => epsv ω o) μ)
    (hint₁ : ∀ o, Integrable (fun ω => epsv ω o) μ)
    (hint : ∀ o' o'', Integrable (fun ω => epsv ω o' * epsv ω o'') μ)
    (hmean : ∀ o, μ[fun ω => epsv ω o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[fun ω => epsv ω o ; μ | 𝒟] =ᵐ[μ] sig o)
    (hintw : ∀ o, Integrable (fun ω => w o ω / opEntry R o o * R (epsv ω) o ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * (R (epsv ω) o ^ 2 / opEntry R o o) | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, w o ω * sig o ω :=
  condExp_meatLC_of_homoskedastic 𝒟 hsym hidem hRpos hhom hw hint
    (condExp_cross_of_regimeOne 𝒟 hmeas hindep hint₁ hint hmean hvar) hintw

end Siblings

/-! ### Random design

The entries of `R` are `𝒟`-measurable functions `r o o' : Ω → ℝ` satisfying, pointwise in `ω`,

* `hres`: `ν̂_{FE,o} = ∑_{o'} R_{oo'} ε_{o'}`;
* `hrow`: `∑_{o'} R²_{oo'} = R_{oo}`. -/

section RandomDesign

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable {r : O → O → Ω → ℝ} {eps sig w resid : O → Ω → ℝ}

omit [DecidableEq O] in
/-- The squared residual is integrable when every coefficient-weighted cross product is. -/
theorem integrable_resid_sq
    (hres : ∀ o ω, resid o ω = ∑ o' : O, r o o' ω * eps o' ω)
    (hint' : ∀ o o' o'',
      Integrable (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) μ) (o : O) :
    Integrable (fun ω => resid o ω ^ 2) μ := by
  have hrw : (fun ω => resid o ω ^ 2)
      = ∑ o' : O, ∑ o'' : O,
          (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) := by
    rw [← LeverageCond.sq_sum_eq_double_sum (r o) eps]
    funext ω
    rw [hres o ω]
  rw [hrw]
  exact integrable_finsetSum' _ fun o' _ =>
    integrable_finsetSum' _ fun o'' _ => hint' o o' o''

/-- **Lemma SM.B.6 (ii), first form, at a random design.**
`E[ν̂²_{FE,o} | 𝒟] = ∑_{o'} R²_{oo'} σ²_ε(o')` with `𝒟`-measurable random entries `R_{oo'}`. -/
theorem condExp_resid_sq_random
    (hr : ∀ o o', StronglyMeasurable[𝒟] (r o o'))
    (hres : ∀ o ω, resid o ω = ∑ o' : O, r o o' ω * eps o' ω)
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hint' : ∀ o o' o'',
      Integrable (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0) (o : O) :
    μ[fun ω => resid o ω ^ 2 | 𝒟] =ᵐ[μ] fun ω => ∑ o' : O, r o o' ω ^ 2 * sig o' ω := by
  have hfun : (fun ω => resid o ω ^ 2) = fun ω => (∑ o' : O, r o o' ω * eps o' ω) ^ 2 := by
    funext ω
    rw [hres o ω]
  rw [hfun]
  exact LeverageCond.condExp_sq_linearCombination 𝒟 (hr o) hint (hint' o) hcross

/-- **Lemma SM.B.6 (ii), second form, at a random design.** -/
theorem condExp_resid_sq_leverage_random
    (hr : ∀ o o', StronglyMeasurable[𝒟] (r o o'))
    (hres : ∀ o ω, resid o ω = ∑ o' : O, r o o' ω * eps o' ω)
    (hrow : ∀ o ω, ∑ o' : O, r o o' ω ^ 2 = r o o ω)
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hint' : ∀ o o' o'',
      Integrable (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0) (o : O) :
    μ[fun ω => resid o ω ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => r o o ω * sig o ω
        + ∑ o' ∈ Finset.univ.erase o, r o o' ω ^ 2 * (sig o' ω - sig o ω) := by
  filter_upwards [condExp_resid_sq_random 𝒟 hr hres hint hint' hcross o] with ω hω
  rw [hω]
  exact LeverageCond.sum_sq_split (hrow o ω) (fun o' => sig o' ω) o

/-- The weighted conditional residual variance at a random design. -/
theorem condExp_weighted_resid_sq_random
    (hr : ∀ o o', StronglyMeasurable[𝒟] (r o o'))
    (hres : ∀ o ω, resid o ω = ∑ o' : O, r o o' ω * eps o' ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hint' : ∀ o o' o'',
      Integrable (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0)
    (hintw : ∀ o, Integrable (fun ω => w o ω * resid o ω ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * resid o ω ^ 2 | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, w o ω * ∑ o' : O, r o o' ω ^ 2 * sig o' ω := by
  have hrw : (fun ω => ∑ o : O, w o ω * resid o ω ^ 2)
      = ∑ o : O, (fun ω => w o ω * resid o ω ^ 2) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hrw]
  have h1 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
    (fun o _ => hintw o) 𝒟
  have h2 : ∀ᵐ ω ∂μ, ∀ o : O, μ[fun ω => w o ω * resid o ω ^ 2 | 𝒟] ω
      = w o ω * μ[fun ω => resid o ω ^ 2 | 𝒟] ω :=
    ae_all_iff.2 fun o => condExp_mul_of_stronglyMeasurable_left (hw o) (hintw o)
      (integrable_resid_sq hres hint' o)
  have h3 : ∀ᵐ ω ∂μ, ∀ o : O, μ[fun ω => resid o ω ^ 2 | 𝒟] ω
      = ∑ o' : O, r o o' ω ^ 2 * sig o' ω :=
    ae_all_iff.2 fun o => condExp_resid_sq_random 𝒟 hr hres hint hint' hcross o
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun o _ => by rw [e2 o, e3 o]

/-- **Proposition SM.D.4 (a) at a random design.** `hRpos` requires `R_oo > 0` for every `o`,
in every realization. -/
theorem condExp_meatLC_sub_meat_random
    (hr : ∀ o o', StronglyMeasurable[𝒟] (r o o'))
    (hres : ∀ o ω, resid o ω = ∑ o' : O, r o o' ω * eps o' ω)
    (hrow : ∀ o ω, ∑ o' : O, r o o' ω ^ 2 = r o o ω)
    (hRpos : ∀ o ω, 0 < r o o ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hint' : ∀ o o' o'',
      Integrable (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0)
    (hintw : ∀ o, Integrable (fun ω => w o ω / r o o ω * resid o ω ^ 2) μ) :
    (fun ω => μ[fun ω => ∑ o : O, w o ω * (resid o ω ^ 2 / r o o ω) | 𝒟] ω
        - ∑ o : O, w o ω * sig o ω)
      =ᵐ[μ] fun ω => ∑ o : O, w o ω / r o o ω
          * ∑ o' ∈ Finset.univ.erase o, r o o' ω ^ 2 * (sig o' ω - sig o ω) := by
  have hdiv : (fun ω => ∑ o : O, w o ω * (resid o ω ^ 2 / r o o ω))
      = fun ω => ∑ o : O, w o ω / r o o ω * resid o ω ^ 2 := by
    funext ω
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [mul_div_assoc']
    ring
  rw [hdiv]
  filter_upwards [condExp_weighted_resid_sq_random 𝒟 (w := fun o ω => w o ω / r o o ω)
    hr hres (fun o => (hw o).div (hr o o)) hint hint' hcross hintw] with ω hω
  rw [hω, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hcancel : w o ω / r o o ω * (r o o ω * sig o ω) = w o ω * sig o ω := by
    rw [← mul_assoc, div_mul_cancel₀ _ (hRpos o ω).ne']
  rw [LeverageCond.sum_sq_split (hrow o ω) (fun o' => sig o' ω) o, mul_add, hcancel]
  ring

/-- **Proposition SM.D.4 (b) at a random design.** -/
theorem condExp_meatLC_of_homoskedastic_random {s : Ω → ℝ}
    (hr : ∀ o o', StronglyMeasurable[𝒟] (r o o'))
    (hres : ∀ o ω, resid o ω = ∑ o' : O, r o o' ω * eps o' ω)
    (hrow : ∀ o ω, ∑ o' : O, r o o' ω ^ 2 = r o o ω)
    (hRpos : ∀ o ω, 0 < r o o ω)
    (hhom : ∀ o ω, sig o ω = s ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hint' : ∀ o o' o'',
      Integrable (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) μ)
    (hcross : ∀ o' o'', μ[fun ω => eps o' ω * eps o'' ω | 𝒟]
      =ᵐ[μ] fun ω => if o' = o'' then sig o' ω else 0)
    (hintw : ∀ o, Integrable (fun ω => w o ω / r o o ω * resid o ω ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * (resid o ω ^ 2 / r o o ω) | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, w o ω * sig o ω := by
  filter_upwards [condExp_meatLC_sub_meat_random 𝒟 hr hres hrow hRpos hw hint hint' hcross
    hintw] with ω hω
  have hzero : ∑ o : O, w o ω / r o o ω
      * ∑ o' ∈ Finset.univ.erase o, r o o' ω ^ 2 * (sig o' ω - sig o ω) = 0 := by
    refine Finset.sum_eq_zero fun o _ => ?_
    have hin : ∑ o' ∈ Finset.univ.erase o, r o o' ω ^ 2 * (sig o' ω - sig o ω) = 0 := by
      refine Finset.sum_eq_zero fun o' _ => ?_
      rw [hhom o' ω, hhom o ω, sub_self, mul_zero]
    rw [hin, mul_zero]
  rw [hzero] at hω
  linarith [hω]

/-- A deterministic self-adjoint idempotent operator satisfies `hres` and `hrow` with
`r o o' ω = R_{oo'}`. -/
theorem randomDesign_of_opEntry {R : EuclideanSpace ℝ O →L[ℝ] EuclideanSpace ℝ O}
    (hsym : ∀ u v : EuclideanSpace ℝ O, ⟪R u, v⟫ = ⟪u, R v⟫)
    (hidem : ∀ u : EuclideanSpace ℝ O, R (R u) = R u)
    (epsv : Ω → EuclideanSpace ℝ O) :
    (∀ o o', StronglyMeasurable[𝒟] fun _ : Ω => LeverageCond.opEntry R o o')
    ∧ (∀ o ω, R (epsv ω) o = ∑ o' : O, LeverageCond.opEntry R o o' * epsv ω o')
    ∧ (∀ o (_ : Ω), ∑ o' : O, LeverageCond.opEntry R o o' ^ 2
        = LeverageCond.opEntry R o o) :=
  ⟨fun _ _ => stronglyMeasurable_const,
    fun o ω => LeverageCond.apply_eq_sum_opEntry R (epsv ω) o,
    fun o _ => LeverageCond.sum_opEntry_sq hsym hidem o⟩

end RandomDesign

/-! ### Random design under Regime 1 -/

section Together

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable {r : O → O → Ω → ℝ} {eps sig w resid : O → Ω → ℝ}

/-- **Proposition SM.D.4 (a)** at a random design under Regime 1. -/
theorem prop_lc_a_random_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    (hr : ∀ o o', StronglyMeasurable[𝒟] (r o o'))
    (hres : ∀ o ω, resid o ω = ∑ o' : O, r o o' ω * eps o' ω)
    (hrow : ∀ o ω, ∑ o' : O, r o o' ω ^ 2 = r o o ω)
    (hRpos : ∀ o ω, 0 < r o o ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hmeas : ∀ o, Measurable[mΩ] (eps o))
    (hindep : iCondIndepFun 𝒟 h𝒟 eps μ)
    (hint₁ : ∀ o, Integrable (eps o) μ)
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hint' : ∀ o o' o'',
      Integrable (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) μ)
    (hmean : ∀ o, μ[eps o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[eps o ; μ | 𝒟] =ᵐ[μ] sig o)
    (hintw : ∀ o, Integrable (fun ω => w o ω / r o o ω * resid o ω ^ 2) μ) :
    (fun ω => μ[fun ω => ∑ o : O, w o ω * (resid o ω ^ 2 / r o o ω) | 𝒟] ω
        - ∑ o : O, w o ω * sig o ω)
      =ᵐ[μ] fun ω => ∑ o : O, w o ω / r o o ω
          * ∑ o' ∈ Finset.univ.erase o, r o o' ω ^ 2 * (sig o' ω - sig o ω) :=
  condExp_meatLC_sub_meat_random 𝒟 hr hres hrow hRpos hw hint hint'
    (condExp_cross_of_regimeOne 𝒟 hmeas hindep hint₁ hint hmean hvar) hintw

/-- **Proposition SM.D.4 (b)** at a random design under Regime 1. -/
theorem prop_lc_b_random_regimeOne [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    {s : Ω → ℝ}
    (hr : ∀ o o', StronglyMeasurable[𝒟] (r o o'))
    (hres : ∀ o ω, resid o ω = ∑ o' : O, r o o' ω * eps o' ω)
    (hrow : ∀ o ω, ∑ o' : O, r o o' ω ^ 2 = r o o ω)
    (hRpos : ∀ o ω, 0 < r o o ω)
    (hhom : ∀ o ω, sig o ω = s ω)
    (hw : ∀ o, StronglyMeasurable[𝒟] (w o))
    (hmeas : ∀ o, Measurable[mΩ] (eps o))
    (hindep : iCondIndepFun 𝒟 h𝒟 eps μ)
    (hint₁ : ∀ o, Integrable (eps o) μ)
    (hint : ∀ o' o'', Integrable (fun ω => eps o' ω * eps o'' ω) μ)
    (hint' : ∀ o o' o'',
      Integrable (fun ω => (r o o' ω * r o o'' ω) * (eps o' ω * eps o'' ω)) μ)
    (hmean : ∀ o, μ[eps o | 𝒟] =ᵐ[μ] 0)
    (hvar : ∀ o, Var[eps o ; μ | 𝒟] =ᵐ[μ] sig o)
    (hintw : ∀ o, Integrable (fun ω => w o ω / r o o ω * resid o ω ^ 2) μ) :
    μ[fun ω => ∑ o : O, w o ω * (resid o ω ^ 2 / r o o ω) | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, w o ω * sig o ω :=
  condExp_meatLC_of_homoskedastic_random 𝒟 hr hres hrow hRpos hhom hw hint hint'
    (condExp_cross_of_regimeOne 𝒟 hmeas hindep hint₁ hint hmean hvar) hintw

end Together

end LeverageCondRegime1
end Multiway
