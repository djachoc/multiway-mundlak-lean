import Multiway.Concentration
import Multiway.CondIndep
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.CondVar
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# The variance of a quadratic form in conditionally independent variables

This file formalizes Lemma SM.C.5 of the paper (variance of a quadratic form in independent
variables): if `ε_1, …, ε_n` are, conditionally on `𝒟`, independent with mean zero and
`E[ε_o⁴ | 𝒟] ≤ C`, and `W` is a `𝒟`-measurable random matrix, not necessarily symmetric, then
`Var(ε'Wε | 𝒟) ≤ 3C‖W‖_F²`.

The general statements take the needed four-index conditional moment identities (`hvar`,
`hcross`, `hpair`, `hmixed`, `hquad`) as hypotheses; section `FromCondIndep` derives them from
`ProbabilityTheory.iCondIndepFun`. The `𝒟`-measurability of `W` enters through the pull-out
property in `condExp_sum_mul`.

## Main results

* `condExp_quadForm_sq_sub_sq_condExp_le`: `E[(ε'Wε)²|𝒟] - (E[ε'Wε|𝒟])² ≤ 3C‖W‖_F²`.
* `condVar_quadForm_le`: the same bound for `ProbabilityTheory.condVar`.
* `condVar_quadForm_le_of_condIndep`: the lemma under conditional independence.
-/

namespace Multiway
namespace Quadform

open MeasureTheory

/-! ## The quadratic form and the diagonal / off-diagonal split

`ε'Wε = ∑_o W_{oo}ε_o² + ∑_{o≠o'} W_{oo'}ε_oε_{o'}`, and the corresponding split of the
four-index sum, as identities over `Finset (O × O)`. -/

section Algebra

variable {O : Type*} [Fintype O] [DecidableEq O] {Ω : Type*}

/-- The quadratic form `ε'Wε = ∑_{(o,o')} W_{oo'} ε_o ε_{o'}`. -/
def quadForm (W : Ω → Matrix O O ℝ) (eps : O → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ p : O × O, W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω)

omit [DecidableEq O] in
theorem quadForm_apply (W : Ω → Matrix O O ℝ) (eps : O → Ω → ℝ) (ω : Ω) :
    quadForm W eps ω = ∑ p : O × O, W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω) := rfl

omit [DecidableEq O] in
theorem quadForm_eq (W : Ω → Matrix O O ℝ) (eps : O → Ω → ℝ) :
    quadForm W eps = fun ω => ∑ p : O × O, W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω) := rfl

omit [DecidableEq O] in
/-- `ε'Wε` as the iterated sum `∑_o ∑_{o'}`. -/
theorem quadForm_eq_double_sum (W : Ω → Matrix O O ℝ) (eps : O → Ω → ℝ) (ω : Ω) :
    quadForm W eps ω = ∑ o : O, ∑ o' : O, W ω o o' * (eps o ω * eps o' ω) := by
  rw [quadForm_apply, Fintype.sum_prod_type]

/-- A sum over ordered pairs splits into its diagonal and off-diagonal parts. -/
theorem sum_split (f : O × O → ℝ) :
    ∑ p : O × O, f p
      = ∑ o : O, f (o, o) + ∑ p ∈ (Finset.univ : Finset O).offDiag, f p := by
  rw [← Finset.univ_product_univ, ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]

/-- The diagonal / off-diagonal split applied to both factors of a sum over pairs of pairs,
giving four blocks. -/
theorem sum_split4 (g : (O × O) × (O × O) → ℝ) :
    ∑ r : (O × O) × (O × O), g r
      = (∑ a : O, ∑ b : O, g ((a, a), (b, b))
          + ∑ a : O, ∑ q ∈ (Finset.univ : Finset O).offDiag, g ((a, a), q))
        + (∑ p ∈ (Finset.univ : Finset O).offDiag, ∑ b : O, g (p, (b, b))
          + ∑ p ∈ (Finset.univ : Finset O).offDiag,
              ∑ q ∈ (Finset.univ : Finset O).offDiag, g (p, q)) := by
  rw [Fintype.sum_prod_type, sum_split (fun p : O × O => ∑ q : O × O, g (p, q))]
  congr 1
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => sum_split fun q : O × O => g ((a, a), q)
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => sum_split fun q : O × O => g (p, q)

omit [DecidableEq O] in
/-- Reindexing an off-diagonal sum by the transposition `(o,o') ↦ (o',o)` leaves it
unchanged. -/
theorem sum_offDiag_swap (f : O × O → ℝ) :
    ∑ p ∈ (Finset.univ : Finset O).offDiag, f (p.2, p.1)
      = ∑ p ∈ (Finset.univ : Finset O).offDiag, f p := by
  have hmem : ∀ p : O × O, p ∈ (Finset.univ : Finset O).offDiag →
      ((p.2, p.1) : O × O) ∈ (Finset.univ : Finset O).offDiag := by
    intro p hp
    rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, Ne.symm hp.2.2⟩
  exact Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) hmem hmem
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `‖W‖_F²` split into its diagonal and off-diagonal parts. -/
theorem rectFrobSq_split (W : Matrix O O ℝ) :
    rectFrobSq W
      = ∑ o : O, W o o ^ 2 + ∑ p ∈ (Finset.univ : Finset O).offDiag, W p.1 p.2 ^ 2 := by
  have h : rectFrobSq W = ∑ p : O × O, W p.1 p.2 ^ 2 := by
    rw [rectFrobSq, Fintype.sum_prod_type]
  rw [h, sum_split fun p : O × O => W p.1 p.2 ^ 2]

/-- The square `(∑_o u_o v_o)²`, expanded and split into diagonal and off-diagonal parts. -/
theorem sq_sum_diag (u v : O → ℝ) :
    (∑ o : O, u o * v o) ^ 2
      = ∑ o : O, u o ^ 2 * v o ^ 2
        + ∑ p ∈ (Finset.univ : Finset O).offDiag, u p.1 * u p.2 * (v p.1 * v p.2) := by
  have h : (∑ o : O, u o * v o) ^ 2
      = ∑ p : O × O, u p.1 * u p.2 * (v p.1 * v p.2) := by
    rw [Fintype.sum_prod_type, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h, sum_split fun p : O × O => u p.1 * u p.2 * (v p.1 * v p.2)]
  congr 1
  exact Finset.sum_congr rfl fun o _ => by ring

end Algebra

/-! ## The conditional layer -/

section Conditional

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conditional expectation respects pointwise equality of integrands. -/
theorem condExp_congr_fun {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) : μ[f | 𝒟] = μ[g | 𝒟] := by
  have hfg : f = g := funext h
  rw [hfg]

/-- Pull-out: the conditional expectation of a finite sum of products of a `𝒟`-measurable
coefficient with an integrable variable is taken term by term, with the coefficient outside. -/
theorem condExp_sum_mul {κ : Type*} (s : Finset κ) {a Z : κ → Ω → ℝ}
    (ha : ∀ i, StronglyMeasurable[𝒟] (a i))
    (hZ : ∀ i, Integrable (Z i) μ)
    (haZ : ∀ i, Integrable (fun ω => a i ω * Z i ω) μ) :
    μ[fun ω => ∑ i ∈ s, a i ω * Z i ω | 𝒟]
      =ᵐ[μ] fun ω => ∑ i ∈ s, a i ω * μ[Z i | 𝒟] ω := by
  have hrw : (fun ω => ∑ i ∈ s, a i ω * Z i ω) = ∑ i ∈ s, fun ω => a i ω * Z i ω := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hrw]
  have h1 := condExp_finsetSum (μ := μ) (s := s) (fun i _ => haZ i) 𝒟
  have h2 : ∀ᵐ ω ∂μ, ∀ i ∈ s, μ[fun ω => a i ω * Z i ω | 𝒟] ω = a i ω * μ[Z i | 𝒟] ω :=
    (Filter.eventually_all_finset s).2 fun i _ =>
      condExp_mul_of_stronglyMeasurable_left (ha i) (haZ i) (hZ i)
  filter_upwards [h1, h2] with ω e1 e2
  rw [e1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => e2 i hi

/-! ### The two moment facts about a single observation -/

/-- `σ²_ε(o) ≥ 0`: a conditional second moment is nonnegative. -/
theorem sig_nonneg {e s : Ω → ℝ} (hvar : μ[fun ω => e ω * e ω | 𝒟] =ᵐ[μ] s) :
    0 ≤ᵐ[μ] s := by
  have h : (0 : Ω → ℝ) ≤ᵐ[μ] μ[fun ω => e ω * e ω | 𝒟] :=
    condExp_nonneg (m := 𝒟) (Filter.Eventually.of_forall fun ω => mul_self_nonneg (e ω))
  filter_upwards [h, hvar] with ω h1 h2
  rw [← h2]
  exact h1

/-- Conditional Jensen at `x ↦ x²`: `(E[ε_o²|𝒟])² ≤ E[ε_o⁴|𝒟] ≤ C`. -/
theorem condExp_sq_sq_le [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ) {e s : Ω → ℝ} {C : ℝ}
    (hi2 : Integrable (fun ω => e ω * e ω) μ)
    (hi4 : Integrable (fun ω => e ω * e ω * (e ω * e ω)) μ)
    (hvar : μ[fun ω => e ω * e ω | 𝒟] =ᵐ[μ] s)
    (hfour : μ[fun ω => e ω * e ω * (e ω * e ω) | 𝒟] ≤ᵐ[μ] fun _ => C) :
    (fun ω => s ω ^ 2) ≤ᵐ[μ] fun _ => C := by
  have hcvx : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 2) := Even.convexOn_pow (by decide)
  have hlsc : LowerSemicontinuous (fun x : ℝ => x ^ 2) := (continuous_pow 2).lowerSemicontinuous
  have heq : (fun ω => e ω * e ω * (e ω * e ω))
      = (fun x : ℝ => x ^ 2) ∘ fun ω => e ω * e ω := by
    funext ω
    simp only [Function.comp_apply]
    ring
  have hcomp : Integrable ((fun x : ℝ => x ^ 2) ∘ fun ω => e ω * e ω) μ := heq ▸ hi4
  have hjen := hcvx.map_condExp_le_univ (m := 𝒟) h𝒟 hlsc hi2 hcomp
  have hcongr : μ[(fun x : ℝ => x ^ 2) ∘ fun ω => e ω * e ω | 𝒟]
      = μ[fun ω => e ω * e ω * (e ω * e ω) | 𝒟] := by
    rw [heq]
  filter_upwards [hjen, hvar, hfour] with ω h1 h2 h3
  simp only [Function.comp_apply] at h1
  rw [h2] at h1
  rw [hcongr] at h1
  exact h1.trans h3

/-- `E[ε_o²|𝒟] ≤ C^{1/2}`. -/
theorem condExp_sq_le_sqrt [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ) {e s : Ω → ℝ} {C : ℝ}
    (hi2 : Integrable (fun ω => e ω * e ω) μ)
    (hi4 : Integrable (fun ω => e ω * e ω * (e ω * e ω)) μ)
    (hvar : μ[fun ω => e ω * e ω | 𝒟] =ᵐ[μ] s)
    (hfour : μ[fun ω => e ω * e ω * (e ω * e ω) | 𝒟] ≤ᵐ[μ] fun _ => C) :
    s ≤ᵐ[μ] fun _ => Real.sqrt C := by
  filter_upwards [condExp_sq_sq_le 𝒟 h𝒟 hi2 hi4 hvar hfour, sig_nonneg 𝒟 hvar] with ω h1 h2
  have h3 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq h2] at h3

/-! ### The conditional mean of `ε'Wε` -/

/-- `E[ε'Wε | 𝒟] = ∑_o W_{oo} σ²_ε(o)`: the off-diagonal part vanishes by `hcross`. -/
theorem condExp_quadForm {W : Ω → Matrix O O ℝ} {eps sig : O → Ω → ℝ}
    (hW : ∀ o o', StronglyMeasurable[𝒟] fun ω => W ω o o')
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hiW2 : ∀ p : O × O, Integrable (fun ω => W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω)) μ)
    (hvar : ∀ o, μ[fun ω => eps o ω * eps o ω | 𝒟] =ᵐ[μ] sig o)
    (hcross : ∀ o o', o ≠ o' → μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0) :
    μ[quadForm W eps | 𝒟] =ᵐ[μ] fun ω => ∑ o : O, W ω o o * sig o ω := by
  rw [quadForm_eq]
  have h1 := condExp_sum_mul 𝒟 (Finset.univ : Finset (O × O))
    (a := fun p ω => W ω p.1 p.2) (Z := fun p ω => eps p.1 ω * eps p.2 ω)
    (fun p => hW p.1 p.2) hi2 hiW2
  have hv : ∀ᵐ ω ∂μ, ∀ o : O, μ[fun ω => eps o ω * eps o ω | 𝒟] ω = sig o ω :=
    ae_all_iff.2 fun o => hvar o
  have hc : ∀ᵐ ω ∂μ, ∀ p : O × O, p.1 ≠ p.2 →
      μ[fun ω => eps p.1 ω * eps p.2 ω | 𝒟] ω = 0 := by
    refine ae_all_iff.2 fun p => ?_
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun _ h => absurd hp h
    · filter_upwards [hcross p.1 p.2 hp] with ω hω
      intro _
      simpa using hω
  filter_upwards [h1, hv, hc] with ω e1 e2 e3
  rw [e1, sum_split fun p : O × O => W ω p.1 p.2 * μ[fun ω => eps p.1 ω * eps p.2 ω | 𝒟] ω]
  have hoff : ∑ p ∈ (Finset.univ : Finset O).offDiag,
      W ω p.1 p.2 * μ[fun ω => eps p.1 ω * eps p.2 ω | 𝒟] ω = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_offDiag] at hp
    rw [e3 p hp.2.2, mul_zero]
  rw [hoff, add_zero]
  exact Finset.sum_congr rfl fun o _ => by rw [e2 o]

/-! ### The conditional second moment, by the four-index classification -/

/-- `E[(ε'Wε)² | 𝒟]`, block by block: the diagonal-diagonal block splits into
`∑_o W²_{oo}E[ε_o⁴|𝒟]` and `∑_{o≠o'} W_{oo}W_{o'o'}σ²_ε(o)σ²_ε(o')`; the two mixed blocks
vanish by `hmixed`; and in the off-diagonal block only the patterns `(o,o')` and `(o',o)`
survive, by `hquad`. -/
theorem condExp_quadForm_sq {W : Ω → Matrix O O ℝ} {eps sig : O → Ω → ℝ}
    (hW : ∀ o o', StronglyMeasurable[𝒟] fun ω => W ω o o')
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hiW4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
        * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))) μ)
    (hpair : ∀ o o', o ≠ o' →
      μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
        =ᵐ[μ] fun ω => sig o ω * sig o' ω)
    (hmixed : ∀ a o o' : O, o ≠ o' →
      μ[fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0)
    (hquad : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0) :
    μ[fun ω => quadForm W eps ω ^ 2 | 𝒟]
      =ᵐ[μ] fun ω =>
        (∑ o : O, W ω o o ^ 2
              * μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω
            + ∑ p ∈ (Finset.univ : Finset O).offDiag,
                W ω p.1 p.1 * W ω p.2 p.2 * (sig p.1 ω * sig p.2 ω))
          + ∑ p ∈ (Finset.univ : Finset O).offDiag,
              (W ω p.1 p.2 ^ 2 + W ω p.1 p.2 * W ω p.2 p.1) * (sig p.1 ω * sig p.2 ω) := by
  have hsq : (fun ω => quadForm W eps ω ^ 2)
      = fun ω => ∑ r : (O × O) × (O × O),
          W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
            * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) := by
    funext ω
    have hexp : ∑ r : (O × O) × (O × O),
          W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
            * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))
        = ∑ p : O × O, ∑ q : O × O,
            W ω p.1 p.2 * W ω q.1 q.2
              * (eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω)) :=
      Fintype.sum_prod_type _
    rw [hexp, quadForm_apply, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [hsq]
  have h1 := condExp_sum_mul 𝒟 (Finset.univ : Finset ((O × O) × (O × O)))
    (a := fun r ω => W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2)
    (Z := fun r ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))
    (fun r => (hW r.1.1 r.1.2).mul (hW r.2.1 r.2.2)) hi4 hiW4
  -- the three a.e. families the classification consumes
  have hp4 : ∀ᵐ ω ∂μ, ∀ p : O × O, p.1 ≠ p.2 →
      μ[fun ω => eps p.1 ω * eps p.1 ω * (eps p.2 ω * eps p.2 ω) | 𝒟] ω
        = sig p.1 ω * sig p.2 ω := by
    refine ae_all_iff.2 fun p => ?_
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun _ h => absurd hp h
    · filter_upwards [hpair p.1 p.2 hp] with ω hω
      intro _
      exact hω
  have hm4 : ∀ᵐ ω ∂μ, ∀ (a : O) (q : O × O), q.1 ≠ q.2 →
      μ[fun ω => eps a ω * eps a ω * (eps q.1 ω * eps q.2 ω) | 𝒟] ω = 0 := by
    refine ae_all_iff.2 fun a => ae_all_iff.2 fun q => ?_
    by_cases hr : q.1 = q.2
    · exact Filter.Eventually.of_forall fun _ h => absurd hr h
    · filter_upwards [hmixed a q.1 q.2 hr] with ω hω
      intro _
      simpa using hω
  have hq4 : ∀ᵐ ω ∂μ, ∀ p q : O × O,
      p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] ω = 0 := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
    by_cases c1 : p.1 = p.2
    · exact Filter.Eventually.of_forall fun _ h => absurd c1 h
    by_cases c2 : q.1 = q.2
    · exact Filter.Eventually.of_forall fun _ _ h => absurd c2 h
    by_cases c3 : q = p
    · exact Filter.Eventually.of_forall fun _ _ _ h => absurd c3 h
    by_cases c4 : q = (p.2, p.1)
    · exact Filter.Eventually.of_forall fun _ _ _ _ h => absurd c4 h
    · filter_upwards [hquad p q c1 c2 c3 c4] with ω hω
      intro _ _ _ _
      simpa using hω
  filter_upwards [h1, hp4, hm4, hq4] with ω e1 ep em eqd
  rw [e1, sum_split4 fun r : (O × O) × (O × O) =>
    W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
      * μ[fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω) | 𝒟] ω]
  -- block 2: `diag × offDiag`
  have hb2 : ∑ a : O, ∑ q ∈ (Finset.univ : Finset O).offDiag,
      W ω a a * W ω q.1 q.2
        * μ[fun ω => eps a ω * eps a ω * (eps q.1 ω * eps q.2 ω) | 𝒟] ω = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.mem_offDiag] at hq
    rw [em a q hq.2.2, mul_zero]
  -- block 3: `offDiag × diag`
  have hb3 : ∑ p ∈ (Finset.univ : Finset O).offDiag, ∑ b : O,
      W ω p.1 p.2 * W ω b b
        * μ[fun ω => eps p.1 ω * eps p.2 ω * (eps b ω * eps b ω) | 𝒟] ω = 0 := by
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.mem_offDiag] at hp
    have hswap : μ[fun ω => eps p.1 ω * eps p.2 ω * (eps b ω * eps b ω) | 𝒟]
        = μ[fun ω => eps b ω * eps b ω * (eps p.1 ω * eps p.2 ω) | 𝒟] :=
      condExp_congr_fun 𝒟 fun ω => by ring
    rw [hswap, em b p hp.2.2, mul_zero]
  -- block 1: the diagonal-diagonal block, split once more
  have hb1 : ∑ a : O, ∑ b : O, W ω a a * W ω b b
        * μ[fun ω => eps a ω * eps a ω * (eps b ω * eps b ω) | 𝒟] ω
      = ∑ o : O, W ω o o ^ 2
            * μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω
          + ∑ p ∈ (Finset.univ : Finset O).offDiag,
              W ω p.1 p.1 * W ω p.2 p.2 * (sig p.1 ω * sig p.2 ω) := by
    have hexp : ∑ a : O, ∑ b : O, W ω a a * W ω b b
          * μ[fun ω => eps a ω * eps a ω * (eps b ω * eps b ω) | 𝒟] ω
        = ∑ p : O × O, W ω p.1 p.1 * W ω p.2 p.2
            * μ[fun ω => eps p.1 ω * eps p.1 ω * (eps p.2 ω * eps p.2 ω) | 𝒟] ω :=
      (Fintype.sum_prod_type fun p : O × O => W ω p.1 p.1 * W ω p.2 p.2
        * μ[fun ω => eps p.1 ω * eps p.1 ω * (eps p.2 ω * eps p.2 ω) | 𝒟] ω).symm
    rw [hexp, sum_split fun p : O × O => W ω p.1 p.1 * W ω p.2 p.2
      * μ[fun ω => eps p.1 ω * eps p.1 ω * (eps p.2 ω * eps p.2 ω) | 𝒟] ω]
    congr 1
    · exact Finset.sum_congr rfl fun o _ => by ring
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_offDiag] at hp
      rw [ep p hp.2.2]
  -- block 4: the off-diagonal-off-diagonal block, two surviving patterns per pair
  have hb4 : ∑ p ∈ (Finset.univ : Finset O).offDiag,
        ∑ q ∈ (Finset.univ : Finset O).offDiag, W ω p.1 p.2 * W ω q.1 q.2
          * μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] ω
      = ∑ p ∈ (Finset.univ : Finset O).offDiag,
          (W ω p.1 p.2 ^ 2 + W ω p.1 p.2 * W ω p.2 p.1) * (sig p.1 ω * sig p.2 ω) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_offDiag] at hp
    have hpmem : p ∈ (Finset.univ : Finset O).offDiag := by
      rw [Finset.mem_offDiag]; exact hp
    have hsmem : ((p.2, p.1) : O × O) ∈ (Finset.univ : Finset O).offDiag := by
      rw [Finset.mem_offDiag]
      exact ⟨Finset.mem_univ _, Finset.mem_univ _, Ne.symm hp.2.2⟩
    have hne : p ≠ ((p.2, p.1) : O × O) := fun h => hp.2.2 (congrArg Prod.fst h)
    have hzero : ∀ c ∈ (Finset.univ : Finset O).offDiag,
        c ≠ p ∧ c ≠ ((p.2, p.1) : O × O) →
        W ω p.1 p.2 * W ω c.1 c.2
          * μ[fun ω => eps p.1 ω * eps p.2 ω * (eps c.1 ω * eps c.2 ω) | 𝒟] ω = 0 := by
      intro c hc hcne
      rw [Finset.mem_offDiag] at hc
      rw [eqd p c hp.2.2 hc.2.2 hcne.1 hcne.2, mul_zero]
    rw [Finset.sum_eq_add_of_mem p ((p.2, p.1) : O × O) hpmem hsmem hne hzero]
    have hdiag : μ[fun ω => eps p.1 ω * eps p.2 ω * (eps p.1 ω * eps p.2 ω) | 𝒟]
        = μ[fun ω => eps p.1 ω * eps p.1 ω * (eps p.2 ω * eps p.2 ω) | 𝒟] :=
      condExp_congr_fun 𝒟 fun ω => by ring
    have hanti : μ[fun ω => eps p.1 ω * eps p.2 ω * (eps p.2 ω * eps p.1 ω) | 𝒟]
        = μ[fun ω => eps p.1 ω * eps p.1 ω * (eps p.2 ω * eps p.2 ω) | 𝒟] :=
      condExp_congr_fun 𝒟 fun ω => by ring
    rw [hdiag, hanti, ep p hp.2.2]
    ring
  rw [hb1, hb2, hb3, hb4, add_zero, zero_add]

/-! ### The variance -/

/-- The variance decomposition
`E[(ε'Wε)²|𝒟] - (E[ε'Wε|𝒟])² = ∑_o W²_{oo} Var(ε_o²|𝒟) + ∑_{o≠o'}(W²_{oo'} + W_{oo'}W_{o'o})σ²_ε(o)σ²_ε(o')`. -/
theorem condExp_quadForm_sq_sub_sq_condExp {W : Ω → Matrix O O ℝ} {eps sig : O → Ω → ℝ}
    (hW : ∀ o o', StronglyMeasurable[𝒟] fun ω => W ω o o')
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hiW2 : ∀ p : O × O, Integrable (fun ω => W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω)) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hiW4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
        * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))) μ)
    (hvar : ∀ o, μ[fun ω => eps o ω * eps o ω | 𝒟] =ᵐ[μ] sig o)
    (hcross : ∀ o o', o ≠ o' → μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0)
    (hpair : ∀ o o', o ≠ o' →
      μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
        =ᵐ[μ] fun ω => sig o ω * sig o' ω)
    (hmixed : ∀ a o o' : O, o ≠ o' →
      μ[fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0)
    (hquad : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0) :
    (fun ω => μ[fun ω => quadForm W eps ω ^ 2 | 𝒟] ω - μ[quadForm W eps | 𝒟] ω ^ 2)
      =ᵐ[μ] fun ω =>
        ∑ o : O, W ω o o ^ 2
            * (μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω - sig o ω ^ 2)
          + ∑ p ∈ (Finset.univ : Finset O).offDiag,
              (W ω p.1 p.2 ^ 2 + W ω p.1 p.2 * W ω p.2 p.1) * (sig p.1 ω * sig p.2 ω) := by
  filter_upwards [condExp_quadForm_sq 𝒟 hW hi4 hiW4 hpair hmixed hquad,
    condExp_quadForm 𝒟 hW hi2 hiW2 hvar hcross] with ω e1 e2
  rw [e1, e2, sq_sum_diag (fun o : O => W ω o o) (fun o : O => sig o ω)]
  have hcombine : ∑ o : O, W ω o o ^ 2
        * μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω
      - ∑ o : O, W ω o o ^ 2 * sig o ω ^ 2
      = ∑ o : O, W ω o o ^ 2
          * (μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω - sig o ω ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun o _ => by ring
  linarith [hcombine]

/-- **Lemma SM.C.5**, unpackaged form: `E[(ε'Wε)²|𝒟] - (E[ε'Wε|𝒟])² ≤ 3C‖W‖_F²`. The
diagonal part contributes `C ∑_o W²_{oo}` and the off-diagonal part `2C ∑_{o≠o'} W²_{oo'}`. -/
theorem condExp_quadForm_sq_sub_sq_condExp_le [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ)
    {W : Ω → Matrix O O ℝ} {eps sig : O → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hW : ∀ o o', StronglyMeasurable[𝒟] fun ω => W ω o o')
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hiW2 : ∀ p : O × O, Integrable (fun ω => W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω)) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hiW4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
        * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))) μ)
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
    (fun ω => μ[fun ω => quadForm W eps ω ^ 2 | 𝒟] ω - μ[quadForm W eps | 𝒟] ω ^ 2)
      ≤ᵐ[μ] fun ω => 3 * C * rectFrobSq (W ω) := by
  have hid := condExp_quadForm_sq_sub_sq_condExp 𝒟 hW hi2 hiW2 hi4 hiW4 hvar hcross hpair
    hmixed hquad
  have hnn : ∀ᵐ ω ∂μ, ∀ o : O, 0 ≤ sig o ω :=
    ae_all_iff.2 fun o => sig_nonneg 𝒟 (hvar o)
  have hsq : ∀ᵐ ω ∂μ, ∀ o : O, sig o ω ^ 2 ≤ C :=
    ae_all_iff.2 fun o => condExp_sq_sq_le 𝒟 h𝒟 (hi2 (o, o)) (hi4 ((o, o), (o, o)))
      (hvar o) (hfour o)
  have hfr : ∀ᵐ ω ∂μ, ∀ o : O,
      μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω ≤ C :=
    ae_all_iff.2 fun o => hfour o
  filter_upwards [hid, hnn, hsq, hfr] with ω hω hn hs hf
  rw [hω, rectFrobSq_split (W ω)]
  set Dg : ℝ := ∑ o : O, W ω o o ^ 2 with hDg
  set Off : ℝ := ∑ p ∈ (Finset.univ : Finset O).offDiag, W ω p.1 p.2 ^ 2 with hOff
  have hDgnn : 0 ≤ Dg := Finset.sum_nonneg fun o _ => sq_nonneg _
  have hOffnn : 0 ≤ Off := Finset.sum_nonneg fun p _ => sq_nonneg _
  -- `σ²_ε(o)σ²_ε(o') ≤ C`
  have hprod : ∀ o o' : O, sig o ω * sig o' ω ≤ C := by
    intro o o'
    nlinarith [hs o, hs o', hn o, hn o', sq_nonneg (sig o ω - sig o' ω)]
  -- the diagonal bound
  have hdiag : ∑ o : O, W ω o o ^ 2
      * (μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω - sig o ω ^ 2)
      ≤ C * Dg := by
    rw [hDg, Finset.mul_sum]
    refine Finset.sum_le_sum fun o _ => ?_
    have h1 : μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω - sig o ω ^ 2 ≤ C := by
      linarith [hf o, sq_nonneg (sig o ω)]
    calc W ω o o ^ 2
          * (μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ω - sig o ω ^ 2)
        ≤ W ω o o ^ 2 * C := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = C * W ω o o ^ 2 := mul_comm _ _
  -- the off-diagonal bound, via the transposition reindexing
  have hswap : ∑ p ∈ (Finset.univ : Finset O).offDiag,
        W ω p.2 p.1 ^ 2 * (sig p.1 ω * sig p.2 ω)
      = ∑ p ∈ (Finset.univ : Finset O).offDiag,
        W ω p.1 p.2 ^ 2 * (sig p.1 ω * sig p.2 ω) := by
    have h := sum_offDiag_swap
      fun p : O × O => W ω p.1 p.2 ^ 2 * (sig p.1 ω * sig p.2 ω)
    rw [← h]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hstep : ∑ p ∈ (Finset.univ : Finset O).offDiag,
        (W ω p.1 p.2 ^ 2 + W ω p.1 p.2 * W ω p.2 p.1) * (sig p.1 ω * sig p.2 ω)
      ≤ ∑ p ∈ (Finset.univ : Finset O).offDiag,
          (3 / 2 * (W ω p.1 p.2 ^ 2 * (sig p.1 ω * sig p.2 ω))
            + 1 / 2 * (W ω p.2 p.1 ^ 2 * (sig p.1 ω * sig p.2 ω))) := by
    refine Finset.sum_le_sum fun p _ => ?_
    have hsn : 0 ≤ sig p.1 ω * sig p.2 ω := mul_nonneg (hn p.1) (hn p.2)
    nlinarith [mul_nonneg (sq_nonneg (W ω p.1 p.2 - W ω p.2 p.1)) hsn, hsn]
  have hbase : ∑ p ∈ (Finset.univ : Finset O).offDiag,
      W ω p.1 p.2 ^ 2 * (sig p.1 ω * sig p.2 ω) ≤ C * Off := by
    rw [hOff, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    calc W ω p.1 p.2 ^ 2 * (sig p.1 ω * sig p.2 ω)
        ≤ W ω p.1 p.2 ^ 2 * C := mul_le_mul_of_nonneg_left (hprod p.1 p.2) (sq_nonneg _)
      _ = C * W ω p.1 p.2 ^ 2 := mul_comm _ _
  have hoff : ∑ p ∈ (Finset.univ : Finset O).offDiag,
      (W ω p.1 p.2 ^ 2 + W ω p.1 p.2 * W ω p.2 p.1) * (sig p.1 ω * sig p.2 ω)
      ≤ 2 * (C * Off) := by
    refine hstep.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hswap]
    linarith [hbase]
  nlinarith [hdiag, hoff, mul_nonneg hC hDgnn, mul_nonneg hC hOffnn]

/-- **Lemma SM.C.5.** `Var(ε'Wε | 𝒟) ≤ 3C‖W‖_F²`, with `Var(· | 𝒟)` Mathlib's
`ProbabilityTheory.condVar`. -/
theorem condVar_quadForm_le [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ)
    {W : Ω → Matrix O O ℝ} {eps sig : O → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL2 : MemLp (quadForm W eps) 2 μ)
    (hW : ∀ o o', StronglyMeasurable[𝒟] fun ω => W ω o o')
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hiW2 : ∀ p : O × O, Integrable (fun ω => W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω)) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hiW4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
        * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))) μ)
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
    ProbabilityTheory.condVar 𝒟 (quadForm W eps) μ
      ≤ᵐ[μ] fun ω => 3 * C * rectFrobSq (W ω) := by
  have hv := ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp
    (μ := μ) (m := 𝒟) (X := quadForm W eps) h𝒟 hL2
  have hpow : (quadForm W eps) ^ 2 = fun ω => quadForm W eps ω ^ 2 := rfl
  rw [hpow] at hv
  filter_upwards [hv, condExp_quadForm_sq_sub_sq_condExp_le 𝒟 h𝒟 hC hW hi2 hiW2 hi4 hiW4
    hvar hcross hfour hpair hmixed hquad] with ω h1 h2
  rw [h1]
  simpa using h2

end Conditional

/-! ## The moment identities under conditional independence

The identities `hcross`, `hpair`, `hmixed` and `hquad` are derived from
`Multiway.CondIndep.condExp_mul_triple`, which factorizes the conditional expectation of a
product of three slots of a conditionally independent family against a fourth, distinct slot.
Integrability of the products follows from the fourth moments; `hiW2` and `hiW4` remain
hypotheses. -/

section FromCondIndep

open ProbabilityTheory

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {eps : O → Ω → ℝ}

/-! ### Integrability from fourth moments -/

omit [Fintype O] [DecidableEq O] in
theorem integrable_prod1 [IsFiniteMeasure μ] (hmeas : ∀ o, Measurable (eps o))
    (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ) (a : O) :
    Integrable (fun ω => eps a ω) μ :=
  CondIndep.integrable_of_pow_four_bound (a := eps a) (b := fun _ => 1) (c := fun _ => 1)
    (d := fun _ => 1) (hmeas a).aestronglyMeasurable (fun ω => by ring) (hint4 a)
    CondIndep.integrable_one_pow_four CondIndep.integrable_one_pow_four
    CondIndep.integrable_one_pow_four

omit [Fintype O] [DecidableEq O] in
theorem integrable_prod2 [IsFiniteMeasure μ] (hmeas : ∀ o, Measurable (eps o))
    (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ) (a b : O) :
    Integrable (fun ω => eps a ω * eps b ω) μ :=
  CondIndep.integrable_of_pow_four_bound (a := eps a) (b := eps b) (c := fun _ => 1)
    (d := fun _ => 1) ((hmeas a).mul (hmeas b)).aestronglyMeasurable (fun ω => by ring)
    (hint4 a) (hint4 b) CondIndep.integrable_one_pow_four CondIndep.integrable_one_pow_four

omit [Fintype O] [DecidableEq O] in
theorem integrable_prod3 [IsFiniteMeasure μ] (hmeas : ∀ o, Measurable (eps o))
    (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ) (a b c : O) :
    Integrable (fun ω => eps a ω * eps b ω * eps c ω) μ :=
  CondIndep.integrable_of_pow_four_bound (a := eps a) (b := eps b) (c := eps c)
    (d := fun _ => 1) (((hmeas a).mul (hmeas b)).mul (hmeas c)).aestronglyMeasurable
    (fun ω => by ring) (hint4 a) (hint4 b) (hint4 c) CondIndep.integrable_one_pow_four

omit [Fintype O] [DecidableEq O] in
theorem integrable_prod4 [IsFiniteMeasure μ] (hmeas : ∀ o, Measurable (eps o))
    (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ) (a b c d : O) :
    Integrable (fun ω => eps a ω * eps b ω * (eps c ω * eps d ω)) μ :=
  CondIndep.integrable_of_pow_four_bound (a := eps a) (b := eps b) (c := eps c) (d := eps d)
    (((hmeas a).mul (hmeas b)).mul ((hmeas c).mul (hmeas d))).aestronglyMeasurable
    (fun _ => rfl) (hint4 a) (hint4 b) (hint4 c) (hint4 d)

omit [Fintype O] [DecidableEq O] in
theorem integrable_prod4' [IsFiniteMeasure μ] (hmeas : ∀ o, Measurable (eps o))
    (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ) (a b c d : O) :
    Integrable (fun ω => eps a ω * eps b ω * eps c ω * eps d ω) μ :=
  CondIndep.integrable_of_pow_four_bound (a := eps a) (b := eps b) (c := eps c) (d := eps d)
    ((((hmeas a).mul (hmeas b)).mul (hmeas c)).mul (hmeas d)).aestronglyMeasurable
    (fun ω => by ring) (hint4 a) (hint4 b) (hint4 c) (hint4 d)

/-! ### The four identities -/

omit [Fintype O] in
theorem condExp_cross_eq_zero [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    (hmeas : ∀ o, Measurable (eps o)) (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ)
    (hindep : iCondIndepFun 𝒟 h𝒟 eps μ) (hmean : ∀ o, μ[eps o | 𝒟] =ᵐ[μ] 0)
    {o o' : O} (hne : o ≠ o') :
    μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0 :=
  CondIndep.condExp_mul_triple_eq_zero 𝒟 hmeas hindep (i := o) (j := o) (k := o) (l := o')
    hne hne hne (G := fun p : ℝ × ℝ × ℝ => p.1) (H := fun x : ℝ => x)
    measurable_fst measurable_id (integrable_prod1 hmeas hint4 o)
    (integrable_prod1 hmeas hint4 o') (integrable_prod2 hmeas hint4 o o') (hmean o')

omit [Fintype O] in
theorem condExp_pair_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    (hmeas : ∀ o, Measurable (eps o)) (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ)
    (hindep : iCondIndepFun 𝒟 h𝒟 eps μ) {o o' : O} (hne : o ≠ o') :
    μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
      =ᵐ[μ] fun ω => μ[fun ω => eps o ω * eps o ω | 𝒟] ω
        * μ[fun ω => eps o' ω * eps o' ω | 𝒟] ω :=
  CondIndep.condExp_mul_triple 𝒟 hmeas hindep (i := o) (j := o) (k := o) (l := o')
    hne hne hne (G := fun p : ℝ × ℝ × ℝ => p.1 * p.1) (H := fun x : ℝ => x * x)
    (measurable_fst.mul measurable_fst) (measurable_id.mul measurable_id)
    (integrable_prod2 hmeas hint4 o o) (integrable_prod2 hmeas hint4 o' o')
    (integrable_prod4 hmeas hint4 o o o' o')

omit [Fintype O] in
theorem condExp_mixed_eq_zero [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    (hmeas : ∀ o, Measurable (eps o)) (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ)
    (hindep : iCondIndepFun 𝒟 h𝒟 eps μ) (hmean : ∀ o, μ[eps o | 𝒟] =ᵐ[μ] 0)
    (a : O) {o o' : O} (hne : o ≠ o') :
    μ[fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0 := by
  have hG : Measurable (fun r : ℝ × ℝ × ℝ => r.1 * r.1 * r.2.2) :=
    (measurable_fst.mul measurable_fst).mul (measurable_snd.comp measurable_snd)
  by_cases ha : a = o'
  · have hao : a ≠ o := fun h => hne (h.symm.trans ha)
    have h := CondIndep.condExp_mul_triple_eq_zero 𝒟 hmeas hindep (i := a) (j := a) (k := o')
      (l := o) hao hao (Ne.symm hne) (G := fun r : ℝ × ℝ × ℝ => r.1 * r.1 * r.2.2)
      (H := fun x : ℝ => x) hG measurable_id (integrable_prod3 hmeas hint4 a a o')
      (integrable_prod1 hmeas hint4 o) (integrable_prod4' hmeas hint4 a a o' o) (hmean o)
    rw [show (fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω))
        = fun ω => eps a ω * eps a ω * eps o' ω * eps o ω from funext fun ω => by ring]
    exact h
  · have h := CondIndep.condExp_mul_triple_eq_zero 𝒟 hmeas hindep (i := a) (j := a) (k := o)
      (l := o') ha ha hne (G := fun r : ℝ × ℝ × ℝ => r.1 * r.1 * r.2.2)
      (H := fun x : ℝ => x) hG measurable_id (integrable_prod3 hmeas hint4 a a o)
      (integrable_prod1 hmeas hint4 o') (integrable_prod4' hmeas hint4 a a o o') (hmean o')
    rw [show (fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω))
        = fun ω => eps a ω * eps a ω * eps o ω * eps o' ω from funext fun ω => by ring]
    exact h

omit [Fintype O] in
theorem condExp_quad_eq_zero [StandardBorelSpace Ω] [IsFiniteMeasure μ] {h𝒟 : 𝒟 ≤ mΩ}
    (hmeas : ∀ o, Measurable (eps o)) (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ)
    (hindep : iCondIndepFun 𝒟 h𝒟 eps μ) (hmean : ∀ o, μ[eps o | 𝒟] =ᵐ[μ] 0)
    (p q : O × O) (_hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) (hqp : q ≠ p) (hqT : q ≠ (p.2, p.1)) :
    μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0 := by
  have hG : Measurable (fun r : ℝ × ℝ × ℝ => r.1 * r.2.1 * r.2.2) :=
    (measurable_fst.mul (measurable_fst.comp measurable_snd)).mul
      (measurable_snd.comp measurable_snd)
  have hswap : (fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω))
      = fun ω => eps p.1 ω * eps p.2 ω * eps q.2 ω * eps q.1 ω := funext fun ω => by ring
  have hkeep : (fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω))
      = fun ω => eps p.1 ω * eps p.2 ω * eps q.1 ω * eps q.2 ω := funext fun ω => by ring
  by_cases h1 : q.2 = p.1
  · have hq1a : q.1 ≠ p.1 := fun h => hq (h.trans h1.symm)
    have hq1b : q.1 ≠ p.2 := fun h => hqT (Prod.ext_iff.mpr ⟨h, h1⟩)
    have h := CondIndep.condExp_mul_triple_eq_zero 𝒟 hmeas hindep (i := p.1) (j := p.2)
      (k := q.2) (l := q.1) (Ne.symm hq1a) (Ne.symm hq1b) (Ne.symm hq)
      (G := fun r : ℝ × ℝ × ℝ => r.1 * r.2.1 * r.2.2) (H := fun x : ℝ => x) hG measurable_id
      (integrable_prod3 hmeas hint4 p.1 p.2 q.2) (integrable_prod1 hmeas hint4 q.1)
      (integrable_prod4' hmeas hint4 p.1 p.2 q.2 q.1) (hmean q.1)
    rw [hswap]
    exact h
  by_cases h2 : q.2 = p.2
  · have hq1a : q.1 ≠ p.2 := fun h => hq (h.trans h2.symm)
    have hq1b : q.1 ≠ p.1 := fun h => hqp (Prod.ext_iff.mpr ⟨h, h2⟩)
    have h := CondIndep.condExp_mul_triple_eq_zero 𝒟 hmeas hindep (i := p.1) (j := p.2)
      (k := q.2) (l := q.1) (Ne.symm hq1b) (Ne.symm hq1a) (Ne.symm hq)
      (G := fun r : ℝ × ℝ × ℝ => r.1 * r.2.1 * r.2.2) (H := fun x : ℝ => x) hG measurable_id
      (integrable_prod3 hmeas hint4 p.1 p.2 q.2) (integrable_prod1 hmeas hint4 q.1)
      (integrable_prod4' hmeas hint4 p.1 p.2 q.2 q.1) (hmean q.1)
    rw [hswap]
    exact h
  · have h := CondIndep.condExp_mul_triple_eq_zero 𝒟 hmeas hindep (i := p.1) (j := p.2)
      (k := q.1) (l := q.2) (Ne.symm h1) (Ne.symm h2) hq
      (G := fun r : ℝ × ℝ × ℝ => r.1 * r.2.1 * r.2.2) (H := fun x : ℝ => x) hG measurable_id
      (integrable_prod3 hmeas hint4 p.1 p.2 q.1) (integrable_prod1 hmeas hint4 q.2)
      (integrable_prod4' hmeas hint4 p.1 p.2 q.1 q.2) (hmean q.2)
    rw [hkeep]
    exact h

/-! ### Main theorem -/

theorem condVar_quadForm_le_of_condIndep [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {h𝒟 : 𝒟 ≤ mΩ} {W : Ω → Matrix O O ℝ} {eps : O → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL2 : MemLp (quadForm W eps) 2 μ)
    (hW : ∀ o o', StronglyMeasurable[𝒟] fun ω => W ω o o')
    (hiW2 : ∀ p : O × O, Integrable (fun ω => W ω p.1 p.2 * (eps p.1 ω * eps p.2 ω)) μ)
    (hiW4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => W ω r.1.1 r.1.2 * W ω r.2.1 r.2.2
        * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))) μ)
    (hmeas : ∀ o, Measurable (eps o))
    (hint4 : ∀ o, Integrable (fun ω => eps o ω ^ 4) μ)
    (hindep : iCondIndepFun 𝒟 h𝒟 eps μ)
    (hmean : ∀ o, μ[eps o | 𝒟] =ᵐ[μ] 0)
    (hfour : ∀ o, μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ≤ᵐ[μ] fun _ => C) :
    ProbabilityTheory.condVar 𝒟 (quadForm W eps) μ ≤ᵐ[μ] fun ω => 3 * C * rectFrobSq (W ω) :=
  condVar_quadForm_le 𝒟 h𝒟 hC hL2 hW
    (fun p => integrable_prod2 hmeas hint4 p.1 p.2) hiW2
    (fun r => integrable_prod4 hmeas hint4 r.1.1 r.1.2 r.2.1 r.2.2) hiW4
    (sig := fun o => μ[fun ω => eps o ω * eps o ω | 𝒟]) (fun _ => Filter.EventuallyEq.rfl)
    (fun _ _ h => condExp_cross_eq_zero 𝒟 hmeas hint4 hindep hmean h) hfour
    (fun _ _ h => condExp_pair_eq 𝒟 hmeas hint4 hindep h)
    (fun a _ _ h => condExp_mixed_eq_zero 𝒟 hmeas hint4 hindep hmean a h)
    (fun p q h1 h2 h3 h4 => condExp_quad_eq_zero 𝒟 hmeas hint4 hindep hmean p q h1 h2 h3 h4)

end FromCondIndep

/-! ## Non-vacuity

A deterministic model on a one-point space satisfying every hypothesis of
`condVar_quadForm_le`. -/

section Witness

open MeasureTheory

/-- On a one-point space every function is constant. -/
theorem eq_const_unit (f : Unit → ℝ) : f = fun _ : Unit => f () :=
  funext fun u => by cases u; rfl

/-- Every real function on the one-point space is integrable for the Dirac law. -/
theorem integrable_unit (f : Unit → ℝ) : Integrable f (Measure.dirac ()) := by
  rw [eq_const_unit f]
  exact integrable_const _

/-- Every real function on the one-point space lies in `L²`. -/
theorem memLp_unit (f : Unit → ℝ) : MemLp f 2 (Measure.dirac ()) := by
  rw [eq_const_unit f]
  exact memLp_const _

/-- Conditioning on the trivial σ-algebra over a one-point space returns the function. -/
theorem condExp_unit (f : Unit → ℝ) :
    (Measure.dirac ())[f | (⊥ : MeasurableSpace Unit)] = f := by
  conv_lhs => rw [eq_const_unit f]
  rw [condExp_const bot_le]

/-- The disturbance `ε_o = 𝟙{o = o₀}`, constant in `ω`. -/
def witnessEps {O : Type*} [DecidableEq O] (o₀ : O) : O → Unit → ℝ :=
  fun o _ => if o = o₀ then (1 : ℝ) else 0

theorem witnessEps_mul_self {O : Type*} [DecidableEq O] (o₀ o : O) (u : Unit) :
    witnessEps o₀ o u * witnessEps o₀ o u = if o = o₀ then (1 : ℝ) else 0 := by
  by_cases h : o = o₀ <;> simp [witnessEps, h]

theorem witnessEps_mul_eq_zero {O : Type*} [DecidableEq O] (o₀ : O) {o o' : O} (h : o ≠ o')
    (u : Unit) : witnessEps o₀ o u * witnessEps o₀ o' u = 0 := by
  by_cases h1 : o = o₀
  · have h2 : o' ≠ o₀ := fun h3 => h (h1.trans h3.symm)
    simp [witnessEps, h2]
  · simp [witnessEps, h1]

/-- The all-ones matrix, the witness's `W`. -/
def witnessW (O : Type*) : Matrix O O ℝ := fun _ _ => (1 : ℝ)

/-- `condVar_quadForm_le` on the model `Ω = Unit`, `μ = dirac ()`, `𝒟 = ⊥`, `W ≡ 1`,
`ε_o = 𝟙{o = o₀}`, `σ²_ε(o) = 𝟙{o = o₀}`, `C = 1`. -/
theorem condVar_quadForm_le_witness {O : Type*} [Fintype O] [DecidableEq O] (o₀ : O) :
    ProbabilityTheory.condVar (⊥ : MeasurableSpace Unit)
        (quadForm (fun _ : Unit => witnessW O) (witnessEps o₀)) (Measure.dirac ())
      ≤ᵐ[Measure.dirac ()] fun _ : Unit => 3 * (1 : ℝ) * rectFrobSq (witnessW O) := by
  refine condVar_quadForm_le (⊥ : MeasurableSpace Unit) bot_le (C := (1 : ℝ)) zero_le_one
    (W := fun _ : Unit => witnessW O) (eps := witnessEps o₀)
    (sig := fun o _ => if o = o₀ then (1 : ℝ) else 0)
    (memLp_unit _) (fun _ _ => stronglyMeasurable_const)
    (fun _ => integrable_unit _) (fun _ => integrable_unit _)
    (fun _ => integrable_unit _) (fun _ => integrable_unit _) ?_ ?_ ?_ ?_ ?_ ?_
  · intro o
    rw [condExp_unit]
    exact Filter.Eventually.of_forall fun u => witnessEps_mul_self o₀ o u
  · intro o o' h
    rw [condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show witnessEps o₀ o u * witnessEps o₀ o' u = (0 : ℝ)
    exact witnessEps_mul_eq_zero o₀ h u
  · intro o
    rw [condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show witnessEps o₀ o u * witnessEps o₀ o u
        * (witnessEps o₀ o u * witnessEps o₀ o u) ≤ (1 : ℝ)
    rw [witnessEps_mul_self o₀ o u]
    by_cases h : o = o₀ <;> simp [h]
  · intro o o' h
    rw [condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show witnessEps o₀ o u * witnessEps o₀ o u
        * (witnessEps o₀ o' u * witnessEps o₀ o' u)
        = (if o = o₀ then (1 : ℝ) else 0) * (if o' = o₀ then (1 : ℝ) else 0)
    rw [witnessEps_mul_self o₀ o u, witnessEps_mul_self o₀ o' u]
  · intro a o o' h
    rw [condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show witnessEps o₀ a u * witnessEps o₀ a u
        * (witnessEps o₀ o u * witnessEps o₀ o' u) = (0 : ℝ)
    rw [witnessEps_mul_eq_zero o₀ h u, mul_zero]
  · intro p q hp _ _ _
    rw [condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show witnessEps o₀ p.1 u * witnessEps o₀ p.2 u
        * (witnessEps o₀ q.1 u * witnessEps o₀ q.2 u) = (0 : ℝ)
    rw [witnessEps_mul_eq_zero o₀ hp u, zero_mul]

end Witness

namespace CondIndepWitness

open MeasureTheory ProbabilityTheory
open Multiway.GeneralWitness

/-- Truncation to `[-1,1]`: the identity on `{-1, 1}`, and bounded. -/
def clamp (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem measurable_clamp : Measurable clamp := by
  unfold clamp
  fun_prop

theorem clamp_one : clamp 1 = 1 := by norm_num [clamp]

theorem clamp_neg_one : clamp (-1) = -1 := by norm_num [clamp]

theorem neg_one_le_clamp (x : ℝ) : -1 ≤ clamp x := le_max_left _ _

theorem clamp_le_one (x : ℝ) : clamp x ≤ 1 := max_le (by norm_num) (min_le_left 1 x)

theorem abs_clamp_le (x : ℝ) : |clamp x| ≤ 1 := abs_le.2 ⟨neg_one_le_clamp x, clamp_le_one x⟩

theorem abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) :
    |a| * |b| ≤ A * B := mul_le_mul ha hb (abs_nonneg b) hA

theorem pow4_le_one {x : ℝ} (h : |x| ≤ 1) : x * x * (x * x) ≤ 1 := by
  have h' := abs_le.1 h
  have hy : x * x ≤ 1 := by nlinarith [h'.1, h'.2]
  have hy0 : 0 ≤ x * x := mul_self_nonneg x
  nlinarith [hy, hy0]

theorem abs_pow4_le_one {x : ℝ} (h : |x| ≤ 1) : |x * x * (x * x)| ≤ 1 := by
  rw [abs_of_nonneg (mul_nonneg (mul_self_nonneg x) (mul_self_nonneg x))]
  exact pow4_le_one h

section Model

variable (O : Type*) [Fintype O] [DecidableEq O]

/-- The sample space: one fair sign per observation, plus a design coordinate indexed by
`none`. -/
noncomputable def wP : Measure (Option O → ℝ) := gmu (Option O)

instance instIsProbabilityMeasureWP : IsProbabilityMeasure (wP O) := by
  unfold wP
  infer_instance

set_option warn.classDefReducibility false in
/-- `𝒟 = σ(design coordinate)`, a proper sub-σ-algebra. -/
def wD : MeasurableSpace (Option O → ℝ) :=
  MeasurableSpace.comap (fun ω : Option O → ℝ => ω none) inferInstance

omit [Fintype O] [DecidableEq O] in
theorem wD_le : wD O ≤ (inferInstance : MeasurableSpace (Option O → ℝ)) :=
  (measurable_pi_apply none).comap_le

/-- The innovations. -/
def wEps (o : O) (ω : Option O → ℝ) : ℝ := clamp (ω (some o))

/-- The coefficient matrix: every entry is `1 + (design coordinate)`, a `𝒟`-measurable
random variable taking the values `2` and `0`. -/
def wMat (ω : Option O → ℝ) : Matrix O O ℝ := fun _ _ => 1 + clamp (ω none)

omit [Fintype O] [DecidableEq O] in
theorem measurable_wEps (o : O) : Measurable (wEps O o) :=
  measurable_clamp.comp (measurable_pi_apply (some o))

omit [Fintype O] [DecidableEq O] in
theorem abs_wEps_le (o : O) (ω : Option O → ℝ) : |wEps O o ω| ≤ 1 := abs_clamp_le _

omit [Fintype O] [DecidableEq O] in
theorem abs_wMat_le (ω : Option O → ℝ) (o o' : O) : |wMat O ω o o'| ≤ 2 := by
  have h1 := neg_one_le_clamp (ω none)
  have h2 := clamp_le_one (ω none)
  rw [abs_le]
  constructor <;> simp only [wMat] <;> linarith

omit [DecidableEq O] in
theorem integrable_of_bound {f : (Option O → ℝ) → ℝ} (hf : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f (wP O) :=
  Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)

/-! ### The family is independent, and jointly independent of the design -/

omit [DecidableEq O] in
theorem wIndepCoord :
    iIndepFun (fun (i : Option O) (ω : Option O → ℝ) => ω i) (wP O) := by
  unfold wP gmu
  exact iIndepFun_pi (μ := fun _ : Option O => ClauseAWitness.signLaw)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)

omit [DecidableEq O] in
theorem wIndep : iIndepFun (wEps O) (wP O) :=
  ((wIndepCoord O).precomp (Option.some_injective O)).comp (fun _ => clamp)
    (fun _ => measurable_clamp)

omit [Fintype O] [DecidableEq O] in
theorem wEps_comap_le (o : O) :
    MeasurableSpace.comap (wEps O o) inferInstance
      ≤ MeasurableSpace.comap (fun ω : Option O → ℝ => ω (some o)) inferInstance :=
  (measurable_clamp.comp
    (measurable_iff_comap_le.2 (le_refl
      (MeasurableSpace.comap (fun ω : Option O → ℝ => ω (some o)) inferInstance)))).comap_le

omit [DecidableEq O] in
theorem wIndepD :
    Indep (⨆ o : O, MeasurableSpace.comap (wEps O o) inferInstance) (wD O) (wP O) := by
  have hind : iIndep (fun i : Option O =>
      MeasurableSpace.comap (fun ω : Option O → ℝ => ω i) inferInstance) (wP O) :=
    wIndepCoord O
  have hdisj : Disjoint (Set.range (Option.some : O → Option O)) ({none} : Set (Option O)) :=
    Set.disjoint_singleton_right.2 (by simp)
  have h := indep_iSup_of_disjoint
    (m := fun i : Option O =>
      MeasurableSpace.comap (fun ω : Option O → ℝ => ω i) inferInstance)
    (fun i => (measurable_pi_apply i).comap_le) hind hdisj
  have hsing : (⨆ i ∈ ({none} : Set (Option O)),
      MeasurableSpace.comap (fun ω : Option O → ℝ => ω i) inferInstance) = wD O :=
    iSup_singleton
  rw [hsing] at h
  refine indep_of_indep_of_le_left h (iSup_le fun o => (wEps_comap_le O o).trans ?_)
  exact le_iSup₂ (f := fun (i : Option O) (_ : i ∈ Set.range (Option.some : O → Option O)) =>
    MeasurableSpace.comap (fun ω : Option O → ℝ => ω i) inferInstance)
    (some o) (Set.mem_range_self o)

omit [DecidableEq O] in
/-- Conditional independence of the innovations given `𝒟`. -/
theorem wCondIndep : iCondIndepFun (wD O) (wD_le O) (wEps O) (wP O) :=
  Multiway.CondIndep.iCondIndepFun_of_indep (wD O) (measurable_wEps O) (wIndep O) (wIndepD O)

/-! ### The mean-zero and fourth-moment hypotheses on this model -/

omit [DecidableEq O] in
theorem wMean (o : O) : (wP O)[wEps O o | wD O] =ᵐ[wP O] 0 := by
  have hI : Indep (MeasurableSpace.comap (wEps O o) inferInstance) (wD O) (wP O) :=
    indep_of_indep_of_le_left (wIndepD O)
      (le_iSup (fun o : O => MeasurableSpace.comap (wEps O o) inferInstance) o)
  have hsm : StronglyMeasurable[MeasurableSpace.comap (wEps O o) inferInstance] (wEps O o) :=
    (measurable_iff_comap_le.2 (le_refl
      (MeasurableSpace.comap (wEps O o) inferInstance))).stronglyMeasurable
  have h := condExp_indep_eq (measurable_wEps O o).comap_le (wD_le O) hsm hI
  have hzero : ∫ ω, wEps O o ω ∂(wP O) = 0 := by
    have hg := gintegral (W := Option O) (f := clamp) measurable_clamp (some o)
    rw [clamp_one, clamp_neg_one] at hg
    simpa [wP, wEps, gU] using hg
  filter_upwards [h] with ω hω
  rw [hω]
  simpa using hzero

omit [DecidableEq O] in
theorem wFour (o : O) :
    (wP O)[fun ω => wEps O o ω * wEps O o ω * (wEps O o ω * wEps O o ω) | wD O]
      ≤ᵐ[wP O] fun _ => (1 : ℝ) := by
  have hi : Integrable
      (fun ω => wEps O o ω * wEps O o ω * (wEps O o ω * wEps O o ω)) (wP O) :=
    integrable_of_bound O
      (((measurable_wEps O o).mul (measurable_wEps O o)).mul
        ((measurable_wEps O o).mul (measurable_wEps O o))) (B := 1)
      (fun ω => abs_pow4_le_one (abs_wEps_le O o ω))
  have hle : (fun ω => wEps O o ω * wEps O o ω * (wEps O o ω * wEps O o ω))
      ≤ᵐ[wP O] fun _ => (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun ω => pow4_le_one (abs_wEps_le O o ω)
  have hmono := condExp_mono (m := wD O) hi (integrable_const (1 : ℝ)) hle
  rwa [condExp_const (wD_le O)] at hmono

/-! ### The remaining side conditions, all from boundedness -/

theorem pow4_eq (x : ℝ) : x ^ 4 = x * x * (x * x) := by ring

omit [DecidableEq O] in
theorem wInt4 (o : O) : Integrable (fun ω => wEps O o ω ^ 4) (wP O) :=
  integrable_of_bound O ((measurable_wEps O o).pow_const 4) (B := 1) (fun ω => by
    rw [pow4_eq]
    exact abs_pow4_le_one (abs_wEps_le O o ω))

omit [Fintype O] [DecidableEq O] in
theorem wMeasurableW (o o' : O) : StronglyMeasurable[wD O] (fun ω => wMat O ω o o') := by
  exact ((measurable_clamp.comp
    (measurable_iff_comap_le.2 (le_refl (wD O)))).const_add 1).stronglyMeasurable

omit [DecidableEq O] in
theorem wIW2 (p : O × O) :
    Integrable (fun ω => wMat O ω p.1 p.2 * (wEps O p.1 ω * wEps O p.2 ω)) (wP O) := by
  refine integrable_of_bound O ?_ (B := 2) (fun ω => ?_)
  · exact ((measurable_clamp.comp (measurable_pi_apply none)).const_add 1).mul
      ((measurable_wEps O p.1).mul (measurable_wEps O p.2))
  · simp only [abs_mul]
    have h1 := abs_wMat_le O ω p.1 p.2
    have h2 := abs_wEps_le O p.1 ω
    have h3 := abs_wEps_le O p.2 ω
    have hin : |wEps O p.1 ω| * |wEps O p.2 ω| ≤ 1 * 1 := abs_mul_le_of h2 h3 zero_le_one
    have hall := mul_le_mul h1 hin (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num : (0:ℝ) ≤ 2)
    linarith

omit [DecidableEq O] in
theorem wIW4 (r : (O × O) × (O × O)) :
    Integrable (fun ω => wMat O ω r.1.1 r.1.2 * wMat O ω r.2.1 r.2.2
      * (wEps O r.1.1 ω * wEps O r.1.2 ω * (wEps O r.2.1 ω * wEps O r.2.2 ω))) (wP O) := by
  refine integrable_of_bound O ?_ (B := 4) (fun ω => ?_)
  · exact (((measurable_clamp.comp (measurable_pi_apply none)).const_add 1).mul
      ((measurable_clamp.comp (measurable_pi_apply none)).const_add 1)).mul
      (((measurable_wEps O r.1.1).mul (measurable_wEps O r.1.2)).mul
        ((measurable_wEps O r.2.1).mul (measurable_wEps O r.2.2)))
  · simp only [abs_mul]
    have a1 := abs_wMat_le O ω r.1.1 r.1.2
    have a2 := abs_wMat_le O ω r.2.1 r.2.2
    have b1 := abs_wEps_le O r.1.1 ω
    have b2 := abs_wEps_le O r.1.2 ω
    have b3 := abs_wEps_le O r.2.1 ω
    have b4 := abs_wEps_le O r.2.2 ω
    have hw : |wMat O ω r.1.1 r.1.2| * |wMat O ω r.2.1 r.2.2| ≤ 2 * 2 :=
      abs_mul_le_of a1 a2 (by norm_num)
    have he1 : |wEps O r.1.1 ω| * |wEps O r.1.2 ω| ≤ 1 * 1 := abs_mul_le_of b1 b2 zero_le_one
    have he2 : |wEps O r.2.1 ω| * |wEps O r.2.2 ω| ≤ 1 * 1 := abs_mul_le_of b3 b4 zero_le_one
    have he := mul_le_mul he1 he2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num : (0:ℝ) ≤ 1 * 1)
    have hall := mul_le_mul hw he
      (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))) (by norm_num : (0:ℝ) ≤ 2 * 2)
    linarith

omit [DecidableEq O] in
theorem abs_quadForm_le (ω : Option O → ℝ) :
    |quadForm (wMat O) (wEps O) ω| ≤ 2 * (Fintype.card (O × O) : ℝ) := by
  rw [quadForm_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (O × O)),
      |wMat O ω p.1 p.2 * (wEps O p.1 ω * wEps O p.2 ω)| ≤ (2 : ℝ) := by
    intro p _
    simp only [abs_mul]
    have h1 := abs_wMat_le O ω p.1 p.2
    have h2 := abs_wEps_le O p.1 ω
    have h3 := abs_wEps_le O p.2 ω
    have hin : |wEps O p.1 ω| * |wEps O p.2 ω| ≤ 1 * 1 := abs_mul_le_of h2 h3 zero_le_one
    have hall := mul_le_mul h1 hin (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num : (0:ℝ) ≤ 2)
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [DecidableEq O] in
theorem wL2 : MemLp (quadForm (wMat O) (wEps O)) 2 (wP O) := by
  have hmeas : Measurable (quadForm (wMat O) (wEps O)) := by
    rw [quadForm_eq]
    exact Finset.measurable_sum _ fun p _ =>
      ((measurable_clamp.comp (measurable_pi_apply none)).const_add 1).mul
        ((measurable_wEps O p.1).mul (measurable_wEps O p.2))
  exact MemLp.of_bound hmeas.aestronglyMeasurable (2 * (Fintype.card (O × O) : ℝ))
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_quadForm_le O ω)

/-! ### The three non-degeneracy facts -/

omit [Fintype O] in
theorem wD_proper (o₀ : O) :
    ∃ B : Set (Option O → ℝ), MeasurableSet B ∧ ¬ MeasurableSet[wD O] B := by
  refine ⟨(fun ω : Option O → ℝ => ω (some o₀)) ⁻¹' (Set.Ioi (0 : ℝ)),
    (measurable_pi_apply (some o₀)) measurableSet_Ioi, ?_⟩
  rintro ⟨t, -, ht⟩
  have h1 : (fun i : Option O => if i = some o₀ then (1 : ℝ) else 0)
      ∈ (fun ω : Option O → ℝ => ω (some o₀)) ⁻¹' (Set.Ioi (0 : ℝ)) := by
    simp [Set.mem_Ioi]
  have h2 : (fun _ : Option O => (0 : ℝ))
      ∉ (fun ω : Option O → ℝ => ω (some o₀)) ⁻¹' (Set.Ioi (0 : ℝ)) := by
    simp [Set.mem_Ioi]
  rw [← ht] at h1 h2
  simp only [Set.mem_preimage] at h1 h2
  exact h2 (by simpa using h1)

omit [Fintype O] [DecidableEq O] in
theorem wMat_one (o o' : O) : wMat O (fun _ => (1 : ℝ)) o o' = 2 := by
  norm_num [wMat, clamp_one]

omit [Fintype O] [DecidableEq O] in
theorem wMat_neg_one (o o' : O) : wMat O (fun _ => (-1 : ℝ)) o o' = 0 := by
  simp [wMat, clamp_neg_one]

omit [DecidableEq O] in
theorem rectFrobSq_wMat_neg_one : rectFrobSq (wMat O (fun _ => (-1 : ℝ))) = 0 := by
  simp [rectFrobSq, wMat_neg_one]

omit [DecidableEq O] in
theorem rectFrobSq_wMat_one (o₀ : O) : rectFrobSq (wMat O (fun _ => (1 : ℝ))) ≠ 0 := by
  have h : rectFrobSq (wMat O (fun _ => (1 : ℝ)))
      = ∑ _a : O, ∑ _b : O, (4 : ℝ) := by
    simp only [rectFrobSq, wMat_one]
    norm_num
  rw [h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (0 : ℝ) < (Fintype.card O : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨o₀⟩
  positivity

omit [DecidableEq O] in
theorem wEps_second_moment (o : O) :
    ∫ ω, wEps O o ω * wEps O o ω ∂(wP O) = 1 := by
  have hg := gintegral (W := Option O) (f := fun x => clamp x * clamp x)
    (measurable_clamp.mul measurable_clamp) (some o)
  rw [clamp_one, clamp_neg_one] at hg
  simpa [wP, wEps, gU] using hg


/-! ### Main theorem -/

/-- Non-vacuity of `condVar_quadForm_le_of_condIndep` with a non-trivial `𝒟`. The four
conjuncts: the conclusion holds on this model; `𝒟` is a proper sub-σ-algebra; `‖W‖_F²` is a
non-constant function of `ω`; and `E[ε_o²] = 1 ≠ 0`. On this model the innovations are
independent of `𝒟`. -/
theorem condVar_quadForm_le_of_condIndep_witness (o₀ : O) :
    ProbabilityTheory.condVar (wD O) (quadForm (wMat O) (wEps O)) (wP O)
        ≤ᵐ[wP O] (fun ω => 3 * (1 : ℝ) * rectFrobSq (wMat O ω))
    ∧ (∃ B : Set (Option O → ℝ), MeasurableSet B ∧ ¬ MeasurableSet[wD O] B)
    ∧ rectFrobSq (wMat O (fun _ => (1 : ℝ))) ≠ rectFrobSq (wMat O (fun _ => (-1 : ℝ)))
    ∧ ∫ ω, wEps O o₀ ω * wEps O o₀ ω ∂(wP O) = 1 := by
  refine ⟨?_, wD_proper O o₀, ?_, wEps_second_moment O o₀⟩
  · exact condVar_quadForm_le_of_condIndep (wD O) (h𝒟 := wD_le O) zero_le_one (wL2 O)
      (wMeasurableW O) (wIW2 O) (wIW4 O) (measurable_wEps O) (wInt4 O) (wCondIndep O)
      (wMean O) (wFour O)
  · rw [rectFrobSq_wMat_neg_one]
    exact rectFrobSq_wMat_one O o₀

end Model

end CondIndepWitness

end Quadform
end Multiway
