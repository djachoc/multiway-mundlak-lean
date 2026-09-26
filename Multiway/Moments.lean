import Multiway.CondIndep
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul

/-!
# Fourth moments pass to the idiosyncratic component

This file formalizes Lemma SM.B.5 of the paper (fourth moments pass to the idiosyncratic
component): under the Regime-1 decomposition `ν_o = ∑_m a^{(m)}_{i_m(o)} + ε_o` and the moment
bound `E[ν_o⁴ | 𝒟] ≤ C`, one has `E[ε_o⁴ | 𝒟] ≤ E[ν_o⁴ | 𝒟] ≤ C`. The proof is conditional
Jensen at `x ↦ x⁴` applied to a splitting `ν = U + V` in which `V` has vanishing conditional
mean given `σ(U, 𝒟)`.

## Notation

* `mD` is `𝒟`; `mG` is an intermediate σ-algebra `mD ≤ mG ≤ mΩ` playing the role of `σ(U, 𝒟)`.
* `eps` is `ε_o`, and `A m` is the category-level shock `a^{(m)}_{i_m(o)}`.
* `hA0` states `E[a^{(m)} | mG] = 0` for each dimension.

## Main results

* `condExp_pow_four_le_of_condExp_eq_zero`: the Jensen step for an arbitrary splitting.
* `condExp_fourth_idiosyncratic_le_const`: Lemma SM.B.5, given `hA0`.
* `condExp_sup_eq_zero_of_condIndepFun`: `E[X | σ(Y, 𝒟)] = 0` from conditional independence.
* `condExp_fourth_idiosyncratic_le_const_regime1`: Lemma SM.B.5 under conditional independence.
-/

namespace Multiway
namespace Moments

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Workhorse

/-- The Jensen step for an arbitrary splitting `ν = U + V`: if `U` is `mG`-measurable and `V`
has vanishing `mG`-conditional mean, then `E[U⁴ | mD] ≤ E[(U + V)⁴ | mD]`. -/
theorem condExp_pow_four_le_of_condExp_eq_zero
    [IsFiniteMeasure μ] {mD mG : MeasurableSpace Ω} (hDG : mD ≤ mG) (hG : mG ≤ mΩ)
    {U V : Ω → ℝ} (hUm : StronglyMeasurable[mG] U)
    (hU : Integrable U μ) (hV : Integrable V μ)
    (hU4 : Integrable (fun ω => U ω ^ 4) μ)
    (hUV4 : Integrable (fun ω => (U ω + V ω) ^ 4) μ)
    (hV0 : μ[V | mG] =ᵐ[μ] 0) :
    μ[fun ω => U ω ^ 4 | mD] ≤ᵐ[μ] μ[fun ω => (U ω + V ω) ^ 4 | mD] := by
  have hUV : Integrable (U + V) μ := hU.add hV
  -- `E[U + V | mG] = U`
  have h1 : μ[U + V | mG] =ᵐ[μ] U := by
    refine (condExp_add hU hV mG).trans ?_
    rw [condExp_of_stronglyMeasurable hG hUm hU]
    filter_upwards [hV0] with ω hω
    simp [hω]
  -- conditional Jensen at the convex function `x ↦ x⁴`
  have hcvx : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 4) :=
    Even.convexOn_pow (by decide)
  have hlsc : LowerSemicontinuous (fun x : ℝ => x ^ 4) :=
    (continuous_pow 4).lowerSemicontinuous
  have hjen := hcvx.map_condExp_le_univ (m := mG) hG hlsc hUV hUV4
  have h2 : (fun ω => U ω ^ 4) ≤ᵐ[μ] μ[fun ω => (U ω + V ω) ^ 4 | mG] := by
    filter_upwards [hjen, h1] with ω h h'
    simp only [Function.comp_apply] at h
    rw [h'] at h
    exact h
  -- condition on `mD` and use the tower property
  have h3 := condExp_mono (m := mD) hU4 integrable_condExp h2
  have h4 := condExp_condExp_of_le (μ := μ) (f := fun ω => (U ω + V ω) ^ 4) hDG hG
  filter_upwards [h3, h4] with ω ha hb
  exact ha.trans hb.le

/-- The `mG`-conditional mean of `V := ∑_m a^{(m)}_{i_m(o)}` vanishes as soon as each
summand's does. -/
theorem condExp_sum_eq_zero {D : Type*} {mG : MeasurableSpace Ω} {dims : Finset D}
    {A : D → Ω → ℝ} (hA : ∀ m ∈ dims, Integrable (A m) μ)
    (hA0 : ∀ m ∈ dims, μ[A m | mG] =ᵐ[μ] 0) :
    μ[∑ m ∈ dims, A m | mG] =ᵐ[μ] 0 := by
  refine (condExp_finsetSum hA mG).trans ?_
  have h : ∀ᵐ ω ∂μ, ∀ m ∈ dims, μ[A m | mG] ω = 0 :=
    (Filter.eventually_all_finset dims).2 fun m hm => by
      filter_upwards [hA0 m hm] with ω hω using hω
  filter_upwards [h] with ω hω
  simpa using Finset.sum_eq_zero hω

end Workhorse

section Lemma

variable {D : Type*} {dims : Finset D} {A : D → Ω → ℝ} {eps nu : Ω → ℝ} {C : ℝ}

/-- **Lemma SM.B.5, first inequality.** Under `ν_o = ∑_m a^{(m)}_{i_m(o)} + ε_o`,
`E[ε_o⁴ | 𝒟] ≤ E[ν_o⁴ | 𝒟]`. -/
theorem condExp_fourth_idiosyncratic_le
    [IsFiniteMeasure μ] {mD mG : MeasurableSpace Ω} (hDG : mD ≤ mG) (hG : mG ≤ mΩ)
    (hnu : nu = eps + ∑ m ∈ dims, A m)
    (hepsm : StronglyMeasurable[mG] eps)
    (heps : Integrable eps μ) (hA : ∀ m ∈ dims, Integrable (A m) μ)
    (hA0 : ∀ m ∈ dims, μ[A m | mG] =ᵐ[μ] 0)
    (heps4 : Integrable (fun ω => eps ω ^ 4) μ)
    (hnu4 : Integrable (fun ω => nu ω ^ 4) μ) :
    μ[fun ω => eps ω ^ 4 | mD] ≤ᵐ[μ] μ[fun ω => nu ω ^ 4 | mD] := by
  subst hnu
  exact condExp_pow_four_le_of_condExp_eq_zero hDG hG hepsm heps
    (integrable_finsetSum' _ hA) heps4 hnu4 (condExp_sum_eq_zero hA hA0)

/-- **Lemma SM.B.5.** `E[ε_o⁴ | 𝒟] ≤ E[ν_o⁴ | 𝒟] ≤ C`. -/
theorem condExp_fourth_idiosyncratic_le_const
    [IsFiniteMeasure μ] {mD mG : MeasurableSpace Ω} (hDG : mD ≤ mG) (hG : mG ≤ mΩ)
    (hnu : nu = eps + ∑ m ∈ dims, A m)
    (hepsm : StronglyMeasurable[mG] eps)
    (heps : Integrable eps μ) (hA : ∀ m ∈ dims, Integrable (A m) μ)
    (hA0 : ∀ m ∈ dims, μ[A m | mG] =ᵐ[μ] 0)
    (heps4 : Integrable (fun ω => eps ω ^ 4) μ)
    (hnu4 : Integrable (fun ω => nu ω ^ 4) μ)
    (hC : μ[fun ω => nu ω ^ 4 | mD] ≤ᵐ[μ] fun _ => C) :
    μ[fun ω => eps ω ^ 4 | mD] ≤ᵐ[μ] fun _ => C := by
  filter_upwards [condExp_fourth_idiosyncratic_le hDG hG hnu hepsm heps hA hA0 heps4 hnu4, hC]
    with ω h1 h2
  exact h1.trans h2

/-- **Lemma SM.B.5, category-level part.** `E[V⁴ | 𝒟] ≤ E[ν⁴ | 𝒟] ≤ C`, with the roles of
the two summands exchanged and the intermediate σ-algebra `mG'`. -/
theorem condExp_fourth_components_le
    [IsFiniteMeasure μ] {mD mG' : MeasurableSpace Ω} (hDG : mD ≤ mG') (hG : mG' ≤ mΩ)
    (hnu : nu = eps + ∑ m ∈ dims, A m)
    (hAm : StronglyMeasurable[mG'] (∑ m ∈ dims, A m))
    (heps : Integrable eps μ) (hA : ∀ m ∈ dims, Integrable (A m) μ)
    (heps0 : μ[eps | mG'] =ᵐ[μ] 0)
    (hA4 : Integrable (fun ω => (∑ m ∈ dims, A m) ω ^ 4) μ)
    (hnu4 : Integrable (fun ω => nu ω ^ 4) μ) :
    μ[fun ω => (∑ m ∈ dims, A m) ω ^ 4 | mD] ≤ᵐ[μ] μ[fun ω => nu ω ^ 4 | mD] := by
  have hswap : (fun ω => nu ω ^ 4) = fun ω => ((∑ m ∈ dims, A m) ω + eps ω) ^ 4 := by
    subst hnu
    funext ω
    simp only [Pi.add_apply]
    rw [add_comm]
  rw [hswap]
  exact condExp_pow_four_le_of_condExp_eq_zero hDG hG hAm (integrable_finsetSum' _ hA) heps
    hA4 (hswap ▸ hnu4) heps0

end Lemma

/-! ## Regime 1: the vanishing conditional mean from conditional independence

`condSup mD Y := mD ⊔ comap Y` is the σ-algebra `σ(Y, 𝒟)`. If `X` is conditionally independent
of `Y` given `𝒟` and `E[X | 𝒟] = 0`, then `E[X | σ(Y, 𝒟)] = 0`; the proof is a π-system argument
over the rectangles `d ∩ Y⁻¹B`. The results above then hold with `hA0`
replaced by conditional independence and conditional mean zero.
-/

section Regime1

open ProbabilityTheory MeasurableSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

set_option warn.classDefReducibility false in
/-- `σ(Y, 𝒟)`, the join of `𝒟` with the σ-algebra generated by `Y`. -/
def condSup (mD : MeasurableSpace Ω) (Y : Ω → ℝ) : MeasurableSpace Ω :=
  mD ⊔ MeasurableSpace.comap Y inferInstance

theorem le_condSup (mD : MeasurableSpace Ω) (Y : Ω → ℝ) : mD ≤ condSup mD Y := le_sup_left

/-- `σ(Y, 𝒟) ≤ mΩ` when `Y` is measurable. Measurability hypotheses in this section are
written `Measurable[mΩ]` to avoid resolving to `mD`. -/
theorem condSup_le {mD : MeasurableSpace Ω} (hD : mD ≤ mΩ) {Y : Ω → ℝ}
    (hY : Measurable[mΩ] Y) : condSup mD Y ≤ mΩ := sup_le hD hY.comap_le

/-- `Y` is `σ(Y, 𝒟)`-measurable. -/
theorem stronglyMeasurable_condSup (mD : MeasurableSpace Ω) {Y : Ω → ℝ} :
    StronglyMeasurable[condSup mD Y] Y :=
  ((measurable_iff_comap_le.2
    (le_refl (MeasurableSpace.comap Y (inferInstance : MeasurableSpace ℝ)))).mono
      le_sup_right le_rfl).stronglyMeasurable

/-- The rectangles `d ∩ Y⁻¹B`, `d ∈ 𝒟`: the π-system that generates `σ(Y, 𝒟)`. -/
def condRect (mD : MeasurableSpace Ω) (Y : Ω → ℝ) : Set (Set Ω) :=
  {s | ∃ d : Set Ω, ∃ B : Set ℝ, MeasurableSet[mD] d ∧ MeasurableSet B ∧ s = d ∩ Y ⁻¹' B}

theorem isPiSystem_condRect (mD : MeasurableSpace Ω) (Y : Ω → ℝ) :
    IsPiSystem (condRect mD Y) := by
  rintro s ⟨d₁, B₁, hd₁, hB₁, rfl⟩ t ⟨d₂, B₂, hd₂, hB₂, rfl⟩ -
  refine ⟨d₁ ∩ d₂, B₁ ∩ B₂, hd₁.inter hd₂, hB₁.inter hB₂, ?_⟩
  rw [Set.preimage_inter]
  ext ω
  simp only [Set.mem_inter_iff]
  tauto

theorem generateFrom_condRect (mD : MeasurableSpace Ω) (Y : Ω → ℝ) :
    condSup mD Y = MeasurableSpace.generateFrom (condRect mD Y) := by
  refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
  · refine MeasurableSpace.le_def.2 fun d hd => ?_
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨d, Set.univ, hd, MeasurableSet.univ, by simp⟩
  · refine MeasurableSpace.le_def.2 fun s hs => ?_
    obtain ⟨B, hB, rfl⟩ := hs
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨Set.univ, B, MeasurableSet.univ, hB, by simp⟩
  · rintro s ⟨d, B, hd, hB, rfl⟩
    refine MeasurableSet.inter ?_ ?_
    · exact (le_sup_left : mD ≤ condSup mD Y) d hd
    · exact (le_sup_right : MeasurableSpace.comap Y (inferInstance : MeasurableSpace ℝ)
        ≤ condSup mD Y) _ ⟨B, hB, rfl⟩

/-- If `X` and `Y` are conditionally independent given `𝒟` and `E[X | 𝒟] = 0`, then
`E[X | σ(Y, 𝒟)] = 0`. -/
theorem condExp_sup_eq_zero_of_condIndepFun [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {mD : MeasurableSpace Ω} (hD : mD ≤ mΩ) {X Y : Ω → ℝ}
    (hX : Measurable[mΩ] X) (hY : Measurable[mΩ] Y)
    (hind : CondIndepFun mD hD X Y μ) (hXi : Integrable X μ)
    (hX0 : μ[X | mD] =ᵐ[μ] 0) :
    μ[X | condSup mD Y] =ᵐ[μ] 0 := by
  classical
  have hle : condSup mD Y ≤ mΩ := condSup_le hD hY
  -- `∫ X dμ = ∫ E[X | 𝒟] dμ = 0`
  have htot : ∫ ω, X ω ∂μ = 0 := by
    rw [← integral_condExp (μ := μ) (f := X) hD, integral_congr_ae hX0]
    simp
  have key : ∀ t, MeasurableSet[condSup mD Y] t → ∫ ω in t, X ω ∂μ = 0 := by
    refine MeasurableSpace.induction_on_inter (m := condSup mD Y)
      (C := fun t _ => ∫ ω in t, X ω ∂μ = 0)
      (generateFrom_condRect mD Y) (isPiSystem_condRect mD Y) (by simp) ?_ ?_ ?_
    · -- On a rectangle, the conditional product rule and `E[X | 𝒟] = 0`.
      rintro t ⟨d, B, hd, hB, rfl⟩
      have hE : MeasurableSet[mΩ] (Y ⁻¹' B) := hY hB
      set W : Ω → ℝ := Set.indicator (Y ⁻¹' B) (fun _ => (1 : ℝ)) with hWdef
      have hWm : Measurable[mΩ] W := measurable_const.indicator hE
      have hWi : Integrable W μ := (integrable_const (1 : ℝ)).indicator hE
      have hfun : Set.indicator (Y ⁻¹' B) X = fun ω => W ω * X ω := by
        funext ω
        by_cases h : ω ∈ Y ⁻¹' B <;> simp [hWdef, h]
      have hWXi : Integrable (fun ω => W ω * X ω) μ := by
        have h := hXi.indicator hE
        rw [hfun] at h
        exact h
      have hCI : CondIndepFun mD hD W X μ := by
        have h0 : CondIndepFun mD hD
            ((Set.indicator B (fun _ : ℝ => (1 : ℝ))) ∘ Y) (id ∘ X) μ :=
          hind.symm.comp (measurable_const.indicator hB) measurable_id
        have heq : ((Set.indicator B (fun _ : ℝ => (1 : ℝ))) ∘ Y) = W := by
          funext ω
          by_cases h : Y ω ∈ B <;> simp [hWdef, Set.mem_preimage, h]
        rw [heq] at h0
        exact h0
      have hzero : μ[fun ω => W ω * X ω | mD] =ᵐ[μ] 0 :=
        CondIndep.condExp_mul_eq_zero_of_condIndepFun mD hWm hX hCI hWi hXi hWXi hX0
      have hcong : ∫ x in d, (μ[fun ω => W ω * X ω | mD]) x ∂μ = ∫ _x in d, (0 : ℝ) ∂μ := by
        refine setIntegral_congr_ae (hD d hd) ?_
        filter_upwards [hzero] with ω hω _
        simpa using hω
      rw [← setIntegral_indicator hE, hfun, ← setIntegral_condExp hD hWXi hd, hcong,
        integral_zero]
    · -- Complements, using `∫ X dμ = 0`.
      intro t htm ih
      have h := integral_add_compl (hle t htm) hXi
      rw [ih, htot] at h
      simpa using h
    · -- Countable disjoint unions.
      intro f hfd hfm ih
      rw [integral_iUnion (fun i => hle _ (hfm i)) hfd hXi.integrableOn]
      simp [ih]
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) hle hXi
    (fun s _ _ => integrable_zero _ _ _) (fun s hs _ => ?_) aestronglyMeasurable_zero).symm
  simp only [Pi.zero_apply, integral_zero]
  exact (key s hs).symm

variable {D : Type*} {dims : Finset D} {A : D → Ω → ℝ} {eps nu : Ω → ℝ} {C : ℝ}

/-- **Lemma SM.B.5, first inequality, under Regime 1.** The vanishing conditional mean at
`σ(ε, 𝒟)` is derived from conditional independence given `𝒟` and `E[a^{(m)} | 𝒟] = 0`. -/
theorem condExp_fourth_idiosyncratic_le_regime1 [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {mD : MeasurableSpace Ω} (hD : mD ≤ mΩ)
    (hnu : nu = eps + ∑ m ∈ dims, A m)
    (hepsm : Measurable[mΩ] eps) (hAm : ∀ m ∈ dims, Measurable[mΩ] (A m))
    (heps : Integrable eps μ) (hA : ∀ m ∈ dims, Integrable (A m) μ)
    (hCI : ∀ m ∈ dims, CondIndepFun mD hD (A m) eps μ)
    (hA0D : ∀ m ∈ dims, μ[A m | mD] =ᵐ[μ] 0)
    (heps4 : Integrable (fun ω => eps ω ^ 4) μ)
    (hnu4 : Integrable (fun ω => nu ω ^ 4) μ) :
    μ[fun ω => eps ω ^ 4 | mD] ≤ᵐ[μ] μ[fun ω => nu ω ^ 4 | mD] :=
  condExp_fourth_idiosyncratic_le (mG := condSup mD eps) (le_condSup mD eps)
    (condSup_le hD hepsm) hnu (stronglyMeasurable_condSup mD) heps hA
    (fun m hm => condExp_sup_eq_zero_of_condIndepFun hD (hAm m hm) hepsm (hCI m hm)
      (hA m hm) (hA0D m hm))
    heps4 hnu4

/-- **Lemma SM.B.5 under Regime 1.** `E[ε_o⁴ | 𝒟] ≤ E[ν_o⁴ | 𝒟] ≤ C`. -/
theorem condExp_fourth_idiosyncratic_le_const_regime1 [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {mD : MeasurableSpace Ω} (hD : mD ≤ mΩ)
    (hnu : nu = eps + ∑ m ∈ dims, A m)
    (hepsm : Measurable[mΩ] eps) (hAm : ∀ m ∈ dims, Measurable[mΩ] (A m))
    (heps : Integrable eps μ) (hA : ∀ m ∈ dims, Integrable (A m) μ)
    (hCI : ∀ m ∈ dims, CondIndepFun mD hD (A m) eps μ)
    (hA0D : ∀ m ∈ dims, μ[A m | mD] =ᵐ[μ] 0)
    (heps4 : Integrable (fun ω => eps ω ^ 4) μ)
    (hnu4 : Integrable (fun ω => nu ω ^ 4) μ)
    (hC : μ[fun ω => nu ω ^ 4 | mD] ≤ᵐ[μ] fun _ => C) :
    μ[fun ω => eps ω ^ 4 | mD] ≤ᵐ[μ] fun _ => C := by
  filter_upwards [condExp_fourth_idiosyncratic_le_regime1 hD hnu hepsm hAm heps hA hCI hA0D
    heps4 hnu4, hC] with ω h1 h2
  exact h1.trans h2

/-- **Lemma SM.B.5, category-level part, under Regime 1.** `E[V⁴ | 𝒟] ≤ E[ν⁴ | 𝒟] ≤ C`,
with `E[ε_o | σ(V, 𝒟)] = 0` derived from the conditional independence of `ε_o` and `V` given
`𝒟` and `E[ε_o | 𝒟] = 0`. -/
theorem condExp_fourth_components_le_regime1 [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {mD : MeasurableSpace Ω} (hD : mD ≤ mΩ)
    (hnu : nu = eps + ∑ m ∈ dims, A m)
    (hepsm : Measurable[mΩ] eps) (hAm : ∀ m ∈ dims, Measurable[mΩ] (A m))
    (heps : Integrable eps μ) (hA : ∀ m ∈ dims, Integrable (A m) μ)
    (hCIV : CondIndepFun mD hD eps (∑ m ∈ dims, A m) μ)
    (heps0D : μ[eps | mD] =ᵐ[μ] 0)
    (hA4 : Integrable (fun ω => (∑ m ∈ dims, A m) ω ^ 4) μ)
    (hnu4 : Integrable (fun ω => nu ω ^ 4) μ) :
    μ[fun ω => (∑ m ∈ dims, A m) ω ^ 4 | mD] ≤ᵐ[μ] μ[fun ω => nu ω ^ 4 | mD] := by
  have hVm : Measurable[mΩ] (∑ m ∈ dims, A m) := by
    have h := Finset.measurable_sum dims hAm
    simpa only [← Finset.sum_apply] using h
  exact condExp_fourth_components_le (mG' := condSup mD (∑ m ∈ dims, A m))
    (le_condSup mD _) (condSup_le hD hVm) hnu (stronglyMeasurable_condSup mD) heps hA
    (condExp_sup_eq_zero_of_condIndepFun hD hepsm hVm hCIV heps heps0D) hA4 hnu4

end Regime1

end Moments
end Multiway
