import Multiway.PiHat
import Multiway.Quadform

/-!
# The conditional mean of the diagnostic coefficient

This file derives the conditional mean-zero condition used in Lemma SM.B.4 (the diagnostic
coefficient) from its two components: the composite error `u = Δη + ν` has
`E[u_o | 𝒟] = 0` whenever `E[Δη_o | 𝒟] = 0` (the correlated-random-effects assumption) and
`E[ν_o | 𝒟] = 0` (the exogeneity assumption). Both conditions are taken with respect to `𝒟`.

## Main results

* `condExp_add_eq_zero`: the conditional mean of `u` vanishes.
* `condExp_piHat_sub_eq_zero_of_components`: `E[π̂ - π | 𝒟] = 0` from the two components.
* `condExp_add_eq_zero_witness`: a non-degenerate model satisfying all hypotheses.
-/

namespace Multiway
namespace PiHatCre

open Matrix MeasureTheory

/-! ## The conditional mean of the composite error -/

section Step

variable {O : Type*}
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `u = Δη + ν` with `E[Δη_o | 𝒟] = 0` and `E[ν_o | 𝒟] = 0`, then `E[u_o | 𝒟] = 0` for
every observation `o`. -/
theorem condExp_add_eq_zero {u deta nu : Ω → O → ℝ}
    (hu : ∀ ω o, u ω o = deta ω o + nu ω o)
    (hdi : ∀ o, Integrable (fun ω => deta ω o) μ)
    (hni : ∀ o, Integrable (fun ω => nu ω o) μ)
    (hdeta : ∀ o, μ[fun ω => deta ω o | 𝒟] =ᵐ[μ] 0)
    (hnu : ∀ o, μ[fun ω => nu ω o | 𝒟] =ᵐ[μ] 0) (o : O) :
    μ[fun ω => u ω o | 𝒟] =ᵐ[μ] 0 := by
  have hfun : (fun ω => u ω o) = (fun ω => deta ω o) + fun ω => nu ω o := by
    funext ω
    exact hu ω o
  rw [hfun]
  filter_upwards [condExp_add (hdi o) (hni o) 𝒟, hdeta o, hnu o] with ω h1 h2 h3
  simp only [Pi.zero_apply] at h2 h3 ⊢
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2, h3, add_zero]

end Step

/-! ## The conditional mean of the diagnostic coefficient -/

section Sibling

variable {O K : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [DecidableEq O] in
/-- `E[π̂ - π | 𝒟] = 0` when the composite error `u = Δη + ν` has components with vanishing
conditional mean. -/
theorem condExp_piHat_sub_eq_zero_of_components {M : Matrix O O ℝ} {Z : Matrix O K ℝ}
    {π : K → ℝ} {pv : Ω → K → ℝ} {u deta nu : Ω → O → ℝ}
    (hstep : ∀ ω, pv ω - π = (((M * Z)ᵀ * (M * Z))⁻¹ * (M * Z)ᵀ) *ᵥ u ω)
    (hu : ∀ ω o, u ω o = deta ω o + nu ω o)
    (hdi : ∀ o, Integrable (fun ω => deta ω o) μ)
    (hni : ∀ o, Integrable (fun ω => nu ω o) μ)
    (hdeta : ∀ o, μ[fun ω => deta ω o | 𝒟] =ᵐ[μ] 0)
    (hnu : ∀ o, μ[fun ω => nu ω o | 𝒟] =ᵐ[μ] 0) (k : K) :
    μ[fun ω => pv ω k - π k | 𝒟] =ᵐ[μ] 0 :=
  PiHat.condExp_piHat_sub_eq_zero 𝒟 hstep
    (fun o => by
      have h : (fun ω => u ω o) = (fun ω => deta ω o) + fun ω => nu ω o := by
        funext ω
        exact hu ω o
      rw [h]
      exact (hdi o).add (hni o))
    (condExp_add_eq_zero 𝒟 hu hdi hni hdeta hnu) k

end Sibling

/-! ## A witness

On the fair-sign model of `Multiway.Quadform`, where `𝒟` is a proper sub-σ-field, take `Δη_o`
to be the sign at site `o` and `ν_o = -2 Δη_o`. Both components have vanishing conditional mean
and `u_o = -Δη_o` is not almost everywhere zero. -/

section Witness

open Multiway.Quadform.CondIndepWitness

variable (O : Type*) [Fintype O] [DecidableEq O]

/-- `Δη_o`, the correlated-effect component of the witness: the fair sign at site `o`. -/
noncomputable def detaW (ω : Option O → ℝ) (o : O) : ℝ := wEps O o ω

/-- `ν_o`, the disturbance of the witness: minus twice the same sign, so that `u_o = -sign_o` is
nonzero and the two components do not cancel to the zero model. -/
noncomputable def nuW (ω : Option O → ℝ) (o : O) : ℝ := -2 * wEps O o ω

/-- `u_o = Δη_o + ν_o = -sign_o`. -/
noncomputable def uW (ω : Option O → ℝ) (o : O) : ℝ := -wEps O o ω

omit [Fintype O] [DecidableEq O] in
theorem uW_eq (ω : Option O → ℝ) (o : O) : uW O ω o = detaW O ω o + nuW O ω o := by
  simp only [uW, detaW, nuW]
  ring

omit [DecidableEq O] in
theorem condExp_smul_eq_zero (a : ℝ) (o : O) :
    (wP O)[fun ω => a * wEps O o ω | wD O] =ᵐ[wP O] 0 := by
  have hs : (fun ω => a * wEps O o ω) = a • wEps O o := rfl
  rw [hs]
  filter_upwards [condExp_smul (μ := wP O) (m := wD O) a (wEps O o), wMean O o] with ω h1 h2
  simp only [Pi.zero_apply] at h2 ⊢
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2, mul_zero]

/-- A model of `condExp_add_eq_zero`: `𝒟` is a proper sub-σ-field, both components and `u` have
vanishing conditional mean, and `∫ u_o² = 1`. -/
theorem condExp_add_eq_zero_witness (o₀ : O) :
    (∃ B : Set (Option O → ℝ), MeasurableSet B ∧ ¬ MeasurableSet[wD O] B)
    ∧ (∀ o, (wP O)[fun ω => detaW O ω o | wD O] =ᵐ[wP O] 0)
    ∧ (∀ o, (wP O)[fun ω => nuW O ω o | wD O] =ᵐ[wP O] 0)
    ∧ (∀ o, (wP O)[fun ω => uW O ω o | wD O] =ᵐ[wP O] 0)
    ∧ ∫ ω, uW O ω o₀ * uW O ω o₀ ∂(wP O) = 1 := by
  have hint : ∀ (a : ℝ) (o : O), Integrable (fun ω => a * wEps O o ω) (wP O) := by
    intro a o
    exact integrable_of_bound O ((measurable_wEps O o).const_mul a) (B := |a|) fun ω => by
      rw [abs_mul]
      have h := abs_wEps_le O o ω
      nlinarith [abs_nonneg a, abs_nonneg (wEps O o ω), h]
  have hdi : ∀ o : O, Integrable (fun ω => detaW O ω o) (wP O) := by
    intro o
    have h := hint 1 o
    simpa [detaW] using h
  have hni : ∀ o : O, Integrable (fun ω => nuW O ω o) (wP O) := fun o => hint (-2) o
  have hdeta : ∀ o : O, (wP O)[fun ω => detaW O ω o | wD O] =ᵐ[wP O] 0 := by
    intro o
    have h := condExp_smul_eq_zero O 1 o
    simpa [detaW] using h
  have hnu : ∀ o : O, (wP O)[fun ω => nuW O ω o | wD O] =ᵐ[wP O] 0 :=
    fun o => condExp_smul_eq_zero O (-2) o
  refine ⟨wD_proper O o₀, hdeta, hnu, ?_, ?_⟩
  · exact condExp_add_eq_zero (wD O) (uW_eq O) hdi hni hdeta hnu
  · have h : (fun ω => uW O ω o₀ * uW O ω o₀)
        = fun ω => wEps O o₀ ω * wEps O o₀ ω := by
      funext ω
      simp only [uW]
      ring
    rw [h]
    exact wEps_second_moment O o₀

end Witness

end PiHatCre
end Multiway
