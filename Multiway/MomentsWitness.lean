import Multiway.Moments
import Multiway.Quadform

/-!
# A model for the Regime-1 fourth-moment bounds

A single model satisfies every hypothesis of the three Regime-1 forms of Lemma SM.B.5 (Fourth
moments pass to the idiosyncratic component) in `Multiway.Moments`, and their conclusions are
derived through those theorems. The model has three independent fair signs, `ε_o` at site `0` and
the shocks `a^{(1)}`, `a^{(2)}` at sites `1` and `2`, and the design σ-field `𝒟` is a proper
sub-σ-field. Both conditional-independence hypotheses are derived from
mutual conditional independence given `𝒟`, and `∫ ε_o⁴ = 1`, so the bounds are non-degenerate.

## Main results

* `lem_fourth_regime1_witness`: all hypotheses hold simultaneously and the three bounds follow.
-/

namespace Multiway
namespace MomentsWitness

open MeasureTheory ProbabilityTheory
open Multiway.GeneralWitness
open Multiway.Quadform.CondIndepWitness

/-! ### The model -/

/-- The three sites, `0` for `ε_o` and `1`, `2` for the two category-level shocks. -/
abbrev Site : Type := Fin 3

/-- The sample space: one fair sign per site, plus the design coordinate `none`. -/
abbrev Om : Type := Option Site → ℝ

/-- `ε_o`, the idiosyncratic component. -/
noncomputable def epsW : Om → ℝ := wEps Site 0

/-- `a^{(1)}` and `a^{(2)}`, the two category-level shocks. -/
noncomputable def aW : Fin 2 → Om → ℝ := fun m => wEps Site m.succ

/-- `ν_o = ε_o + ∑_m a^{(m)}`, the Regime-1 decomposition. -/
noncomputable def nuW : Om → ℝ := epsW + ∑ m : Fin 2, aW m

theorem measurable_epsW : Measurable epsW := measurable_wEps Site 0

theorem measurable_aW (m : Fin 2) : Measurable (aW m) := measurable_wEps Site m.succ

theorem abs_epsW_le (ω : Om) : |epsW ω| ≤ 1 := abs_wEps_le Site 0 ω

theorem abs_aW_le (m : Fin 2) (ω : Om) : |aW m ω| ≤ 1 := abs_wEps_le Site m.succ ω

theorem sum_aW_apply (ω : Om) : (∑ m : Fin 2, aW m) ω = aW 0 ω + aW 1 ω := by
  rw [Finset.sum_apply, Fin.sum_univ_two]

theorem nuW_apply (ω : Om) : nuW ω = epsW ω + (aW 0 ω + aW 1 ω) := by
  show (epsW + ∑ m : Fin 2, aW m) ω = _
  rw [Pi.add_apply, sum_aW_apply]

theorem abs_sum_aW_le (ω : Om) : |(∑ m : Fin 2, aW m) ω| ≤ 2 := by
  rw [sum_aW_apply]
  have h0 := abs_add_le (aW 0 ω) (aW 1 ω)
  have h1 := abs_aW_le 0 ω
  have h2 := abs_aW_le 1 ω
  linarith

theorem abs_nuW_le (ω : Om) : |nuW ω| ≤ 3 := by
  rw [nuW_apply]
  have h0 := abs_add_le (epsW ω) (aW 0 ω + aW 1 ω)
  have h1 := abs_epsW_le ω
  have h2 : |aW 0 ω + aW 1 ω| ≤ 2 := by
    have h := abs_sum_aW_le ω
    rwa [sum_aW_apply] at h
  linarith

/-- `|x| ≤ B` implies `x⁴ ≤ B⁴`. -/
theorem pow_four_le_of_abs_le {x B : ℝ} (h : |x| ≤ B) : x ^ 4 ≤ B ^ 4 := by
  have hB : (0 : ℝ) ≤ B := (abs_nonneg x).trans h
  have h2 : x ^ 2 ≤ B ^ 2 := by
    have hsq := sq_abs x
    nlinarith [abs_nonneg x]
  calc x ^ 4 = x ^ 2 * x ^ 2 := by ring
    _ ≤ B ^ 2 * B ^ 2 := mul_self_le_mul_self (sq_nonneg x) h2
    _ = B ^ 4 := by ring

/-! ### Integrability -/

theorem integrable_epsW : Integrable epsW (wP Site) :=
  integrable_of_bound Site measurable_epsW (B := 1) abs_epsW_le

theorem integrable_aW (m : Fin 2) : Integrable (aW m) (wP Site) :=
  integrable_of_bound Site (measurable_aW m) (B := 1) (abs_aW_le m)

theorem sum_aW_eq : (∑ m : Fin 2, aW m) = fun ω : Om => aW 0 ω + aW 1 ω := funext sum_aW_apply

theorem nuW_eq : nuW = fun ω : Om => epsW ω + (aW 0 ω + aW 1 ω) := funext nuW_apply

theorem measurable_sum_aW : Measurable (∑ m : Fin 2, aW m) := by
  rw [sum_aW_eq]
  exact (measurable_aW 0).add (measurable_aW 1)

theorem measurable_nuW : Measurable nuW := by
  rw [nuW_eq]
  exact measurable_epsW.add ((measurable_aW 0).add (measurable_aW 1))

theorem integrable_epsW_pow_four : Integrable (fun ω => epsW ω ^ 4) (wP Site) :=
  integrable_of_bound Site (measurable_epsW.pow_const 4) (B := 1) fun ω => by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ epsW ω ^ 4)]
    simpa using pow_four_le_of_abs_le (abs_epsW_le ω)

theorem integrable_sum_aW_pow_four :
    Integrable (fun ω => (∑ m : Fin 2, aW m) ω ^ 4) (wP Site) :=
  integrable_of_bound Site (measurable_sum_aW.pow_const 4) (B := 16) fun ω => by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (∑ m : Fin 2, aW m) ω ^ 4)]
    have := pow_four_le_of_abs_le (abs_sum_aW_le ω)
    norm_num at this ⊢
    linarith

theorem nuW_pow_four_le (ω : Om) : nuW ω ^ 4 ≤ 81 := by
  have := pow_four_le_of_abs_le (abs_nuW_le ω)
  norm_num at this
  linarith

theorem integrable_nuW_pow_four : Integrable (fun ω => nuW ω ^ 4) (wP Site) :=
  integrable_of_bound Site (measurable_nuW.pow_const 4) (B := 81) fun ω => by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ nuW ω ^ 4)]
    exact nuW_pow_four_le ω

/-- The conditional fourth-moment bound `E[ν_o⁴ | 𝒟] ≤ 81` on this model. -/
theorem condExp_nuW_pow_four_le :
    (wP Site)[fun ω => nuW ω ^ 4 | wD Site] ≤ᵐ[wP Site] fun _ => (81 : ℝ) := by
  have hmono := condExp_mono (m := wD Site) integrable_nuW_pow_four
    (integrable_const (81 : ℝ))
    (Filter.Eventually.of_forall fun ω => nuW_pow_four_le ω)
  rwa [condExp_const (wD_le Site)] at hmono

/-! ### Pairwise conditional independence from mutual conditional independence -/

/-- `a^{(m)}` is conditionally independent of `ε_o` given `𝒟`: mutual conditional independence
read at two indices, by `ProbabilityTheory.iCondIndepFun.condIndepFun`. -/
theorem condIndep_aW_epsW (m : Fin 2) :
    CondIndepFun (wD Site) (wD_le Site) (aW m) epsW (wP Site) :=
  (wCondIndep Site).condIndepFun (Fin.succ_ne_zero m)

/-- `ε_o` is conditionally independent of `V = ∑_m a^{(m)}` given `𝒟`: the two shock sites are
grouped against the innovation site by `iCondIndepFun.condIndepFun_prodMk`, and the pair is then
added up by `CondIndepFun.comp`. -/
theorem condIndep_epsW_sum :
    CondIndepFun (wD Site) (wD_le Site) epsW (∑ m : Fin 2, aW m) (wP Site) := by
  have h := (wCondIndep Site).condIndepFun_prodMk (measurable_wEps Site)
    ((0 : Fin 2).succ) ((1 : Fin 2).succ) (0 : Site)
    (Fin.succ_ne_zero _) (Fin.succ_ne_zero _)
  have h2 := h.comp (φ := fun p : ℝ × ℝ => p.1 + p.2) (ψ := (id : ℝ → ℝ))
    (by fun_prop) measurable_id
  have heq : ((fun p : ℝ × ℝ => p.1 + p.2) ∘
      fun ω : Om => (wEps Site (0 : Fin 2).succ ω, wEps Site (1 : Fin 2).succ ω))
      = ∑ m : Fin 2, aW m := by
    funext ω
    rw [sum_aW_apply]
    rfl
  rw [heq] at h2
  exact h2.symm

/-! ### Non-degeneracy -/

theorem integral_epsW_pow_four : ∫ ω, epsW ω ^ 4 ∂(wP Site) = 1 := by
  have hg := gintegral (W := Option Site) (f := fun x => clamp x ^ 4)
    (measurable_clamp.pow_const 4) (some (0 : Site))
  rw [clamp_one, clamp_neg_one] at hg
  norm_num at hg
  simpa [wP, epsW, wEps, gU] using hg

/-! ### Example -/

/-- Every hypothesis of `Moments.condExp_fourth_idiosyncratic_le_regime1`,
`Moments.condExp_fourth_idiosyncratic_le_const_regime1` and
`Moments.condExp_fourth_components_le_regime1` holds on this model, with `𝒟` a proper
sub-σ-field, and their three conclusions follow; moreover `∫ ε_o⁴ = 1`. -/
theorem lem_fourth_regime1_witness :
    (∃ B : Set Om, MeasurableSet B ∧ ¬ MeasurableSet[wD Site] B)
    ∧ (∀ m : Fin 2, CondIndepFun (wD Site) (wD_le Site) (aW m) epsW (wP Site))
    ∧ CondIndepFun (wD Site) (wD_le Site) epsW (∑ m : Fin 2, aW m) (wP Site)
    ∧ ((wP Site)[fun ω => epsW ω ^ 4 | wD Site]
        ≤ᵐ[wP Site] (wP Site)[fun ω => nuW ω ^ 4 | wD Site])
    ∧ ((wP Site)[fun ω => epsW ω ^ 4 | wD Site] ≤ᵐ[wP Site] fun _ => (81 : ℝ))
    ∧ ((wP Site)[fun ω => (∑ m : Fin 2, aW m) ω ^ 4 | wD Site]
        ≤ᵐ[wP Site] (wP Site)[fun ω => nuW ω ^ 4 | wD Site])
    ∧ ∫ ω, epsW ω ^ 4 ∂(wP Site) = 1 := by
  refine ⟨wD_proper Site 0, condIndep_aW_epsW, condIndep_epsW_sum, ?_, ?_, ?_,
    integral_epsW_pow_four⟩
  · exact Moments.condExp_fourth_idiosyncratic_le_regime1 (wD_le Site) rfl
      measurable_epsW (fun m _ => measurable_aW m) integrable_epsW
      (fun m _ => integrable_aW m) (fun m _ => condIndep_aW_epsW m)
      (fun m _ => wMean Site m.succ) integrable_epsW_pow_four integrable_nuW_pow_four
  · exact Moments.condExp_fourth_idiosyncratic_le_const_regime1 (wD_le Site) rfl
      measurable_epsW (fun m _ => measurable_aW m) integrable_epsW
      (fun m _ => integrable_aW m) (fun m _ => condIndep_aW_epsW m)
      (fun m _ => wMean Site m.succ) integrable_epsW_pow_four integrable_nuW_pow_four
      condExp_nuW_pow_four_le
  · exact Moments.condExp_fourth_components_le_regime1 (wD_le Site) rfl
      measurable_epsW (fun m _ => measurable_aW m) integrable_epsW
      (fun m _ => integrable_aW m) condIndep_epsW_sum (wMean Site 0)
      integrable_sum_aW_pow_four integrable_nuW_pow_four

end MomentsWitness
end Multiway
