import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Multiway.DimensionWise

/-!
# Commutativity under minimal overlap

This file formalizes Corollary SM.D.1 of the paper (commutativity under minimal overlap): if
`𝒮_m ∩ 𝒮_{-m} = span(ι_n)` for every `m`, then dimension-wise Mundlak augmentation is
uniformly fixed-effects equivalent if and only if `P_m P_{-m} = P_{-m} P_m` for every `m`.

## Main results

* `comp_starProjection_of_commute`: commuting orthogonal projectors multiply to the orthogonal
  projector onto the intersection of their ranges.
* `proj_comp_proj_eq_const`: under minimal overlap and commutativity, `P_m P_ℓ = P_0` for
  `ℓ ≠ m`.
* `overlap_iff_commute`: the corollary, with the two clauses of Proposition 1 as hypotheses.
* `overlap_iff_commute_of_dimensionWise`: the corollary with those clauses supplied by
  `Multiway.DimensionWise`.
-/

namespace Multiway

open Submodule LinearMap

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {D : Type*}

/-! ### Commuting orthogonal projectors -/

section Commute

variable {T U : Submodule ℝ E}

/-- The composite of two orthogonal projectors that commute is a symmetric projection. -/
theorem isSymmetricProjection_comp_of_commute
    (hcomm : (T.starProjection : E →ₗ[ℝ] E).comp (U.starProjection : E →ₗ[ℝ] E)
      = (U.starProjection : E →ₗ[ℝ] E).comp (T.starProjection : E →ₗ[ℝ] E)) :
    ((T.starProjection : E →ₗ[ℝ] E).comp
      (U.starProjection : E →ₗ[ℝ] E)).IsSymmetricProjection := by
  constructor
  · show ((T.starProjection : E →ₗ[ℝ] E).comp (U.starProjection : E →ₗ[ℝ] E)) *
      ((T.starProjection : E →ₗ[ℝ] E).comp (U.starProjection : E →ₗ[ℝ] E))
      = (T.starProjection : E →ₗ[ℝ] E).comp (U.starProjection : E →ₗ[ℝ] E)
    ext x
    have hy : U.starProjection (U.starProjection x) = U.starProjection x :=
      starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
    have hc : U.starProjection (T.starProjection (U.starProjection x))
        = T.starProjection (U.starProjection (U.starProjection x)) :=
      (DFunLike.congr_fun hcomm (U.starProjection x)).symm
    have hT : T.starProjection (T.starProjection (U.starProjection x))
        = T.starProjection (U.starProjection x) :=
      starProjection_eq_self_iff.mpr (T.starProjection_apply_mem _)
    simp only [Module.End.mul_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hc, hy, hT]
  · intro x y
    have h₁ : ⟪T.starProjection (U.starProjection x), y⟫
        = ⟪U.starProjection x, T.starProjection y⟫ :=
      Submodule.inner_starProjection_left_eq_right _ _ _
    have h₂ : ⟪U.starProjection x, T.starProjection y⟫
        = ⟪x, U.starProjection (T.starProjection y)⟫ :=
      Submodule.inner_starProjection_left_eq_right _ _ _
    have h₃ : U.starProjection (T.starProjection y) = T.starProjection (U.starProjection y) :=
      (DFunLike.congr_fun hcomm y).symm
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [h₁, h₂, h₃]

/-- The range of the composite is the intersection of the two ranges. -/
theorem range_comp_starProjection_of_commute
    (hcomm : (T.starProjection : E →ₗ[ℝ] E).comp (U.starProjection : E →ₗ[ℝ] E)
      = (U.starProjection : E →ₗ[ℝ] E).comp (T.starProjection : E →ₗ[ℝ] E)) :
    LinearMap.range ((T.starProjection : E →ₗ[ℝ] E).comp
      (U.starProjection : E →ₗ[ℝ] E)) = T ⊓ U := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine Submodule.mem_inf.mpr ⟨T.starProjection_apply_mem _, ?_⟩
    have h : T.starProjection (U.starProjection x) = U.starProjection (T.starProjection x) :=
      DFunLike.congr_fun hcomm x
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, h]
    exact U.starProjection_apply_mem _
  · intro y hy
    obtain ⟨hyT, hyU⟩ := Submodule.mem_inf.mp hy
    refine ⟨y, ?_⟩
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      starProjection_eq_self_iff.mpr hyU, starProjection_eq_self_iff.mpr hyT]

/-- Commuting orthogonal projectors multiply to the orthogonal projector onto the
intersection of their ranges. -/
theorem comp_starProjection_of_commute
    (hcomm : (T.starProjection : E →ₗ[ℝ] E).comp (U.starProjection : E →ₗ[ℝ] E)
      = (U.starProjection : E →ₗ[ℝ] E).comp (T.starProjection : E →ₗ[ℝ] E)) :
    (T.starProjection : E →ₗ[ℝ] E).comp (U.starProjection : E →ₗ[ℝ] E)
      = ((T ⊓ U).starProjection : E →ₗ[ℝ] E) :=
  LinearMap.IsSymmetricProjection.ext (isSymmetricProjection_comp_of_commute hcomm)
    (isSymmetricProjection_starProjection _)
    (by rw [range_comp_starProjection_of_commute hcomm, range_starProjection])

end Commute

/-! ### The corollary -/

section Overlap

variable {S rest : D → Submodule ℝ E} {S₀ : Submodule ℝ E}

/-- `𝒮_{-m} = ∑_{ℓ ≠ m} 𝒮_ℓ`, the span of the remaining dimensions. -/
def restSpace (S : D → Submodule ℝ E) (m : D) : Submodule ℝ E := ⨆ ℓ, ⨆ _ : ℓ ≠ m, S ℓ

omit [FiniteDimensional ℝ E] in
/-- `𝒮_ℓ ⊆ 𝒮_{-m}` for `ℓ ≠ m`. -/
theorem le_restSpace (S : D → Submodule ℝ E) {m ℓ : D} (h : ℓ ≠ m) : S ℓ ≤ restSpace S m :=
  le_iSup₂ (f := fun ℓ (_ : ℓ ≠ m) => S ℓ) ℓ h

/-- If `𝒮_ℓ ⊆ 𝒮_{-m}`, then `P_{-m} P_ℓ = P_ℓ`. -/
theorem rest_comp_proj {m ℓ : D} (hle : S ℓ ≤ rest m) :
    ((rest m).starProjection : E →ₗ[ℝ] E).comp ((S ℓ).starProjection : E →ₗ[ℝ] E)
      = ((S ℓ).starProjection : E →ₗ[ℝ] E) := by
  ext x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  exact starProjection_eq_self_iff.mpr (hle ((S ℓ).starProjection_apply_mem x))

/-- Under the overlap condition `𝒮_m ∩ 𝒮_{-m} = 𝒮_0`, commutativity gives
`P_m P_{-m} = P_0`. -/
theorem proj_comp_rest_eq_const {m : D} (hoverlap : S m ⊓ rest m = S₀)
    (hcomm : ((S m).starProjection : E →ₗ[ℝ] E).comp ((rest m).starProjection : E →ₗ[ℝ] E)
      = ((rest m).starProjection : E →ₗ[ℝ] E).comp ((S m).starProjection : E →ₗ[ℝ] E)) :
    ((S m).starProjection : E →ₗ[ℝ] E).comp ((rest m).starProjection : E →ₗ[ℝ] E)
      = (S₀.starProjection : E →ₗ[ℝ] E) := by
  subst hoverlap
  exact comp_starProjection_of_commute hcomm

/-- Under minimal overlap and commutativity,
`P_m P_ℓ = P_m P_{-m} P_ℓ = P_0 P_ℓ = P_0` for every `ℓ ≠ m`. -/
theorem proj_comp_proj_eq_const (hconst : ∀ k : D, S₀ ≤ S k)
    (hle : ∀ k l : D, l ≠ k → S l ≤ rest k)
    (hoverlap : ∀ k : D, S k ⊓ rest k = S₀)
    (hcomm : ∀ k : D, ((S k).starProjection : E →ₗ[ℝ] E).comp
        ((rest k).starProjection : E →ₗ[ℝ] E)
      = ((rest k).starProjection : E →ₗ[ℝ] E).comp ((S k).starProjection : E →ₗ[ℝ] E))
    {m ℓ : D} (hml : ℓ ≠ m) :
    ((S m).starProjection : E →ₗ[ℝ] E).comp ((S ℓ).starProjection : E →ₗ[ℝ] E)
      = (S₀.starProjection : E →ₗ[ℝ] E) := by
  have h1 : ((S m).starProjection : E →ₗ[ℝ] E).comp ((rest m).starProjection : E →ₗ[ℝ] E)
      = (S₀.starProjection : E →ₗ[ℝ] E) := proj_comp_rest_eq_const (hoverlap m) (hcomm m)
  have h2 : ((rest m).starProjection : E →ₗ[ℝ] E).comp ((S ℓ).starProjection : E →ₗ[ℝ] E)
      = ((S ℓ).starProjection : E →ₗ[ℝ] E) := rest_comp_proj (hle m ℓ hml)
  have h3 : (S₀.starProjection : E →ₗ[ℝ] E).comp ((S ℓ).starProjection : E →ₗ[ℝ] E)
      = (S₀.starProjection : E →ₗ[ℝ] E) := by
    ext x
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    exact DFunLike.congr_fun (starProjection_comp_starProjection_of_le (hconst ℓ)) x
  calc ((S m).starProjection : E →ₗ[ℝ] E).comp ((S ℓ).starProjection : E →ₗ[ℝ] E)
      = ((S m).starProjection : E →ₗ[ℝ] E).comp
          (((rest m).starProjection : E →ₗ[ℝ] E).comp
            ((S ℓ).starProjection : E →ₗ[ℝ] E)) := by rw [h2]
    _ = (((S m).starProjection : E →ₗ[ℝ] E).comp ((rest m).starProjection : E →ₗ[ℝ] E)).comp
          ((S ℓ).starProjection : E →ₗ[ℝ] E) := (LinearMap.comp_assoc _ _ _).symm
    _ = (S₀.starProjection : E →ₗ[ℝ] E).comp ((S ℓ).starProjection : E →ₗ[ℝ] E) := by rw [h1]
    _ = (S₀.starProjection : E →ₗ[ℝ] E) := h3

/-- **Corollary SM.D.1.** Given clauses (ii) and (iii) of Proposition 1 as hypotheses,
equivalence holds if and only if `P_m P_{-m} = P_{-m} P_m` for every `m`. -/
theorem overlap_iff_commute (Equivalent : Prop) (hconst : ∀ k : D, S₀ ≤ S k)
    (hle : ∀ k l : D, l ≠ k → S l ≤ rest k)
    (hoverlap : ∀ k : D, S k ⊓ rest k = S₀)
    (hdw2 : (∀ k l : D, l ≠ k → ((S k).starProjection : E →ₗ[ℝ] E).comp
        ((S l).starProjection : E →ₗ[ℝ] E) = (S₀.starProjection : E →ₗ[ℝ] E)) → Equivalent)
    (hdw3 : (∃ k : D, ((S k).starProjection : E →ₗ[ℝ] E).comp
        ((rest k).starProjection : E →ₗ[ℝ] E)
      ≠ ((rest k).starProjection : E →ₗ[ℝ] E).comp ((S k).starProjection : E →ₗ[ℝ] E)) →
      ¬ Equivalent) :
    Equivalent ↔ ∀ k : D, ((S k).starProjection : E →ₗ[ℝ] E).comp
        ((rest k).starProjection : E →ₗ[ℝ] E)
      = ((rest k).starProjection : E →ₗ[ℝ] E).comp ((S k).starProjection : E →ₗ[ℝ] E) := by
  constructor
  · intro hEq k
    by_contra hk
    exact hdw3 ⟨k, hk⟩ hEq
  · intro hcomm
    exact hdw2 fun k l hlk => proj_comp_proj_eq_const hconst hle hoverlap hcomm hlk

end Overlap

/-! ### The corollary in terms of the spanning condition -/

section Discharged

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
variable [Fintype D] [Nontrivial D] {C₀ : Submodule ℝ E} {P : D → Submodule ℝ E}

/-- **Corollary SM.D.1.** Under minimal overlap, `M ≥ 2` (`[Nontrivial D]`) and
`rank(Q_[Δ]) ≥ K` (`hrank`), the spanning condition holds at every identified `X` if and only if
`P_m P_{-m} = P_{-m} P_m` for every `m`. -/
theorem overlap_iff_commute_of_dimensionWise (hconst : ∀ k, C₀ ≤ P k)
    (hoverlap : ∀ k, P k ⊓ restSpace P k = C₀)
    (hrank : Module.finrank ℝ F ≤ Module.finrank ℝ ((⨆ ℓ, P ℓ)ᗮ : Submodule ℝ E)) :
    (∀ X : F →ₗ[ℝ] E, Identified (⨆ ℓ, P ℓ) X →
        (LinearMap.range X).map (((⨆ ℓ, P ℓ).starProjection : E →ₗ[ℝ] E))
          ≤ dwControls C₀ P (LinearMap.range X))
      ↔ ∀ k, ((P k).starProjection : E →ₗ[ℝ] E).comp
            ((restSpace P k).starProjection : E →ₗ[ℝ] E)
          = ((restSpace P k).starProjection : E →ₗ[ℝ] E).comp
            ((P k).starProjection : E →ₗ[ℝ] E) := by
  classical
  refine overlap_iff_commute _ hconst (fun k l h => le_restSpace P h) hoverlap ?_ ?_
  · -- Proposition 1(ii)
    intro hpair X _
    refine spanning_of_pairwise hconst ?_
    intro k l hkl x
    exact DFunLike.congr_fun (hpair k l (Ne.symm hkl)) x
  · -- Proposition 1(iii)
    rintro ⟨k, hk⟩ huniform
    exact hk (commute_of_uniform_spanning (exists_ne k) hconst hrank huniform)

end Discharged

end Multiway
