import Multiway.Incremental

/-!
# Global spanning implies local spanning

This file formalizes Lemma SM.B.2 of the paper (global spanning implies local spanning): for
`M ≥ 2`, if `col(P_[Δ]X) ⊆ col(𝒞_DW(X))` then `col(A_mX) ⊆ col(B_mX)` for every `m`. As in
`Multiway.Incremental`, the setting is orthogonal projectors onto submodules of a
finite-dimensional real inner product space `E`, and a matrix product `N X` is represented by
the column space `W.map N` with `W = col(X)`.

## Notation

* `P ℓ` is `𝒮_ℓ = col(Δ_ℓ)`; `S` is `𝒮`; `T` is `𝒮_{-m}`; `C₀` is `span(ι_n)`.
* `Tᗮ.starProjection` is `Q_{-m} = I_n - P_{-m}`.
* `incrementalProjector S T` is `A_m` and `incrementalMundlak T (P m)` is `B_m`.

## Main results

* `local_spanning`: the lemma, with the consequences of `M ≥ 2` as hypotheses.
* `local_spanning_of_two_dimensions`: the lemma with `𝒮` and `𝒮_{-m}` written as suprema.
-/

namespace Multiway

open Submodule LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `col(P_ℓ X) ⊆ 𝒮_ℓ`: the image of any subspace under an orthogonal projector lies in the
subspace projected onto. -/
theorem map_starProjection_le (U V : Submodule ℝ E) :
    V.map ((U.starProjection : E →ₗ[ℝ] E)) ≤ U := by
  rintro _ ⟨v, -, rfl⟩
  exact U.starProjection_apply_mem v

/-- `Q_{-m}` annihilates every subspace of `𝒮_{-m}`. -/
theorem map_starProjection_orthogonal_eq_bot {T V : Submodule ℝ E} (h : V ≤ T) :
    V.map ((Tᗮ).starProjection : E →ₗ[ℝ] E) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro _ ⟨v, hv, rfl⟩
  simpa only [ContinuousLinearMap.coe_coe] using
    Submodule.starProjection_orthogonal_apply_eq_zero (h hv)

/-- `Q_{-m}P_[Δ] = P_[Δ] - P_{-m} = A_m` when `𝒮_{-m} ⊆ 𝒮`. -/
theorem starProjection_orthogonal_comp_starProjection {S T : Submodule ℝ E} (hTS : T ≤ S) :
    ((Tᗮ).starProjection : E →ₗ[ℝ] E).comp ((S.starProjection : E →ₗ[ℝ] E))
      = incrementalProjector S T := by
  ext x
  have h : T.starProjection (S.starProjection x) = T.starProjection x :=
    DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le hTS) x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, incrementalProjector_apply]
  rw [Submodule.starProjection_orthogonal_val, h]

/-- **Lemma SM.B.2.** If `𝒮_{-m} ⊆ 𝒮`, `ι_n ∈ 𝒮_{-m}` and `𝒮_ℓ ⊆ 𝒮_{-m}` for `ℓ ≠ m`, then
`col(P_[Δ]X) ⊆ col(𝒞_DW(X))` implies `col(A_mX) ⊆ col(B_mX)`. -/
theorem local_spanning {D : Type*} {P : D → Submodule ℝ E} {m : D}
    {S T W C₀ : Submodule ℝ E} (hTS : T ≤ S) (hconst : C₀ ≤ T)
    (hother : ∀ ℓ, ℓ ≠ m → P ℓ ≤ T)
    (hglobal : W.map ((S.starProjection : E →ₗ[ℝ] E))
      ≤ C₀ ⊔ ⨆ ℓ, W.map (((P ℓ).starProjection : E →ₗ[ℝ] E))) :
    W.map (incrementalProjector S T) ≤ W.map (incrementalMundlak T (P m)) := by
  have hA : W.map (incrementalProjector S T)
      = (W.map ((S.starProjection : E →ₗ[ℝ] E))).map ((Tᗮ).starProjection : E →ₗ[ℝ] E) := by
    rw [← Submodule.map_comp, starProjection_orthogonal_comp_starProjection hTS]
  rw [hA]
  refine le_trans (Submodule.map_mono hglobal) ?_
  rw [Submodule.map_sup, Submodule.map_iSup]
  refine sup_le ?_ (iSup_le fun ℓ => ?_)
  · rw [map_starProjection_orthogonal_eq_bot hconst]
    exact bot_le
  · by_cases h : ℓ = m
    · subst h
      rw [← Submodule.map_comp]
      exact le_of_eq rfl
    · rw [map_starProjection_orthogonal_eq_bot
        (le_trans (map_starProjection_le (P ℓ) W) (hother ℓ h))]
      exact bot_le

/-- Lemma SM.B.2 with `𝒮 = 𝒮_1 + ⋯ + 𝒮_M` and `𝒮_{-m} = Σ_{ℓ ≠ m} 𝒮_ℓ`. The condition `M ≥ 2`
is the hypothesis `hM : ∃ ℓ, ℓ ≠ m`; together with `hC` (each `𝒮_ℓ` contains `ι_n`) it places
`ι_n` in `𝒮_{-m}`. -/
theorem local_spanning_of_two_dimensions {D : Type*} {P : D → Submodule ℝ E} {m : D}
    {W C₀ : Submodule ℝ E} (hM : ∃ ℓ, ℓ ≠ m) (hC : ∀ ℓ, C₀ ≤ P ℓ)
    (hglobal : W.map (((⨆ ℓ, P ℓ).starProjection : E →ₗ[ℝ] E))
      ≤ C₀ ⊔ ⨆ ℓ, W.map (((P ℓ).starProjection : E →ₗ[ℝ] E))) :
    W.map (incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ))
      ≤ W.map (incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m)) := by
  have hother : ∀ ℓ, ℓ ≠ m → P ℓ ≤ ⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ := fun ℓ h =>
    le_iSup_of_le ℓ (le_iSup_of_le h le_rfl)
  obtain ⟨ℓ₀, hℓ₀⟩ := hM
  exact local_spanning (iSup_le fun ℓ => iSup_le fun _ => le_iSup P ℓ)
    (le_trans (hC ℓ₀) (hother ℓ₀ hℓ₀)) hother hglobal

end Multiway
