import Multiway.Spanning

/-!
# Joint-projection equivalence, minimality and exact absorption

This file formalizes Theorem 3 of the paper (Joint-projection equivalence, minimality and exact
absorption), in the abstract setting of `Multiway.Spanning`, where `E` is the observation space, `X : F →ₗ[ℝ] E`
the regressors, `S` the joint fixed-effects space `𝒮`, and the estimators are given by their
normal equations. The intercept `ι` is an arbitrary element of `S`.

## Notation

* `jointProjControls S X` is `col(P_[Δ]X)`.
* `jmControls ι S X` is `col(𝒞_JM(X)) = span(ι_n) + col(P_[Δ]X)`.
* `Sm : D → Submodule ℝ E` gives the spaces `col(Δ_m)`, with `𝒮 = ⨆ m, Sm m`.

## Main results

* `jm_equiv`: clause (a), `β̂_JM = β̂_MFE`.
* `jointProjControls_le_of_equiv`, `jm_isLeast`: clause (b), minimality and attainment.
* `within_inner_dummy_eq_zero`, `within_inner_add_mem_eq`: clause (c), exact absorption, without
  the identification hypothesis.
-/

namespace Multiway

open RealInnerProductSpace

section JointProjection

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [AddCommGroup F] [Module ℝ F]

/-! ### The two control spaces -/

/-- `col(P_[Δ]X)`, the image of `col(X)` under `P_[Δ]`, spanned by the joint between
component of the regressors. -/
noncomputable def jointProjControls (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) : Submodule ℝ E :=
  (LinearMap.range X).map (S.starProjection : E →L[ℝ] E).toLinearMap

/-- `col(𝒞_JM(X)) = span(ι_n) + col(P_[Δ]X)`, the span of the joint-projection Mundlak
controls `𝒞_JM(X) := [ι_n, P_[Δ]X]`. -/
noncomputable def jmControls (ι : E) (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) : Submodule ℝ E :=
  Submodule.span ℝ {ι} ⊔ jointProjControls S X

/-- `col(P_[Δ]X) ⊆ 𝒮`. -/
theorem jointProjControls_le (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) :
    jointProjControls S X ≤ S := by
  rintro u ⟨v, -, rfl⟩
  exact S.starProjection_apply_mem v

/-- Every column of `P_[Δ]X` lies in `col(P_[Δ]X)`, stated as the spanning condition of
Theorem 1 at the control space `col(P_[Δ]X)`. -/
theorem starProjection_mem_jointProjControls (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) (a : F) :
    S.starProjection (X a) ∈ jointProjControls S X :=
  (spanning_condition_iff S (jointProjControls S X) X).mp le_rfl a

/-- `col(𝒞_JM(X)) ⊆ 𝒮` when `ι_n ∈ 𝒮`. -/
theorem jmControls_le {ι : E} {S : Submodule ℝ E} (hι : ι ∈ S) (X : F →ₗ[ℝ] E) :
    jmControls ι S X ≤ S :=
  sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hι)) (jointProjControls_le S X)

/-- `col(P_[Δ]X) ⊆ col(𝒞_JM(X))`. -/
theorem starProjection_mem_jmControls (ι : E) (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) (a : F) :
    S.starProjection (X a) ∈ jmControls ι S X :=
  Submodule.mem_sup_right (starProjection_mem_jointProjControls S X a)

/-! ### Clause (a): joint-projection equivalence -/

/-- **Theorem 3(a).** `β̂_JM = β̂_MFE` for every `y`, by Theorem 1, since
`col(𝒞_JM(X)) ⊆ 𝒮` and `col(P_[Δ]X) ⊆ col(𝒞_JM(X))`. -/
theorem jm_equiv {ι : E} {S : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hid : Identified S X)
    (hι : ι ∈ S) (y : E) (b : F) :
    IsAugSlope (jmControls ι S X) X y b ↔ IsMFESlope S X y b :=
  (spanning hid (jmControls_le hι X)).mpr
    (starProjection_mem_jmControls ι S X) y b

/-! ### Clause (b): minimality -/

/-- **Theorem 3(b), first claim.** If `col(𝒞) ⊆ 𝒮` and `β̂_𝒞 = β̂_MFE` for every `y`, then
`col(P_[Δ]X) ⊆ col(𝒞)`. This half does not need the identification hypothesis. -/
theorem jointProjControls_le_of_equiv {S W : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hWS : W ≤ S)
    (hequiv : ∀ (y : E) (b : F), IsAugSlope W X y b ↔ IsMFESlope S X y b) :
    jointProjControls S X ≤ W :=
  (spanning_condition_iff S W X).mpr
    (starProjection_mem_of_isMFESlope_imp hWS fun y b hb => (hequiv y b).mpr hb)

/-- **Theorem 3(b), second claim.** With the control space `col(P_[Δ]X)`,
`β̂_𝒞 = β̂_MFE` for every `y`. -/
theorem jm_equiv_jointProjControls {S : Submodule ℝ E} {X : F →ₗ[ℝ] E}
    (hid : Identified S X) (y : E) (b : F) :
    IsAugSlope (jointProjControls S X) X y b ↔ IsMFESlope S X y b :=
  (spanning hid (jointProjControls_le S X)).mpr
    (starProjection_mem_jointProjControls S X) y b

/-- **Theorem 3(b).** `col(P_[Δ]X)` is the smallest subspace `W ⊆ 𝒮` such that the control
space `W` gives `β̂_𝒞 = β̂_MFE` for every `y`, and it is attained by `P_[Δ]X`. -/
theorem jm_isLeast {S : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hid : Identified S X) :
    IsLeast {W : Submodule ℝ E |
        W ≤ S ∧ ∀ (y : E) (b : F), IsAugSlope W X y b ↔ IsMFESlope S X y b}
      (jointProjControls S X) :=
  ⟨⟨jointProjControls_le S X, jm_equiv_jointProjControls hid⟩,
    fun _ hW => jointProjControls_le_of_equiv hW.1 hW.2⟩

/-! ### Clause (c): exact absorption

No identification hypothesis is needed in this section. -/

/-- `Q_[Δ]` is symmetric: `(Q_[Δ]u)'v = u'(Q_[Δ]v)`. -/
theorem inner_jointWithin_symm (S : Submodule ℝ E) (u v : E) :
    ⟪jointWithin S u, v⟫ = ⟪u, jointWithin S v⟫ := by
  rw [inner_jointWithin_comp' S u v, ← inner_jointWithin_comp S u v]

/-- **Theorem 3(c), first claim.** `X̃'Δ_m a = 0` for every `m` and every `a ∈ ℝ^{N_m}`,
stated as `⟪Q_[Δ]X a, d⟫ = 0` for every `d ∈ col(Δ_m)`. -/
theorem within_inner_dummy_eq_zero {D : Type*} {Sm : D → Submodule ℝ E} {X : F →ₗ[ℝ] E}
    (m : D) {d : E} (hd : d ∈ Sm m) (a : F) :
    ⟪jointWithin (⨆ k, Sm k) (X a), d⟫ = 0 := by
  rw [inner_jointWithin_symm,
    jointWithin_eq_zero_iff.mpr (Submodule.mem_iSup_of_mem m hd), inner_zero_right]

/-- **Theorem 3(c), second claim.** `X̃'(ν + s) = X̃'ν` for every `s ∈ 𝒮`. -/
theorem within_inner_add_mem_eq {S : Submodule ℝ E} {X : F →ₗ[ℝ] E} (a : F) (ν : E) {s : E}
    (hs : s ∈ S) : ⟪jointWithin S (X a), ν + s⟫ = ⟪jointWithin S (X a), ν⟫ := by
  rw [inner_add_right, inner_jointWithin_right hs (X a), add_zero]

end JointProjection

end Multiway
