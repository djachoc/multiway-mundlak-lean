import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Spanning: when a Mundlak augmentation reproduces the multiway fixed-effects slope

This file formalizes Theorem 1 of the paper (Spanning). Under the rank condition
`X'Q_[Δ]X ≻ 0` and `col(𝒞) ⊆ 𝒮`, the augmented slope `β̂_𝒞` is uniquely defined, and
`β̂_𝒞 = β̂_MFE` for every `y` if and only if `col(P_[Δ]X) ⊆ col(𝒞)`. Matrices are replaced by
subspaces of a finite-dimensional real inner product space and both estimators are
characterized by their normal equations, so no (generalized) inverse is needed.

## Notation

* `E` is the observation space `ℝⁿ`, `F` the coefficient space, `X : F →ₗ[ℝ] E` the regressors;
* `S` is the fixed-effects space `𝒮` and `W ≤ S` is `col(𝒞)`;
* `S.starProjection` is `P_[Δ]` and `jointWithin S` is `Q_[Δ] = I_n - P_[Δ]`;
* `Identified S X` is the rank condition; `IsMFESlope` and `IsAugSlope` are the normal
  equations of `β̂_MFE` and `β̂_𝒞`.

## Main results

* `mfeSlope_exists`, `mfeSlope_unique`, `augSlope_existsUnique`: existence and uniqueness.
* `spanning`: the characterization. Necessity is proved by testing the hypothesis at
  `y = M_𝒞P_[Δ]Xa`, which forces `‖M_𝒞P_[Δ]Xa‖² = 0`.
-/

namespace Multiway

open RealInnerProductSpace

section Spanning

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [AddCommGroup F] [Module ℝ F]

/-! ### The joint within transformation `Q_[Δ] = I_n - P_[Δ]` -/

/-- `I_n - P_S`, the residual maker of a subspace: `Q_[Δ]` at `S = 𝒮` and `M_𝒞` at
`S = col(𝒞)`. -/
noncomputable def jointWithin (S : Submodule ℝ E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - S.starProjection

@[simp]
lemma jointWithin_apply (S : Submodule ℝ E) (u : E) :
    jointWithin S u = u - S.starProjection u := rfl

lemma jointWithin_sub (S : Submodule ℝ E) (u v : E) :
    jointWithin S (u - v) = jointWithin S u - jointWithin S v := by
  simp only [jointWithin_apply, map_sub]

lemma jointWithin_mem_orthogonal (S : Submodule ℝ E) (u : E) : jointWithin S u ∈ Sᗮ :=
  S.sub_starProjection_mem_orthogonal u

/-- `Q_[Δ]u = 0` exactly when `u ∈ 𝒮`. -/
lemma jointWithin_eq_zero_iff {S : Submodule ℝ E} {u : E} :
    jointWithin S u = 0 ↔ u ∈ S := by
  rw [jointWithin_apply, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- `u = P_[Δ]u + Q_[Δ]u`. -/
lemma starProjection_add_jointWithin (S : Submodule ℝ E) (u : E) :
    S.starProjection u + jointWithin S u = u := by
  rw [jointWithin_apply, add_sub_cancel]

/-- Anything in `𝒮` is orthogonal to any joint within component. -/
lemma inner_jointWithin_left {S : Submodule ℝ E} {s : E} (hs : s ∈ S) (u : E) :
    ⟪s, jointWithin S u⟫ = 0 :=
  Submodule.inner_right_of_mem_orthogonal hs (jointWithin_mem_orthogonal S u)

/-- The same orthogonality with the arguments the other way round. -/
lemma inner_jointWithin_right {S : Submodule ℝ E} {s : E} (hs : s ∈ S) (u : E) :
    ⟪jointWithin S u, s⟫ = 0 :=
  Submodule.inner_left_of_mem_orthogonal hs (jointWithin_mem_orthogonal S u)

lemma inner_split_left (S : Submodule ℝ E) (u v : E) :
    ⟪u, v⟫ = ⟪S.starProjection u, v⟫ + ⟪jointWithin S u, v⟫ := by
  conv_lhs => rw [← starProjection_add_jointWithin S u]
  rw [inner_add_left]

lemma inner_split_right (S : Submodule ℝ E) (u v : E) :
    ⟪u, v⟫ = ⟪u, S.starProjection v⟫ + ⟪u, jointWithin S v⟫ := by
  conv_lhs => rw [← starProjection_add_jointWithin S v]
  rw [inner_add_right]

/-- `u'v = (P_[Δ]u)'v` whenever `v ∈ 𝒮`: only the joint between component of `u` matters. -/
lemma inner_eq_inner_starProjection {S : Submodule ℝ E} {v : E} (hv : v ∈ S) (u : E) :
    ⟪u, v⟫ = ⟪S.starProjection u, v⟫ := by
  rw [inner_split_left S u v, inner_jointWithin_right hv u, add_zero]

/-- `u'Q_[Δ]v = (Q_[Δ]u)'(Q_[Δ]v)`. -/
lemma inner_jointWithin_comp (S : Submodule ℝ E) (u v : E) :
    ⟪u, jointWithin S v⟫ = ⟪jointWithin S u, jointWithin S v⟫ := by
  rw [inner_split_left S u (jointWithin S v),
    inner_jointWithin_left (S.starProjection_apply_mem u) v, zero_add]

/-- `(Q_[Δ]u)'v = (Q_[Δ]u)'(Q_[Δ]v)`. -/
lemma inner_jointWithin_comp' (S : Submodule ℝ E) (u v : E) :
    ⟪jointWithin S u, v⟫ = ⟪jointWithin S u, jointWithin S v⟫ := by
  rw [inner_split_right S (jointWithin S u) v,
    inner_jointWithin_right (S.starProjection_apply_mem v) u, zero_add]

/-! ### The rank condition -/

/-- The rank condition `X'Q_[Δ]X ≻ 0`: no nonzero linear combination of the regressors lies
in the fixed-effects space. -/
def Identified (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) : Prop := ∀ a : F, X a ∈ S → a = 0

/-- `Identified` is equivalent to `a'X'Q_[Δ]Xa > 0` for every `a ≠ 0`, since the quadratic
form equals `‖Q_[Δ]Xa‖²`. -/
theorem identified_iff_inner_pos (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) :
    Identified S X ↔ ∀ a : F, a ≠ 0 → 0 < ⟪X a, jointWithin S (X a)⟫ := by
  constructor
  · intro hid a ha
    rw [inner_jointWithin_comp, real_inner_self_pos]
    intro hzero
    exact ha (hid a (jointWithin_eq_zero_iff.mp hzero))
  · intro hpos a hmem
    by_contra ha
    have hz : jointWithin S (X a) = 0 := jointWithin_eq_zero_iff.mpr hmem
    have hlt := hpos a ha
    rw [hz, inner_zero_right] at hlt
    exact lt_irrefl 0 hlt

/-! ### The two estimators, by their normal equations -/

/-- `b` is a multiway fixed-effects slope at `y`: the normal equations
`X'Q_[Δ](y - Xb) = 0`. -/
def IsMFESlope (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) (y : E) (b : F) : Prop :=
  ∀ a : F, ⟪X a, jointWithin S (y - X b)⟫ = 0

/-- `b` is the coefficient on `X` in the OLS regression of `y` on `(X, 𝒞)`: there is a
control fit `w ∈ col(𝒞)` making the residual `y - Xb - w` orthogonal to `col(X)` and to
`col(𝒞)`. -/
def IsAugSlope (W : Submodule ℝ E) (X : F →ₗ[ℝ] E) (y : E) (b : F) : Prop :=
  ∃ w ∈ W, (∀ a : F, ⟪X a, y - X b - w⟫ = 0) ∧ (∀ v ∈ W, ⟪v, y - X b - w⟫ = 0)

/-! ### `β̂_MFE` exists and is unique -/

theorem mfeSlope_exists (S : Submodule ℝ E) (X : F →ₗ[ℝ] E) (y : E) :
    ∃ b : F, IsMFESlope S X y b := by
  -- project `Q_[Δ]y` onto the range of `T := Q_[Δ]X`
  let T : F →ₗ[ℝ] E := (jointWithin S : E →L[ℝ] E).toLinearMap ∘ₗ X
  have hTapply : ∀ a : F, T a = jointWithin S (X a) := fun _ => rfl
  obtain ⟨b, hb⟩ :=
    LinearMap.mem_range.mp ((LinearMap.range T).starProjection_apply_mem (jointWithin S y))
  refine ⟨b, fun a => ?_⟩
  have horth := (LinearMap.range T).sub_starProjection_mem_orthogonal (jointWithin S y)
  have h0 : ⟪T a, jointWithin S y - T b⟫ = 0 := by
    rw [hb]
    exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self T a) horth
  rw [hTapply, hTapply] at h0
  rw [inner_jointWithin_comp, jointWithin_sub]
  exact h0

theorem mfeSlope_unique {S : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hid : Identified S X) {y : E}
    {b₁ b₂ : F} (h₁ : IsMFESlope S X y b₁) (h₂ : IsMFESlope S X y b₂) : b₁ = b₂ := by
  -- subtract the normal equations and apply the rank condition
  have hsplit : X (b₂ - b₁) = (y - X b₁) - (y - X b₂) := by rw [map_sub]; abel
  have hc : ∀ a : F, ⟪X a, jointWithin S (X (b₂ - b₁))⟫ = 0 := by
    intro a
    rw [hsplit, jointWithin_sub, inner_sub_right, h₁ a, h₂ a, sub_zero]
  have hzero : jointWithin S (X (b₂ - b₁)) = 0 := by
    have h0 := hc (b₂ - b₁)
    rw [inner_jointWithin_comp] at h0
    exact inner_self_eq_zero.mp h0
  have hb : b₂ - b₁ = 0 := hid _ (jointWithin_eq_zero_iff.mp hzero)
  exact (sub_eq_zero.mp hb).symm

/-! ### `β̂_𝒞` exists and is unique -/

theorem augSlope_exists (W : Submodule ℝ E) (X : F →ₗ[ℝ] E) (y : E) :
    ∃ b : F, IsAugSlope W X y b := by
  -- project `y` onto `col(X) + col(𝒞)` and split along the sum
  obtain ⟨u, hu, w, hw, huw⟩ :=
    Submodule.mem_sup.mp ((LinearMap.range X ⊔ W).starProjection_apply_mem y)
  obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hu
  have horth : y - (LinearMap.range X ⊔ W).starProjection y ∈ (LinearMap.range X ⊔ W)ᗮ :=
    (LinearMap.range X ⊔ W).sub_starProjection_mem_orthogonal y
  have hres : y - X b - w = y - (LinearMap.range X ⊔ W).starProjection y := by
    rw [← huw]; abel
  refine ⟨b, w, hw, fun a => ?_, fun v hv => ?_⟩
  · rw [hres]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_sup_left (LinearMap.mem_range_self X a)) horth
  · rw [hres]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_sup_right hv) horth

omit [FiniteDimensional ℝ E] in
theorem augSlope_unique {S W : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hid : Identified S X)
    (hWS : W ≤ S) {y : E} {b₁ b₂ : F} (h₁ : IsAugSlope W X y b₁)
    (h₂ : IsAugSlope W X y b₂) : b₁ = b₂ := by
  -- the residual difference lies in `col(X) + col(𝒞)` and is orthogonal to it
  obtain ⟨w₁, hw₁, hx₁, hv₁⟩ := h₁
  obtain ⟨w₂, hw₂, hx₂, hv₂⟩ := h₂
  have hwmem : w₁ - w₂ ∈ W := W.sub_mem hw₁ hw₂
  have hg1 : ⟪X (b₂ - b₁) - (w₁ - w₂), y - X b₁ - w₁⟫ = 0 := by
    rw [inner_sub_left, hx₁ (b₂ - b₁), hv₁ _ hwmem, sub_zero]
  have hg2 : ⟪X (b₂ - b₁) - (w₁ - w₂), y - X b₂ - w₂⟫ = 0 := by
    rw [inner_sub_left, hx₂ (b₂ - b₁), hv₂ _ hwmem, sub_zero]
  have hdiff : (y - X b₁ - w₁) - (y - X b₂ - w₂) = X (b₂ - b₁) - (w₁ - w₂) := by
    rw [map_sub]; abel
  have hgself : ⟪X (b₂ - b₁) - (w₁ - w₂), X (b₂ - b₁) - (w₁ - w₂)⟫ = 0 := by
    have hstep : ⟪X (b₂ - b₁) - (w₁ - w₂), (y - X b₁ - w₁) - (y - X b₂ - w₂)⟫ = 0 := by
      rw [inner_sub_right, hg1, hg2, sub_zero]
    rwa [hdiff] at hstep
  have hg0 : X (b₂ - b₁) - (w₁ - w₂) = 0 := inner_self_eq_zero.mp hgself
  rw [sub_eq_zero] at hg0
  have hb : b₂ - b₁ = 0 := hid _ (hg0 ▸ hWS hwmem)
  exact (sub_eq_zero.mp hb).symm

/-- Under the rank condition and `col(𝒞) ⊆ 𝒮`, the coefficient `β̂_𝒞` is uniquely defined. -/
theorem augSlope_existsUnique {S W : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hid : Identified S X)
    (hWS : W ≤ S) (y : E) : ∃! b : F, IsAugSlope W X y b := by
  obtain ⟨b, hb⟩ := augSlope_exists W X y
  exact ⟨b, hb, fun b' hb' => augSlope_unique hid hWS hb' hb⟩

/-! ### The spanning condition -/

/-- `col(P_[Δ]X) ⊆ col(𝒞)` as a submodule inclusion is the pointwise condition used below. -/
theorem spanning_condition_iff (S W : Submodule ℝ E) (X : F →ₗ[ℝ] E) :
    (LinearMap.range X).map (S.starProjection : E →L[ℝ] E).toLinearMap ≤ W ↔
      ∀ a : F, S.starProjection (X a) ∈ W := by
  constructor
  · intro h a
    exact h (Submodule.mem_map.mpr ⟨X a, LinearMap.mem_range_self X a, rfl⟩)
  · intro h u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hv
    exact h a

/-! ### Sufficiency -/

/-- Sufficiency in Theorem 1: if `M_𝒞P_[Δ]X = 0`, the augmented normal equations reduce to the
fixed-effects ones. -/
theorem isAugSlope_of_isMFESlope {S W : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hWS : W ≤ S)
    (hspan : ∀ a : F, S.starProjection (X a) ∈ W) {y : E} {b : F}
    (h : IsMFESlope S X y b) : IsAugSlope W X y b := by
  refine ⟨W.starProjection (y - X b), W.starProjection_apply_mem _, fun a => ?_,
    fun v hv => ?_⟩
  · -- split `Xa` into `P_[Δ]Xa ∈ col(𝒞)` and `Q_[Δ]Xa`
    show ⟪X a, jointWithin W (y - X b)⟫ = 0
    rw [inner_split_left S (X a) (jointWithin W (y - X b)),
      inner_jointWithin_left (hspan a) (y - X b), zero_add, jointWithin_apply W (y - X b),
      inner_sub_right,
      inner_jointWithin_right (hWS (W.starProjection_apply_mem (y - X b))) (X a), sub_zero,
      inner_jointWithin_comp' S (X a) (y - X b), ← inner_jointWithin_comp S (X a) (y - X b)]
    exact h a
  · show ⟪v, jointWithin W (y - X b)⟫ = 0
    exact inner_jointWithin_left hv (y - X b)

/-! ### Necessity -/

/-- Necessity in Theorem 1: testing the hypothesis at `y = M_𝒞P_[Δ]Xa` forces
`M_𝒞P_[Δ]Xa = 0`. -/
theorem starProjection_mem_of_isMFESlope_imp {S W : Submodule ℝ E} {X : F →ₗ[ℝ] E}
    (hWS : W ≤ S) (h : ∀ (y : E) (b : F), IsMFESlope S X y b → IsAugSlope W X y b) (a : F) :
    S.starProjection (X a) ∈ W := by
  have hdS : jointWithin W (S.starProjection (X a)) ∈ S := by
    rw [jointWithin_apply]
    exact S.sub_mem (S.starProjection_apply_mem (X a))
      (hWS (W.starProjection_apply_mem (S.starProjection (X a))))
  have hdW : jointWithin W (S.starProjection (X a)) ∈ Wᗮ :=
    jointWithin_mem_orthogonal W (S.starProjection (X a))
  -- the column lies in `𝒮`, so the fixed-effects slope is `0`
  have hmfe : IsMFESlope S X (jointWithin W (S.starProjection (X a))) 0 := by
    intro a'
    rw [map_zero, sub_zero, jointWithin_eq_zero_iff.mpr hdS, inner_zero_right]
  obtain ⟨w, hw, hx, hv⟩ := h _ 0 hmfe
  simp only [map_zero, sub_zero] at hx hv
  -- the control fit is orthogonal to the column
  have hw0 : w = 0 := by
    have h1 := hv w hw
    rw [inner_sub_right, Submodule.inner_right_of_mem_orthogonal hw hdW, zero_sub,
      neg_eq_zero] at h1
    exact inner_self_eq_zero.mp h1
  rw [hw0, sub_zero] at hx
  -- the first normal equation reads `⟪Xa, Da⟫ = ‖Da‖² = 0`
  have hxa := hx a
  have hchain : ⟪X a, jointWithin W (S.starProjection (X a))⟫
      = ⟪jointWithin W (S.starProjection (X a)),
          jointWithin W (S.starProjection (X a))⟫ := by
    rw [inner_eq_inner_starProjection hdS (X a), real_inner_comm,
      inner_jointWithin_comp' W (S.starProjection (X a)) (S.starProjection (X a))]
  rw [hchain] at hxa
  exact jointWithin_eq_zero_iff.mp (inner_self_eq_zero.mp hxa)

/-! ### Theorem 1 -/

/-- **Theorem 1 (Spanning).** Under the rank condition and `col(𝒞) ⊆ 𝒮`, the augmented slope
`β̂_𝒞` equals the multiway fixed-effects slope `β̂_MFE` at every outcome `y` if and only if
`col(P_[Δ]X) ⊆ col(𝒞)`. -/
theorem spanning {S W : Submodule ℝ E} {X : F →ₗ[ℝ] E} (hid : Identified S X) (hWS : W ≤ S) :
    (∀ (y : E) (b : F), IsAugSlope W X y b ↔ IsMFESlope S X y b) ↔
      ∀ a : F, S.starProjection (X a) ∈ W := by
  constructor
  · intro h
    exact starProjection_mem_of_isMFESlope_imp hWS fun y b hb => (h y b).mpr hb
  · intro hspan y b
    refine ⟨fun hb => ?_, isAugSlope_of_isMFESlope hWS hspan⟩
    obtain ⟨b', hb'⟩ := mfeSlope_exists S X y
    have hbb : b = b' := augSlope_unique hid hWS hb (isAugSlope_of_isMFESlope hWS hspan hb')
    rw [hbb]
    exact hb'

end Spanning

end Multiway
