import Multiway.OrthoSum
import Multiway.Incremental
import Multiway.RankExtract
import Multiway.Local
import Multiway.Parallel
import Multiway.Spanning

/-!
# Dimension-wise Mundlak equivalence

This file formalizes Proposition 1 of the paper (dimension-wise Mundlak equivalence). The
fixed-effect spaces are a family `P : D → Submodule ℝ E` containing the constant space `C₀`, the
dimension-wise controls span `dwControls C₀ P W`, and `G_X = 0` is the containment
`col(P_[Δ]X) ⊆ col(𝒞_DW(X))`, which Theorem 1 turns into equality of coefficients.

## Main results

* `spanning_of_single`: clause (i), a single dimension.
* `starProjection_iSup_eq`: `P_[Δ] = ∑_m P_m - (M-1)P_0` under pairwise `P_mP_ℓ = P_0`.
* `spanning_of_pairwise`: clause (ii), `G_X = 0` under pairwise `P_mP_ℓ = P_0`.
* `commute_of_uniform_spanning`: clause (iii) in contrapositive form: uniform equivalence
  forces `P_mP_{-m} = P_{-m}P_m`.
-/

namespace Multiway

open Submodule LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {D : Type*}

/-- `col(𝒞_DW(X)) = span(ι_n) + ∑_m col(P_mX)`, the span of the dimension-wise controls. -/
noncomputable def dwControls (C₀ : Submodule ℝ E) (P : D → Submodule ℝ E)
    (W : Submodule ℝ E) : Submodule ℝ E :=
  C₀ ⊔ ⨆ m, W.map ((P m).starProjection : E →ₗ[ℝ] E)

section Single

variable {C₀ : Submodule ℝ E} {P : D → Submodule ℝ E} {W : Submodule ℝ E}

/-- **Proposition 1(i).** If `𝒮` is the fixed-effect space of a single dimension, then
`G_X = 0`. -/
theorem spanning_of_single {m₀ : D} (hone : (⨆ m, P m) = P m₀) :
    W.map (((⨆ m, P m).starProjection : E →ₗ[ℝ] E)) ≤ dwControls C₀ P W := by
  rw [hone, dwControls]
  exact le_sup_of_le_right (le_iSup (fun m => W.map (((P m).starProjection : E →ₗ[ℝ] E))) m₀)

end Single

section Pairwise

variable [Fintype D] [Nonempty D] {C₀ : Submodule ℝ E} {P : D → Submodule ℝ E}
variable {W : Submodule ℝ E}

omit [Fintype D] [Nonempty D] in
/-- `P_mP_0 = P_0`: the constant space sits inside every dimension's space, so its projector
is fixed by each `P_m`. The companion `P_0P_m = P_0` is Mathlib's
`starProjection_comp_starProjection_of_le`. -/
theorem starProjection_const_fixed (hconst : ∀ m, C₀ ≤ P m) (m : D) (x : E) :
    (P m).starProjection (C₀.starProjection x) = C₀.starProjection x :=
  starProjection_eq_self_iff.mpr (hconst m (C₀.starProjection_apply_mem x))

omit [Fintype D] [Nonempty D] in
/-- `R_m := P_m - P_0` is the orthogonal projector onto `𝒮_m ∩ span(ι_n)^⊥`
(Lemma SM.B.1). -/
theorem starProjection_inf_orthogonal (hconst : ∀ m, C₀ ≤ P m) (m : D) (x : E) :
    (P m ⊓ C₀ᗮ).starProjection x = (P m).starProjection x - C₀.starProjection x := by
  have h := DFunLike.congr_fun (incrementalProjector_eq_starProjection_inf (hconst m)) x
  simpa using h.symm

omit [Fintype D] [Nonempty D] in
/-- For `m ≠ ℓ` with `P_mP_ℓ = P_0`, the spaces `𝒮_m ∩ span(ι_n)^⊥` and
`𝒮_ℓ ∩ span(ι_n)^⊥` are orthogonal. -/
theorem inf_orthogonal_isOrtho (hconst : ∀ m, C₀ ≤ P m)
    (hpair : ∀ m ℓ, m ≠ ℓ → ∀ x : E,
      (P m).starProjection ((P ℓ).starProjection x) = C₀.starProjection x)
    {m ℓ : D} (hml : m ≠ ℓ) : (P m ⊓ C₀ᗮ) ⟂ (P ℓ ⊓ C₀ᗮ) := by
  refine (starProjection_comp_eq_zero_iff _ _).mp ?_
  intro x
  have h0 : ∀ y : E, C₀.starProjection ((P ℓ).starProjection y) = C₀.starProjection y :=
    fun y => DFunLike.congr_fun (starProjection_comp_starProjection_of_le (hconst ℓ)) y
  have hC : C₀.starProjection (C₀.starProjection x) = C₀.starProjection x :=
    starProjection_eq_self_iff.mpr (C₀.starProjection_apply_mem x)
  rw [starProjection_inf_orthogonal hconst ℓ x, map_sub,
    starProjection_inf_orthogonal hconst m, starProjection_inf_orthogonal hconst m,
    hpair m ℓ hml x, h0 x, starProjection_const_fixed hconst m x, hC]
  abel

/-- The family the decomposition runs over: the constant space, and one `𝒮_m ∩ span(ι_n)^⊥`
per dimension. -/
noncomputable def constFamily (C₀ : Submodule ℝ E) (P : D → Submodule ℝ E) : Option D → Submodule ℝ E
  | none => C₀
  | some m => P m ⊓ C₀ᗮ

omit [FiniteDimensional ℝ E] [Fintype D] [Nonempty D] in
/-- The constant space is orthogonal to every `𝒮_m ∩ span(ι_n)^⊥`. -/
theorem const_isOrtho_inf (m : D) : C₀ ⟂ (P m ⊓ C₀ᗮ) :=
  (Submodule.isOrtho_iff_le.mpr inf_le_right).symm

omit [Fintype D] in
/-- `𝒮_m = span(ι_n) ⊕ (𝒮_m ∩ ι_n^⊥)` for every `m`, so the constant space and the
`col(R_m)` together span `𝒮_1 + ⋯ + 𝒮_M`. -/
theorem iSup_option_eq (hconst : ∀ m, C₀ ≤ P m) :
    (⨆ i, constFamily C₀ P i) = ⨆ m, P m := by
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    rintro (_ | m)
    · exact le_trans (hconst (Classical.arbitrary D)) (le_iSup P _)
    · exact le_trans inf_le_left (le_iSup P m)
  · refine iSup_le fun m => ?_
    have hdecomp : C₀ ⊔ (C₀ᗮ ⊓ P m) = P m :=
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hconst m)
    rw [← hdecomp]
    refine sup_le ?_ ?_
    · exact le_iSup (constFamily C₀ P) none
    · exact le_trans (le_of_eq (inf_comm _ _)) (le_iSup (constFamily C₀ P) (some m))

/-- **Proposition 1(ii), projector identity.** `P_[Δ] = ∑_m P_m - (M-1)P_0`. -/
theorem starProjection_iSup_eq (hconst : ∀ m, C₀ ≤ P m)
    (hpair : ∀ m ℓ, m ≠ ℓ → ∀ x : E,
      (P m).starProjection ((P ℓ).starProjection x) = C₀.starProjection x) (x : E) :
    (⨆ m, P m).starProjection x
      = (∑ m, (P m).starProjection x)
        - ((Fintype.card D : ℝ) - 1) • C₀.starProjection x := by
  classical
  have hfam : ∀ i j : Option D, i ≠ j → constFamily C₀ P i ⟂ constFamily C₀ P j := by
    rintro (_ | m) (_ | ℓ) hij
    · exact absurd rfl hij
    · exact const_isOrtho_inf ℓ
    · exact (const_isOrtho_inf m).symm
    · exact inf_orthogonal_isOrtho hconst hpair fun h => hij (by rw [h])
  have hsum := sum_starProjection_of_isOrtho hfam x
  simp only [iSup_option_eq hconst] at hsum
  rw [← hsum, Fintype.sum_option]
  show C₀.starProjection x + ∑ m : D, (P m ⊓ C₀ᗮ).starProjection x = _
  simp only [starProjection_inf_orthogonal hconst]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ, sub_smul, one_smul]
  abel

/-- **Proposition 1(ii).** Every column of `P_[Δ]X` lies in `col(𝒞_DW(X))`, that is,
`G_X = 0`. -/
theorem spanning_of_pairwise (hconst : ∀ m, C₀ ≤ P m)
    (hpair : ∀ m ℓ, m ≠ ℓ → ∀ x : E,
      (P m).starProjection ((P ℓ).starProjection x) = C₀.starProjection x) :
    W.map (((⨆ m, P m).starProjection : E →ₗ[ℝ] E)) ≤ dwControls C₀ P W := by
  classical
  rintro _ ⟨y, hy, rfl⟩
  have hid := starProjection_iSup_eq hconst hpair y
  show ((⨆ m, P m).starProjection : E →ₗ[ℝ] E) y ∈ dwControls C₀ P W
  have hy' : ((⨆ m, P m).starProjection : E →ₗ[ℝ] E) y
      = (∑ m, (P m).starProjection y)
        - ((Fintype.card D : ℝ) - 1) • C₀.starProjection y := hid
  rw [hy']
  refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · refine Submodule.sum_mem _ fun m _ => ?_
    refine Submodule.mem_sup_right ?_
    exact le_iSup (fun m => W.map (((P m).starProjection : E →ₗ[ℝ] E))) m ⟨y, hy, rfl⟩
  · exact Submodule.mem_sup_left (C₀.starProjection_apply_mem y)

end Pairwise

/-! ### Clause (iii): non-commuting projectors rule equivalence out -/

section Existence

open scoped RealInnerProductSpace

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
variable {C₀ : Submodule ℝ E} {P : D → Submodule ℝ E} {m : D}

/-- The regressor `X_x := [x + w_1 - Q_[Δ]x, w_2, …, w_K]`: the map `a ↦ w a + φ(a) • v`,
with `w` carrying `K` independent columns from `col(Q_[Δ])` and `φ` selecting the first. -/
def perturbedRegressor (w : F →ₗ[ℝ] E) (φ : F →ₗ[ℝ] ℝ) (v : E) : F →ₗ[ℝ] E :=
  w + LinearMap.smulRight φ v

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem perturbedRegressor_apply (w : F →ₗ[ℝ] E) (φ : F →ₗ[ℝ] ℝ) (v : E) (a : F) :
    perturbedRegressor w φ v a = w a + φ a • v := rfl

/-- **Proposition 1(iii)**, contrapositive form: if the spanning condition holds at every
identified `X`, then `P_mP_{-m} = P_{-m}P_m`. -/
theorem commute_of_uniform_spanning [Nontrivial F] (hM : ∃ ℓ, ℓ ≠ m)
    (hconst : ∀ ℓ, C₀ ≤ P ℓ)
    (hrank : Module.finrank ℝ F ≤ Module.finrank ℝ ((⨆ ℓ, P ℓ)ᗮ : Submodule ℝ E))
    (huniform : ∀ X : F →ₗ[ℝ] E, Identified (⨆ ℓ, P ℓ) X →
      (LinearMap.range X).map (((⨆ ℓ, P ℓ).starProjection : E →ₗ[ℝ] E))
        ≤ dwControls C₀ P (LinearMap.range X)) :
    ((P m).starProjection : E →ₗ[ℝ] E).comp
        ((⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ).starProjection : E →ₗ[ℝ] E)
      = ((⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ).starProjection : E →ₗ[ℝ] E).comp
        ((P m).starProjection : E →ₗ[ℝ] E) := by
  classical
  have hTS : (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) ≤ ⨆ ℓ, P ℓ :=
    iSup_le fun ℓ => iSup_le fun _ => le_iSup P ℓ
  have hPmS : P m ≤ ⨆ ℓ, P ℓ := le_iSup P m
  -- `A_m` and `B_m`
  have hA0 := incrementalProjector_comp_orthogonal hTS
  have hB0 := incrementalMundlak_comp_orthogonal (T := ⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) hPmS
  -- `A_mQ_[Δ] = B_mQ_[Δ] = 0` on `col(Q_[Δ])`
  have hAmem : ∀ z : E, z ∈ ((⨆ ℓ, P ℓ)ᗮ : Submodule ℝ E) →
      incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) z = 0 := by
    intro z hz
    have h := DFunLike.congr_fun hA0 z
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply,
      starProjection_eq_self_iff.mpr hz] at h
    exact h
  have hBmem : ∀ z : E, z ∈ ((⨆ ℓ, P ℓ)ᗮ : Submodule ℝ E) →
      incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) z = 0 := by
    intro z hz
    have h := DFunLike.congr_fun hB0 z
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply,
      starProjection_eq_self_iff.mpr hz] at h
    exact h
  -- both maps see only the fitted component of their argument
  have hAsplit : ∀ x : E, incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) x
      = incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ)
        ((⨆ ℓ, P ℓ).starProjection x) := by
    intro x
    conv_lhs => rw [← (⨆ ℓ, P ℓ).starProjection_add_starProjection_orthogonal x]
    rw [map_add, hAmem _ ((⨆ ℓ, P ℓ)ᗮ.starProjection_apply_mem x), add_zero]
  have hBsplit : ∀ x : E, incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) x
      = incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m)
        ((⨆ ℓ, P ℓ).starProjection x) := by
    intro x
    conv_lhs => rw [← (⨆ ℓ, P ℓ).starProjection_add_starProjection_orthogonal x]
    rw [map_add, hBmem _ ((⨆ ℓ, P ℓ)ᗮ.starProjection_apply_mem x), add_zero]
  -- the columns, and the functional that picks the first of them
  obtain ⟨w, hwinj, hwmem⟩ := exists_injective_range_le (F := F) ((⨆ ℓ, P ℓ)ᗮ) hrank
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : F)
  have hwa₀ : w a₀ ≠ 0 := fun h => ha₀ (hwinj (by rw [h, map_zero]))
  set φ : F →ₗ[ℝ] ℝ := ((innerSL ℝ (w a₀) : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ).comp w with hφdef
  have hφa₀ : φ a₀ ≠ 0 := by
    have : φ a₀ = ⟪w a₀, w a₀⟫ := rfl
    rw [this, real_inner_self_eq_norm_sq]
    positivity
  -- `A_mx ∈ span(B_mx)` for every `x`
  have hkey : ∀ x : E, incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) x
      ∈ Submodule.span ℝ {incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) x} := by
    intro x
    set X : F →ₗ[ℝ] E := perturbedRegressor w φ ((⨆ ℓ, P ℓ).starProjection x) with hXdef
    -- `Q_[Δ]X_x = [w_1,…,w_K]` has full column rank, so `X_x` is identified
    have hQX : ∀ a, ((⨆ ℓ, P ℓ)ᗮ).starProjection (X a) = w a := by
      intro a
      rw [hXdef, perturbedRegressor_apply, map_add, map_smul,
        starProjection_eq_self_iff.mpr (hwmem a),
        starProjection_orthogonal_apply_eq_zero ((⨆ ℓ, P ℓ).starProjection_apply_mem x),
        smul_zero, add_zero]
    have hid : Identified (⨆ ℓ, P ℓ) X := by
      intro a ha
      have h0 : ((⨆ ℓ, P ℓ)ᗮ).starProjection (X a) = 0 :=
        starProjection_orthogonal_apply_eq_zero ha
      rw [hQX a] at h0
      exact hwinj (by rw [h0, map_zero])
    -- `col(A_mX_x) ⊆ col(B_mX_x)` by Theorem 1 and Lemma SM.B.2
    have hloc := local_spanning_of_two_dimensions (P := P) (m := m)
      (W := LinearMap.range X) (C₀ := C₀) hM hconst (huniform X hid)
    -- the two images are the single columns `A_mx` and `B_mx`
    have hAX : ∀ a, incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (X a)
        = φ a • incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) x := by
      intro a
      rw [hXdef, perturbedRegressor_apply, map_add, map_smul, hAmem _ (hwmem a), zero_add,
        ← hAsplit x]
    have hBX : ∀ a, incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) (X a)
        = φ a • incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) x := by
      intro a
      rw [hXdef, perturbedRegressor_apply, map_add, map_smul, hBmem _ (hwmem a), zero_add,
        ← hBsplit x]
    have hmem : incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (X a₀)
        ∈ (LinearMap.range X).map
          (incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m)) :=
      hloc ⟨X a₀, ⟨a₀, rfl⟩, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hmem
    obtain ⟨a, rfl⟩ := hz
    rw [hAX a₀, hBX a] at hzeq
    -- `φ a₀ • A_mx = φ a • B_mx`, and `φ a₀ ≠ 0`
    refine Submodule.mem_span_singleton.mpr ⟨(φ a₀)⁻¹ * φ a, ?_⟩
    rw [mul_smul, hzeq, smul_smul, inv_mul_cancel₀ hφa₀, one_smul]
  -- `A_m = λB_m` by Lemma SM.C.1
  obtain ⟨lam, hlam⟩ := exists_smul_eq_of_forall_mem_span_singleton hkey
  by_cases hA : incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) = 0
  · -- if `A_m = 0` then `𝒮_m ⊆ 𝒮_{-m}`, so the two commute
    have hPeq : ((⨆ ℓ, P ℓ).starProjection : E →ₗ[ℝ] E)
        = ((⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ).starProjection : E →ₗ[ℝ] E) := by
      ext x
      have h := DFunLike.congr_fun hA x
      rw [incrementalProjector_apply, LinearMap.zero_apply, sub_eq_zero] at h
      exact h
    have hST : (⨆ ℓ, P ℓ) = (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) := by
      calc (⨆ ℓ, P ℓ)
          = LinearMap.range (((⨆ ℓ, P ℓ).starProjection : E →ₗ[ℝ] E)) :=
            (range_starProjection _).symm
        _ = LinearMap.range (((⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ).starProjection : E →ₗ[ℝ] E)) := by
            rw [hPeq]
        _ = _ := range_starProjection _
    have hle : P m ≤ ⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ := hST ▸ hPmS
    ext x
    have h1 : (P m).starProjection ((⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ).starProjection x)
        = (P m).starProjection x :=
      DFunLike.congr_fun (starProjection_comp_starProjection_of_le hle) x
    have h2 : (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ).starProjection ((P m).starProjection x)
        = (P m).starProjection x :=
      starProjection_eq_self_iff.mpr (hle ((P m).starProjection_apply_mem x))
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, h1, h2]
  · -- `B_m = λ⁻¹A_m` is symmetric, which forces commutation
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      exact hA (by rw [hlam, zero_smul])
    have hAsymm := (incrementalProjector_isSymmetricProjection hTS).isSymmetric
    have hBsymm : ∀ u v : E,
        ⟪incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) u, v⟫
          = ⟪u, incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) v⟫ := by
      intro u v
      have hB : ∀ z : E, incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) z
          = lam⁻¹ • incrementalProjector (⨆ ℓ, P ℓ) (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) z := by
        intro z
        have := DFunLike.congr_fun hlam z
        rw [LinearMap.smul_apply] at this
        rw [this, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      rw [hB u, hB v, real_inner_smul_left, real_inner_smul_right, hAsymm u v]
    -- unwind `B_m = Q_{-m}P_m` and cancel the common `⟪·, P_m ·⟫` term
    have hBval : ∀ z : E, incrementalMundlak (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ) (P m) z
        = (P m).starProjection z
          - (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ).starProjection ((P m).starProjection z) := by
      intro z
      rw [incrementalMundlak_apply, Submodule.starProjection_orthogonal_val]
    ext x
    refine ext_inner_left ℝ fun u => ?_
    have h := hBsymm u x
    rw [hBval u, hBval x, inner_sub_left, inner_sub_right,
      Submodule.inner_starProjection_left_eq_right (P m) u x,
      Submodule.inner_starProjection_left_eq_right (⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ)
        ((P m).starProjection u) x,
      Submodule.inner_starProjection_left_eq_right (P m) u
        ((⨆ ℓ, ⨆ (_ : ℓ ≠ m), P ℓ).starProjection x)] at h
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    linarith [h]

end Existence

end Multiway
