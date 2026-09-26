import Multiway.Parallel
import Multiway.Local
import Multiway.JointProjection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Nonvacuity witnesses for the algebraic results

A theorem whose hypotheses cannot hold simultaneously is vacuously true. This file exhibits
concrete models in which the hypotheses of four algebraic results hold jointly and the
conclusions are non-trivial: Lemma SM.C.1 (parallel images), Lemma SM.B.1 (incremental
projector), Lemma SM.B.2 (global spanning implies local spanning) and the minimality part of
Theorem 3. Each witness applies the theorem to its model and then proves that the model is not
degenerate.

The inner-product models live in `EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`,
and every geometric step reduces to `⟪e_i, e_j⟫ = 𝟙{i = j}`. The parallel-images model lives
on `Fin 2 → ℝ`.
-/

namespace Multiway
namespace AlgebraWitness

open Submodule LinearMap
open RealInnerProductSpace

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Lemma SM.C.1: parallel images

With `B = I` and `A = 3I`, the hypothesis `∀ x, Ax ∈ span{Bx}` holds with `A`, `B` and the
scalar all non-zero, and the scalar is determined. -/

section ParallelWitness

/-- `B = I` on `ℝ²`. -/
def parB : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.id

/-- `A = 3I`, so that the scalar the lemma produces is `3` and not `0`. -/
def parA : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := (3 : ℝ) • LinearMap.id

theorem parA_apply (x : Fin 2 → ℝ) : parA x = (3 : ℝ) • x := rfl

theorem parB_apply (x : Fin 2 → ℝ) : parB x = x := rfl

/-- The lemma's hypothesis holds: `Ax = 3x` is on the line through `Bx = x`. -/
theorem par_hyp (x : Fin 2 → ℝ) : parA x ∈ Submodule.span ℝ {parB x} := by
  rw [parA_apply, parB_apply]
  exact Submodule.mem_span_singleton.mpr ⟨3, rfl⟩

theorem parA_ne_zero : parA ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (fun _ => (1 : ℝ))
  have h2 := congrFun h1 0
  rw [parA_apply] at h2
  norm_num at h2

theorem parB_ne_zero : parB ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (fun _ => (1 : ℝ))
  have h2 := congrFun h1 0
  rw [parB_apply] at h2
  norm_num at h2

/-- **Nonvacuity witness for `Multiway.parallel_images`.** The scalar the lemma produces is
`3`, and no other scalar works. -/
theorem parallel_images_witness :
    (∃ lam : ℝ, parA = lam • parB)
      ∧ parA = (3 : ℝ) • parB
      ∧ (∀ lam : ℝ, parA = lam • parB → lam = 3)
      ∧ parA ≠ 0 ∧ parB ≠ 0 := by
  refine ⟨Multiway.parallel_images par_hyp, ?_, ?_, parA_ne_zero, parB_ne_zero⟩
  · refine LinearMap.ext fun x => ?_
    rw [parA_apply, LinearMap.smul_apply, parB_apply]
  · intro lam hlam
    have h1 := DFunLike.congr_fun hlam (fun _ => (1 : ℝ))
    have h2 := congrFun h1 0
    rw [parA_apply, LinearMap.smul_apply, parB_apply] at h2
    simpa using h2.symm

end ParallelWitness

/-! ## 2. Coordinate vectors

Basic facts about the standard coordinate vectors used by the witnesses below. -/

section Coords

/-- `e_i`, the `i`-th standard coordinate vector of `ℝⁿ`. -/
noncomputable def ev {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single i (1 : ℝ)

theorem inner_ev_self {n : ℕ} (i : Fin n) : ⟪(ev i : EuclideanSpace ℝ (Fin n)), ev i⟫ = 1 := by
  rw [ev, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp

theorem inner_ev_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    ⟪(ev i : EuclideanSpace ℝ (Fin n)), ev j⟫ = 0 := by
  rw [ev, ev, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  simp [h]

theorem ev_ne_zero {n : ℕ} (i : Fin n) : (ev i : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
  intro h
  have h1 : ⟪(ev i : EuclideanSpace ℝ (Fin n)), ev i⟫ = 1 := inner_ev_self i
  rw [h, inner_zero_right] at h1
  norm_num at h1

/-- `e_j ≠ e_i + e_j` for `i ≠ j`, read off the inner product with `e_i`. -/
theorem ev_ne_add {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (ev j : EuclideanSpace ℝ (Fin n)) ≠ ev i + ev j := by
  intro hEq
  have h1 : ⟪(ev i : EuclideanSpace ℝ (Fin n)), ev j⟫
      = ⟪(ev i : EuclideanSpace ℝ (Fin n)), ev i + ev j⟫ := by rw [← hEq]
  rw [inner_add_right, inner_ev_self, inner_ev_ne h] at h1
  norm_num at h1

/-- `e_j ⟂ span{e_i}` for `i ≠ j`. -/
theorem ev_mem_orthogonal_singleton {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (ev j : EuclideanSpace ℝ (Fin n))
      ∈ (Submodule.span ℝ {(ev i : EuclideanSpace ℝ (Fin n))})ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  rw [← hc, inner_smul_left, inner_ev_ne h]
  simp

/-- `e_j ∉ span{e_i}` for `i ≠ j`: a member of that span is orthogonal to `e_j`, so `⟪e_j,e_j⟫`
would be `0`. -/
theorem ev_notMem_span_singleton {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (ev j : EuclideanSpace ℝ (Fin n))
      ∉ Submodule.span ℝ {(ev i : EuclideanSpace ℝ (Fin n))} := by
  intro hmem
  have h0 : ⟪(ev j : EuclideanSpace ℝ (Fin n)), ev j⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hmem (ev_mem_orthogonal_singleton h)
  rw [inner_ev_self] at h0
  norm_num at h0

/-- `e_2 ⟂ span{e_0, e_1}` in `ℝ³`. -/
theorem ev2_mem_orthogonal_pair :
    (ev 2 : E3) ∈ (Submodule.span ℝ {(ev 0 : E3), ev 1})ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hu
  rw [← hab, inner_add_left, inner_smul_left, inner_smul_left,
    inner_ev_ne (by decide : (0 : Fin 3) ≠ 2), inner_ev_ne (by decide : (1 : Fin 3) ≠ 2)]
  simp

/-- `⊤.map P_V = V`: the image of the whole space under an orthogonal projector is the
subspace it projects onto. -/
theorem top_map_starProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Submodule ℝ E) :
    (⊤ : Submodule ℝ E).map ((V.starProjection : E →ₗ[ℝ] E)) = V := by
  refine le_antisymm (Multiway.map_starProjection_le V ⊤) ?_
  intro v hv
  refine ⟨v, Submodule.mem_top, ?_⟩
  simpa using Submodule.starProjection_eq_self_iff.mpr hv

end Coords

/-! ## 3. Lemma SM.B.1: the incremental projector

The model: `𝒮_{-m} = span{e_0}`, `𝒮_m = span{e_0 + e_1}` and `𝒮 = 𝒮_{-m} + 𝒮_m` in `ℝ²`. Neither
subspace is trivial and they are not orthogonal, so `A_m`, the projector onto
`Q_{-m}𝒮_m = span{e_1}`, is non-zero and differs from `P_{𝒮_m}`. -/

section IncrementalWitness

/-- `𝒮_{-m}`, the span of the other dimensions' dummies. -/
noncomputable def incT : Submodule ℝ E2 := Submodule.span ℝ {(ev 0 : E2)}

/-- `𝒮_m`, dimension `m`'s own span, not orthogonal to `incT`. -/
noncomputable def incU : Submodule ℝ E2 := Submodule.span ℝ {(ev 0 : E2) + ev 1}

/-- `𝒮 = 𝒮_{-m} + 𝒮_m`. -/
noncomputable def incS : Submodule ℝ E2 := incT ⊔ incU

theorem incS_def : incS = incT ⊔ incU := rfl

/-- The lemma's hypothesis `T ⊔ U = S`. -/
theorem inc_hS : incT ⊔ incU = incS := rfl

theorem ev0_mem_incT : (ev 0 : E2) ∈ incT := Submodule.mem_span_singleton_self _

theorem inc_sum_mem_incU : (ev 0 : E2) + ev 1 ∈ incU := Submodule.mem_span_singleton_self _

theorem inc_sum_mem_incS : (ev 0 : E2) + ev 1 ∈ incS := by
  rw [incS_def]
  exact Submodule.mem_sup_right inc_sum_mem_incU

theorem ev0_mem_incS : (ev 0 : E2) ∈ incS := by
  rw [incS_def]
  exact Submodule.mem_sup_left ev0_mem_incT

theorem ev1_mem_incS : (ev 1 : E2) ∈ incS := by
  have h := incS.sub_mem inc_sum_mem_incS ev0_mem_incS
  simpa using h

theorem starProjection_incT_ev0 : incT.starProjection (ev 0 : E2) = ev 0 :=
  Submodule.starProjection_eq_self_iff.mpr ev0_mem_incT

theorem starProjection_incT_ev1 : incT.starProjection (ev 1 : E2) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff incT).mpr
    (ev_mem_orthogonal_singleton (by decide : (0 : Fin 2) ≠ 1))

/-- `A_m e_1 = e_1`: `e_1 ∈ 𝒮` and `e_1 ⟂ 𝒮_{-m}`. -/
theorem inc_projector_ev1 :
    incrementalProjector incS incT (ev 1 : E2) = ev 1 := by
  rw [incrementalProjector_apply, starProjection_incT_ev1,
    Submodule.starProjection_eq_self_iff.mpr ev1_mem_incS, sub_zero]

/-- `A_m ≠ 0`. -/
theorem inc_projector_ne_zero :
    incrementalProjector incS incT ≠ (0 : E2 →ₗ[ℝ] E2) := by
  intro h
  have h1 := DFunLike.congr_fun h (ev 1 : E2)
  rw [inc_projector_ev1] at h1
  exact ev_ne_zero 1 h1

/-- `A_m(e_0 + e_1) = e_1`, whereas `P_{𝒮_m}(e_0+e_1) = e_0+e_1`. -/
theorem inc_projector_sum :
    incrementalProjector incS incT ((ev 0 : E2) + ev 1) = ev 1 := by
  rw [incrementalProjector_apply,
    Submodule.starProjection_eq_self_iff.mpr inc_sum_mem_incS, map_add,
    starProjection_incT_ev0, starProjection_incT_ev1, add_zero]
  abel

/-- `A_m ≠ P_{𝒮_m}`: the incremental projector differs from dimension `m`'s own projector. -/
theorem inc_projector_ne_starProjection_U :
    incrementalProjector incS incT ≠ ((incU.starProjection : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) := by
  intro h
  have h1 := DFunLike.congr_fun h ((ev 0 : E2) + ev 1)
  rw [inc_projector_sum, ContinuousLinearMap.coe_coe,
    Submodule.starProjection_eq_self_iff.mpr inc_sum_mem_incU] at h1
  exact ev_ne_add (by decide : (0 : Fin 2) ≠ 1) h1

/-- **Nonvacuity witness for `Multiway.incremental_projector`**, on a model where `𝒮_{-m}`
and `𝒮_m` are non-trivial and non-orthogonal. The first clause is used through
`inc_projector_ne_starProjection_U`; the remaining clauses are stated in full. -/
theorem incremental_projector_witness :
    LinearMap.range (incrementalMundlak incT incU)
        = LinearMap.range (incrementalProjector incS incT)
      ∧ Module.finrank ℝ (LinearMap.range (incrementalProjector incS incT))
          = Module.finrank ℝ (LinearMap.range (incrementalMundlak incT incU))
      ∧ (incrementalProjector incS incT).comp
          ((incSᗮ).starProjection : E2 →ₗ[ℝ] E2) = 0
      ∧ (incrementalMundlak incT incU).comp
          ((incSᗮ).starProjection : E2 →ₗ[ℝ] E2) = 0
      ∧ incrementalProjector incS incT ≠ 0
      ∧ incrementalProjector incS incT
          ≠ ((incU.starProjection : E2 →L[ℝ] E2) : E2 →ₗ[ℝ] E2) := by
  obtain ⟨-, h2, h3, h4, h5⟩ := Multiway.incremental_projector inc_hS
  exact ⟨h2, h3, h4, h5, inc_projector_ne_zero, inc_projector_ne_starProjection_U⟩

end IncrementalWitness

/-! ## 4. Lemma SM.B.2: global spanning implies local spanning

The model has `M = 2`: `D = Fin 2`, `m = 0`, `𝒮_0 = span{e_0, e_1}`, `𝒮_1 = span{e_0}` and
`ι_n = e_0`, so `C₀ = span{e_0} ≤ 𝒮_ℓ` for both `ℓ`. The hypothesis `hM : ∃ ℓ, ℓ ≠ m` is used to
obtain `C₀ ≤ 𝒮_{-m}`; `local_boundary_at_one_dimension` shows that this containment fails at
`M = 1` whenever `C₀ ≠ ⊥`. -/

section LocalWitness

/-- The two fixed-effect dimensions: `𝒮_0` carries `e_0` and `e_1`, `𝒮_1` only `e_0`. -/
noncomputable def locP : Fin 2 → Submodule ℝ E2 := fun k =>
  if k = 0 then Submodule.span ℝ {(ev 0 : E2), ev 1} else Submodule.span ℝ {(ev 0 : E2)}

/-- `C₀ = span(ι_n)`, with `ι_n = e_0`. -/
noncomputable def locC : Submodule ℝ E2 := Submodule.span ℝ {(ev 0 : E2)}

theorem locC_def : locC = Submodule.span ℝ {(ev 0 : E2)} := rfl

theorem locP_zero : locP 0 = Submodule.span ℝ {(ev 0 : E2), ev 1} := by simp [locP]

theorem locP_one : locP 1 = Submodule.span ℝ {(ev 0 : E2)} := by simp [locP]

/-- `M ≥ 2`: there is a dimension other than `m = 0`. -/
theorem loc_hM : ∃ ℓ : Fin 2, ℓ ≠ (0 : Fin 2) := ⟨1, by decide⟩

/-- `𝒮_ℓ = span{e_0}` at every dimension other than `m = 0`. -/
theorem locP_of_ne {ℓ : Fin 2} (h : ℓ ≠ 0) : locP ℓ = Submodule.span ℝ {(ev 0 : E2)} := by
  simp only [locP]
  rw [if_neg h]

theorem loc_hC : ∀ ℓ : Fin 2, locC ≤ locP ℓ := by
  intro ℓ
  rw [locC_def]
  by_cases h : ℓ = 0
  · subst h
    rw [locP_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp))
  · rw [locP_of_ne h]

/-- Global spanning, at `W = col(X) = ⊤`: every column of `P_[Δ]X` lies in
`span(ι_n) + ∑_ℓ col(P_ℓX)` because the whole joint span does. -/
theorem loc_hglobal :
    (⊤ : Submodule ℝ E2).map (((⨆ ℓ, locP ℓ).starProjection : E2 →ₗ[ℝ] E2))
      ≤ locC ⊔ ⨆ ℓ, (⊤ : Submodule ℝ E2).map (((locP ℓ).starProjection : E2 →ₗ[ℝ] E2)) := by
  rw [top_map_starProjection]
  refine le_trans ?_ le_sup_right
  refine iSup_le fun ℓ => ?_
  rw [← top_map_starProjection (locP ℓ)]
  exact le_iSup
    (fun ℓ => (⊤ : Submodule ℝ E2).map (((locP ℓ).starProjection : E2 →ₗ[ℝ] E2))) ℓ

/-- `𝒮_{-m} ≤ span{e_0}`: the only dimension other than `m = 0` is `1`, whose span is
`span{e_0}`. -/
theorem loc_rest_le :
    (⨆ ℓ : Fin 2, ⨆ (_ : ℓ ≠ (0 : Fin 2)), locP ℓ) ≤ Submodule.span ℝ {(ev 0 : E2)} := by
  refine iSup_le fun ℓ => iSup_le fun h => ?_
  rw [locP_of_ne h]

/-- `A_m e_1 = e_1` on this model: `e_1 ∈ 𝒮` because it is in `𝒮_0`, and `e_1 ⟂ 𝒮_{-m}`. -/
theorem loc_projector_ev1 :
    incrementalProjector (⨆ ℓ : Fin 2, locP ℓ)
        (⨆ ℓ : Fin 2, ⨆ (_ : ℓ ≠ (0 : Fin 2)), locP ℓ) (ev 1 : E2) = ev 1 := by
  have hmemS : (ev 1 : E2) ∈ ⨆ ℓ : Fin 2, locP ℓ := by
    refine le_iSup locP 0 ?_
    rw [locP_zero]
    exact Submodule.subset_span (by simp)
  have hperp : (ev 1 : E2) ∈ (⨆ ℓ : Fin 2, ⨆ (_ : ℓ ≠ (0 : Fin 2)), locP ℓ)ᗮ :=
    Submodule.orthogonal_le loc_rest_le
      (ev_mem_orthogonal_singleton (by decide : (0 : Fin 2) ≠ 1))
  rw [incrementalProjector_apply, Submodule.starProjection_eq_self_iff.mpr hmemS,
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hperp, sub_zero]

/-- **Nonvacuity witness for `Multiway.local_spanning_of_two_dimensions`** at `M = 2`. The
second conjunct shows the containment is not `⊥ ≤ ⊥`. -/
theorem local_spanning_witness :
    ((⊤ : Submodule ℝ E2).map
        (incrementalProjector (⨆ ℓ : Fin 2, locP ℓ)
          (⨆ ℓ : Fin 2, ⨆ (_ : ℓ ≠ (0 : Fin 2)), locP ℓ))
      ≤ (⊤ : Submodule ℝ E2).map
          (incrementalMundlak (⨆ ℓ : Fin 2, ⨆ (_ : ℓ ≠ (0 : Fin 2)), locP ℓ) (locP 0)))
      ∧ (⊤ : Submodule ℝ E2).map
          (incrementalProjector (⨆ ℓ : Fin 2, locP ℓ)
            (⨆ ℓ : Fin 2, ⨆ (_ : ℓ ≠ (0 : Fin 2)), locP ℓ)) ≠ ⊥ := by
  refine ⟨Multiway.local_spanning_of_two_dimensions loc_hM loc_hC loc_hglobal, ?_⟩
  intro h
  have hmem : (ev 1 : E2) ∈ (⊤ : Submodule ℝ E2).map
      (incrementalProjector (⨆ ℓ : Fin 2, locP ℓ)
        (⨆ ℓ : Fin 2, ⨆ (_ : ℓ ≠ (0 : Fin 2)), locP ℓ)) :=
    ⟨ev 1, Submodule.mem_top, loc_projector_ev1⟩
  rw [h, Submodule.mem_bot] at hmem
  exact ev_ne_zero 1 hmem

/-- At `M = 1` the residual span `𝒮_{-m}` is `⊥`, so the containment `C₀ ≤ 𝒮_{-m}` fails
whenever `C₀ ≠ ⊥`. -/
theorem local_boundary_at_one_dimension (Q : Fin 1 → Submodule ℝ E2) :
    (⨆ ℓ : Fin 1, ⨆ (_ : ℓ ≠ (0 : Fin 1)), Q ℓ) = ⊥
      ∧ ¬ (locC ≤ ⨆ ℓ : Fin 1, ⨆ (_ : ℓ ≠ (0 : Fin 1)), Q ℓ) := by
  have hbot : (⨆ ℓ : Fin 1, ⨆ (_ : ℓ ≠ (0 : Fin 1)), Q ℓ) = ⊥ :=
    le_antisymm (iSup_le fun ℓ => iSup_le fun h => absurd (Subsingleton.elim ℓ 0) h) bot_le
  refine ⟨hbot, ?_⟩
  rw [hbot]
  intro hle
  have h0 : (ev 0 : E2) ∈ (⊥ : Submodule ℝ E2) := hle (Submodule.mem_span_singleton_self _)
  rw [Submodule.mem_bot] at h0
  exact ev_ne_zero 0 h0

end LocalWitness

/-! ## 5. Theorem 3: minimality

The model: `ℝ³` with `𝒮 = span{e_0, e_1}`, `K = 1` and `X a = a(e_0 + e_2)`. Then
`X'Q_[Δ]X ≻ 0` because `e_0 + e_2 ∉ 𝒮`, and `col(P_[Δ]X) = span{e_0}`. The least element lies
strictly between `⊥` and `𝒮`, and `𝒮` itself belongs to the set, so the minimality claim is
non-trivial. -/

section JmWitness

/-- `𝒮 = span{e_0, e_1}`, the joint fixed-effects space, two-dimensional inside `ℝ³`. -/
noncomputable def jmS : Submodule ℝ E3 := Submodule.span ℝ {(ev 0 : E3), ev 1}

/-- `X : ℝ → ℝ³`, `X a = a(e_0 + e_2)`: one regressor, with a component inside `𝒮` and a
component orthogonal to it. -/
noncomputable def jmX : ℝ →ₗ[ℝ] E3 :=
  LinearMap.toSpanSingleton ℝ E3 ((ev 0 : E3) + ev 2)

theorem jmX_apply (a : ℝ) : jmX a = a • ((ev 0 : E3) + ev 2) := rfl

theorem ev0_mem_jmS : (ev 0 : E3) ∈ jmS := Submodule.subset_span (by simp)

theorem ev1_mem_jmS : (ev 1 : E3) ∈ jmS := Submodule.subset_span (by simp)

theorem jm_regressor_notMem : (ev 0 : E3) + ev 2 ∉ jmS := by
  intro hmem
  have h2 : (ev 2 : E3) ∈ jmS := by
    have h := jmS.sub_mem hmem ev0_mem_jmS
    simpa using h
  have h0 : ⟪(ev 2 : E3), ev 2⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal h2 ev2_mem_orthogonal_pair
  rw [inner_ev_self] at h0
  norm_num at h0

/-- The identification condition holds: `Xa ∈ 𝒮` forces `a = 0`, because
`e_0 + e_2 ∉ 𝒮`. -/
theorem jm_identified : Identified jmS jmX := by
  intro a ha
  by_contra hne
  refine jm_regressor_notMem ?_
  have h := jmS.smul_mem a⁻¹ ha
  rwa [jmX_apply, smul_smul, inv_mul_cancel₀ hne, one_smul] at h

theorem starProjection_jmS_regressor :
    jmS.starProjection ((ev 0 : E3) + ev 2) = ev 0 := by
  rw [map_add, Submodule.starProjection_eq_self_iff.mpr ev0_mem_jmS,
    (Submodule.starProjection_apply_eq_zero_iff jmS).mpr ev2_mem_orthogonal_pair, add_zero]

/-- `col(P_[Δ]X) = span{e_0}`. -/
theorem jm_jointProjControls :
    jointProjControls jmS jmX = Submodule.span ℝ {(ev 0 : E3)} := by
  have hrange : LinearMap.range jmX = Submodule.span ℝ {((ev 0 : E3) + ev 2)} :=
    LinearMap.range_toSpanSingleton _
  show (LinearMap.range jmX).map (jmS.starProjection : E3 →L[ℝ] E3).toLinearMap
      = Submodule.span ℝ {(ev 0 : E3)}
  rw [hrange, Submodule.map_span, Set.image_singleton,
    show (jmS.starProjection : E3 →L[ℝ] E3).toLinearMap ((ev 0 : E3) + ev 2) = ev 0 from
      starProjection_jmS_regressor]

/-- `col(P_[Δ]X) ≠ ⊥`. -/
theorem jm_jointProjControls_ne_bot : jointProjControls jmS jmX ≠ ⊥ := by
  rw [jm_jointProjControls]
  intro h
  have h0 : (ev 0 : E3) ∈ (⊥ : Submodule ℝ E3) := by
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  rw [Submodule.mem_bot] at h0
  exact ev_ne_zero 0 h0

/-- `col(P_[Δ]X) ≠ 𝒮`: `e_1 ∈ 𝒮` is not in it. -/
theorem jm_jointProjControls_ne_S : jointProjControls jmS jmX ≠ jmS := by
  rw [jm_jointProjControls]
  intro h
  exact ev_notMem_span_singleton (by decide : (0 : Fin 3) ≠ 1) (h ▸ ev1_mem_jmS)

/-- **Nonvacuity witness for `Multiway.jm_isLeast`** (Theorem 3, minimality). The least
element is neither `⊥` nor `𝒮`, and `𝒮` itself belongs to the set. -/
theorem jm_isLeast_witness :
    IsLeast {W : Submodule ℝ E3 |
        W ≤ jmS ∧ ∀ (y : E3) (b : ℝ), IsAugSlope W jmX y b ↔ IsMFESlope jmS jmX y b}
        (jointProjControls jmS jmX)
      ∧ jointProjControls jmS jmX ≠ ⊥
      ∧ jointProjControls jmS jmX ≠ jmS
      ∧ jmS ∈ {W : Submodule ℝ E3 |
          W ≤ jmS ∧ ∀ (y : E3) (b : ℝ), IsAugSlope W jmX y b ↔ IsMFESlope jmS jmX y b} := by
  refine ⟨Multiway.jm_isLeast jm_identified, jm_jointProjControls_ne_bot,
    jm_jointProjControls_ne_S, le_rfl, ?_⟩
  exact (Multiway.spanning jm_identified le_rfl).mpr fun a => jmS.starProjection_apply_mem (jmX a)

end JmWitness

end AlgebraWitness
end Multiway
