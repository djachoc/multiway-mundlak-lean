import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Abel

/-!
# Parallel images

This file formalizes Lemma SM.C.1 of the paper (Parallel images): if `A, B` are linear maps with
`A x ∈ span(B x)` for every `x`, then `A = λ B` for some scalar `λ`. The statement is proved for
an arbitrary real vector space, with no finite-dimensionality or inner product, and then
specialised to `Fin n → ℝ`.

The proof is pointwise. A fixed `x₀` with `B x₀ ≠ 0` determines `λ`, and each `x` with
`B x ≠ 0` is handled according to whether `B x` and `B x₀` are linearly dependent (using that
`B x = B y` forces `A x = A y`) or independent (comparing coefficients).

## Main results

* `ker_le_ker_of_forall_mem_span`, `apply_eq_of_apply_eq`: `ker B ⊆ ker A` and its consequence.
* `exists_smul_eq_of_forall_mem_span_singleton`: the lemma on a general real vector space.
* `eq_smul_id_of_forall_mem_span_singleton`: the case `B = id`.
* `parallel_images`: the lemma on `ℝⁿ`.
-/

namespace Multiway

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- If `A x ∈ span(B x)` for every `x`, then `ker B ⊆ ker A`. -/
theorem ker_le_ker_of_forall_mem_span {A B : V →ₗ[ℝ] V}
    (h : ∀ x, A x ∈ Submodule.span ℝ {B x}) :
    LinearMap.ker B ≤ LinearMap.ker A := by
  intro x hx
  have hBx : B x = 0 := LinearMap.mem_ker.mp hx
  have hA := h x
  rw [hBx, Submodule.span_zero_singleton, Submodule.mem_bot] at hA
  exact LinearMap.mem_ker.mpr hA

/-- If `A x ∈ span(B x)` for every `x`, then two points with the same image under `B` have the
same image under `A`. -/
theorem apply_eq_of_apply_eq {A B : V →ₗ[ℝ] V}
    (h : ∀ x, A x ∈ Submodule.span ℝ {B x}) {x y : V} (hxy : B x = B y) :
    A x = A y := by
  have hk : x - y ∈ LinearMap.ker B := by
    simp [LinearMap.mem_ker, map_sub, hxy]
  have hA := ker_le_ker_of_forall_mem_span h hk
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hA
  exact hA

/-- **Lemma SM.C.1.** If `A x` lies on the line through `B x` for every `x`, then `A = λ B` for a
single scalar `λ`, on an arbitrary real vector space. -/
theorem exists_smul_eq_of_forall_mem_span_singleton {A B : V →ₗ[ℝ] V}
    (h : ∀ x, A x ∈ Submodule.span ℝ {B x}) :
    ∃ lam : ℝ, A = lam • B := by
  -- if `B = 0`, then `A = 0`
  by_cases hB : ∀ x, B x = 0
  · refine ⟨0, ?_⟩
    ext x
    have hAx : A x = 0 :=
      LinearMap.mem_ker.mp
        (ker_le_ker_of_forall_mem_span h (LinearMap.mem_ker.mpr (hB x)))
    simp [hAx]
  -- otherwise choose `x₀` with `B x₀ ≠ 0`; it determines `λ`
  rw [not_forall] at hB
  obtain ⟨x₀, hx₀⟩ := hB
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp (h x₀)
  refine ⟨lam, ?_⟩
  ext x
  simp only [LinearMap.smul_apply]
  -- if `B x = 0`, use the kernel inclusion
  by_cases hBx : B x = 0
  · have hAx : A x = 0 :=
      LinearMap.mem_ker.mp
        (ker_le_ker_of_forall_mem_span h (LinearMap.mem_ker.mpr hBx))
    rw [hAx, hBx, smul_zero]
  by_cases hdep : ∃ μ : ℝ, B x = μ • B x₀
  · -- `B x` and `B x₀` are collinear, so `B x = B (μ • x₀)`
    obtain ⟨μ, hμ⟩ := hdep
    have hBeq : B x = B (μ • x₀) := by rw [map_smul]; exact hμ
    have hA : A x = A (μ • x₀) := apply_eq_of_apply_eq h hBeq
    rw [hA, map_smul, ← hlam, hμ, smul_smul, smul_smul, mul_comm]
  · -- if `B x` and `B x₀` are independent, compare coefficients
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h x)
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (h (x + x₀))
    -- by linearity, `c • B x + lam • B x₀ = d • B x + d • B x₀`
    have h1 : d • B x + d • B x₀ = c • B x + lam • B x₀ := by
      simp only [map_add, smul_add] at hd
      rw [← hc, ← hlam] at hd
      exact hd
    have key : (c - d) • B x = (d - lam) • B x₀ := by
      have h2 : (c - d) • B x - (d - lam) • B x₀
          = (c • B x + lam • B x₀) - (d • B x + d • B x₀) := by
        rw [sub_smul, sub_smul]; abel
      rw [← h1, sub_self] at h2
      exact sub_eq_zero.mp h2
    -- if `c ≠ d`, `B x` would be a multiple of `B x₀`
    have hcd : c = d := by
      by_contra hne
      refine hdep ⟨(d - lam) / (c - d), ?_⟩
      have hne' : c - d ≠ 0 := sub_ne_zero.mpr hne
      rw [div_eq_inv_mul, ← smul_smul, ← key, smul_smul, inv_mul_cancel₀ hne', one_smul]
    -- with `c = d`, `(d - lam) • B x₀ = 0` and `B x₀ ≠ 0`
    rw [hcd, sub_self, zero_smul] at key
    have hdlam : d = lam := sub_eq_zero.mp ((smul_eq_zero.mp key.symm).resolve_right hx₀)
    rw [← hc, hcd, hdlam]

/-- If `T v ∈ span(v)` for every `v`, then `T = λ I`: the case `B = id` of the lemma. -/
theorem eq_smul_id_of_forall_mem_span_singleton {T : V →ₗ[ℝ] V}
    (h : ∀ v, T v ∈ Submodule.span ℝ {v}) :
    ∃ lam : ℝ, T = lam • LinearMap.id :=
  exists_smul_eq_of_forall_mem_span_singleton (B := LinearMap.id) (by simpa using h)

/-- **Lemma SM.C.1** on `ℝⁿ = Fin n → ℝ`. -/
theorem parallel_images {n : ℕ} {A B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (h : ∀ x, A x ∈ Submodule.span ℝ {B x}) :
    ∃ lam : ℝ, A = lam • B :=
  exists_smul_eq_of_forall_mem_span_singleton h

end Multiway
