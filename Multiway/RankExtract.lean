import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Real.Basic

/-!
# Extracting an injective map into a subspace from a rank inequality

If a finite-dimensional space `F` has no more dimensions than a subspace `V`, then there is an
injective linear map from `F` whose range lies in `V`. The proof of Proposition 1(iii) uses it
to choose linearly independent `w_1, …, w_K ∈ col(Q_[Δ])` from `rank(Q_[Δ]) ≥ K`.

## Main results

* `exists_injective_range_le`: the injective map into the subspace.
-/

namespace Multiway

open Module

variable {E F : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- If `finrank F ≤ finrank V`, there is an injective linear map into `E` whose range lies
in `V`. -/
theorem exists_injective_range_le [FiniteDimensional ℝ F] (V : Submodule ℝ E)
    [FiniteDimensional ℝ V] (h : finrank ℝ F ≤ finrank ℝ V) :
    ∃ w : F →ₗ[ℝ] E, Function.Injective w ∧ ∀ a, w a ∈ V := by
  classical
  set bF : Basis (Fin (finrank ℝ F)) ℝ F := finBasis ℝ F with hbF
  set bV : Basis (Fin (finrank ℝ V)) ℝ V := finBasis ℝ V with hbV
  -- the `K` columns are a subfamily of a basis of `V`, mapped into `E`
  set f : Fin (finrank ℝ F) → E := fun i => (bV (Fin.castLE h i) : E) with hf
  have hsub : LinearIndependent ℝ (fun i : Fin (finrank ℝ F) => bV (Fin.castLE h i)) :=
    bV.linearIndependent.comp _ (Fin.castLE_injective h)
  have hli : LinearIndependent ℝ f := hsub.map' V.subtype (Submodule.ker_subtype V)
  refine ⟨bF.constr ℝ f, bF.injective_constr_of_linearIndependent hli, ?_⟩
  intro a
  rw [Basis.constr_apply_fintype]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bV (Fin.castLE h i)).2

end Multiway
