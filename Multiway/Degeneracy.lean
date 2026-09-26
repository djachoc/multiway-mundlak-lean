import Multiway.GroupCompute

/-!
# Degeneracy along the fixed-effect dimensions

This file formalizes Corollary SM.D.2 of the paper (degeneracy along the fixed-effect
dimensions). Under the Regime 2 decomposition `ν_o = ∑_{∅≠e} h^{(e)}(U_{o⊙e}) + ε_o`,
`X̃'ν = ∑_{2≤|e|≤M} ∑_{t ∈ 𝒯_e} w^{(e)}_t h^{(e)}(U_t) + ∑_o x̃_o ε_o`, and every level-one
term vanishes identically. The statement is an identity in every realization: `h^{(e)}(U_t)`
and `ε_o` are arbitrary reals indexed by sub-tuple and observation, and the weight `f` is
arbitrary apart from `hzero` (`Δ_m'X̃ = 0`, the sum of `f` over each level-`{m}` cell is zero).

## Notation

* `c : D → O → L` gives `i_m(o)`; `cellOf c e o` and `cells c e` are `o ⊙ e` and `𝒯_e`;
* `h e t` is `h^{(e)}(U_t)`; `eps` and `nu` are `ε` and `ν`;
* `cellWeight f t` is the score weight `w^{(e)}_t = ∑_{o : o⊙e = t} x̃_o`.

## Main results

* `score_decomposition`: the score decomposition over all nonempty levels.
* `score_degeneracy`: the level-one terms vanish (Corollary SM.D.2).
* `withinScore_degeneracy`: the `ℝ^K`-valued form.
-/

namespace Multiway

open Finset

variable {O D L K : Type*}

section Degeneracy

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `w^{(e)}_t = ∑_{o : o⊙e = t} x̃_o`, the score weight of a sub-tuple. -/
def cellWeight (f : O → ℝ) (t : Finset O) : ℝ := ∑ o ∈ t, f o

/-- A cell of `𝒯_e` is the cell of each of its members. -/
theorem cellOf_eq_of_mem {c : D → O → L} {e : Finset D} {t : Finset O} (ht : t ∈ cells c e)
    {o : O} (ho : o ∈ t) : cellOf c e o = t := by
  classical
  obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 ht
  exact cellOf_eq_iff.2 (by simpa using ho)

/-- A sum over observations of a weight times a quantity depending on `o` only through
`o ⊙ e` is a sum over `𝒯_e` of the score weights times that quantity. -/
theorem sum_mul_kernel (c : D → O → L) (e : Finset D) (f : O → ℝ) (g : Finset O → ℝ) :
    ∑ o : O, f o * g (cellOf c e o) = ∑ t ∈ cells c e, cellWeight f t * g t := by
  classical
  rw [← sum_over_cells c e (fun o => f o * g (cellOf c e o))]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [cellWeight, Finset.sum_mul]
  exact Finset.sum_congr rfl fun o ho => by rw [cellOf_eq_of_mem ht ho]

/-- The score decomposition: substituting the Regime 2 decomposition into `X̃'ν` and
collecting terms by sub-tuple, over all nonempty levels. -/
theorem score_decomposition (c : D → O → L) (dims : Finset D) (f : O → ℝ)
    (h : Finset D → Finset O → ℝ) (eps nu : O → ℝ)
    (hnu : ∀ o : O, nu o
      = (∑ e ∈ dims.powerset.filter (fun e => e.Nonempty), h e (cellOf c e o)) + eps o) :
    ∑ o : O, f o * nu o
      = (∑ e ∈ dims.powerset.filter (fun e => e.Nonempty),
          ∑ t ∈ cells c e, cellWeight f t * h e t) + ∑ o : O, f o * eps o := by
  classical
  have hterm : ∀ o : O, f o * nu o
      = (∑ e ∈ dims.powerset.filter (fun e => e.Nonempty), f o * h e (cellOf c e o))
        + f o * eps o := by
    intro o
    rw [hnu o, mul_add, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun o _ => hterm o), Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun e _ => sum_mul_kernel c e f (h e)

/-- Under `Δ_m'X̃ = 0`, every level-one score weight vanishes. -/
theorem level_one_eq_zero (c : D → O → L) {f : O → ℝ} {m : D}
    (hzero : ∀ t ∈ cells c ({m} : Finset D), cellWeight f t = 0) (g : Finset O → ℝ) :
    ∑ o : O, f o * g (cellOf c ({m} : Finset D) o) = 0 := by
  rw [sum_mul_kernel]
  exact Finset.sum_eq_zero fun t ht => by rw [hzero t ht, zero_mul]

/-- **Corollary SM.D.2.** With the level-one terms deleted, the score is carried by the
interactions of order at least two and the idiosyncratic part alone. -/
theorem score_degeneracy (c : D → O → L) (dims : Finset D) (f : O → ℝ)
    (h : Finset D → Finset O → ℝ) (eps nu : O → ℝ)
    (hnu : ∀ o : O, nu o
      = (∑ e ∈ dims.powerset.filter (fun e => e.Nonempty), h e (cellOf c e o)) + eps o)
    (hzero : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), cellWeight f t = 0) :
    ∑ o : O, f o * nu o
      = (∑ e ∈ dims.powerset.filter (fun e => 2 ≤ e.card),
          ∑ t ∈ cells c e, cellWeight f t * h e t) + ∑ o : O, f o * eps o := by
  classical
  rw [score_decomposition c dims f h eps nu hnu]
  congr 1
  set P : Finset (Finset D) := dims.powerset.filter (fun e => e.Nonempty) with hP
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun e => e.card = 1)
      (fun e => ∑ t ∈ cells c e, cellWeight f t * h e t)
  rw [← hsplit]
  have hone : ∑ e ∈ P.filter (fun e => e.card = 1),
      (∑ t ∈ cells c e, cellWeight f t * h e t) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨heP, hcard⟩ := Finset.mem_filter.1 he
    obtain ⟨m, rfl⟩ := Finset.card_eq_one.1 hcard
    have hm : m ∈ dims := by
      have : ({m} : Finset D) ⊆ dims := Finset.mem_powerset.1 (Finset.mem_filter.1 heP).1
      exact this (Finset.mem_singleton_self m)
    exact Finset.sum_eq_zero fun t ht => by rw [hzero m hm t ht, zero_mul]
  have hrest : P.filter (fun e => ¬ e.card = 1) = dims.powerset.filter (fun e => 2 ≤ e.card) := by
    ext e
    simp only [hP, Finset.mem_filter, Finset.mem_powerset, Finset.nonempty_iff_ne_empty]
    constructor
    · rintro ⟨⟨hsub, hne⟩, hcard⟩
      refine ⟨hsub, ?_⟩
      have h1 : e.card ≠ 0 := fun hc => hne (Finset.card_eq_zero.1 hc)
      omega
    · rintro ⟨hsub, hcard⟩
      refine ⟨⟨hsub, ?_⟩, by omega⟩
      intro hc
      rw [hc] at hcard
      simp at hcard
  rw [hone, hrest, zero_add]

/-- **Corollary SM.D.2**, `ℝ^K`-valued form. `X̃'ν` is the vector whose `k`-th coordinate
is `∑_o x̃_{ok} ν_o`; `hzero` is `Δ_m'X̃ = 0`, one equation per dimension, category and
coordinate. -/
theorem withinScore_degeneracy (c : D → O → L) (dims : Finset D) (xt : O → K → ℝ)
    (h : Finset D → Finset O → ℝ) (eps nu : O → ℝ)
    (hnu : ∀ o : O, nu o
      = (∑ e ∈ dims.powerset.filter (fun e => e.Nonempty), h e (cellOf c e o)) + eps o)
    (hzero : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ k : K,
      cellWeight (fun o => xt o k) t = 0) :
    (fun k : K => ∑ o : O, xt o k * nu o)
      = fun k : K => (∑ e ∈ dims.powerset.filter (fun e => 2 ≤ e.card),
          ∑ t ∈ cells c e, cellWeight (fun o => xt o k) t * h e t)
        + ∑ o : O, xt o k * eps o := by
  funext k
  exact score_degeneracy c dims (fun o => xt o k) h eps nu hnu
    (fun m hm t ht => hzero m hm t ht k)

end Degeneracy

end Multiway
