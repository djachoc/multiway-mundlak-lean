import Multiway.GroupCompute
import Multiway.Degeneracy
import Mathlib.Algebra.Module.BigOperators

/-!
# Identification after residualization

This file formalizes Lemma SM.B.10 of the paper (identification after residualization): for
every fixed-effect dimension `m`, `R Sh_{m} R = R Δ_m Δ_m' R = 0`, hence
`E[ν̂_FE ν̂_FE' | 𝒟] = R(s̄²I_n + ∑_{e ∈ 𝓔} σ_e² Sh^off_e)R`, a degenerate level contributes
`∑_o x̃_o x̃_o'`, and `nS_n` has the stated plug-in form.

The residual maker `R : Matrix O O ℝ` is abstract, with symmetry, idempotence and `RΔ_m = 0`
as hypotheses (`Multiway.ResidualBridge.residualMatrix` satisfies them). The interaction
structure of the conditional covariance `Om` is the hypothesis `hOmega`. The statement
that the level-one variances do not enter `nS_n` is `Multiway.UnionMeat.nSn_levelOne_invariant`.

## Main results

* `residual_sharing_singleton`: `R Sh_{m} R = R Δ_m Δ_m' R = 0`.
* `residual_moment`, `residual_moment_smul`: the second moments of the residuals.
* `levelOne_variances_absent`: clause (i), level-one variances do not affect `RΩR`.
* `weightGram_eq_obsGram`: clause (ii).
* `targetplug`: the plug-in form of `nS_n`.
-/

namespace Multiway

namespace IdentE2

open Finset

variable {O D L K : Type*}

/-! ### `Δ_eΔ_e'` and the annihilation `R Sh_{m} R = 0` -/

section Headline

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `Δ_eΔ_e'`, the columns of `Δ_e` being the indicators of the cells of level `e`. -/
def deltaGram (c : D → O → L) (e : Finset D) : Matrix O O ℝ :=
  Matrix.of fun o o' =>
    ∑ t ∈ cells c e, (if o ∈ t then (1 : ℝ) else 0) * (if o' ∈ t then (1 : ℝ) else 0)

/-- `Sh_e = Δ_eΔ_e'`. -/
theorem deltaGram_eq_shMat (c : D → O → L) (e : Finset D) : deltaGram c e = shMat c e := by
  ext o o'
  rw [deltaGram, Matrix.of_apply, ← shMat_apply_eq_sum_cells]

/-- A cell of a level on which every pair of observations agrees is all of `𝒪`. -/
theorem mem_cells_eq_univ {c : D → O → L} {e : Finset D} (h : ∀ o o' : O, SameOn c e o o')
    {t : Finset O} (ht : t ∈ cells c e) : t = Finset.univ := by
  classical
  obtain ⟨o₀, -, rfl⟩ := Finset.mem_image.1 ht
  ext o
  simp only [mem_cellOf, Finset.mem_univ, iff_true]
  exact h o o₀

/-- `R Sh_e R = 0` whenever `R` annihilates the indicator of every cell of level `e`; for
`e = {m}` this is `RΔ_m = 0`. -/
theorem residual_shMat_eq_zero (c : D → O → L) (e : Finset D) {R : Matrix O O ℝ}
    (hsymm : R.IsSymm) (hRD : ∀ t ∈ cells c e, ∀ o : O, ∑ o' ∈ t, R o o' = 0) :
    R * shMat c e * R = 0 := by
  ext o o'
  rw [mul_shMat_mul_apply c e hsymm o o', Matrix.zero_apply]
  exact Finset.sum_eq_zero fun s hs => by rw [hRD s hs o, zero_mul]

/-- **Lemma SM.B.10.** `R Sh_{m} R = R Δ_m Δ_m' R = 0`, given `RΔ_m = 0` in the cells form
`hRD`. -/
theorem residual_sharing_singleton (c : D → O → L) (m : D) {R : Matrix O O ℝ}
    (hsymm : R.IsSymm)
    (hRD : ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0) :
    R * shMat c ({m} : Finset D) * R = R * deltaGram c ({m} : Finset D) * R
      ∧ R * deltaGram c ({m} : Finset D) * R = 0 := by
  refine ⟨by rw [deltaGram_eq_shMat], ?_⟩
  rw [deltaGram_eq_shMat]
  exact residual_shMat_eq_zero c _ hsymm hRD

end Headline

/-! ### The second moments of the fixed-effects residuals -/

section Moment

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- **Lemma SM.B.10, second-moment display.** Under the covariance structure `hOmega`, the
level-one blocks are annihilated and `RΩR = R(s̄²I_n + ∑_{e ∈ 𝓔} σ_e² Sh^off_e)R`. Idempotence
of `R` is not needed. -/
theorem residual_moment (c : D → O → L) (dims : Finset D) (Esets : Finset (Finset D))
    (sig1 : D → ℝ) (sige : Finset D → ℝ) (sbar : ℝ) {R Om : Matrix O O ℝ}
    (hsymm : R.IsSymm)
    (hRD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0)
    (hOmega : Om = (∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
      + (sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e)) :
    R * Om * R
      = R * (sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e) * R := by
  have key : R * (∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D)) * R = 0 := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [mul_smul_comm, smul_mul_assoc, residual_shMat_eq_zero c _ hsymm (hRD m hm), smul_zero]
  rw [hOmega, mul_add, add_mul, key, zero_add]

/-- If `R² = R`, then `RΩR = s̄²R + ∑_{e ∈ 𝓔} σ_e² R Sh^off_e R`. -/
theorem residual_moment_smul (c : D → O → L) (dims : Finset D) (Esets : Finset (Finset D))
    (sig1 : D → ℝ) (sige : Finset D → ℝ) (sbar : ℝ) {R Om : Matrix O O ℝ}
    (hsymm : R.IsSymm) (hidem : R * R = R)
    (hRD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0)
    (hOmega : Om = (∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
      + (sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e)) :
    R * Om * R = sbar • R + ∑ e ∈ Esets, sige e • (R * shOff c e * R) := by
  rw [residual_moment c dims Esets sig1 sige sbar hsymm hRD hOmega, mul_add, add_mul]
  congr 1
  · rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hidem]
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]

/-- **Lemma SM.B.10(i), residual moments.** Replacing the level-one variances
`σ²_{1},…,σ²_{M}` by any other values leaves `RΩR` unchanged. -/
theorem levelOne_variances_absent (c : D → O → L) (dims : Finset D)
    (Esets : Finset (Finset D)) (sig1 sig1' : D → ℝ) (sige : Finset D → ℝ) (sbar : ℝ)
    {R Om Om' : Matrix O O ℝ} (hsymm : R.IsSymm)
    (hRD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0)
    (hOmega : Om = (∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
      + (sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e))
    (hOmega' : Om' = (∑ m ∈ dims, sig1' m • shMat c ({m} : Finset D))
      + (sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e)) :
    R * Om * R = R * Om' * R := by
  rw [residual_moment c dims Esets sig1 sige sbar hsymm hRD hOmega,
    residual_moment c dims Esets sig1' sige sbar hsymm hRD hOmega']

end Moment

/-! ### Clause (ii): a degenerate level contributes `∑_o x̃_ox̃_o'` -/

section Weights

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- `∑_{t ∈ 𝒯_e} w^{(e)}_t w^{(e)'}_t`, with `w^{(e)}_t` the score weight
`Multiway.Degeneracy.cellWeight` taken one coordinate at a time. -/
def weightGram (c : D → O → L) (xt : O → K → ℝ) (e : Finset D) : Matrix K K ℝ :=
  Matrix.of fun a b =>
    ∑ t ∈ cells c e, cellWeight (fun o => xt o a) t * cellWeight (fun o => xt o b) t

/-- `∑_{o ∈ 𝒪} x̃_o x̃_o'`. -/
def obsGram (xt : O → K → ℝ) : Matrix K K ℝ :=
  Matrix.of fun a b => ∑ o : O, xt o a * xt o b

/-- If `Sh^off_e = 0`, every realized sub-tuple of level `e` contains exactly one
observation. -/
theorem cellOf_eq_singleton_of_shOff_eq_zero (c : D → O → L) {e : Finset D}
    (h : shOff c e = 0) (o : O) : cellOf c e o = {o} := by
  classical
  have h1 : shMat c e = 1 := by
    rw [shOff, sub_eq_iff_eq_add, zero_add] at h
    exact h
  ext o'
  simp only [mem_cellOf, Finset.mem_singleton]
  constructor
  · intro hs
    by_contra hne
    have h2 : shMat c e o' o = 1 := by simp [shMat, hs]
    have h3 : shMat c e o' o = 0 := by rw [h1, Matrix.one_apply_ne hne]
    rw [h2] at h3
    exact one_ne_zero h3
  · rintro rfl
    exact sameOn_refl o'

/-- **Lemma SM.B.10(ii).** If `Sh^off_e = 0`, then `∑_t w^{(e)}_t w^{(e)'}_t = ∑_o x̃_o x̃_o'`. -/
theorem weightGram_eq_obsGram (c : D → O → L) (xt : O → K → ℝ) {e : Finset D}
    (h : shOff c e = 0) : weightGram c xt e = obsGram xt := by
  classical
  have hcell := cellOf_eq_singleton_of_shOff_eq_zero c h
  have hinj : ∀ o ∈ (univ : Finset O), ∀ o' ∈ (univ : Finset O),
      cellOf c e o = cellOf c e o' → o = o' := by
    intro o _ o' _ hoo
    rw [hcell o, hcell o'] at hoo
    exact Finset.singleton_injective hoo
  ext a b
  rw [weightGram, Matrix.of_apply, obsGram, Matrix.of_apply, cells, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [hcell o, cellWeight, cellWeight, Finset.sum_singleton, Finset.sum_singleton]

end Weights

/-! ### The plug-in form of `nS_n` -/

section TargetPlug

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

/-- **Lemma SM.B.10, plug-in form.**
`nS_n = (s̄² - ∑_{e ∈ 𝓔} σ_e²) ∑_o x̃_o x̃_o' + ∑_{e ∈ 𝓔} σ_e² ∑_t w^{(e)}_t w^{(e)'}_t`,
for `𝓔 ⊆ levels` whose complement in `levels` is degenerate (`hdeg`), with
`s̄² = σ²_ε + ∑_{e ∈ levels} σ_e²` (`hsbar`). -/
theorem targetplug (c : D → O → L) (xt : O → K → ℝ) (levels Esets : Finset (Finset D))
    (sige : Finset D → ℝ) (sigeps sbar : ℝ) {nSn : Matrix K K ℝ}
    (hEsub : Esets ⊆ levels)
    (hdeg : ∀ e ∈ levels \ Esets, shOff c e = 0)
    (hsbar : sbar = sigeps + ∑ e ∈ levels, sige e)
    (hnSn : nSn = sigeps • obsGram xt + ∑ e ∈ levels, sige e • weightGram c xt e) :
    nSn = (sbar - ∑ e ∈ Esets, sige e) • obsGram xt
      + ∑ e ∈ Esets, sige e • weightGram c xt e := by
  classical
  have hsplit : ∑ e ∈ levels, sige e • weightGram c xt e
      = (∑ e ∈ levels \ Esets, sige e • weightGram c xt e)
        + ∑ e ∈ Esets, sige e • weightGram c xt e := (Finset.sum_sdiff hEsub).symm
  have hcomp : ∑ e ∈ levels \ Esets, sige e • weightGram c xt e
      = (∑ e ∈ levels \ Esets, sige e) • obsGram xt := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun e he => by rw [weightGram_eq_obsGram c xt (hdeg e he)]
  have hcoef : sbar - ∑ e ∈ Esets, sige e = sigeps + ∑ e ∈ levels \ Esets, sige e := by
    rw [hsbar, ← Finset.sum_sdiff hEsub]
    ring
  rw [hnSn, hsplit, hcomp, hcoef, add_smul, add_assoc]

end TargetPlug

/-! ### Examples

A model with two observations and three dimensions (dimensions `0` and `1` constant,
dimension `2` the identity) and `R = I - ιι'/2` satisfies every hypothesis of
`residual_moment_smul` and `targetplug`. The level `{0,1}` lies in `𝓔` and `{0,2}` is
degenerate. -/

section Witness

/-- The design of the example, in which dimensions `0` and `1` are constant and dimension `2` is
the identity. -/
def wc : Fin 3 → Fin 2 → Fin 2 := fun d o => if d = 2 then o else 0

/-- The residual maker of the example, the within transformation on two observations. -/
noncomputable def wR : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then (1 / 2 : ℝ) else -(1 / 2)

theorem wR_apply (i j : Fin 2) : wR i j = if i = j then (1 / 2 : ℝ) else -(1 / 2) := rfl

theorem wR_isSymm : wR.IsSymm := by
  show Matrix.transpose wR = wR
  ext i j
  rw [Matrix.transpose_apply, wR_apply, wR_apply]
  rcases eq_or_ne i j with h | h
  · rw [h]
  · simp [h, Ne.symm h]

theorem wR_row_sum (i : Fin 2) : ∑ j : Fin 2, wR i j = 0 := by
  rw [Fin.sum_univ_two, wR_apply, wR_apply]
  fin_cases i <;> norm_num

theorem wR_idem : wR * wR = wR := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [wR_apply]
  fin_cases i <;> fin_cases j <;> norm_num

/-- Every pair of observations agrees on any level avoiding dimension `2`. -/
theorem wc_sameOn {e : Finset (Fin 3)} (he : (2 : Fin 3) ∉ e) (o o' : Fin 2) :
    SameOn wc e o o' := by
  intro d hd
  have hd2 : d ≠ 2 := fun h => he (h ▸ hd)
  simp [wc, hd2]

/-- On such a level `R` annihilates every cell indicator, which is `hRD`. -/
theorem wR_cell_sum {e : Finset (Fin 3)} (he : (2 : Fin 3) ∉ e) :
    ∀ t ∈ cells wc e, ∀ o : Fin 2, ∑ o' ∈ t, wR o o' = 0 := by
  intro t ht o
  rw [mem_cells_eq_univ (wc_sameOn he) ht]
  exact wR_row_sum o

/-- The covariance structure of the example, with level-one variances `3` on each of the two
constant dimensions, `s̄² = 7`, and the single interaction level `{0,1} ∈ 𝓔` with `σ² = 2`. -/
noncomputable def wOm : Matrix (Fin 2) (Fin 2) ℝ :=
  (∑ m ∈ ({0, 1} : Finset (Fin 3)), (3 : ℝ) • shMat wc ({m} : Finset (Fin 3)))
    + ((7 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      + ∑ e ∈ ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))), (2 : ℝ) • shOff wc e)

/-- `residual_moment_smul` on the example. The level-one variance `3` is annihilated and
`R Sh^off_{0,1} R = -R`, so the coefficient is `7 - 2 = 5`. -/
theorem identE2_witness : wR * wOm * wR = (5 : ℝ) • wR := by
  have hRD : ∀ m ∈ ({0, 1} : Finset (Fin 3)),
      ∀ t ∈ cells wc ({m} : Finset (Fin 3)), ∀ o : Fin 2, ∑ o' ∈ t, wR o o' = 0 := by
    intro m hm
    have hm2 : m ≠ 2 := by
      rcases Finset.mem_insert.1 hm with h | h
      · rw [h]; decide
      · rw [Finset.mem_singleton.1 h]; decide
    refine wR_cell_sum ?_
    simp only [Finset.mem_singleton]
    exact fun h => hm2 h.symm
  have hoff : wR * shOff wc ({0, 1} : Finset (Fin 3)) * wR = -wR := by
    ext o o'
    rw [mul_shOff_mul_apply wc _ wR_isSymm wR_idem o o', Matrix.neg_apply]
    have hz : ∀ s ∈ cells wc ({0, 1} : Finset (Fin 3)),
        (∑ a ∈ s, wR o a) * (∑ b ∈ s, wR o' b) = 0 := fun s hs => by
      rw [wR_cell_sum (by decide) s hs o, zero_mul]
    rw [Finset.sum_eq_zero hz, zero_sub]
  rw [residual_moment_smul (Om := wOm) wc ({0, 1} : Finset (Fin 3))
      ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
      (fun _ => (3 : ℝ)) (fun _ => (2 : ℝ)) (7 : ℝ) wR_isSymm wR_idem hRD rfl,
    Finset.sum_singleton, hoff, smul_neg, ← sub_eq_add_neg, ← sub_smul]
  norm_num

/-- `Sh^off = 0` at the level `{0,2}`, so this level is degenerate and lies outside `𝓔`. -/
theorem wc_shOff_zero : shOff wc ({0, 2} : Finset (Fin 3)) = 0 := by
  have hiff : ∀ i j : Fin 2, SameOn wc ({0, 2} : Finset (Fin 3)) i j ↔ i = j := by
    intro i j
    constructor
    · intro h
      simpa [wc] using h 2 (by decide)
    · rintro rfl
      exact sameOn_refl i
  ext i j
  rw [shOff, Matrix.sub_apply, shMat, Matrix.of_apply, Matrix.one_apply, Matrix.zero_apply]
  by_cases h : i = j
  · simp [h, sameOn_refl]
  · have h2 : ¬ SameOn wc ({0, 2} : Finset (Fin 3)) i j := fun hc => h ((hiff i j).1 hc)
    simp [h, h2]

/-- `targetplug` on the example, with `levels = {{0,1},{0,2}}`, `𝓔 = {{0,1}}`,
`σ²_ε = 1` and every `σ_e² = 2`, so that `s̄² = 5`. -/
theorem targetplug_witness :
    (1 : ℝ) • obsGram (fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ))
        + ∑ e ∈ ({({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3))} :
            Finset (Finset (Fin 3))),
          (2 : ℝ) • weightGram wc (fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ)) e
      = ((5 : ℝ) - ∑ _e ∈ ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))), (2 : ℝ))
          • obsGram (fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ))
        + ∑ e ∈ ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))),
          (2 : ℝ) • weightGram wc (fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ)) e := by
  refine targetplug wc (fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ))
    ({({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
    ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
    (fun _ => (2 : ℝ)) (1 : ℝ) (5 : ℝ) (by decide) ?_ ?_ rfl
  · intro e he
    have h1 : e = ({0, 2} : Finset (Fin 3)) := by
      rcases Finset.mem_sdiff.1 he with ⟨hmem, hnot⟩
      rcases Finset.mem_insert.1 hmem with h | h
      · exact absurd (Finset.mem_singleton.2 h) hnot
      · exact Finset.mem_singleton.1 h
    rw [h1]
    exact wc_shOff_zero
  · have hc : ({({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))).card = 2 := by decide
    rw [Finset.sum_const, hc]
    norm_num

end Witness

end IdentE2

end Multiway
