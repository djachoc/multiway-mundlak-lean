import Multiway.IdentE2
import Multiway.Wald
import Multiway.Absorbed
import Multiway.QuadformE2
import Multiway.Sequence

/-!
# Feasible inference by plug-in estimation of the interaction variances

This file formalizes Theorem 9 of the paper (Feasible inference by plug-in estimation of the
interaction variances). With `θ = (s̄², (σ_e²)_{e ∈ 𝓔})'`, the moment design matrix `𝒜` and
`θ̂ = (𝒜'𝒜)^{-1}𝒜'm̂`, it proves (a) `E[m̂ | 𝒟] = 𝒜θ` and `E[θ̂ | 𝒟] = θ`; (b)
`θ̂ − θ = O_p(ϱ_n/c_max)`, `n^{-1}M̂_PI − S_n = O_p(ϱ_n) → 0`, `M̂_PI ⪰ 0` and the restricted
limit of `nV̂_PI`; and (c) the `χ²_r` limit of the plug-in Wald statistic, given the central
limit theorem of Theorem 4(b). The conditional expectation in (a) is an abstract linear
functional; Sections 10 and 11 read the variance inputs of (b) under the regular conditional law.

## Main results

* `moment_eq_design_mulVec`, `thetaHat_unbiased`, `plugin_moment_unbiased`: clause (a).
* `plugMeat_posSemidef`, `frobNorm_plugMeat_sub_plugTarget_le`, `weightGram_le_cmax_obsGram`.
* `thetaHat_sub_isBigOp`, `plugMeat_sub_target_isBigOp`, `tendstoInProb_restricted_of_meat`.
* `plugin_wald`, `plugin_wald_of_meat`: clause (c).
* `thetaHat_sub_isBigOp_cond` and the conditional form of the second claim of (b).
-/

namespace Multiway

namespace Plugin

open Finset Matrix

variable {O D L K : Type*} {Ω : Type*}

/-! ## 0. Definitional unfoldings -/

section Unfold

/-- `v ⬝ᵥ w = ∑ i, v i * w i`, by definition. -/
theorem dotProduct_eq_sum {n : Type*} [Fintype n] (v w : n → ℝ) : v ⬝ᵥ w = ∑ i, v i * w i := rfl

/-- `(M *ᵥ v) i = ∑ j, M i j * v j`, by definition. -/
theorem mulVec_eq_sum {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (v : n → ℝ) (i : m) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

end Unfold

/-! ## 1. The averaging functionals

Each row of `m̂` and the matching row of `𝒜` are the same linear functional `pairAvg` on
`ℝ^{n×n}`, applied to `E[ν̂_FEν̂_FE' | 𝒟]` and to `R`, `R Sh^off_e R` respectively. -/

section Average

variable [Fintype O]

/-- `ρ_w(Ξ) := ∑_{o,o'} w_{oo'} Ξ_{oo'}`, the weighted pair average of a matrix. -/
def pairAvg (w : Matrix O O ℝ) (Ξ : Matrix O O ℝ) : ℝ := ∑ o : O, ∑ o' : O, w o o' * Ξ o o'

theorem pairAvg_add (w A B : Matrix O O ℝ) : pairAvg w (A + B) = pairAvg w A + pairAvg w B := by
  simp only [pairAvg, Matrix.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_add_distrib

theorem pairAvg_smul (w : Matrix O O ℝ) (a : ℝ) (A : Matrix O O ℝ) :
    pairAvg w (a • A) = a * pairAvg w A := by
  simp only [pairAvg, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

theorem pairAvg_sum {γ : Type*} (w : Matrix O O ℝ) (s : Finset γ) (f : γ → Matrix O O ℝ) :
    pairAvg w (∑ i ∈ s, f i) = ∑ i ∈ s, pairAvg w (f i) := by
  classical
  simp only [pairAvg, Matrix.sum_apply, Finset.mul_sum]
  calc ∑ o : O, ∑ o' : O, ∑ i ∈ s, w o o' * f i o o'
      = ∑ o : O, ∑ i ∈ s, ∑ o' : O, w o o' * f i o o' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ o : O, ∑ o' : O, w o o' * f i o o' := Finset.sum_comm

/-- The outer product `ν̂ν̂'` in a single realization. -/
def outerMat (z : O → Ω → ℝ) (ω : Ω) : Matrix O O ℝ := Matrix.of fun o o' => z o ω * z o' ω

/-- A row of `m̂`: the weighted pair average of the residual products. -/
def momentStat (w : Matrix O O ℝ) (z : O → Ω → ℝ) : Ω → ℝ := fun ω => pairAvg w (outerMat z ω)

/-- Let `M` denote `E[ν̂_FEν̂_FE' | 𝒟]`. The expectation of a row of `m̂` is the same
weighted average applied to `M`. Only linearity of the expectation over a finite sum is used. -/
theorem expect_momentStat (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (w : Matrix O O ℝ) (z : O → Ω → ℝ)
    {M : Matrix O O ℝ} (hM : ∀ o o', E (z o * z o') = M o o') :
    E (momentStat w z) = pairAvg w M := by
  have hfun : momentStat w z = ∑ o : O, ∑ o' : O, w o o' • (z o * z o') := by
    funext ω
    simp only [momentStat, pairAvg, outerMat, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul]
  rw [hfun, map_sum, pairAvg]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [map_smul, smul_eq_mul, hM]

/-! ### The two averaging weights -/

variable [DecidableEq O]

/-- The weight of `m̂_0`, `n^{-1}I_n`, which averages over the diagonal. -/
noncomputable def wDiag : Matrix O O ℝ := (Fintype.card O : ℝ)⁻¹ • (1 : Matrix O O ℝ)

/-- The weight of `m̂_F`, `|P_F|^{-1}𝟙_{P_F}`, which averages over the class `P_F`. -/
noncomputable def wPair (P : Finset (O × O)) : Matrix O O ℝ :=
  Matrix.of fun o o' => if (o, o') ∈ P then ((P.card : ℝ))⁻¹ else 0

/-- The diagonal average of `Ξ` is `n^{-1}tr(Ξ)`, so that `𝒜_{0,s̄} = n^{-1}tr(R)` and
`𝒜_{0,e} = n^{-1}tr(R Sh^off_e R)`. -/
theorem pairAvg_wDiag (Ξ : Matrix O O ℝ) :
    pairAvg (wDiag : Matrix O O ℝ) Ξ = (Fintype.card O : ℝ)⁻¹ * Ξ.trace := by
  have h : ∀ o : O, ∑ o' : O, (wDiag : Matrix O O ℝ) o o' * Ξ o o'
      = (Fintype.card O : ℝ)⁻¹ * Ξ o o := by
    intro o
    rw [Finset.sum_eq_single o
      (fun b _ hb => by simp [wDiag, Matrix.smul_apply, Ne.symm hb])
      (fun hb => absurd (Finset.mem_univ o) hb)]
    simp [wDiag, Matrix.smul_apply]
  rw [pairAvg, Finset.sum_congr rfl (fun o _ => h o), ← Finset.mul_sum]
  rfl

/-- The average of `Ξ` over `P_F` is `|P_F|^{-1}∑_{(o,o') ∈ P_F} Ξ_{oo'}`, so that
`𝒜_{F,s̄} = |P_F|^{-1}∑_{P_F}R_{oo'}` and `𝒜_{F,e} = |P_F|^{-1}∑_{P_F}(R Sh^off_e R)_{oo'}`. -/
theorem pairAvg_wPair (P : Finset (O × O)) (Ξ : Matrix O O ℝ) :
    pairAvg (wPair P) Ξ = ((P.card : ℝ))⁻¹ * ∑ p ∈ P, Ξ p.1 p.2 := by
  classical
  have h1 : pairAvg (wPair P) Ξ = ∑ p : O × O, (wPair P) p.1 p.2 * Ξ p.1 p.2 := by
    rw [pairAvg, Fintype.sum_prod_type]
  have h2 : ∀ p : O × O, (wPair P) p.1 p.2 * Ξ p.1 p.2
      = if p ∈ P then ((P.card : ℝ))⁻¹ * Ξ p.1 p.2 else 0 := by
    intro p
    by_cases hp : p ∈ P <;> simp [wPair, hp]
  rw [h1, Finset.sum_congr rfl (fun p _ => h2 p), Fintype.sum_ite_mem, ← Finset.mul_sum]

/-- `m̂_0 = n^{-1}∑_o ν̂_{FE,o}²`. -/
theorem momentStat_wDiag (z : O → Ω → ℝ) (ω : Ω) :
    momentStat (wDiag : Matrix O O ℝ) z ω = (Fintype.card O : ℝ)⁻¹ * ∑ o : O, z o ω ^ 2 := by
  rw [momentStat, pairAvg_wDiag]
  congr 1
  exact Finset.sum_congr rfl fun o _ => (sq (z o ω)).symm

/-- `m̂_F = |P_F|^{-1}∑_{(o,o') ∈ P_F} ν̂_{FE,o}ν̂_{FE,o'}`. -/
theorem momentStat_wPair (P : Finset (O × O)) (z : O → Ω → ℝ) (ω : Ω) :
    momentStat (wPair P) z ω = ((P.card : ℝ))⁻¹ * ∑ p ∈ P, z p.1 ω * z p.2 ω := by
  rw [momentStat, pairAvg_wPair]
  rfl

end Average

/-! ## 2. Clause (a): the moment relation `E[m̂ | 𝒟] = 𝒜θ` -/

section ClauseA

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]
variable {Rw Es : Type*} [Fintype Rw] [Fintype Es]

/-- The moment design matrix `𝒜`. Its rows are indexed by `Rw` through the averaging weights
`wt`, its columns by `Option Es` (`none` is the `s̄` column and `some e` the level-`e` column).
Each entry is the row's averaging functional applied to `R` or to `R Sh^off_e R`. -/
def momentDesign (c : D → O → L) (R : Matrix O O ℝ) (wt : Rw → Matrix O O ℝ)
    (lev : Es → Finset D) : Matrix Rw (Option Es) ℝ :=
  Matrix.of fun r j =>
    Option.rec (motive := fun _ => ℝ) (pairAvg (wt r) R)
      (fun e => pairAvg (wt r) (R * shOff c (lev e) * R)) j

omit [DecidableEq D] [Fintype Rw] [Fintype Es] in
@[simp] theorem momentDesign_none (c : D → O → L) (R : Matrix O O ℝ) (wt : Rw → Matrix O O ℝ)
    (lev : Es → Finset D) (r : Rw) : momentDesign c R wt lev r none = pairAvg (wt r) R := rfl

omit [DecidableEq D] [Fintype Rw] [Fintype Es] in
@[simp] theorem momentDesign_some (c : D → O → L) (R : Matrix O O ℝ) (wt : Rw → Matrix O O ℝ)
    (lev : Es → Finset D) (r : Rw) (e : Es) :
    momentDesign c R wt lev r (some e) = pairAvg (wt r) (R * shOff c (lev e) * R) := rfl

/-- `θ = (s̄², (σ_e²)_{e ∈ 𝓔})'`, on the same column index. -/
def paramVec (lev : Es → Finset D) (sbar : ℝ) (sige : Finset D → ℝ) : Option Es → ℝ :=
  fun j => Option.rec (motive := fun _ => ℝ) sbar (fun e => sige (lev e)) j

omit [DecidableEq D] [Fintype Es] in
@[simp] theorem paramVec_none (lev : Es → Finset D) (sbar : ℝ) (sige : Finset D → ℝ) :
    paramVec lev sbar sige none = sbar := rfl

omit [DecidableEq D] [Fintype Es] in
@[simp] theorem paramVec_some (lev : Es → Finset D) (sbar : ℝ) (sige : Finset D → ℝ) (e : Es) :
    paramVec lev sbar sige (some e) = sige (lev e) := rfl

omit [Fintype Rw] in
/-- **Theorem 9(a), first claim.** `E[m̂ | 𝒟] = 𝒜θ`, one row at a time. The conditional
second moment of the residuals is `IdentE2.residual_moment_smul`, and the averaging step is the
linearity of `pairAvg`. -/
theorem moment_eq_design_mulVec
    (c : D → O → L) (dims : Finset D) (Esets : Finset (Finset D))
    (lev : Es → Finset D) (hlev : Function.Injective lev)
    (hEsets : Esets = Finset.image lev Finset.univ)
    (wt : Rw → Matrix O O ℝ) (sig1 : D → ℝ) (sige : Finset D → ℝ) (sbar : ℝ)
    {R Om : Matrix O O ℝ} (hsymm : R.IsSymm) (hidem : R * R = R)
    (hRD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0)
    (hOmega : Om = (∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
      + (sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e))
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (nuh : O → Ω → ℝ)
    (hM : ∀ o o', E (nuh o * nuh o') = (R * Om * R) o o') (r : Rw) :
    E (momentStat (wt r) nuh)
      = (momentDesign c R wt lev).mulVec (paramVec lev sbar sige) r := by
  classical
  have hinj : ∀ x ∈ (Finset.univ : Finset Es), ∀ y ∈ (Finset.univ : Finset Es),
      lev x = lev y → x = y := fun _ _ _ _ h => hlev h
  rw [expect_momentStat E (wt r) nuh hM,
    IdentE2.residual_moment_smul c dims Esets sig1 sige sbar hsymm hidem hRD hOmega,
    pairAvg_add, pairAvg_smul, pairAvg_sum]
  simp only [mulVec_eq_sum, Fintype.sum_option, momentDesign_none, momentDesign_some,
    paramVec_none, paramVec_some]
  rw [hEsets, Finset.sum_image hinj]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun x _ => by rw [pairAvg_smul]; ring

/-! ### `θ̂` and its unbiasedness

The second claim of clause (a) requires only that `𝒜'𝒜` be invertible, so it is stated for an
arbitrary matrix; `plugin_moment_unbiased` below combines the two claims. -/

variable {Cl : Type*} [Fintype Cl] [DecidableEq Cl]

/-- `θ̂ := (𝒜'𝒜)^{-1}𝒜'm̂`, the least-squares solution of the moment system. -/
noncomputable def thetaHat (A : Matrix Rw Cl ℝ) (mh : Rw → Ω → ℝ) : Cl → Ω → ℝ :=
  fun j ω => ∑ r : Rw, ((Aᵀ * A)⁻¹ * Aᵀ) j r * mh r ω

/-- Full column rank of `𝒜` (injectivity of `x ↦ 𝒜x`) gives `𝒜'𝒜 ≻ 0` and hence a
nonsingular `𝒜'𝒜`. -/
theorem isUnit_det_gram_of_injective {A : Matrix Rw Cl ℝ} (hA : Function.Injective A.mulVec) :
    IsUnit (Aᵀ * A).det := by
  have hconj : (Aᵀ : Matrix Cl Rw ℝ) = Aᴴ := by
    ext j i
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [hconj]
  exact isUnit_det_of_posDef (Matrix.PosDef.conjTranspose_mul_self A hA)

/-- **Theorem 9(a), second claim.** `E[θ̂ | 𝒟] = θ`, since `θ̂` is a linear function of `m̂`
whose coefficients are constant under the functional `E`. -/
theorem thetaHat_unbiased (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (A : Matrix Rw Cl ℝ) (hA : IsUnit (Aᵀ * A).det)
    (th : Cl → ℝ) (mh : Rw → Ω → ℝ) (hm : ∀ r, E (mh r) = (A *ᵥ th) r) (j : Cl) :
    E (thetaHat A mh j) = th j := by
  have hfun : thetaHat A mh j = ∑ r : Rw, (((Aᵀ * A)⁻¹ * Aᵀ) j r) • mh r := by
    funext ω
    simp only [thetaHat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, map_sum]
  have h1 : ∀ r : Rw, E ((((Aᵀ * A)⁻¹ * Aᵀ) j r) • mh r)
      = ((Aᵀ * A)⁻¹ * Aᵀ) j r * (A *ᵥ th) r := by
    intro r
    rw [map_smul, smul_eq_mul, hm]
  rw [Finset.sum_congr rfl (fun r _ => h1 r)]
  have h2 : ∑ r : Rw, ((Aᵀ * A)⁻¹ * Aᵀ) j r * (A *ᵥ th) r
      = ((((Aᵀ * A)⁻¹ * Aᵀ)) *ᵥ (A *ᵥ th)) j := rfl
  rw [h2, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec]

variable [DecidableEq Es]

/-- **Theorem 9(a)**, both claims together. -/
theorem plugin_moment_unbiased
    (c : D → O → L) (dims : Finset D) (Esets : Finset (Finset D))
    (lev : Es → Finset D) (hlev : Function.Injective lev)
    (hEsets : Esets = Finset.image lev Finset.univ)
    (wt : Rw → Matrix O O ℝ) (sig1 : D → ℝ) (sige : Finset D → ℝ) (sbar : ℝ)
    {R Om : Matrix O O ℝ} (hsymm : R.IsSymm) (hidem : R * R = R)
    (hRD : ∀ m ∈ dims, ∀ t ∈ cells c ({m} : Finset D), ∀ o : O, ∑ o' ∈ t, R o o' = 0)
    (hOmega : Om = (∑ m ∈ dims, sig1 m • shMat c ({m} : Finset D))
      + (sbar • (1 : Matrix O O ℝ) + ∑ e ∈ Esets, sige e • shOff c e))
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (nuh : O → Ω → ℝ)
    (hM : ∀ o o', E (nuh o * nuh o') = (R * Om * R) o o')
    (hrank : Function.Injective (momentDesign c R wt lev).mulVec) (j : Option Es) :
    (∀ r : Rw, E (momentStat (wt r) nuh)
        = (momentDesign c R wt lev).mulVec (paramVec lev sbar sige) r)
      ∧ E (thetaHat (momentDesign c R wt lev) (fun r => momentStat (wt r) nuh) j)
        = paramVec lev sbar sige j := by
  have ha := fun r => moment_eq_design_mulVec c dims Esets lev hlev hEsets wt sig1 sige sbar
    hsymm hidem hRD hOmega E nuh hM r
  exact ⟨ha, thetaHat_unbiased E _ (isUnit_det_gram_of_injective hrank) _ _ ha j⟩

end ClauseA

/-! ## 3. The Frobenius norm

The norm laws for `frobNorm` are those of `Multiway/Sqrt.lean`. -/

/-! ## 4. Clause (b): the plug-in meat

The plug-in meat is positive semidefinite in every sample, its distance from the target is bounded
by the `ℓ¹` deviation of `θ̂` from `θ` with constant `1`, and
`∑_{t ∈ 𝒯_e} w^{(e)}_tw^{(e)'}_t ⪯ c_max ∑_o x̃_ox̃_o'`. -/

section ClauseB

variable [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K]
variable {Es : Type*} [Fintype Es]

/-! ### The two Gram matrices are positive semidefinite -/

omit [DecidableEq O] [DecidableEq K] in
/-- `∑_o x̃_ox̃_o' = X̃'X̃ ⪰ 0`. -/
theorem obsGram_posSemidef (xt : O → K → ℝ) : (IdentE2.obsGram xt).PosSemidef := by
  have h : IdentE2.obsGram xt = (Matrix.of xt)ᴴ * Matrix.of xt := by
    ext a b
    simp [IdentE2.obsGram, Matrix.mul_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq D] [DecidableEq K] in
/-- `∑_{t ∈ 𝒯_e} w^{(e)}_tw^{(e)'}_t ⪰ 0`, as the Gram matrix of the cell weights. -/
theorem weightGram_posSemidef (c : D → O → L) (xt : O → K → ℝ) (e : Finset D) :
    (IdentE2.weightGram c xt e).PosSemidef := by
  classical
  have h : IdentE2.weightGram c xt e
      = (Matrix.of fun (t : {t : Finset O // t ∈ cells c e}) (a : K) =>
          cellWeight (fun o => xt o a) (t : Finset O))ᴴ
        * Matrix.of fun (t : {t : Finset O // t ∈ cells c e}) (a : K) =>
            cellWeight (fun o => xt o a) (t : Finset O) := by
    ext a b
    rw [IdentE2.weightGram, Matrix.of_apply, Matrix.mul_apply,
      ← Finset.sum_coe_sort (cells c e)
        (fun t => cellWeight (fun o => xt o a) t * cellWeight (fun o => xt o b) t)]
    exact Finset.sum_congr rfl fun t _ => by
      simp [Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K] in
/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_sum {γ : Type*} (s : Finset γ) (f : γ → Matrix K K ℝ)
    (h : ∀ i ∈ s, (f i).PosSemidef) : (∑ i ∈ s, f i).PosSemidef :=
  Finset.sum_induction f Matrix.PosSemidef (fun _ _ ha hb => ha.add hb)
    Matrix.PosSemidef.zero h

/-! ### The plug-in meat and its target -/

/-- `M̂_PI`, with `(x)_+` written `max x 0`. -/
noncomputable def plugMeat (c : D → O → L) (xt : O → K → ℝ) (lev : Es → Finset D)
    (sh2 : ℝ) (sg : Es → ℝ) : Matrix K K ℝ :=
  (max (sh2 - ∑ e : Es, max (sg e) 0) 0) • IdentE2.obsGram xt
    + ∑ e : Es, (max (sg e) 0) • IdentE2.weightGram c xt (lev e)

/-- `nS_n` in the form of `M̂_PI`, with `θ` in place of `θ̂` and without truncation. -/
noncomputable def plugTarget (c : D → O → L) (xt : O → K → ℝ) (lev : Es → Finset D)
    (sbar : ℝ) (sige : Finset D → ℝ) : Matrix K K ℝ :=
  (sbar - ∑ e : Es, sige (lev e)) • IdentE2.obsGram xt
    + ∑ e : Es, sige (lev e) • IdentE2.weightGram c xt (lev e)

omit [Fintype K] [DecidableEq K] in
/-- `plugTarget` is `nS_n`. This is `IdentE2.targetplug` reindexed from the `Finset` `𝓔` to
the index type `Es`. -/
theorem plugTarget_eq_targetplug (c : D → O → L) (xt : O → K → ℝ)
    (levels Esets : Finset (Finset D)) (lev : Es → Finset D) (hlev : Function.Injective lev)
    (hEsets : Esets = Finset.image lev Finset.univ)
    (sige : Finset D → ℝ) (sigeps sbar : ℝ) {nSn : Matrix K K ℝ}
    (hEsub : Esets ⊆ levels)
    (hdeg : ∀ e ∈ levels \ Esets, shOff c e = 0)
    (hsbar : sbar = sigeps + ∑ e ∈ levels, sige e)
    (hnSn : nSn = sigeps • IdentE2.obsGram xt
      + ∑ e ∈ levels, sige e • IdentE2.weightGram c xt e) :
    nSn = plugTarget c xt lev sbar sige := by
  classical
  have hinj : ∀ x ∈ (Finset.univ : Finset Es), ∀ y ∈ (Finset.univ : Finset Es),
      lev x = lev y → x = y := fun _ _ _ _ h => hlev h
  rw [IdentE2.targetplug c xt levels Esets sige sigeps sbar hEsub hdeg hsbar hnSn, plugTarget,
    hEsets]
  simp only [Finset.sum_image hinj]

omit [DecidableEq D] [DecidableEq K] in
/-- **Theorem 9(b)**, positive semidefiniteness: both Gram matrices are positive
semidefinite and both coefficients are nonnegative after truncation. -/
theorem plugMeat_posSemidef (c : D → O → L) (xt : O → K → ℝ) (lev : Es → Finset D)
    (sh2 : ℝ) (sg : Es → ℝ) : (plugMeat c xt lev sh2 sg).PosSemidef :=
  Matrix.PosSemidef.add ((obsGram_posSemidef xt).smul (le_max_right _ _))
    (posSemidef_sum _ _ fun e _ => (weightGram_posSemidef c xt (lev e)).smul (le_max_right _ _))

/-! ### The truncation, and the meat error -/

/-- `|(x)_+ − y| ≤ |x − y|` whenever `y ≥ 0`, so truncation does not increase the error. -/
theorem abs_posPart_sub_le {x y : ℝ} (hy : 0 ≤ y) : |max x 0 - y| ≤ |x - y| := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]
  · rw [max_eq_right hx, zero_sub, abs_neg, abs_of_nonneg hy,
      abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith

/-- The `ℓ¹` deviation `‖θ̂ − θ‖` of `θ̂` from `θ`. -/
noncomputable def devL1 (lev : Es → Finset D) (sh2 sbar : ℝ) (sg : Es → ℝ)
    (sige : Finset D → ℝ) : ℝ :=
  |sh2 - sbar| + ∑ e : Es, |sg e - sige (lev e)|

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] [Fintype K] [DecidableEq K] in
theorem devL1_nonneg (lev : Es → Finset D) (sh2 sbar : ℝ) (sg : Es → ℝ) (sige : Finset D → ℝ) :
    0 ≤ devL1 lev sh2 sbar sg sige :=
  add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

omit [DecidableEq D] [DecidableEq K] in
/-- **Theorem 9(b)**, the deterministic meat-error bound
`‖M̂_PI − nS_n‖ ≤ ‖θ̂ − θ‖[‖∑_o x̃_ox̃_o'‖ + ∑_{e ∈ 𝓔}‖∑_t w^{(e)}_tw^{(e)'}_t‖]`, with the `ℓ¹`
deviation and constant `1`. It assumes every coordinate of `θ` and `s̄² − ∑_{e ∈ 𝓔}σ_e²` are
nonnegative. -/
theorem frobNorm_plugMeat_sub_plugTarget_le (c : D → O → L) (xt : O → K → ℝ)
    (lev : Es → Finset D) (sh2 sbar : ℝ) (sg : Es → ℝ) (sige : Finset D → ℝ)
    (hnn : ∀ e : Es, 0 ≤ sige (lev e))
    (halpha : 0 ≤ sbar - ∑ e : Es, sige (lev e)) :
    frobNorm (plugMeat c xt lev sh2 sg - plugTarget c xt lev sbar sige)
      ≤ devL1 lev sh2 sbar sg sige
        * (frobNorm (IdentE2.obsGram xt)
            + ∑ e : Es, frobNorm (IdentE2.weightGram c xt (lev e))) := by
  classical
  set dev := devL1 lev sh2 sbar sg sige with hdev
  set bh : Es → ℝ := fun e => max (sg e) 0 with hbh
  set b : Es → ℝ := fun e => sige (lev e) with hb
  set ah : ℝ := max (sh2 - ∑ e : Es, bh e) 0 with hah
  set a : ℝ := sbar - ∑ e : Es, b e with hasm
  -- the difference is a linear combination of the two Gram matrices
  have hdiff : plugMeat c xt lev sh2 sg - plugTarget c xt lev sbar sige
      = (ah - a) • IdentE2.obsGram xt
        + ∑ e : Es, (bh e - b e) • IdentE2.weightGram c xt (lev e) := by
    rw [plugMeat, plugTarget]
    simp only [← hbh, ← hb, ← hah, ← hasm, sub_smul, Finset.sum_sub_distrib]
    abel
  -- each coefficient is bounded by the `ℓ¹` deviation
  have habs_b : ∀ e : Es, |bh e - b e| ≤ |sg e - sige (lev e)| := fun e =>
    abs_posPart_sub_le (hnn e)
  have hsum_le : ∑ e : Es, |bh e - b e| ≤ ∑ e : Es, |sg e - sige (lev e)| :=
    Finset.sum_le_sum fun e _ => habs_b e
  have hb_le : ∀ e : Es, |bh e - b e| ≤ dev := by
    intro e
    refine (habs_b e).trans ?_
    rw [hdev, devL1]
    have h1 : |sg e - sige (lev e)| ≤ ∑ e' : Es, |sg e' - sige (lev e')| :=
      Finset.single_le_sum (f := fun e' => |sg e' - sige (lev e')|)
        (fun e' _ => abs_nonneg _) (Finset.mem_univ e)
    have h2 : (0 : ℝ) ≤ |sh2 - sbar| := abs_nonneg _
    linarith
  have ha_le : |ah - a| ≤ dev := by
    have h1 : |ah - a| ≤ |(sh2 - ∑ e : Es, bh e) - a| := abs_posPart_sub_le (by rw [hasm]; exact halpha)
    have hrw : (sh2 - ∑ e : Es, bh e) - a = (sh2 - sbar) + (-(∑ e : Es, (bh e - b e))) := by
      rw [hasm, Finset.sum_sub_distrib]
      ring
    have h2 : |(sh2 - sbar) + (-(∑ e : Es, (bh e - b e)))|
        ≤ |sh2 - sbar| + |(-(∑ e : Es, (bh e - b e)))| := abs_add_le _ _
    have h3 : |(-(∑ e : Es, (bh e - b e)))| = |∑ e : Es, (bh e - b e)| := abs_neg _
    have h4 : |∑ e : Es, (bh e - b e)| ≤ ∑ e : Es, |bh e - b e| :=
      Finset.abs_sum_le_sum_abs _ _
    rw [hrw] at h1
    rw [hdev, devL1]
    linarith
  -- the triangle inequality, then the two bounds
  rw [hdiff]
  have hstep : frobNorm ((ah - a) • IdentE2.obsGram xt
        + ∑ e : Es, (bh e - b e) • IdentE2.weightGram c xt (lev e))
      ≤ |ah - a| * frobNorm (IdentE2.obsGram xt)
        + ∑ e : Es, |bh e - b e| * frobNorm (IdentE2.weightGram c xt (lev e)) := by
    have h1 : frobNorm (∑ e : Es, (bh e - b e) • IdentE2.weightGram c xt (lev e))
        ≤ ∑ e : Es, |bh e - b e| * frobNorm (IdentE2.weightGram c xt (lev e)) := by
      refine (frobNorm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun e _ => frobNorm_smul _ _
    refine (frobNorm_add_le _ _).trans ?_
    rw [frobNorm_smul]
    linarith
  refine hstep.trans ?_
  have hG0 : (0 : ℝ) ≤ frobNorm (IdentE2.obsGram xt) := Wald.frobNorm_nonneg _
  have hfin : |ah - a| * frobNorm (IdentE2.obsGram xt)
        + ∑ e : Es, |bh e - b e| * frobNorm (IdentE2.weightGram c xt (lev e))
      ≤ dev * frobNorm (IdentE2.obsGram xt)
        + ∑ e : Es, dev * frobNorm (IdentE2.weightGram c xt (lev e)) := by
    refine add_le_add (mul_le_mul_of_nonneg_right ha_le hG0) ?_
    exact Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_right (hb_le e) (Wald.frobNorm_nonneg _)
  refine hfin.trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  ring

/-! ### `∑_{t ∈ 𝒯_e} w^{(e)}_tw^{(e)'}_t ⪯ c_max ∑_o x̃_ox̃_o'` -/

omit [DecidableEq O] [DecidableEq K] in
/-- The quadratic form of `∑_o x̃_ox̃_o'` is `∑_o (x̃_o'v)²`. -/
theorem dot_obsGram (xt : O → K → ℝ) (v : K → ℝ) :
    v ⬝ᵥ (IdentE2.obsGram xt *ᵥ v) = ∑ o : O, (∑ a : K, xt o a * v a) ^ 2 := by
  have hL : ∀ a : K, v a * ((IdentE2.obsGram xt *ᵥ v) a)
      = ∑ b : K, ∑ o : O, (xt o a * v a) * (xt o b * v b) := by
    intro a
    rw [mulVec_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [IdentE2.obsGram, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun o _ => by ring
  have hR : ∀ o : O, (∑ a : K, xt o a * v a) ^ 2
      = ∑ a : K, ∑ b : K, (xt o a * v a) * (xt o b * v b) := by
    intro o
    rw [sq, Finset.sum_mul_sum]
  rw [dotProduct_eq_sum, Finset.sum_congr rfl (fun a _ => hL a),
    Finset.sum_congr rfl (fun o _ => hR o)]
  calc ∑ a : K, ∑ b : K, ∑ o : O, (xt o a * v a) * (xt o b * v b)
      = ∑ a : K, ∑ o : O, ∑ b : K, (xt o a * v a) * (xt o b * v b) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ o : O, ∑ a : K, ∑ b : K, (xt o a * v a) * (xt o b * v b) := Finset.sum_comm

omit [DecidableEq D] [DecidableEq K] in
/-- The quadratic form of `∑_{t ∈ 𝒯_e} w^{(e)}_tw^{(e)'}_t` is `∑_{t}(∑_{o ∈ t} x̃_o'v)²`. -/
theorem dot_weightGram (c : D → O → L) (xt : O → K → ℝ) (e : Finset D) (v : K → ℝ) :
    v ⬝ᵥ (IdentE2.weightGram c xt e *ᵥ v)
      = ∑ t ∈ cells c e, (∑ o ∈ t, ∑ a : K, xt o a * v a) ^ 2 := by
  have hcw : ∀ t : Finset O, (∑ o ∈ t, ∑ a : K, xt o a * v a)
      = ∑ a : K, cellWeight (fun o => xt o a) t * v a := by
    intro t
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => by rw [cellWeight, Finset.sum_mul]
  have hL : ∀ a : K, v a * ((IdentE2.weightGram c xt e *ᵥ v) a)
      = ∑ b : K, ∑ t ∈ cells c e,
          (cellWeight (fun o => xt o a) t * v a) * (cellWeight (fun o => xt o b) t * v b) := by
    intro a
    rw [mulVec_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [IdentE2.weightGram, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hR : ∀ t : Finset O, (∑ o ∈ t, ∑ a : K, xt o a * v a) ^ 2
      = ∑ a : K, ∑ b : K,
        (cellWeight (fun o => xt o a) t * v a) * (cellWeight (fun o => xt o b) t * v b) := by
    intro t
    rw [hcw t, sq, Finset.sum_mul_sum]
  rw [dotProduct_eq_sum, Finset.sum_congr rfl (fun a _ => hL a),
    Finset.sum_congr rfl (fun t (_ : t ∈ cells c e) => hR t)]
  calc ∑ a : K, ∑ b : K, ∑ t ∈ cells c e,
        (cellWeight (fun o => xt o a) t * v a) * (cellWeight (fun o => xt o b) t * v b)
      = ∑ a : K, ∑ t ∈ cells c e, ∑ b : K,
          (cellWeight (fun o => xt o a) t * v a) * (cellWeight (fun o => xt o b) t * v b) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ t ∈ cells c e, ∑ a : K, ∑ b : K,
          (cellWeight (fun o => xt o a) t * v a) * (cellWeight (fun o => xt o b) t * v b) :=
        Finset.sum_comm

omit [DecidableEq K] in
theorem dotProduct_mulVec_sub (A B : Matrix K K ℝ) (v : K → ℝ) :
    v ⬝ᵥ ((A - B) *ᵥ v) = v ⬝ᵥ (A *ᵥ v) - v ⬝ᵥ (B *ᵥ v) := by
  rw [Matrix.sub_mulVec, dotProduct_sub]

omit [DecidableEq K] in
theorem dotProduct_mulVec_smul (r : ℝ) (A : Matrix K K ℝ) (v : K → ℝ) :
    v ⬝ᵥ ((r • A) *ᵥ v) = r * (v ⬝ᵥ (A *ᵥ v)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

omit [DecidableEq K] in
/-- `∑_{t ∈ 𝒯_e} w^{(e)}_tw^{(e)'}_t ⪯ c_max X̃'X̃`, where `cmax` bounds the size of every
level-`e` cell. The proof applies Cauchy–Schwarz within each cell and
`Multiway.sum_over_cells`. -/
theorem weightGram_le_cmax_obsGram (c : D → O → L) (xt : O → K → ℝ) (e : Finset D)
    {cmax : ℕ} (hc : ∀ t ∈ cells c e, t.card ≤ cmax) :
    (((cmax : ℝ)) • IdentE2.obsGram xt - IdentE2.weightGram c xt e).PosSemidef := by
  classical
  have hsymm : ∀ a b : K,
      (((cmax : ℝ)) • IdentE2.obsGram xt - IdentE2.weightGram c xt e) b a
        = (((cmax : ℝ)) • IdentE2.obsGram xt - IdentE2.weightGram c xt e) a b := by
    intro a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, IdentE2.obsGram,
      IdentE2.weightGram, Matrix.of_apply]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.ext fun a b => by
      rw [Matrix.conjTranspose_apply, star_trivial]
      exact hsymm a b) ?_
  intro v
  have hs : star v = v := by
    funext i
    exact star_trivial _
  rw [hs, dotProduct_mulVec_sub, dotProduct_mulVec_smul, dot_obsGram, dot_weightGram,
    sub_nonneg]
  calc ∑ t ∈ cells c e, (∑ o ∈ t, ∑ a : K, xt o a * v a) ^ 2
      ≤ ∑ t ∈ cells c e, (cmax : ℝ) * ∑ o ∈ t, (∑ a : K, xt o a * v a) ^ 2 := by
        refine Finset.sum_le_sum fun t ht => ?_
        refine (sq_sum_le_card_mul_sum_sq).trans ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc t ht)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = (cmax : ℝ) * ∑ t ∈ cells c e, ∑ o ∈ t, (∑ a : K, xt o a * v a) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (cmax : ℝ) * ∑ o : O, (∑ a : K, xt o a * v a) ^ 2 := by
        rw [sum_over_cells]

end ClauseB

/-! ## 5. Clause (b): two conjugation bounds

For symmetric `B`, `tr((RBR)Ω'(RBR)Ω') = tr(BΩ*BΩ*) ≤ ‖Ω*‖²‖B‖_F²` with `Ω* = RΩ'R`, and
`‖RBR‖_F ≤ ‖B‖_F` (`Multiway.Absorbed.rectFrobSq_conj_le`). The identity uses only cyclicity of
the trace. The bound `‖Ω*‖ ≤ λ` is stated in its Loewner form `Ω*Ω* ⪯ λ²I`. A related bound in
Frobenius-operator form is `Multiway.UnionMeat.trace_conj_le`. -/

section ConjBound

open scoped MatrixOrder

variable [Fintype O] [DecidableEq O]

omit [DecidableEq O] in
/-- `Multiway.Sqrt.frobSq` and `Multiway.Concentration.rectFrobSq` agree on square
matrices. -/
theorem frobSq_eq_rectFrobSq (M : Matrix O O ℝ) : frobSq M = rectFrobSq M := rfl

/-- `‖RBR‖_F ≤ ‖B‖_F` for symmetric idempotent `R`, from
`Multiway.Absorbed.rectFrobSq_conj_le`. -/
theorem frobSq_conj_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    (B : Matrix O O ℝ) : frobSq (R * B * R) ≤ frobSq B :=
  Absorbed.rectFrobSq_conj_le hsym hidem B

omit [DecidableEq O] in
/-- `tr((RBR)Ω'(RBR)Ω') = tr(BΩ*BΩ*)` with `Ω* = RΩ'R`, by cyclicity of the trace. -/
theorem trace_conj_quad_eq (R B Om : Matrix O O ℝ) :
    ((R * B * R) * Om * (R * B * R) * Om).trace
      = (B * (R * Om * R) * B * (R * Om * R)).trace := by
  calc ((R * B * R) * Om * (R * B * R) * Om).trace
      = (R * (B * R * Om * R * B * R * Om)).trace := by
        congr 1
        noncomm_ring
    _ = ((B * R * Om * R * B * R * Om) * R).trace := Matrix.trace_mul_comm _ _
    _ = (B * (R * Om * R) * B * (R * Om * R)).trace := by
        congr 1
        noncomm_ring

/-- `tr(BΩ*BΩ*) ≤ λ²‖B‖_F²` for symmetric `B` and `Ω*` with `Ω*Ω* ⪯ λ²I`. The proof uses
`Sqrt.trace_mul_self_le_frobSq`, `Sqrt.frobSq_eq_trace` and `Sqrt.mul_mul_transpose_le`. -/
theorem trace_quad_le_of_sq_le {B Om : Matrix O O ℝ} (hB : Bᵀ = B) (hOm : Omᵀ = Om)
    {lam : ℝ} (hlam : Om * Om ≤ lam ^ 2 • (1 : Matrix O O ℝ)) :
    (B * Om * B * Om).trace ≤ lam ^ 2 * frobSq B := by
  have h1 : (B * Om * B * Om).trace = ((Om * B) * (Om * B)).trace := by
    calc (B * Om * B * Om).trace = (B * (Om * B * Om)).trace := by congr 1; noncomm_ring
      _ = ((Om * B * Om) * B).trace := Matrix.trace_mul_comm _ _
      _ = ((Om * B) * (Om * B)).trace := by congr 1; noncomm_ring
  have h2 : ((Om * B) * (Om * B)).trace ≤ frobSq (Om * B) := trace_mul_self_le_frobSq _
  have h3 : frobSq (Om * B) = (B * (Om * Om) * B).trace := by
    rw [frobSq_eq_trace, Matrix.transpose_mul, hB, hOm]
    congr 1
    noncomm_ring
  have h4 : B * (Om * Om) * B ≤ B * (lam ^ 2 • (1 : Matrix O O ℝ)) * B := by
    have h := mul_mul_transpose_le hlam B
    rwa [hB] at h
  have h5 : B * (lam ^ 2 • (1 : Matrix O O ℝ)) * B = lam ^ 2 • (B * B) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have h9 := trace_le_of_le h4
  rw [h5, Matrix.trace_smul, smul_eq_mul] at h9
  have h10 : lam ^ 2 * (B * B).trace ≤ lam ^ 2 * frobSq B :=
    mul_le_mul_of_nonneg_left (trace_mul_self_le_frobSq _) (sq_nonneg _)
  rw [h1]
  exact h2.trans (h3.trans_le (h9.trans h10))

/-- The variance bound of Lemma SM.C.6 at `W = RBR`, combined with the two conjugation bounds
into a bound in terms of `‖B‖_F²`. The hypothesis `hquad` has the form of the conclusion of
`QuadformE2.var_quadForm_le_sites`. -/
theorem varQuad_conj_le {Ω' : Type*} (E : (Ω' → ℝ) →ₗ[ℝ] ℝ) {R B Om : Matrix O O ℝ}
    (hRsym : Rᵀ = R) (hRidem : R * R = R) (hB : Bᵀ = B) (hOm : Omᵀ = Om)
    {lam Cst : ℝ} (hlam : (R * Om * R) * (R * Om * R) ≤ lam ^ 2 • (1 : Matrix O O ℝ))
    (hCst : 0 ≤ Cst) (z : O → Ω' → ℝ)
    (hquad : QuadformE2.varQuad E (R * B * R) z
      ≤ 2 * ((R * B * R) * Om * (R * B * R) * Om).trace + Cst * frobSq (R * B * R)) :
    QuadformE2.varQuad E (R * B * R) z ≤ (2 * lam ^ 2 + Cst) * frobSq B := by
  have hOmst : (R * Om * R)ᵀ = R * Om * R := by
    simp [Matrix.transpose_mul, hRsym, hOm, Matrix.mul_assoc]
  have hQ := trace_quad_le_of_sq_le hB hOmst hlam
  have hF : Cst * frobSq (R * B * R) ≤ Cst * frobSq B :=
    mul_le_mul_of_nonneg_left (frobSq_conj_le hRsym hRidem B) hCst
  refine hquad.trans ?_
  rw [trace_conj_quad_eq R B Om, show (2 * lam ^ 2 + Cst) * frobSq B
    = 2 * (lam ^ 2 * frobSq B) + Cst * frobSq B by ring]
  linarith

/-- Lemma SM.C.6 (Variance of a quadratic form under interaction dependence) composed with the
two conjugation bounds: `Var(ζ'RBRζ | 𝒟) ≤ (2λ² + C(M)G_max c_max)‖B‖_F²`, where `λ` bounds
`‖Ω*‖`. -/
theorem varQuad_conj_le_sites {Ω' : Type*} {Γ Dm Lm : Type*} [DecidableEq Dm] [DecidableEq Lm]
    [Fintype Dm] (E : (Ω' → ℝ) →ₗ[ℝ] ℝ) {R B Om : Matrix O O ℝ}
    (hRsym : Rᵀ = R) (hRidem : R * R = R) (hB : Bᵀ = B) (hOm : Om.IsSymm)
    {lam : ℝ} (hlam : (R * Om * R) * (R * Om * R) ≤ lam ^ 2 • (1 : Matrix O O ℝ))
    (z : O → Ω' → ℝ) (hOmdef : ∀ o o', Om o o' = E (z o * z o'))
    (s : Finset Γ) (cc : Γ → O → O → O → O → ℝ)
    (hdecomp : ∀ o₁ o₂ o₃ o₄ : O,
      QuadformE2.cum4 E (z o₁) (z o₂) (z o₃) (z o₄) = ∑ g ∈ s, cc g o₁ o₂ o₃ o₄)
    (idx : Dm → O → Lm) (e : Γ → Fin 4 → Finset Dm) {Gmax cmax : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ g ∈ s, ∀ i, 2 ≤ (e g i).card)
    (hG : ∀ (k : Dm) (o : O), (cellOf idx ({k} : Finset Dm) o).card ≤ Gmax)
    (hc : ∀ (A : Finset Dm) (o : O), 2 ≤ A.card → (cellOf idx A o).card ≤ cmax)
    (hsupp : ∀ g ∈ s, ∀ o₁ o₂ o₃ o₄ : O,
      ¬ (QuadformE2.Admissible idx (e g) (QuadformE2.quad o₁ o₂ o₃ o₄)
          ∧ QuadformE2.Linked idx (e g) (QuadformE2.quad o₁ o₂ o₃ o₄)) →
        cc g o₁ o₂ o₃ o₄ = 0)
    (hbdd : ∀ g ∈ s, ∀ o₁ o₂ o₃ o₄ : O, |cc g o₁ o₂ o₃ o₄| ≤ K) :
    QuadformE2.varQuad E (R * B * R) z
      ≤ (2 * lam ^ 2 + (s.card : ℝ) * K * ((4 * Fintype.card Dm * Gmax * cmax : ℕ) : ℝ))
          * frobSq B := by
  have hW : (R * B * R).IsSymm := by
    show (R * B * R)ᵀ = R * B * R
    simp [Matrix.transpose_mul, hRsym, hB, Matrix.mul_assoc]
  have hCst : (0 : ℝ) ≤ (s.card : ℝ) * K * ((4 * Fintype.card Dm * Gmax * cmax : ℕ) : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) (Nat.cast_nonneg _)
  exact varQuad_conj_le E hRsym hRidem hB hOm.eq hlam hCst z
    (QuadformE2.var_quadForm_le_sites E hW hOm z hOmdef s cc hdecomp idx e hK he hG hc
      hsupp hbdd)

end ConjBound

/-! ## 6. Clause (b): closure laws for `O_p`

`IsBigOp` is `O_p(a_n)`, written as `O_p(1)` of the ratio. The rate `a_n` is a deterministic
sequence. -/

section OpToolkit

open Filter MeasureTheory
open scoped Topology ENNReal

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- `Z_n = O_p(a_n)`, as `Sequence.BddInProb` of the ratio. -/
def IsBigOp (P : Measure Ω) (Z : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  Sequence.BddInProb P (fun n ω => Z n ω / a n)

/-- A constant sequence is `O_p(1)`. -/
theorem bddInProb_const (c : ℝ) : Sequence.BddInProb P (fun (_ : ℕ) (_ : Ω) => c) := by
  intro δ _
  refine ⟨|c| + 1, by positivity, fun _ => ?_⟩
  have hsub : {ω : Ω | |c| + 1 ≤ |c|} ⊆ (∅ : Set Ω) := by
    intro ω hω
    have hω' : |c| + 1 ≤ |c| := hω
    exact absurd hω' (not_le.mpr (by linarith))
  rw [measure_mono_null hsub (by simp)]
  exact zero_le

/-- If `|Z_n| ≤ |W_n|` a.e. and `W_n = O_p(1)`, then `Z_n = O_p(1)`. -/
theorem bddInProb_of_abs_le {Z W : ℕ → Ω → ℝ} (hle : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ |W n ω|)
    (hW : Sequence.BddInProb P W) : Sequence.BddInProb P Z := by
  intro δ hδ
  obtain ⟨C, hC, hb⟩ := hW δ hδ
  refine ⟨C, hC, fun n => le_trans (measure_mono_ae ?_) (hb n)⟩
  filter_upwards [hle n] with ω hω hmem
  exact (hmem : C ≤ |Z n ω|).trans hω

/-- The product of two `O_p(1)` sequences is `O_p(1)`, by a union bound at `δ/2` each. -/
theorem bddInProb_mul {W₁ W₂ : ℕ → Ω → ℝ} (h₁ : Sequence.BddInProb P W₁)
    (h₂ : Sequence.BddInProb P W₂) :
    Sequence.BddInProb P (fun n ω => W₁ n ω * W₂ n ω) := by
  intro δ hδ
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁ (δ / 2) (ENNReal.half_pos hδ.ne')
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂ (δ / 2) (ENNReal.half_pos hδ.ne')
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, fun n => ?_⟩
  have hsub : {ω | C₁ * C₂ ≤ |W₁ n ω * W₂ n ω|}
      ⊆ {ω | C₁ ≤ |W₁ n ω|} ∪ {ω | C₂ ≤ |W₂ n ω|} := by
    intro ω hω
    by_contra hcon
    have h1 : |W₁ n ω| < C₁ := not_le.mp fun h => hcon (Or.inl h)
    have h2 : |W₂ n ω| < C₂ := not_le.mp fun h => hcon (Or.inr h)
    have hlt : |W₁ n ω * W₂ n ω| < C₁ * C₂ := by
      rw [abs_mul]
      exact mul_lt_mul'' h1 h2 (abs_nonneg _) (abs_nonneg _)
    exact absurd (hω : C₁ * C₂ ≤ |W₁ n ω * W₂ n ω|) (not_le.mpr hlt)
  calc P {ω | C₁ * C₂ ≤ |W₁ n ω * W₂ n ω|}
      ≤ P ({ω | C₁ ≤ |W₁ n ω|} ∪ {ω | C₂ ≤ |W₂ n ω|}) := measure_mono hsub
    _ ≤ P {ω | C₁ ≤ |W₁ n ω|} + P {ω | C₂ ≤ |W₂ n ω|} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (hb₁ n) (hb₂ n)
    _ = δ := ENNReal.add_halves δ

/-- A constant multiple of an `O_p(1)` sequence is `O_p(1)`. -/
theorem bddInProb_const_mul {W : ℕ → Ω → ℝ} (c : ℝ) (h : Sequence.BddInProb P W) :
    Sequence.BddInProb P (fun n ω => c * W n ω) :=
  bddInProb_mul (bddInProb_const c) h

/-- `W² = O_p(1)` gives `W = O_p(1)`. -/
theorem bddInProb_of_sq {W : ℕ → Ω → ℝ}
    (h : Sequence.BddInProb P (fun n ω => W n ω ^ 2)) : Sequence.BddInProb P W := by
  intro δ hδ
  obtain ⟨C, hC, hb⟩ := h δ hδ
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun n => le_trans (measure_mono ?_) (hb n)⟩
  intro ω hω
  have hω' : Real.sqrt C ≤ |W n ω| := hω
  show C ≤ |W n ω ^ 2|
  have hsq : C ≤ |W n ω| ^ 2 := by
    nlinarith [Real.sq_sqrt hC.le, Real.sqrt_nonneg C, abs_nonneg (W n ω)]
  rwa [abs_pow]

end OpToolkit

/-! ## 7. Clause (b), first claim: `θ̂ − θ = O_p(ϱ_n/c_max)`

The claim is proved over a sequence of designs whose row and column index types vary with `n`.
`b n` is `ϱ_n/c_max`, the square root of the common bound on the two variance displays. The
hypotheses `hNrow`, `hNcol` (`|𝓕| + 1 ≤ 2^M`, `|𝓔| + 1 ≤ 2^M`) express that `M` is fixed, and
`hLam` bounds `(𝒜'𝒜)^{-1}𝒜'` entrywise. -/

section ClauseBOp

open Filter MeasureTheory
open scoped Topology ENNReal

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- **Theorem 9(b), first claim.** `θ̂ − θ = O_p(ϱ_n/c_max)` in the `ℓ¹` norm. `hvar`
bounds the second moment of each moment's deviation from its mean, divided by `ϱ_n/c_max`,
uniformly in `n` and in the row. See `thetaHat_sub_isBigOp_cond` for the conditional form. -/
theorem thetaHat_sub_isBigOp
    {Rw Cl : ℕ → Type*} [∀ n, Fintype (Rw n)] [∀ n, Fintype (Cl n)] [∀ n, DecidableEq (Cl n)]
    (A : ∀ n, Matrix (Rw n) (Cl n) ℝ) (hA : ∀ n, IsUnit ((A n)ᵀ * A n).det)
    (th : ∀ n, Cl n → ℝ) (mh : ∀ n, Rw n → Ω → ℝ)
    {b : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    (hmeas : ∀ n r, AEMeasurable (mh n r) P)
    {Msq : ℝ≥0∞} (hMsq : Msq ≠ ⊤)
    (hvar : ∀ n r, ∫⁻ ω, ‖((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ ∂P ≤ Msq)
    {Nrow Ncol : ℕ} (hNrow : ∀ n, Fintype.card (Rw n) ≤ Nrow)
    (hNcol : ∀ n, Fintype.card (Cl n) ≤ Ncol)
    {Lam : ℝ} (hLam0 : 0 ≤ Lam)
    (hLam : ∀ (n : ℕ) (j : Cl n) (r : Rw n),
      |(((A n)ᵀ * A n)⁻¹ * (A n)ᵀ) j r| ≤ Lam) :
    IsBigOp P (fun n ω => ∑ j : Cl n, |thetaHat (A n) (mh n) j ω - th n j|) b := by
  classical
  -- (i) `θ̂ − θ` is the same linear map applied to `m̂ − 𝒜θ`
  have hkey : ∀ (n : ℕ) (j : Cl n) (ω : Ω),
      thetaHat (A n) (mh n) j ω - th n j
        = ∑ r : Rw n, (((A n)ᵀ * A n)⁻¹ * (A n)ᵀ) j r * (mh n r ω - (A n *ᵥ th n) r) := by
    intro n j ω
    have hid : ∑ r : Rw n, (((A n)ᵀ * A n)⁻¹ * (A n)ᵀ) j r * (A n *ᵥ th n) r = th n j := by
      have h2 : ∑ r : Rw n, (((A n)ᵀ * A n)⁻¹ * (A n)ᵀ) j r * (A n *ᵥ th n) r
          = ((((A n)ᵀ * A n)⁻¹ * (A n)ᵀ) *ᵥ (A n *ᵥ th n)) j := rfl
      rw [h2, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hA n),
        Matrix.one_mulVec]
    simp only [thetaHat]
    rw [← hid, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  -- (ii) the `ℓ¹` deviation of `θ̂` is bounded by that of `m̂`, at the constant `|Cl| · Λ`.
  have hbound : ∀ (n : ℕ) (ω : Ω),
      ∑ j : Cl n, |thetaHat (A n) (mh n) j ω - th n j|
        ≤ ((Ncol : ℝ) * Lam) * ∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r| := by
    intro n ω
    have hsnn : (0 : ℝ) ≤ ∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hrow : ∀ j : Cl n, |thetaHat (A n) (mh n) j ω - th n j|
        ≤ Lam * ∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r| := by
      intro j
      rw [hkey n j ω]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hLam n j r) (abs_nonneg _)
    calc ∑ j : Cl n, |thetaHat (A n) (mh n) j ω - th n j|
        ≤ ∑ _j : Cl n, Lam * ∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r| :=
          Finset.sum_le_sum fun j _ => hrow j
      _ = (Fintype.card (Cl n) : ℝ) * (Lam * ∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r|) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Ncol : ℝ) * (Lam * ∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r|) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hNcol n) (mul_nonneg hLam0 hsnn)
      _ = ((Ncol : ℝ) * Lam) * ∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r| := by ring
  -- (iii) Chebyshev: the scaled `ℓ¹` deviation of `m̂` is `O_p(1)`.
  have hd0 : ∀ (n : ℕ) (r : Rw n),
      AEMeasurable (fun ω => (mh n r ω - (A n *ᵥ th n) r) / b n) P :=
    fun n r => ((hmeas n r).sub aemeasurable_const).div_const _
  have hdm : ∀ (n : ℕ) (r : Rw n),
      AEMeasurable (fun ω => |(mh n r ω - (A n *ᵥ th n) r) / b n|) P := by
    intro n r
    simpa [Real.norm_eq_abs, abs_div] using (hd0 n r).norm
  have hde : ∀ (n : ℕ) (r : Rw n),
      AEMeasurable (fun ω => ‖((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ) P := by
    intro n r
    have h2 : AEMeasurable (fun ω => ((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2) P := by
      simpa [pow_two, Pi.mul_def] using (hd0 n r).mul (hd0 n r)
    exact h2.enorm
  have hTm : ∀ n : ℕ,
      AEMeasurable (fun ω => ∑ r : Rw n, |(mh n r ω - (A n *ᵥ th n) r) / b n|) P :=
    fun n => Finset.aemeasurable_fun_sum _ fun r _ => hdm n r
  have hTm2 : ∀ n : ℕ,
      AEMeasurable (fun ω => (∑ r : Rw n, |(mh n r ω - (A n *ᵥ th n) r) / b n|) ^ 2) P := by
    intro n
    simpa [pow_two, Pi.mul_def] using (hTm n).mul (hTm n)
  have hT : Sequence.BddInProb P
      (fun n ω => ∑ r : Rw n, |(mh n r ω - (A n *ᵥ th n) r) / b n|) := by
    refine bddInProb_of_sq (Sequence.bddInProb_of_lintegral_le
      hTm2 (M := (Nrow : ℝ≥0∞) * ((Nrow : ℝ≥0∞) * Msq))
      (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) hMsq)) ?_)
    intro n
    have hpt : ∀ ω : Ω,
        ‖(∑ r : Rw n, |(mh n r ω - (A n *ᵥ th n) r) / b n|) ^ 2‖ₑ
          ≤ (Nrow : ℝ≥0∞) * ∑ r : Rw n, ‖((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ := by
      intro ω
      set d : Rw n → ℝ := fun r => (mh n r ω - (A n *ᵥ th n) r) / b n with hddef
      have h1 : (∑ r : Rw n, |d r|) ^ 2 ≤ (Nrow : ℝ) * ∑ r : Rw n, d r ^ 2 := by
        have hcs : (∑ r : Rw n, |d r|) ^ 2
            ≤ (((Finset.univ : Finset (Rw n)).card : ℕ) : ℝ) * ∑ r : Rw n, |d r| ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        have hcard : (((Finset.univ : Finset (Rw n)).card : ℕ) : ℝ) ≤ (Nrow : ℝ) := by
          rw [Finset.card_univ]
          exact_mod_cast hNrow n
        rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) => sq_abs (d r))] at hcs
        exact hcs.trans (mul_le_mul_of_nonneg_right hcard
          (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      have hL : ‖(∑ r : Rw n, |d r|) ^ 2‖ₑ = ENNReal.ofReal ((∑ r : Rw n, |d r|) ^ 2) := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
      have hR : (Nrow : ℝ≥0∞) * ∑ r : Rw n, ‖d r ^ 2‖ₑ
          = ENNReal.ofReal ((Nrow : ℝ) * ∑ r : Rw n, d r ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun r _ => sq_nonneg (d r))]
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
      rw [hL, hR]
      exact ENNReal.ofReal_le_ofReal h1
    have hinner : ∑ r : Rw n,
        ∫⁻ ω, ‖((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ ∂P ≤ (Nrow : ℝ≥0∞) * Msq := by
      calc ∑ r : Rw n, ∫⁻ ω, ‖((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ ∂P
          ≤ ∑ _r : Rw n, Msq := Finset.sum_le_sum fun r _ => hvar n r
        _ = ((Fintype.card (Rw n) : ℕ) : ℝ≥0∞) * Msq := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ (Nrow : ℝ≥0∞) * Msq :=
            mul_le_mul' (by exact_mod_cast hNrow n) le_rfl
    calc ∫⁻ ω, ‖(∑ r : Rw n, |(mh n r ω - (A n *ᵥ th n) r) / b n|) ^ 2‖ₑ ∂P
        ≤ ∫⁻ ω, (Nrow : ℝ≥0∞) * ∑ r : Rw n,
            ‖((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ ∂P := lintegral_mono hpt
      _ = (Nrow : ℝ≥0∞) * ∫⁻ ω, ∑ r : Rw n,
            ‖((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ ∂P :=
          lintegral_const_mul' _ _ (by simp)
      _ = (Nrow : ℝ≥0∞) * ∑ r : Rw n,
            ∫⁻ ω, ‖((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ ∂P := by
          rw [lintegral_finsetSum' _ fun r _ => hde n r]
      _ ≤ (Nrow : ℝ≥0∞) * ((Nrow : ℝ≥0∞) * Msq) := mul_le_mul' le_rfl hinner
  -- (iv) domination transfers `O_p(1)` from `m̂` to `θ̂`.
  have hsum : ∀ (n : ℕ) (ω : Ω), ∑ r : Rw n, |(mh n r ω - (A n *ᵥ th n) r) / b n|
      = (∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r|) / b n := by
    intro n ω
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun r _ => by rw [abs_div, abs_of_pos (hb n)]
  refine bddInProb_of_abs_le (W := fun n ω =>
      ((Ncol : ℝ) * Lam) * ∑ r : Rw n, |(mh n r ω - (A n *ᵥ th n) r) / b n|) ?_
    (bddInProb_const_mul _ hT)
  intro n
  filter_upwards with ω
  have hSnn : (0 : ℝ) ≤ ∑ j : Cl n, |thetaHat (A n) (mh n) j ω - th n j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hTnn : (0 : ℝ) ≤ ∑ r : Rw n, |mh n r ω - (A n *ᵥ th n) r| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcnn : (0 : ℝ) ≤ (Ncol : ℝ) * Lam := mul_nonneg (Nat.cast_nonneg _) hLam0
  have hbpos := hb n
  rw [hsum n ω, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
    ← mul_div_assoc]
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hbound n ω) (inv_nonneg.mpr hbpos.le)

/-! ### Clause (b), second claim: `n^{-1}M̂_PI − S_n = O_p(ϱ_n) →^p 0`

The claim follows from the deterministic bound of Section 4 and the first claim, over a sequence
of designs whose observation, regressor, dimension, label and level types all vary with `n`. -/

/-- If `0 ≤ Z_n ≤ k_n W_n` with `W_n = O_p(1)` and `k_n → 0`, then `Z_n = O_p(k_n)` and
`Z_n` converges to zero in probability. -/
theorem isBigOp_and_tendsto_of_le {Z W : ℕ → Ω → ℝ} {k : ℕ → ℝ}
    (hk : ∀ n, 0 < k n) (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hW0 : ∀ n ω, 0 ≤ W n ω)
    (hle : ∀ n ω, Z n ω ≤ k n * W n ω)
    (hWb : Sequence.BddInProb P W) (hk0 : Tendsto k atTop (𝓝 0)) :
    IsBigOp P Z k ∧ TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  refine ⟨?_, Sequence.tendstoInProb_zero_of_bddInProb_mul (fun n => (hk n).le)
    (fun n => by
      filter_upwards with ω
      rw [abs_of_nonneg (hZ0 n ω), abs_of_nonneg (hW0 n ω)]
      exact hle n ω) hWb hk0⟩
  refine bddInProb_of_abs_le (W := W) (fun n => ?_) hWb
  filter_upwards with ω
  rw [abs_of_nonneg (div_nonneg (hZ0 n ω) (hk n).le), abs_of_nonneg (hW0 n ω), div_eq_mul_inv]
  have hkne : k n ≠ 0 := (hk n).ne'
  have h3 : k n * W n ω * (k n)⁻¹ = W n ω := by
    field_simp
  rw [← h3]
  exact mul_le_mul_of_nonneg_right (hle n ω) (inv_nonneg.mpr (hk n).le)

/-- **Theorem 9(b), second claim.** `n^{-1}M̂_PI − S_n = O_p(ϱ_n) →^p 0`. `hSn` identifies
`S_n` with `n^{-1}` times the target, `hdev` is the first claim in the `ℓ¹` norm, and `hbr`
states that the bracket is `O_p(c_max)` after normalization by `n`. -/
theorem plugMeat_sub_target_isBigOp
    {Oq Dq Lq Kq Esq : ℕ → Type*}
    [∀ n, Fintype (Oq n)] [∀ n, DecidableEq (Oq n)] [∀ n, DecidableEq (Dq n)]
    [∀ n, DecidableEq (Lq n)] [∀ n, Fintype (Kq n)] [∀ n, DecidableEq (Kq n)]
    [∀ n, Fintype (Esq n)]
    (c : ∀ n, Dq n → Oq n → Lq n) (xt : ∀ n, Ω → Oq n → Kq n → ℝ)
    (lev : ∀ n, Esq n → Finset (Dq n))
    (sh2 : ℕ → Ω → ℝ) (sg : ∀ n, Esq n → Ω → ℝ)
    (sbar : ℕ → ℝ) (sige : ∀ n, Finset (Dq n) → ℝ)
    (Sn : ∀ n, Ω → Matrix (Kq n) (Kq n) ℝ)
    (hSn : ∀ n ω, Sn n ω
      = ((Fintype.card (Oq n) : ℝ))⁻¹ • plugTarget (c n) (xt n ω) (lev n) (sbar n) (sige n))
    (hnn : ∀ (n : ℕ) (e : Esq n), 0 ≤ sige n (lev n e))
    (halpha : ∀ n, 0 ≤ sbar n - ∑ e : Esq n, sige n (lev n e))
    {rho cmax : ℕ → ℝ} (hrho0 : ∀ n, 0 < rho n) (hcmax0 : ∀ n, 0 < cmax n)
    (hcard : ∀ n, 0 < (Fintype.card (Oq n) : ℝ))
    (hdev : IsBigOp P (fun n ω =>
        devL1 (lev n) (sh2 n ω) (sbar n) (fun e => sg n e ω) (sige n))
      (fun n => rho n / cmax n))
    (hbr : IsBigOp P (fun n ω => frobNorm (IdentE2.obsGram (xt n ω))
        + ∑ e : Esq n, frobNorm (IdentE2.weightGram (c n) (xt n ω) (lev n e)))
      (fun n => (Fintype.card (Oq n) : ℝ) * cmax n))
    (hrho : Tendsto rho atTop (𝓝 0)) :
    IsBigOp P (fun n ω => frobNorm (((Fintype.card (Oq n) : ℝ))⁻¹
        • plugMeat (c n) (xt n ω) (lev n) (sh2 n ω) (fun e => sg n e ω) - Sn n ω)) rho
      ∧ TendstoInMeasure P (fun n ω => frobNorm (((Fintype.card (Oq n) : ℝ))⁻¹
        • plugMeat (c n) (xt n ω) (lev n) (sh2 n ω) (fun e => sg n e ω) - Sn n ω))
        atTop (fun _ => (0 : ℝ)) := by
  classical
  have harith : ∀ N r cm d B : ℝ, 0 < N → 0 < r → 0 < cm →
      N⁻¹ * (d * B) = r * ((d / (r / cm)) * (B / (N * cm))) := by
    intro N r cm d B hN hr hcm
    field_simp
  refine isBigOp_and_tendsto_of_le (W := fun n ω =>
      (devL1 (lev n) (sh2 n ω) (sbar n) (fun e => sg n e ω) (sige n) / (rho n / cmax n))
        * ((frobNorm (IdentE2.obsGram (xt n ω))
            + ∑ e : Esq n, frobNorm (IdentE2.weightGram (c n) (xt n ω) (lev n e)))
          / ((Fintype.card (Oq n) : ℝ) * cmax n)))
    hrho0 (fun n ω => Wald.frobNorm_nonneg _) (fun n ω => ?_) (fun n ω => ?_)
    (bddInProb_mul hdev hbr) hrho
  · exact mul_nonneg
      (div_nonneg (devL1_nonneg _ _ _ _ _) (div_nonneg (hrho0 n).le (hcmax0 n).le))
      (div_nonneg (add_nonneg (Wald.frobNorm_nonneg _)
        (Finset.sum_nonneg fun _ _ => Wald.frobNorm_nonneg _))
        (mul_nonneg (hcard n).le (hcmax0 n).le))
  · have hsub : ((Fintype.card (Oq n) : ℝ))⁻¹
        • plugMeat (c n) (xt n ω) (lev n) (sh2 n ω) (fun e => sg n e ω) - Sn n ω
        = ((Fintype.card (Oq n) : ℝ))⁻¹
          • (plugMeat (c n) (xt n ω) (lev n) (sh2 n ω) (fun e => sg n e ω)
              - plugTarget (c n) (xt n ω) (lev n) (sbar n) (sige n)) := by
      rw [hSn n ω, smul_sub]
    have hinvnn : (0 : ℝ) ≤ ((Fintype.card (Oq n) : ℝ))⁻¹ := le_of_lt (inv_pos.mpr (hcard n))
    rw [hsub, frobNorm_smul, abs_of_nonneg hinvnn]
    have hstep := mul_le_mul_of_nonneg_left
      (frobNorm_plugMeat_sub_plugTarget_le (c n) (xt n ω) (lev n) (sh2 n ω) (sbar n)
        (fun e => sg n e ω) (sige n) (hnn n) (halpha n)) hinvnn
    rw [harith ((Fintype.card (Oq n) : ℝ)) (rho n) (cmax n) _ _
      (hcard n) (hrho0 n) (hcmax0 n)] at hstep
    exact hstep

/-! ### Clause (b), third claim: `nV̂_PI →^p H^{-1}SH^{-1}`, restricted through `𝓡`

With `Ĝ_n := (n^{-1}X̃'X̃)^{-1}`, `nV̂_PI = Ĝ_n(n^{-1}M̂_PI)Ĝ_n`. The difference
`𝓡(nV̂_PI)𝓡' − 𝓡H^{-1}SH^{-1}𝓡'` splits into a term bounded by `‖𝓡‖_F²‖Ĝ_n‖_F²` times the second
claim and a deterministic term. `Ĝ_n` and `S_n` are nonrandom, and `Ĝ_n` enters through a
uniform bound on its Frobenius norm (`hLg`) together with `hdet`. -/

/-- Sub-multiplicativity of the squared Frobenius norm for rectangular factors. A sharper
operator-norm form is in `Multiway.RateAgnostic`. -/
theorem rectFrobSq_mul_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    rectFrobSq (A * B) ≤ rectFrobSq A * rectFrobSq B := by
  have hstep : ∀ (i : α) (k : γ), ((A * B) i k) ^ 2
      ≤ (∑ j : β, A i j ^ 2) * (∑ j : β, B j k ^ 2) := by
    intro i k
    have h : (A * B) i k = ∑ j : β, A i j * B j k := by
      simp only [Matrix.mul_apply]
    rw [h]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hsum : rectFrobSq (A * B)
      ≤ ∑ i : α, ∑ k : γ, (∑ j : β, A i j ^ 2) * (∑ j : β, B j k ^ 2) := by
    rw [rectFrobSq]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hstep i k
  have hfact : ∑ i : α, ∑ k : γ, (∑ j : β, A i j ^ 2) * (∑ j : β, B j k ^ 2)
      = (∑ i : α, ∑ j : β, A i j ^ 2) * (∑ k : γ, ∑ j : β, B j k ^ 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hB : ∑ k : γ, ∑ j : β, B j k ^ 2 = rectFrobSq B := by
    rw [rectFrobSq]
    exact Finset.sum_comm
  rw [hfact, hB] at hsum
  exact hsum

theorem rectFrobNorm_mul_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    rectFrobNorm (A * B) ≤ rectFrobNorm A * rectFrobNorm B := by
  rw [rectFrobNorm, rectFrobNorm, rectFrobNorm, ← Real.sqrt_mul (rectFrobSq_nonneg A)]
  exact Real.sqrt_le_sqrt (rectFrobSq_mul_le A B)

theorem rectFrobNorm_mul3_le {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) (C : Matrix γ δ ℝ) :
    rectFrobNorm (A * B * C) ≤ rectFrobNorm A * rectFrobNorm B * rectFrobNorm C :=
  le_trans (rectFrobNorm_mul_le _ _)
    (mul_le_mul_of_nonneg_right (rectFrobNorm_mul_le _ _) (rectFrobNorm_nonneg _))

theorem rectFrobNorm_transpose {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℝ) :
    rectFrobNorm (Aᵀ) = rectFrobNorm A := by
  rw [rectFrobNorm, rectFrobNorm, rectFrobSq_transpose]

/-- A nonnegative `Z_n ≤ c Y_n + d_n` with `Y_n ⟶^p 0` and deterministic `d_n → 0` converges
in probability to zero. -/
theorem tendstoInProb_zero_of_le_mul_add {Z Y : ℕ → Ω → ℝ} {d : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hY0 : ∀ n ω, 0 ≤ Y n ω)
    (hle : ∀ n ω, Z n ω ≤ c * Y n ω + d n)
    (hY : TendstoInMeasure P Y atTop (fun _ => (0 : ℝ)))
    (hd : Tendsto d atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  have hc0 : (0 : ℝ) < c + 1 := by linarith
  have hYlim := hY (ε / (2 * (c + 1))) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hYlim
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Filter.Tendsto.eventually_lt_const (by positivity : (0 : ℝ) < ε / 2) hd]
    with n hn
  refine measure_mono fun ω hω => ?_
  have h1 : ε ≤ dist (Z n ω) 0 := hω
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hZ0 n ω)] at h1
  show ε / (2 * (c + 1)) ≤ dist (Y n ω) 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hY0 n ω)]
  by_contra hcon
  have hlt : Y n ω < ε / (2 * (c + 1)) := not_le.mp hcon
  have h4 : (c + 1) * Y n ω < (c + 1) * (ε / (2 * (c + 1))) :=
    mul_lt_mul_of_pos_left hlt hc0
  have h5 : (c + 1) * (ε / (2 * (c + 1))) = ε / 2 := by
    field_simp
  have h6 : c * Y n ω ≤ (c + 1) * Y n ω := by nlinarith [hY0 n ω]
  have h7 := hle n ω
  rw [h5] at h4
  linarith

/-- **Theorem 9(b), third claim**, restricted through `𝓡`. `Mn` is `n^{-1}M̂_PI`, `Sn` is `S_n`,
`Gn` is `(n^{-1}X̃'X̃)^{-1}` and `Rm` is `𝓡`; the conclusion is
`𝓡(nV̂_PI)𝓡' →^p 𝓡H^{-1}SH^{-1}𝓡'`. `hM` is the second claim. -/
theorem tendstoInProb_restricted_of_meat
    {Kq : ℕ → Type*} [∀ n, Fintype (Kq n)] {ι : Type*} [Fintype ι]
    (Mn : ∀ n, Ω → Matrix (Kq n) (Kq n) ℝ) (Sn : ∀ n, Matrix (Kq n) (Kq n) ℝ)
    (Gn : ∀ n, Matrix (Kq n) (Kq n) ℝ) (Rm : ∀ n, Matrix ι (Kq n) ℝ) (Sg : Matrix ι ι ℝ)
    {Lg Lr : ℝ} (hLg0 : 0 ≤ Lg) (hLr0 : 0 ≤ Lr)
    (hLg : ∀ n, frobNorm (Gn n) ≤ Lg) (hLr : ∀ n, rectFrobNorm (Rm n) ≤ Lr)
    (hdet : Tendsto (fun n => frobNorm (Rm n * (Gn n * Sn n * Gn n) * (Rm n)ᵀ - Sg))
      atTop (𝓝 0))
    (hM : TendstoInMeasure P (fun n ω => frobNorm (Mn n ω - Sn n)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P
      (fun n ω => frobNorm (Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ - Sg))
      atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_zero_of_le_mul_add (c := Lr ^ 2 * Lg ^ 2) (by positivity)
    (fun n ω => Wald.frobNorm_nonneg _) (fun n ω => Wald.frobNorm_nonneg _)
    (fun n ω => ?_) hM hdet
  have hsplit : Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ - Sg
      = Rm n * (Gn n * (Mn n ω - Sn n) * Gn n) * (Rm n)ᵀ
        + (Rm n * (Gn n * Sn n * Gn n) * (Rm n)ᵀ - Sg) := by
    have hexp : Rm n * (Gn n * (Mn n ω - Sn n) * Gn n) * (Rm n)ᵀ
        = Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ
          - Rm n * (Gn n * Sn n * Gn n) * (Rm n)ᵀ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    rw [hexp]
    abel
  have hEnn : (0 : ℝ) ≤ frobNorm (Mn n ω - Sn n) := Wald.frobNorm_nonneg _
  have hmid : rectFrobNorm (Gn n * (Mn n ω - Sn n) * Gn n)
      ≤ Lg * frobNorm (Mn n ω - Sn n) * Lg := by
    refine (rectFrobNorm_mul3_le _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul (hLg n) le_rfl (rectFrobNorm_nonneg _) hLg0) (hLg n)
      (rectFrobNorm_nonneg _) (mul_nonneg hLg0 hEnn)
  have hout : frobNorm (Rm n * (Gn n * (Mn n ω - Sn n) * Gn n) * (Rm n)ᵀ)
      ≤ Lr ^ 2 * Lg ^ 2 * frobNorm (Mn n ω - Sn n) := by
    have hRT : rectFrobNorm ((Rm n)ᵀ) ≤ Lr := by
      rw [rectFrobNorm_transpose]
      exact hLr n
    have h1 : rectFrobNorm (Rm n * (Gn n * (Mn n ω - Sn n) * Gn n) * (Rm n)ᵀ)
        ≤ Lr * (Lg * frobNorm (Mn n ω - Sn n) * Lg) * Lr := by
      refine (rectFrobNorm_mul3_le _ _ _).trans ?_
      exact mul_le_mul (mul_le_mul (hLr n) hmid (rectFrobNorm_nonneg _) hLr0) hRT
        (rectFrobNorm_nonneg _) (mul_nonneg hLr0 (mul_nonneg (mul_nonneg hLg0 hEnn) hLg0))
    refine h1.trans (le_of_eq ?_)
    ring
  rw [hsplit]
  refine (frobNorm_add_le _ _).trans ?_
  linarith

end ClauseBOp

/-! ## 8. Clause (c): Wald inference

Clause (c) applies `wald_of_clt` of `Multiway/Wald.lean` to the plug-in estimator. The
normalization `a_n` cancels by `Wald.waldStat_smul` and `Wald.posDef_smul_iff`. -/

section ClauseC

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ωp : Type*} {mΩp : MeasurableSpace Ωp} {P : Measure Ωp} [IsProbabilityMeasure P]
variable {Ωq : Type*} {mΩq : MeasurableSpace Ωq} {P' : Measure Ωq} [IsProbabilityMeasure P']

/-- **Theorem 9(c).** Let `Vh n ω = 𝓡V̂_PI𝓡'`, `Sg = 𝓡H^{-1}SH^{-1}𝓡' ≻ 0` and
`dev n ω = 𝓡(β̂_JM − β)`. If `√a_n dev_n` is asymptotically `N(0, Sg)` (`hCLT`, the restricted
form of Theorem 4(b)) and `a_n Vh_n →^p Sg` (`hV`), then `P(Vh_n ≻ 0) → 1` and the Wald statistic
converges in distribution to `χ²_r`. -/
theorem plugin_wald
    {Sg : Matrix ι ι ℝ} (hSg : Sg.PosDef)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {Vh : ℕ → Ωp → Matrix ι ι ℝ} (hVherm : ∀ n ω, (Vh n ω).IsHermitian)
    (hVmeas : ∀ n, Measurable (Vh n))
    (hV : TendstoInMeasure P (fun n ω => frobNorm (a n • Vh n ω - Sg)) atTop (fun _ => 0))
    {dev : ℕ → Ωp → EuclideanSpace ℝ ι} {G : Ωq → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution (fun n ω => Real.sqrt (a n) • dev n ω) atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 Sg) :
    Tendsto (fun n => P {ω | (Vh n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution (fun n ω => Wald.waldStat (Vh n ω) (dev n ω)) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P) (multivariateGaussian 0 1) := by
  obtain ⟨h1, h2⟩ := Wald.wald_of_clt hSg (A := fun n ω => a n • Vh n ω)
    (fun n ω => (hVherm n ω).smul (IsSelfAdjoint.all (a n)))
    (fun n => (hVmeas n).const_smul (a n)) hV hCLT hG
  have hset : (fun n => P {ω | (a n • Vh n ω).PosDef}) = fun n => P {ω | (Vh n ω).PosDef} := by
    funext n
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact Wald.posDef_smul_iff (ha n) _
  have hfun : (fun n ω => Wald.waldStat (a n • Vh n ω) (Real.sqrt (a n) • dev n ω))
      = fun n ω => Wald.waldStat (Vh n ω) (dev n ω) := by
    funext n ω
    exact Wald.waldStat_smul (ha n) _ _
  rw [hset] at h1
  rw [hfun] at h2
  exact ⟨h1, h2⟩

/-- **Theorem 9(c)** with the variance limit derived from the second claim of clause (b)
through `tendstoInProb_restricted_of_meat`, using `hLg`, `hLr` and `hdet`. The central limit
theorem `hCLT` remains a hypothesis. -/
theorem plugin_wald_of_meat
    {Kq : ℕ → Type*} [∀ n, Fintype (Kq n)]
    (Mn : ∀ n, Ωp → Matrix (Kq n) (Kq n) ℝ) (Sn : ∀ n, Matrix (Kq n) (Kq n) ℝ)
    (Gn : ∀ n, Matrix (Kq n) (Kq n) ℝ) (Rm : ∀ n, Matrix ι (Kq n) ℝ)
    {Sg : Matrix ι ι ℝ} (hSg : Sg.PosDef)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hVherm : ∀ n ω, ((a n)⁻¹ • (Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ)).IsHermitian)
    (hVmeas : ∀ n, Measurable fun ω => (a n)⁻¹ • (Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ))
    {Lg Lr : ℝ} (hLg0 : 0 ≤ Lg) (hLr0 : 0 ≤ Lr)
    (hLg : ∀ n, frobNorm (Gn n) ≤ Lg) (hLr : ∀ n, rectFrobNorm (Rm n) ≤ Lr)
    (hdet : Tendsto (fun n => frobNorm (Rm n * (Gn n * Sn n * Gn n) * (Rm n)ᵀ - Sg))
      atTop (𝓝 0))
    (hM : TendstoInMeasure P (fun n ω => frobNorm (Mn n ω - Sn n)) atTop (fun _ => (0 : ℝ)))
    {dev : ℕ → Ωp → EuclideanSpace ℝ ι} {G : Ωq → EuclideanSpace ℝ ι}
    (hCLT : TendstoInDistribution (fun n ω => Real.sqrt (a n) • dev n ω) atTop G (fun _ => P) P')
    (hG : P'.map G = multivariateGaussian 0 Sg) :
    Tendsto (fun n => P {ω | ((a n)⁻¹ • (Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ)).PosDef})
        atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => Wald.waldStat ((a n)⁻¹ • (Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ))
            (dev n ω)) atTop (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (fun _ => P)
          (multivariateGaussian 0 1) := by
  refine plugin_wald hSg ha hVherm hVmeas ?_ hCLT hG
  have hfun : (fun n ω => frobNorm (a n • ((a n)⁻¹
        • (Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ)) - Sg))
      = fun n ω => frobNorm (Rm n * (Gn n * Mn n ω * Gn n) * (Rm n)ᵀ - Sg) := by
    funext n ω
    rw [smul_smul, mul_inv_cancel₀ (ha n).ne', one_smul]
  rw [hfun]
  exact tendstoInProb_restricted_of_meat Mn Sn Gn Rm Sg hLg0 hLr0 hLg hLr hdet hM

end ClauseC

/-! ## 9. Examples

Each example below applies a theorem of this file to an explicit model satisfying all of its
hypotheses. The theorems about sequences of designs are applied to growing designs or growing
normalizations. -/

section Witness

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-! ### Clause (a)

Two observations and three dimensions, of which `0` and `1` are constant and `2` separates the
observations; `R = I − ιι'/2`; `s̄² = 7` and a single interaction level `{0,1}` with `σ² = 2`, so
that `R Ω R = 5R` by `IdentE2.identE2_witness`. The residual vector is `ν̂ = (z, −z)` with
`E[ν̂ν̂'] = 5R`. -/

/-- The expectation of the example, the average under the uniform law on `Bool` as a linear
functional. -/
noncomputable def wExp : (Bool → ℝ) →ₗ[ℝ] ℝ where
  toFun f := (f true + f false) / 2
  map_add' f g := by simp; ring
  map_smul' c f := by simp; ring

@[simp] theorem wExp_apply (f : Bool → ℝ) : wExp f = (f true + f false) / 2 := rfl

/-- The disturbance `z` of the example, taking the values `2` and `1`, with second moment
`(2² + 1²)/2 = 5/2` under the uniform law on `Bool`. -/
def wZ : Bool → ℝ := fun b => if b then 2 else 1

/-- The residual vector `ν̂ = (z, −z)` of the example, whose second-moment matrix is `5R`. -/
def wNu : Fin 2 → Bool → ℝ := fun o b => (if o = 0 then (1 : ℝ) else -1) * wZ b

theorem wNu_moment (o o' : Fin 2) :
    wExp (wNu o * wNu o') = ((5 : ℝ) • IdentE2.wR) o o' := by
  simp only [wExp_apply, Pi.mul_apply, wNu, wZ, Matrix.smul_apply, IdentE2.wR_apply, smul_eq_mul]
  fin_cases o <;> fin_cases o' <;> norm_num

/-- An example for `moment_eq_design_mulVec` (clause (a), first claim). -/
theorem moment_eq_design_witness :
    wExp (momentStat (wDiag : Matrix (Fin 2) (Fin 2) ℝ) wNu)
      = (momentDesign IdentE2.wc IdentE2.wR (fun _ : Fin 1 => (wDiag : Matrix (Fin 2) (Fin 2) ℝ))
            (fun _ : Fin 1 => ({0, 1} : Finset (Fin 3)))).mulVec
          (paramVec (fun _ : Fin 1 => ({0, 1} : Finset (Fin 3))) (7 : ℝ) (fun _ => (2 : ℝ))) 0 := by
  have hRD : ∀ m ∈ ({0, 1} : Finset (Fin 3)),
      ∀ t ∈ cells IdentE2.wc ({m} : Finset (Fin 3)), ∀ o : Fin 2,
        ∑ o' ∈ t, IdentE2.wR o o' = 0 := by
    intro m hm
    have hm2 : m ≠ 2 := by
      rcases Finset.mem_insert.1 hm with h | h
      · rw [h]; decide
      · rw [Finset.mem_singleton.1 h]; decide
    refine IdentE2.wR_cell_sum ?_
    simp only [Finset.mem_singleton]
    exact fun h => hm2 h.symm
  refine moment_eq_design_mulVec IdentE2.wc ({0, 1} : Finset (Fin 3))
    ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
    (fun _ : Fin 1 => ({0, 1} : Finset (Fin 3))) (fun x y _ => Subsingleton.elim x y) ?_
    (fun _ : Fin 1 => (wDiag : Matrix (Fin 2) (Fin 2) ℝ)) (fun _ => (3 : ℝ)) (fun _ => (2 : ℝ))
    (7 : ℝ) (Om := IdentE2.wOm) IdentE2.wR_isSymm IdentE2.wR_idem hRD rfl wExp wNu ?_ 0
  · exact (Finset.image_const ⟨0, Finset.mem_univ 0⟩ _).symm
  · intro o o'
    rw [IdentE2.identE2_witness]
    exact wNu_moment o o'

/-- An example for `thetaHat_unbiased` (clause (a), second claim), with the identity design over
one row and one column, `m̂ ≡ 1` and `θ = 1`. -/
theorem thetaHat_unbiased_witness :
    wExp (thetaHat (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => (1 : ℝ)) 0) = 1 := by
  refine thetaHat_unbiased wExp (1 : Matrix (Fin 1) (Fin 1) ℝ) ?_ (fun _ => (1 : ℝ))
    (fun _ _ => (1 : ℝ)) ?_ 0
  · simp
  · intro r
    simp [Matrix.one_mulVec]

/-! ### Clause (b): a one-observation, one-regressor design -/

/-- The design of the clause (b) examples, with one observation, one dimension and one regressor. -/
def bc : Fin 1 → Fin 1 → Fin 1 := fun _ _ => 0

/-- The regressor matrix of the clause (b) examples. -/
def bxt : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

/-- The level map of the clause (b) examples, whose single level is `∅`. -/
def blev : Fin 1 → Finset (Fin 1) := fun _ => ∅

/-- An example for `frobNorm_plugMeat_sub_plugTarget_le`, at `σ² = 1` and `s̄² = 3`. -/
theorem plugMeat_error_witness :
    frobNorm (plugMeat bc bxt blev 4 (fun _ => 1) - plugTarget bc bxt blev 3 (fun _ => 1))
      ≤ devL1 blev 4 3 (fun _ => 1) (fun _ => 1)
        * (frobNorm (IdentE2.obsGram bxt)
            + ∑ e : Fin 1, frobNorm (IdentE2.weightGram bc bxt (blev e))) := by
  refine frobNorm_plugMeat_sub_plugTarget_le bc bxt blev 4 3 (fun _ => 1) (fun _ => 1)
    (fun _ => zero_le_one) ?_
  norm_num

/-- An example for `weightGram_le_cmax_obsGram`, at `c_max = 1`. -/
theorem weightGram_le_cmax_witness :
    ((((1 : ℕ) : ℝ)) • IdentE2.obsGram bxt
      - IdentE2.weightGram bc bxt (∅ : Finset (Fin 1))).PosSemidef := by
  refine weightGram_le_cmax_obsGram bc bxt (∅ : Finset (Fin 1)) ?_
  intro t _
  calc t.card ≤ Fintype.card (Fin 1) := Finset.card_le_univ t
    _ = 1 := by simp

/-! ### Clause (c) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An example for `plugin_wald` with `Σ = I_r`, `𝓡V̂_PI𝓡' = I_r` at `a_n = 1`, and the identity
deviation on `(EuclideanSpace ℝ ι, N(0, I_r))`. At `Σ̂ = I_r` the Wald statistic is `‖x‖²`
(`Wald.waldStat_one`). -/
theorem plugin_wald_witness :
    Tendsto (fun _ : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
        {_x : EuclideanSpace ℝ ι | (1 : Matrix ι ι ℝ).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun (_ : ℕ) (y : EuclideanSpace ℝ ι) => Wald.waldStat (1 : Matrix ι ι ℝ) y) atTop
          (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2)
          (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
          (multivariateGaussian 0 1) := by
  refine plugin_wald (P := multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) (Sg := 1) Matrix.PosDef.one
    (a := fun _ => (1 : ℝ)) (fun _ => one_pos)
    (Vh := fun _ _ => (1 : Matrix ι ι ℝ)) (fun _ _ => Matrix.isHermitian_one)
    (fun _ => measurable_const) ?_ (dev := fun _ => id) (G := id) ?_ ?_
  · intro ε hε
    have hz : frobNorm ((1 : ℝ) • (1 : Matrix ι ι ℝ) - 1) = 0 := by
      simp [frobNorm, frobSq]
    have hset : {y : EuclideanSpace ℝ ι |
        ε ≤ edist (frobNorm ((1 : ℝ) • (1 : Matrix ι ι ℝ) - 1)) ((fun _ => (0 : ℝ)) y)} = ∅ := by
      ext y
      simp only [hz, edist_self, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    simp only [hset, measure_empty]
    exact tendsto_const_nhds
  · have h : (fun (_ : ℕ) (y : EuclideanSpace ℝ ι) => Real.sqrt (1 : ℝ) • id y)
        = fun (_ : ℕ) (y : EuclideanSpace ℝ ι) => id y := by
      funext n y
      simp
    rw [h]
    exact tendstoInDistribution_const aemeasurable_id
  · exact Measure.map_id

/-! ### Clause (b), `O_p` claims: a growing design with no interaction levels

`𝒪_n` has `n + 1` observations, so that `ϱ_n = (n+1)^{-1}` vanishes and the bracket
`‖X̃'X̃‖_F = n + 1` is `O_p(n c_max)`. The model has `𝓔 = ∅`, one regressor with `x̃_o ≡ 1`,
`s̄² = 1`, `c_max = 1` and `ŝ² = 1 + ϱ_n`, so that `n^{-1}M̂_PI − S_n = ϱ_n`. The probability space
is a point mass. -/

open scoped ENNReal

/-- The probability space of the `O_p` examples. -/
noncomputable def wP : Measure ℝ := Measure.dirac 0

/-- The rate `ϱ_n = (n+1)^{-1}` of the `O_p` examples. -/
noncomputable def wRho (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem wRho_pos (n : ℕ) : 0 < wRho n := by
  rw [wRho]
  positivity

theorem wRho_tendsto : Tendsto wRho atTop (𝓝 0) := by
  have he : wRho = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    funext n
    rw [wRho, one_div]
  rw [he]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- An example for `thetaHat_sub_isBigOp` with one row and one column, `𝒜 = I₁`, and a moment
that differs from its mean by `ϱ_n`. -/
theorem thetaHat_sub_witness :
    IsBigOp wP (fun n (ω : ℝ) => ∑ j : Fin 1,
      |thetaHat (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun (_ : Fin 1) (_ : ℝ) => wRho n) j ω
        - (0 : ℝ)|) wRho := by
  refine thetaHat_sub_isBigOp (P := wP) (Rw := fun _ => Fin 1) (Cl := fun _ => Fin 1)
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => by simp)
    (fun _ _ => (0 : ℝ)) (fun n _ _ => wRho n) wRho_pos (fun _ _ => aemeasurable_const)
    (Msq := 1) (by simp) ?_ (Nrow := 1) (fun _ => by simp) (Ncol := 1) (fun _ => by simp)
    (Lam := 1) zero_le_one ?_
  · intro n r
    have hz : ∀ _ : ℝ,
        ‖((wRho n - ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun _ => (0 : ℝ)) r) / wRho n) ^ 2‖ₑ
          = (1 : ℝ≥0∞) := by
      intro _
      rw [Matrix.one_mulVec, sub_zero, div_self (wRho_pos n).ne']
      simp
    rw [lintegral_congr hz]
    simp [wP]
  · intro n j r
    fin_cases j
    fin_cases r
    simp

/-! #### A growing design for the second claim -/

/-- The growing design, with `n+1` observations, one fixed-effect dimension and one category. -/
def qc (n : ℕ) : Fin 1 → Fin (n + 1) → Fin 1 := fun _ _ => 0

/-- The regressor matrix of the growing design, with one regressor equal to `1`, so `X̃'X̃ = n+1`. -/
def qxt (n : ℕ) : ℝ → Fin (n + 1) → Fin 1 → ℝ := fun _ _ _ => 1

/-- `𝓔 = ∅`. -/
def qlev (_n : ℕ) : Fin 0 → Finset (Fin 1) := fun e => e.elim0

/-- `ŝ² = 1 + ϱ_n`. -/
noncomputable def qsh2 (n : ℕ) : ℝ → ℝ := fun _ => 1 + wRho n

/-- The empty family of `σ̂_e²`. -/
def qsg (_n : ℕ) : Fin 0 → ℝ → ℝ := fun e _ => e.elim0

/-- The empty family of `σ_e²`. -/
def qsige (_n : ℕ) : Finset (Fin 1) → ℝ := fun _ => 0

/-- `S_n`, as `n^{-1}` times the target. -/
noncomputable def qSn (n : ℕ) : ℝ → Matrix (Fin 1) (Fin 1) ℝ :=
  fun ω => ((Fintype.card (Fin (n + 1)) : ℝ))⁻¹
    • plugTarget (qc n) (qxt n ω) (qlev n) 1 (qsige n)

theorem qobsGram_frobNorm (n : ℕ) (ω : ℝ) :
    frobNorm (IdentE2.obsGram (qxt n ω)) = (n : ℝ) + 1 := by
  have hg : IdentE2.obsGram (qxt n ω) = Matrix.of (fun _ _ => ((n : ℝ) + 1)) := by
    ext a b
    simp [IdentE2.obsGram, qxt, Finset.card_univ]
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [hg, frobNorm, frobSq]
  simp only [Matrix.of_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  rw [Real.sqrt_sq hnn]

/-- An example for `plugMeat_sub_target_isBigOp` on the growing design above. -/
theorem plugMeat_sub_target_witness :
    IsBigOp wP (fun n ω => frobNorm (((Fintype.card (Fin (n + 1)) : ℝ))⁻¹
        • plugMeat (qc n) (qxt n ω) (qlev n) (qsh2 n ω) (fun e => qsg n e ω) - qSn n ω)) wRho
      ∧ TendstoInMeasure wP (fun n ω => frobNorm (((Fintype.card (Fin (n + 1)) : ℝ))⁻¹
        • plugMeat (qc n) (qxt n ω) (qlev n) (qsh2 n ω) (fun e => qsg n e ω) - qSn n ω))
        atTop (fun _ => (0 : ℝ)) := by
  refine plugMeat_sub_target_isBigOp (P := wP) qc qxt qlev qsh2 qsg (fun _ => (1 : ℝ)) qsige qSn
    (fun n ω => rfl) (fun n e => e.elim0) (fun n => by simp)
    (rho := wRho) (cmax := fun _ => (1 : ℝ)) wRho_pos (fun _ => one_pos)
    (fun n => by rw [Fintype.card_fin]; positivity) ?_ ?_ wRho_tendsto
  · refine bddInProb_of_abs_le (W := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (fun n => ?_)
      (bddInProb_const 1)
    filter_upwards with ω
    have hdv : devL1 (qlev n) (qsh2 n ω) 1 (fun e => qsg n e ω) (qsige n) = wRho n := by
      simp only [devL1, qsh2, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
        add_sub_cancel_left]
      exact abs_of_nonneg (wRho_pos n).le
    rw [hdv, div_one, div_self (wRho_pos n).ne']
  · refine bddInProb_of_abs_le (W := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (fun n => ?_)
      (bddInProb_const 1)
    filter_upwards with ω
    rw [qobsGram_frobNorm n ω]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one]
    rw [div_self (by positivity : ((n : ℝ) + 1) ≠ 0)]

/-! #### The third claim and clause (c) -/

theorem qfrobNorm_one : frobNorm (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  rw [frobNorm, frobSq]
  simp [Matrix.one_apply]

theorem qrectFrobNorm_one : rectFrobNorm (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := qfrobNorm_one

/-- An example for `tendstoInProb_restricted_of_meat` with one regressor, `Ĝ_n = 𝓡 = I₁`, and a
meat that differs from its target by `ϱ_n`. -/
theorem tendstoInProb_restricted_witness :
    TendstoInMeasure wP
      (fun (n : ℕ) (_ : ℝ) => frobNorm ((1 : Matrix (Fin 1) (Fin 1) ℝ)
        * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * ((1 + wRho n) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
            * (1 : Matrix (Fin 1) (Fin 1) ℝ))
        * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ - (1 : Matrix (Fin 1) (Fin 1) ℝ)))
      atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_restricted_of_meat (P := wP)
    (fun n (_ : ℝ) => (1 + wRho n) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (Lg := 1) (Lr := 1) zero_le_one zero_le_one (fun _ => le_of_eq qfrobNorm_one)
    (fun _ => le_of_eq qrectFrobNorm_one) ?_ ?_
  · have h : ∀ _ : ℕ, (0 : ℝ) = frobNorm ((1 : Matrix (Fin 1) (Fin 1) ℝ)
        * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)
            * (1 : Matrix (Fin 1) (Fin 1) ℝ))
        * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ - (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
      intro _
      simp [frobNorm_zero]
    exact Filter.Tendsto.congr h tendsto_const_nhds
  · refine Sequence.tendstoInProb_zero_of_abs_le_const (b := wRho) (fun n => ?_) wRho_tendsto
    filter_upwards with ω
    have hEq : ((1 + wRho n) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - 1)
        = wRho n • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [add_smul, one_smul]
      abel
    rw [hEq, frobNorm_smul, qfrobNorm_one, mul_one, abs_abs,
      abs_of_nonneg (wRho_pos n).le]

/-- An example for `plugin_wald_of_meat` with one regressor, `𝓡 = Ĝ_n = I₁`, meat equal to its
target, `Σ = I₁`, normalization `a_n = n + 1` and deviation `n^{-1/2}ω` on `(ℝ¹, N(0, I₁))`, so
that `√a_n(β̂ − β) = ω` is Gaussian for every `n`. -/
theorem plugin_wald_of_meat_witness :
    Tendsto (fun n : ℕ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
        {_ω : EuclideanSpace ℝ (Fin 1) | ((((n : ℝ) + 1)⁻¹)
          • ((1 : Matrix (Fin 1) (Fin 1) ℝ)
              * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)
                  * (1 : Matrix (Fin 1) (Fin 1) ℝ))
              * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
            Wald.waldStat ((((n : ℝ) + 1)⁻¹)
              • ((1 : Matrix (Fin 1) (Fin 1) ℝ)
                  * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)
                      * (1 : Matrix (Fin 1) (Fin 1) ℝ))
                  * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ))
              ((Real.sqrt ((n : ℝ) + 1))⁻¹ • ω))
          atTop (fun z : EuclideanSpace ℝ (Fin 1) => ‖z‖ ^ 2)
          (fun _ : ℕ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
          (multivariateGaussian 0 1) := by
  refine plugin_wald_of_meat (P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Sg := 1) Matrix.PosDef.one (a := fun n => (n : ℝ) + 1) (fun n => by positivity)
    (fun n ω => ?_) (fun n => measurable_const) (Lg := 1) (Lr := 1) zero_le_one zero_le_one
    (fun _ => le_of_eq qfrobNorm_one) (fun _ => le_of_eq qrectFrobNorm_one) ?_ ?_
    (dev := fun n ω => (Real.sqrt ((n : ℝ) + 1))⁻¹ • ω) (G := id) ?_ Measure.map_id
  · simp only [Matrix.mul_one, Matrix.transpose_one]
    exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
  · have h : ∀ _ : ℕ, (0 : ℝ) = frobNorm ((1 : Matrix (Fin 1) (Fin 1) ℝ)
        * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)
            * (1 : Matrix (Fin 1) (Fin 1) ℝ))
        * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ - (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
      intro _
      simp [frobNorm_zero]
    exact Filter.Tendsto.congr h tendsto_const_nhds
  · refine Sequence.tendstoInProb_zero_of_abs_le_const (b := fun _ => (0 : ℝ)) (fun n => ?_)
      tendsto_const_nhds
    filter_upwards with ω
    simp [frobNorm_zero]
  · have h : (fun (n : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) =>
        Real.sqrt ((n : ℝ) + 1) • ((Real.sqrt ((n : ℝ) + 1))⁻¹ • ω))
        = fun (_ : ℕ) (ω : EuclideanSpace ℝ (Fin 1)) => id ω := by
      funext n ω
      rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by positivity)), one_smul]
      rfl
    rw [h]
    exact tendstoInDistribution_const aemeasurable_id

end Witness

/-! ## 10. Clause (b), second claim, under the conditional law

The two `O_p` inputs are read under the regular conditional law `ℙ_ω := condExpKernel P 𝒟 ω` at
`P`-almost every `ω`, and the conclusion `n^{-1}M̂_PI − S_n ⟶^p 0` holds under `P`, by
`PrimitiveDesign.CondP.tendstoInMeasure_of_deconditioning`. The level map `c` and the level index
`lev` are deterministic. -/

section DesignDecond

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]

/-- **Theorem 9(b), second claim, conditional form.** `hdev` and `hbr` hold under
`ℙ_ω := condExpKernel P 𝒟 ω` for `P`-almost every `ω`, and the conclusion is convergence in
probability under `P`. It is derived from `plugMeat_sub_target_isBigOp` via
`PrimitiveDesign.CondP.tendstoInMeasure_of_deconditioning`. `hmeas` requires the deviation sets to be
measurable. -/
theorem plugMeat_sub_target_tendstoInProb_uncond
    {Oq Dq Lq Kq Esq : ℕ → Type*}
    [∀ n, Fintype (Oq n)] [∀ n, DecidableEq (Oq n)] [∀ n, DecidableEq (Dq n)]
    [∀ n, DecidableEq (Lq n)] [∀ n, Fintype (Kq n)] [∀ n, DecidableEq (Kq n)]
    [∀ n, Fintype (Esq n)]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ∀ n, Dq n → Oq n → Lq n) (xt : ∀ n, Ω → Oq n → Kq n → ℝ)
    (lev : ∀ n, Esq n → Finset (Dq n))
    (sh2 : ℕ → Ω → ℝ) (sg : ∀ n, Esq n → Ω → ℝ)
    (sbar : ℕ → ℝ) (sige : ∀ n, Finset (Dq n) → ℝ)
    (Sn : ∀ n, Ω → Matrix (Kq n) (Kq n) ℝ)
    (hSn : ∀ n ω, Sn n ω
      = ((Fintype.card (Oq n) : ℝ))⁻¹ • plugTarget (c n) (xt n ω) (lev n) (sbar n) (sige n))
    (hnn : ∀ (n : ℕ) (e : Esq n), 0 ≤ sige n (lev n e))
    (halpha : ∀ n, 0 ≤ sbar n - ∑ e : Esq n, sige n (lev n e))
    {rho cmax : ℕ → ℝ} (hrho0 : ∀ n, 0 < rho n) (hcmax0 : ∀ n, 0 < cmax n)
    (hcard : ∀ n, 0 < (Fintype.card (Oq n) : ℝ))
    (hmeas : ∀ n, Measurable fun y : Ω => frobNorm (((Fintype.card (Oq n) : ℝ))⁻¹
        • plugMeat (c n) (xt n y) (lev n) (sh2 n y) (fun e => sg n e y) - Sn n y))
    (hdev : ∀ᵐ ω ∂P, IsBigOp (condExpKernel P 𝒟 ω) (fun n y =>
        devL1 (lev n) (sh2 n y) (sbar n) (fun e => sg n e y) (sige n))
      (fun n => rho n / cmax n))
    (hbr : ∀ᵐ ω ∂P, IsBigOp (condExpKernel P 𝒟 ω) (fun n y =>
        frobNorm (IdentE2.obsGram (xt n y))
          + ∑ e : Esq n, frobNorm (IdentE2.weightGram (c n) (xt n y) (lev n e)))
      (fun n => (Fintype.card (Oq n) : ℝ) * cmax n))
    (hrho : Tendsto rho atTop (𝓝 0)) :
    TendstoInMeasure P (fun n y => frobNorm (((Fintype.card (Oq n) : ℝ))⁻¹
        • plugMeat (c n) (xt n y) (lev n) (sh2 n y) (fun e => sg n e y) - Sn n y))
      atTop (fun _ => (0 : ℝ)) := by
  refine PrimitiveDesign.CondP.tendstoInMeasure_of_deconditioning h𝒟 P
    (fun ε n => measurableSet_le measurable_const ((hmeas n).edist measurable_const)) ?_
  filter_upwards [hdev, hbr] with ω h1 h2
  exact (plugMeat_sub_target_isBigOp (P := condExpKernel P 𝒟 ω) c xt lev sh2 sg sbar sige Sn
    hSn hnn halpha hrho0 hcmax0 hcard h1 h2 hrho).2

/-! ### An example for the conditional second claim

The space is the two-coin space `Ω = Bool × Bool` of `Multiway/CLTMartingale.lean`, with
`𝒟 = σ(first coin)` a proper sub-σ-field and `ℙ_ω ≠ P`. The design is degenerate (`x̃ ≡ 0`,
`ŝ² ≡ 0`, `σ̂²_e ≡ 0`), so the statistic is identically zero, and the rate is `ϱ_n = (n+1)^{-1}`. -/

section PluginDecondWitness

namespace PluginDecondWitness

open Multiway.CLTMartingale.CondD.FrozenWitness
open ProbabilityTheory Filter
open scoped ENNReal Topology

/-- The degenerate regressor array. -/
def pXt (_ : ℕ) (_ : Omg) (_ : Fin 1) (_ : Fin 1) : ℝ := 0

/-- `ϱ_n = (n+1)^{-1}`. -/
noncomputable def pRho (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem pRho_pos (n : ℕ) : 0 < pRho n := by
  rw [pRho]; positivity

theorem pRho_tendsto : Tendsto pRho atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    simpa [Pi.inv_def] using h.inv_tendsto_atTop
  exact h2

theorem pObsGram (n : ℕ) (y : Omg) :
    IdentE2.obsGram (pXt n y) = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext a b
  simp [IdentE2.obsGram, pXt]

theorem pWeightGram (n : ℕ) (y : Omg) (e : Finset (Fin 1)) :
    IdentE2.weightGram (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) (pXt n y) e
      = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext a b
  simp [IdentE2.weightGram, cellWeight, pXt]

theorem pFrobNorm_zero : frobNorm (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
  simp [frobNorm, frobSq]

/-- An example for the conditional second claim, with a proper `𝒟`. -/
theorem plugMeat_sub_target_tendstoInProb_uncond_witness :
    (∃ B : Set Omg, MeasurableSet B ∧ ¬ MeasurableSet[Dsig] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dsig ω = Pw)
    ∧ (∀ n : ℕ, 0 < pRho n) ∧ Tendsto pRho atTop (𝓝 0)
    ∧ TendstoInMeasure Pw (fun n y => frobNorm (((Fintype.card (Fin 1) : ℝ))⁻¹
        • plugMeat (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) (pXt n y)
            (fun (_ : Fin 1) => (∅ : Finset (Fin 1))) (0 : ℝ) (fun _ : Fin 1 => (0 : ℝ))
          - ((Fintype.card (Fin 1) : ℝ))⁻¹
              • plugTarget (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) (pXt n y)
                  (fun (_ : Fin 1) => (∅ : Finset (Fin 1))) (0 : ℝ)
                  (fun _ : Finset (Fin 1) => (0 : ℝ))))
      atTop (fun _ => (0 : ℝ)) := by
  classical
  have hstat : ∀ (n : ℕ) (y : Omg), frobNorm (((Fintype.card (Fin 1) : ℝ))⁻¹
      • plugMeat (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) (pXt n y)
          (fun (_ : Fin 1) => (∅ : Finset (Fin 1))) (0 : ℝ) (fun _ : Fin 1 => (0 : ℝ))
        - ((Fintype.card (Fin 1) : ℝ))⁻¹
            • plugTarget (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) (pXt n y)
                (fun (_ : Fin 1) => (∅ : Finset (Fin 1))) (0 : ℝ)
                (fun _ : Finset (Fin 1) => (0 : ℝ))) = 0 := by
    intro n y
    rw [plugMeat, plugTarget, pObsGram n y, pWeightGram n y]
    simp [pFrobNorm_zero]
  refine ⟨Dsig_proper, freeze_witness.2.2.2.2, pRho_pos, pRho_tendsto, ?_⟩
  refine plugMeat_sub_target_tendstoInProb_uncond (𝒟 := Dsig)
    (Oq := fun _ => Fin 1) (Dq := fun _ => Fin 1) (Lq := fun _ => Fin 1)
    (Kq := fun _ => Fin 1) (Esq := fun _ => Fin 1)
    Dsig_le Pw (fun (_ : ℕ) (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) pXt
    (fun (_ : ℕ) (_ : Fin 1) => (∅ : Finset (Fin 1)))
    (fun (_ : ℕ) (_ : Omg) => (0 : ℝ)) (fun (_ : ℕ) (_ : Fin 1) (_ : Omg) => (0 : ℝ))
    (fun _ : ℕ => (0 : ℝ)) (fun (_ : ℕ) (_ : Finset (Fin 1)) => (0 : ℝ))
    (fun (n : ℕ) (y : Omg) => ((Fintype.card (Fin 1) : ℝ))⁻¹
      • plugTarget (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) (pXt n y)
          (fun (_ : Fin 1) => (∅ : Finset (Fin 1))) (0 : ℝ)
          (fun _ : Finset (Fin 1) => (0 : ℝ)))
    (fun _ _ => rfl) (fun _ _ => le_rfl) (fun _ => by simp)
    (rho := pRho) (cmax := fun _ => (1 : ℝ)) pRho_pos (fun _ => zero_lt_one)
    (fun _ => by simp) ?_ ?_ ?_ pRho_tendsto
  · intro n
    have hz : (fun y : Omg => frobNorm (((Fintype.card (Fin 1) : ℝ))⁻¹
        • plugMeat (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) (pXt n y)
            (fun (_ : Fin 1) => (∅ : Finset (Fin 1))) (0 : ℝ) (fun _ : Fin 1 => (0 : ℝ))
          - ((Fintype.card (Fin 1) : ℝ))⁻¹
              • plugTarget (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 1)) (pXt n y)
                  (fun (_ : Fin 1) => (∅ : Finset (Fin 1))) (0 : ℝ)
                  (fun _ : Finset (Fin 1) => (0 : ℝ))))
        = fun _ : Omg => (0 : ℝ) := funext fun y => hstat n y
    rw [hz]
    exact measurable_const
  · refine Filter.Eventually.of_forall fun ω => ?_
    refine Sequence.bddInProb_of_abs_le_const (M := 1) (fun n => ?_)
    filter_upwards with y
    simp [devL1]
  · refine Filter.Eventually.of_forall fun ω => ?_
    refine Sequence.bddInProb_of_abs_le_const (M := 1) (fun n => ?_)
    filter_upwards with y
    rw [pObsGram n y]
    simp [pWeightGram n y, pFrobNorm_zero]

end PluginDecondWitness

end PluginDecondWitness

end DesignDecond

/-! ## 11. Clause (b), first claim, under the conditional law

The variance input `hvar` of `thetaHat_sub_isBigOp` is read under `ℙ_ω := condExpKernel P 𝒟 ω`.
Since it is a `∫⁻` bound, disintegration of `P` turns it into the unconditional bound
(`PrimitiveDesign.CondP.lintegral_le_of_deconditioning`), and the conclusion is unchanged. The
rate `b n` is deterministic. -/

section CondVarDecond

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]

/-- **Theorem 9(b), first claim, conditional form.** The hypotheses are those of
`thetaHat_sub_isBigOp` except `hvar`, which bounds the normalized second moment of each moment
row under `ℙ_ω := condExpKernel P 𝒟 ω` for `P`-almost every `ω`. The conclusion is
`‖θ̂ − θ‖₁ = O_p(ϱ_n/c_max)` under `P`. -/
theorem thetaHat_sub_isBigOp_cond
    {Rw Cl : ℕ → Type*} [∀ n, Fintype (Rw n)] [∀ n, Fintype (Cl n)] [∀ n, DecidableEq (Cl n)]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ∀ n, Matrix (Rw n) (Cl n) ℝ) (hA : ∀ n, IsUnit ((A n)ᵀ * A n).det)
    (th : ∀ n, Cl n → ℝ) (mh : ∀ n, Rw n → Ω → ℝ)
    {b : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    (hmeas : ∀ n r, AEMeasurable (mh n r) P)
    {Msq : ℝ≥0∞} (hMsq : Msq ≠ ⊤)
    (hvar : ∀ (n : ℕ) (r : Rw n), ∀ᵐ ω ∂P,
      ∫⁻ y, ‖((mh n r y - (A n *ᵥ th n) r) / b n) ^ 2‖ₑ ∂(condExpKernel P 𝒟 ω) ≤ Msq)
    {Nrow Ncol : ℕ} (hNrow : ∀ n, Fintype.card (Rw n) ≤ Nrow)
    (hNcol : ∀ n, Fintype.card (Cl n) ≤ Ncol)
    {Lam : ℝ} (hLam0 : 0 ≤ Lam)
    (hLam : ∀ (n : ℕ) (j : Cl n) (r : Rw n),
      |(((A n)ᵀ * A n)⁻¹ * (A n)ᵀ) j r| ≤ Lam) :
    IsBigOp P (fun n ω => ∑ j : Cl n, |thetaHat (A n) (mh n) j ω - th n j|) b := by
  refine thetaHat_sub_isBigOp (P := P) A hA th mh hb hmeas hMsq ?_ hNrow hNcol hLam0 hLam
  intro n r
  refine PrimitiveDesign.CondP.lintegral_le_of_deconditioning h𝒟 P ?_ (hvar n r)
  have hd0 : AEMeasurable (fun ω => (mh n r ω - (A n *ᵥ th n) r) / b n) P :=
    ((hmeas n r).sub aemeasurable_const).div_const _
  have h2 : AEMeasurable (fun ω => ((mh n r ω - (A n *ᵥ th n) r) / b n) ^ 2) P := by
    simpa [pow_two, Pi.mul_def] using hd0.mul hd0
  exact h2.enorm

/-! ### An example for the conditional first claim

On `Ω = Bool × Bool` with two fair coins and `𝒟 = σ(first coin)`, `m̂` depends on both coins,
`ℙ_ω ≠ P`, and the conditional second moment `(pScale ω)²(pRowc r)²` depends on `ω`. The moment
system is overidentified, with `𝒜` of size `2 × 1`, `𝒜'𝒜 = 2` and `θ̂ = (m̂₀ + m̂₁)/2`. The statistic
equals `(3/2)(n+1)^{-1}(pScale y)`. -/

namespace PluginCondVarWitness

open Multiway.CLTMartingale.CondD.FrozenWitness

/-- The rate `ϱ_n/c_max = (n+1)^{-1}`. -/
noncomputable def pB (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem pB_pos (n : ℕ) : 0 < pB n := by rw [pB]; positivity

theorem pB_tendsto : Tendsto pB atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    simpa [Pi.inv_def] using h.inv_tendsto_atTop
  exact h2

/-- The design-measurable scale, equal to `2` where the design coin is `true` and `1` where it
is `false`. -/
def pScale (y : Omg) : ℝ := if y.1 then 2 else 1

/-- The disturbance sign, a function of the second coin. -/
def pSign (y : Omg) : ℝ := if y.2 then 1 else -1

/-- The row loading, `1` on the first moment row and `2` on the second. -/
def pRowc (r : Fin 2) : ℝ := ((r : ℕ) : ℝ) + 1

/-- The moment design `𝒜`, with two rows, one column and both entries equal to `1`. -/
def pA : Matrix (Fin 2) (Fin 1) ℝ := fun _ _ => 1

/-- The parameter `θ = 1`. -/
def pTh : Fin 1 → ℝ := fun _ => 1

/-- The moment vector: `𝒜θ` plus the rate times a random deviation. -/
noncomputable def pMh (n : ℕ) (r : Fin 2) (y : Omg) : ℝ :=
  1 + pB n * (pScale y * pSign y * pRowc r)

theorem pGram_apply : ((pA)ᵀ * pA) 0 0 = (2 : ℝ) := by
  simp [pA, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

/-- `𝒜'𝒜 = 2`. -/
theorem pGram_det : ((pA)ᵀ * pA).det = (2 : ℝ) := by
  rw [Matrix.det_fin_one, pGram_apply]

theorem pGram_unit : IsUnit ((pA)ᵀ * pA).det := by
  rw [pGram_det]
  exact isUnit_iff_ne_zero.2 two_ne_zero

/-- `(𝒜'𝒜)^{-1}` is the constant `1/2`. -/
theorem pGram_inv : ((pA)ᵀ * pA)⁻¹ = (fun _ _ => (2 : ℝ)⁻¹) := by
  refine Matrix.inv_eq_right_inv (Matrix.ext fun i j => ?_)
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  subst hi; subst hj
  show ∑ k : Fin 1, ((pA)ᵀ * pA) 0 k * (2 : ℝ)⁻¹ = (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
  rw [Fin.sum_univ_one, pGram_apply, Matrix.one_apply_eq]
  norm_num

theorem pGram_inv_apply (i j : Fin 1) : (((pA)ᵀ * pA)⁻¹) i j = (2 : ℝ)⁻¹ := by
  rw [pGram_inv]

/-- `(𝒜'𝒜)^{-1}𝒜' = (1/2, 1/2)`. -/
theorem pCoef (j : Fin 1) (r : Fin 2) : (((pA)ᵀ * pA)⁻¹ * (pA)ᵀ) j r = (2 : ℝ)⁻¹ := by
  rw [Matrix.mul_apply, Fin.sum_univ_one, pGram_inv_apply, Matrix.transpose_apply]
  simp [pA]

theorem pMulVec (r : Fin 2) : (pA *ᵥ pTh) r = (1 : ℝ) := by
  simp [pA, pTh, Matrix.mulVec, dotProduct]

theorem pSign_sq (y : Omg) : (pSign y) ^ 2 = 1 := by
  rw [pSign]; cases y.2 <;> norm_num

theorem pSign_abs (y : Omg) : |pSign y| = 1 := by
  rw [pSign]; cases y.2 <;> norm_num

theorem pScale_pos (y : Omg) : 0 < pScale y := by
  rw [pScale]; cases y.1 <;> norm_num

theorem pScale_le (y : Omg) : pScale y ≤ 2 := by
  rw [pScale]; cases y.1 <;> norm_num

theorem pRowc_pos (r : Fin 2) : 0 < pRowc r := by
  rw [pRowc]; positivity

theorem pRowc_le (r : Fin 2) : pRowc r ≤ 2 := by
  fin_cases r <;> norm_num [pRowc]

theorem pMeas (n : ℕ) (r : Fin 2) : AEMeasurable (pMh n r) Pw :=
  (measurable_of_countable _).aemeasurable

/-- The normalized deviation of moment row `r`, the product of the design scale, the disturbance
sign and the row loading. -/
theorem pDevEq (n : ℕ) (r : Fin 2) (y : Omg) :
    (pMh n r y - (pA *ᵥ pTh) r) / pB n = pScale y * pSign y * pRowc r := by
  have h : pMh n r y - (pA *ᵥ pTh) r = pB n * (pScale y * pSign y * pRowc r) := by
    rw [pMulVec r, pMh]; ring
  rw [h, mul_comm, mul_div_assoc, div_self (pB_pos n).ne', mul_one]

/-- The conditional second moment of row `r` is `(pScale ω)²(pRowc r)²`. -/
theorem pCondVar_eq (n : ℕ) (r : Fin 2) : ∀ᵐ ω ∂Pw,
    ∫⁻ y, ‖((pMh n r y - (pA *ᵥ pTh) r) / pB n) ^ 2‖ₑ ∂(condExpKernel Pw Dsig ω)
      = ‖(pScale ω ^ 2 * pRowc r ^ 2 : ℝ)‖ₑ := by
  have hfz : ∀ᵐ ω ∂Pw, ∀ᵐ y ∂(condExpKernel Pw Dsig ω), y.1 = ω.1 :=
    Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel Dsig_le Pw meas_fst
  filter_upwards [hfz] with ω hω
  have hEq : ∀ᵐ y ∂(condExpKernel Pw Dsig ω),
      ‖((pMh n r y - (pA *ᵥ pTh) r) / pB n) ^ 2‖ₑ = ‖(pScale ω ^ 2 * pRowc r ^ 2 : ℝ)‖ₑ := by
    filter_upwards [hω] with y hy
    have hsc : pScale y = pScale ω := by rw [pScale, pScale, hy]
    congr 1
    rw [pDevEq n r y, mul_pow, mul_pow, pSign_sq, mul_one, hsc]
  rw [lintegral_congr_ae hEq, lintegral_const]
  simp

/-- The conditional second-moment bound, at `Msq = ofReal 16`. -/
theorem pCondVar_le (n : ℕ) (r : Fin 2) : ∀ᵐ ω ∂Pw,
    ∫⁻ y, ‖((pMh n r y - (pA *ᵥ pTh) r) / pB n) ^ 2‖ₑ ∂(condExpKernel Pw Dsig ω)
      ≤ ENNReal.ofReal 16 := by
  filter_upwards [pCondVar_eq n r] with ω hω
  rw [hω]
  have h0 : (0 : ℝ) ≤ pScale ω ^ 2 * pRowc r ^ 2 := by positivity
  have h1 : pScale ω ^ 2 * pRowc r ^ 2 ≤ 16 := by
    have ha : pScale ω ^ 2 ≤ 4 := by nlinarith [pScale_pos ω, pScale_le ω]
    have hb : pRowc r ^ 2 ≤ 4 := by nlinarith [pRowc_pos r, pRowc_le r]
    nlinarith [sq_nonneg (pScale ω), sq_nonneg (pRowc r)]
  calc ‖(pScale ω ^ 2 * pRowc r ^ 2 : ℝ)‖ₑ = ENNReal.ofReal (pScale ω ^ 2 * pRowc r ^ 2) :=
        Real.enorm_eq_ofReal h0
    _ ≤ ENNReal.ofReal 16 := ENNReal.ofReal_le_ofReal h1

/-- `‖θ̂ − θ‖₁ = (3/2)(n+1)^{-1}(pScale y)` at every point. -/
theorem pStat (n : ℕ) (y : Omg) :
    ∑ j : Fin 1, |thetaHat pA (pMh n) j y - pTh j| = (3 / 2) * pB n * pScale y := by
  have h0 : pRowc 0 = 1 := by simp [pRowc]
  have h1 : pRowc 1 = 2 := by norm_num [pRowc]
  have hth : thetaHat pA (pMh n) 0 y = 1 + (3 / 2) * pB n * pScale y * pSign y := by
    simp only [thetaHat]
    rw [Fin.sum_univ_two, pCoef 0 0, pCoef 0 1]
    simp only [pMh]
    rw [h0, h1]
    ring
  have hpos : 0 < (3 / 2) * pB n * pScale y :=
    mul_pos (mul_pos (by norm_num) (pB_pos n)) (pScale_pos y)
  rw [Fin.sum_univ_one, hth]
  have hpt : pTh 0 = (1 : ℝ) := rfl
  rw [hpt, add_sub_cancel_left, abs_mul, pSign_abs, mul_one, abs_of_pos hpos]

/-- An example for the conditional first claim, with a proper `𝒟`, `ℙ_ω ≠ P`, an overidentified
nonsingular moment design and a random statistic of the exact order of the rate. -/
theorem thetaHat_sub_isBigOp_cond_witness :
    (∃ B : Set Omg, MeasurableSet B ∧ ¬ MeasurableSet[Dsig] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dsig ω = Pw)
    ∧ Pw {y : Omg | y.1 = true} = 2⁻¹
    ∧ ((pA)ᵀ * pA).det = (2 : ℝ)
    ∧ (∀ n : ℕ, 0 < pB n) ∧ Tendsto pB atTop (𝓝 0)
    ∧ (∀ (n : ℕ) (y : Omg),
        ∑ j : Fin 1, |thetaHat pA (pMh n) j y - pTh j| = (3 / 2) * pB n * pScale y)
    ∧ IsBigOp Pw (fun n y => ∑ j : Fin 1, |thetaHat pA (pMh n) j y - pTh j|) pB := by
  refine ⟨Dsig_proper, freeze_witness.2.2.2.2, Pw_fst true, pGram_det, pB_pos, pB_tendsto,
    pStat, ?_⟩
  refine thetaHat_sub_isBigOp_cond (𝒟 := Dsig) (Rw := fun _ => Fin 2) (Cl := fun _ => Fin 1)
    Dsig_le Pw (fun _ => pA) (fun _ => pGram_unit) (fun _ => pTh) pMh pB_pos
    (fun n r => pMeas n r) (Msq := ENNReal.ofReal 16) ENNReal.ofReal_ne_top
    (fun n r => pCondVar_le n r) (Nrow := 2) (fun _ => by simp) (Ncol := 1) (fun _ => by simp)
    (Lam := (2 : ℝ)⁻¹) (by norm_num) ?_
  intro n j r
  rw [pCoef j r]
  norm_num

end PluginCondVarWitness

end CondVarDecond

end Plugin

end Multiway
