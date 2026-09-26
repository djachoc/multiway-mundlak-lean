import Multiway.ResidualBridge
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The diagnostic coefficient

This file formalizes Lemma SM.B.4 (The diagnostic coefficient). With `Z := P_[Δ]X`,
`C₀ := [X, ι_n]`, `Z̃ := M_{C₀}Z` and `Z̃'Z̃ ≻ 0`, the OLS coefficient `π̂` on `Z` in the
regression of `y` on `(X, Z, ι_n)` satisfies `π̂ = (Z'M_{C₀}Z)⁻¹ Z'M_{C₀}y`,
`π̂ - π = (Z̃'Z̃)⁻¹ Z̃'u` and `Var(π̂ | X, 𝒪) = (Z̃'Z̃)⁻¹ Z̃'Ω_u Z̃ (Z̃'Z̃)⁻¹`. The Frisch–Waugh–Lovell
step is proved from the normal equations (`IsOLSFit`). The annihilator `M_{C₀}` is characterized
by `IsAnnihilator`, the design is non-random, and the conditional variance is expressed as a
conditional second moment together with a conditional mean-zero statement.

## Main results

* `piHat_eq`, `piHat_sub_eq`: the first two displays.
* `condExp_piHat_sub_mul`, `condExp_piHat_sub_eq_zero`: the third display.
* `isOLSFit_le_sumSq`: an `IsOLSFit` triple minimizes the sum of squared residuals.
* `isAnnihilator_annihilatorMatrix`: `IsAnnihilator` holds for the residual-maker matrix.
-/

namespace Multiway
namespace PiHat

open Matrix MeasureTheory

/-! ### The annihilator `M_{C₀}` -/

section Annihilator

variable {O K : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]

/-- `M_{C₀}` is the annihilator of `C₀ = [X, ι_n]`. It is symmetric, maps `X` and `ι_n` to zero
and fixes every vector of `col(C₀)ᗮ`, and these properties determine it uniquely. -/
structure IsAnnihilator (M : Matrix O O ℝ) (X : Matrix O K ℝ) (ιn : O → ℝ) : Prop where
  /-- `M_{C₀}` is symmetric. -/
  symm : Mᵀ = M
  /-- `M_{C₀}X = 0`. -/
  regressors : M * X = 0
  /-- `M_{C₀}ι_n = 0`. -/
  const : M *ᵥ ιn = 0
  /-- `M_{C₀}` fixes every vector orthogonal to `col(C₀)`. -/
  fixes : ∀ v : O → ℝ, Xᵀ *ᵥ v = 0 → ιn ⬝ᵥ v = 0 → M *ᵥ v = v

variable {M : Matrix O O ℝ} {X : Matrix O K ℝ} {ιn : O → ℝ}

omit [Fintype K] [DecidableEq K] in
/-- Two square matrices that agree on every vector are equal. -/
theorem ext_of_mulVec {A B : Matrix O O ℝ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext o o'
  simpa [Matrix.mulVec_single] using congrFun (h (Pi.single o' 1)) o

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- `X'M_{C₀} = 0`, the transposed form of `M_{C₀}X = 0`. -/
theorem IsAnnihilator.transpose_regressors (h : IsAnnihilator M X ιn) : Xᵀ * M = 0 := by
  have h2 : (M * X)ᵀ = 0 := by rw [h.regressors]; exact Matrix.transpose_zero
  rw [Matrix.transpose_mul, h.symm] at h2
  exact h2

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- `ι_n'M_{C₀} = 0`, the transposed form of `M_{C₀}ι_n = 0`. -/
theorem IsAnnihilator.vecMul_const (h : IsAnnihilator M X ιn) : ιn ᵥ* M = 0 := by
  rw [← Matrix.mulVec_transpose, h.symm, h.const]

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- Every vector in the range of `M_{C₀}` is orthogonal to `col(X)`. -/
theorem IsAnnihilator.orth_regressors (h : IsAnnihilator M X ιn) (v : O → ℝ) :
    Xᵀ *ᵥ (M *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, h.transpose_regressors, Matrix.zero_mulVec]

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- Every vector in the range of `M_{C₀}` is orthogonal to `ι_n`. -/
theorem IsAnnihilator.orth_const (h : IsAnnihilator M X ιn) (v : O → ℝ) :
    ιn ⬝ᵥ (M *ᵥ v) = 0 := by
  rw [Matrix.dotProduct_mulVec, h.vecMul_const, zero_dotProduct]

omit [Fintype K] [DecidableEq K] in
/-- `M_{C₀}` is idempotent. -/
theorem IsAnnihilator.mul_self (h : IsAnnihilator M X ιn) : M * M = M := by
  refine ext_of_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec]
  exact h.fixes (M *ᵥ v) (h.orth_regressors v) (h.orth_const v)

omit [Fintype K] [DecidableEq K] in
/-- `Z'M_{C₀}Z = Z̃'Z̃`. -/
theorem gram_eq (h : IsAnnihilator M X ιn) (Z : Matrix O K ℝ) :
    (M * Z)ᵀ * (M * Z) = Zᵀ * M * Z := by
  rw [Matrix.transpose_mul, h.symm, Matrix.mul_assoc, ← Matrix.mul_assoc M M Z, h.mul_self,
    ← Matrix.mul_assoc]

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- `Z'M_{C₀}u = Z̃'u`. -/
theorem transpose_zTilde_mulVec (h : IsAnnihilator M X ιn) (Z : Matrix O K ℝ) (v : O → ℝ) :
    (M * Z)ᵀ *ᵥ v = Zᵀ *ᵥ (M *ᵥ v) := by
  rw [Matrix.transpose_mul, h.symm, ← Matrix.mulVec_mulVec]

end Annihilator

/-! ### The OLS fit -/

section OLS

variable {O K : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]

/-- The residual `y - Xb - Zp - sι_n`. -/
def olsResid (X Z : Matrix O K ℝ) (ιn y : O → ℝ) (b p : K → ℝ) (s : ℝ) : O → ℝ :=
  y - X *ᵥ b - Z *ᵥ p - s • ιn

/-- The OLS fit of `y` on `(X, Z, ι_n)`, defined by its normal equations. -/
structure IsOLSFit (X Z : Matrix O K ℝ) (ιn y : O → ℝ) (b p : K → ℝ) (s : ℝ) : Prop where
  /-- `X'r = 0`. -/
  orthRegressors : Xᵀ *ᵥ olsResid X Z ιn y b p s = 0
  /-- `Z'r = 0`. -/
  orthControls : Zᵀ *ᵥ olsResid X Z ιn y b p s = 0
  /-- `ι_n'r = 0`. -/
  orthConst : ιn ⬝ᵥ olsResid X Z ιn y b p s = 0

variable {X Z : Matrix O K ℝ} {ιn y : O → ℝ} {b p : K → ℝ} {s : ℝ}

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
theorem dotProduct_self_nonneg (w : O → ℝ) : 0 ≤ w ⬝ᵥ w :=
  Finset.sum_nonneg fun o _ => mul_self_nonneg (w o)

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- Adding to the residual a vector orthogonal to it can only increase the sum of squares. -/
theorem sumSq_le_of_orth {r w : O → ℝ} (h : r ⬝ᵥ w = 0) : r ⬝ᵥ r ≤ (r + w) ⬝ᵥ (r + w) := by
  have hwr : w ⬝ᵥ r = 0 := by rw [dotProduct_comm]; exact h
  rw [add_dotProduct, dotProduct_add, dotProduct_add, h, hwr]
  have := dotProduct_self_nonneg w
  linarith

omit [Fintype O] [DecidableEq O] [DecidableEq K] in
/-- The decomposition `y = Xb + Zp + sι_n + r`. -/
theorem eq_add_olsResid (X Z : Matrix O K ℝ) (ιn y : O → ℝ) (b p : K → ℝ) (s : ℝ) :
    y = X *ᵥ b + Z *ᵥ p + s • ιn + olsResid X Z ιn y b p s := by
  funext o
  simp only [olsResid, Pi.add_apply, Pi.sub_apply]
  ring

omit [DecidableEq O] [DecidableEq K] in
/-- An `IsOLSFit` triple minimizes the sum of squared residuals over every competing
`(b', p', s')`. -/
theorem isOLSFit_le_sumSq (h : IsOLSFit X Z ιn y b p s) (b' p' : K → ℝ) (s' : ℝ) :
    olsResid X Z ιn y b p s ⬝ᵥ olsResid X Z ιn y b p s
      ≤ olsResid X Z ιn y b' p' s' ⬝ᵥ olsResid X Z ιn y b' p' s' := by
  set r := olsResid X Z ιn y b p s with hrdef
  set w := X *ᵥ (b - b') + Z *ᵥ (p - p') + (s - s') • ιn with hwdef
  have hsum : olsResid X Z ιn y b' p' s' = r + w := by
    funext o
    simp only [hrdef, hwdef, olsResid, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, sub_smul]
    ring
  have hX : r ⬝ᵥ (X *ᵥ (b - b')) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h.orthRegressors, zero_dotProduct]
  have hZ : r ⬝ᵥ (Z *ᵥ (p - p')) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h.orthControls, zero_dotProduct]
  have hC : r ⬝ᵥ ((s - s') • ιn) = 0 := by
    rw [dotProduct_smul, dotProduct_comm, h.orthConst, smul_zero]
  have hrw : r ⬝ᵥ w = 0 := by
    rw [hwdef, dotProduct_add, dotProduct_add, hX, hZ, hC, add_zero, add_zero]
  rw [hsum]
  exact sumSq_le_of_orth hrw

end OLS

/-! ### The first two displays -/

section Displays

variable {O K : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable {M : Matrix O O ℝ} {X Z : Matrix O K ℝ} {ιn y : O → ℝ} {b p : K → ℝ} {s : ℝ}

omit [DecidableEq O] [DecidableEq K] in
/-- The Frisch–Waugh–Lovell step in normal-equation form: `(Z'M_{C₀}Z)π̂ = Z'M_{C₀}y`. -/
theorem normalEquation (hM : IsAnnihilator M X ιn) (hfit : IsOLSFit X Z ιn y b p s) :
    (Zᵀ * M * Z) *ᵥ p = (Zᵀ * M) *ᵥ y := by
  have hfix : M *ᵥ olsResid X Z ιn y b p s = olsResid X Z ιn y b p s :=
    hM.fixes _ hfit.orthRegressors hfit.orthConst
  have hy : y = X *ᵥ b + Z *ᵥ p + s • ιn + olsResid X Z ιn y b p s :=
    eq_add_olsResid X Z ιn y b p s
  have h1 : M *ᵥ (X *ᵥ b) = 0 := by
    rw [Matrix.mulVec_mulVec, hM.regressors, Matrix.zero_mulVec]
  have h2 : M *ᵥ (s • ιn) = 0 := by
    rw [Matrix.mulVec_smul, hM.const, smul_zero]
  have key : M *ᵥ y = M *ᵥ (Z *ᵥ p) + olsResid X Z ιn y b p s := by
    conv_lhs => rw [hy]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, hfix, zero_add,
      add_zero]
  calc (Zᵀ * M * Z) *ᵥ p = Zᵀ *ᵥ (M *ᵥ (Z *ᵥ p)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = Zᵀ *ᵥ (M *ᵥ (Z *ᵥ p)) + Zᵀ *ᵥ olsResid X Z ιn y b p s := by
        rw [hfit.orthControls, add_zero]
    _ = Zᵀ *ᵥ (M *ᵥ y) := by rw [← Matrix.mulVec_add, ← key]
    _ = (Zᵀ * M) *ᵥ y := by rw [Matrix.mulVec_mulVec]

/-- `Z̃'Z̃ ≻ 0` makes `Z'M_{C₀}Z` invertible. -/
theorem isUnit_det (hM : IsAnnihilator M X ιn) (hPD : ((M * Z)ᵀ * (M * Z)).PosDef) :
    IsUnit (Zᵀ * M * Z).det := by
  have h := hPD.det_pos
  rw [gram_eq hM Z] at h
  exact Ne.isUnit h.ne'

/-- **Lemma SM.B.4**, first display: `π̂ = (Z'M_{C₀}Z)⁻¹ Z'M_{C₀}y` for every OLS fit. -/
theorem piHat_eq (hM : IsAnnihilator M X ιn) (hfit : IsOLSFit X Z ιn y b p s)
    (hPD : ((M * Z)ᵀ * (M * Z)).PosDef) :
    p = (Zᵀ * M * Z)⁻¹ *ᵥ ((Zᵀ * M) *ᵥ y) := by
  rw [← normalEquation hM hfit, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_det hM hPD), Matrix.one_mulVec]

/-- **Lemma SM.B.4**, second display: `π̂ - π = (Z̃'Z̃)⁻¹ Z̃'u` under the model equation
`y = Xβ + Zπ + u`. -/
theorem piHat_sub_eq {β π : K → ℝ} {u : O → ℝ} (hM : IsAnnihilator M X ιn)
    (hfit : IsOLSFit X Z ιn y b p s) (hPD : ((M * Z)ᵀ * (M * Z)).PosDef)
    (hmodel : y = X *ᵥ β + Z *ᵥ π + u) :
    p - π = ((M * Z)ᵀ * (M * Z))⁻¹ *ᵥ ((M * Z)ᵀ *ᵥ u) := by
  have hrhs : (Zᵀ * M) *ᵥ y = (Zᵀ * M * Z) *ᵥ π + (Zᵀ * M) *ᵥ u := by
    rw [hmodel, Matrix.mulVec_add, Matrix.mulVec_add]
    have h1 : (Zᵀ * M) *ᵥ (X *ᵥ β) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hM.regressors, Matrix.mul_zero,
        Matrix.zero_mulVec]
    have h2 : (Zᵀ * M) *ᵥ (Z *ᵥ π) = (Zᵀ * M * Z) *ᵥ π := by rw [Matrix.mulVec_mulVec]
    rw [h1, h2, zero_add]
  have hsub : (Zᵀ * M * Z) *ᵥ (p - π) = (Zᵀ * M) *ᵥ u := by
    rw [Matrix.mulVec_sub, normalEquation hM hfit, hrhs]
    abel
  have hfinal : p - π = (Zᵀ * M * Z)⁻¹ *ᵥ ((Zᵀ * M) *ᵥ u) := by
    rw [← hsub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det hM hPD),
      Matrix.one_mulVec]
  rw [hfinal, gram_eq hM Z, transpose_zTilde_mulVec hM Z u]
  congr 1
  rw [Matrix.mulVec_mulVec]

/-- The second display in the form `π̂ - π = A u` with `A := (Z̃'Z̃)⁻¹Z̃'`. -/
theorem piHat_sub_eq_mulVec {β π : K → ℝ} {u : O → ℝ} (hM : IsAnnihilator M X ιn)
    (hfit : IsOLSFit X Z ιn y b p s) (hPD : ((M * Z)ᵀ * (M * Z)).PosDef)
    (hmodel : y = X *ᵥ β + Z *ᵥ π + u) :
    p - π = (((M * Z)ᵀ * (M * Z))⁻¹ * (M * Z)ᵀ) *ᵥ u := by
  rw [piHat_sub_eq hM hfit hPD hmodel, Matrix.mulVec_mulVec]

end Displays

/-! ### The third display -/

section Conditional

variable {O K : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
-- `𝒟` precedes `mΩ` so that instance synthesis uses the ambient `mΩ`.
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- The product of two linear combinations as a double sum. -/
theorem mul_sum_eq_double_sum (c d : O → ℝ) (v : O → Ω → ℝ) :
    (fun ω => (∑ o : O, c o * v o ω) * (∑ o' : O, d o' * v o' ω))
      = ∑ o : O, ∑ o' : O, (fun ω => (c o * d o') * (v o ω * v o' ω)) := by
  funext ω
  simp only [Finset.sum_apply]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- `E[(∑_o c_o u_o)(∑_{o'} d_{o'} u_{o'}) | 𝒟] = ∑_o ∑_{o'} c_o d_{o'} Ω_u(o, o')` when
`E[u_o u_{o'} | 𝒟] = Ω_u(o, o')`. -/
theorem condExp_bilinear_linearCombination {c d : O → ℝ} {v : O → Ω → ℝ} {Om : O → O → Ω → ℝ}
    (hint : ∀ o o', Integrable (fun ω => v o ω * v o' ω) μ)
    (hOm : ∀ o o', μ[fun ω => v o ω * v o' ω | 𝒟] =ᵐ[μ] Om o o') :
    μ[fun ω => (∑ o : O, c o * v o ω) * (∑ o' : O, d o' * v o' ω) | 𝒟]
      =ᵐ[μ] fun ω => ∑ o : O, ∑ o' : O, (c o * d o') * Om o o' ω := by
  classical
  rw [mul_sum_eq_double_sum c d v]
  have hintc : ∀ o o' : O, Integrable (fun ω => (c o * d o') * (v o ω * v o' ω)) μ :=
    fun o o' => (hint o o').const_mul _
  have h1 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
    (f := fun o : O => ∑ o' : O, (fun ω => (c o * d o') * (v o ω * v o' ω)))
    (fun o _ => integrable_finsetSum' _ fun o' _ => hintc o o') 𝒟
  have h2 : ∀ᵐ ω ∂μ, ∀ o : O,
      μ[∑ o' : O, (fun ω => (c o * d o') * (v o ω * v o' ω)) | 𝒟] ω
        = ∑ o' : O, μ[fun ω => (c o * d o') * (v o ω * v o' ω) | 𝒟] ω := by
    refine ae_all_iff.2 fun o => ?_
    filter_upwards [condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
      (fun o' _ => hintc o o') 𝒟] with ω hω
    rw [hω, Finset.sum_apply]
  have hpull : ∀ o o' : O,
      μ[fun ω => (c o * d o') * (v o ω * v o' ω) | 𝒟]
        =ᵐ[μ] fun ω => (c o * d o') * μ[fun ω => v o ω * v o' ω | 𝒟] ω :=
    fun o o' => condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_const
      (hintc o o') (hint o o')
  have h3 : ∀ᵐ ω ∂μ, ∀ q : O × O,
      μ[fun ω => (c q.1 * d q.2) * (v q.1 ω * v q.2 ω) | 𝒟] ω
        = (c q.1 * d q.2) * Om q.1 q.2 ω := by
    refine ae_all_iff.2 fun q => ?_
    filter_upwards [hpull q.1 q.2, hOm q.1 q.2] with ω ha hb
    rw [ha, hb]
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, Finset.sum_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [e2 o]
  exact Finset.sum_congr rfl fun o' _ => e3 (o, o')

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- The conditional mean of a linear combination with vanishing conditional means. -/
theorem condExp_linearCombination_eq_zero {c : O → ℝ} {v : O → Ω → ℝ}
    (hint : ∀ o, Integrable (v o) μ) (hmean : ∀ o, μ[v o | 𝒟] =ᵐ[μ] 0) :
    μ[fun ω => ∑ o : O, c o * v o ω | 𝒟] =ᵐ[μ] 0 := by
  classical
  have hrw : (fun ω => ∑ o : O, c o * v o ω) = ∑ o : O, (fun ω => c o * v o ω) := by
    funext ω; simp only [Finset.sum_apply]
  rw [hrw]
  have h1 := condExp_finsetSum (μ := μ) (s := (Finset.univ : Finset O))
    (f := fun o : O => (fun ω => c o * v o ω)) (fun o _ => (hint o).const_mul _) 𝒟
  have hpull : ∀ o : O, μ[fun ω => c o * v o ω | 𝒟] =ᵐ[μ] fun ω => c o * μ[v o | 𝒟] ω :=
    fun o => condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_const
      ((hint o).const_mul _) (hint o)
  have h2 : ∀ᵐ ω ∂μ, ∀ o : O, μ[fun ω => c o * v o ω | 𝒟] ω = 0 := by
    refine ae_all_iff.2 fun o => ?_
    filter_upwards [hpull o, hmean o] with ω ha hb
    rw [ha, hb]
    simp
  filter_upwards [h1, h2] with ω e1 e2
  rw [e1, Finset.sum_apply, Finset.sum_congr rfl fun o _ => e2 o]
  simp

omit [DecidableEq O] [Fintype K] [DecidableEq K] in
/-- The double sum of the third display written as a matrix product. -/
theorem double_sum_eq_conj (A : Matrix K O ℝ) (W : Matrix O O ℝ) (k l : K) :
    ∑ o : O, ∑ o' : O, (A k o * A l o') * W o o' = (A * W * Aᵀ) k l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => by ring

variable {M : Matrix O O ℝ} {Z : Matrix O K ℝ}

omit [DecidableEq O] in
/-- `A' = Z̃(Z̃'Z̃)⁻¹` for `A = (Z̃'Z̃)⁻¹Z̃'`. -/
theorem transpose_score (M : Matrix O O ℝ) (Z : Matrix O K ℝ) :
    (((M * Z)ᵀ * (M * Z))⁻¹ * (M * Z)ᵀ)ᵀ = (M * Z) * ((M * Z)ᵀ * (M * Z))⁻¹ := by
  have hGsymm : ((M * Z)ᵀ * (M * Z))ᵀ = (M * Z)ᵀ * (M * Z) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, hGsymm]

omit [DecidableEq O] in
/-- **Lemma SM.B.4**, third display, entry by entry:
`E[(π̂ - π)(π̂ - π)' | 𝒟] = (Z̃'Z̃)⁻¹ Z̃'Ω_u Z̃ (Z̃'Z̃)⁻¹`, where `Om` is the conditional second-moment
matrix of `u`. -/
theorem condExp_piHat_sub_mul {π : K → ℝ} {pv : Ω → K → ℝ} {u : Ω → O → ℝ}
    {Om : Ω → Matrix O O ℝ}
    (hstep : ∀ ω, pv ω - π = (((M * Z)ᵀ * (M * Z))⁻¹ * (M * Z)ᵀ) *ᵥ u ω)
    (hint : ∀ o o', Integrable (fun ω => u ω o * u ω o') μ)
    (hOm : ∀ o o', μ[fun ω => u ω o * u ω o' | 𝒟] =ᵐ[μ] fun ω => Om ω o o') (k l : K) :
    μ[fun ω => (pv ω k - π k) * (pv ω l - π l) | 𝒟]
      =ᵐ[μ] fun ω =>
        (((M * Z)ᵀ * (M * Z))⁻¹ * (M * Z)ᵀ * Om ω * (M * Z) * ((M * Z)ᵀ * (M * Z))⁻¹) k l := by
  classical
  set A : Matrix K O ℝ := ((M * Z)ᵀ * (M * Z))⁻¹ * (M * Z)ᵀ with hA
  have hcoord : ∀ (ω : Ω) (j : K), pv ω j - π j = ∑ o : O, A j o * u ω o := by
    intro ω j
    have h := congrFun (hstep ω) j
    simpa [Matrix.mulVec, dotProduct] using h
  have hfun : (fun ω => (pv ω k - π k) * (pv ω l - π l))
      = fun ω => (∑ o : O, A k o * u ω o) * (∑ o' : O, A l o' * u ω o') := by
    funext ω
    rw [hcoord ω k, hcoord ω l]
  rw [hfun]
  refine (condExp_bilinear_linearCombination 𝒟 (c := fun o => A k o) (d := fun o => A l o)
    (v := fun o ω => u ω o) (Om := fun o o' ω => Om ω o o') hint hOm).trans ?_
  filter_upwards with ω
  rw [double_sum_eq_conj A (Om ω) k l, transpose_score M Z, hA]
  simp only [Matrix.mul_assoc]

omit [DecidableEq O] in
/-- `E[π̂ - π | 𝒟] = 0` when `E[u_o | 𝒟] = 0` for every `o`, so the conditional second moment of
`condExp_piHat_sub_mul` is the conditional variance. -/
theorem condExp_piHat_sub_eq_zero {π : K → ℝ} {pv : Ω → K → ℝ} {u : Ω → O → ℝ}
    (hstep : ∀ ω, pv ω - π = (((M * Z)ᵀ * (M * Z))⁻¹ * (M * Z)ᵀ) *ᵥ u ω)
    (hint : ∀ o, Integrable (fun ω => u ω o) μ)
    (hmean : ∀ o, μ[fun ω => u ω o | 𝒟] =ᵐ[μ] 0) (k : K) :
    μ[fun ω => pv ω k - π k | 𝒟] =ᵐ[μ] 0 := by
  classical
  set A : Matrix K O ℝ := ((M * Z)ᵀ * (M * Z))⁻¹ * (M * Z)ᵀ with hA
  have hfun : (fun ω => pv ω k - π k) = fun ω => ∑ o : O, A k o * u ω o := by
    funext ω
    have h := congrFun (hstep ω) k
    simpa [Matrix.mulVec, dotProduct] using h
  rw [hfun]
  exact condExp_linearCombination_eq_zero 𝒟 hint hmean

end Conditional

/-! ### `M_{C₀}` as a residual-maker matrix

`ResidualBridge.residualMatrix S x` is the orthogonal projector onto `(S ⊔ col(x))ᗮ`; with `S`
the line through `ι_n` and `x` the columns of `X` it is `M_{C₀}`. -/

section Bridge

variable {O K : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]

open scoped RealInnerProductSpace

/-- The columns of `X`, as vectors of `ℝⁿ`. -/
noncomputable def regressorColumns (X : Matrix O K ℝ) (k : K) : EuclideanSpace ℝ O :=
  WithLp.toLp 2 fun o => X o k

/-- The line through `ι_n`. -/
noncomputable def constLine (ιn : O → ℝ) : Submodule ℝ (EuclideanSpace ℝ O) :=
  Submodule.span ℝ {(WithLp.toLp 2 ιn : EuclideanSpace ℝ O)}

/-- `M_{C₀}` as a residual-maker matrix. -/
noncomputable def annihilatorMatrix (X : Matrix O K ℝ) (ιn : O → ℝ) : Matrix O O ℝ :=
  ResidualBridge.residualMatrix (constLine ιn) (regressorColumns X)

omit [DecidableEq O] in
/-- A vector orthogonal to every member of a spanning family is orthogonal to their span. -/
theorem mem_orthogonal_span_range {ι : Type*} (x : ι → EuclideanSpace ℝ O)
    (v : EuclideanSpace ℝ O) (h : ∀ k, ⟪x k, v⟫ = 0) :
    v ∈ (Submodule.span ℝ (Set.range x))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact h k
  | zero => simp
  | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [real_inner_smul_left, ha, mul_zero]

omit [Fintype K] [DecidableEq K] in
/-- `IsAnnihilator` holds for `annihilatorMatrix`, for arbitrary `O`, `X` and `ιn`. -/
theorem isAnnihilator_annihilatorMatrix (X : Matrix O K ℝ) (ιn : O → ℝ) :
    IsAnnihilator (annihilatorMatrix X ιn) X ιn := by
  classical
  have hcol : ∀ (v : O → ℝ),
      annihilatorMatrix X ιn *ᵥ v
        = WithLp.ofLp (residualMaker (constLine ιn) (regressorColumns X)
            (WithLp.toLp 2 v : EuclideanSpace ℝ O)) := by
    intro v
    exact ResidualBridge.residualMatrix_mulVec _ _ (WithLp.toLp 2 v)
  refine ⟨ResidualBridge.residualMatrix_transpose _ _, ?_, ?_, ?_⟩
  ·
    exact ResidualBridge.residualMatrix_mul_eq_zero (constLine ιn) (regressorColumns X) X
      fun k => regressor_mem_fittedSpace k
  · rw [hcol]
    have hmem : (WithLp.toLp 2 ιn : EuclideanSpace ℝ O) ∈ constLine ιn :=
      Submodule.mem_span_singleton_self _
    rw [residualMaker_apply_of_mem_fixedEffects hmem]
    rfl
  ·
    intro v hX hι
    have hιinner : ⟪(WithLp.toLp 2 ιn : EuclideanSpace ℝ O),
        (WithLp.toLp 2 v : EuclideanSpace ℝ O)⟫ = ιn ⬝ᵥ v := by
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    have hXinner : ∀ k, ⟪regressorColumns X k, (WithLp.toLp 2 v : EuclideanSpace ℝ O)⟫
        = (Xᵀ *ᵥ v) k := by
      intro k
      simp [regressorColumns, PiLp.inner_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, mul_comm]
    have hS : ∀ w ∈ constLine ιn, ⟪w, (WithLp.toLp 2 v : EuclideanSpace ℝ O)⟫ = 0 := by
      intro w hw
      rw [constLine, Submodule.mem_span_singleton] at hw
      obtain ⟨c, rfl⟩ := hw
      rw [real_inner_smul_left, hιinner, hι, mul_zero]
    exact ResidualBridge.residualMatrix_mulVec_of_orthogonal (constLine ιn)
      (regressorColumns X) (v := (WithLp.toLp 2 v : EuclideanSpace ℝ O)) hS
      fun k => by simp [hXinner k, hX]

end Bridge

/-! ### A worked example

`O = Fin 3`, `K = Fin 1`, `ι_n = (1, 1, 1)'`, `X = (1, 1, -2)'`, `Z = (1, 0, 0)'`, so that
`Z̃ = (1/2, -1/2, 0)'` and `Z̃'Z̃ = 1/2 ≻ 0`. With `y = (2, 1, 1)'` the fit is exact at `b = 0`,
`π̂ = 1`, `s = 1`, and the model equation holds with `β = 0`, `π = 0`, `u = y`. -/

section Witness

/-- The regressor column `(1, 1, -2)'`. -/
noncomputable def witX : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun o _ => ![1, 1, -2] o

/-- The column `Z = (1, 0, 0)'` of the example. -/
noncomputable def witZ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun o _ => ![1, 0, 0] o

/-- The vector of ones. -/
noncomputable def witIota : Fin 3 → ℝ := ![1, 1, 1]

/-- `M_{C₀}` for the example design. -/
noncomputable def witM : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2, -1/2, 0; -1/2, 1/2, 0; 0, 0, 0]

/-- The outcome, `(2, 1, 1)' = Z + ι_n`. -/
noncomputable def witY : Fin 3 → ℝ := ![2, 1, 1]

/-- The disturbance, equal to `y` because `β = 0` and `π = 0`. -/
noncomputable def witU : Fin 3 → ℝ := ![2, 1, 1]

/-- `π̂ = 1`. -/
noncomputable def witP : Fin 1 → ℝ := fun _ => 1

/-- The zero coefficient vector, used for `b`, for `β` and for `π`. -/
noncomputable def witZeroK : Fin 1 → ℝ := fun _ => 0

theorem witM_isAnnihilator : IsAnnihilator witM witX witIota := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [witM, Matrix.transpose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witM, witX, Matrix.mul_apply, Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      norm_num [witM, witIota, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro v hX hι
    have e1 := congrFun hX 0
    have e2 := hι
    simp [witX, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply] at e1
    simp [witIota, dotProduct, Fin.sum_univ_three] at e2
    funext i
    fin_cases i <;>
      simp [witM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> linarith

theorem witM_isOLSFit : IsOLSFit witX witZ witIota witY witZeroK witP 1 := by
  have hres : olsResid witX witZ witIota witY witZeroK witP 1 = 0 := by
    funext i
    fin_cases i <;>
      norm_num [olsResid, witX, witZ, witIota, witY, witP, witZeroK, Matrix.mulVec, dotProduct,
        Fin.sum_univ_one, Matrix.vecHead, Matrix.vecTail]
  refine ⟨?_, ?_, ?_⟩ <;> rw [hres] <;> simp

theorem witM_posDef : ((witM * witZ)ᵀ * (witM * witZ)).PosDef := by
  have hval : (witM * witZ)ᵀ * (witM * witZ) = Matrix.of fun (_ _ : Fin 1) => (1 : ℝ)/2 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [witM, witZ, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      Fin.sum_univ_one, Matrix.vecHead, Matrix.vecTail]
  rw [hval]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.conjTranspose_apply]
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro h
      exact hx (by funext i; fin_cases i; simpa using h)
    have hpos : 0 < x 0 * x 0 := mul_self_pos.mpr hx0
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.star_apply, star_trivial,
      Matrix.of_apply]
    nlinarith

/-- The first display holds at the example. -/
theorem piHat_eq_witness :
    witP = (witZᵀ * witM * witZ)⁻¹ *ᵥ ((witZᵀ * witM) *ᵥ witY) :=
  piHat_eq witM_isAnnihilator witM_isOLSFit witM_posDef

/-- The model equation `y = Xβ + Zπ + u` at `β = 0`, `π = 0` and `u = y`. -/
theorem witM_model : witY = witX *ᵥ witZeroK + witZ *ᵥ witZeroK + witU := by
  funext i
  fin_cases i <;>
    norm_num [witX, witZ, witY, witU, witZeroK, Matrix.mulVec, dotProduct, Fin.sum_univ_one]

/-- The second display holds at the example. -/
theorem piHat_sub_eq_witness :
    witP - witZeroK
      = ((witM * witZ)ᵀ * (witM * witZ))⁻¹ *ᵥ ((witM * witZ)ᵀ *ᵥ witU) :=
  piHat_sub_eq witM_isAnnihilator witM_isOLSFit witM_posDef witM_model

/-- The second display in the `A`-form at the example. -/
theorem piHat_sub_eq_mulVec_witness (ω : Unit) :
    (fun _ : Unit => witP) ω - witZeroK
      = (((witM * witZ)ᵀ * (witM * witZ))⁻¹ * (witM * witZ)ᵀ) *ᵥ (fun _ : Unit => witU) ω :=
  piHat_sub_eq_mulVec witM_isAnnihilator witM_isOLSFit witM_posDef witM_model

/-- The third display holds at the example, with `Ω = Unit`, `μ = dirac ()`, `𝒟 = ⊥` and
`Ω_u = uu'`. -/
theorem condExp_piHat_sub_mul_witness (k l : Fin 1) :
    (Measure.dirac ())[fun ω : Unit =>
        ((fun _ : Unit => witP) ω k - witZeroK k)
          * ((fun _ : Unit => witP) ω l - witZeroK l) | (⊥ : MeasurableSpace Unit)]
      =ᵐ[Measure.dirac ()] fun ω : Unit =>
        (((witM * witZ)ᵀ * (witM * witZ))⁻¹ * (witM * witZ)ᵀ
            * (fun _ : Unit => Matrix.of fun o o' => witU o * witU o') ω
            * (witM * witZ) * ((witM * witZ)ᵀ * (witM * witZ))⁻¹) k l :=
  condExp_piHat_sub_mul (⊥ : MeasurableSpace Unit) piHat_sub_eq_mulVec_witness
    (fun _ _ => integrable_const _)
    (fun _ _ => by rw [condExp_const bot_le]; exact Filter.EventuallyEq.rfl) k l

/-- The conditional mean-zero statement holds at the example with `u ≡ 0`. -/
theorem condExp_piHat_sub_eq_zero_witness (k : Fin 1) :
    (Measure.dirac ())[fun ω : Unit =>
        (fun _ : Unit => witZeroK) ω k - witZeroK k
        | (⊥ : MeasurableSpace Unit)] =ᵐ[Measure.dirac ()] 0 := by
  refine condExp_piHat_sub_eq_zero (M := witM) (Z := witZ) (⊥ : MeasurableSpace Unit)
    (u := fun _ _ => (0 : ℝ)) ?_ (fun _ => integrable_const _) ?_ k
  · intro ω
    funext j
    simp [Matrix.mulVec, dotProduct]
  · intro o
    rw [condExp_const (μ := Measure.dirac ()) (m := (⊥ : MeasurableSpace Unit)) bot_le (0 : ℝ)]
    exact Filter.EventuallyEq.rfl

end Witness

end PiHat
end Multiway
