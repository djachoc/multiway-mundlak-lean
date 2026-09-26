import Multiway.Cgm
import Multiway.Quadform
import Multiway.ResidualBridge
import Multiway.PrimitiveDesign
import Multiway.Vhat

/-!
# Clustering on absorbed dimensions

This file formalizes Theorem 10 of the paper (Clustering on absorbed dimensions): when each
maintained clustering dimension coincides with a fixed-effect dimension and `σ²_ε(o) ≡ σ²_ε`,
the normalized clustered meat satisfies `n⁻¹𝓜̂_CGM - S_n ⟶^p 0` with the stated rates, in case
(i) (`J = 1`) and case (ii) (the primitive-design assumption, any `J`), and
`nV̂_CGM ⟶^p H⁻¹SH⁻¹`. The proof rests on an identity for the conditional bias,
`(∑_o x̃_o x̃_o' R_oo + Ξ_n) - ∑_o x̃_o x̃_o' = -X̃' bd_m(Π) X̃`, together with a conditional
variance bound for the fluctuation. The last sections allow a `𝒟`-measurable random design.

## Main results

* `condMean_sub_target_eq`, `bias_opNorm_le`: the conditional bias identity and its bound.
* `condVar_normalizedMeatEntry_le`: the conditional variance of the normalized meat entry.
* `caseOne_meat_tendstoInProb`, `caseTwo_meat_tendstoInProb`: cases (i) and (ii).
* `tendstoInProb_nVhatCGM`: `nV̂_CGM ⟶^p H⁻¹SH⁻¹`.
* `caseTwo_meat_tendstoInProb_uncond`, `caseOne_meat_tendstoInProb_uncond`: random design.
-/

namespace Multiway
namespace Absorbed

open Finset MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

/-! ### An identity for the conditional bias

Under Regime 1 with `σ²_ε(o) ≡ σ²_ε`, `S_n = σ²_ε n⁻¹ ∑_o x̃_o x̃_o'`, so the conditional bias of
the meat relative to `𝓜_n` is `σ²_ε` times the left-hand side below. -/

section Bias

variable {O K D L N : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [Fintype N] [DecidableEq N] [DecidableEq D] [DecidableEq L]

omit [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K] [Fintype N] [DecidableEq N]
  [DecidableEq D] [DecidableEq L] in
/-- If the maintained sharing relation is the fibres of `i` and an observation exists, some
dimension is maintained. -/
theorem dims_nonempty_of_link [Nonempty O] (c : D → O → L) {dims : Finset D} {i : O → N}
    (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o') : dims.Nonempty := by
  obtain ⟨o⟩ := (inferInstance : Nonempty O)
  obtain ⟨j, hj, -⟩ := (hlink o o).2 rfl
  exact ⟨j, hj⟩

omit [Fintype K] [DecidableEq K] [Fintype N] [DecidableEq D] in
/-- The conditional bias of the clustered meat satisfies
`(∑_o x̃_o x̃_o' R_oo + Ξ_n) - ∑_o x̃_o x̃_o' = -X̃' bd_m(Π) X̃`, with `Π = I - R`, for arbitrary
regressors. -/
theorem condMean_sub_target_eq (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    {R Pi : Matrix O O ℝ} (hPi : Pi = 1 - R) (x : Matrix O K ℝ) (a b : K) :
    (∑ o : O, x o a * x o b * R o o) + Cgm.xiMat c dims R x a b
        - ∑ o : O, x o a * x o b
      = -((xᵀ * Cgm.blockPart i Pi * x) a b) := by
  classical
  have hdiag : (xᵀ * Matrix.diagonal (fun o => Pi o o) * x) a b
      = ∑ o : O, x o a * x o b * Pi o o := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  have hR : ∀ o : O, R o o = 1 - Pi o o := by
    intro o
    have h0 : Pi o o = (1 : Matrix O O ℝ) o o - R o o := by rw [hPi]; simp
    have h1 : (1 : Matrix O O ℝ) o o = 1 := by simp
    rw [h1] at h0
    linarith
  have hsum : (∑ o : O, x o a * x o b * R o o) + ∑ o : O, x o a * x o b * Pi o o
      = ∑ o : O, x o a * x o b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [hR o]; ring
  rw [Cgm.xiMat_eq c hdims i hlink hPi x]
  simp only [Matrix.add_apply, Matrix.neg_apply]
  rw [hdiag]
  linarith

omit [Fintype K] [DecidableEq K] [Fintype N] [DecidableEq D] in
/-- `condMean_sub_target_eq` without the hypothesis `hdims`, for a nonempty observation set. -/
theorem condMean_sub_target_eq_of_link [Nonempty O] (c : D → O → L) {dims : Finset D}
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    {R Pi : Matrix O O ℝ} (hPi : Pi = 1 - R) (x : Matrix O K ℝ) (a b : K) :
    (∑ o : O, x o a * x o b * R o o) + Cgm.xiMat c dims R x a b
        - ∑ o : O, x o a * x o b
      = -((xᵀ * Cgm.blockPart i Pi * x) a b) :=
  condMean_sub_target_eq c (dims_nonempty_of_link c hlink) i hlink hPi x a b

end Bias

/-! ### The conditional mean of the clustered meat -/

section CondBias

variable {O K D L N : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [Fintype N] [DecidableEq N] [DecidableEq D] [DecidableEq L]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [Fintype K] [DecidableEq K] [Fintype N] in
/-- The conditional mean of the clustered meat is, entry by entry,
`E[𝓜̂_CGM | 𝒟]_{ab} = σ²_ε[(∑_o x̃_o x̃_o')_{ab} - (X̃' bd_m(Π) X̃)_{ab}]`, with `Π = I - R`. -/
theorem condExp_meatCGM_sub_target {c : D → O → L} {dims : Finset D}
    {X : O → K → Ω → ℝ} {nuh : O → Ω → ℝ} {R : O → O → Ω → ℝ} {s : Ω → ℝ} {a b : K}
    (hdims : dims.Nonempty)
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    (hX : ∀ o k, StronglyMeasurable[𝒟] (X o k))
    (hint : ∀ o o', Integrable (fun ω => nuh o ω * nuh o' ω) μ)
    (hint' : ∀ o o', Integrable
      (fun ω => (if Linked c dims o o' then X o a ω * X o' b ω else 0)
        * (nuh o ω * nuh o' ω)) μ)
    (hcross : ∀ o o', μ[fun ω => nuh o ω * nuh o' ω | 𝒟]
      =ᵐ[μ] fun ω => s ω * R o o' ω) :
    μ[fun ω => ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty),
        (-1 : ℝ) ^ (A.card + 1) *
          ∑ g ∈ cells c A,
            (∑ o ∈ g, X o a ω * nuh o ω) * (∑ o' ∈ g, X o' b ω * nuh o' ω) | 𝒟]
      =ᵐ[μ] fun ω => s ω * ((∑ o : O, X o a ω * X o b ω)
          - ((Matrix.of fun o k => X o k ω)ᵀ
              * Cgm.blockPart i (1 - Matrix.of fun o o' => R o o' ω)
              * (Matrix.of fun o k => X o k ω)) a b) := by
  classical
  filter_upwards [Cgm.condExp_meatCGM 𝒟 hdims hX hint hint' hcross] with ω hω
  have h := condMean_sub_target_eq c hdims i hlink
      (R := Matrix.of fun o o' => R o o' ω) (Pi := 1 - Matrix.of fun o o' => R o o' ω) rfl
      (Matrix.of fun o k => X o k ω) a b
  simp only [Matrix.of_apply] at h
  have hAB : (∑ o : O, X o a ω * X o b ω * R o o ω)
        + Cgm.xiMat c dims (Matrix.of fun o o' => R o o' ω)
            (Matrix.of fun o k => X o k ω) a b
      = (∑ o : O, X o a ω * X o b ω)
        - ((Matrix.of fun o k => X o k ω)ᵀ
            * Cgm.blockPart i (1 - Matrix.of fun o o' => R o o' ω)
            * (Matrix.of fun o k => X o k ω)) a b := by linarith
  rw [hω, hAB]

end CondBias

/-! ### The conditional bias in operator norm -/

section BiasBound

variable {O K N : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [Fintype N] [DecidableEq N]

/-- `‖X̃' bd_m(Π) X̃‖ ≤ B²[√(tr(A^{(m)}) G^{(m)}_max n) + √(tr(Λ) G^{(m)}_max n)]` when
`Π = P_m + A^{(m)} + Λ`. The `P_m` block vanishes because `Δ_m'X̃ = 0`. -/
theorem blockPart_hat_opNorm_le (i : O → N) (x : Matrix O K ℝ)
    {Pi Pm A Lam : Matrix O O ℝ}
    (hdecomp : Pi = Pm + A + Lam)
    (hPm : ∀ o o' : O,
      Pm o o' = if i o = i o' then ((Cgm.clusterCard i (i o) : ℝ))⁻¹ else 0)
    (hAsym : Aᵀ = A) (hAidem : A * A = A)
    (hLsym : Lamᵀ = Lam) (hLidem : Lam * Lam = Lam)
    (hXcl : ∀ (j : N) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O => i o = j), x o k = 0)
    {B Gmax : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j : N, (Cgm.clusterCard i j : ℝ) ≤ Gmax) :
    ‖xᵀ * Cgm.blockPart i Pi * x‖
      ≤ B ^ 2 * (Real.sqrt (A.trace * (Gmax * (Fintype.card O : ℝ)))
          + Real.sqrt (Lam.trace * (Gmax * (Fintype.card O : ℝ)))) := by
  classical
  -- `X̃'D_jP_mD_jX̃ = 0` on each cluster `j`
  have hPmBlock : Cgm.blockPart i Pm = Pm := by
    ext o o'
    by_cases h : i o = i o' <;> simp [hPm o o', h]
  have hzero : xᵀ * Cgm.blockPart i Pm * x = 0 := by
    ext a b
    rw [hPmBlock, Cgm.transpose_mul_mul_apply]
    have hterm : ∀ o : O, ∑ o' : O, x o a * (Pm o o' * x o' b) = 0 := by
      intro o
      have hin : ∑ o' : O, x o a * (Pm o o' * x o' b)
          = x o a * ((Cgm.clusterCard i (i o) : ℝ))⁻¹
            * ∑ o' ∈ Finset.univ.filter (fun o' : O => i o' = i o), x o' b := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun o' _ => ?_
        rw [hPm o o']
        split_ifs with h1 h2 h2
        · ring
        · exact absurd h1.symm h2
        · exact absurd h2.symm h1
        · ring
      rw [hin, hXcl (i o) b, mul_zero]
    simp only [Matrix.zero_apply]
    exact Finset.sum_eq_zero fun o _ => hterm o
  have hsplit : xᵀ * Cgm.blockPart i Pi * x
      = xᵀ * Cgm.blockPart i A * x + xᵀ * Cgm.blockPart i Lam * x := by
    rw [hdecomp, Cgm.blockPart_add, Cgm.blockPart_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_add, Matrix.add_mul, hzero, zero_add]
  rw [hsplit]
  have h1 := Cgm.opNorm_xT_blockPart_le i x hAsym hAidem hB hG
  have h2 := Cgm.opNorm_xT_blockPart_le i x hLsym hLidem hB hG
  calc ‖xᵀ * Cgm.blockPart i A * x + xᵀ * Cgm.blockPart i Lam * x‖
      ≤ ‖xᵀ * Cgm.blockPart i A * x‖ + ‖xᵀ * Cgm.blockPart i Lam * x‖ := norm_add_le _ _
    _ ≤ B ^ 2 * Real.sqrt (A.trace * (Gmax * (Fintype.card O : ℝ)))
          + B ^ 2 * Real.sqrt (Lam.trace * (Gmax * (Fintype.card O : ℝ))) := by
        exact add_le_add h1 h2
    _ = B ^ 2 * (Real.sqrt (A.trace * (Gmax * (Fintype.card O : ℝ)))
          + Real.sqrt (Lam.trace * (Gmax * (Fintype.card O : ℝ)))) := by ring

end BiasBound

section BiasBoundLink

variable {O K D L N : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [Fintype N] [DecidableEq N] [DecidableEq D] [DecidableEq L]

omit [DecidableEq D] in
/-- The conditional bias matrix of the clustered meat in operator norm. -/
theorem bias_opNorm_le (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    (x : Matrix O K ℝ) {R Pi Pm A Lam : Matrix O O ℝ}
    (hPi : Pi = 1 - R) (hdecomp : Pi = Pm + A + Lam)
    (hPm : ∀ o o' : O,
      Pm o o' = if i o = i o' then ((Cgm.clusterCard i (i o) : ℝ))⁻¹ else 0)
    (hAsym : Aᵀ = A) (hAidem : A * A = A)
    (hLsym : Lamᵀ = Lam) (hLidem : Lam * Lam = Lam)
    (hXcl : ∀ (j : N) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O => i o = j), x o k = 0)
    {B Gmax : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j : N, (Cgm.clusterCard i j : ℝ) ≤ Gmax) :
    ‖(Matrix.of fun a b : K => (∑ o : O, x o a * x o b * R o o)
          + Cgm.xiMat c dims R x a b - ∑ o : O, x o a * x o b)‖
      ≤ B ^ 2 * (Real.sqrt (A.trace * (Gmax * (Fintype.card O : ℝ)))
          + Real.sqrt (Lam.trace * (Gmax * (Fintype.card O : ℝ)))) := by
  have hmat : (Matrix.of fun a b : K => (∑ o : O, x o a * x o b * R o o)
        + Cgm.xiMat c dims R x a b - ∑ o : O, x o a * x o b)
      = -(xᵀ * Cgm.blockPart i Pi * x) := by
    ext a b
    simp only [Matrix.of_apply, Matrix.neg_apply]
    exact condMean_sub_target_eq c hdims i hlink hPi x a b
  rw [hmat, norm_neg]
  exact blockPart_hat_opNorm_le i x hdecomp hPm hAsym hAidem hLsym hLidem hXcl hB hG

end BiasBoundLink

/-! ### The fluctuation

Entry `(a,b)` of `𝓜̂_CGM` is `ε'RW_{ab}Rε` with `W_{ab,oo'} = x̃_{oa} x̃_{o'b} 𝟙{o ∼ o'}`, and
`‖RW_{ab}R‖_F ≤ ‖W_{ab}‖_F ≤ B²(JG_max n)^{1/2}`. -/

section Contraction

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- `‖RM‖_F ≤ ‖M‖_F` for a symmetric idempotent `R`, from
`‖M‖_F² = ‖RM‖_F² + ‖(I-R)M‖_F²`. -/
theorem rectFrobSq_symmProj_mul_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    (M : Matrix O O ℝ) : rectFrobSq (R * M) ≤ rectFrobSq M := by
  have hkey : ∀ S : Matrix O O ℝ, Sᵀ = S → S * S = S →
      rectFrobSq (S * M) = (Mᵀ * S * M).trace := by
    intro S hs hi
    rw [rectFrobSq_eq_trace]
    congr 1
    calc (S * M)ᵀ * (S * M) = Mᵀ * Sᵀ * (S * M) := by rw [Matrix.transpose_mul]
      _ = Mᵀ * (S * S) * M := by rw [hs]; noncomm_ring
      _ = Mᵀ * S * M := by rw [hi]
  have hSsym : (1 - R : Matrix O O ℝ)ᵀ = 1 - R := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsym]
  have hSidem : (1 - R : Matrix O O ℝ) * (1 - R) = 1 - R := by
    have hexp : (1 - R : Matrix O O ℝ) * (1 - R) = 1 - R - R + R * R := by noncomm_ring
    rw [hexp, hidem]
    abel
  have h1 := hkey R hsym hidem
  have h2 := hkey (1 - R) hSsym hSidem
  have hsum : (Mᵀ * R * M).trace + (Mᵀ * (1 - R) * M).trace = rectFrobSq M := by
    rw [rectFrobSq_eq_trace, ← Matrix.trace_add]
    congr 1
    noncomm_ring
  have hnn : (0 : ℝ) ≤ (Mᵀ * (1 - R) * M).trace := by
    rw [← h2]; exact rectFrobSq_nonneg _
  rw [h1]
  linarith

/-- `‖MR‖_F ≤ ‖M‖_F` for a symmetric idempotent `R`, by transposition. -/
theorem rectFrobSq_mul_symmProj_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    (M : Matrix O O ℝ) : rectFrobSq (M * R) ≤ rectFrobSq M := by
  calc rectFrobSq (M * R) = rectFrobSq ((M * R)ᵀ) := (rectFrobSq_transpose _).symm
    _ = rectFrobSq (R * Mᵀ) := by rw [Matrix.transpose_mul, hsym]
    _ ≤ rectFrobSq Mᵀ := rectFrobSq_symmProj_mul_le hsym hidem Mᵀ
    _ = rectFrobSq M := rectFrobSq_transpose M

/-- `‖RWR‖_F ≤ ‖W‖_F` for a symmetric idempotent `R` and every `W`. -/
theorem rectFrobSq_conj_le {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    (M : Matrix O O ℝ) : rectFrobSq (R * M * R) ≤ rectFrobSq M :=
  le_trans (rectFrobSq_mul_symmProj_le hsym hidem (R * M))
    (rectFrobSq_symmProj_mul_le hsym hidem M)

omit [DecidableEq O] in
/-- `‖tM‖_F² = t²‖M‖_F²`. -/
theorem rectFrobSq_smul (t : ℝ) (M : Matrix O O ℝ) :
    rectFrobSq (t • M) = t ^ 2 * rectFrobSq M := by
  simp only [rectFrobSq, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

end Contraction

section LinkW

variable {O K D L : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [DecidableEq D] [Fintype L] [DecidableEq L]

/-- `W_{ab,oo'} = x̃_{oa} x̃_{o'b} 𝟙{o ∼ o'}`. -/
def linkW (c : D → O → L) (dims : Finset D) (x : Matrix O K ℝ) (a b : K) : Matrix O O ℝ :=
  Matrix.of fun o o' => if Linked c dims o o' then x o a * x o' b else 0

omit [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K] [DecidableEq D] [Fintype L] in
@[simp] theorem linkW_apply (c : D → O → L) (dims : Finset D) (x : Matrix O K ℝ) (a b : K)
    (o o' : O) :
    linkW c dims x a b o o' = if Linked c dims o o' then x o a * x o' b else 0 := rfl

omit [DecidableEq O] [DecidableEq K] [DecidableEq D] in
/-- `‖W_{ab}‖_F² ≤ B⁴ J G_max n`, for an arbitrary maintained set of `J` dimensions. -/
theorem rectFrobSq_linkW_le (c : D → O → L) (dims : Finset D) (x : Matrix O K ℝ)
    {B Gmax : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j ∈ dims, ∀ l : L, (Cgm.clusterCard (c j) l : ℝ) ≤ Gmax) (a b : K) :
    rectFrobSq (linkW c dims x a b)
      ≤ B ^ 4 * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ))) := by
  classical
  have hB4 : (0 : ℝ) ≤ B ^ 4 := by positivity
  have hsq : ∀ (o : O) (k : K), x o k ^ 2 ≤ B ^ 2 := by
    intro o k
    refine le_trans ?_ (hB o)
    exact Finset.single_le_sum (f := fun k : K => x o k ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ k)
  -- the union bound, entry by entry
  have hentry : ∀ o o' : O, (linkW c dims x a b o o') ^ 2
      ≤ B ^ 4 * ∑ j ∈ dims, (if c j o = c j o' then (1 : ℝ) else 0) := by
    intro o o'
    by_cases h : Linked c dims o o'
    · have hone : (1 : ℝ) ≤ ∑ j ∈ dims, (if c j o = c j o' then (1 : ℝ) else 0) := by
        obtain ⟨j0, hj0, hc0⟩ := h
        have hle := Finset.single_le_sum
          (f := fun j : D => (if c j o = c j o' then (1 : ℝ) else 0))
          (fun j _ => by split_ifs <;> norm_num) hj0
        simpa [hc0] using hle
      have hlhs : (linkW c dims x a b o o') ^ 2 ≤ B ^ 4 := by
        have hval : linkW c dims x a b o o' = x o a * x o' b := by simp [linkW, h]
        rw [hval, mul_pow]
        calc x o a ^ 2 * x o' b ^ 2 ≤ B ^ 2 * B ^ 2 :=
              mul_le_mul (hsq o a) (hsq o' b) (sq_nonneg _) (sq_nonneg B)
          _ = B ^ 4 := by ring
      calc (linkW c dims x a b o o') ^ 2 ≤ B ^ 4 := hlhs
        _ = B ^ 4 * 1 := (mul_one _).symm
        _ ≤ B ^ 4 * ∑ j ∈ dims, (if c j o = c j o' then (1 : ℝ) else 0) :=
            mul_le_mul_of_nonneg_left hone hB4
    · have hval : linkW c dims x a b o o' = 0 := by simp [linkW, h]
      have hnn : (0 : ℝ) ≤ ∑ j ∈ dims, (if c j o = c j o' then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
      rw [hval]
      simpa using mul_nonneg hB4 hnn
  have hstep : rectFrobSq (linkW c dims x a b)
      ≤ ∑ o : O, ∑ o' : O, B ^ 4 * ∑ j ∈ dims, (if c j o = c j o' then (1 : ℝ) else 0) := by
    rw [rectFrobSq]
    exact Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ => hentry o o'
  -- pull the dimension sum outermost
  have hswap : ∑ o : O, ∑ o' : O, B ^ 4 * ∑ j ∈ dims,
        (if c j o = c j o' then (1 : ℝ) else 0)
      = ∑ j ∈ dims, ∑ o : O, ∑ o' : O,
          B ^ 4 * (if c j o = c j o' then (1 : ℝ) else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun o (_ : o ∈ (Finset.univ : Finset O)) =>
      (Finset.sum_comm : ∑ o' : O, ∑ j ∈ dims,
          B ^ 4 * (if c j o = c j o' then (1 : ℝ) else 0)
        = ∑ j ∈ dims, ∑ o' : O, B ^ 4 * (if c j o = c j o' then (1 : ℝ) else 0))]
    exact Finset.sum_comm
  -- the counting step, one dimension at a time
  have hdim : ∀ j ∈ dims, ∑ o : O, ∑ o' : O,
        B ^ 4 * (if c j o = c j o' then (1 : ℝ) else 0)
      ≤ B ^ 4 * (Gmax * (Fintype.card O : ℝ)) := by
    intro j hj
    have hcount : ∑ o : O, ∑ o' : O, (if c j o = c j o' then (1 : ℝ) else 0)
        ≤ Gmax * (Fintype.card O : ℝ) := by
      rw [Cgm.sum_pairs_sameCluster (c j)]
      exact Cgm.sum_clusterCard_sq_le (c j) (hG j hj)
    calc ∑ o : O, ∑ o' : O, B ^ 4 * (if c j o = c j o' then (1 : ℝ) else 0)
        = B ^ 4 * ∑ o : O, ∑ o' : O, (if c j o = c j o' then (1 : ℝ) else 0) := by
          simp only [Finset.mul_sum]
      _ ≤ B ^ 4 * (Gmax * (Fintype.card O : ℝ)) :=
          mul_le_mul_of_nonneg_left hcount hB4
  have hfin : ∑ j ∈ dims, ∑ o : O, ∑ o' : O,
        B ^ 4 * (if c j o = c j o' then (1 : ℝ) else 0)
      ≤ (dims.card : ℝ) * (B ^ 4 * (Gmax * (Fintype.card O : ℝ))) := by
    have h := Finset.sum_le_sum hdim
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  calc rectFrobSq (linkW c dims x a b)
      ≤ ∑ o : O, ∑ o' : O, B ^ 4 * ∑ j ∈ dims,
          (if c j o = c j o' then (1 : ℝ) else 0) := hstep
    _ = ∑ j ∈ dims, ∑ o : O, ∑ o' : O,
          B ^ 4 * (if c j o = c j o' then (1 : ℝ) else 0) := hswap
    _ ≤ (dims.card : ℝ) * (B ^ 4 * (Gmax * (Fintype.card O : ℝ))) := hfin
    _ = B ^ 4 * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ))) := by ring

omit [DecidableEq K] [DecidableEq D] in
/-- `‖RW_{ab}R‖_F² ≤ B⁴ J G_max n` for a symmetric idempotent `R`. -/
theorem rectFrobSq_conj_linkW_le (c : D → O → L) (dims : Finset D) (x : Matrix O K ℝ)
    {R : Matrix O O ℝ} (hsym : Rᵀ = R) (hidem : R * R = R)
    {B Gmax : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j ∈ dims, ∀ l : L, (Cgm.clusterCard (c j) l : ℝ) ≤ Gmax) (a b : K) :
    rectFrobSq (R * linkW c dims x a b * R)
      ≤ B ^ 4 * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ))) :=
  le_trans (rectFrobSq_conj_le hsym hidem (linkW c dims x a b))
    (rectFrobSq_linkW_le c dims x hB hG a b)

end LinkW

/-! ### The conditional variance of the normalized entry -/

section CondVar

variable {O K D L : Type*}
variable [Fintype O] [DecidableEq O] [Nonempty O] [Fintype K] [DecidableEq K]
variable [DecidableEq D] [Fintype L] [DecidableEq L]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The matrix `n⁻¹ R W_{ab} R`, whose quadratic form is the normalized entry
`n⁻¹ ε'RW_{ab}Rε`. -/
noncomputable def normalizedMeatEntry (c : D → O → L) (dims : Finset D)
    (R : Ω → Matrix O O ℝ) (X : Ω → Matrix O K ℝ) (a b : K) : Ω → Matrix O O ℝ :=
  fun ω => ((Fintype.card O : ℝ))⁻¹ • (R ω * linkW c dims (X ω) a b * R ω)

omit [Fintype O] [DecidableEq O] [Nonempty O] [Fintype K] [DecidableEq K] [DecidableEq D]
  [Fintype L] in
/-- The entries of `W_{ab}` are `𝒟`-measurable whenever the regressors are. -/
theorem stronglyMeasurable_linkW (c : D → O → L) (dims : Finset D)
    {X : Ω → Matrix O K ℝ} (a b : K)
    (hX : ∀ o k, StronglyMeasurable[𝒟] fun ω => X ω o k) (o o' : O) :
    StronglyMeasurable[𝒟] fun ω => linkW c dims (X ω) a b o o' := by
  by_cases h : Linked c dims o o'
  · have hfun : (fun ω => linkW c dims (X ω) a b o o') = fun ω => X ω o a * X ω o' b :=
      funext fun ω => by simp [linkW, h]
    rw [hfun]
    exact (hX o a).mul (hX o' b)
  · have hfun : (fun ω => linkW c dims (X ω) a b o o') = fun _ : Ω => (0 : ℝ) :=
      funext fun ω => by simp [linkW, h]
    rw [hfun]
    exact stronglyMeasurable_const

omit [DecidableEq O] [Nonempty O] [Fintype K] [DecidableEq K] [DecidableEq D] [Fintype L] in
theorem stronglyMeasurable_normalizedMeatEntry (c : D → O → L) (dims : Finset D)
    {R : Ω → Matrix O O ℝ} {X : Ω → Matrix O K ℝ} (a b : K)
    (hR : ∀ o o', StronglyMeasurable[𝒟] fun ω => R ω o o')
    (hX : ∀ o k, StronglyMeasurable[𝒟] fun ω => X ω o k) (o o' : O) :
    StronglyMeasurable[𝒟] fun ω => normalizedMeatEntry c dims R X a b ω o o' := by
  have hrw : (fun ω => normalizedMeatEntry c dims R X a b ω o o')
      = fun ω => ((Fintype.card O : ℝ))⁻¹ *
          ∑ p : O, (∑ q : O, R ω o q * linkW c dims (X ω) a b q p) * R ω p o' := by
    funext ω
    simp only [normalizedMeatEntry, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  have hinner : ∀ p : O, StronglyMeasurable[𝒟]
      fun ω => (∑ q : O, R ω o q * linkW c dims (X ω) a b q p) * R ω p o' := by
    intro p
    have hq : StronglyMeasurable[𝒟]
        fun ω => ∑ q : O, R ω o q * linkW c dims (X ω) a b q p := by
      have hsplit : (fun ω => ∑ q : O, R ω o q * linkW c dims (X ω) a b q p)
          = ∑ q : O, fun ω => R ω o q * linkW c dims (X ω) a b q p := by
        funext ω; simp only [Finset.sum_apply]
      rw [hsplit]
      exact Finset.stronglyMeasurable_sum _ fun q _ =>
        (hR o q).mul (stronglyMeasurable_linkW 𝒟 c dims a b hX q p)
    exact hq.mul (hR p o')
  have hsum : StronglyMeasurable[𝒟]
      fun ω => ∑ p : O, (∑ q : O, R ω o q * linkW c dims (X ω) a b q p) * R ω p o' := by
    have hsplit : (fun ω => ∑ p : O,
          (∑ q : O, R ω o q * linkW c dims (X ω) a b q p) * R ω p o')
        = ∑ p : O, fun ω =>
          (∑ q : O, R ω o q * linkW c dims (X ω) a b q p) * R ω p o' := by
      funext ω; simp only [Finset.sum_apply]
    rw [hsplit]
    exact Finset.stronglyMeasurable_sum _ fun p _ => hinner p
  rw [hrw]
  exact hsum.const_mul _

omit [DecidableEq K] [DecidableEq D] in
/-- `Var(n⁻¹ ε'RW_{ab}Rε | 𝒟) ≤ 3C B⁴ J G_max / n`, from Lemma SM.C.5 (Variance of a quadratic
form in independent variables). The hypotheses after `hG` are those of
`Quadform.condVar_quadForm_le`. -/
theorem condVar_normalizedMeatEntry_le [IsFiniteMeasure μ] (h𝒟 : 𝒟 ≤ mΩ)
    (c : D → O → L) (dims : Finset D)
    {R : Ω → Matrix O O ℝ} {X : Ω → Matrix O K ℝ} {eps sig : O → Ω → ℝ} {a b : K}
    {B Gmax C : ℝ} (hC : 0 ≤ C)
    (hRsym : ∀ ω, (R ω)ᵀ = R ω) (hRidem : ∀ ω, R ω * R ω = R ω)
    (hB : ∀ ω, ∀ o : O, ∑ k : K, X ω o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j ∈ dims, ∀ l : L, (Cgm.clusterCard (c j) l : ℝ) ≤ Gmax)
    (hL2 : MemLp (Quadform.quadForm (normalizedMeatEntry c dims R X a b) eps) 2 μ)
    (hW : ∀ o o', StronglyMeasurable[𝒟]
      fun ω => normalizedMeatEntry c dims R X a b ω o o')
    (hi2 : ∀ p : O × O, Integrable (fun ω => eps p.1 ω * eps p.2 ω) μ)
    (hiW2 : ∀ p : O × O, Integrable
      (fun ω => normalizedMeatEntry c dims R X a b ω p.1 p.2
        * (eps p.1 ω * eps p.2 ω)) μ)
    (hi4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω)) μ)
    (hiW4 : ∀ r : (O × O) × (O × O),
      Integrable (fun ω => normalizedMeatEntry c dims R X a b ω r.1.1 r.1.2
        * normalizedMeatEntry c dims R X a b ω r.2.1 r.2.2
        * (eps r.1.1 ω * eps r.1.2 ω * (eps r.2.1 ω * eps r.2.2 ω))) μ)
    (hvar : ∀ o, μ[fun ω => eps o ω * eps o ω | 𝒟] =ᵐ[μ] sig o)
    (hcross : ∀ o o', o ≠ o' → μ[fun ω => eps o ω * eps o' ω | 𝒟] =ᵐ[μ] 0)
    (hfour : ∀ o, μ[fun ω => eps o ω * eps o ω * (eps o ω * eps o ω) | 𝒟] ≤ᵐ[μ] fun _ => C)
    (hpair : ∀ o o', o ≠ o' →
      μ[fun ω => eps o ω * eps o ω * (eps o' ω * eps o' ω) | 𝒟]
        =ᵐ[μ] fun ω => sig o ω * sig o' ω)
    (hmixed : ∀ a o o' : O, o ≠ o' →
      μ[fun ω => eps a ω * eps a ω * (eps o ω * eps o' ω) | 𝒟] =ᵐ[μ] 0)
    (hquad : ∀ p q : O × O, p.1 ≠ p.2 → q.1 ≠ q.2 → q ≠ p → q ≠ (p.2, p.1) →
      μ[fun ω => eps p.1 ω * eps p.2 ω * (eps q.1 ω * eps q.2 ω) | 𝒟] =ᵐ[μ] 0) :
    ProbabilityTheory.condVar 𝒟
        (Quadform.quadForm (normalizedMeatEntry c dims R X a b) eps) μ
      ≤ᵐ[μ] fun _ => 3 * C
          * (B ^ 4 * ((dims.card : ℝ) * (Gmax / (Fintype.card O : ℝ)))) := by
  have hn : (0 : ℝ) < (Fintype.card O : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := O)
  have hne : (Fintype.card O : ℝ) ≠ 0 := ne_of_gt hn
  have hbound : ∀ ω, rectFrobSq (normalizedMeatEntry c dims R X a b ω)
      ≤ B ^ 4 * ((dims.card : ℝ) * (Gmax / (Fintype.card O : ℝ))) := by
    intro ω
    rw [normalizedMeatEntry, rectFrobSq_smul]
    have h1 := rectFrobSq_conj_linkW_le c dims (X ω) (hRsym ω) (hRidem ω) (hB ω) hG a b
    have h2 : ((Fintype.card O : ℝ))⁻¹ ^ 2
          * rectFrobSq (R ω * linkW c dims (X ω) a b * R ω)
        ≤ ((Fintype.card O : ℝ))⁻¹ ^ 2
          * (B ^ 4 * ((dims.card : ℝ) * (Gmax * (Fintype.card O : ℝ)))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine h2.trans (le_of_eq ?_)
    field_simp
  filter_upwards [Quadform.condVar_quadForm_le 𝒟 h𝒟 hC hL2 hW hi2 hiW2 hi4 hiW4 hvar hcross
    hfour hpair hmixed hquad] with ω hω
  refine hω.trans ?_
  exact mul_le_mul_of_nonneg_left (hbound ω) (by linarith)

end CondVar

/-! ### The residual-maker matrix -/

section Bridge

variable {O ι : Type*} [Fintype O] [DecidableEq O]

/-- `‖RWR‖_F ≤ ‖W‖_F` for the residual-maker matrix `ResidualBridge.residualMatrix`. -/
theorem rectFrobSq_conj_residualMatrix_le
    (S : Submodule ℝ (EuclideanSpace ℝ O)) (x : ι → EuclideanSpace ℝ O)
    (M : Matrix O O ℝ) :
    rectFrobSq (ResidualBridge.residualMatrix S x * M * ResidualBridge.residualMatrix S x)
      ≤ rectFrobSq M :=
  rectFrobSq_conj_le (ResidualBridge.residualMatrix_isSymm S x)
    (ResidualBridge.residualMatrix_mul_self S x) M

end Bridge

/-! ### Case (ii)

Case (ii) of Theorem 10 states that under the primitive-design assumption and `G_max/n → 0`,
for any number of maintained dimensions,
`n⁻¹𝓜̂_CGM - S_n = O_p(d_[Δ]/n + [G_max/n]^{1/2}) ⟶^p 0`. The bias is split
as `Ξ_n - X̃'diag(Π)X̃`, with `Ξ_n` bounded by Lemma SM.B.9 (hypothesis `hXi`) and the
diagonal term by `B²tr(Π)`; the fluctuation is bounded by Chebyshev's inequality from the
conditional variance bound (hypothesis `hcv`). The residual is written as `(I - P_[Δ] - Λ) *ᵥ ε`,
with `P_[Δ]`, `Λ` and the clustering deterministic. -/

section EntryNorm

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `|M_{ab}| ≤ ‖M‖` for the `l2` operator norm. -/
theorem abs_entry_le_l2_opNorm (M : Matrix α β ℝ) (a : α) (b : β) : |M a b| ≤ ‖M‖ := by
  have hmv := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single b (1 : ℝ))
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at hmv
  refine le_trans ?_ hmv
  have hval : ∀ i : α, (M *ᵥ (EuclideanSpace.single b (1 : ℝ))) i = M i b := by
    intro i
    simp [Matrix.mulVec, dotProduct]
  have hnormsq :
      ‖(EuclideanSpace.equiv α ℝ).symm (M *ᵥ (EuclideanSpace.single b (1 : ℝ)))‖ ^ 2
        = ∑ i : α, (M *ᵥ (EuclideanSpace.single b (1 : ℝ))) i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  have hsum : (M a b) ^ 2
      ≤ ∑ i : α, (M *ᵥ (EuclideanSpace.single b (1 : ℝ))) i ^ 2 := by
    rw [← hval a]
    exact Finset.single_le_sum
      (f := fun i : α => (M *ᵥ (EuclideanSpace.single b (1 : ℝ))) i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ a)
  have hle : (M a b) ^ 2
      ≤ ‖(EuclideanSpace.equiv α ℝ).symm (M *ᵥ (EuclideanSpace.single b (1 : ℝ)))‖ ^ 2 := by
    rw [hnormsq]; exact hsum
  nlinarith [abs_nonneg (M a b), sq_abs (M a b),
    norm_nonneg ((EuclideanSpace.equiv α ℝ).symm (M *ᵥ (EuclideanSpace.single b (1 : ℝ))))]

end EntryNorm

section CaseTwoBiasFinite

variable {O K D L : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [DecidableEq D] [Fintype L] [DecidableEq L]

/-- The unnormalized conditional bias entry
`(∑_o x̃_{oa}x̃_{ob}R_{oo} + Ξ_{n,ab}) - ∑_o x̃_{oa}x̃_{ob}`. -/
def biasEntry (c : D → O → L) (dims : Finset D) (R : Matrix O O ℝ) (x : Matrix O K ℝ)
    (a b : K) : ℝ :=
  (∑ o : O, x o a * x o b * R o o) + Cgm.xiMat c dims R x a b - ∑ o : O, x o a * x o b

/-- The conditional bias equals `Ξ_n - X̃'diag(Π)X̃` with `Π = P_[Δ] + Λ`, for any maintained
set. -/
theorem caseTwo_bias_eq (c : D → O → L) (dims : Finset D) {Pm Lam R : Matrix O O ℝ}
    (hR : R = 1 - Pm - Lam) (x : Matrix O K ℝ) (a b : K) :
    biasEntry c dims R x a b
      = Cgm.xiMat c dims R x a b
        - (xᵀ * Matrix.diagonal (fun o => Pm o o + Lam o o) * x) a b := by
  classical
  have hdiag : (xᵀ * Matrix.diagonal (fun o => Pm o o + Lam o o) * x) a b
      = ∑ o : O, x o a * x o b * (Pm o o + Lam o o) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  have hR' : ∀ o : O, R o o = 1 - (Pm o o + Lam o o) := by
    intro o
    rw [hR]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq]
    ring
  have hsum : (∑ o : O, x o a * x o b * R o o) - ∑ o : O, x o a * x o b
      = -∑ o : O, x o a * x o b * (Pm o o + Lam o o) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [hR' o]; ring
  rw [biasEntry, hdiag]
  linarith [hsum]

/-- `|bias_{ab}| ≤ ‖Ξ_n‖ + B²[tr(P_[Δ]) + tr(Λ)]`. -/
theorem caseTwo_bias_abs_le (c : D → O → L) (dims : Finset D) {Pm Lam R : Matrix O O ℝ}
    (hR : R = 1 - Pm - Lam)
    (hPms : Pmᵀ = Pm) (hPmi : Pm * Pm = Pm) (hLs : Lamᵀ = Lam) (hLi : Lam * Lam = Lam)
    (x : Matrix O K ℝ) {B : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2) (a b : K) :
    |biasEntry c dims R x a b|
      ≤ ‖Cgm.xiMat c dims R x‖ + B ^ 2 * (Pm.trace + Lam.trace) := by
  classical
  have hdnn : ∀ o : O, 0 ≤ Pm o o + Lam o o := fun o =>
    add_nonneg (Cgm.diag_nonneg_of_symmProj hPms hPmi o)
      (Cgm.diag_nonneg_of_symmProj hLs hLi o)
  have hdsum : ∑ o : O, (Pm o o + Lam o o) = Pm.trace + Lam.trace := by
    rw [Finset.sum_add_distrib]
    rfl
  have hdiagle : |(xᵀ * Matrix.diagonal (fun o => Pm o o + Lam o o) * x) a b|
      ≤ B ^ 2 * (Pm.trace + Lam.trace) := by
    refine le_trans (abs_entry_le_l2_opNorm _ a b) ?_
    have h := Cgm.opNorm_xT_diagonal_le x (fun o => Pm o o + Lam o o) hdnn hB
    rwa [hdsum] at h
  have hxile : |Cgm.xiMat c dims R x a b| ≤ ‖Cgm.xiMat c dims R x‖ :=
    abs_entry_le_l2_opNorm _ a b
  rw [caseTwo_bias_eq c dims hR x a b]
  exact le_trans (abs_sub _ _) (add_le_add hxile hdiagle)

end CaseTwoBiasFinite

/-! ### Sums of sequences bounded in probability -/

section OpLayer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- If `|Z_n| ≤ |Y_n| + |W_n|` and `Y`, `W` are `O_p(1)`, then `Z` is `O_p(1)`. -/
theorem bddInProb_of_abs_le_add {Z Y W : ℕ → Ω → ℝ}
    (hle : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ |Y n ω| + |W n ω|)
    (hY : Sequence.BddInProb P Y) (hW : Sequence.BddInProb P W) :
    Sequence.BddInProb P Z := by
  intro δ hδ
  obtain ⟨C₁, hC₁, hb₁⟩ := hY (δ / 2) (ENNReal.half_pos hδ.ne')
  obtain ⟨C₂, hC₂, hb₂⟩ := hW (δ / 2) (ENNReal.half_pos hδ.ne')
  refine ⟨C₁ + C₂, by linarith, fun n => ?_⟩
  have hsub : P {ω | C₁ + C₂ ≤ |Z n ω|}
      ≤ P {ω | C₁ ≤ |Y n ω|} + P {ω | C₂ ≤ |W n ω|} := by
    refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
    filter_upwards [hle n] with ω hω hmem
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hmem ⊢
    by_contra hc
    rw [not_or, not_le, not_le] at hc
    linarith [hc.1, hc.2, hmem]
  calc P {ω | C₁ + C₂ ≤ |Z n ω|}
      ≤ P {ω | C₁ ≤ |Y n ω|} + P {ω | C₂ ≤ |W n ω|} := hsub
    _ ≤ δ / 2 + δ / 2 := add_le_add (hb₁ n) (hb₂ n)
    _ = δ := ENNReal.add_halves δ

end OpLayer

section CaseTwoBiasSeq

variable {O D L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The conditional bias in case (ii) is `O_p(d_[Δ] + (G_max n)^{1/2})`, for any maintained
set. -/
theorem caseTwo_bias_bddInProb
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n))
    {Pm Lam : ∀ n, Matrix (O n) (O n) ℝ} {xi : ∀ n, O n → K → Ω → ℝ}
    {s : Ω → ℝ} {a b : K} {B sbar Kbd : ℝ} {aN : ℕ → ℝ}
    (hPms : ∀ n, (Pm n)ᵀ = Pm n) (hPmi : ∀ n, Pm n * Pm n = Pm n)
    (hLs : ∀ n, (Lam n)ᵀ = Lam n) (hLi : ∀ n, Lam n * Lam n = Lam n)
    (hB : ∀ (n : ℕ) (ω : Ω), ∀ o : O n,
      ∑ k : K, PrimitiveDesign.within (Pm n) (xi n) ω o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hK : ∀ n, (Lam n).trace ≤ Kbd)
    (hPmle : ∀ n, (Pm n).trace ≤ aN n) (hone : ∀ n, 1 ≤ aN n)
    (hXi : Sequence.BddInProb P (fun n ω =>
      ‖PrimitiveDesign.xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖ / aN n)) :
    Sequence.BddInProb P (fun n ω =>
      s ω * biasEntry (c n) (dims n) (1 - Pm n - Lam n)
          (PrimitiveDesign.within (Pm n) (xi n) ω) a b / aN n) := by
  classical
  have hKnn : (0 : ℝ) ≤ Kbd :=
    le_trans (Cgm.trace_nonneg_of_symmProj (hLs 0) (hLi 0)) (hK 0)
  refine bddInProb_of_abs_le_add
    (Y := fun n ω => sbar
      * (‖PrimitiveDesign.xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖ / aN n))
    (W := fun _ _ => sbar * (B ^ 2 * (1 + Kbd))) (fun n => ?_)
    (Sequence.bddInProb_const_mul sbar hXi)
    (Sequence.bddInProb_of_abs_le_const (fun _ => Filter.Eventually.of_forall fun _ => le_rfl))
  filter_upwards with ω
  set x : Matrix (O n) K ℝ := PrimitiveDesign.within (Pm n) (xi n) ω with hx
  set Xi : Matrix K K ℝ := Cgm.xiMat (c n) (dims n) (1 - Pm n - Lam n) x with hXidef
  have haN0 : (0 : ℝ) < aN n := lt_of_lt_of_le zero_lt_one (hone n)
  have hnrm : (0 : ℝ) ≤ ‖Xi‖ := norm_nonneg _
  have hbias := caseTwo_bias_abs_le (c n) (dims n) (Pm := Pm n) (Lam := Lam n)
    (R := 1 - Pm n - Lam n) rfl (hPms n) (hPmi n) (hLs n) (hLi n) x (hB n ω) a b
  have hsnn : (0 : ℝ) ≤ sbar := le_trans (abs_nonneg (s ω)) (hs ω)
  have hLnn : (0 : ℝ) ≤ (Lam n).trace := Cgm.trace_nonneg_of_symmProj (hLs n) (hLi n)
  have hPnn : (0 : ℝ) ≤ (Pm n).trace := Cgm.trace_nonneg_of_symmProj (hPms n) (hPmi n)
  have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
  -- `B²(d_[Δ] + K) ≤ B²(1 + K̄)a_n`, from `d_[Δ] ≤ a_n` and `1 ≤ a_n`
  have hdiv : B ^ 2 * ((Pm n).trace + (Lam n).trace) ≤ B ^ 2 * (1 + Kbd) * aN n := by
    have h1 : (Pm n).trace + (Lam n).trace ≤ aN n + Kbd * aN n := by
      have h2 : Kbd ≤ Kbd * aN n := by nlinarith [hone n]
      linarith [hPmle n, hK n]
    nlinarith [h1]
  have hnum : |s ω * biasEntry (c n) (dims n) (1 - Pm n - Lam n) x a b|
      ≤ sbar * ‖Xi‖ + sbar * (B ^ 2 * (1 + Kbd)) * aN n := by
    rw [abs_mul]
    have hmul : |s ω| * |biasEntry (c n) (dims n) (1 - Pm n - Lam n) x a b|
        ≤ sbar * (‖Xi‖ + B ^ 2 * ((Pm n).trace + (Lam n).trace)) := by
      refine mul_le_mul (hs ω) hbias (abs_nonneg _) hsnn
    nlinarith [hmul, hdiv, hsnn]
  show |s ω * biasEntry (c n) (dims n) (1 - Pm n - Lam n) x a b / aN n|
      ≤ |sbar * (‖Xi‖ / aN n)| + |sbar * (B ^ 2 * (1 + Kbd))|
  have habs1 : |sbar * (‖Xi‖ / aN n)| = sbar * (‖Xi‖ / aN n) :=
    abs_of_nonneg (mul_nonneg hsnn (div_nonneg hnrm haN0.le))
  have habs2 : sbar * (B ^ 2 * (1 + Kbd)) ≤ |sbar * (B ^ 2 * (1 + Kbd))| := le_abs_self _
  rw [abs_div, abs_of_pos haN0, habs1, div_le_iff₀ haN0]
  have hexp : (sbar * (‖Xi‖ / aN n) + |sbar * (B ^ 2 * (1 + Kbd))|) * aN n
      = sbar * ‖Xi‖ + |sbar * (B ^ 2 * (1 + Kbd))| * aN n := by
    field_simp
  rw [hexp]
  nlinarith [hnum, habs2, haN0]

end CaseTwoBiasSeq

/-! ### The meat entry as a quadratic form -/

section MeatBridge

variable {O K D L : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [DecidableEq D] [Fintype L] [DecidableEq L]
variable {Ω : Type*}

omit [DecidableEq O] [Fintype K] [DecidableEq K] [DecidableEq D] [Fintype L] [DecidableEq L] in
/-- A bilinear form written as a double sum is a dot product. -/
theorem sum_bilin_eq_dotProduct (M : Matrix O O ℝ) (u : O → ℝ) :
    ∑ p : O, ∑ q : O, M p q * (u p * u q) = u ⬝ᵥ (M *ᵥ u) := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : (M *ᵥ u) p = ∑ q : O, M p q * u q := rfl
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

omit [DecidableEq O] [Fintype K] [DecidableEq K] [DecidableEq D] [Fintype L] [DecidableEq L] in
/-- `ε'(RWR)ε = (Rε)'W(Rε)` for a symmetric `R`. -/
theorem quadForm_conj_eq {R : Matrix O O ℝ} (hRs : Rᵀ = R) (W : Matrix O O ℝ) (e : O → ℝ) :
    ∑ p : O, ∑ q : O, (R * W * R) p q * (e p * e q)
      = ∑ o : O, ∑ o' : O, W o o' * ((R *ᵥ e) o * (R *ᵥ e) o') := by
  rw [sum_bilin_eq_dotProduct, sum_bilin_eq_dotProduct]
  have h1 : (R * W * R) *ᵥ e = R *ᵥ (W *ᵥ (R *ᵥ e)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRs]

/-- Entry `(a,b)` of `𝓜̂_CGM` at a realization, in inclusion–exclusion form
`∑_{∅≠A⊆{1..J}}(-1)^{|A|+1}∑_{g∈𝒢_A}ŝ_gŝ_g'`. -/
def meatCGM (c : D → O → L) (dims : Finset D) (X : O → K → Ω → ℝ) (v : O → Ω → ℝ)
    (a b : K) (ω : Ω) : ℝ :=
  ∑ A ∈ dims.powerset.filter (fun A => A.Nonempty), (-1 : ℝ) ^ (A.card + 1) *
    ∑ g ∈ cells c A, (∑ o ∈ g, X o a ω * v o ω) * (∑ o' ∈ g, X o' b ω * v o' ω)

/-- `𝓜̂_{CGM,ab} = ε'RW_{ab}Rε` when the residual is `Rε`, by Lemma SM.B.7
(`Cgm.meat_eq_linkedPairs`). -/
theorem meatCGM_eq_quadForm (c : D → O → L) (dims : Finset D) {R : Ω → Matrix O O ℝ}
    (hRs : ∀ ω, (R ω)ᵀ = R ω) (X : Ω → Matrix O K ℝ) (eps : O → Ω → ℝ) (a b : K) :
    meatCGM c dims (fun o k ω => X ω o k)
        (fun o ω => (R ω *ᵥ fun o' => eps o' ω) o) a b
      = Quadform.quadForm (fun ω => R ω * linkW c dims (X ω) a b * R ω) eps := by
  classical
  funext ω
  rw [meatCGM, Cgm.meat_eq_linkedPairs c dims (fun o k ω => X ω o k)
      (fun o ω => (R ω *ᵥ fun o' => eps o' ω) o) a b ω,
    Quadform.quadForm_eq_double_sum,
    quadForm_conj_eq (hRs ω) (linkW c dims (X ω) a b) (fun o' => eps o' ω)]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
  simp only [linkW_apply]
  split_ifs with h
  · ring
  · rw [zero_mul]

/-- The normalized form of `meatCGM_eq_quadForm`. -/
theorem normalizedMeatCGM_eq_quadForm (c : D → O → L) (dims : Finset D)
    {R : Ω → Matrix O O ℝ} (hRs : ∀ ω, (R ω)ᵀ = R ω) (X : Ω → Matrix O K ℝ)
    (eps : O → Ω → ℝ) (a b : K) :
    (fun ω => ((Fintype.card O : ℝ))⁻¹
        * meatCGM c dims (fun o k ω => X ω o k)
            (fun o ω => (R ω *ᵥ fun o' => eps o' ω) o) a b ω)
      = Quadform.quadForm (normalizedMeatEntry c dims R X a b) eps := by
  rw [meatCGM_eq_quadForm c dims hRs X eps a b]
  funext ω
  rw [Quadform.quadForm_apply, Quadform.quadForm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [normalizedMeatEntry]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

end MeatBridge

/-! ### Chebyshev's inequality for a conditional variance -/

section Chebyshev

variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `∫ Var(Z | 𝒟) = ∫ (Z - E[Z|𝒟])²`. -/
theorem integral_condVar_eq [IsFiniteMeasure P] (h𝒟 : 𝒟 ≤ mΩ) (Z : Ω → ℝ) :
    ∫ ω, ProbabilityTheory.condVar 𝒟 Z P ω ∂P
      = ∫ ω, (Z ω - (P[Z | 𝒟]) ω) ^ 2 ∂P := by
  have hfun : ProbabilityTheory.condVar 𝒟 Z P
      = P[fun ω => (Z ω - (P[Z | 𝒟]) ω) ^ 2 | 𝒟] := rfl
  rw [hfun]
  exact integral_condExp (μ := P) (m := 𝒟) h𝒟

/-- A conditional variance bounded by `M a_n²` makes the centered variable `O_p(a_n)`. -/
theorem chebyshev_bddInProb [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    {Z : ℕ → Ω → ℝ} {an : ℕ → ℝ} {M : ℝ}
    (han : ∀ n, 0 < an n) (hL2 : ∀ n, MemLp (Z n) 2 P)
    (hcv : ∀ n, ProbabilityTheory.condVar 𝒟 (Z n) P ≤ᵐ[P] fun _ => M * (an n) ^ 2) :
    Sequence.BddInProb P (fun n ω => (Z n ω - (P[Z n | 𝒟]) ω) / an n) := by
  have hd : ∀ n, MemLp (fun ω => Z n ω - (P[Z n | 𝒟]) ω) 2 P := fun n =>
    (hL2 n).sub ((hL2 n).condExp one_le_two)
  have hint : ∀ n, Integrable (fun ω => (Z n ω - (P[Z n | 𝒟]) ω) ^ 2) P :=
    fun n => (hd n).integrable_sq
  have hM : ∀ n, ∫ ω, (Z n ω - (P[Z n | 𝒟]) ω) ^ 2 ∂P ≤ M * (an n) ^ 2 := by
    intro n
    rw [← integral_condVar_eq 𝒟 h𝒟 (Z n)]
    have h2 : ∫ ω, ProbabilityTheory.condVar 𝒟 (Z n) P ω ∂P
        ≤ ∫ _ω : Ω, M * (an n) ^ 2 ∂P :=
      integral_mono_ae integrable_condExp (integrable_const _) (hcv n)
    simpa using h2
  have hB := PrimitiveDesign.bddInProb_of_integral_sq_le (P := P)
    (Nrm := fun n ω => |Z n ω - (P[Z n | 𝒟]) ω|)
    (S := fun n ω => (Z n ω - (P[Z n | 𝒟]) ω) ^ 2) (an := an) (M := M)
    han (fun _ _ => sq_nonneg _) (fun _ _ => abs_nonneg _)
    (fun _ _ => le_of_eq (Real.sqrt_sq_eq_abs _).symm)
    (fun n => (hint n).aemeasurable) hint hM
  refine PrimitiveDesign.bddInProb_of_abs_le_abs (fun n ω => le_of_eq ?_) hB
  rw [abs_div, abs_div, abs_abs]

end Chebyshev

/-! ### Proof of case (ii) -/

section CaseTwo

variable {O D L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, Nonempty (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Theorem 10**, case (ii), rate. `n⁻¹𝓜̂_CGM - S_n = O_p(d_[Δ]/n + [G_max/n]^{1/2})`, entry
by entry, for any number of maintained dimensions, with `X̃ = Q_[Δ]Θ` and
`S_n = σ²_ε n⁻¹∑_o x̃_ox̃_o'`. `hXi` is the conclusion of Lemma SM.B.9 and `hcv` that of
`condVar_normalizedMeatEntry_le`. -/
theorem caseTwo_bddInProb [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    {Pm Lam : ∀ n, Matrix (O n) (O n) ℝ} {xi : ∀ n, O n → K → Ω → ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ} {a b : K}
    {B sbar Kbd Jbd C : ℝ} {aN Gmax : ℕ → ℝ}
    (hPms : ∀ n, (Pm n)ᵀ = Pm n) (hPmi : ∀ n, Pm n * Pm n = Pm n)
    (hLs : ∀ n, (Lam n)ᵀ = Lam n) (hLi : ∀ n, Lam n * Lam n = Lam n)
    (hB : ∀ (n : ℕ) (ω : Ω), ∀ o : O n,
      ∑ k : K, PrimitiveDesign.within (Pm n) (xi n) ω o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hK : ∀ n, (Lam n).trace ≤ Kbd)
    (hJ : ∀ n, ((dims n).card : ℝ) ≤ Jbd) (hC : 0 ≤ C)
    (hPmle : ∀ n, (Pm n).trace ≤ aN n) (hone : ∀ n, 1 ≤ aN n)
    (hGsq : ∀ n, Gmax n * (Fintype.card (O n) : ℝ) ≤ (aN n) ^ 2)
    (hGnn : ∀ n, 0 ≤ Gmax n)
    (hXm : ∀ (n : ℕ) (o : O n) (k : K),
      StronglyMeasurable[𝒟] fun ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
    (hint : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
        * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o') P)
    (hint' : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      (if Linked (c n) (dims n) o o' then
          PrimitiveDesign.within (Pm n) (xi n) ω o a
            * PrimitiveDesign.within (Pm n) (xi n) ω o' b else 0)
        * (((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
            * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o')) P)
    (hcross : ∀ (n : ℕ) (o o' : O n),
      P[fun ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
          * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o' | 𝒟]
        =ᵐ[P] fun ω => s ω * (1 - Pm n - Lam n) o o')
    (hXi : Sequence.BddInProb P (fun n ω =>
      ‖PrimitiveDesign.xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖ / aN n))
    (hL2 : ∀ n, MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - Lam n)
        (fun ω => PrimitiveDesign.within (Pm n) (xi n) ω) a b) (eps n)) 2 P)
    (hcv : ∀ n, ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - Lam n)
          (fun ω => PrimitiveDesign.within (Pm n) (xi n) ω) a b) (eps n)) P
      ≤ᵐ[P] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ))))) :
    Sequence.BddInProb P (fun n ω =>
      (((Fintype.card (O n) : ℝ))⁻¹
            * meatCGM (c n) (dims n)
                (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
                (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω
          - s ω * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n,
              PrimitiveDesign.within (Pm n) (xi n) ω o a
                * PrimitiveDesign.within (Pm n) (xi n) ω o b))
        / (aN n / (Fintype.card (O n) : ℝ))) := by
  classical
  have hRs : ∀ n, ((1 : Matrix (O n) (O n) ℝ) - Pm n - Lam n)ᵀ = 1 - Pm n - Lam n := by
    intro n
    rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_one, hPms n, hLs n]
  have hcard : ∀ n : ℕ, (0 : ℝ) < (Fintype.card (O n) : ℝ) := fun n => by
    exact_mod_cast Fintype.card_pos (α := O n)
  have haN0 : ∀ n, (0 : ℝ) < aN n := fun n => lt_of_lt_of_le zero_lt_one (hone n)
  have hratio : ∀ n, (0 : ℝ) < aN n / (Fintype.card (O n) : ℝ) :=
    fun n => div_pos (haN0 n) (hcard n)
  set Z : ℕ → Ω → ℝ := fun n => Quadform.quadForm
    (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - Lam n)
      (fun ω => PrimitiveDesign.within (Pm n) (xi n) ω) a b) (eps n) with hZ
  -- the normalized meat entry is a quadratic form
  have hbridge : ∀ n, (fun ω => ((Fintype.card (O n) : ℝ))⁻¹
      * meatCGM (c n) (dims n)
          (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
          (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω) = Z n := fun n =>
    normalizedMeatCGM_eq_quadForm (c n) (dims n) (fun _ => hRs n)
      (fun ω => PrimitiveDesign.within (Pm n) (xi n) ω) (eps n) a b
  -- the conditional mean
  have hcond : ∀ n, (P[Z n | 𝒟]) =ᵐ[P] fun ω => ((Fintype.card (O n) : ℝ))⁻¹
      * (s ω * biasEntry (c n) (dims n) (1 - Pm n - Lam n)
          (PrimitiveDesign.within (Pm n) (xi n) ω) a b
        + s ω * ∑ o : O n, PrimitiveDesign.within (Pm n) (xi n) ω o a
            * PrimitiveDesign.within (Pm n) (xi n) ω o b) := by
    intro n
    have hbase : (P[fun ω => meatCGM (c n) (dims n)
          (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
          (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω | 𝒟])
        =ᵐ[P] fun ω => s ω * ((∑ o : O n, PrimitiveDesign.within (Pm n) (xi n) ω o a
                * PrimitiveDesign.within (Pm n) (xi n) ω o b * (1 - Pm n - Lam n) o o)
            + Cgm.xiMat (c n) (dims n) (1 - Pm n - Lam n)
                (PrimitiveDesign.within (Pm n) (xi n) ω) a b) :=
      Cgm.condExp_meatCGM (μ := P) 𝒟 (c := c n) (dims := dims n)
        (X := fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
        (nuh := fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o)
        (R := fun o o' _ => (1 - Pm n - Lam n) o o') (s := s) (a := a) (b := b)
        (hdims n) (hXm n) (hint n) (hint' n) (hcross n)
    have hsm : (P[fun ω => ((Fintype.card (O n) : ℝ))⁻¹
          * meatCGM (c n) (dims n)
              (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
              (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω | 𝒟])
        =ᵐ[P] fun ω => ((Fintype.card (O n) : ℝ))⁻¹
          * (P[fun ω => meatCGM (c n) (dims n)
              (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
              (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω | 𝒟]) ω :=
      condExp_smul (𝕜 := ℝ) (μ := P) ((Fintype.card (O n) : ℝ))⁻¹
        (fun ω => meatCGM (c n) (dims n)
          (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
          (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω) 𝒟
    have hZeq : (P[Z n | 𝒟]) =ᵐ[P] fun ω => ((Fintype.card (O n) : ℝ))⁻¹
        * (P[fun ω => meatCGM (c n) (dims n)
            (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
            (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω | 𝒟]) ω := by
      rw [← hbridge n]
      exact hsm
    filter_upwards [hZeq, hbase] with ω h1 h2
    rw [h1, h2, biasEntry]
    ring
  -- the fluctuation, by Chebyshev
  have hfl : Sequence.BddInProb P (fun n ω =>
      (Z n ω - (P[Z n | 𝒟]) ω) / (aN n / (Fintype.card (O n) : ℝ))) := by
    refine chebyshev_bddInProb 𝒟 h𝒟 (M := 3 * C * (B ^ 4 * Jbd)) hratio hL2 (fun n => ?_)
    filter_upwards [hcv n] with ω hω
    refine hω.trans ?_
    have hJ0 : (0 : ℝ) ≤ ((dims n).card : ℝ) := Nat.cast_nonneg _
    have hdiv : Gmax n / (Fintype.card (O n) : ℝ)
        ≤ (aN n / (Fintype.card (O n) : ℝ)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (hcard n) (pow_pos (hcard n) 2)]
      have h1 : Gmax n * (Fintype.card (O n) : ℝ) ^ 2
          ≤ (aN n) ^ 2 * (Fintype.card (O n) : ℝ) := by
        have h2 := hGsq n
        nlinarith [hcard n, hGnn n]
      linarith
    have hCB : (0 : ℝ) ≤ 3 * C * B ^ 4 := by positivity
    have hstep : ((dims n).card : ℝ) * (Gmax n / (Fintype.card (O n) : ℝ))
        ≤ Jbd * (aN n / (Fintype.card (O n) : ℝ)) ^ 2 := by
      have hq : (0 : ℝ) ≤ (aN n / (Fintype.card (O n) : ℝ)) ^ 2 := sq_nonneg _
      have hg : (0 : ℝ) ≤ Gmax n / (Fintype.card (O n) : ℝ) :=
        div_nonneg (hGnn n) (hcard n).le
      nlinarith [hJ n, hdiv]
    nlinarith [hstep, hCB]
  -- the bias
  have hbi := caseTwo_bias_bddInProb (P := P) c dims (Pm := Pm) (Lam := Lam) (xi := xi)
    (s := s) (a := a) (b := b) (B := B) (sbar := sbar) (Kbd := Kbd) (aN := aN)
    hPms hPmi hLs hLi hB hs hK hPmle hone hXi
  refine bddInProb_of_abs_le_add
    (Y := fun n ω => (Z n ω - (P[Z n | 𝒟]) ω) / (aN n / (Fintype.card (O n) : ℝ)))
    (W := fun n ω => s ω * biasEntry (c n) (dims n) (1 - Pm n - Lam n)
      (PrimitiveDesign.within (Pm n) (xi n) ω) a b / aN n) (fun n => ?_) hfl hbi
  filter_upwards [hcond n] with ω hω
  have hb : ((Fintype.card (O n) : ℝ))⁻¹
      * meatCGM (c n) (dims n)
          (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
          (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω = Z n ω :=
    congrFun (hbridge n) ω
  have hA : aN n ≠ 0 := (haN0 n).ne'
  have ht : (Fintype.card (O n) : ℝ) ≠ 0 := (hcard n).ne'
  have hsplit : (Z n ω - s ω * (((Fintype.card (O n) : ℝ))⁻¹
        * ∑ o : O n, PrimitiveDesign.within (Pm n) (xi n) ω o a
            * PrimitiveDesign.within (Pm n) (xi n) ω o b))
      / (aN n / (Fintype.card (O n) : ℝ))
      = (Z n ω - (P[Z n | 𝒟]) ω) / (aN n / (Fintype.card (O n) : ℝ))
        + s ω * biasEntry (c n) (dims n) (1 - Pm n - Lam n)
            (PrimitiveDesign.within (Pm n) (xi n) ω) a b / aN n := by
    rw [hω]
    field_simp
    ring
  rw [hb, hsplit]
  exact abs_add_le _ _

/-- An `O_p(a_n/n)` sequence with `a_n/n → 0` tends to zero in probability. -/
theorem caseTwo_tendstoInProb {aN : ℕ → ℝ} {Z : ℕ → Ω → ℝ}
    (hone : ∀ n, 1 ≤ aN n)
    (hB : Sequence.BddInProb P (fun n ω => Z n ω / (aN n / (Fintype.card (O n) : ℝ))))
    (hrate : Filter.Tendsto (fun n : ℕ => aN n / (Fintype.card (O n) : ℝ)) Filter.atTop
      (nhds 0)) :
    TendstoInMeasure P Z Filter.atTop (fun _ => (0 : ℝ)) := by
  have hcard : ∀ n : ℕ, (0 : ℝ) < (Fintype.card (O n) : ℝ) := fun n => by
    exact_mod_cast Fintype.card_pos (α := O n)
  have haN0 : ∀ n, (0 : ℝ) < aN n := fun n => lt_of_lt_of_le zero_lt_one (hone n)
  have hratio : ∀ n, (0 : ℝ) < aN n / (Fintype.card (O n) : ℝ) :=
    fun n => div_pos (haN0 n) (hcard n)
  refine Sequence.tendstoInProb_zero_of_bddInProb_mul
    (k := fun n => aN n / (Fintype.card (O n) : ℝ)) (fun n => (hratio n).le)
    (fun n => Filter.Eventually.of_forall fun ω => ?_) hB hrate
  have h0 : aN n / (Fintype.card (O n) : ℝ) ≠ 0 := (hratio n).ne'
  have hA : aN n ≠ 0 := (haN0 n).ne'
  have ht : (Fintype.card (O n) : ℝ) ≠ 0 := (hcard n).ne'
  rw [abs_div, abs_of_pos (hratio n)]
  refine le_of_eq ?_
  field_simp

/-- **Theorem 10**, case (ii). `n⁻¹𝓜̂_CGM - S_n ⟶^p 0`, entry by entry, for any number of
maintained dimensions. -/
theorem caseTwo_meat_tendstoInProb [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    {Pm Lam : ∀ n, Matrix (O n) (O n) ℝ} {xi : ∀ n, O n → K → Ω → ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ} {a b : K}
    {B sbar Kbd Jbd C : ℝ} {aN Gmax : ℕ → ℝ}
    (hPms : ∀ n, (Pm n)ᵀ = Pm n) (hPmi : ∀ n, Pm n * Pm n = Pm n)
    (hLs : ∀ n, (Lam n)ᵀ = Lam n) (hLi : ∀ n, Lam n * Lam n = Lam n)
    (hB : ∀ (n : ℕ) (ω : Ω), ∀ o : O n,
      ∑ k : K, PrimitiveDesign.within (Pm n) (xi n) ω o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hK : ∀ n, (Lam n).trace ≤ Kbd)
    (hJ : ∀ n, ((dims n).card : ℝ) ≤ Jbd) (hC : 0 ≤ C)
    (hPmle : ∀ n, (Pm n).trace ≤ aN n) (hone : ∀ n, 1 ≤ aN n)
    (hGsq : ∀ n, Gmax n * (Fintype.card (O n) : ℝ) ≤ (aN n) ^ 2)
    (hGnn : ∀ n, 0 ≤ Gmax n)
    (hXm : ∀ (n : ℕ) (o : O n) (k : K),
      StronglyMeasurable[𝒟] fun ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
    (hint : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
        * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o') P)
    (hint' : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      (if Linked (c n) (dims n) o o' then
          PrimitiveDesign.within (Pm n) (xi n) ω o a
            * PrimitiveDesign.within (Pm n) (xi n) ω o' b else 0)
        * (((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
            * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o')) P)
    (hcross : ∀ (n : ℕ) (o o' : O n),
      P[fun ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
          * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o' | 𝒟]
        =ᵐ[P] fun ω => s ω * (1 - Pm n - Lam n) o o')
    (hXi : Sequence.BddInProb P (fun n ω =>
      ‖PrimitiveDesign.xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖ / aN n))
    (hL2 : ∀ n, MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - Lam n)
        (fun ω => PrimitiveDesign.within (Pm n) (xi n) ω) a b) (eps n)) 2 P)
    (hcv : ∀ n, ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - Lam n)
          (fun ω => PrimitiveDesign.within (Pm n) (xi n) ω) a b) (eps n)) P
      ≤ᵐ[P] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ)))))
    (hrate : Filter.Tendsto (fun n : ℕ => aN n / (Fintype.card (O n) : ℝ)) Filter.atTop
      (nhds 0)) :
    TendstoInMeasure P (fun n ω =>
        ((Fintype.card (O n) : ℝ))⁻¹
              * meatCGM (c n) (dims n)
                  (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
                  (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω
            - s ω * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n,
                PrimitiveDesign.within (Pm n) (xi n) ω o a
                  * PrimitiveDesign.within (Pm n) (xi n) ω o b))
      Filter.atTop (fun _ => (0 : ℝ)) :=
  caseTwo_tendstoInProb hone
    (caseTwo_bddInProb 𝒟 h𝒟 c dims hdims hPms hPmi hLs hLi hB hs hK hJ hC hPmle hone hGsq
      hGnn hXm hint hint' hcross hXi hL2 hcv) hrate

end CaseTwo

/-! ### Case (i)

Case (i) of Theorem 10 states that if `J = 1` with the maintained dimension equal to
fixed-effect dimension `m`, and `(d_[Δ] - N_m + K)G^{(m)}_max = o(n)`, then
`n⁻¹𝓜̂_CGM - S_n = O_p([(d_[Δ]-N_m+K)G^{(m)}_max/n]^{1/2} + [G^{(m)}_max/n]^{1/2}) ⟶^p 0`.
The conditional bias is bounded deterministically by `bias_opNorm_le`; the fluctuation is bounded
by Chebyshev's inequality (hypothesis `hcv`). The residual is written as
`(I - P_m - A^{(m)} - Λ) *ᵥ ε`, and `hGpos` requires `G^{(m)}_max > 0`. -/


section CaseOneBiasFinite

variable {O K D L N : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [Fintype N] [DecidableEq N] [DecidableEq D] [DecidableEq L]

omit [DecidableEq D] in
theorem caseOne_bias_abs_le (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    (x : Matrix O K ℝ) {R Pi Pm A Lam : Matrix O O ℝ}
    (hPi : Pi = 1 - R) (hdecomp : Pi = Pm + A + Lam)
    (hPm : ∀ o o' : O,
      Pm o o' = if i o = i o' then ((Cgm.clusterCard i (i o) : ℝ))⁻¹ else 0)
    (hAsym : Aᵀ = A) (hAidem : A * A = A)
    (hLsym : Lamᵀ = Lam) (hLidem : Lam * Lam = Lam)
    (hXcl : ∀ (j : N) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O => i o = j), x o k = 0)
    {B Gmax : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hG : ∀ j : N, (Cgm.clusterCard i j : ℝ) ≤ Gmax) (a b : K) :
    |biasEntry c dims R x a b|
      ≤ B ^ 2 * (Real.sqrt (A.trace * (Gmax * (Fintype.card O : ℝ)))
          + Real.sqrt (Lam.trace * (Gmax * (Fintype.card O : ℝ)))) := by
  have hmat := bias_opNorm_le c hdims i hlink x hPi hdecomp hPm hAsym hAidem hLsym hLidem
    hXcl hB hG
  refine le_trans ?_ hmat
  exact abs_entry_le_l2_opNorm _ a b

end CaseOneBiasFinite

/-- The rate of case (i),
`[(d_[Δ]-N_m+K)G^{(m)}_max/n]^{1/2} + [G^{(m)}_max/n]^{1/2}`, with `trA = tr(A^{(m)})`,
`trL = tr(Λ)` and `Gmax = G^{(m)}_max`. -/
noncomputable def caseOneRate (trA trL Gmax nn : ℝ) : ℝ :=
  Real.sqrt ((trA + trL) * (Gmax / nn)) + Real.sqrt (Gmax / nn)

theorem caseOneRate_nonneg (trA trL Gmax nn : ℝ) : 0 ≤ caseOneRate trA trL Gmax nn := by
  unfold caseOneRate; positivity

theorem caseOneRate_pos {trA trL Gmax nn : ℝ} (hG : 0 < Gmax) (hn : 0 < nn) :
    0 < caseOneRate trA trL Gmax nn := by
  have h : 0 < Real.sqrt (Gmax / nn) := Real.sqrt_pos.2 (div_pos hG hn)
  unfold caseOneRate
  positivity

/-- `Gmax/n ≤ (rate)²`. -/
theorem div_le_caseOneRate_sq {trA trL Gmax nn : ℝ} (hG : 0 ≤ Gmax) (hn : 0 ≤ nn) :
    Gmax / nn ≤ caseOneRate trA trL Gmax nn ^ 2 := by
  have hg : (0 : ℝ) ≤ Gmax / nn := div_nonneg hG hn
  have h1 : Real.sqrt (Gmax / nn) ^ 2 = Gmax / nn := Real.sq_sqrt hg
  have h2 : (0 : ℝ) ≤ Real.sqrt ((trA + trL) * (Gmax / nn)) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ Real.sqrt (Gmax / nn) := Real.sqrt_nonneg _
  unfold caseOneRate
  nlinarith [h1, h2, h3]

section CaseOneBiasRate

variable {O K D L N : Type*}
variable [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]
variable [Fintype N] [DecidableEq N] [DecidableEq D] [DecidableEq L]
variable [Nonempty O]

omit [DecidableEq D] in
/-- The normalized conditional bias in case (i) satisfies `|bias_{ab}|/n ≤ 2B²·rate`. -/
theorem caseOne_bias_abs_div_le (c : D → O → L) {dims : Finset D} (hdims : dims.Nonempty)
    (i : O → N) (hlink : ∀ o o' : O, Linked c dims o o' ↔ i o = i o')
    (x : Matrix O K ℝ) {R Pi Pm A Lam : Matrix O O ℝ}
    (hPi : Pi = 1 - R) (hdecomp : Pi = Pm + A + Lam)
    (hPm : ∀ o o' : O,
      Pm o o' = if i o = i o' then ((Cgm.clusterCard i (i o) : ℝ))⁻¹ else 0)
    (hAsym : Aᵀ = A) (hAidem : A * A = A)
    (hLsym : Lamᵀ = Lam) (hLidem : Lam * Lam = Lam)
    (hXcl : ∀ (j : N) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O => i o = j), x o k = 0)
    {B Gmax : ℝ} (hB : ∀ o : O, ∑ k : K, x o k ^ 2 ≤ B ^ 2)
    (hGnn : 0 ≤ Gmax)
    (hG : ∀ j : N, (Cgm.clusterCard i j : ℝ) ≤ Gmax) (a b : K) :
    |biasEntry c dims R x a b| / (Fintype.card O : ℝ)
      ≤ 2 * B ^ 2 * caseOneRate A.trace Lam.trace Gmax (Fintype.card O : ℝ) := by
  classical
  have hn : (0 : ℝ) < (Fintype.card O : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := O)
  have hAnn : (0 : ℝ) ≤ A.trace := Cgm.trace_nonneg_of_symmProj hAsym hAidem
  have hLnn : (0 : ℝ) ≤ Lam.trace := Cgm.trace_nonneg_of_symmProj hLsym hLidem
  have hg : (0 : ℝ) ≤ Gmax / (Fintype.card O : ℝ) := div_nonneg hGnn hn.le
  have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
  have hbase := caseOne_bias_abs_le c hdims i hlink x hPi hdecomp hPm hAsym hAidem hLsym
    hLidem hXcl hB hG a b
  -- `√(t·(G·n)) = √(t·(G/n))·n`
  have hsplit : ∀ t : ℝ, 0 ≤ t →
      Real.sqrt (t * (Gmax * (Fintype.card O : ℝ)))
        = Real.sqrt (t * (Gmax / (Fintype.card O : ℝ))) * (Fintype.card O : ℝ) := by
    intro t ht
    have h1 : t * (Gmax * (Fintype.card O : ℝ))
        = t * (Gmax / (Fintype.card O : ℝ)) * (Fintype.card O : ℝ) ^ 2 := by
      field_simp
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hn.le]
  rw [hsplit A.trace hAnn, hsplit Lam.trace hLnn] at hbase
  -- each summand is `≤ √((trA+trΛ)g) ≤ rate`
  have hmono : ∀ t : ℝ, 0 ≤ t → t ≤ A.trace + Lam.trace →
      Real.sqrt (t * (Gmax / (Fintype.card O : ℝ)))
        ≤ caseOneRate A.trace Lam.trace Gmax (Fintype.card O : ℝ) := by
    intro t _ hle
    have h1 : Real.sqrt (t * (Gmax / (Fintype.card O : ℝ)))
        ≤ Real.sqrt ((A.trace + Lam.trace) * (Gmax / (Fintype.card O : ℝ))) :=
      Real.sqrt_le_sqrt (by nlinarith [hg])
    unfold caseOneRate
    linarith [Real.sqrt_nonneg (Gmax / (Fintype.card O : ℝ))]
  have h1 := hmono A.trace hAnn (by linarith)
  have h2 := hmono Lam.trace hLnn (by linarith)
  rw [div_le_iff₀ hn]
  refine hbase.trans ?_
  set u := Real.sqrt (A.trace * (Gmax / (Fintype.card O : ℝ))) with hu
  set v := Real.sqrt (Lam.trace * (Gmax / (Fintype.card O : ℝ))) with hv
  set r := caseOneRate A.trace Lam.trace Gmax (Fintype.card O : ℝ) with hr
  set nn := (Fintype.card O : ℝ) with hnn
  have h3 : u * nn + v * nn ≤ 2 * r * nn := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) hn.le, mul_nonneg (sub_nonneg.2 h2) hn.le]
  calc B ^ 2 * (u * nn + v * nn) ≤ B ^ 2 * (2 * r * nn) :=
        mul_le_mul_of_nonneg_left h3 hB2
    _ = 2 * B ^ 2 * r * nn := by ring

end CaseOneBiasRate

section CaseOneSeq

variable {O D L N : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, Nonempty (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable [∀ n, Fintype (N n)] [∀ n, DecidableEq (N n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [(n : ℕ) → DecidableEq (O n)] [∀ (n : ℕ), Nonempty (O n)]
  [(n : ℕ) → Fintype (N n)] in
/-- A matrix given entrywise as the cluster-mean projector of `i` is symmetric. -/
theorem transpose_eq_of_clusterMean {n : ℕ} {i : O n → N n} {Pm : Matrix (O n) (O n) ℝ}
    (hPm : ∀ o o' : O n,
      Pm o o' = if i o = i o' then ((Cgm.clusterCard i (i o) : ℝ))⁻¹ else 0) :
    Pmᵀ = Pm := by
  ext o o'
  rw [Matrix.transpose_apply, hPm o' o, hPm o o']
  by_cases h : i o = i o'
  · rw [h]
  · simp [h, Ne.symm h]

omit [(n : ℕ) → DecidableEq (D n)] [(n : ℕ) → Fintype (L n)] in
/-- The conditional bias in case (i) is `O_p(rate)`. -/
theorem caseOne_bias_bddInProb
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    (i : ∀ n, O n → N n)
    (hlink : ∀ (n : ℕ) (o o' : O n), Linked (c n) (dims n) o o' ↔ i n o = i n o')
    {Pm A Lam : ∀ n, Matrix (O n) (O n) ℝ} {Xr : ∀ n, Ω → Matrix (O n) K ℝ}
    {s : Ω → ℝ} {a b : K} {B sbar : ℝ} {Gmax : ℕ → ℝ}
    (hPm : ∀ (n : ℕ) (o o' : O n),
      Pm n o o' = if i n o = i n o' then ((Cgm.clusterCard (i n) (i n o) : ℝ))⁻¹ else 0)
    (hAsym : ∀ n, (A n)ᵀ = A n) (hAidem : ∀ n, A n * A n = A n)
    (hLsym : ∀ n, (Lam n)ᵀ = Lam n) (hLidem : ∀ n, Lam n * Lam n = Lam n)
    (hXcl : ∀ (n : ℕ) (ω : Ω) (j : N n) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O n => i n o = j), Xr n ω o k = 0)
    (hB : ∀ (n : ℕ) (ω : Ω), ∀ o : O n, ∑ k : K, Xr n ω o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar)
    (hGnn : ∀ n, 0 ≤ Gmax n)
    (hG : ∀ (n : ℕ) (j : N n), (Cgm.clusterCard (i n) j : ℝ) ≤ Gmax n) :
    Sequence.BddInProb P (fun n ω =>
      s ω * biasEntry (c n) (dims n) (1 - Pm n - A n - Lam n) (Xr n ω) a b
        / ((Fintype.card (O n) : ℝ)
            * caseOneRate (A n).trace (Lam n).trace (Gmax n)
                (Fintype.card (O n) : ℝ))) := by
  classical
  refine Sequence.bddInProb_of_abs_le_const (M := sbar * (2 * B ^ 2)) (fun n => ?_)
  filter_upwards with ω
  have hsnn : (0 : ℝ) ≤ sbar := le_trans (abs_nonneg (s ω)) (hs ω)
  have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
  have hn : (0 : ℝ) < (Fintype.card (O n) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := O n)
  set r := caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ) with hr
  have hrnn : (0 : ℝ) ≤ r := caseOneRate_nonneg _ _ _ _
  rcases eq_or_lt_of_le hrnn with hr0 | hrpos
  · rw [← hr0, mul_zero, div_zero, abs_zero]
    positivity
  · have hbd := caseOne_bias_abs_div_le (c n) (hdims n) (i n) (hlink n) (Xr n ω)
      (R := 1 - Pm n - A n - Lam n) (Pi := Pm n + A n + Lam n) (by abel) rfl (hPm n)
      (hAsym n) (hAidem n) (hLsym n) (hLidem n) (hXcl n ω) (hB n ω) (hGnn n) (hG n) a b
    rw [← hr, div_le_iff₀ hn] at hbd
    have hden : (0 : ℝ) < (Fintype.card (O n) : ℝ) * r := by positivity
    rw [abs_div, abs_mul, abs_of_pos hden, div_le_iff₀ hden]
    calc |s ω| * |biasEntry (c n) (dims n) (1 - Pm n - A n - Lam n) (Xr n ω) a b|
        ≤ sbar * (2 * B ^ 2 * r * (Fintype.card (O n) : ℝ)) :=
          mul_le_mul (hs ω) hbd (abs_nonneg _) hsnn
      _ = sbar * (2 * B ^ 2) * ((Fintype.card (O n) : ℝ) * r) := by ring

end CaseOneSeq

section CaseOne

variable {O D L N : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, Nonempty (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable [∀ n, Fintype (N n)] [∀ n, DecidableEq (N n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem caseOne_bddInProb [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    (i : ∀ n, O n → N n)
    (hlink : ∀ (n : ℕ) (o o' : O n), Linked (c n) (dims n) o o' ↔ i n o = i n o')
    {Pm A Lam : ∀ n, Matrix (O n) (O n) ℝ} {Xr : ∀ n, Ω → Matrix (O n) K ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ} {a b : K}
    {B sbar C : ℝ} {Gmax : ℕ → ℝ}
    (hPm : ∀ (n : ℕ) (o o' : O n),
      Pm n o o' = if i n o = i n o' then ((Cgm.clusterCard (i n) (i n o) : ℝ))⁻¹ else 0)
    (hAsym : ∀ n, (A n)ᵀ = A n) (hAidem : ∀ n, A n * A n = A n)
    (hLsym : ∀ n, (Lam n)ᵀ = Lam n) (hLidem : ∀ n, Lam n * Lam n = Lam n)
    (hXcl : ∀ (n : ℕ) (ω : Ω) (j : N n) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O n => i n o = j), Xr n ω o k = 0)
    (hB : ∀ (n : ℕ) (ω : Ω), ∀ o : O n, ∑ k : K, Xr n ω o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hJ : ∀ n, ((dims n).card : ℝ) ≤ 1) (hC : 0 ≤ C)
    (hGpos : ∀ n, 0 < Gmax n)
    (hG : ∀ (n : ℕ) (j : N n), (Cgm.clusterCard (i n) j : ℝ) ≤ Gmax n)
    (hXm : ∀ (n : ℕ) (o : O n) (k : K), StronglyMeasurable[𝒟] fun ω => Xr n ω o k)
    (hint : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
        * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o') P)
    (hint' : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      (if Linked (c n) (dims n) o o' then Xr n ω o a * Xr n ω o' b else 0)
        * (((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
            * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o')) P)
    (hcross : ∀ (n : ℕ) (o o' : O n),
      P[fun ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
          * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o' | 𝒟]
        =ᵐ[P] fun ω => s ω * (1 - Pm n - A n - Lam n) o o')
    (hL2 : ∀ n, MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - A n - Lam n)
        (fun ω => Xr n ω) a b) (eps n)) 2 P)
    (hcv : ∀ n, ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - A n - Lam n)
          (fun ω => Xr n ω) a b) (eps n)) P
      ≤ᵐ[P] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ))))) :
    Sequence.BddInProb P (fun n ω =>
      ((((Fintype.card (O n) : ℝ))⁻¹
            * meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
                (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω)
          - s ω * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n, Xr n ω o a * Xr n ω o b))
        / caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ)) := by
  classical
  have hPms : ∀ n, (Pm n)ᵀ = Pm n := fun n => transpose_eq_of_clusterMean (hPm n)
  have hRs : ∀ n, ((1 : Matrix (O n) (O n) ℝ) - Pm n - A n - Lam n)ᵀ
      = 1 - Pm n - A n - Lam n := by
    intro n
    rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_sub,
      Matrix.transpose_one, hPms n, hAsym n, hLsym n]
  have hcard : ∀ n : ℕ, (0 : ℝ) < (Fintype.card (O n) : ℝ) := fun n => by
    exact_mod_cast Fintype.card_pos (α := O n)
  have hrate : ∀ n, (0 : ℝ)
      < caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ) :=
    fun n => caseOneRate_pos (hGpos n) (hcard n)
  set Z : ℕ → Ω → ℝ := fun n => Quadform.quadForm
    (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - A n - Lam n)
      (fun ω => Xr n ω) a b) (eps n) with hZ
  have hbridge : ∀ n, (fun ω => ((Fintype.card (O n) : ℝ))⁻¹
      * meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
          (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω)
      = Z n := fun n =>
    normalizedMeatCGM_eq_quadForm (c n) (dims n) (fun _ => hRs n)
      (fun ω => Xr n ω) (eps n) a b
  have hcond : ∀ n, (P[Z n | 𝒟]) =ᵐ[P] fun ω => ((Fintype.card (O n) : ℝ))⁻¹
      * (s ω * biasEntry (c n) (dims n) (1 - Pm n - A n - Lam n) (Xr n ω) a b
        + s ω * ∑ o : O n, Xr n ω o a * Xr n ω o b) := by
    intro n
    have hbase : (P[fun ω => meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
          (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω | 𝒟])
        =ᵐ[P] fun ω => s ω * ((∑ o : O n, Xr n ω o a * Xr n ω o b
                * (1 - Pm n - A n - Lam n) o o)
            + Cgm.xiMat (c n) (dims n) (1 - Pm n - A n - Lam n) (Xr n ω) a b) :=
      Cgm.condExp_meatCGM (μ := P) 𝒟 (c := c n) (dims := dims n)
        (X := fun o k ω => Xr n ω o k)
        (nuh := fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o)
        (R := fun o o' _ => (1 - Pm n - A n - Lam n) o o') (s := s) (a := a) (b := b)
        (hdims n) (hXm n) (hint n) (hint' n) (hcross n)
    have hsm : (P[fun ω => ((Fintype.card (O n) : ℝ))⁻¹
          * meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
              (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω | 𝒟])
        =ᵐ[P] fun ω => ((Fintype.card (O n) : ℝ))⁻¹
          * (P[fun ω => meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
              (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o)
              a b ω | 𝒟]) ω :=
      condExp_smul (𝕜 := ℝ) (μ := P) ((Fintype.card (O n) : ℝ))⁻¹
        (fun ω => meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
          (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω) 𝒟
    have hZeq : (P[Z n | 𝒟]) =ᵐ[P] fun ω => ((Fintype.card (O n) : ℝ))⁻¹
        * (P[fun ω => meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
            (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o)
            a b ω | 𝒟]) ω := by
      rw [← hbridge n]
      exact hsm
    filter_upwards [hZeq, hbase] with ω h1 h2
    rw [h1, h2, biasEntry]
    ring
  have hfl : Sequence.BddInProb P (fun n ω =>
      (Z n ω - (P[Z n | 𝒟]) ω)
        / caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ)) := by
    refine chebyshev_bddInProb 𝒟 h𝒟 (M := 3 * C * B ^ 4) hrate hL2 (fun n => ?_)
    filter_upwards [hcv n] with ω hω
    refine hω.trans ?_
    have hCB : (0 : ℝ) ≤ 3 * C * B ^ 4 := by positivity
    have hg : (0 : ℝ) ≤ Gmax n / (Fintype.card (O n) : ℝ) :=
      div_nonneg (hGpos n).le (hcard n).le
    have hsq := div_le_caseOneRate_sq (trA := (A n).trace) (trL := (Lam n).trace)
      (hGpos n).le (hcard n).le
    have hstep : ((dims n).card : ℝ) * (Gmax n / (Fintype.card (O n) : ℝ))
        ≤ caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ) ^ 2 := by
      nlinarith [hJ n, hsq, hg, Nat.cast_nonneg (α := ℝ) (dims n).card]
    nlinarith [hstep, hCB]
  have hbi := caseOne_bias_bddInProb (P := P) c dims hdims i hlink (Pm := Pm) (A := A)
    (Lam := Lam) (Xr := Xr) (s := s) (a := a) (b := b) (B := B) (sbar := sbar) (Gmax := Gmax)
    hPm hAsym hAidem hLsym hLidem hXcl hB hs (fun n => (hGpos n).le) hG
  refine bddInProb_of_abs_le_add
    (Y := fun n ω => (Z n ω - (P[Z n | 𝒟]) ω)
      / caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ))
    (W := fun n ω => s ω * biasEntry (c n) (dims n) (1 - Pm n - A n - Lam n) (Xr n ω) a b
      / ((Fintype.card (O n) : ℝ)
          * caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ)))
    (fun n => ?_) hfl hbi
  filter_upwards [hcond n] with ω hω
  have hb : ((Fintype.card (O n) : ℝ))⁻¹
      * meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
          (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω = Z n ω :=
    congrFun (hbridge n) ω
  have ht : (Fintype.card (O n) : ℝ) ≠ 0 := (hcard n).ne'
  have hrn : caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ) ≠ 0 :=
    (hrate n).ne'
  have hsplit : (Z n ω - s ω * (((Fintype.card (O n) : ℝ))⁻¹
        * ∑ o : O n, Xr n ω o a * Xr n ω o b))
      / caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ)
      = (Z n ω - (P[Z n | 𝒟]) ω)
          / caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ)
        + s ω * biasEntry (c n) (dims n) (1 - Pm n - A n - Lam n) (Xr n ω) a b
            / ((Fintype.card (O n) : ℝ)
                * caseOneRate (A n).trace (Lam n).trace (Gmax n)
                    (Fintype.card (O n) : ℝ)) := by
    rw [hω]
    field_simp
    ring
  rw [hb, hsplit]
  exact abs_add_le _ _

end CaseOne

section CaseOneLimit

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, Nonempty (O n)]
variable {D L N : ℕ → Type*} [∀ n, DecidableEq (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable [∀ n, Fintype (N n)] [∀ n, DecidableEq (N n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A sequence that is `O_p(a_n)` with `a_n → 0` tends to zero in probability. -/
theorem tendstoInProb_of_bddInProb_div {rate : ℕ → ℝ} {Z : ℕ → Ω → ℝ}
    (hpos : ∀ n, 0 < rate n)
    (hB : Sequence.BddInProb P (fun n ω => Z n ω / rate n))
    (hr : Filter.Tendsto rate Filter.atTop (nhds 0)) :
    TendstoInMeasure P Z Filter.atTop (fun _ => (0 : ℝ)) := by
  refine Sequence.tendstoInProb_zero_of_bddInProb_mul (k := rate) (fun n => (hpos n).le)
    (fun n => Filter.Eventually.of_forall fun ω => ?_) hB hr
  rw [abs_div, abs_of_pos (hpos n)]
  refine le_of_eq ?_
  field_simp
  rw [mul_div_assoc, div_self (hpos n).ne', mul_one]

end CaseOneLimit

section CaseOneAll

variable {O D L N : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, Nonempty (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable [∀ n, Fintype (N n)] [∀ n, DecidableEq (N n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem caseOne_meat_tendstoInProb [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    (i : ∀ n, O n → N n)
    (hlink : ∀ (n : ℕ) (o o' : O n), Linked (c n) (dims n) o o' ↔ i n o = i n o')
    {Pm A Lam : ∀ n, Matrix (O n) (O n) ℝ} {Xr : ∀ n, Ω → Matrix (O n) K ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ} {a b : K}
    {B sbar C : ℝ} {Gmax : ℕ → ℝ}
    (hPm : ∀ (n : ℕ) (o o' : O n),
      Pm n o o' = if i n o = i n o' then ((Cgm.clusterCard (i n) (i n o) : ℝ))⁻¹ else 0)
    (hAsym : ∀ n, (A n)ᵀ = A n) (hAidem : ∀ n, A n * A n = A n)
    (hLsym : ∀ n, (Lam n)ᵀ = Lam n) (hLidem : ∀ n, Lam n * Lam n = Lam n)
    (hXcl : ∀ (n : ℕ) (ω : Ω) (j : N n) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O n => i n o = j), Xr n ω o k = 0)
    (hB : ∀ (n : ℕ) (ω : Ω), ∀ o : O n, ∑ k : K, Xr n ω o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hJ : ∀ n, ((dims n).card : ℝ) ≤ 1) (hC : 0 ≤ C)
    (hGpos : ∀ n, 0 < Gmax n)
    (hG : ∀ (n : ℕ) (j : N n), (Cgm.clusterCard (i n) j : ℝ) ≤ Gmax n)
    (hXm : ∀ (n : ℕ) (o : O n) (k : K), StronglyMeasurable[𝒟] fun ω => Xr n ω o k)
    (hint : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
        * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o') P)
    (hint' : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      (if Linked (c n) (dims n) o o' then Xr n ω o a * Xr n ω o' b else 0)
        * (((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
            * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o')) P)
    (hcross : ∀ (n : ℕ) (o o' : O n),
      P[fun ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
          * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o' | 𝒟]
        =ᵐ[P] fun ω => s ω * (1 - Pm n - A n - Lam n) o o')
    (hL2 : ∀ n, MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - A n - Lam n)
        (fun ω => Xr n ω) a b) (eps n)) 2 P)
    (hcv : ∀ n, ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - A n - Lam n)
          (fun ω => Xr n ω) a b) (eps n)) P
      ≤ᵐ[P] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ)))))
    (hrate : Filter.Tendsto (fun n : ℕ =>
        caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ))
      Filter.atTop (nhds 0)) :
    TendstoInMeasure P (fun n ω =>
        (((Fintype.card (O n) : ℝ))⁻¹
              * meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k)
                  (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o) a b ω)
          - s ω * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n, Xr n ω o a * Xr n ω o b))
      Filter.atTop (fun _ => (0 : ℝ)) := by
  have hcard : ∀ n : ℕ, (0 : ℝ) < (Fintype.card (O n) : ℝ) := fun n => by
    exact_mod_cast Fintype.card_pos (α := O n)
  exact tendstoInProb_of_bddInProb_div (fun n => caseOneRate_pos (hGpos n) (hcard n))
    (caseOne_bddInProb 𝒟 h𝒟 c dims hdims i hlink hPm hAsym hAidem hLsym hLidem hXcl hB hs
      hJ hC hGpos hG hXm hint hint' hcross hL2 hcv) hrate

end CaseOneAll

/-! ### Consistency of the variance estimator

With `V̂_CGM = (X̃'X̃)⁻¹𝓜̂_CGM(X̃'X̃)⁻¹`, the limit follows from `Vhat.tendstoInProb_nVhat`.
`hH` and `hG : n⁻¹X̃'X̃ ⟶^p H` are the design assumption, `hM` is the conclusion of case (i) or
case (ii) at every entry, and `hS : S_n ⟶^p S`. -/


section NVhatCGM

variable {O D L : Type*} [Fintype O] [DecidableEq O]
variable [DecidableEq D] [Fintype L] [DecidableEq L]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*}

/-- `𝓜̂_CGM` as a `K × K` matrix. -/
def meatCGMMat (c : D → O → L) (dims : Finset D) (X : O → K → Ω → ℝ) (v : O → Ω → ℝ)
    (ω : Ω) : Matrix K K ℝ :=
  Matrix.of fun a b => meatCGM c dims X v a b ω

omit [DecidableEq D] [Fintype L] [Fintype K] [DecidableEq K] in
@[simp] theorem meatCGMMat_apply (c : D → O → L) (dims : Finset D) (X : O → K → Ω → ℝ)
    (v : O → Ω → ℝ) (ω : Ω) (a b : K) :
    meatCGMMat c dims X v ω a b = meatCGM c dims X v a b ω := rfl

end NVhatCGM

section NVhatCGMLimit

open Filter

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Theorem 10**, `nV̂_CGM ⟶^p H⁻¹SH⁻¹`, with `V̂_CGM = (X̃'X̃)⁻¹𝓜̂_CGM(X̃'X̃)⁻¹`. `Gr`, `Mh`
and `Sn` are the unnormalized `X̃'X̃`, `𝓜̂_CGM` and `S_n`; `hM` is taken entry by entry. -/
theorem tendstoInProb_nVhatCGM {Gr Mh Sn : ℕ → Ω → Matrix K K ℝ} {H S : Matrix K K ℝ}
    {N : ℕ → ℝ} (hN : ∀ n, 0 < N n) (hH : H.PosDef)
    (hG : TendstoInMeasure P (fun n ω => frobNorm ((N n)⁻¹ • Gr n ω - H))
      atTop (fun _ => (0 : ℝ)))
    (hM : ∀ a b : K, TendstoInMeasure P
      (fun n ω => (N n)⁻¹ * Mh n ω a b - Sn n ω a b) atTop (fun _ => (0 : ℝ)))
    (hS : TendstoInMeasure P (fun n ω => frobNorm (Sn n ω - S)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P
      (fun n ω => frobNorm (N n • ((Gr n ω)⁻¹ * Mh n ω * (Gr n ω)⁻¹) - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  refine Vhat.tendstoInProb_nVhat hN hH hG ?_ hS
  refine Vhat.tendstoInProb_frobNorm_of_entries (fun a b => ?_)
  have heq : (fun (n : ℕ) (ω : Ω) => ((N n)⁻¹ • Mh n ω) a b - Sn n ω a b)
      = fun (n : ℕ) (ω : Ω) => (N n)⁻¹ * Mh n ω a b - Sn n ω a b := by
    funext n ω
    simp [Matrix.smul_apply]
  rw [heq]
  exact hM a b

end NVhatCGMLimit

section NVhatCGMDesign

open Filter

variable {O D L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, Nonempty (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

omit [(n : ℕ) → DecidableEq (D n)] [(n : ℕ) → Fintype (L n)] in
/-- `nV̂_CGM ⟶^p H⁻¹SH⁻¹` with `X̃'X̃` and `𝓜̂_CGM` written out and `S_n = σ²_ε n⁻¹X̃'X̃`. `hM`
is the conclusion of `caseOne_meat_tendstoInProb` or `caseTwo_meat_tendstoInProb`. -/
theorem tendstoInProb_nVhatCGM_of_entries
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n))
    {Xr : ∀ n, Ω → Matrix (O n) K ℝ} {v : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ}
    {H S : Matrix K K ℝ} (hH : H.PosDef)
    (hG : TendstoInMeasure P (fun n ω =>
        frobNorm (((Fintype.card (O n) : ℝ))⁻¹ • ((Xr n ω)ᵀ * Xr n ω) - H))
      atTop (fun _ => (0 : ℝ)))
    (hM : ∀ a b : K, TendstoInMeasure P (fun n ω =>
        ((Fintype.card (O n) : ℝ))⁻¹
            * meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k) (v n) a b ω
          - s ω * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n, Xr n ω o a * Xr n ω o b))
      atTop (fun _ => (0 : ℝ)))
    (hS : TendstoInMeasure P (fun n ω =>
        frobNorm (s ω • (((Fintype.card (O n) : ℝ))⁻¹ • ((Xr n ω)ᵀ * Xr n ω)) - S))
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω =>
        frobNorm ((Fintype.card (O n) : ℝ) •
            (((Xr n ω)ᵀ * Xr n ω)⁻¹
              * meatCGMMat (c n) (dims n) (fun o k ω => Xr n ω o k) (v n) ω
              * ((Xr n ω)ᵀ * Xr n ω)⁻¹)
          - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  have hcard : ∀ n : ℕ, (0 : ℝ) < (Fintype.card (O n) : ℝ) := fun n => by
    exact_mod_cast Fintype.card_pos (α := O n)
  refine tendstoInProb_nVhatCGM (N := fun n => (Fintype.card (O n) : ℝ))
    (Gr := fun n ω => (Xr n ω)ᵀ * Xr n ω)
    (Mh := fun n ω => meatCGMMat (c n) (dims n) (fun o k ω => Xr n ω o k) (v n) ω)
    (Sn := fun n ω => s ω • (((Fintype.card (O n) : ℝ))⁻¹ • ((Xr n ω)ᵀ * Xr n ω)))
    hcard hH hG (fun a b => ?_) hS
  have heq : (fun (n : ℕ) (ω : Ω) =>
        ((Fintype.card (O n) : ℝ))⁻¹
            * meatCGMMat (c n) (dims n) (fun o k ω => Xr n ω o k) (v n) ω a b
          - (s ω • (((Fintype.card (O n) : ℝ))⁻¹ • ((Xr n ω)ᵀ * Xr n ω))) a b)
      = fun (n : ℕ) (ω : Ω) =>
        ((Fintype.card (O n) : ℝ))⁻¹
            * meatCGM (c n) (dims n) (fun o k ω => Xr n ω o k) (v n) a b ω
          - s ω * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n, Xr n ω o a * Xr n ω o b) := by
    funext n ω
    simp only [meatCGMMat_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.transpose_apply]
  rw [heq]
  exact hM a b

end NVhatCGMDesign

/-! ### Both cases composed with the variance estimator -/

section Compose

open Filter

variable {O D L N : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, Nonempty (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable [∀ n, Fintype (N n)] [∀ n, DecidableEq (N n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem caseOne_nVhatCGM_tendstoInProb [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    (i : ∀ n, O n → N n)
    (hlink : ∀ (n : ℕ) (o o' : O n), Linked (c n) (dims n) o o' ↔ i n o = i n o')
    {Pm A Lam : ∀ n, Matrix (O n) (O n) ℝ} {Xr : ∀ n, Ω → Matrix (O n) K ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ}
    {B sbar C : ℝ} {Gmax : ℕ → ℝ} {H S : Matrix K K ℝ}
    (hPm : ∀ (n : ℕ) (o o' : O n),
      Pm n o o' = if i n o = i n o' then ((Cgm.clusterCard (i n) (i n o) : ℝ))⁻¹ else 0)
    (hAsym : ∀ n, (A n)ᵀ = A n) (hAidem : ∀ n, A n * A n = A n)
    (hLsym : ∀ n, (Lam n)ᵀ = Lam n) (hLidem : ∀ n, Lam n * Lam n = Lam n)
    (hXcl : ∀ (n : ℕ) (ω : Ω) (j : N n) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O n => i n o = j), Xr n ω o k = 0)
    (hB : ∀ (n : ℕ) (ω : Ω), ∀ o : O n, ∑ k : K, Xr n ω o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hJ : ∀ n, ((dims n).card : ℝ) ≤ 1) (hC : 0 ≤ C)
    (hGpos : ∀ n, 0 < Gmax n)
    (hG : ∀ (n : ℕ) (j : N n), (Cgm.clusterCard (i n) j : ℝ) ≤ Gmax n)
    (hXm : ∀ (n : ℕ) (o : O n) (k : K), StronglyMeasurable[𝒟] fun ω => Xr n ω o k)
    (hint : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
        * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o') P)
    (hint' : ∀ (a b : K) (n : ℕ) (o o' : O n), Integrable (fun ω =>
      (if Linked (c n) (dims n) o o' then Xr n ω o a * Xr n ω o' b else 0)
        * (((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
            * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o')) P)
    (hcross : ∀ (n : ℕ) (o o' : O n),
      P[fun ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o
          * ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o' | 𝒟]
        =ᵐ[P] fun ω => s ω * (1 - Pm n - A n - Lam n) o o')
    (hL2 : ∀ (a b : K) (n : ℕ), MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - A n - Lam n)
        (fun ω => Xr n ω) a b) (eps n)) 2 P)
    (hcv : ∀ (a b : K) (n : ℕ), ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - A n - Lam n)
          (fun ω => Xr n ω) a b) (eps n)) P
      ≤ᵐ[P] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ)))))
    (hrate : Tendsto (fun n : ℕ =>
        caseOneRate (A n).trace (Lam n).trace (Gmax n) (Fintype.card (O n) : ℝ))
      atTop (nhds 0))
    (hH : H.PosDef)
    (hGram : TendstoInMeasure P (fun n ω =>
        frobNorm (((Fintype.card (O n) : ℝ))⁻¹ • ((Xr n ω)ᵀ * Xr n ω) - H))
      atTop (fun _ => (0 : ℝ)))
    (hSn : TendstoInMeasure P (fun n ω =>
        frobNorm (s ω • (((Fintype.card (O n) : ℝ))⁻¹ • ((Xr n ω)ᵀ * Xr n ω)) - S))
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω =>
        frobNorm ((Fintype.card (O n) : ℝ) •
            (((Xr n ω)ᵀ * Xr n ω)⁻¹
              * meatCGMMat (c n) (dims n) (fun o k ω => Xr n ω o k)
                  (fun o ω => ((1 - Pm n - A n - Lam n) *ᵥ fun p => eps n p ω) o) ω
              * ((Xr n ω)ᵀ * Xr n ω)⁻¹)
          - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) :=
  tendstoInProb_nVhatCGM_of_entries c dims hH hGram
    (fun a b => caseOne_meat_tendstoInProb 𝒟 h𝒟 c dims hdims i hlink hPm hAsym hAidem hLsym
      hLidem hXcl hB hs hJ hC hGpos hG hXm hint (hint' a b) hcross (hL2 a b) (hcv a b) hrate)
    hSn

end Compose

section ComposeTwo

open Filter

variable {O D L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, Nonempty (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem caseTwo_nVhatCGM_tendstoInProb [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    {Pm Lam : ∀ n, Matrix (O n) (O n) ℝ} {xi : ∀ n, O n → K → Ω → ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ}
    {B sbar Kbd Jbd C : ℝ} {aN Gmax : ℕ → ℝ} {H S : Matrix K K ℝ}
    (hPms : ∀ n, (Pm n)ᵀ = Pm n) (hPmi : ∀ n, Pm n * Pm n = Pm n)
    (hLs : ∀ n, (Lam n)ᵀ = Lam n) (hLi : ∀ n, Lam n * Lam n = Lam n)
    (hB : ∀ (n : ℕ) (ω : Ω), ∀ o : O n,
      ∑ k : K, PrimitiveDesign.within (Pm n) (xi n) ω o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hK : ∀ n, (Lam n).trace ≤ Kbd)
    (hJ : ∀ n, ((dims n).card : ℝ) ≤ Jbd) (hC : 0 ≤ C)
    (hPmle : ∀ n, (Pm n).trace ≤ aN n) (hone : ∀ n, 1 ≤ aN n)
    (hGsq : ∀ n, Gmax n * (Fintype.card (O n) : ℝ) ≤ (aN n) ^ 2)
    (hGnn : ∀ n, 0 ≤ Gmax n)
    (hXm : ∀ (n : ℕ) (o : O n) (k : K),
      StronglyMeasurable[𝒟] fun ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
    (hint : ∀ (n : ℕ) (o o' : O n), Integrable (fun ω =>
      ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
        * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o') P)
    (hint' : ∀ (a b : K) (n : ℕ) (o o' : O n), Integrable (fun ω =>
      (if Linked (c n) (dims n) o o' then
          PrimitiveDesign.within (Pm n) (xi n) ω o a
            * PrimitiveDesign.within (Pm n) (xi n) ω o' b else 0)
        * (((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
            * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o')) P)
    (hcross : ∀ (n : ℕ) (o o' : O n),
      P[fun ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o
          * ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o' | 𝒟]
        =ᵐ[P] fun ω => s ω * (1 - Pm n - Lam n) o o')
    (hXi : Sequence.BddInProb P (fun n ω =>
      ‖PrimitiveDesign.xiSharp (c n) (dims n) (Pm n) (Lam n) (xi n) ω‖ / aN n))
    (hL2 : ∀ (a b : K) (n : ℕ), MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - Lam n)
        (fun ω => PrimitiveDesign.within (Pm n) (xi n) ω) a b) (eps n)) 2 P)
    (hcv : ∀ (a b : K) (n : ℕ), ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n - Lam n)
          (fun ω => PrimitiveDesign.within (Pm n) (xi n) ω) a b) (eps n)) P
      ≤ᵐ[P] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ)))))
    (hrate : Tendsto (fun n : ℕ => aN n / (Fintype.card (O n) : ℝ)) atTop (nhds 0))
    (hH : H.PosDef)
    (hGram : TendstoInMeasure P (fun n ω =>
        frobNorm (((Fintype.card (O n) : ℝ))⁻¹
          • ((PrimitiveDesign.within (Pm n) (xi n) ω)ᵀ
              * PrimitiveDesign.within (Pm n) (xi n) ω) - H))
      atTop (fun _ => (0 : ℝ)))
    (hSn : TendstoInMeasure P (fun n ω =>
        frobNorm (s ω • (((Fintype.card (O n) : ℝ))⁻¹
          • ((PrimitiveDesign.within (Pm n) (xi n) ω)ᵀ
              * PrimitiveDesign.within (Pm n) (xi n) ω)) - S))
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n ω =>
        frobNorm ((Fintype.card (O n) : ℝ) •
            (((PrimitiveDesign.within (Pm n) (xi n) ω)ᵀ
                * PrimitiveDesign.within (Pm n) (xi n) ω)⁻¹
              * meatCGMMat (c n) (dims n)
                  (fun o k ω => PrimitiveDesign.within (Pm n) (xi n) ω o k)
                  (fun o ω => ((1 - Pm n - Lam n) *ᵥ fun p => eps n p ω) o) ω
              * ((PrimitiveDesign.within (Pm n) (xi n) ω)ᵀ
                  * PrimitiveDesign.within (Pm n) (xi n) ω)⁻¹)
          - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) :=
  tendstoInProb_nVhatCGM_of_entries c dims hH hGram
    (fun a b => caseTwo_meat_tendstoInProb 𝒟 h𝒟 c dims hdims hPms hPmi hLs hLi hB hs hK hJ hC
      hPmle hone hGsq hGnn hXm hint (hint' a b) hcross hXi (hL2 a b) (hcv a b) hrate)
    hSn

end ComposeTwo

/-! ### Examples -/

section Witness

/-- `condMean_sub_target_eq` at `O = {1,2}` in a single cluster, `K = 1`, `X̃ = (1,-1)'`,
`Π = P_m = (1/2)ιι'` and `R = I - P_m`. -/
theorem condMean_sub_target_eq_witness :
    (∑ o : Fin 2, Cgm.witnessX o 0 * Cgm.witnessX o 0 * (1 - Cgm.witnessPm) o o)
        + Cgm.xiMat (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
            (1 - Cgm.witnessPm) Cgm.witnessX 0 0
        - ∑ o : Fin 2, Cgm.witnessX o 0 * Cgm.witnessX o 0
      = -((Cgm.witnessXᵀ
            * Cgm.blockPart (fun _ : Fin 2 => (0 : Fin 1)) Cgm.witnessPm
            * Cgm.witnessX) 0 0) := by
  refine condMean_sub_target_eq (fun _ _ => (0 : Fin 1)) (Finset.singleton_nonempty 0)
    (fun _ => (0 : Fin 1)) ?_ ?_ Cgm.witnessX 0 0
  · exact fun o o' => ⟨fun _ => rfl, fun _ => ⟨0, Finset.mem_singleton_self 0, rfl⟩⟩
  · exact (sub_sub_cancel _ _).symm

/-- `condMean_sub_target_eq` at `X̃ = (1,-1)'`, `R = 0` and `Π = I`, where both sides equal
`-2`. -/
theorem condMean_sub_target_eq_witness_nonzero :
    ((∑ o : Fin 2, Cgm.witnessX o 0 * Cgm.witnessX o 0
            * (0 : Matrix (Fin 2) (Fin 2) ℝ) o o)
        + Cgm.xiMat (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
            (0 : Matrix (Fin 2) (Fin 2) ℝ) Cgm.witnessX 0 0
        - ∑ o : Fin 2, Cgm.witnessX o 0 * Cgm.witnessX o 0
      = -((Cgm.witnessXᵀ
            * Cgm.blockPart (fun _ : Fin 2 => (0 : Fin 1)) (1 : Matrix (Fin 2) (Fin 2) ℝ)
            * Cgm.witnessX) 0 0))
    ∧ -((Cgm.witnessXᵀ
            * Cgm.blockPart (fun _ : Fin 2 => (0 : Fin 1)) (1 : Matrix (Fin 2) (Fin 2) ℝ)
            * Cgm.witnessX) 0 0) = (-2 : ℝ) := by
  constructor
  · refine condMean_sub_target_eq (fun _ _ => (0 : Fin 1)) (Finset.singleton_nonempty 0)
      (fun _ => (0 : Fin 1)) ?_ ?_ Cgm.witnessX 0 0
    · exact fun o o' => ⟨fun _ => rfl, fun _ => ⟨0, Finset.mem_singleton_self 0, rfl⟩⟩
    · rw [sub_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.mul_apply, Cgm.blockPart_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Matrix.one_apply, Cgm.witnessX, Matrix.of_apply]
    norm_num

/-- `blockPart_hat_opNorm_le` at a two-observation design with `A^{(m)} = Λ = 0`. -/
theorem blockPart_hat_opNorm_le_witness :
    ‖Cgm.witnessXᵀ
        * Cgm.blockPart (fun _ : Fin 2 => (0 : Fin 1)) Cgm.witnessPm
        * Cgm.witnessX‖
      ≤ (1 : ℝ) ^ 2 *
          (Real.sqrt ((0 : Matrix (Fin 2) (Fin 2) ℝ).trace
              * (2 * (Fintype.card (Fin 2) : ℝ)))
            + Real.sqrt ((0 : Matrix (Fin 2) (Fin 2) ℝ).trace
              * (2 * (Fintype.card (Fin 2) : ℝ)))) := by
  have hcard : Cgm.clusterCard (fun _ : Fin 2 => (0 : Fin 1)) 0 = 2 := by
    simp [Cgm.clusterCard]
  refine blockPart_hat_opNorm_le (fun _ => (0 : Fin 1)) Cgm.witnessX
    (Pm := Cgm.witnessPm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [add_zero, add_zero]
  · intro o o'
    rw [Cgm.witnessPm]
    simp only [Matrix.of_apply, hcard]
    norm_num
  · simp
  · simp
  · simp
  · simp
  · intro j k
    have hfil : (Finset.univ.filter fun o : Fin 2 => (0 : Fin 1) = j)
        = (Finset.univ : Finset (Fin 2)) := by
      refine Finset.filter_true_of_mem fun o _ => ?_
      exact Subsingleton.elim _ _
    rw [hfil, Fin.sum_univ_two]
    simp [Cgm.witnessX]
  · intro o
    rw [Fin.sum_univ_one]
    fin_cases o <;> norm_num [Cgm.witnessX]
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hj, hcard]
    norm_num

/-- `rectFrobSq_conj_linkW_le` at `O = {1,2}`, a single cluster, `X̃ = (1,-1)'`, `R = I`,
`B = 1`, `G_max = 2`, `J = 1`; both sides equal `4`. -/
theorem rectFrobSq_conj_linkW_le_witness :
    rectFrobSq ((1 : Matrix (Fin 2) (Fin 2) ℝ)
        * linkW (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1)) Cgm.witnessX 0 0
        * (1 : Matrix (Fin 2) (Fin 2) ℝ))
      ≤ (1 : ℝ) ^ 4
          * ((({0} : Finset (Fin 1)).card : ℝ) * (2 * (Fintype.card (Fin 2) : ℝ))) := by
  refine rectFrobSq_conj_linkW_le (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
    Cgm.witnessX (Matrix.transpose_one) (one_mul _) ?_ ?_ 0 0
  · intro o
    rw [Fin.sum_univ_one]
    fin_cases o <;> norm_num [Cgm.witnessX]
  · intro j _ l
    have hfil : (Finset.univ.filter fun o : Fin 2 => (0 : Fin 1) = l)
        = (Finset.univ : Finset (Fin 2)) := by
      refine Finset.filter_true_of_mem fun o _ => ?_
      exact Subsingleton.elim _ _
    rw [Cgm.clusterCard, hfil]
    norm_num

/-- `condVar_normalizedMeatEntry_le` at `Ω = Unit`, `μ = dirac ()`, `𝒟 = ⊥`, `O = {1,2}` in a
single cluster, `R = I`, `X̃ = (1,-1)'`, `ε_o = 𝟙{o = 1}`, `C = B = 1`, `G_max = 2`. -/
theorem condVar_normalizedMeatEntry_le_witness :
    ProbabilityTheory.condVar (⊥ : MeasurableSpace Unit)
        (Quadform.quadForm
          (normalizedMeatEntry (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
            (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℝ))
            (fun _ : Unit => Cgm.witnessX) 0 0)
          (Quadform.witnessEps 0)) (Measure.dirac ())
      ≤ᵐ[Measure.dirac ()] fun _ : Unit =>
        3 * (1 : ℝ) * ((1 : ℝ) ^ 4
          * ((({0} : Finset (Fin 1)).card : ℝ) * (2 / (Fintype.card (Fin 2) : ℝ)))) := by
  have hWm : ∀ o o' : Fin 2, StronglyMeasurable[(⊥ : MeasurableSpace Unit)]
      fun ω => normalizedMeatEntry (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
        (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (fun _ : Unit => Cgm.witnessX) 0 0 ω o o' :=
    fun o o' => stronglyMeasurable_normalizedMeatEntry (⊥ : MeasurableSpace Unit)
      (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
      (R := fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (X := fun _ : Unit => Cgm.witnessX) 0 0
      (fun _ _ => stronglyMeasurable_const) (fun _ _ => stronglyMeasurable_const) o o'
  refine condVar_normalizedMeatEntry_le (⊥ : MeasurableSpace Unit) bot_le
    (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
    (eps := Quadform.witnessEps 0)
    (sig := fun o _ => if o = 0 then (1 : ℝ) else 0)
    (C := (1 : ℝ)) (B := (1 : ℝ)) (Gmax := (2 : ℝ))
    zero_le_one (fun _ => Matrix.transpose_one) (fun _ => one_mul _) ?_ ?_
    (Quadform.memLp_unit _)
    hWm
    (fun _ => Quadform.integrable_unit _) (fun _ => Quadform.integrable_unit _)
    (fun _ => Quadform.integrable_unit _) (fun _ => Quadform.integrable_unit _)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ o
    rw [Fin.sum_univ_one]
    fin_cases o <;> norm_num [Cgm.witnessX]
  · intro j _ l
    have hfil : (Finset.univ.filter fun o : Fin 2 => (0 : Fin 1) = l)
        = (Finset.univ : Finset (Fin 2)) :=
      Finset.filter_true_of_mem fun o _ => Subsingleton.elim _ _
    rw [Cgm.clusterCard, hfil]
    norm_num
  · intro o
    rw [Quadform.condExp_unit]
    exact Filter.Eventually.of_forall fun u => Quadform.witnessEps_mul_self 0 o u
  · intro o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps 0 o u * Quadform.witnessEps 0 o' u = (0 : ℝ)
    exact Quadform.witnessEps_mul_eq_zero 0 h u
  · intro o
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps 0 o u * Quadform.witnessEps 0 o u
        * (Quadform.witnessEps 0 o u * Quadform.witnessEps 0 o u) ≤ (1 : ℝ)
    rw [Quadform.witnessEps_mul_self 0 o u]
    by_cases h : o = 0 <;> simp [h]
  · intro o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps 0 o u * Quadform.witnessEps 0 o u
        * (Quadform.witnessEps 0 o' u * Quadform.witnessEps 0 o' u)
        = (if o = 0 then (1 : ℝ) else 0) * (if o' = 0 then (1 : ℝ) else 0)
    rw [Quadform.witnessEps_mul_self 0 o u, Quadform.witnessEps_mul_self 0 o' u]
  · intro a o o' h
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps 0 a u * Quadform.witnessEps 0 a u
        * (Quadform.witnessEps 0 o u * Quadform.witnessEps 0 o' u) = (0 : ℝ)
    rw [Quadform.witnessEps_mul_eq_zero 0 h u, mul_zero]
  · intro p q hp _ _ _
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show Quadform.witnessEps 0 p.1 u * Quadform.witnessEps 0 p.2 u
        * (Quadform.witnessEps 0 q.1 u * Quadform.witnessEps 0 q.2 u) = (0 : ℝ)
    rw [Quadform.witnessEps_mul_eq_zero 0 hp u, zero_mul]

/-- The bound of `rectFrobSq_conj_linkW_le_witness` holds with equality. -/
theorem rectFrobSq_conj_linkW_le_witness_sharp :
    rectFrobSq ((1 : Matrix (Fin 2) (Fin 2) ℝ)
        * linkW (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1)) Cgm.witnessX 0 0
        * (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 4
      ∧ (1 : ℝ) ^ 4
          * ((({0} : Finset (Fin 1)).card : ℝ) * (2 * (Fintype.card (Fin 2) : ℝ))) = 4 := by
  constructor
  · have hlink : ∀ o o' : Fin 2, Linked (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1)) o o' :=
      fun o o' => ⟨0, Finset.mem_singleton_self 0, rfl⟩
    simp only [rectFrobSq, one_mul, mul_one]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [linkW, hlink, Cgm.witnessX]
    norm_num
  · norm_num

/-! ### Examples for case (ii) -/

/-- `caseTwo_bias_abs_le` at `O = {1,2}`, `K = 1`, `X̃ = (1,-1)'`, `P_[Δ] = I` and `Λ = 0`, so
`R = 0`; both sides equal `2`. -/
theorem caseTwo_bias_abs_le_witness :
    |biasEntry (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
          (0 : Matrix (Fin 2) (Fin 2) ℝ) Cgm.witnessX 0 0|
      ≤ ‖Cgm.xiMat (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
            (0 : Matrix (Fin 2) (Fin 2) ℝ) Cgm.witnessX‖
        + (1 : ℝ) ^ 2 * ((1 : Matrix (Fin 2) (Fin 2) ℝ).trace
            + (0 : Matrix (Fin 2) (Fin 2) ℝ).trace) := by
  refine caseTwo_bias_abs_le (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
    (Pm := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (Lam := (0 : Matrix (Fin 2) (Fin 2) ℝ))
    (R := (0 : Matrix (Fin 2) (Fin 2) ℝ)) ?_ Matrix.transpose_one (one_mul _)
    Matrix.transpose_zero (by simp) Cgm.witnessX (B := (1 : ℝ)) ?_ 0 0
  · simp
  · intro o
    rw [Fin.sum_univ_one]
    fin_cases o <;> norm_num [Cgm.witnessX]

/-- The bound of `caseTwo_bias_abs_le_witness` holds with equality, since the bias is `-2`. -/
theorem caseTwo_bias_abs_le_witness_sharp :
    biasEntry (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
        (0 : Matrix (Fin 2) (Fin 2) ℝ) Cgm.witnessX 0 0 = -2
      ∧ ‖Cgm.xiMat (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
            (0 : Matrix (Fin 2) (Fin 2) ℝ) Cgm.witnessX‖
          + (1 : ℝ) ^ 2 * ((1 : Matrix (Fin 2) (Fin 2) ℝ).trace
              + (0 : Matrix (Fin 2) (Fin 2) ℝ).trace) = 2 := by
  have hxi : Cgm.xiMat (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
      (0 : Matrix (Fin 2) (Fin 2) ℝ) Cgm.witnessX = 0 := by
    rw [Cgm.xiMat]
    simp
  constructor
  · rw [biasEntry, hxi]
    simp only [Matrix.zero_apply, Fin.sum_univ_two, Cgm.witnessX, Matrix.of_apply]
    norm_num
  · rw [hxi, norm_zero, Matrix.trace_zero, Matrix.trace_one]
    norm_num

/-- The disturbance `ε = (1,0)'`. -/
def witnessE : Fin 2 → ℝ := fun o => if o = 0 then 1 else 0

/-- `meatCGM_eq_quadForm` at `O = {1,2}` in one cluster, `X̃ = (1,-1)'`, `R = I` and
`ε = (1,0)'`; both sides equal `1`. -/
theorem meatCGM_eq_quadForm_witness_nonzero :
    meatCGM (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
        (fun o k (_ : Unit) => Cgm.witnessX o k)
        (fun o (_ : Unit) => ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ fun p => witnessE p) o)
        0 0 () = 1 := by
  have h := congrFun (meatCGM_eq_quadForm (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1))
    (R := fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℝ)) (fun _ => Matrix.transpose_one)
    (fun _ : Unit => Cgm.witnessX) (fun o (_ : Unit) => witnessE o) 0 0) ()
  rw [h, Quadform.quadForm_apply]
  have hlink : ∀ o o' : Fin 2,
      Linked (fun _ _ => (0 : Fin 1)) ({0} : Finset (Fin 1)) o o' :=
    fun o o' => ⟨0, Finset.mem_singleton_self 0, rfl⟩
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [linkW, hlink, Cgm.witnessX, witnessE, Matrix.mul_apply, Fin.sum_univ_two]

/-- `caseTwo_bddInProb` on a growing design with `n+1` observations at index `n`, one
clustering dimension with one label, `P_[Δ]` a rank-one diagonal projector, `Λ = 0` and
`G_max = 1`. The disturbances are degenerate (`ξ ≡ 0`, `ε ≡ 0`, `σ²_ε = 0`). -/
theorem caseTwo_bddInProb_witness :
    Sequence.BddInProb (Measure.dirac ())
      (fun (n : ℕ) (u : Unit) =>
        (((Fintype.card (Fin (n + 1)) : ℝ))⁻¹
              * meatCGM (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
                  ({0} : Finset (Fin 1))
                  (fun o k u => PrimitiveDesign.within (PrimitiveDesign.sharpWitnessPm n)
                    (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u o k)
                  (fun o _ => ((1 - PrimitiveDesign.sharpWitnessPm n
                      - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
                    *ᵥ fun _ => (0 : ℝ)) o) 0 0 u
            - (0 : ℝ) * (((Fintype.card (Fin (n + 1)) : ℝ))⁻¹
                * ∑ o : Fin (n + 1),
                    PrimitiveDesign.within (PrimitiveDesign.sharpWitnessPm n)
                      (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u o 0
                      * PrimitiveDesign.within (PrimitiveDesign.sharpWitnessPm n)
                          (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u o 0))
          / (((PrimitiveDesign.sharpWitnessPm n).trace
                + Real.sqrt (1 * (Fintype.card (Fin (n + 1)) : ℝ)))
              / (Fintype.card (Fin (n + 1)) : ℝ))) := by
  classical
  have hwithin : ∀ (n : ℕ) (u : Unit),
      PrimitiveDesign.within (PrimitiveDesign.sharpWitnessPm n)
        (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u = 0 := by
    intro n u
    have hth : PrimitiveDesign.theta
        (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u = 0 := by
      ext o j; rfl
    rw [PrimitiveDesign.within, hth, Matrix.mul_zero]
  have hnu : ∀ (n : ℕ) (o : Fin (n + 1)),
      ((1 - PrimitiveDesign.sharpWitnessPm n
          - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) *ᵥ fun _ : Fin (n + 1) => (0 : ℝ)) o
        = 0 := by
    intro n o
    simp [Matrix.mulVec, dotProduct]
  have hsqrt : ∀ n : ℕ, Real.sqrt (1 * (Fintype.card (Fin (n + 1)) : ℝ))
      * Real.sqrt (1 * (Fintype.card (Fin (n + 1)) : ℝ))
      = 1 * (Fintype.card (Fin (n + 1)) : ℝ) := fun n =>
    Real.mul_self_sqrt (by positivity)
  refine caseTwo_bddInProb (⊥ : MeasurableSpace Unit) bot_le
    (fun (n : ℕ) (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
    (fun (_ : ℕ) => ({0} : Finset (Fin 1)))
    (fun _ => Finset.singleton_nonempty 0)
    (Pm := PrimitiveDesign.sharpWitnessPm)
    (Lam := fun n => (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (xi := fun (n : ℕ) (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ))
    (eps := fun (n : ℕ) (_ : Fin (n + 1)) (_ : Unit) => (0 : ℝ))
    (s := fun _ : Unit => (0 : ℝ)) (a := 0) (b := 0)
    (B := (0 : ℝ)) (sbar := (0 : ℝ)) (Kbd := (0 : ℝ)) (Jbd := (1 : ℝ)) (C := (0 : ℝ))
    (aN := fun n => (PrimitiveDesign.sharpWitnessPm n).trace
      + Real.sqrt (1 * (Fintype.card (Fin (n + 1)) : ℝ)))
    (Gmax := fun _ => (1 : ℝ))
    ?_ ?_ (fun _ => Matrix.transpose_zero) (fun _ => by simp) ?_ (fun _ => by norm_num)
    (fun _ => by simp) (fun _ => by simp) le_rfl ?_ ?_ ?_ (fun _ => zero_le_one)
    ?_ (fun _ _ _ => Quadform.integrable_unit _) (fun _ _ _ => Quadform.integrable_unit _)
    ?_ PrimitiveDesign.cgmsharp_witness (fun _ => Quadform.memLp_unit _) ?_
  · intro n
    rw [PrimitiveDesign.sharpWitnessPm, Matrix.diagonal_transpose]
  · intro n
    rw [PrimitiveDesign.sharpWitnessPm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext o
    by_cases h : o = 0 <;> simp [h]
  · intro n u o
    rw [hwithin n u]
    simp
  · intro n
    rw [PrimitiveDesign.sharpWitnessPm_trace]
    have := Real.sqrt_nonneg (1 * (Fintype.card (Fin (n + 1)) : ℝ))
    linarith
  · intro n
    rw [PrimitiveDesign.sharpWitnessPm_trace]
    have := Real.sqrt_nonneg (1 * (Fintype.card (Fin (n + 1)) : ℝ))
    linarith
  · intro n
    rw [PrimitiveDesign.sharpWitnessPm_trace]
    have h1 := hsqrt n
    have h2 := Real.sqrt_nonneg (1 * (Fintype.card (Fin (n + 1)) : ℝ))
    nlinarith [h1, h2]
  · intro n o k
    have hz : (fun u : Unit => PrimitiveDesign.within (PrimitiveDesign.sharpWitnessPm n)
        (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u o k)
        = fun _ : Unit => (0 : ℝ) := by
      funext u
      rw [hwithin n u]
      rfl
    rw [hz]
    exact stronglyMeasurable_const
  · intro n o o'
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show ((1 - PrimitiveDesign.sharpWitnessPm n
          - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) *ᵥ fun _ => (0 : ℝ)) o
        * ((1 - PrimitiveDesign.sharpWitnessPm n
            - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) *ᵥ fun _ => (0 : ℝ)) o'
          = (0 : ℝ) * (1 - PrimitiveDesign.sharpWitnessPm n
            - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) o o'
    rw [hnu n o, zero_mul, zero_mul]
  · intro n
    have hq : Quadform.quadForm
        (normalizedMeatEntry (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
          ({0} : Finset (Fin 1))
          (fun _ : Unit => 1 - PrimitiveDesign.sharpWitnessPm n
            - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
          (fun u : Unit => PrimitiveDesign.within (PrimitiveDesign.sharpWitnessPm n)
            (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Unit) => (0 : ℝ)) u) 0 0)
        (fun (_ : Fin (n + 1)) (_ : Unit) => (0 : ℝ)) = 0 := by
      funext u
      rw [Quadform.quadForm_apply]
      simp
    rw [hq, ProbabilityTheory.condVar_zero]
    exact Filter.Eventually.of_forall fun _ => by norm_num

/-- The case (ii) normalizer `[d_[Δ] + (G_max n)^{1/2}]/n` of the example equals `2` at index
`0` and `(1 + √2)/2` at index `1`. -/
theorem caseTwo_witness_boundary :
    ((PrimitiveDesign.sharpWitnessPm 0).trace
        + Real.sqrt (1 * (Fintype.card (Fin 1) : ℝ))) / (Fintype.card (Fin 1) : ℝ) = 2
      ∧ ((PrimitiveDesign.sharpWitnessPm 1).trace
          + Real.sqrt (1 * (Fintype.card (Fin 2) : ℝ))) / (Fintype.card (Fin 2) : ℝ)
        = (1 + Real.sqrt 2) / 2 := by
  constructor
  · rw [PrimitiveDesign.sharpWitnessPm_trace]
    norm_num
  · rw [PrimitiveDesign.sharpWitnessPm_trace]
    norm_num

/-! ### Examples for case (i) and the variance estimator

The case (i) example has `3 + n` observations at index `n` in one maintained cluster, on
`Ω = Unit` with `𝒟 = ⊥`. It takes `R = vv'` with `‖v‖ = 1` and `v ⊥ ι_n`, `ε = v`, `σ²_ε = 1`,
`P_m = uu'` with `u = ι_n/√n`, `A^{(m)} = I - vv' - uu'`, `Λ = 0`, and a regressor orthogonal
to `ι_n` and not parallel to `v`, so that the meat, the target and the rate are all nonzero. -/


section RankOne

variable {O : Type*} [Fintype O] [DecidableEq O]

omit [DecidableEq O] in
theorem vecMulVec_mul_vecMulVec (p q r t : O → ℝ) :
    Matrix.vecMulVec p q * Matrix.vecMulVec r t
      = (∑ o : O, q o * r o) • Matrix.vecMulVec p t := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  have hre : ∀ o : O, p k * q o * (r o * t l) = q o * r o * (p k * t l) := fun o => by ring
  simp only [hre]
  rw [← Finset.sum_mul]

omit [Fintype O] [DecidableEq O] in
theorem vecMulVec_transpose_self (p : O → ℝ) :
    (Matrix.vecMulVec p p)ᵀ = Matrix.vecMulVec p p := by
  ext k l
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- `I - pp' - qq'` is symmetric and idempotent when `p, q` are orthonormal. -/
theorem one_sub_two_rankOne_idem {p q : O → ℝ} (hp : ∑ o : O, p o * p o = 1)
    (hq : ∑ o : O, q o * q o = 1) (hpq : ∑ o : O, p o * q o = 0) :
    (1 - Matrix.vecMulVec p p - Matrix.vecMulVec q q)
        * (1 - Matrix.vecMulVec p p - Matrix.vecMulVec q q)
      = 1 - Matrix.vecMulVec p p - Matrix.vecMulVec q q := by
  have hqp : ∑ o : O, q o * p o = 0 := by
    rw [← hpq]; exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  have hpp := vecMulVec_mul_vecMulVec p p p p
  have hpq' := vecMulVec_mul_vecMulVec p p q q
  have hqp' := vecMulVec_mul_vecMulVec q q p p
  have hqq := vecMulVec_mul_vecMulVec q q q q
  rw [hp, one_smul] at hpp
  rw [hq, one_smul] at hqq
  rw [hpq, zero_smul] at hpq'
  rw [hqp, zero_smul] at hqp'
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hpp, hpq',
    hqp', hqq]
  abel

omit [DecidableEq O] in
/-- `(pp')ε = (ε·p) p`. -/
theorem vecMulVec_mulVec (p q : O → ℝ) (e : O → ℝ) :
    (Matrix.vecMulVec p q) *ᵥ e = (∑ o : O, q o * e o) • p := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  have hre : ∀ o : O, p k * q o * e o = q o * e o * p k := fun o => by ring
  simp only [hre]
  rw [← Finset.sum_mul]

end RankOne

section CaseOneWitnessDesign

/-- The observation set at index `n`, with `3 + n` observations. -/
abbrev wObs (n : ℕ) : Type := Fin 3 ⊕ Fin n

/-- The cluster-mean direction `u = ι_n/√n`. -/
noncomputable def wU (n : ℕ) : wObs n → ℝ := fun _ => (Real.sqrt ((n : ℝ) + 3))⁻¹

/-- A unit vector `v` orthogonal to `ι_n`. -/
noncomputable def wV (n : ℕ) : wObs n → ℝ :=
  Sum.elim (fun j : Fin 3 => if j = 0 then (Real.sqrt 2)⁻¹
    else if j = 1 then -(Real.sqrt 2)⁻¹ else 0) (fun _ => 0)

/-- The within regressor, orthogonal to `ι_n` and not proportional to `v`. -/
def wXvec (n : ℕ) : wObs n → ℝ :=
  Sum.elim (fun j : Fin 3 => if j = 0 then (1 : ℝ) else if j = 2 then -1 else 0) (fun _ => 0)

theorem wcard (n : ℕ) : (Fintype.card (wObs n) : ℝ) = (n : ℝ) + 3 := by
  simp [wObs]
  ring

theorem wsum (n : ℕ) (f : wObs n → ℝ) :
    ∑ o : wObs n, f o
      = (f (Sum.inl 0) + f (Sum.inl 1) + f (Sum.inl 2)) + ∑ k : Fin n, f (Sum.inr k) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_three]

theorem wsqrt2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]

theorem wUU (n : ℕ) : ∑ o : wObs n, wU n o * wU n o = 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have hsq : (Real.sqrt ((n : ℝ) + 3))⁻¹ * (Real.sqrt ((n : ℝ) + 3))⁻¹ = ((n : ℝ) + 3)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  simp only [wU, hsq]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, wcard n]
  field_simp

theorem wVV (n : ℕ) : ∑ o : wObs n, wV n o * wV n o = 1 := by
  rw [wsum]
  simp only [wV, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const, smul_zero]
  norm_num
  rw [wsqrt2]
  norm_num

theorem wUV (n : ℕ) : ∑ o : wObs n, wU n o * wV n o = 0 := by
  rw [wsum]
  simp only [wU, wV, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const, smul_zero]
  norm_num

theorem wXsum (n : ℕ) : ∑ o : wObs n, wXvec n o = 0 := by
  rw [wsum]
  simp only [wXvec, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, smul_zero]
  norm_num

theorem wXX (n : ℕ) : ∑ o : wObs n, wXvec n o * wXvec n o = 2 := by
  rw [wsum]
  simp only [wXvec, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const, smul_zero]
  norm_num

theorem wXV (n : ℕ) : ∑ o : wObs n, wXvec n o * wV n o = (Real.sqrt 2)⁻¹ := by
  rw [wsum]
  simp only [wXvec, wV, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const, smul_zero]
  norm_num

end CaseOneWitnessDesign

section CaseOneWitness

/-- `P_m = uu'`, for a single cluster holding every observation. -/
noncomputable def wPm (n : ℕ) : Matrix (wObs n) (wObs n) ℝ :=
  Matrix.vecMulVec (wU n) (wU n)

/-- `R = vv'`. -/
noncomputable def wRmat (n : ℕ) : Matrix (wObs n) (wObs n) ℝ :=
  Matrix.vecMulVec (wV n) (wV n)

/-- `A^{(m)} = I - vv' - uu'`. -/
noncomputable def wA (n : ℕ) : Matrix (wObs n) (wObs n) ℝ := 1 - wRmat n - wPm n

/-- The within regressor matrix, one column. -/
def wXmat (n : ℕ) : Matrix (wObs n) (Fin 1) ℝ := Matrix.of fun o _ => wXvec n o

theorem wVU (n : ℕ) : ∑ o : wObs n, wV n o * wU n o = 0 := by
  rw [← wUV n]
  exact Finset.sum_congr rfl fun o _ => mul_comm _ _

theorem wR_eq (n : ℕ) :
    (1 : Matrix (wObs n) (wObs n) ℝ) - wPm n - wA n - 0 = wRmat n := by
  rw [wA]
  abel

theorem wA_transpose (n : ℕ) : (wA n)ᵀ = wA n := by
  rw [wA, Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_one, wRmat, wPm,
    vecMulVec_transpose_self, vecMulVec_transpose_self]

theorem wA_idem (n : ℕ) : wA n * wA n = wA n := by
  rw [wA, wRmat, wPm]
  exact one_sub_two_rankOne_idem (wVV n) (wUU n) (wVU n)

theorem wPm_apply (n : ℕ) (o o' : wObs n) : wPm n o o' = ((n : ℝ) + 3)⁻¹ := by
  have hpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  rw [wPm, Matrix.vecMulVec_apply]
  simp only [wU]
  rw [← mul_inv, Real.mul_self_sqrt hpos.le]

theorem wclusterCard (n : ℕ) (j : Fin 1) :
    (Cgm.clusterCard (fun _ : wObs n => (0 : Fin 1)) j : ℝ) = (n : ℝ) + 3 := by
  have h : (Finset.univ.filter fun _ : wObs n => (0 : Fin 1) = j) = Finset.univ := by
    refine Finset.filter_true_of_mem fun o _ => Subsingleton.elim _ _
  rw [Cgm.clusterCard, h, Finset.card_univ, wcard n]

theorem wnu (n : ℕ) (o : wObs n) :
    (((1 : Matrix (wObs n) (wObs n) ℝ) - wPm n - wA n - 0) *ᵥ fun p => wV n p) o = wV n o := by
  rw [wR_eq n, wRmat, vecMulVec_mulVec, wVV n]
  simp

/-- `Var(Z | ⊥) = 0` under the Dirac measure on `Unit`. -/
theorem condVar_unit (Z : Unit → ℝ) :
    ProbabilityTheory.condVar (⊥ : MeasurableSpace Unit) Z (Measure.dirac ()) = 0 := by
  have h : ProbabilityTheory.condVar (⊥ : MeasurableSpace Unit) Z (Measure.dirac ())
      = (Measure.dirac ())[fun u =>
          (Z u - ((Measure.dirac ())[Z | (⊥ : MeasurableSpace Unit)]) u) ^ 2
        | (⊥ : MeasurableSpace Unit)] := rfl
  rw [h, Quadform.condExp_unit Z]
  simp
  rfl

end CaseOneWitness

section CaseOneWitnessMain

theorem wXvec_sq_le (n : ℕ) (o : wObs n) : wXvec n o ^ 2 ≤ 1 := by
  cases o with
  | inl j => fin_cases j <;> simp [wXvec]
  | inr k => simp [wXvec]

theorem wXfilter (n : ℕ) (j : Fin 1) :
    (Finset.univ.filter fun o : wObs n => (0 : Fin 1) = j) = Finset.univ :=
  Finset.filter_true_of_mem fun o _ => Subsingleton.elim _ _

theorem caseOne_bddInProb_witness :
    Sequence.BddInProb (Measure.dirac ()) (fun (n : ℕ) (u : Unit) =>
      ((((Fintype.card (wObs n) : ℝ))⁻¹
            * meatCGM (fun (_ : Fin 1) (_ : wObs n) => (0 : Fin 1)) ({0} : Finset (Fin 1))
                (fun o k (_ : Unit) => wXmat n o k)
                (fun o (_ : Unit) =>
                  ((1 - wPm n - wA n - (0 : Matrix (wObs n) (wObs n) ℝ))
                    *ᵥ fun p => wV n p) o) 0 0 u)
          - (1 : ℝ) * (((Fintype.card (wObs n) : ℝ))⁻¹
              * ∑ o : wObs n, wXmat n o 0 * wXmat n o 0))
        / caseOneRate (wA n).trace (0 : Matrix (wObs n) (wObs n) ℝ).trace ((n : ℝ) + 3)
            (Fintype.card (wObs n) : ℝ)) := by
  classical
  refine caseOne_bddInProb (⊥ : MeasurableSpace Unit) bot_le
    (fun (n : ℕ) (_ : Fin 1) (_ : wObs n) => (0 : Fin 1))
    (fun _ => ({0} : Finset (Fin 1)))
    (fun _ => Finset.singleton_nonempty 0)
    (fun (n : ℕ) (_ : wObs n) => (0 : Fin 1))
    (fun n o o' => ⟨fun _ => rfl, fun _ => ⟨0, Finset.mem_singleton_self 0, rfl⟩⟩)
    (Pm := wPm) (A := wA) (Lam := fun n => (0 : Matrix (wObs n) (wObs n) ℝ))
    (Xr := fun n (_ : Unit) => wXmat n)
    (eps := fun (n : ℕ) (o : wObs n) (_ : Unit) => wV n o)
    (s := fun _ : Unit => (1 : ℝ)) (a := 0) (b := 0)
    (B := (1 : ℝ)) (sbar := (1 : ℝ)) (C := (1 : ℝ)) (Gmax := fun n => (n : ℝ) + 3)
    ?_ wA_transpose wA_idem (fun _ => Matrix.transpose_zero) (fun _ => by simp)
    ?_ ?_ (fun _ => by norm_num) (fun _ => by simp) zero_le_one
    (fun n => by positivity) ?_ (fun _ _ _ => stronglyMeasurable_const)
    (fun _ _ _ => Quadform.integrable_unit _) (fun _ _ _ => Quadform.integrable_unit _)
    ?_ (fun _ => Quadform.memLp_unit _) ?_
  · intro n o o'
    rw [wPm_apply n o o', if_pos rfl, wclusterCard n]
  · intro n u j k
    rw [wXfilter n j]
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    exact wXsum n
  · intro n u o
    rw [Fin.sum_univ_one]
    have h : wXmat n o 0 = wXvec n o := rfl
    rw [h, one_pow]
    exact wXvec_sq_le n o
  · intro n j
    rw [wclusterCard n]
  · intro n o o'
    rw [Quadform.condExp_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    show (((1 : Matrix (wObs n) (wObs n) ℝ) - wPm n - wA n - 0) *ᵥ fun p => wV n p) o
        * (((1 : Matrix (wObs n) (wObs n) ℝ) - wPm n - wA n - 0) *ᵥ fun p => wV n p) o'
      = (1 : ℝ) * ((1 : Matrix (wObs n) (wObs n) ℝ) - wPm n - wA n - 0) o o'
    rw [wnu n o, wnu n o', wR_eq n, wRmat, Matrix.vecMulVec_apply, one_mul]
  · intro n
    rw [condVar_unit]
    refine Filter.Eventually.of_forall fun u => ?_
    have hcard : (0 : ℝ) < (Fintype.card (wObs n) : ℝ) := by
      rw [wcard n]; positivity
    show (0 : ℝ) ≤ 3 * (1 : ℝ) * ((1 : ℝ) ^ 4
      * (((({0} : Finset (Fin 1))).card : ℝ) * (((n : ℝ) + 3) / (Fintype.card (wObs n) : ℝ))))
    positivity

end CaseOneWitnessMain

section CaseOneWitnessValue

theorem wtrace_vecMulVec (n : ℕ) (p q : wObs n → ℝ) :
    (Matrix.vecMulVec p q).trace = ∑ o : wObs n, p o * q o := rfl

theorem wA_trace (n : ℕ) : (wA n).trace = (n : ℝ) + 1 := by
  rw [wA, wRmat, wPm, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one,
    wtrace_vecMulVec, wtrace_vecMulVec, wVV n, wUU n, wcard n]
  ring

theorem wmeat_eq (n : ℕ) :
    meatCGM (fun (_ : Fin 1) (_ : wObs n) => (0 : Fin 1)) ({0} : Finset (Fin 1))
        (fun o k (_ : Unit) => wXmat n o k)
        (fun o (_ : Unit) =>
          ((1 - wPm n - wA n - (0 : Matrix (wObs n) (wObs n) ℝ)) *ᵥ fun p => wV n p) o)
        0 0 () = 2⁻¹ := by
  classical
  have hlink : ∀ o o' : wObs n,
      Linked (fun (_ : Fin 1) (_ : wObs n) => (0 : Fin 1)) ({0} : Finset (Fin 1)) o o' :=
    fun o o' => ⟨0, Finset.mem_singleton_self 0, rfl⟩
  have h1 : meatCGM (fun (_ : Fin 1) (_ : wObs n) => (0 : Fin 1)) ({0} : Finset (Fin 1))
        (fun o k (_ : Unit) => wXmat n o k)
        (fun o (_ : Unit) =>
          ((1 - wPm n - wA n - (0 : Matrix (wObs n) (wObs n) ℝ)) *ᵥ fun p => wV n p) o)
        0 0 ()
      = ∑ o : wObs n, ∑ o' : wObs n,
        (if Linked (fun (_ : Fin 1) (_ : wObs n) => (0 : Fin 1)) ({0} : Finset (Fin 1)) o o'
          then wXmat n o 0 * wXmat n o' 0
            * (((1 - wPm n - wA n - (0 : Matrix (wObs n) (wObs n) ℝ)) *ᵥ fun p => wV n p) o
              * ((1 - wPm n - wA n - (0 : Matrix (wObs n) (wObs n) ℝ)) *ᵥ fun p => wV n p) o')
          else 0) :=
    Cgm.meat_eq_linkedPairs (fun (_ : Fin 1) (_ : wObs n) => (0 : Fin 1))
      ({0} : Finset (Fin 1)) (fun o k (_ : Unit) => wXmat n o k)
      (fun o (_ : Unit) =>
        ((1 - wPm n - wA n - (0 : Matrix (wObs n) (wObs n) ℝ)) *ᵥ fun p => wV n p) o) 0 0 ()
  rw [h1]
  trans (∑ o : wObs n, ∑ o' : wObs n, (wXvec n o * wV n o) * (wXvec n o' * wV n o'))
  · refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
    rw [if_pos (hlink o o'), wnu n o, wnu n o']
    show wXvec n o * wXvec n o' * (wV n o * wV n o')
      = wXvec n o * wV n o * (wXvec n o' * wV n o')
    ring
  · rw [← Finset.sum_mul_sum, wXV n, wsqrt2]

/-- At index `0` the normalized quantity `n⁻¹𝓜̂_CGM - S_n` divided by the case (i) rate
equals `-1/4`. -/
theorem caseOne_witness_nonzero :
    ((((Fintype.card (wObs 0) : ℝ))⁻¹
          * meatCGM (fun (_ : Fin 1) (_ : wObs 0) => (0 : Fin 1)) ({0} : Finset (Fin 1))
              (fun o k (_ : Unit) => wXmat 0 o k)
              (fun o (_ : Unit) =>
                ((1 - wPm 0 - wA 0 - (0 : Matrix (wObs 0) (wObs 0) ℝ))
                  *ᵥ fun p => wV 0 p) o) 0 0 ())
        - (1 : ℝ) * (((Fintype.card (wObs 0) : ℝ))⁻¹
            * ∑ o : wObs 0, wXmat 0 o 0 * wXmat 0 o 0))
      / caseOneRate (wA 0).trace (0 : Matrix (wObs 0) (wObs 0) ℝ).trace (((0 : ℕ) : ℝ) + 3)
          (Fintype.card (wObs 0) : ℝ)
      = -(1 / 4) := by
  have hX : ∑ o : wObs 0, wXmat 0 o 0 * wXmat 0 o 0 = 2 := wXX 0
  have hrate : caseOneRate (wA 0).trace (0 : Matrix (wObs 0) (wObs 0) ℝ).trace
      (((0 : ℕ) : ℝ) + 3) (Fintype.card (wObs 0) : ℝ) = 2 := by
    rw [caseOneRate, wA_trace 0, Matrix.trace_zero, wcard 0]
    norm_num
  rw [wmeat_eq 0, hX, hrate, wcard 0]
  norm_num

/-- The case (i) rate of the example equals `2` at index `0` and `√2 + 1` at index `1`. -/
theorem caseOne_witness_boundary :
    caseOneRate (wA 0).trace (0 : Matrix (wObs 0) (wObs 0) ℝ).trace (((0 : ℕ) : ℝ) + 3)
        (Fintype.card (wObs 0) : ℝ) = 2
      ∧ caseOneRate (wA 1).trace (0 : Matrix (wObs 1) (wObs 1) ℝ).trace (((1 : ℕ) : ℝ) + 3)
          (Fintype.card (wObs 1) : ℝ) = Real.sqrt 2 + 1 := by
  constructor
  · rw [caseOneRate, wA_trace 0, Matrix.trace_zero, wcard 0]
    norm_num
  · rw [caseOneRate, wA_trace 1, Matrix.trace_zero, wcard 1]
    norm_num

end CaseOneWitnessValue

section NVhatCGMWitness

open Filter

/-- `tendstoInProb_nVhatCGM` on a growing design with `K = 1`, `Ω = {*}`, `n = N_j = j+1`,
`X̃'X̃ = [j+1]`, `H = [1]`, `S_n = [1 + (j+1)⁻¹]`, `𝓜̂_CGM = [(j+1)(1 + (j+1)⁻¹)]` and `S = [1]`. -/
theorem tendstoInProb_nVhatCGM_witness :
    TendstoInMeasure (Measure.dirac ())
      (fun (n : ℕ) (_ : Unit) => frobNorm (((n : ℝ) + 1) •
          (((Matrix.of fun _ _ => (n : ℝ) + 1) : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
              * ((Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹))
                  : Matrix (Fin 1) (Fin 1) ℝ)
              * ((Matrix.of fun _ _ => (n : ℝ) + 1) : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)
            - (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹))
      atTop (fun _ => (0 : ℝ)) := by
  refine tendstoInProb_nVhatCGM (P := Measure.dirac ()) (H := 1) (S := 1)
    (N := fun n : ℕ => (n : ℝ) + 1)
    (Sn := fun (n : ℕ) (_ : Unit) => (Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹))
    (fun n => by positivity) Matrix.PosDef.one ?_ ?_ ?_
  · refine Vhat.tendstoInProb_of_tendsto ?_
    have hval : ∀ n : ℕ, frobNorm ((((n : ℝ) + 1)⁻¹ • (Matrix.of fun _ _ => (n : ℝ) + 1) - 1 :
        Matrix (Fin 1) (Fin 1) ℝ)) = 0 := by
      intro n
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      have heq : ((((n : ℝ) + 1)⁻¹ • (Matrix.of fun _ _ => (n : ℝ) + 1) - 1 :
          Matrix (Fin 1) (Fin 1) ℝ)) = Matrix.of fun _ _ => (0 : ℝ) := by
        ext i j
        fin_cases i; fin_cases j; simp [inv_mul_cancel₀ hne]
      rw [heq, Vhat.frobNorm_scalar]
      simp
    simp only [hval]
    exact tendsto_const_nhds
  · intro a b
    refine Vhat.tendstoInProb_of_tendsto (c := (0 : ℝ)) ?_
    have hval : ∀ n : ℕ, ((n : ℝ) + 1)⁻¹
        * ((Matrix.of fun _ _ => ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹))
            : Matrix (Fin 1) (Fin 1) ℝ) a b
        - ((Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) : Matrix (Fin 1) (Fin 1) ℝ) a b = 0 := by
      intro n
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      simp only [Matrix.of_apply]
      field_simp
      ring
    simp only [hval]
    exact tendsto_const_nhds
  · refine Vhat.tendstoInProb_of_tendsto ?_
    have hval : ∀ n : ℕ, frobNorm (((Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) - 1 :
        Matrix (Fin 1) (Fin 1) ℝ)) = ((n : ℝ) + 1)⁻¹ := by
      intro n
      have heq : (((Matrix.of fun _ _ => 1 + ((n : ℝ) + 1)⁻¹) - 1 :
          Matrix (Fin 1) (Fin 1) ℝ)) = Matrix.of fun _ _ => ((n : ℝ) + 1)⁻¹ := by
        ext i j
        fin_cases i; fin_cases j; simp
      rw [heq, Vhat.frobNorm_scalar, abs_of_nonneg (by positivity)]
    simp only [hval]
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => ?_
    rw [one_div]

end NVhatCGMWitness

end Witness

/-! ### Random design

`P_[Δ]`, `A`, `Λ` and the clustering `i` are `𝒟`-measurable; every hypothesis is read under the
regular conditional law `ℙ_ω := condExpKernel P 𝒟 ω` at the design frozen at `ω`, and the
conclusion is under `P`, through `PrimitiveDesign.CondP.tendstoInMeasure_of_deconditioning`.
The level map `c`, the maintained set `dims`, the rate sequences and the constants remain
deterministic. -/

section DesignDecond

open ProbabilityTheory Filter
open scoped ENNReal Topology

variable {O D L N : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable [∀ n, Nonempty (O n)]
variable [∀ n, DecidableEq (D n)] [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable [∀ n, Fintype (N n)] [∀ n, DecidableEq (N n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω}

/-- Freezing a pair of `O n × O n` design matrices, entry by entry. -/
theorem ae_ae_eq_pairDesign (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P]
    {Pm Lam : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o')
    (hLamD : ∀ n o o', Measurable[𝒟] fun ω => Lam n ω o o') :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Pm n y = Pm n ω ∧ Lam n y = Lam n ω := by
  refine ae_all_iff.2 fun n => ?_
  have h1 : ∀ᵐ ω ∂P, ∀ p : O n × O n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Pm n y p.1 p.2 = Pm n ω p.1 p.2 :=
    ae_all_iff.2 fun p =>
      Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel h𝒟 P (hPmD n p.1 p.2)
  have h2 : ∀ᵐ ω ∂P, ∀ p : O n × O n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Lam n y p.1 p.2 = Lam n ω p.1 p.2 :=
    ae_all_iff.2 fun p =>
      Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel h𝒟 P (hLamD n p.1 p.2)
  filter_upwards [h1, h2] with ω hω1 hω2
  filter_upwards [ae_all_iff.2 hω1, ae_all_iff.2 hω2] with y hy1 hy2
  exact ⟨Matrix.ext fun o o' => hy1 (o, o'), Matrix.ext fun o o' => hy2 (o, o')⟩

/-- The within-transformed regressor is measurable for a random `P_[Δ]`. -/
theorem measurable_withinEntry {n : ℕ} {Pm : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    {xi : ∀ n, O n → K → Ω → ℝ}
    (hPmM : ∀ o o', Measurable fun y : Ω => Pm n y o o')
    (hxiM : ∀ o k, Measurable (xi n o k)) (o : O n) (k : K) :
    Measurable fun y : Ω => PrimitiveDesign.within (Pm n y) (xi n) y o k := by
  have hQ : ∀ o o', Measurable fun y : Ω => ((1 : Matrix (O n) (O n) ℝ) - Pm n y) o o' := by
    intro o o'
    simp only [Matrix.sub_apply]
    exact measurable_const.sub (hPmM o o')
  have hT : ∀ o (k : K), Measurable fun y : Ω => PrimitiveDesign.theta (xi n) y o k := by
    intro o k
    simpa only [PrimitiveDesign.theta, Matrix.of_apply] using hxiM o k
  exact PrimitiveDesign.measurable_matmul_apply hQ hT o k

/-- The absorbed residual is measurable for random `P_[Δ]` and `Λ`. -/
theorem measurable_residEntry {n : ℕ} {Pm Lam : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    {eps : ∀ n, O n → Ω → ℝ}
    (hPmM : ∀ o o', Measurable fun y : Ω => Pm n y o o')
    (hLamM : ∀ o o', Measurable fun y : Ω => Lam n y o o')
    (hepsM : ∀ o, Measurable (eps n o)) (o : O n) :
    Measurable fun y : Ω =>
      ((1 - Pm n y - Lam n y) *ᵥ fun p => eps n p y) o := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
  exact Finset.measurable_sum _ fun p _ =>
    ((measurable_const.sub (hPmM o p)).sub (hLamM o p)).mul (hepsM p)

/-- `𝓜̂_CGM` depends on its two inputs only through their values at the point. -/
theorem meatCGM_congr {n : ℕ} (c : D n → O n → L n) (dims : Finset (D n))
    {X X' : O n → K → Ω → ℝ} {v v' : O n → Ω → ℝ} (a b : K) (y : Ω)
    (hX : ∀ o k, X o k y = X' o k y) (hv : ∀ o, v o y = v' o y) :
    meatCGM c dims X v a b y = meatCGM c dims X' v' a b y := by
  simp only [meatCGM]
  refine Finset.sum_congr rfl fun A _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  · exact Finset.sum_congr rfl fun o _ => by rw [hX o a, hv o]
  · exact Finset.sum_congr rfl fun o' _ => by rw [hX o' b, hv o']

/-- The entries of `𝓜̂_CGM` are measurable when its inputs are. -/
theorem measurable_meatCGM {n : ℕ} (c : D n → O n → L n) (dims : Finset (D n))
    {X : O n → K → Ω → ℝ} {v : O n → Ω → ℝ} (a b : K)
    (hX : ∀ o k, Measurable (X o k)) (hv : ∀ o, Measurable (v o)) :
    Measurable (meatCGM c dims X v a b) := by
  refine Finset.measurable_sum _ fun A _ => Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun g _ => Measurable.mul ?_ ?_
  · exact Finset.measurable_sum _ fun o _ => (hX o a).mul (hv o)
  · exact Finset.measurable_sum _ fun o' _ => (hX o' b).mul (hv o')

/-- **Theorem 10**, case (ii), with `P_[Δ]` and `Λ` `𝒟`-measurable random matrices. The
hypotheses of `caseTwo_meat_tendstoInProb` hold under `ℙ_ω` for `P`-almost every `ω` at the
design frozen at `ω`; the conclusion is under `P`. -/
theorem caseTwo_meat_tendstoInProb_uncond [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    {Pm Lam : ∀ n, Ω → Matrix (O n) (O n) ℝ} {xi : ∀ n, O n → K → Ω → ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ} {a b : K}
    {B sbar Kbd Jbd C : ℝ} {aN Gmax : ℕ → ℝ}
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o')
    (hLamD : ∀ n o o', Measurable[𝒟] fun ω => Lam n ω o o')
    (hxiM : ∀ n o k, Measurable (xi n o k)) (hepsM : ∀ n o, Measurable (eps n o))
    (hsM : Measurable s)
    (hPms : ∀ᵐ ω ∂P, ∀ n, (Pm n ω)ᵀ = Pm n ω)
    (hPmi : ∀ᵐ ω ∂P, ∀ n, Pm n ω * Pm n ω = Pm n ω)
    (hLs : ∀ᵐ ω ∂P, ∀ n, (Lam n ω)ᵀ = Lam n ω)
    (hLi : ∀ᵐ ω ∂P, ∀ n, Lam n ω * Lam n ω = Lam n ω)
    (hB : ∀ᵐ ω ∂P, ∀ (n : ℕ) (y : Ω), ∀ o : O n,
      ∑ k : K, PrimitiveDesign.within (Pm n ω) (xi n) y o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar)
    (hK : ∀ᵐ ω ∂P, ∀ n, (Lam n ω).trace ≤ Kbd)
    (hJ : ∀ n, ((dims n).card : ℝ) ≤ Jbd) (hC : 0 ≤ C)
    (hPmle : ∀ᵐ ω ∂P, ∀ n, (Pm n ω).trace ≤ aN n) (hone : ∀ n, 1 ≤ aN n)
    (hGsq : ∀ n, Gmax n * (Fintype.card (O n) : ℝ) ≤ (aN n) ^ 2)
    (hGnn : ∀ n, 0 ≤ Gmax n)
    (hXm : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o : O n) (k : K),
      StronglyMeasurable[𝒟] fun y => PrimitiveDesign.within (Pm n ω) (xi n) y o k)
    (hint : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n), Integrable (fun y =>
      ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o
        * ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o') (condExpKernel P 𝒟 ω))
    (hint' : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n), Integrable (fun y =>
      (if Linked (c n) (dims n) o o' then
          PrimitiveDesign.within (Pm n ω) (xi n) y o a
            * PrimitiveDesign.within (Pm n ω) (xi n) y o' b else 0)
        * (((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o
            * ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o'))
      (condExpKernel P 𝒟 ω))
    (hcross : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n),
      (condExpKernel P 𝒟 ω)[fun y => ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o
          * ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o' | 𝒟]
        =ᵐ[condExpKernel P 𝒟 ω] fun y => s y * (1 - Pm n ω - Lam n ω) o o')
    (hXi : ∀ᵐ ω ∂P, Sequence.BddInProb (condExpKernel P 𝒟 ω) (fun n y =>
      ‖PrimitiveDesign.xiSharp (c n) (dims n) (Pm n ω) (Lam n ω) (xi n) y‖ / aN n))
    (hL2 : ∀ᵐ ω ∂P, ∀ n, MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n ω - Lam n ω)
        (fun y => PrimitiveDesign.within (Pm n ω) (xi n) y) a b) (eps n)) 2
      (condExpKernel P 𝒟 ω))
    (hcv : ∀ᵐ ω ∂P, ∀ n, ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n ω - Lam n ω)
          (fun y => PrimitiveDesign.within (Pm n ω) (xi n) y) a b) (eps n))
        (condExpKernel P 𝒟 ω)
      ≤ᵐ[condExpKernel P 𝒟 ω] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ)))))
    (hrate : Tendsto (fun n : ℕ => aN n / (Fintype.card (O n) : ℝ)) atTop (nhds 0)) :
    TendstoInMeasure P (fun n y =>
        ((Fintype.card (O n) : ℝ))⁻¹
              * meatCGM (c n) (dims n)
                  (fun o k y => PrimitiveDesign.within (Pm n y) (xi n) y o k)
                  (fun o y => ((1 - Pm n y - Lam n y) *ᵥ fun p => eps n p y) o) a b y
            - s y * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n,
                PrimitiveDesign.within (Pm n y) (xi n) y o a
                  * PrimitiveDesign.within (Pm n y) (xi n) y o b))
      atTop (fun _ => (0 : ℝ)) := by
  classical
  have hPmM : ∀ n o o', Measurable fun y : Ω => Pm n y o o' :=
    fun n o o' => (hPmD n o o').mono h𝒟 le_rfl
  have hLamM : ∀ n o o', Measurable fun y : Ω => Lam n y o o' :=
    fun n o o' => (hLamD n o o').mono h𝒟 le_rfl
  have hZ : ∀ n : ℕ, Measurable fun y : Ω =>
      ((Fintype.card (O n) : ℝ))⁻¹
            * meatCGM (c n) (dims n)
                (fun o k y => PrimitiveDesign.within (Pm n y) (xi n) y o k)
                (fun o y => ((1 - Pm n y - Lam n y) *ᵥ fun p => eps n p y) o) a b y
          - s y * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n,
              PrimitiveDesign.within (Pm n y) (xi n) y o a
                * PrimitiveDesign.within (Pm n y) (xi n) y o b) := by
    intro n
    have hw : ∀ (o : O n) (k : K), Measurable fun y : Ω =>
        PrimitiveDesign.within (Pm n y) (xi n) y o k :=
      fun o k => measurable_withinEntry (hPmM n) (hxiM n) o k
    have hv : ∀ o : O n, Measurable fun y : Ω =>
        ((1 - Pm n y - Lam n y) *ᵥ fun p => eps n p y) o :=
      fun o => measurable_residEntry (hPmM n) (hLamM n) (hepsM n) o
    refine Measurable.sub ((measurable_meatCGM (c n) (dims n) a b hw hv).const_mul _) ?_
    exact hsM.mul ((Finset.measurable_sum _ fun o _ => (hw o a).mul (hw o b)).const_mul _)
  have hsets : ∀ (ε : ℝ≥0∞) (n : ℕ), MeasurableSet {y : Ω | ε ≤ edist
      (((Fintype.card (O n) : ℝ))⁻¹
            * meatCGM (c n) (dims n)
                (fun o k y => PrimitiveDesign.within (Pm n y) (xi n) y o k)
                (fun o y => ((1 - Pm n y - Lam n y) *ᵥ fun p => eps n p y) o) a b y
          - s y * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n,
              PrimitiveDesign.within (Pm n y) (xi n) y o a
                * PrimitiveDesign.within (Pm n y) (xi n) y o b))
      ((fun _ => (0 : ℝ)) y)} := fun ε n =>
    measurableSet_le measurable_const ((hZ n).edist measurable_const)
  refine PrimitiveDesign.CondP.tendstoInMeasure_of_deconditioning h𝒟 P hsets ?_
  filter_upwards [ae_ae_eq_pairDesign h𝒟 P hPmD hLamD, hPms, hPmi, hLs, hLi, hB, hK, hPmle,
    hXm, hint, hint', hcross, hXi, hL2, hcv]
    with ω hfz h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  have hcondlaw := caseTwo_meat_tendstoInProb (P := condExpKernel P 𝒟 ω) 𝒟 h𝒟 c dims hdims
    (Pm := fun n => Pm n ω) (Lam := fun n => Lam n ω) (xi := xi) (eps := eps) (s := s)
    h1 h2 h3 h4 h5 hs h6 hJ hC h7 hone hGsq hGnn h8 h9 h10 h11 h12 h13 h14 hrate
  refine PrimitiveDesign.CondP.tendstoInMeasure_congr_ae (fun n => ?_) hcondlaw
  filter_upwards [hfz n] with y hy
  have hX : ∀ (o : O n) (k : K),
      PrimitiveDesign.within (Pm n ω) (xi n) y o k
        = PrimitiveDesign.within (Pm n y) (xi n) y o k := fun o k => by rw [hy.1]
  have hv : ∀ o : O n, ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o
      = ((1 - Pm n y - Lam n y) *ᵥ fun p => eps n p y) o := fun o => by rw [hy.1, hy.2]
  have hm := meatCGM_congr (c n) (dims n)
      (X := fun o k y' => PrimitiveDesign.within (Pm n ω) (xi n) y' o k)
      (X' := fun o k y' => PrimitiveDesign.within (Pm n y') (xi n) y' o k)
      (v := fun o y' => ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y') o)
      (v' := fun o y' => ((1 - Pm n y' - Lam n y') *ᵥ fun p => eps n p y') o) a b y hX hv
  have hsum : ∑ o : O n, PrimitiveDesign.within (Pm n ω) (xi n) y o a
        * PrimitiveDesign.within (Pm n ω) (xi n) y o b
      = ∑ o : O n, PrimitiveDesign.within (Pm n y) (xi n) y o a
        * PrimitiveDesign.within (Pm n y) (xi n) y o b :=
    Finset.sum_congr rfl fun o _ => by rw [hX o a, hX o b]
  show _ = _
  rw [hm, hsum]

/-- Freezing a triple of `O n × O n` design matrices, entry by entry. -/
theorem ae_ae_eq_tripleDesign (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P]
    {Pm A Lam : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o')
    (hAD : ∀ n o o', Measurable[𝒟] fun ω => A n ω o o')
    (hLamD : ∀ n o o', Measurable[𝒟] fun ω => Lam n ω o o') :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Pm n y = Pm n ω ∧ A n y = A n ω ∧ Lam n y = Lam n ω := by
  refine ae_all_iff.2 fun n => ?_
  have h1 : ∀ᵐ ω ∂P, ∀ p : O n × O n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Pm n y p.1 p.2 = Pm n ω p.1 p.2 :=
    ae_all_iff.2 fun p =>
      Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel h𝒟 P (hPmD n p.1 p.2)
  have h2 : ∀ᵐ ω ∂P, ∀ p : O n × O n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      A n y p.1 p.2 = A n ω p.1 p.2 :=
    ae_all_iff.2 fun p =>
      Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel h𝒟 P (hAD n p.1 p.2)
  have h3 : ∀ᵐ ω ∂P, ∀ p : O n × O n, ∀ᵐ y ∂(condExpKernel P 𝒟 ω),
      Lam n y p.1 p.2 = Lam n ω p.1 p.2 :=
    ae_all_iff.2 fun p =>
      Multiway.CLTMartingale.CondD.ae_ae_eq_condExpKernel h𝒟 P (hLamD n p.1 p.2)
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  filter_upwards [ae_all_iff.2 hω1, ae_all_iff.2 hω2, ae_all_iff.2 hω3] with y hy1 hy2 hy3
  exact ⟨Matrix.ext fun o o' => hy1 (o, o'), Matrix.ext fun o o' => hy2 (o, o'),
    Matrix.ext fun o o' => hy3 (o, o')⟩

/-- The absorbed residual of case (i) is measurable for random `P_[Δ]`, `A` and `Λ`. -/
theorem measurable_residEntry3 {n : ℕ} {Pm A Lam : ∀ n, Ω → Matrix (O n) (O n) ℝ}
    {eps : ∀ n, O n → Ω → ℝ}
    (hPmM : ∀ o o', Measurable fun y : Ω => Pm n y o o')
    (hAM : ∀ o o', Measurable fun y : Ω => A n y o o')
    (hLamM : ∀ o o', Measurable fun y : Ω => Lam n y o o')
    (hepsM : ∀ o, Measurable (eps n o)) (o : O n) :
    Measurable fun y : Ω =>
      ((1 - Pm n y - A n y - Lam n y) *ᵥ fun p => eps n p y) o := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
  exact Finset.measurable_sum _ fun p _ =>
    (((measurable_const.sub (hPmM o p)).sub (hAM o p)).sub (hLamM o p)).mul (hepsM p)

/-- **Theorem 10**, case (i), with `P_[Δ]`, `A`, `Λ` and the clustering `i` random. The
hypotheses of `caseOne_meat_tendstoInProb` hold under `ℙ_ω` for `P`-almost every `ω` at the
design frozen at `ω`; the conclusion is under `P`. -/
theorem caseOne_meat_tendstoInProb_uncond [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    (i : ∀ n, Ω → O n → N n)
    {Pm A Lam : ∀ n, Ω → Matrix (O n) (O n) ℝ} {Xr : ∀ n, Ω → Matrix (O n) K ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ} {a b : K}
    {B sbar C : ℝ} {Gmax : ℕ → ℝ}
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o')
    (hAD : ∀ n o o', Measurable[𝒟] fun ω => A n ω o o')
    (hLamD : ∀ n o o', Measurable[𝒟] fun ω => Lam n ω o o')
    (hepsM : ∀ n o, Measurable (eps n o)) (hsM : Measurable s)
    (hlink : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n),
      Linked (c n) (dims n) o o' ↔ i n ω o = i n ω o')
    (hPm : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n),
      Pm n ω o o'
        = if i n ω o = i n ω o' then ((Cgm.clusterCard (i n ω) (i n ω o) : ℝ))⁻¹ else 0)
    (hAsym : ∀ᵐ ω ∂P, ∀ n, (A n ω)ᵀ = A n ω)
    (hAidem : ∀ᵐ ω ∂P, ∀ n, A n ω * A n ω = A n ω)
    (hLsym : ∀ᵐ ω ∂P, ∀ n, (Lam n ω)ᵀ = Lam n ω)
    (hLidem : ∀ᵐ ω ∂P, ∀ n, Lam n ω * Lam n ω = Lam n ω)
    (hXcl : ∀ᵐ ω ∂P, ∀ (n : ℕ) (y : Ω) (j : N n) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O n => i n ω o = j), Xr n y o k = 0)
    (hB : ∀ (n : ℕ) (y : Ω), ∀ o : O n, ∑ k : K, Xr n y o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hJ : ∀ n, ((dims n).card : ℝ) ≤ 1) (hC : 0 ≤ C)
    (hGpos : ∀ n, 0 < Gmax n)
    (hG : ∀ᵐ ω ∂P, ∀ (n : ℕ) (j : N n), (Cgm.clusterCard (i n ω) j : ℝ) ≤ Gmax n)
    (hXm : ∀ (n : ℕ) (o : O n) (k : K), StronglyMeasurable[𝒟] fun y => Xr n y o k)
    (hint : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n), Integrable (fun y =>
      ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o
        * ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o') (condExpKernel P 𝒟 ω))
    (hint' : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n), Integrable (fun y =>
      (if Linked (c n) (dims n) o o' then Xr n y o a * Xr n y o' b else 0)
        * (((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o
            * ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o'))
      (condExpKernel P 𝒟 ω))
    (hcross : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n),
      (condExpKernel P 𝒟 ω)[fun y =>
          ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o
            * ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o' | 𝒟]
        =ᵐ[condExpKernel P 𝒟 ω] fun y => s y * (1 - Pm n ω - A n ω - Lam n ω) o o')
    (hL2 : ∀ᵐ ω ∂P, ∀ n, MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n ω - A n ω - Lam n ω)
        (fun y => Xr n y) a b) (eps n)) 2 (condExpKernel P 𝒟 ω))
    (hcv : ∀ᵐ ω ∂P, ∀ n, ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n ω - A n ω - Lam n ω)
          (fun y => Xr n y) a b) (eps n)) (condExpKernel P 𝒟 ω)
      ≤ᵐ[condExpKernel P 𝒟 ω] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ)))))
    (hrate : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
        caseOneRate (A n ω).trace (Lam n ω).trace (Gmax n) (Fintype.card (O n) : ℝ))
      atTop (nhds 0)) :
    TendstoInMeasure P (fun n y =>
        (((Fintype.card (O n) : ℝ))⁻¹
              * meatCGM (c n) (dims n) (fun o k y => Xr n y o k)
                  (fun o y => ((1 - Pm n y - A n y - Lam n y) *ᵥ fun p => eps n p y) o) a b y)
          - s y * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n, Xr n y o a * Xr n y o b))
      atTop (fun _ => (0 : ℝ)) := by
  classical
  have hPmM : ∀ n o o', Measurable fun y : Ω => Pm n y o o' :=
    fun n o o' => (hPmD n o o').mono h𝒟 le_rfl
  have hAM : ∀ n o o', Measurable fun y : Ω => A n y o o' :=
    fun n o o' => (hAD n o o').mono h𝒟 le_rfl
  have hLamM : ∀ n o o', Measurable fun y : Ω => Lam n y o o' :=
    fun n o o' => (hLamD n o o').mono h𝒟 le_rfl
  have hXM : ∀ n o k, Measurable fun y : Ω => Xr n y o k :=
    fun n o k => ((hXm n o k).mono h𝒟).measurable
  have hZ : ∀ n : ℕ, Measurable fun y : Ω =>
      (((Fintype.card (O n) : ℝ))⁻¹
            * meatCGM (c n) (dims n) (fun o k y => Xr n y o k)
                (fun o y => ((1 - Pm n y - A n y - Lam n y) *ᵥ fun p => eps n p y) o) a b y)
        - s y * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n, Xr n y o a * Xr n y o b) := by
    intro n
    have hv : ∀ o : O n, Measurable fun y : Ω =>
        ((1 - Pm n y - A n y - Lam n y) *ᵥ fun p => eps n p y) o :=
      fun o => measurable_residEntry3 (hPmM n) (hAM n) (hLamM n) (hepsM n) o
    refine Measurable.sub
      ((measurable_meatCGM (c n) (dims n) a b (fun o k => hXM n o k) hv).const_mul _) ?_
    exact hsM.mul
      ((Finset.measurable_sum _ fun o _ => (hXM n o a).mul (hXM n o b)).const_mul _)
  have hsets : ∀ (ε : ℝ≥0∞) (n : ℕ), MeasurableSet {y : Ω | ε ≤ edist
      ((((Fintype.card (O n) : ℝ))⁻¹
            * meatCGM (c n) (dims n) (fun o k y => Xr n y o k)
                (fun o y => ((1 - Pm n y - A n y - Lam n y) *ᵥ fun p => eps n p y) o) a b y)
        - s y * (((Fintype.card (O n) : ℝ))⁻¹ * ∑ o : O n, Xr n y o a * Xr n y o b))
      ((fun _ => (0 : ℝ)) y)} := fun ε n =>
    measurableSet_le measurable_const ((hZ n).edist measurable_const)
  refine PrimitiveDesign.CondP.tendstoInMeasure_of_deconditioning h𝒟 P hsets ?_
  filter_upwards [ae_ae_eq_tripleDesign h𝒟 P hPmD hAD hLamD, hlink, hPm, hAsym, hAidem,
    hLsym, hLidem, hXcl, hG, hint, hint', hcross, hL2, hcv, hrate]
    with ω hfz h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  have hcondlaw := caseOne_meat_tendstoInProb (P := condExpKernel P 𝒟 ω) 𝒟 h𝒟 c dims hdims
    (i := fun n => i n ω) h1 (Pm := fun n => Pm n ω) (A := fun n => A n ω)
    (Lam := fun n => Lam n ω) (Xr := Xr) (eps := eps) (s := s)
    h2 h3 h4 h5 h6 h7 hB hs hJ hC hGpos h8 hXm h9 h10 h11 h12 h13 h14
  refine PrimitiveDesign.CondP.tendstoInMeasure_congr_ae (fun n => ?_) hcondlaw
  filter_upwards [hfz n] with y hy
  have hv : ∀ o : O n, ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o
      = ((1 - Pm n y - A n y - Lam n y) *ᵥ fun p => eps n p y) o :=
    fun o => by rw [hy.1, hy.2.1, hy.2.2]
  have hm := meatCGM_congr (c n) (dims n)
      (X := fun o k y' => Xr n y' o k) (X' := fun o k y' => Xr n y' o k)
      (v := fun o y' => ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y') o)
      (v' := fun o y' => ((1 - Pm n y' - A n y' - Lam n y') *ᵥ fun p => eps n p y') o)
      a b y (fun o k => rfl) hv
  show _ = _
  rw [hm]

/-- `nV̂_CGM ⟶^p H⁻¹SH⁻¹` in case (ii) with `P_[Δ]` and `Λ` random. -/
theorem caseTwo_nVhatCGM_tendstoInProb_uncond [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    {Pm Lam : ∀ n, Ω → Matrix (O n) (O n) ℝ} {xi : ∀ n, O n → K → Ω → ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ}
    {B sbar Kbd Jbd C : ℝ} {aN Gmax : ℕ → ℝ} {H S : Matrix K K ℝ}
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o')
    (hLamD : ∀ n o o', Measurable[𝒟] fun ω => Lam n ω o o')
    (hxiM : ∀ n o k, Measurable (xi n o k)) (hepsM : ∀ n o, Measurable (eps n o))
    (hsM : Measurable s)
    (hPms : ∀ᵐ ω ∂P, ∀ n, (Pm n ω)ᵀ = Pm n ω)
    (hPmi : ∀ᵐ ω ∂P, ∀ n, Pm n ω * Pm n ω = Pm n ω)
    (hLs : ∀ᵐ ω ∂P, ∀ n, (Lam n ω)ᵀ = Lam n ω)
    (hLi : ∀ᵐ ω ∂P, ∀ n, Lam n ω * Lam n ω = Lam n ω)
    (hB : ∀ᵐ ω ∂P, ∀ (n : ℕ) (y : Ω), ∀ o : O n,
      ∑ k : K, PrimitiveDesign.within (Pm n ω) (xi n) y o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar)
    (hK : ∀ᵐ ω ∂P, ∀ n, (Lam n ω).trace ≤ Kbd)
    (hJ : ∀ n, ((dims n).card : ℝ) ≤ Jbd) (hC : 0 ≤ C)
    (hPmle : ∀ᵐ ω ∂P, ∀ n, (Pm n ω).trace ≤ aN n) (hone : ∀ n, 1 ≤ aN n)
    (hGsq : ∀ n, Gmax n * (Fintype.card (O n) : ℝ) ≤ (aN n) ^ 2)
    (hGnn : ∀ n, 0 ≤ Gmax n)
    (hXm : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o : O n) (k : K),
      StronglyMeasurable[𝒟] fun y => PrimitiveDesign.within (Pm n ω) (xi n) y o k)
    (hint : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n), Integrable (fun y =>
      ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o
        * ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o') (condExpKernel P 𝒟 ω))
    (hint' : ∀ (a b : K), ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n), Integrable (fun y =>
      (if Linked (c n) (dims n) o o' then
          PrimitiveDesign.within (Pm n ω) (xi n) y o a
            * PrimitiveDesign.within (Pm n ω) (xi n) y o' b else 0)
        * (((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o
            * ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o'))
      (condExpKernel P 𝒟 ω))
    (hcross : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n),
      (condExpKernel P 𝒟 ω)[fun y => ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o
          * ((1 - Pm n ω - Lam n ω) *ᵥ fun p => eps n p y) o' | 𝒟]
        =ᵐ[condExpKernel P 𝒟 ω] fun y => s y * (1 - Pm n ω - Lam n ω) o o')
    (hXi : ∀ᵐ ω ∂P, Sequence.BddInProb (condExpKernel P 𝒟 ω) (fun n y =>
      ‖PrimitiveDesign.xiSharp (c n) (dims n) (Pm n ω) (Lam n ω) (xi n) y‖ / aN n))
    (hL2 : ∀ (a b : K), ∀ᵐ ω ∂P, ∀ n, MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n ω - Lam n ω)
        (fun y => PrimitiveDesign.within (Pm n ω) (xi n) y) a b) (eps n)) 2
      (condExpKernel P 𝒟 ω))
    (hcv : ∀ (a b : K), ∀ᵐ ω ∂P, ∀ n, ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n ω - Lam n ω)
          (fun y => PrimitiveDesign.within (Pm n ω) (xi n) y) a b) (eps n))
        (condExpKernel P 𝒟 ω)
      ≤ᵐ[condExpKernel P 𝒟 ω] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ)))))
    (hrate : Tendsto (fun n : ℕ => aN n / (Fintype.card (O n) : ℝ)) atTop (nhds 0))
    (hH : H.PosDef)
    (hGram : TendstoInMeasure P (fun n y =>
        frobNorm (((Fintype.card (O n) : ℝ))⁻¹
          • ((PrimitiveDesign.within (Pm n y) (xi n) y)ᵀ
              * PrimitiveDesign.within (Pm n y) (xi n) y) - H))
      atTop (fun _ => (0 : ℝ)))
    (hSn : TendstoInMeasure P (fun n y =>
        frobNorm (s y • (((Fintype.card (O n) : ℝ))⁻¹
          • ((PrimitiveDesign.within (Pm n y) (xi n) y)ᵀ
              * PrimitiveDesign.within (Pm n y) (xi n) y)) - S))
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n y =>
        frobNorm ((Fintype.card (O n) : ℝ) •
            (((PrimitiveDesign.within (Pm n y) (xi n) y)ᵀ
                * PrimitiveDesign.within (Pm n y) (xi n) y)⁻¹
              * meatCGMMat (c n) (dims n)
                  (fun o k y => PrimitiveDesign.within (Pm n y) (xi n) y o k)
                  (fun o y => ((1 - Pm n y - Lam n y) *ᵥ fun p => eps n p y) o) y
              * ((PrimitiveDesign.within (Pm n y) (xi n) y)ᵀ
                  * PrimitiveDesign.within (Pm n y) (xi n) y)⁻¹)
          - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) :=
  tendstoInProb_nVhatCGM_of_entries c dims hH hGram
    (fun a b => caseTwo_meat_tendstoInProb_uncond h𝒟 c dims hdims hPmD hLamD hxiM hepsM hsM
      hPms hPmi hLs hLi hB hs hK hJ hC hPmle hone hGsq hGnn hXm hint (hint' a b) hcross hXi
      (hL2 a b) (hcv a b) hrate)
    hSn

/-- `nV̂_CGM ⟶^p H⁻¹SH⁻¹` in case (i) with the design and the clustering random. -/
theorem caseOne_nVhatCGM_tendstoInProb_uncond [IsProbabilityMeasure P] (h𝒟 : 𝒟 ≤ mΩ)
    (c : ∀ n, D n → O n → L n) (dims : ∀ n, Finset (D n)) (hdims : ∀ n, (dims n).Nonempty)
    (i : ∀ n, Ω → O n → N n)
    {Pm A Lam : ∀ n, Ω → Matrix (O n) (O n) ℝ} {Xr : ∀ n, Ω → Matrix (O n) K ℝ}
    {eps : ∀ n, O n → Ω → ℝ} {s : Ω → ℝ}
    {B sbar C : ℝ} {Gmax : ℕ → ℝ} {H S : Matrix K K ℝ}
    (hPmD : ∀ n o o', Measurable[𝒟] fun ω => Pm n ω o o')
    (hAD : ∀ n o o', Measurable[𝒟] fun ω => A n ω o o')
    (hLamD : ∀ n o o', Measurable[𝒟] fun ω => Lam n ω o o')
    (hepsM : ∀ n o, Measurable (eps n o)) (hsM : Measurable s)
    (hlink : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n),
      Linked (c n) (dims n) o o' ↔ i n ω o = i n ω o')
    (hPm : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n),
      Pm n ω o o'
        = if i n ω o = i n ω o' then ((Cgm.clusterCard (i n ω) (i n ω o) : ℝ))⁻¹ else 0)
    (hAsym : ∀ᵐ ω ∂P, ∀ n, (A n ω)ᵀ = A n ω)
    (hAidem : ∀ᵐ ω ∂P, ∀ n, A n ω * A n ω = A n ω)
    (hLsym : ∀ᵐ ω ∂P, ∀ n, (Lam n ω)ᵀ = Lam n ω)
    (hLidem : ∀ᵐ ω ∂P, ∀ n, Lam n ω * Lam n ω = Lam n ω)
    (hXcl : ∀ᵐ ω ∂P, ∀ (n : ℕ) (y : Ω) (j : N n) (k : K),
      ∑ o ∈ Finset.univ.filter (fun o : O n => i n ω o = j), Xr n y o k = 0)
    (hB : ∀ (n : ℕ) (y : Ω), ∀ o : O n, ∑ k : K, Xr n y o k ^ 2 ≤ B ^ 2)
    (hs : ∀ ω, |s ω| ≤ sbar) (hJ : ∀ n, ((dims n).card : ℝ) ≤ 1) (hC : 0 ≤ C)
    (hGpos : ∀ n, 0 < Gmax n)
    (hG : ∀ᵐ ω ∂P, ∀ (n : ℕ) (j : N n), (Cgm.clusterCard (i n ω) j : ℝ) ≤ Gmax n)
    (hXm : ∀ (n : ℕ) (o : O n) (k : K), StronglyMeasurable[𝒟] fun y => Xr n y o k)
    (hint : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n), Integrable (fun y =>
      ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o
        * ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o') (condExpKernel P 𝒟 ω))
    (hint' : ∀ (a b : K), ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n), Integrable (fun y =>
      (if Linked (c n) (dims n) o o' then Xr n y o a * Xr n y o' b else 0)
        * (((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o
            * ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o'))
      (condExpKernel P 𝒟 ω))
    (hcross : ∀ᵐ ω ∂P, ∀ (n : ℕ) (o o' : O n),
      (condExpKernel P 𝒟 ω)[fun y =>
          ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o
            * ((1 - Pm n ω - A n ω - Lam n ω) *ᵥ fun p => eps n p y) o' | 𝒟]
        =ᵐ[condExpKernel P 𝒟 ω] fun y => s y * (1 - Pm n ω - A n ω - Lam n ω) o o')
    (hL2 : ∀ (a b : K), ∀ᵐ ω ∂P, ∀ n, MemLp (Quadform.quadForm
      (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n ω - A n ω - Lam n ω)
        (fun y => Xr n y) a b) (eps n)) 2 (condExpKernel P 𝒟 ω))
    (hcv : ∀ (a b : K), ∀ᵐ ω ∂P, ∀ n, ProbabilityTheory.condVar 𝒟 (Quadform.quadForm
        (normalizedMeatEntry (c n) (dims n) (fun _ => 1 - Pm n ω - A n ω - Lam n ω)
          (fun y => Xr n y) a b) (eps n)) (condExpKernel P 𝒟 ω)
      ≤ᵐ[condExpKernel P 𝒟 ω] fun _ => 3 * C * (B ^ 4 * (((dims n).card : ℝ)
          * (Gmax n / (Fintype.card (O n) : ℝ)))))
    (hrate : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
        caseOneRate (A n ω).trace (Lam n ω).trace (Gmax n) (Fintype.card (O n) : ℝ))
      atTop (nhds 0))
    (hH : H.PosDef)
    (hGram : TendstoInMeasure P (fun n y =>
        frobNorm (((Fintype.card (O n) : ℝ))⁻¹ • ((Xr n y)ᵀ * Xr n y) - H))
      atTop (fun _ => (0 : ℝ)))
    (hSn : TendstoInMeasure P (fun n y =>
        frobNorm (s y • (((Fintype.card (O n) : ℝ))⁻¹ • ((Xr n y)ᵀ * Xr n y)) - S))
      atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n y =>
        frobNorm ((Fintype.card (O n) : ℝ) •
            (((Xr n y)ᵀ * Xr n y)⁻¹
              * meatCGMMat (c n) (dims n) (fun o k y => Xr n y o k)
                  (fun o y => ((1 - Pm n y - A n y - Lam n y) *ᵥ fun p => eps n p y) o) y
              * ((Xr n y)ᵀ * Xr n y)⁻¹)
          - H⁻¹ * S * H⁻¹))
      atTop (fun _ => (0 : ℝ)) :=
  tendstoInProb_nVhatCGM_of_entries c dims hH hGram
    (fun a b => caseOne_meat_tendstoInProb_uncond h𝒟 c dims hdims i hPmD hAD hLamD hepsM hsM
      hlink hPm hAsym hAidem hLsym hLidem hXcl hB hs hJ hC hGpos hG hXm hint (hint' a b)
      hcross (hL2 a b) (hcv a b) hrate)
    hSn

/-! ### Example for the random design

On the two-coin space `Ω = Bool × Bool` with `𝒟 = σ(first coin)`, `P_[Δ],n(ω)` is the rank-one
projector `sharpWitnessPm n` when the first coin is `true` and `0` otherwise, with `n+1`
observations at index `n`. The disturbances are degenerate (`ξ ≡ 0`, `ε ≡ 0`, `σ²_ε = 0`). -/

section CaseTwoDecondWitness

namespace CaseTwoDecondWitness

open Multiway.CLTMartingale.CondD.FrozenWitness

/-- The random `P_[Δ],n`, equal to the rank-one projector when the first coin is `true` and to `0`
otherwise. -/
noncomputable def wPmR (n : ℕ) (ω : Omg) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  if ω.1 then PrimitiveDesign.sharpWitnessPm n else 0

theorem wPmR_trace (n : ℕ) (ω : Omg) : (wPmR n ω).trace = if ω.1 then 1 else 0 := by
  unfold wPmR
  by_cases h : ω.1 <;> simp [h, PrimitiveDesign.sharpWitnessPm_trace]

theorem wPmR_transpose (n : ℕ) (ω : Omg) : (wPmR n ω)ᵀ = wPmR n ω := by
  unfold wPmR
  by_cases h : ω.1
  · simp only [h, if_true, PrimitiveDesign.sharpWitnessPm, Matrix.diagonal_transpose]
  · simp [h]

theorem wPmR_idem (n : ℕ) (ω : Omg) : wPmR n ω * wPmR n ω = wPmR n ω := by
  unfold wPmR
  by_cases h : ω.1
  · simp only [h, if_true, PrimitiveDesign.sharpWitnessPm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext o
    by_cases ho : o = 0 <;> simp [ho]
  · simp [h]

theorem wPmR_meas (n : ℕ) (o o' : Fin (n + 1)) :
    Measurable[Dsig] fun ω : Omg => wPmR n ω o o' := by
  have h : (fun ω : Omg => wPmR n ω o o')
      = (fun c : Bool => if c then PrimitiveDesign.sharpWitnessPm n o o' else 0) ∘ Prod.fst := by
    funext ω
    unfold wPmR
    by_cases hc : ω.1 <;> simp [hc, Function.comp]
  rw [h]
  exact Measurable.of_discrete.comp meas_fst

/-- The within-transformed regressor vanishes. -/
theorem wWithin (n : ℕ) (ω y : Omg) :
    PrimitiveDesign.within (wPmR n ω)
      (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y = 0 := by
  have hth : PrimitiveDesign.theta
      (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y = 0 := by
    ext o j; rfl
  rw [PrimitiveDesign.within, hth, Matrix.mul_zero]

theorem wResid (n : ℕ) (ω : Omg) (o : Fin (n + 1)) :
    ((1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
      *ᵥ fun _ : Fin (n + 1) => (0 : ℝ)) o = 0 := by
  simp [Matrix.mulVec, dotProduct]

theorem wXiSharp (n : ℕ) (ω y : Omg) :
    PrimitiveDesign.xiSharp (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
      ({0} : Finset (Fin 1)) (wPmR n ω)
      (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y = 0 := by
  rw [PrimitiveDesign.xiSharp, wWithin n ω y, Cgm.xiMat, Matrix.transpose_zero,
    Matrix.zero_mul, Matrix.zero_mul]

theorem wRate :
    Tendsto (fun n : ℕ => (1 : ℝ) / (Fintype.card (Fin (n + 1)) : ℝ)) atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (((n : ℝ) + 1))⁻¹) atTop (nhds 0) := by
    simpa [Pi.inv_def] using h.inv_tendsto_atTop
  refine h2.congr fun n => ?_
  rw [Fintype.card_fin]
  push_cast
  rw [one_div]

/-- `caseTwo_meat_tendstoInProb_uncond` holds at the example, with `𝒟` a proper sub-σ-field,
`ℙ_ω ≠ P`, and `d_[Δ]` taking the values `1` and `0` with probability `1/2` each. -/
theorem caseTwo_meat_tendstoInProb_uncond_witness :
    (∃ B : Set Omg, MeasurableSet B ∧ ¬ MeasurableSet[Dsig] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dsig ω = Pw)
    ∧ Pw {y : Omg | y.1 = true} = 2⁻¹
    ∧ (∀ n : ℕ, (wPmR n (true, true)).trace = 1 ∧ (wPmR n (false, true)).trace = 0)
    ∧ TendstoInMeasure Pw (fun n y =>
        ((Fintype.card (Fin (n + 1)) : ℝ))⁻¹
              * meatCGM (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
                  ({0} : Finset (Fin 1))
                  (fun o k y => PrimitiveDesign.within (wPmR n y)
                    (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y o k)
                  (fun o y => ((1 - wPmR n y
                      - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
                    *ᵥ fun p => (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) p y) o) 0 0 y
            - (0 : ℝ) * (((Fintype.card (Fin (n + 1)) : ℝ))⁻¹
                * ∑ o : Fin (n + 1),
                    PrimitiveDesign.within (wPmR n y)
                      (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y o 0
                      * PrimitiveDesign.within (wPmR n y)
                          (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y o 0))
      atTop (fun _ => (0 : ℝ)) := by
  classical
  refine ⟨Dsig_proper, freeze_witness.2.2.2.2, Pw_fst true,
    fun n => ⟨by rw [wPmR_trace]; norm_num, by rw [wPmR_trace]; norm_num⟩, ?_⟩
  refine caseTwo_meat_tendstoInProb_uncond (𝒟 := Dsig) (P := Pw)
    (O := fun n => Fin (n + 1)) (D := fun _ => Fin 1) (L := fun _ => Fin 1)
    Dsig_le (fun (n : ℕ) (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
    (fun _ => ({0} : Finset (Fin 1))) (fun _ => Finset.singleton_nonempty 0)
    (Pm := wPmR) (Lam := fun n _ => (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (xi := fun (n : ℕ) (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ))
    (eps := fun (n : ℕ) (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ))
    (s := fun _ : Omg => (0 : ℝ)) (a := 0) (b := 0)
    (B := (0 : ℝ)) (sbar := (0 : ℝ)) (Kbd := (0 : ℝ)) (Jbd := (1 : ℝ)) (C := (0 : ℝ))
    (aN := fun _ => (1 : ℝ)) (Gmax := fun _ => (0 : ℝ))
    wPmR_meas (fun _ _ _ => measurable_const) (fun _ _ _ => measurable_const)
    (fun _ _ => measurable_const) measurable_const
    (Filter.Eventually.of_forall fun ω n => wPmR_transpose n ω)
    (Filter.Eventually.of_forall fun ω n => wPmR_idem n ω)
    (Filter.Eventually.of_forall fun _ _ => Matrix.transpose_zero)
    (Filter.Eventually.of_forall fun _ _ => by simp)
    ?_ (fun _ => by norm_num) (Filter.Eventually.of_forall fun _ _ => by simp)
    (fun _ => by norm_num) le_rfl ?_ (fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => le_rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ wRate
  · refine Filter.Eventually.of_forall fun ω n y o => ?_
    rw [wWithin n ω y]
    simp
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [wPmR_trace]
    by_cases h : ω.1 <;> simp [h]
  · refine Filter.Eventually.of_forall fun ω n o k => ?_
    have hz : (fun y : Omg => PrimitiveDesign.within (wPmR n ω)
        (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y o k)
        = fun _ : Omg => (0 : ℝ) := by
      funext y
      rw [wWithin n ω y]
      rfl
    rw [hz]
    exact stronglyMeasurable_const
  · refine Filter.Eventually.of_forall fun ω n o o' => ?_
    have hz : (fun y : Omg =>
        ((1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
            *ᵥ fun p => (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) p y) o
          * ((1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
            *ᵥ fun p => (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) p y) o')
        = fun _ : Omg => (0 : ℝ) := by
      funext y
      rw [wResid n ω o, zero_mul]
    rw [hz]
    exact integrable_const 0
  · refine Filter.Eventually.of_forall fun ω n o o' => ?_
    have hz : (fun y : Omg =>
        (if Linked (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
              ({0} : Finset (Fin 1)) o o' then
            PrimitiveDesign.within (wPmR n ω)
              (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y o 0
              * PrimitiveDesign.within (wPmR n ω)
                  (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y o' 0 else 0)
          * (((1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
              *ᵥ fun p => (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) p y) o
            * ((1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
              *ᵥ fun p => (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) p y) o'))
        = fun _ : Omg => (0 : ℝ) := by
      funext y
      rw [wResid n ω o, zero_mul, mul_zero]
    rw [hz]
    exact integrable_const 0
  · refine Filter.Eventually.of_forall fun ω n o o' => ?_
    have hz : (fun y : Omg =>
        ((1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
            *ᵥ fun p => (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) p y) o
          * ((1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
            *ᵥ fun p => (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) p y) o')
        = fun _ : Omg => (0 : ℝ) := by
      funext y
      rw [wResid n ω o, zero_mul]
    rw [hz, show (fun _ : Omg => (0 : ℝ)) = 0 from rfl, MeasureTheory.condExp_zero]
    exact Filter.Eventually.of_forall fun y => by simp
  · refine Filter.Eventually.of_forall fun ω => ?_
    refine Sequence.bddInProb_of_abs_le_const (M := 1) (fun n => ?_)
    filter_upwards with y
    rw [wXiSharp n ω y]
    simp
  · refine Filter.Eventually.of_forall fun ω n => ?_
    have hq : Quadform.quadForm
        (normalizedMeatEntry (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
          ({0} : Finset (Fin 1))
          (fun _ : Omg => 1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
          (fun y : Omg => PrimitiveDesign.within (wPmR n ω)
            (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y) 0 0)
        (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext y
      rw [Quadform.quadForm_apply]
      simp
    rw [hq]
    exact memLp_const 0
  · refine Filter.Eventually.of_forall fun ω n => ?_
    have hq : Quadform.quadForm
        (normalizedMeatEntry (fun (_ : Fin 1) (_ : Fin (n + 1)) => (0 : Fin 1))
          ({0} : Finset (Fin 1))
          (fun _ : Omg => 1 - wPmR n ω - (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
          (fun y : Omg => PrimitiveDesign.within (wPmR n ω)
            (fun (_ : Fin (n + 1)) (_ : Fin 1) (_ : Omg) => (0 : ℝ)) y) 0 0)
        (fun (_ : Fin (n + 1)) (_ : Omg) => (0 : ℝ)) = 0 := by
      funext y
      rw [Quadform.quadForm_apply]
      simp
    rw [hq, ProbabilityTheory.condVar_zero]
    exact Filter.Eventually.of_forall fun _ => by norm_num

end CaseTwoDecondWitness

end CaseTwoDecondWitness

end DesignDecond

end Absorbed
end Multiway
