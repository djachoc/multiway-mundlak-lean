import Multiway.SteinCluster
import Multiway.Sharing
import Multiway.RateAgnostic

/-!
# Feasible inference under the cluster-shock model

This file formalizes Corollary SM.D.3 of the paper (Feasible inference under the cluster-shock
model). The disturbance is `ν_o = ∑_j c^{(j)}_{g_j(o)} + ε_o` with independent cluster shocks and
idiosyncratic terms, and the covariance matrix is `Ω = ∑_j σ²_{c,j} Sh^{(j)} + diag(Var(ε_o ∣ 𝒟))`.
The central limit theorems are obtained through the Stein dependency-graph bound of
`Multiway.SteinCluster`: with one clustering dimension at the rate `Ḡ_n³/n → 0`, and with `J`
dimensions at the rate `Ḡ_n⁴/n → 0`.

## Main results

* `clustershock_a_oneDimension`: asymptotic normality at `J = 1` under `Ḡ_n³/n → 0`.
* `clustershock_a_general`, `clustershock_b_general`: bounded shocks, resp. bounded conditional
  fourth moments, at general `J` under `Ḡ_n⁴/n → 0`.
* `clustershock_a_general_unconditional_vector`: `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)` under
  the full measure with a `𝒟`-measurable random design.
* `clustershock_rateagnostic_a`, `_b`, `_c`: Theorem 11 (Rate-agnostic inference under multiway
  clustering) for the cluster-shock model, including the Wald step.
* Vacuity witnesses on explicit cluster-shock designs.
-/

namespace Multiway.ClusterShock

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators MatrixOrder
open Matrix
open Causalean.Mathlib.Probability.SteinMethod
open Multiway.SteinCluster

/-! ### The cluster-shock covariance matrix at `J = 1` -/

section Omega

variable {O L : Type*} [Fintype O] [DecidableEq O] [DecidableEq L]

/-- The cluster-shock covariance matrix at `J = 1`, `Ω = σ²_c Sh^{(1)} + diag(Var(ε_o ∣ 𝒟))`,
defined as `Multiway.Sharing.clusterOmega` over a one-element dimension index. -/
noncomputable def omegaOf (g : O → L) (scv : ℝ) (ve : O → ℝ) : Matrix O O ℝ :=
  Multiway.Sharing.clusterOmega (fun _ : Fin 1 => g) Finset.univ (fun _ => scv) ve

omit [Fintype O] [DecidableEq O] [DecidableEq L] in
theorem sameOn_iff {g : O → L} {o o' : O} :
    Multiway.SameOn (fun _ : Fin 1 => g) {(0 : Fin 1)} o o' ↔ g o = g o' :=
  ⟨fun h => h 0 (Finset.mem_singleton_self 0), fun h _ _ => h⟩

omit [Fintype O] in
/-- The entries of `omegaOf`. -/
theorem omegaOf_apply (g : O → L) (scv : ℝ) (ve : O → ℝ) (o o' : O) :
    omegaOf g scv ve o o'
      = (if g o = g o' then scv else 0) + (if o = o' then ve o else 0) := by
  rw [omegaOf, Multiway.Sharing.clusterOmega_apply]
  congr 1
  rw [show (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} from rfl, Finset.sum_singleton]
  by_cases h : g o = g o'
  · rw [ite_eq_left (sameOn_iff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hs => h (sameOn_iff.mp hs)), ite_eq_right h]

/-- The variance floor `Ω ⪰ σ̲²I_n`. -/
theorem smul_one_le_omegaOf {g : O → L} {scv s2 : ℝ} {ve : O → ℝ} (hsc : 0 ≤ scv)
    (hve : ∀ o, s2 ≤ ve o) : s2 • (1 : Matrix O O ℝ) ≤ omegaOf g scv ve :=
  Multiway.Sharing.smul_one_le_clusterOmega (fun _ _ => hsc) hve

omit [Fintype O] in
/-- `Ω_{oo'} = 0` whenever `o` and `o'` lie in different clusters. -/
theorem omegaOf_eq_zero_of_ne {g : O → L} {scv : ℝ} {ve : O → ℝ} {o o' : O}
    (hne : g o ≠ g o') : omegaOf g scv ve o o' = 0 :=
  Multiway.Sharing.clusterOmega_eq_zero_of_not_linked (c := fun _ : Fin 1 => g)
    Finset.univ_nonempty (by rintro ⟨j, -, hj⟩; exact hne hj)

end Omega

/-! ### The rate: from the cluster-size condition to the Stein rate -/

/-- With `λ_min(Ω_n) ≥ λ₀n` and `φ_n = BC_ν/√(λ₀n)`, `Ḡ_nφ_n ≤ (BC_ν/√λ₀)·√(Ḡ_n³/n)`,
using `Ḡ_n ≤ √(Ḡ_n³)` for `Ḡ_n ≥ 1`. -/
theorem rate_le_sqrt_cube {B Cnu lam0 nO Gbr : ℝ} (hB : 0 ≤ B) (hCnu : 0 ≤ Cnu)
    (hlam0 : 0 < lam0) (hnO : 0 < nO) (hG : 1 ≤ Gbr) :
    Gbr * (B * Cnu / Real.sqrt (lam0 * nO))
      ≤ (B * Cnu / Real.sqrt lam0) * Real.sqrt (Gbr ^ 3 / nO) := by
  have hG0 : (0 : ℝ) ≤ Gbr := le_trans zero_le_one hG
  have hl : 0 < Real.sqrt lam0 := Real.sqrt_pos.mpr hlam0
  have hn : 0 < Real.sqrt nO := Real.sqrt_pos.mpr hnO
  have hcube : Gbr ≤ Real.sqrt (Gbr ^ 3) := by
    have h2 : Gbr ^ 2 ≤ Gbr ^ 3 := by nlinarith
    calc Gbr = Real.sqrt (Gbr ^ 2) := (Real.sqrt_sq hG0).symm
      _ ≤ Real.sqrt (Gbr ^ 3) := Real.sqrt_le_sqrt h2
  have hs1 : Real.sqrt (lam0 * nO) = Real.sqrt lam0 * Real.sqrt nO :=
    Real.sqrt_mul hlam0.le nO
  have hs2 : Real.sqrt (Gbr ^ 3 / nO) = Real.sqrt (Gbr ^ 3) / Real.sqrt nO :=
    Real.sqrt_div (by positivity) nO
  have key : Gbr * (B * Cnu) ≤ B * Cnu * Real.sqrt (Gbr ^ 3) := by
    nlinarith [hcube, mul_nonneg hB hCnu]
  rw [hs1, hs2]
  calc Gbr * (B * Cnu / (Real.sqrt lam0 * Real.sqrt nO))
      = Gbr * (B * Cnu) / (Real.sqrt lam0 * Real.sqrt nO) := by ring
    _ ≤ B * Cnu * Real.sqrt (Gbr ^ 3) / (Real.sqrt lam0 * Real.sqrt nO) := by
        gcongr
    _ = B * Cnu / Real.sqrt lam0 * (Real.sqrt (Gbr ^ 3) / Real.sqrt nO) := by
        field_simp

/-! ### The corollary at `J = 1` -/

/-- **Corollary SM.D.3 at `J = 1`.** Under the cluster-shock model with one clustering
dimension, bounded shocks, a variance floor `Var(ε_o ∣ 𝒟) ≥ σ̲² > 0` and `Ḡ_n³/n → 0`, the
standardized restriction `b'𝒱_n^{-1/2}𝓡_n(β̂_JM − β)` is asymptotically standard normal. -/
theorem clustershock_a_oneDimension
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, O n → L n)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ g n o = g n o')
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (sc : ℕ → ℝ) (ve : ∀ n, O n → ℝ) (hsc : ∀ n, 0 ≤ sc n)
    (s2 : ℝ) (hs2 : 0 < s2) (hve : ∀ n o, s2 ≤ ve n o)
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n) = omegaOf (g n) (sc n) (ve n) o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (θ : ℝ) (hθ : 0 < θ) (nObs : ℕ → ℝ) (hnObs : ∀ n, 0 < nObs n)
    (hdesign : ∀ n, (θ * nObs n) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (Gb : ℕ → ℕ) (hGb1 : ∀ n, 1 ≤ Gb n) (hGb : ∀ n γ, (cluster (g n) γ).card ≤ Gb n)
    (hGrate : Tendsto (fun n => (Gb n : ℝ) ^ 3 / nObs n) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n) (omegaOf (g n) (sc n) (ve n)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  -- `Ω ⪰ σ̲²I_n`
  have hfloorOm : ∀ n, s2 • (1 : Matrix (O n) (O n) ℝ) ≤ omegaOf (g n) (sc n) (ve n) :=
    fun n => smul_one_le_omegaOf (hsc n) (hve n)
  -- `Ω_n = X̃'ΩX̃ ⪰ σ̲²X̃'X̃ ⪰ σ̲²θnI`
  have hfloorK : ∀ n, (s2 * (θ * nObs n)) • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n) (omegaOf (g n) (sc n) (ve n)) := by
    intro n
    have h1 : s2 • ((θ * nObs n) • (1 : Matrix K K ℝ)) ≤ s2 • ((Xt n)ᵀ * Xt n) :=
      Multiway.loewner_smul_le_smul hs2.le (hdesign n)
    rw [smul_smul] at h1
    exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj (hfloorOm n) (Xt n))
  refine cltcluster_a_oneDimension_betaJM_of_delta μ Xt
    (fun n => omegaOf (g n) (sc n) (ve n)) Rn ν bhat β g Dv hshare hscore hA
    (fun n => s2 * (θ * nObs n)) (fun n => mul_pos hs2 (mul_pos hθ (hnObs n))) hfloorK hOm hmean
    B Cnu hB0 hCnu0 hB hnu Gb hGb
    (fun n => (Gb n : ℝ) ^ 3 / nObs n) (B * Cnu / Real.sqrt (s2 * θ)) ?_ hGrate b hb s
  intro n
  have hassoc : s2 * (θ * nObs n) = (s2 * θ) * nObs n := by ring
  rw [hassoc]
  exact rate_le_sqrt_cube hB0 hCnu0 (by positivity) (hnObs n)
    (by exact_mod_cast hGb1 n)

/-! ### Vacuity witness

At sample size `n` there are `n+1` clusters of two observations; the members of a cluster share
one fair-sign shock and each observation carries its own fair sign, so `Ḡ_n = 2` and `Ω` is not
diagonal. -/

section Witness

open Multiway.Multilinear

/-- `𝒪_n := {0,…,n} × {0,1}`: `n+1` clusters of two observations each, `2(n+1)` observations. -/
abbrev WsO (n : ℕ) := Fin (n + 1) × Fin 2

/-- The cluster shock of cluster `γ` reads coin `3γ`. -/
def cIdx (n : ℕ) (γ : Fin (n + 1)) : Fin (3 * (n + 1)) :=
  ⟨3 * γ.val, by have := γ.isLt; omega⟩

/-- The idiosyncratic disturbance of `o = (γ,k)` reads coin `3γ + 1 + k`. -/
def eIdx (n : ℕ) (o : WsO n) : Fin (3 * (n + 1)) :=
  ⟨3 * o.1.val + 1 + o.2.val, by have := o.1.isLt; have := o.2.isLt; omega⟩

theorem cIdx_injective (n : ℕ) : Function.Injective (cIdx n) := by
  intro a c h
  have h1 := congrArg Fin.val h
  simp only [cIdx] at h1
  exact Fin.ext (by omega)

theorem eIdx_injective (n : ℕ) : Function.Injective (eIdx n) := by
  intro a c h
  have h1 := congrArg Fin.val h
  simp only [eIdx] at h1
  have ha := a.2.isLt
  have hc := c.2.isLt
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem cIdx_ne_eIdx (n : ℕ) (γ : Fin (n + 1)) (o : WsO n) : cIdx n γ ≠ eIdx n o := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [cIdx, eIdx] at h1
  have := o.2.isLt
  omega

/-- `ν_o = c_{g(o)} + ε_o`, the cluster-shock representation with both components fair signs. -/
noncomputable def wsNu (n : ℕ) (o : WsO n) (ω : Fin (3 * (n + 1)) → Bool) : ℝ :=
  sign2 (cIdx n o.1) ω + sign2 (eIdx n o) ω

theorem measurable_wsNu (n : ℕ) (o : WsO n) : Measurable (wsNu n o) :=
  (measurable_sign2 _).add (measurable_sign2 _)

theorem abs_wsNu_le (n : ℕ) (o : WsO n) (ω : Fin (3 * (n + 1)) → Bool) : |wsNu n o ω| ≤ 2 := by
  refine (abs_add_le _ _).trans ?_
  have h1 := Multiway.SteinCluster.abs_sign2_le' (cIdx n o.1) ω
  have h2 := Multiway.SteinCluster.abs_sign2_le' (eIdx n o) ω
  linarith

/-- The coin indices the observations in `A` depend on. -/
def wsIdx (n : ℕ) (A : Finset (WsO n)) : Finset (Fin (3 * (n + 1))) :=
  A.image (fun o => cIdx n o.1) ∪ A.image (eIdx n)

theorem cIdx_mem_wsIdx {n : ℕ} {A : Finset (WsO n)} {o : WsO n} (ho : o ∈ A) :
    cIdx n o.1 ∈ wsIdx n A :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ ho)

theorem eIdx_mem_wsIdx {n : ℕ} {A : Finset (WsO n)} {o : WsO n} (ho : o ∈ A) :
    eIdx n o ∈ wsIdx n A :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ ho)

/-- Two non-adjacent sets of observations depend on disjoint sets of coins. -/
theorem wsIdx_disjoint {n : ℕ} {A Bs : Finset (WsO n)}
    (hsep : ∀ a ∈ A, ∀ c ∈ Bs, ¬ (a.1 = c.1)) : Disjoint (wsIdx n A) (wsIdx n Bs) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  simp only [wsIdx, Finset.mem_union, Finset.mem_image] at hxA hxB
  rcases hxA with ⟨a, ha, hax⟩ | ⟨a, ha, hax⟩ <;> rcases hxB with ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
  · exact hsep a ha c hc (cIdx_injective n (hax.trans hcx.symm))
  · exact cIdx_ne_eIdx n a.1 c (hax.trans hcx.symm)
  · exact cIdx_ne_eIdx n c.1 a (hcx.trans hax.symm)
  · have hac : a = c := eIdx_injective n (hax.trans hcx.symm)
    exact hsep a ha c hc (by rw [hac])

/-- The map that rebuilds `(ν_o)_{o∈A}` out of the shock coordinates indexed by `S`. -/
noncomputable def wsRebuild (n : ℕ) (A : Finset (WsO n)) (S : Finset (Fin (3 * (n + 1))))
    (t : ↥S → ℝ) (o : ↥A) : ℝ :=
  (if h : cIdx n (o : WsO n).1 ∈ S then t ⟨cIdx n (o : WsO n).1, h⟩ else 0)
  + (if h : eIdx n (o : WsO n) ∈ S then t ⟨eIdx n (o : WsO n), h⟩ else 0)

theorem measurable_wsRebuild (n : ℕ) (A : Finset (WsO n)) (S : Finset (Fin (3 * (n + 1)))) :
    Measurable (wsRebuild n A S) := by
  refine Measurable.of_eval fun o => ?_
  simp only [wsRebuild]
  refine Measurable.add ?_ ?_
  · by_cases h : cIdx n (o : WsO n).1 ∈ S
    · simp only [dite_eq_left h]
      exact measurable_pi_apply _
    · simp only [dite_eq_right h]
      exact measurable_const
  · by_cases h : eIdx n (o : WsO n) ∈ S
    · simp only [dite_eq_left h]
      exact measurable_pi_apply _
    · simp only [dite_eq_right h]
      exact measurable_const

theorem wsRebuild_comp (n : ℕ) (A : Finset (WsO n)) :
    wsRebuild n A (wsIdx n A)
        ∘ (fun ω (i : ↥(wsIdx n A)) => sign2 (i : Fin (3 * (n + 1))) ω)
      = fun ω => fun o : ↥A => wsNu n (o : WsO n) ω := by
  funext ω o
  simp only [Function.comp_apply, wsRebuild, wsNu]
  rw [dite_eq_left (cIdx_mem_wsIdx o.2), dite_eq_left (eIdx_mem_wsIdx o.2)]

/-- The sharing graph of the witness design is a dependency graph for `ν`. -/
noncomputable def wsDep (n : ℕ) : DepGraph (wsNu n) (coins (3 * (n + 1))) where
  G := fun o o' => o.1 = o'.1
  decG := fun _ _ => inferInstance
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  meas := measurable_wsNu n
  indep := by
    intro A Bs hsep
    have h0 := (iIndepFun_sign2 (3 * (n + 1))).indepFun_finset (wsIdx n A) (wsIdx n Bs)
      (wsIdx_disjoint hsep) measurable_sign2
    have key := h0.comp (measurable_wsRebuild n A (wsIdx n A))
      (measurable_wsRebuild n Bs (wsIdx n Bs))
    rwa [wsRebuild_comp, wsRebuild_comp] at key

theorem integrable_sign2_mul {m : ℕ} (i j : Fin m) :
    Integrable (fun ω => sign2 i ω * sign2 j ω) (coins m) := by
  refine Integrable.of_bound
    ((measurable_sign2 i).mul (measurable_sign2 j)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := Multiway.SteinCluster.abs_sign2_le' i ω
  have h2 := Multiway.SteinCluster.abs_sign2_le' j ω
  nlinarith [abs_nonneg (sign2 i ω), abs_nonneg (sign2 j ω)]

theorem integrable_sign2 {m : ℕ} (i : Fin m) : Integrable (sign2 i) (coins m) :=
  Integrable.of_bound (measurable_sign2 i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact Multiway.SteinCluster.abs_sign2_le' i ω)

/-- The integral of a four-term sum. -/
theorem integral_four {m : ℕ} (f1 f2 f3 f4 : (Fin m → Bool) → ℝ)
    (h1 : Integrable f1 (coins m)) (h2 : Integrable f2 (coins m))
    (h3 : Integrable f3 (coins m)) (h4 : Integrable f4 (coins m)) :
    ∫ ω, (f1 ω + f2 ω + f3 ω + f4 ω) ∂(coins m)
      = ∫ ω, f1 ω ∂(coins m) + ∫ ω, f2 ω ∂(coins m) + ∫ ω, f3 ω ∂(coins m)
        + ∫ ω, f4 ω ∂(coins m) := by
  have h12 : Integrable (fun ω => f1 ω + f2 ω) (coins m) := h1.add h2
  have h123 : Integrable (fun ω => f1 ω + f2 ω + f3 ω) (coins m) := h12.add h3
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]

/-- The second moments of the witness disturbance: `2` on the diagonal, `1` within a cluster,
`0` across clusters. -/
theorem integral_wsNu_mul (n : ℕ) (o o' : WsO n) :
    ∫ ω, wsNu n o ω * wsNu n o' ω ∂(coins (3 * (n + 1)))
      = (if o.1 = o'.1 then (1 : ℝ) else 0) + (if o = o' then 1 else 0) := by
  have hexp : (fun ω => wsNu n o ω * wsNu n o' ω)
      = fun ω => sign2 (cIdx n o.1) ω * sign2 (cIdx n o'.1) ω
          + sign2 (cIdx n o.1) ω * sign2 (eIdx n o') ω
          + sign2 (eIdx n o) ω * sign2 (cIdx n o'.1) ω
          + sign2 (eIdx n o) ω * sign2 (eIdx n o') ω := by
    funext ω
    simp only [wsNu]
    ring
  rw [hexp, integral_four _ _ _ _ (integrable_sign2_mul _ _) (integrable_sign2_mul _ _)
      (integrable_sign2_mul _ _) (integrable_sign2_mul _ _),
    Multiway.SteinCluster.integral_sign2_mul, Multiway.SteinCluster.integral_sign2_mul,
    Multiway.SteinCluster.integral_sign2_mul, Multiway.SteinCluster.integral_sign2_mul]
  have hc1 : (cIdx n o.1 = cIdx n o'.1) ↔ (o.1 = o'.1) :=
    ⟨fun h => cIdx_injective n h, fun h => by rw [h]⟩
  have he1 : (eIdx n o = eIdx n o') ↔ (o = o') :=
    ⟨fun h => eIdx_injective n h, fun h => by rw [h]⟩
  rw [ite_eq_right (cIdx_ne_eIdx n o.1 o'), ite_eq_right (Ne.symm (cIdx_ne_eIdx n o'.1 o))]
  simp only [hc1, he1, add_zero]

/-- The witness design matrix: one regressor, equal to `1` at every observation. -/
noncomputable def wsXt (n : ℕ) : Matrix (WsO n) (Fin 1) ℝ := fun _ _ => 1

theorem wsXt_transpose_mul_self (n : ℕ) :
    (wsXt n)ᵀ * wsXt n = (((n : ℝ) + 1) * 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [wsXt, Matrix.mul_apply, Fintype.card_prod]

theorem wsXt_scoreMap_injective (n : ℕ) :
    Function.Injective (scoreMap (wsXt n) (1 : Matrix (Fin 1) (Fin 1) ℝ)).mulVec := by
  refine Matrix.mulVec_injective_of_isUnit ?_
  have h : scoreMap (wsXt n) (1 : Matrix (Fin 1) (Fin 1) ℝ) = ((wsXt n)ᵀ * wsXt n)⁻¹ := by
    rw [scoreMap, Matrix.transpose_one, Matrix.mul_one]
  rw [h, Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det,
    wsXt_transpose_mul_self, Matrix.det_smul, Matrix.det_one]
  refine isUnit_iff_ne_zero.mpr ?_
  simp
  positivity

theorem wsCluster_card (n : ℕ) (γ : Fin (n + 1)) :
    (cluster (Prod.fst : WsO n → Fin (n + 1)) γ).card ≤ 2 := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (fun o => o.2)
    (fun _ _ => Finset.mem_univ _) ?_) ?_
  · intro a ha c hc h
    simp only [Finset.mem_coe, mem_cluster] at ha hc
    exact Prod.ext (ha.trans hc.symm) h
  · simp

/-- Vacuity witness for `clustershock_a_oneDimension`: `n+1` clusters of two observations, one
regressor `x̃_o = 1`, and `ν_o = c_{g(o)} + ε_o` with independent fair signs, so that
`σ²_{c,1} = 1`, `σ̲² = 1`, `C_ν = 2` and `Ω` is not diagonal. -/
theorem clustershock_a_oneDimension_witness (s : ℝ) :
    Tendsto (fun n => ((coins (3 * (n + 1))).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (wsXt n)
              (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((wsXt n)ᵀ * wsXt n)⁻¹ *ᵥ ((wsXt n)ᵀ *ᵥ (fun o => wsNu n o ω)))
                - (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine clustershock_a_oneDimension (O := fun n => WsO n) (L := fun n => Fin (n + 1))
    (fun n => coins (3 * (n + 1))) wsXt (fun _ => 1) wsNu
    (fun n ω => ((wsXt n)ᵀ * wsXt n)⁻¹ *ᵥ ((wsXt n)ᵀ *ᵥ (fun o => wsNu n o ω)))
    (fun _ => 0) (fun _ => Prod.fst) wsDep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    wsXt_scoreMap_injective (fun _ => 1) (fun _ _ => 1) (fun _ => zero_le_one) 1 zero_lt_one
    (fun _ _ => le_refl 1) ?_ ?_ 1 2 zero_le_one (by norm_num) ?_ ?_
    1 zero_lt_one (fun n => ((n : ℝ) + 1) * 2) (fun n => by positivity) ?_
    (fun _ => 2) (fun _ => one_le_two) ?_ ?_ (fun _ => (1 : ℝ)) ?_ s
  · -- `hOm`
    intro n o o'
    rw [integral_wsNu_mul, omegaOf_apply]
  · -- `hmean`
    intro n o
    simp only [wsNu]
    rw [integral_add (integrable_sign2 _) (integrable_sign2 _), integral_sign2, integral_sign2,
      add_zero]
  · -- `hB`
    intro _ _
    simp [wsXt, dotProduct]
  · -- `hnu`
    intro n o ω
    exact abs_wsNu_le n o ω
  · -- `hdesign`
    intro n
    rw [wsXt_transpose_mul_self, one_mul]
  · -- `hGb`
    intro n γ
    exact wsCluster_card n γ
  · -- `hGrate`
    have hd : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * 2) atTop atTop := by
      refine Filter.Tendsto.atTop_mul_const (by norm_num) ?_
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using (tendsto_const_nhds (x := (2 : ℝ) ^ 3) (f := atTop (α := ℕ))).div_atTop hd
  · -- `hb`
    simp [dotProduct]

end Witness

/-! ### The corollary at `J = 1` with a random design, under the full measure

Here `X̃_n` is a `𝒟`-measurable random matrix, the cluster map and the variances are functions of
`ω`, every hypothesis is read under the regular conditional law `ℙ_ω := condExpKernel P 𝒟 ω` at
`P`-almost every `ω`, and the conclusion is a limit law under `P`. The rate is `Ḡ_n³/n → 0`, as in
`clustershock_a_oneDimension`. -/

section Unconditional

open Multiway.SteinCluster

theorem clustershock_a_oneDimension_unconditional
    {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (g : ∀ n, Ω → O n → L n) (sc : ℕ → Ω → ℝ) (ve : ∀ n, Ω → O n → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω => omegaOf (g n ω) (sc n ω) (ve n ω) o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (s2 : ℝ) (hs2 : 0 < s2) (θ : ℝ) (hθ : 0 < θ)
    (nObs : ℕ → Ω → ℝ) (Gb : ℕ → Ω → ℕ)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1)
    (hWm : ∀ n, Measurable fun y => b ⬝ᵥ
      ((sqrtPD (restrictedVar (Xt n y) (omegaOf (g n y) (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n))))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ g n ω o = g n ω o')
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hsc : ∀ᵐ ω ∂P, ∀ n, 0 ≤ sc n ω)
    (hve : ∀ᵐ ω ∂P, ∀ n o, s2 ≤ ve n ω o)
    (hOm : ∀ᵐ ω ∂P, ∀ n o o', ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω)
      = omegaOf (g n ω) (sc n ω) (ve n ω) o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hnObs : ∀ᵐ ω ∂P, ∀ n, 0 < nObs n ω)
    (hdesign : ∀ᵐ ω ∂P, ∀ n, (θ * nObs n ω) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hGb1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Gb n ω)
    (hGb : ∀ᵐ ω ∂P, ∀ n γ, (cluster (g n ω) γ).card ≤ Gb n ω)
    (hGrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) ^ 3 / nObs n ω) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y) (omegaOf (g n y) (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  refine cltcluster_a_oneDimension_betaJM_unconditional h𝒟 P Xt
    (fun n ω => omegaOf (g n ω) (sc n ω) (ve n ω)) Rn ν bhat β g hXtD hOmD hscore
    (fun n ω => s2 * (θ * nObs n ω)) Gb B Cnu hB0 hCnu0 hnu b hb hWm hdep hA ?_ ?_ hOm hmean
    hB hGb ?_
  · filter_upwards [hnObs] with ω hω n
    exact mul_pos hs2 (mul_pos hθ (hω n))
  · filter_upwards [hsc, hve, hdesign] with ω hscω hveω hdesω n
    have hfloorOm : s2 • (1 : Matrix (O n) (O n) ℝ)
        ≤ omegaOf (g n ω) (sc n ω) (ve n ω) :=
      smul_one_le_omegaOf (hscω n) (hveω n)
    have h1 : s2 • ((θ * nObs n ω) • (1 : Matrix K K ℝ)) ≤ s2 • ((Xt n ω)ᵀ * Xt n ω) :=
      Multiway.loewner_smul_le_smul hs2.le (hdesω n)
    rw [smul_smul] at h1
    exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj hfloorOm (Xt n ω))
  · filter_upwards [hnObs, hGb1, hGrate] with ω hnω hG1ω hGrω
    have hbound : ∀ n, (Gb n ω : ℝ) * (B * Cnu / Real.sqrt (s2 * (θ * nObs n ω)))
        ≤ (B * Cnu / Real.sqrt (s2 * θ)) * Real.sqrt ((Gb n ω : ℝ) ^ 3 / nObs n ω) := by
      intro n
      have hassoc : s2 * (θ * nObs n ω) = (s2 * θ) * nObs n ω := by ring
      rw [hassoc]
      exact rate_le_sqrt_cube hB0 hCnu0 (by positivity) (hnω n)
        (by exact_mod_cast hG1ω n)
    have hsqrt : Tendsto (fun n => Real.sqrt ((Gb n ω : ℝ) ^ 3 / nObs n ω)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hGrω
      rw [Real.sqrt_zero] at h
      exact h
    have hlim : Tendsto (fun n => (B * Cnu / Real.sqrt (s2 * θ)) *
        Real.sqrt ((Gb n ω : ℝ) ^ 3 / nObs n ω)) atTop (𝓝 0) := by
      have h2 := hsqrt.const_mul (B * Cnu / Real.sqrt (s2 * θ))
      rw [mul_zero] at h2
      exact h2
    refine squeeze_zero (fun n => ?_) hbound hlim
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg hB0 hCnu0) (Real.sqrt_nonneg _))

end Unconditional

/-! ### Vacuity witness for `clustershock_a_oneDimension_unconditional`

The witness lives on the single space `Bool × ((ℕ × ℕ) → Bool)` of
`SteinCluster.FrozenDesignWitness`. At index `n` there are `n+1` clusters of two observations;
cluster `γ` reads shock coin `(n, 3γ)` and observation `(γ, k)` reads coin `(n, 3γ+1+k)`. The single
regressor is `x̃_o = ±1`, with sign read off the design coin, so the design is random and
`𝒟`-measurable, and the within-cluster covariance under `ℙ_ω` is `1`. -/

section FrozenShockWitness

namespace FrozenShockWitness

open Multiway.SteinCluster.FrozenDesignWitness

/-- The cluster shock of cluster `γ` at index `n` reads coin `(n, 3γ)`. -/
def csIdx (n : ℕ) (γ : Fin (n + 1)) : ℕ × ℕ := (n, 3 * γ.val)

/-- The idiosyncratic disturbance of `o = (γ,k)` at index `n` reads coin `(n, 3γ + 1 + k)`. -/
def esIdx (n : ℕ) (o : WsO n) : ℕ × ℕ := (n, 3 * o.1.val + 1 + o.2.val)

theorem csIdx_injective (n : ℕ) : Function.Injective (csIdx n) := by
  intro a c h
  have h1 := congrArg Prod.snd h
  simp only [csIdx] at h1
  exact Fin.ext (by omega)

theorem esIdx_injective (n : ℕ) : Function.Injective (esIdx n) := by
  intro a c h
  have h1 := congrArg Prod.snd h
  simp only [esIdx] at h1
  have ha := a.2.isLt
  have hc := c.2.isLt
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem csIdx_ne_esIdx (n : ℕ) (γ : Fin (n + 1)) (o : WsO n) : csIdx n γ ≠ esIdx n o := by
  intro h
  have h1 := congrArg Prod.snd h
  simp only [csIdx, esIdx] at h1
  have := o.2.isLt
  omega

/-- `ν_o = c_{g(o)} + ε_o` on the disturbance coordinate of the product space. -/
noncomputable def csNu (n : ℕ) (o : WsO n) (z : Cw) : ℝ :=
  coinSign (csIdx n o.1) z + coinSign (esIdx n o) z

/-- The same, on the whole space. -/
noncomputable def cuNu (n : ℕ) (o : WsO n) (y : Aw) : ℝ := csNu n o y.2

theorem meas_csNu (n : ℕ) (o : WsO n) : Measurable (csNu n o) :=
  (meas_coinSign _).add (meas_coinSign _)

theorem meas_cuNu (n : ℕ) (o : WsO n) : Measurable (cuNu n o) :=
  (meas_csNu n o).comp measurable_snd

theorem abs_csNu_le (n : ℕ) (o : WsO n) (z : Cw) : |csNu n o z| ≤ 2 := by
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_coinSign_le (csIdx n o.1) z
  have h2 := abs_coinSign_le (esIdx n o) z
  linarith

/-- The coins the observations in `A` read. -/
def csIdxSet (n : ℕ) (A : Finset (WsO n)) : Finset (ℕ × ℕ) :=
  A.image (fun o => csIdx n o.1) ∪ A.image (esIdx n)

theorem csIdx_mem_csIdxSet {n : ℕ} {A : Finset (WsO n)} {o : WsO n} (ho : o ∈ A) :
    csIdx n o.1 ∈ csIdxSet n A :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ ho)

theorem esIdx_mem_csIdxSet {n : ℕ} {A : Finset (WsO n)} {o : WsO n} (ho : o ∈ A) :
    esIdx n o ∈ csIdxSet n A :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ ho)

theorem csIdxSet_disjoint {n : ℕ} {A Bs : Finset (WsO n)}
    (hsep : ∀ a ∈ A, ∀ c ∈ Bs, ¬ (a.1 = c.1)) : Disjoint (csIdxSet n A) (csIdxSet n Bs) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  simp only [csIdxSet, Finset.mem_union, Finset.mem_image] at hxA hxB
  rcases hxA with ⟨a, ha, hax⟩ | ⟨a, ha, hax⟩ <;> rcases hxB with ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
  · exact hsep a ha c hc (csIdx_injective n (hax.trans hcx.symm))
  · exact csIdx_ne_esIdx n a.1 c (hax.trans hcx.symm)
  · exact csIdx_ne_esIdx n c.1 a (hcx.trans hax.symm)
  · have hac : a = c := esIdx_injective n (hax.trans hcx.symm)
    exact hsep a ha c hc (by rw [hac])

/-- The map that rebuilds `(ν_o)_{o∈A}` out of the shock coordinates indexed by `S`. -/
noncomputable def csRebuild (n : ℕ) (A : Finset (WsO n)) (S : Finset (ℕ × ℕ))
    (t : ↥S → ℝ) (o : ↥A) : ℝ :=
  (if h : csIdx n (o : WsO n).1 ∈ S then t ⟨csIdx n (o : WsO n).1, h⟩ else 0)
  + (if h : esIdx n (o : WsO n) ∈ S then t ⟨esIdx n (o : WsO n), h⟩ else 0)

theorem measurable_csRebuild (n : ℕ) (A : Finset (WsO n)) (S : Finset (ℕ × ℕ)) :
    Measurable (csRebuild n A S) := by
  refine Measurable.of_eval fun o => ?_
  simp only [csRebuild]
  refine Measurable.add ?_ ?_
  · by_cases h : csIdx n (o : WsO n).1 ∈ S
    · simp only [dite_eq_left h]
      exact measurable_pi_apply _
    · simp only [dite_eq_right h]
      exact measurable_const
  · by_cases h : esIdx n (o : WsO n) ∈ S
    · simp only [dite_eq_left h]
      exact measurable_pi_apply _
    · simp only [dite_eq_right h]
      exact measurable_const

theorem csRebuild_comp (n : ℕ) (A : Finset (WsO n)) :
    csRebuild n A (csIdxSet n A)
        ∘ (fun z (i : ↥(csIdxSet n A)) => coinSign (i : ℕ × ℕ) z)
      = fun z => fun o : ↥A => csNu n (o : WsO n) z := by
  funext z o
  simp only [Function.comp_apply, csRebuild, csNu]
  rw [dite_eq_left (csIdx_mem_csIdxSet o.2), dite_eq_left (esIdx_mem_csIdxSet o.2)]

/-- The sharing graph of the cluster-shock model is a dependency graph under `ℙ_ω`. -/
noncomputable def cuDep {μ : Measure Aw} [IsProbabilityMeasure μ]
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1) (n : ℕ) :
    DepGraph (cuNu n) μ where
  G := fun o o' => o.1 = o'.1
  decG := fun _ _ => inferInstance
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  meas := meas_cuNu n
  indep := by
    intro A Bs hsep
    have h0 := indep_coinSign.indepFun_finset (csIdxSet n A) (csIdxSet n Bs)
      (csIdxSet_disjoint hsep) meas_coinSign
    have key := h0.comp (measurable_csRebuild n A (csIdxSet n A))
      (measurable_csRebuild n Bs (csIdxSet n Bs))
    rw [csRebuild_comp, csRebuild_comp] at key
    exact indepFun_of_snd (F := fun z : Cw => fun o : ↥A => csNu n (o : WsO n) z)
      (G := fun z : Cw => fun o : ↥Bs => csNu n (o : WsO n) z) hmap
      (Measurable.of_eval fun o : ↥A => meas_csNu n (o : WsO n))
      (Measurable.of_eval fun o : ↥Bs => meas_csNu n (o : WsO n)) key

theorem integral_four_P1 (f1 f2 f3 f4 : Cw → ℝ)
    (h1 : Integrable f1 P1) (h2 : Integrable f2 P1)
    (h3 : Integrable f3 P1) (h4 : Integrable f4 P1) :
    ∫ z, (f1 z + f2 z + f3 z + f4 z) ∂P1
      = ∫ z, f1 z ∂P1 + ∫ z, f2 z ∂P1 + ∫ z, f3 z ∂P1 + ∫ z, f4 z ∂P1 := by
  have h12 : Integrable (fun z => f1 z + f2 z) P1 := h1.add h2
  have h123 : Integrable (fun z => f1 z + f2 z + f3 z) P1 := h12.add h3
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]

/-- **The second moments of the cluster-shock disturbance**: `2` on the diagonal, `1` within a
cluster, `0` across clusters. -/
theorem integral_csNu_mul (n : ℕ) (o o' : WsO n) :
    ∫ z, csNu n o z * csNu n o' z ∂P1
      = (if o.1 = o'.1 then (1 : ℝ) else 0) + (if o = o' then 1 else 0) := by
  have hexp : (fun z => csNu n o z * csNu n o' z)
      = fun z => coinSign (csIdx n o.1) z * coinSign (csIdx n o'.1) z
          + coinSign (csIdx n o.1) z * coinSign (esIdx n o') z
          + coinSign (esIdx n o) z * coinSign (csIdx n o'.1) z
          + coinSign (esIdx n o) z * coinSign (esIdx n o') z := by
    funext z
    simp only [csNu]
    ring
  rw [hexp, integral_four_P1 _ _ _ _ (integrable_coinSign_mul _ _)
      (integrable_coinSign_mul _ _) (integrable_coinSign_mul _ _) (integrable_coinSign_mul _ _),
    integral_coinSign_mul, integral_coinSign_mul, integral_coinSign_mul, integral_coinSign_mul]
  have hc1 : (csIdx n o.1 = csIdx n o'.1) ↔ (o.1 = o'.1) :=
    ⟨fun h => csIdx_injective n h, fun h => by rw [h]⟩
  have he1 : (esIdx n o = esIdx n o') ↔ (o = o') :=
    ⟨fun h => esIdx_injective n h, fun h => by rw [h]⟩
  rw [ite_eq_right (csIdx_ne_esIdx n o.1 o'), ite_eq_right (Ne.symm (csIdx_ne_esIdx n o'.1 o))]
  simp only [hc1, he1, add_zero]

theorem integral_csNu (n : ℕ) (o : WsO n) : ∫ z, csNu n o z ∂P1 = 0 := by
  simp only [csNu]
  rw [integral_add (integrable_coinSign _) (integrable_coinSign _), integral_coinSign,
    integral_coinSign, add_zero]

/-- The two members of a cluster have covariance `1`. -/
theorem integral_csNu_within (n : ℕ) (γ : Fin (n + 1)) :
    ∫ z, csNu n (γ, 0) z * csNu n (γ, 1) z ∂P1 = 1 := by
  rw [integral_csNu_mul]
  norm_num


/-- The design at index `n`: the all-ones regressor, with the sign of the design coin. -/
noncomputable def cXt (n : ℕ) (y : Aw) : Matrix (WsO n) (Fin 1) ℝ := sgnA y • wsXt n

noncomputable def cBhat (n : ℕ) (y : Aw) : Fin 1 → ℝ :=
  ((cXt n y)ᵀ * cXt n y)⁻¹ *ᵥ ((cXt n y)ᵀ *ᵥ (fun o => cuNu n o y))

theorem c_hXtD (n : ℕ) (o : WsO n) (k : Fin 1) :
    Measurable[Dw] fun y => cXt n y o k := by
  have : (fun y : Aw => cXt n y o k) = fun y => sgnA y * 1 := rfl
  rw [this]
  exact meas_sgnA.mul_const 1

theorem integral_csNu_mul_omegaOf (n : ℕ) (o o' : WsO n) :
    ∫ z, csNu n o z * csNu n o' z ∂P1
      = omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1) o o' := by
  rw [integral_csNu_mul, omegaOf_apply]

theorem c_hPD (n : ℕ) :
    (scoreVar (wsXt n) (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))).PosDef := by
  refine Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one
    (show (0 : ℝ) < ((n : ℝ) + 1) * 2 by positivity)) ?_
  have hfloorOm : (1 : ℝ) • (1 : Matrix (WsO n) (WsO n) ℝ)
      ≤ omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1) :=
    smul_one_le_omegaOf zero_le_one (fun _ => le_refl 1)
  have h2 := Multiway.Sharing.smul_transpose_mul_self_le_conj hfloorOm (wsXt n)
  rw [one_smul, wsXt_transpose_mul_self] at h2
  exact h2

theorem c_statistic (n : ℕ) :
    (fun y : Aw => wb ⬝ᵥ
        ((sqrtPD (restrictedVar (cXt n y)
            (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
            (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (cBhat n y - (0 : Fin 1 → ℝ)))))
      = fun y => sgnA y *
          depSum (scoreArray (wsXt n)
            (steinWeight (wsXt n) (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
              (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (cuNu n)) y := by
  funext y
  rw [show cBhat n y - (0 : Fin 1 → ℝ)
      = ((cXt n y)ᵀ * cXt n y)⁻¹ *ᵥ ((cXt n y)ᵀ *ᵥ (fun o => cuNu n o y)) from sub_zero _,
    dotProduct_standardized_eq_depSum,
    show cXt n y = sgnA y • wsXt n from rfl,
    steinWeight_smul (sgnA_mul y), depSum_scoreArray_smul]

theorem c_hWm (n : ℕ) : Measurable fun y : Aw => wb ⬝ᵥ
    ((sqrtPD (restrictedVar (cXt n y)
        (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (cBhat n y - (0 : Fin 1 → ℝ)))) := by
  rw [c_statistic n]
  exact (meas_sgnA.mono Dw_le le_rfl).mul
    (Finset.measurable_sum _ fun o _ => (meas_cuNu n o).const_mul _)

/-- The total conditional variance is `1` at every `n`. -/
theorem c_total_variance (n : ℕ) :
    ∫ z, (depSum (scoreArray (wsXt n)
      (steinWeight (wsXt n) (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (csNu n)) z) ^ 2 ∂P1 = 1 :=
  integral_depSum_scoreArray_sq_eq_one (c_hPD n) (wsXt_scoreMap_injective n)
    (meas_csNu n) (fun o z => abs_csNu_le n o z) (integral_csNu_mul_omegaOf n) wb_dot

theorem c_total_variance_cond :
    ∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (wsXt n)
        (steinWeight (wsXt n) (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (cuNu n)) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n
  have hmeas : Measurable fun z : Cw => (depSum (scoreArray (wsXt n)
      (steinWeight (wsXt n) (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (csNu n)) z) ^ 2 :=
    (Finset.measurable_sum _ fun o _ => (meas_csNu n o).const_mul _).pow_const 2
  exact (integral_of_snd hω hmeas).trans (c_total_variance n)

/-- The within-cluster covariance is `1` under `ℙ_ω`. -/
theorem c_within_cond :
    ∀ᵐ ω ∂Pw, ∀ (n : ℕ) (γ : Fin (n + 1)),
      ∫ y, cuNu n (γ, 0) y * cuNu n (γ, 1) y ∂(condExpKernel Pw Dw ω) = 1 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n γ
  exact (integral_of_snd hω ((meas_csNu n (γ, 0)).mul (meas_csNu n (γ, 1)))).trans
    (integral_csNu_within n γ)

theorem c_hGrate : Tendsto (fun n : ℕ => (((2 : ℕ) : ℝ)) ^ 3 / (((n : ℝ) + 1) * 2))
    atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * 2) atTop atTop := by
    refine Filter.Tendsto.atTop_mul_const (by norm_num) ?_
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa using (tendsto_const_nhds (x := (((2 : ℕ) : ℝ)) ^ 3) (f := atTop (α := ℕ))).div_atTop hd

/-- Vacuity witness for `clustershock_a_oneDimension_unconditional`. -/
theorem clustershock_a_oneDimension_unconditional_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), cXt n y = (if y.1 then (1 : ℝ) else -1) • wsXt n)
    ∧ (∀ (n : ℕ) (γ : Fin (n + 1)), ∫ z, csNu n (γ, 0) z * csNu n (γ, 1) z ∂P1 = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ (n : ℕ) (γ : Fin (n + 1)),
        ∫ y, cuNu n (γ, 0) y * cuNu n (γ, 1) y ∂(condExpKernel Pw Dw ω) = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (wsXt n)
        (steinWeight (wsXt n) (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (cuNu n)) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => wb ⬝ᵥ
          ((sqrtPD (restrictedVar (cXt n y)
              (omegaOf (Prod.fst : WsO n → Fin (n + 1)) 1 (fun _ => 1))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (cBhat n y - (0 : Fin 1 → ℝ)))))
        atTop (id : ℝ → ℝ) (fun _ => Pw) (gaussianReal 0 1) := by
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ => rfl,
    integral_csNu_within, c_within_cond, c_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine clustershock_a_oneDimension_unconditional
    (O := fun n => WsO n) (L := fun n => Fin (n + 1))
    Dw_le Pw cXt (fun _ => 1) cuNu cBhat (fun _ => 0)
    (fun _ _ => Prod.fst) (fun _ _ => 1) (fun _ _ _ => 1)
    c_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    1 zero_lt_one 1 zero_lt_one (fun n _ => ((n : ℝ) + 1) * 2) (fun _ _ => 2)
    1 2 zero_le_one (by norm_num) (fun n o y => abs_csNu_le n o y.2) wb wb_dot c_hWm
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [map_snd_condExpKernel] with ω hω
    exact ⟨fun n => cuDep hω n, fun _ _ _ => Iff.rfl⟩
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show cXt n ω = sgnA ω • wsXt n from rfl, scoreMap_smul (sgnA_mul ω)]
    exact wsXt_scoreMap_injective n
  · exact Filter.Eventually.of_forall fun _ _ => zero_le_one
  · exact Filter.Eventually.of_forall fun _ _ _ => le_refl 1
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o o'
    exact (integral_of_snd hω ((meas_csNu n o).mul (meas_csNu n o'))).trans
      (integral_csNu_mul_omegaOf n o o')
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o
    exact (integral_of_snd hω (meas_csNu n o)).trans (integral_csNu n o)
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun k => cXt n ω o k) ⬝ᵥ (fun k => cXt n ω o k) = 1 := by
      simp [cXt, wsXt, dotProduct, sgnA_mul ω]
    rw [h]
    norm_num
  · exact Filter.Eventually.of_forall fun _ n => by positivity
  · refine Filter.Eventually.of_forall fun ω n => ?_
    have h : (cXt n ω)ᵀ * cXt n ω = (((n : ℝ) + 1) * 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [show cXt n ω = sgnA ω • wsXt n from rfl, gram_smul (sgnA_mul ω),
        wsXt_transpose_mul_self]
    rw [h]
    exact le_of_eq (by rw [one_mul])
  · exact Filter.Eventually.of_forall fun _ _ => one_le_two
  · exact Filter.Eventually.of_forall fun _ n γ => wsCluster_card n γ
  · exact Filter.Eventually.of_forall fun _ => c_hGrate

end FrozenShockWitness

end FrozenShockWitness

/-! ## General `J`

The asymptotic content is `Multiway.SteinCluster.cltcluster_a_general_betaJM`. This section
supplies the covariance matrix at general `J` (`Multiway.Sharing.clusterOmega`), the degree bound
`D_n + 1 ≤ JḠ_n` of the union sharing graph, and the rate bridge from `Ḡ_n⁴/n → 0` to the Stein
rate. -/

/-! ### The covariance matrix and the degree of the union sharing graph -/

section GeneralOmega

variable {O D L : Type*} [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L]

omit [Fintype O] [DecidableEq O] [DecidableEq D] [DecidableEq L] in
/-- `o ∼_{\{j\}} o'` iff `c^{(j)}(o) = c^{(j)}(o')`. -/
theorem sameOn_singleton_iff {c : D → O → L} {j : D} {o o' : O} :
    Multiway.SameOn c {j} o o' ↔ c j o = c j o' :=
  ⟨fun h => h j (Finset.mem_singleton_self j), fun h k hk => by
    rw [Finset.mem_singleton] at hk; subst hk; exact h⟩

omit [Fintype O] in
/-- `omegaOf` is `Multiway.Sharing.clusterOmega` at a one-element dimension index. -/
theorem omegaOf_eq_clusterOmega (g : O → L) (scv : ℝ) (ve : O → ℝ) :
    omegaOf g scv ve
      = Multiway.Sharing.clusterOmega (fun _ : Fin 1 => g) Finset.univ (fun _ => scv) ve := rfl

omit [DecidableEq D] in
/-- The closed neighbourhood of `o` in the union sharing graph has at most `J·Ḡ_n` elements. -/
theorem card_closedNbhd_le_mul {c : D → O → L} {dims : Finset D} {Gb : ℕ}
    (hGb : ∀ j ∈ dims, ∀ γ : L, (cluster (c j) γ).card ≤ Gb) (o : O) :
    (Multiway.Sharing.closedNbhd c dims o).card ≤ dims.card * Gb := by
  classical
  have hsub : Multiway.Sharing.closedNbhd c dims o
      ⊆ dims.biUnion (fun j => cluster (c j) (c j o)) := by
    intro o' ho'
    rw [Multiway.Sharing.mem_closedNbhd] at ho'
    obtain ⟨j, hj, hcj⟩ := ho'
    exact Finset.mem_biUnion.mpr ⟨j, hj, mem_cluster.mpr hcj.symm⟩
  calc (Multiway.Sharing.closedNbhd c dims o).card
      ≤ (dims.biUnion (fun j => cluster (c j) (c j o))).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ dims, (cluster (c j) (c j o)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ dims, Gb := Finset.sum_le_sum (fun j hj => hGb j hj _)
    _ = dims.card * Gb := by rw [Finset.sum_const, smul_eq_mul]

end GeneralOmega

/-! ### The rate bridge: from `Ḡ_n⁴/n → 0` to `(n/D_n)^{1/3}δ_n → 0`

With `λ_min(Ω_n) ≥ c·n` and `D_n ≤ JḠ_n`,
`steinRate³ = n⁴D_n⁸/(cn)⁶ ≤ (J⁸/c⁶)(Ḡ_n⁴/n)²`, and the cube root is taken by an `ε`-argument. -/

section RateBridge

/-- If `x_n ≥ 0` and `x_n³ → 0` then `x_n → 0`. -/
theorem tendsto_zero_of_pow_three {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : Tendsto (fun n => f n ^ 3) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε ^ 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg (hf n) 3)] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)]
  rcases lt_or_ge (f n) ε with h2 | h2
  · exact h2
  · exact absurd h1 (not_lt.mpr (pow_le_pow_left₀ hε.le h2 3))

/-- `((n/D_n)^{1/3}δ_n)³ = n⁴D_n⁸/λ_min(Ω_n)⁶`. -/
theorem steinRate_pow_three {N D : ℕ} (hD1 : 1 ≤ D) {lmin : ℝ} (hl : 0 < lmin) :
    steinRate N D lmin ^ 3 = (N : ℝ) ^ 4 * (D : ℝ) ^ 8 / lmin ^ 6 := by
  have hD : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hcube : (((N : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3)) ^ 3 = (N : ℝ) / (D : ℝ) := by
    rw [← Real.rpow_natCast (((N : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3)) 3,
      ← Real.rpow_mul (by positivity)]
    norm_num
  unfold steinRate accumRate
  rw [mul_pow, hcube]
  field_simp

/-- Under `λ_min(Ω_n) ≥ c·n` and `D_n ≤ JḠ_n`, `((n/D_n)^{1/3}δ_n)³ ≤ (J⁸/c⁶)·(Ḡ_n⁴/n)²`. -/
theorem steinRate_pow_three_le {N D Gb Jc : ℕ} {c : ℝ} (hc : 0 < c) (hN : 1 ≤ N) (hD1 : 1 ≤ D)
    (hDJG : D ≤ Jc * Gb) :
    steinRate N D (c * (N : ℝ)) ^ 3 ≤ ((Jc : ℝ) ^ 8 / c ^ 6) * ((Gb : ℝ) ^ 4 / (N : ℝ)) ^ 2 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hl : (0 : ℝ) < c * (N : ℝ) := mul_pos hc hNR
  have hDR : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hDJ : (D : ℝ) ≤ (Jc : ℝ) * (Gb : ℝ) := by exact_mod_cast hDJG
  have h8 : (D : ℝ) ^ 8 ≤ ((Jc : ℝ) * (Gb : ℝ)) ^ 8 := pow_le_pow_left₀ hDR hDJ 8
  rw [steinRate_pow_three hD1 hl]
  have hrw : (N : ℝ) ^ 4 * (D : ℝ) ^ 8 / (c * (N : ℝ)) ^ 6
      = (D : ℝ) ^ 8 / (c ^ 6 * (N : ℝ) ^ 2) := by
    field_simp
  have hrw2 : ((Jc : ℝ) ^ 8 / c ^ 6) * ((Gb : ℝ) ^ 4 / (N : ℝ)) ^ 2
      = ((Jc : ℝ) * (Gb : ℝ)) ^ 8 / (c ^ 6 * (N : ℝ) ^ 2) := by
    field_simp
  rw [hrw, hrw2]
  exact div_le_div_of_nonneg_right h8 (by positivity)

/-- `Ḡ_n⁴/n → 0` implies the rate condition of `cltcluster_a_general_betaJM`. -/
theorem tendsto_steinRate_of_cluster_size {N D Gb : ℕ → ℕ} {Jc : ℕ} {c : ℝ} (hc : 0 < c)
    (hN : ∀ n, 1 ≤ N n) (hD1 : ∀ n, 1 ≤ D n) (hDJG : ∀ n, D n ≤ Jc * Gb n)
    (hG : Tendsto (fun n => (Gb n : ℝ) ^ 4 / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => steinRate (N n) (D n) (c * (N n : ℝ))) atTop (𝓝 0) := by
  refine tendsto_zero_of_pow_three (fun n => steinRate_nonneg _ _ _) ?_
  refine squeeze_zero (fun n => pow_nonneg (steinRate_nonneg _ _ _) 3)
    (fun n => steinRate_pow_three_le hc (hN n) (hD1 n) (hDJG n)) ?_
  have h2 : Tendsto (fun n => ((Gb n : ℝ) ^ 4 / (N n : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using hG.pow 2
  simpa using h2.const_mul ((Jc : ℝ) ^ 8 / c ^ 6)

end RateBridge

/-! ### The corollary at general `J` -/

/-- **Corollary SM.D.3, bounded shocks, general `J`.** Under the cluster-shock model with
`J = dims.card` clustering dimensions, bounded shocks, a variance floor `Var(ε_o ∣ 𝒟) ≥ σ̲² > 0`
and `Ḡ_n⁴/n → 0`, the standardized restriction `b'𝒱_n^{-1/2}𝓡_n(β̂_JM − β)` is asymptotically
standard normal. -/
theorem clustershock_a_general
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Dm : Type*} [DecidableEq Dm]
    {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n) dims o o')
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (sc : ℕ → Dm → ℝ) (ve : ∀ n, O n → ℝ) (hsc : ∀ n, ∀ j ∈ dims, 0 ≤ sc n j)
    (s2 : ℝ) (hs2 : 0 < s2) (hve : ∀ n o, s2 ≤ ve n o)
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n)
      = Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n) o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hnu : ∀ n o ω, |ν n o ω| ≤ Cnu)
    (θ : ℝ) (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (hGrate : Tendsto (fun n => (Gb n : ℝ) ^ 4 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n)
              (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  -- `Ω ⪰ σ̲²I_n`
  have hfloorOm : ∀ n, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n) :=
    fun n => Multiway.Sharing.smul_one_le_clusterOmega (hsc n) (hve n)
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  -- `Ω_n = X̃'ΩX̃ ⪰ σ̲²X̃'X̃ ⪰ σ̲²θnI`
  have hfloorK : ∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n) (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) := by
    intro n
    have h1 : s2 • ((θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ))
        ≤ s2 • ((Xt n)ᵀ * Xt n) := Multiway.loewner_smul_le_smul hs2.le (hdesign n)
    rw [smul_smul, ← mul_assoc] at h1
    exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj (hfloorOm n) (Xt n))
  have hnbhd : ∀ n o, (Dv n).nbhd o = Multiway.Sharing.closedNbhd (c n) dims o := by
    intro n o
    ext o'
    rw [DepGraph.mem_nbhd_iff, Multiway.Sharing.mem_closedNbhd]
    exact hshare n o o'
  -- `D_n := min{JḠ_n, n}`
  set Dn : ℕ → ℕ := fun n => min (dims.card * Gb n) (Fintype.card (O n)) with hDndef
  have hdegF : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n := by
    intro n o
    refine le_min ?_ ?_
    · rw [hnbhd n o]; exact card_closedNbhd_le_mul (hGb n) o
    · exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  -- `D_n ≥ 1`
  have hDn1 : ∀ n, 1 ≤ Dn n := by
    intro n
    obtain ⟨o⟩ := hne n
    refine le_trans ?_ (hdegF n o)
    exact Finset.card_pos.mpr ⟨o, (Dv n).self_mem_nbhd o⟩
  refine cltcluster_a_general_betaJM μ Xt
    (fun n => Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) Rn ν bhat β Dv hscore hA
    (fun n => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n => mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n)) hfloorK hOm hmean
    B Cnu hB0 hCnu0 hB hnu Dn hDn1 (fun n => min_le_right _ _)
    (fun n o => le_trans (hdegF n o) (Nat.le_succ _)) ?_ b hb s
  exact tendsto_steinRate_of_cluster_size (mul_pos hs2 hθ) (fun n => hcard n)
    hDn1 (fun n => min_le_left _ _) hGrate

/-! ### A disturbance that is a sum of independent fair shocks

Witness infrastructure: `ν_o = ∑_k s_{idx(o,k)}` over an arbitrary component index, with its
moments and its dependency graph. -/

section ShockSum

open Multiway.Multilinear

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m : ℕ}

/-- `ν_o := ∑_k s_{idx(o,k)}`, where `idx o k` is the coin that component `k` of `o` reads. -/
noncomputable def shockSum (idx : O → κ → Fin m) (o : O) (ω : Fin m → Bool) : ℝ :=
  ∑ k : κ, sign2 (idx o k) ω

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem measurable_shockSum (idx : O → κ → Fin m) (o : O) : Measurable (shockSum idx o) :=
  Finset.measurable_sum _ fun _ _ => measurable_sign2 _

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
/-- `|ν_o|` is at most the number of components. -/
theorem abs_shockSum_le (idx : O → κ → Fin m) (o : O) (ω : Fin m → Bool) :
    |shockSum idx o ω| ≤ (Fintype.card κ : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (fun k _ => Multiway.SteinCluster.abs_sign2_le' (idx o k) ω)) ?_
  simp [Finset.card_univ]

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
/-- Every component has mean zero, so `ν` does. -/
theorem integral_shockSum (idx : O → κ → Fin m) (o : O) :
    ∫ ω, shockSum idx o ω ∂(coins m) = 0 := by
  unfold shockSum
  rw [integral_finsetSum _ (fun k _ => integrable_sign2 _)]
  simp [integral_sign2]

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
/-- `E[ν_oν_{o'}]` counts the components at which `o` and `o'` read the same coin, provided two
components of different kind never read the same coin. -/
theorem integral_shockSum_mul {idx : O → κ → Fin m}
    (hinj : ∀ o o' : O, ∀ k k' : κ, idx o k = idx o' k' → k = k') (o o' : O) :
    ∫ ω, shockSum idx o ω * shockSum idx o' ω ∂(coins m)
      = ∑ k : κ, (if idx o k = idx o' k then (1 : ℝ) else 0) := by
  have hexp : (fun ω => shockSum idx o ω * shockSum idx o' ω)
      = fun ω => ∑ k : κ, ∑ k' : κ, sign2 (idx o k) ω * sign2 (idx o' k') ω := by
    funext ω
    simp only [shockSum]
    rw [Finset.sum_mul_sum]
  rw [hexp, integral_finsetSum _
    (fun k _ => integrable_finsetSum _ (fun k' _ => integrable_sign2_mul _ _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ (fun k' _ => integrable_sign2_mul _ _)]
  have hsingle : (∑ k' : κ, ∫ ω, sign2 (idx o k) ω * sign2 (idx o' k') ω ∂(coins m))
      = ∫ ω, sign2 (idx o k) ω * sign2 (idx o' k) ω ∂(coins m) := by
    refine Finset.sum_eq_single_of_mem k (Finset.mem_univ k) ?_
    intro k' _ hk'
    rw [Multiway.SteinCluster.integral_sign2_mul]
    exact ite_eq_right fun heq => hk' (hinj o o' k k' heq).symm
  rw [hsingle, Multiway.SteinCluster.integral_sign2_mul]

/-- The coins the observations in `A` read. -/
def shockIdxSet (idx : O → κ → Fin m) (A : Finset O) : Finset (Fin m) :=
  A.biUnion fun o => Finset.univ.image (idx o)

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem mem_shockIdxSet {idx : O → κ → Fin m} {A : Finset O} {o : O} (ho : o ∈ A) (k : κ) :
    idx o k ∈ shockIdxSet idx A :=
  Finset.mem_biUnion.mpr ⟨o, ho, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩

/-- The map that rebuilds `(ν_o)_{o∈A}` out of the shock coordinates indexed by `S`. -/
noncomputable def shockRebuild (idx : O → κ → Fin m) (A : Finset O) (S : Finset (Fin m))
    (t : ↥S → ℝ) (o : ↥A) : ℝ :=
  ∑ k : κ, (if h : idx (o : O) k ∈ S then t ⟨idx (o : O) k, h⟩ else 0)

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem measurable_shockRebuild (idx : O → κ → Fin m) (A : Finset O) (S : Finset (Fin m)) :
    Measurable (shockRebuild idx A S) := by
  refine Measurable.of_eval fun o => ?_
  simp only [shockRebuild]
  refine Finset.measurable_sum _ fun k _ => ?_
  by_cases h : idx (o : O) k ∈ S
  · simp only [dite_eq_left h]
    exact measurable_pi_apply _
  · simp only [dite_eq_right h]
    exact measurable_const

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem shockRebuild_comp (idx : O → κ → Fin m) (A : Finset O) :
    shockRebuild idx A (shockIdxSet idx A)
        ∘ (fun ω (i : ↥(shockIdxSet idx A)) => sign2 (i : Fin m) ω)
      = fun ω => fun o : ↥A => shockSum idx (o : O) ω := by
  funext ω o
  simp only [Function.comp_apply, shockRebuild, shockSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dite_eq_left (mem_shockIdxSet o.2 k)]

/-- Two non-adjacent blocks of observations are functions of disjoint collections of independent
shocks, so the graph is a dependency graph for `ν`. -/
noncomputable def shockDep (idx : O → κ → Fin m) (G : O → O → Prop) [DecidableRel G]
    (hrefl : ∀ o, G o o) (hsymm : ∀ o o', G o o' → G o' o)
    (hdisj : ∀ o o', ¬ G o o' → ∀ k k' : κ, idx o k ≠ idx o' k') :
    DepGraph (shockSum idx) (coins m) where
  G := G
  decG := inferInstance
  refl := hrefl
  symm := hsymm
  meas := measurable_shockSum idx
  indep := by
    intro A Bs hsep
    have hdisjoint : Disjoint (shockIdxSet idx A) (shockIdxSet idx Bs) := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      simp only [shockIdxSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
        true_and] at hxA hxB
      obtain ⟨a, ha, k, hk⟩ := hxA
      obtain ⟨d, hd, k', hk'⟩ := hxB
      exact hdisj a d (hsep a ha d hd) k k' (hk.trans hk'.symm)
    have h0 := (iIndepFun_sign2 m).indepFun_finset (shockIdxSet idx A) (shockIdxSet idx Bs)
      hdisjoint measurable_sign2
    have key := h0.comp (measurable_shockRebuild idx A (shockIdxSet idx A))
      (measurable_shockRebuild idx Bs (shockIdxSet idx Bs))
    rwa [shockRebuild_comp, shockRebuild_comp] at key

end ShockSum

/-! ### Vacuity witness at general `J`, on a design with `J = 2`

`n+3` observations, one regressor `x̃_o = 1`, `𝓡_n = I_1`, and two clustering dimensions
`g^{(1)}(o) = ⌊o/2⌋` and `g^{(2)}(o) = ⌊(o+1)/2⌋`. The disturbance is
`ν_o = c^{(1)}_{g₁(o)} + c^{(2)}_{g₂(o)} + ε_o` with independent fair signs, so `Ḡ_n = 2` and
`C_ν = 3`. The sharing relation is `|o − o'| ≤ 1`, which is not transitive, and `Ω` is not
diagonal. -/

section GeneralWitness

open Multiway.Multilinear

/-- The two maintained clustering maps of the witness: `g^{(1)}(o) = ⌊o/2⌋` and
`g^{(2)}(o) = ⌊(o+1)/2⌋`. -/
def wtC (n : ℕ) (j : Fin 2) (o : Fin (n + 3)) : Fin (n + 3) :=
  if j = 0 then ⟨o.val / 2, by have := o.isLt; omega⟩
  else ⟨(o.val + 1) / 2, by have := o.isLt; omega⟩

theorem wtC_val (n : ℕ) (j : Fin 2) (o : Fin (n + 3)) :
    (wtC n j o).val = if j = 0 then o.val / 2 else (o.val + 1) / 2 := by
  unfold wtC; by_cases h : j = 0 <;> simp [h]

/-- The label component `k` of `o` reads: its dimension-1 cluster at `k = 0`, its dimension-2
cluster at `k = 1`, and `o` itself at `k = 2` (the idiosyncratic disturbance). -/
def wtLab (n : ℕ) (o : Fin (n + 3)) (k : Fin 3) : ℕ :=
  if k = 0 then o.val / 2 else if k = 1 then (o.val + 1) / 2 else o.val

theorem wtLab_lt (n : ℕ) (o : Fin (n + 3)) (k : Fin 3) : wtLab n o k < n + 3 := by
  have := o.isLt
  unfold wtLab
  by_cases h0 : k = 0
  · rw [ite_eq_left h0]; omega
  · rw [ite_eq_right h0]
    by_cases h1 : k = 1
    · rw [ite_eq_left h1]; omega
    · rw [ite_eq_right h1]; omega

/-- Component `k` of observation `o` reads coin `3·label + k`, so the three kinds of shock never
collide. -/
def wtIdx (n : ℕ) (o : Fin (n + 3)) (k : Fin 3) : Fin (3 * (n + 3)) :=
  ⟨3 * wtLab n o k + k.val, by have h1 := wtLab_lt n o k; have h2 := k.isLt; omega⟩

/-- Two components of different kind never read the same coin. -/
theorem wtIdx_component (n : ℕ) (o o' : Fin (n + 3)) (k k' : Fin 3)
    (h : wtIdx n o k = wtIdx n o' k') : k = k' := by
  have h1 := congrArg Fin.val h
  simp only [wtIdx] at h1
  have h2 := k.isLt
  have h3 := k'.isLt
  exact Fin.ext (by omega)

theorem wtIdx_eq_iff (n : ℕ) (o o' : Fin (n + 3)) (k : Fin 3) :
    wtIdx n o k = wtIdx n o' k ↔ wtLab n o k = wtLab n o' k := by
  constructor
  · intro h
    have h1 := congrArg Fin.val h
    simp only [wtIdx] at h1
    omega
  · intro h
    refine Fin.ext ?_
    simp only [wtIdx, h]

theorem wtLab_eq_zero_iff (n : ℕ) (o o' : Fin (n + 3)) :
    wtLab n o 0 = wtLab n o' 0 ↔ wtC n 0 o = wtC n 0 o' := by
  rw [Fin.ext_iff, wtC_val, wtC_val, ite_eq_left rfl, ite_eq_left rfl]
  simp [wtLab]

theorem wtLab_eq_one_iff (n : ℕ) (o o' : Fin (n + 3)) :
    wtLab n o 1 = wtLab n o' 1 ↔ wtC n 1 o = wtC n 1 o' := by
  rw [Fin.ext_iff, wtC_val, wtC_val, ite_eq_right (by decide), ite_eq_right (by decide)]
  simp [wtLab]

theorem wtLab_eq_two_iff (n : ℕ) (o o' : Fin (n + 3)) :
    wtLab n o 2 = wtLab n o' 2 ↔ o = o' := by
  rw [Fin.ext_iff]
  simp [wtLab]

/-- `Ḡ_n = 2`: every cluster of either dimension has at most two members. -/
theorem wtCluster_card (n : ℕ) (j : Fin 2) (γ : Fin (n + 3)) :
    (cluster (wtC n j) γ).card ≤ 2 := by
  classical
  have hcard : (cluster (wtC n j) γ).card ≤ (Finset.range 2).card := by
    refine Finset.card_le_card_of_injOn (fun o => o.val % 2)
      (fun o _ => Finset.mem_range.mpr (Nat.mod_lt o.val (by norm_num))) ?_
    intro a ha b hb h
    simp only [Finset.mem_coe, mem_cluster] at ha hb
    have hav := congrArg Fin.val ha
    have hbv := congrArg Fin.val hb
    rw [wtC_val] at hav hbv
    simp only at h
    refine Fin.ext ?_
    by_cases hj : j = 0
    · rw [ite_eq_left hj] at hav hbv; omega
    · rw [ite_eq_right hj] at hav hbv; omega
  simpa using hcard

/-- The union sharing relation of the witness is `|o − o'| ≤ 1`. -/
theorem wtLinked_iff_pathG (n : ℕ) (o o' : Fin (n + 3)) :
    Multiway.Linked (wtC n) Finset.univ o o' ↔ pathG (n + 3) o o' := by
  rw [pathG_iff_two_dimensions]
  constructor
  · rintro ⟨j, -, hj⟩
    by_cases h0 : j = 0
    · subst h0
      exact Or.inl (by
        have := congrArg Fin.val hj
        rwa [wtC_val, wtC_val, ite_eq_left rfl, ite_eq_left rfl] at this)
    · refine Or.inr ?_
      have := congrArg Fin.val hj
      rwa [wtC_val, wtC_val, ite_eq_right h0, ite_eq_right h0] at this
  · rintro (h | h)
    · exact ⟨0, Finset.mem_univ 0, (wtLab_eq_zero_iff n o o').mp (by simpa [wtLab] using h)⟩
    · exact ⟨1, Finset.mem_univ 1, (wtLab_eq_one_iff n o o').mp (by simpa [wtLab] using h)⟩

/-- The sharing relation is not transitive: `0 ∼ 1` and `1 ∼ 2` while `0 ≁ 2`. -/
theorem wtLinked_not_transitive (n : ℕ) :
    ∃ a b c : Fin (n + 3), Multiway.Linked (wtC n) Finset.univ a b ∧
      Multiway.Linked (wtC n) Finset.univ b c ∧
      ¬ Multiway.Linked (wtC n) Finset.univ a c := by
  obtain ⟨a, b, c, h1, h2, h3⟩ := pathG_not_transitive n
  exact ⟨a, b, c, (wtLinked_iff_pathG n a b).mpr h1, (wtLinked_iff_pathG n b c).mpr h2,
    fun h => h3 ((wtLinked_iff_pathG n a c).mp h)⟩

/-- Non-adjacent observations read disjoint sets of coins. -/
theorem wtIdx_ne_of_not_linked (n : ℕ) (o o' : Fin (n + 3))
    (h : ¬ Multiway.Linked (wtC n) Finset.univ o o') (k k' : Fin 3) :
    wtIdx n o k ≠ wtIdx n o' k' := by
  intro heq
  have hkk := wtIdx_component n o o' k k' heq
  subst hkk
  have hlab := (wtIdx_eq_iff n o o' k).mp heq
  refine h ?_
  fin_cases k
  · exact ⟨0, Finset.mem_univ 0, (wtLab_eq_zero_iff n o o').mp hlab⟩
  · exact ⟨1, Finset.mem_univ 1, (wtLab_eq_one_iff n o o').mp hlab⟩
  · have hoo : o = o' := (wtLab_eq_two_iff n o o').mp hlab
    exact ⟨0, Finset.mem_univ 0, by rw [hoo]⟩

/-- The sharing graph of the witness design is a dependency graph for `ν`. -/
noncomputable def wtDep (n : ℕ) :
    DepGraph (shockSum (wtIdx n)) (coins (3 * (n + 3))) :=
  shockDep (wtIdx n) (Multiway.Linked (wtC n) Finset.univ)
    (fun _ => ⟨0, Finset.mem_univ 0, rfl⟩)
    (fun _ _ h => Multiway.Sharing.linked_symm h)
    (wtIdx_ne_of_not_linked n)

/-- The witness `Ω` is not diagonal: its entry at the members `0` and `1` of the cluster `{0,1}`
is `1`. -/
theorem wtOmega_offDiag (n : ℕ) :
    Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ)) (fun _ => 1)
        (⟨0, by omega⟩ : Fin (n + 3)) (⟨1, by omega⟩ : Fin (n + 3)) = 1 := by
  rw [Multiway.Sharing.clusterOmega_apply, Fin.sum_univ_two]
  have e0 : Multiway.SameOn (wtC n) {(0 : Fin 2)} (⟨0, by omega⟩ : Fin (n + 3))
      (⟨1, by omega⟩ : Fin (n + 3)) := by
    rw [sameOn_singleton_iff, Fin.ext_iff, wtC_val, wtC_val, ite_eq_left rfl, ite_eq_left rfl]
    simp
  have e1 : ¬ Multiway.SameOn (wtC n) {(1 : Fin 2)} (⟨0, by omega⟩ : Fin (n + 3))
      (⟨1, by omega⟩ : Fin (n + 3)) := by
    rw [sameOn_singleton_iff, Fin.ext_iff, wtC_val, wtC_val, ite_eq_right (by decide),
      ite_eq_right (by decide)]
    simp
  have e2 : ¬ ((⟨0, by omega⟩ : Fin (n + 3)) = (⟨1, by omega⟩ : Fin (n + 3))) := by
    rw [Fin.ext_iff]
    simp
  rw [ite_eq_left e0, ite_eq_right e1, ite_eq_right e2]
  ring

/-- Vacuity witness for `clustershock_a_general`, on the `J = 2` design above. -/
theorem clustershock_a_general_witness (s : ℝ) :
    Tendsto (fun n => ((coins (3 * (n + 3))).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt (n + 2))
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => 1) (fun _ => 1))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
                  ((redXt (n + 2))ᵀ *ᵥ (fun o => shockSum (wtIdx n) o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine clustershock_a_general (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    (fun n => coins (3 * (n + 3))) (fun n => redXt (n + 2)) (fun _ => 1)
    (fun n => shockSum (wtIdx n))
    (fun n ω => ((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
      ((redXt (n + 2))ᵀ *ᵥ (fun o => shockSum (wtIdx n) o ω)))
    (fun _ => 0) wtC Finset.univ wtDep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    (fun n => redXt_scoreMap_isUnit (n + 2))
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => zero_le_one) 1 zero_lt_one (fun _ _ => le_refl 1)
    ?_ (fun n o => integral_shockSum (wtIdx n) o)
    1 3 zero_le_one (by norm_num) ?_ ?_
    1 zero_lt_one ?_ (fun n => ⟨⟨0, by omega⟩⟩)
    (fun _ => 2) (fun n j _ γ => wtCluster_card n j γ) ?_ (fun _ => (1 : ℝ)) ?_ s
  · -- `hOm`
    intro n o o'
    rw [integral_shockSum_mul (wtIdx_component n), Multiway.Sharing.clusterOmega_apply,
      Fin.sum_univ_three, Fin.sum_univ_two]
    have e0 : (wtIdx n o 0 = wtIdx n o' 0) ↔ Multiway.SameOn (wtC n) {0} o o' := by
      rw [wtIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_zero_iff]
    have e1 : (wtIdx n o 1 = wtIdx n o' 1) ↔ Multiway.SameOn (wtC n) {1} o o' := by
      rw [wtIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_one_iff]
    have e2 : (wtIdx n o 2 = wtIdx n o' 2) ↔ (o = o') := by
      rw [wtIdx_eq_iff, wtLab_eq_two_iff]
    rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  · -- `hB`
    intro _ _
    simp [redXt, dotProduct]
  · -- `hnu`
    intro n o ω
    simpa using abs_shockSum_le (wtIdx n) o ω
  · -- `hdesign`
    intro n
    simp only [Fintype.card_fin]
    rw [redXt_transpose_mul_self]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · -- `hGrate`: `Ḡ_n⁴/n = 16/(n+3) → 0`
    simp only [Fintype.card_fin]
    have hd : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop := by
      have hcast : ∀ n : ℕ, ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := fun n => by push_cast; ring
      simp only [hcast]
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using (tendsto_const_nhds (x := ((2 : ℕ) : ℝ) ^ 4) (f := atTop (α := ℕ))).div_atTop hd
  · -- `hb`
    simp [dotProduct]

end GeneralWitness

section PartBRate

/-- `Ḡ_n^{3-ε}/n^{1-ε} → 0` at `ε = 1/3` is equivalent to `Ḡ_n⁴/n → 0`. -/
theorem tendsto_pow_four_div_of_threeseq_b {Gb N : ℕ → ℕ}
    (h : Tendsto (fun n => (Gb n : ℝ) ^ (3 - (1 : ℝ) / 3) / (N n : ℝ) ^ (1 - (1 : ℝ) / 3))
      atTop (𝓝 0)) :
    Tendsto (fun n => (Gb n : ℝ) ^ 4 / (N n : ℝ)) atTop (𝓝 0) := by
  have hcube : ∀ x : ℝ, 0 ≤ x → (x ^ (3 - (1 : ℝ) / 3)) ^ (3 : ℕ) = x ^ (8 : ℕ) := by
    intro x hx
    rw [← Real.rpow_natCast (x ^ (3 - (1 : ℝ) / 3)) 3, ← Real.rpow_mul hx,
      ← Real.rpow_natCast x 8]
    norm_num
  have hcube' : ∀ x : ℝ, 0 ≤ x → (x ^ (1 - (1 : ℝ) / 3)) ^ (3 : ℕ) = x ^ (2 : ℕ) := by
    intro x hx
    rw [← Real.rpow_natCast (x ^ (1 - (1 : ℝ) / 3)) 3, ← Real.rpow_mul hx,
      ← Real.rpow_natCast x 2]
    norm_num
  have hkey : ∀ n, ((Gb n : ℝ) ^ 4 / (N n : ℝ)) ^ (2 : ℕ)
      = ((Gb n : ℝ) ^ (3 - (1 : ℝ) / 3) / (N n : ℝ) ^ (1 - (1 : ℝ) / 3)) ^ (3 : ℕ) := by
    intro n
    rw [div_pow, div_pow, hcube _ (by positivity), hcube' _ (by positivity)]
    ring
  have h3 : Tendsto
      (fun n => ((Gb n : ℝ) ^ (3 - (1 : ℝ) / 3) / (N n : ℝ) ^ (1 - (1 : ℝ) / 3)) ^ (3 : ℕ))
      atTop (𝓝 0) := by simpa using h.pow 3
  have hg2 : Tendsto (fun n => ((Gb n : ℝ) ^ 4 / (N n : ℝ)) ^ (2 : ℕ)) atTop (𝓝 0) :=
    h3.congr (fun n => (hkey n).symm)
  have hre : ∀ n, Real.sqrt (((Gb n : ℝ) ^ 4 / (N n : ℝ)) ^ (2 : ℕ))
      = (Gb n : ℝ) ^ 4 / (N n : ℝ) := by
    intro n
    rw [Real.sqrt_sq (by positivity)]
  have hcont : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_sqrt.tendsto 0
  exact (hcont.comp hg2).congr hre

end PartBRate

/-- **Corollary SM.D.3, bounded fourth moments, general `J`.** Under the cluster-shock model with
`∫ν_o⁴ ≤ C₄⁴` in place of bounded shocks and `Ḡ_n⁴/n → 0`, the standardized restriction
`b'𝒱_n^{-1/2}𝓡_n(β̂_JM − β)` is asymptotically standard normal. -/
theorem clustershock_b_general
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Dm : Type*} [DecidableEq Dm]
    {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (μ : ∀ n, Measure (W n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Xt : ∀ n, Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → W n → ℝ) (bhat : ∀ n, W n → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm)
    (Dv : ∀ n, DepGraph (ν n) (μ n))
    (hshare : ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n) dims o o')
    (hscore : ∀ n ω, bhat n ω - β n
      = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ ((Xt n)ᵀ *ᵥ (fun o => ν n o ω)))
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    (sc : ℕ → Dm → ℝ) (ve : ∀ n, O n → ℝ) (hsc : ∀ n, ∀ j ∈ dims, 0 ≤ sc n j)
    (s2 : ℝ) (hs2 : 0 < s2) (hve : ∀ n o, s2 ≤ ve n o)
    (hOm : ∀ n o o', ∫ ω, ν n o ω * ν n o' ω ∂(μ n)
      = Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n) o o')
    (hmean : ∀ n o, ∫ ω, ν n o ω ∂(μ n) = 0)
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (hB : ∀ n o, (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) ≤ B ^ 2)
    (hint4 : ∀ n o, Integrable (fun ω => (ν n o ω) ^ 4) (μ n))
    (hfour : ∀ n o, ∫ ω, (ν n o ω) ^ 4 ∂(μ n) ≤ C4 ^ 4)
    (θ : ℝ) (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (hGrate : Tendsto (fun n => (Gb n : ℝ) ^ 4 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n)
              (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  classical
  have hfloorOm : ∀ n, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n) :=
    fun n => Multiway.Sharing.smul_one_le_clusterOmega (hsc n) (hve n)
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hfloorK : ∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n) (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) := by
    intro n
    have h1 : s2 • ((θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ))
        ≤ s2 • ((Xt n)ᵀ * Xt n) := Multiway.loewner_smul_le_smul hs2.le (hdesign n)
    rw [smul_smul, ← mul_assoc] at h1
    exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj (hfloorOm n) (Xt n))
  have hnbhd : ∀ n o, (Dv n).nbhd o = Multiway.Sharing.closedNbhd (c n) dims o := by
    intro n o
    ext o'
    rw [DepGraph.mem_nbhd_iff, Multiway.Sharing.mem_closedNbhd]
    exact hshare n o o'
  set Dn : ℕ → ℕ := fun n => min (dims.card * Gb n) (Fintype.card (O n)) with hDndef
  have hdegF : ∀ n o, ((Dv n).nbhd o).card ≤ Dn n := by
    intro n o
    refine le_min ?_ ?_
    · rw [hnbhd n o]; exact card_closedNbhd_le_mul (hGb n) o
    · exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  have hDn1 : ∀ n, 1 ≤ Dn n := by
    intro n
    obtain ⟨o⟩ := hne n
    refine le_trans ?_ (hdegF n o)
    exact Finset.card_pos.mpr ⟨o, (Dv n).self_mem_nbhd o⟩
  refine cltcluster_b_general_betaJM μ Xt
    (fun n => Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) Rn ν bhat β Dv hscore hA
    (fun n => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n => mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n)) hfloorK hOm hmean
    B C4 hB0 hC40 hB hint4 hfour Dn hDn1 (fun n => min_le_right _ _)
    (fun n o => le_trans (hdegF n o) (Nat.le_succ _)) ?_ b hb s
  exact tendsto_steinRate_of_cluster_size (mul_pos hs2 hθ) (fun n => hcard n)
    hDn1 (fun n => min_le_left _ _) hGrate

section PartBWitness

open Multiway.Multilinear

/-- Vacuity witness for `clustershock_b_general`, on the `J = 2` design of
`clustershock_a_general_witness`, with the fourth-moment bound at `C₄ = 3`. -/
theorem clustershock_b_general_witness (s : ℝ) :
    Tendsto (fun n => ((coins (3 * (n + 3))).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt (n + 2))
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => 1) (fun _ => 1))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
                  ((redXt (n + 2))ᵀ *ᵥ (fun o => shockSum (wtIdx n) o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  have habs : ∀ (n : ℕ) (o : Fin (n + 3)) (ω : Fin (3 * (n + 3)) → Bool),
      |shockSum (wtIdx n) o ω| ≤ 3 := by
    intro n o ω
    simpa using abs_shockSum_le (wtIdx n) o ω
  have hpow : ∀ (n : ℕ) (o : Fin (n + 3)) (ω : Fin (3 * (n + 3)) → Bool),
      (shockSum (wtIdx n) o ω) ^ 4 ≤ 3 ^ 4 := by
    intro n o ω
    have h1 : (shockSum (wtIdx n) o ω) ^ 4 = |shockSum (wtIdx n) o ω| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h1]
    exact pow_le_pow_left₀ (abs_nonneg _) (habs n o ω) 4
  have hint4 : ∀ (n : ℕ) (o : Fin (n + 3)),
      Integrable (fun ω => (shockSum (wtIdx n) o ω) ^ 4) (coins (3 * (n + 3))) := by
    intro n o
    refine Multiway.SteinCluster.integrable_of_abs_le
      ((measurable_shockSum (wtIdx n) o).pow_const 4) (C := 3 ^ 4) (fun ω => ?_)
    rw [abs_of_nonneg (by positivity)]
    exact hpow n o ω
  refine clustershock_b_general (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    (fun n => coins (3 * (n + 3))) (fun n => redXt (n + 2)) (fun _ => 1)
    (fun n => shockSum (wtIdx n))
    (fun n ω => ((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
      ((redXt (n + 2))ᵀ *ᵥ (fun o => shockSum (wtIdx n) o ω)))
    (fun _ => 0) wtC Finset.univ wtDep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    (fun n => redXt_scoreMap_isUnit (n + 2))
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => zero_le_one) 1 zero_lt_one (fun _ _ => le_refl 1)
    ?_ (fun n o => integral_shockSum (wtIdx n) o)
    1 3 zero_lt_one (by norm_num) ?_ (fun n o => hint4 n o) ?_
    1 zero_lt_one ?_ (fun n => ⟨⟨0, by omega⟩⟩)
    (fun _ => 2) (fun n j _ γ => wtCluster_card n j γ) ?_ (fun _ => (1 : ℝ)) ?_ s
  · -- `hOm`
    intro n o o'
    rw [integral_shockSum_mul (wtIdx_component n), Multiway.Sharing.clusterOmega_apply,
      Fin.sum_univ_three, Fin.sum_univ_two]
    have e0 : (wtIdx n o 0 = wtIdx n o' 0) ↔ Multiway.SameOn (wtC n) {0} o o' := by
      rw [wtIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_zero_iff]
    have e1 : (wtIdx n o 1 = wtIdx n o' 1) ↔ Multiway.SameOn (wtC n) {1} o o' := by
      rw [wtIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_one_iff]
    have e2 : (wtIdx n o 2 = wtIdx n o' 2) ↔ (o = o') := by
      rw [wtIdx_eq_iff, wtLab_eq_two_iff]
    rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  · -- `hB`
    intro _ _
    simp [redXt, dotProduct]
  · -- `hfour`
    intro n o
    calc ∫ ω, (shockSum (wtIdx n) o ω) ^ 4 ∂(coins (3 * (n + 3)))
        ≤ ∫ _ω, (3 : ℝ) ^ 4 ∂(coins (3 * (n + 3))) :=
          integral_mono (hint4 n o) (integrable_const _) (fun ω => hpow n o ω)
      _ = 3 ^ 4 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  · -- `hdesign`
    intro n
    simp only [Fintype.card_fin]
    rw [redXt_transpose_mul_self]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · -- `hGrate`
    simp only [Fintype.card_fin]
    have hd : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop := by
      have hcast : ∀ n : ℕ, ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := fun n => by push_cast; ring
      simp only [hcast]
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using (tendsto_const_nhds (x := ((2 : ℕ) : ℝ) ^ 4) (f := atTop (α := ℕ))).div_atTop hd
  · -- `hb`
    simp [dotProduct]

end PartBWitness

/-! ## Rate-agnostic inference for the cluster-shock model

Theorem 11 (Rate-agnostic inference under multiway clustering) for the cluster-shock model, at the
cluster-size condition `Ḡ_n³d_[Δ]/n → 0` and general `J`; no central limit theorem is involved.
The disturbance enters only through the conditional fourth-moment bound `𝔼[ν_o⁴ ∣ 𝒟] ≤ C`. The
limits are those of `Multiway.RateAgnostic`; this section supplies the model-specific inputs:
the dependency structure, the conditional mean zero, the variance floor `Ω_n ⪰ σ̲²θnI_K`, the
vanishing of `Ω` off the sharing graph, and the accumulation bounds. Since `Ω` is a conditional
expectation, these hold almost everywhere. -/

section RAHelpers

/-- An entrywise bound from a bound on the sum of squares. -/
theorem abs_le_of_sum_sq_le {K : Type*} [Fintype K] {x : K → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∑ k : K, x k ^ 2 ≤ B ^ 2) (k : K) : |x k| ≤ B := by
  have h1 : x k ^ 2 ≤ ∑ k : K, x k ^ 2 :=
    Finset.single_le_sum (f := fun k : K => x k ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have h2 := Real.sqrt_le_sqrt (h1.trans h)
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hB] at h2

/-- `a • I ⪯ b • I` implies `a ≤ b` when there is at least one coordinate. -/
theorem le_of_smul_one_le_smul_one {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    {a b : ℝ} (h : a • (1 : Matrix K K ℝ) ≤ b • (1 : Matrix K K ℝ)) : a ≤ b := by
  have ht := Multiway.trace_le_of_le h
  rw [Multiway.trace_smul_one, Multiway.trace_smul_one] at ht
  have hc : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  exact le_of_mul_le_mul_right ht hc

/-- `Ḡ_n ≥ 1`: a cluster of a maintained dimension contains the observation that indexes it. -/
theorem one_le_of_cluster_bound {O D L : Type*} [Fintype O] [DecidableEq O] [DecidableEq L]
    {c : D → O → L} {dims : Finset D} {Gb : ℕ} (hdims : dims.Nonempty) (hne : Nonempty O)
    (hGb : ∀ j ∈ dims, ∀ γ : L, (cluster (c j) γ).card ≤ Gb) : 1 ≤ Gb := by
  obtain ⟨o⟩ := hne
  obtain ⟨j, hj⟩ := hdims
  exact le_trans (Finset.card_pos.mpr ⟨o, mem_cluster.mpr rfl⟩) (hGb j hj (c j o))

/-- The maximal open degree of the sharing graph is at most `JḠ_n`. -/
theorem maxDegree_le_mul_of_cluster_bound {O D L : Type*} [Fintype O] [DecidableEq O]
    [DecidableEq D] [DecidableEq L] {c : D → O → L} {dims : Finset D} {Gb : ℕ}
    (hdims : dims.Nonempty) (hGb1 : 1 ≤ Gb)
    (hGb : ∀ j ∈ dims, ∀ γ : L, (cluster (c j) γ).card ≤ Gb) :
    Multiway.Sharing.maxDegree c dims ≤ dims.card * Gb := by
  rw [Multiway.Sharing.maxDegree]
  refine max_le ?_ (Finset.sup_le fun o _ => ?_)
  · have hJ : 1 ≤ dims.card := Finset.card_pos.mpr hdims
    simpa using Nat.mul_le_mul hJ hGb1
  · refine le_trans (Finset.card_le_card ?_) (card_closedNbhd_le_mul hGb o)
    intro o' ho'
    rw [Multiway.Sharing.mem_openNbhd] at ho'
    rw [Multiway.Sharing.mem_closedNbhd]
    exact ho'.2

/-- `scoreVar` at a deterministic design and a kernel vanishing off the sharing graph is
`X̃'ΩX̃`. -/
theorem scoreVar_apply_eq_conj {O D L K Ω : Type*} [Fintype O] [DecidableEq O] [DecidableEq D]
    [DecidableEq L] [Fintype K] {c : D → O → L} {dims : Finset D}
    {xt : O → K → Ω → ℝ} {Om : O → O → Ω → ℝ} {Xt : Matrix O K ℝ} {ω : Ω}
    (hxt : ∀ o k, xt o k ω = Xt o k)
    (hz : ∀ o o', ¬ Multiway.Linked c dims o o' → Om o o' ω = 0) :
    RateAgnostic.scoreVar c dims xt Om ω
      = Xtᵀ * (Matrix.of fun o o' => Om o o' ω) * Xt := by
  ext k l
  rw [Multiway.Sharing.conj_apply_eq_double_sum]
  show (∑ p ∈ Multiway.Sharing.linkedPairs c dims,
      xt p.1 k ω * xt p.2 l ω * Om p.1 p.2 ω) = _
  simp only [Matrix.of_apply]
  rw [Multiway.Sharing.sum_eq_sum_over_linkedPairs c dims
    (fun o o' => Om o o' ω) (fun o o' => Xt o k * Xt o' l) hz]
  exact Finset.sum_congr rfl fun p _ => by rw [hxt p.1 k, hxt p.2 l]

/-- `𝓜̃_n` and `𝓜̂_CGM` are symmetric. -/
theorem isHermitian_unionMeat {O D L K Ω : Type*} [Fintype O] [DecidableEq O] [DecidableEq D]
    [DecidableEq L] [Fintype K] [DecidableEq K] (c : D → O → L) (dims : Finset D)
    (xt : O → K → Ω → ℝ) (nu : O → Ω → ℝ) (ω : Ω) :
    (RateAgnostic.unionMeat c dims xt nu ω).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext k l
  rw [Matrix.conjTranspose_apply, star_trivial]
  show (∑ p ∈ Multiway.Sharing.linkedPairs c dims,
      xt p.1 l ω * xt p.2 k ω * (nu p.1 ω * nu p.2 ω))
    = ∑ p ∈ Multiway.Sharing.linkedPairs c dims,
      xt p.1 k ω * xt p.2 l ω * (nu p.1 ω * nu p.2 ω)
  refine Finset.sum_nbij' (i := Prod.swap) (j := Prod.swap) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Multiway.Sharing.linkedPairs, Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, Multiway.Sharing.linked_symm hp.2⟩
  · intro p hp
    rw [Multiway.Sharing.linkedPairs, Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, Multiway.Sharing.linked_symm hp.2⟩
  · intro p _; exact Prod.swap_swap p
  · intro p _; exact Prod.swap_swap p
  · intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring

/-- `Ω ⪰ σ̲²I_n` and `X̃'X̃ ⪰ θnI_K` give `Ω_n = X̃'ΩX̃ ⪰ σ̲²θn I_K`. -/
theorem smul_one_le_conj_of_floor_design {O K : Type*} [Fintype O] [DecidableEq O] [Fintype K]
    [DecidableEq K] {Om : Matrix O O ℝ} {Xt : Matrix O K ℝ} {s2 θ nR : ℝ}
    (hs2 : 0 ≤ s2) (hfloor : s2 • (1 : Matrix O O ℝ) ≤ Om)
    (hdesign : (θ * nR) • (1 : Matrix K K ℝ) ≤ Xtᵀ * Xt) :
    ((s2 * θ) * nR) • (1 : Matrix K K ℝ) ≤ Xtᵀ * Om * Xt := by
  have h1 : s2 • ((θ * nR) • (1 : Matrix K K ℝ)) ≤ s2 • (Xtᵀ * Xt) :=
    Multiway.loewner_smul_le_smul hs2 hdesign
  rw [smul_smul, ← mul_assoc] at h1
  exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj hfloor Xt)

/-- At `λ_min(Ω_n) ≥ a·n`, `δ_n = nD_n³/λ_min(Ω_n)² ≤ (J³/a²)(Ḡ_n³/n)`. -/
theorem deltaSeq_le_of_cluster_size {nR Dn Gb J a : ℝ} (ha : 0 < a) (hnR : 0 < nR)
    (hD0 : 0 ≤ Dn) (hD : Dn ≤ J * Gb) :
    Multiway.Sharing.deltaSeq nR Dn (a * nR) ≤ (J ^ 3 / a ^ 2) * (Gb ^ 3 / nR) := by
  rw [Multiway.Sharing.deltaSeq]
  have h3 : Dn ^ 3 ≤ (J * Gb) ^ 3 := pow_le_pow_left₀ hD0 hD 3
  have e1 : nR * Dn ^ 3 / (a * nR) ^ 2 = Dn ^ 3 / (a ^ 2 * nR) := by field_simp
  have e2 : (J ^ 3 / a ^ 2) * (Gb ^ 3 / nR) = (J * Gb) ^ 3 / (a ^ 2 * nR) := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h3 (by positivity)

theorem deltaSeq_nonneg {nR Dn lmin : ℝ} (hnR : 0 ≤ nR) (hD : 0 ≤ Dn) :
    0 ≤ Multiway.Sharing.deltaSeq nR Dn lmin := by
  rw [Multiway.Sharing.deltaSeq]
  positivity

end RAHelpers

/-! ### The conditional covariance matrix of the cluster-shock model -/

/-- `Ω(ω) := (𝔼[ν_oν_{o'} ∣ 𝒟](ω))_{o,o'}`, the conditional covariance matrix; its entries are
`Multiway.RateAgnostic.condOmegaKernel`. -/
noncomputable def condOmegaMat {O Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (nu : O → Ω → ℝ) (ω : Ω) : Matrix O O ℝ :=
  Matrix.of fun o o' => (P[nu o * nu o' | 𝒟]) ω

theorem condOmegaMat_apply {O Ω : Type*} (𝒟 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (nu : O → Ω → ℝ) (ω : Ω) (o o' : O) :
    condOmegaMat 𝒟 P nu ω o o' = (P[nu o * nu o' | 𝒟]) ω := rfl

section RateAgnosticHalf

variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Lemma SM.B.13 (The infeasible union meat), second claim, for the cluster-shock model:
`‖𝓜̃_n − Ω_n‖_F/λ_min(Ω_n) ⟶ᵖ 0` with `Ω_n = X̃'ΩX̃`. -/
theorem clustershock_meat_tendstoInProb (hm : 𝒟 ≤ mΩ) [SigmaFinite (P.trim hm)]
    {O L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)] [∀ n, DecidableEq (L n)]
    {Dm : Type*} [DecidableEq Dm] {K : Type*} [Fintype K] [DecidableEq K]
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm) (hdims : dims.Nonempty)
    (Z : ∀ n, ((Dm × L n) ⊕ O n) → Ω → ℝ)
    (hZmeas : ∀ n s, Measurable (Z n s))
    (hZ4 : ∀ n s, MemLp (Z n s) 4 P)
    (hZind : ∀ n, iCondIndepFun 𝒟 hm (Z n) P)
    (hZmean : ∀ n s, P[Z n s | 𝒟] =ᵐ[P] 0)
    {sc : ℕ → Dm → ℝ}
    (hsc : ∀ n, ∀ j ∈ dims, ∀ g : L n,
      P[Z n (Sum.inl (j, g)) * Z n (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc n j)
    {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hmom : ∀ n (o : O n), ∀ᵐ ω ∂P,
      (P[fun ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (Xt : ∀ n, Matrix (O n) K ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n (o : O n), ∑ k : K, (Xt n o k) ^ 2 ≤ B ^ 2)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hdelta : Tendsto (fun n => 64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
        * Multiway.Sharing.deltaSeq (Fintype.card (O n) : ℝ)
            (Multiway.Sharing.maxDegree (c n) dims : ℝ) (lam n)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω =>
        rectFrobNorm (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
            (Multiway.Sharing.nuRV (c n) dims (Z n)) ω
          - (Xt n)ᵀ * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n)
        / lam n)
      atTop (fun _ => 0) := by
  classical
  set nu : ∀ n, O n → Ω → ℝ := fun n => Multiway.Sharing.nuRV (c n) dims (Z n) with hnudef
  have hnuform : ∀ n (o : O n), nu n o
      = fun ω => (∑ j ∈ dims, Z n (Sum.inl (j, c n j o)) ω) + Z n (Sum.inr o) ω := by
    intro n o
    funext ω
    exact Multiway.Sharing.nuRV_apply (c n) dims (Z n) o ω
  have hnuMeas : ∀ n (o : O n), Measurable (nu n o) := by
    intro n o
    rw [hnuform n o]
    exact (Finset.measurable_sum dims fun j _ => hZmeas n _).add (hZmeas n _)
  have hnu4 : ∀ n (o : O n), MemLp (nu n o) 4 P := by
    intro n o
    rw [hnuform n o]
    exact (memLp_finsetSum dims fun j _ => hZ4 n _).add (hZ4 n _)
  have hprod : ∀ n (o o' : O n), MemLp (nu n o * nu n o') 2 P := fun n o o' =>
    RateAgnostic.memLp_two_mul_of_memLp_four (hnu4 n) o o'
  have hZ2 : ∀ n s, MemLp (Z n s) 2 P := fun n s => (hZ4 n s).mono_exponent (by norm_num)
  have hreg : ∀ n, Multiway.Sharing.Regime3 𝒟 hm (c n) dims (nu n) P := fun n =>
    Multiway.Sharing.regime3_of_clusterShock 𝒟 hm (c n) dims (hZmeas n) (hZind n)
  have hzero : ∀ n, ∀ᵐ ω ∂P, ∀ o o' : O n, ¬ Multiway.Linked (c n) dims o o' →
      (P[nu n o * nu n o' | 𝒟]) ω = 0 := fun n =>
    Multiway.Sharing.condOmega_eq_zero_of_not_linked (h𝒟 := hm) hdims (hZmeas n) (hZ2 n)
      (hZind n) (hZmean n) (hsc n)
  have hcondMeas : ∀ n (o o' : O n), Measurable (P[nu n o * nu n o' | 𝒟]) := fun n o o' =>
    (stronglyMeasurable_condExp.mono hm).measurable
  have hentMeas : ∀ n (k l : K), Measurable (fun ω =>
      (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k) (nu n) ω
        - RateAgnostic.scoreVar (c n) dims (fun o k (_ : Ω) => Xt n o k)
            (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) ω) k l) := by
    intro n k l
    have he : (fun ω =>
        (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k) (nu n) ω
          - RateAgnostic.scoreVar (c n) dims (fun o k (_ : Ω) => Xt n o k)
              (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) ω) k l)
        = fun ω => ∑ p ∈ Multiway.Sharing.linkedPairs (c n) dims,
            RateAgnostic.centeredSummand (fun o k (_ : Ω) => Xt n o k) (nu n)
              (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) k l p ω := by
      funext ω
      exact RateAgnostic.unionMeat_sub_apply (c n) dims _ _ _ k l ω
    rw [he]
    refine Finset.measurable_sum _ fun p _ => ?_
    show Measurable fun ω => Xt n p.1 k * Xt n p.2 l
      * (nu n p.1 ω * nu n p.2 ω - (P[nu n p.1 * nu n p.2 | 𝒟]) ω)
    exact measurable_const.mul (((hnuMeas n p.1).mul (hnuMeas n p.2)).sub (hcondMeas n p.1 p.2))
  have hentLp : ∀ n (k l : K), MemLp (fun ω =>
      (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k) (nu n) ω
        - RateAgnostic.scoreVar (c n) dims (fun o k (_ : Ω) => Xt n o k)
            (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) ω) k l) 2 P := by
    intro n k l
    have he : (fun ω =>
        (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k) (nu n) ω
          - RateAgnostic.scoreVar (c n) dims (fun o k (_ : Ω) => Xt n o k)
              (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) ω) k l)
        = fun ω => ∑ p ∈ Multiway.Sharing.linkedPairs (c n) dims,
            RateAgnostic.centeredSummand (fun o k (_ : Ω) => Xt n o k) (nu n)
              (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) k l p ω := by
      funext ω
      exact RateAgnostic.unionMeat_sub_apply (c n) dims _ _ _ k l ω
    rw [he]
    refine memLp_finsetSum _ fun p _ => ?_
    have h1 : MemLp (fun ω => nu n p.1 ω * nu n p.2 ω - (P[nu n p.1 * nu n p.2 | 𝒟]) ω) 2 P :=
      (hprod n p.1 p.2).sub (MemLp.condExp one_le_two (hprod n p.1 p.2))
    exact h1.const_mul _
  have hFmeas : ∀ n, Measurable (fun ω =>
      rectFrobNorm (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k) (nu n) ω
        - RateAgnostic.scoreVar (c n) dims (fun o k (_ : Ω) => Xt n o k)
            (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) ω)) := by
    intro n
    simp only [rectFrobNorm, rectFrobSq]
    exact (Finset.measurable_sum _ fun k _ =>
      Finset.measurable_sum _ fun l _ => (hentMeas n k l).pow_const 2).sqrt
  have hFint : ∀ n, Integrable (fun ω =>
      frobSq (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k) (nu n) ω
        - RateAgnostic.scoreVar (c n) dims (fun o k (_ : Ω) => Xt n o k)
            (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) ω)) P := by
    intro n
    simp only [frobSq]
    exact integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => (hentLp n k l).integrable_sq
  have hbase := RateAgnostic.infeasibleMeat_tendstoInProb_of_regime3_nodiv 𝒟 hm
    (O := O) (D := fun _ => Dm) (L := L) (κ := fun _ => K)
    c (fun _ => dims) (fun n o k (_ : Ω) => Xt n o k) nu (B := B) hCm
    (lam := fun n _ => lam n) (fun _ => measurable_const) (fun n _ => hlam0 n)
    hFmeas hFint (fun _ => hdims) hreg hnuMeas hprod (fun _ _ _ => stronglyMeasurable_const)
    (fun n o k _ => abs_le_of_sum_sq_le hB0 (hB n o) k) hmom
    (RateAgnostic.tendstoInMeasure_zero_of_tendsto_const hdelta)
  refine RateAgnostic.tendstoInMeasure_zero_of_le_ae
    (fun n => Filter.Eventually.of_forall fun ω =>
      div_nonneg (rectFrobNorm_nonneg _) (hlam0 n).le) (fun n => ?_) hbase
  filter_upwards [hzero n] with ω hz
  have heq : RateAgnostic.scoreVar (c n) dims (fun o k (_ : Ω) => Xt n o k)
      (RateAgnostic.condOmegaKernel 𝒟 P (nu n)) ω
      = (Xt n)ᵀ * condOmegaMat 𝒟 P (nu n) ω * Xt n :=
    scoreVar_apply_eq_conj (fun o k => rfl) (fun o o' h => hz o o' h)
  rw [heq]

/-- **Corollary SM.D.3, Theorem 11(a) for the cluster-shock model.** At general `J` and under
`Ḡ_n³/n → 0`, `‖Ω_n^{-1/2}(𝓜̃_n − Ω_n)Ω_n^{-1/2}‖_F ⟶ᵖ 0` and
`𝒱_n^{-1/2}𝒱̃_n𝒱_n^{-1/2} ⟶ᵖ I_r`. -/
theorem clustershock_rateagnostic_a (hm : 𝒟 ≤ mΩ) [SigmaFinite (P.trim hm)]
    {O L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)] [∀ n, DecidableEq (L n)]
    {Dm : Type*} [DecidableEq Dm] {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm) (hdims : dims.Nonempty)
    (Z : ∀ n, ((Dm × L n) ⊕ O n) → Ω → ℝ)
    (hZmeas : ∀ n s, Measurable (Z n s))
    (hZ4 : ∀ n s, MemLp (Z n s) 4 P)
    (hZind : ∀ n, iCondIndepFun 𝒟 hm (Z n) P)
    (hZmean : ∀ n s, P[Z n s | 𝒟] =ᵐ[P] 0)
    {sc : ℕ → Dm → ℝ}
    (hsc : ∀ n, ∀ j ∈ dims, ∀ g : L n,
      P[Z n (Sum.inl (j, g)) * Z n (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc n j)
    {s2 : ℝ} (hs2 : 0 < s2)
    (hve : ∀ n (o : O n), ∀ᵐ ω ∂P, s2 ≤ (P[Z n (Sum.inr o) * Z n (Sum.inr o) | 𝒟]) ω)
    {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hmom : ∀ n (o : O n), ∀ᵐ ω ∂P,
      (P[fun ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (Xt : ∀ n, Matrix (O n) K ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n (o : O n), ∑ k : K, (Xt n o k) ^ 2 ≤ B ^ 2)
    {θ : ℝ} (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (hGrate : Tendsto (fun n => (Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0))
    (A : ℕ → Matrix K r ℝ) (hA : ∀ n, Function.Injective (A n).mulVec) :
    TendstoInMeasure P (fun n ω =>
        rectFrobNorm ((sqrtPD ((Xt n)ᵀ
              * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n))⁻¹
          * (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
                (Multiway.Sharing.nuRV (c n) dims (Z n)) ω
              - (Xt n)ᵀ * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n)
          * (sqrtPD ((Xt n)ᵀ
              * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n))⁻¹))
        atTop (fun _ => 0)
      ∧ TendstoInMeasure P (fun n ω =>
        rectFrobNorm ((sqrtPD ((A n)ᵀ * ((Xt n)ᵀ
                * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n) * A n))⁻¹
          * ((A n)ᵀ * RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
                (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * A n)
          * (sqrtPD ((A n)ᵀ * ((Xt n)ᵀ
                * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n)
              * A n))⁻¹ - 1))
        atTop (fun _ => 0) := by
  classical
  have hZ2 : ∀ n s, MemLp (Z n s) 2 P := fun n s => (hZ4 n s).mono_exponent (by norm_num)
  have hcard : ∀ n, 0 < (Fintype.card (O n) : ℝ) := by
    intro n
    have := hne n
    exact_mod_cast Fintype.card_pos
  have ha : (0 : ℝ) < s2 * θ := mul_pos hs2 hθ
  have hlam0 : ∀ n, 0 < (s2 * θ) * (Fintype.card (O n) : ℝ) := fun n => mul_pos ha (hcard n)
  have hfloorOm : ∀ n, ∀ᵐ ω ∂P, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω := by
    intro n
    have hnn := hne n
    exact Multiway.Sharing.smul_one_le_condOmega (h𝒟 := hm) (IsProbabilityMeasure.ne_zero P)
      (hZmeas n) (hZ2 n) (hZind n) (hZmean n) (hsc n) (hve n)
  have hfloorK : ∀ n, ∀ᵐ ω ∂P, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ (Xt n)ᵀ * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n := by
    intro n
    filter_upwards [hfloorOm n] with ω hω
    exact smul_one_le_conj_of_floor_design hs2.le hω (hdesign n)
  have hposdef : ∀ n, ∀ᵐ ω ∂P,
      ((Xt n)ᵀ * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n).PosDef := by
    intro n
    filter_upwards [hfloorK n] with ω hω
    exact Multiway.posDef_of_le (Matrix.PosDef.one.smul (hlam0 n)) hω
  have hGb1 : ∀ n, 1 ≤ Gb n := fun n => one_le_of_cluster_bound hdims (hne n) (hGb n)
  have hDle : ∀ n, (Multiway.Sharing.maxDegree (c n) dims : ℝ)
      ≤ (dims.card : ℝ) * (Gb n : ℝ) := by
    intro n
    exact_mod_cast maxDegree_le_mul_of_cluster_bound hdims (hGb1 n) (hGb n)
  have hdelta : Tendsto (fun n => 64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
      * Multiway.Sharing.deltaSeq (Fintype.card (O n) : ℝ)
          (Multiway.Sharing.maxDegree (c n) dims : ℝ)
          ((s2 * θ) * (Fintype.card (O n) : ℝ))) atTop (𝓝 0) := by
    have hCbig : Tendsto (fun n => (64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
        * ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2)) * ((Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)))
        atTop (𝓝 0) := by
      simpa using hGrate.const_mul (64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
        * ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2))
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hCbig
    · exact mul_nonneg (by positivity)
        (deltaSeq_nonneg (le_of_lt (hcard n)) (by positivity))
    · have hb := deltaSeq_le_of_cluster_size (a := s2 * θ) ha (hcard n) (by positivity) (hDle n)
      calc 64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
            * Multiway.Sharing.deltaSeq (Fintype.card (O n) : ℝ)
                (Multiway.Sharing.maxDegree (c n) dims : ℝ)
                ((s2 * θ) * (Fintype.card (O n) : ℝ))
          ≤ 64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
            * (((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2)
              * ((Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ))) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
              * ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2))
            * ((Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) := by ring
  have hE := clustershock_meat_tendstoInProb hm c dims hdims Z hZmeas hZ4 hZind hZmean hsc hCm
    hmom Xt hB0 hB (lam := fun n => (s2 * θ) * (Fintype.card (O n) : ℝ)) hlam0 hdelta
  exact RateAgnostic.rateAgnostic_a_ae (c := fun n (_ : Ω) => (s2 * θ) * (Fintype.card (O n) : ℝ))
    hposdef (fun n _ => hlam0 n) hfloorK hE
    (A := fun n (_ : Ω) => A n) (fun n => Filter.Eventually.of_forall fun _ => hA n)

end RateAgnosticHalf

section RateAgnosticHalfB

variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

omit [StandardBorelSpace Ω] in
omit [StandardBorelSpace Ω] in
/-- `Ω(ω)` is symmetric. -/
theorem isHermitian_condOmegaMat {O : Type*} [Fintype O] [DecidableEq O]
    (nu : O → Ω → ℝ) (ω : Ω) :
    (condOmegaMat 𝒟 P nu ω).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext o o'
  rw [Matrix.conjTranspose_apply, star_trivial]
  show (P[nu o' * nu o | 𝒟]) ω = (P[nu o * nu o' | 𝒟]) ω
  rw [mul_comm]

omit [StandardBorelSpace Ω] in
/-- A bound `|ν_o| ≤ C_ν` gives `𝔼[ν_o⁴ ∣ 𝒟] ≤ C_ν⁴`. -/
theorem condExp_pow_four_le_of_bound (hm : 𝒟 ≤ mΩ) {f : Ω → ℝ} {Cnu : ℝ}
    (hf : ∀ ω, |f ω| ≤ Cnu) (hint : Integrable (fun ω => f ω ^ 4) P) :
    ∀ᵐ ω ∂P, (P[fun ω => f ω ^ 4 | 𝒟]) ω ≤ Cnu ^ 4 := by
  have hle : (fun ω => f ω ^ 4) ≤ᵐ[P] fun _ => Cnu ^ 4 := by
    filter_upwards with ω
    calc f ω ^ 4 = |f ω| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ Cnu ^ 4 := pow_le_pow_left₀ (abs_nonneg _) (hf ω) 4
  have hmono := condExp_mono (μ := P) (m := 𝒟) hint (integrable_const _) hle
  filter_upwards [hmono] with ω hω
  rwa [condExp_const hm (Cnu ^ 4)] at hω

/-- For the cluster-shock model, `‖𝓜̂_CGM − 𝓜̃_n‖_F/λ_min(Ω_n) ⟶ᵖ 0` with `ν̂_FE = ν − Πν`, where
`Π` is a deterministic symmetric idempotent of trace `d_{[Δ]}+K`. -/
theorem clustershock_perturb_tendstoInProb (hm : 𝒟 ≤ mΩ) [SigmaFinite (P.trim hm)]
    {O L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)] [∀ n, DecidableEq (L n)]
    {Dm : Type*} [DecidableEq Dm] {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm) (hdims : dims.Nonempty)
    (Z : ∀ n, ((Dm × L n) ⊕ O n) → Ω → ℝ)
    (hZmeas : ∀ n s, Measurable (Z n s))
    (hZ4 : ∀ n s, MemLp (Z n s) 4 P)
    (hZind : ∀ n, iCondIndepFun 𝒟 hm (Z n) P)
    (hZmean : ∀ n s, P[Z n s | 𝒟] =ᵐ[P] 0)
    {sc : ℕ → Dm → ℝ}
    (hsc : ∀ n, ∀ j ∈ dims, ∀ g : L n,
      P[Z n (Sum.inl (j, g)) * Z n (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc n j)
    {s2 : ℝ} (hs2 : 0 < s2)
    (hve : ∀ n (o : O n), ∀ᵐ ω ∂P, s2 ≤ (P[Z n (Sum.inr o) * Z n (Sum.inr o) | 𝒟]) ω)
    {Cm : ℝ} (hCm : 0 < Cm)
    (hmom : ∀ n (o : O n), ∀ᵐ ω ∂P,
      (P[fun ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (Xt : ∀ n, Matrix (O n) K ℝ) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ n (o : O n), ∑ k : K, (Xt n o k) ^ 2 ≤ B ^ 2)
    {θ : ℝ} (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Prm : ∀ n, Matrix (O n) (O n) ℝ) {dd : ℕ → ℝ} {Kr : ℝ} (hK0 : 0 ≤ Kr)
    (hdd : ∀ n, 1 ≤ dd n)
    (hPrH : ∀ n, (Prm n).IsHermitian) (hPrI : ∀ n, Prm n * Prm n = Prm n)
    (hPrtr : ∀ n, (Prm n).trace = dd n + Kr)
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (hGdrate : Tendsto (fun n => (Gb n : ℝ) ^ 3 * dd n / (Fintype.card (O n) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω =>
        rectFrobNorm (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
            (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
              - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
          - RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
              (Multiway.Sharing.nuRV (c n) dims (Z n)) ω)
        / ((s2 * θ) * (Fintype.card (O n) : ℝ)))
      atTop (fun _ => 0) := by
  classical
  set nu : ∀ n, O n → Ω → ℝ := fun n => Multiway.Sharing.nuRV (c n) dims (Z n) with hnudef
  have hnuform : ∀ n (o : O n), nu n o
      = fun ω => (∑ j ∈ dims, Z n (Sum.inl (j, c n j o)) ω) + Z n (Sum.inr o) ω := by
    intro n o
    funext ω
    exact Multiway.Sharing.nuRV_apply (c n) dims (Z n) o ω
  have hnuMeas : ∀ n (o : O n), Measurable (nu n o) := by
    intro n o
    rw [hnuform n o]
    exact (Finset.measurable_sum dims fun j _ => hZmeas n _).add (hZmeas n _)
  have hnu4 : ∀ n (o : O n), MemLp (nu n o) 4 P := by
    intro n o
    rw [hnuform n o]
    exact (memLp_finsetSum dims fun j _ => hZ4 n _).add (hZ4 n _)
  have hnuL2 : ∀ n (o : O n), MemLp (nu n o) 2 P := fun n o =>
    (hnu4 n o).mono_exponent (by norm_num)
  have hprod : ∀ n (o o' : O n), MemLp (nu n o * nu n o') 2 P := fun n o o' =>
    RateAgnostic.memLp_two_mul_of_memLp_four (hnu4 n) o o'
  have hZ2 : ∀ n s, MemLp (Z n s) 2 P := fun n s => (hZ4 n s).mono_exponent (by norm_num)
  have hzero : ∀ n, ∀ᵐ ω ∂P, ∀ o o' : O n, ¬ Multiway.Linked (c n) dims o o' →
      (P[nu n o * nu n o' | 𝒟]) ω = 0 := fun n =>
    Multiway.Sharing.condOmega_eq_zero_of_not_linked (h𝒟 := hm) hdims (hZmeas n) (hZ2 n)
      (hZind n) (hZmean n) (hsc n)
  have hz : ∀ n (o o' : O n), ¬ Multiway.Linked (c n) dims o o' →
      P[nu n o * nu n o' | 𝒟] =ᵐ[P] 0 := by
    intro n o o' hsep
    filter_upwards [hzero n] with ω hω
    exact hω o o' hsep
  have hcard : ∀ n, 0 < (Fintype.card (O n) : ℝ) := by
    intro n
    have := hne n
    exact_mod_cast Fintype.card_pos
  have ha : (0 : ℝ) < s2 * θ := mul_pos hs2 hθ
  have hlam0 : ∀ n, 0 < (s2 * θ) * (Fintype.card (O n) : ℝ) := fun n => mul_pos ha (hcard n)
  -- the variance floor and the upper bound, at the same `ω`
  have hfloorOm : ∀ n, ∀ᵐ ω ∂P, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ condOmegaMat 𝒟 P (nu n) ω := by
    intro n
    have := hne n
    exact Multiway.Sharing.smul_one_le_condOmega (h𝒟 := hm) (IsProbabilityMeasure.ne_zero P)
      (hZmeas n) (hZ2 n) (hZind n) (hZmean n) (hsc n) (hve n)
  have hfloorK : ∀ n, ∀ᵐ ω ∂P, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ (Xt n)ᵀ * condOmegaMat 𝒟 P (nu n) ω * Xt n := by
    intro n
    filter_upwards [hfloorOm n] with ω hω
    exact smul_one_le_conj_of_floor_design hs2.le hω (hdesign n)
  have hupper : ∀ n, ∀ᵐ ω ∂P, (Xt n)ᵀ * condOmegaMat 𝒟 P (nu n) ω * Xt n
      ≤ (Real.sqrt Cm * ((Multiway.Sharing.maxDegree (c n) dims : ℝ) + 1)
          * ((Fintype.card (O n) : ℝ) * B ^ 2)) • (1 : Matrix K K ℝ) := by
    intro n
    have hbd : ∀ᵐ ω ∂P, ∀ o o' : O n,
        |condOmegaMat 𝒟 P (nu n) ω o o'| ≤ Real.sqrt Cm := by
      rw [ae_all_iff]
      intro o
      rw [ae_all_iff]
      intro o'
      exact RateAgnostic.abs_condOmega_le_sqrt (hprod n) (hmom n) o o'
    filter_upwards [hbd, hzero n] with ω h1 h2
    exact Multiway.Sharing.conj_le_smul_one_of_graphSupported (c n) dims
      (isHermitian_condOmegaMat (nu n) ω) (Real.sqrt_nonneg Cm) h1 h2 (hB n)
  -- `λ_min(Ω_n) ≤ λ_max(Ω_n) ≤ B²C^{1/2}n(D_n+1)`
  have hneBot : (MeasureTheory.ae P).NeBot :=
    MeasureTheory.ae_neBot.2 (IsProbabilityMeasure.ne_zero P)
  have hdscalar : ∀ n, (s2 * θ) * (Fintype.card (O n) : ℝ)
      ≤ B ^ 2 * Real.sqrt Cm * (Fintype.card (O n) : ℝ)
        * ((Multiway.Sharing.maxDegree (c n) dims : ℝ) + 1) := by
    intro n
    have hae : ∀ᵐ _ω ∂P, (s2 * θ) * (Fintype.card (O n) : ℝ)
        ≤ B ^ 2 * Real.sqrt Cm * (Fintype.card (O n) : ℝ)
          * ((Multiway.Sharing.maxDegree (c n) dims : ℝ) + 1) := by
      filter_upwards [hfloorK n, hupper n] with ω h1 h2
      have h3 := le_of_smul_one_le_smul_one (h1.trans h2)
      calc (s2 * θ) * (Fintype.card (O n) : ℝ)
          ≤ Real.sqrt Cm * ((Multiway.Sharing.maxDegree (c n) dims : ℝ) + 1)
            * ((Fintype.card (O n) : ℝ) * B ^ 2) := h3
        _ = B ^ 2 * Real.sqrt Cm * (Fintype.card (O n) : ℝ)
            * ((Multiway.Sharing.maxDegree (c n) dims : ℝ) + 1) := by ring
    exact Filter.eventually_const.mp hae
  have hsharing : ∀ (n : ℕ) (_ω : Ω), ((Multiway.Sharing.maxDegree (c n) dims : ℝ)) ^ 2
      / ((s2 * θ) * (Fintype.card (O n) : ℝ))
      ≤ 2 * B ^ 2 * Real.sqrt Cm
        * Multiway.Sharing.deltaSeq (Fintype.card (O n) : ℝ)
            ((Multiway.Sharing.maxDegree (c n) dims : ℝ))
            ((s2 * θ) * (Fintype.card (O n) : ℝ)) := by
    intro n _
    exact Multiway.Sharing.sharing_e hB0 (Real.sqrt_pos.mpr hCm)
      (by exact_mod_cast Multiway.Sharing.one_le_maxDegree (c n) dims) (hlam0 n) (hdscalar n)
  -- the accumulation condition
  have hGb1 : ∀ n, 1 ≤ Gb n := fun n => one_le_of_cluster_bound hdims (hne n) (hGb n)
  have hDle : ∀ n, (Multiway.Sharing.maxDegree (c n) dims : ℝ)
      ≤ (dims.card : ℝ) * (Gb n : ℝ) := by
    intro n
    exact_mod_cast maxDegree_le_mul_of_cluster_bound hdims (hGb1 n) (hGb n)
  have hacc : TendstoInMeasure P (fun (n : ℕ) (_ω : Ω) =>
      Multiway.Sharing.deltaSeq (Fintype.card (O n) : ℝ)
          ((Multiway.Sharing.maxDegree (c n) dims : ℝ))
          ((s2 * θ) * (Fintype.card (O n) : ℝ)) * dd n) atTop (fun _ => 0) := by
    refine RateAgnostic.tendstoInMeasure_zero_of_tendsto_const ?_
    have hCbig : Tendsto (fun n => ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2)
        * ((Gb n : ℝ) ^ 3 * dd n / (Fintype.card (O n) : ℝ))) atTop (𝓝 0) := by
      simpa using hGdrate.const_mul ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2)
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hCbig
    · exact mul_nonneg (deltaSeq_nonneg (le_of_lt (hcard n)) (by positivity))
        (le_trans zero_le_one (hdd n))
    · have hb := deltaSeq_le_of_cluster_size (a := s2 * θ) ha (hcard n) (by positivity) (hDle n)
      calc Multiway.Sharing.deltaSeq (Fintype.card (O n) : ℝ)
              ((Multiway.Sharing.maxDegree (c n) dims : ℝ))
              ((s2 * θ) * (Fintype.card (O n) : ℝ)) * dd n
          ≤ (((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2)
              * ((Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ))) * dd n :=
            mul_le_mul_of_nonneg_right hb (le_trans zero_le_one (hdd n))
        _ = ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2)
            * ((Gb n : ℝ) ^ 3 * dd n / (Fintype.card (O n) : ℝ)) := by ring
  -- integrability side conditions
  have hvpform : ∀ n (o : O n),
      (fun ω => (Prm n *ᵥ fun o' => nu n o' ω) o) = fun ω => ∑ o' : O n, Prm n o o' * nu n o' ω :=
    fun n o => rfl
  have hvpMeas : ∀ n (o : O n), Measurable fun ω => (Prm n *ᵥ fun o' => nu n o' ω) o := by
    intro n o
    rw [hvpform n o]
    exact Finset.measurable_sum _ fun o' _ => measurable_const.mul (hnuMeas n o')
  have hvpL2 : ∀ n (o : O n), MemLp (fun ω => (Prm n *ᵥ fun o' => nu n o' ω) o) 2 P := by
    intro n o
    rw [hvpform n o]
    exact memLp_finsetSum _ fun o' _ => (hnuL2 n o').const_mul _
  have hnuint : ∀ n, Integrable (fun ω => RateAgnostic.l2Norm (fun o => nu n o ω) ^ 2) P := by
    intro n
    have he : (fun ω => RateAgnostic.l2Norm (fun o => nu n o ω) ^ 2)
        = fun ω => ∑ o : O n, nu n o ω ^ 2 := by
      funext ω
      exact RateAgnostic.sq_l2Norm _
    rw [he]
    exact integrable_finsetSum _ fun o _ => (hnuL2 n o).integrable_sq
  have hvpint : ∀ n, Integrable (fun ω =>
      RateAgnostic.l2Norm (fun o => (Prm n *ᵥ fun o' => nu n o' ω) o) ^ 2) P := by
    intro n
    have he : (fun ω => RateAgnostic.l2Norm (fun o => (Prm n *ᵥ fun o' => nu n o' ω) o) ^ 2)
        = fun ω => ∑ o : O n, ((Prm n *ᵥ fun o' => nu n o' ω) o) ^ 2 := by
      funext ω
      exact RateAgnostic.sq_l2Norm _
    rw [he]
    exact integrable_finsetSum _ fun o _ => (hvpL2 n o).integrable_sq
  have hnuNormMeas : ∀ n, Measurable (fun ω => RateAgnostic.l2Norm (fun o => nu n o ω)) := by
    intro n
    simp only [RateAgnostic.l2Norm]
    exact (Finset.measurable_sum _ fun o _ => (hnuMeas n o).pow_const 2).sqrt
  have hvpNormMeas : ∀ n, Measurable
      (fun ω => RateAgnostic.l2Norm (fun o => (Prm n *ᵥ fun o' => nu n o' ω) o)) := by
    intro n
    simp only [RateAgnostic.l2Norm]
    exact (Finset.measurable_sum _ fun o _ => (hvpMeas n o).pow_const 2).sqrt
  have hmajint : ∀ n, Integrable (fun ω =>
      B ^ 2 * ((Multiway.Sharing.maxDegree (c n) dims : ℝ) + 1)
        / ((s2 * θ) * (Fintype.card (O n) : ℝ))
        * (2 * RateAgnostic.l2Norm (fun o => nu n o ω)
            * RateAgnostic.l2Norm (fun o => (Prm n *ᵥ fun o' => nu n o' ω) o)
          + RateAgnostic.l2Norm (fun o => (Prm n *ᵥ fun o' => nu n o' ω) o) ^ 2)) P := by
    intro n
    refine Integrable.const_mul ?_ _
    refine Integrable.add ?_ (hvpint n)
    refine Integrable.mono' ((hnuint n).add (hvpint n))
      (((measurable_const.mul (hnuNormMeas n)).mul (hvpNormMeas n)).aestronglyMeasurable) ?_
    filter_upwards with ω
    have h1 := RateAgnostic.l2Norm_nonneg (fun o => nu n o ω)
    have h2 := RateAgnostic.l2Norm_nonneg (fun o => (Prm n *ᵥ fun o' => nu n o' ω) o)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (RateAgnostic.l2Norm (fun o => nu n o ω)
      - RateAgnostic.l2Norm (fun o => (Prm n *ᵥ fun o' => nu n o' ω) o))]
  exact RateAgnostic.perturb_tendstoInProb_of_moments 𝒟 hm
    (O := O) (D := fun _ => Dm) (L := L) (κ := fun _ => K)
    c (fun _ => dims) (fun n o k (_ : Ω) => Xt n o k) nu (fun n (_ : Ω) => Prm n)
    hB0.le (fun n o _ => hB n o)
    (lam := fun n (_ : Ω) => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun _ => measurable_const) (fun n _ => hlam0 n) hCm hK0
    (nR := fun n => (Fintype.card (O n) : ℝ)) (dd := dd) hcard hdd (fun _ => rfl)
    (fun _ _ _ => stronglyMeasurable_const) (fun n _ => hPrH n) (fun n _ => hPrI n)
    (fun n _ => hPrtr n) hnuMeas hvpMeas hnuint hvpint hmajint hprod hmom hz hsharing hacc

/-- **Corollary SM.D.3, Theorem 11(b) for the cluster-shock model.** At general `J` and under
`Ḡ_n³d_[Δ]/n → 0`, `‖Ω_n^{-1/2}(𝓜̂_CGM − Ω_n)Ω_n^{-1/2}‖_F ⟶ᵖ 0`,
`𝒱_n^{-1/2}𝒱̂_n𝒱_n^{-1/2} ⟶ᵖ I_r`, and `P(𝒱̂_n ≻ 0) → 1`. -/
theorem clustershock_rateagnostic_b (hm : 𝒟 ≤ mΩ) [SigmaFinite (P.trim hm)]
    {O L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)] [∀ n, DecidableEq (L n)]
    {Dm : Type*} [DecidableEq Dm] {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    {r : Type*} [Fintype r] [DecidableEq r]
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm) (hdims : dims.Nonempty)
    (Z : ∀ n, ((Dm × L n) ⊕ O n) → Ω → ℝ)
    (hZmeas : ∀ n s, Measurable (Z n s))
    (hZ4 : ∀ n s, MemLp (Z n s) 4 P)
    (hZind : ∀ n, iCondIndepFun 𝒟 hm (Z n) P)
    (hZmean : ∀ n s, P[Z n s | 𝒟] =ᵐ[P] 0)
    {sc : ℕ → Dm → ℝ}
    (hsc : ∀ n, ∀ j ∈ dims, ∀ g : L n,
      P[Z n (Sum.inl (j, g)) * Z n (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc n j)
    {s2 : ℝ} (hs2 : 0 < s2)
    (hve : ∀ n (o : O n), ∀ᵐ ω ∂P, s2 ≤ (P[Z n (Sum.inr o) * Z n (Sum.inr o) | 𝒟]) ω)
    {Cm : ℝ} (hCm : 0 < Cm)
    (hmom : ∀ n (o : O n), ∀ᵐ ω ∂P,
      (P[fun ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (Xt : ∀ n, Matrix (O n) K ℝ) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ n (o : O n), ∑ k : K, (Xt n o k) ^ 2 ≤ B ^ 2)
    {θ : ℝ} (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Prm : ∀ n, Matrix (O n) (O n) ℝ) {dd : ℕ → ℝ} {Kr : ℝ} (hK0 : 0 ≤ Kr)
    (hdd : ∀ n, 1 ≤ dd n)
    (hPrH : ∀ n, (Prm n).IsHermitian) (hPrI : ∀ n, Prm n * Prm n = Prm n)
    (hPrtr : ∀ n, (Prm n).trace = dd n + Kr)
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (hGdrate : Tendsto (fun n => (Gb n : ℝ) ^ 3 * dd n / (Fintype.card (O n) : ℝ)) atTop (𝓝 0))
    (A : ℕ → Matrix K r ℝ) (hA : ∀ n, Function.Injective (A n).mulVec) :
    TendstoInMeasure P (fun n ω =>
        rectFrobNorm ((sqrtPD ((Xt n)ᵀ
              * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n))⁻¹
          * (RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
                (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
                  - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
              - (Xt n)ᵀ * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n)
          * (sqrtPD ((Xt n)ᵀ
              * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n))⁻¹))
        atTop (fun _ => 0)
      ∧ TendstoInMeasure P (fun n ω =>
        rectFrobNorm ((sqrtPD ((A n)ᵀ * ((Xt n)ᵀ
                * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n) * A n))⁻¹
          * ((A n)ᵀ * RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
                (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
                  - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω * A n)
          * (sqrtPD ((A n)ᵀ * ((Xt n)ᵀ
                * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n)
              * A n))⁻¹ - 1))
        atTop (fun _ => 0)
      ∧ Tendsto (fun n => P {ω | ((A n)ᵀ
          * RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
              (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
                - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
          * A n).PosDef}) atTop (𝓝 1) := by
  classical
  have hcard : ∀ n, 0 < (Fintype.card (O n) : ℝ) := by
    intro n
    have := hne n
    exact_mod_cast Fintype.card_pos
  have ha : (0 : ℝ) < s2 * θ := mul_pos hs2 hθ
  have hlam0 : ∀ n, 0 < (s2 * θ) * (Fintype.card (O n) : ℝ) := fun n => mul_pos ha (hcard n)
  have hZ2 : ∀ n s, MemLp (Z n s) 2 P := fun n s => (hZ4 n s).mono_exponent (by norm_num)
  have hfloorOm : ∀ n, ∀ᵐ ω ∂P, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω := by
    intro n
    have := hne n
    exact Multiway.Sharing.smul_one_le_condOmega (h𝒟 := hm) (IsProbabilityMeasure.ne_zero P)
      (hZmeas n) (hZ2 n) (hZind n) (hZmean n) (hsc n) (hve n)
  have hfloorK : ∀ n, ∀ᵐ ω ∂P, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ (Xt n)ᵀ * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n := by
    intro n
    filter_upwards [hfloorOm n] with ω hω
    exact smul_one_le_conj_of_floor_design hs2.le hω (hdesign n)
  have hposdef : ∀ n, ∀ᵐ ω ∂P,
      ((Xt n)ᵀ * condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω * Xt n).PosDef := by
    intro n
    filter_upwards [hfloorK n] with ω hω
    exact Multiway.posDef_of_le (Matrix.PosDef.one.smul (hlam0 n)) hω
  -- `Ḡ_n³/n → 0`, since `d_{[Δ]} ≥ 1`
  have hGrate : Tendsto (fun n => (Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hGdrate
    rw [div_le_div_iff_of_pos_right (hcard n)]
    have hmul : (0 : ℝ) ≤ (Gb n : ℝ) ^ 3 * (dd n - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (hdd n))
    nlinarith [hmul]
  have hE := clustershock_meat_tendstoInProb hm c dims hdims Z hZmeas hZ4 hZind hZmean hsc
    hCm.le hmom Xt hB0.le hB (lam := fun n => (s2 * θ) * (Fintype.card (O n) : ℝ)) hlam0
    (by
      have hCbig : Tendsto (fun n => (64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
          * ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2)) * ((Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)))
          atTop (𝓝 0) := by
        simpa using hGrate.const_mul (64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
          * ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2))
      have hGb1 : ∀ n, 1 ≤ Gb n := fun n => one_le_of_cluster_bound hdims (hne n) (hGb n)
      have hDle : ∀ n, (Multiway.Sharing.maxDegree (c n) dims : ℝ)
          ≤ (dims.card : ℝ) * (Gb n : ℝ) := by
        intro n
        exact_mod_cast maxDegree_le_mul_of_cluster_bound hdims (hGb1 n) (hGb n)
      refine squeeze_zero (fun n => ?_) (fun n => ?_) hCbig
      · exact mul_nonneg (by positivity)
          (deltaSeq_nonneg (le_of_lt (hcard n)) (by positivity))
      · have hb := deltaSeq_le_of_cluster_size (a := s2 * θ) ha (hcard n) (by positivity) (hDle n)
        calc 64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
              * Multiway.Sharing.deltaSeq (Fintype.card (O n) : ℝ)
                  (Multiway.Sharing.maxDegree (c n) dims : ℝ)
                  ((s2 * θ) * (Fintype.card (O n) : ℝ))
            ≤ 64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
              * (((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2)
                * ((Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ))) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = (64 * (Fintype.card K : ℝ) ^ 2 * B ^ 4 * Cm
                * ((dims.card : ℝ) ^ 3 / (s2 * θ) ^ 2))
              * ((Gb n : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) := by ring)
  have hperturb := clustershock_perturb_tendstoInProb hm c dims hdims Z hZmeas hZ4 hZind hZmean
    hsc hs2 hve hCm hmom Xt hB0 hB hθ hdesign hne Prm hK0 hdd hPrH hPrI hPrtr Gb hGb hGdrate
  have hHerm : ∀ n, ∀ᵐ ω ∂P, ((A n)ᵀ
      * RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
          (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
            - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
      * A n).IsHermitian := by
    intro n
    filter_upwards with ω
    have h := Matrix.isHermitian_conjTranspose_mul_mul (A n)
      (isHermitian_unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
        (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
          - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω)
    rwa [Multiway.conjTranspose_eq_transpose] at h
  exact RateAgnostic.rateAgnostic_b_ae (cn := fun n (_ : Ω) => (s2 * θ) * (Fintype.card (O n) : ℝ))
    hposdef (fun n _ => hlam0 n) hfloorK hE hperturb
    (A := fun n (_ : Ω) => A n) (fun n => Filter.Eventually.of_forall fun _ => hA n) hHerm

end RateAgnosticHalfB

/-! ### Vacuity witnesses for the rate-agnostic theorems

A cluster-shock design with `J = 1` and `n+1` clusters of two observations, on the infinite
product of fair coins `bigCoins`, with `𝒟 = ⊥`. The shocks are independent fair signs, one per
cluster and one per observation, so `Ω` is not diagonal and the sharing graph is not complete. -/

section RAWitness

/-- The infinite product of fair coins, on `ℕ → Bool`. -/
noncomputable def bigCoins : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => Multiway.Multilinear.coin

instance : IsProbabilityMeasure bigCoins := by
  unfold bigCoins
  infer_instance

/-- A fair sign read off coordinate `i`. -/
noncomputable def bigSign (i : ℕ) (ω : ℕ → Bool) : ℝ := if ω i then 1 else -1

theorem measurable_bigSign (i : ℕ) : Measurable (bigSign i) :=
  (measurable_of_finite fun b : Bool => if b then (1 : ℝ) else -1).comp (measurable_pi_apply i)

theorem abs_bigSign_le (i : ℕ) (ω : ℕ → Bool) : |bigSign i ω| ≤ 1 := by
  unfold bigSign
  by_cases h : ω i <;> simp [h]

theorem bigSign_mul_self (i : ℕ) : bigSign i * bigSign i = fun _ => (1 : ℝ) := by
  funext ω
  unfold bigSign
  by_cases h : ω i <;> simp [h]

theorem memLp_bigSign (i : ℕ) (p : ENNReal) : MemLp (bigSign i) p bigCoins :=
  (memLp_top_of_bound (measurable_bigSign i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_bigSign_le i ω)).mono_exponent le_top

theorem integral_bigCoins_eval (g : Bool → ℝ) (i : ℕ) :
    ∫ ω, g (ω i) ∂bigCoins = ∫ b, g b ∂Multiway.Multilinear.coin := by
  have hmap : Measure.map (fun ω : ℕ → Bool => ω i) bigCoins
      = Multiway.Multilinear.coin := Measure.infinitePi_map_eval _ i
  rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable
    ((measurable_of_finite g).aestronglyMeasurable)]

theorem integral_bigSign (i : ℕ) : ∫ ω, bigSign i ω ∂bigCoins = 0 := by
  have h := integral_bigCoins_eval (fun b => if b then (1 : ℝ) else -1) i
  rw [show (fun ω : ℕ → Bool => bigSign i ω) = fun ω => (if ω i then (1 : ℝ) else -1) from rfl,
    h, Multiway.Multilinear.integral_coin]
  norm_num

theorem iIndepFun_bigSign : iIndepFun (fun i : ℕ => bigSign i) bigCoins :=
  iIndepFun_infinitePi (X := fun (_ : ℕ) (b : Bool) => if b then (1 : ℝ) else -1)
    fun _ => measurable_of_finite _

/-- The observations of the `n`-th design: `n+1` clusters of two. -/
abbrev WrO (n : ℕ) := Fin (n + 1) × Fin 2

/-- The cluster labels of the `n`-th design. -/
abbrev WrL (n : ℕ) := Fin (n + 1)

/-- One maintained clustering dimension, `J = 1`. -/
abbrev WrD := Fin 1

def wrC (n : ℕ) : WrD → WrO n → WrL n := fun _ o => o.1

def wrDims : Finset WrD := Finset.univ

theorem wrDims_nonempty : wrDims.Nonempty := ⟨0, Finset.mem_univ _⟩

/-- The shocks, indexed injectively into `ℕ`: `3g` carries the cluster shock of cluster `g`, and
`3i+1`, `3i+2` the two idiosyncratic shocks of cluster `i`. -/
def wrIdx (n : ℕ) : ((WrD × WrL n) ⊕ WrO n) → ℕ
  | Sum.inl p => 3 * p.2.val
  | Sum.inr p => 3 * p.1.val + 1 + p.2.val

theorem wrIdx_injective (n : ℕ) : Function.Injective (wrIdx n) := by
  rintro (⟨j, g⟩ | ⟨i, t⟩) (⟨j', g'⟩ | ⟨i', t'⟩) h <;>
    simp only [wrIdx] at h
  · have hg : g = g' := Fin.ext (by omega)
    have hj : j = j' := Subsingleton.elim _ _
    rw [hg, hj]
  · exact absurd h (by have := t'.isLt; omega)
  · exact absurd h (by have := t.isLt; omega)
  · have ht := t.isLt
    have ht' := t'.isLt
    have hi : i = i' := Fin.ext (by omega)
    have h2 : t = t' := Fin.ext (by omega)
    rw [hi, h2]

noncomputable def wrZ (n : ℕ) : ((WrD × WrL n) ⊕ WrO n) → (ℕ → Bool) → ℝ :=
  fun s => bigSign (wrIdx n s)

theorem iIndepFun_wrZ (n : ℕ) : iIndepFun (wrZ n) bigCoins :=
  iIndepFun.precomp (g := wrIdx n) (wrIdx_injective n) iIndepFun_bigSign

theorem iCondIndepFun_wrZ (n : ℕ) : iCondIndepFun ⊥ bot_le (wrZ n) bigCoins :=
  Multiway.Sharing.iCondIndepFun_bot_of_iIndepFun (fun _ => measurable_bigSign _)
    (iIndepFun_wrZ n)

noncomputable def wrXt (n : ℕ) : Matrix (WrO n) (Fin 1) ℝ := fun _ _ => 1

/-- The mean projector, symmetric, idempotent, of trace `1`. -/
noncomputable def wrPr (n : ℕ) : Matrix (WrO n) (WrO n) ℝ :=
  fun _ _ => 1 / (Fintype.card (WrO n) : ℝ)

theorem wr_card (n : ℕ) : (Fintype.card (WrO n) : ℝ) = ((n : ℝ) + 1) * 2 := by
  simp only [WrO, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]

theorem wr_card_pos (n : ℕ) : (0 : ℝ) < (Fintype.card (WrO n) : ℝ) := by
  rw [wr_card]
  positivity

theorem wr_ne (n : ℕ) : Nonempty (WrO n) := ⟨(0, 0)⟩

theorem wr_cluster_card (n : ℕ) (j : WrD) (γ : WrL n) : (cluster (wrC n j) γ).card ≤ 2 := by
  classical
  have hsub : cluster (wrC n j) γ ⊆ ({(γ, 0), (γ, 1)} : Finset (WrO n)) := by
    intro o ho
    rw [mem_cluster] at ho
    obtain ⟨a, b⟩ := o
    have ha : a = γ := ho
    subst ha
    fin_cases b <;> simp
  calc (cluster (wrC n j) γ).card ≤ ({(γ, 0), (γ, 1)} : Finset (WrO n)).card :=
        Finset.card_le_card hsub
    _ ≤ 2 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp

theorem wr_linked (n : ℕ) (i : WrL n) :
    Multiway.Linked (wrC n) wrDims ((i, 0) : WrO n) ((i, 1) : WrO n) :=
  ⟨0, Finset.mem_univ _, rfl⟩

theorem wr_not_linked (n : ℕ) :
    ¬ Multiway.Linked (wrC (n + 1)) wrDims ((0, 0) : WrO (n + 1)) ((1, 0) : WrO (n + 1)) := by
  rintro ⟨j, -, hj⟩
  have h0 : (0 : Fin (n + 2)) = (1 : Fin (n + 2)) := hj
  have h2 : ((0 : Fin (n + 2)) : ℕ) = ((1 : Fin (n + 2)) : ℕ) := congrArg Fin.val h0
  simp at h2

theorem measurable_wrNu (n : ℕ) (o : WrO n) :
    Measurable (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o) := by
  have he : Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o
      = fun ω => (∑ j ∈ wrDims, wrZ n (Sum.inl (j, wrC n j o)) ω) + wrZ n (Sum.inr o) ω :=
    funext fun ω => Multiway.Sharing.nuRV_apply _ _ _ o ω
  rw [he]
  exact (Finset.measurable_sum _ fun j _ => measurable_bigSign _).add (measurable_bigSign _)

theorem abs_wrNu_le (n : ℕ) (o : WrO n) (ω : ℕ → Bool) :
    |Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω| ≤ 2 := by
  rw [Multiway.Sharing.nuRV_apply]
  have hs : (∑ j ∈ wrDims, wrZ n (Sum.inl (j, wrC n j o)) ω)
      = wrZ n (Sum.inl ((0 : WrD), wrC n 0 o)) ω := by
    simp [wrDims]
  rw [hs]
  calc |wrZ n (Sum.inl ((0 : WrD), wrC n 0 o)) ω + wrZ n (Sum.inr o) ω|
      ≤ |wrZ n (Sum.inl ((0 : WrD), wrC n 0 o)) ω| + |wrZ n (Sum.inr o) ω| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add (abs_bigSign_le _ _) (abs_bigSign_le _ _)
    _ = 2 := by norm_num

theorem integrable_wrNu_four (n : ℕ) (o : WrO n) :
    Integrable (fun ω => Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω ^ 4) bigCoins := by
  refine Integrable.mono' (integrable_const (16 : ℝ))
    (((measurable_wrNu n o).pow_const 4).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h4 : Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω ^ 4
      = |Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [h4]
  calc |Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω| ^ 4 ≤ (2 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_wrNu_le n o ω) 4
    _ = 16 := by norm_num

theorem wrXt_gram (n : ℕ) : (wrXt n)ᵀ * wrXt n
    = ((Fintype.card (WrO n) : ℝ)) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext k l
  fin_cases k
  fin_cases l
  simp [wrXt, Matrix.mul_apply, Matrix.transpose_apply]

theorem wrPr_isHermitian (n : ℕ) : (wrPr n).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext a b
  simp [wrPr, Matrix.conjTranspose_apply]

theorem wrPr_idem (n : ℕ) : wrPr n * wrPr n = wrPr n := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [wrPr]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Fintype.card (WrO n) : ℝ) ≠ 0 := ne_of_gt (wr_card_pos n)
  field_simp

theorem wrPr_trace (n : ℕ) : (wrPr n).trace = 1 + 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, wrPr]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Fintype.card (WrO n) : ℝ) ≠ 0 := ne_of_gt (wr_card_pos n)
  field_simp
  norm_num

theorem wrA_injective : Function.Injective ((1 : Matrix (Fin 1) (Fin 1) ℝ)).mulVec := by
  intro v w h
  simpa [Matrix.one_mulVec] using h

theorem wr_tendsto : Tendsto (fun n : ℕ => ((2 : ℕ) : ℝ) ^ 3 * (1 : ℝ)
    / (Fintype.card (WrO n) : ℝ)) atTop (𝓝 0) := by
  have he : (fun n : ℕ => ((2 : ℕ) : ℝ) ^ 3 * (1 : ℝ) / (Fintype.card (WrO n) : ℝ))
      = fun n : ℕ => 4 * (1 / ((n : ℝ) + 1)) := by
    funext n
    rw [wr_card]
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [he]
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 : ℝ)

theorem wr_tendsto' : Tendsto (fun n : ℕ => ((2 : ℕ) : ℝ) ^ 3
    / (Fintype.card (WrO n) : ℝ)) atTop (𝓝 0) := by
  simpa using wr_tendsto

/-- `Ω_{(i,0),(i,1)} = 1`: the two observations of a cluster share the cluster shock. -/
theorem wr_condOmega_offDiag (n : ℕ) (i : WrL n) :
    Multiway.Sharing.clusterOmega (wrC n) wrDims (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      ((i, 0) : WrO n) ((i, 1) : WrO n) = 1 := by
  rw [Multiway.Sharing.clusterOmega_apply]
  have h1 : ∀ j ∈ wrDims, (if Multiway.SameOn (wrC n) {j} ((i, 0) : WrO n) ((i, 1) : WrO n)
      then (1 : ℝ) else 0) = 1 := by
    intro j _
    rw [ite_eq_left]
    intro k _
    rfl
  rw [Finset.sum_congr rfl h1]
  simp [wrDims]

end RAWitness

section RAWitnessProofs

theorem wrZ_mean (n : ℕ) (s : (WrD × WrL n) ⊕ WrO n) :
    bigCoins[wrZ n s | ⊥] =ᵐ[bigCoins] 0 := by
  rw [condExp_bot]
  have h : ∫ ω, wrZ n s ω ∂bigCoins = 0 := integral_bigSign _
  rw [h]
  exact Filter.EventuallyEq.rfl

theorem wrZ_var_cluster (n : ℕ) (j : WrD) (g : WrL n) :
    bigCoins[wrZ n (Sum.inl (j, g)) * wrZ n (Sum.inl (j, g)) | ⊥]
      =ᵐ[bigCoins] fun _ => (1 : ℝ) := by
  rw [show wrZ n (Sum.inl (j, g)) * wrZ n (Sum.inl (j, g)) = fun _ => (1 : ℝ) from
    bigSign_mul_self _, condExp_const bot_le (1 : ℝ)]

theorem wrZ_var_idio (n : ℕ) (o : WrO n) :
    ∀ᵐ ω ∂bigCoins, (1 : ℝ) ≤ (bigCoins[wrZ n (Sum.inr o) * wrZ n (Sum.inr o) | ⊥]) ω := by
  rw [show wrZ n (Sum.inr o) * wrZ n (Sum.inr o) = fun _ => (1 : ℝ) from bigSign_mul_self _,
    condExp_const bot_le (1 : ℝ)]
  filter_upwards with ω
  exact le_refl 1

theorem wr_mom (n : ℕ) (o : WrO n) : ∀ᵐ ω ∂bigCoins,
    (bigCoins[fun ω => Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω ^ 4 | ⊥]
      : (ℕ → Bool) → ℝ) ω ≤ (16 : ℝ) := by
  have h := condExp_pow_four_le_of_bound (𝒟 := ⊥) bot_le (Cnu := 2)
    (abs_wrNu_le n o) (integrable_wrNu_four n o)
  have h16 : (2 : ℝ) ^ 4 = 16 := by norm_num
  filter_upwards [h] with ω hω
  rw [h16] at hω
  exact hω

/-- Vacuity witness for `clustershock_rateagnostic_a`. -/
theorem clustershock_rateagnostic_a_witness :
    TendstoInMeasure bigCoins (fun n ω =>
        rectFrobNorm ((sqrtPD ((wrXt n)ᵀ
              * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
              * wrXt n))⁻¹
          * (RateAgnostic.unionMeat (wrC n) wrDims (fun o k (_ : ℕ → Bool) => wrXt n o k)
                (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
              - (wrXt n)ᵀ
                * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
                * wrXt n)
          * (sqrtPD ((wrXt n)ᵀ
              * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
              * wrXt n))⁻¹))
        atTop (fun _ => 0)
      ∧ TendstoInMeasure bigCoins (fun n ω =>
        rectFrobNorm ((sqrtPD ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * ((wrXt n)ᵀ
                * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
                * wrXt n) * (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹
          * ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ
              * RateAgnostic.unionMeat (wrC n) wrDims (fun o k (_ : ℕ → Bool) => wrXt n o k)
                  (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
              * (1 : Matrix (Fin 1) (Fin 1) ℝ))
          * (sqrtPD ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * ((wrXt n)ᵀ
                * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
                * wrXt n) * (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ - 1))
        atTop (fun _ => 0) := by
  refine clustershock_rateagnostic_a (𝒟 := ⊥) bot_le wrC wrDims wrDims_nonempty wrZ
    (fun n s => measurable_bigSign _) (fun n s => memLp_bigSign _ _)
    iCondIndepFun_wrZ
    wrZ_mean (sc := fun _ _ => 1) (fun n j _ g => wrZ_var_cluster n j g)
    (s2 := 1) one_pos wrZ_var_idio (Cm := 16) (by norm_num) wr_mom
    wrXt (B := 1) zero_le_one ?_ (θ := 1) one_pos ?_ wr_ne (fun _ => 2)
    (fun n j _ γ => wr_cluster_card n j γ) wr_tendsto' (fun _ => 1) (fun _ => wrA_injective)
  · intro n o
    simp [wrXt]
  · intro n
    rw [one_mul, wrXt_gram]

/-- Vacuity witness for `clustershock_rateagnostic_b`, with `Π` the mean projector,
`d_{[Δ]} = 1` and `K = 0`. -/
theorem clustershock_rateagnostic_b_witness :
    TendstoInMeasure bigCoins (fun n ω =>
        rectFrobNorm ((sqrtPD ((wrXt n)ᵀ
              * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
              * wrXt n))⁻¹
          * (RateAgnostic.unionMeat (wrC n) wrDims (fun o k (_ : ℕ → Bool) => wrXt n o k)
                (fun o ω => Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω
                  - (wrPr n *ᵥ fun o' => Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o' ω) o) ω
              - (wrXt n)ᵀ
                * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
                * wrXt n)
          * (sqrtPD ((wrXt n)ᵀ
              * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
              * wrXt n))⁻¹))
        atTop (fun _ => 0)
      ∧ TendstoInMeasure bigCoins (fun n ω =>
        rectFrobNorm ((sqrtPD ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * ((wrXt n)ᵀ
                * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
                * wrXt n) * (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹
          * ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ
              * RateAgnostic.unionMeat (wrC n) wrDims (fun o k (_ : ℕ → Bool) => wrXt n o k)
                  (fun o ω => Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω
                    - (wrPr n *ᵥ fun o' =>
                        Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o' ω) o) ω
              * (1 : Matrix (Fin 1) (Fin 1) ℝ))
          * (sqrtPD ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * ((wrXt n)ᵀ
                * condOmegaMat ⊥ bigCoins (Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n)) ω
                * wrXt n) * (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ - 1))
        atTop (fun _ => 0)
      ∧ Tendsto (fun n => bigCoins {ω | ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ
          * RateAgnostic.unionMeat (wrC n) wrDims (fun o k (_ : ℕ → Bool) => wrXt n o k)
              (fun o ω => Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o ω
                - (wrPr n *ᵥ fun o' =>
                    Multiway.Sharing.nuRV (wrC n) wrDims (wrZ n) o' ω) o) ω
          * (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef}) atTop (𝓝 1) := by
  refine clustershock_rateagnostic_b (𝒟 := ⊥) bot_le wrC wrDims wrDims_nonempty wrZ
    (fun n s => measurable_bigSign _) (fun n s => memLp_bigSign _ _)
    iCondIndepFun_wrZ
    wrZ_mean (sc := fun _ _ => 1) (fun n j _ g => wrZ_var_cluster n j g)
    (s2 := 1) one_pos wrZ_var_idio (Cm := 16) (by norm_num) wr_mom
    wrXt (B := 1) one_pos ?_ (θ := 1) one_pos ?_ wr_ne
    wrPr (dd := fun _ => 1) (Kr := 0) le_rfl (fun _ => le_rfl)
    wrPr_isHermitian wrPr_idem wrPr_trace (fun _ => 2)
    (fun n j _ γ => wr_cluster_card n j γ) wr_tendsto (fun _ => 1) (fun _ => wrA_injective)
  · intro n o
    simp [wrXt]
  · intro n
    rw [one_mul, wrXt_gram]

end RAWitnessProofs

/-! ## General `J` with a random design, under the full measure

The forms of `clustershock_a_general` and `clustershock_b_general` with a `𝒟`-measurable random
design, hypotheses read under `ℙ_ω` at `P`-almost every `ω`, and conclusions under `P`, together
with the `r`-dimensional law `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)`. The rate is `Ḡ_n⁴/n → 0`. -/

section GeneralUnconditional

/-- The almost-everywhere facts shared by the general-`J` unconditional forms: the degree bound
with `D_n(ω) := min{JḠ_n(ω), n}`, `D_n ≥ 1`, the floor `Ω_n ⪰ σ̲²θnI_K`, and the rate
`(n/D_n)^{1/3}δ_n → 0`. -/
theorem clustershock_general_uncond_package
    {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Dm : Type*} [DecidableEq Dm]
    {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (ν : ∀ n, O n → Ω → ℝ)
    (c : ∀ n, Ω → Dm → O n → L n) (dims : Finset Dm)
    (sc : ℕ → Ω → Dm → ℝ) (ve : ∀ n, Ω → O n → ℝ)
    {s2 θ : ℝ} (hs2 : 0 < s2) (hθ : 0 < θ) (Gb : ℕ → Ω → ℕ)
    (hne : ∀ n, Nonempty (O n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n ω) dims o o')
    (hsc : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, 0 ≤ sc n ω j)
    (hve : ∀ᵐ ω ∂P, ∀ n o, s2 ≤ ve n ω o)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => (Gb n ω : ℝ) ^ 4 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P,
      (∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
        ∀ n o, ((Dv n).nbhd o).card ≤ min (dims.card * Gb n ω) (Fintype.card (O n)) + 1)
      ∧ (∀ n, 1 ≤ min (dims.card * Gb n ω) (Fintype.card (O n)))
      ∧ (∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
          ≤ scoreVar (Xt n ω) (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)))
      ∧ Tendsto (fun n => steinRate (Fintype.card (O n))
          (min (dims.card * Gb n ω) (Fintype.card (O n)))
          ((s2 * θ) * (Fintype.card (O n) : ℝ))) atTop (𝓝 0) := by
  classical
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  filter_upwards [hdep, hsc, hve, hdesign, hGb, hGrate]
    with ω hdepω hscω hveω hdesω hGbω hGrω
  obtain ⟨Dv, hshareω⟩ := hdepω
  have hfloorOm : ∀ n, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) :=
    fun n => Multiway.Sharing.smul_one_le_clusterOmega (hscω n) (hveω n)
  have hfloorK : ∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n ω) (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) := by
    intro n
    have h1 : s2 • ((θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ))
        ≤ s2 • ((Xt n ω)ᵀ * Xt n ω) := Multiway.loewner_smul_le_smul hs2.le (hdesω n)
    rw [smul_smul, ← mul_assoc] at h1
    exact h1.trans (Multiway.Sharing.smul_transpose_mul_self_le_conj (hfloorOm n) (Xt n ω))
  have hnbhd : ∀ n o, (Dv n).nbhd o = Multiway.Sharing.closedNbhd (c n ω) dims o := by
    intro n o
    ext o'
    rw [DepGraph.mem_nbhd_iff, Multiway.Sharing.mem_closedNbhd]
    exact hshareω n o o'
  have hdegF : ∀ n o, ((Dv n).nbhd o).card
      ≤ min (dims.card * Gb n ω) (Fintype.card (O n)) := by
    intro n o
    refine le_min ?_ ?_
    · rw [hnbhd n o]; exact card_closedNbhd_le_mul (hGbω n) o
    · exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  have hDn1 : ∀ n, 1 ≤ min (dims.card * Gb n ω) (Fintype.card (O n)) := by
    intro n
    obtain ⟨o⟩ := hne n
    refine le_trans ?_ (hdegF n o)
    exact Finset.card_pos.mpr ⟨o, (Dv n).self_mem_nbhd o⟩
  refine ⟨⟨Dv, fun n o => le_trans (hdegF n o) (Nat.le_succ _)⟩, hDn1, hfloorK, ?_⟩
  exact tendsto_steinRate_of_cluster_size (mul_pos hs2 hθ) (fun n => hcard n)
    hDn1 (fun n => min_le_left _ _) hGrω

/-- **Corollary SM.D.3, bounded shocks, general `J`, random design.** The statement of
`clustershock_a_general` with the design, cluster maps and variances functions of `ω`, hypotheses
under `ℙ_ω` for `P`-almost every `ω`, and the limit law under `P`. -/
theorem clustershock_a_general_unconditional
    {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Dm : Type*} [DecidableEq Dm]
    {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Ω → Dm → O n → L n) (dims : Finset Dm)
    (sc : ℕ → Ω → Dm → ℝ) (ve : ∀ n, Ω → O n → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω =>
      Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (s2 : ℝ) (hs2 : 0 < s2) (θ : ℝ) (hθ : 0 < θ) (Gb : ℕ → Ω → ℕ)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1)
    (hWm : ∀ n, Measurable fun y => b ⬝ᵥ
      ((sqrtPD (restrictedVar (Xt n y)
          (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n))))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n ω) dims o o')
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hsc : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, 0 ≤ sc n ω j)
    (hve : ∀ᵐ ω ∂P, ∀ n o, s2 ≤ ve n ω o)
    (hOm : ∀ᵐ ω ∂P, ∀ n o o', ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω)
      = Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hne : ∀ n, Nonempty (O n))
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => (Gb n ω : ℝ) ^ 4 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y)
            (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hpkg := clustershock_general_uncond_package (𝒟 := 𝒟) P Xt ν c dims sc ve hs2 hθ Gb hne
    hdep hsc hve hdesign hGb hGrate
  exact cltcluster_a_general_betaJM_unconditional h𝒟 P Xt
    (fun n ω => Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) Rn ν bhat β
    hXtD hOmD hscore
    (fun n _ => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n ω => min (dims.card * Gb n ω) (Fintype.card (O n)))
    B Cnu hB0 hCnu0 hnu b hb hWm
    (hpkg.mono fun _ h => h.1) hA
    (Filter.Eventually.of_forall fun _ n =>
      mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n))
    (hpkg.mono fun _ h => h.2.2.1) hOm hmean hB
    (hpkg.mono fun _ h => h.2.1)
    (Filter.Eventually.of_forall fun _ _ => min_le_right _ _)
    (hpkg.mono fun _ h => h.2.2.2)

/-- **Corollary SM.D.3, bounded fourth moments, general `J`, random design.** The statement of
`clustershock_b_general` with hypotheses under `ℙ_ω` for `P`-almost every `ω` and the limit law
under `P`. -/
theorem clustershock_b_general_unconditional
    {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Dm : Type*} [DecidableEq Dm]
    {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Rn : ℕ → Matrix r K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Ω → Dm → O n → L n) (dims : Finset Dm)
    (sc : ℕ → Ω → Dm → ℝ) (ve : ∀ n, Ω → O n → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω =>
      Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (s2 : ℝ) (hs2 : 0 < s2) (θ : ℝ) (hθ : 0 < θ) (Gb : ℕ → Ω → ℕ)
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1)
    (hWm : ∀ n, Measurable fun y => b ⬝ᵥ
      ((sqrtPD (restrictedVar (Xt n y)
          (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
        (Rn n *ᵥ (bhat n y - β n))))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n ω) dims o o')
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hsc : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, 0 ≤ sc n ω j)
    (hve : ∀ᵐ ω ∂P, ∀ n o, s2 ≤ ve n ω o)
    (hOm : ∀ᵐ ω ∂P, ∀ n o o', ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω)
      = Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hint4 : ∀ᵐ ω ∂P, ∀ n o, Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hne : ∀ n, Nonempty (O n))
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => (Gb n ω : ℝ) ^ 4 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y)
            (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hpkg := clustershock_general_uncond_package (𝒟 := 𝒟) P Xt ν c dims sc ve hs2 hθ Gb hne
    hdep hsc hve hdesign hGb hGrate
  exact cltcluster_b_general_betaJM_unconditional h𝒟 P Xt
    (fun n ω => Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) Rn ν bhat β
    hXtD hOmD hscore
    (fun n _ => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n ω => min (dims.card * Gb n ω) (Fintype.card (O n)))
    B C4 hB0 hC40 b hb hWm
    (hpkg.mono fun _ h => h.1) hA
    (Filter.Eventually.of_forall fun _ n =>
      mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n))
    (hpkg.mono fun _ h => h.2.2.1) hOm hmean hB hint4 hfour
    (hpkg.mono fun _ h => h.2.1)
    (Filter.Eventually.of_forall fun _ _ => min_le_right _ _)
    (hpkg.mono fun _ h => h.2.2.2)

/-- `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)` under `P` at a random design, at general `J`. -/
theorem clustershock_a_general_unconditional_vector
    {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {Dm : Type*} [DecidableEq Dm]
    {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (h𝒟 : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Rn : ℕ → Matrix rr K ℝ)
    (ν : ∀ n, O n → Ω → ℝ) (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (c : ∀ n, Ω → Dm → O n → L n) (dims : Finset Dm)
    (sc : ℕ → Ω → Dm → ℝ) (ve : ∀ n, Ω → O n → ℝ)
    (hXtD : ∀ n o k, Measurable[𝒟] fun ω => Xt n ω o k)
    (hOmD : ∀ n o o', Measurable[𝒟] fun ω =>
      Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hscore : ∀ n y, bhat n y - β n
      = ((Xt n y)ᵀ * Xt n y)⁻¹ *ᵥ ((Xt n y)ᵀ *ᵥ (fun o => ν n o y)))
    (s2 : ℝ) (hs2 : 0 < s2) (θ : ℝ) (hθ : 0 < θ) (Gb : ℕ → Ω → ℕ)
    (B Cnu : ℝ) (hB0 : 0 ≤ B) (hCnu0 : 0 ≤ Cnu)
    (hnu : ∀ n o y, |ν n o y| ≤ Cnu)
    (hWvm : ∀ n, Measurable fun y =>
      restrictedStat (Xt n y)
        (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)
        (bhat n y - β n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n ω) dims o o')
    (hA : ∀ᵐ ω ∂P, ∀ n, Function.Injective (scoreMap (Xt n ω) (Rn n)).mulVec)
    (hsc : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, 0 ≤ sc n ω j)
    (hve : ∀ᵐ ω ∂P, ∀ n o, s2 ≤ ve n ω o)
    (hOm : ∀ᵐ ω ∂P, ∀ n o o', ∫ y, ν n o y * ν n o' y ∂(condExpKernel P 𝒟 ω)
      = Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω) o o')
    (hmean : ∀ᵐ ω ∂P, ∀ n o, ∫ y, ν n o y ∂(condExpKernel P 𝒟 ω) = 0)
    (hB : ∀ᵐ ω ∂P, ∀ n o, (fun k => Xt n ω o k) ⬝ᵥ (fun k => Xt n ω o k) ≤ B ^ 2)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hne : ∀ n, Nonempty (O n))
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGrate : ∀ᵐ ω ∂P,
      Tendsto (fun n => (Gb n ω : ℝ) ^ 4 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y)
        (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)
        (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hpkg := clustershock_general_uncond_package (𝒟 := 𝒟) P Xt ν c dims sc ve hs2 hθ Gb hne
    hdep hsc hve hdesign hGb hGrate
  exact cltcluster_a_general_betaJM_unconditional_vector h𝒟 P Xt
    (fun n ω => Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) Rn ν bhat β
    hXtD hOmD hscore
    (fun n _ => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n ω => min (dims.card * Gb n ω) (Fintype.card (O n)))
    B Cnu hB0 hCnu0 hnu hWvm
    (hpkg.mono fun _ h => h.1) hA
    (Filter.Eventually.of_forall fun _ n =>
      mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n))
    (hpkg.mono fun _ h => h.2.2.1) hOm hmean hB
    (hpkg.mono fun _ h => h.2.1)
    (Filter.Eventually.of_forall fun _ _ => min_le_right _ _)
    (hpkg.mono fun _ h => h.2.2.2)

end GeneralUnconditional

/-! ## The Wald step

Theorem 11(c) for the cluster-shock model, obtained by chaining the vector limit law with the
ratio limit `𝒱_n^{-1/2}𝒱̂_n𝒱_n^{-1/2} ⟶ᵖ I_r` through `Multiway.Wald.wald_of_clt_rateAgnostic`. -/

section WaldStep

open Matrix

/-- **Corollary SM.D.3, Theorem 11(c) for the cluster-shock model.** If
`‖𝒱_n^{-1/2}𝒱̂_n𝒱_n^{-1/2} − I_r‖_F ⟶ᵖ 0` and `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)`, then
`P(𝒱̂_n ≻ 0) → 1`, `𝒱̂_n^{-1/2}𝓡_n(β̂ − β) ⟶ᵈ N(0, I_r)`, and `𝒲 ⟶ᵈ χ²_r`. -/
theorem clustershock_rateagnostic_c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
    {K : Type*} [Fintype K] [DecidableEq K]
    {r : Type*} [Fintype r] [DecidableEq r]
    (Xt : ∀ n, Ω → Matrix (O n) K ℝ) (Om : ∀ n, Ω → Matrix (O n) (O n) ℝ)
    (Rn : ℕ → Matrix r K ℝ) (dv : ℕ → Ω → (K → ℝ)) (Vh : ℕ → Ω → Matrix r r ℝ)
    (hV : ∀ n ω, (restrictedVar (Xt n ω) (Om n ω) (Rn n)).PosDef)
    (hVmeas : ∀ n, Measurable fun ω => restrictedVar (Xt n ω) (Om n ω) (Rn n))
    (hVhherm : ∀ n ω, (Vh n ω).IsHermitian) (hVhmeas : ∀ n, Measurable (Vh n))
    (hratio : TendstoInMeasure P (fun n ω => rectFrobNorm
        ((sqrtPD (restrictedVar (Xt n ω) (Om n ω) (Rn n)))⁻¹ * Vh n ω
          * (sqrtPD (restrictedVar (Xt n ω) (Om n ω) (Rn n)))⁻¹ - 1)) atTop (fun _ => 0))
    (hclt : TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n ω => restrictedStat (Xt n ω) (Om n ω) (Rn n) (dv n ω)) atTop
      (id : EuclideanSpace ℝ r → EuclideanSpace ℝ r) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ r))) :
    Tendsto (fun n => P {ω | (Vh n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (Vh n ω))⁻¹)
            (WithLp.toLp 2 (Rn n *ᵥ dv n ω) : EuclideanSpace ℝ r)) atTop
          (id : EuclideanSpace ℝ r → EuclideanSpace ℝ r) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ r))
      ∧ TendstoInDistribution
          (fun n ω => Multiway.Wald.waldStat (Vh n ω)
            (WithLp.toLp 2 (Rn n *ᵥ dv n ω) : EuclideanSpace ℝ r)) atTop
          (fun z : EuclideanSpace ℝ r => ‖z‖ ^ 2) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ r)) := by
  have hmain := Multiway.Wald.wald_of_clt_rateAgnostic (P := P)
    (P' := stdGaussian (EuclideanSpace ℝ r))
    (V := fun n ω => restrictedVar (Xt n ω) (Om n ω) (Rn n)) hV hVmeas
    (Vh := Vh) hVhherm hVhmeas hratio
    (x := fun n ω => (WithLp.toLp 2 (Rn n *ᵥ dv n ω) : EuclideanSpace ℝ r))
    (G := id) hclt (by rw [Measure.map_id, multivariateGaussian_zero_one])
  simp only [multivariateGaussian_zero_one] at hmain
  exact hmain

end WaldStep

/-! ### A sum of independent fair shocks on a single probability space

Witness infrastructure: `ν_o = ∑_k s_{idx(o,k)}` on `Aw = Bool × ((ℕ × ℕ) → Bool)`, which carries
the whole sequence of designs. -/

section CoinShockSum

open Multiway.SteinCluster.FrozenDesignWitness

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def coinShockSum (idx : O → κ → ℕ × ℕ) (o : O) (z : Cw) : ℝ :=
  ∑ k : κ, coinSign (idx o k) z

noncomputable def coinShockSumA (idx : O → κ → ℕ × ℕ) (o : O) (y : Aw) : ℝ :=
  coinShockSum idx o y.2

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem measurable_coinShockSum (idx : O → κ → ℕ × ℕ) (o : O) :
    Measurable (coinShockSum idx o) :=
  Finset.measurable_sum _ fun _ _ => meas_coinSign _

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem measurable_coinShockSumA (idx : O → κ → ℕ × ℕ) (o : O) :
    Measurable (coinShockSumA idx o) :=
  (measurable_coinShockSum idx o).comp measurable_snd

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem abs_coinShockSum_le (idx : O → κ → ℕ × ℕ) (o : O) (z : Cw) :
    |coinShockSum idx o z| ≤ (Fintype.card κ : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun k _ => abs_coinSign_le (idx o k) z)) ?_
  simp [Finset.card_univ]

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem abs_coinShockSumA_le (idx : O → κ → ℕ × ℕ) (o : O) (y : Aw) :
    |coinShockSumA idx o y| ≤ (Fintype.card κ : ℝ) :=
  abs_coinShockSum_le idx o y.2

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem integral_coinShockSum (idx : O → κ → ℕ × ℕ) (o : O) :
    ∫ z, coinShockSum idx o z ∂P1 = 0 := by
  unfold coinShockSum
  rw [integral_finsetSum _ (fun k _ => integrable_coinSign _)]
  simp [integral_coinSign]

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem integral_coinShockSum_mul {idx : O → κ → ℕ × ℕ}
    (hinj : ∀ o o' : O, ∀ k k' : κ, idx o k = idx o' k' → k = k') (o o' : O) :
    ∫ z, coinShockSum idx o z * coinShockSum idx o' z ∂P1
      = ∑ k : κ, (if idx o k = idx o' k then (1 : ℝ) else 0) := by
  have hexp : (fun z => coinShockSum idx o z * coinShockSum idx o' z)
      = fun z => ∑ k : κ, ∑ k' : κ, coinSign (idx o k) z * coinSign (idx o' k') z := by
    funext z
    simp only [coinShockSum]
    rw [Finset.sum_mul_sum]
  rw [hexp, integral_finsetSum _
    (fun k _ => integrable_finsetSum _ (fun k' _ => integrable_coinSign_mul _ _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ (fun k' _ => integrable_coinSign_mul _ _)]
  have hsingle : (∑ k' : κ, ∫ z, coinSign (idx o k) z * coinSign (idx o' k') z ∂P1)
      = ∫ z, coinSign (idx o k) z * coinSign (idx o' k) z ∂P1 := by
    refine Finset.sum_eq_single_of_mem k (Finset.mem_univ k) ?_
    intro k' _ hk'
    rw [integral_coinSign_mul]
    exact ite_eq_right fun heq => hk' (hinj o o' k k' heq).symm
  rw [hsingle, integral_coinSign_mul]

def coinShockIdxSet (idx : O → κ → ℕ × ℕ) (A : Finset O) : Finset (ℕ × ℕ) :=
  A.biUnion fun o => Finset.univ.image (idx o)

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem mem_coinShockIdxSet {idx : O → κ → ℕ × ℕ} {A : Finset O} {o : O} (ho : o ∈ A) (k : κ) :
    idx o k ∈ coinShockIdxSet idx A :=
  Finset.mem_biUnion.mpr ⟨o, ho, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩

noncomputable def coinShockRebuild (idx : O → κ → ℕ × ℕ) (A : Finset O) (S : Finset (ℕ × ℕ))
    (t : ↥S → ℝ) (o : ↥A) : ℝ :=
  ∑ k : κ, (if h : idx (o : O) k ∈ S then t ⟨idx (o : O) k, h⟩ else 0)

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem measurable_coinShockRebuild (idx : O → κ → ℕ × ℕ) (A : Finset O) (S : Finset (ℕ × ℕ)) :
    Measurable (coinShockRebuild idx A S) := by
  refine Measurable.of_eval fun o => ?_
  simp only [coinShockRebuild]
  refine Finset.measurable_sum _ fun k _ => ?_
  by_cases h : idx (o : O) k ∈ S
  · simp only [dite_eq_left h]
    exact measurable_pi_apply _
  · simp only [dite_eq_right h]
    exact measurable_const

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem coinShockRebuild_comp (idx : O → κ → ℕ × ℕ) (A : Finset O) :
    coinShockRebuild idx A (coinShockIdxSet idx A)
        ∘ (fun z (i : ↥(coinShockIdxSet idx A)) => coinSign (i : ℕ × ℕ) z)
      = fun z => fun o : ↥A => coinShockSum idx (o : O) z := by
  funext z o
  simp only [Function.comp_apply, coinShockRebuild, coinShockSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dite_eq_left (mem_coinShockIdxSet o.2 k)]

noncomputable def coinShockDep {μ : Measure Aw} [IsProbabilityMeasure μ]
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1)
    (idx : O → κ → ℕ × ℕ) (G : O → O → Prop) [DecidableRel G]
    (hrefl : ∀ o, G o o) (hsymm : ∀ o o', G o o' → G o' o)
    (hdisj : ∀ o o', ¬ G o o' → ∀ k k' : κ, idx o k ≠ idx o' k') :
    DepGraph (coinShockSumA idx) μ where
  G := G
  decG := inferInstance
  refl := hrefl
  symm := hsymm
  meas := measurable_coinShockSumA idx
  indep := by
    intro A Bs hsep
    have hdisjoint : Disjoint (coinShockIdxSet idx A) (coinShockIdxSet idx Bs) := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      simp only [coinShockIdxSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
        true_and] at hxA hxB
      obtain ⟨a, ha, k, hk⟩ := hxA
      obtain ⟨d, hd, k', hk'⟩ := hxB
      exact hdisj a d (hsep a ha d hd) k k' (hk.trans hk'.symm)
    have h0 := indep_coinSign.indepFun_finset (coinShockIdxSet idx A) (coinShockIdxSet idx Bs)
      hdisjoint meas_coinSign
    have key := h0.comp (measurable_coinShockRebuild idx A (coinShockIdxSet idx A))
      (measurable_coinShockRebuild idx Bs (coinShockIdxSet idx Bs))
    rw [coinShockRebuild_comp, coinShockRebuild_comp] at key
    exact indepFun_of_snd
      (F := fun z : Cw => fun o : ↥A => coinShockSum idx (o : O) z)
      (G := fun z : Cw => fun o : ↥Bs => coinShockSum idx (o : O) z) hmap
      (Measurable.of_eval fun o : ↥A => measurable_coinShockSum idx (o : O))
      (Measurable.of_eval fun o : ↥Bs => measurable_coinShockSum idx (o : O)) key

end CoinShockSum

/-! ### Vacuity witnesses for the general-`J` random-design and Wald forms

At index `n` there are `n+3` observations with clustering maps `g^{(1)}(o) = ⌊o/2⌋` and
`g^{(2)}(o) = ⌊(o+1)/2⌋`; component `k` of observation `o` reads coin `(n, 3·label_k(o) + k)`, so
`ν_o = c^{(1)}_{g₁(o)} + c^{(2)}_{g₂(o)} + ε_o` with fair signs. The regressor is `x̃_o = ±1` with
the sign read off the design coin, `𝓡_n = I_1`, and `Ḡ_n⁴/n = 16/(n+3) → 0`. The variance
estimator of the Wald witness is `𝒱_n` inflated by `1 + 1/(n+1)`. -/

section FrozenGeneralShockWitness

namespace FrozenGeneralShockWitness

open Multiway.SteinCluster.FrozenDesignWitness
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- Component `k` of observation `o` at index `n` reads coin `(n, 3·label + k)`. -/
def gcIdx (n : ℕ) (o : Fin (n + 3)) (k : Fin 3) : ℕ × ℕ := (n, 3 * wtLab n o k + k.val)

theorem gcIdx_component (n : ℕ) (o o' : Fin (n + 3)) (k k' : Fin 3)
    (h : gcIdx n o k = gcIdx n o' k') : k = k' := by
  have h1 := congrArg Prod.snd h
  simp only [gcIdx] at h1
  have h2 := k.isLt
  have h3 := k'.isLt
  exact Fin.ext (by omega)

theorem gcIdx_eq_iff (n : ℕ) (o o' : Fin (n + 3)) (k : Fin 3) :
    gcIdx n o k = gcIdx n o' k ↔ wtLab n o k = wtLab n o' k := by
  constructor
  · intro h
    have h1 := congrArg Prod.snd h
    simp only [gcIdx] at h1
    omega
  · intro h
    simp only [gcIdx, h]

theorem gcIdx_ne_of_not_linked (n : ℕ) (o o' : Fin (n + 3))
    (h : ¬ Multiway.Linked (wtC n) Finset.univ o o') (k k' : Fin 3) :
    gcIdx n o k ≠ gcIdx n o' k' := by
  intro heq
  have hkk := gcIdx_component n o o' k k' heq
  subst hkk
  have hlab := (gcIdx_eq_iff n o o' k).mp heq
  refine h ?_
  fin_cases k
  · exact ⟨0, Finset.mem_univ 0, (wtLab_eq_zero_iff n o o').mp hlab⟩
  · exact ⟨1, Finset.mem_univ 1, (wtLab_eq_one_iff n o o').mp hlab⟩
  · have hoo : o = o' := (wtLab_eq_two_iff n o o').mp hlab
    exact ⟨0, Finset.mem_univ 0, by rw [hoo]⟩

/-- The second moments of the disturbance are the entries of `clusterOmega`. -/
theorem gc_hOm (n : ℕ) (o o' : Fin (n + 3)) :
    ∫ z, coinShockSum (gcIdx n) o z * coinShockSum (gcIdx n) o' z ∂P1
      = Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)) o o' := by
  rw [integral_coinShockSum_mul (gcIdx_component n), Multiway.Sharing.clusterOmega_apply,
    Fin.sum_univ_three, Fin.sum_univ_two]
  have e0 : (gcIdx n o 0 = gcIdx n o' 0) ↔ Multiway.SameOn (wtC n) {0} o o' := by
    rw [gcIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_zero_iff]
  have e1 : (gcIdx n o 1 = gcIdx n o' 1) ↔ Multiway.SameOn (wtC n) {1} o o' := by
    rw [gcIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_one_iff]
  have e2 : (gcIdx n o 2 = gcIdx n o' 2) ↔ (o = o') := by
    rw [gcIdx_eq_iff, wtLab_eq_two_iff]
  rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl, if_congr e2 rfl rfl]

noncomputable def gcDep {μ : Measure Aw} [IsProbabilityMeasure μ]
    (hmap : Measure.map (Prod.snd : Aw → Cw) μ = P1) (n : ℕ) :
    DepGraph (coinShockSumA (gcIdx n)) μ :=
  coinShockDep hmap (gcIdx n) (Multiway.Linked (wtC n) Finset.univ)
    (fun _ => ⟨0, Finset.mem_univ 0, rfl⟩)
    (fun _ _ h => Multiway.Sharing.linked_symm h)
    (gcIdx_ne_of_not_linked n)

/-- The design at index `n`: the all-ones regressor over `n+3` observations, with the sign of
the design coin. -/
noncomputable def gcXt (n : ℕ) (y : Aw) : Matrix (Fin (n + 3)) (Fin 1) ℝ :=
  sgnA y • redXt (n + 2)

noncomputable def gcBhat (n : ℕ) (y : Aw) : Fin 1 → ℝ :=
  ((gcXt n y)ᵀ * gcXt n y)⁻¹ *ᵥ ((gcXt n y)ᵀ *ᵥ (fun o => coinShockSumA (gcIdx n) o y))

theorem gc_hXtD (n : ℕ) (o : Fin (n + 3)) (k : Fin 1) :
    Measurable[Dw] fun y => gcXt n y o k := by
  have : (fun y : Aw => gcXt n y o k) = fun y => sgnA y * 1 := rfl
  rw [this]
  exact meas_sgnA.mul_const 1

theorem gc_hPD (n : ℕ) :
    (scoreVar (redXt (n + 2)) (Multiway.Sharing.clusterOmega (wtC n) Finset.univ
      (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)))).PosDef := by
  have hfloorOm : (1 : ℝ) • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
      ≤ Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)) :=
    Multiway.Sharing.smul_one_le_clusterOmega (fun _ _ => zero_le_one) (fun _ => le_refl 1)
  have h2 := Multiway.Sharing.smul_transpose_mul_self_le_conj hfloorOm (redXt (n + 2))
  rw [one_smul, redXt_transpose_mul_self] at h2
  exact Multiway.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one
    (show (0 : ℝ) < (((n + 2 : ℕ) : ℝ) + 1) by positivity)) h2

theorem gc_statistic (n : ℕ) :
    (fun y : Aw => wb ⬝ᵥ
        ((sqrtPD (restrictedVar (gcXt n y)
            (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
              (fun _ => (1 : ℝ)))
            (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gcBhat n y - (0 : Fin 1 → ℝ)))))
      = fun y => sgnA y *
          depSum (scoreArray (redXt (n + 2))
            (steinWeight (redXt (n + 2))
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
                (fun _ => (1 : ℝ)))
              (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSumA (gcIdx n))) y := by
  funext y
  rw [show gcBhat n y - (0 : Fin 1 → ℝ)
      = ((gcXt n y)ᵀ * gcXt n y)⁻¹ *ᵥ
        ((gcXt n y)ᵀ *ᵥ (fun o => coinShockSumA (gcIdx n) o y)) from sub_zero _,
    dotProduct_standardized_eq_depSum,
    show gcXt n y = sgnA y • redXt (n + 2) from rfl,
    steinWeight_smul (sgnA_mul y), depSum_scoreArray_smul]

theorem gc_hWm (n : ℕ) : Measurable fun y : Aw => wb ⬝ᵥ
    ((sqrtPD (restrictedVar (gcXt n y)
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gcBhat n y - (0 : Fin 1 → ℝ)))) := by
  rw [gc_statistic n]
  exact (meas_sgnA.mono Dw_le le_rfl).mul
    (Finset.measurable_sum _ fun o _ => (measurable_coinShockSumA (gcIdx n) o).const_mul _)

theorem gc_total_variance (n : ℕ) :
    ∫ z, (depSum (scoreArray (redXt (n + 2))
      (steinWeight (redXt (n + 2))
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSum (gcIdx n))) z) ^ 2 ∂P1 = 1 :=
  integral_depSum_scoreArray_sq_eq_one (gc_hPD n) (redXt_scoreMap_isUnit (n + 2))
    (measurable_coinShockSum (gcIdx n)) (fun o z => abs_coinShockSum_le (gcIdx n) o z)
    (gc_hOm n) wb_dot

theorem gc_total_variance_cond :
    ∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2))
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSumA (gcIdx n))) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n
  have hmeas : Measurable fun z : Cw => (depSum (scoreArray (redXt (n + 2))
      (steinWeight (redXt (n + 2))
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSum (gcIdx n))) z) ^ 2 :=
    (Finset.measurable_sum _ fun o _ =>
      (measurable_coinShockSum (gcIdx n) o).const_mul _).pow_const 2
  exact (integral_of_snd hω hmeas).trans (gc_total_variance n)

/-- The within-cluster covariance is `1` under `ℙ_ω`. -/
theorem gc_within_cond :
    ∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, coinShockSumA (gcIdx n) ⟨0, by omega⟩ y
        * coinShockSumA (gcIdx n) ⟨1, by omega⟩ y ∂(condExpKernel Pw Dw ω) = 1 := by
  filter_upwards [map_snd_condExpKernel] with ω hω n
  refine (integral_of_snd hω ((measurable_coinShockSum (gcIdx n) ⟨0, by omega⟩).mul
    (measurable_coinShockSum (gcIdx n) ⟨1, by omega⟩))).trans ?_
  simp only [Pi.mul_apply]
  rw [gc_hOm n]
  exact wtOmega_offDiag n

theorem gc_pow_four_le (n : ℕ) (o : Fin (n + 3)) (z : Cw) :
    (coinShockSum (gcIdx n) o z) ^ 4 ≤ (3 : ℝ) ^ 4 := by
  have h := abs_coinShockSum_le (gcIdx n) o z
  have h3 : |coinShockSum (gcIdx n) o z| ≤ 3 := by simpa using h
  have habs : (coinShockSum (gcIdx n) o z) ^ 4 = |coinShockSum (gcIdx n) o z| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [habs]
  exact pow_le_pow_left₀ (abs_nonneg _) h3 4

theorem gc_hGrate : Tendsto (fun n : ℕ => (((2 : ℕ) : ℝ)) ^ 4 / ((n + 3 : ℕ) : ℝ))
    atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop := by
    have hcast : ∀ n : ℕ, ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := fun n => by push_cast; ring
    simp only [hcast]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa using (tendsto_const_nhds (x := (((2 : ℕ) : ℝ)) ^ 4) (f := atTop (α := ℕ))).div_atTop hd

theorem gc_vectorStat (n : ℕ) :
    (fun y : Aw => restrictedStat (gcXt n y)
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (gcBhat n y - (0 : Fin 1 → ℝ)))
      = fun y => (WithLp.toLp 2
          ![wb ⬝ᵥ ((sqrtPD (restrictedVar (gcXt n y)
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
                (fun _ => (1 : ℝ)))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gcBhat n y - (0 : Fin 1 → ℝ))))]
          : EuclideanSpace ℝ (Fin 1)) := by
  funext y
  refine congrArg (WithLp.toLp 2) ?_
  funext k
  fin_cases k
  simp [wb, dotProduct]

theorem gc_hWvm (n : ℕ) : Measurable fun y : Aw =>
    restrictedStat (gcXt n y)
      (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
        (fun _ => (1 : ℝ)))
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (gcBhat n y - (0 : Fin 1 → ℝ)) := by
  rw [gc_vectorStat n]
  exact (by fun_prop : Measurable
    (fun x : ℝ => (WithLp.toLp 2 ![x] : EuclideanSpace ℝ (Fin 1)))).comp (gc_hWm n)

/-- Vacuity witness for `clustershock_a_general_unconditional`. -/
theorem clustershock_a_general_unconditional_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), gcXt n y = (if y.1 then (1 : ℝ) else -1) • redXt (n + 2))
    ∧ (∀ n : ℕ, ∃ a b d : Fin (n + 3),
        Multiway.Linked (wtC n) Finset.univ a b
        ∧ Multiway.Linked (wtC n) Finset.univ b d
        ∧ ¬ Multiway.Linked (wtC n) Finset.univ a d)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, coinShockSumA (gcIdx n) ⟨0, by omega⟩ y
        * coinShockSumA (gcIdx n) ⟨1, by omega⟩ y ∂(condExpKernel Pw Dw ω) = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2))
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSumA (gcIdx n))) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => wb ⬝ᵥ
          ((sqrtPD (restrictedVar (gcXt n y)
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
                (fun _ => (1 : ℝ)))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gcBhat n y - (0 : Fin 1 → ℝ)))))
        atTop (id : ℝ → ℝ) (fun _ => Pw) (gaussianReal 0 1) := by
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ => rfl,
    wtLinked_not_transitive, gc_within_cond, gc_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine clustershock_a_general_unconditional (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    Dw_le Pw gcXt (fun _ => 1) (fun n => coinShockSumA (gcIdx n)) gcBhat (fun _ => 0)
    (fun n _ => wtC n) Finset.univ (fun _ _ _ => 1) (fun _ _ _ => 1)
    gc_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    1 zero_lt_one 1 zero_lt_one (fun _ _ => 2)
    1 3 zero_le_one (by norm_num)
    (fun n o y => by simpa using abs_coinShockSumA_le (gcIdx n) o y)
    wb wb_dot gc_hWm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun n => ⟨⟨0, by omega⟩⟩) ?_ ?_
  · filter_upwards [map_snd_condExpKernel] with ω hω
    exact ⟨fun n => gcDep hω n, fun _ _ _ => Iff.rfl⟩
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, scoreMap_smul (sgnA_mul ω)]
    exact redXt_scoreMap_isUnit (n + 2)
  · exact Filter.Eventually.of_forall fun _ _ _ _ => zero_le_one
  · exact Filter.Eventually.of_forall fun _ _ _ => le_refl 1
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o o'
    refine (integral_of_snd hω ((measurable_coinShockSum (gcIdx n) o).mul
      (measurable_coinShockSum (gcIdx n) o'))).trans ?_
    simp only [Pi.mul_apply]
    exact gc_hOm n o o'
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o
    exact (integral_of_snd hω (measurable_coinShockSum (gcIdx n) o)).trans
      (integral_coinShockSum (gcIdx n) o)
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun k => gcXt n ω o k) ⬝ᵥ (fun k => gcXt n ω o k) = 1 := by
      simp [gcXt, redXt, dotProduct, sgnA_mul ω]
    rw [h]
    norm_num
  · refine Filter.Eventually.of_forall fun ω n => ?_
    have h : (gcXt n ω)ᵀ * gcXt n ω
        = (((n + 2 : ℕ) : ℝ) + 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, gram_smul (sgnA_mul ω),
        redXt_transpose_mul_self]
    rw [h, Fintype.card_fin]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · exact Filter.Eventually.of_forall fun _ n j _ γ => wtCluster_card n j γ
  · refine Filter.Eventually.of_forall fun _ => ?_
    simp only [Fintype.card_fin]
    exact gc_hGrate

/-- Vacuity witness for `clustershock_b_general_unconditional`, with the fourth-moment bound at
`C₄ = 3`. -/
theorem clustershock_b_general_unconditional_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ B : Set Aw, MeasurableSet B ∧ ¬ MeasurableSet[Dw] B)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ (n : ℕ) (y : Aw), gcXt n y = (if y.1 then (1 : ℝ) else -1) • redXt (n + 2))
    ∧ (∀ n : ℕ, ∃ a b d : Fin (n + 3),
        Multiway.Linked (wtC n) Finset.univ a b
        ∧ Multiway.Linked (wtC n) Finset.univ b d
        ∧ ¬ Multiway.Linked (wtC n) Finset.univ a d)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, coinShockSumA (gcIdx n) ⟨0, by omega⟩ y
        * coinShockSumA (gcIdx n) ⟨1, by omega⟩ y ∂(condExpKernel Pw Dw ω) = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2))
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSumA (gcIdx n))) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => wb ⬝ᵥ
          ((sqrtPD (restrictedVar (gcXt n y)
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
                (fun _ => (1 : ℝ)))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gcBhat n y - (0 : Fin 1 → ℝ)))))
        atTop (id : ℝ → ℝ) (fun _ => Pw) (gaussianReal 0 1) := by
  refine ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, fun _ _ => rfl,
    wtLinked_not_transitive, gc_within_cond, gc_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine clustershock_b_general_unconditional (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    Dw_le Pw gcXt (fun _ => 1) (fun n => coinShockSumA (gcIdx n)) gcBhat (fun _ => 0)
    (fun n _ => wtC n) Finset.univ (fun _ _ _ => 1) (fun _ _ _ => 1)
    gc_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    1 zero_lt_one 1 zero_lt_one (fun _ _ => 2)
    1 3 zero_lt_one (by norm_num)
    wb wb_dot gc_hWm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun n => ⟨⟨0, by omega⟩⟩) ?_ ?_
  · filter_upwards [map_snd_condExpKernel] with ω hω
    exact ⟨fun n => gcDep hω n, fun _ _ _ => Iff.rfl⟩
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, scoreMap_smul (sgnA_mul ω)]
    exact redXt_scoreMap_isUnit (n + 2)
  · exact Filter.Eventually.of_forall fun _ _ _ _ => zero_le_one
  · exact Filter.Eventually.of_forall fun _ _ _ => le_refl 1
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o o'
    refine (integral_of_snd hω ((measurable_coinShockSum (gcIdx n) o).mul
      (measurable_coinShockSum (gcIdx n) o'))).trans ?_
    simp only [Pi.mul_apply]
    exact gc_hOm n o o'
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o
    exact (integral_of_snd hω (measurable_coinShockSum (gcIdx n) o)).trans
      (integral_coinShockSum (gcIdx n) o)
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun k => gcXt n ω o k) ⬝ᵥ (fun k => gcXt n ω o k) = 1 := by
      simp [gcXt, redXt, dotProduct, sgnA_mul ω]
    rw [h]
    norm_num
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    refine Integrable.of_bound
      ((measurable_coinShockSumA (gcIdx n) o).pow_const 4).aestronglyMeasurable ((3 : ℝ) ^ 4)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact gc_pow_four_le n o y.2
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have hint : Integrable (fun y : Aw => (coinShockSumA (gcIdx n) o y) ^ 4)
        (condExpKernel Pw Dw ω) := by
      refine Integrable.of_bound
        ((measurable_coinShockSumA (gcIdx n) o).pow_const 4).aestronglyMeasurable ((3 : ℝ) ^ 4)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact gc_pow_four_le n o y.2
    calc ∫ y, (coinShockSumA (gcIdx n) o y) ^ 4 ∂(condExpKernel Pw Dw ω)
        ≤ ∫ _y, (3 : ℝ) ^ 4 ∂(condExpKernel Pw Dw ω) :=
          integral_mono hint (integrable_const _) (fun y => gc_pow_four_le n o y.2)
      _ = (3 : ℝ) ^ 4 := by simp
  · refine Filter.Eventually.of_forall fun ω n => ?_
    have h : (gcXt n ω)ᵀ * gcXt n ω
        = (((n + 2 : ℕ) : ℝ) + 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, gram_smul (sgnA_mul ω),
        redXt_transpose_mul_self]
    rw [h, Fintype.card_fin]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · exact Filter.Eventually.of_forall fun _ n j _ γ => wtCluster_card n j γ
  · refine Filter.Eventually.of_forall fun _ => ?_
    simp only [Fintype.card_fin]
    exact gc_hGrate

/-- Vacuity witness for `clustershock_a_general_unconditional_vector`, at `r = 1`. -/
theorem clustershock_a_general_unconditional_vector_witness :
    (∀ n : ℕ, ∃ a b d : Fin (n + 3),
        Multiway.Linked (wtC n) Finset.univ a b
        ∧ Multiway.Linked (wtC n) Finset.univ b d
        ∧ ¬ Multiway.Linked (wtC n) Finset.univ a d)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, coinShockSumA (gcIdx n) ⟨0, by omega⟩ y
        * coinShockSumA (gcIdx n) ⟨1, by omega⟩ y ∂(condExpKernel Pw Dw ω) = 1)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, (depSum (scoreArray (redXt (n + 2))
        (steinWeight (redXt (n + 2))
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) wb) (coinShockSumA (gcIdx n))) y) ^ 2
      ∂(condExpKernel Pw Dw ω) = 1)
    ∧ TendstoInDistribution (m := fun _ : ℕ => (inferInstance : MeasurableSpace Aw))
        (fun (n : ℕ) (y : Aw) => restrictedStat (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ) (gcBhat n y - (0 : Fin 1 → ℝ))) atTop
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (fun _ => Pw)
        (stdGaussian (EuclideanSpace ℝ (Fin 1))) := by
  refine ⟨wtLinked_not_transitive, gc_within_cond, gc_total_variance_cond, ?_⟩
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  refine clustershock_a_general_unconditional_vector (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    Dw_le Pw gcXt (fun _ => 1) (fun n => coinShockSumA (gcIdx n)) gcBhat (fun _ => 0)
    (fun n _ => wtC n) Finset.univ (fun _ _ _ => 1) (fun _ _ _ => 1)
    gc_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    1 zero_lt_one 1 zero_lt_one (fun _ _ => 2)
    1 3 zero_le_one (by norm_num)
    (fun n o y => by simpa using abs_coinShockSumA_le (gcIdx n) o y)
    gc_hWvm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun n => ⟨⟨0, by omega⟩⟩) ?_ ?_
  · filter_upwards [map_snd_condExpKernel] with ω hω
    exact ⟨fun n => gcDep hω n, fun _ _ _ => Iff.rfl⟩
  · refine Filter.Eventually.of_forall fun ω n => ?_
    rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, scoreMap_smul (sgnA_mul ω)]
    exact redXt_scoreMap_isUnit (n + 2)
  · exact Filter.Eventually.of_forall fun _ _ _ _ => zero_le_one
  · exact Filter.Eventually.of_forall fun _ _ _ => le_refl 1
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o o'
    refine (integral_of_snd hω ((measurable_coinShockSum (gcIdx n) o).mul
      (measurable_coinShockSum (gcIdx n) o'))).trans ?_
    simp only [Pi.mul_apply]
    exact gc_hOm n o o'
  · filter_upwards [map_snd_condExpKernel] with ω hω
    intro n o
    exact (integral_of_snd hω (measurable_coinShockSum (gcIdx n) o)).trans
      (integral_coinShockSum (gcIdx n) o)
  · refine Filter.Eventually.of_forall fun ω n o => ?_
    have h : (fun k => gcXt n ω o k) ⬝ᵥ (fun k => gcXt n ω o k) = 1 := by
      simp [gcXt, redXt, dotProduct, sgnA_mul ω]
    rw [h]
    norm_num
  · refine Filter.Eventually.of_forall fun ω n => ?_
    have h : (gcXt n ω)ᵀ * gcXt n ω
        = (((n + 2 : ℕ) : ℝ) + 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, gram_smul (sgnA_mul ω),
        redXt_transpose_mul_self]
    rw [h, Fintype.card_fin]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · exact Filter.Eventually.of_forall fun _ n j _ γ => wtCluster_card n j γ
  · refine Filter.Eventually.of_forall fun _ => ?_
    simp only [Fintype.card_fin]
    exact gc_hGrate

/-- The restricted variance is invariant under the sign of the design. -/
theorem gc_restrictedVar (n : ℕ) (y : Aw) :
    restrictedVar (gcXt n y)
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
      = restrictedVar (redXt (n + 2))
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  unfold restrictedVar
  rw [show gcXt n y = sgnA y • redXt (n + 2) from rfl, scoreMap_smul (sgnA_mul y),
    scoreVar_smul (sgnA_mul y)]

theorem gc_hVpd (n : ℕ) (y : Aw) :
    (restrictedVar (gcXt n y)
      (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
        (fun _ => (1 : ℝ)))
      (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
  rw [gc_restrictedVar n y]
  exact Multiway.posDef_restricted (gc_hPD n) (redXt_scoreMap_isUnit (n + 2))

theorem gc_hVmeas (n : ℕ) : Measurable fun y : Aw =>
    restrictedVar (gcXt n y)
      (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
        (fun _ => (1 : ℝ)))
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have h : (fun y : Aw => restrictedVar (gcXt n y)
      (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
        (fun _ => (1 : ℝ)))
      (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = fun _ : Aw => restrictedVar (redXt (n + 2))
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) := funext (gc_restrictedVar n)
  rw [h]
  exact measurable_const

/-- The variance estimator of the witness: the exact variance inflated by `1 + 1/(n+1)`. -/
noncomputable def gcVh (n : ℕ) (y : Aw) : Matrix (Fin 1) (Fin 1) ℝ :=
  (1 + 1 / ((n : ℝ) + 1)) • restrictedVar (gcXt n y)
    (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)))
    (1 : Matrix (Fin 1) (Fin 1) ℝ)

theorem gc_hVhherm (n : ℕ) (y : Aw) : (gcVh n y).IsHermitian :=
  ((gc_hVpd n y).smul (by positivity)).isHermitian

theorem gc_hVhmeas (n : ℕ) : Measurable (gcVh n) := by
  have h : gcVh n = fun _ : Aw => (1 + 1 / ((n : ℝ) + 1)) • restrictedVar (redXt (n + 2))
      (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
        (fun _ => (1 : ℝ)))
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    funext y
    show (1 + 1 / ((n : ℝ) + 1)) • restrictedVar (gcXt n y) _ _ = _
    rw [gc_restrictedVar n y]
  rw [h]
  exact measurable_const

/-- `‖𝒱_n^{-1/2}𝒱̂_n𝒱_n^{-1/2} − I‖_F = 1/(n+1)`. -/
theorem gc_ratio (n : ℕ) (y : Aw) :
    rectFrobNorm ((sqrtPD (restrictedVar (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ * gcVh n y
        * (sqrtPD (restrictedVar (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ - 1) = 1 / ((n : ℝ) + 1) := by
  have hpd := gc_hVpd n y
  have hone : (sqrtPD (restrictedVar (gcXt n y)
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹
      * restrictedVar (gcXt n y)
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
      * (sqrtPD (restrictedVar (gcXt n y)
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ = 1 :=
    Multiway.inv_conj_eq_one (sqrtPD_mul_self hpd.posSemidef) (sqrtPD_inv_mul hpd)
      (sqrtPD_mul_inv hpd)
  have hexp : (sqrtPD (restrictedVar (gcXt n y)
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ * gcVh n y
      * (sqrtPD (restrictedVar (gcXt n y)
        (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ - 1
      = (1 / ((n : ℝ) + 1)) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    show _ * ((1 + 1 / ((n : ℝ) + 1)) • restrictedVar (gcXt n y) _ _) * _ - 1 = _
    rw [Matrix.mul_smul, Matrix.smul_mul, hone, add_smul, one_smul, add_sub_cancel_left]
  rw [hexp, rectFrobNorm]
  have h1 : rectFrobSq ((1 / ((n : ℝ) + 1)) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (1 / ((n : ℝ) + 1)) ^ 2 := by
    simp [rectFrobSq, Matrix.smul_apply, Matrix.one_apply]
  rw [h1, Real.sqrt_sq (by positivity)]

/-- Vacuity witness for `clustershock_rateagnostic_c`. -/
theorem clustershock_rateagnostic_c_witness :
    (∀ (n : ℕ) (y : Aw), rectFrobNorm ((sqrtPD (restrictedVar (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ * gcVh n y
        * (sqrtPD (restrictedVar (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ - 1) = 1 / ((n : ℝ) + 1))
    ∧ (∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1))
    ∧ (∀ n : ℕ, ∃ a b d : Fin (n + 3),
        Multiway.Linked (wtC n) Finset.univ a b
        ∧ Multiway.Linked (wtC n) Finset.univ b d
        ∧ ¬ Multiway.Linked (wtC n) Finset.univ a d)
    ∧ Tendsto (fun n => Pw {y : Aw | (gcVh n y).PosDef}) atTop (𝓝 1)
    ∧ TendstoInDistribution
        (fun (n : ℕ) (y : Aw) => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (gcVh n y))⁻¹)
          (WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gcBhat n y - (0 : Fin 1 → ℝ)))
            : EuclideanSpace ℝ (Fin 1))) atTop
        (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (fun _ => Pw)
        (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    ∧ TendstoInDistribution
        (fun (n : ℕ) (y : Aw) => Multiway.Wald.waldStat (gcVh n y)
          (WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (gcBhat n y - (0 : Fin 1 → ℝ)))
            : EuclideanSpace ℝ (Fin 1))) atTop
        (fun z : EuclideanSpace ℝ (Fin 1) => ‖z‖ ^ 2) (fun _ => Pw)
        (stdGaussian (EuclideanSpace ℝ (Fin 1))) := by
  have hratio : TendstoInMeasure Pw (fun n (y : Aw) => rectFrobNorm
      ((sqrtPD (restrictedVar (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ * gcVh n y
        * (sqrtPD (restrictedVar (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ - 1)) atTop (fun _ => 0) := by
    have hfun : (fun n (y : Aw) => rectFrobNorm
        ((sqrtPD (restrictedVar (gcXt n y)
            (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
              (fun _ => (1 : ℝ)))
            (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ * gcVh n y
          * (sqrtPD (restrictedVar (gcXt n y)
            (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
              (fun _ => (1 : ℝ)))
            (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ - 1))
        = fun (n : ℕ) (_ : Aw) => 1 / ((n : ℝ) + 1) := by
      funext n y
      exact gc_ratio n y
    rw [hfun]
    exact Multiway.RateAgnostic.tendstoInMeasure_zero_of_tendsto_const
      tendsto_one_div_add_atTop_nhds_zero_nat
  have h := clustershock_rateagnostic_c Pw gcXt
    (fun n (_ : Aw) => Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
      (fun _ => (1 : ℝ)))
    (fun _ => 1) (fun n y => gcBhat n y - (0 : Fin 1 → ℝ)) gcVh
    gc_hVpd gc_hVmeas gc_hVhherm gc_hVhmeas hratio
    clustershock_a_general_unconditional_vector_witness.2.2.2
  exact ⟨gc_ratio, fun n => by positivity, wtLinked_not_transitive, h.1, h.2.1, h.2.2⟩

end FrozenGeneralShockWitness

end FrozenGeneralShockWitness

end Multiway.ClusterShock
