/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Multiway.ClusterJansonB

/-!
# Feasible inference under the cluster-shock model: further forms

This file completes the formalization of Corollary SM.D.3 of the paper (feasible inference
under the cluster-shock model). It extends the second sentence (bounded conditional fourth
moments) to every `ε > 0` and to unconditional and vector form, derives the limit law in
part (c), states part (c) under the Theorem 5 and Theorem 11 hypothesis sets in one theorem, and
derives the moment assumption on `ν` from fourth moments of the shocks. The examples include a
weighted cluster-shock representation with an unbounded disturbance and a design with `r = 2`.

## Main results

* `clustershock_b_general_janson_anyEps`: the second sentence at arbitrary `ε > 0`.
* `clustershock_b_general_janson_unconditional_vector`: its unconditional vector form.
* `clustershock_b_general_janson_unbounded_witness`: an example with an unbounded disturbance.
* `clustershock_rateagnostic_c_janson`: part (c) with the limit law derived.
* `clustershock_wald_both_halves`: part (c) under both hypothesis sets at once.
* `condExp_nuRV_pow_four_le`: the fourth-moment bound on `ν` from the shocks'.
* `clustershock_wald_both_halves_shockmoments`: the end-to-end form under shock moments.
-/

namespace Multiway.ClusterJanson

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology BigOperators MatrixOrder
open Matrix
open Causalean.Mathlib.Probability.SteinMethod
open Multiway.SteinCluster
open Multiway.ClusterShock

/-! ### Section C1. Arbitrary `ε > 0`

For `ε > 3` the rate hypothesis of the second sentence cannot hold when `1 ≤ Ḡ_n ≤ n`. -/

section AnyEps

/-- For `ε > 3` and `1 ≤ Ḡ_n ≤ n`, the sequence `Ḡ_n^{3−ε}/n^{1−ε}` is bounded below by `1`
and so does not tend to `0`, since `Ḡ_n^{3−ε}/n^{1−ε} = n^{ε−1}/Ḡ_n^{ε−3} ≥ n² ≥ 1`. -/
theorem epsHyp_false_of_three_lt {N Gb : ℕ → ℕ} {ε : ℝ} (hε3 : 3 < ε)
    (hN1 : ∀ n, 1 ≤ N n) (hG1 : ∀ n, 1 ≤ Gb n) (hGN : ∀ n, Gb n ≤ N n)
    (h : Tendsto (fun n => (Gb n : ℝ) ^ ((3 : ℝ) - ε) / (N n : ℝ) ^ ((1 : ℝ) - ε))
      atTop (𝓝 0)) : False := by
  have hfloor : ∀ n, (1 : ℝ) ≤ (Gb n : ℝ) ^ ((3 : ℝ) - ε) / (N n : ℝ) ^ ((1 : ℝ) - ε) := by
    intro n
    have hG1R : (1 : ℝ) ≤ (Gb n : ℝ) := by exact_mod_cast hG1 n
    have hN1R : (1 : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hN1 n
    have hG0 : (0 : ℝ) < (Gb n : ℝ) := lt_of_lt_of_le zero_lt_one hG1R
    have hN0 : (0 : ℝ) < (N n : ℝ) := lt_of_lt_of_le zero_lt_one hN1R
    have hGNR : (Gb n : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hGN n
    have e1 : (Gb n : ℝ) ^ ((3 : ℝ) - ε) = ((Gb n : ℝ) ^ (ε - 3))⁻¹ := by
      rw [show (3 : ℝ) - ε = -(ε - 3) by ring, Real.rpow_neg hG0.le]
    have e2 : (N n : ℝ) ^ ((1 : ℝ) - ε) = ((N n : ℝ) ^ (ε - 1))⁻¹ := by
      rw [show (1 : ℝ) - ε = -(ε - 1) by ring, Real.rpow_neg hN0.le]
    have hGp : (Gb n : ℝ) ^ (ε - 3) ≤ (N n : ℝ) ^ (ε - 3) :=
      Real.rpow_le_rpow hG0.le hGNR (by linarith)
    have hGp0 : (0 : ℝ) < (Gb n : ℝ) ^ (ε - 3) := Real.rpow_pos_of_pos hG0 _
    have hstep : (N n : ℝ) ^ (ε - 1) / (N n : ℝ) ^ (ε - 3)
        ≤ (N n : ℝ) ^ (ε - 1) / (Gb n : ℝ) ^ (ε - 3) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) hGp0 hGp
    have hsq : (N n : ℝ) ^ (ε - 1) / (N n : ℝ) ^ (ε - 3) = (N n : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_sub hN0]
      congr 1
      ring
    have hone : (1 : ℝ) ≤ (N n : ℝ) ^ (2 : ℝ) := Real.one_le_rpow hN1R (by norm_num)
    rw [e1, e2, inv_div_inv]
    calc (1 : ℝ) ≤ (N n : ℝ) ^ (2 : ℝ) := hone
      _ = (N n : ℝ) ^ (ε - 1) / (N n : ℝ) ^ (ε - 3) := hsq.symm
      _ ≤ (N n : ℝ) ^ (ε - 1) / (Gb n : ℝ) ^ (ε - 3) := hstep
  have hle : (1 : ℝ) ≤ 0 := ge_of_tendsto' h hfloor
  linarith

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Dm : Type*} [DecidableEq Dm]
variable {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Corollary SM.D.3**, second sentence, at general `J` and arbitrary `ε > 0`. The binders
`hGb1` and `hGbN` say `1 ≤ Ḡ_n ≤ n`; for `ε > 3` the rate hypothesis is then false
(`epsHyp_false_of_three_lt`), and for `ε ≤ 3` this is
`ClusterJansonB.clustershock_b_general_janson`. -/
theorem clustershock_b_general_janson_anyEps
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
    (hGb1 : ∀ n, 1 ≤ Gb n) (hGbN : ∀ n, Gb n ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hGrate : Tendsto (fun n => (Gb n : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0))
    (b : r → ℝ) (hb : b ⬝ᵥ b = 1) (s : ℝ) :
    Tendsto (fun n => ((μ n).map (fun ω =>
        b ⬝ᵥ ((sqrtPD (restrictedVar (Xt n)
              (Multiway.Sharing.clusterOmega (c n) dims (sc n) (ve n)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n ω - β n))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  rcases le_or_gt ε 3 with hε3 | hε3
  · exact clustershock_b_general_janson μ Xt Rn ν bhat β c dims Dv hshare hscore hA sc ve hsc
      s2 hs2 hve hOm hmean B C4 hB0 hC40 hB hint4 hfour θ hθ hdesign hne Gb hGb ε hε hε3
      hGrate b hb s
  · exact absurd hGrate (fun hc => (epsHyp_false_of_three_lt hε3
      (fun n => @Fintype.card_pos _ _ (hne n)) hGb1 hGbN hc).elim)

end AnyEps

/-! ### Section C2. The second sentence unconditionally and in vector form -/

section PartBUnconditional

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Dm : Type*} [DecidableEq Dm]
variable {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The four almost-everywhere facts shared by the general-`J` unconditional forms of the
second sentence, at arbitrary `ε > 0`. -/
theorem clustershock_general_uncond_package_janson_eps
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
    (ε : ℝ) (hε3 : ε ≤ 3)
    (hGrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P,
      (∃ Dv : ∀ n, DepGraph (ν n) (condExpKernel P 𝒟 ω),
        ∀ n o, ((Dv n).nbhd o).card ≤ min (dims.card * Gb n ω) (Fintype.card (O n)) + 1)
      ∧ (∀ n, 1 ≤ min (dims.card * Gb n ω) (Fintype.card (O n)))
      ∧ (∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
          ≤ scoreVar (Xt n ω) (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)))
      ∧ Tendsto (fun n => epsRate (Fintype.card (O n))
          (min (dims.card * Gb n ω) (Fintype.card (O n)))
          ((s2 * θ) * (Fintype.card (O n) : ℝ)) ε) atTop (𝓝 0) := by
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
  exact tendsto_epsRate_of_cluster_size (mul_pos hs2 hθ) hε3 (fun n => hcard n) hDn1
    (fun n => min_le_left _ _) hGrω

/-- **Corollary SM.D.3**, second sentence, at general `J`, under the full measure with a
random design, at arbitrary `ε > 0`. The binder `hWm` is a measurability side condition. -/
theorem clustershock_b_general_janson_unconditional
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
    (ε : ℝ) (hε : 0 < ε) (hε3 : ε ≤ 3)
    (hGrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y)
            (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hpkg := clustershock_general_uncond_package_janson_eps (𝒟 := 𝒟) P Xt ν c dims sc ve
    hs2 hθ Gb hne hdep hsc hve hdesign hGb ε hε3 hGrate
  exact cltcluster_b_general_betaJM_janson_unconditional h𝒟 P Xt
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
    ε hε (hpkg.mono fun _ h => h.2.2.2)

/-- The vector form: `𝒱_n^{-1/2}𝓡_n(β̂_JM − β) ⟶ᵈ N(0, I_r)` under `P`, at a random design,
at general `J`, under bounded conditional fourth moments, at arbitrary `ε > 0`. -/
theorem clustershock_b_general_janson_unconditional_vector
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
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
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
    (hint4 : ∀ᵐ ω ∂P, ∀ n o, Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hne : ∀ n, Nonempty (O n))
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (ε : ℝ) (hε : 0 < ε) (hε3 : ε ≤ 3)
    (hGrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y)
        (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)
        (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  have hcard : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hpkg := clustershock_general_uncond_package_janson_eps (𝒟 := 𝒟) P Xt ν c dims sc ve
    hs2 hθ Gb hne hdep hsc hve hdesign hGb ε hε3 hGrate
  exact cltcluster_b_general_betaJM_janson_unconditional_vector h𝒟 P Xt
    (fun n ω => Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) Rn ν bhat β
    hXtD hOmD hscore
    (fun n _ => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n ω => min (dims.card * Gb n ω) (Fintype.card (O n)))
    B C4 hB0 hC40 hWvm
    (hpkg.mono fun _ h => h.1) hA
    (Filter.Eventually.of_forall fun _ n =>
      mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcard n))
    (hpkg.mono fun _ h => h.2.2.1) hOm hmean hB hint4 hfour
    (hpkg.mono fun _ h => h.2.1)
    (Filter.Eventually.of_forall fun _ _ => min_le_right _ _)
    ε hε (hpkg.mono fun _ h => h.2.2.2)

end PartBUnconditional

/-! ### Section C2b. The unconditional forms at arbitrary `ε` -/

section AnyEpsUnconditional

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Dm : Type*} [DecidableEq Dm]
variable {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The almost-everywhere form of `epsHyp_false_of_three_lt`. -/
theorem epsHyp_ae_false_of_three_lt {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ → ℕ} {Gb : ℕ → Ω → ℕ} {ε : ℝ} (hε3 : 3 < ε) (hN1 : ∀ n, 1 ≤ N n)
    (hG1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Gb n ω) (hGN : ∀ᵐ ω ∂P, ∀ n, Gb n ω ≤ N n)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) ^ ((3 : ℝ) - ε) / (N n : ℝ) ^ ((1 : ℝ) - ε))
      atTop (𝓝 0)) : False := by
  obtain ⟨ω, ⟨hGω, h1ω⟩, hNω⟩ := ((h.and hG1).and hGN).exists
  exact epsHyp_false_of_three_lt hε3 hN1 h1ω hNω hGω

/-- `clustershock_b_general_janson_unconditional` for every `ε > 0`, given `1 ≤ Ḡ_n ≤ n`. -/
theorem clustershock_b_general_janson_unconditional_anyEps
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
    (hGb1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Gb n ω)
    (hGbN : ∀ᵐ ω ∂P, ∀ n, Gb n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hGrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => b ⬝ᵥ
        ((sqrtPD (restrictedVar (Xt n y)
            (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)))⁻¹ *ᵥ
          (Rn n *ᵥ (bhat n y - β n)))) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1) := by
  rcases le_or_gt ε 3 with hε3 | hε3
  · exact clustershock_b_general_janson_unconditional h𝒟 P Xt Rn ν bhat β c dims sc ve
      hXtD hOmD hscore s2 hs2 θ hθ Gb B C4 hB0 hC40 b hb hWm hdep hA hsc hve hOm hmean hB
      hint4 hfour hdesign hne hGb ε hε hε3 hGrate
  · exact (epsHyp_ae_false_of_three_lt hε3 (fun n => @Fintype.card_pos _ _ (hne n))
      hGb1 hGbN hGrate).elim

/-- The vector form for every `ε > 0`, given `1 ≤ Ḡ_n ≤ n`. -/
theorem clustershock_b_general_janson_unconditional_vector_anyEps
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
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
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
    (hint4 : ∀ᵐ ω ∂P, ∀ n o, Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hne : ∀ n, Nonempty (O n))
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGb1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Gb n ω)
    (hGbN : ∀ᵐ ω ∂P, ∀ n, Gb n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hGrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0)) :
    TendstoInDistribution (m := fun _ : ℕ => mΩ)
      (fun n y => restrictedStat (Xt n y)
        (Multiway.Sharing.clusterOmega (c n y) dims (sc n y) (ve n y)) (Rn n)
        (bhat n y - β n)) atTop
      (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
      (stdGaussian (EuclideanSpace ℝ rr)) := by
  rcases le_or_gt ε 3 with hε3 | hε3
  · exact clustershock_b_general_janson_unconditional_vector h𝒟 P Xt Rn ν bhat β c dims sc ve
      hXtD hOmD hscore s2 hs2 θ hθ Gb B C4 hB0 hC40 hWvm hdep hA hsc hve hOm hmean hB
      hint4 hfour hdesign hne hGb ε hε hε3 hGrate
  · exact (epsHyp_ae_false_of_three_lt hε3 (fun n => @Fintype.card_pos _ _ (hne n))
      hGb1 hGbN hGrate).elim

end AnyEpsUnconditional

/-! ### Section C3. A weighted cluster-shock representation

`ν_o = w∑_{k∈κ}s_{idx(o,k)}` with a scalar weight `w`. With `κ` enlarged to kind-and-replicate
pairs and `w = (n+1)^{-1/2}`, the second moments match the unweighted model while the supremum
of `|ν_o|` grows like `√(n+1)`; the fourth moment `3(w²|κ|)²` stays bounded. -/

section WeightedShockSum

open Multiway.Multilinear

variable {O : Type*} [Fintype O] [DecidableEq O]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m : ℕ}

/-- `ν_o := w∑_{k}s_{idx(o,k)}`, the cluster-shock sum `ClusterShock.shockSum` with a scalar
weight. -/
noncomputable def wShockSum (idx : O → κ → Fin m) (w : ℝ) (o : O) (ω : Fin m → Bool) : ℝ :=
  w * shockSum idx o ω

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem measurable_wShockSum (idx : O → κ → Fin m) (w : ℝ) (o : O) :
    Measurable (wShockSum idx w o) := (measurable_shockSum idx o).const_mul w

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
theorem abs_wShockSum_le (idx : O → κ → Fin m) {w : ℝ} (hw : 0 ≤ w) (o : O)
    (ω : Fin m → Bool) : |wShockSum idx w o ω| ≤ w * (Fintype.card κ : ℝ) := by
  rw [wShockSum, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (abs_shockSum_le idx o ω) hw

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
/-- The weighted representation has mean zero. -/
theorem integral_wShockSum (idx : O → κ → Fin m) (w : ℝ) (o : O) :
    ∫ ω, wShockSum idx w o ω ∂(coins m) = 0 := by
  simp only [wShockSum]
  rw [integral_const_mul, integral_shockSum idx o, mul_zero]

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
/-- `E[ν_oν_{o'}] = w²·#{k : idx(o,k) = idx(o',k)}`, provided components of different kind
never read the same coin (`hinj`). -/
theorem integral_wShockSum_mul {idx : O → κ → Fin m} (w : ℝ)
    (hinj : ∀ o o' : O, ∀ k k' : κ, idx o k = idx o' k' → k = k') (o o' : O) :
    ∫ ω, wShockSum idx w o ω * wShockSum idx w o' ω ∂(coins m)
      = w ^ 2 * ∑ k : κ, (if idx o k = idx o' k then (1 : ℝ) else 0) := by
  have hre : ∀ ω, wShockSum idx w o ω * wShockSum idx w o' ω
      = w ^ 2 * (shockSum idx o ω * shockSum idx o' ω) := by
    intro ω
    simp only [wShockSum]
    ring
  simp only [hre]
  rw [integral_const_mul, integral_shockSum_mul hinj o o']

omit [Fintype O] [DecidableEq O] [DecidableEq κ] in
/-- The weighted representation equals `w·|κ|` at the all-heads realization. -/
theorem wShockSum_all_true (idx : O → κ → Fin m) (w : ℝ) (o : O) :
    wShockSum idx w o (fun _ => true) = w * (Fintype.card κ : ℝ) := by
  have hs : ∀ i : Fin m, sign2 i (fun _ => true) = 1 := fun i => by simp [sign2]
  simp only [wShockSum, shockSum, hs]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- `E[ν_o⁴] ≤ 3(w²|κ|)²`, when observation `o` reads `|κ|` distinct coins (`hinjo`). -/
theorem integral_wShockSum_pow_four_le {idx : O → κ → Fin m} {w : ℝ} (o : O)
    (hinjo : Function.Injective (idx o)) :
    ∫ ω, (wShockSum idx w o ω) ^ 4 ∂(coins m)
      ≤ 3 * (w ^ 2 * (Fintype.card κ : ℝ)) ^ 2 := by
  classical
  set F : Finset (Fin m) := Finset.univ.image (idx o) with hF
  have hinjOn : ∀ x ∈ (Finset.univ : Finset κ), ∀ y ∈ (Finset.univ : Finset κ),
      idx o x = idx o y → x = y := fun x _ y _ h => hinjo h
  have hsum : ∀ ω, wShockSum idx w o ω = ∑ i ∈ F, w * sign2 i ω := by
    intro ω
    rw [← Finset.mul_sum, hF, Finset.sum_image hinjOn]
    rfl
  have hcardF : F.card = Fintype.card κ := by
    rw [hF, Finset.card_image_of_injective _ hinjo, Finset.card_univ]
  have hcoef : ∑ _i ∈ F, w ^ 2 = w ^ 2 * (Fintype.card κ : ℝ) := by
    rw [Finset.sum_const, hcardF, nsmul_eq_mul]
    ring
  have hmain := Multiway.Multilinear.integral_pow_four_linear_le
    (μ := coins m) (ξ := fun i : Fin m => sign2 i) (a := fun _ => w) (B := 1)
    (iIndepFun_sign2 _) measurable_sign2 (fun i => integral_sign2 i)
    (fun i => Filter.Eventually.of_forall
      (fun ω => Multiway.SteinCluster.abs_sign2_le' i ω)) F
  rw [hcoef] at hmain
  calc ∫ ω, (wShockSum idx w o ω) ^ 4 ∂(coins m)
      = ∫ ω, (∑ i ∈ F, w * sign2 i ω) ^ 4 ∂(coins m) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show (wShockSum idx w o ω) ^ 4 = (∑ i ∈ F, w * sign2 i ω) ^ 4
        rw [hsum ω]
    _ ≤ 3 * (1 : ℝ) ^ 4 * (w ^ 2 * (Fintype.card κ : ℝ)) ^ 2 := hmain
    _ = 3 * (w ^ 2 * (Fintype.card κ : ℝ)) ^ 2 := by ring

/-- The sharing graph is a dependency graph for the weighted representation. -/
noncomputable def wShockDep (idx : O → κ → Fin m) (w : ℝ) (G : O → O → Prop) [DecidableRel G]
    (hrefl : ∀ o, G o o) (hsymm : ∀ o o', G o o' → G o' o)
    (hdisj : ∀ o o', ¬ G o o' → ∀ k k' : κ, idx o k ≠ idx o' k') :
    DepGraph (wShockSum idx w) (coins m) :=
  Multiway.SteinCluster.mapDepGraph (shockDep idx G hrefl hsymm hdisj)
    (fun _ x => w * x) (fun _ => measurable_id.const_mul w)

end WeightedShockSum

/-! ### Section C4. An example for the second sentence with an unbounded disturbance

The `J = 2` cluster-shock design of `ClusterShock.GeneralWitness` (`n+3` observations,
clustering maps `⌊o/2⌋` and `⌊(o+1)/2⌋`, `Ḡ_n = 2`), with each of the three shock components
replaced by a standardized sum of `n+1` fair signs, so that
`ν_o = (n+1)^{-1/2}∑_{j<3}∑_{i≤n}s_{(j,i)-th coin of o}`. The matrix `Ω` is unchanged, while
`sup_ω|ν_{n,o}| = 3√(n+1) → ∞` and `E[ν_o⁴] ≤ 27` for every `n`. -/

section UnboundedShockWitness

open Filter
open Multiway.Multilinear
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace UnboundedShockWitness

/-- Component `(j,i)` of observation `o` reads the `i`-th coin of the block that
`ClusterShock.wtIdx` assigns to component `j`. -/
def ugIdx (n : ℕ) (o : Fin (n + 3)) (k : Fin 3 × Fin (n + 1)) : Fin (3 * (n + 3) * (n + 1)) :=
  ⟨(wtIdx n o k.1).val * (n + 1) + k.2.val, by
    have h1 : (wtIdx n o k.1).val + 1 ≤ 3 * (n + 3) := (wtIdx n o k.1).isLt
    have h2 : k.2.val < n + 1 := k.2.isLt
    calc (wtIdx n o k.1).val * (n + 1) + k.2.val
        < (wtIdx n o k.1).val * (n + 1) + (n + 1) := by omega
      _ = ((wtIdx n o k.1).val + 1) * (n + 1) := by ring
      _ ≤ (3 * (n + 3)) * (n + 1) := Nat.mul_le_mul_right _ h1⟩

theorem ugIdx_eq_iff (n : ℕ) (o o' : Fin (n + 3)) (k k' : Fin 3 × Fin (n + 1)) :
    ugIdx n o k = ugIdx n o' k' ↔ (wtIdx n o k.1 = wtIdx n o' k'.1 ∧ k.2 = k'.2) := by
  constructor
  · intro h
    have hv : (wtIdx n o k.1).val * (n + 1) + k.2.val
        = (wtIdx n o' k'.1).val * (n + 1) + k'.2.val := congrArg Fin.val h
    have hk : k.2.val < n + 1 := k.2.isLt
    have hk' : k'.2.val < n + 1 := k'.2.isLt
    have e1 : ((wtIdx n o k.1).val * (n + 1) + k.2.val) % (n + 1) = k.2.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
    have e2 : ((wtIdx n o' k'.1).val * (n + 1) + k'.2.val) % (n + 1) = k'.2.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk']
    have hkk : k.2.val = k'.2.val := by rw [← e1, ← e2, hv]
    have hoo : (wtIdx n o k.1).val * (n + 1) = (wtIdx n o' k'.1).val * (n + 1) := by omega
    exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) hoo), Fin.ext hkk⟩
  · rintro ⟨h1, h2⟩
    refine Fin.ext ?_
    show (wtIdx n o k.1).val * (n + 1) + k.2.val
      = (wtIdx n o' k'.1).val * (n + 1) + k'.2.val
    rw [h1, h2]

/-- Two components of different kind or different replicate never read the same coin. -/
theorem ugIdx_component (n : ℕ) (o o' : Fin (n + 3)) (k k' : Fin 3 × Fin (n + 1))
    (h : ugIdx n o k = ugIdx n o' k') : k = k' := by
  obtain ⟨h1, h2⟩ := (ugIdx_eq_iff n o o' k k').mp h
  exact Prod.ext (wtIdx_component n o o' k.1 k'.1 h1) h2

theorem ugIdx_injective (n : ℕ) (o : Fin (n + 3)) : Function.Injective (ugIdx n o) :=
  fun k k' h => ugIdx_component n o o k k' h

/-- Non-adjacent observations read disjoint blocks. -/
theorem ugIdx_ne_of_not_linked (n : ℕ) (o o' : Fin (n + 3))
    (h : ¬ Multiway.Linked (wtC n) Finset.univ o o') (k k' : Fin 3 × Fin (n + 1)) :
    ugIdx n o k ≠ ugIdx n o' k' := by
  intro heq
  exact wtIdx_ne_of_not_linked n o o' h k.1 k'.1 ((ugIdx_eq_iff n o o' k k').mp heq).1

/-- The standardizing weight `(n+1)^{-1/2}`. -/
noncomputable def ugW (n : ℕ) : ℝ := 1 / Real.sqrt ((n : ℝ) + 1)

/-- The unbounded cluster-shock disturbance. -/
noncomputable def ugNu (n : ℕ) (o : Fin (n + 3))
    (ω : Fin (3 * (n + 3) * (n + 1)) → Bool) : ℝ :=
  wShockSum (ugIdx n) (ugW n) o ω

theorem ugW_pos (n : ℕ) : (0 : ℝ) < ugW n := by
  have h : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  exact div_pos one_pos h

theorem ugW_le_one (n : ℕ) : ugW n ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
    have h3 : Real.sqrt 1 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at h3
  rw [ugW, div_le_one (lt_of_lt_of_le zero_lt_one h2)]
  exact h2

theorem ugW_sq (n : ℕ) : (ugW n) ^ 2 = 1 / ((n : ℝ) + 1) := by
  have hK : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [ugW, div_pow, one_pow, Real.sq_sqrt hK]

theorem ug_card (n : ℕ) : (Fintype.card (Fin 3 × Fin (n + 1)) : ℝ) = 3 * ((n : ℝ) + 1) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

theorem ugW_sq_mul (n : ℕ) : (ugW n) ^ 2 * ((n : ℝ) + 1) = 1 := by
  rw [ugW_sq]
  field_simp

theorem ugW_sq_card (n : ℕ) :
    (ugW n) ^ 2 * (Fintype.card (Fin 3 × Fin (n + 1)) : ℝ) = 3 := by
  rw [ug_card, ← mul_assoc, mul_comm ((ugW n) ^ 2) (3 : ℝ), mul_assoc, ugW_sq_mul, mul_one]

/-- The second moments of the `J = 2` cluster-shock model, at three components, in the form
of `Sharing.clusterOmega`. -/
theorem wtIdx_sum_eq_clusterOmega (n : ℕ) (o o' : Fin (n + 3)) :
    (∑ j : Fin 3, (if wtIdx n o j = wtIdx n o' j then (1 : ℝ) else 0))
      = Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)) o o' := by
  rw [Multiway.Sharing.clusterOmega_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  have e0 : (wtIdx n o 0 = wtIdx n o' 0) ↔ Multiway.SameOn (wtC n) {0} o o' := by
    rw [wtIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_zero_iff]
  have e1 : (wtIdx n o 1 = wtIdx n o' 1) ↔ Multiway.SameOn (wtC n) {1} o o' := by
    rw [wtIdx_eq_iff, sameOn_singleton_iff, wtLab_eq_one_iff]
  have e2 : (wtIdx n o 2 = wtIdx n o' 2) ↔ (o = o') := by
    rw [wtIdx_eq_iff, wtLab_eq_two_iff]
  rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl, if_congr e2 rfl rfl]

/-- `E[ν_oν_{o'}]` is the same cluster-shock matrix as in the bounded model, because the
`n+1` replicates of a shared component contribute `(n+1)w² = 1`. -/
theorem ug_hOm (n : ℕ) (o o' : Fin (n + 3)) :
    ∫ ω, ugNu n o ω * ugNu n o' ω ∂(coins (3 * (n + 3) * (n + 1)))
      = Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
          (fun _ => (1 : ℝ)) o o' := by
  classical
  show ∫ ω, wShockSum (ugIdx n) (ugW n) o ω * wShockSum (ugIdx n) (ugW n) o' ω
      ∂(coins (3 * (n + 3) * (n + 1))) = _
  rw [integral_wShockSum_mul (ugW n) (ugIdx_component n) o o']
  have hsplit : (∑ k : Fin 3 × Fin (n + 1),
        (if ugIdx n o k = ugIdx n o' k then (1 : ℝ) else 0))
      = ((n : ℝ) + 1) * ∑ j : Fin 3, (if wtIdx n o j = wtIdx n o' j then (1 : ℝ) else 0) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hiff : ∀ i : Fin (n + 1),
        (ugIdx n o (j, i) = ugIdx n o' (j, i)) ↔ (wtIdx n o j = wtIdx n o' j) := by
      intro i
      rw [ugIdx_eq_iff]
      simp
    by_cases h : wtIdx n o j = wtIdx n o' j
    · have hone : ∀ i : Fin (n + 1),
          (if ugIdx n o (j, i) = ugIdx n o' (j, i) then (1 : ℝ) else 0) = 1 :=
        fun i => if_pos ((hiff i).mpr h)
      rw [Finset.sum_congr rfl (fun i _ => hone i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, if_pos h]
      push_cast
      ring
    · have hzero : ∀ i : Fin (n + 1),
          (if ugIdx n o (j, i) = ugIdx n o' (j, i) then (1 : ℝ) else 0) = 0 :=
        fun i => if_neg (fun hc => h ((hiff i).mp hc))
      rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const_zero, if_neg h, mul_zero]
  rw [hsplit, ← mul_assoc, ugW_sq_mul, one_mul, wtIdx_sum_eq_clusterOmega]

theorem ug_hmean (n : ℕ) (o : Fin (n + 3)) :
    ∫ ω, ugNu n o ω ∂(coins (3 * (n + 3) * (n + 1))) = 0 :=
  integral_wShockSum (ugIdx n) (ugW n) o

/-- The sharing graph `|o − o'| ≤ 1` is a dependency graph for the replicated disturbance. -/
noncomputable def ugDep (n : ℕ) :
    DepGraph (ugNu n) (coins (3 * (n + 3) * (n + 1))) :=
  wShockDep (ugIdx n) (ugW n) (Multiway.Linked (wtC n) Finset.univ)
    (fun _ => ⟨0, Finset.mem_univ 0, rfl⟩)
    (fun _ _ h => Multiway.Sharing.linked_symm h)
    (ugIdx_ne_of_not_linked n)

theorem abs_ugNu_le (n : ℕ) (o : Fin (n + 3)) (ω : Fin (3 * (n + 3) * (n + 1)) → Bool) :
    |ugNu n o ω| ≤ 3 * ((n : ℝ) + 1) := by
  have h := abs_wShockSum_le (ugIdx n) (ugW_pos n).le o ω
  rw [ug_card] at h
  refine h.trans ?_
  have hK : (0 : ℝ) ≤ 3 * ((n : ℝ) + 1) := by positivity
  nlinarith [ugW_le_one n, hK]

theorem ug_integrable_pow_four (n : ℕ) (o : Fin (n + 3)) :
    Integrable (fun ω => (ugNu n o ω) ^ 4) (coins (3 * (n + 3) * (n + 1))) := by
  refine Multiway.SteinCluster.integrable_of_abs_le
    ((measurable_wShockSum (ugIdx n) (ugW n) o).pow_const 4)
    (C := (3 * ((n : ℝ) + 1)) ^ 4) (fun ω => ?_)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_ugNu_le n o ω) 4

/-- `E[ν_o⁴] ≤ 3(w²|κ|)² = 27` for every `n`. -/
theorem ug_pow_four_le (n : ℕ) (o : Fin (n + 3)) :
    ∫ ω, (ugNu n o ω) ^ 4 ∂(coins (3 * (n + 3) * (n + 1))) ≤ (3 : ℝ) ^ 4 := by
  have h := integral_wShockSum_pow_four_le (idx := ugIdx n) (w := ugW n) o (ugIdx_injective n o)
  rw [ugW_sq_card n] at h
  refine h.trans ?_
  norm_num

theorem ugNu_all_true (n : ℕ) (o : Fin (n + 3)) :
    ugNu n o (fun _ => true) = 3 * Real.sqrt ((n : ℝ) + 1) := by
  have hK : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  show wShockSum (ugIdx n) (ugW n) o (fun _ => true) = _
  rw [wShockSum_all_true, ug_card, ugW, div_mul_eq_mul_div, one_mul,
    show (3 : ℝ) * ((n : ℝ) + 1) = 3 * ((n : ℝ) + 1) from rfl]
  rw [mul_div_assoc, Real.div_sqrt]

/-- No constant bounds `sup_o|ν_{n,o}|` uniformly in `n`. -/
theorem ugNu_unbounded (C : ℝ) :
    ∃ (n : ℕ) (o : Fin (n + 3)) (ω : Fin (3 * (n + 3) * (n + 1)) → Bool), C < ugNu n o ω := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2)
  refine ⟨n, ⟨0, by omega⟩, fun _ => true, ?_⟩
  rw [ugNu_all_true]
  have h1 : C ^ 2 < (n : ℝ) + 1 := by linarith
  have h2 : Real.sqrt (C ^ 2) < Real.sqrt ((n : ℝ) + 1) :=
    Real.sqrt_lt_sqrt (by positivity) h1
  have h3 : C ≤ Real.sqrt (C ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
    exact le_abs_self C
  have h4 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  linarith

end UnboundedShockWitness

open UnboundedShockWitness

/-- The hypotheses of `clustershock_b_general_janson` hold at `ε = 1/4` on the `J = 2`
cluster-shock design with an unbounded disturbance. The statement also asserts that the
disturbance is unbounded
across `n`, that the sharing relation is not transitive, that the within-cluster covariance is
`1` (so `Ω` is not diagonal), and the CDF convergence. -/
theorem clustershock_b_general_janson_unbounded_witness (s : ℝ) :
    (∀ C : ℝ, ∃ (n : ℕ) (o : Fin (n + 3)) (ω : Fin (3 * (n + 3) * (n + 1)) → Bool),
        C < ugNu n o ω)
    ∧ (∀ n : ℕ, ∃ a b d : Fin (n + 3),
        Multiway.Linked (wtC n) Finset.univ a b
        ∧ Multiway.Linked (wtC n) Finset.univ b d
        ∧ ¬ Multiway.Linked (wtC n) Finset.univ a d)
    ∧ (∀ n : ℕ, ∫ ω, ugNu n ⟨0, by omega⟩ ω * ugNu n ⟨1, by omega⟩ ω
        ∂(coins (3 * (n + 3) * (n + 1))) = 1)
    ∧ Tendsto (fun n => ((coins (3 * (n + 3) * (n + 1))).map (fun ω =>
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ((sqrtPD (restrictedVar (redXt (n + 2))
              (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => 1) (fun _ => 1))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
              ((((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
                  ((redXt (n + 2))ᵀ *ᵥ (fun o => ugNu n o ω))) -
                (0 : Fin 1 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine ⟨ugNu_unbounded, wtLinked_not_transitive,
    fun n => (ug_hOm n ⟨0, by omega⟩ ⟨1, by omega⟩).trans (wtOmega_offDiag n), ?_⟩
  refine clustershock_b_general_janson (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    (fun n => coins (3 * (n + 3) * (n + 1))) (fun n => redXt (n + 2)) (fun _ => 1)
    (fun n => ugNu n)
    (fun n ω => ((redXt (n + 2))ᵀ * redXt (n + 2))⁻¹ *ᵥ
      ((redXt (n + 2))ᵀ *ᵥ (fun o => ugNu n o ω)))
    (fun _ => 0) wtC Finset.univ ugDep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    (fun n => redXt_scoreMap_isUnit (n + 2))
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => zero_le_one) 1 zero_lt_one (fun _ _ => le_refl 1)
    ug_hOm ug_hmean
    1 3 zero_lt_one (by norm_num) ?_ ug_integrable_pow_four ug_pow_four_le
    1 zero_lt_one ?_ (fun n => ⟨⟨0, by omega⟩⟩)
    (fun _ => 2) (fun n j _ γ => wtCluster_card n j γ)
    ((1 : ℝ) / 4) (by norm_num) (by norm_num) ?_ (fun _ => (1 : ℝ)) ?_ s
  · intro _ _
    simp [redXt, dotProduct]
  · intro n
    simp only [Fintype.card_fin]
    rw [redXt_transpose_mul_self]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  · simp only [Fintype.card_fin]
    exact gc_hGrate_eps
  · simp [dotProduct]

end UnboundedShockWitness

/-! ### Section C5. Part (c) with the limit law derived

The theorems below assume the hypotheses of the Theorem 5 half and prove the limit law `hclt`
used by `ClusterShock.clustershock_rateagnostic_c`, from either sentence of the corollary. The
ratio input `hratio` remains a hypothesis; Section C7 derives it. -/

section WaldDischarged

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {O : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)]
variable {Dm : Type*} [DecidableEq Dm]
variable {L : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, DecidableEq (L n)]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Corollary SM.D.3**, part (c), with the limit law derived from the first sentence:

> (c) `P(𝒱̂_n ≻ 0) → 1`, `𝟙{𝒱̂_n ≻ 0}𝒱̂_n^{-1/2}𝓡_n(β̂ − β) ⟶ᵈ N(0, I_r)`, and `𝒲 ⟶ᵈ χ²_r`.

The matrix `𝒱_n` is `restrictedVar X̃_n Ω_n 𝓡_n` with `Ω_n = Sharing.clusterOmega`. -/
theorem clustershock_rateagnostic_c_janson
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
      Tendsto (fun n => (Gb n ω : ℝ) ^ 3 / (Fintype.card (O n) : ℝ)) atTop (𝓝 0))
    (Vh : ℕ → Ω → Matrix rr rr ℝ)
    (hV : ∀ n ω, (restrictedVar (Xt n ω)
      (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) (Rn n)).PosDef)
    (hVmeas : ∀ n, Measurable fun ω => restrictedVar (Xt n ω)
      (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) (Rn n))
    (hVhherm : ∀ n ω, (Vh n ω).IsHermitian) (hVhmeas : ∀ n, Measurable (Vh n))
    (hratio : TendstoInMeasure P (fun n ω => rectFrobNorm
        ((sqrtPD (restrictedVar (Xt n ω)
              (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) (Rn n)))⁻¹
          * Vh n ω
          * (sqrtPD (restrictedVar (Xt n ω)
              (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) (Rn n)))⁻¹ - 1))
        atTop (fun _ => 0)) :
    Tendsto (fun n => P {ω | (Vh n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (Vh n ω))⁻¹)
            (WithLp.toLp 2 (Rn n *ᵥ (bhat n ω - β n)) : EuclideanSpace ℝ rr)) atTop
          (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ rr))
      ∧ TendstoInDistribution
          (fun n ω => Multiway.Wald.waldStat (Vh n ω)
            (WithLp.toLp 2 (Rn n *ᵥ (bhat n ω - β n)) : EuclideanSpace ℝ rr)) atTop
          (fun z : EuclideanSpace ℝ rr => ‖z‖ ^ 2) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ rr)) :=
  clustershock_rateagnostic_c P Xt
    (fun n ω => Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) Rn
    (fun n y => bhat n y - β n) Vh hV hVmeas hVhherm hVhmeas hratio
    (clustershock_a_general_janson_unconditional_vector h𝒟 P Xt Rn ν bhat β c dims sc ve
      hXtD hOmD hscore s2 hs2 θ hθ Gb B Cnu hB0 hCnu0 hnu hWvm hdep hA hsc hve hOm hmean hB
      hdesign hne hGb hGrate)

/-- Part (c) with the limit law derived from the second sentence (bounded conditional
fourth moments), at arbitrary `ε > 0`. -/
theorem clustershock_rateagnostic_c_janson_b
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
    (B C4 : ℝ) (hB0 : 0 < B) (hC40 : 0 < C4)
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
    (hint4 : ∀ᵐ ω ∂P, ∀ n o, Integrable (fun y => (ν n o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfour : ∀ᵐ ω ∂P, ∀ n o, ∫ y, (ν n o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hdesign : ∀ᵐ ω ∂P, ∀ n,
      (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n ω)ᵀ * Xt n ω)
    (hne : ∀ n, Nonempty (O n))
    (hGb : ∀ᵐ ω ∂P, ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n ω j) γ).card ≤ Gb n ω)
    (hGb1 : ∀ᵐ ω ∂P, ∀ n, 1 ≤ Gb n ω)
    (hGbN : ∀ᵐ ω ∂P, ∀ n, Gb n ω ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hGrate : ∀ᵐ ω ∂P, Tendsto (fun n => (Gb n ω : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0))
    (Vh : ℕ → Ω → Matrix rr rr ℝ)
    (hV : ∀ n ω, (restrictedVar (Xt n ω)
      (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) (Rn n)).PosDef)
    (hVmeas : ∀ n, Measurable fun ω => restrictedVar (Xt n ω)
      (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) (Rn n))
    (hVhherm : ∀ n ω, (Vh n ω).IsHermitian) (hVhmeas : ∀ n, Measurable (Vh n))
    (hratio : TendstoInMeasure P (fun n ω => rectFrobNorm
        ((sqrtPD (restrictedVar (Xt n ω)
              (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) (Rn n)))⁻¹
          * Vh n ω
          * (sqrtPD (restrictedVar (Xt n ω)
              (Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) (Rn n)))⁻¹ - 1))
        atTop (fun _ => 0)) :
    Tendsto (fun n => P {ω | (Vh n ω).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD (Vh n ω))⁻¹)
            (WithLp.toLp 2 (Rn n *ᵥ (bhat n ω - β n)) : EuclideanSpace ℝ rr)) atTop
          (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ rr))
      ∧ TendstoInDistribution
          (fun n ω => Multiway.Wald.waldStat (Vh n ω)
            (WithLp.toLp 2 (Rn n *ᵥ (bhat n ω - β n)) : EuclideanSpace ℝ rr)) atTop
          (fun z : EuclideanSpace ℝ rr => ‖z‖ ^ 2) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ rr)) :=
  clustershock_rateagnostic_c P Xt
    (fun n ω => Multiway.Sharing.clusterOmega (c n ω) dims (sc n ω) (ve n ω)) Rn
    (fun n y => bhat n y - β n) Vh hV hVmeas hVhherm hVhmeas hratio
    (clustershock_b_general_janson_unconditional_vector_anyEps h𝒟 P Xt Rn ν bhat β c dims sc ve
      hXtD hOmD hscore s2 hs2 θ hθ Gb B C4 hB0 hC40 hWvm hdep hA hsc hve hOm hmean hB
      hint4 hfour hdesign hne hGb hGb1 hGbN ε hε hGrate)

end WaldDischarged

/-! ### Section C5b. An example for part (c) -/

section WaldDischargedWitness

open Filter
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix
open Multiway.SteinCluster.FrozenDesignWitness
open Multiway.ClusterShock.FrozenGeneralShockWitness

/-- The hypotheses of `clustershock_rateagnostic_c_janson` hold on the `J = 2` cluster-shock
design of `ClusterShock.FrozenGeneralShockWitness`, which has a nontrivial `𝒟`, a random
`𝒟`-measurable design, `Ω` not diagonal, `Ḡ_n = 2` and `Ḡ_n³/n = 8/(n+3) → 0`. The variance
estimator `𝒱̂_n` is `𝒱_n` inflated by `1 + 1/(n+1)`. -/
theorem clustershock_rateagnostic_c_janson_witness :
    Pw {y : Aw | y.1 = true} = 2⁻¹
    ∧ (∃ Bs : Set Aw, MeasurableSet Bs ∧ ¬ MeasurableSet[Dw] Bs)
    ∧ ¬ (∀ᵐ ω ∂Pw, condExpKernel Pw Dw ω = Pw)
    ∧ (∀ n : ℕ, ∃ a b d : Fin (n + 3),
        Multiway.Linked (wtC n) Finset.univ a b
        ∧ Multiway.Linked (wtC n) Finset.univ b d
        ∧ ¬ Multiway.Linked (wtC n) Finset.univ a d)
    ∧ (∀ᵐ ω ∂Pw, ∀ n : ℕ, ∫ y, coinShockSumA (gcIdx n) ⟨0, by omega⟩ y
        * coinShockSumA (gcIdx n) ⟨1, by omega⟩ y ∂(condExpKernel Pw Dw ω) = 1)
    ∧ (∀ (n : ℕ) (y : Aw), rectFrobNorm ((sqrtPD (restrictedVar (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ * gcVh n y
        * (sqrtPD (restrictedVar (gcXt n y)
          (Multiway.Sharing.clusterOmega (wtC n) Finset.univ (fun _ => (1 : ℝ))
            (fun _ => (1 : ℝ)))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)))⁻¹ - 1) = 1 / ((n : ℝ) + 1))
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
        = fun (n : ℕ) (_ : Aw) => 1 / ((n : ℝ) + 1) := funext fun n => funext fun y => gc_ratio n y
    rw [hfun]
    exact Multiway.RateAgnostic.tendstoInMeasure_zero_of_tendsto_const
      tendsto_one_div_add_atTop_nhds_zero_nat
  let _ : ∀ ω : Aw, IsProbabilityMeasure (condExpKernel Pw Dw ω) := fun _ => inferInstance
  have hmain := clustershock_rateagnostic_c_janson (O := fun n => Fin (n + 3)) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    Dw_le Pw gcXt (fun _ => 1) (fun n => coinShockSumA (gcIdx n)) gcBhat (fun _ => 0)
    (fun n _ => wtC n) Finset.univ (fun _ _ _ => 1) (fun _ _ _ => 1)
    gc_hXtD (fun _ _ _ => measurable_const) (fun n y => sub_zero _)
    1 zero_lt_one 1 zero_lt_one (fun _ _ => 2)
    1 3 zero_le_one (by norm_num)
    (fun n o y => by simpa using abs_coinShockSumA_le (gcIdx n) o y)
    gc_hWvm
    (by
      filter_upwards [map_snd_condExpKernel] with ω hω
      exact ⟨fun n => gcDep hω n, fun _ _ _ => Iff.rfl⟩)
    (by
      refine Filter.Eventually.of_forall fun ω n => ?_
      rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, scoreMap_smul (sgnA_mul ω)]
      exact redXt_scoreMap_isUnit (n + 2))
    (Filter.Eventually.of_forall fun _ _ _ _ => zero_le_one)
    (Filter.Eventually.of_forall fun _ _ _ => le_refl 1)
    (by
      filter_upwards [map_snd_condExpKernel] with ω hω
      intro n o o'
      refine (integral_of_snd hω ((measurable_coinShockSum (gcIdx n) o).mul
        (measurable_coinShockSum (gcIdx n) o'))).trans ?_
      simp only [Pi.mul_apply]
      exact gc_hOm n o o')
    (by
      filter_upwards [map_snd_condExpKernel] with ω hω
      intro n o
      exact (integral_of_snd hω (measurable_coinShockSum (gcIdx n) o)).trans
        (integral_coinShockSum (gcIdx n) o))
    (by
      refine Filter.Eventually.of_forall fun ω n o => ?_
      have h : (fun k => gcXt n ω o k) ⬝ᵥ (fun k => gcXt n ω o k) = 1 := by
        simp [gcXt, redXt, dotProduct, sgnA_mul ω]
      rw [h]
      norm_num)
    (by
      refine Filter.Eventually.of_forall fun ω n => ?_
      have h : (gcXt n ω)ᵀ * gcXt n ω
          = (((n + 2 : ℕ) : ℝ) + 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
        rw [show gcXt n ω = sgnA ω • redXt (n + 2) from rfl, gram_smul (sgnA_mul ω),
          redXt_transpose_mul_self]
      rw [h, Fintype.card_fin]
      refine le_of_eq ?_
      congr 1
      push_cast
      ring)
    (fun n => ⟨⟨0, by omega⟩⟩)
    (Filter.Eventually.of_forall fun _ n j _ γ => wtCluster_card n j γ)
    (by
      refine Filter.Eventually.of_forall fun _ => ?_
      simp only [Fintype.card_fin]
      exact gc_hGrate_cube)
    gcVh gc_hVpd gc_hVmeas gc_hVhherm gc_hVhmeas hratio
  exact ⟨Pw_fst true, Dw_proper, condExpKernel_ne_Pw, wtLinked_not_transitive, gc_within_cond,
    gc_ratio, hmain.1, hmain.2.1, hmain.2.2⟩

end WaldDischargedWitness

/-! ### Section C6. An example at `r = 2`

The observation set is `{0,…,n+2} × {0,1}` and the regressors are the side indicators scaled by
`1` and `2`, so `X̃'X̃ = diag(n+3, 4(n+3))`. The clustering maps are those of `ClusterShock.wtC`
applied to the base index, so both sides share the cluster shocks and `𝒱_{n,01} > 0`; hence
`𝒱_n` is not a multiple of the identity. The model has `J = 2` and `Ḡ_n = 4`, its sharing
relation is not transitive and `Ω` is not diagonal. The design is deterministic. -/

section ShockRank2Witness

open Filter
open Multiway.Multilinear
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace ShockRank2Witness

/-! #### The design and its Gram matrix -/

/-- The two regressor scales, `1` on side `0` and `2` on side `1`. -/
noncomputable def cr2w : Fin 2 → ℝ := fun k => if k = 0 then 1 else 2

theorem cr2w_pos (k : Fin 2) : (0 : ℝ) < cr2w k := by
  fin_cases k <;> norm_num [cr2w]

theorem cr2w_sq_le (k : Fin 2) : (cr2w k) ^ 2 ≤ (2 : ℝ) ^ 2 := by
  fin_cases k <;> norm_num [cr2w]

/-- `x̃_{(i,s)} = (1{s=0}, 2·1{s=1})`, the scaled side indicators. -/
noncomputable def cr2Xt (n : ℕ) : Matrix (Fin (n + 3) × Fin 2) (Fin 2) ℝ :=
  fun p k => if p.2 = k then cr2w k else 0

noncomputable def cr2d (n : ℕ) : Fin 2 → ℝ := fun k => ((n : ℝ) + 3) * (cr2w k) ^ 2

theorem cr2d_pos (n : ℕ) (k : Fin 2) : 0 < cr2d n k := by
  have h := cr2w_pos k
  have hn : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  unfold cr2d
  positivity

theorem cr2d_ne_zero (n : ℕ) (k : Fin 2) : cr2d n k ≠ 0 := ne_of_gt (cr2d_pos n k)

theorem cr2Gram (n : ℕ) : (cr2Xt n)ᵀ * cr2Xt n = Matrix.diagonal (cr2d n) := by
  ext j k
  rw [Matrix.mul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type]
  have hinner : ∀ i : Fin (n + 3),
      (∑ s : Fin 2, (cr2Xt n)ᵀ j (i, s) * cr2Xt n (i, s) k)
        = if j = k then (cr2w k) ^ 2 else 0 := by
    intro i
    fin_cases j <;> fin_cases k <;>
      simp [cr2Xt, cr2w, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases h : j = k
  · subst h
    rw [if_pos rfl, if_pos rfl]
    unfold cr2d
    push_cast
    ring
  · rw [if_neg h, if_neg h, mul_zero]

theorem cr2_inv_gram (n : ℕ) :
    ((cr2Xt n)ᵀ * cr2Xt n)⁻¹ = Matrix.diagonal (fun k => (cr2d n k)⁻¹) := by
  rw [cr2Gram]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal,
    show (fun k => cr2d n k * (cr2d n k)⁻¹) = (1 : Fin 2 → ℝ) from
      funext fun k => mul_inv_cancel₀ (cr2d_ne_zero n k)]
  exact Matrix.diagonal_one

theorem cr2_scoreMap (n : ℕ) :
    scoreMap (cr2Xt n) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.diagonal (fun k => (cr2d n k)⁻¹) := by
  rw [scoreMap, Matrix.transpose_one, Matrix.mul_one, cr2_inv_gram]

theorem cr2_hA (n : ℕ) :
    Function.Injective (scoreMap (cr2Xt n) (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec := by
  refine Matrix.mulVec_injective_of_isUnit ?_
  rw [cr2_scoreMap, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [Fin.prod_univ_two]
  exact mul_ne_zero (inv_ne_zero (cr2d_ne_zero n 0)) (inv_ne_zero (cr2d_ne_zero n 1))

theorem cr2_row_dot (n : ℕ) (p : Fin (n + 3) × Fin 2) :
    (fun k => cr2Xt n p k) ⬝ᵥ (fun k => cr2Xt n p k) ≤ (2 : ℝ) ^ 2 := by
  have hval : (fun k => cr2Xt n p k) ⬝ᵥ (fun k => cr2Xt n p k) = (cr2w p.2) ^ 2 := by
    obtain ⟨i, s⟩ := p
    fin_cases s <;> simp [cr2Xt, cr2w, dotProduct, Fin.sum_univ_two] <;> ring
  rw [hval]
  exact cr2w_sq_le p.2

theorem cr2_card (n : ℕ) : Fintype.card (Fin (n + 3) × Fin 2) = (n + 3) * 2 := by
  simp

theorem cr2_hdesign (n : ℕ) :
    (((1 : ℝ) / 2) * (Fintype.card (Fin (n + 3) × Fin 2) : ℝ)) •
        (1 : Matrix (Fin 2) (Fin 2) ℝ)
      ≤ (cr2Xt n)ᵀ * cr2Xt n := by
  have hc : (((1 : ℝ) / 2) * (Fintype.card (Fin (n + 3) × Fin 2) : ℝ)) = (n : ℝ) + 3 := by
    rw [cr2_card]
    push_cast
    ring
  have hdiff : (cr2Xt n)ᵀ * cr2Xt n - (((1 : ℝ) / 2)
        * (Fintype.card (Fin (n + 3) × Fin 2) : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.diagonal (fun k => cr2d n k - ((n : ℝ) + 3)) := by
    rw [cr2Gram, hc]
    ext j k
    by_cases h : j = k
    · subst h
      simp [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, h]
  rw [Matrix.le_iff, hdiff]
  refine Matrix.posSemidef_diagonal_iff.mpr fun k => ?_
  have hw : (1 : ℝ) ≤ (cr2w k) ^ 2 := by fin_cases k <;> norm_num [cr2w]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 3 := by positivity
  unfold cr2d
  nlinarith

/-! #### The clustering, the covariance matrix, and the disturbance -/

/-- The two clustering maps, read off the base index only, so that the cluster shocks are
common to the two sides. -/
def cr2C (n : ℕ) (j : Fin 2) (p : Fin (n + 3) × Fin 2) : Fin (n + 3) := wtC n j p.1

noncomputable def cr2Om (n : ℕ) : Matrix (Fin (n + 3) × Fin 2) (Fin (n + 3) × Fin 2) ℝ :=
  Multiway.Sharing.clusterOmega (cr2C n) Finset.univ (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))

theorem cr2Om_nonneg (n : ℕ) (o o' : Fin (n + 3) × Fin 2) : (0 : ℝ) ≤ cr2Om n o o' := by
  rw [cr2Om, Multiway.Sharing.clusterOmega_apply]
  have h1 : (0 : ℝ) ≤ ∑ j ∈ (Finset.univ : Finset (Fin 2)),
      (if Multiway.SameOn (cr2C n) {j} o o' then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun j _ => by split <;> norm_num
  have h2 : (0 : ℝ) ≤ (if o = o' then (1 : ℝ) else 0) := by split <;> norm_num
  linarith

/-- The two sides of one base index share both cluster shocks, so this entry of `Ω` is
`2`. -/
theorem cr2Om_sides (n : ℕ) (i : Fin (n + 3)) : cr2Om n (i, 0) (i, 1) = 2 := by
  rw [cr2Om, Multiway.Sharing.clusterOmega_apply, Fin.sum_univ_two]
  have e0 : Multiway.SameOn (cr2C n) {(0 : Fin 2)} (i, (0 : Fin 2)) (i, (1 : Fin 2)) := by
    rw [sameOn_singleton_iff]
    rfl
  have e1 : Multiway.SameOn (cr2C n) {(1 : Fin 2)} (i, (0 : Fin 2)) (i, (1 : Fin 2)) := by
    rw [sameOn_singleton_iff]
    rfl
  have e2 : ¬ ((i, (0 : Fin 2)) = ((i, (1 : Fin 2)) : Fin (n + 3) × Fin 2)) := by
    intro h
    have h2 : (0 : Fin 2) = 1 := congrArg Prod.snd h
    exact absurd h2 (by decide)
  rw [if_pos e0, if_pos e1, if_neg e2]
  norm_num

/-- Base indices `0` and `1` share the first cluster and not the second, so this entry of
`Ω` is `1`. -/
theorem cr2Om_offDiag (n : ℕ) :
    cr2Om n ((⟨0, by omega⟩ : Fin (n + 3)), (0 : Fin 2))
      ((⟨1, by omega⟩ : Fin (n + 3)), (0 : Fin 2)) = 1 := by
  rw [cr2Om, Multiway.Sharing.clusterOmega_apply, Fin.sum_univ_two]
  have e0 : Multiway.SameOn (cr2C n) {(0 : Fin 2)}
      ((⟨0, by omega⟩ : Fin (n + 3)), (0 : Fin 2))
      ((⟨1, by omega⟩ : Fin (n + 3)), (0 : Fin 2)) := by
    rw [sameOn_singleton_iff]
    show wtC n 0 (⟨0, by omega⟩ : Fin (n + 3)) = wtC n 0 (⟨1, by omega⟩ : Fin (n + 3))
    rw [Fin.ext_iff, wtC_val, wtC_val, ite_eq_left rfl, ite_eq_left rfl]
    simp
  have e1 : ¬ Multiway.SameOn (cr2C n) {(1 : Fin 2)}
      ((⟨0, by omega⟩ : Fin (n + 3)), (0 : Fin 2))
      ((⟨1, by omega⟩ : Fin (n + 3)), (0 : Fin 2)) := by
    rw [sameOn_singleton_iff]
    show ¬ (wtC n 1 (⟨0, by omega⟩ : Fin (n + 3)) = wtC n 1 (⟨1, by omega⟩ : Fin (n + 3)))
    rw [Fin.ext_iff, wtC_val, wtC_val, ite_eq_right (by decide), ite_eq_right (by decide)]
    simp
  have e2 : ¬ (((⟨0, by omega⟩ : Fin (n + 3)), (0 : Fin 2))
      = (((⟨1, by omega⟩ : Fin (n + 3)), (0 : Fin 2)) : Fin (n + 3) × Fin 2)) := by
    intro h
    have := congrArg Prod.fst h
    rw [Fin.ext_iff] at this
    simp at this
  rw [if_pos e0, if_neg e1, if_neg e2]
  norm_num

/-- The sharing relation on the product index set is the base one. -/
theorem cr2Linked_iff (n : ℕ) (o o' : Fin (n + 3) × Fin 2) :
    Multiway.Linked (cr2C n) Finset.univ o o'
      ↔ Multiway.Linked (wtC n) Finset.univ o.1 o'.1 := Iff.rfl

/-- The sharing relation is not transitive. -/
theorem cr2Linked_not_transitive (n : ℕ) :
    ∃ a b d : Fin (n + 3) × Fin 2, Multiway.Linked (cr2C n) Finset.univ a b
      ∧ Multiway.Linked (cr2C n) Finset.univ b d
      ∧ ¬ Multiway.Linked (cr2C n) Finset.univ a d := by
  obtain ⟨a, b, d, h1, h2, h3⟩ := wtLinked_not_transitive n
  exact ⟨(a, 0), (b, 0), (d, 0), h1, h2, h3⟩

theorem cr2Cluster_card (n : ℕ) (j : Fin 2) (γ : Fin (n + 3)) :
    (cluster (cr2C n j) γ).card ≤ 4 := by
  classical
  have hsub : cluster (cr2C n j) γ ⊆ (cluster (wtC n j) γ) ×ˢ (Finset.univ : Finset (Fin 2)) := by
    intro o ho
    rw [mem_cluster] at ho
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    rw [mem_cluster]
    exact ho
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have := wtCluster_card n j γ
  omega

/-- The coin that component `k` of observation `(i,s)` reads, with index twice the base model's
index for `k`, plus the side `s` for the idiosyncratic component `k = 2`. -/
def cr2Idx (n : ℕ) (p : Fin (n + 3) × Fin 2) (k : Fin 3) : Fin (3 * (n + 3) * 2) :=
  ⟨2 * (wtIdx n p.1 k).val + (if k = (2 : Fin 3) then p.2.val else 0), by
    have h1 : (wtIdx n p.1 k).val < 3 * (n + 3) := (wtIdx n p.1 k).isLt
    have h2 : p.2.val < 2 := p.2.isLt
    have h3 : (if k = (2 : Fin 3) then p.2.val else 0) < 2 := by split <;> omega
    omega⟩

theorem cr2Idx_eq_iff_gen (n : ℕ) (o o' : Fin (n + 3) × Fin 2) (k k' : Fin 3) :
    cr2Idx n o k = cr2Idx n o' k' ↔
      (wtIdx n o.1 k = wtIdx n o'.1 k'
        ∧ (if k = (2 : Fin 3) then o.2.val else 0)
          = (if k' = (2 : Fin 3) then o'.2.val else 0)) := by
  have hb : o.2.val < 2 := o.2.isLt
  have hb' : o'.2.val < 2 := o'.2.isLt
  have h1 : (if k = (2 : Fin 3) then o.2.val else 0) < 2 := by split <;> omega
  have h2 : (if k' = (2 : Fin 3) then o'.2.val else 0) < 2 := by split <;> omega
  constructor
  · intro h
    have hv : 2 * (wtIdx n o.1 k).val + (if k = (2 : Fin 3) then o.2.val else 0)
        = 2 * (wtIdx n o'.1 k').val + (if k' = (2 : Fin 3) then o'.2.val else 0) :=
      congrArg Fin.val h
    exact ⟨Fin.ext (by omega), by omega⟩
  · rintro ⟨hw, hs⟩
    refine Fin.ext ?_
    show 2 * (wtIdx n o.1 k).val + (if k = (2 : Fin 3) then o.2.val else 0)
      = 2 * (wtIdx n o'.1 k').val + (if k' = (2 : Fin 3) then o'.2.val else 0)
    rw [hw, hs]

theorem cr2Idx_component (n : ℕ) (o o' : Fin (n + 3) × Fin 2) (k k' : Fin 3)
    (h : cr2Idx n o k = cr2Idx n o' k') : k = k' :=
  wtIdx_component n o.1 o'.1 k k' ((cr2Idx_eq_iff_gen n o o' k k').mp h).1

theorem cr2Idx_ne_of_not_linked (n : ℕ) (o o' : Fin (n + 3) × Fin 2)
    (h : ¬ Multiway.Linked (cr2C n) Finset.univ o o') (k k' : Fin 3) :
    cr2Idx n o k ≠ cr2Idx n o' k' := by
  intro heq
  have hkk := cr2Idx_component n o o' k k' heq
  subst hkk
  obtain ⟨hw, hs⟩ := (cr2Idx_eq_iff_gen n o o' k k).mp heq
  have hlab := (wtIdx_eq_iff n o.1 o'.1 k).mp hw
  refine h ?_
  fin_cases k
  · exact ⟨0, Finset.mem_univ 0, (wtLab_eq_zero_iff n o.1 o'.1).mp hlab⟩
  · exact ⟨1, Finset.mem_univ 1, (wtLab_eq_one_iff n o.1 o'.1).mp hlab⟩
  · have hbase : o.1 = o'.1 := (wtLab_eq_two_iff n o.1 o'.1).mp hlab
    exact ⟨0, Finset.mem_univ 0, by
      show wtC n 0 o.1 = wtC n 0 o'.1
      rw [hbase]⟩

/-- The second moments of the model are the entries of `clusterOmega`. -/
theorem cr2_hOm (n : ℕ) (o o' : Fin (n + 3) × Fin 2) :
    ∫ ω, shockSum (cr2Idx n) o ω * shockSum (cr2Idx n) o' ω ∂(coins (3 * (n + 3) * 2))
      = cr2Om n o o' := by
  rw [integral_shockSum_mul (cr2Idx_component n) o o', cr2Om,
    Multiway.Sharing.clusterOmega_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  have e0 : (cr2Idx n o 0 = cr2Idx n o' 0) ↔ Multiway.SameOn (cr2C n) {0} o o' := by
    rw [cr2Idx_eq_iff_gen, sameOn_singleton_iff]
    constructor
    · rintro ⟨hw, -⟩
      exact (wtLab_eq_zero_iff n o.1 o'.1).mp ((wtIdx_eq_iff n o.1 o'.1 0).mp hw)
    · intro h
      exact ⟨(wtIdx_eq_iff n o.1 o'.1 0).mpr ((wtLab_eq_zero_iff n o.1 o'.1).mpr h), by simp⟩
  have e1 : (cr2Idx n o 1 = cr2Idx n o' 1) ↔ Multiway.SameOn (cr2C n) {1} o o' := by
    rw [cr2Idx_eq_iff_gen, sameOn_singleton_iff]
    constructor
    · rintro ⟨hw, -⟩
      exact (wtLab_eq_one_iff n o.1 o'.1).mp ((wtIdx_eq_iff n o.1 o'.1 1).mp hw)
    · intro h
      exact ⟨(wtIdx_eq_iff n o.1 o'.1 1).mpr ((wtLab_eq_one_iff n o.1 o'.1).mpr h), by simp⟩
  have e2 : (cr2Idx n o 2 = cr2Idx n o' 2) ↔ (o = o') := by
    rw [cr2Idx_eq_iff_gen]
    constructor
    · rintro ⟨hw, hs⟩
      have hbase : o.1 = o'.1 := (wtLab_eq_two_iff n o.1 o'.1).mp
        ((wtIdx_eq_iff n o.1 o'.1 2).mp hw)
      have hside : o.2 = o'.2 := by
        refine Fin.ext ?_
        simpa using hs
      exact Prod.ext hbase hside
    · rintro rfl
      exact ⟨rfl, rfl⟩
  rw [if_congr e0 rfl rfl, if_congr e1 rfl rfl, if_congr e2 rfl rfl]

noncomputable def cr2Dep (n : ℕ) :
    DepGraph (shockSum (cr2Idx n)) (coins (3 * (n + 3) * 2)) :=
  shockDep (cr2Idx n) (Multiway.Linked (cr2C n) Finset.univ)
    (fun _ => ⟨0, Finset.mem_univ 0, rfl⟩)
    (fun _ _ h => Multiway.Sharing.linked_symm h)
    (cr2Idx_ne_of_not_linked n)

/-! #### `𝒱_n` is not a multiple of the identity -/

theorem cr2_scoreVar_offDiag_pos (n : ℕ) : (0 : ℝ) < scoreVar (cr2Xt n) (cr2Om n) 0 1 := by
  classical
  have hentry : scoreVar (cr2Xt n) (cr2Om n) 0 1
      = ∑ p : Fin (n + 3) × Fin 2, (∑ q : Fin (n + 3) × Fin 2,
          cr2Xt n q 0 * cr2Om n q p) * cr2Xt n p 1 := by
    rw [scoreVar, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
  have hnn : ∀ p : Fin (n + 3) × Fin 2, (0 : ℝ) ≤ (∑ q : Fin (n + 3) × Fin 2,
      cr2Xt n q 0 * cr2Om n q p) * cr2Xt n p 1 := by
    intro p
    refine mul_nonneg (Finset.sum_nonneg fun q _ => mul_nonneg ?_ (cr2Om_nonneg n q p)) ?_
    · unfold cr2Xt
      split
      · exact (cr2w_pos 0).le
      · exact le_refl 0
    · unfold cr2Xt
      split
      · exact (cr2w_pos 1).le
      · exact le_refl 0
  set p0 : Fin (n + 3) × Fin 2 := (⟨0, by omega⟩, 1) with hp0
  set q0 : Fin (n + 3) × Fin 2 := (⟨0, by omega⟩, 0) with hq0
  have hq0x : cr2Xt n q0 0 = 1 := by simp [cr2Xt, cr2w, hq0]
  have hp0x : cr2Xt n p0 1 = 2 := by simp [cr2Xt, cr2w, hp0]
  have hOm0 : cr2Om n q0 p0 = 2 := cr2Om_sides n ⟨0, by omega⟩
  have hinner : (2 : ℝ) ≤ (∑ q : Fin (n + 3) × Fin 2, cr2Xt n q 0 * cr2Om n q p0) := by
    have hsingle : cr2Xt n q0 0 * cr2Om n q0 p0 ≤
        ∑ q : Fin (n + 3) × Fin 2, cr2Xt n q 0 * cr2Om n q p0 := by
      refine Finset.single_le_sum (f := fun q => cr2Xt n q 0 * cr2Om n q p0) ?_ (Finset.mem_univ q0)
      intro q _
      refine mul_nonneg ?_ (cr2Om_nonneg n q p0)
      unfold cr2Xt
      split
      · exact (cr2w_pos 0).le
      · exact le_refl 0
    rw [hq0x, hOm0] at hsingle
    linarith
  have hterm : (4 : ℝ) ≤ (∑ q : Fin (n + 3) × Fin 2, cr2Xt n q 0 * cr2Om n q p0) * cr2Xt n p0 1 := by
    rw [hp0x]
    linarith
  have hbig : (4 : ℝ) ≤ scoreVar (cr2Xt n) (cr2Om n) 0 1 := by
    rw [hentry]
    refine le_trans hterm ?_
    exact Finset.single_le_sum (f := fun p => (∑ q : Fin (n + 3) × Fin 2,
      cr2Xt n q 0 * cr2Om n q p) * cr2Xt n p 1) (fun p _ => hnn p) (Finset.mem_univ p0)
  linarith

theorem cr2_restrictedVar_offDiag (n : ℕ) :
    restrictedVar (cr2Xt n) (cr2Om n) (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1
      = (cr2d n 0)⁻¹ * scoreVar (cr2Xt n) (cr2Om n) 0 1 * (cr2d n 1)⁻¹ := by
  rw [restrictedVar, cr2_scoreMap, Matrix.diagonal_transpose, Matrix.mul_diagonal,
    Matrix.diagonal_mul]

/-- `𝒱_n ≠ c·I₂` for every `c`, since its `(0,1)` entry is strictly positive. -/
theorem cr2_restrictedVar_ne_smul_one (n : ℕ) (t : ℝ) :
    restrictedVar (cr2Xt n) (cr2Om n) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      ≠ t • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [cr2_restrictedVar_offDiag] at h01
  have hz : (t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = 0 := by
    simp [Matrix.one_apply_ne, (by decide : (0 : Fin 2) ≠ 1)]
  rw [hz] at h01
  have hpos : (0 : ℝ) < (cr2d n 0)⁻¹ * scoreVar (cr2Xt n) (cr2Om n) 0 1 * (cr2d n 1)⁻¹ := by
    have h0 := cr2d_pos n 0
    have h1 := cr2d_pos n 1
    have h2 := cr2_scoreVar_offDiag_pos n
    positivity
  rw [h01] at hpos
  exact lt_irrefl 0 hpos

/-! #### The two rates -/

theorem cr2_card_atTop : Tendsto (fun n : ℕ => (((n + 3) * 2 : ℕ) : ℝ)) atTop atTop := by
  have hcast : ∀ n : ℕ, (((n + 3) * 2 : ℕ) : ℝ) = ((n : ℝ) + 3) * 2 := fun n => by
    push_cast; ring
  simp only [hcast]
  exact Filter.Tendsto.atTop_mul_const (by norm_num)
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem cr2_hGrate_cube :
    Tendsto (fun n : ℕ => (((4 : ℕ)) : ℝ) ^ 3 / (((n + 3) * 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  simpa using (tendsto_const_nhds (x := (((4 : ℕ)) : ℝ) ^ 3)
    (f := atTop (α := ℕ))).div_atTop cr2_card_atTop

theorem cr2_hGrate_eps :
    Tendsto (fun n : ℕ => (((4 : ℕ)) : ℝ) ^ ((3 : ℝ) - (1 : ℝ) / 4)
      / (((n + 3) * 2 : ℕ) : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 4)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (((n + 3) * 2 : ℕ) : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 4))
      atTop atTop := (tendsto_rpow_atTop (by norm_num)).comp cr2_card_atTop
  simpa using (tendsto_const_nhds (x := (((4 : ℕ)) : ℝ) ^ ((3 : ℝ) - (1 : ℝ) / 4))
    (f := atTop (α := ℕ))).div_atTop h1

/-- The unit direction along which the CDF form is read. -/
noncomputable def cr2b : Fin 2 → ℝ := ![1, 0]

theorem cr2b_dot : cr2b ⬝ᵥ cr2b = 1 := by
  simp [cr2b, dotProduct, Fin.sum_univ_two]

theorem cr2_bounded (n : ℕ) (o : Fin (n + 3) × Fin 2) (ω : Fin (3 * (n + 3) * 2) → Bool) :
    |shockSum (cr2Idx n) o ω| ≤ 3 := by
  simpa using abs_shockSum_le (cr2Idx n) o ω

theorem cr2_pow_four (n : ℕ) (o : Fin (n + 3) × Fin 2)
    (ω : Fin (3 * (n + 3) * 2) → Bool) : (shockSum (cr2Idx n) o ω) ^ 4 ≤ (3 : ℝ) ^ 4 := by
  have h1 : (shockSum (cr2Idx n) o ω) ^ 4 = |shockSum (cr2Idx n) o ω| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [h1]
  exact pow_le_pow_left₀ (abs_nonneg _) (cr2_bounded n o ω) 4

theorem cr2_int_four (n : ℕ) (o : Fin (n + 3) × Fin 2) :
    Integrable (fun ω => (shockSum (cr2Idx n) o ω) ^ 4) (coins (3 * (n + 3) * 2)) := by
  refine Multiway.SteinCluster.integrable_of_abs_le
    ((measurable_shockSum (cr2Idx n) o).pow_const 4) (C := (3 : ℝ) ^ 4) (fun ω => ?_)
  rw [abs_of_nonneg (by positivity)]
  exact cr2_pow_four n o ω

theorem cr2_four_le (n : ℕ) (o : Fin (n + 3) × Fin 2) :
    ∫ ω, (shockSum (cr2Idx n) o ω) ^ 4 ∂(coins (3 * (n + 3) * 2)) ≤ (3 : ℝ) ^ 4 := by
  calc ∫ ω, (shockSum (cr2Idx n) o ω) ^ 4 ∂(coins (3 * (n + 3) * 2))
      ≤ ∫ _ω, (3 : ℝ) ^ 4 ∂(coins (3 * (n + 3) * 2)) :=
        integral_mono (cr2_int_four n o) (integrable_const _) (fun ω => cr2_pow_four n o ω)
    _ = (3 : ℝ) ^ 4 := by simp

end ShockRank2Witness

open ShockRank2Witness

/-- The hypotheses of `clustershock_a_general_janson` hold at `r = K = 2`, with `𝓡_n = I₂` and
`𝒱_n` not a multiple of the identity. The statement also asserts that the sharing relation is not
transitive and that `Ω` has a nonzero off-diagonal entry. -/
theorem clustershock_a_general_janson_rank2_witness (s : ℝ) :
    (∀ (n : ℕ) (t : ℝ), restrictedVar (cr2Xt n) (cr2Om n) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        ≠ t • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ n : ℕ, ∃ a b d : Fin (n + 3) × Fin 2,
        Multiway.Linked (cr2C n) Finset.univ a b
        ∧ Multiway.Linked (cr2C n) Finset.univ b d
        ∧ ¬ Multiway.Linked (cr2C n) Finset.univ a d)
    ∧ (∀ n : ℕ, cr2Om n ((⟨0, by omega⟩ : Fin (n + 3)), (0 : Fin 2))
        ((⟨1, by omega⟩ : Fin (n + 3)), (0 : Fin 2)) = 1)
    ∧ Tendsto (fun n => ((coins (3 * (n + 3) * 2)).map (fun ω =>
        cr2b ⬝ᵥ ((sqrtPD (restrictedVar (cr2Xt n) (cr2Om n)
              (1 : Matrix (Fin 2) (Fin 2) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
              ((((cr2Xt n)ᵀ * cr2Xt n)⁻¹ *ᵥ
                  ((cr2Xt n)ᵀ *ᵥ (fun o => shockSum (cr2Idx n) o ω))) -
                (0 : Fin 2 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine ⟨cr2_restrictedVar_ne_smul_one, cr2Linked_not_transitive, cr2Om_offDiag, ?_⟩
  refine clustershock_a_general_janson (O := fun n => Fin (n + 3) × Fin 2) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    (fun n => coins (3 * (n + 3) * 2)) cr2Xt (fun _ => 1)
    (fun n => shockSum (cr2Idx n))
    (fun n ω => ((cr2Xt n)ᵀ * cr2Xt n)⁻¹ *ᵥ
      ((cr2Xt n)ᵀ *ᵥ (fun o => shockSum (cr2Idx n) o ω)))
    (fun _ => 0) cr2C Finset.univ cr2Dep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    cr2_hA
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => zero_le_one) 1 zero_lt_one (fun _ _ => le_refl 1)
    cr2_hOm (fun n o => integral_shockSum (cr2Idx n) o)
    2 3 (by norm_num) (by norm_num) cr2_row_dot cr2_bounded
    ((1 : ℝ) / 2) (by norm_num) cr2_hdesign (fun n => ⟨(⟨0, by omega⟩, 0)⟩)
    (fun _ => 4) (fun n j _ γ => cr2Cluster_card n j γ) ?_ cr2b cr2b_dot s
  · simp only [cr2_card]
    exact cr2_hGrate_cube

/-- The hypotheses of `clustershock_b_general_janson_anyEps` hold at `r = K = 2` and
`ε = 1/4` on the same design, where `Ḡ_n = 4` and the sample size is `2(n+3)`. -/
theorem clustershock_b_general_janson_rank2_witness (s : ℝ) :
    (∀ (n : ℕ) (t : ℝ), restrictedVar (cr2Xt n) (cr2Om n) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        ≠ t • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ n : ℕ, ∃ a b d : Fin (n + 3) × Fin 2,
        Multiway.Linked (cr2C n) Finset.univ a b
        ∧ Multiway.Linked (cr2C n) Finset.univ b d
        ∧ ¬ Multiway.Linked (cr2C n) Finset.univ a d)
    ∧ Tendsto (fun n => ((coins (3 * (n + 3) * 2)).map (fun ω =>
        cr2b ⬝ᵥ ((sqrtPD (restrictedVar (cr2Xt n) (cr2Om n)
              (1 : Matrix (Fin 2) (Fin 2) ℝ)))⁻¹ *ᵥ
            ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
              ((((cr2Xt n)ᵀ * cr2Xt n)⁻¹ *ᵥ
                  ((cr2Xt n)ᵀ *ᵥ (fun o => shockSum (cr2Idx n) o ω))) -
                (0 : Fin 2 → ℝ)))))).real (Set.Iic s)) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic s))) := by
  refine ⟨cr2_restrictedVar_ne_smul_one, cr2Linked_not_transitive, ?_⟩
  refine clustershock_b_general_janson_anyEps (O := fun n => Fin (n + 3) × Fin 2) (Dm := Fin 2)
    (L := fun n => Fin (n + 3))
    (fun n => coins (3 * (n + 3) * 2)) cr2Xt (fun _ => 1)
    (fun n => shockSum (cr2Idx n))
    (fun n ω => ((cr2Xt n)ᵀ * cr2Xt n)⁻¹ *ᵥ
      ((cr2Xt n)ᵀ *ᵥ (fun o => shockSum (cr2Idx n) o ω)))
    (fun _ => 0) cr2C Finset.univ cr2Dep (fun _ _ _ => Iff.rfl) (fun _ _ => by simp)
    cr2_hA
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => zero_le_one) 1 zero_lt_one (fun _ _ => le_refl 1)
    cr2_hOm (fun n o => integral_shockSum (cr2Idx n) o)
    2 3 (by norm_num) (by norm_num) cr2_row_dot cr2_int_four cr2_four_le
    ((1 : ℝ) / 2) (by norm_num) cr2_hdesign (fun n => ⟨(⟨0, by omega⟩, 0)⟩)
    (fun _ => 4) (fun n j _ γ => cr2Cluster_card n j γ)
    (fun _ => by norm_num) ?_ ((1 : ℝ) / 4) (by norm_num) ?_ cr2b cr2b_dot s
  · intro n
    rw [cr2_card]
    omega
  · simp only [cr2_card]
    exact cr2_hGrate_eps

end ShockRank2Witness

/-! ### Section C7. Both hypothesis sets at once

One theorem assumes the hypotheses of the Theorem 5 half and of the Theorem 11 half. Both
halves run at `Ω_n(ω) := 𝔼[ν_oν_{o'} ∣ 𝒟](ω)` (`condOmegaMat`); the identification with the
cluster-shock matrix `∑_jσ²_{c,j}Sh^{(j)} + diag(Var(ε_o ∣ 𝒟))` via
`Sharing.condOmega_eq_clusterOmega` is a conclusion. The ratio input and the limit
law are derived. The dependency graph, second moments, means and fourth moments are stated both
under `ℙ_ω := condExpKernel P 𝒟 ω` (for the Theorem 5 half) and as conditional expectations
(for the Theorem 11 half). -/

section BothHalves

open Filter
open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Corollary SM.D.3**, part (c), under both hypothesis sets:

> (c) `P(𝒱̂_n ≻ 0) → 1`, `𝟙{𝒱̂_n ≻ 0}𝒱̂_n^{-1/2}𝓡_n(β̂ − β) ⟶ᵈ N(0, I_r)`, and `𝒲 ⟶ᵈ χ²_r`,

with `𝒱̂_n := A_n'𝓜̃_n A_n` the union meat at `A_n = scoreMap X̃_n 𝓡_n`; the fourth conclusion
identifies `Ω_n` with the cluster-shock matrix. -/
theorem clustershock_wald_both_halves
    {O L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)] [∀ n, DecidableEq (L n)]
    {Dm : Type*} [DecidableEq Dm] {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (hm : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P] [SigmaFinite (P.trim hm)]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    -- hypotheses of the Theorem 11 half
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm) (hdims : dims.Nonempty)
    (Z : ∀ n, ((Dm × L n) ⊕ O n) → Ω → ℝ)
    (hZmeas : ∀ n s, Measurable (Z n s))
    (hZ4 : ∀ n s, MemLp (Z n s) 4 P)
    (hZind : ∀ n, iCondIndepFun 𝒟 hm (Z n) P)
    (hZmean : ∀ n s, P[Z n s | 𝒟] =ᵐ[P] 0)
    (sc : ℕ → Dm → ℝ)
    (hsc : ∀ n, ∀ j ∈ dims, ∀ g : L n,
      P[Z n (Sum.inl (j, g)) * Z n (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc n j)
    (s2 : ℝ) (hs2 : 0 < s2)
    (hve : ∀ n (o : O n), ∀ᵐ ω ∂P, s2 ≤ (P[Z n (Sum.inr o) * Z n (Sum.inr o) | 𝒟]) ω)
    (Cm : ℝ) (hCm : 0 < Cm)
    (hmom : ∀ n (o : O n), ∀ᵐ ω ∂P,
      (P[fun ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω ^ 4 | 𝒟]) ω ≤ Cm)
    (Xt : ∀ n, Matrix (O n) K ℝ) (B : ℝ) (hB0 : 0 < B)
    (hB : ∀ n (o : O n), ∑ k : K, (Xt n o k) ^ 2 ≤ B ^ 2)
    (θ : ℝ) (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Prm : ∀ n, Matrix (O n) (O n) ℝ) (dd : ℕ → ℝ) (Kr : ℝ) (hK0 : 0 ≤ Kr)
    (hdd : ∀ n, 1 ≤ dd n)
    (hPrH : ∀ n, (Prm n).IsHermitian) (hPrI : ∀ n, Prm n * Prm n = Prm n)
    (hPrtr : ∀ n, (Prm n).trace = dd n + Kr)
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (hGdrate : Tendsto (fun n => (Gb n : ℝ) ^ 3 * dd n / (Fintype.card (O n) : ℝ)) atTop (𝓝 0))
    (Rn : ℕ → Matrix rr K ℝ)
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    -- hypotheses of the Theorem 5 half, under `ℙ_ω`
    (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hscore : ∀ n y, bhat n y - β n = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ
      ((Xt n)ᵀ *ᵥ (fun o => Multiway.Sharing.nuRV (c n) dims (Z n) o y)))
    (hWvm : ∀ n, Measurable fun y => restrictedStat (Xt n)
      (condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) y) (Rn n) (bhat n y - β n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (Multiway.Sharing.nuRV (c n) dims (Z n))
        (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n) dims o o')
    (hOmK : ∀ᵐ ω ∂P, ∀ n o o', ∫ y, Multiway.Sharing.nuRV (c n) dims (Z n) o y
        * Multiway.Sharing.nuRV (c n) dims (Z n) o' y ∂(condExpKernel P 𝒟 ω)
      = condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω o o')
    (hmeanK : ∀ᵐ ω ∂P, ∀ n o,
      ∫ y, Multiway.Sharing.nuRV (c n) dims (Z n) o y ∂(condExpKernel P 𝒟 ω) = 0)
    (C4 : ℝ) (hC40 : 0 < C4)
    (hint4K : ∀ᵐ ω ∂P, ∀ n o, Integrable
      (fun y => (Multiway.Sharing.nuRV (c n) dims (Z n) o y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfourK : ∀ᵐ ω ∂P, ∀ n o,
      ∫ y, (Multiway.Sharing.nuRV (c n) dims (Z n) o y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4 ^ 4)
    (hGbN : ∀ n, Gb n ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hGeps : Tendsto (fun n => (Gb n : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0))
    -- side conditions on `𝒱_n` and `𝒱̂_n`
    (hV : ∀ n ω, (restrictedVar (Xt n)
      (condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω) (Rn n)).PosDef)
    (hVmeas : ∀ n, Measurable fun ω => restrictedVar (Xt n)
      (condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω) (Rn n))
    (hVhmeas : ∀ n, Measurable fun ω => (scoreMap (Xt n) (Rn n))ᵀ
      * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
          (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
            - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
      * scoreMap (Xt n) (Rn n)) :
    Tendsto (fun n => P {ω | ((scoreMap (Xt n) (Rn n))ᵀ
        * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
            (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
              - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
        * scoreMap (Xt n) (Rn n)).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD ((scoreMap (Xt n) (Rn n))ᵀ
              * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
                  (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
                    - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
              * scoreMap (Xt n) (Rn n)))⁻¹)
            (WithLp.toLp 2 (Rn n *ᵥ (bhat n ω - β n)) : EuclideanSpace ℝ rr)) atTop
          (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ rr))
      ∧ TendstoInDistribution
          (fun n ω => Multiway.Wald.waldStat ((scoreMap (Xt n) (Rn n))ᵀ
              * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
                  (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
                    - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
              * scoreMap (Xt n) (Rn n))
            (WithLp.toLp 2 (Rn n *ᵥ (bhat n ω - β n)) : EuclideanSpace ℝ rr)) atTop
          (fun z : EuclideanSpace ℝ rr => ‖z‖ ^ 2) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ rr))
      ∧ (∀ n, ∀ᵐ ω ∂P, condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω
          = Multiway.Sharing.clusterOmega (c n) dims (sc n)
              (fun o => (P[Z n (Sum.inr o) * Z n (Sum.inr o) | 𝒟]) ω)) := by
  classical
  have hcardN : ∀ n, 0 < Fintype.card (O n) := fun n => @Fintype.card_pos _ _ (hne n)
  have hGb1 : ∀ n, 1 ≤ Gb n := fun n => one_le_of_cluster_bound hdims (hne n) (hGb n)
  -- for `ε > 3` the rate hypothesis is unsatisfiable
  obtain hε3 | hεbig := le_or_gt ε 3
  swap
  · exact (epsHyp_false_of_three_lt hεbig hcardN hGb1 hGbN hGeps).elim
  have hZ2 : ∀ n s, MemLp (Z n s) 2 P := fun n s => (hZ4 n s).mono_exponent (by norm_num)
  -- the Theorem 11 half
  have hbb := clustershock_rateagnostic_b hm c dims hdims Z hZmeas hZ4 hZind hZmean hsc hs2 hve
    hCm hmom Xt hB0 hB hθ hdesign hne Prm hK0 hdd hPrH hPrI hPrtr Gb hGb hGdrate
    (fun n => scoreMap (Xt n) (Rn n)) hA
  -- the variance floor `Ω_n ⪰ σ̲²θnI_K`
  have hfloorOm : ∀ n, ∀ᵐ ω ∂P, s2 • (1 : Matrix (O n) (O n) ℝ)
      ≤ condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω := by
    intro n
    have := hne n
    exact Multiway.Sharing.smul_one_le_condOmega (h𝒟 := hm) (IsProbabilityMeasure.ne_zero P)
      (hZmeas n) (hZ2 n) (hZind n) (hZmean n) (hsc n) (hve n)
  have hfloorK : ∀ᵐ ω ∂P, ∀ n, ((s2 * θ) * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ)
      ≤ scoreVar (Xt n) (condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hfloorOm n] with ω hω
    exact smul_one_le_conj_of_floor_design hs2.le hω (hdesign n)
  -- the degree bound and `D_n ≥ 1`
  have hDn1 : ∀ n, 1 ≤ min (dims.card * Gb n) (Fintype.card (O n)) := by
    intro n
    have h1 : 1 ≤ dims.card := Finset.card_pos.mpr hdims
    have h2 : 1 ≤ Gb n := hGb1 n
    refine le_min ?_ (hcardN n)
    calc 1 = 1 * 1 := by norm_num
      _ ≤ dims.card * Gb n := Nat.mul_le_mul h1 h2
  have hdepC : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (Multiway.Sharing.nuRV (c n) dims (Z n))
        (condExpKernel P 𝒟 ω),
      ∀ n o, ((Dv n).nbhd o).card ≤ min (dims.card * Gb n) (Fintype.card (O n)) + 1 := by
    filter_upwards [hdep] with ω hω
    obtain ⟨Dv, hshare⟩ := hω
    refine ⟨Dv, fun n o => ?_⟩
    refine le_trans (le_min ?_ ?_) (Nat.le_succ _)
    · have hnbhd : (Dv n).nbhd o = Multiway.Sharing.closedNbhd (c n) dims o := by
        ext o'
        rw [DepGraph.mem_nbhd_iff, Multiway.Sharing.mem_closedNbhd]
        exact hshare n o o'
      rw [hnbhd]
      exact card_closedNbhd_le_mul (hGb n) o
    · exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  -- the Theorem 5 half, at `Ω_n = 𝔼[ν_oν_{o'} ∣ 𝒟]`
  have hclt := cltcluster_b_general_betaJM_janson_unconditional_vector hm P
    (fun n (_ : Ω) => Xt n)
    (fun n ω => condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω) Rn
    (fun n => Multiway.Sharing.nuRV (c n) dims (Z n)) bhat β
    (fun _ _ _ => measurable_const)
    (fun n o o' => (MeasureTheory.stronglyMeasurable_condExp
      (m := 𝒟) (μ := P)
      (f := fun y => Multiway.Sharing.nuRV (c n) dims (Z n) o y
        * Multiway.Sharing.nuRV (c n) dims (Z n) o' y)).measurable)
    (fun n y => hscore n y)
    (fun n (_ : Ω) => (s2 * θ) * (Fintype.card (O n) : ℝ))
    (fun n (_ : Ω) => min (dims.card * Gb n) (Fintype.card (O n)))
    B C4 hB0 hC40 hWvm hdepC
    (Filter.Eventually.of_forall fun _ n => hA n)
    (Filter.Eventually.of_forall fun _ n =>
      mul_pos (mul_pos hs2 hθ) (by exact_mod_cast hcardN n))
    hfloorK hOmK hmeanK
    (Filter.Eventually.of_forall fun _ n o => by
      have h := hB n o
      have he : (fun k => Xt n o k) ⬝ᵥ (fun k => Xt n o k) = ∑ k : K, (Xt n o k) ^ 2 := by
        simp [dotProduct, sq]
      rw [he]
      exact h)
    hint4K hfourK
    (Filter.Eventually.of_forall fun _ n => hDn1 n)
    (Filter.Eventually.of_forall fun _ n => min_le_right _ _)
    ε hε
    (Filter.Eventually.of_forall fun _ =>
      tendsto_epsRate_of_cluster_size (mul_pos hs2 hθ) hε3 (fun n => hcardN n) hDn1
        (fun n => min_le_left _ _) hGeps)
  -- `𝒱̂_n` is Hermitian at every `ω`
  have hVhherm : ∀ n ω, ((scoreMap (Xt n) (Rn n))ᵀ
      * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
          (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
            - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
      * scoreMap (Xt n) (Rn n)).IsHermitian := by
    intro n ω
    have h := Matrix.isHermitian_conjTranspose_mul_mul (scoreMap (Xt n) (Rn n))
      (isHermitian_unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
        (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
          - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω)
    rwa [Multiway.conjTranspose_eq_transpose] at h
  have hwald := clustershock_rateagnostic_c P (fun n (_ : Ω) => Xt n)
    (fun n ω => condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω) Rn
    (fun n y => bhat n y - β n)
    (fun n ω => (scoreMap (Xt n) (Rn n))ᵀ
      * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
          (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
            - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
      * scoreMap (Xt n) (Rn n))
    hV hVmeas hVhherm hVhmeas hbb.2.1 hclt
  refine ⟨hwald.1, hwald.2.1, hwald.2.2, fun n => ?_⟩
  exact Multiway.Sharing.condOmega_eq_clusterOmega (h𝒟 := hm) (hZmeas n) (hZ2 n) (hZind n)
    (hZmean n) (hsc n)

end BothHalves


/-! ### Section C8. Fourth moments of `ν` from fourth moments of the shocks

Under the representation `ν_o = ∑_jc^{(j)}_{g^{(j)}(o)} + ε_o`, with no bound on the shocks,
the power-mean inequality `(∑_{j∈dims}a_j + b)⁴ ≤ (J+1)³(∑_{j∈dims}a_j⁴ + b⁴)` gives
`𝔼[ν_o⁴ ∣ 𝒟] ≤ (J+1)⁴C` when each shock has conditional fourth moment at most `C`
(`condExp_nuRV_pow_four_le`), and the corresponding bound under any measure
(`integral_nuRV_pow_four_le`). The chained theorems replace the fourth-moment hypotheses on `ν`
by hypotheses on the shocks. The shocks are assumed to lie in `L⁴` (`hZ4`, `hint4KZ`). -/

section RepresentationStep

variable {D O L : Type*}

/-- `(∑_{i∈s}a_i)⁴ ≤ |s|³∑_{i∈s}a_i⁴`. The same statement as
`Multiway.CLT.pow_four_sum_le_card_pow_three`. -/
theorem pow_four_sum_le_card_pow_three {κ : Type*} (s : Finset κ) (f : κ → ℝ) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h1 : (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : (∑ i ∈ s, f i ^ 2) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i ^ 2) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc (∑ i ∈ s, f i) ^ 4 = ((∑ i ∈ s, f i) ^ 2) ^ 2 := by ring
    _ ≤ ((s.card : ℝ) * ∑ i ∈ s, f i ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, (f i ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
        rw [Finset.sum_congr rfl fun i _ => (by ring : (f i ^ 2) ^ 2 = f i ^ 4)]
        ring

/-- `(∑_{i∈s}a_i + b)⁴ ≤ (|s|+1)³(∑_{i∈s}a_i⁴ + b⁴)`. -/
theorem pow_four_sum_add_le {κ : Type*} (s : Finset κ) (f : κ → ℝ) (b : ℝ) :
    ((∑ i ∈ s, f i) + b) ^ 4
      ≤ ((s.card : ℝ) + 1) ^ 3 * ((∑ i ∈ s, f i ^ 4) + b ^ 4) := by
  classical
  have hnm : (none : Option κ) ∉ s.image some := by simp
  have hinj : ∀ x ∈ s, ∀ y ∈ s, (some x : Option κ) = some y → x = y := by
    intro x _ y _ h
    exact Option.some_injective _ h
  have key : ∀ (F : κ → ℝ) (cst : ℝ),
      ∑ x ∈ insert (none : Option κ) (s.image some), (Option.elim x cst F)
        = cst + ∑ i ∈ s, F i := by
    intro F cst
    rw [Finset.sum_insert hnm, Finset.sum_image hinj]
    rfl
  have hcard : (insert (none : Option κ) (s.image some)).card = s.card + 1 := by
    rw [Finset.card_insert_of_notMem hnm,
      Finset.card_image_of_injective _ (Option.some_injective κ)]
  have h := pow_four_sum_le_card_pow_three (insert (none : Option κ) (s.image some))
      (fun x => Option.elim x b f)
  have hpow : ∀ x : Option κ,
      (Option.elim x b f) ^ 4 = Option.elim x (b ^ 4) (fun i => f i ^ 4) := by
    intro x
    cases x <;> rfl
  simp only [hpow] at h
  rw [key f b, key (fun i => f i ^ 4) (b ^ 4), hcard] at h
  push_cast at h
  calc ((∑ i ∈ s, f i) + b) ^ 4 = (b + ∑ i ∈ s, f i) ^ 4 := by ring
    _ ≤ ((s.card : ℝ) + 1) ^ 3 * (b ^ 4 + ∑ i ∈ s, f i ^ 4) := h
    _ = ((s.card : ℝ) + 1) ^ 3 * ((∑ i ∈ s, f i ^ 4) + b ^ 4) := by ring

/-- The representation step, pointwise. -/
theorem nuVal_pow_four_le_sum {c : D → O → L} {dims : Finset D} {cs : D × L → ℝ} {ep : O → ℝ}
    (o : O) :
    Multiway.Sharing.nuVal c dims cs ep o ^ 4
      ≤ ((dims.card : ℝ) + 1) ^ 3 * ((∑ j ∈ dims, cs (j, c j o) ^ 4) + ep o ^ 4) :=
  pow_four_sum_add_le dims (fun j => cs (j, c j o)) (ep o)

/-- The representation step, pointwise, on the random-variable form. -/
theorem nuRV_pow_four_le {Ω : Type*} {c : D → O → L} {dims : Finset D}
    {Z : ((D × L) ⊕ O) → Ω → ℝ} (o : O) (ω : Ω) :
    Multiway.Sharing.nuRV c dims Z o ω ^ 4
      ≤ ((dims.card : ℝ) + 1) ^ 3
        * ((∑ j ∈ dims, Z (Sum.inl (j, c j o)) ω ^ 4) + Z (Sum.inr o) ω ^ 4) := by
  rw [Multiway.Sharing.nuRV_apply]
  exact pow_four_sum_add_le dims (fun j => Z (Sum.inl (j, c j o)) ω) (Z (Sum.inr o) ω)

section CondExpForm

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- `E[K(∑_{i∈s}f_i + g) | 𝒟] ≤ K(|s|+1)C` when each piece has conditional expectation `≤ C`. -/
theorem condExp_smul_finsetSum_add_le {ι : Type*} (s : Finset ι)
    (f : ι → Ω → ℝ) (g : Ω → ℝ) (hf : ∀ i ∈ s, Integrable (f i) P) (hg : Integrable g P)
    {K C : ℝ} (hK : 0 ≤ K)
    (hfC : ∀ i ∈ s, ∀ᵐ ω ∂P, (P[f i | 𝒟]) ω ≤ C) (hgC : ∀ᵐ ω ∂P, (P[g | 𝒟]) ω ≤ C) :
    ∀ᵐ ω ∂P, (P[fun ω => K * ((∑ i ∈ s, f i ω) + g ω) | 𝒟]) ω ≤ K * ((s.card : ℝ) + 1) * C := by
  have hsum : Integrable (∑ i ∈ s, f i) P := integrable_finsetSum' s hf
  have hfun : (fun ω => K * ((∑ i ∈ s, f i ω) + g ω)) = K • ((∑ i ∈ s, f i) + g) := by
    funext ω
    simp [Finset.sum_apply]
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ s, (P[f i | 𝒟]) ω ≤ C := (Finset.eventually_all s).2 hfC
  rw [hfun]
  filter_upwards [condExp_smul (𝕜 := ℝ) K ((∑ i ∈ s, f i) + g) 𝒟,
    condExp_add hsum hg 𝒟, condExp_finsetSum hf 𝒟, hall, hgC] with ω h1 h2 h3 h4 h5
  rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, Finset.sum_apply, smul_eq_mul]
  have hs : ∑ i ∈ s, (P[f i | 𝒟]) ω ≤ (s.card : ℝ) * C := by
    calc ∑ i ∈ s, (P[f i | 𝒟]) ω ≤ ∑ _i ∈ s, C := Finset.sum_le_sum h4
      _ = (s.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
  calc K * ((∑ i ∈ s, (P[f i | 𝒟]) ω) + (P[g | 𝒟]) ω)
      ≤ K * ((s.card : ℝ) * C + C) := mul_le_mul_of_nonneg_left (add_le_add hs h5) hK
    _ = K * ((s.card : ℝ) + 1) * C := by ring

/-- `𝔼[ν_o⁴ ∣ 𝒟] ≤ (J+1)⁴C` when each shock has conditional fourth moment at most `C`. -/
theorem condExp_nuRV_pow_four_le [IsFiniteMeasure P] {c : D → O → L} {dims : Finset D}
    {Z : ((D × L) ⊕ O) → Ω → ℝ} (hZ4 : ∀ s, MemLp (Z s) 4 P) {C : ℝ}
    (hmomZ : ∀ s, ∀ᵐ ω ∂P, (P[fun ω => Z s ω ^ 4 | 𝒟]) ω ≤ C) (o : O) :
    ∀ᵐ ω ∂P, (P[fun ω => Multiway.Sharing.nuRV c dims Z o ω ^ 4 | 𝒟]) ω
      ≤ ((dims.card : ℝ) + 1) ^ 4 * C := by
  classical
  have hintZ : ∀ s, Integrable (fun ω => Z s ω ^ 4) P := fun s =>
    Multiway.RateAgnostic.integrable_pow_four (nu := fun _ : Unit => Z s)
      (fun _ _ => (hZ4 s).mul (hZ4 s)) ()
  have hnuform : Multiway.Sharing.nuRV c dims Z o
      = fun ω => (∑ j ∈ dims, Z (Sum.inl (j, c j o)) ω) + Z (Sum.inr o) ω := by
    funext ω
    rw [Multiway.Sharing.nuRV_apply]
  have hnu4 : MemLp (Multiway.Sharing.nuRV c dims Z o) 4 P := by
    rw [hnuform]
    exact (memLp_finsetSum dims fun j _ => hZ4 _).add (hZ4 _)
  have hintnu : Integrable (fun ω => Multiway.Sharing.nuRV c dims Z o ω ^ 4) P :=
    Multiway.RateAgnostic.integrable_pow_four
      (nu := fun _ : Unit => Multiway.Sharing.nuRV c dims Z o)
      (fun _ _ => hnu4.mul hnu4) ()
  set K : ℝ := ((dims.card : ℝ) + 1) ^ 3 with hKdef
  have hK : (0 : ℝ) ≤ K := by positivity
  have hGint : Integrable (fun ω => K * ((∑ j ∈ dims, Z (Sum.inl (j, c j o)) ω ^ 4)
      + Z (Sum.inr o) ω ^ 4)) P := by
    refine Integrable.const_mul ?_ K
    exact (integrable_finsetSum dims fun j _ => hintZ _).add (hintZ _)
  have hle : (fun ω => Multiway.Sharing.nuRV c dims Z o ω ^ 4)
      ≤ᵐ[P] fun ω => K * ((∑ j ∈ dims, Z (Sum.inl (j, c j o)) ω ^ 4) + Z (Sum.inr o) ω ^ 4) :=
    Filter.Eventually.of_forall fun ω => nuRV_pow_four_le o ω
  have hmono := condExp_mono (m := 𝒟) hintnu hGint hle
  have hbd := condExp_smul_finsetSum_add_le (𝒟 := 𝒟) (P := P) dims
    (fun j ω => Z (Sum.inl (j, c j o)) ω ^ 4) (fun ω => Z (Sum.inr o) ω ^ 4)
    (fun j _ => hintZ _) (hintZ _) hK (fun j _ => hmomZ _) (hmomZ _)
  filter_upwards [hmono, hbd] with ω h1 h2
  refine h1.trans (h2.trans ?_)
  rw [hKdef]
  refine le_of_eq ?_
  ring

end CondExpForm

section IntegralForm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The representation step under a measure, giving integrability of `ν_o⁴` from that of the
shocks. -/
theorem integrable_nuRV_pow_four (μ : Measure Ω) {c : D → O → L} {dims : Finset D}
    {Z : ((D × L) ⊕ O) → Ω → ℝ} (hZmeas : ∀ s, Measurable (Z s))
    (hint : ∀ s, Integrable (fun ω => Z s ω ^ 4) μ) (o : O) :
    Integrable (fun ω => Multiway.Sharing.nuRV c dims Z o ω ^ 4) μ := by
  classical
  have hmeas : Measurable (Multiway.Sharing.nuRV c dims Z o) := by
    have : Multiway.Sharing.nuRV c dims Z o
        = fun ω => (∑ j ∈ dims, Z (Sum.inl (j, c j o)) ω) + Z (Sum.inr o) ω := by
      funext ω
      rw [Multiway.Sharing.nuRV_apply]
    rw [this]
    exact (Finset.measurable_sum dims fun j _ => hZmeas _).add (hZmeas _)
  refine Integrable.mono' (g := fun ω => ((dims.card : ℝ) + 1) ^ 3
      * ((∑ j ∈ dims, Z (Sum.inl (j, c j o)) ω ^ 4) + Z (Sum.inr o) ω ^ 4)) ?_
    (hmeas.pow_const 4).aestronglyMeasurable ?_
  · exact Integrable.const_mul ((integrable_finsetSum dims fun j _ => hint _).add (hint _)) _
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact nuRV_pow_four_le o ω

/-- The fourth-moment bound on `ν` under a measure, from the shocks'. -/
theorem integral_nuRV_pow_four_le (μ : Measure Ω) {c : D → O → L} {dims : Finset D}
    {Z : ((D × L) ⊕ O) → Ω → ℝ} (hZmeas : ∀ s, Measurable (Z s))
    (hint : ∀ s, Integrable (fun ω => Z s ω ^ 4) μ) {C : ℝ}
    (hmomZ : ∀ s, ∫ ω, Z s ω ^ 4 ∂μ ≤ C) (o : O) :
    ∫ ω, Multiway.Sharing.nuRV c dims Z o ω ^ 4 ∂μ ≤ ((dims.card : ℝ) + 1) ^ 4 * C := by
  classical
  have hGint : Integrable (fun ω => ((dims.card : ℝ) + 1) ^ 3
      * ((∑ j ∈ dims, Z (Sum.inl (j, c j o)) ω ^ 4) + Z (Sum.inr o) ω ^ 4)) μ :=
    Integrable.const_mul ((integrable_finsetSum dims fun j _ => hint _).add (hint _)) _
  have hmono := integral_mono (integrable_nuRV_pow_four μ hZmeas hint o) hGint
    (fun ω => nuRV_pow_four_le (c := c) (dims := dims) (Z := Z) o ω)
  refine hmono.trans ?_
  rw [integral_const_mul,
    integral_add (integrable_finsetSum dims fun j _ => hint _) (hint _),
    integral_finsetSum dims fun j _ => hint _]
  have hs : ∑ j ∈ dims, ∫ ω, Z (Sum.inl (j, c j o)) ω ^ 4 ∂μ ≤ (dims.card : ℝ) * C := by
    calc ∑ j ∈ dims, ∫ ω, Z (Sum.inl (j, c j o)) ω ^ 4 ∂μ ≤ ∑ _j ∈ dims, C :=
          Finset.sum_le_sum fun j _ => hmomZ _
      _ = (dims.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ((dims.card : ℝ) + 1) ^ 3
        * ((∑ j ∈ dims, ∫ ω, Z (Sum.inl (j, c j o)) ω ^ 4 ∂μ) + ∫ ω, Z (Sum.inr o) ω ^ 4 ∂μ)
      ≤ ((dims.card : ℝ) + 1) ^ 3 * ((dims.card : ℝ) * C + C) :=
        mul_le_mul_of_nonneg_left (add_le_add hs (hmomZ _)) (by positivity)
    _ = ((dims.card : ℝ) + 1) ^ 4 * C := by ring

end IntegralForm

end RepresentationStep



section ChainedRateAgnostic

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {Ω : Type*} {𝒟 mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Corollary SM.D.3**, part (a) of the Theorem 11 half, with the fourth-moment hypothesis
stated on the shocks `{c^{(j)}_g} ∪ {ε_o}`; the bound on `ν` follows with
constant `(J+1)⁴C_Z` from `condExp_nuRV_pow_four_le`. -/
theorem clustershock_rateagnostic_a_shockmoments (hm : 𝒟 ≤ mΩ) [SigmaFinite (P.trim hm)]
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
    (Cz : ℝ) (hCz : 0 ≤ Cz)
    (hmomZ : ∀ n s, ∀ᵐ ω ∂P, (P[fun ω => Z n s ω ^ 4 | 𝒟]) ω ≤ Cz)
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
        atTop (fun _ => 0) :=
  clustershock_rateagnostic_a hm c dims hdims Z hZmeas hZ4 hZind hZmean hsc hs2 hve
    (Cm := ((dims.card : ℝ) + 1) ^ 4 * Cz) (by positivity)
    (fun n o => condExp_nuRV_pow_four_le (hZ4 n) (hmomZ n) o)
    Xt hB0 hB hθ hdesign hne Gb hGb hGrate A hA

/-- The same for part (b). -/
theorem clustershock_rateagnostic_b_shockmoments (hm : 𝒟 ≤ mΩ) [SigmaFinite (P.trim hm)]
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
    (Cz : ℝ) (hCz : 0 < Cz)
    (hmomZ : ∀ n s, ∀ᵐ ω ∂P, (P[fun ω => Z n s ω ^ 4 | 𝒟]) ω ≤ Cz)
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
          * A n).PosDef}) atTop (𝓝 1) :=
  clustershock_rateagnostic_b hm c dims hdims Z hZmeas hZ4 hZind hZmean hsc hs2 hve
    (Cm := ((dims.card : ℝ) + 1) ^ 4 * Cz) (mul_pos (by positivity) hCz)
    (fun n o => condExp_nuRV_pow_four_le (hZ4 n) (hmomZ n) o)
    Xt hB0 hB hθ hdesign hne Prm hK0 hdd hPrH hPrI hPrtr Gb hGb hGdrate A hA

end ChainedRateAgnostic

section ChainedWald

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {Ω : Type*} {𝒟 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]

/-- **Corollary SM.D.3**, part (c), under both hypothesis sets, with the fourth-moment
hypotheses stated on the shocks. The bounds on `ν` follow with constants `C = (J+1)⁴C_Z` and
`C₄ = (J+1)C_{4Z}`, where `J = dims.card`. -/
theorem clustershock_wald_both_halves_shockmoments
    {O L : ℕ → Type*} [∀ n, Fintype (O n)] [∀ n, DecidableEq (O n)] [∀ n, DecidableEq (L n)]
    {Dm : Type*} [DecidableEq Dm] {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    {rr : Type*} [Fintype rr] [DecidableEq rr]
    (hm : 𝒟 ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P] [SigmaFinite (P.trim hm)]
    [∀ ω : Ω, IsProbabilityMeasure (condExpKernel P 𝒟 ω)]
    -- hypotheses of the Theorem 11 half
    (c : ∀ n, Dm → O n → L n) (dims : Finset Dm) (hdims : dims.Nonempty)
    (Z : ∀ n, ((Dm × L n) ⊕ O n) → Ω → ℝ)
    (hZmeas : ∀ n s, Measurable (Z n s))
    (hZ4 : ∀ n s, MemLp (Z n s) 4 P)
    (hZind : ∀ n, iCondIndepFun 𝒟 hm (Z n) P)
    (hZmean : ∀ n s, P[Z n s | 𝒟] =ᵐ[P] 0)
    (sc : ℕ → Dm → ℝ)
    (hsc : ∀ n, ∀ j ∈ dims, ∀ g : L n,
      P[Z n (Sum.inl (j, g)) * Z n (Sum.inl (j, g)) | 𝒟] =ᵐ[P] fun _ => sc n j)
    (s2 : ℝ) (hs2 : 0 < s2)
    (hve : ∀ n (o : O n), ∀ᵐ ω ∂P, s2 ≤ (P[Z n (Sum.inr o) * Z n (Sum.inr o) | 𝒟]) ω)
    (Cz : ℝ) (hCz : 0 < Cz)
    (hmomZ : ∀ n s, ∀ᵐ ω ∂P, (P[fun ω => Z n s ω ^ 4 | 𝒟]) ω ≤ Cz)
    (Xt : ∀ n, Matrix (O n) K ℝ) (B : ℝ) (hB0 : 0 < B)
    (hB : ∀ n (o : O n), ∑ k : K, (Xt n o k) ^ 2 ≤ B ^ 2)
    (θ : ℝ) (hθ : 0 < θ)
    (hdesign : ∀ n, (θ * (Fintype.card (O n) : ℝ)) • (1 : Matrix K K ℝ) ≤ (Xt n)ᵀ * Xt n)
    (hne : ∀ n, Nonempty (O n))
    (Prm : ∀ n, Matrix (O n) (O n) ℝ) (dd : ℕ → ℝ) (Kr : ℝ) (hK0 : 0 ≤ Kr)
    (hdd : ∀ n, 1 ≤ dd n)
    (hPrH : ∀ n, (Prm n).IsHermitian) (hPrI : ∀ n, Prm n * Prm n = Prm n)
    (hPrtr : ∀ n, (Prm n).trace = dd n + Kr)
    (Gb : ℕ → ℕ) (hGb : ∀ n, ∀ j ∈ dims, ∀ γ : L n, (cluster (c n j) γ).card ≤ Gb n)
    (hGdrate : Tendsto (fun n => (Gb n : ℝ) ^ 3 * dd n / (Fintype.card (O n) : ℝ)) atTop (𝓝 0))
    (Rn : ℕ → Matrix rr K ℝ)
    (hA : ∀ n, Function.Injective (scoreMap (Xt n) (Rn n)).mulVec)
    -- hypotheses of the Theorem 5 half, under `ℙ_ω`
    (bhat : ℕ → Ω → (K → ℝ)) (β : ℕ → K → ℝ)
    (hscore : ∀ n y, bhat n y - β n = ((Xt n)ᵀ * Xt n)⁻¹ *ᵥ
      ((Xt n)ᵀ *ᵥ (fun o => Multiway.Sharing.nuRV (c n) dims (Z n) o y)))
    (hWvm : ∀ n, Measurable fun y => restrictedStat (Xt n)
      (condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) y) (Rn n) (bhat n y - β n))
    (hdep : ∀ᵐ ω ∂P, ∃ Dv : ∀ n, DepGraph (Multiway.Sharing.nuRV (c n) dims (Z n))
        (condExpKernel P 𝒟 ω),
      ∀ n o o', (Dv n).G o o' ↔ Multiway.Linked (c n) dims o o')
    (hOmK : ∀ᵐ ω ∂P, ∀ n o o', ∫ y, Multiway.Sharing.nuRV (c n) dims (Z n) o y
        * Multiway.Sharing.nuRV (c n) dims (Z n) o' y ∂(condExpKernel P 𝒟 ω)
      = condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω o o')
    (hmeanK : ∀ᵐ ω ∂P, ∀ n o,
      ∫ y, Multiway.Sharing.nuRV (c n) dims (Z n) o y ∂(condExpKernel P 𝒟 ω) = 0)
    (C4z : ℝ) (hC4z0 : 0 < C4z)
    (hint4KZ : ∀ᵐ ω ∂P, ∀ n s, Integrable
      (fun y => (Z n s y) ^ 4) (condExpKernel P 𝒟 ω))
    (hfourKZ : ∀ᵐ ω ∂P, ∀ n s,
      ∫ y, (Z n s y) ^ 4 ∂(condExpKernel P 𝒟 ω) ≤ C4z ^ 4)
    (hGbN : ∀ n, Gb n ≤ Fintype.card (O n))
    (ε : ℝ) (hε : 0 < ε)
    (hGeps : Tendsto (fun n => (Gb n : ℝ) ^ ((3 : ℝ) - ε)
      / (Fintype.card (O n) : ℝ) ^ ((1 : ℝ) - ε)) atTop (𝓝 0))
    -- side conditions on `𝒱_n` and `𝒱̂_n`
    (hV : ∀ n ω, (restrictedVar (Xt n)
      (condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω) (Rn n)).PosDef)
    (hVmeas : ∀ n, Measurable fun ω => restrictedVar (Xt n)
      (condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω) (Rn n))
    (hVhmeas : ∀ n, Measurable fun ω => (scoreMap (Xt n) (Rn n))ᵀ
      * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
          (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
            - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
      * scoreMap (Xt n) (Rn n)) :
    Tendsto (fun n => P {ω | ((scoreMap (Xt n) (Rn n))ᵀ
        * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
            (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
              - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
        * scoreMap (Xt n) (Rn n)).PosDef}) atTop (𝓝 1)
      ∧ TendstoInDistribution
          (fun n ω => toEuclideanCLM (𝕜 := ℝ) ((sqrtPD ((scoreMap (Xt n) (Rn n))ᵀ
              * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
                  (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
                    - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
              * scoreMap (Xt n) (Rn n)))⁻¹)
            (WithLp.toLp 2 (Rn n *ᵥ (bhat n ω - β n)) : EuclideanSpace ℝ rr)) atTop
          (id : EuclideanSpace ℝ rr → EuclideanSpace ℝ rr) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ rr))
      ∧ TendstoInDistribution
          (fun n ω => Multiway.Wald.waldStat ((scoreMap (Xt n) (Rn n))ᵀ
              * Multiway.RateAgnostic.unionMeat (c n) dims (fun o k (_ : Ω) => Xt n o k)
                  (fun o ω => Multiway.Sharing.nuRV (c n) dims (Z n) o ω
                    - (Prm n *ᵥ fun o' => Multiway.Sharing.nuRV (c n) dims (Z n) o' ω) o) ω
              * scoreMap (Xt n) (Rn n))
            (WithLp.toLp 2 (Rn n *ᵥ (bhat n ω - β n)) : EuclideanSpace ℝ rr)) atTop
          (fun z : EuclideanSpace ℝ rr => ‖z‖ ^ 2) (fun _ => P)
          (stdGaussian (EuclideanSpace ℝ rr))
      ∧ (∀ n, ∀ᵐ ω ∂P, condOmegaMat 𝒟 P (Multiway.Sharing.nuRV (c n) dims (Z n)) ω
          = Multiway.Sharing.clusterOmega (c n) dims (sc n)
              (fun o => (P[Z n (Sum.inr o) * Z n (Sum.inr o) | 𝒟]) ω)) := by
  have hint4K : ∀ᵐ ω ∂P, ∀ n (o : O n), Integrable
      (fun y => (Multiway.Sharing.nuRV (c n) dims (Z n) o y) ^ 4) (condExpKernel P 𝒟 ω) := by
    filter_upwards [hint4KZ] with ω hω n o
    exact integrable_nuRV_pow_four (condExpKernel P 𝒟 ω) (hZmeas n) (fun s => hω n s) o
  have hfourK : ∀ᵐ ω ∂P, ∀ n (o : O n),
      ∫ y, (Multiway.Sharing.nuRV (c n) dims (Z n) o y) ^ 4 ∂(condExpKernel P 𝒟 ω)
        ≤ (((dims.card : ℝ) + 1) * C4z) ^ 4 := by
    filter_upwards [hint4KZ, hfourKZ] with ω h1 h2 n o
    calc ∫ y, (Multiway.Sharing.nuRV (c n) dims (Z n) o y) ^ 4 ∂(condExpKernel P 𝒟 ω)
        ≤ ((dims.card : ℝ) + 1) ^ 4 * C4z ^ 4 :=
          integral_nuRV_pow_four_le (condExpKernel P 𝒟 ω) (hZmeas n)
            (fun s => h1 n s) (fun s => h2 n s) o
      _ = (((dims.card : ℝ) + 1) * C4z) ^ 4 := by ring
  exact clustershock_wald_both_halves hm P c dims hdims Z hZmeas hZ4 hZind hZmean sc hsc s2 hs2
    hve (((dims.card : ℝ) + 1) ^ 4 * Cz) (mul_pos (by positivity) hCz)
    (fun n o => condExp_nuRV_pow_four_le (hZ4 n) (hmomZ n) o)
    Xt B hB0 hB θ hθ hdesign hne Prm dd Kr hK0 hdd hPrH hPrI hPrtr Gb hGb hGdrate Rn hA
    bhat β hscore hWvm hdep hOmK hmeanK (((dims.card : ℝ) + 1) * C4z)
    (mul_pos (by positivity) hC4z0) hint4K hfourK hGbN ε hε hGeps hV hVmeas hVhmeas

end ChainedWald


/-! ### An example for the representation step

The model has `J = 2` clustering dimensions with two labels each and two observations, hence six
shocks. Each shock is `Z_s = (n+1)^{-1/2}∑_{i≤n}s_{block(s),i}` on a separate block of coins. Then
`sup_ω|Z_{n,s}| = √(n+1) → ∞` while `𝔼[Z_{n,s}⁴] ≤ 3`, and the derived bound on `ν` is
`(2+1)⁴·3 = 243`. -/

section RepresentationWitness

open Multiway.Multilinear
open UnboundedShockWitness

namespace RepresentationWitness

/-- The six shocks of the model, namely `c^{(1)}_g` and `c^{(2)}_g` at two labels each and `ε_o`
at two observations. -/
abbrev RsS := (Fin 2 × Fin 2) ⊕ Fin 2

/-- An explicit enumeration of the six shocks, so that each reads a separate block of coins. -/
def rsIdx : RsS → Fin 6
  | Sum.inl (j, g) => ⟨2 * j.val + g.val, by have := j.isLt; have := g.isLt; omega⟩
  | Sum.inr o => ⟨4 + o.val, by have := o.isLt; omega⟩

theorem rsIdx_injective : Function.Injective rsIdx := by
  rintro (⟨j, g⟩ | o) (⟨j', g'⟩ | o') h <;>
    · have hv : (rsIdx _).val = (rsIdx _).val := congrArg Fin.val h
      simp only [rsIdx] at hv
      first
        | (have hj := j.isLt; have hg := g.isLt; have hj' := j'.isLt; have hg' := g'.isLt
           have e1 : j = j' := Fin.ext (by omega)
           have e2 : g = g' := Fin.ext (by omega)
           rw [e1, e2])
        | (have ho := o.isLt; have ho' := o'.isLt
           have e1 : o = o' := Fin.ext (by omega)
           rw [e1])
        | (have := j.isLt; have := g.isLt; have := o'.isLt; omega)
        | (have := o.isLt; have := j'.isLt; have := g'.isLt; omega)

/-- Shock `s` reads the `i`-th coin of its block. -/
def rsBlk (n : ℕ) (s : RsS) (i : Fin (n + 1)) : Fin (6 * (n + 1)) :=
  ⟨(rsIdx s).val * (n + 1) + i.val, by
    have h1 : (rsIdx s).val + 1 ≤ 6 := (rsIdx s).isLt
    have h2 : i.val < n + 1 := i.isLt
    calc (rsIdx s).val * (n + 1) + i.val
        < (rsIdx s).val * (n + 1) + (n + 1) := by omega
      _ = ((rsIdx s).val + 1) * (n + 1) := by ring
      _ ≤ 6 * (n + 1) := Nat.mul_le_mul_right _ h1⟩

theorem rsBlk_injective (n : ℕ) (s : RsS) : Function.Injective (rsBlk n s) := by
  intro i i' h
  have hv : (rsIdx s).val * (n + 1) + i.val = (rsIdx s).val * (n + 1) + i'.val :=
    congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The unbounded shock family, each shock standardized by `(n+1)^{-1/2}`. -/
noncomputable def rsZ (n : ℕ) (s : RsS) : (Fin (6 * (n + 1)) → Bool) → ℝ :=
  wShockSum (rsBlk n) (ugW n) s

theorem measurable_rsZ (n : ℕ) (s : RsS) : Measurable (rsZ n s) :=
  measurable_wShockSum (rsBlk n) (ugW n) s

theorem abs_rsZ_le (n : ℕ) (s : RsS) (ω : Fin (6 * (n + 1)) → Bool) :
    |rsZ n s ω| ≤ (n : ℝ) + 1 := by
  have h := abs_wShockSum_le (rsBlk n) (ugW_pos n).le s ω
  rw [Fintype.card_fin] at h
  refine h.trans ?_
  have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hc]
  nlinarith [ugW_le_one n, (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)]

theorem memLp_rsZ (n : ℕ) (s : RsS) : MemLp (rsZ n s) 4 (coins (6 * (n + 1))) :=
  (memLp_top_of_bound (measurable_rsZ n s).aestronglyMeasurable ((n : ℝ) + 1)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_rsZ_le n s ω)).mono_exponent le_top

theorem integrable_rsZ_pow_four (n : ℕ) (s : RsS) :
    Integrable (fun ω => rsZ n s ω ^ 4) (coins (6 * (n + 1))) := by
  refine Multiway.SteinCluster.integrable_of_abs_le ((measurable_rsZ n s).pow_const 4)
    (C := ((n : ℝ) + 1) ^ 4) fun ω => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_rsZ_le n s ω) 4

/-- Each shock has fourth moment at most `3`, for every `n`. -/
theorem integral_rsZ_pow_four_le (n : ℕ) (s : RsS) :
    ∫ ω, rsZ n s ω ^ 4 ∂(coins (6 * (n + 1))) ≤ 3 := by
  have h := integral_wShockSum_pow_four_le (idx := rsBlk n) (w := ugW n) s (rsBlk_injective n s)
  rw [Fintype.card_fin] at h
  refine h.trans (le_of_eq ?_)
  have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hc, ugW_sq_mul]
  norm_num

theorem rsZ_all_true (n : ℕ) (s : RsS) :
    rsZ n s (fun _ => true) = Real.sqrt ((n : ℝ) + 1) := by
  have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  show wShockSum (rsBlk n) (ugW n) s (fun _ => true) = _
  rw [wShockSum_all_true, Fintype.card_fin, hc, ugW, div_mul_eq_mul_div, one_mul, Real.div_sqrt]

/-- The shocks are unbounded across `n`. -/
theorem rsZ_unbounded (C : ℝ) :
    ∃ (n : ℕ) (s : RsS) (ω : Fin (6 * (n + 1)) → Bool), C < rsZ n s ω := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2)
  refine ⟨n, Sum.inr 0, fun _ => true, ?_⟩
  rw [rsZ_all_true]
  have h1 : C ^ 2 < (n : ℝ) + 1 := by linarith
  have h2 : Real.sqrt (C ^ 2) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_lt_sqrt (by positivity) h1
  have h3 : C ≤ Real.sqrt (C ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
    exact le_abs_self C
  linarith

/-- The two clustering maps. Dimension `0` separates the two observations and dimension `1`
puts both in one cluster, so the second cluster shock is shared. -/
def rsC : Fin 2 → Fin 2 → Fin 2 := fun j o => if j = 0 then o else 0

theorem rsDims_card : (Finset.univ : Finset (Fin 2)).card = 2 := by simp

end RepresentationWitness

open RepresentationWitness

/-- The representation step at `J = 2` with unbounded shocks. The statement asserts that no
constant bounds the shocks uniformly in `n`; that `J = 2`; the representation
`ν_o = c^{(1)}_{g₁(o)} + c^{(2)}_{g₂(o)} + ε_o` at both observations; and `𝔼[ν_o⁴] ≤ 243` and
`𝔼[ν_o⁴ ∣ ⊥] ≤ 243` almost surely, for every `n`. -/
theorem representation_pow_four_witness :
    (∀ C : ℝ, ∃ (n : ℕ) (s : RsS) (ω : Fin (6 * (n + 1)) → Bool), C < rsZ n s ω)
    ∧ (Finset.univ : Finset (Fin 2)).card = 2
    ∧ (∀ (n : ℕ) (o : Fin 2) (ω : Fin (6 * (n + 1)) → Bool),
        Multiway.Sharing.nuRV rsC Finset.univ (rsZ n) o ω
          = rsZ n (Sum.inl (0, rsC 0 o)) ω + rsZ n (Sum.inl (1, rsC 1 o)) ω
            + rsZ n (Sum.inr o) ω)
    ∧ (∀ (n : ℕ) (o : Fin 2),
        ∫ ω, Multiway.Sharing.nuRV rsC Finset.univ (rsZ n) o ω ^ 4 ∂(coins (6 * (n + 1)))
          ≤ 243)
    ∧ (∀ (n : ℕ) (o : Fin 2), ∀ᵐ ω ∂(coins (6 * (n + 1))),
        ((coins (6 * (n + 1)))[fun ω =>
            Multiway.Sharing.nuRV rsC Finset.univ (rsZ n) o ω ^ 4
          | (⊥ : MeasurableSpace (Fin (6 * (n + 1)) → Bool))]) ω ≤ 243) := by
  refine ⟨rsZ_unbounded, rsDims_card, ?_, ?_, ?_⟩
  · intro n o ω
    rw [Multiway.Sharing.nuRV_apply, Fin.sum_univ_two]
  · intro n o
    have h := integral_nuRV_pow_four_le (c := rsC) (dims := (Finset.univ : Finset (Fin 2)))
      (Z := rsZ n) (coins (6 * (n + 1))) (measurable_rsZ n) (integrable_rsZ_pow_four n)
      (C := 3) (integral_rsZ_pow_four_le n) o
    refine h.trans (le_of_eq ?_)
    rw [rsDims_card]
    norm_num
  · intro n o
    have h := condExp_nuRV_pow_four_le (c := rsC) (dims := (Finset.univ : Finset (Fin 2)))
      (Z := rsZ n) (𝒟 := (⊥ : MeasurableSpace (Fin (6 * (n + 1)) → Bool)))
      (P := coins (6 * (n + 1))) (memLp_rsZ n) (C := 3) ?_ o
    · filter_upwards [h] with ω hω
      refine hω.trans (le_of_eq ?_)
      rw [rsDims_card]
      norm_num
    · intro s
      rw [condExp_bot]
      filter_upwards with ω
      exact integral_rsZ_pow_four_le n s

end RepresentationWitness

/-! ### Examples for the chained theorems

They use the bounded `bigCoins` design of `ClusterShock`, with `J = 1` and derived constant
`(1+1)⁴·1 = 16`. -/

section ChainedWitness

open Multiway.Multilinear
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Each shock of the `bigCoins` design is a fair sign, so its conditional fourth moment is
`1`. -/
theorem wr_momZ (n : ℕ) (s : (WrD × WrL n) ⊕ WrO n) : ∀ᵐ ω ∂bigCoins,
    (bigCoins[fun ω => wrZ n s ω ^ 4 | ⊥] : (ℕ → Bool) → ℝ) ω ≤ (1 : ℝ) := by
  have hfun : (fun ω => wrZ n s ω ^ 4) = fun _ : ℕ → Bool => (1 : ℝ) := by
    funext ω
    show (bigSign (wrIdx n s) ω) ^ 4 = 1
    unfold bigSign
    by_cases h : ω (wrIdx n s) <;> norm_num [h]
  rw [hfun, condExp_const bot_le (1 : ℝ)]
  filter_upwards with ω
  exact le_refl 1

/-- An example for `clustershock_rateagnostic_a_shockmoments`. -/
theorem clustershock_rateagnostic_a_shockmoments_witness :
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
  refine clustershock_rateagnostic_a_shockmoments (𝒟 := ⊥) bot_le wrC wrDims wrDims_nonempty wrZ
    (fun n s => measurable_bigSign _) (fun n s => memLp_bigSign _ _)
    iCondIndepFun_wrZ
    wrZ_mean (sc := fun _ _ => 1) (fun n j _ g => wrZ_var_cluster n j g)
    (s2 := 1) one_pos wrZ_var_idio 1 zero_le_one wr_momZ
    wrXt (B := 1) zero_le_one ?_ (θ := 1) one_pos ?_ wr_ne (fun _ => 2)
    (fun n j _ γ => wr_cluster_card n j γ) wr_tendsto' (fun _ => 1) (fun _ => wrA_injective)
  · intro n o
    simp [wrXt]
  · intro n
    rw [one_mul, wrXt_gram]

/-- An example for `clustershock_rateagnostic_b_shockmoments`. -/
theorem clustershock_rateagnostic_b_shockmoments_witness :
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
  refine clustershock_rateagnostic_b_shockmoments (𝒟 := ⊥) bot_le wrC wrDims wrDims_nonempty wrZ
    (fun n s => measurable_bigSign _) (fun n s => memLp_bigSign _ _)
    iCondIndepFun_wrZ
    wrZ_mean (sc := fun _ _ => 1) (fun n j _ g => wrZ_var_cluster n j g)
    (s2 := 1) one_pos wrZ_var_idio 1 one_pos wr_momZ
    wrXt (B := 1) one_pos ?_ (θ := 1) one_pos ?_ wr_ne
    wrPr (dd := fun _ => 1) (Kr := 0) le_rfl (fun _ => le_rfl)
    wrPr_isHermitian wrPr_idem wrPr_trace (fun _ => 2)
    (fun n j _ γ => wr_cluster_card n j γ) wr_tendsto (fun _ => 1) (fun _ => wrA_injective)
  · intro n o
    simp [wrXt]
  · intro n
    rw [one_mul, wrXt_gram]

end ChainedWitness

end Multiway.ClusterJanson
