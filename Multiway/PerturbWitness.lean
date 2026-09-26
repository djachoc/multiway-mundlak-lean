import Multiway.ClusterShock

/-!
# An example for the perturbation step of Theorem 11

The hypotheses of `RateAgnostic.perturb_tendstoInProb_of_moments`, the perturbation step of
Theorem 11(b) (rate-agnostic inference under multiway clustering) at `ϖ = Πν`, hold on the
following model, and the theorem is applied to it.

Take `𝒪_j = Fin (j+1)` with every observation a cluster by itself (so `D_j = 1`), disturbances
`ν_o` independent fair signs on `ClusterShock.bigCoins`, `x̃_{ok} ≡ 1` with `K = 1`,
`Π = n^{-1}J` the mean projector, and `λ_j = n_j = j+1`, so `δ_j = (j+1)^{-1} → 0`. The design
is deterministic (`𝒟 = ⊥`).

## Main results

* `perturb_tendstoInProb_of_moments_witness`: the theorem applied to the model.
* `pw_condExp_l2Norm_nu_sq`, `pw_condOmega_diag`, `pw_perturb_ne_zero`: the model is not
  degenerate.
* `wr_centeredSummand_ne_zero`: on the cluster-shock design of `ClusterShock`, the centered
  summands of the infeasible union meat (Lemma SM.B.13) are nonzero at every point.
-/

namespace Multiway
namespace PerturbWitness

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology

/-! ## The model -/

/-- `ν_o = s_o`, the fair sign on coordinate `o` of `ℕ → Bool`; distinct observations use
distinct coordinates. -/
noncomputable def pwNu (j : ℕ) (o : Fin (j + 1)) : (ℕ → Bool) → ℝ :=
  ClusterShock.bigSign o.val

/-- `x̃_{ok} ≡ 1` at `K = 1`, so that `B = 1`. -/
def pwXt (j : ℕ) : Fin (j + 1) → Fin 1 → (ℕ → Bool) → ℝ := fun _ _ _ => 1

/-- `Π = n^{-1}J`, the mean projector, deterministic and hence `⊥`-measurable. -/
noncomputable def pwPr (j : ℕ) : (ℕ → Bool) → Matrix (Fin (j + 1)) (Fin (j + 1)) ℝ :=
  fun _ => fun _ _ => 1 / ((j : ℝ) + 1)

/-- `λ_j = n_j = j+1`. -/
def pwLam (j : ℕ) : (ℕ → Bool) → ℝ := fun _ => (j : ℝ) + 1

theorem pwN_pos (j : ℕ) : (0 : ℝ) < (j : ℝ) + 1 := by positivity

theorem pwN_ne (j : ℕ) : ((j : ℝ) + 1) ≠ 0 := (pwN_pos j).ne'

theorem measurable_pwNu (j : ℕ) (o : Fin (j + 1)) : Measurable (pwNu j o) :=
  ClusterShock.measurable_bigSign _

theorem abs_pwNu_le (j : ℕ) (o : Fin (j + 1)) (ω : ℕ → Bool) : |pwNu j o ω| ≤ 1 :=
  ClusterShock.abs_bigSign_le _ ω

theorem pwNu_sq (j : ℕ) (o : Fin (j + 1)) (ω : ℕ → Bool) : pwNu j o ω ^ 2 = 1 := by
  have h := congrFun (ClusterShock.bigSign_mul_self o.val) ω
  simpa [pwNu, sq] using h

theorem pwNu_pow_four (j : ℕ) (o : Fin (j + 1)) :
    (fun ω => pwNu j o ω ^ 4) = fun _ => (1 : ℝ) := by
  funext ω
  have h : pwNu j o ω ^ 4 = (pwNu j o ω ^ 2) ^ 2 := by ring
  rw [h, pwNu_sq j o ω, one_pow]

/-- `‖ν‖² = n_j` identically, since every coordinate is a sign. -/
theorem pw_sum_sq_nu (j : ℕ) (ω : ℕ → Bool) :
    ∑ o : Fin (j + 1), pwNu j o ω ^ 2 = (j : ℝ) + 1 := by
  rw [Finset.sum_congr rfl fun o (_ : o ∈ Finset.univ) => pwNu_sq j o ω]
  simp

theorem pw_l2Norm_nu (j : ℕ) (ω : ℕ → Bool) :
    RateAgnostic.l2Norm (fun o => pwNu j o ω) = Real.sqrt ((j : ℝ) + 1) := by
  rw [RateAgnostic.l2Norm, pw_sum_sq_nu j ω]

theorem pw_l2Norm_nu_sq (j : ℕ) (ω : ℕ → Bool) :
    RateAgnostic.l2Norm (fun o => pwNu j o ω) ^ 2 = (j : ℝ) + 1 := by
  rw [RateAgnostic.sq_l2Norm, pw_sum_sq_nu j ω]

/-! ## `ϖ = Πν` is the sample mean, bounded by one -/

theorem pw_vp_apply (j : ℕ) (ω : ℕ → Bool) (o : Fin (j + 1)) :
    (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o
      = (∑ o' : Fin (j + 1), pwNu j o' ω) / ((j : ℝ) + 1) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [pwPr, Finset.sum_div]
  exact Finset.sum_congr rfl fun o' _ => by rw [one_div, inv_mul_eq_div]

theorem abs_pw_vp_le (j : ℕ) (ω : ℕ → Bool) (o : Fin (j + 1)) :
    |(pwPr j ω *ᵥ fun o' => pwNu j o' ω) o| ≤ 1 := by
  rw [pw_vp_apply, abs_div, abs_of_pos (pwN_pos j), div_le_one (pwN_pos j)]
  calc |∑ o' : Fin (j + 1), pwNu j o' ω| ≤ ∑ o' : Fin (j + 1), |pwNu j o' ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _o' : Fin (j + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun o' _ => abs_pwNu_le j o' ω
    _ = (j : ℝ) + 1 := by simp

theorem measurable_pw_vp (j : ℕ) (o : Fin (j + 1)) :
    Measurable fun ω => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o := by
  have he : (fun ω => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o)
      = fun ω => (∑ o' : Fin (j + 1), pwNu j o' ω) / ((j : ℝ) + 1) :=
    funext fun ω => pw_vp_apply j ω o
  rw [he]
  exact (Finset.measurable_sum _ fun o' _ => measurable_pwNu j o').div measurable_const

theorem pw_sum_sq_vp_le (j : ℕ) (ω : ℕ → Bool) :
    ∑ o : Fin (j + 1), ((pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) ^ 2 ≤ (j : ℝ) + 1 := by
  calc ∑ o : Fin (j + 1), ((pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) ^ 2
      ≤ ∑ _o : Fin (j + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun o _ => ?_
        have h := abs_pw_vp_le j ω o
        nlinarith [abs_nonneg ((pwPr j ω *ᵥ fun o' => pwNu j o' ω) o),
          sq_abs ((pwPr j ω *ᵥ fun o' => pwNu j o' ω) o)]
    _ = (j : ℝ) + 1 := by simp

theorem pw_l2Norm_vp_sq_le (j : ℕ) (ω : ℕ → Bool) :
    RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) ^ 2 ≤ (j : ℝ) + 1 := by
  rw [RateAgnostic.sq_l2Norm]
  exact pw_sum_sq_vp_le j ω

theorem pw_l2Norm_vp_le (j : ℕ) (ω : ℕ → Bool) :
    RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o)
      ≤ Real.sqrt ((j : ℝ) + 1) := by
  rw [RateAgnostic.l2Norm]
  exact Real.sqrt_le_sqrt (pw_sum_sq_vp_le j ω)

theorem measurable_pw_l2Norm_vp (j : ℕ) :
    Measurable fun ω =>
      RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) := by
  simp only [RateAgnostic.l2Norm]
  exact (Finset.measurable_sum _ fun o _ => (measurable_pw_vp j o).pow_const 2).sqrt

/-! ## The projector: Hermitian, idempotent, of trace `d_{[Δ]} + K_r = 1 + 0` -/

theorem pwPr_isHermitian (j : ℕ) (ω : ℕ → Bool) : (pwPr j ω).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext a b
  simp [pwPr, Matrix.conjTranspose_apply]

theorem pwPr_idem (j : ℕ) (ω : ℕ → Bool) : pwPr j ω * pwPr j ω = pwPr j ω := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [pwPr]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  push_cast
  field_simp

theorem pwPr_trace (j : ℕ) (ω : ℕ → Bool) : (pwPr j ω).trace = 1 + 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, pwPr]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  push_cast
  field_simp
  norm_num

/-! ## The conditional covariance vanishes off the sharing graph

Off the diagonal the two signs depend on different coordinates, so the integral of their product
factorizes and vanishes. -/

theorem pw_integral_nu_mul (j : ℕ) {o o' : Fin (j + 1)} (h : o ≠ o') :
    ∫ ω, pwNu j o ω * pwNu j o' ω ∂ClusterShock.bigCoins = 0 := by
  have hne : o.val ≠ o'.val := fun hv => h (Fin.ext hv)
  have hind : ProbabilityTheory.IndepFun (ClusterShock.bigSign o.val)
      (ClusterShock.bigSign o'.val) ClusterShock.bigCoins :=
    ClusterShock.iIndepFun_bigSign.indepFun hne
  have hfac := hind.integral_fun_mul_eq_mul_integral
    (ClusterShock.measurable_bigSign o.val).aestronglyMeasurable
    (ClusterShock.measurable_bigSign o'.val).aestronglyMeasurable
  simp only [pwNu]
  rw [hfac, ClusterShock.integral_bigSign o.val, zero_mul]

theorem pw_hz (j : ℕ) (o o' : Fin (j + 1))
    (h : ¬ Linked (RateAgnostic.seqC j) (RateAgnostic.seqDims j) o o') :
    ClusterShock.bigCoins[pwNu j o * pwNu j o' | (⊥ : MeasurableSpace (ℕ → Bool))]
      =ᵐ[ClusterShock.bigCoins] 0 := by
  have hne : o ≠ o' := fun he => h ((RateAgnostic.seqLinked_iff j o o').mpr he)
  rw [condExp_bot]
  have hint : ∫ ω, (pwNu j o * pwNu j o') ω ∂ClusterShock.bigCoins = 0 := by
    simp only [Pi.mul_apply]
    exact pw_integral_nu_mul j hne
  rw [hint]
  exact Filter.EventuallyEq.rfl

/-! ## The moment condition, and `hprod` -/

theorem pw_mom (j : ℕ) (o : Fin (j + 1)) : ∀ᵐ ω ∂ClusterShock.bigCoins,
    (ClusterShock.bigCoins[fun ω => pwNu j o ω ^ 4 | (⊥ : MeasurableSpace (ℕ → Bool))]) ω
      ≤ (1 : ℝ) := by
  rw [pwNu_pow_four j o, condExp_const bot_le]
  filter_upwards with ω
  exact le_rfl

theorem pw_prod (j : ℕ) (o o' : Fin (j + 1)) :
    MemLp (pwNu j o * pwNu j o') 2 ClusterShock.bigCoins := by
  refine (memLp_top_of_bound
    ((measurable_pwNu j o).mul (measurable_pwNu j o')).aestronglyMeasurable 1 ?_).mono_exponent
    le_top
  filter_upwards with ω
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  calc |pwNu j o ω| * |pwNu j o' ω| ≤ 1 * 1 :=
        mul_le_mul (abs_pwNu_le j o ω) (abs_pwNu_le j o' ω) (abs_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-! ## Integrability conditions -/

theorem pw_nuint (j : ℕ) :
    Integrable (fun ω => RateAgnostic.l2Norm (fun o => pwNu j o ω) ^ 2)
      ClusterShock.bigCoins := by
  have he : (fun ω => RateAgnostic.l2Norm (fun o => pwNu j o ω) ^ 2)
      = fun _ : ℕ → Bool => (j : ℝ) + 1 := funext fun ω => pw_l2Norm_nu_sq j ω
  rw [he]
  exact integrable_const _

theorem pw_vpint (j : ℕ) :
    Integrable (fun ω =>
        RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) ^ 2)
      ClusterShock.bigCoins := by
  refine Integrable.mono' (integrable_const ((j : ℝ) + 1))
    ((measurable_pw_l2Norm_vp j).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pw_l2Norm_vp_sq_le j ω

theorem pw_majint (j : ℕ) :
    Integrable (fun ω =>
        (1 : ℝ) ^ 2
            * ((Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ) + 1)
            / pwLam j ω
          * (2 * RateAgnostic.l2Norm (fun o => pwNu j o ω)
              * RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o)
            + RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) ^ 2))
      ClusterShock.bigCoins := by
  have hmeas : Measurable fun ω : ℕ → Bool =>
      (1 : ℝ) ^ 2
          * ((Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ) + 1)
          / pwLam j ω
        * (2 * RateAgnostic.l2Norm (fun o => pwNu j o ω)
            * RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o)
          + RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) ^ 2) := by
    simp only [pwLam]
    refine Measurable.mul measurable_const (Measurable.add ?_ ?_)
    · exact (measurable_const.mul
        (Finset.measurable_sum _ fun o _ =>
          (measurable_pwNu j o).pow_const 2).sqrt).mul (measurable_pw_l2Norm_vp j)
    · exact (measurable_pw_l2Norm_vp j).pow_const 2
  refine Integrable.mono' (integrable_const (6 : ℝ)) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  set s : ℝ := Real.sqrt ((j : ℝ) + 1) with hs
  set v : ℝ := RateAgnostic.l2Norm (fun o => (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) with hv
  have hs2 : s ^ 2 = (j : ℝ) + 1 := Real.sq_sqrt (pwN_pos j).le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := RateAgnostic.l2Norm_nonneg _
  have hvs : v ≤ s := pw_l2Norm_vp_le j ω
  have hnu : RateAgnostic.l2Norm (fun o => pwNu j o ω) = s := pw_l2Norm_nu j ω
  have hlam : pwLam j ω = (j : ℝ) + 1 := rfl
  have hD : (Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ) = 1 := by
    rw [RateAgnostic.seq_maxDegree j]
    norm_num
  rw [hnu, hlam, hD]
  have hnonneg : 0 ≤ (1 : ℝ) ^ 2 * ((1 : ℝ) + 1) / ((j : ℝ) + 1) * (2 * s * v + v ^ 2) := by
    have : 0 ≤ 2 * s * v + v ^ 2 := by positivity
    have h2 : 0 ≤ (1 : ℝ) ^ 2 * ((1 : ℝ) + 1) / ((j : ℝ) + 1) := by positivity
    exact mul_nonneg h2 this
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [div_mul_eq_mul_div, div_le_iff₀ (pwN_pos j)]
  nlinarith [hs2, hs0, hv0, hvs, mul_le_mul_of_nonneg_left hvs hs0,
    mul_self_le_mul_self hv0 hvs]

/-! ## The sharing and accumulation conditions at `λ_j = n_j`

`hsharing` holds as `(j+1)^{-1} ≤ 2(j+1)^{-1}` and `hacc` as `δ_j d_{[Δ]} = (j+1)^{-1} → 0`. -/

theorem pw_deltaSeq (j : ℕ) :
    Sharing.deltaSeq ((j : ℝ) + 1)
        ((Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ))
        (pwLam j default) = ((j : ℝ) + 1)⁻¹ := by
  have hD : (Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ) = 1 := by
    rw [RateAgnostic.seq_maxDegree j]
    norm_num
  rw [Sharing.deltaSeq, hD]
  have hlam : pwLam j default = (j : ℝ) + 1 := rfl
  rw [hlam]
  have hne := pwN_ne j
  field_simp

theorem pw_sharing (j : ℕ) (ω : ℕ → Bool) :
    ((Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ)) ^ 2 / pwLam j ω
      ≤ 2 * (1 : ℝ) ^ 2 * Real.sqrt 1
        * Sharing.deltaSeq ((j : ℝ) + 1)
            ((Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ))
            (pwLam j ω) := by
  have hD : (Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ) = 1 := by
    rw [RateAgnostic.seq_maxDegree j]
    norm_num
  have hlam : pwLam j ω = (j : ℝ) + 1 := rfl
  have hne := pwN_ne j
  rw [hD, hlam, Sharing.deltaSeq, Real.sqrt_one]
  rw [div_le_iff₀ (pwN_pos j)]
  field_simp
  norm_num

theorem pw_acc :
    TendstoInMeasure ClusterShock.bigCoins
      (fun (j : ℕ) (ω : ℕ → Bool) =>
        Sharing.deltaSeq ((j : ℝ) + 1)
            ((Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ))
            (pwLam j ω) * 1)
      atTop (fun _ => (0 : ℝ)) := by
  have hfun : (fun (j : ℕ) (_ : ℕ → Bool) =>
      Sharing.deltaSeq ((j : ℝ) + 1)
          ((Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ))
          (pwLam j default) * 1)
      = fun (j : ℕ) (_ : ℕ → Bool) => 1 / ((j : ℝ) + 1) := by
    funext j ω
    rw [pw_deltaSeq j, mul_one, inv_eq_one_div]
  rw [show (fun (j : ℕ) (ω : ℕ → Bool) =>
      Sharing.deltaSeq ((j : ℝ) + 1)
          ((Sharing.maxDegree (RateAgnostic.seqC j) (RateAgnostic.seqDims j) : ℝ))
          (pwLam j ω) * 1)
      = fun (j : ℕ) (_ : ℕ → Bool) => 1 / ((j : ℝ) + 1) from hfun]
  refine RateAgnostic.tendstoInMeasure_zero_of_tendsto_const ?_
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-! ## The theorem applied to the model -/

/-- `RateAgnostic.perturb_tendstoInProb_of_moments` applied to the growing product model above,
with every hypothesis verified. -/
theorem perturb_tendstoInProb_of_moments_witness :
    TendstoInMeasure ClusterShock.bigCoins
      (fun (j : ℕ) (ω : ℕ → Bool) =>
        rectFrobNorm (RateAgnostic.unionMeat (RateAgnostic.seqC j) (RateAgnostic.seqDims j)
            (pwXt j) (fun o ω => pwNu j o ω - (pwPr j ω *ᵥ fun o' => pwNu j o' ω) o) ω
          - RateAgnostic.unionMeat (RateAgnostic.seqC j) (RateAgnostic.seqDims j)
              (pwXt j) (pwNu j) ω) / pwLam j ω)
      atTop (fun _ => 0) := by
  refine RateAgnostic.perturb_tendstoInProb_of_moments (⊥ : MeasurableSpace (ℕ → Bool))
    (P := ClusterShock.bigCoins) bot_le
    (O := fun j => Fin (j + 1)) (D := fun _ => Fin 1) (L := fun j => Fin (j + 1))
    (κ := fun _ => Fin 1) RateAgnostic.seqC RateAgnostic.seqDims pwXt pwNu pwPr
    (B := 1) zero_le_one (fun j o ω => by simp [pwXt])
    (lam := pwLam) (fun _ => measurable_const) (fun j _ => pwN_pos j)
    (Cm := 1) (Kr := 0) one_pos le_rfl
    (nR := fun j => (j : ℝ) + 1) (dd := fun _ => 1) (fun j => pwN_pos j) (fun _ => le_rfl)
    (fun j => by simp) (fun _ _ _ => stronglyMeasurable_const)
    pwPr_isHermitian pwPr_idem pwPr_trace
    measurable_pwNu measurable_pw_vp pw_nuint pw_vpint pw_majint
    pw_prod pw_mom pw_hz pw_sharing ?_
  simpa using pw_acc

/-! ## Non-degeneracy of the model -/

/-- `E[‖ν‖² ∣ 𝒟] = n_j`, so the bound `a_j = C^{1/2} n_j` at `C = 1` holds with equality. -/
theorem pw_condExp_l2Norm_nu_sq (j : ℕ) :
    ClusterShock.bigCoins[fun ω => RateAgnostic.l2Norm (fun o => pwNu j o ω) ^ 2
        | (⊥ : MeasurableSpace (ℕ → Bool))] = fun _ => (j : ℝ) + 1 := by
  have he : (fun ω => RateAgnostic.l2Norm (fun o => pwNu j o ω) ^ 2)
      = fun _ : ℕ → Bool => (j : ℝ) + 1 := funext fun ω => pw_l2Norm_nu_sq j ω
  rw [he, condExp_const bot_le]

/-- `Ω_{oo} = E[ν_o² ∣ 𝒟] = 1`. -/
theorem pw_condOmega_diag (j : ℕ) (o : Fin (j + 1)) :
    ClusterShock.bigCoins[pwNu j o * pwNu j o | (⊥ : MeasurableSpace (ℕ → Bool))]
      = fun _ => (1 : ℝ) := by
  have he : pwNu j o * pwNu j o = fun _ : ℕ → Bool => (1 : ℝ) := by
    funext ω
    have h := pwNu_sq j o ω
    simpa [Pi.mul_apply, sq] using h
  rw [he, condExp_const bot_le]

/-- The point with coordinates `0` and `1` up and coordinate `2` down. -/
def pwOmega : ℕ → Bool := fun i => if i = 2 then false else true

/-- At `j = 2` and `ω = pwOmega`, `ν = (1,1,-1)`, `ϖ = Πν = (1/3,1/3,1/3)` and
`ν̂_FE = ν - ϖ = (2/3,2/3,-4/3)`; in particular `ϖ ≠ 0`, `ν̂_FE ≠ 0` and `ν̂_FE ≠ ν`. -/
theorem pw_perturb_ne_zero :
    (pwPr 2 pwOmega *ᵥ fun o' => pwNu 2 o' pwOmega) 0 = 1 / 3
      ∧ pwNu 2 0 pwOmega - (pwPr 2 pwOmega *ᵥ fun o' => pwNu 2 o' pwOmega) 0 ≠ 0
      ∧ pwNu 2 0 pwOmega - (pwPr 2 pwOmega *ᵥ fun o' => pwNu 2 o' pwOmega) 0
          ≠ pwNu 2 0 pwOmega := by
  have hsum : ∑ o' : Fin 3, pwNu 2 o' pwOmega = 1 := by
    rw [Fin.sum_univ_three]
    norm_num [pwNu, ClusterShock.bigSign, pwOmega]
  have hvp : (pwPr 2 pwOmega *ᵥ fun o' => pwNu 2 o' pwOmega) 0 = 1 / 3 := by
    rw [pw_vp_apply, hsum]
    norm_num
  have hnu : pwNu 2 0 pwOmega = 1 := by
    norm_num [pwNu, ClusterShock.bigSign, pwOmega]
  refine ⟨hvp, ?_, ?_⟩
  · rw [hvp, hnu]; norm_num
  · rw [hvp, hnu]; norm_num

/-! ## Nonzero centered summands on the cluster-shock design

On the design of `ClusterShock`'s `RAWitness` section (`𝒪_n = Fin (n+1) × Fin 2`, clusters of
two, `ν_o = c_{g(o)} + ε_o`), the centered summand `ν_o² - Ω_{oo} = 2 c_{g(o)} ε_o` is `±2` at
every point. -/

section MeatNonDegenerate

open ClusterShock

/-- `ν_o` on the cluster-shock design of `ClusterShock`'s `RAWitness` section. -/
noncomputable def wrNu (n : ℕ) (o : WrO n) : (ℕ → Bool) → ℝ :=
  Sharing.nuRV (wrC n) wrDims (wrZ n) o

/-- `ν_o = c_{g(o)} + ε_o`, with the two shocks named by their coordinates of `ℕ → Bool`. -/
theorem wrNu_apply (n : ℕ) (o : WrO n) (ω : ℕ → Bool) :
    wrNu n o ω = bigSign (3 * o.1.val) ω + bigSign (3 * o.1.val + 1 + o.2.val) ω := by
  rw [wrNu, Sharing.nuRV_apply]
  simp [wrDims, wrZ, wrIdx, wrC]

/-- The cluster shock and the idiosyncratic shock of one observation depend on different
coordinates. -/
theorem wr_idx_ne (n : ℕ) (o : WrO n) :
    3 * o.1.val ≠ 3 * o.1.val + 1 + o.2.val := by omega

theorem wr_integral_cross (n : ℕ) (o : WrO n) :
    ∫ ω, bigSign (3 * o.1.val) ω * bigSign (3 * o.1.val + 1 + o.2.val) ω ∂bigCoins = 0 := by
  have hind : ProbabilityTheory.IndepFun (bigSign (3 * o.1.val))
      (bigSign (3 * o.1.val + 1 + o.2.val)) bigCoins :=
    iIndepFun_bigSign.indepFun (wr_idx_ne n o)
  rw [hind.integral_fun_mul_eq_mul_integral
    (measurable_bigSign _).aestronglyMeasurable
    (measurable_bigSign _).aestronglyMeasurable,
    integral_bigSign (3 * o.1.val), zero_mul]

/-- `ν_o² = 2 + 2c_{g(o)}ε_o` pointwise, since both squares equal `1`. -/
theorem wrNu_sq_apply (n : ℕ) (o : WrO n) (ω : ℕ → Bool) :
    wrNu n o ω * wrNu n o ω
      = 2 + 2 * (bigSign (3 * o.1.val) ω * bigSign (3 * o.1.val + 1 + o.2.val) ω) := by
  have ha := congrFun (bigSign_mul_self (3 * o.1.val)) ω
  have hb := congrFun (bigSign_mul_self (3 * o.1.val + 1 + o.2.val)) ω
  simp only [Pi.mul_apply] at ha hb
  rw [wrNu_apply]
  nlinarith [ha, hb]

/-- `Ω_{oo} = E[ν_o² ∣ 𝒟] = 2` on the cluster-shock design, as an equality of functions. -/
theorem wr_condOmega_diag_eq_two (n : ℕ) (o : WrO n) :
    RateAgnostic.condOmegaKernel (⊥ : MeasurableSpace (ℕ → Bool)) bigCoins (wrNu n) o o
      = fun _ => (2 : ℝ) := by
  have hfun : wrNu n o * wrNu n o
      = fun ω => 2 + 2 * (bigSign (3 * o.1.val) ω
        * bigSign (3 * o.1.val + 1 + o.2.val) ω) := funext fun ω => wrNu_sq_apply n o ω
  have hmeas : Measurable fun ω : ℕ → Bool =>
      bigSign (3 * o.1.val) ω * bigSign (3 * o.1.val + 1 + o.2.val) ω :=
    (measurable_bigSign _).mul (measurable_bigSign _)
  have hcross : Integrable (fun ω : ℕ → Bool =>
      bigSign (3 * o.1.val) ω * bigSign (3 * o.1.val + 1 + o.2.val) ω) bigCoins := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    calc |bigSign (3 * o.1.val) ω| * |bigSign (3 * o.1.val + 1 + o.2.val) ω| ≤ 1 * 1 :=
          mul_le_mul (abs_bigSign_le _ ω) (abs_bigSign_le _ ω) (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hint : ∫ ω, (wrNu n o * wrNu n o) ω ∂bigCoins = 2 := by
    rw [hfun, integral_add (integrable_const (2 : ℝ)) (hcross.const_mul 2),
      integral_const_mul, wr_integral_cross n o]
    simp
  rw [RateAgnostic.condOmegaKernel, condExp_bot, hint]

/-- The centered summand `ξ̄_{oo} = ν_o² - Ω_{oo} = 2 c_{g(o)} ε_o` is `±2`, hence nonzero, at every
point. -/
theorem wr_centeredSummand_ne_zero (n : ℕ) (k l : Fin 1) (o : WrO n) (ω : ℕ → Bool) :
    RateAgnostic.centeredSummand (fun o k (_ : ℕ → Bool) => wrXt n o k) (wrNu n)
        (RateAgnostic.condOmegaKernel (⊥ : MeasurableSpace (ℕ → Bool)) bigCoins (wrNu n))
        k l (o, o) ω ≠ 0 := by
  have ha : bigSign (3 * o.1.val) ω = 1 ∨ bigSign (3 * o.1.val) ω = -1 := by
    unfold bigSign
    by_cases h : ω (3 * o.1.val) <;> simp [h]
  have hb : bigSign (3 * o.1.val + 1 + o.2.val) ω = 1
      ∨ bigSign (3 * o.1.val + 1 + o.2.val) ω = -1 := by
    unfold bigSign
    by_cases h : ω (3 * o.1.val + 1 + o.2.val) <;> simp [h]
  have hOm : RateAgnostic.condOmegaKernel (⊥ : MeasurableSpace (ℕ → Bool)) bigCoins (wrNu n) o o ω
      = 2 := congrFun (wr_condOmega_diag_eq_two n o) ω
  simp only [RateAgnostic.centeredSummand, wrXt, hOm, one_mul]
  rw [wrNu_sq_apply n o ω]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> norm_num

end MeatNonDegenerate

end PerturbWitness
end Multiway
