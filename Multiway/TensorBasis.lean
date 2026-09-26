/-
# Tensor-product bases of `L²` of a product measure

This file proves that the coordinatewise products of complete orthonormal systems form a
complete orthonormal system of `L²` of the product measure, and derives the expansion,
Parseval and the vanishing of the truncation gap. This is the basis expansion used in Step 2
of the proof of Theorem 4(b), stated for a general finite coordinate set `ι`, general factor
spaces and a general scalar field.

Completeness is reduced to one-dimensional completeness by Fubini
(`MeasureTheory.integral_fintype_prod_eq_prod`) and the fact that boxes generate the product
σ-algebra (`isPiSystem_pi`, `generateFrom_pi`).

## Main results

* `inner_tensorLp`: `⟪tensorLp g, tensorLp h⟫ = ∏ i, ⟪g i, h i⟫`.
* `prodHilbertBasis`: the product system as a `HilbertBasis`.
* `tensorFun_split`: an elementary tensor splits at any one coordinate.
* `norm_sq_trunc_add_norm_sq_sub`, `tendsto_norm_sub_truncBox`: Pythagoras for the
  truncation, and `‖h - h_L‖ → 0` for the box truncation `max_k r_k ≤ L`.
* `Witness.tensorBasis_witness`: a two-dimensional instance with the Fourier basis.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Analysis.Fourier.AddCircle

namespace Multiway.TensorBasis

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

/-! ## Elementary tensors in `L²` of a product measure -/

section Tensor

variable {ι : Type*} [Fintype ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {μ : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- The pointwise product of chosen representatives, `u ↦ ∏ i, g i (u i)`. -/
noncomputable def tensorFun (g : ∀ i, Lp 𝕜 2 (μ i)) : ((i : ι) → α i) → 𝕜 :=
  fun u => ∏ i, (g i) (u i)

theorem aestronglyMeasurable_tensorFun (g : ∀ i, Lp 𝕜 2 (μ i)) :
    AEStronglyMeasurable (tensorFun g) (Measure.pi μ) := by
  have h : tensorFun g = ∏ i : ι, (fun u : (i : ι) → α i => (g i) (u i)) := by
    funext u; simp [tensorFun, Finset.prod_apply]
  rw [h]
  refine Finset.aestronglyMeasurable_prod _ (fun i _ => ?_)
  exact (Lp.aestronglyMeasurable (g i)).comp_measurePreserving (measurePreserving_eval μ i)

theorem memLp_tensorFun (g : ∀ i, Lp 𝕜 2 (μ i)) : MemLp (tensorFun g) 2 (Measure.pi μ) := by
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_tensorFun g)]
  have key : (fun u : (i : ι) → α i => ‖tensorFun g u‖ ^ 2)
      = fun u => ∏ i, ‖(g i) (u i)‖ ^ 2 := by
    funext u; simp only [tensorFun, norm_prod, Finset.prod_pow]
  rw [key]
  refine Integrable.fintype_prod_dep (f := fun i x => ‖(g i) x‖ ^ 2) (fun i => ?_)
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (g i))).mp (Lp.memLp (g i))

/-- The elementary tensor `⨂ i, g i` as an element of `L²` of the product measure. -/
noncomputable def tensorLp (g : ∀ i, Lp 𝕜 2 (μ i)) : Lp 𝕜 2 (Measure.pi μ) :=
  (memLp_tensorFun g).toLp _

theorem coeFn_tensorLp (g : ∀ i, Lp 𝕜 2 (μ i)) :
    (tensorLp g : ((i : ι) → α i) → 𝕜) =ᵐ[Measure.pi μ] tensorFun g :=
  MemLp.coeFn_toLp _

/-- **Fubini.**  The inner product of two elementary tensors is the product of the
coordinatewise inner products. -/
theorem inner_tensorLp (g h : ∀ i, Lp 𝕜 2 (μ i)) :
    ⟪tensorLp g, tensorLp h⟫_𝕜 = ∏ i, ⟪g i, h i⟫_𝕜 := by
  rw [L2.inner_def]
  have hae : ∀ᵐ u ∂(Measure.pi μ),
      ⟪(tensorLp g : ((i : ι) → α i) → 𝕜) u, (tensorLp h : ((i : ι) → α i) → 𝕜) u⟫_𝕜
        = ∏ i, ((h i) (u i) * (starRingEnd 𝕜) ((g i) (u i))) := by
    filter_upwards [coeFn_tensorLp g, coeFn_tensorLp h] with u hu hv
    rw [hu, hv, RCLike.inner_apply]
    simp only [tensorFun, map_prod, Finset.prod_mul_distrib]
  rw [integral_congr_ae hae,
    integral_fintype_prod_eq_prod (fun i (x : α i) => (h i) x * (starRingEnd 𝕜) ((g i) x))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall (fun x => RCLike.inner_apply _ _))

theorem norm_tensorLp (g : ∀ i, Lp 𝕜 2 (μ i)) : ‖tensorLp g‖ = ∏ i, ‖g i‖ := by
  have key : ⟪tensorLp g, tensorLp g⟫_𝕜 = (((∏ i, ‖g i‖) ^ 2 : ℝ) : 𝕜) := by
    rw [inner_tensorLp]
    push_cast
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => inner_self_eq_norm_sq_to_K _
  have h2 : ‖tensorLp g‖ ^ 2 = (∏ i, ‖g i‖) ^ 2 := by
    have := congrArg (RCLike.re (K := 𝕜)) key
    rwa [inner_self_eq_norm_sq, RCLike.ofReal_re] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)).mp h2

/-! ### The slice of an elementary tensor in one coordinate -/

/-- A `μ j`-a.e. statement pulls back to a `Measure.pi μ`-a.e. statement about the
`j`-th coordinate. -/
private theorem ae_eval {j : ι} (p : α j → Prop) (h : ∀ᵐ x ∂(μ j), p x) :
    ∀ᵐ u ∂(Measure.pi μ), p (u j) :=
  (Measure.quasiMeasurePreserving_eval μ j).ae h

variable [DecidableEq ι]

omit [Fintype ι] in
/-- Reading an update off coordinatewise. -/
private theorem apply_update {β : ι → Sort*} {γ : Sort*} (F : ∀ i, β i → γ) (g : ∀ i, β i)
    (j : ι) (z : β j) (i : ι) :
    F i (Function.update g j z i) = Function.update (fun i => F i (g i)) j (F j z) i := by
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update_of_ne h]

omit [∀ i, IsProbabilityMeasure (μ i)] in
theorem tensorFun_update (g : ∀ i, Lp 𝕜 2 (μ i)) (j : ι) (z : Lp 𝕜 2 (μ j))
    (u : (i : ι) → α i) :
    tensorFun (Function.update g j z) u
      = (z : α j → 𝕜) (u j) * ∏ i ∈ Finset.univ \ {j}, (g i) (u i) := by
  have h : (fun i => ((Function.update g j z) i : α i → 𝕜) (u i))
      = Function.update (fun i => ((g i : α i → 𝕜) (u i))) j ((z : α j → 𝕜) (u j)) :=
    funext fun i => apply_update (fun i (x : Lp 𝕜 2 (μ i)) => (x : α i → 𝕜) (u i)) g j z i
  show ∏ i, ((Function.update g j z) i : α i → 𝕜) (u i) = _
  rw [h]
  exact Finset.prod_update_of_mem (Finset.mem_univ j) _ _

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- An elementary tensor splits at any one coordinate into the factor at that coordinate
times the product of the others. -/
theorem tensorFun_split (g : ∀ i, Lp 𝕜 2 (μ i)) (j : ι) (u : (i : ι) → α i) :
    tensorFun g u = (g j : α j → 𝕜) (u j) * ∏ i ∈ Finset.univ \ {j}, (g i) (u i) := by
  have h := tensorFun_update g j (g j) u
  rwa [Function.update_eq_self] at h

theorem norm_tensorLp_update (g : ∀ i, Lp 𝕜 2 (μ i)) (j : ι) (z : Lp 𝕜 2 (μ j)) :
    ‖tensorLp (Function.update g j z)‖ = ‖z‖ * ∏ i ∈ Finset.univ \ {j}, ‖g i‖ := by
  rw [norm_tensorLp]
  have h : (fun i => ‖Function.update g j z i‖)
      = Function.update (fun i => ‖g i‖) j ‖z‖ :=
    funext fun i => apply_update (fun i (x : Lp 𝕜 2 (μ i)) => ‖x‖) g j z i
  show ∏ i, ‖Function.update g j z i‖ = _
  rw [h]
  exact Finset.prod_update_of_mem (Finset.mem_univ j) _ _

theorem tensorLp_update_add (g : ∀ i, Lp 𝕜 2 (μ i)) (j : ι) (z₁ z₂ : Lp 𝕜 2 (μ j)) :
    tensorLp (Function.update g j (z₁ + z₂))
      = tensorLp (Function.update g j z₁) + tensorLp (Function.update g j z₂) := by
  refine Lp.ext ?_
  have hz : ∀ᵐ u ∂(Measure.pi μ),
      ((z₁ + z₂ : Lp 𝕜 2 (μ j)) : α j → 𝕜) (u j)
        = (z₁ : α j → 𝕜) (u j) + (z₂ : α j → 𝕜) (u j) := by
    refine ae_eval (fun x => ((z₁ + z₂ : Lp 𝕜 2 (μ j)) : α j → 𝕜) x
      = (z₁ : α j → 𝕜) x + (z₂ : α j → 𝕜) x) ?_
    filter_upwards [Lp.coeFn_add z₁ z₂] with x hx
    rw [hx]; rfl
  filter_upwards [coeFn_tensorLp (Function.update g j (z₁ + z₂)),
    coeFn_tensorLp (Function.update g j z₁), coeFn_tensorLp (Function.update g j z₂),
    Lp.coeFn_add (tensorLp (Function.update g j z₁)) (tensorLp (Function.update g j z₂)),
    hz] with u h0 h1 h2 h3 h4
  rw [h0, h3, Pi.add_apply, h1, h2, tensorFun_update, tensorFun_update, tensorFun_update, h4]
  ring

theorem tensorLp_update_smul (g : ∀ i, Lp 𝕜 2 (μ i)) (j : ι) (c : 𝕜) (z : Lp 𝕜 2 (μ j)) :
    tensorLp (Function.update g j (c • z)) = c • tensorLp (Function.update g j z) := by
  refine Lp.ext ?_
  have hz : ∀ᵐ u ∂(Measure.pi μ),
      ((c • z : Lp 𝕜 2 (μ j)) : α j → 𝕜) (u j) = c * (z : α j → 𝕜) (u j) := by
    refine ae_eval (fun x => ((c • z : Lp 𝕜 2 (μ j)) : α j → 𝕜) x
      = c * (z : α j → 𝕜) x) ?_
    filter_upwards [Lp.coeFn_smul c z] with x hx
    rw [hx]; rfl
  filter_upwards [coeFn_tensorLp (Function.update g j (c • z)),
    coeFn_tensorLp (Function.update g j z),
    Lp.coeFn_smul c (tensorLp (Function.update g j z)), hz] with u h0 h1 h2 h3
  rw [h0, h2, Pi.smul_apply, h1, tensorFun_update, tensorFun_update, h3, smul_eq_mul]
  ring

/-- The elementary tensor, as a function of its `j`-th factor alone, is linear. -/
noncomputable def sliceLM (g : ∀ i, Lp 𝕜 2 (μ i)) (j : ι) :
    Lp 𝕜 2 (μ j) →ₗ[𝕜] Lp 𝕜 2 (Measure.pi μ) where
  toFun z := tensorLp (Function.update g j z)
  map_add' := tensorLp_update_add g j
  map_smul' c z := tensorLp_update_smul g j c z

/-- The slice map is continuous, with norm the product of the remaining factors' norms. -/
noncomputable def sliceCLM (g : ∀ i, Lp 𝕜 2 (μ i)) (j : ι) :
    Lp 𝕜 2 (μ j) →L[𝕜] Lp 𝕜 2 (Measure.pi μ) :=
  (sliceLM g j).mkContinuous (∏ i ∈ Finset.univ \ {j}, ‖g i‖) fun z => by
    show ‖tensorLp (Function.update g j z)‖ ≤ _
    rw [norm_tensorLp_update, mul_comm]

@[simp] theorem sliceCLM_apply (g : ∀ i, Lp 𝕜 2 (μ i)) (j : ι) (z : Lp 𝕜 2 (μ j)) :
    sliceCLM g j z = tensorLp (Function.update g j z) := rfl

end Tensor

/-! ## The product system is orthonormal -/

section Orthonormal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {μ : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (μ i)]
variable {R : Type*}

/-- The product basis element `⨂_i b_i(r_i)` at a multi-index `r`. -/
noncomputable def basisProd (b : ∀ i, HilbertBasis R 𝕜 (Lp 𝕜 2 (μ i))) (r : ι → R) :
    Lp 𝕜 2 (Measure.pi μ) :=
  tensorLp (fun i => b i (r i))

omit [DecidableEq ι] in
theorem orthonormal_basisProd (b : ∀ i, HilbertBasis R 𝕜 (Lp 𝕜 2 (μ i))) :
    Orthonormal 𝕜 (basisProd b) := by
  constructor
  · intro r
    rw [basisProd, norm_tensorLp]
    exact Finset.prod_eq_one fun i _ => (b i).orthonormal.1 (r i)
  · intro r s hrs
    rw [basisProd, basisProd, inner_tensorLp]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hrs
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((b i).orthonormal.2 hi)

end Orthonormal

/-! ## The product system is complete -/

section Complete

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {μ : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (μ i)]
variable {R : Type*}

/-- A vector orthogonal to every product of basis elements is orthogonal to every
elementary tensor. -/
theorem inner_tensorLp_eq_zero (b : ∀ i, HilbertBasis R 𝕜 (Lp 𝕜 2 (μ i)))
    {f : Lp 𝕜 2 (Measure.pi μ)} (hf : ∀ r : ι → R, ⟪f, basisProd b r⟫_𝕜 = 0)
    (g : ∀ i, Lp 𝕜 2 (μ i)) : ⟪f, tensorLp g⟫_𝕜 = 0 := by
  suffices H : ∀ T : Finset ι, ∀ g : ∀ i, Lp 𝕜 2 (μ i),
      (∀ i ∉ T, g i ∈ Set.range (b i)) → ⟪f, tensorLp g⟫_𝕜 = 0 by
    exact H Finset.univ g (by simp)
  intro T
  induction T using Finset.induction with
  | empty =>
      intro g hg
      choose r hr using fun i => hg i (Finset.notMem_empty i)
      have : g = fun i => b i (r i) := funext fun i => (hr i).symm
      rw [this]
      exact hf r
  | insert j T hj ih =>
      intro g hg
      set L : Lp 𝕜 2 (μ j) →L[𝕜] 𝕜 := (innerSL 𝕜 f).comp (sliceCLM g j) with hL
      have hker : Set.range (b j) ⊆ (LinearMap.ker (L : Lp 𝕜 2 (μ j) →ₗ[𝕜] 𝕜) : Set _) := by
        rintro _ ⟨t, rfl⟩
        have : ⟪f, tensorLp (Function.update g j (b j t))⟫_𝕜 = 0 := by
          refine ih _ fun i hi => ?_
          by_cases hij : i = j
          · subst hij; rw [Function.update_self]; exact ⟨t, rfl⟩
          · rw [Function.update_of_ne hij]
            exact hg i (by simp [hij, hi])
        simpa [hL, LinearMap.mem_ker] using this
      have hspan : Submodule.span 𝕜 (Set.range (b j))
          ≤ LinearMap.ker (L : Lp 𝕜 2 (μ j) →ₗ[𝕜] 𝕜) := Submodule.span_le.mpr hker
      have htop : (⊤ : Submodule 𝕜 (Lp 𝕜 2 (μ j)))
          ≤ LinearMap.ker (L : Lp 𝕜 2 (μ j) →ₗ[𝕜] 𝕜) := by
        rw [← (b j).dense_span]
        exact Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
      have hgj : L (g j) = 0 := htop (Submodule.mem_top)
      have : Function.update g j (g j) = g := Function.update_eq_self j g
      simpa [hL, this] using hgj

omit [DecidableEq ι] in
/-- At indicator factors the elementary tensor is the indicator of the box. -/
theorem tensorLp_indicatorConst (s : ∀ i, Set (α i)) (hs : ∀ i, MeasurableSet (s i)) :
    tensorLp (fun i => indicatorConstLp 2 (hs i) (measure_ne_top (μ i) (s i)) (1 : 𝕜))
      = indicatorConstLp 2 (MeasurableSet.univ_pi hs)
          (measure_ne_top (Measure.pi μ) _) (1 : 𝕜) := by
  refine Lp.ext ?_
  have hcoord : ∀ᵐ u ∂(Measure.pi μ), ∀ i,
      ((indicatorConstLp 2 (hs i) (measure_ne_top (μ i) (s i)) (1 : 𝕜)) : α i → 𝕜) (u i)
        = (s i).indicator (fun _ => (1 : 𝕜)) (u i) := by
    rw [ae_all_iff]
    intro i
    exact ae_eval _ indicatorConstLp_coeFn
  filter_upwards [coeFn_tensorLp
      (fun i => indicatorConstLp 2 (hs i) (measure_ne_top (μ i) (s i)) (1 : 𝕜)),
    (indicatorConstLp_coeFn :
      ((indicatorConstLp 2 (MeasurableSet.univ_pi hs)
        (measure_ne_top (Measure.pi μ) _) (1 : 𝕜)) : ((i : ι) → α i) → 𝕜)
        =ᵐ[Measure.pi μ] _),
    hcoord] with u h0 h1 h2
  rw [h0, h1]
  show (∏ i, _) = _
  simp_rw [h2]
  by_cases h : u ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem h]
    exact Finset.prod_eq_one fun i _ => Set.indicator_of_mem (h i (Set.mem_univ i)) _
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- **Completeness.** Only `0` is orthogonal to every product of basis
elements. -/
theorem orthogonal_span_basisProd_eq_bot (b : ∀ i, HilbertBasis R 𝕜 (Lp 𝕜 2 (μ i))) :
    (Submodule.span 𝕜 (Set.range (basisProd b)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hzero : ∀ r : ι → R, ⟪f, basisProd b r⟫_𝕜 = 0 := by
    intro r
    rw [← inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ f).mp hf _ (Submodule.subset_span ⟨r, rfl⟩)
  -- every box integral vanishes
  have hbox : ∀ (s : ∀ i, Set (α i)), (∀ i, MeasurableSet (s i)) →
      ∫ u in Set.univ.pi s, (f : ((i : ι) → α i) → 𝕜) u ∂(Measure.pi μ) = 0 := by
    intro s hs
    rw [← L2.inner_indicatorConstLp_one (MeasurableSet.univ_pi hs)
      (measure_ne_top (Measure.pi μ) _) f, ← tensorLp_indicatorConst s hs,
      ← inner_eq_zero_symm]
    exact inner_tensorLp_eq_zero b hzero _
  have hint : Integrable (f : ((i : ι) → α i) → 𝕜) (Measure.pi μ) :=
    (Lp.memLp f).integrable one_le_two
  have huniv : ∫ u, (f : ((i : ι) → α i) → 𝕜) u ∂(Measure.pi μ) = 0 := by
    have := hbox (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
    rwa [Set.pi_univ, Measure.restrict_univ] at this
  -- Dynkin argument over the boxes
  have hall : ∀ t, MeasurableSet t →
      ∫ u in t, (f : ((i : ι) → α i) → 𝕜) u ∂(Measure.pi μ) = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => ∫ u in t, (f : ((i : ι) → α i) → 𝕜) u ∂(Measure.pi μ) = 0)
      generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_
    · simp
    · rintro t ⟨s, hs, rfl⟩
      exact hbox s fun i => hs i (Set.mem_univ i)
    · intro t htm ht
      have := integral_add_compl htm hint
      rw [ht, huniv, zero_add] at this
      exact this
    · intro u hud hum hu
      rw [integral_iUnion hum hud hint.integrableOn]
      simp [hu]
  have : (f : ((i : ι) → α i) → 𝕜) =ᵐ[Measure.pi μ] 0 :=
    Lp.ae_eq_zero_of_forall_setIntegral_eq_zero f two_ne_zero ENNReal.ofNat_ne_top
      (fun s _ _ => hint.integrableOn) (fun s hs _ => hall s hs)
  exact Lp.eq_zero_iff_ae_eq_zero.mpr this

/-- The coordinatewise products of complete orthonormal systems form a complete orthonormal
system of `L²` of the product measure. -/
noncomputable def prodHilbertBasis (b : ∀ i, HilbertBasis R 𝕜 (Lp 𝕜 2 (μ i))) :
    HilbertBasis (ι → R) 𝕜 (Lp 𝕜 2 (Measure.pi μ)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_basisProd b) (orthogonal_span_basisProd_eq_bot b)

@[simp] theorem coe_prodHilbertBasis (b : ∀ i, HilbertBasis R 𝕜 (Lp 𝕜 2 (μ i))) :
    ⇑(prodHilbertBasis b) = basisProd b :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

end Complete

/-! ## Truncation -/

section Truncation

variable {Λ 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The truncation of `x` to a finite set of indices. -/
noncomputable def trunc (B : HilbertBasis Λ 𝕜 E) (x : E) (F : Finset Λ) : E :=
  ∑ r ∈ F, B.repr x r • B r

/-- The truncation gap `‖x - trunc B x F‖` tends to `0` along the finite subsets of the
index set. -/
theorem tendsto_norm_sub_trunc (B : HilbertBasis Λ 𝕜 E) (x : E) :
    Tendsto (fun F => ‖x - trunc B x F‖) atTop (nhds 0) := by
  have h : Tendsto (fun F : Finset Λ => trunc B x F) atTop (nhds x) := B.hasSum_repr x
  have h2 : Tendsto (fun F : Finset Λ => x - trunc B x F) atTop (nhds (x - x)) :=
    tendsto_const_nhds.sub h
  simpa using h2.norm

/-- The coefficient of an index outside the truncation set is unchanged by truncating. -/
theorem inner_sub_trunc (B : HilbertBasis Λ 𝕜 E) (x : E) (F : Finset Λ) {r : Λ} (hr : r ∉ F) :
    ⟪B r, x - trunc B x F⟫_𝕜 = B.repr x r := by
  rw [inner_sub_right, ← B.repr_apply_apply, trunc, inner_sum]
  have hz : ∀ s ∈ F, ⟪B r, B.repr x s • B s⟫_𝕜 = 0 := by
    intro s hs
    have hne : r ≠ s := by rintro rfl; exact hr hs
    rw [inner_smul_right, B.orthonormal.2 hne, mul_zero]
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, sub_zero]

/-- The coefficient of an index inside the truncation set is annihilated by truncating. -/
theorem inner_sub_trunc_of_mem (B : HilbertBasis Λ 𝕜 E) (x : E) (F : Finset Λ) {s : Λ}
    (hs : s ∈ F) : ⟪B s, x - trunc B x F⟫_𝕜 = 0 := by
  classical
  rw [inner_sub_right, ← B.repr_apply_apply, trunc, inner_sum,
    Finset.sum_eq_single s (fun t ht hts => by
      rw [inner_smul_right, B.orthonormal.2 (Ne.symm hts), mul_zero])
      (fun h => absurd hs h)]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, B.orthonormal.1 s]
  simp

theorem inner_trunc_sub_eq_zero (B : HilbertBasis Λ 𝕜 E) (x : E) (F : Finset Λ) :
    ⟪trunc B x F, x - trunc B x F⟫_𝕜 = 0 := by
  show ⟪∑ s ∈ F, B.repr x s • B s, x - trunc B x F⟫_𝕜 = 0
  rw [sum_inner]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [inner_smul_left, inner_sub_trunc_of_mem B x F hs, mul_zero]

/-- **Pythagoras for the truncation.** The squared norm of the truncation and the squared
truncation gap add up to `‖x‖²`. -/
theorem norm_sq_trunc_add_norm_sq_sub (B : HilbertBasis Λ 𝕜 E) (x : E) (F : Finset Λ) :
    ‖trunc B x F‖ ^ 2 + ‖x - trunc B x F‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (trunc B x F) (x - trunc B x F) (inner_trunc_sub_eq_zero B x F)
  rw [add_sub_cancel] at h
  rw [pow_two, pow_two, pow_two]
  exact h.symm

/-- If `x` has a nonvanishing coefficient outside the truncation set, the truncation error is
strictly positive. -/
theorem norm_sub_trunc_pos (B : HilbertBasis Λ 𝕜 E) (x : E) (F : Finset Λ) {r : Λ}
    (hr : r ∉ F) (hx : B.repr x r ≠ 0) : 0 < ‖x - trunc B x F‖ := by
  rw [norm_pos_iff]
  intro h
  refine hx ?_
  rw [← inner_sub_trunc B x F hr, h, inner_zero_right]

/-! ### Box truncation `max_k r_k ≤ L` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The truncation set `{𝐫 : max_k r_k ≤ L}`. -/
def box (ι : Type*) [Fintype ι] [DecidableEq ι] (L : ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (L + 1)

theorem mem_box {L : ℕ} {r : ι → ℕ} : r ∈ box ι L ↔ ∀ i, r i ≤ L := by
  simp [box, Fintype.mem_piFinset]

theorem tendsto_box : Tendsto (box ι) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun F => ⟨F.sup fun r => Finset.univ.sup r, fun L hL => ?_⟩
  intro r hr
  rw [mem_box]
  intro i
  calc r i ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ i)
    _ ≤ F.sup fun r => Finset.univ.sup r := Finset.le_sup hr
    _ ≤ L := hL

/-- With the truncation taken at `max_k r_k ≤ L`, the `L²` distance from `x` to its
truncation tends to `0` as `L → ∞`. -/
theorem tendsto_norm_sub_truncBox (B : HilbertBasis (ι → ℕ) 𝕜 E) (x : E) :
    Tendsto (fun L => ‖x - trunc B x (box ι L)‖) atTop (nhds 0) :=
  (tendsto_norm_sub_trunc B x).comp tendsto_box

/-! ### The truncation of a kernel, in the product basis -/

section KernelTruncation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {μ : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (μ i)]
variable {R : Type*}

/-- The truncation of `h` in the product basis is the finite linear combination
`∑_{𝐫 ∈ F} λ_𝐫 ⨂_k ψ_{r_k}` with `λ_𝐫 = ⟪⨂_k ψ_{r_k}, h⟫`. -/
theorem trunc_prodHilbertBasis (b : ∀ i, HilbertBasis R 𝕜 (Lp 𝕜 2 (μ i)))
    (x : Lp 𝕜 2 (Measure.pi μ)) (F : Finset (ι → R)) :
    trunc (prodHilbertBasis b) x F
      = ∑ r ∈ F, ⟪basisProd b r, x⟫_𝕜 • basisProd b r := by
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [HilbertBasis.repr_apply_apply, coe_prodHilbertBasis]

end KernelTruncation

end Truncation

/-! ## Example

The coordinate set is `Fin 2` and the one-dimensional system is Mathlib's `fourierBasis` on
`AddCircle 1`, reindexed by `ℕ`. The vector `wit` has a nonzero coefficient at every
multi-index, so its truncation gap is strictly positive at every level `L` while tending to `0`.
-/

namespace Witness

open AddCircle

/-- Each coordinate is the circle `ℝ/ℤ`. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

/-- Each coordinate has the Haar probability measure. -/
noncomputable abbrev hmu : ∀ _ : Fin 2, Measure Circ := fun _ => AddCircle.haarAddCircle

/-- Mathlib's Fourier basis of `L²` of the circle, reindexed by `ℕ`. -/
noncomputable def fourierNat : HilbertBasis ℕ ℂ (Lp ℂ 2 (hmu 0)) :=
  HilbertBasis.mk
    ((fourierBasis (T := (1 : ℝ))).orthonormal.comp _ (Denumerable.eqv ℤ).symm.injective)
    (by
      have hrange : Set.range (⇑(fourierBasis (T := (1 : ℝ))) ∘ ⇑(Denumerable.eqv ℤ).symm)
          = Set.range ⇑(fourierBasis (T := (1 : ℝ))) := by
        rw [Set.range_comp, (Denumerable.eqv ℤ).symm.range_eq_univ, Set.image_univ]
      rw [hrange]
      exact (fourierBasis (T := (1 : ℝ))).dense_span.ge)

/-- The one-dimensional system `{ψ_r}`, the same in each of the two coordinates. -/
noncomputable def psi : ∀ i : Fin 2, HilbertBasis ℕ ℂ (Lp ℂ 2 (hmu i)) := fun _ => fourierNat

/-- The product system at `k = 2`. -/
noncomputable def PB : HilbertBasis (Fin 2 → ℕ) ℂ (Lp ℂ 2 (Measure.pi hmu)) :=
  prodHilbertBasis psi

/-- An injection of the multi-index set into `ℕ`, so that a geometric series can be indexed
by it. -/
def enc (r : Fin 2 → ℕ) : ℕ := Nat.pair (r 0) (r 1)

theorem enc_injective : Function.Injective enc := by
  intro r s h
  rw [enc, enc, Nat.pair_eq_pair] at h
  funext i
  fin_cases i
  · exact h.1
  · exact h.2

/-- Coefficients that are nonzero at every multi-index. -/
noncomputable def coefs (r : Fin 2 → ℕ) : ℂ := ((1 : ℂ) / 2) ^ enc r

theorem coefs_ne_zero (r : Fin 2 → ℕ) : coefs r ≠ 0 := pow_ne_zero _ (by norm_num)

theorem memlp_coefs : Memℓp coefs 2 := by
  refine memℓp_gen ?_
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2]
  have hfun : (fun r : Fin 2 → ℕ => ‖coefs r‖ ^ (((2 : ℕ)) : ℝ))
      = (fun n : ℕ => ((1 : ℝ) / 4) ^ n) ∘ enc := by
    funext r
    rw [Real.rpow_natCast]
    simp only [Function.comp_apply, coefs, norm_pow]
    rw [show ‖((1 : ℂ) / 2)‖ = (1 : ℝ) / 2 from by norm_num, ← pow_mul,
      show (1 : ℝ) / 4 = ((1 : ℝ) / 2) ^ 2 from by norm_num, ← pow_mul, mul_comm]
  rw [hfun]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective enc_injective

/-- The vector `wit`, the element of `L²` of the two-dimensional torus whose coefficient
against every product `ψ_{r_0} ⊗ ψ_{r_1}` is nonzero. -/
noncomputable def wit : Lp ℂ 2 (Measure.pi hmu) := PB.repr.symm ⟨coefs, memlp_coefs⟩

theorem repr_wit (r : Fin 2 → ℕ) : PB.repr wit r = coefs r := by
  rw [wit, LinearIsometryEquiv.apply_symm_apply]

/-- Two multi-indices agreeing in the first coordinate and differing in the second give
orthogonal products. -/
theorem cross_orthogonal : ⟪basisProd psi ![0, 0], basisProd psi ![0, 1]⟫_ℂ = 0 := by
  refine (orthonormal_basisProd psi).2 (fun h => ?_)
  have := congrFun h 1
  simp at this

theorem basisProd_norm_one (r : Fin 2 → ℕ) : ‖basisProd psi r‖ = 1 :=
  (orthonormal_basisProd psi).1 r

/-- At `k = 2`, the truncation gap of `wit` in the product basis is strictly positive at
every finite level `L` and tends to `0`. -/
theorem tensorBasis_witness :
    Fintype.card (Fin 2) = 2 ∧
    (∀ L : ℕ, 0 < ‖wit - trunc PB wit (box (Fin 2) L)‖) ∧
    Tendsto (fun L : ℕ => ‖wit - trunc PB wit (box (Fin 2) L)‖) atTop (nhds 0) := by
  refine ⟨by simp, fun L => ?_, tendsto_norm_sub_truncBox _ _⟩
  refine norm_sub_trunc_pos PB wit _ (r := fun _ => L + 1) ?_ ?_
  · simp only [mem_box, not_forall]
    exact ⟨0, by omega⟩
  · rw [repr_wit]
    exact coefs_ne_zero _

end Witness

end Multiway.TensorBasis
