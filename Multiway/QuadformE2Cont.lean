import Multiway.QuadformE2Indep
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Lemma SM.C.6 under Regime 2 with a continuum latent alphabet

This file formalizes Lemma SM.C.6 of the paper (variance of a quadratic form under interaction
dependence) under Regime 2 of the dependence assumption, with latent variables on an arbitrary
measurable alphabet `V`. The law is `P := Measure.pi μ` on `Ω := Site D L O → V`, one probability
measure per site; `V = ℝ` with the uniform law on `[0,1]` is the model of the paper. The site
bookkeeping and Young's inequalities come from `Multiway/QuadformE2Indep.lean`. The expectation
`E` in `var_quadForm_le_levels` is `expLM P`, a linear extension of the Bochner integral to
all of `Ω → ℝ`; it agrees with `∫ · ∂P` on integrable functions and does not appear in any
statement. `P` is read as the conditional law given `𝒟` along a realization, with `W` fixed.

## Main results

* `integral_mul_eq_zero_of_intZeroAt`, `integral_mul_eq_mul_of_disjoint`: the two probabilistic
  facts (complete degeneracy at a site; independence across disjoint sets of sites).
* `var_quadForm_le_regime2_cont`: Lemma SM.C.6 under Regime 2, stated with Bochner integrals.
* `regime2_cont_witness`: an example with latents uniform on `[0,1]` and
  `Var(ζ'Wζ ∣ 𝒟) = 4`.
-/

namespace Multiway
namespace QuadformE2Cont

open Finset MeasureTheory
open Multiway.QuadformE2
open Multiway.QuadformE2Indep (FreeAt DependsOn dependsOn_mono dependsOn_mul dependsOn_one
  freeAt_of_dependsOn freeAt_mul freeAt_one Site sitemap siteSet mem_siteSet siteSet_nonempty
  sitemap_of_idio sitemap_of_not_idio mem_lev_and_idx_eq_of_mem_siteSet sharesSite_of_mem_both
  abs_mul_four_le abs_mul_two_le)

/-! ## `E`: a linear extension of the integral

The integrable functions form a submodule of `Ω → ℝ`, and the integral extends from it to a
linear functional on all of `Ω → ℝ` (`LinearMap.exists_extend`). Its values off `L¹` are never
used. -/

section Extension

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `P`-integrable functions, as a submodule of all real functions on `Ω`. -/
def integrableSub (P : Measure Ω) : Submodule ℝ (Ω → ℝ) where
  carrier := {f | Integrable f P}
  add_mem' hf hg := hf.add hg
  zero_mem' := integrable_zero _ _ _
  smul_mem' c _ hf := hf.smul c

theorem mem_integrableSub {P : Measure Ω} {f : Ω → ℝ} :
    f ∈ integrableSub P ↔ Integrable f P := Iff.rfl

/-- The integral, as a linear functional on the integrable functions. -/
noncomputable def intLin (P : Measure Ω) : integrableSub P →ₗ[ℝ] ℝ where
  toFun f := ∫ ω, (f : Ω → ℝ) ω ∂P
  map_add' f g := integral_add f.2 g.2
  map_smul' c f := by
    simpa using integral_smul (μ := P) c (f : Ω → ℝ)

/-- A linear functional on all of `Ω → ℝ` agreeing with `∫ · ∂P` on `L¹`. -/
noncomputable def expLM (P : Measure Ω) : (Ω → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.exists_extend (intLin P)).choose

/-- `expLM P f = ∫ f ∂P` for integrable `f`. -/
theorem expLM_apply {P : Measure Ω} {f : Ω → ℝ} (hf : Integrable f P) :
    expLM P f = ∫ ω, f ω ∂P := by
  have h := (LinearMap.exists_extend (intLin P)).choose_spec
  have h2 := LinearMap.ext_iff.mp h ⟨f, hf⟩
  simpa [expLM, intLin] using h2

end Extension

/-! ## The product law, and complete degeneracy at one coordinate

`Ω := S → V` has one coordinate per site, with probability law `μ s` at site `s`, and
`P := Measure.pi μ`. -/

section Setup

variable {S V : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace V]

/-- `f` is completely degenerate at site `s` if integrating `f` over the latent at `s`, with every
other latent held fixed, gives zero almost surely. This is Regime 2(b) at the proper subset
`e \ {s}` and, at a private site, Regime 2(c)'s `E[ε_o ∣ 𝒟] = 0`. -/
def IntZeroAt (μ : S → Measure V) (s : S) (f : (S → V) → ℝ) : Prop :=
  ∀ᵐ ω ∂(Measure.pi μ), ∫ v, f (Function.update ω s v) ∂(μ s) = 0

/-- A probability law has a point in its space. -/
theorem nonempty_of_law (ν : Measure V) [IsProbabilityMeasure ν] : Nonempty V := by
  have h : ν Set.univ ≠ 0 := by
    rw [measure_univ]; exact one_ne_zero
  exact ⟨(nonempty_of_measure_ne_zero h).some⟩

end Setup

/-! ## The two probabilistic facts

Both come from the factorization of `Measure.pi μ` across a set of coordinates and its complement
(`measurePreserving_piEquivPiSubtypeProd`). The transport lemmas take the predicate `p` as a
variable and are specialized inside the two facts, since `{x // x = s₀}` has two
`Fintype` instances that are not syntactically equal. -/

section ProdLaw

variable {S V : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace V]
variable {μ : S → Measure V} [∀ s, IsProbabilityMeasure (μ s)]

/-- `Ω` splits along a set of coordinates and its complement. -/
def splitE (p : S → Prop) [DecidablePred p] :
    (S → V) ≃ᵐ (({x // p x}) → V) × (({x // ¬ p x}) → V) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : S => V) p

omit [Fintype S] [DecidableEq S] in
theorem splitE_symm_apply (p : S → Prop) [DecidablePred p]
    (z : (({x // p x}) → V) × (({x // ¬ p x}) → V)) (x : S) :
    (splitE p).symm z x = if h : p x then z.1 ⟨x, h⟩ else z.2 ⟨x, h⟩ := rfl

omit [DecidableEq S] in
theorem splitE_measurePreserving (μ : S → Measure V) [∀ s, IsProbabilityMeasure (μ s)]
    (p : S → Prop) [DecidablePred p] :
    MeasurePreserving (splitE (V := V) p) (Measure.pi μ)
      ((Measure.pi fun i : {x // p x} => μ ↑i).prod
        (Measure.pi fun i : {x // ¬ p x} => μ ↑i)) :=
  measurePreserving_piEquivPiSubtypeProd μ p

omit [DecidableEq S] in
/-- The change of variables along a measurable equivalence, with no integrability side
condition. -/
theorem integral_eq_integral_split (p : S → Prop) [DecidablePred p] (F : (S → V) → ℝ) :
    ∫ ω, F ω ∂(Measure.pi μ)
      = ∫ z, F ((splitE p).symm z)
          ∂((Measure.pi fun i : {x // p x} => μ ↑i).prod
            (Measure.pi fun i : {x // ¬ p x} => μ ↑i)) :=
  ((MeasurePreserving.symm (splitE (V := V) p) (splitE_measurePreserving μ p)).integral_comp
    (splitE (V := V) p).symm.measurableEmbedding F).symm

omit [DecidableEq S] in
/-- Fubini on the split, with the `p`-block innermost. -/
theorem integral_eq_integral_split_symm (p : S → Prop) [DecidablePred p] (F : (S → V) → ℝ)
    (hF : Integrable F (Measure.pi μ)) :
    ∫ ω, F ω ∂(Measure.pi μ)
      = ∫ b, ∫ a, F ((splitE p).symm (a, b))
            ∂(Measure.pi fun i : {x // p x} => μ ↑i)
          ∂(Measure.pi fun i : {x // ¬ p x} => μ ↑i) := by
  have hsym := MeasurePreserving.symm (splitE (V := V) p) (splitE_measurePreserving μ p)
  have hint := (hsym.integrable_comp hF.aestronglyMeasurable).mpr hF
  rw [integral_eq_integral_split p F]
  exact integral_prod_symm _ hint

omit [DecidableEq S] [∀ s, IsProbabilityMeasure (μ s)] in
/-- A one-element block is the site itself. -/
theorem integral_piUnique (p : S → Prop) [DecidablePred p] [Unique {x // p x}] (H : V → ℝ) :
    ∫ a : {x // p x} → V, H (a default) ∂(Measure.pi fun i : {x // p x} => μ ↑i)
      = ∫ v, H v ∂(μ ↑(default : {x // p x})) :=
  (measurePreserving_piUnique fun i : {x // p x} => μ ↑i).integral_comp
    (MeasurableEquiv.piUnique fun _ : {x // p x} => V).measurableEmbedding H

/-- Property (i). If `f` integrates to zero over the latent at site `s₀` (almost surely in the
other latents), `g` does not depend on that site, and `f * g` is integrable, then
`E[fg] = 0`. -/
theorem integral_mul_eq_zero_of_intZeroAt {s₀ : S} {f g : (S → V) → ℝ}
    (hfg : Integrable (f * g) (Measure.pi μ))
    (hf : IntZeroAt μ s₀ f) (hg : FreeAt s₀ g) :
    ∫ ω, (f * g) ω ∂(Measure.pi μ) = 0 := by
  let huniq : Unique {x : S // x = s₀} := ⟨⟨⟨s₀, rfl⟩⟩, fun y => Subtype.ext y.2⟩
  obtain ⟨v₀⟩ := nonempty_of_law (μ s₀)
  have hd : ((default : {x // x = s₀}) : S) = s₀ := (default : {x // x = s₀}).2
  have hsym := MeasurePreserving.symm (splitE (V := V) fun x => x = s₀)
    (splitE_measurePreserving (V := V) μ fun x => x = s₀)
  -- every point of the fibre over `b` is the base point updated at `s₀`
  have hupd : ∀ (a : {x // x = s₀} → V) (b : {x // ¬ (x = s₀)} → V),
      (splitE fun x => x = s₀).symm (a, b)
        = Function.update ((splitE fun x => x = s₀).symm (fun _ => v₀, b)) s₀ (a default) := by
    intro a b
    funext x
    by_cases hx : x = s₀
    · subst hx
      rw [Function.update_self, splitE_symm_apply]
      simp
      exact congrArg a (Subsingleton.elim _ _)
    · rw [Function.update_of_ne hx, splitE_symm_apply, splitE_symm_apply]
      simp [hx]
  -- the inner integral is a function of `b` alone; transport the a.e. degeneracy
  have hkey : ∀ (a : {x // x = s₀} → V) (b : {x // ¬ (x = s₀)} → V) (v : V),
      Function.update ((splitE fun x => x = s₀).symm (a, b)) s₀ v
        = Function.update ((splitE fun x => x = s₀).symm (fun _ => v₀, b)) s₀ v := by
    intro a b v
    rw [hupd a b, Function.update_idem]
  have hae : ∀ᵐ b ∂(Measure.pi fun i : {x // ¬ (x = s₀)} => μ ↑i),
      ∫ v, f (Function.update ((splitE fun x => x = s₀).symm (fun _ => v₀, b)) s₀ v) ∂(μ s₀)
        = 0 := by
    obtain ⟨a, ha⟩ := (Measure.ae_ae_of_ae_prod (hsym.quasiMeasurePreserving.ae hf)).exists
    refine ha.mono fun b hb => ?_
    rw [← hb]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v => by simp only [hkey a b v])
  rw [integral_eq_integral_split_symm (fun x => x = s₀) (f * g) hfg]
  refine integral_eq_zero_of_ae (hae.mono fun b hb => ?_)
  set ω₀ : S → V := (splitE fun x => x = s₀).symm (fun _ => v₀, b) with hω₀
  have hgc : ∀ a : {x // x = s₀} → V,
      g ((splitE fun x => x = s₀).symm (a, b)) = g ω₀ := fun a => by
    rw [hupd a b]; exact hg ω₀ _
  have hrw : ∀ a : {x // x = s₀} → V,
      (f * g) ((splitE fun x => x = s₀).symm (a, b))
        = f (Function.update ω₀ s₀ (a default)) * g ω₀ := by
    intro a
    simp only [Pi.mul_apply]
    rw [hgc a, hupd a b]
  simp only [hrw]
  rw [integral_mul_const,
    integral_piUnique (fun x => x = s₀) fun v => f (Function.update ω₀ s₀ v), hd, hb, zero_mul]
  rfl

/-- Property (ii). Functions of disjoint sets of sites are independent, so
`E[fg] = E[f] E[g]`. No integrability hypothesis is needed, since `integral_prod_mul` requires
none. -/
theorem integral_mul_eq_mul_of_disjoint {T T' : Finset S} (hTT : ∀ s ∈ T', s ∉ T)
    {f g : (S → V) → ℝ} (hf : DependsOn T f) (hg : DependsOn T' g) :
    ∫ ω, (f * g) ω ∂(Measure.pi μ)
      = (∫ ω, f ω ∂(Measure.pi μ)) * (∫ ω, g ω ∂(Measure.pi μ)) := by
  classical
  obtain ⟨a₀⟩ := nonempty_of_law (Measure.pi fun i : {x // x ∈ T} => μ ↑i)
  obtain ⟨b₀⟩ := nonempty_of_law (Measure.pi fun i : {x // ¬ (x ∈ T)} => μ ↑i)
  set F : ({x // x ∈ T} → V) → ℝ := fun a => f ((splitE fun x => x ∈ T).symm (a, b₀)) with hF
  set G : ({x // ¬ (x ∈ T)} → V) → ℝ := fun b => g ((splitE fun x => x ∈ T).symm (a₀, b))
    with hG
  have hfz : ∀ z : (({x // x ∈ T}) → V) × (({x // ¬ (x ∈ T)}) → V),
      f ((splitE fun x => x ∈ T).symm z) = F z.1 := by
    intro z
    refine hf _ _ fun s hs => ?_
    rw [splitE_symm_apply, splitE_symm_apply]
    simp [hs]
  have hgz : ∀ z : (({x // x ∈ T}) → V) × (({x // ¬ (x ∈ T)}) → V),
      g ((splitE fun x => x ∈ T).symm z) = G z.2 := by
    intro z
    refine hg _ _ fun s hs => ?_
    have hps : ¬ (s ∈ T) := hTT s hs
    rw [splitE_symm_apply, splitE_symm_apply]
    simp [hps]
  have hz1 : ∀ z : (({x // x ∈ T}) → V) × (({x // ¬ (x ∈ T)}) → V),
      f ((splitE fun x => x ∈ T).symm z)
        = F z.1 * (fun _ : ({x // ¬ (x ∈ T)}) → V => (1 : ℝ)) z.2 := by
    intro z; rw [hfz z]; ring
  have hz2 : ∀ z : (({x // x ∈ T}) → V) × (({x // ¬ (x ∈ T)}) → V),
      g ((splitE fun x => x ∈ T).symm z)
        = (fun _ : ({x // x ∈ T}) → V => (1 : ℝ)) z.1 * G z.2 := by
    intro z; rw [hgz z]; ring
  have hz3 : ∀ z : (({x // x ∈ T}) → V) × (({x // ¬ (x ∈ T)}) → V),
      (f * g) ((splitE fun x => x ∈ T).symm z) = F z.1 * G z.2 := by
    intro z; rw [Pi.mul_apply, hfz z, hgz z]
  rw [integral_eq_integral_split (fun x => x ∈ T) (f * g),
    integral_eq_integral_split (fun x => x ∈ T) f,
    integral_eq_integral_split (fun x => x ∈ T) g]
  simp only [hz1, hz2, hz3]
  rw [integral_prod_mul F G, integral_prod_mul F fun _ => (1 : ℝ),
    integral_prod_mul (fun _ => (1 : ℝ)) G]
  simp

end ProdLaw


/-! ## Fourth moments and integrability

The Young inequalities `|abcd| ≤ (a⁴+b⁴+c⁴+d⁴)/4` and `|ab| ≤ (a⁴+b⁴+2)/4` dominate each product
formed below by an integrable function. -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A variable with a finite fourth moment (implied by `MemLp f 4 P`). -/
structure FourthMom (P : Measure Ω) (f : Ω → ℝ) : Prop where
  meas : AEStronglyMeasurable f P
  int4 : Integrable (fun ω => f ω ^ 4) P

/-- The dominating function of the four-factor Young bound. -/
theorem integrable_sum_pow_four {a b c d : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b)
    (hc : FourthMom P c) (hd : FourthMom P d) :
    Integrable (fun ω => (a ω ^ 4 + b ω ^ 4 + c ω ^ 4 + d ω ^ 4) / 4) P := by
  have h1 : Integrable (fun ω => a ω ^ 4 + b ω ^ 4) P := ha.int4.add hb.int4
  have h2 : Integrable (fun ω => a ω ^ 4 + b ω ^ 4 + c ω ^ 4) P := h1.add hc.int4
  exact (h2.add hd.int4).div_const 4

/-- The integral of the four-factor dominating function, as a sum of four integrals. -/
theorem integral_sum_pow_four {a b c d : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b)
    (hc : FourthMom P c) (hd : FourthMom P d) :
    ∫ ω, (a ω ^ 4 + b ω ^ 4 + c ω ^ 4 + d ω ^ 4) / 4 ∂P
      = ((∫ ω, a ω ^ 4 ∂P) + (∫ ω, b ω ^ 4 ∂P) + (∫ ω, c ω ^ 4 ∂P) + (∫ ω, d ω ^ 4 ∂P)) / 4 := by
  have h1 : Integrable (fun ω => a ω ^ 4 + b ω ^ 4) P := ha.int4.add hb.int4
  have h2 : Integrable (fun ω => a ω ^ 4 + b ω ^ 4 + c ω ^ 4) P := h1.add hc.int4
  rw [integral_div, integral_add h2 hd.int4, integral_add h1 hc.int4,
    integral_add ha.int4 hb.int4]

/-- By Young's inequality, a product of four variables with finite fourth moments is
integrable. -/
theorem FourthMom.integrable_mul4 {a b c d : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b)
    (hc : FourthMom P c) (hd : FourthMom P d) : Integrable (a * b * c * d) P := by
  refine Integrable.mono' (integrable_sum_pow_four ha hb hc hd)
    (((ha.meas.mul hb.meas).mul hc.meas).mul hd.meas)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.mul_apply, Real.norm_eq_abs]
  exact abs_mul_four_le (a ω) (b ω) (c ω) (d ω)

/-- `FourthMom` is closed under addition: `(x+y)⁴ ≤ 8(x⁴+y⁴)` pointwise. -/
theorem FourthMom.add {a b : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b) :
    FourthMom P (a + b) := by
  refine ⟨ha.meas.add hb.meas, ?_⟩
  have hdom : Integrable (fun ω => 8 * (a ω ^ 4 + b ω ^ 4)) P := (ha.int4.add hb.int4).const_mul 8
  have hgoal : Integrable (fun ω => (a ω + b ω) ^ 4) P := by
    refine Integrable.mono' hdom ((ha.meas.add hb.meas).pow 4)
      (Filter.Eventually.of_forall fun ω => ?_)
    have hpt : (a ω + b ω) ^ 4 ≤ 8 * (a ω ^ 4 + b ω ^ 4) := by
      nlinarith [sq_nonneg (a ω - b ω), sq_nonneg (a ω + b ω), sq_nonneg (a ω ^ 2 - b ω ^ 2),
        sq_nonneg (a ω ^ 2 + b ω ^ 2), sq_nonneg (a ω * b ω), sq_nonneg (a ω), sq_nonneg (b ω)]
    have hnn : (0 : ℝ) ≤ (a ω + b ω) ^ 4 := by positivity
    rw [Real.norm_of_nonneg hnn]
    exact hpt
  exact hgoal

theorem fourthMom_zero : FourthMom P (0 : Ω → ℝ) :=
  ⟨aestronglyMeasurable_const, by simp⟩

/-- A finite sum of variables with finite fourth moments has one, as for
`ζ_o = ∑_γ ξ^γ_o`. -/
theorem FourthMom.finsetSum {ι : Type*} {A : Finset ι} {x : ι → Ω → ℝ}
    (h : ∀ i ∈ A, FourthMom P (x i)) : FourthMom P (∑ i ∈ A, x i) := by
  classical
  induction A using Finset.induction with
  | empty => simpa using fourthMom_zero
  | insert i A hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i A)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- `|∫ f| ≤ c` from a pointwise two-sided bound by a function whose integral is at most `c`. -/
theorem abs_integral_le_of_bound {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (h : ∀ ω, |f ω| ≤ g ω) {c : ℝ} (hc : ∫ ω, g ω ∂P ≤ c) : |∫ ω, f ω ∂P| ≤ c := by
  have h1 : |∫ ω, f ω ∂P| ≤ ∫ ω, |f ω| ∂P := abs_integral_le_integral_abs
  have h2 : ∫ ω, |f ω| ∂P ≤ ∫ ω, g ω ∂P := integral_mono hf.abs hg h
  linarith

/-- The four-factor moment bound. -/
theorem abs_integral_mul4_le {a b c d : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b)
    (hc : FourthMom P c) (hd : FourthMom P d) {C : ℝ}
    (hA : ∫ ω, a ω ^ 4 ∂P ≤ C) (hB : ∫ ω, b ω ^ 4 ∂P ≤ C) (hC : ∫ ω, c ω ^ 4 ∂P ≤ C)
    (hD : ∫ ω, d ω ^ 4 ∂P ≤ C) : |∫ ω, (a * b * c * d) ω ∂P| ≤ C := by
  refine abs_integral_le_of_bound (ha.integrable_mul4 hb hc hd)
    (integrable_sum_pow_four ha hb hc hd) (fun ω => ?_) ?_
  · simp only [Pi.mul_apply]
    exact abs_mul_four_le (a ω) (b ω) (c ω) (d ω)
  · rw [integral_sum_pow_four ha hb hc hd]
    linarith

variable [IsProbabilityMeasure P]

/-- The dominating function of the two-factor Young bound. -/
theorem integrable_sum_pow_four_two {a b : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b) :
    Integrable (fun ω => (a ω ^ 4 + b ω ^ 4 + 2) / 4) P := by
  have h1 : Integrable (fun ω => a ω ^ 4 + b ω ^ 4) P := ha.int4.add hb.int4
  exact (h1.add (integrable_const (2 : ℝ))).div_const 4

theorem integral_sum_pow_four_two {a b : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b) :
    ∫ ω, (a ω ^ 4 + b ω ^ 4 + 2) / 4 ∂P
      = ((∫ ω, a ω ^ 4 ∂P) + (∫ ω, b ω ^ 4 ∂P) + 2) / 4 := by
  have h1 : Integrable (fun ω => a ω ^ 4 + b ω ^ 4) P := ha.int4.add hb.int4
  rw [integral_div, integral_add h1 (integrable_const (2 : ℝ)),
    integral_add ha.int4 hb.int4, integral_const]
  simp

/-- By Young's inequality, a product of two variables with finite fourth moments is integrable.
The constant `2` is integrable because `P` is a probability measure. -/
theorem FourthMom.integrable_mul2 {a b : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b) :
    Integrable (a * b) P := by
  refine Integrable.mono' (integrable_sum_pow_four_two ha hb) (ha.meas.mul hb.meas)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.mul_apply, Real.norm_eq_abs]
  exact abs_mul_two_le (a ω) (b ω)

/-- A variable with a finite fourth moment is itself integrable. -/
theorem FourthMom.integrable {a : Ω → ℝ} (ha : FourthMom P a) : Integrable a P := by
  have hone : FourthMom P (fun _ : Ω => (1 : ℝ)) :=
    ⟨aestronglyMeasurable_const, by simp⟩
  refine Integrable.mono' (integrable_sum_pow_four_two ha hone) ha.meas
    (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := abs_mul_two_le (a ω) 1
  rw [mul_one] at h1
  simp only [Real.norm_eq_abs]
  have h2 : (1 : ℝ) ^ 4 = 1 := by norm_num
  linarith

/-- The two-factor moment bound. -/
theorem abs_integral_mul2_le {a b : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b) {C : ℝ}
    (hA : ∫ ω, a ω ^ 4 ∂P ≤ C) (hB : ∫ ω, b ω ^ 4 ∂P ≤ C) :
    |∫ ω, (a * b) ω ∂P| ≤ (C + 1) / 2 := by
  refine abs_integral_le_of_bound (ha.integrable_mul2 hb) (integrable_sum_pow_four_two ha hb)
    (fun ω => ?_) ?_
  · simp only [Pi.mul_apply]
    exact abs_mul_two_le (a ω) (b ω)
  · rw [integral_sum_pow_four_two ha hb]
    linarith

end Moments


/-! ## The two properties at the level of `cum₄`

In every proof `expLM` is eliminated by `expLM_apply`, so nothing depends on the choice of
extension. -/

section Cumulants

variable {S V : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace V]
variable {μ : S → Measure V} [∀ s, IsProbabilityMeasure (μ s)]

theorem expLM_mul_eq_zero_of_intZeroAt {s₀ : S} {f g : (S → V) → ℝ}
    (hfg : Integrable (f * g) (Measure.pi μ)) (hf : IntZeroAt μ s₀ f) (hg : FreeAt s₀ g) :
    expLM (Measure.pi μ) (f * g) = 0 := by
  rw [expLM_apply hfg]
  exact integral_mul_eq_zero_of_intZeroAt hfg hf hg

/-- A variable that integrates to zero over one of its coordinates has mean zero. -/
theorem expLM_eq_zero_of_intZeroAt {s₀ : S} {f : (S → V) → ℝ}
    (hfi : Integrable f (Measure.pi μ)) (hf : IntZeroAt μ s₀ f) :
    expLM (Measure.pi μ) f = 0 := by
  have hass : f = f * 1 := by rw [mul_one]
  rw [hass]
  exact expLM_mul_eq_zero_of_intZeroAt (by rwa [mul_one]) hf (freeAt_one s₀)

theorem expLM_mul_eq_mul_of_disjoint {T T' : Finset S} (hTT : ∀ s ∈ T', s ∉ T)
    {f g : (S → V) → ℝ} (hfg : Integrable (f * g) (Measure.pi μ))
    (hfi : Integrable f (Measure.pi μ)) (hgi : Integrable g (Measure.pi μ))
    (hf : DependsOn T f) (hg : DependsOn T' g) :
    expLM (Measure.pi μ) (f * g) = expLM (Measure.pi μ) f * expLM (Measure.pi μ) g := by
  rw [expLM_apply hfg, expLM_apply hfi, expLM_apply hgi]
  exact integral_mul_eq_mul_of_disjoint hTT hf hg

/-- Property (i) for `cum₄`. If `a` integrates to zero over the latent at site `s₀` and `b`, `c`,
`d` do not depend on that site, then `cum₄(a, b, c, d) = 0`, since every term of the moment formula
contains `a`. -/
theorem cum4_eq_zero_of_intZeroAt {s₀ : S} {a b c d : (S → V) → ℝ}
    (ha : FourthMom (Measure.pi μ) a) (hb : FourthMom (Measure.pi μ) b)
    (hc : FourthMom (Measure.pi μ) c) (hd : FourthMom (Measure.pi μ) d)
    (hz : IntZeroAt μ s₀ a) (hfb : FreeAt s₀ b) (hfc : FreeAt s₀ c) (hfd : FreeAt s₀ d) :
    cum4 (expLM (Measure.pi μ)) a b c d = 0 := by
  refine cum4_eq_zero_of_moments_vanish _ ?_ ?_ ?_ ?_
  · have hass : a * b * c * d = a * (b * c * d) := by ring
    rw [hass]
    refine expLM_mul_eq_zero_of_intZeroAt ?_ hz (freeAt_mul (freeAt_mul hfb hfc) hfd)
    rw [← hass]
    exact ha.integrable_mul4 hb hc hd
  · exact expLM_mul_eq_zero_of_intZeroAt (ha.integrable_mul2 hb) hz hfb
  · exact expLM_mul_eq_zero_of_intZeroAt (ha.integrable_mul2 hc) hz hfc
  · exact expLM_mul_eq_zero_of_intZeroAt (ha.integrable_mul2 hd) hz hfd

/-- Property (i) for `cum₄`, with the degenerate argument in any of the four positions. -/
theorem cum4_eq_zero_of_unshared {s₀ : S} {X : Fin 4 → (S → V) → ℝ}
    (hmom : ∀ i, FourthMom (Measure.pi μ) (X i)) {i₀ : Fin 4}
    (hz : IntZeroAt μ s₀ (X i₀)) (hf : ∀ i, i ≠ i₀ → FreeAt s₀ (X i)) :
    cum4 (expLM (Measure.pi μ)) (X 0) (X 1) (X 2) (X 3) = 0 := by
  fin_cases i₀
  · exact cum4_eq_zero_of_intZeroAt (hmom 0) (hmom 1) (hmom 2) (hmom 3) hz
      (hf 1 (by decide)) (hf 2 (by decide)) (hf 3 (by decide))
  · rw [cum4_swap_one_two]
    exact cum4_eq_zero_of_intZeroAt (hmom 1) (hmom 0) (hmom 2) (hmom 3) hz
      (hf 0 (by decide)) (hf 2 (by decide)) (hf 3 (by decide))
  · rw [cum4_swap_two_three, cum4_swap_one_two]
    exact cum4_eq_zero_of_intZeroAt (hmom 2) (hmom 0) (hmom 1) (hmom 3) hz
      (hf 0 (by decide)) (hf 1 (by decide)) (hf 3 (by decide))
  · rw [cum4_swap_three_four, cum4_swap_two_three, cum4_swap_one_two]
    exact cum4_eq_zero_of_intZeroAt (hmom 3) (hmom 0) (hmom 1) (hmom 2) hz
      (hf 0 (by decide)) (hf 1 (by decide)) (hf 2 (by decide))

/-- Property (ii) for `cum₄`. If `a`, `b` depend on `T₁`, `c`, `d` depend on the disjoint set `T₂`,
and `E[a] = E[b] = 0`, then `cum₄(a, b, c, d) = 0`, since `E[abcd] = E[ab] E[cd]` and every cross
pair-moment such as `E[ac] = E[a] E[c]` vanishes. -/
theorem cum4_eq_zero_of_disjoint {T₁ T₂ : Finset S} (hdisj : ∀ s ∈ T₂, s ∉ T₁)
    {a b c d : (S → V) → ℝ}
    (hma : FourthMom (Measure.pi μ) a) (hmb : FourthMom (Measure.pi μ) b)
    (hmc : FourthMom (Measure.pi μ) c) (hmd : FourthMom (Measure.pi μ) d)
    (ha : DependsOn T₁ a) (hb : DependsOn T₁ b) (hc : DependsOn T₂ c) (hd : DependsOn T₂ d)
    (ha0 : expLM (Measure.pi μ) a = 0) (hb0 : expLM (Measure.pi μ) b = 0) :
    cum4 (expLM (Measure.pi μ)) a b c d = 0 := by
  refine cum4_eq_zero_of_indep_pair _ ?_ ?_ ?_ ?_ ?_ ha0 hb0
  · have hass : a * b * c * d = (a * b) * (c * d) := by ring
    rw [hass]
    refine expLM_mul_eq_mul_of_disjoint hdisj ?_ (hma.integrable_mul2 hmb)
      (hmc.integrable_mul2 hmd) (dependsOn_mul ha hb) (dependsOn_mul hc hd)
    rw [← hass]
    exact hma.integrable_mul4 hmb hmc hmd
  · exact expLM_mul_eq_mul_of_disjoint hdisj (hma.integrable_mul2 hmc) hma.integrable
      hmc.integrable ha hc
  · exact expLM_mul_eq_mul_of_disjoint hdisj (hma.integrable_mul2 hmd) hma.integrable
      hmd.integrable ha hd
  · exact expLM_mul_eq_mul_of_disjoint hdisj (hmb.integrable_mul2 hmc) hmb.integrable
      hmc.integrable hb hc
  · exact expLM_mul_eq_mul_of_disjoint hdisj (hmb.integrable_mul2 hmd) hmb.integrable
      hmd.integrable hb hd

end Cumulants

/-! ## The support hypothesis `hsupp` -/

section Supp

variable {D L O Γ₀ V : Type*}
  [Fintype D] [DecidableEq D] [Fintype L] [DecidableEq L] [Fintype O] [DecidableEq O]
  [MeasurableSpace V]
  {idio : Γ₀ → Prop} [DecidablePred idio] {idx : D → O → L} {lev : Γ₀ → Finset D}
  {μ : Site D L O → Measure V} [∀ s, IsProbabilityMeasure (μ s)]

/-- The support hypothesis `hsupp` of `var_quadForm_le_levels` in this model. -/
theorem assignCum_eq_zero_of_not_supported
    (hidio : ∀ γ : Γ₀, idio γ → lev γ = Finset.univ)
    {Lv : Finset Γ₀} (he : ∀ γ ∈ Lv, 2 ≤ (lev γ).card)
    {xi : Γ₀ → O → (Site D L O → V) → ℝ}
    (hmom : ∀ γ ∈ Lv, ∀ o, FourthMom (Measure.pi μ) (xi γ o))
    (hdep : ∀ γ ∈ Lv, ∀ o, DependsOn (siteSet idio idx lev γ o) (xi γ o))
    (hdeg : ∀ γ ∈ Lv, ∀ o, ∀ s ∈ siteSet idio idx lev γ o, IntZeroAt μ s (xi γ o))
    {g : Γ₀ × Γ₀ × Γ₀ × Γ₀} (hg : g ∈ levelQuadruples Lv) (o₁ o₂ o₃ o₄ : O)
    (hns : ¬ (Admissible idx (assignLevels lev g) (quad o₁ o₂ o₃ o₄)
        ∧ QuadformE2.Linked idx (assignLevels lev g) (quad o₁ o₂ o₃ o₄))) :
    assignCum (expLM (Measure.pi μ)) xi g o₁ o₂ o₃ o₄ = 0 := by
  classical
  rw [mem_levelQuadruples] at hg
  have hγmem : ∀ i : Fin 4, quad g.1 g.2.1 g.2.2.1 g.2.2.2 i ∈ Lv := by
    intro i
    fin_cases i
    · simpa using hg.1
    · simpa using hg.2.1
    · simpa using hg.2.2.1
    · simpa using hg.2.2.2
  set γf : Fin 4 → Γ₀ := quad g.1 g.2.1 g.2.2.1 g.2.2.2 with hγf
  set of : Fin 4 → O := quad o₁ o₂ o₃ o₄ with hof
  set X : Fin 4 → (Site D L O → V) → ℝ := fun i => xi (γf i) (of i) with hX
  have hmomX : ∀ i, FourthMom (Measure.pi μ) (X i) := fun i =>
    hmom (γf i) (hγmem i) (of i)
  have hcum : assignCum (expLM (Measure.pi μ)) xi g o₁ o₂ o₃ o₄
      = cum4 (expLM (Measure.pi μ)) (X 0) (X 1) (X 2) (X 3) := by
    simp [assignCum, hX, hγf, hof]
  rw [hcum]
  rw [not_and_or] at hns
  rcases hns with hna | hnl
  · rw [Admissible] at hna
    push Not at hna
    obtain ⟨i₀, k₀, hk₀, hno⟩ := hna
    have hk₀' : k₀ ∈ lev (γf i₀) := hk₀
    refine cum4_eq_zero_of_unshared (s₀ := sitemap idio idx (γf i₀) k₀ (of i₀)) hmomX
      (hdeg (γf i₀) (hγmem i₀) (of i₀) _ (mem_siteSet hk₀')) ?_
    intro i hi
    refine freeAt_of_dependsOn ?_ (hdep (γf i) (hγmem i) (of i))
    intro hcon
    obtain ⟨h1, h2⟩ := mem_lev_and_idx_eq_of_mem_siteSet hidio hk₀' hcon
    exact hno i hi h1 h2
  · have h20 : ¬ QuadformE2.SharesSite idx (assignLevels lev g) of 2 0 :=
      fun h => hnl (Or.inl h)
    have h21 : ¬ QuadformE2.SharesSite idx (assignLevels lev g) of 2 1 :=
      fun h => hnl (Or.inr (Or.inl h))
    have h30 : ¬ QuadformE2.SharesSite idx (assignLevels lev g) of 3 0 :=
      fun h => hnl (Or.inr (Or.inr (Or.inl h)))
    have h31 : ¬ QuadformE2.SharesSite idx (assignLevels lev g) of 3 1 :=
      fun h => hnl (Or.inr (Or.inr (Or.inr h)))
    have hdisj : ∀ s ∈ siteSet idio idx lev (γf 2) (of 2) ∪ siteSet idio idx lev (γf 3) (of 3),
        s ∉ siteSet idio idx lev (γf 0) (of 0) ∪ siteSet idio idx lev (γf 1) (of 1) := by
      intro s hs hs'
      rw [Finset.mem_union] at hs hs'
      rcases hs with h2 | h3 <;> rcases hs' with h0 | h1
      · exact h20 (sharesSite_of_mem_both hidio h2 h0)
      · exact h21 (sharesSite_of_mem_both hidio h2 h1)
      · exact h30 (sharesSite_of_mem_both hidio h3 h0)
      · exact h31 (sharesSite_of_mem_both hidio h3 h1)
    have hmean : ∀ i : Fin 4, expLM (Measure.pi μ) (X i) = 0 := by
      intro i
      obtain ⟨s, hs⟩ : (siteSet idio idx lev (γf i) (of i)).Nonempty :=
        siteSet_nonempty (of i) (Finset.card_pos.mp (by have := he _ (hγmem i); omega))
      exact expLM_eq_zero_of_intZeroAt (hmomX i).integrable
        (hdeg (γf i) (hγmem i) (of i) s hs)
    exact cum4_eq_zero_of_disjoint hdisj (hmomX 0) (hmomX 1) (hmomX 2) (hmomX 3)
      (dependsOn_mono Finset.subset_union_left (hdep (γf 0) (hγmem 0) (of 0)))
      (dependsOn_mono Finset.subset_union_right (hdep (γf 1) (hγmem 1) (of 1)))
      (dependsOn_mono Finset.subset_union_left (hdep (γf 2) (hγmem 2) (of 2)))
      (dependsOn_mono Finset.subset_union_right (hdep (γf 3) (hγmem 3) (of 3)))
      (hmean 0) (hmean 1)

end Supp


/-! ## The bound `hbdd` on the cumulant of an assignment

The cumulant of an assignment is bounded by `K = C + 3((C+1)/2)²`, by Young's inequality. -/

section Bound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `hbdd` for `cum₄`, with the constant `K` explicit. -/
theorem abs_cum4_le_cont {a b c d : Ω → ℝ} (ha : FourthMom P a) (hb : FourthMom P b)
    (hc : FourthMom P c) (hd : FourthMom P d) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∫ ω, a ω ^ 4 ∂P ≤ C) (hB : ∫ ω, b ω ^ 4 ∂P ≤ C) (hCc : ∫ ω, c ω ^ 4 ∂P ≤ C)
    (hD : ∫ ω, d ω ^ 4 ∂P ≤ C) :
    |cum4 (expLM P) a b c d| ≤ C + 3 * ((C + 1) / 2) ^ 2 := by
  have hk : (0 : ℝ) ≤ (C + 1) / 2 := by linarith
  have hprod : ∀ x y : ℝ, |x| ≤ (C + 1) / 2 → |y| ≤ (C + 1) / 2 →
      |x * y| ≤ ((C + 1) / 2) ^ 2 := by
    intro x y hx hy
    rw [abs_mul, sq]
    exact mul_le_mul hx hy (abs_nonneg _) hk
  rw [cum4, expLM_apply (ha.integrable_mul4 hb hc hd), expLM_apply (ha.integrable_mul2 hb),
    expLM_apply (hc.integrable_mul2 hd), expLM_apply (ha.integrable_mul2 hc),
    expLM_apply (hb.integrable_mul2 hd), expLM_apply (ha.integrable_mul2 hd),
    expLM_apply (hb.integrable_mul2 hc)]
  have h4 := abs_le.mp (abs_integral_mul4_le ha hb hc hd hA hB hCc hD)
  have h1 := abs_le.mp (hprod _ _ (abs_integral_mul2_le ha hb hA hB)
    (abs_integral_mul2_le hc hd hCc hD))
  have h2 := abs_le.mp (hprod _ _ (abs_integral_mul2_le ha hc hA hCc)
    (abs_integral_mul2_le hb hd hB hD))
  have h3 := abs_le.mp (hprod _ _ (abs_integral_mul2_le ha hd hA hD)
    (abs_integral_mul2_le hb hc hB hCc))
  rw [abs_le]
  constructor <;> linarith [h4.1, h4.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end Bound

/-! ## Lemma SM.C.6 under Regime 2 with a continuum alphabet -/

section Assembled

variable {D L O Γ₀ V : Type*}
  [Fintype D] [DecidableEq D] [Fintype L] [DecidableEq L] [Fintype O] [DecidableEq O]
  [MeasurableSpace V]

/-- `ζ_o = ∑_{2≤|e|≤M} ξ^e_o + ε_o`, the level decomposition. -/
def levelSumC (Lv : Finset Γ₀) (xi : Γ₀ → O → (Site D L O → V) → ℝ) :
    O → (Site D L O → V) → ℝ := fun o => ∑ γ ∈ Lv, xi γ o

/-- `Ω'_{oo'} = E[ζ_oζ_{o'} ∣ 𝒟]`, computed in the model. -/
noncomputable def levelGramC (μ : Site D L O → Measure V) (Lv : Finset Γ₀)
    (xi : Γ₀ → O → (Site D L O → V) → ℝ) : Matrix O O ℝ :=
  Matrix.of fun o o' =>
    ∫ ω, levelSumC Lv xi o ω * levelSumC Lv xi o' ω ∂(Measure.pi μ)

omit [DecidableEq D] [DecidableEq L] [DecidableEq O] in
theorem levelGramC_isSymm (μ : Site D L O → Measure V) (Lv : Finset Γ₀)
    (xi : Γ₀ → O → (Site D L O → V) → ℝ) : (levelGramC μ Lv xi).IsSymm := by
  ext o o'
  simp only [Matrix.transpose_apply, levelGramC, Matrix.of_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

variable {μ : Site D L O → Measure V} [∀ s, IsProbabilityMeasure (μ s)]

omit [DecidableEq D] [DecidableEq L] [DecidableEq O]
  [∀ s, IsProbabilityMeasure (μ s)] in
/-- Each `ζ_o` inherits a fourth moment from the levels. -/
theorem fourthMom_levelSumC {Lv : Finset Γ₀} {xi : Γ₀ → O → (Site D L O → V) → ℝ}
    (hmem : ∀ γ ∈ Lv, ∀ o, FourthMom (Measure.pi μ) (xi γ o)) (o : O) :
    FourthMom (Measure.pi μ) (levelSumC Lv xi o) :=
  FourthMom.finsetSum fun γ hγ => hmem γ hγ o

omit [DecidableEq D] [DecidableEq L] [DecidableEq O] in
/-- `ζ'Wζ` is integrable. -/
theorem integrable_quadForm {Lv : Finset Γ₀} {xi : Γ₀ → O → (Site D L O → V) → ℝ}
    (hmem : ∀ γ ∈ Lv, ∀ o, FourthMom (Measure.pi μ) (xi γ o)) (W : Matrix O O ℝ) :
    Integrable (quadForm W (levelSumC Lv xi)) (Measure.pi μ) := by
  rw [quadForm]
  refine integrable_finsetSum' _ fun o _ => integrable_finsetSum' _ fun o' _ => ?_
  exact Integrable.smul (W o o')
    ((fourthMom_levelSumC hmem o).integrable_mul2 (fourthMom_levelSumC hmem o'))

omit [DecidableEq D] [DecidableEq L] [DecidableEq O]
  [∀ s, IsProbabilityMeasure (μ s)] in
/-- The square of `ζ'Wζ` is integrable. -/
theorem integrable_quadForm_sq {Lv : Finset Γ₀} {xi : Γ₀ → O → (Site D L O → V) → ℝ}
    (hmem : ∀ γ ∈ Lv, ∀ o, FourthMom (Measure.pi μ) (xi γ o)) (W : Matrix O O ℝ) :
    Integrable (quadForm W (levelSumC Lv xi) ^ 2) (Measure.pi μ) := by
  rw [quadForm_sq]
  refine integrable_finsetSum' _ fun o₁ _ => integrable_finsetSum' _ fun o₂ _ =>
    integrable_finsetSum' _ fun o₃ _ => integrable_finsetSum' _ fun o₄ _ => ?_
  exact Integrable.smul (W o₁ o₂ * W o₃ o₄)
    ((fourthMom_levelSumC hmem o₁).integrable_mul4 (fourthMom_levelSumC hmem o₂)
      (fourthMom_levelSumC hmem o₃) (fourthMom_levelSumC hmem o₄))

/-- **Lemma SM.C.6 under Regime 2, with a continuum latent alphabet.**

`Var(ζ'Wζ ∣ 𝒟) ≤ 2 tr(WΩ'WΩ') + C(M) G_max c_max ‖W‖_F²`, with `C(M) = (2^M)⁴ · 4M` and the
per-cumulant constant `K = C + 3((C+1)/2)²`, for latents with an arbitrary probability law at
each site. The hypothesis `hW` makes `W` symmetric; `hC`, `hmom` bound the fourth moments; `hmem` makes
each `ξ^γ_o` a.e.-measurable with a finite fourth moment; `hLv`, `he` describe the levels;
`hG`, `hc` bound the category and cell sizes; `hdep` is `ξ^e_o := h^{(e)}(U_{o⊙e})`; `hdeg` is
complete degeneracy; and `hidio` gives the symbol `ε` the full dimension set. -/
theorem var_quadForm_le_regime2_cont {idio : Γ₀ → Prop} [DecidablePred idio] (idx : D → O → L)
    (lev : Γ₀ → Finset D) (μ : Site D L O → Measure V) [∀ s, IsProbabilityMeasure (μ s)]
    {W : Matrix O O ℝ} (hW : W.IsSymm)
    (Lv : Finset Γ₀) (xi : Γ₀ → O → (Site D L O → V) → ℝ)
    {Gmax cmax : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hLv : Lv.card ≤ 2 ^ Fintype.card D)
    (he : ∀ γ ∈ Lv, 2 ≤ (lev γ).card)
    (hidio : ∀ γ : Γ₀, idio γ → lev γ = Finset.univ)
    (hG : ∀ (k : D) (o : O), (cellOf idx ({k} : Finset D) o).card ≤ Gmax)
    (hc : ∀ (A : Finset D) (o : O), 2 ≤ A.card → (cellOf idx A o).card ≤ cmax)
    (hmem : ∀ γ ∈ Lv, ∀ o, FourthMom (Measure.pi μ) (xi γ o))
    (hdep : ∀ γ ∈ Lv, ∀ o, DependsOn (siteSet idio idx lev γ o) (xi γ o))
    (hdeg : ∀ γ ∈ Lv, ∀ o, ∀ s ∈ siteSet idio idx lev γ o, IntZeroAt μ s (xi γ o))
    (hmom : ∀ γ ∈ Lv, ∀ o, ∫ ω, xi γ o ω ^ 4 ∂(Measure.pi μ) ≤ C) :
    (∫ ω, quadForm W (levelSumC Lv xi) ω ^ 2 ∂(Measure.pi μ))
        - (∫ ω, quadForm W (levelSumC Lv xi) ω ∂(Measure.pi μ)) ^ 2
      ≤ 2 * (W * levelGramC μ Lv xi * W * levelGramC μ Lv xi).trace
        + ((2 ^ Fintype.card D) ^ 4 : ℕ) * (C + 3 * ((C + 1) / 2) ^ 2)
            * (4 * Fintype.card D * Gmax * cmax : ℕ) * frobSq W := by
  have hmain := var_quadForm_le_levels (K := C + 3 * ((C + 1) / 2) ^ 2)
    (expLM (Measure.pi μ)) hW (levelGramC_isSymm μ Lv xi)
    (levelSumC Lv xi) ?_ Lv xi (fun _ => rfl) lev idx
    (by nlinarith [sq_nonneg ((C + 1) / 2)]) hLv he hG hc ?_ ?_
  · have h1 : expLM (Measure.pi μ) (quadForm W (levelSumC Lv xi) ^ 2)
        = ∫ ω, quadForm W (levelSumC Lv xi) ω ^ 2 ∂(Measure.pi μ) :=
      expLM_apply (integrable_quadForm_sq hmem W)
    have h2 : expLM (Measure.pi μ) (quadForm W (levelSumC Lv xi))
        = ∫ ω, quadForm W (levelSumC Lv xi) ω ∂(Measure.pi μ) :=
      expLM_apply (integrable_quadForm hmem W)
    rw [varQuad, h1, h2] at hmain
    exact hmain
  · intro o o'
    rw [levelGramC, Matrix.of_apply,
      expLM_apply ((fourthMom_levelSumC hmem o).integrable_mul2 (fourthMom_levelSumC hmem o'))]
    rfl
  · intro g hg o₁ o₂ o₃ o₄ hns
    exact assignCum_eq_zero_of_not_supported hidio he hmem hdep hdeg hg o₁ o₂ o₃ o₄ hns
  · intro g hg o₁ o₂ o₃ o₄
    rw [mem_levelQuadruples] at hg
    exact abs_cum4_le_cont (hmem _ hg.1 o₁) (hmem _ hg.2.1 o₂) (hmem _ hg.2.2.1 o₃)
      (hmem _ hg.2.2.2 o₄) hC (hmom _ hg.1 o₁) (hmom _ hg.2.1 o₂) (hmom _ hg.2.2.1 o₃)
      (hmom _ hg.2.2.2 o₄)

end Assembled


/-! ## An example with uniform latents

`regime2_cont_witness` applies `var_quadForm_le_regime2_cont` to a model with `M = 2`, one
category per dimension, one observation and every latent uniform on `[0,1]`. The kernel is
`ξ_o = σ(U^{(1)})σ(U^{(2)})` with `σ(u) = 1 - 2·1{u ≤ 1/2}`, and `ε_o = σ(U_o)`. In this model
`Var(ζ'Wζ ∣ 𝒟) = 4` and `tr(WΩ'WΩ') = 4`. -/

section Witness

open Multiway.QuadformE2Indep (witIdx witLev witIdio WSite witSite_kernel witSite_eps
  witSite_mem_false witSite_mem_true)

/-- The uniform law on `[0,1]`. -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance unif01_isProb : IsProbabilityMeasure unif01 := ⟨by
  rw [unif01, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num⟩

/-- The uniform law on `[0,1]` has no atoms. -/
theorem unif01_singleton (a : ℝ) : unif01 {a} = 0 := by
  rw [unif01, Measure.restrict_apply (measurableSet_singleton a)]
  exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)

/-- `σ(u) = -1` on `[0,1/2]` and `1` above. Under the uniform law it has mean zero and `σ² = 1`. -/
noncomputable def sgnU (u : ℝ) : ℝ := if u ≤ 1 / 2 then -1 else 1

theorem measurable_sgnU : Measurable sgnU :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem sgnU_mul_self (u : ℝ) : sgnU u * sgnU u = 1 := by
  unfold sgnU; split <;> norm_num

theorem sgnU_eq_sub_indicator (u : ℝ) :
    sgnU u = 1 - 2 * Set.indicator (Set.Iic (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) u := by
  unfold sgnU
  rw [Set.indicator_apply]
  simp only [Set.mem_Iic]
  split_ifs <;> norm_num

/-- `E[σ(U)] = 0` for `U` uniform on `[0,1]`. -/
theorem integral_sgnU : ∫ u, sgnU u ∂unif01 = 0 := by
  have hmeas : MeasurableSet (Set.Iic (1 / 2 : ℝ)) := measurableSet_Iic
  have hint : Integrable (Set.indicator (Set.Iic (1 / 2 : ℝ)) fun _ => (1 : ℝ)) unif01 :=
    (integrable_const (1 : ℝ)).indicator hmeas
  have hset : unif01 (Set.Iic (1 / 2 : ℝ)) = ENNReal.ofReal (1 / 2) := by
    have hinter : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [unif01, Measure.restrict_apply hmeas, hinter, Real.volume_Icc]
    norm_num
  calc ∫ u, sgnU u ∂unif01
      = ∫ u, (1 - 2 * Set.indicator (Set.Iic (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) u) ∂unif01 := by
        simp only [sgnU_eq_sub_indicator]
    _ = (∫ _u, (1 : ℝ) ∂unif01)
          - 2 * ∫ u, Set.indicator (Set.Iic (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) u ∂unif01 := by
        rw [integral_sub (integrable_const (1 : ℝ)) (hint.const_mul 2), integral_const_mul]
    _ = 0 := by
        rw [integral_indicator_const _ hmeas, integral_const, measureReal_def, measure_univ,
          measureReal_def, hset]
        simp

/-- The sample space of the example, with one uniform coordinate per site. -/
noncomputable def witQC : WSite → Measure ℝ := fun _ => unif01

instance witQC_isProb (s : WSite) : IsProbabilityMeasure (witQC s) :=
  inferInstanceAs (IsProbabilityMeasure unif01)

/-- The two-way interaction kernel `h^{\{1,2\}}(U^{(1)},U^{(2)}) = σ(U^{(1)})σ(U^{(2)})`, which
is completely degenerate. -/
noncomputable def witKernelC (ω : WSite → ℝ) : ℝ :=
  sgnU (ω (Sum.inl (0, 0))) * sgnU (ω (Sum.inl (1, 0)))

/-- The idiosyncratic term, a function of the private site of `o`. -/
noncomputable def witEpsC (o : Fin 1) (ω : WSite → ℝ) : ℝ := sgnU (ω (Sum.inr o))

/-- The level family. -/
noncomputable def witXiC : Bool → Fin 1 → (WSite → ℝ) → ℝ :=
  fun γ o => if γ then witEpsC o else witKernelC

@[simp] theorem witXiC_true (o : Fin 1) : witXiC true o = witEpsC o := by simp [witXiC]
@[simp] theorem witXiC_false (o : Fin 1) : witXiC false o = witKernelC := by simp [witXiC]

theorem measurable_witKernelC : Measurable witKernelC :=
  (measurable_sgnU.comp (measurable_pi_apply _)).mul (measurable_sgnU.comp (measurable_pi_apply _))

theorem measurable_witEpsC (o : Fin 1) : Measurable (witEpsC o) :=
  measurable_sgnU.comp (measurable_pi_apply _)

theorem witKernelC_mul_self (ω : WSite → ℝ) : witKernelC ω * witKernelC ω = 1 := by
  simp only [witKernelC]
  have h1 := sgnU_mul_self (ω (Sum.inl (0, 0)))
  have h2 := sgnU_mul_self (ω (Sum.inl (1, 0)))
  nlinarith [h1, h2]

theorem witEpsC_mul_self (o : Fin 1) (ω : WSite → ℝ) : witEpsC o ω * witEpsC o ω = 1 :=
  sgnU_mul_self _

theorem witXiC_pow_four (γ : Bool) (o : Fin 1) (ω : WSite → ℝ) : witXiC γ o ω ^ 4 = 1 := by
  cases γ
  · have h := witKernelC_mul_self ω
    simp only [witXiC_false]
    nlinarith [h]
  · have h := witEpsC_mul_self o ω
    simp only [witXiC_true]
    nlinarith [h]

theorem witMom : ∀ γ ∈ (Finset.univ : Finset Bool), ∀ o : Fin 1,
    FourthMom (Measure.pi witQC) (witXiC γ o) := by
  intro γ _ o
  have h4 : (fun ω => witXiC γ o ω ^ 4) = fun _ : WSite → ℝ => (1 : ℝ) := by
    funext ω; exact witXiC_pow_four γ o ω
  refine ⟨?_, by rw [h4]; exact integrable_const 1⟩
  cases γ
  · simp only [witXiC_false]
    exact measurable_witKernelC.aestronglyMeasurable
  · simp only [witXiC_true]
    exact (measurable_witEpsC o).aestronglyMeasurable

theorem witMomBound : ∀ γ ∈ (Finset.univ : Finset Bool), ∀ o : Fin 1,
    ∫ ω, witXiC γ o ω ^ 4 ∂(Measure.pi witQC) ≤ (1 : ℝ) := by
  intro γ _ o
  have h : (fun ω => witXiC γ o ω ^ 4) = fun _ : WSite → ℝ => (1 : ℝ) := by
    funext ω; exact witXiC_pow_four γ o ω
  rw [h]
  simp

theorem witDepC : ∀ γ ∈ (Finset.univ : Finset Bool), ∀ o : Fin 1,
    DependsOn (siteSet witIdio witIdx witLev γ o) (witXiC γ o) := by
  intro γ _ o
  cases γ
  · intro ω ω' h
    simp only [witXiC_false, witKernelC]
    rw [h _ (witSite_kernel 0 o), h _ (witSite_kernel 1 o)]
  · intro ω ω' h
    simp only [witXiC_true, witEpsC]
    rw [h _ (witSite_eps o)]

theorem witDegC : ∀ γ ∈ (Finset.univ : Finset Bool), ∀ o : Fin 1,
    ∀ s ∈ siteSet witIdio witIdx witLev γ o, IntZeroAt witQC s (witXiC γ o) := by
  intro γ _ o s hs
  cases γ
  · rcases witSite_mem_false hs with rfl | rfl
    · refine Filter.Eventually.of_forall fun ω => ?_
      have hne : (Sum.inl (1, 0) : WSite) ≠ Sum.inl (0, 0) := by decide
      simp only [witXiC_false, witKernelC, Function.update_self, Function.update_of_ne hne,
        witQC]
      rw [integral_mul_const, integral_sgnU, zero_mul]
    · refine Filter.Eventually.of_forall fun ω => ?_
      have hne : (Sum.inl (0, 0) : WSite) ≠ Sum.inl (1, 0) := by decide
      simp only [witXiC_false, witKernelC, Function.update_self, Function.update_of_ne hne,
        witQC]
      rw [integral_const_mul, integral_sgnU, mul_zero]
  · rw [witSite_mem_true hs]
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [witXiC_true, witEpsC, Function.update_self, witQC]
    exact integral_sgnU

/-- `E[ε_oξ_o ∣ 𝒟] = 0`, by property (i) at a site of the kernel. -/
theorem witMixC : ∫ ω, (witKernelC * witEpsC 0) ω ∂(Measure.pi witQC) = 0 := by
  refine integral_mul_eq_zero_of_intZeroAt (s₀ := (Sum.inl (0, 0) : WSite)) ?_ ?_ ?_
  · exact (witMom false (Finset.mem_univ _) 0).integrable_mul2 (witMom true (Finset.mem_univ _) 0)
  · have h := witDegC false (Finset.mem_univ _) 0 _ (witSite_kernel 0 0)
    simpa using h
  · intro ω v
    simp [witEpsC]

theorem witZC_apply (ω : WSite → ℝ) :
    levelSumC (Finset.univ : Finset Bool) witXiC 0 ω = witEpsC 0 ω + witKernelC ω := by
  simp [levelSumC]

/-- In the example `ζ² = 2 + 2ξε` pointwise, since `ξ² = ε² = 1`. -/
theorem witQuadFormC_eq (ω : WSite → ℝ) :
    quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ) (levelSumC (Finset.univ : Finset Bool) witXiC) ω
      = 2 + 2 * (witKernelC ω * witEpsC 0 ω) := by
  have hk := witKernelC_mul_self ω
  have he := witEpsC_mul_self 0 ω
  simp only [quadForm_apply, Fin.sum_univ_one, Matrix.one_apply_eq, witZC_apply]
  linear_combination hk + he

/-- In the example `ζ⁴ = 8 + 8ξε` pointwise. -/
theorem witQuadFormC_sq_eq (ω : WSite → ℝ) :
    quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ) (levelSumC (Finset.univ : Finset Bool) witXiC) ω ^ 2
      = 8 + 8 * (witKernelC ω * witEpsC 0 ω) := by
  rw [witQuadFormC_eq ω]
  have hk := witKernelC_mul_self ω
  have he := witEpsC_mul_self 0 ω
  nlinarith [hk, he]

theorem witMixC' : ∫ ω, witKernelC ω * witEpsC 0 ω ∂(Measure.pi witQC) = 0 := witMixC

theorem witMix_integrable : Integrable (fun ω => witKernelC ω * witEpsC 0 ω)
    (Measure.pi witQC) :=
  (witMom false (Finset.mem_univ _) 0).integrable_mul2 (witMom true (Finset.mem_univ _) 0)

theorem witness_integral_quadForm :
    ∫ ω, quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (levelSumC (Finset.univ : Finset Bool) witXiC) ω ∂(Measure.pi witQC) = 2 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall witQuadFormC_eq),
    integral_add (integrable_const 2) (witMix_integrable.const_mul 2), integral_const_mul,
    witMixC', integral_const]
  simp

theorem witness_integral_quadForm_sq :
    ∫ ω, quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (levelSumC (Finset.univ : Finset Bool) witXiC) ω ^ 2 ∂(Measure.pi witQC) = 8 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall witQuadFormC_sq_eq),
    integral_add (integrable_const 8) (witMix_integrable.const_mul 8), integral_const_mul,
    witMixC', integral_const]
  simp

/-- `Var(ζ'Wζ ∣ 𝒟) = 4`. -/
theorem witness_varQuad_cont :
    (∫ ω, quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (levelSumC (Finset.univ : Finset Bool) witXiC) ω ^ 2 ∂(Measure.pi witQC))
      - (∫ ω, quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (levelSumC (Finset.univ : Finset Bool) witXiC) ω ∂(Measure.pi witQC)) ^ 2 = 4 := by
  rw [witness_integral_quadForm, witness_integral_quadForm_sq]
  norm_num

/-- `Ω'_{oo'} = 2`, so `tr(WΩ'WΩ') = 4` and the bound's leading term is `8`. -/
theorem witness_levelGramC :
    levelGramC witQC (Finset.univ : Finset Bool) witXiC 0 0 = 2 := by
  rw [levelGramC, Matrix.of_apply]
  have h : ∀ ω : WSite → ℝ, levelSumC (Finset.univ : Finset Bool) witXiC 0 ω
      * levelSumC (Finset.univ : Finset Bool) witXiC 0 ω
      = quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (levelSumC (Finset.univ : Finset Bool) witXiC) ω := by
    intro ω
    simp [quadForm_apply, Matrix.one_apply_eq]
  rw [integral_congr_ae (Filter.Eventually.of_forall h), witness_integral_quadForm]

theorem witness_trace_cont :
    ((1 : Matrix (Fin 1) (Fin 1) ℝ) * levelGramC witQC Finset.univ witXiC * 1
        * levelGramC witQC Finset.univ witXiC).trace = 4 := by
  have h : ((1 : Matrix (Fin 1) (Fin 1) ℝ) * levelGramC witQC Finset.univ witXiC * 1
      * levelGramC witQC Finset.univ witXiC)
      = levelGramC witQC Finset.univ witXiC * levelGramC witQC Finset.univ witXiC := by
    rw [one_mul, mul_one]
  rw [h]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_one,
    witness_levelGramC]
  norm_num

/-- Every hypothesis of `var_quadForm_le_regime2_cont` holds on a model whose latents are uniform
on `[0,1]`. -/
theorem regime2_cont_witness :
    (∫ ω, quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (levelSumC (Finset.univ : Finset Bool) witXiC) ω ^ 2 ∂(Measure.pi witQC))
        - (∫ ω, quadForm (1 : Matrix (Fin 1) (Fin 1) ℝ)
            (levelSumC (Finset.univ : Finset Bool) witXiC) ω ∂(Measure.pi witQC)) ^ 2
      ≤ 2 * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * levelGramC witQC Finset.univ witXiC * 1
              * levelGramC witQC Finset.univ witXiC).trace
        + ((2 ^ Fintype.card (Fin 2)) ^ 4 : ℕ) * ((1 : ℝ) + 3 * (((1 : ℝ) + 1) / 2) ^ 2)
            * (4 * Fintype.card (Fin 2) * 1 * 1 : ℕ)
            * frobSq (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
  var_quadForm_le_regime2_cont (idio := witIdio) witIdx witLev witQC
    Matrix.isSymm_one Finset.univ witXiC (Gmax := 1) (cmax := 1) (C := 1) zero_le_one
    (by decide) (by intro γ _; simp [witLev]) (fun _ _ => rfl)
    (fun _ _ => le_trans (Finset.card_le_univ _) (by simp))
    (fun _ _ _ => le_trans (Finset.card_le_univ _) (by simp))
    witMom witDepC witDegC witMomBound

end Witness

end QuadformE2Cont
end Multiway
