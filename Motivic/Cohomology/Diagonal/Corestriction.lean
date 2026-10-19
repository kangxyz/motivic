/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.CycleSymbols
public import Motivic.Cohomology.WeightTwo.CorestrictionMixed

/-!
# Actual finite-extension corestriction in every diagonal weight

The already constructed finite cycle pushforward, identity-axis descent, and
full endpoint-fiber law work in every weight. They descend here through the
literal singular-boundary quotient to the original raw and derived `H^{q,q}`.
The coefficient fields remain unchanged, no separability is assumed, and a
rational graph transfers to its entire finite point with its residue degree.
This construction does not identify the transfer with an unconstructed Milnor norm.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.DiagonalCorestriction
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open DiagonalTopDegree
open DiagonalCycleSymbols
open WeightOneBoundaryNorm
open WeightTwoCorestriction (cyclePushforward reducedPushforward reducedPushforward_quotient
  cyclePushforward_face source ambientMap zeroSourceIso graphEmbedding torusMap)

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- Actual finite pushforward preserves each endpoint on the original reduced torus. -/
theorem reducedPushforward_face (q : ℕ) (i : Fin 2) :
    transfer (reducedTorus E q) ((Cor.simplexProductCosimplicial (point E)).δ i) ≫
      reducedPushforward (k := k) (E := E) 0 q =
    reducedPushforward (k := k) (E := E) 1 q ≫
      transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ i) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective E q
    (Cor.simplexProduct (point E) 1) s
  change reducedPushforward (k := k) (E := E) 0 q
      (transfer (reducedTorus E q) ((Cor.simplexProductCosimplicial (point E)).δ i)
        ((toReducedTorus E q).hom.app _ (ULift.up α))) =
    transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ i)
      (reducedPushforward (k := k) (E := E) 1 q
        ((toReducedTorus E q).hom.app _ (ULift.up α)))
  rw [reducedTorus_transfer_apply]
  have h₀ := reducedPushforward_quotient (k := k) (E := E) 0 q
    ((Cor.simplexProductCosimplicial (point E)).δ i ≫ α)
  have h₁ := reducedPushforward_quotient (k := k) (E := E) 1 q α
  refine h₀.trans ?_
  rw [cyclePushforward_face]
  exact (reducedTorus_transfer_apply k q
    ((Cor.simplexProductCosimplicial (point k)).δ i)
    (cyclePushforward (k := k) (E := E) 1 q α)).symm.trans
      (congrArg (transfer (reducedTorus k q)
        ((Cor.simplexProductCosimplicial (point k)).δ i)) h₁.symm)

/-- Whole singular boundaries transfer with their original alternating endpoint signs. -/
theorem reducedPushforward_boundary (q : ℕ) (x : chains E q 1) :
    reducedPushforward (k := k) (E := E) 0 q (boundary E q x) =
      boundary k q (reducedPushforward (k := k) (E := E) 1 q x) := by
  rw [boundary_eq_endpoints, boundary_eq_endpoints, map_sub]
  exact congrArg₂ (· - ·)
    (ConcreteCategory.congr_hom (reducedPushforward_face (k := k) (E := E) q 0) x)
    (ConcreteCategory.congr_hom (reducedPushforward_face (k := k) (E := E) q 1) x)

/-- Actual finite pushforward on the literal zero-cycle quotient. -/
def quotientCorestriction (q : ℕ) : zeroHomology E q →+ zeroHomology k q :=
  QuotientAddGroup.map (boundary E q).range (boundary k q).range
    (reducedPushforward (k := k) (E := E) 0 q).hom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨reducedPushforward (k := k) (E := E) 1 q x,
        (reducedPushforward_boundary q x).symm⟩)

/-- The descended quotient map retains the actual zero-cycle representative. -/
theorem quotientCorestriction_mk (q : ℕ) (x : chains E q 0) :
    quotientCorestriction (k := k) q (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (reducedPushforward (k := k) (E := E) 0 q x) := rfl

/-- Finite-extension transfer on the original raw diagonal homology, in every weight. -/
def corestriction (q : ℕ) : (motivicRawBaseComplex E q).homology q →+
    (motivicRawBaseComplex k q).homology q :=
  (quotientToRawEquiv k q).toAddMonoidHom.comp
    ((quotientCorestriction (k := k) (E := E) q).comp
      (quotientToRawEquiv E q).symm.toAddMonoidHom)

/-- The raw transfer sends the original singular class to its actual finite pushforward. -/
theorem corestriction_singularClass (q : ℕ) (x : chains E q 0) :
    corestriction (k := k) q (singularClass E q x) =
      singularClass k q (reducedPushforward (k := k) (E := E) 0 q x) := by
  rw [← quotientToRawEquiv_mk]
  change quotientToRawEquiv k q (quotientCorestriction (k := k) q
    ((quotientToRawEquiv E q).symm (quotientToRawEquiv E q _))) = _
  rw [AddEquiv.symm_apply_apply, quotientCorestriction_mk, quotientToRawEquiv_mk]

/-- The same finite cycle pushforward with the original zero simplex removed. -/
def pointPushforward (q : ℕ) : (point E ⟶ target E q) →+ (point k ⟶ target k q) :=
  (Preadditive.leftComp (target k q) (zeroProductIso k).inv).comp
    ((cyclePushforward (k := k) (E := E) 0 q).comp
      (Preadditive.leftComp (target E q) (zeroProductIso E).hom))

/-- The point transfer retains every original signed coefficient and finite image degree. -/
theorem pointPushforward_apply (q : ℕ) (α : point E ⟶ target E q) :
    pointPushforward (k := k) q α = (zeroProductIso k).inv ≫
      cyclePushforward (k := k) 0 q ((zeroProductIso E).hom ≫ α) := rfl

/-- Every signed point-cycle class transfers by its original actual finite pushforward. -/
theorem corestriction_cycleClass (q : ℕ) (α : point E ⟶ target E q) :
    corestriction (k := k) q (cycleClass E q α) =
      cycleClass k q (pointPushforward (k := k) q α) := by
  change corestriction (k := k) q (singularClass E q ((toReducedTorus E q).hom.app
    (op (Cor.simplexProduct (point E) 0)) (ULift.up ((zeroProductIso E).hom ≫ α)))) = _
  rw [corestriction_singularClass]
  exact (congrArg (singularClass k q)
    (reducedPushforward_quotient (k := k) (E := E) 0 q
      ((zeroProductIso E).hom ≫ α))).trans (singularClass_quotient k q _)

/-- Actual signed cycle representatives uniquely determine the raw transfer. -/
theorem corestriction_unique (q : ℕ)
    (f : (motivicRawBaseComplex E q).homology q →+ (motivicRawBaseComplex k q).homology q)
    (hf : ∀ α : point E ⟶ target E q,
      f (cycleClass E q α) = cycleClass k q (pointPushforward (k := k) q α)) :
    f = corestriction (k := k) (E := E) q := by
  ext x
  obtain ⟨α, rfl⟩ := cycleClass_surjective E q x
  exact (hf α).trans (corestriction_cycleClass q α).symm

/-- Specializing the all-weight transfer recovers the original weight-two raw transfer. -/
theorem corestriction_two :
    corestriction (k := k) (E := E) 2 = WeightTwoCorestriction.corestriction (k := k) := by
  symm
  apply corestriction_unique
  intro α
  exact WeightTwoCorestriction.corestriction_cycleClass α

/-- A rational tuple transfers to the class of the whole original finite point. -/
theorem corestriction_graphSymbol (q : ℕ) (a : Fin q → Eˣ) :
    corestriction (k := k) q (graphSymbol E q a) =
      cycleClass k q (pointPushforward (k := k) q
        ((Cor.graphFunctor E).map (rationalTuple E q a))) :=
  corestriction_cycleClass q _

section FinitePoint

local instance base_integral (F : Type u) [Field F] :
    IsIntegral (SmoothSite.base (Spec (.of F))).left :=
  inferInstanceAs (IsIntegral (Spec (.of F)))

/-- The entire finite point, expressed using the existing ambient and zero-simplex maps. -/
def finitePointMap (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (.of E) q) :
    Spec (.of E) ⟶
      (SmoothSite.product (SmoothSite.base (Spec (.of k)))
        (SmoothSite.torusPower (.of k) q)).left :=
  (zeroSourceIso E).inv.left ≫ graphEmbedding ((zeroSourceIso E).hom ≫ f) ≫
    ambientMap (k := k) (E := E) 0 q ≫
      (Cor.graphTransportIso k (zeroSourceIso k)
        (Iso.refl (SmoothSite.torusPower (.of k) q))).hom

instance finitePointMap_isFinite (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (.of E) q) :
    IsFinite (finitePointMap (k := k) q f) := by
  unfold finitePointMap
  infer_instance

omit [Module.Finite k E] in
/-- The transferred point retains exactly the given original scalar-field map. -/
@[reassoc (attr := simp)]
theorem finitePointMap_fst (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (.of E) q) :
    finitePointMap (k := k) q f ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom
        (SmoothSite.torusPower (.of k) q).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  simp only [finitePointMap, Category.assoc, Cor.graphTransportIso_hom_fst,
    WeightTwoCorestriction.ambientMap_fst_assoc,
    WeightTwoCorestriction.graphEmbedding_fst_assoc]
  have hk : (zeroSourceIso k).hom.left = (source k 0).hom := by
    have h := MorphismProperty.Over.w (zeroSourceIso k).hom
    exact (Category.comp_id _).symm.trans h
  rw [hk, WeightTwoCorestriction.sourceMap_projection]
  rw [← Category.assoc, MorphismProperty.Over.w]
  exact Category.id_comp _

omit [Module.Finite k E] in
/-- Every coordinate of the finite point is the original tuple followed by scalar projection. -/
@[reassoc (attr := simp)]
theorem finitePointMap_snd (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (.of E) q) :
    finitePointMap (k := k) q f ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom
        (SmoothSite.torusPower (.of k) q).hom = f.left ≫ torusMap (k := k) q := by
  simp only [finitePointMap, Category.assoc, Cor.graphTransportIso_hom_snd,
    Iso.refl_hom, WeightTwoCorestriction.ambientMap_snd_assoc,
    WeightTwoCorestriction.graphEmbedding_snd_assoc, MorphismProperty.Comma.comp_left]
  have he : (zeroSourceIso E).inv.left ≫ (zeroSourceIso E).hom.left = 𝟙 _ :=
    congrArg (fun f => f.left) (zeroSourceIso E).inv_hom_id
  rw [← Category.assoc, ← Category.assoc, he]
  change (𝟙 _ ≫ f.left) ≫ torusMap (k := k) q ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- Graph transfer is the genuine pushforward of the full finite-point fundamental cycle. -/
theorem toIntegralCycle_pointPushforward_graph (q : ℕ)
    (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (.of E) q) :
    FiniteCorrespondence.toIntegralCycle
      (f := (SmoothSite.base (Spec (.of k))).hom)
      (g := (SmoothSite.torusPower (.of k) q).hom)
      (pointPushforward (k := k) q ((Cor.graphFunctor E).map f)) =
    IntegralCycle.finitePushforward (finitePointMap (k := k) q f)
      (fundamentalCycle (Spec (.of E))) := by
  rw [pointPushforward_apply]
  change FiniteCorrespondence.toIntegralCycle
    (f := (SmoothSite.base (Spec (.of k))).hom)
    (g := (SmoothSite.torusPower (.of k) q).hom)
    ((Cor.graphFunctor k).map (zeroSourceIso k).inv ≫
      cyclePushforward (k := k) 0 q
        ((Cor.graphFunctor E).map (zeroSourceIso E).hom ≫ (Cor.graphFunctor E).map f)) = _
  rw [Cor.toIntegralCycle_graphIso_comp, WeightTwoCorestriction.toIntegralCycle_cyclePushforward,
    ← Functor.map_comp, WeightTwoCorestriction.toIntegralCycle_graph]
  rw [← finitePushforward_fundamentalCycle (zeroSourceIso E).inv.left]
  simp only [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  erw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  rfl

end FinitePoint

section Derived

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- Actual finite-extension transfer on the originally defined derived diagonal group. -/
def motivicCorestriction (q : ℕ) :
    motivicCohomology E q q (SmoothSite.base (Spec (.of E))) →+
      motivicCohomology k q q (SmoothSite.base (Spec (.of k))) :=
  (motivicRawBaseEvaluationComparison k q q).symm.toAddMonoidHom.comp
    ((corestriction (k := k) (E := E) q).comp
      (motivicRawBaseEvaluationComparison E q q).toAddMonoidHom)

/-- The derived transfer uses the original raw comparison without changing either field. -/
theorem motivicCorestriction_comparison (q : ℕ)
    (x : motivicCohomology E q q (SmoothSite.base (Spec (.of E)))) :
    motivicRawBaseEvaluationComparison k q q (motivicCorestriction (k := k) q x) =
      corestriction (k := k) q (motivicRawBaseEvaluationComparison E q q x) :=
  (motivicRawBaseEvaluationComparison k q q).apply_symm_apply _

/-- The original derived class of a signed point cycle has its actual transferred representative. -/
theorem motivicCorestriction_cycleClass (q : ℕ) (α : point E ⟶ target E q) :
    motivicCorestriction (k := k) q
      ((motivicRawBaseEvaluationComparison E q q).symm (cycleClass E q α)) =
    (motivicRawBaseEvaluationComparison k q q).symm
      (cycleClass k q (pointPushforward (k := k) q α)) := by
  apply (motivicRawBaseEvaluationComparison k q q).injective
  rw [motivicCorestriction_comparison, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, corestriction_cycleClass]

end Derived

end Motivic.DiagonalCorestriction
