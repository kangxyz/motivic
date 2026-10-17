/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionBoundary

/-!
# Actual finite-extension corestriction on original weight-two homology

The proved finite cycle map preserves whole signed endpoint boundaries and every
identity-axis relation. Its two relevant degrees descend to the original raw
weight-two homology and, through the canonical comparison, to the original
derived motivic group. No replacement presentation or assumed boundary theorem
is used, and the extension need not be separable.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.WeightTwoSymbols

open PresheafWithTransfers WeightOnePointNorm WeightOneBoundaryNorm

variable (k : Type u) [Field k]

/-- Every genuine weight-two homology class comes from the original top raw term. -/
theorem rawClass_surjective : Function.Surjective (rawClass k) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  unfold rawClass
  infer_instance

/-- Every genuine weight-two class has an actual signed point-cycle representative. -/
theorem cycleClass_surjective : Function.Surjective (cycleClass k) := by
  intro y
  obtain ⟨x, rfl⟩ := rawClass_surjective k y
  obtain ⟨⟨α⟩, hα⟩ := toReducedTorus_surjective k 2
    (Cor.simplexProduct (point k) 0) ((motivicRawBaseComplexXIso k 2 0).hom x)
  refine ⟨(zeroProductIso k).inv ≫ α, ?_⟩
  change rawClass k ((motivicRawBaseComplexXIso k 2 0).inv
    ((toReducedTorus k 2).hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ (zeroProductIso k).inv ≫ α)))) = _
  rw [Iso.hom_inv_id_assoc, hα, Iso.hom_inv_id_apply]

end Motivic.WeightTwoSymbols

namespace Motivic.WeightTwoCorestriction

open PresheafWithTransfers WeightOnePointNorm WeightOneBoundaryNorm

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- The degree-one map in the original positively shifted weight-two raw complex. -/
def rawDegreeOnePushforward : (motivicRawBaseComplex E 2).X 1 ⟶
    (motivicRawBaseComplex k 2).X 1 :=
  (motivicRawBaseComplexXIso E 2 1).hom ≫
    reducedPushforward (k := k) (E := E) 1 2 ≫
      (motivicRawBaseComplexXIso k 2 1).inv

/-- The top degree-two map in the original raw complex. -/
def rawDegreeTwoPushforward : (motivicRawBaseComplex E 2).X 2 ⟶
    (motivicRawBaseComplex k 2).X 2 :=
  (motivicRawBaseComplexXIso E 2 0).hom ≫
    reducedPushforward (k := k) (E := E) 0 2 ≫
      (motivicRawBaseComplexXIso k 2 0).inv

/-- The same actual finite cycle transfer with the original zero-simplex removed. -/
def pointPushforward : (point E ⟶ WeightTwoSymbols.target E) →+
    (point k ⟶ WeightTwoSymbols.target k) :=
  (Preadditive.leftComp (WeightTwoSymbols.target k) (zeroProductIso k).inv).comp
    ((cyclePushforward (k := k) (E := E) 0 2).comp
      (Preadditive.leftComp (WeightTwoSymbols.target E) (zeroProductIso E).hom))

/-- Its point formula contains no change of the original signed coefficients. -/
theorem pointPushforward_apply (α : point E ⟶ WeightTwoSymbols.target E) :
    pointPushforward (k := k) α = (zeroProductIso k).inv ≫
      cyclePushforward (k := k) 0 2 ((zeroProductIso E).hom ≫ α) := rfl

/-- The original top raw representative gives the transferred point-cycle class. -/
theorem rawDegreeTwoPushforward_cycleClass (α : point E ⟶ WeightTwoSymbols.target E) :
    WeightTwoSymbols.rawClass k
      (rawDegreeTwoPushforward (k := k) (E := E)
        ((motivicRawBaseComplexXIso E 2 0).inv
          ((toReducedTorus E 2).hom.app (op (Cor.simplexProduct (point E) 0))
            (ULift.up ((zeroProductIso E).hom ≫ α))))) =
      WeightTwoSymbols.cycleClass k (pointPushforward (k := k) α) := by
  change WeightTwoSymbols.singularClass k
    (reducedPushforward (k := k) (E := E) 0 2
      ((motivicRawBaseComplexXIso E 2 0).hom
        ((motivicRawBaseComplexXIso E 2 0).inv
          ((toReducedTorus E 2).hom.app (op (Cor.simplexProduct (point E) 0))
            (ULift.up ((zeroProductIso E).hom ≫ α)))))) = _
  rw [Iso.inv_hom_id_apply]
  exact (congrArg (WeightTwoSymbols.singularClass k)
    (reducedPushforward_quotient (k := k) (E := E) 0 2 ((zeroProductIso E).hom ≫ α))).trans
      (WeightTwoSymbols.singularClass_quotient k _)

/-- Actual finite pushforward commutes with each represented endpoint on the original quotient. -/
theorem reducedPushforward_face (i : Fin 2) :
    transfer (reducedTorus E 2) ((Cor.simplexProductCosimplicial (point E)).δ i) ≫
      reducedPushforward (k := k) (E := E) 0 2 =
    reducedPushforward (k := k) (E := E) 1 2 ≫
      transfer (reducedTorus k 2) ((Cor.simplexProductCosimplicial (point k)).δ i) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective E 2
    (Cor.simplexProduct (point E) 1) s
  change reducedPushforward (k := k) (E := E) 0 2
      (transfer (reducedTorus E 2) ((Cor.simplexProductCosimplicial (point E)).δ i)
        ((toReducedTorus E 2).hom.app _ (ULift.up α))) =
    transfer (reducedTorus k 2) ((Cor.simplexProductCosimplicial (point k)).δ i)
      (reducedPushforward (k := k) (E := E) 1 2
        ((toReducedTorus E 2).hom.app _ (ULift.up α)))
  rw [reducedTorus_transfer_apply]
  have h₀ := reducedPushforward_quotient (k := k) (E := E) 0 2
    ((Cor.simplexProductCosimplicial (point E)).δ i ≫ α)
  have h₁ := reducedPushforward_quotient (k := k) (E := E) 1 2 α
  refine h₀.trans ?_
  rw [cyclePushforward_face]
  exact (reducedTorus_transfer_apply k 2
    ((Cor.simplexProductCosimplicial (point k)).δ i)
    (cyclePushforward (k := k) (E := E) 1 2 α)).symm.trans
      (congrArg (transfer (reducedTorus k 2)
        ((Cor.simplexProductCosimplicial (point k)).δ i)) h₁.symm)

/-- The actual singular differential is preserved, with both original endpoint signs. -/
theorem reducedPushforward_d :
    (singularObj (reducedTorus E 2) (point E)).d 1 0 ≫
      reducedPushforward (k := k) (E := E) 0 2 =
    reducedPushforward (k := k) (E := E) 1 2 ≫
      (singularObj (reducedTorus k 2) (point k)).d 1 0 := by
  rw [WeightTwoSymbols.singular_d_one_zero, WeightTwoSymbols.singular_d_one_zero,
    Preadditive.sub_comp, Preadditive.comp_sub, reducedPushforward_face,
    reducedPushforward_face]

/-- The two actual raw maps preserve the original positively signed weight-two boundary. -/
theorem rawPushforward_d :
    rawDegreeOnePushforward (k := k) (E := E) ≫ (motivicRawBaseComplex k 2).d 1 2 =
      (motivicRawBaseComplex E 2).d 1 2 ≫ rawDegreeTwoPushforward (k := k) (E := E) := by
  rw [rawDegreeOnePushforward, rawDegreeTwoPushforward,
    WeightTwoSymbols.raw_d_one_two, WeightTwoSymbols.raw_d_one_two]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h := congrArg (fun f => (motivicRawBaseComplexXIso E 2 1).hom ≫ f ≫
    (motivicRawBaseComplexXIso k 2 0).inv) (reducedPushforward_d (k := k) (E := E)).symm
  simpa only [Category.assoc] using h

/-- The top raw transfer sends each genuine boundary to zero in the original target homology. -/
theorem rawPushforward_boundary :
    (motivicRawBaseComplex E 2).d 1 2 ≫ rawDegreeTwoPushforward (k := k) (E := E) ≫
      WeightTwoSymbols.rawClass k = 0 := by
  rw [← Category.assoc, ← rawPushforward_d, Category.assoc,
    WeightTwoSymbols.differential_rawClass, comp_zero]

/-- Finite-extension corestriction on the original weight-two raw homology group. -/
def corestrictionHom : (motivicRawBaseComplex E 2).homology 2 ⟶
    (motivicRawBaseComplex k 2).homology 2 :=
  ((motivicRawBaseComplex E 2).sc 2).descHomology
    ((motivicRawBaseComplex E 2).iCycles 2 ≫
      rawDegreeTwoPushforward (k := k) (E := E) ≫ WeightTwoSymbols.rawClass k) (by
        change ((motivicRawBaseComplex E 2).sc 2).toCycles ≫
          (((motivicRawBaseComplex E 2).sc 2).iCycles ≫ _) = 0
        rw [← Category.assoc, ShortComplex.toCycles_i]
        change (motivicRawBaseComplex E 2).d ((ComplexShape.up ℤ).prev 2) 2 ≫ _ = 0
        rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel 1 2 from rfl)]
        exact rawPushforward_boundary)

/-- The additive corestriction, without changing the original homology group. -/
def corestriction : (motivicRawBaseComplex E 2).homology 2 →+
    (motivicRawBaseComplex k 2).homology 2 :=
  (corestrictionHom (k := k) (E := E)).hom

/-- Its defining equality uses the original cycle inclusion and homology quotient. -/
theorem corestriction_class (x : (motivicRawBaseComplex E 2).cycles 2) :
    corestriction (k := k) ((motivicRawBaseComplex E 2).homologyπ 2 x) =
      WeightTwoSymbols.rawClass k
        (rawDegreeTwoPushforward (k := k) (E := E)
          ((motivicRawBaseComplex E 2).iCycles 2 x)) := by
  have h := ((motivicRawBaseComplex E 2).sc 2).π_descHomology
    ((motivicRawBaseComplex E 2).iCycles 2 ≫
      rawDegreeTwoPushforward (k := k) (E := E) ≫ WeightTwoSymbols.rawClass k) (by
        change ((motivicRawBaseComplex E 2).sc 2).toCycles ≫
          (((motivicRawBaseComplex E 2).sc 2).iCycles ≫ _) = 0
        rw [← Category.assoc, ShortComplex.toCycles_i]
        change (motivicRawBaseComplex E 2).d ((ComplexShape.up ℤ).prev 2) 2 ≫ _ = 0
        rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel 1 2 from rfl)]
        exact rawPushforward_boundary)
  exact ConcreteCategory.congr_hom h x

/-- Corestriction on a top raw class is the actual top raw pushforward. -/
theorem corestriction_rawClass (x : (motivicRawBaseComplex E 2).X 2) :
    corestriction (k := k) (WeightTwoSymbols.rawClass E x) =
      WeightTwoSymbols.rawClass k (rawDegreeTwoPushforward (k := k) (E := E) x) := by
  rw [WeightTwoSymbols.rawClass, ConcreteCategory.comp_apply, corestriction_class]
  have h := ConcreteCategory.congr_hom
    ((motivicRawBaseComplex E 2).iCyclesIso_inv_hom_id 2 3 ((ComplexShape.up ℤ).next_eq' rfl)
      (WeightTwoSymbols.raw_outgoing_d_zero E)) x
  exact congrArg (fun y => WeightTwoSymbols.rawClass k
    (rawDegreeTwoPushforward (k := k) (E := E) y)) h

/-- The actual finite pushforward gives corestriction on every signed point-cycle class. -/
theorem corestriction_cycleClass (α : point E ⟶ WeightTwoSymbols.target E) :
    corestriction (k := k) (WeightTwoSymbols.cycleClass E α) =
      WeightTwoSymbols.cycleClass k (pointPushforward (k := k) α) := by
  change corestriction (k := k)
    (WeightTwoSymbols.rawClass E ((motivicRawBaseComplexXIso E 2 0).inv
      ((toReducedTorus E 2).hom.app (op (Cor.simplexProduct (point E) 0))
        (ULift.up ((zeroProductIso E).hom ≫ α))))) = _
  rw [corestriction_rawClass]
  exact rawDegreeTwoPushforward_cycleClass α

/-- Actual signed cycles determine the homology corestriction uniquely. -/
theorem corestriction_unique
    (f : (motivicRawBaseComplex E 2).homology 2 →+ (motivicRawBaseComplex k 2).homology 2)
    (hf : ∀ α : point E ⟶ WeightTwoSymbols.target E,
      f (WeightTwoSymbols.cycleClass E α) =
        WeightTwoSymbols.cycleClass k (pointPushforward (k := k) α)) :
    f = corestriction (k := k) (E := E) := by
  ext x
  obtain ⟨α, rfl⟩ := WeightTwoSymbols.cycleClass_surjective E x
  exact (hf α).trans (corestriction_cycleClass α).symm

section Derived

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- Corestriction on the original derived motivic group via its canonical raw comparison. -/
def motivicCorestriction :
    motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E))) →+
      motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k))) :=
  (motivicRawBaseEvaluationComparison k 2 2).symm.toAddMonoidHom.comp
    ((corestriction (k := k) (E := E)).comp
      (motivicRawBaseEvaluationComparison E 2 2).toAddMonoidHom)

/-- The derived transfer is the same original raw map under the original comparison. -/
theorem motivicCorestriction_comparison
    (x : motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E)))) :
    motivicRawBaseEvaluationComparison k 2 2 (motivicCorestriction (k := k) x) =
      corestriction (k := k) (motivicRawBaseEvaluationComparison E 2 2 x) :=
  (motivicRawBaseEvaluationComparison k 2 2).apply_symm_apply _

end Derived

end Motivic.WeightTwoCorestriction
