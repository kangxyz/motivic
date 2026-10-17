/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralGenericFiniteImage
public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorClosedFiber
public import Motivic.AlgebraicGeometry.Graph.CommonStalkTransport
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorGeneric

/-!
# Original pair/image finite integral-support factorization

The original pair incidence maps to its whole scheme image. Restrict that
actual finite map to the point closure of one original pair generic point and
the point closure of its actual image inside the whole image scheme. Then
exterior-base-change this finite support map, keeping the actual Cartesian
square and its commuting square with the original intermediate-image map.

Reconstructed on 2026-10-14 from the preserved first 130 lines and current
library APIs. The missing original tail and its original full-file identity
have not been recovered. This complete consumer needs new verification.

Neither whole pair incidence nor its whole image is asserted integral. The
exterior support products retain all branches and nilpotents. No comparison
of a mere carrier fiber with a whole tensor algebra is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.IntegralGenericFiniteImage

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

local instance : IsFinite (F.incidenceMap G).toImage := F.incidenceToImage_isFinite G

/-- The reduced integral point closure inside the original pair incidence. -/
abbrev pairSupport := IntegralClosedSubscheme.pointClosure z.1

/-- The integral point closure inside the original whole scheme image. -/
abbrev imageSupport := IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1)

/-- The actual image kernel in the whole intermediate image is the target point-closure ideal. -/
theorem actualPairImageKernel :
    ((pairSupport F G z).val.subschemeι ≫ (F.incidenceMap G).toImage).ker =
      (imageSupport F G z).val :=
  IntegralClosedSubscheme.pointClosure_image_kernel (F.incidenceMap G).toImage z.1

/-- The original pair-to-image map restricted to the two integral supports. -/
abbrev pairMap : (pairSupport F G z).val.subscheme ⟶ (imageSupport F G z).val.subscheme :=
  IntegralClosedSubscheme.pointClosureMap (F.incidenceMap G).toImage z.1

instance pairMap_isFinite : IsFinite (pairMap F G z) := inferInstance

instance pairMap_isDominant : IsDominant (pairMap F G z) := inferInstance

/-- The support morphism commutes with the original pair-to-whole-image factor. -/
@[reassoc] theorem pairMap_ambient :
    pairMap F G z ≫ (imageSupport F G z).val.subschemeι =
      (pairSupport F G z).val.subschemeι ≫ (F.incidenceMap G).toImage :=
  IntegralClosedSubscheme.pointClosureMap_ambient (F.incidenceMap G).toImage z.1

/-- The second ambient immersion recovers the original pair-incidence map itself. -/
@[reassoc] theorem pairMap_product :
    pairMap F G z ≫ (imageSupport F G z).val.subschemeι ≫ (F.incidenceMap G).imageι =
      (pairSupport F G z).val.subschemeι ≫ F.incidenceMap G := by
  simp only [pairMap_ambient_assoc, Scheme.Hom.toImage_imageι]

/-- Its generic point maps to the target integral support's generic point. -/
theorem pairMap_genericPoint :
    pairMap F G z (genericPoint (pairSupport F G z).val.subscheme) =
      genericPoint (imageSupport F G z).val.subscheme :=
  IntegralClosedSubscheme.pointClosureMap_genericPoint (F.incidenceMap G).toImage z.1

/-- This is the original pair residue degree, proved by the actual closed-immersion squares. -/
theorem pairMap_residueDegree :
    (pairMap F G z).residueDegree (genericPoint (pairSupport F G z).val.subscheme) =
      (F.incidenceMap G).residueDegree z.1 := by
  rw [IntegralClosedSubscheme.pointClosureMap_residueDegree]
  have he := congrArg (fun m => m.residueDegree z.1) (F.incidenceMap G).toImage_imageι
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks, one_mul] using he

/-- The original pair-incidence structure map used for exterior products. -/
abbrev pairStructure := F.incidenceTarget G ≫ Z.hom

/-- The original whole-image structure map used for exterior products. -/
abbrev imageStructure := (F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom

/-- The support factorization is over the same literal exterior base. -/
@[reassoc] theorem pairMap_structure :
    pairMap F G z ≫ (imageSupport F G z).val.subschemeι ≫ imageStructure F G =
      (pairSupport F G z).val.subschemeι ≫ pairStructure F G := by
  simp [imageStructure, pairStructure, Category.assoc]

/-- The full exterior product of the original integral pair support. -/
abbrev pairExterior :=
  (pairSupport F G z).exteriorProduct (pairStructure F G) (H.projection ≫ Z.hom)

/-- The full exterior product of the integral target support. -/
abbrev imageExterior :=
  (imageSupport F G z).exteriorProduct (imageStructure F G) (H.projection ≫ Z.hom)

/-- The literal source support-product immersion into the whole exterior incidence. -/
abbrev pairExteriorInclusion : pairExterior F G H z ⟶ F.leftIntermediateSupportProduct G H :=
  (pairSupport F G z).exteriorInclusion (pairStructure F G) (H.projection ≫ Z.hom)

/-- The literal target support-product immersion into the whole exterior image. -/
abbrev imageExteriorInclusion : imageExterior F G H z ⟶ F.leftIntermediateImageProduct G H :=
  (imageSupport F G z).exteriorInclusion (imageStructure F G) (H.projection ≫ Z.hom)

/-- The whole exterior of this finite integral-support map, before any localization or reduction. -/
def pairExteriorMap : pairExterior F G H z ⟶ imageExterior F G H z :=
  pullback.map _ _ _ _ (pairMap F G z) (𝟙 H.scheme) (𝟙 (Spec (.of k)))
    (by simp) (by simp)

/-- The exterior finite map retains the actual original integral-support map. -/
@[reassoc (attr := simp)] theorem pairExteriorMap_fst :
    pairExteriorMap F G H z ≫
      pullback.fst ((imageSupport F G z).val.subschemeι ≫ imageStructure F G)
        (H.projection ≫ Z.hom) =
      pullback.fst ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
        (H.projection ≫ Z.hom) ≫ pairMap F G z :=
  pullback.lift_fst _ _ _

/-- The exterior factor is literally unchanged. -/
@[reassoc (attr := simp)] theorem pairExteriorMap_snd :
    pairExteriorMap F G H z ≫
      pullback.snd ((imageSupport F G z).val.subschemeι ≫ imageStructure F G)
        (H.projection ≫ Z.hom) =
      pullback.snd ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
        (H.projection ≫ Z.hom) := by
  simp only [pairExteriorMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The whole exterior map is the actual Cartesian base change of the support map. -/
theorem pairExteriorMap_isPullback :
    IsPullback
      (pullback.fst ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
        (H.projection ≫ Z.hom))
      (pairExteriorMap F G H z) (pairMap F G z)
      (pullback.fst ((imageSupport F G z).val.subschemeι ≫ imageStructure F G)
        (H.projection ≫ Z.hom)) := by
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback
      ((imageSupport F G z).val.subschemeι ≫ imageStructure F G)
      (H.projection ≫ Z.hom)) ?_ (pairExteriorMap_fst F G H z).symm
  simpa only [pairExteriorMap_snd, pairMap_structure] using
    (IsPullback.of_hasPullback
      ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
      (H.projection ≫ Z.hom))

/-- Finiteness comes from the original finite map by this proved Cartesian square. -/
instance pairExteriorMap_isFinite : IsFinite (pairExteriorMap F G H z) :=
  MorphismProperty.of_isPullback (pairExteriorMap_isPullback F G H z) inferInstance

/-- The support-product map commutes with the original whole intermediate-image map. -/
@[reassoc] theorem pairExteriorMap_ambient :
    pairExteriorMap F G H z ≫ imageExteriorInclusion F G H z =
      pairExteriorInclusion F G H z ≫ F.leftIntermediateImageMap G H := by
  apply pullback.hom_ext
  · simp [pairExteriorInclusion, imageExteriorInclusion, Category.assoc]
  · simp [pairExteriorInclusion, imageExteriorInclusion, Category.assoc]

/-- The actual exterior square retains the original ambient stalk action,
with its equal-point transport displayed explicitly. -/
theorem pairExteriorMap_stalkSquare (w : pairExterior F G H z) :
    Graph.alignedStalkMap (F.leftIntermediateImageMap G H)
        (pairExteriorInclusion F G H z w)
        (imageExteriorInclusion F G H z (pairExteriorMap F G H z w))
        (by
          exact congrArg (fun m => m w) (pairExteriorMap_ambient F G H z)) ≫
      (pairExteriorInclusion F G H z).stalkMap w =
    (imageExteriorInclusion F G H z).stalkMap (pairExteriorMap F G H z w) ≫
      (pairExteriorMap F G H z).stalkMap w := by
  simpa only [Graph.alignedStalkMap_rfl] using
    Graph.alignedStalkMap_naturality (F.leftIntermediateImageMap G H)
      (pairExteriorMap F G H z) (pairExteriorInclusion F G H z)
      (imageExteriorInclusion F G H z) (pairExteriorMap_ambient F G H z)
      w (pairExteriorMap F G H z w) rfl
      (by exact congrArg (fun m => m w) (pairExteriorMap_ambient F G H z))

/-- Residue degrees use the actual exterior morphisms, via their immersion square. -/
theorem pairExteriorMap_residueDegree (w : pairExterior F G H z) :
    (pairExteriorMap F G H z).residueDegree w =
      (F.leftIntermediateImageMap G H).residueDegree (pairExteriorInclusion F G H z w) := by
  have he := congrArg (fun m => m.residueDegree w) (pairExteriorMap_ambient F G H z)
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks, one_mul, mul_one]
    using he

/-- Flat projection from a genuine exterior generic point recovers the original pair point. -/
theorem pairExteriorGeneric_projection (w : genericPoints (pairExterior F G H z)) :
    F.leftExteriorPairProjection G H (pairExteriorInclusion F G H z w.1) = z.1 := by
  simpa only [IntegralClosedSubscheme.point_pointClosure] using
    (pairSupport F G z).exteriorGeneric_ambientProjection (S := Spec (.of k))
      (pairStructure F G) (H.projection ≫ Z.hom) w

/-- The source closed fiber is the whole actual support-product stalk,
including any nilpotents introduced by exterior base change. -/
def pairExteriorClosedFiberEquiv (w : genericPoints (pairExterior F G H z)) :
    F.leftExteriorClosedFiber G H (pairExteriorInclusion F G H z w.1) ≃+*
      (pairExterior F G H z).presheaf.stalk w.1 :=
  (pairSupport F G z).exteriorGenericClosedFiberEquiv (S := Spec (.of k))
    (pairStructure F G) (H.projection ≫ Z.hom) w

/-- This source quotient comparison preserves the literal original ambient scalar map. -/
theorem pairExteriorClosedFiberEquiv_scalarSquare
    (w : genericPoints (pairExterior F G H z)) :
    (pairExteriorClosedFiberEquiv F G H z w).toRingHom.comp (Ideal.Quotient.mk _) =
      ((pairExteriorInclusion F G H z).stalkMap w.1).hom :=
  (pairSupport F G z).exteriorGenericClosedFiberEquiv_scalarSquare (S := Spec (.of k))
    (pairStructure F G) (H.projection ≫ Z.hom) w

/-- The actual target closed fiber is its entire exterior support stalk,
without identifying it with a field or choosing a branch. -/
def imageExteriorClosedFiberEquiv (v : genericPoints (imageExterior F G H z)) :
    Koszul.coefficientClosedFiber
      ((pullback.fst (imageStructure F G) (H.projection ≫ Z.hom)).stalkMap
        (imageExteriorInclusion F G H z v.1)).hom ≃+*
      (imageExterior F G H z).presheaf.stalk v.1 :=
  (imageSupport F G z).exteriorGenericClosedFiberEquiv (S := Spec (.of k))
    (imageStructure F G) (H.projection ≫ Z.hom) v

/-- The target quotient comparison preserves the literal original image-product action. -/
theorem imageExteriorClosedFiberEquiv_scalarSquare
    (v : genericPoints (imageExterior F G H z)) :
    (imageExteriorClosedFiberEquiv F G H z v).toRingHom.comp (Ideal.Quotient.mk _) =
      ((imageExteriorInclusion F G H z).stalkMap v.1).hom :=
  (imageSupport F G z).exteriorGenericClosedFiberEquiv_scalarSquare (S := Spec (.of k))
    (imageStructure F G) (H.projection ≫ Z.hom) v

end MotivicTest.IntegralGenericFiniteImage
