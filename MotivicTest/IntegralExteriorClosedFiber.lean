/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorClosedFiber
public import Motivic.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorGeneric

/-!
# Original pair and integral-image exterior closed-fiber consumers

The pair support is the integral point closure inside the original incidence
scheme. The target support is separately the integral point closure inside the
whole scheme image. Its image under the actual closed immersion into the
ambient product is proved to be the ambient point closure. No identification of
that integral support with the entire unreduced scheme image is made.

The source and target exterior products retain their genuine local rings. The
fiber equivalences are induced by their literal closed-immersion stalk maps.
All-branch tensor-algebra localization and finite-map degree comparison remain
separate from these support-quotient identities.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.IntegralExteriorClosedFiber

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

/-- The actual exterior of one original integral pair support. -/
abbrev pairIntegralExterior :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorProduct
    (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)

/-- The literal inclusion into the original, unreduced whole exterior incidence. -/
abbrev pairIntegralExteriorInclusion : pairIntegralExterior F G H z ⟶
    F.leftIntermediateSupportProduct G H :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorInclusion
    (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)

/-- Flat exterior projection recovers the original pair point from a genuine
generic point of its integral-support exterior. -/
theorem actualPairProjection (w : genericPoints (pairIntegralExterior F G H z)) :
    F.leftExteriorPairProjection G H (pairIntegralExteriorInclusion F G H z w.1) = z.1 := by
  simpa only [IntegralClosedSubscheme.point_pointClosure] using
    (IntegralClosedSubscheme.pointClosure z.1).exteriorGeneric_ambientProjection (S := Spec (.of k))
      (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) w

/-- The original pair's actual exterior closed fiber is its integral-exterior stalk. -/
def actualPairClosedFiberEquiv (w : genericPoints (pairIntegralExterior F G H z)) :
    F.leftExteriorClosedFiber G H (pairIntegralExteriorInclusion F G H z w.1) ≃+*
      (pairIntegralExterior F G H z).presheaf.stalk w.1 :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorGenericClosedFiberEquiv (S := Spec (.of k))
    (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) w

/-- The identification is induced by the actual source support's closed-immersion stalk map. -/
@[simp] theorem actualPairClosedFiberEquiv_mk
    (w : genericPoints (pairIntegralExterior F G H z))
    (r : (F.leftIntermediateSupportProduct G H).presheaf.stalk
      (pairIntegralExteriorInclusion F G H z w.1)) :
    actualPairClosedFiberEquiv F G H z w (Ideal.Quotient.mk _ r) =
      (pairIntegralExteriorInclusion F G H z).stalkMap w.1 r :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorGenericClosedFiberEquiv_mk (S := Spec (.of k))
    (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) w r

/-- The source comparison commutes with the original whole incidence-product action. -/
theorem actualPairClosedFiberEquiv_scalarSquare
    (w : genericPoints (pairIntegralExterior F G H z)) :
    (actualPairClosedFiberEquiv F G H z w).toRingHom.comp (Ideal.Quotient.mk _) =
      ((pairIntegralExteriorInclusion F G H z).stalkMap w.1).hom :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorGenericClosedFiberEquiv_scalarSquare
    (S := Spec (.of k))
    (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) w

/-- The source closed-fiber quotient is the actual support stalk as an original ambient module. -/
def actualPairClosedFiberModuleIso (w : genericPoints (pairIntegralExterior F G H z)) :
    ModuleCat.of ((F.leftIntermediateSupportProduct G H).presheaf.stalk
        (pairIntegralExteriorInclusion F G H z w.1))
        (F.leftExteriorClosedFiber G H (pairIntegralExteriorInclusion F G H z w.1)) ≅
      (ModuleCat.restrictScalars
        ((pairIntegralExteriorInclusion F G H z).stalkMap w.1).hom).obj
        (ModuleCat.of ((pairIntegralExterior F G H z).presheaf.stalk w.1)
          ((pairIntegralExterior F G H z).presheaf.stalk w.1)) :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorGenericClosedFiberModuleIso (S := Spec (.of k))
    (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) w

/-- The original closed-fiber multiplicity retains the full exterior-support local length. -/
theorem actualPairClosedFiberLength (w : genericPoints (pairIntegralExterior F G H z)) :
    Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk
        (pairIntegralExteriorInclusion F G H z w.1))
        (F.leftExteriorClosedFiber G H (pairIntegralExteriorInclusion F G H z w.1)) =
      Module.length ((pairIntegralExterior F G H z).presheaf.stalk w.1)
        ((pairIntegralExterior F G H z).presheaf.stalk w.1) :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorGenericClosedFiber_length (S := Spec (.of k))
    (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) w

/-- The original image point's integral closure is taken inside the whole image scheme. -/
abbrev imageIntegralSupport : IntegralClosedSubscheme (F.incidenceMap G).image :=
  IntegralClosedSubscheme.pointClosure ((F.incidenceMap G).toImage z.1)

/-- The inside-image integral support has the correct ambient integral finite image.
Only this proved closed-immersion image identification connects the two supports. -/
theorem imageIntegralSupport_ambientImage :
    (imageIntegralSupport F G z).finiteImage (F.incidenceMap G).imageι =
      IntegralClosedSubscheme.pointClosure (F.incidenceMap G z.1) := by
  rw [imageIntegralSupport, IntegralClosedSubscheme.pointClosure_finiteImage]
  congr 1

/-- The exterior of the integral support inside the whole image, retaining its own nilpotents. -/
abbrev imageIntegralExterior :=
  (imageIntegralSupport F G z).exteriorProduct
    ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
    (H.projection ≫ Z.hom)

/-- The actual integral-image exterior inclusion into the unreduced whole image product. -/
abbrev imageIntegralExteriorInclusion : imageIntegralExterior F G H z ⟶
    F.leftIntermediateImageProduct G H :=
  (imageIntegralSupport F G z).exteriorInclusion
    ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
    (H.projection ≫ Z.hom)

/-- Flat exterior projection recovers the actual point inside the whole image scheme. -/
theorem actualImageProjection (v : genericPoints (imageIntegralExterior F G H z)) :
    pullback.fst
        ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
        (H.projection ≫ Z.hom) (imageIntegralExteriorInclusion F G H z v.1) =
      (F.incidenceMap G).toImage z.1 := by
  simpa only [imageIntegralSupport, IntegralClosedSubscheme.point_pointClosure] using
    (imageIntegralSupport F G z).exteriorGeneric_ambientProjection (S := Spec (.of k))
      ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
      (H.projection ≫ Z.hom) v

/-- The actual target support-product stalk is the whole image-product closed fiber
over the original image point; the whole image-product stalk itself is not replaced. -/
def actualImageClosedFiberEquiv (v : genericPoints (imageIntegralExterior F G H z)) :
    Koszul.coefficientClosedFiber
        ((pullback.fst
          ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
          (H.projection ≫ Z.hom)).stalkMap (imageIntegralExteriorInclusion F G H z v.1)).hom ≃+*
      (imageIntegralExterior F G H z).presheaf.stalk v.1 :=
  (imageIntegralSupport F G z).exteriorGenericClosedFiberEquiv (S := Spec (.of k))
    ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
    (H.projection ≫ Z.hom) v

/-- The target quotient identification is induced by the literal inside-image support inclusion. -/
@[simp] theorem actualImageClosedFiberEquiv_mk
    (v : genericPoints (imageIntegralExterior F G H z))
    (r : (F.leftIntermediateImageProduct G H).presheaf.stalk
      (imageIntegralExteriorInclusion F G H z v.1)) :
    actualImageClosedFiberEquiv F G H z v (Ideal.Quotient.mk _ r) =
      (imageIntegralExteriorInclusion F G H z).stalkMap v.1 r :=
  (imageIntegralSupport F G z).exteriorGenericClosedFiberEquiv_mk (S := Spec (.of k))
    ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
    (H.projection ≫ Z.hom) v r

/-- The target comparison preserves the whole image-product ambient scalar action. -/
theorem actualImageClosedFiberEquiv_scalarSquare
    (v : genericPoints (imageIntegralExterior F G H z)) :
    (actualImageClosedFiberEquiv F G H z v).toRingHom.comp (Ideal.Quotient.mk _) =
      ((imageIntegralExteriorInclusion F G H z).stalkMap v.1).hom :=
  (imageIntegralSupport F G z).exteriorGenericClosedFiberEquiv_scalarSquare
    (S := Spec (.of k))
    ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
    (H.projection ≫ Z.hom) v

/-- The target quotient has the actual support-stalk module,
with its original image-product action. -/
def actualImageClosedFiberModuleIso (v : genericPoints (imageIntegralExterior F G H z)) :
    ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk
        (imageIntegralExteriorInclusion F G H z v.1))
        (Koszul.coefficientClosedFiber
          ((pullback.fst
            ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
            (H.projection ≫ Z.hom)).stalkMap (imageIntegralExteriorInclusion F G H z v.1)).hom) ≅
      (ModuleCat.restrictScalars
        ((imageIntegralExteriorInclusion F G H z).stalkMap v.1).hom).obj
        (ModuleCat.of ((imageIntegralExterior F G H z).presheaf.stalk v.1)
          ((imageIntegralExterior F G H z).presheaf.stalk v.1)) :=
  (imageIntegralSupport F G z).exteriorGenericClosedFiberModuleIso (S := Spec (.of k))
    ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
    (H.projection ≫ Z.hom) v

/-- The target cycle-support multiplicity is its own actual exterior stalk length. -/
theorem actualImageClosedFiberLength (v : genericPoints (imageIntegralExterior F G H z)) :
    Module.length ((F.leftIntermediateImageProduct G H).presheaf.stalk
        (imageIntegralExteriorInclusion F G H z v.1))
        (Koszul.coefficientClosedFiber
          ((pullback.fst
            ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
            (H.projection ≫ Z.hom)).stalkMap (imageIntegralExteriorInclusion F G H z v.1)).hom) =
      Module.length ((imageIntegralExterior F G H z).presheaf.stalk v.1)
        ((imageIntegralExterior F G H z).presheaf.stalk v.1) :=
  (imageIntegralSupport F G z).exteriorGenericClosedFiber_length (S := Spec (.of k))
    ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
    (H.projection ≫ Z.hom) v

end MotivicTest.IntegralExteriorClosedFiber
