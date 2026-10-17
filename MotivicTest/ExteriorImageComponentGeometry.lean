/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageComponentGeometry
public import MotivicTest.IntegralExteriorCyclePushforward

/-!
# The original image component and its actual remaining incidence

These consumers use the imageSupport and imageExterior already occurring in
the global exterior cycle pushforward. The generator is literally the original
smoothIncidenceComponentGenerator, with the image-ideal equality derived from
the accepted ambient finite-image equality. No new comparison datum is supplied.

The full imageExterior is identified with that generator's full support product
with H. Its Cartesian intersection with the original whole-image incidence is
the original generator incidence. Both projections and the original middle-stalk
list, through the actual immersion quotient, are retained over arbitrary fields.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open MotivicTest.IntegralGenericFiniteImage
open MotivicTest.IntegralExteriorCyclePushforward

universe u

namespace MotivicTest.ExteriorImageComponentGeometry

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

/-- The actual ambient finite-image equality supplies the required ideal equality. -/
theorem actualImageKernel :
    ((imageSupport F G z).val.subschemeι ≫ (F.incidenceMap G).imageι).ker =
      (F.smoothIncidenceComponentGenerator k G z).val :=
  congrArg Subtype.val (imageSupport_ambient_eq_smoothIncidenceComponent F G z)

/-- The original inside-image integral support is the original component generator. -/
abbrev actualSupportIso : (imageSupport F G z).val.subscheme ≅
    (F.smoothIncidenceComponentGenerator k G z).scheme :=
  Motivic.ExteriorImageComponentGeometry.supportIso F G (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The constructed support isomorphism preserves the original ambient closed immersion. -/
@[reassoc] theorem actualSupportIso_ambient :
    (actualSupportIso F G z).hom ≫ (F.smoothIncidenceComponentGenerator k G z).inclusion =
      (imageSupport F G z).val.subschemeι ≫ (F.incidenceMap G).imageι :=
  Motivic.ExteriorImageComponentGeometry.supportIso_ambient F G (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The actual image exterior is the generator's full support product with H. -/
abbrev actualExteriorIso : imageExterior F G H z ≅
    (F.smoothIncidenceComponentGenerator k G z).supportProduct H :=
  Motivic.ExteriorImageComponentGeometry.exteriorIso F G H (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The first projection is the actual component-support isomorphism. -/
@[reassoc] theorem actualExteriorIso_fst :
    (actualExteriorIso F G H z).hom ≫
      pullback.fst ((F.smoothIncidenceComponentGenerator k G z).targetProjection ≫ Z.hom)
        (H.projection ≫ Z.hom) =
    pullback.fst ((imageSupport F G z).val.subschemeι ≫ imageStructure F G)
      (H.projection ≫ Z.hom) ≫ (actualSupportIso F G z).hom :=
  Motivic.ExteriorImageComponentGeometry.exteriorIso_fst F G H (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The third support and its projection are literally unchanged. -/
@[reassoc] theorem actualExteriorIso_snd :
    (actualExteriorIso F G H z).hom ≫
      pullback.snd ((F.smoothIncidenceComponentGenerator k G z).targetProjection ≫ Z.hom)
        (H.projection ≫ Z.hom) =
    pullback.snd ((imageSupport F G z).val.subschemeι ≫ imageStructure F G)
      (H.projection ≫ Z.hom) :=
  Motivic.ExteriorImageComponentGeometry.exteriorIso_snd F G H (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The two actual middle maps commute through the constructed exterior isomorphism. -/
@[reassoc] theorem actualExteriorIso_middlePair :
    imageExteriorInclusion F G H z ≫ F.leftImageMiddlePair G H =
      (actualExteriorIso F G H z).hom ≫
        (F.smoothIncidenceComponentGenerator k G z).supportProductInclusion H ≫
          correspondenceMiddlePair X.hom Z.hom W.hom :=
  Motivic.ExteriorImageComponentGeometry.exteriorInclusion_middlePair F G H (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The component's original incidence maps into the whole image's original incidence. -/
abbrev actualRemainingToImage :
    (F.smoothIncidenceComponentGenerator k G z).incidence H ⟶ F.leftImageIncidence G H :=
  Motivic.ExteriorImageComponentGeometry.remainingToImage F G H (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The first remaining projection is the original generator point included in the whole image. -/
@[reassoc] theorem actualRemainingToImage_fst :
    actualRemainingToImage F G H z ≫
      pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom) H.projection =
    (F.smoothIncidenceComponentGenerator k G z).incidenceFst H ≫
      (actualSupportIso F G z).inv ≫ (imageSupport F G z).val.subschemeι :=
  Motivic.ExteriorImageComponentGeometry.remainingToImage_fst
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z)

/-- The second remaining projection is the original third-support point. -/
@[reassoc] theorem actualRemainingToImage_snd :
    actualRemainingToImage F G H z ≫
      pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom) H.projection =
    (F.smoothIncidenceComponentGenerator k G z).incidenceSnd H :=
  Motivic.ExteriorImageComponentGeometry.remainingToImage_snd
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z)

/-- The component incidence and whole image incidence use the identical original X projection. -/
@[reassoc] theorem actualRemainingToImage_source :
    actualRemainingToImage F G H z ≫ F.leftImageIncidenceSource G H =
      (F.smoothIncidenceComponentGenerator k G z).incidenceSource H :=
  Motivic.ExteriorImageComponentGeometry.remainingToImage_source
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z)

/-- Every actual component-incidence generic maps to a whole image-incidence generic. -/
theorem actualRemainingToImage_mem_genericPoints
    (w : (F.smoothIncidenceComponentGenerator k G z).incidence H)
    (hw : w ∈ genericPoints ((F.smoothIncidenceComponentGenerator k G z).incidence H)) :
    actualRemainingToImage F G H z w ∈ genericPoints (F.leftImageIncidence G H) :=
  Motivic.ExteriorImageComponentGeometry.remainingToImage_mem_genericPoints k
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z) w hw

/-- The same original incidence maps into the full, possibly nonreduced image exterior. -/
abbrev actualRemainingToExterior :
    (F.smoothIncidenceComponentGenerator k G z).incidence H ⟶ imageExterior F G H z :=
  (F.smoothIncidenceComponentGenerator k G z).incidenceToSupportProduct H ≫
    (actualExteriorIso F G H z).inv

/-- The remaining incidence square is genuinely Cartesian in schemes. -/
theorem actualRemaining_isPullback :
    IsPullback (actualRemainingToImage F G H z) (actualRemainingToExterior F G H z)
      (F.leftImageIncidenceInclusion G H) (imageExteriorInclusion F G H z) :=
  Motivic.ExteriorImageComponentGeometry.remainingToImage_isPullback F G H (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The actual map of remaining incidences is a closed immersion. -/
instance actualRemainingToImage_isClosedImmersion :
    IsClosedImmersion (actualRemainingToImage F G H z) :=
  Motivic.ExteriorImageComponentGeometry.remainingToImage_isClosedImmersion
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z)

/-- The actual component's full incidence Tor cycle has no coefficient away
from generic points of the final whole image incidence. -/
theorem actualRemainingTorCycle_finitePushforward_offGeneric
    (y : F.leftImageIncidence G H) (hy : y ∉ genericPoints (F.leftImageIncidence G H)) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (actualRemainingToImage F G H z)
        (IntegralCycle.ofGenericCoefficients
          ((F.smoothIncidenceComponentGenerator k G z).incidence H)
          ((F.smoothIncidenceComponentGenerator k G z).incidenceTorCoefficient
            (S := Spec (.of k)) H))) y = 0 :=
  Motivic.ExteriorImageComponentGeometry.remainingToImage_finitePushforward_offGeneric k
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z) _ y hy

/-- The actual pullback of the original two inclusions is the original component incidence. -/
abbrev actualRemainingPullbackIso :
    pullback (imageExteriorInclusion F G H z) (F.leftImageIncidenceInclusion G H) ≅
      (F.smoothIncidenceComponentGenerator k G z).incidence H :=
  Motivic.ExteriorImageComponentGeometry.remainingPullbackIso F G H (imageSupport F G z)
    (F.smoothIncidenceComponentGenerator k G z) (actualImageKernel F G z)

/-- The pullback isomorphism preserves the original component-exterior projection. -/
@[reassoc] theorem actualRemainingPullbackIso_exterior :
    (actualRemainingPullbackIso F G H z).hom ≫ actualRemainingToExterior F G H z =
      pullback.fst (imageExteriorInclusion F G H z) (F.leftImageIncidenceInclusion G H) :=
  Motivic.ExteriorImageComponentGeometry.remainingPullbackIso_exterior
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z)

/-- The pullback isomorphism preserves the original whole-image incidence projection. -/
@[reassoc] theorem actualRemainingPullbackIso_image :
    (actualRemainingPullbackIso F G H z).hom ≫ actualRemainingToImage F G H z =
      pullback.snd (imageExteriorInclusion F G H z) (F.leftImageIncidenceInclusion G H) :=
  Motivic.ExteriorImageComponentGeometry.remainingPullbackIso_image
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z)

/-- The equality of original middle points is induced by the proved scheme-map square. -/
theorem actualExterior_middlePoint (e : imageExterior F G H z) :
    F.leftImageMiddlePair G H (imageExteriorInclusion F G H z e) =
      ((F.smoothIncidenceComponentGenerator k G z).supportProductInclusion H ≫
        correspondenceMiddlePair X.hom Z.hom W.hom) ((actualExteriorIso F G H z).hom e) :=
  Motivic.ExteriorImageComponentGeometry.exterior_middlePoint
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z) e

/-- The original middle list is transported through the actual immersion quotient,
with the original middle point and the constructed exterior stalk isomorphism. -/
theorem actualExterior_middleList_quotient (e : imageExterior F G H z)
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (imageExteriorInclusion F G H z e)))) :
    ((s.map ((F.leftImageMiddlePair G H).stalkMap
        (imageExteriorInclusion F G H z e)).hom).map
        (Ideal.Quotient.mk (RingHom.ker ((imageExteriorInclusion F G H z).stalkMap e).hom))).map
        (stalkQuotientKerEquiv (imageExteriorInclusion F G H z) e) =
      (s.map (StalkTransport.pointedMap
        ((F.smoothIncidenceComponentGenerator k G z).supportProductInclusion H ≫
          correspondenceMiddlePair X.hom Z.hom W.hom)
        ((actualExteriorIso F G H z).hom e)
        (F.leftImageMiddlePair G H (imageExteriorInclusion F G H z e))
        (actualExterior_middlePoint F G H z e)).hom).map
        (((actualExteriorIso F G H z).hom).stalkMap e).hom :=
  Motivic.ExteriorImageComponentGeometry.exterior_middleList_quotient
    F G H (imageSupport F G z) (F.smoothIncidenceComponentGenerator k G z)
    (actualImageKernel F G z) e s

end MotivicTest.ExteriorImageComponentGeometry
