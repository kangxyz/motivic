/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RightExteriorImageComponentGeometry
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageRemainingLiftCases

/-!
# Consumers of the original right image support and remaining Y square

These source-only consumers instantiate the geometry at every original G,H
generic label, its actual image point closure, and the original smooth component
generator. The required equality is the accepted image-ideal theorem, not an
assumed carrier equality or an unrelated support isomorphism.

The actual full shared exterior, both projections, original source and remaining
Y maps, Cartesian square, closed immersion, and genericity are retained over an
arbitrary field. Scalar consumers use the same actual Y list through the literal
immersion, the constructed exterior isomorphism, and original coefficient map.
No list regularity, exterior reducedness, or flatness of F over Y is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.RightExteriorImageComponentGeometry
open IntegralClosedSubscheme

universe u

namespace MotivicTest.RightExteriorImageComponentGeometry

section GeneralSupport

variable {S Y Z W : Scheme.{u}} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (G : FiniteCorrespondenceGenerator g h) (H : FiniteCorrespondenceGenerator h i)
  (C : IntegralClosedSubscheme (G.incidenceMap H).image)
  (P : FiniteCorrespondenceGenerator g i)
  (hC : (C.val.subschemeι ≫ (G.incidenceMap H).imageι).ker = P.val)

/-- The source-support identity is available without any smooth-site hypotheses. -/
theorem generalSupport_source :
    ExteriorImageComponentGeometry.supportInImage G H C P hC ≫
        (G.incidenceMap H).imageι ≫ pullback.fst g i = P.projection :=
  ExteriorImageComponentGeometry.supportInImage_source G H C P hC

end GeneralSupport

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (G.incidence H))

/-- This is the original image point closure, indexed by the original G,H label. -/
abbrev imageSupport : IntegralClosedSubscheme (G.incidenceMap H).image :=
  pointClosure ((G.incidenceMap H).toImage z.1)

/-- The exact ideal equality comes from the original finite-image theorem. -/
theorem actualImageKernel :
    ((imageSupport G H z).val.subschemeι ≫ (G.incidenceMap H).imageι).ker =
      (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z).val :=
  ExteriorImageComponentGeometry.smoothComponent_imageKernel k G H z

/-- The shared full exterior is the original first support times the component generator. -/
abbrev actualExteriorIso : F.rightImageComponentExterior G H (imageSupport G H z) ≅
    F.supportProduct (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) :=
  exteriorIso F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
    (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

/-- The first exterior projection fixes F.scheme, rather than a reduced replacement. -/
@[reassoc] theorem actualExteriorIso_fst :
    (actualExteriorIso F G H z).hom ≫
      pullback.fst (F.targetProjection ≫ Y.hom)
        ((G.smoothIncidenceComponentGenerator
          (X := Y) (Y := Z) (Z := W) k H z).projection ≫ Y.hom) =
    pullback.fst (F.targetProjection ≫ Y.hom)
      ((imageSupport G H z).val.subschemeι ≫ (G.incidenceMap H).imageι ≫
        pullback.fst Y.hom W.hom ≫ Y.hom) :=
  exteriorIso_fst F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
    (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

/-- The second exterior projection uses the accepted literal support isomorphism. -/
@[reassoc] theorem actualExteriorIso_snd :
    (actualExteriorIso F G H z).hom ≫
      pullback.snd (F.targetProjection ≫ Y.hom)
        ((G.smoothIncidenceComponentGenerator
          (X := Y) (Y := Z) (Z := W) k H z).projection ≫ Y.hom) =
    pullback.snd (F.targetProjection ≫ Y.hom)
      ((imageSupport G H z).val.subschemeι ≫ (G.incidenceMap H).imageι ≫
        pullback.fst Y.hom W.hom ≫ Y.hom) ≫
      (ExteriorImageComponentGeometry.supportIso G H (imageSupport G H z)
        (G.smoothIncidenceComponentGenerator
          (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z)).hom :=
  exteriorIso_snd F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
    (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

/-- The original remaining Y pair is preserved by the shared full exterior inclusion. -/
@[reassoc] theorem actualExterior_middlePair :
    F.rightImageComponentExteriorInclusion G H (imageSupport G H z) ≫
        F.rightImageMiddlePair G H =
      (actualExteriorIso F G H z).hom ≫
        F.supportProductInclusion (G.smoothIncidenceComponentGenerator
          (X := Y) (Y := Z) (Z := W) k H z) ≫
          correspondenceMiddlePair X.hom Y.hom W.hom :=
  exteriorInclusion_middlePair F G H (imageSupport G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z)

/-- The original incidence with the actual component maps into the right image incidence. -/
abbrev actualRemainingToImage :
    F.incidence (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) ⟶ F.rightImageIncidence G H :=
  remainingToImage F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
    (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

/-- The original remaining incidence uses the shared full exterior, including nilpotents. -/
abbrev actualRemainingToExterior :
    F.incidence (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) ⟶
      F.rightImageComponentExterior G H (imageSupport G H z) :=
  remainingToExterior F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
    (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

/-- The first remaining projection is the original incidence projection to F. -/
@[reassoc] theorem actualRemainingToImage_fst :
    actualRemainingToImage F G H z ≫
      pullback.fst F.targetProjection
        ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom) =
      F.incidenceFst (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) :=
  remainingToImage_fst F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
    (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

/-- The second remaining projection retains the actual whole-image support immersion. -/
@[reassoc] theorem actualRemainingToImage_snd :
    actualRemainingToImage F G H z ≫
      pullback.snd F.targetProjection
        ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom) =
      F.incidenceSnd (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) ≫
        ExteriorImageComponentGeometry.supportInImage G H (imageSupport G H z)
          (G.smoothIncidenceComponentGenerator
            (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z) :=
  remainingToImage_snd F G H (imageSupport G H z) (G.smoothIncidenceComponentGenerator
    (X := Y) (Y := Z) (Z := W) k H z)
    (actualImageKernel G H z)

/-- The same original X source projection is used before and after the image map. -/
@[reassoc] theorem actualRemainingToImage_source :
    actualRemainingToImage F G H z ≫ F.rightImageIncidenceSource G H =
      F.incidenceSource (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) :=
  remainingToImage_source F G H (imageSupport G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z)

/-- The literal remaining square is Cartesian, with no reduction of either exterior. -/
theorem actualRemaining_isPullback :
    IsPullback (actualRemainingToImage F G H z) (actualRemainingToExterior F G H z)
      (F.rightImageIncidenceInclusion G H)
      (F.rightImageComponentExteriorInclusion G H (imageSupport G H z)) :=
  remainingToImage_isPullback F G H (imageSupport G H z)
    (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z)

/-- Closed immersion follows from the genuine Cartesian exterior-support square. -/
example : IsClosedImmersion (actualRemainingToImage F G H z) := inferInstance

/-- Original incidence-source genericity supplies the needed generic-image statement. -/
theorem actualRemaining_generic
    (w : genericPoints (F.incidence (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z))) :
    actualRemainingToImage F G H z w.1 ∈ genericPoints (F.rightImageIncidence G H) :=
  remainingToImage_mem_genericPoints F G H (imageSupport G H z)
    (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z) w.1 w.2

variable (w : F.incidence (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z))

/-- The actual image point is determined by the proved remaining square. -/
theorem actualRemaining_imagePoint :
    F.rightImageIncidenceInclusion G H (actualRemainingToImage F G H z w) =
      F.rightImageComponentExteriorInclusion G H (imageSupport G H z)
        (actualRemainingToExterior F G H z w) :=
  remainingExterior_imagePoint F G H (imageSupport G H z)
    (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z) w

/-- The diagonal point is the original incidence's Y point in the original triple ambient. -/
theorem actualRemaining_middlePoint :
    F.rightImageMiddlePair G H
        (F.rightImageComponentExteriorInclusion G H (imageSupport G H z)
          (actualRemainingToExterior F G H z w)) =
      pullback.diagonal Y.hom
        (correspondenceTripleMiddle X.hom Y.hom W.hom
          (F.incidenceInclusion (G.smoothIncidenceComponentGenerator
            (X := Y) (Y := Z) (Z := W) k H z) w)) :=
  remainingExterior_middlePoint F G H (imageSupport G H z)
    (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z) w

/-- The actual coefficient stalk map occurs in the original remaining scalar square. -/
theorem actualRemaining_scalarSquare :
    let C := imageSupport G H z
    let P := G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z
    let e := actualRemainingToExterior F G H z w
    let a := Intersection.coefficientStalkMap
      (correspondenceTripleInclusion X.hom Y.hom W.hom) (F.incidenceInclusion P w)
      (F.supportProductInclusion P) ((actualExteriorIso F G H z).hom e)
      (remainingExterior_ambientPoint F G H C P (actualImageKernel G H z) w)
    (F.rightImageMiddlePair G H).stalkMap
        (F.rightImageComponentExteriorInclusion G H C e) ≫
      (F.rightImageComponentExteriorInclusion G H C).stalkMap e =
    remainingExteriorAmbientStalkMap F G H C P (actualImageKernel G H z) w ≫
      a ≫ (actualExteriorIso F G H z).hom.stalkMap e :=
  remainingExterior_stalkSquare F G H (imageSupport G H z)
    (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z) w

variable (s : List ((pullback Y.hom Y.hom).presheaf.stalk
  (F.rightImageMiddlePair G H
    (F.rightImageComponentExteriorInclusion G H (imageSupport G H z)
      (actualRemainingToExterior F G H z w)))))

/-- The same arbitrary original Y list retains its literal immersion-kernel quotient. -/
theorem actualRemaining_listQuotient :
    let C := imageSupport G H z
    let P := G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z
    let e := actualRemainingToExterior F G H z w
    let r := remainingExteriorAmbientList F G H C P (actualImageKernel G H z) w s
    let a := Intersection.coefficientStalkMap
      (correspondenceTripleInclusion X.hom Y.hom W.hom) (F.incidenceInclusion P w)
      (F.supportProductInclusion P) ((actualExteriorIso F G H z).hom e)
      (remainingExterior_ambientPoint F G H C P (actualImageKernel G H z) w)
    ((F.rightTargetRemainingList G H
        (F.rightImageComponentExteriorInclusion G H C e) s).map
        (Ideal.Quotient.mk
          (RingHom.ker ((F.rightImageComponentExteriorInclusion G H C).stalkMap e).hom))).map
        (stalkQuotientKerEquiv (F.rightImageComponentExteriorInclusion G H C) e) =
      (r.map a.hom).map ((actualExteriorIso F G H z).hom.stalkMap e).hom :=
  remainingExterior_list_quotient_identity F G H (imageSupport G H z)
    (G.smoothIncidenceComponentGenerator
      (X := Y) (Y := Z) (Z := W) k H z) (actualImageKernel G H z) w s

omit w s in
/-- The actual ideal-sheaf stalk agrees with the kernel used in the quotient scalar identity. -/
theorem actualExterior_kernel (e : F.rightImageComponentExterior G H (imageSupport G H z)) :
    (F.rightImageComponentExteriorInclusion G H (imageSupport G H z)).ker.stalk
        (F.rightImageComponentExteriorInclusion G H (imageSupport G H z) e) =
      RingHom.ker
        ((F.rightImageComponentExteriorInclusion G H (imageSupport G H z)).stalkMap e).hom :=
  (F.rightImageComponentExteriorInclusion G H (imageSupport G H z)).ker_stalk e

end MotivicTest.RightExteriorImageComponentGeometry
