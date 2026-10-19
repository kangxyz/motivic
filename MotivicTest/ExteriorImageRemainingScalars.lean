/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Image.RemainingScalars
public import MotivicTest.IntegralGenericFiniteImage

/-!
# The scalar identity on the original imageSupport over an arbitrary field

These consumers use the original `F`, `G`, `H`,
`imageSupport`, `imageExteriorInclusion`, and the given generator `P` with
the same explicit image-ideal equality. Both statements display the literal
closed-immersion, coefficient, and exterior-isomorphism stalk maps. The
quotient is by the literal stalk-map kernel; its equality with the original
ideal-sheaf stalk is separately supplied by `ker_stalk`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (stalkQuotientKerEquiv)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Intersection (coefficientStalkMap)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceTripleInclusion)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.ExteriorImageComponentGeometry
open MotivicTest.IntegralGenericFiniteImage

universe u

namespace MotivicTest.ExteriorImageRemainingScalars

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))
  (P : FiniteCorrespondenceGenerator X.hom Z.hom)
  (hC : ((imageSupport F G z).val.subschemeι ≫ (F.incidenceMap G).imageι).ker = P.val)
  (w : P.incidence H)
  (s : List ((pullback Z.hom Z.hom).presheaf.stalk
    (F.leftImageMiddlePair G H (imageExteriorInclusion F G H z
      (remainingToExterior F G H (imageSupport F G z) P hC w)))))

/-- The original target list maps to the original ambient-list coefficient image. -/
theorem originalImage_remaining_scalar :
    let e := remainingToExterior F G H (imageSupport F G z) P hC w
    let r := remainingExteriorAmbientList F G H (imageSupport F G z) P hC w s
    let a := coefficientStalkMap
      (correspondenceTripleInclusion X.hom Z.hom W.hom) (P.incidenceInclusion H w)
      (P.supportProductInclusion H)
      ((exteriorIso F G H (imageSupport F G z) P hC).hom e)
      (remainingExterior_ambientPoint F G H (imageSupport F G z) P hC w)
    (F.leftTargetRemainingList G H (imageExteriorInclusion F G H z e) s).map
        ((imageExteriorInclusion F G H z).stalkMap e).hom =
      (r.map a.hom).map
        ((exteriorIso F G H (imageSupport F G z) P hC).hom.stalkMap e).hom :=
  remainingExterior_list_scalar_identity F G H (imageSupport F G z) P hC w s

/-- The same original imageSupport list retains its actual immersion-kernel quotient. -/
theorem originalImage_remaining_quotient :
    let e := remainingToExterior F G H (imageSupport F G z) P hC w
    let r := remainingExteriorAmbientList F G H (imageSupport F G z) P hC w s
    let a := coefficientStalkMap
      (correspondenceTripleInclusion X.hom Z.hom W.hom) (P.incidenceInclusion H w)
      (P.supportProductInclusion H)
      ((exteriorIso F G H (imageSupport F G z) P hC).hom e)
      (remainingExterior_ambientPoint F G H (imageSupport F G z) P hC w)
    ((F.leftTargetRemainingList G H (imageExteriorInclusion F G H z e) s).map
        (Ideal.Quotient.mk
          (RingHom.ker ((imageExteriorInclusion F G H z).stalkMap e).hom))).map
        (stalkQuotientKerEquiv (imageExteriorInclusion F G H z) e) =
      (r.map a.hom).map
        ((exteriorIso F G H (imageSupport F G z) P hC).hom.stalkMap e).hom :=
  remainingExterior_list_quotient_identity F G H (imageSupport F G z) P hC w s

omit P hC w s in
/-- The original immersion-ideal stalk equals its stalk-map kernel by a theorem. -/
theorem originalImage_exterior_kernel (e : imageExterior F G H z) :
    (imageExteriorInclusion F G H z).ker.stalk (imageExteriorInclusion F G H z e) =
      RingHom.ker ((imageExteriorInclusion F G H z).stalkMap e).hom :=
  (imageExteriorInclusion F G H z).ker_stalk e

end MotivicTest.ExteriorImageRemainingScalars
