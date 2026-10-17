/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityIncidenceProjection

/-!
# Original incidence Tor from the original middle list

Any chosen regular kernel list for the original middle diagonal gives the
actual incidence Tor length after its literal action on the coefficient
stalk. This retains every degree and imposes no regularity on the coefficient
images of that list.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The two actual routes from the original middle diagonal stalk to coefficients agree. -/
theorem incidenceMiddleStalkMap_comp (w : A.incidence B) :
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback X.hom Y.hom Z.hom)
        (A.incidenceInclusion B w) ≫
      Intersection.coefficientStalkMap (correspondenceTripleInclusion X.hom Y.hom Z.hom)
        (A.incidenceInclusion B w) (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    Diagonal.baseChangeStalkMap (A.originalIncidence_middle_isPullback B) w := by
  change StalkTransport.pointedMap (correspondenceMiddlePair X.hom Y.hom Z.hom) _ _
      (congrArg (fun m => m (A.incidenceInclusion B w))
        (correspondenceTriple_isPullback X.hom Y.hom Z.hom).w) ≫
      StalkTransport.pointedMap (A.supportProductInclusion B) _ _
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (A.originalCoefficientMiddlePair B) _ _
      (congrArg (fun m => m w) (A.originalIncidence_middle_isPullback B).w)
  exact StalkTransport.pointedMap_comp _ _ _ _ _ _ _

/-- Actual incidence Tor has the length of the original middle Koszul complex
on the actual support-product stalk, with the same equations and scalar action. -/
theorem incidenceTor_length_eq_middleKoszul (w : A.incidence B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom
        (correspondenceTripleMiddle X.hom Y.hom Z.hom (A.incidenceInclusion B w)))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom
        (correspondenceTripleMiddle X.hom Y.hom Z.hom (A.incidenceInclusion B w)))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (correspondenceTripleMiddle X.hom Y.hom Z.hom (A.incidenceInclusion B w))).hom =
        Ideal.ofList s) (n : ℕ) :
    Module.length (A.incidenceAmbientStalk B w) (A.incidenceTor B w n) =
      Module.length ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w))
        ((Koszul.coefficientComplex
          (ModuleCat.of ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w))
            ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w)))
          (s.map (Diagonal.baseChangeStalkMap
            (A.originalIncidence_middle_isPullback B) w).hom)).homology n) := by
  obtain ⟨hregular, hkernel⟩ := Diagonal.mapped_equations_regular_kernel
    (correspondenceTriple_isPullback X.hom Y.hom Z.hom) (A.incidenceInclusion B w) hs hker
  refine (Intersection.torIsoHomology (correspondenceTripleInclusion X.hom Y.hom Z.hom)
    (A.incidenceInclusion B w) (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
    (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)
    _ hkernel hregular n).toLinearEquiv.length_eq.trans ?_
  refine (Koszul.coordinateHomology_length
    (Intersection.coefficientStalkMap (correspondenceTripleInclusion X.hom Y.hom Z.hom)
      (A.incidenceInclusion B w) (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
      (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)).hom
    (Intersection.coefficientStalkMap_surjective _ _ _ _
      (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)) _ n).trans ?_
  have hlists :
      (s.map (Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback X.hom Y.hom Z.hom)
        (A.incidenceInclusion B w)).hom).map
          (Intersection.coefficientStalkMap (correspondenceTripleInclusion X.hom Y.hom Z.hom)
            (A.incidenceInclusion B w) (A.supportProductInclusion B)
            (A.incidenceToSupportProduct B w)
            (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)).hom =
      s.map (Diagonal.baseChangeStalkMap (A.originalIncidence_middle_isPullback B) w).hom := by
    simp only [List.map_map]
    congr 1
    funext r
    exact ConcreteCategory.congr_hom (A.incidenceMiddleStalkMap_comp B w) r
  exact congrArg (fun l : List ((A.supportProduct B).presheaf.stalk
      (A.incidenceToSupportProduct B w)) =>
    Module.length ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w))
      ((Koszul.coefficientComplex
        (ModuleCat.of ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w))
          ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w))) l).homology n))
    hlists

end Motivic.FiniteCorrespondenceGenerator
