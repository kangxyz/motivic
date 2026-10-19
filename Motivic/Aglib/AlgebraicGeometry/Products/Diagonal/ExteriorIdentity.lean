/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.BaseChange
public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.TripleIdeals
public import Motivic.Aglib.RingTheory.RegularSequence.SurjectiveComposition
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.FlatBaseChange

/-!
# Separating the two actual exterior ambient diagonals

The exterior four-factor ambient first imposes the parameter diagonal and
then the original middle diagonal. Both squares are genuinely Cartesian.
Flatness is proved for the ambient maps from the independent smooth factors;
no support-to-middle morphism is assumed flat. The original middle-diagonal
list remains the same literal mapped list in the quotient ambient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.Products

variable {k : Type u} [Field k]
  (X Y Z T : SmoothSite (Spec (.of k)))

/-- The actual parameter pair on the exterior correspondence ambient. -/
abbrev exteriorAmbientParameterPair :=
  correspondenceMiddlePair (SmoothSite.product X T).hom
    (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom ≫
      ProductDiagonal.parameterPair Y.hom T.hom

/-- The literal parameter-diagonal inverse image in the exterior ambient. -/
abbrev exteriorAmbientParameterQuotient :=
  ProductDiagonalBaseChange.parameterQuotient Y.hom T.hom
    (correspondenceMiddlePair (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)

/-- Its actual closed inclusion into the exterior four-factor ambient. -/
abbrev exteriorAmbientParameterInclusion :=
  ProductDiagonalBaseChange.quotientInclusion Y.hom T.hom
    (correspondenceMiddlePair (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)

instance exteriorAmbientParameterPair_flat : Flat (exteriorAmbientParameterPair X Y Z T) := by
  unfold exteriorAmbientParameterPair
  infer_instance

instance exteriorAmbientParameterInclusion_isClosedImmersion :
    IsClosedImmersion (exteriorAmbientParameterInclusion X Y Z T) := inferInstance

/-- The first block is the genuine flat ambient base change of the parameter diagonal. -/
theorem exteriorAmbientParameter_isPullback :
    IsPullback
      (pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T))
      (exteriorAmbientParameterInclusion X Y Z T)
      (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T) :=
  IsPullback.of_hasPullback _ _

/-- The original middle pair after identifying only the parameter coordinates. -/
abbrev exteriorAmbientRemainingPair :=
  ProductDiagonalBaseChange.remainingMap Y.hom T.hom
    (correspondenceMiddlePair (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)

instance exteriorAmbientRemainingPair_flat : Flat (exteriorAmbientRemainingPair X Y Z T) := by
  unfold exteriorAmbientRemainingPair
  infer_instance

/-- Factor the actual triple inclusion through the parameter-diagonal ambient. -/
abbrev exteriorAmbientRemainingInclusion :=
  ProductDiagonalBaseChange.diagonalLift Y.hom T.hom
    (correspondenceMiddlePair (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)
    (correspondenceTripleMiddle (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)
    (correspondenceTripleInclusion (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)
    (correspondenceTriple_isPullback _ _ _)

@[reassoc (attr := simp)]
theorem exteriorAmbientRemainingInclusion_parameterInclusion :
    exteriorAmbientRemainingInclusion X Y Z T ≫ exteriorAmbientParameterInclusion X Y Z T =
      correspondenceTripleInclusion (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom :=
  ProductDiagonalBaseChange.diagonalLift_quotientInclusion _ _ _ _ _ _

/-- The remaining block is literally the original middle diagonal by Cartesian base change. -/
theorem exteriorAmbientRemaining_isPullback :
    IsPullback
      (correspondenceTripleMiddle (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom ≫ pullback.fst Y.hom T.hom)
      (exteriorAmbientRemainingInclusion X Y Z T)
      (pullback.diagonal Y.hom) (exteriorAmbientRemainingPair X Y Z T) :=
  ProductDiagonalBaseChange.diagonalLift_isPullback _ _ _ _ _ _

instance exteriorAmbientRemainingInclusion_isClosedImmersion :
    IsClosedImmersion (exteriorAmbientRemainingInclusion X Y Z T) :=
  MorphismProperty.of_isPullback (exteriorAmbientRemaining_isPullback X Y Z T) inferInstance

/-- The ambient parameter-diagonal kernel has a genuine regular generating list. -/
theorem exteriorAmbientParameter_exists_regular_kernel
    (z : exteriorAmbientParameterQuotient X Y Z T) :
    ∃ t : List ((correspondenceIntersectionAmbient (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom).presheaf.stalk
          (exteriorAmbientParameterInclusion X Y Z T z)),
      IsRegular ((correspondenceIntersectionAmbient (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom).presheaf.stalk
          (exteriorAmbientParameterInclusion X Y Z T z)) t ∧
        RingHom.ker ((exteriorAmbientParameterInclusion X Y Z T).stalkMap z).hom =
          Ideal.ofList t :=
  Diagonal.exists_regular_kernel_of_flat_isPullback
    (exteriorAmbientParameter_isPullback X Y Z T) z
    (Diagonal.exists_regular_kernel_of_smooth T.hom _)

/-- The remaining ambient kernel uses the literal image of any chosen original
middle-diagonal regular kernel list. Its coefficient images need not be regular. -/
theorem exteriorAmbientRemaining_mapped_regular_kernel
    (z : correspondenceTripleProduct (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom
        (pullback.fst Y.hom T.hom
          (correspondenceTripleMiddle (SmoothSite.product X T).hom
            (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom z)))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom
        (pullback.fst Y.hom T.hom
          (correspondenceTripleMiddle (SmoothSite.product X T).hom
            (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom z)))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (pullback.fst Y.hom T.hom
        (correspondenceTripleMiddle (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom z))).hom = Ideal.ofList s) :
    IsRegular ((exteriorAmbientParameterQuotient X Y Z T).presheaf.stalk
      (exteriorAmbientRemainingInclusion X Y Z T z)) (s.map (Diagonal.baseChangeStalkMap
      (exteriorAmbientRemaining_isPullback X Y Z T) z).hom) ∧
      RingHom.ker ((exteriorAmbientRemainingInclusion X Y Z T).stalkMap z).hom =
        Ideal.ofList (s.map (Diagonal.baseChangeStalkMap
          (exteriorAmbientRemaining_isPullback X Y Z T) z).hom) :=
  Diagonal.mapped_equations_regular_kernel
    (exteriorAmbientRemaining_isPullback X Y Z T) z hs hker

end AlgebraicGeometry.Scheme.Products
