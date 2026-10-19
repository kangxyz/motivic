/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.ExteriorIdentity
public import Motivic.Aglib.AlgebraicGeometry.Simplex.ExteriorGeometry

/-! # The actual simplex exterior ambient has two Cartesian diagonal blocks -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.ExteriorIdentityAmbientDiagonal

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))

example : Flat (_root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientRemainingPair X Y Z T) :=
    inferInstance

example :
    _root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientRemainingInclusion X Y Z T ≫
        _root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientParameterInclusion X Y Z T =
      _root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleInclusion (SmoothSite.product X
          T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom :=
  _root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientRemainingInclusion_parameterInclusion X Y
      Z T

example :
    IsPullback
      (_root_.AlgebraicGeometry.Scheme.Products.correspondenceTripleMiddle (SmoothSite.product X
          T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom ≫ pullback.fst Y.hom T.hom)
      (_root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientRemainingInclusion X Y Z T)
      (pullback.diagonal Y.hom)
          (_root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientRemainingPair X Y Z T) :=
  _root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientRemaining_isPullback X Y Z T

example (n : ℕ) :
    Flat (_root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientRemainingPair X Y Z
        (_root_.AlgebraicSimplex.smoothSiteObj k n)) :=
  inferInstance

example (z : _root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientParameterQuotient X Y Z T) :
    ∃ t : List ((_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient
        (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom).presheaf.stalk
          (_root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientParameterInclusion X Y Z T z)),
      RingTheory.Sequence.IsRegular
        ((_root_.AlgebraicGeometry.Scheme.Products.correspondenceIntersectionAmbient
            (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom).presheaf.stalk
            (_root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientParameterInclusion X Y Z T z))
                t ∧
        RingHom.ker ((_root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientParameterInclusion X Y
            Z T).stalkMap z).hom =
          Ideal.ofList t :=
  _root_.AlgebraicGeometry.Scheme.Products.exteriorAmbientParameter_exists_regular_kernel X Y Z T z

end MotivicTest.ExteriorIdentityAmbientDiagonal
