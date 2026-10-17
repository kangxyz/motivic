/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBasePencilMaps
/-! # The pencil maps have the literal refined projections and original target map -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable (k : Type u) [Field k] (R : Type u) [CommRing R] (ι : Type u)
  {X Y A C T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine T]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] (a : A ⟶ X) [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) (j : Y ⟶ C)
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (U : X.Opens) (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme] [IsAffine (boundaryBaseSourceOpen q U V).toScheme]
example : (boundaryBasePencilAlpha k R ι t q p a f j hj U V).left =
    pullback.fst (boundaryBaseCoverMap q p U V) (boundaryBaseCoverMap q a U V) := rfl
example : (boundaryBasePencilBeta k R ι t q p a f j hj U V).left =
    pullback.snd (boundaryBaseCoverMap q p U V) (boundaryBaseCoverMap q a U V) := rfl
example (v : T ⟶ C) [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
    (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j) :
    (boundaryBasePencilGraph k R ι t q p a f j hj U V v φ hφ).left =
      boundaryBaseOverlapTarget q p a U V (f ≫ toSpec R ι) j hj v φ hφ := rfl
#print axioms boundaryBasePencilAlpha
#print axioms boundaryBasePencilBeta
#print axioms boundaryBasePencilGraph
end AlgebraicGeometry.Scheme.Hom
