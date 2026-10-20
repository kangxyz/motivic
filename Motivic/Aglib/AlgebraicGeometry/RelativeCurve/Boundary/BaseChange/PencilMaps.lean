/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilSites
/-! # The original scheme restrictions as actual smooth-site pencil maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
universe u
namespace AlgebraicGeometry.Scheme.Hom
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R] (ι : Type u)
  {X Y A C T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine A]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] (a : A ⟶ X) [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) (j : Y ⟶ C)
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (U : X.Opens) (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme] [IsAffine (boundaryBaseSourceOpen q U V).toScheme]

/-- The lambda-source smooth-site map for the pencil after restriction to the base open. -/
abbrev boundaryBasePencilAlpha :=
  RelativeCurvePencil.relativeAlpha k (boundaryBaseFieldMap V t)
    (boundaryBaseProjectiveMap R ι f V ≫ toSpec Γ(V.toScheme, ⊤) ι)
    (boundaryBaseCoverInclusion q p (f ≫ toSpec R ι) j hj U V)
    (pullback.fst (boundaryBaseCoverMap q p U V) (boundaryBaseCoverMap q a U V))

/-- The psi-source smooth-site map for the pencil after restriction to the base open. -/
abbrev boundaryBasePencilBeta :=
  RelativeCurvePencil.relativeBeta k (boundaryBaseFieldMap V t)
    (boundaryBaseSpecProjection q U V)
    (boundaryBaseProjectiveMap R ι f V ≫ toSpec Γ(V.toScheme, ⊤) ι)
    (boundaryBaseCoverInclusion q p (f ≫ toSpec R ι) j hj U V)
    (boundaryBaseCoverMap q a U V)
    (pullback.fst (boundaryBaseCoverMap q p U V) (boundaryBaseCoverMap q a U V))
    (boundaryBaseCoverMap q p U V)
    (boundaryBaseCoverInclusion_spec_projection R ι q p f j hj U V)
    (pullback.snd (boundaryBaseCoverMap q p U V) (boundaryBaseCoverMap q a U V))
    pullback.condition

/-- The retained-target smooth-site map for the pencil after restriction to the base open. -/
abbrev boundaryBasePencilGraph [IsAffine T] (v : T ⟶ C)
    [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
    (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j) :=
  RelativeCurvePencil.relativeGraphMap k (boundaryBaseFieldMap V t)
    (boundaryBaseProjectiveMap R ι f V ≫ toSpec Γ(V.toScheme, ⊤) ι)
    (boundaryBaseCoverInclusion q p (f ≫ toSpec R ι) j hj U V)
    (pullback.fst (boundaryBaseCoverMap q p U V) (boundaryBaseCoverMap q a U V))
    (boundaryBaseRetainedTarget (f ≫ toSpec R ι) V v)
    (boundaryBaseOverlapTarget q p a U V (f ≫ toSpec R ι) j hj v φ hφ)
    (boundaryBaseOverlapTarget_inclusion q p a U V (f ≫ toSpec R ι) j hj v φ hφ)
end AlgebraicGeometry.Scheme.Hom
