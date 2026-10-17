/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBasePuncturedSquare
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseSourceBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CorrespondenceSites
/-! # Native affine and smooth objects of the constructed same-base pencil refinement -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y A : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X) (a : A ⟶ X)
  (U : X.Opens) (V : S.Opens)

instance boundaryBaseCoverOpen_affine_instance [IsAffine X] [IsAffine Y]
    [IsAffine (boundaryBaseSourceOpen q U V).toScheme] :
    IsAffine (boundaryBaseCoverOpen q p U V).toScheme := by
  apply boundaryBaseCoverOpen_affine q p U V
  simpa only [Scheme.Opens.opensRange_ι] using
    isAffineOpen_opensRange (boundaryBaseSourceOpen q U V).ι

instance boundaryBaseOverlap_affine_instance [IsAffine X] [IsAffine Y] [IsAffine A]
    [IsAffine (boundaryBaseSourceOpen q U V).toScheme] :
    IsAffine (boundaryBaseOverlap q p a U V) := by
  dsimp [boundaryBaseOverlap]
  infer_instance

/-- The base is presented as its actual spectrum, with no new coefficient ring chosen. -/
def boundaryBaseSpecProjection [IsAffine V.toScheme] :
    (boundaryBaseSourceOpen q U V).toScheme ⟶ Spec Γ(V.toScheme, ⊤) :=
  boundaryBaseSourceProjection q U V ≫ V.toScheme.isoSpec.hom

instance boundaryBaseSpecProjection_smooth [IsAffine V.toScheme]
    [SmoothOfRelativeDimension 1 q] :
    SmoothOfRelativeDimension 1 (boundaryBaseSpecProjection q U V) := by
  have := boundaryBaseSourceProjection_smooth q U V
  exact smoothOfRelativeDimension_comp (n := 1) (m := 0) _ _

instance boundaryBaseSpecProjection_separated [IsAffine V.toScheme] [IsSeparated q] :
    IsSeparated (boundaryBaseSpecProjection q U V) := by
  dsimp [boundaryBaseSpecProjection, boundaryBaseSourceProjection]
  infer_instance

/-- The smaller base retains its original field structure map. -/
def boundaryBaseFieldMap {k : Type u} [Field k] (t : S ⟶ Spec (.of k))
    [IsAffine V.toScheme] : Spec Γ(V.toScheme, ⊤) ⟶ Spec (.of k) :=
  V.toScheme.isoSpec.inv ≫ V.ι ≫ t

instance boundaryBaseFieldMap_smooth {k : Type u} [Field k] (t : S ⟶ Spec (.of k))
    [Smooth t] [IsAffine V.toScheme] : Smooth (boundaryBaseFieldMap V t) := by
  dsimp [boundaryBaseFieldMap]
  infer_instance

instance boundaryBaseRetainedOpen_affine {C T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (π : C ⟶ S) (v : T ⟶ C) [IsAffine V.toScheme] :
    IsAffine ((v ≫ π) ⁻¹ᵁ V).toScheme := by
  have hV : IsAffineOpen V := by
    simpa only [Scheme.Opens.opensRange_ι] using isAffineOpen_opensRange V.ι
  exact hV.preimage (v ≫ π)
section Projective
variable (R : Type u) [CommRing R] (ι : Type u) {X Y C T : Scheme.{u}}
  (q : X ⟶ Spec (.of R)) (p : Y ⟶ X)
  (f : C ⟶ ProjectiveSpace R ι) (j : Y ⟶ C)
  (hj : j ≫ (f ≫ ProjectiveSpace.toSpec R ι) = p ≫ q)
  (U : X.Opens) (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]

@[reassoc]
theorem boundaryBaseCoverInclusion_spec_projection :
    boundaryBaseCoverInclusion q p (f ≫ ProjectiveSpace.toSpec R ι) j hj U V ≫
      (boundaryBaseProjectiveMap R ι f V ≫
        ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) ι) =
      boundaryBaseCoverMap q p U V ≫ boundaryBaseSpecProjection q U V := by
  rw [boundaryBaseProjectiveMap_toSpec, ← Category.assoc,
    boundaryBaseCoverInclusion_fst]
  rfl

instance boundaryBaseCoverInclusion_projective_smooth
    [Etale p] [SmoothOfRelativeDimension 1 q] :
    SmoothOfRelativeDimension 1
      (boundaryBaseCoverInclusion q p (f ≫ ProjectiveSpace.toSpec R ι) j hj U V ≫
        (boundaryBaseProjectiveMap R ι f V ≫
          ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) ι)) := by
  rw [boundaryBaseProjectiveMap_toSpec, ← Category.assoc]
  have := boundaryBaseCoverInclusion_smooth q p
    (f ≫ ProjectiveSpace.toSpec R ι) j hj U V
  exact smoothOfRelativeDimension_comp (n := 1) (m := 0) _ _

instance boundaryBaseRetainedTarget_projective_smooth (v : T ⟶ C)
    [SmoothOfRelativeDimension 1 (v ≫ (f ≫ ProjectiveSpace.toSpec R ι))] :
    SmoothOfRelativeDimension 1
      (boundaryBaseRetainedTarget (f ≫ ProjectiveSpace.toSpec R ι) V v ≫
        (boundaryBaseProjectiveMap R ι f V ≫
          ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) ι)) := by
  rw [boundaryBaseProjectiveMap_toSpec]
  have := boundaryBaseRetainedTarget_smooth (f ≫ ProjectiveSpace.toSpec R ι) V v
  exact (Category.assoc (boundaryBaseRetainedTarget (f ≫ ProjectiveSpace.toSpec R ι) V v)
    (pullback.fst V.ι (f ≫ ProjectiveSpace.toSpec R ι)) V.toScheme.isoSpec.hom) ▸
    (smoothOfRelativeDimension_comp (n := 1) (m := 0)
      (boundaryBaseRetainedTarget (f ≫ ProjectiveSpace.toSpec R ι) V v ≫
        pullback.fst V.ι (f ≫ ProjectiveSpace.toSpec R ι)) V.toScheme.isoSpec.hom)
end Projective
end AlgebraicGeometry.Scheme.Hom
