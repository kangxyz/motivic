module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Cover
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSource
/-! # The fixed compactification survives the constructed base and source shrink -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y C : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
  (π : C ⟶ S) (j : Y ⟶ C) (hj : j ≫ π = p ≫ q)
  (U : X.Opens) (V : S.Opens)

/-- The compactification pulled back to the base open `V`. -/
abbrev boundaryBaseCompactification := pullback V.ι π

/-- The map from the restricted cover to the compactification over `V` induced by `j`. -/
def boundaryBaseCoverInclusion : (boundaryBaseCoverOpen q p U V).toScheme ⟶
    boundaryBaseCompactification π V :=
  pullback.lift (boundaryBaseCoverMap q p U V ≫ boundaryBaseSourceProjection q U V)
    ((boundaryBaseCoverOpen q p U V).ι ≫ j) (by
      simp only [Category.assoc, boundaryBaseSourceProjection_ι]
      rw [← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc, hj])

@[reassoc (attr := simp)]
theorem boundaryBaseCoverInclusion_fst :
    boundaryBaseCoverInclusion q p π j hj U V ≫ pullback.fst V.ι π =
      boundaryBaseCoverMap q p U V ≫ boundaryBaseSourceProjection q U V :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem boundaryBaseCoverInclusion_snd :
    boundaryBaseCoverInclusion q p π j hj U V ≫ pullback.snd V.ι π =
      (boundaryBaseCoverOpen q p U V).ι ≫ j := pullback.lift_snd _ _ _

/-- The actual original cover remains an open of the same base-changed compactification. -/
theorem boundaryBaseCoverInclusion_open [IsOpenImmersion j] :
    IsOpenImmersion (boundaryBaseCoverInclusion q p π j hj U V) := by
  have : IsOpenImmersion
      (boundaryBaseCoverInclusion q p π j hj U V ≫ pullback.snd V.ι π) := by
    rw [boundaryBaseCoverInclusion_snd]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.snd V.ι π)

/-- Smoothness is used only on the actual retained open, not on the compactification. -/
theorem boundaryBaseCoverInclusion_smooth [Etale p] [SmoothOfRelativeDimension 1 q] :
    SmoothOfRelativeDimension 1
      (boundaryBaseCoverInclusion q p π j hj U V ≫ pullback.fst V.ι π) := by
  rw [boundaryBaseCoverInclusion_fst]
  have := boundaryBaseCoverMap_etale q p U V
  have := boundaryBaseSourceProjection_smooth q U V
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _

/-- The given finite projective coordinate map is transported, never inferred from properness. -/
def boundaryBaseProjectiveMap
    (R : Type u) [CommRing R] (ι : Type u) {C : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R ι) (V : (Spec (.of R)).Opens) [IsAffine V.toScheme] :
    boundaryBaseCompactification (f ≫ ProjectiveSpace.toSpec R ι) V ⟶
      ProjectiveSpace Γ(V.toScheme, ⊤) ι :=
  ConstantCurve.affineSourceToProjectiveSpace R ι V.ι f

instance boundaryBaseProjectiveMap_finite
    (R : Type u) [CommRing R] (ι : Type u) {C : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
    (V : (Spec (.of R)).Opens) [IsAffine V.toScheme] :
    IsFinite (boundaryBaseProjectiveMap R ι f V) := by
  dsimp [boundaryBaseProjectiveMap]
  infer_instance

@[reassoc]
theorem boundaryBaseProjectiveMap_toSpec
    (R : Type u) [CommRing R] (ι : Type u) {C : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R ι) (V : (Spec (.of R)).Opens) [IsAffine V.toScheme] :
    boundaryBaseProjectiveMap R ι f V ≫ ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) ι =
      pullback.fst V.ι (f ≫ ProjectiveSpace.toSpec R ι) ≫ V.toScheme.isoSpec.hom :=
  ConstantCurve.affineSourceToProjectiveSpace_toSpec R ι V.ι f
end AlgebraicGeometry.Scheme.Hom
