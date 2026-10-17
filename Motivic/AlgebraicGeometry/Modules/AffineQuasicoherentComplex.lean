/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.OpenRestrictionStalk
public import Motivic.AlgebraicGeometry.Cycles.FiniteAffineChart

/-!
# Coordinate complexes of genuinely given quasi-coherent sheaf complexes

Global sections construct the actual coordinate module complex of a given
termwise-quasi-coherent complex on an affine chart. The existing tilde-Gamma
counit supplies the actual differential-compatible comparison. Applied to the
whole affine inverse image of a finite map, it also compares every original
source stalk with its canonical ring action. This is a chart adapter; it does
not construct the first-stage Tor coefficient sheaf.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.AffineQuasicoherent

variable (R : CommRingCat.{u}) {ι : Type*} (c : ComplexShape ι)

/-- Actual global sections preserve addition of module-sheaf morphisms. -/
instance coordinateSections_additive : (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by intros; rfl

/-- The actual global-sections module complex, with the original mapped differentials. -/
abbrev coordinateComplex (K : HomologicalComplex (Spec R).Modules c) :
    HomologicalComplex (ModuleCat.{u} R) c :=
  (moduleSpecΓFunctor.mapHomologicalComplex c).obj K

/-- The actual tilde-Gamma counit is a morphism of the original complexes. -/
def fromCoordinateComplex (K : HomologicalComplex (Spec R).Modules c) :
    ((tilde.functor R).mapHomologicalComplex c).obj (coordinateComplex R c K) ⟶ K where
  f n := (K.X n).fromTildeΓ
  comm' n m _ := (Scheme.Modules.fromTildeΓNatTrans.naturality (K.d n m)).symm

/-- Every actual component is the existing affine tilde-Gamma comparison. -/
theorem fromCoordinateComplex_f (K : HomologicalComplex (Spec R).Modules c) (n : ι) :
    (fromCoordinateComplex R c K).f n = (K.X n).fromTildeΓ := rfl

/-- The actual coordinate comparison is natural in arbitrary original complex maps. -/
@[reassoc] theorem fromCoordinateComplex_naturality
    {K L : HomologicalComplex (Spec R).Modules c} (φ : K ⟶ L) :
    ((tilde.functor R).mapHomologicalComplex c).map
        ((moduleSpecΓFunctor.mapHomologicalComplex c).map φ) ≫
        fromCoordinateComplex R c L = fromCoordinateComplex R c K ≫ φ := by
  apply HomologicalComplex.hom_ext
  intro n
  exact Scheme.Modules.fromTildeΓNatTrans.naturality (φ.f n)

/-- Termwise quasi-coherence, rather than an assumed comparison, proves that
the constructed counit is an isomorphism of complexes. -/
instance fromCoordinateComplex_isIso (K : HomologicalComplex (Spec R).Modules c)
    [∀ n, (K.X n).IsQuasicoherent] : IsIso (fromCoordinateComplex R c K) := by
  have (n : ι) : IsIso ((fromCoordinateComplex R c K).f n) :=
    inferInstanceAs (IsIso (K.X n).fromTildeΓ)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The constructed coordinate module complex presents the genuinely given QC sheaf complex. -/
def coordinateComplexIso (K : HomologicalComplex (Spec R).Modules c)
    [∀ n, (K.X n).IsQuasicoherent] :
    ((tilde.functor R).mapHomologicalComplex c).obj (coordinateComplex R c K) ≅ K :=
  asIso (fromCoordinateComplex R c K)

/-- The isomorphism preserves every actual original differential. -/
theorem coordinateComplexIso_hom_comm (K : HomologicalComplex (Spec R).Modules c)
    [∀ n, (K.X n).IsQuasicoherent] (n m : ι) :
    (((tilde.functor R).mapHomologicalComplex c).obj (coordinateComplex R c K)).d n m ≫
        (coordinateComplexIso R c K).hom.f m =
      (coordinateComplexIso R c K).hom.f n ≫ K.d n m :=
  ((coordinateComplexIso R c K).hom.comm n m).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U)

open FiniteAffineChart ModuleStalk

/-- A genuinely given complex restricted to the entire finite affine inverse image. -/
abbrev wholeChartSheafComplex (K : HomologicalComplex X.Modules c) :=
  ((Scheme.Modules.restrictFunctor (sourceChart f hU)).mapHomologicalComplex c).obj K

/-- The actual coordinate module complex of the entire finite inverse image. -/
abbrev wholeChartCoordinateComplex (K : HomologicalComplex X.Modules c) :=
  coordinateComplex Γ(X, f ⁻¹ᵁ U) c (wholeChartSheafComplex c f hU K)

/-- Restriction preserves each proved quasi-coherent term of the original complex. -/
instance wholeChartSheafComplex_quasicoherent (K : HomologicalComplex X.Modules c)
    [∀ n, (K.X n).IsQuasicoherent] (n : ι) :
    ((wholeChartSheafComplex c f hU K).X n).IsQuasicoherent :=
  inferInstanceAs
    (((Scheme.Modules.restrictFunctor (sourceChart f hU)).obj (K.X n)).IsQuasicoherent)

/-- The actual whole-chart coordinate complex presents the restricted given sheaf complex. -/
def wholeChartTildeIso (K : HomologicalComplex X.Modules c)
    [∀ n, (K.X n).IsQuasicoherent] :
    ((tilde.functor Γ(X, f ⁻¹ᵁ U)).mapHomologicalComplex c).obj
        (wholeChartCoordinateComplex c f hU K) ≅ wholeChartSheafComplex c f hU K :=
  coordinateComplexIso _ c _

/-- Every original source-fiber stalk is the stalk of the constructed coordinate
tilde complex, with the canonical open-chart scalar restriction. -/
def wholeChartStalkIso (K : HomologicalComplex X.Modules c)
    [∀ n, (K.X n).IsQuasicoherent] (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    ((tilde.functor Γ(X, f ⁻¹ᵁ U) ⋙ functor q).mapHomologicalComplex c).obj
        (wholeChartCoordinateComplex c f hU K) ≅
      ((functor (sourceChart f hU q) ⋙ ModuleCat.restrictScalars
        (inv ((sourceChart f hU).stalkMap q)).hom).mapHomologicalComplex c).obj K :=
  ((functor q).mapHomologicalComplex c).mapIso (wholeChartTildeIso c f hU K) ≪≫
    (openRestrictionComplexIso (sourceChart f hU) q c).app K

/-- The whole-chart stalk comparison uses the actual counit map and actual open
restriction map in every degree. -/
theorem wholeChartStalkIso_hom_f (K : HomologicalComplex X.Modules c)
    [∀ n, (K.X n).IsQuasicoherent] (q : Spec Γ(X, f ⁻¹ᵁ U)) (n : ι) :
    (wholeChartStalkIso c f hU K q).hom.f n =
      (functor q).map (((wholeChartSheafComplex c f hU K).X n).fromTildeΓ) ≫
        (openRestrictionIso (sourceChart f hU) q).hom.app (K.X n) := rfl

end Motivic.AffineQuasicoherent
