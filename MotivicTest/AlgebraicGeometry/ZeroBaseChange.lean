module

import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange

/-! Direct tests of arbitrary image-ideal and whole-zero-scheme base change. -/

noncomputable section
set_option linter.hashCommand false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y : Scheme.{u}} {M : Y.Modules} [M.IsQuasicoherent]
variable (φ : M ⟶ SheafOfModules.unit Y.ringCatSheaf) (f : X ⟶ Y)

example : Hom.imageIdealData ((Scheme.Modules.pullback f).map φ ≫
    (pullbackUnitIso f).hom) = (Hom.imageIdealData φ).comap f :=
  Hom.imageIdealData_pullbackToUnit_of_isQuasicoherent φ f

example : Hom.zeroScheme ((Scheme.Modules.pullback f).map φ ≫
    (pullbackUnitIso f).hom) ≅ Limits.pullback f (Hom.zeroInclusion φ) :=
  Hom.zeroSchemePullbackIso φ f

example : (Hom.zeroSchemePullbackIso φ f).hom ≫
    Limits.pullback.fst f (Hom.zeroInclusion φ) =
      Hom.zeroInclusion ((Scheme.Modules.pullback f).map φ ≫ (pullbackUnitIso f).hom) :=
  Hom.zeroSchemePullbackIso_hom_fst φ f

example [IsIso (Hom.pullbackToUnit φ f)] :
    IsEmpty (Limits.pullback (C := Scheme.{u}) f (Hom.zeroInclusion φ)) :=
  Hom.isEmpty_pullback_zeroInclusion φ f

#print axioms Hom.imageIdealData_pullbackToUnit_of_isQuasicoherent
#print axioms Hom.zeroSchemePullbackIso
#print axioms Hom.zeroSchemePullbackIso_hom_fst
#print axioms Hom.isEmpty_pullback_zeroInclusion
