/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Affine.Localization
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.ResidueDegree
public import Motivic.Aglib.Algebra.Homology.LengthEuler.FiniteAlgebra

/-!
# Actual localized source coefficient complexes

Localizing the whole finite-algebra coefficient at a maximal point gives the
original source tilde stalk with its actual scalar action. This is natural for
all original module maps and hence for arbitrary original complexes.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteFiber
open _root_.AlgebraicGeometry.Scheme.Modules _root_.PrimeSpectrum.FiniteFiber

open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.Affine

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B]
  (p : PrimeSpectrum A) (q : MaximalSpectrum (localAlgebra A B p))

/-- The canonical commutative-localization ring instance, exposed for category elaboration. -/
local instance canonicalLocalizationRing : Ring (Localization.AtPrime q.asIdeal) :=
  (inferInstance : CommRing (Localization.AtPrime q.asIdeal)).toRing

/-- The source structure-stalk comparison retains the original B-algebra action. -/
def sourceSchemeStalkAlgEquiv :
    Localization.AtPrime q.asIdeal ≃ₐ[B] (Spec B).presheaf.stalk (sourcePoint A B p q).1 :=
  (sourceLocalizationEquiv A B p q).trans (StructureSheaf.stalkIso B (sourcePoint A B p q).1)

/-- The B-algebra comparison has exactly the already checked actual scheme-stalk map. -/
theorem sourceSchemeStalkAlgEquiv_toRingHom :
    (sourceSchemeStalkAlgEquiv A B p q).toRingHom = (sourceSchemeStalkIso A B p q).hom.hom := rfl

/-- Literal successive extension to the whole algebra and then its maximal localization. -/
abbrev localCoefficientFunctor : ModuleCat.{u} B ⥤ ModuleCat.{u} (Localization.AtPrime q.asIdeal) :=
  ModuleCat.extendScalars (algebraMap B (localAlgebra A B p)) ⋙
    ModuleCat.extendScalars (algebraMap (localAlgebra A B p) (Localization.AtPrime q.asIdeal))

/-- The actual source tilde-stalk functor with its canonical localization-ring action. -/
abbrev restrictedSourceStalkFunctor :
    ModuleCat.{u} B ⥤ ModuleCat.{u} (Localization.AtPrime q.asIdeal) :=
  (tilde.functor B ⋙ Stalk.functor (X := Spec B) (sourcePoint A B p q).1) ⋙
    ModuleCat.restrictScalars (sourceSchemeStalkIso A B p q).hom.hom

/-- The localized original whole-algebra coefficient is the actual source stalk,
with scalar restriction along the literal source scheme-stalk isomorphism. -/
def localCoefficientStalkIso :
    localCoefficientFunctor A B p q ≅ restrictedSourceStalkFunctor A B p q := by
  unfold localCoefficientFunctor restrictedSourceStalkFunctor
  rw [← sourceSchemeStalkAlgEquiv_toRingHom]
  refine coordinateExtendCompIso B (localAlgebra A B p) (Localization.AtPrime q.asIdeal) ≪≫ ?_
  refine coordinateTensorExtendIso B (Localization.AtPrime q.asIdeal) ≪≫ ?_
  refine coordinateTensorRingIso B (Localization.AtPrime q.asIdeal)
    ((Spec B).presheaf.stalk (sourcePoint A B p q).1) (sourceSchemeStalkAlgEquiv A B p q) ≪≫ ?_
  exact Functor.isoWhiskerRight (tildeStalkIso B (sourcePoint A B p q).1) _

/-- The local coefficient comparison intertwines every original module map. -/
theorem localCoefficientStalkIso_naturality {M N : ModuleCat.{u} B} (g : M ⟶ N) :
    (localCoefficientFunctor A B p q).map g ≫ (localCoefficientStalkIso A B p q).hom.app N =
      (localCoefficientStalkIso A B p q).hom.app M ≫
        (restrictedSourceStalkFunctor A B p q).map g :=
  (localCoefficientStalkIso A B p q).hom.naturality g

/-- All localized original coefficient differentials compare to the actual source stalk ones. -/
def localCoefficientStalkComplexIso {ι : Type*} (c : ComplexShape ι) :
    (ModuleCat.extendScalars (algebraMap B (localAlgebra A B p)) ⋙
      ModuleCat.extendScalars
        (algebraMap (localAlgebra A B p) (Localization.AtPrime q.asIdeal))).mapHomologicalComplex
          c ≅
      ((tilde.functor B ⋙ Stalk.functor (X := Spec B) (sourcePoint A B p q).1) ⋙
        ModuleCat.restrictScalars (sourceSchemeStalkIso A B p q).hom.hom).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (localCoefficientStalkIso A B p q) c

/-- Degree components are the original natural coefficient comparisons. -/
theorem localCoefficientStalkComplexIso_hom_f {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (ModuleCat.{u} B) c) (i : ι) :
    ((localCoefficientStalkComplexIso A B p q c).app K).hom.f i =
      (localCoefficientStalkIso A B p q).hom.app (K.X i) := rfl

end AlgebraicGeometry.Scheme.Hom.FiniteFiber
