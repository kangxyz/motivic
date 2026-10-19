/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Additive

/-!
# Affine pushforward and the tilde construction

The pushforward of the tilde sheaf along an arbitrary map of affine schemes is
naturally the tilde sheaf of the restricted module. This comparison is natural
on genuine module maps, so it also compares the actual differentials of complexes.
No finiteness, flatness, or surjectivity hypothesis is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Pushforward.Affine

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

set_option backward.isDefEq.respectTransparency false in
/-- Global sections of affine pushforward agree naturally with restricted global sections. -/
def globalSectionsIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun M =>
    ((CategoryTheory.evaluation _ _).obj (op ⊤)).mapIso
      ((TopCat.Sheaf.forget _ _).mapIso
        ((pushforwardCompModulesSpecToSheafIso φ).app M)))
    (fun f => by
      exact congrArg (fun g => g.hom.app (op ⊤))
        ((pushforwardCompModulesSpecToSheafIso φ).hom.naturality f))

/-- The global sections of the pushforward of a tilde sheaf are the original restricted module. -/
def tildeGlobalSectionsIso :
    (tilde.functor B ⋙ Scheme.Modules.pushforward (Spec.map φ)) ⋙ moduleSpecΓFunctor ≅
      ModuleCat.restrictScalars φ.hom :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tilde.functor B) (globalSectionsIso φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight tilde.toTildeΓNatIso.symm (ModuleCat.restrictScalars φ.hom) ≪≫
    Functor.leftUnitor _

set_option backward.isDefEq.respectTransparency false in
/-- The natural affine pushforward comparison for every ring homomorphism. -/
def tildePushforwardIso :
    tilde.functor B ⋙ Scheme.Modules.pushforward (Spec.map φ) ≅
      ModuleCat.restrictScalars φ.hom ⋙ tilde.functor A := by
  let F := tilde.functor B ⋙ Scheme.Modules.pushforward (Spec.map φ)
  have (M : ModuleCat B) : IsIso (F.obj M).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ (tilde M)
  let α := Functor.whiskerLeft F Scheme.Modules.fromTildeΓNatTrans
  have (M : ModuleCat B) : IsIso (α.app M) :=
    inferInstanceAs (IsIso (F.obj M).fromTildeΓ)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact (Functor.rightUnitor F).symm ≪≫ (asIso α).symm ≪≫
    (Functor.associator F moduleSpecΓFunctor (tilde.functor A)).symm ≪≫
    Functor.isoWhiskerRight (tildeGlobalSectionsIso φ) (tilde.functor A)

/-- The actual module morphism square underlying the affine pushforward comparison. -/
@[reassoc]
theorem tildePushforwardIso_naturality {M N : ModuleCat B} (g : M ⟶ N) :
    (Scheme.Modules.pushforward (Spec.map φ)).map (tilde.map g) ≫
        (tildePushforwardIso φ).hom.app N =
      (tildePushforwardIso φ).hom.app M ≫
        tilde.map ((ModuleCat.restrictScalars φ.hom).map g) :=
  (tildePushforwardIso φ).hom.naturality g

/-- The affine comparison prolongs to complexes with their literal differentials. -/
def tildePushforwardComplexIso {ι : Type*} (c : ComplexShape ι) :
    (tilde.functor B ⋙ Scheme.Modules.pushforward (Spec.map φ)).mapHomologicalComplex c ≅
      (ModuleCat.restrictScalars φ.hom ⋙ tilde.functor A).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (tildePushforwardIso φ) c

/-- In every degree the complex comparison is the module comparison. -/
@[simp]
theorem tildePushforwardComplexIso_hom_f {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (ModuleCat B) c) (i : ι) :
    ((tildePushforwardComplexIso φ c).hom.app K).f i =
      (tildePushforwardIso φ).hom.app (K.X i) := rfl

/-- The comparison commutes with every actual differential, including zero differentials. -/
theorem tildePushforwardComplexIso_d {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (ModuleCat B) c) (i j : ι) :
    (Scheme.Modules.pushforward (Spec.map φ)).map (tilde.map (K.d i j)) ≫
        (tildePushforwardIso φ).hom.app (K.X j) =
      (tildePushforwardIso φ).hom.app (K.X i) ≫
        tilde.map ((ModuleCat.restrictScalars φ.hom).map (K.d i j)) :=
  tildePushforwardIso_naturality φ (K.d i j)

end AlgebraicGeometry.Scheme.Modules.Pushforward.Affine
