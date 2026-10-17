/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Restriction.Sections
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-! # Actual unit-domain morphisms attached to sections on an open -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original open section, viewed as a global section of its restriction. -/
def openSection (X : Scheme.{u}) (U : X.Opens) (M : X.Modules) (s : Γ(M, U)) :
    Γ(M.restrict U.ι, ⊤) :=
  M.presheaf.map (eqToHom (show U.ι ''ᵁ ⊤ = U by simp)).op s

/-- This is precisely the existing restriction-section isomorphism transport. -/
theorem openSection_eq_restrictedSectionsIso (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) (s : Γ(M, U)) :
    openSection X U M s = ((restrictedSectionsIso U.ι).app M).inv
      ((M.presheaf.mapIso (eqToIso (Scheme.Opens.opensRange_ι U)).op).hom s) := by
  change M.presheaf.map _ s = M.presheaf.map _ (M.presheaf.map _ s)
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  congr 1

/-- Multiplication by an original section on the actual open subscheme. -/
def openSectionHom (X : Scheme.{u}) (U : X.Opens) (M : X.Modules) (s : Γ(M, U)) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ M.restrict U.ι :=
  (unitHomGlobalSectionsEquiv U.toScheme _).symm (openSection X U M s)

/-- Converting an open section to a sheaf map commutes with every coefficient map. -/
theorem openSectionHom_naturality (X : Scheme.{u}) (U : X.Opens)
    {M N : X.Modules} (α : M ⟶ N) (s : Γ(M, U)) :
    openSectionHom X U M s ≫ (restrictFunctor U.ι).map α =
      openSectionHom X U N (α.app U s) := by
  apply (unitHomGlobalSectionsEquiv U.toScheme _).injective
  rw [unitHomGlobalSectionsEquiv_naturality]
  simp only [openSectionHom, Equiv.apply_symm_apply]
  change α.app (U.ι ''ᵁ ⊤)
    (M.presheaf.map (eqToHom (show U.ι ''ᵁ ⊤ = U by simp)).op s) =
    N.presheaf.map (eqToHom (show U.ι ''ᵁ ⊤ = U by simp)).op (α.app U s)
  exact congrArg (fun f ↦ f s) (α.mapPresheaf.naturality
    (eqToHom (show U.ι ''ᵁ ⊤ = U by simp)).op)

open Pullback.OpenRestriction in
/-- Direct image on an open sends the original section to the unit-domain map
of its actual inverse-image restriction. -/
theorem openSectionHom_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (N : X.Modules) (σ : Γ(N, f ⁻¹ᵁ U)) :
    openSectionHom Y U ((pushforward f).obj N) σ ≫ restrictedPushforwardMap f U N =
      SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom ≫
        (pushforward (f ∣_ U)).map (openSectionHom X (f ⁻¹ᵁ U) N σ) := by
  apply (unitHomGlobalSectionsEquiv U.toScheme _).injective
  rw [unitHomGlobalSectionsEquiv_naturality]
  simp only [openSectionHom, Equiv.apply_symm_apply]
  change (restrictedPushforwardMap f U N).app ⊤ (openSection Y U _ σ) =
    Hom.app ((unitHomGlobalSectionsEquiv (f ⁻¹ᵁ U).toScheme _).symm
      (openSection X (f ⁻¹ᵁ U) N σ)) ((f ∣_ U) ⁻¹ᵁ ⊤) ((f ∣_ U).app ⊤ 1)
  rw [map_one, unitHomGlobalSectionsEquiv_symm_app, one_smul,
    restrictedPushforwardMap_app]
  simp only [openSection, pushforward_obj_presheaf_map, restrict_map]
  erw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.Modules
