/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.TildeOpenBaseChange

/-!
# The canonical identity law for tilde and affine open restriction

The canonical geometric restriction unitor is compared with the actual
scalar-extension unitor using the constructed adjunction coordinates.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace Motivic.TildeOpenBaseChange

/-- The affine pushforward section comparison retains the actual underlying section. -/
theorem globalSectionsIso_hom_apply {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (N : (Spec B).Modules)
    (x : (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor).obj N) :
    (AffinePushforward.globalSectionsIso φ).hom.app N x = x := rfl

/-- The actual restriction unitor, including the spectrum identity-map equality. -/
def identityRestrictionIso (A : CommRingCat.{u}) :
    Scheme.Modules.restrictFunctor (Spec.map (𝟙 A)) ≅ 𝟭 (Spec A).Modules :=
  Scheme.Modules.restrictFunctorCongr (Spec.map_id A) ≪≫ Scheme.Modules.restrictFunctorId

/-- The canonical geometric restriction unitor has the expected adjoint section coordinate. -/
theorem identityRestrictionIso_hom_coordinate (A : CommRingCat.{u})
    (M : ModuleCat.{u} A) (m : M) :
    ((restrictionAdjunction (𝟙 A)).homEquiv M (tilde M)
      ((identityRestrictionIso A).hom.app (tilde M))) m = (tilde.isoTop M).hom m := by
  rfl

/-- Tilde/open restriction respects the actual geometric and scalar-extension unitors. -/
theorem restrictionIso_hom_id (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    (restrictionIso (𝟙 A)).hom.app M ≫
        tilde.map ((ModuleCat.extendScalarsId A).hom.app M) =
      (identityRestrictionIso A).hom.app (tilde M) := by
  apply ((restrictionAdjunction (𝟙 A)).homEquiv M (tilde M)).injective
  erw [Adjunction.homEquiv_naturality_right, restrictionIso_hom_homEquiv]
  ext m
  rw [identityRestrictionIso_hom_coordinate]
  change (moduleSpecΓFunctor.map (tilde.map ((ModuleCat.extendScalarsId A).hom.app M)))
      ((tilde.isoTop ((ModuleCat.extendScalars (RingHom.id A)).obj M)).hom
        ((1 : A) ⊗ₜ[A,RingHom.id A] m)) = (tilde.isoTop M).hom m
  have h := (tilde.toTildeΓNatIso (R := A)).hom.naturality
    ((ModuleCat.extendScalarsId A).hom.app M)
  have hm := congrArg (fun f => f ((1 : A) ⊗ₜ[A,RingHom.id A] m)) h
  exact hm.symm.trans (congrArg (tilde.isoTop M).hom
    (ModuleCat.extendScalarsId_hom_app_one_tmul M m))

end Motivic.TildeOpenBaseChange
