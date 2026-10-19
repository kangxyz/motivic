/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Affine.Tilde

/-!
# Tilde and actual affine open restriction

The genuine restriction of a tilde module along an affine open immersion is
naturally the tilde module of scalar extension. The comparison is determined by
the actual adjunctions and the accepted global-sections pushforward isomorphism.
No module flatness or finite-generation hypothesis is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward

variable {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]

/-- Actual affine open restriction of tilde is left adjoint to the common scalar-restricted
section functor, using the canonical pushforward/global-sections comparison. -/
def restrictionAdjunction :
    tilde.functor A ⋙ Scheme.Modules.restrictFunctor (Spec.map φ) ⊣
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  ((tilde.adjunction (R := A)).comp (Scheme.Modules.restrictAdjunction (Spec.map φ))).ofNatIsoRight
    (Affine.globalSectionsIso φ)

/-- Tilde after actual scalar extension is left adjoint to the same section functor. -/
def scalarAdjunction :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor B ⊣
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := B))

/-- The natural comparison between actual open restriction and scalar extension of tilde. -/
def restrictionIso :
    tilde.functor A ⋙ Scheme.Modules.restrictFunctor (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor B :=
  (restrictionAdjunction φ).leftAdjointUniq (scalarAdjunction φ)

/-- The comparison is natural in every actual module morphism. -/
@[reassoc] theorem restrictionIso_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor (Spec.map φ)).map (tilde.map f) ≫
        (restrictionIso φ).hom.app N =
      (restrictionIso φ).hom.app M ≫
        tilde.map ((ModuleCat.extendScalars φ.hom).map f) :=
  (restrictionIso φ).hom.naturality f

/-- The actual adjunction unit determines the canonical comparison. -/
theorem restrictionIso_hom_homEquiv (M : ModuleCat.{u} A) :
    (restrictionAdjunction φ).homEquiv M _ ((restrictionIso φ).hom.app M) =
      (scalarAdjunction φ).unit.app M :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app (restrictionAdjunction φ) (scalarAdjunction φ) M

/-- The comparison commutes with the actual units into the common section functor. -/
@[reassoc] theorem restrictionIso_unit (M : ModuleCat.{u} A) :
    (restrictionAdjunction φ).unit.app M ≫
        (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).map
          ((restrictionIso φ).hom.app M) =
      (scalarAdjunction φ).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app (restrictionAdjunction φ) (scalarAdjunction φ) M

/-- The comparison's section coordinate is exactly the extension-of-scalars unit followed
by the actual tilde global-section unit. -/
theorem restrictionIso_globalSections (M : ModuleCat.{u} A) :
    ((tilde.adjunction (R := A)).comp
      (Scheme.Modules.restrictAdjunction (Spec.map φ))).homEquiv M _
        ((restrictionIso φ).hom.app M) ≫
      (Affine.globalSectionsIso φ).hom.app
        (tilde ((ModuleCat.extendScalars φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := B)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h := restrictionIso_hom_homEquiv φ M
  rw [restrictionAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply] at h
  exact h.trans (Adjunction.comp_unit_app _ _ M)

/-- In the canonical global-section coordinates the adjoint comparison sends `m` to `1 ⊗ m`. -/
theorem restrictionIso_globalSections_apply (M : ModuleCat.{u} A) (m : M) :
    (((tilde.adjunction (R := A)).comp
      (Scheme.Modules.restrictAdjunction (Spec.map φ))).homEquiv M _
        ((restrictionIso φ).hom.app M) ≫
      (Affine.globalSectionsIso φ).hom.app
        (tilde ((ModuleCat.extendScalars φ.hom).obj M))) m =
      (tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj M)).hom ((1 : B) ⊗ₜ[A,φ.hom] m) := by
  exact congrArg (fun f => f m) (restrictionIso_globalSections φ M)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange
