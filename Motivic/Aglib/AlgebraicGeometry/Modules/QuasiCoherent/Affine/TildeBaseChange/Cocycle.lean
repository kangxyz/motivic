/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeBaseChange.Composition

/-!
# The canonical tilde/open composition square

The actual comparison commutes with the geometric restriction associator and
scalar-extension associator. The proof transports the proved section square
through the genuine adjunctions.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange

variable {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]

local instance : IsOpenImmersion (Spec.map (φ ≫ ψ)) := by
  rw [Spec.map_comp]
  infer_instance

/-- Canonical tilde/open comparison commutes with the genuine geometric and scalar associators. -/
theorem restrictionIso_hom_comp :
    Functor.whiskerLeft (tilde.functor (R := A)) (compositionRestrictionIso φ ψ).hom ≫
      (Functor.associator (tilde.functor (R := A))
        (restrictFunctor (Spec.map φ)) (restrictFunctor (Spec.map ψ))).inv ≫
      Functor.whiskerRight (restrictionIso φ).hom (restrictFunctor (Spec.map ψ)) ≫
      (Functor.associator (ModuleCat.extendScalars φ.hom) (tilde.functor (R := B))
        (restrictFunctor (Spec.map ψ))).hom ≫
      Functor.whiskerLeft (ModuleCat.extendScalars φ.hom) (restrictionIso ψ).hom ≫
      (Functor.associator (ModuleCat.extendScalars φ.hom) (ModuleCat.extendScalars ψ.hom)
        (tilde.functor (R := C))).inv =
    (restrictionIso (φ ≫ ψ)).hom ≫
      Functor.whiskerRight (ModuleCat.extendScalarsComp φ.hom ψ.hom).hom
        (tilde.functor (R := C)) := by
  let a₀ := (tilde.adjunction (R := A)).comp (restrictAdjunction (Spec.map (φ ≫ ψ)))
  let a₁ := (tilde.adjunction (R := A)).comp
    ((restrictAdjunction (Spec.map φ)).comp (restrictAdjunction (Spec.map ψ)))
  let a₂ := ((tilde.adjunction (R := A)).comp (restrictAdjunction (Spec.map φ))).comp
    (restrictAdjunction (Spec.map ψ))
  let a₃ := (scalarAdjunction φ).comp (restrictAdjunction (Spec.map ψ))
  let a₄ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    ((tilde.adjunction (R := B)).comp (restrictAdjunction (Spec.map ψ)))
  let a₅ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (scalarAdjunction ψ)
  let a₆ := ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (ModuleCat.extendRestrictScalarsAdj ψ.hom)).comp (tilde.adjunction (R := C))
  apply (conjugateEquiv a₆ a₀).injective
  rw [← conjugateEquiv_comp a₆ a₁ a₀, ← conjugateEquiv_comp a₆ a₂ a₁,
    ← conjugateEquiv_comp a₆ a₃ a₂, ← conjugateEquiv_comp a₆ a₄ a₃,
    ← conjugateEquiv_comp a₆ a₅ a₄,
    ← conjugateEquiv_comp a₆ (scalarAdjunction (φ ≫ ψ)) a₀]
  dsimp only [a₀, a₁, a₂, a₃, a₄, a₅, a₆, scalarAdjunction]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugateEquiv_associator_inv]
  erw [conjugate_compositionRestrictionIso_hom φ ψ,
    conjugate_restrictionIso_hom ψ, conjugate_restrictionIso_hom φ,
    conjugate_restrictionIso_hom (φ ≫ ψ), conjugate_extendScalarsComp_hom φ ψ]
  apply NatTrans.ext
  funext N
  simpa only [NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congr_app (globalSectionsIso_inv_comp φ ψ) N

/-- Component form of the genuine tilde/open cocycle on every actual module. -/
theorem restrictionIso_hom_comp_app (M : ModuleCat.{u} A) :
    (compositionRestrictionIso φ ψ).hom.app (tilde M) ≫
      (restrictFunctor (Spec.map ψ)).map ((restrictionIso φ).hom.app M) ≫
      (restrictionIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) =
    (restrictionIso (φ ≫ ψ)).hom.app M ≫
      tilde.map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) := by
  simpa only [tilde.functor, Functor.comp_obj, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] using congr_app (restrictionIso_hom_comp φ ψ) M

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange
