/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeBaseChange.Basic
public import Aglib.CategoryTheory.Adjunction.Mates

/-!
# The actual adjoint mate defining affine tilde/open comparison

The previously constructed comparison is exactly the mate of the accepted
affine global-sections isomorphism under the genuine composite adjunctions.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward

variable {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]

/-- The actual tilde/open comparison is the conjugate of the canonical section isomorphism. -/
theorem restrictionIso_hom_eq_conjugate :
    (restrictionIso φ).hom =
      (conjugateEquiv (scalarAdjunction φ)
        ((tilde.adjunction (R := A)).comp (Scheme.Modules.restrictAdjunction (Spec.map φ)))).symm
          (Affine.globalSectionsIso φ).inv := by
  apply NatTrans.ext
  funext M
  apply ((restrictionAdjunction φ).homEquiv M _).injective
  rw [restrictionIso_hom_homEquiv]
  erw [restrictionAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit]
  have h := unit_conjugateEquiv_symm (scalarAdjunction φ)
    ((tilde.adjunction (R := A)).comp (Scheme.Modules.restrictAdjunction (Spec.map φ)))
    (Affine.globalSectionsIso φ).inv M
  rw [← h]
  simp

/-- Conjugation recovers exactly the original canonical section isomorphism. -/
theorem conjugate_restrictionIso_hom :
    conjugateEquiv (scalarAdjunction φ)
      ((tilde.adjunction (R := A)).comp (Scheme.Modules.restrictAdjunction (Spec.map φ)))
      (restrictionIso φ).hom = (Affine.globalSectionsIso φ).inv := by
  rw [restrictionIso_hom_eq_conjugate]
  exact Equiv.apply_symm_apply _ _

omit [IsOpenImmersion (Spec.map φ)] in
/-- The canonical scalar-extension associator is the mate of scalar restriction composition. -/
theorem conjugate_extendScalarsComp_hom {C : CommRingCat.{u}} (ψ : B ⟶ C) :
    conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
        (ModuleCat.extendRestrictScalarsAdj ψ.hom))
      (ModuleCat.extendRestrictScalarsAdj (ψ.hom.comp φ.hom))
      (ModuleCat.extendScalarsComp φ.hom ψ.hom).hom =
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).inv := by
  change (conjugateEquiv _ _) ((conjugateEquiv _ _).symm _) = _
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange

