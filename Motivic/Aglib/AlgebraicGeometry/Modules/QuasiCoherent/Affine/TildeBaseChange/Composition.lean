/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeBaseChange.Identity
public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeBaseChange.Mates
public import Motivic.Aglib.AlgebraicGeometry.Modules.Restriction.Open.RestrictionAdjunctionCoherence

/-!
# Composition of actual affine tilde/open restriction

The genuine geometric and scalar associators are attached to the canonical
affine section comparison, then transported across the actual adjunctions.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward
open _root_.AlgebraicGeometry.Scheme.Modules.Restriction

variable {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)

/-- The actual affine pushforward composition comparison, including the spectrum-map equality. -/
def compositionPushforwardIso :
    pushforward (Spec.map ψ) ⋙ pushforward (Spec.map φ) ≅ pushforward (Spec.map (φ ≫ ψ)) :=
  pushforwardComp (Spec.map ψ) (Spec.map φ) ≪≫ pushforwardCongr (Spec.map_comp φ ψ).symm

/-- Canonical pushforward composition keeps the same genuine global section. -/
theorem compositionPushforwardIso_globalSections_hom_apply (N : (Spec C).Modules)
    (x : ((pushforward (Spec.map ψ) ⋙ pushforward (Spec.map φ)) ⋙ moduleSpecΓFunctor).obj N) :
    (moduleSpecΓFunctor.map ((compositionPushforwardIso φ ψ).hom.app N)) x = x := by
  change Γ(N, ⊤) at x
  change N.presheaf.map (𝟙 (op ⊤)) x = x
  rw [N.presheaf.map_id]
  rfl

/-- The canonical affine section comparison respects genuine pushforward and scalar associators. -/
theorem globalSectionsIso_comp :
    Functor.whiskerRight (compositionPushforwardIso φ ψ).hom (moduleSpecΓFunctor (R := A)) ≫
        (Affine.globalSectionsIso (φ ≫ ψ)).hom =
      Functor.whiskerLeft (pushforward (Spec.map ψ)) (Affine.globalSectionsIso φ).hom ≫
        Functor.whiskerRight (Affine.globalSectionsIso ψ).hom
          (ModuleCat.restrictScalars φ.hom) ≫
        Functor.whiskerLeft (moduleSpecΓFunctor (R := C))
          (ModuleCat.restrictScalarsComp φ.hom ψ.hom).inv := by
  apply NatTrans.ext
  funext N
  ext x
  exact compositionPushforwardIso_globalSections_hom_apply φ ψ N x

/-- The inverse section comparisons have the corresponding actual composition square. -/
theorem globalSectionsIso_inv_comp :
    Functor.whiskerRight (Affine.globalSectionsIso ψ).inv
        (ModuleCat.restrictScalars φ.hom) ≫
      Functor.whiskerLeft (pushforward (Spec.map ψ)) (Affine.globalSectionsIso φ).inv ≫
      Functor.whiskerRight (compositionPushforwardIso φ ψ).hom (moduleSpecΓFunctor (R := A)) =
    Functor.whiskerLeft (moduleSpecΓFunctor (R := C))
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).inv ≫
      (Affine.globalSectionsIso (φ ≫ ψ)).inv := by
  apply NatTrans.ext
  funext N
  ext x
  exact compositionPushforwardIso_globalSections_hom_apply φ ψ N x

variable [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]

local instance : IsOpenImmersion (Spec.map (φ ≫ ψ)) := by
  rw [Spec.map_comp]
  infer_instance

/-- The actual affine open-restriction associator, including spectrum composition. -/
def compositionRestrictionIso :
    restrictFunctor (Spec.map (φ ≫ ψ)) ≅
      restrictFunctor (Spec.map φ) ⋙ restrictFunctor (Spec.map ψ) :=
  restrictFunctorCongr (Spec.map_comp φ ψ) ≪≫ restrictFunctorComp (Spec.map ψ) (Spec.map φ)

/-- The genuine geometric composition comparison has the canonical pushforward mate. -/
theorem conjugate_compositionRestrictionIso_hom :
    conjugateEquiv
      ((restrictAdjunction (Spec.map φ)).comp (restrictAdjunction (Spec.map ψ)))
      (restrictAdjunction (Spec.map (φ ≫ ψ))) (compositionRestrictionIso φ ψ).hom =
        (compositionPushforwardIso φ ψ).hom := by
  have h := conjugateEquiv_comp
    ((restrictAdjunction (Spec.map φ)).comp (restrictAdjunction (Spec.map ψ)))
    (restrictAdjunction (Spec.map ψ ≫ Spec.map φ))
    (restrictAdjunction (Spec.map (φ ≫ ψ)))
    (restrictFunctorComp (Spec.map ψ) (Spec.map φ)).hom
    (restrictFunctorCongr (Spec.map_comp φ ψ)).hom
  rw [AdjunctionCoherence.conjugate_restrictFunctorComp_hom,
    AdjunctionCoherence.conjugate_restrictFunctorCongr_hom] at h
  calc
    _ = (pushforwardComp (Spec.map ψ) (Spec.map φ)).hom ≫
        (pushforwardCongr (Spec.map_comp φ ψ)).inv := h.symm
    _ = _ := by
      unfold compositionPushforwardIso
      rw [Iso.trans_hom, AdjunctionCoherence.pushforwardCongr_symm_hom]

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange
