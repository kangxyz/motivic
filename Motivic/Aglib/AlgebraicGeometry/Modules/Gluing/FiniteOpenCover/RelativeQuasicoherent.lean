/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.FiniteOpenCover.Quasicoherent

/-!
# Quasi-coherence over the union of the actual gluing opens

The ambient equalizer need not be quasi-coherent outside the union of its
charts. Its restriction to that union is quasi-coherent, using actual
restriction-composition maps and the open-subscheme isomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover

open Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u} [Fintype ι]
  (U : ι → X.Opens) (M : ∀ i, (U i).toScheme.Modules) (d : Datum U M)

/-- The relative local comparison uses the actual nested-open isomorphism and restrictions. -/
def relativeLocalIso (V : X.Opens) (i : ι) (hi : U i ≤ V) :
    (restrictFunctor (V.ι ⁻¹ᵁ U i).ι).obj ((restrictFunctor V.ι).obj (glued U M d)) ≅
      (restrictFunctor (Scheme.Opens.isoOfLE hi).hom).obj (M i) :=
  (restrictFunctorComp (V.ι ⁻¹ᵁ U i).ι V.ι).symm.app _ ≪≫
    (restrictFunctorCongr (Scheme.Opens.isoOfLE_hom_ι hi).symm).app _ ≪≫
      localRefinementIso U M d i (Scheme.Opens.isoOfLE hi).hom

/-- The restriction to the actual union is quasi-coherent from the local coefficients alone. -/
theorem glued_restrict_isQuasicoherent (V : X.Opens) (hU : ⨆ i, U i = V)
    [∀ i, (M i).IsQuasicoherent] :
    ((restrictFunctor V.ι).obj (glued U M d)).IsQuasicoherent := by
  have hi (i : ι) : U i ≤ V := (le_iSup U i).trans hU.le
  have (i : ι) : ((restrictFunctor (V.ι ⁻¹ᵁ U i).ι).obj
      ((restrictFunctor V.ι).obj (glued U M d))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (V.ι ⁻¹ᵁ U i).toScheme.ringCatSheaf).prop_of_iso
      (relativeLocalIso U M d V i (hi i)).symm inferInstance
  apply isQuasicoherent_of_cover (fun i => V.ι ⁻¹ᵁ U i)
    ((restrictFunctor V.ι).obj (glued U M d))
  rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Opens.ι_preimage_self]

end AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover
