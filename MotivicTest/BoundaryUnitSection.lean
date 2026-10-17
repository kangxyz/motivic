/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.BoundaryUnitSection

/-! # The constructed boundary denominator really generates -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.CoherentGraph
set_option linter.hashCommand false
universe u
example {Z : Scheme.{u}}
    (W : Z.Opens) (M : Z.Modules)
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    IsIso ((unitHomGlobalSectionsEquiv W.toScheme (M.restrict W.ι)).symm
      (((restrictedSectionsIso W.ι).app M).inv
        ((M.presheaf.mapIso (eqToIso (Scheme.Opens.opensRange_ι W)).op).hom
          ((openUnitSectionsIso W M e).inv (1 : Γ(W.toScheme, ⊤)))))) :=
  openUnitSectionsIso_inv_one_isIso W M e

#print axioms openUnitSectionsIso_inv_one_isIso
