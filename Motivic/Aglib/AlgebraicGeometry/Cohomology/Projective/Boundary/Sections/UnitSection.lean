/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.FiniteGraphSections

/-! # The constructed boundary denominator really generates -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Transport of the constructed unit boundary section to the restricted
scheme is the original section of the inverse unit trivialization. -/
theorem openUnitSectionsIso_inv_one_restrict {Z : Scheme.{u}}
    (W : Z.Opens) (M : Z.Modules)
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    ((restrictedSectionsIso W.ι).app M).inv
      ((M.presheaf.mapIso (eqToIso (Scheme.Opens.opensRange_ι W)).op).hom
        ((openUnitSectionsIso W M e).inv (1 : Γ(W.toScheme, ⊤)))) =
      e.inv.app ⊤ (1 : Γ(W.toScheme, ⊤)) := by
  let A := M.presheaf.mapIso (eqToIso (Scheme.Opens.opensRange_ι W)).op
  let F := (restrictedSectionsIso W.ι).app M
  let x := e.inv.app ⊤ (1 : Γ(W.toScheme, ⊤))
  change F.inv (A.hom (A.inv (F.hom x))) = x
  have hA := ConcreteCategory.congr_hom A.inv_hom_id (F.hom x)
  change A.hom (A.inv (F.hom x)) = F.hom x at hA
  rw [hA]
  exact ConcreteCategory.congr_hom F.hom_inv_id x

/-- The actual O-to-coefficient map of the transported boundary denominator
is an isomorphism. In particular it is nowhere vanishing on the entire boundary. -/
theorem openUnitSectionsIso_inv_one_isIso {Z : Scheme.{u}}
    (W : Z.Opens) (M : Z.Modules)
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    IsIso ((unitHomGlobalSectionsEquiv W.toScheme (M.restrict W.ι)).symm
      (((restrictedSectionsIso W.ι).app M).inv
        ((M.presheaf.mapIso (eqToIso (Scheme.Opens.opensRange_ι W)).op).hom
          ((openUnitSectionsIso W M e).inv (1 : Γ(W.toScheme, ⊤)))))) := by
  rw [openUnitSectionsIso_inv_one_restrict]
  have he : (unitHomGlobalSectionsEquiv W.toScheme (M.restrict W.ι)).symm
      (e.inv.app ⊤ (1 : Γ(W.toScheme, ⊤))) = e.inv := by
    apply (unitHomGlobalSectionsEquiv W.toScheme _).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.CoherentGraph
