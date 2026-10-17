/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingDatum

/-!
# Global recovery on an actual open cover

Local isomorphisms on a covering family detect global isomorphisms. The
canonical finite compatible-sections construction recovers the original sheaf.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteOpenModuleGluing

open Scheme.Modules Motivic.OpenModuleGluing

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

set_option backward.isDefEq.respectTransparency false in
/-- Actual open restriction isomorphisms on a covering family detect a global isomorphism. -/
theorem isIso_of_cover {P Q : X.Modules} (φ : P ⟶ Q) (hU : ⨆ i, U i = ⊤)
    [∀ i, IsIso ((restrictFunctor (U i).ι).map φ)] : IsIso φ := by
  have hxiso (x : X) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf) := by
    have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hh := (NatIso.isIso_map_iff (restrictStalkNatIso (U i).ι ⟨x, hi⟩) φ).mp
      (by
        change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hi⟩ : U i)).map
          ((toPresheaf (U i).toScheme).map ((restrictFunctor (U i).ι).map φ)))
        infer_instance)
    exact hh
  let P' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨P.presheaf, P.isSheaf⟩
  let Q' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨Q.presheaf, Q.isSheaf⟩
  let φ' : P' ⟶ Q' := ⟨φ.mapPresheaf⟩
  rw [Hom.isIso_iff_isIso_app]
  intro W
  have (x : W) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.val).map φ'.1) :=
    hxiso x.val
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso φ' W

end Motivic.FiniteOpenModuleGluing
