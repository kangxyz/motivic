/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingComponentLaws

/-!
# Effective finite open module descent

The equalizer sheaf has actual local inverses derived from the standard
normalized overlap cocycle. Its local comparisons realize the supplied
transition and commute with further open restriction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteOpenModuleGluing

open Scheme.Modules Motivic.OpenModuleGluing

variable {X : Scheme.{u}} {ι : Type u} [Fintype ι]
  (U : ι → X.Opens) (M : ∀ i, (U i).toScheme.Modules)

/-- The finite equalizer sheaf recovers each local module from ordinary descent data. -/
def localIso (d : Datum U M) (i : ι) :
    (restrictFunctor (U i).ι).obj (glued U M d) ≅ M i :=
  localIsoOfComponentLaws U M d i (componentsCompatible U M d i)
    (localComponent_diagonal U M d i)

/-- The local comparison is the original restricted equalizer projection. -/
@[simp] theorem localIso_hom (d : Datum U M) (i : ι) :
    (localIso U M d i).hom = localProjection U M d i := rfl

/-- The actual finite-gluing local comparison is invertible. -/
instance localProjection_isIso (d : Datum U M) (i : ι) :
    IsIso (localProjection U M d i) := (localIso U M d i).isIso_hom

set_option backward.isDefEq.respectTransparency false in
/-- The constructed comparisons realize exactly the originally supplied overlap transition. -/
theorem localIso_transition (d : Datum U M) (i j : ι) :
    (restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).map
        (localIso U M d i).hom ≫ (d.transition i j).hom =
      (overlapRestrictionIso (isPullback_opens_inf (U i) (U j))).hom.app (glued U M d) ≫
        (restrictFunctor (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).map
          (localIso U M d j).hom := by
  have hc := congrArg (fun φ =>
    (restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).map φ ≫
      (restrictAdjunction (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).counit.app
        ((restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).obj (M i)))
      (localProjection_unit U M d i j)
  simp only [Functor.map_comp, Category.assoc] at hc
  rw [(restrictAdjunction (X.homOfLE
      (inf_le_left : U i ⊓ U j ≤ U i))).left_triangle_components,
    Category.comp_id, overlapComparison_mate] at hc
  have hn := (overlapRestrictionIso (isPullback_opens_inf (U i) (U j))).hom.naturality
    (projection U M d j)
  change (restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).map
      ((restrictFunctor (U i).ι).map (projection U M d j)) ≫
      (overlapRestrictionIso (isPullback_opens_inf (U i) (U j))).hom.app
        ((pushforward (U j).ι).obj (M j)) =
    (overlapRestrictionIso (isPullback_opens_inf (U i) (U j))).hom.app (glued U M d) ≫
      (restrictFunctor (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).map
        ((restrictFunctor (U j).ι).map (projection U M d j)) at hn
  rw [← Category.assoc, hn, Category.assoc] at hc
  apply (cancel_mono (d.transition i j).inv).mp
  simpa only [localIso_hom, localProjection, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Functor.map_comp] using hc

/-- Every smaller open recovers the restriction of the original local module. -/
def localRefinementIso (d : Datum U M) (i : ι) {W : Scheme.{u}}
    (f : W ⟶ (U i).toScheme) [IsOpenImmersion f] :
    (restrictFunctor (f ≫ (U i).ι)).obj (glued U M d) ≅ (restrictFunctor f).obj (M i) :=
  (restrictFunctorComp f (U i).ι).app _ ≪≫ (restrictFunctor f).mapIso (localIso U M d i)

end Motivic.FiniteOpenModuleGluing
