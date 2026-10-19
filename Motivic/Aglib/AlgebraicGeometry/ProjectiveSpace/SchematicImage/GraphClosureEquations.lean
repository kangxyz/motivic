/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.GraphClosureFiniteness
/-! # Original graph equations extend to the whole schematic closure and boundary

Closed equations satisfied on the original graph hold scheme-theoretically on its image.
Thus empty infinity of those equations proves finiteness of the unchanged coordinate map.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.GraphClosure
variable {X Y S E D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens)
  (h : U.toScheme ⟶ Y) (w : U.ι ≫ f = h ≫ g)
  (e : E ⟶ pullback f g) [IsClosedImmersion e]
  (b : U.toScheme ⟶ E) (hb : b ≫ e = graph f g U h w)

/-- The original graph equations factor the actual schematic image, not its reduction. -/
def toClosedEquations : closure f g U h w ⟶ E :=
  IsClosedImmersion.lift e (graph f g U h w).imageι (by
    rw [IdealSheafData.ker_subschemeι, ← hb]
    exact b.le_ker_comp e)

@[reassoc (attr := simp)]
theorem toClosedEquations_fac :
    toClosedEquations f g U h w e b hb ≫ e = (graph f g U h w).imageι :=
  IsClosedImmersion.lift_fac ..

instance toClosedEquations_closed : IsClosedImmersion (toClosedEquations f g U h w e b hb) := by
  have : IsClosedImmersion (toClosedEquations f g U h w e b hb ≫ e) := by
    rw [toClosedEquations_fac]
    infer_instance
  exact IsClosedImmersion.of_comp _ e

/-- Original representatives are unchanged by the extension to the schematic closure. -/
@[reassoc]
theorem fromOpen_toClosedEquations :
    fromOpen f g U h w ≫ toClosedEquations f g U h w e b hb = b := by
  apply (cancel_mono e).mp
  simp only [Category.assoc, toClosedEquations_fac, Hom.toImage_imageι]
  exact hb.symm

/-- The full graph boundary maps into the full closed-equation boundary. No support-only
substitution or nilpotent removal is made. -/
def boundaryToClosedEquations (d : D ⟶ X) :
    pullback (toSource f g U h w) d ⟶ pullback (e ≫ pullback.fst f g) d :=
  pullback.lift
    (pullback.fst (toSource f g U h w) d ≫ toClosedEquations f g U h w e b hb)
    (pullback.snd (toSource f g U h w) d) (by
      simp only [Category.assoc, toClosedEquations_fac_assoc]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem boundaryToClosedEquations_fst (d : D ⟶ X) :
    boundaryToClosedEquations f g U h w e b hb d ≫
      pullback.fst (e ≫ pullback.fst f g) d =
    pullback.fst (toSource f g U h w) d ≫ toClosedEquations f g U h w e b hb := by
  simp [boundaryToClosedEquations]

@[reassoc (attr := simp)]
theorem boundaryToClosedEquations_snd (d : D ⟶ X) :
    boundaryToClosedEquations f g U h w e b hb d ≫
      pullback.snd (e ≫ pullback.fst f g) d = pullback.snd (toSource f g U h w) d := by
  simp [boundaryToClosedEquations]

include w b hb in
/-- Empty infinity of the actual graph equations implies finiteness of the original map. -/
theorem isFinite_of_closed_graph_equations [IsProper f] [IsSeparated g]
    [QuasiCompact U.ι] [IsAffineHom h]
    (d : D ⟶ X) (hcover : ∀ x : X, x ∈ U ∨ x ∈ Set.range d)
    [IsEmpty (pullback (e ≫ pullback.fst f g) d : Scheme.{u})] : IsFinite h := by
  have : IsEmpty (pullback (toSource f g U h w) d : Scheme.{u}) :=
    ⟨fun x => isEmptyElim (boundaryToClosedEquations f g U h w e b hb d x)⟩
  exact isFinite_of_empty_graph_boundary f g U h w d hcover
end AlgebraicGeometry.Scheme.GraphClosure
