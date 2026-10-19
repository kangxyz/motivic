/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.GraphClosureFiniteness
/-! Direct finiteness of the unchanged affine coordinate map from its actual empty boundary. -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.GraphClosure
variable {X Y S D : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  (g : Y ⟶ S) [IsSeparated g] (U : X.Opens) [QuasiCompact U.ι]
  [IsAffine U.toScheme] [IsAffine Y]
  (h : U.toScheme ⟶ Y) (w : U.ι ≫ f = h ≫ g)

example (d : D ⟶ X) (hcover : ∀ x : X, x ∈ U ∨ x ∈ Set.range d)
    [IsEmpty (pullback (toSource f g U h w) d : Scheme.{u})] : IsFinite h :=
  isFinite_of_empty_graph_boundary f g U h w d hcover

example (hno : ∀ c : closure f g U h w, toSource f g U h w c ∈ U) :
    IsFinite h := isFinite_of_no_graph_infinity f g U h w hno

omit [IsProper f] [IsAffine U.toScheme] [IsAffine Y] in
example (hno : ∀ c : closure f g U h w, toSource f g U h w c ∈ U) :
    IsIso (graph f g U h w).toImage :=
  fromOpen_isIso_of_no_infinity f g U h w hno

#print axioms isFinite_of_empty_graph_boundary
#print axioms fromOpenToPreimage_isIso_of_separated
end AlgebraicGeometry.Scheme.GraphClosure
