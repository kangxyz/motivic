/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.GraphClosureEquations
/-! Direct unchanged-coordinate consumer; only the original graph satisfies the equations. -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.GraphClosure
variable {X Y S E D : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  (g : Y ⟶ S) [IsSeparated g] (U : X.Opens) [QuasiCompact U.ι]
  [IsAffine U.toScheme] [IsAffine Y]
  (h : U.toScheme ⟶ Y) (w : U.ι ≫ f = h ≫ g)
  (e : E ⟶ pullback f g) [IsClosedImmersion e]
  (b : U.toScheme ⟶ E) (hb : b ≫ e = graph f g U h w)

include w b hb in
example (d : D ⟶ X) (hcover : ∀ x : X, x ∈ U ∨ x ∈ Set.range d)
    [IsEmpty (pullback (e ≫ pullback.fst f g) d : Scheme.{u})] : IsFinite h :=
  isFinite_of_closed_graph_equations f g U h w e b hb d hcover

omit [IsProper f] [IsSeparated g] [QuasiCompact U.ι]
  [IsAffine U.toScheme] [IsAffine Y] in
example : fromOpen f g U h w ≫ toClosedEquations f g U h w e b hb = b :=
  fromOpen_toClosedEquations f g U h w e b hb

#print axioms isFinite_of_closed_graph_equations
#print axioms boundaryToClosedEquations
end AlgebraicGeometry.Scheme.GraphClosure
