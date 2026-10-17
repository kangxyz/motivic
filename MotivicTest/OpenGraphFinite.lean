/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.OpenGraphFinite
/-! Exact whole graph-image transport to finiteness of the original map. -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
variable {U X Y S : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ S) (g : Y ⟶ S)
  (h : U ⟶ Y) (w : j ≫ f = h ≫ g)
  [IsOpenImmersion j] [QuasiCompact j] [IsSeparated g] [IsProper f] [IsAffineHom h]
  (hno : ∀ x : (pullback.lift j h w).image,
    ((pullback.lift j h w).imageι ≫ pullback.fst f g) x ∈ Set.range j)

example : IsFinite h := Scheme.isFinite_of_graph_image_range j f g h w hno

#print axioms Scheme.graph_toImage_isIso_of_range
#print axioms Scheme.isFinite_of_graph_image_range
