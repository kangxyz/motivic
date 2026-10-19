/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.OpenChart

/-! # Point properties on actual open charts of a schematic image -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Transport along an actual chart isomorphism, retaining the original inclusions. -/
theorem point_property_of_pullback_chart {Y U Z G : Scheme.{u}}
    (f : Z ⟶ Y) (j : U ⟶ Y) (i : G ⟶ U) (e : pullback j f ≅ G)
    (he : e.hom ≫ i = pullback.fst j f) (P : Set Y)
    (H : ∀ z : G, j (i z) ∈ P)
    (x : Z) (hx : f x ∈ Set.range j) : f x ∈ P := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback j f) a x ha
  have ht' : i (e.hom t) = a := by
    have hh := congrArg (fun m : pullback j f ⟶ U => m t) he
    exact hh.trans ht
  have hz := H (e.hom t)
  rwa [ht', ha] at hz

end AlgebraicGeometry.Scheme
