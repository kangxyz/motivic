/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue-field isomorphism at an actual lifted canonical point

A lift of `Spec κ(x) ⟶ X` through a scheme morphism gives an isomorphism
on residue fields at the image of that lift. The conclusion is at the actual
chosen point; no replacement point, étaleness, or field extension is used.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_residueFieldMap_of_residuePoint_lift
    {U X : Scheme.{u}} (f : U ⟶ X) (x : X)
    (u : U) (b : U.residueField u ⟶ X.residueField x)
    (ht : (Spec.map b ≫ U.fromSpecResidueField u) ≫ f = X.fromSpecResidueField x) :
    IsIso (f.residueFieldMap u) := by
  have hu : f u = x := by
    have h := congrArg (fun g : Spec (X.residueField x) ⟶ X ↦ g default) ht
    change f (U.fromSpecResidueField u (Spec.map b default)) =
      X.fromSpecResidueField x default at h
    simpa only [Scheme.fromSpecResidueField_apply] using h
  subst x
  have hcomp : f.residueFieldMap u ≫ b = 𝟙 _ := by
    rw [← Spec.map_inj]
    apply (cancel_mono (X.fromSpecResidueField (f u))).mp
    change Spec.map b ≫ U.fromSpecResidueField u ≫ f = _ at ht
    rw [Spec.map_comp, Category.assoc,
      f.SpecMap_residueFieldMap_fromSpecResidueField u, Spec.map_id]
    exact ht.trans (Category.id_comp _).symm
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap u).hom.injective, fun z ↦ ⟨b z, ?_⟩⟩
  apply b.hom.injective
  exact congrArg (fun g : X.residueField (f u) ⟶ X.residueField (f u) ↦ g (b z)) hcomp

set_option backward.isDefEq.respectTransparency false in
/-- The actual point of a lift of the canonical residue-field morphism has
an isomorphic residue-field map. -/
theorem isIso_residueFieldMap_of_canonicalPoint_lift
    {U X : Scheme.{u}} (f : U ⟶ X) (x : X)
    (t : Spec (X.residueField x) ⟶ U) (ht : t ≫ f = X.fromSpecResidueField x) :
    IsIso (f.residueFieldMap (t default)) := by
  obtain ⟨⟨u, b⟩, hb⟩ := (Scheme.SpecToEquivOfField (X.residueField x) U).symm.surjective t
  have hb' : Spec.map b ≫ U.fromSpecResidueField u = t := hb
  have hiso := isIso_residueFieldMap_of_residuePoint_lift f x u b (by rw [hb']; exact ht)
  have heq : t default = u :=
    (congrArg (fun g : Spec (X.residueField x) ⟶ U ↦ g default) hb').symm.trans
      (Scheme.fromSpecResidueField_apply (X := U) u (Spec.map b default))
  exact heq.symm ▸ hiso

end AlgebraicGeometry.Scheme.Hom
