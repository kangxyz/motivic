/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Transporting common étale neighborhoods along isomorphisms

The comparison scheme is unchanged. Both Cartesian squares, including their
entire scheme-theoretic fibers, transport along isomorphisms of the pairs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.IsPullback

/-- Transport a neighborhood square while retaining its comparison object. -/
theorem transport_neighborhood
    {C : Type*} [Category* C] {Z X V Z' X' : C}
    {j : Z ⟶ V} {p : V ⟶ X} {a : Z ⟶ X}
    (h : IsPullback j (𝟙 Z) p a) (eZ : Z' ≅ Z) (eX : X' ≅ X)
    (a' : Z' ⟶ X') (ha : eZ.hom ≫ a = a' ≫ eX.hom) :
    IsPullback (eZ.hom ≫ j) (𝟙 Z') (p ≫ eX.inv) a' := by
  apply h.of_iso' eZ (Iso.refl V) eZ eX
  · simp
  · simp
  · simp
  · exact ha

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.Scheme

/-- An isomorphism of the two pairs transports a common étale neighborhood.
No reducedness or pointwise replacement of the Cartesian conditions is used. -/
theorem transport_common_etale_neighborhood
    {Z X Y V Z' X' Y' : Scheme.{u}}
    (p : V ⟶ X) (q : V ⟶ Y) [Etale p] [Etale q]
    (j : Z ⟶ V) (a : Z ⟶ X) (b : Z ⟶ Y)
    (hp : IsPullback j (𝟙 Z) p a) (hq : IsPullback j (𝟙 Z) q b)
    (eZ : Z' ≅ Z) (eX : X' ≅ X) (eY : Y' ≅ Y)
    (a' : Z' ⟶ X') (b' : Z' ⟶ Y')
    (ha : eZ.hom ≫ a = a' ≫ eX.hom) (hb : eZ.hom ≫ b = b' ≫ eY.hom) :
    Etale (p ≫ eX.inv) ∧ Etale (q ≫ eY.inv) ∧
      IsPullback (eZ.hom ≫ j) (𝟙 Z') (p ≫ eX.inv) a' ∧
      IsPullback (eZ.hom ≫ j) (𝟙 Z') (q ≫ eY.inv) b' :=
  ⟨inferInstance, inferInstance, hp.transport_neighborhood eZ eX a' ha,
    hq.transport_neighborhood eZ eY b' hb⟩

end AlgebraicGeometry.Scheme
