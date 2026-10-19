/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
/-! # Determinant norms under an actual scheme isomorphism over Spec

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.SchemeIso`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`GenericFiber.LineRatioIso`, `Norm.SectionPairNormParameterNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u

namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- Determinant norm respects an actual scheme isomorphism over the displayed
Spec base. No domain or reducedness hypothesis is imposed on either source. -/
theorem norm_appTop_of_iso {R : Type u} [CommRing R] {B B' : Scheme.{u}}
    (p : B ⟶ Spec (.of R)) (q : B' ⟶ Spec (.of R))
    (e : B ≅ B') (he : e.hom ≫ q = p) (b : Γ(B', ⊤)) :
    let : Algebra R Γ(B, ⊤) := (scalarMap p).toAlgebra
    let : Algebra R Γ(B', ⊤) := (scalarMap q).toAlgebra
    Algebra.norm R (e.hom.appTop b) = Algebra.norm R b := by
  let : Algebra R Γ(B, ⊤) := (scalarMap p).toAlgebra
  let : Algebra R Γ(B', ⊤) := (scalarMap q).toAlgebra
  let ei : Γ(B', ⊤) ≅ Γ(B, ⊤) :=
    { hom := e.hom.appTop
      inv := e.inv.appTop
      hom_inv_id := by rw [← Scheme.Hom.comp_appTop]; simp
      inv_hom_id := by rw [← Scheme.Hom.comp_appTop]; simp }
  have hc : CommRingCat.ofHom (scalarMap q) ≫ ei.hom =
      CommRingCat.ofHom (scalarMap p) := by
    change (Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop ≫ e.hom.appTop =
      (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop
    rw [← Scheme.Hom.comp_appTop, he]
  let ea : Γ(B', ⊤) ≃ₐ[R] Γ(B, ⊤) :=
    { ei.commRingCatIsoToRingEquiv with
      commutes' a := congrArg (fun h : CommRingCat.of R ⟶ Γ(B, ⊤) => h.hom a) hc }
  exact Algebra.norm_eq_of_algEquiv ea b

end AlgebraicGeometry.FiniteSchemeNormBaseChange
