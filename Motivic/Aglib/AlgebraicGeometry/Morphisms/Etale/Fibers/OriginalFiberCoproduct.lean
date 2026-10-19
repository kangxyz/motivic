/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Properties.Discrete.DiscreteReducedCoproduct

/-! # Étale fibers decomposed using the original scheme's residue fields

The index is the actual set of original points above the base point. The
component morphisms are the native `asFiberHom`, transported only along the
index's defining equality, not replaced by residue fields of new fiber points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)

/-- The literal original residue-field point, regarded as a morphism to the chosen fiber. -/
def originalFiberComponent (x : f ⁻¹' {y}) : Spec (X.residueField x.1) ⟶ f.fiber y := by
  rcases x with ⟨x, hx⟩
  change f x = y at hx
  subst y
  exact f.asFiberHom x

@[reassoc (attr := simp)]
theorem originalFiberComponent_fiberι (x : f ⁻¹' {y}) :
    f.originalFiberComponent y x ≫ f.fiberι y = X.fromSpecResidueField x.1 := by
  rcases x with ⟨x, hx⟩
  change f x = y at hx
  subst y
  exact f.asFiberHom_fiberι x

/-- The field-valued structural map retains the native residue-field homomorphism. -/
def originalFiberFieldMap (x : f ⁻¹' {y}) :
    Spec (X.residueField x.1) ⟶ Spec (Y.residueField y) := by
  rcases x with ⟨x, hx⟩
  change f x = y at hx
  subst y
  exact Spec.map (f.residueFieldMap x)

@[reassoc (attr := simp)]
theorem originalFiberComponent_fiberToSpecResidueField (x : f ⁻¹' {y}) :
    f.originalFiberComponent y x ≫ f.fiberToSpecResidueField y =
      f.originalFiberFieldMap y x := by
  rcases x with ⟨x, hx⟩
  change f x = y at hx
  subst y
  exact f.asFiberHom_fiberToSpecResidueField x

@[simp]
theorem originalFiberComponent_apply (x : f ⁻¹' {y}) (z) :
    f.originalFiberComponent y x z = (f.fiberHomeo y).symm x := by
  apply (f.fiberι y).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply, originalFiberComponent_fiberι,
    X.fromSpecResidueField_apply, fiberι_fiberHomeo_symm]

instance [Etale f] (x : f ⁻¹' {y}) : IsOpenImmersion (f.originalFiberComponent y x) := by
  rcases x with ⟨x, hx⟩
  change f x = y at hx
  subst y
  exact inferInstanceAs (IsOpenImmersion (f.asFiberHom x))

/-- These actual original-field maps form an open cover of the actual fiber. -/
def originalFiberOpenCover [Etale f] : (f.fiber y).OpenCover :=
  Cover.mkOfCovers _ (fun x : f ⁻¹' {y} ↦ Spec (X.residueField x.1))
    (f.originalFiberComponent y) (fun z ↦
      ⟨f.fiberHomeo y z, IsLocalRing.closedPoint _,
        (originalFiberComponent_apply f y (f.fiberHomeo y z) _).trans
        ((f.fiberHomeo y).symm_apply_apply z)⟩)

/-- The fiber is the coproduct of the original residue fields over the original fiber index. -/
def originalFiberCofanIsColimit [Etale f] :
    IsColimit (Cofan.mk (f.fiber y) (f.originalFiberComponent y)) := by
  apply Nonempty.some
  apply nonempty_isColimit_cofanMk_of
  · exact (f.originalFiberOpenCover y).iSup_opensRange
  · intro x x' hxx'
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro z hz
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
    apply False.elim
    apply hxx'
    apply (f.fiberHomeo y).symm.injective
    simpa only [originalFiberComponent_apply] using ha.trans hb.symm

/-- Canonical scheme decomposition, indexed by original points and original residue fields. -/
def originalFiberCoproductIso [Etale f] :
    (∐ fun x : f ⁻¹' {y} ↦ Spec (X.residueField x.1)) ≅ f.fiber y :=
  (colimit.isColimit _).coconePointUniqueUpToIso (f.originalFiberCofanIsColimit y)

@[reassoc (attr := simp)]
theorem originalFiberCoproductIso_ι_hom [Etale f] (x : f ⁻¹' {y}) :
    Sigma.ι (fun x : f ⁻¹' {y} ↦ Spec (X.residueField x.1)) x ≫
      (f.originalFiberCoproductIso y).hom = f.originalFiberComponent y x :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (f.originalFiberCofanIsColimit y) ⟨x⟩

end AlgebraicGeometry.Scheme.Hom
