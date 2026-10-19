/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Fibers.ResidueFieldMap
public import Mathlib.AlgebraicGeometry.Limits

/-! # Canonical residue-field coproduct decomposition

A reduced discrete scheme is the coproduct of its literal residue-field spectra,
with the canonical residue-field morphisms as coproduct injections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsReduced X] [DiscreteTopology X]

/-- The canonical residue-field components form a coproduct cocone. -/
def residueFieldCofanIsColimit :
    IsColimit (Cofan.mk X X.fromSpecResidueField) := by
  apply Nonempty.some
  apply nonempty_isColimit_cofanMk_of
  · exact (X.residueFieldOpenCover).iSup_opensRange
  · intro x y hxy
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro z hz
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
    exact (hxy ((X.fromSpecResidueField_apply x a).symm.trans
      (ha.trans (hb.symm.trans (X.fromSpecResidueField_apply y b))))).elim

/-- The actual scheme is isomorphic to the coproduct of its residue-field spectra. -/
def residueFieldCoproductIso : (∐ fun x : X ↦ Spec (X.residueField x)) ≅ X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (X.residueFieldCofanIsColimit)

@[reassoc (attr := simp)]
theorem residueFieldCoproductIso_ι_hom (x : X) :
    Sigma.ι (fun x : X ↦ Spec (X.residueField x)) x ≫
      X.residueFieldCoproductIso.hom = X.fromSpecResidueField x := by
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    X.residueFieldCofanIsColimit ⟨x⟩

end AlgebraicGeometry.Scheme
