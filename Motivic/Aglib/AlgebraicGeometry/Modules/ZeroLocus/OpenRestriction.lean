/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Restricting the whole zero scheme to an open containing its support

Intended upstream module: `Aglib.AlgebraicGeometry.Modules.ZeroLocus.OpenRestriction`.
Incoming project consumers:
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.PointCycle`,
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.GraphTwistedPoleCorrespondence`,
`Motivic.Transfers.Presheaf.Actions.Pencils.CorrectionBoundary`,
`Motivic.Transfers.Presheaf.Actions.Pencils.GraphBoundary`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- Restricting the actual zero scheme to an open containing its entire support
is an isomorphism, including its original nilpotent structure. -/
def zeroRestrictionIso {C U : Scheme.{u}} {M : C.Modules} [M.IsQuasicoherent]
    (a : M ⟶ SheafOfModules.unit C.ringCatSheaf)
    (j : U ⟶ C) [IsOpenImmersion j]
    (ha : Set.range (zeroInclusion a) ⊆ Set.range j) :
    zeroScheme (pullbackToUnit a j) ≅ zeroScheme a := by
  have : Surjective (pullback.snd j (zeroInclusion a)) := by
    constructor
    intro x
    change x ∈ Set.range (pullback.snd j (zeroInclusion a))
    rw [Scheme.Pullback.range_snd]
    exact ha ⟨x, rfl⟩
  have : IsIso (pullback.snd j (zeroInclusion a)) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  exact zeroSchemePullbackIso a j ≪≫ asIso (pullback.snd j (zeroInclusion a))

@[reassoc]
theorem zeroRestrictionIso_hom_inclusion {C U : Scheme.{u}} {M : C.Modules} [M.IsQuasicoherent]
    (a : M ⟶ SheafOfModules.unit C.ringCatSheaf)
    (j : U ⟶ C) [IsOpenImmersion j]
    (ha : Set.range (zeroInclusion a) ⊆ Set.range j) :
    (zeroRestrictionIso a j ha).hom ≫ zeroInclusion a =
      zeroInclusion (pullbackToUnit a j) ≫ j := by
  simp only [zeroRestrictionIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, zeroSchemePullbackIso_hom_fst_assoc]

end AlgebraicGeometry.Scheme.Modules.Hom
