/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# Boundary frames at multiples of one twist period

A single actual frame of the restricted O(d) determines the frames and generating
sections of O(d*n) by native twist multiplication. No frame of O(1), new choices,
reduced boundary, or change of parameter scheme is required.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.PeriodicBoundaryTwists`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.PeriodicBoundaryAffineNeighborhood`.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Tensor powers of the same frame trivialize every multiple of its twist period. -/
def periodicTwistUnitIso (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι) (d : ℤ)
    (ed : (Modules.pullback g).obj (twistingSheaf R ι d) ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    (n : ℕ) → (Modules.pullback g).obj (twistingSheaf R ι (d * (n : ℤ))) ≅
      SheafOfModules.unit Z.ringCatSheaf
  | 0 => by
      simpa only [Nat.cast_zero, mul_zero] using
        (Modules.pullback g).mapIso (twistingZeroIso R ι) ≪≫ pullbackUnitIso g
  | n + 1 => by
      let := Modules.Pullback.Tensor.pullbackTensorMap_isIso g (twistingSheaf R ι (d * (n : ℤ)))
        (twistingSheaf R ι d)
      have hdegree : d * ((n + 1 : ℕ) : ℤ) = d * (n : ℤ) + d := by
        simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      exact (Modules.pullback g).mapIso
          (eqToIso (congrArg (twistingSheaf R ι) hdegree)) ≪≫
        ((Modules.pullback g).mapIso (twistingTensorIso R ι (d * (n : ℤ)) d)).symm ≪≫
        asIso (pullbackTensorMap g (twistingSheaf R ι (d * (n : ℤ))) (twistingSheaf R ι d)) ≪≫
        tensorSheafIso Z (periodicTwistUnitIso R ι g d ed n) ed ≪≫
        tensorSheafLeftUnit Z (SheafOfModules.unit Z.ringCatSheaf)

/-- The actual generating section induced by the same periodic frame. -/
def periodicTwistUnitSection (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι) (d : ℤ)
    (ed : (Modules.pullback g).obj (twistingSheaf R ι d) ≅
      SheafOfModules.unit Z.ringCatSheaf) (n : ℕ) :
    Γ((Modules.pullback g).obj (twistingSheaf R ι (d * (n : ℤ))), ⊤) :=
  (periodicTwistUnitIso R ι g d ed n).inv.app ⊤ (1 : Γ(Z, ⊤))

/-- Its coefficient is literally one under the constructed full-source
trivialization; this is a generating section, not a possibly vanishing lift. -/
theorem periodicTwistUnitSection_coefficient (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι) (d : ℤ)
    (ed : (Modules.pullback g).obj (twistingSheaf R ι d) ≅
      SheafOfModules.unit Z.ringCatSheaf) (n : ℕ) :
    (periodicTwistUnitIso R ι g d ed n).hom.app ⊤
      (periodicTwistUnitSection R ι g d ed n) = (1 : Γ(Z, ⊤)) := by
  simpa only [periodicTwistUnitSection, Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Modules.Hom.id_app, ConcreteCategory.id_apply] using
      congrArg (fun f => f.app ⊤ (1 : Γ(Z, ⊤))) (periodicTwistUnitIso R ι g d ed n).inv_hom_id

/-- The distinguished section is a genuine basis: its original unit-to-
module map is an isomorphism, not merely a section nonzero at some points. -/
theorem periodicTwistUnitSection_isIso (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι) (d : ℤ)
    (ed : (Modules.pullback g).obj (twistingSheaf R ι d) ≅
      SheafOfModules.unit Z.ringCatSheaf) (n : ℕ) :
    IsIso ((unitHomGlobalSectionsEquiv Z
      ((Modules.pullback g).obj (twistingSheaf R ι (d * (n : ℤ))))).symm
        (periodicTwistUnitSection R ι g d ed n)) := by
  have he : (unitHomGlobalSectionsEquiv Z
      ((Modules.pullback g).obj (twistingSheaf R ι (d * (n : ℤ))))).symm
        (periodicTwistUnitSection R ι g d ed n) =
      (periodicTwistUnitIso R ι g d ed n).inv := by
    apply (unitHomGlobalSectionsEquiv Z _).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.CoherentGraph
