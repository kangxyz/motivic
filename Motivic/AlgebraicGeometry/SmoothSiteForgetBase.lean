/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Etale.Field

/-! # Finite separable forgetting of the smooth ground field -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.SmoothSite

variable {S T : Scheme.{u}} (r : T ⟶ S) [Smooth r] [IsSeparated r] [QuasiCompact r]

/-- Keep the scheme and compose its structure morphism with the given smooth base map. -/
def forgetBase : SmoothSite T ⥤ SmoothSite S where
  obj X := mk (X.hom ≫ r)
  map {X Y} a := homMk (X := mk (X.hom ≫ r)) (Y := mk (Y.hom ≫ r)) a.left (by
    change a.left ≫ (Y.hom ≫ r) = X.hom ≫ r
    rw [← Category.assoc, MorphismProperty.Over.w])
  map_id X := by apply MorphismProperty.Over.Hom.ext; rfl
  map_comp a b := by apply MorphismProperty.Over.Hom.ext; rfl

@[simp]
theorem forgetBase_obj_left (X : SmoothSite T) : ((forgetBase r).obj X).left = X.left := rfl

@[simp]
theorem forgetBase_obj_hom (X : SmoothSite T) : ((forgetBase r).obj X).hom = X.hom ≫ r := rfl

@[simp]
theorem forgetBase_map_left {X Y : SmoothSite T} (a : X ⟶ Y) :
    ((forgetBase r).map a).left = a.left := rfl

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The actual scheme map for the specified scalar algebra structure. -/
abbrev finiteSeparableBaseMap : Spec (.of L) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L))

variable [Module.Finite k L] [Algebra.IsSeparable k L]

instance finiteSeparableBaseMap_etale : Etale (finiteSeparableBaseMap k L) := by
  let : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  let : Algebra.Etale k L :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

instance finiteSeparableBaseMap_isFinite : IsFinite (finiteSeparableBaseMap k L) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Forget the finite separable ground extension, not Weil restriction of scalars. -/
def finiteSeparableForgetBase : SmoothSite (Spec (.of L)) ⥤ SmoothSite (Spec (.of k)) :=
  forgetBase (finiteSeparableBaseMap k L)

end Motivic.SmoothSite
