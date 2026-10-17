/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Continuity of parameter products

Products with a fixed parameter preserve existing pullbacks in arbitrary
category universes. A cartesian projection to the identity then makes such
an endofunctor continuous for every base-change-stable precoverage having
cover-specific pullbacks. No existence of all pullbacks is required.
-/

@[expose] public noncomputable section

universe u v

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-- Taking the product on the right preserves existing pullbacks, without
restricting the morphism universe of the category. -/
theorem Limits.prodRight_preservesPullbacks [HasBinaryProducts C] (T : C) :
    PreservesLimitsOfShape WalkingCospan (prod.functor.flip.obj T) := by
  let : PreservesLimitsOfShape (ULiftHom.{v} (ULift.{v} WalkingCospan))
      (prod.functor.obj T) := prod_preservesConnectedLimits T
  let : PreservesLimitsOfShape WalkingCospan (prod.functor.obj T) :=
    preservesLimitsOfShape_of_equiv
      (ULiftHomULiftCategory.equiv.{v, v} WalkingCospan).symm _
  let e : prod.functor.obj T ≅ prod.functor.flip.obj T :=
    NatIso.ofComponents (fun X ↦ prod.braiding T X)
      (fun f ↦ braid_natural (𝟙 T) f)
  exact preservesLimitsOfShape_of_natIso e

/-- An endofunctor with cartesian projection to the identity preserves all
coverings of a base-change-stable precoverage. -/
theorem Precoverage.le_comap_of_cartesianToId (J : Precoverage C)
    [J.IsStableUnderBaseChange] (F : C ⥤ C) (π : F ⟶ 𝟭 C)
    (hπ : ∀ {X Y : C} (f : X ⟶ Y), IsPullback (F.map f) (π.app X) (π.app Y) f) :
    J ≤ J.comap F := by
  intro X R hR
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  exact Precoverage.mem_coverings_of_isPullback f hR (π.app X)
    (fun i ↦ F.map (f i)) (fun i ↦ π.app (Y i)) (fun i ↦ hπ (f i))

/-- A pullback-preserving endofunctor with cartesian projection to the
identity is continuous for the generated topology. -/
theorem Functor.isContinuous_of_cartesianToId (J : Precoverage C)
    [J.IsStableUnderBaseChange] [J.HasPullbacks] (F : C ⥤ C)
    [PreservesLimitsOfShape WalkingCospan F] (π : F ⟶ 𝟭 C)
    (hπ : ∀ {X Y : C} (f : X ⟶ Y), IsPullback (F.map f) (π.app X) (π.app Y) f) :
    F.IsContinuous J.toGrothendieck J.toGrothendieck :=
  Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy F J J
    (J.le_comap_of_cartesianToId F π hπ)

/-- Product with a fixed parameter is continuous for any base-change-stable
precoverage with cover-specific pullbacks. -/
theorem Functor.prodRight_isContinuous [HasBinaryProducts C] (J : Precoverage C)
    [J.IsStableUnderBaseChange] [J.HasPullbacks] (T : C) :
    (prod.functor.flip.obj T).IsContinuous J.toGrothendieck J.toGrothendieck := by
  let : PreservesLimitsOfShape WalkingCospan (prod.functor.flip.obj T) :=
    Limits.prodRight_preservesPullbacks T
  apply Functor.isContinuous_of_cartesianToId J _
    { app X := prod.fst
      naturality X Y f := prod.map_fst f (𝟙 T) }
  intro X Y f
  exact (IsPullback.of_prod_fst_with_id f T).flip

end CategoryTheory
