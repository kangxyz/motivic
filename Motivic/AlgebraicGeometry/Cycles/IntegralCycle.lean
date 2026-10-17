/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GenericPoint
public import Motivic.AlgebraicGeometry.Cycles.FiniteSupport

/-!
# Pushforward on actual integral closed-subscheme cycles

The generators are ideal sheaves whose associated closed subschemes are
integral. Finite pushforward uses the actual scheme-theoretic image, weighted
by the residue-field degree at the embedded generic point. The generic-point
map is injective, and its induced map on cycles intertwines this construction
with finite point-cycle pushforward. Identity and composition are proved.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

/-- Integer cycles on actual integral closed subschemes. -/
abbrev IntegralCycle (X : Scheme.{u}) : Type u := IntegralClosedSubscheme X →₀ ℤ

namespace IntegralClosedSubscheme

variable {X Y : Scheme.{u}} (V : IntegralClosedSubscheme X)

/-- The degree of the actual map from the integral support onto its closed image. -/
noncomputable def imageDegree (f : X ⟶ Y) : ℕ :=
  (V.val.subschemeι ≫ f).toImage.residueDegree (genericPoint V.val.subscheme)

/-- Its degree agrees with the ambient residue-field degree at the embedded generic point. -/
theorem imageDegree_eq (f : X ⟶ Y) : V.imageDegree f = f.residueDegree V.point := by
  have h₁ := residueDegree_comp V.val.subschemeι f (genericPoint V.val.subscheme)
  have h₂ := residueDegree_comp (V.val.subschemeι ≫ f).toImage
    (V.val.subschemeι ≫ f).imageι (genericPoint V.val.subscheme)
  simp only [residueDegree_of_surjectiveOnStalks, mul_one] at h₁
  simp only [Scheme.Hom.toImage_imageι, residueDegree_of_surjectiveOnStalks, one_mul] at h₂
  exact h₂.symm.trans h₁

end IntegralClosedSubscheme

namespace IntegralCycle

variable {X Y Z : Scheme.{u}}

/-- The faithful additive dictionary taking each integral support to its generic point. -/
noncomputable def toPoints : IntegralCycle X →+ FiniteSupportCycle X :=
  Finsupp.mapDomain.addMonoidHom IntegralClosedSubscheme.point

@[simp]
theorem toPoints_single (V : IntegralClosedSubscheme X) (n : ℤ) :
    toPoints (Finsupp.single V n) = Finsupp.single V.point n :=
  Finsupp.mapDomain_single

/-- The ideal-sheaf model loses no cycles under its generic-point representation. -/
theorem toPoints_injective : Function.Injective (toPoints (X := X)) :=
  Finsupp.mapDomain_injective IntegralClosedSubscheme.point_injective

/-- Finite pushforward on the actual ideal-sheaf basis, with actual generic residue degree. -/
noncomputable def finitePushforward (f : X ⟶ Y) [IsFinite f] :
    IntegralCycle X →+ IntegralCycle Y :=
  Finsupp.liftAddHom fun V =>
    { toFun := fun n => Finsupp.single (V.finiteImage f) (n * (f.residueDegree V.point : ℤ))
      map_zero' := by simp
      map_add' := by intro m n; simp [add_mul, Finsupp.single_add] }

@[simp]
theorem finitePushforward_single (f : X ⟶ Y) [IsFinite f]
    (V : IntegralClosedSubscheme X) (n : ℤ) :
    finitePushforward f (Finsupp.single V n) =
      Finsupp.single (V.finiteImage f) (n * (f.residueDegree V.point : ℤ)) :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- The literal generic degree of the source-to-image map is the coefficient. -/
theorem finitePushforward_single_imageDegree (f : X ⟶ Y) [IsFinite f]
    (V : IntegralClosedSubscheme X) (n : ℤ) :
    finitePushforward f (Finsupp.single V n) =
      Finsupp.single (V.finiteImage f) (n * (V.imageDegree f : ℤ)) := by
  rw [V.imageDegree_eq, finitePushforward_single]

@[simp]
theorem finitePushforward_id :
    finitePushforward (𝟙 X) = AddMonoidHom.id (IntegralCycle X) := by
  apply Finsupp.addHom_ext
  intro V n
  simp

/-- Functoriality on actual integral closed subschemes, including image and degree laws. -/
theorem finitePushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g] :
    finitePushforward (f ≫ g) = (finitePushforward g).comp (finitePushforward f) := by
  apply Finsupp.addHom_ext
  intro V n
  simp [IntegralClosedSubscheme.finiteImage_comp, IntegralClosedSubscheme.point_finiteImage,
    residueDegree_comp, mul_assoc, mul_comm]

/-- The geometric and point-cycle constructions agree through the faithful dictionary. -/
theorem toPoints_finitePushforward (f : X ⟶ Y) [IsFinite f] :
    toPoints.comp (finitePushforward f) =
      (FiniteSupportCycle.residuePushforward f).comp toPoints := by
  apply Finsupp.addHom_ext
  intro V n
  simp [IntegralClosedSubscheme.point_finiteImage]

end IntegralCycle

end Motivic
