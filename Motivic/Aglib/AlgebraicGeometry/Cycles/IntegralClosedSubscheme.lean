/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.IntegralImage
public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Integral closed subschemes
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
/-- An integral closed subscheme specified by its actual ideal sheaf. -/
def IntegralClosedSubscheme (X : Scheme.{u}) : Type u :=
  {I : X.IdealSheafData // IsIntegral I.subscheme}

namespace IntegralClosedSubscheme
open _root_.AlgebraicGeometry.Scheme.Hom _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable (V : IntegralClosedSubscheme X)

noncomputable instance : IsIntegral V.val.subscheme := V.property

/-- The generic point embedded in the ambient scheme. -/
noncomputable def point : X := V.val.subschemeι (genericPoint V.val.subscheme)

/-- The embedded generic point has exactly the given closed subscheme's support. -/
theorem point_spec : IsGenericPoint V.point (V.val.support : Set X) := by
  simpa only [point, Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
    V.val.support.isClosed.closure_eq] using
    (genericPoint_spec V.val.subscheme).image V.val.subschemeι.continuous

/-- The ambient generic point faithfully determines an integral closed subscheme. -/
theorem point_injective : Function.Injective (point (X := X)) := by
  intro V W h
  apply Subtype.ext
  apply idealSheaf_eq_of_support_eq
  apply SetLike.coe_injective
  exact V.point_spec.def.symm.trans ((congrArg (fun x : X => closure ({x} : Set X)) h).trans
    W.point_spec.def)

/-- The actual integral closed image under a finite morphism. -/
noncomputable def finiteImage {Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    IntegralClosedSubscheme Y :=
  ⟨(V.val.subschemeι ≫ f).ker, isIntegral_finiteImage (V.val.subschemeι ≫ f)⟩

/-- Its generic point is the image of the original generic point. -/
theorem point_finiteImage {Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    (V.finiteImage f).point = f V.point := by
  let := isIntegral_finiteImage (V.val.subschemeι ≫ f)
  change (V.val.subschemeι ≫ f).imageι
    (genericPoint (V.val.subschemeι ≫ f).image) = f V.point
  rw [imageι_genericPoint]
  exact Scheme.Hom.comp_apply _ _ _

@[simp]
theorem finiteImage_id : V.finiteImage (𝟙 X) = V := by
  apply point_injective
  rw [point_finiteImage]
  rfl

/-- Equality of actual ideal-sheaf images follows from their faithful generic points. -/
theorem finiteImage_comp {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] : V.finiteImage (f ≫ g) = (V.finiteImage f).finiteImage g := by
  apply point_injective
  simp only [point_finiteImage, Scheme.Hom.comp_apply]

end IntegralClosedSubscheme

end AlgebraicGeometry.Scheme
