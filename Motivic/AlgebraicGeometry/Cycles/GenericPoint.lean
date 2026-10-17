/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralImage
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Integral closed subschemes and their generic points

The ideal-sheaf model of integral closed subschemes has a faithful generic-point
map. Reducedness is used essentially: a reduced closed subscheme's ideal sheaf
is radical, and is therefore recovered from its closed support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

variable {X : Scheme.{u}}

/-- The ideal sheaf of an actual reduced closed subscheme is radical. -/
theorem radical_eq_of_isReduced_subscheme (I : X.IdealSheafData) [IsReduced I.subscheme] :
    I.radical = I := by
  ext U : 2
  change (I.ideal U).radical = I.ideal U
  apply Ideal.radical_eq_iff.mpr
  rw [← I.ker_subschemeι_app U]
  exact (RingHom.ker_isRadical_iff_reduced_of_surjective
    (I.subschemeι_app_surjective U)).mpr inferInstance

/-- Reduced closed subschemes with the same closed support have the same ideal sheaf. -/
theorem idealSheaf_eq_of_support_eq (I J : X.IdealSheafData)
    [IsReduced I.subscheme] [IsReduced J.subscheme] (h : I.support = J.support) : I = J := by
  rw [← radical_eq_of_isReduced_subscheme I, ← radical_eq_of_isReduced_subscheme J,
    ← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.vanishingIdeal_support, h]

/-- An integral closed subscheme specified by its actual ideal sheaf. -/
def IntegralClosedSubscheme (X : Scheme.{u}) : Type u :=
  {I : X.IdealSheafData // IsIntegral I.subscheme}

namespace IntegralClosedSubscheme

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

end Motivic
