module

public import Motivic.Cohomology.Hypercohomology

/-! # Actual shift comparisons for unbounded hypercohomology -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian Opposite

universe w t v u
namespace Motivic.Hypercohomology
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- The original derived localization and signed shift give the actual shifted target. -/
def shiftTargetIso (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ)
    (q p : ℤ) : (DerivedCategory.Q.obj (K⟦q⟧))⟦p⟧ ≅
      (DerivedCategory.Q.obj K)⟦q + p⟧ :=
  (shiftFunctor _ p).mapIso ((DerivedCategory.Q.commShiftIso q).app K) ≪≫
    (shiftFunctorAdd _ q p).symm.app (DerivedCategory.Q.obj K)

/-- Hypercohomology of the actual signed shift, in every integer degree and every site object. -/
def shiftAddEquiv (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ)
    (q p : ℤ) (X : C) : H J (K⟦q⟧) p X ≃+ H J K (q + p) X where
  toEquiv := Iso.homCongr (Iso.refl _) (shiftTargetIso J K q p)
  map_add' f g := by simp [Iso.homCongr]

/-- The shift comparison commutes with actual geometric restriction. -/
theorem shiftAddEquiv_restriction
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (q p : ℤ)
    {X Y : C} (f : X ⟶ Y) (x : H J (K⟦q⟧) p Y) :
    shiftAddEquiv J K q p X (restriction J (K⟦q⟧) p f x) =
      restriction J K (q + p) f (shiftAddEquiv J K q p Y x) := by
  change (𝟙 _ ≫ (_ ≫ x) ≫ (shiftTargetIso J K q p).hom) =
    _ ≫ (𝟙 _ ≫ x ≫ (shiftTargetIso J K q p).hom)
  simp only [Category.id_comp, Category.assoc]


/-- The shift comparison is an isomorphism of genuine hypercohomology presheaves. -/
def shiftPresheafIso (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ)
    (q p : ℤ) : presheaf J (K⟦q⟧) p ≅ presheaf J K (q + p) :=
  NatIso.ofComponents
    (fun X => (shiftAddEquiv J K q p X.unop).toAddCommGrpIso) (by
      intro X Y f
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      exact shiftAddEquiv_restriction J K q p f.unop x)

end Motivic.Hypercohomology
