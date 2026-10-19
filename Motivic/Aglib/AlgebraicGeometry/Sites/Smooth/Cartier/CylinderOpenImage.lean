/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Projection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-! # Original cylinder restrictions on the image of an open immersion

These comparisons hold for any ordinary abelian presheaf. They require no
cohomological continuity or sheaf condition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite
universe u w
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k] {Y X : SmoothSite (Spec (.of k))}

/-- An original cylinder class that is zero on an open immersion is zero on the
literal open image, using only the inverse open-image map. -/
theorem cylinder_zero_on_open_image
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    (f : Y ⟶ X) [IsOpenImmersion f.left]
    (x : P.obj (op (a1Cylinder (.of k) X)))
    (hx : P.map (a1Map (.of k) f).op x = 0) :
    P.map (a1Map (.of k) (openInclusion X f.left.opensRange)).op x = 0 := by
  let O := f.left.opensRange
  let g : (opensFunctor X).obj O ⟶ Y := homMk f.left.isoOpensRange.inv (by
    change f.left.isoOpensRange.inv ≫ Y.hom = O.ι ≫ X.hom
    rw [← MorphismProperty.Over.w f, ← Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp])
  have hg : g ≫ f = openInclusion X O := by
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.Hom.isoOpensRange_inv_comp f.left
  rw [← hg, a1Map_comp, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    hx, map_zero]

/-- A nonempty affine open immersion supplies an affine generic base open for
zero of the original whole-cylinder class. -/
theorem exists_affine_generic_open_cylinder_zero_of_openImmersion
    [IsAffine Y.left] [Nonempty Y.left] [IsIntegral X.left]
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    (f : Y ⟶ X) [IsOpenImmersion f.left]
    (x : P.obj (op (a1Cylinder (.of k) X)))
    (hx : P.map (a1Map (.of k) f).op x = 0) :
    ∃ V : X.left.Opens, IsAffineOpen V ∧ genericPoint X.left ∈ V ∧
      P.map (a1Map (.of k) (openInclusion X V)).op x = 0 := by
  refine ⟨f.left.opensRange, isAffineOpen_opensRange f.left, ?_,
    cylinder_zero_on_open_image P f x hx⟩
  apply ((genericPoint_spec X.left).mem_open_set_iff f.left.opensRange.isOpen).mpr
  exact ⟨f.left (Classical.choice inferInstance), Set.mem_univ _, ⟨_, rfl⟩⟩

end AlgebraicGeometry.Scheme.SmoothSite
