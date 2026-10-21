/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.WholeBase.SquareMaps
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-! # Original open inclusions for a base-restricted whole affine line

The comparison is identity on schemes. Its factorization identifies the actual
ambient restriction with the original open inclusion, for any abelian presheaf.
The existential adapter is kept independent of cohomology and its coefficients.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Hom
universe w u
namespace AlgebraicGeometry.Scheme.Hom

/-- The smoothness instance used in this module. -/
local instance openMapsSmooth {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

variable (k : Type u) [Field k] (R : Type u) [CommRing R]
  {X : Scheme.{u}} [IsAffine X]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 q]

/-- Identity on an original etale leg, with its two smooth-site structures. -/
def originalEtaleComparison {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ originalAmbientSite k R t q) [Etale p.left] :
    originalEtaleSite k R t q p.left ⟶ Y :=
  SmoothSite.homMk (𝟙 _) (by
    change (𝟙 Y.left) ≫ Y.hom = p.left ≫ (originalAmbientSite k R t q).hom
    rw [Category.id_comp, MorphismProperty.Over.w])

/-- The comparison preserves the original etale map, not only its image. -/
lemma originalEtaleComparison_comp {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ originalAmbientSite k R t q) [Etale p.left] :
    originalEtaleComparison k R t q p ≫ p = originalEtaleArrow k R t q p.left := by
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp p.left

/-- A zero etale restriction remains zero under the identity site comparison. -/
lemma originalEtale_restriction_zero
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ originalAmbientSite k R t q) [Etale p.left]
    (x : P.obj (op (originalAmbientSite k R t q))) (hx : P.map p.op x = 0) :
    P.map (originalEtaleArrow k R t q p.left).op x = 0 := by
  rw [← originalEtaleComparison_comp k R t q p, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]
  exact (congrArg (P.map (originalEtaleComparison k R t q p).op) hx).trans (map_zero _)

/-- Identity on the original open, with the two actual smooth-site structures. -/
def boundaryBaseOpenComparison
    (U : X.Opens) (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen q U V).toScheme] :
    (SmoothSite.opensFunctor (originalAmbientSite k R t q)).obj
      (boundaryBaseSourceOpen q U V) ⟶ boundaryBaseAmbientSite k R t q U V :=
  SmoothSite.homMk (𝟙 _) (by
    rw [Category.id_comp, boundaryBaseAmbientSite_hom]
    rfl)

/-- The comparison followed by ambient restriction is the literal open inclusion. -/
lemma boundaryBaseOpenComparison_comp
    (U : X.Opens) (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen q U V).toScheme] :
    boundaryBaseOpenComparison k R t q U V ≫ boundaryBaseAmbientRestriction k R t q U V =
      SmoothSite.openInclusion (originalAmbientSite k R t q)
        (boundaryBaseSourceOpen q U V) := by
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

/-- Zero under the actual ambient restriction gives zero on the original open. -/
lemma boundaryBase_restriction_open_zero
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    (U : X.Opens) (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen q U V).toScheme]
    (x : P.obj (op (originalAmbientSite k R t q)))
    (hx : P.map (boundaryBaseAmbientRestriction k R t q U V).op x = 0) :
    P.map (SmoothSite.openInclusion (originalAmbientSite k R t q)
      (boundaryBaseSourceOpen q U V)).op x = 0 := by
  rw [← boundaryBaseOpenComparison_comp k R t q U V, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]
  exact (congrArg (P.map (boundaryBaseOpenComparison k R t q U V).op) hx).trans (map_zero _)

/-- Preserve the generic base open while transporting only the actual map.
This is a statement about an arbitrary presheaf, not a sheafification or gluing
assertion for positive cohomology. -/
theorem exists_boundaryBase_open_zero_of_restriction [IsDomain R]
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    (x : P.obj (op (originalAmbientSite k R t q)))
    (hx : ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      genericPoint (Spec (.of R)) ∈ V ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen q ⊤ V),
        let : IsAffine (boundaryBaseSourceOpen q ⊤ V).toScheme := hW
        P.map (boundaryBaseAmbientRestriction k R t q ⊤ V).op x = 0) :
    ∃ V : (Spec (.of R)).Opens, IsAffineOpen V ∧ genericPoint (Spec (.of R)) ∈ V ∧
      P.map (SmoothSite.openInclusion (originalAmbientSite k R t q)
        (boundaryBaseSourceOpen q ⊤ V)).op x = 0 := by
  obtain ⟨V, hV, hη, hW, hxV⟩ := hx
  let : IsAffine V.toScheme := hV
  let : IsAffine (boundaryBaseSourceOpen q ⊤ V).toScheme := hW
  exact ⟨V, hV, hη, boundaryBase_restriction_open_zero k R t q P ⊤ V x hxV⟩

end AlgebraicGeometry.Scheme.Hom
