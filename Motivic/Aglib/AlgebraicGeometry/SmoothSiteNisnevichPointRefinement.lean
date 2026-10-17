/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPointSections

/-!
# Refinement at the center of an actual Nisnevich neighborhood

A pointed neighborhood of the distinguished point of a neighborhood refines
the original point index. The construction factors the original field-valued
point through its own residue field, then composes that actual point with the
second neighborhood's chosen lift.

Consequently zero germs at the neighborhood center map to zero under the
original point-fiber cocone. This uses the existing point and colimit maps;
no new point or stalk comparison framework is introduced. The file depends
on the existing smooth-site module and is not a standalone upstream extraction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- A field-valued point factors through the residue field of its actual image point. -/
theorem exists_residueField_factorization {K : Type u} [Field K] {U : Scheme.{u}}
    (t : Spec (.of K) ⟶ U) :
    ∃ b : U.residueField (t default) ⟶ CommRingCat.of K,
      Spec.map b ≫ U.fromSpecResidueField (t default) = t := by
  obtain ⟨⟨a, b⟩, hb⟩ := (Scheme.SpecToEquivOfField K U).symm.surjective t
  have hb' : Spec.map b ≫ U.fromSpecResidueField a = t := hb
  have ha : t default = a :=
    (congrArg (fun g : Spec (.of K) ⟶ U ↦ g default) hb').symm.trans
      (Scheme.fromSpecResidueField_apply (X := U) a (Spec.map b default))
  subst a
  exact ⟨b, hb'⟩

end AlgebraicGeometry.Scheme.Hom

namespace Motivic.SmoothSite

variable {S : Scheme.{u}} {X : SmoothSite S} {x : X.left}

namespace NisnevichNeighborhood

/-- A neighborhood at the distinguished center refines the original point index.
The comparison to its original smooth object is the identity on the underlying scheme. -/
theorem exists_refinement_of_center_neighborhood (N : NisnevichNeighborhood X x)
    (M : NisnevichNeighborhood ((nisnevichNeighborhoodFunctor X x).obj N) N.center) :
    ∃ (P : NisnevichNeighborhood X x) (q : P ⟶ N)
      (t : (nisnevichNeighborhoodFunctor X x).obj P ⟶
        (nisnevichNeighborhoodFunctor ((nisnevichNeighborhoodFunctor X x).obj N) N.center).obj M),
      IsIso t.left ∧ t ≫ M.toBase = (nisnevichNeighborhoodFunctor X x).map q := by
  obtain ⟨b, hb⟩ := N.obj.val.left.exists_residueField_factorization
  let p : Spec (X.left.residueField x) ⟶ M.obj.obj.left := Spec.map b ≫ M.obj.val.left
  have hp : p ≫ M.obj.obj.hom = N.obj.val.left := by
    have hM : M.obj.val.left ≫ M.obj.obj.hom =
        N.obj.obj.left.fromSpecResidueField N.center := Over.w M.obj.val
    dsimp only [p]
    rw [Category.assoc, hM]
    exact hb
  let P₀ : PointedEtaleNeighborhood X x :=
    Functor.elementsMk _ (Scheme.Etale.mk (M.obj.obj.hom ≫ N.obj.obj.hom))
      (Over.homMk p (by
        change p ≫ (M.obj.obj.hom ≫ N.obj.obj.hom) = X.left.fromSpecResidueField x
        rw [← Category.assoc, hp]
        exact Over.w N.obj.val))
  have hP : smoothNeighborhoodProperty X x P₀ := by
    change smoothSeparatedFiniteType ((M.obj.obj.hom ≫ N.obj.obj.hom) ≫ X.hom)
    rw [Category.assoc]
    exact M.property
  let P : NisnevichNeighborhood X x := ⟨P₀, hP⟩
  let q : P ⟶ N := ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk M.obj.obj.hom rfl) (by
      apply Over.OverMorphism.ext
      exact hp))
  let t : (nisnevichNeighborhoodFunctor X x).obj P ⟶
      (nisnevichNeighborhoodFunctor ((nisnevichNeighborhoodFunctor X x).obj N) N.center).obj M :=
    homMk (𝟙 M.obj.obj.left) (by
      change (𝟙 M.obj.obj.left) ≫ (M.obj.obj.hom ≫ (N.obj.obj.hom ≫ X.hom)) =
        (M.obj.obj.hom ≫ N.obj.obj.hom) ≫ X.hom
      simp only [Category.id_comp, Category.assoc])
  refine ⟨P, q, t, inferInstanceAs (IsIso (𝟙 M.obj.obj.left)), ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

end NisnevichNeighborhood

variable [IsAffine S] (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- A section zero at the neighborhood's own center is zero under the original
point-fiber cocone injection. The proof uses an actual original-index refinement. -/
theorem nisnevichPointFiberCocone_eq_zero_of_center_germ_eq_zero
    (N : NisnevichNeighborhood X x)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (hs : sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center s = 0) :
    (nisnevichPointFiberCocone X x F).ι.app (op N) s = 0 := by
  obtain ⟨M, hM⟩ := (sectionToNisnevichPoint_eq_zero_iff F s).mp hs
  obtain ⟨P, q, t, _, ht⟩ := N.exists_refinement_of_center_neighborhood M
  have hq : F.map ((nisnevichNeighborhoodFunctor X x).map q).op s = 0 := by
    rw [← ht, op_comp, F.map_comp, ConcreteCategory.comp_apply, hM, map_zero]
  have h := (nisnevichPointFiberCocone X x F).w q.op
  change F.map ((nisnevichNeighborhoodFunctor X x).map q).op ≫
    (nisnevichPointFiberCocone X x F).ι.app (op P) =
      (nisnevichPointFiberCocone X x F).ι.app (op N) at h
  rw [← h, ConcreteCategory.comp_apply, hq, map_zero]

/-- Equality of center germs implies equality under the original cocone map. -/
theorem nisnevichPointFiberCocone_eq_of_center_germ_eq
    (N : NisnevichNeighborhood X x)
    (s t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (hst : sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center s =
      sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center t) :
    (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op N) t := by
  have h := nisnevichPointFiberCocone_eq_zero_of_center_germ_eq_zero F N (s - t)
    (by rw [map_sub, hst, sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

end Motivic.SmoothSite
