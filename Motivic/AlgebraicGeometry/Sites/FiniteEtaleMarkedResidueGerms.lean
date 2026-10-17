/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleResidueGerms

/-! # Original marked residue points on every small étale test object -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {S : Scheme.{u}}

/-- A residue point of the test object, regarded over the unchanged site base. -/
def markedResiduePoint (V : FiniteEtaleSite S) (z : V.left) :
    (nisnevichTopology S).Point.{u + 1} :=
  relativeFieldPoint (V.left.fromSpecResidueField z ≫ V.hom) (V.left.residueField z) (𝟙 _)

/-- The marking remembers the original map into the test object, not just its base image. -/
def markedResidueElement (V : FiniteEtaleSite S) (z : V.left) :
    (markedResiduePoint V z).fiber.obj V :=
  (relativeFieldPointFiberEquiv (V.left.fromSpecResidueField z ≫ V.hom)
    (V.left.residueField z) (𝟙 _) V).symm
      (Over.homMk (V.left.fromSpecResidueField z) (by simp))

def markedSectionGerm (P : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (V : FiniteEtaleSite S) (z : V.left) :
    P.obj (op V) ⟶ (markedResiduePoint V z).presheafFiber.obj P :=
  (markedResiduePoint V z).toPresheafFiber V (markedResidueElement V z) P

/-- Zero at the marked point gives a genuine residue-splitting zero neighborhood of V. -/
theorem exists_marked_zero_neighborhood
    (P : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (V : FiniteEtaleSite S) (z : V.left) (s : P.obj (op V))
    (hs : markedSectionGerm P V z s = 0) :
    ∃ (W : FiniteEtaleSite S) (f : W ⟶ V) (y : W.left),
      f.left y = z ∧ IsIso (f.left.residueFieldMap y) ∧ P.map f.op s = 0 := by
  let Φ := markedResiduePoint V z
  have hs' : Φ.toPresheafFiber V (markedResidueElement V z) P s =
      Φ.toPresheafFiber V (markedResidueElement V z) P 0 := by
    rw [map_zero]
    exact hs
  obtain ⟨W, f, v, hf, hv⟩ := (Φ.toPresheafFiber_eq_iff' _ _ s 0).mp hs'
  let a := relativeFieldPointFiberEquiv (V.left.fromSpecResidueField z ≫ V.hom)
    (V.left.residueField z) (𝟙 _) W v
  have ha : a.left ≫ f.left = V.left.fromSpecResidueField z := by
    have ht := relativeFieldPointFiberEquiv_naturality
      (V.left.fromSpecResidueField z ≫ V.hom) (V.left.residueField z) (𝟙 _) f v
    dsimp only [Φ, markedResiduePoint] at hf
    erw [hf] at ht
    dsimp only [markedResidueElement] at ht
    rw [Equiv.apply_symm_apply] at ht
    have hh := congrArg (fun t => t.left) ht
    exact hh.symm
  let c := IsLocalRing.closedPoint (V.left.residueField z)
  have hres : IsIso ((a.left ≫ f.left).residueFieldMap c) := by
    rw [ha]
    let : SurjectiveOnStalks (V.left.fromSpecResidueField z) :=
      inferInstanceAs (SurjectiveOnStalks (V.left.fromSpecResidueField z))
    exact Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks _ _
  have hi : IsIso (f.left.residueFieldMap (a.left c)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨(f.left.residueFieldMap _).hom.injective, ?_⟩
    have ht := (ConcreteCategory.bijective_of_isIso
      ((a.left ≫ f.left).residueFieldMap c)).surjective
    rw [Scheme.residueFieldMap_comp] at ht
    change Function.Surjective ((a.left.residueFieldMap c) ∘
      (f.left.residueFieldMap (a.left c))) at ht
    exact ht.of_comp_left (a.left.residueFieldMap c).hom.injective
  refine ⟨W, f, a.left c, ?_, hi, ?_⟩
  · exact (congrArg (fun b => b c) ha).trans (V.left.fromSpecResidueField_apply z c)
  · simpa only [map_zero] using hv

end Motivic.FiniteEtaleSite
