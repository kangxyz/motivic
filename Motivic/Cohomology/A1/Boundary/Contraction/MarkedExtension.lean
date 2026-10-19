/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Contraction.ZeroRepresentative

/-! # The actual residue marking of an ambient boundary extension -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

/-- Equality of the original point markings produces a literal residue-field
lift into the ambient extension, over the original zero section of V. -/
theorem exists_residue_lift_of_marked_zero_fiber
    (V : EtaleSeparatedFiniteType X.left) (v : V.left)
    (E : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left)
    (f : E ⟶ (cylinderNeighborhood X).obj V)
    (e : (markedResiduePoint V v).fiber.obj
      ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj E))
    (he : (markedResiduePoint V v).fiber.map
        ((baseChange (SmoothSite.a1Section (.of k) X 0).left).map f) e =
      (markedResiduePoint V v).fiber.map (zeroNeighborhoodLift X V)
        (markedResidueElement V v)) :
    ∃ c : Spec (V.left.residueField v) ⟶ E.left,
      c ≫ f.left = V.left.fromSpecResidueField v ≫
        (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left := by
  let i := (SmoothSite.a1Section (.of k) X 0).left
  let b := V.left.fromSpecResidueField v ≫ V.hom
  let a := relativeFieldPointFiberEquiv b (V.left.residueField v) (𝟙 _)
    ((baseChange i).obj E) e
  have h₁ := relativeFieldPointFiberEquiv_naturality b (V.left.residueField v) (𝟙 _)
    ((baseChange i).map f) e
  have h₂ := relativeFieldPointFiberEquiv_naturality b (V.left.residueField v) (𝟙 _)
    (zeroNeighborhoodLift X V) (markedResidueElement V v)
  have hh := congrArg (relativeFieldPointFiberEquiv b (V.left.residueField v) (𝟙 _)
    ((zeroNeighborhood X).obj V)) he
  have hh' := h₁.symm.trans (hh.trans h₂)
  have hm : relativeFieldPointFiberEquiv b (V.left.residueField v) (𝟙 _) V
      (markedResidueElement V v) =
      Over.homMk (V.left.fromSpecResidueField v) (by simp [b]) :=
    Equiv.apply_symm_apply _ _
  rw [hm] at hh'
  have ha : a.left ≫ ((baseChange i).map f).left =
      V.left.fromSpecResidueField v ≫ (zeroNeighborhoodLift X V).left :=
    congrArg (fun t => t.left) hh'
  refine ⟨a.left ≫ pullback.fst E.hom i, ?_⟩
  have hf : ((baseChange i).map f).left ≫
      pullback.fst ((cylinderNeighborhood X).obj V).hom i =
      pullback.fst E.hom i ≫ f.left := pullback.lift_fst _ _ _
  have hz : (zeroNeighborhoodLift X V).left ≫
      pullback.fst ((cylinderNeighborhood X).obj V).hom i =
      (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left :=
    pullback.lift_fst _ _ _
  rw [Category.assoc, ← hf, ← Category.assoc, ha, Category.assoc, hz]

end Motivic.FiniteEtaleSite
