/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.RestrictionDifferenceRefinement
public import Motivic.Transfers.Presheaf.FiniteScalarComparisonDifference

/-! # Actual extension corrections on refinements and original coprime descent

The input retains the actual extension puncture, ambient and Laurent objects,
three evaluation squares, and sections satisfying the extension equation.
In particular an independently constructed native Laurent cylinder is never
identified definitionally with a scalar extension of the original cylinder.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe v u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Section-specific correction data on an actual extension refinement.
The maps to its Laurent and ambient objects must retain their literal squares.
No existence of these geometric data or correction sections is asserted here. -/
structure FiniteSeparableRefinementCorrection
    (P : PresheafWithTransfers.{v} k) (L : Type u) [Field L] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    {O T A D : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) (α : O ⟶ A) (φ : O ⟶ D) (s : sections P (Cor.mk D)) where
  /-- Actual extended punctured object. -/
  puncture : SmoothSite (Spec (.of L))
  /-- Actual extended Laurent correction object. -/
  laurent : SmoothSite (Spec (.of L))
  /-- Actual extended ambient correction object. -/
  ambient : SmoothSite (Spec (.of L))
  /-- The Laurent leg of the extended correction square. -/
  beta : puncture ⟶ laurent
  /-- The ambient leg of the extended correction square. -/
  alpha : puncture ⟶ ambient
  /-- The map to the native scalar extension of the original generator object. -/
  generator : puncture ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj D
  /-- Evaluation from the native scalar extension of the original puncture. -/
  punctureMap : (SmoothSite.fieldBaseChange (algebraMap k L)).obj O ⟶ puncture
  /-- Evaluation from the native scalar extension of the original Laurent object. -/
  laurentMap : (SmoothSite.fieldBaseChange (algebraMap k L)).obj T ⟶ laurent
  /-- Evaluation from the native scalar extension of the original ambient object. -/
  ambientMap : (SmoothSite.fieldBaseChange (algebraMap k L)).obj A ⟶ ambient
  /-- Compatibility with the original Laurent leg. -/
  beta_square : punctureMap ≫ beta =
    (SmoothSite.fieldBaseChange (algebraMap k L)).map β ≫ laurentMap
  /-- Compatibility with the original ambient leg. -/
  alpha_square : punctureMap ≫ alpha =
    (SmoothSite.fieldBaseChange (algebraMap k L)).map α ≫ ambientMap
  /-- Compatibility with the original generator map. -/
  generator_square : punctureMap ≫ generator =
    (SmoothSite.fieldBaseChange (algebraMap k L)).map φ
  /-- The actual extended Laurent correction section. -/
  laurentSection : sections (finiteSeparableExtension L P) (Cor.mk laurent)
  /-- The actual extended ambient correction section. -/
  ambientSection : sections (finiteSeparableExtension L P) (Cor.mk ambient)
  /-- The signed correction equation against the scalar restriction of the original section. -/
  relation : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map beta)
        laurentSection -
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map alpha)
        ambientSection =
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map generator)
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)

variable (P : PresheafWithTransfers.{v} k)
  {L : Type u} [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]
  {O T A D : SmoothSite (Spec (.of k))}
  (β : O ⟶ T) (α : O ⟶ A) (φ : O ⟶ D) (s : sections P (Cor.mk D))

/-- Pullback of the actual correction equation supplies exactly the native
extended-coefficient relation on the one original diagram. -/
theorem FiniteSeparableRefinementCorrection.restriction_difference
    (w : FiniteSeparableRefinementCorrection P L β α φ s) :
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map β))
        (transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map w.laurentMap)
          w.laurentSection) -
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map α))
        (transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map w.ambientMap)
          w.ambientSection) =
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map φ))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s) :=
  restriction_difference_refinement (finiteSeparableExtension L P)
    _ _ _ w.beta w.alpha w.generator w.punctureMap w.laurentMap w.ambientMap
    w.beta_square w.alpha_square w.generator_square _ _ _ w.relation

/-- Actual comparison maps turn the restricted native correction into the
scalar trace input. Neither section is supplied on the original scalar diagram. -/
theorem FiniteSeparableRefinementCorrection.scalar_restriction_difference
    (w : FiniteSeparableRefinementCorrection P L β α φ s) :
    ∃ (a : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L) T)))
      (c : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L) A))),
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) β)) a -
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) α)) c =
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) φ))
          (transfer P ((Cor.graphFunctor k).map
            (SmoothSite.finiteScalarProjection (E := L) D)) s) := by
  exact ⟨_, _, finiteScalarSectionIso_restriction_difference P β α φ s _ _
    (w.restriction_difference P β α φ s)⟩

/-- Two actual extension corrections restrict to the common original diagram,
then coprime traces produce its original sections. Geometry is explicit input. -/
theorem exists_restriction_difference_of_coprime_refinements
    {E : Type u} [Field E] [Algebra k E]
    [Module.Finite k E] [Algebra.IsSeparable k E]
    [Flat β.left] [Flat α.left]
    (wE : FiniteSeparableRefinementCorrection P E β α φ s)
    (wL : FiniteSeparableRefinementCorrection P L β α φ s)
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ (a : sections P (Cor.mk T)) (c : sections P (Cor.mk A)),
      transfer P ((Cor.graphFunctor k).map β) a -
        transfer P ((Cor.graphFunctor k).map α) c =
        transfer P ((Cor.graphFunctor k).map φ) s :=
  exists_restriction_difference_of_coprime_finiteScalar P β α φ s
    (wE.scalar_restriction_difference P β α φ s)
    (wL.scalar_restriction_difference P β α φ s) hdegree

end Motivic.PresheafWithTransfers
