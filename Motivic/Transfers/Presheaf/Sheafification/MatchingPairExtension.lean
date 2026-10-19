/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Basic

/-!
# Conditional extension of matching transfer sections

Four simultaneous equalities of actual signed-correspondence actions suffice
for a matching pair to extend to the target diagram. These are the middle-degree
relations of the standard-triple splitting argument, with the correction sign
retained. The witnesses and their four action equalities are explicit inputs;
this leaf constructs neither geometric witnesses nor curve Nisnevich gluing.
No complex, homotopy category, or additional splitting relations are required.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The section obtained by the first correspondence extends a matching pair,
provided the same three correspondences satisfy the four stated action relations.
The arrows may in particular be actual graphs of a refined geometric diagram.
The hypotheses are action equalities, so a homotopy-invariant presheaf can use
homotopic correspondences without requiring equality of their signed cycles. -/
theorem transfer_matchingPair_extension (P : PresheafWithTransfers.{v} k)
    {A Y B X' A' Y' : Cor k}
    (g : B ⟶ A) (u : B ⟶ Y) (i' : A' ⟶ X') (f' : Y' ⟶ X')
    (rA : A' ⟶ A) (rY : Y' ⟶ Y)
    (lambdaA : X' ⟶ A) (lambdaB : Y' ⟶ B) (ψ : A' ⟶ B)
    (hBu : transfer P (lambdaB ≫ u) = transfer P rY)
    (hBg : transfer P (lambdaB ≫ g) = transfer P (f' ≫ lambdaA))
    (hψu : transfer P (ψ ≫ u) = 0)
    (hA : transfer P (i' ≫ lambdaA - ψ ≫ g) = transfer P rA)
    (a : sections P A) (y : sections P Y)
    (hmatch : transfer P g a = transfer P u y) :
    transfer P i' (transfer P lambdaA a) = transfer P rA a ∧
      transfer P f' (transfer P lambdaA a) = transfer P rY y := by
  have hzero := ConcreteCategory.congr_hom hψu y
  rw [transfer_comp, ConcreteCategory.comp_apply] at hzero
  change transfer P ψ (transfer P u y) = 0 at hzero
  have hleft := ConcreteCategory.congr_hom hA a
  rw [transfer_sub, transfer_comp, transfer_comp] at hleft
  change transfer P i' (transfer P lambdaA a) - transfer P ψ (transfer P g a) =
    transfer P rA a at hleft
  rw [hmatch, hzero, sub_zero] at hleft
  refine ⟨hleft, ?_⟩
  have hright := ConcreteCategory.congr_hom hBg a
  simp only [transfer_comp, ConcreteCategory.comp_apply] at hright
  have hrestrict := ConcreteCategory.congr_hom hBu y
  simp only [transfer_comp, ConcreteCategory.comp_apply] at hrestrict
  calc
    transfer P f' (transfer P lambdaA a) = transfer P lambdaB (transfer P g a) := hright.symm
    _ = transfer P lambdaB (transfer P u y) := congrArg (transfer P lambdaB) hmatch
    _ = transfer P rY y := hrestrict

end Motivic.PresheafWithTransfers
