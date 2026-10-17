/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorBoundaryDescent
public import Motivic.Cohomology.Motivic.DiagonalMilnorSymbol

/-! # Retraction of the original all-weight Milnor symbol by the actual norm -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe w u
namespace Motivic.DiagonalMilnorBoundaryDescent
open KTheory
variable (k : Type u) [Field k] [CharZero k] (q : ℕ)

/-- The norm evaluation is a left inverse to the already constructed Milnor symbol map. -/
theorem rawNorm_rawSymbol (x : MilnorK.K k q) :
    rawNorm k q (DiagonalMilnorSymbol.rawSymbol k q x) = x := by
  have h : (rawNorm k q).comp (DiagonalMilnorSymbol.rawSymbol k q) =
      AddMonoidHom.id (MilnorK.K k q) := by
    apply MilnorK.addHom_ext
    intro a
    exact (congrArg (rawNorm k q) (DiagonalMilnorSymbol.rawSymbol_symbol k q a)).trans
      (rawNorm_graphSymbol k q a)
  exact DFunLike.congr_fun h x

/-- In particular, the original Milnor symbol map is injective in every weight. -/
theorem rawSymbol_injective : Function.Injective (DiagonalMilnorSymbol.rawSymbol k q) :=
  Function.LeftInverse.injective (rawNorm_rawSymbol k q)

/-- The actual raw norm is surjective in every weight. -/
theorem rawNorm_surjective : Function.Surjective (rawNorm k q) :=
  Function.RightInverse.surjective (rawNorm_rawSymbol k q)

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original derived Milnor symbol also has the actual norm as a left inverse. -/
theorem motivicNorm_motivicSymbol (x : MilnorK.K k q) :
    motivicNorm k q (DiagonalMilnorSymbol.motivicSymbol k q x) = x := by
  rw [motivicNorm_comparison, DiagonalMilnorSymbol.motivicSymbol_comparison,
    rawNorm_rawSymbol]

/-- The original derived Milnor symbol is injective, without identifying all cycles yet. -/
theorem motivicSymbol_injective :
    Function.Injective (DiagonalMilnorSymbol.motivicSymbol k q) :=
  Function.LeftInverse.injective (motivicNorm_motivicSymbol k q)

/-- Every original Milnor class is the norm of an actual derived diagonal class. -/
theorem motivicNorm_surjective : Function.Surjective (motivicNorm k q) :=
  Function.RightInverse.surjective (motivicNorm_motivicSymbol k q)

end Motivic.DiagonalMilnorBoundaryDescent
