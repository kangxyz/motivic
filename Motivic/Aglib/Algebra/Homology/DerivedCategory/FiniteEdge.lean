/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Triangulated.FiniteEdge
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Finite-degree derived Hom comparison from actual cone homology

The source is the original coefficient object placed in degree `n`. All maps
are postcomposition with the displayed triangle arrow; the assumptions concern
only the actual homology of its cone. This is not yet a Leray comparison.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe w v u
namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C))
  (P : C) (n : ℤ)
include hT

/-- No cone homology below `n` implies injectivity for the original degree-`n` source. -/
theorem single_postcomp_injective_of_cone_homology
    (hcone : ∀ i : ℤ, i < n → IsZero ((homologyFunctor C i).obj T.obj₃)) :
    Function.Injective (fun f : (singleFunctor C n).obj P ⟶ T.obj₁ => f ≫ T.mor₁) := by
  have : T.obj₃.IsGE n := (isGE_iff T.obj₃ n).mpr hcone
  exact TStructure.t.postcomp_injective_of_cone_isGE T hT _ n

/-- No cone homology through `n` implies bijectivity for that same specified map. -/
theorem single_postcomp_bijective_of_cone_homology
    (hcone : ∀ i : ℤ, i ≤ n → IsZero ((homologyFunctor C i).obj T.obj₃)) :
    Function.Bijective (fun f : (singleFunctor C n).obj P ⟶ T.obj₁ => f ≫ T.mor₁) := by
  have : T.obj₃.IsGE (n + 1) := (isGE_iff T.obj₃ (n + 1)).mpr
    (fun i hi => hcone i (by omega))
  exact TStructure.t.postcomp_bijective_of_cone_isGE T hT _ n

end DerivedCategory
