/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.FiniteEdge
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Finite homology windows for a specified cone -/
@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe w v u
namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C))
include hT

/-- An epimorphism in one degree and monomorphism in the next kill that cone degree. -/
theorem cone_homology_isZero_of_epi_mono (i : ℤ)
    [Epi ((homologyFunctor C i).map T.mor₁)]
    [Mono ((homologyFunctor C (i + 1)).map T.mor₁)] :
    IsZero ((homologyFunctor C i).obj T.obj₃) := by
  exact ((homologyFunctor C 0).homologySequence_exact₃ T hT i (i + 1) rfl).isZero_X₂
    (((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff T hT i).mp
      (by simpa only [shift_homologyFunctor] using
        (inferInstance : Epi ((homologyFunctor C i).map T.mor₁))))
    (((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
      T hT i (i + 1) rfl).mp (by simpa only [shift_homologyFunctor] using
        (inferInstance : Mono ((homologyFunctor C (i + 1)).map T.mor₁))))

/-- A finite lower homology window gives bijectivity for the original triangle arrow. -/
theorem single_postcomp_bijective_of_homology_window (P : C) (n : ℤ)
    (hepi : ∀ i : ℤ, i ≤ n → Epi ((homologyFunctor C i).map T.mor₁))
    (hmono : ∀ i : ℤ, i ≤ n + 1 → Mono ((homologyFunctor C i).map T.mor₁)) :
    Function.Bijective (fun f : (singleFunctor C n).obj P ⟶ T.obj₁ => f ≫ T.mor₁) := by
  apply single_postcomp_bijective_of_cone_homology T hT P n
  intro i hi
  have := hepi i hi
  have := hmono (i + 1) (by omega)
  exact cone_homology_isZero_of_epi_mono T hT i

end DerivedCategory
