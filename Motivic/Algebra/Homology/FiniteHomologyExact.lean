/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.LengthEulerChain

/-!
# Finite homology in actual short exact sequences

A middle module in an exact pair has length bounded by the sum of the two
outer lengths. Applied to the genuine long exact homology sequence, this
proves finite-length, finite-support homology is a two-out-of-three property
for short exact nonnegative chain complexes. The degree-zero quotient uses
the actual epimorphism on homology, not a nonexistent negative-degree term.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Motivic.LengthEuler

variable {R : Type u} [Ring R]

/-- The middle length of an actual exact pair is bounded by the outer lengths. -/
theorem length_le_add_of_exact {U V W : Type v}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hex : Function.Exact f g) :
    Module.length R V ≤ Module.length R U + Module.length R W := by
  have he : Function.Exact (LinearMap.range f).subtype g.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp hex
  rw [Module.length_eq_add_of_exact (LinearMap.range f).subtype g.rangeRestrict
    (Submodule.subtype_injective _) (LinearMap.range_eq_top.mp g.range_rangeRestrict) he]
  exact add_le_add
    (Module.length_le_of_surjective f.rangeRestrict
      (LinearMap.range_eq_top.mp f.range_rangeRestrict))
    (Module.length_le_of_injective (LinearMap.range g).subtype
      (Submodule.subtype_injective _))

/-- Actual degreewise exact pairs transfer finite length and finite support. -/
theorem FiniteLengthSupport.of_exact {ι : Type w} {X Y Z : ι → ModuleCat.{v} R}
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i)
    (hex : ∀ i, Function.Exact (f i) (g i))
    (hX : FiniteLengthSupport X) (hZ : FiniteLengthSupport Z) :
    FiniteLengthSupport Y where
  finite_length i := ne_top_of_le_ne_top
    (by simp [hX.finite_length i, hZ.finite_length i])
    (length_le_add_of_exact (f i).hom (g i).hom (hex i))
  finite_support := (hX.finite_support.union hZ.finite_support).subset fun i hi => by
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    have hy := length_le_add_of_exact (f i).hom (g i).hom (hex i)
    rw [hn.1, hn.2, zero_add] at hy
    exact hi (le_antisymm hy bot_le)

/-- A finite successor tail and a finite degree-zero term give finite support. -/
theorem FiniteLengthSupport.of_nat_succ (X : ℕ → ModuleCat.{v} R)
    (hzero : Module.length R (X 0) ≠ ⊤)
    (hsucc : FiniteLengthSupport (fun n => X (n + 1))) : FiniteLengthSupport X where
  finite_length n := by
    cases n with
    | zero => exact hzero
    | succ n => exact hsucc.finite_length n
  finite_support := ((hsucc.finite_support.image Nat.succ).insert 0).subset fun n hn => by
    cases n with
    | zero => exact Set.mem_insert _ _
    | succ n => exact Set.mem_insert_of_mem _ ⟨n, hn, rfl⟩

/-- Finite homology of both outer complexes gives finite homology of the middle. -/
theorem FiniteHomology.shortExact_middle
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (hA : FiniteHomology S.X₁) (hC : FiniteHomology S.X₃) : FiniteHomology S.X₂ :=
  FiniteLengthSupport.of_exact
    (fun n => HomologicalComplex.homologyMap S.f n)
    (fun n => HomologicalComplex.homologyMap S.g n)
    (fun n => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ n)) hA hC

/-- The connecting map from degree n+1 proves the left-hand finiteness direction. -/
theorem FiniteHomology.shortExact_left
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (hB : FiniteHomology S.X₂) (hC : FiniteHomology S.X₃) : FiniteHomology S.X₁ :=
  FiniteLengthSupport.of_exact (fun n => hS.δ (n + 1) n rfl)
    (fun n => HomologicalComplex.homologyMap S.f n)
    (fun n => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ (n + 1) n rfl)) (hC.comp Nat.succ Nat.succ_injective) hB

/-- The right-hand direction includes the genuine degree-zero homology epimorphism. -/
theorem FiniteHomology.shortExact_right
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (hA : FiniteHomology S.X₁) (hB : FiniteHomology S.X₂) : FiniteHomology S.X₃ := by
  apply FiniteLengthSupport.of_nat_succ
  · have hepi : Epi (HomologicalComplex.homologyMap S.g 0) := by
      have := hS.epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by
        intro j
        change ¬ j + 1 = 0
        omega)
    exact ne_top_of_le_ne_top (hB.finite_length 0)
      (Module.length_le_of_surjective (HomologicalComplex.homologyMap S.g 0).hom
        ((ModuleCat.epi_iff_surjective _).mp hepi))
  · exact FiniteLengthSupport.of_exact
      (fun n => HomologicalComplex.homologyMap S.g (n + 1))
      (fun n => hS.δ (n + 1) n rfl)
      (fun n => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (hS.homology_exact₃ (n + 1) n rfl)) (hB.comp Nat.succ Nat.succ_injective) hA

/-- Euler additivity requires only the actual finite homology of the outer terms. -/
theorem chainEuler_add_of_shortExact_outer
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (hA : FiniteHomology S.X₁) (hC : FiniteHomology S.X₃) :
    chainEuler S.X₂ (FiniteHomology.shortExact_middle S hS hA hC) =
      chainEuler S.X₁ hA + chainEuler S.X₃ hC :=
  chainEuler_add_of_shortExact S hS hA _ hC

end Motivic.LengthEuler
