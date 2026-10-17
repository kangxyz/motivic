/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Graph.Transversality
public import Mathlib.Data.ZMod.Basic

/-!
# Actual smooth graph consumers and the original diagonal coefficient action

These tests retain arbitrary source schemes and arbitrary maps to the smooth
target. In particular a nonreduced affine source and a disconnected affine
source are accepted without any flatness assumption. The last consumer keeps
the original diagonal equation list as scalars acting on the graph stalk.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.SmoothGraph

/-- The actual correspondence graph has a regular stalk kernel for an arbitrary source. -/
theorem arbitrary_source_kernel {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth g] (x : X) :
    ∃ rs : List ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x)),
      IsRegular ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x)) rs ∧
      RingHom.ker ((correspondenceGraph f g).stalkMap x).hom = Ideal.ofList rs :=
  Graph.exists_regular_kernel_of_smooth f g x

/-- The smooth graph theorem applies to a genuinely nonreduced source. -/
theorem nonreduced_source_common_list {Y S : Scheme}
    (f : Spec (CommRingCat.of (ZMod 4)) ⟶ Y) (g : Y ⟶ S) [Smooth g]
    (x : Spec (CommRingCat.of (ZMod 4))) :
    ∃ rs : List ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))) rs ∧
      RingHom.ker ((pullback.diagonal g).stalkMap (f x)).hom = Ideal.ofList rs ∧
      IsRegular ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x))
        (rs.map (Graph.diagonalStalkMap f g x).hom) :=
  Graph.exists_common_regular_list_of_smooth f g x

/-- A disconnected source also admits the common literal diagonal equation list. -/
theorem disconnected_source_common_list {Y S : Scheme}
    (f : Spec (CommRingCat.of (ℚ × ℚ)) ⟶ Y) (g : Y ⟶ S) [Smooth g]
    (x : Spec (CommRingCat.of (ℚ × ℚ))) :
    ∃ rs : List ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))) rs ∧
      RingHom.ker ((pullback.diagonal g).stalkMap (f x)).hom = Ideal.ofList rs ∧
      IsRegular ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x))
        (rs.map (Graph.diagonalStalkMap f g x).hom) :=
  Graph.exists_common_regular_list_of_smooth f g x

/-- The original source diagonal list itself acts weakly regularly on the actual graph stalk. -/
theorem original_diagonal_list_action {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth g] (x : X) :
    letI := (Graph.diagonalStalkMap f g x).hom.toAlgebra
    ∃ rs : List ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))) rs ∧
      RingHom.ker ((pullback.diagonal g).stalkMap (f x)).hom = Ideal.ofList rs ∧
      IsWeaklyRegular ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x)) rs := by
  let := (Graph.diagonalStalkMap f g x).hom.toAlgebra
  obtain ⟨rs, hrs, hker, hreg⟩ := Graph.exists_common_regular_list_of_smooth f g x
  refine ⟨rs, hrs, hker, ?_⟩
  exact (isWeaklyRegular_map_algebraMap_iff
    ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x))
    ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x)) rs).mp
      hreg.toIsWeaklyRegular

end Motivic.MotivicTest.SmoothGraph
