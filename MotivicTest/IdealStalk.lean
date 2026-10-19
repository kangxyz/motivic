/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.StalkKernel
public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.StalkPullback
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Consumers of actual ideal-sheaf stalks

These consumers construct maps on actual quotient rings and identify the
quotient stalk of a closed immersion with its source local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MotivicTest.IdealStalk

variable {X Y : Scheme.{u}}

/-- Affine ideal quotients map canonically to the corresponding local quotients. -/
noncomputable def affineQuotientToStalkQuotient (I : X.IdealSheafData)
    (U : X.affineOpens) {x : X} (hx : x ∈ U.1) :
    Γ(X, U) ⧸ I.ideal U →+* (X.presheaf.stalk x) ⧸ I.stalk x :=
  Ideal.quotientMap (I.stalk x) (X.presheaf.germ U.1 x hx).hom
    (fun _ hs => I.germ_mem_stalk U hx hs)

/-- An actual scheme-theoretic pullback induces a map of actual stalk quotients. -/
noncomputable def pullbackQuotientMap (I : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    (Y.presheaf.stalk (f x)) ⧸ I.stalk (f x) →+*
      (X.presheaf.stalk x) ⧸ (I.comap f).stalk x :=
  Ideal.quotientMap ((I.comap f).stalk x) (f.stalkMap x).hom (by
    rw [I.stalk_comap f x]
    exact Ideal.le_comap_map)

/-- The quotient by the actual ideal-sheaf stalk is the source local ring. -/
noncomputable def closedImmersionQuotientEquiv (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    (Y.presheaf.stalk (f x)) ⧸ f.ker.stalk (f x) ≃+* X.presheaf.stalk x := by
  rw [f.ker_stalk x]
  exact (f.stalkMap x).hom.quotientKerEquivOfSurjective (f.stalkMap_surjective x)

/-- Pullback of a sum computes the corresponding literal local-ring ideal sum. -/
theorem pullback_sum_stalk (I J : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    ((I ⊔ J).comap f).stalk x =
      (I.stalk (f x)).map (f.stalkMap x).hom ⊔
        (J.stalk (f x)).map (f.stalkMap x).hom := by
  rw [Scheme.IdealSheafData.stalk_comap, Scheme.IdealSheafData.stalk_sup, Ideal.map_sup]

end MotivicTest.IdealStalk
