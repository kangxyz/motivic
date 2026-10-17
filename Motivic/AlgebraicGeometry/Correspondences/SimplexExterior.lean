/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentity
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry
public import Motivic.AlgebraicGeometry.Correspondences.Category

/-!
# Signed exterior correspondences with the actual simplex

For every degree, an actual signed correspondence has an exterior product
with the identity of the barycentric algebraic simplex. The output uses the
literal product supports and their original integer coefficients. This file
does not claim composition preservation or the mixed coface interchange law;
these are the remaining inputs for a transfer singular complex.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

namespace FiniteCorrespondence

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- Exterior product with the identity of the actual algebraic `n`-simplex. -/
def simplexExterior (n : ℕ) : FiniteCorrespondence X.hom Y.hom →+
    FiniteCorrespondence (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom :=
  exteriorIdentity (X := X) (Y := Y) (AlgebraicSimplex.smoothSiteObj k n)

@[simp] theorem simplexExterior_single (n : ℕ)
    (V : FiniteCorrespondenceGenerator X.hom Y.hom) (m : ℤ) :
    simplexExterior (X := X) (Y := Y) n (Finsupp.single V m) =
      Finsupp.single (V.exteriorIdentityGenerator (AlgebraicSimplex.smoothSiteObj k n)) m :=
  exteriorIdentity_single (X := X) (Y := Y) _ V m

end FiniteCorrespondence

namespace Cor

variable {k : Type u} [Field k]

/-- The actual relative product with the simplex, as an object of correspondences. -/
def simplexProduct (X : Cor k) (n : ℕ) : Cor k :=
  ⟨SmoothSite.product X.toSmoothSite (AlgebraicSimplex.smoothSiteObj k n)⟩

/-- The signed geometric operation on the actual hom groups of `Cor k`. -/
def simplexExterior {X Y : Cor k} (n : ℕ) :
    (X ⟶ Y) →+ (simplexProduct X n ⟶ simplexProduct Y n) :=
  FiniteCorrespondence.simplexExterior (X := X.toSmoothSite) (Y := Y.toSmoothSite) n

@[simp] theorem simplexExterior_add {X Y : Cor k} (n : ℕ) (α β : X ⟶ Y) :
    simplexExterior n (α + β) = simplexExterior n α + simplexExterior n β :=
  map_add _ _ _

@[simp] theorem simplexExterior_neg {X Y : Cor k} (n : ℕ) (α : X ⟶ Y) :
    simplexExterior n (-α) = -simplexExterior n α := map_neg _ _

@[simp] theorem simplexExterior_zsmul {X Y : Cor k} (n : ℕ) (m : ℤ) (α : X ⟶ Y) :
    simplexExterior n (m • α) = m • simplexExterior n α := map_zsmul _ _ _

end Cor

end Motivic
