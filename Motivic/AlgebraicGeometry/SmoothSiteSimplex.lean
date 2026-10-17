/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSite
public import Motivic.AlgebraicGeometry.AlgebraicSimplexPolynomial
public import Motivic.AlgebraicGeometry.AlgebraicSimplexScheme

/-!
# The actual algebraic simplex belongs to the smooth category

The established polynomial chart proves smoothness of the actual barycentric
quotient ring over its coefficient ring. Its affine spectrum is separated and
quasi-compact, so the all-degree algebraic simplex is a cosimplicial object of
`SmoothSite (Spec R)`. Forgetting this object recovers the existing relative
cosimplicial scheme with its literal coface and codegeneracy morphisms.

No comparison between the coefficient-change map and a tensor-product
base-change is asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

universe u

namespace Motivic.AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- The actual barycentric quotient algebra is smooth by its polynomial chart. -/
instance coordinateRing_smooth (n : ℕ) : Algebra.Smooth R (CoordinateRing R n) := by
  let : Algebra.Smooth R (MvPolynomial (Fin n) R) := {}
  exact Algebra.Smooth.of_equiv (polynomialEquiv R n).symm

/-- The structure morphism of the actual affine simplex is smooth. -/
instance structureMap_smooth (n : ℕ) : Smooth (structureMap R n) := by
  rw [structureMap, HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (CoordinateRing R n)).Smooth
  exact RingHom.smooth_algebraMap.mpr inferInstance

instance structureMap_isSeparated (n : ℕ) : IsSeparated (structureMap R n) :=
  inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (constant R n))))

instance structureMap_quasiCompact (n : ℕ) : QuasiCompact (structureMap R n) :=
  inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (constant R n))))

/-- The actual `n`-simplex as an object of the smooth category over its coefficient ring. -/
def smoothSiteObj (n : ℕ) : SmoothSite (Spec (CommRingCat.of R)) :=
  SmoothSite.mk (structureMap R n)

/-- The full cosimplicial algebraic simplex in the actual smooth category. -/
def cosimplicialSmoothSite : CosimplicialObject (SmoothSite (Spec (CommRingCat.of R))) where
  obj n := smoothSiteObj R n.len
  map f := SmoothSite.homMk ((cosimplicialScheme R).map f) (structureMap_naturality R f)
  map_id n := by
    apply MorphismProperty.Over.Hom.ext
    exact (cosimplicialScheme R).map_id n
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (cosimplicialScheme R).map_comp f g

@[simp]
theorem cosimplicialSmoothSite_obj_left (n : SimplexCategory) :
    ((cosimplicialSmoothSite R).obj n).left =
      Spec (CommRingCat.of (CoordinateRing R n.len)) := rfl

@[simp]
theorem cosimplicialSmoothSite_map_left {m n : SimplexCategory} (f : m ⟶ n) :
    ((cosimplicialSmoothSite R).map f).left =
      Spec.map (CommRingCat.ofHom (pullback R f.toOrderHom)) := rfl

/-- Forgetting smooth-site membership recovers the original relative simplex construction. -/
theorem cosimplicialSmoothSite_forget :
    cosimplicialSmoothSite R ⋙ SmoothSite.forget (Spec (CommRingCat.of R)) =
      cosimplicialSchemeOver R := rfl

end Motivic.AlgebraicSimplex
