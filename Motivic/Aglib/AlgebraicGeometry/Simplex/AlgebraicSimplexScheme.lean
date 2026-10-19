/-
Copyright (c) 2026 Motivic Cohomology Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AlgebraicSimplex.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The cosimplicial algebraic simplex as a scheme

Applying the spectrum functor to the simplicial coordinate rings constructs the
full cosimplicial algebraic simplex. Its structural maps to `Spec R` commute
with every coface and codegeneracy, giving `cosimplicialSchemeOver R` in the
category of schemes over `Spec R`. Thus products in this over-category are the
base-relative products required by the singular construction.

Changing coefficients induces a morphism between the underlying cosimplicial
schemes, contravariantly in the coefficient ring. This construction by itself
does not assert a tensor-product base-change comparison or smoothness.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped Simplicial

universe u

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- The all-degree cosimplicial affine algebraic simplex. -/
def cosimplicialScheme : CosimplicialObject Scheme.{u} :=
  (simplicialRing R).rightOp ⋙ Scheme.Spec

@[simp]
theorem cosimplicialScheme_obj (n : SimplexCategory) :
    (cosimplicialScheme R).obj n = Spec (CommRingCat.of (CoordinateRing R n.len)) := rfl

@[simp]
theorem cosimplicialScheme_map {m n : SimplexCategory} (f : m ⟶ n) :
    (cosimplicialScheme R).map f = Spec.map (CommRingCat.ofHom (pullback R f.toOrderHom)) :=
  rfl

/-- The structure morphism from the algebraic simplex to the base spectrum. -/
def structureMap (n : ℕ) :
    Spec (CommRingCat.of (CoordinateRing R n)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (constant R n))

/-- Every simplex morphism is a morphism over the fixed base. -/
@[reassoc]
theorem structureMap_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    (cosimplicialScheme R).map f ≫ structureMap R n.len = structureMap R m.len := by
  change Spec.map (CommRingCat.ofHom (pullback R f.toOrderHom)) ≫
    Spec.map (CommRingCat.ofHom (constant R n.len)) =
      Spec.map (CommRingCat.ofHom (constant R m.len))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (pullback_constant R f.toOrderHom)

/-- The algebraic simplex as a cosimplicial object in schemes over `Spec R`. -/
def cosimplicialSchemeOver : CosimplicialObject (Over (Spec (CommRingCat.of R))) where
  obj n := Over.mk (structureMap R n.len)
  map f := Over.homMk ((cosimplicialScheme R).map f) (structureMap_naturality R f)
  map_id n := by
    apply Over.OverMorphism.ext
    exact (cosimplicialScheme R).map_id n
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact (cosimplicialScheme R).map_comp f g

@[simp]
theorem cosimplicialSchemeOver_forget :
    cosimplicialSchemeOver R ⋙ Over.forget (Spec (CommRingCat.of R)) =
      cosimplicialScheme R := rfl

variable {R} {S T : Type u} [CommRing S] [CommRing T]

/-- The cosimplicial morphism induced contravariantly by a coefficient homomorphism. -/
def cosimplicialSchemeMap (c : R →+* S) : cosimplicialScheme S ⟶ cosimplicialScheme R :=
  Functor.whiskerRight (simplicialMap c).rightOp Scheme.Spec

@[simp]
theorem cosimplicialSchemeMap_app (c : R →+* S) (n : SimplexCategory) :
    (cosimplicialSchemeMap c).app n =
      Spec.map (CommRingCat.ofHom (mapCoefficients c n.len)) := rfl

@[simp]
theorem cosimplicialSchemeMap_id :
    cosimplicialSchemeMap (RingHom.id R) = 𝟙 (cosimplicialScheme R) := by
  simp [cosimplicialSchemeMap, cosimplicialScheme]

/-- Coefficient homomorphisms compose contravariantly on simplex schemes. -/
theorem cosimplicialSchemeMap_comp (c : R →+* S) (d : S →+* T) :
    cosimplicialSchemeMap (d.comp c) =
      cosimplicialSchemeMap d ≫ cosimplicialSchemeMap c := by
  simp [cosimplicialSchemeMap, cosimplicialScheme, simplicialMap_comp]

/-- The change-of-coefficients morphism has the expected map on bases. -/
@[reassoc]
theorem cosimplicialSchemeMap_structureMap (c : R →+* S) (n : SimplexCategory) :
    (cosimplicialSchemeMap c).app n ≫ structureMap R n.len =
      structureMap S n.len ≫ Spec.map (CommRingCat.ofHom c) := by
  change Spec.map (CommRingCat.ofHom (mapCoefficients c n.len)) ≫
    Spec.map (CommRingCat.ofHom (constant R n.len)) =
      Spec.map (CommRingCat.ofHom (constant S n.len)) ≫ Spec.map (CommRingCat.ofHom c)
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (mapCoefficients_constant c n.len)

end AlgebraicSimplex
