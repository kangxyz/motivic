/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.BaseChange

/-!
# Affine models of Laurent scheme products
-/

@[expose] public noncomputable section


set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]

/-- The original affine structure morphism. -/
def baseMap : Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

/- The original geometric generators, not a substitute cycle group. -/
/-- The literal Laurent spectrum is the actual source-torus product. -/
theorem ambient_isPullback :
    IsPullback (laurentProjection (.of R))
      (Spec.map (CommRingCat.PolynomialLaurent.laurentMap
        (CommRingCat.ofHom (algebraMap k R))))
      (baseMap k R) (laurentProjection (.of k)) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.laurent_isPushout
      (CommRingCat.ofHom (algebraMap k R)))

/-- The specified Laurent chart retains both original product projections. -/
def ambientIso : Spec (.of (LaurentPolynomial R)) ≅
    pullback (baseMap k R) (laurentProjection (.of k)) :=
  (ambient_isPullback k R).isoPullback

@[reassoc (attr := simp)] theorem ambientIso_hom_fst :
    (ambientIso k R).hom ≫ pullback.fst _ _ = laurentProjection (.of R) :=
  (ambient_isPullback k R).isoPullback_hom_fst


end AlgebraicGeometry.Scheme.PolynomialLaurent
