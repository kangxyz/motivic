/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.Corestriction

/-!
# The actual finite morphism of corestriction supports

The map of an original integral correspondence support onto its actual finite
image is the literal scheme-theoretic image factor. It retains the original
inclusion and source-projection squares and the original ambient residue degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.WeightTwoCorestriction
open _root_.AlgebraicGeometry.Scheme.Hom

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
variable (r q : ℕ)
variable (A : FiniteCorrespondenceGenerator (source E r).hom (target E q).hom)

/-- The literal finite-image factor from the original integral support. -/
def supportMap : A.scheme ⟶ (imageGenerator (k := k) r q A).scheme :=
  (A.inclusion ≫ ambientMap (k := k) (E := E) r q).toImage

/-- The actual map of supports preserves the original ambient inclusion square. -/
@[reassoc (attr := simp)]
theorem supportMap_inclusion :
    supportMap (k := k) r q A ≫ (imageGenerator (k := k) r q A).inclusion =
      A.inclusion ≫ ambientMap (k := k) (E := E) r q :=
  Scheme.Hom.toImage_imageι _

/-- The actual map of supports preserves the original source-projection square. -/
@[reassoc (attr := simp↓)]
theorem supportMap_projection :
    supportMap (k := k) r q A ≫ (imageGenerator (k := k) r q A).projection =
      A.projection ≫ sourceMap (k := k) (E := E) r := by
  change supportMap (k := k) r q A ≫
      ((imageGenerator (k := k) r q A).inclusion ≫
        pullback.fst (source k r).hom (target k q).hom) = _
  rw [← Category.assoc, supportMap_inclusion, Category.assoc, ambientMap_fst,
    ← Category.assoc]
  rfl

/-- Finiteness is proved for the actual finite-image factor. -/
instance supportMap_isFinite : IsFinite (supportMap (k := k) r q A) :=
  isFinite_toImage (A.inclusion ≫ ambientMap (k := k) (E := E) r q)

/-- Every point of the actual image has a point of the original support above it. -/
theorem supportMap_surjective : Function.Surjective (supportMap (k := k) r q A) :=
  surjective_toImage (A.inclusion ≫ ambientMap (k := k) (E := E) r q)

instance supportMap_isSurjective : Surjective (supportMap (k := k) r q A) :=
  ⟨supportMap_surjective r q A⟩

/-- Generic-point preservation concerns the two actual integral supports. -/
@[simp]
theorem supportMap_genericPoint :
    supportMap (k := k) r q A (genericPoint A.scheme) =
      genericPoint (imageGenerator (k := k) r q A).scheme :=
  genericPoint_toImage (A.inclusion ≫ ambientMap (k := k) (E := E) r q)

/-- The actual generic support degree is the ambient degree at the original
embedded generic point; the original closed immersion has residue degree one. -/
theorem supportMap_residueDegree :
    (supportMap (k := k) r q A).residueDegree (genericPoint A.scheme) =
      (ambientMap (k := k) (E := E) r q).residueDegree A.point :=
  A.toIntegralClosedSubscheme.imageDegree_eq (ambientMap (k := k) (E := E) r q)

end Motivic.WeightTwoCorestriction
