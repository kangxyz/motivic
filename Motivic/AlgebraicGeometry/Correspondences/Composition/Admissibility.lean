/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Support.Basic
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.ImageProjection
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints

/-!
# Relative finiteness of images of incidence components

The actual finite image of any integral closed subscheme of incidence remains
finite over the source. Its projected image is exactly that of the original
integral subscheme. Consequently a proved component-dominance statement gives
an actual finite-correspondence generator on the very same ideal-sheaf basis.

This does not derive dominance from whole-incidence coverage, choose a Tor-Euler
cycle, or assert the category laws of finite correspondences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
variable (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)
variable [IsSeparated h] [LocallyOfFiniteType h]
variable (C : IntegralClosedSubscheme (A.incidence B))

/-- Actual finite images of integral incidence supports are finite over the source. -/
theorem isFinite_incidenceImage_projection :
    IsFinite (correspondenceProjection f h (C.finiteImage (A.incidenceMap B)).val) := by
  have : IsFinite ((C.val.subschemeι ≫ A.incidenceMap B) ≫ pullback.fst f h) := by
    simpa only [Category.assoc, incidenceMap_fst] using
      (inferInstance : IsFinite (C.val.subschemeι ≫ A.incidenceSource B))
  exact isFinite_image_projection (C.val.subschemeι ≫ A.incidenceMap B) (pullback.fst f h)

omit [LocallyOfFiniteType h] in
/-- Relative image factorization preserves the exact source-component condition. -/
theorem range_incidenceImage_projection :
    Set.range (correspondenceProjection f h (C.finiteImage (A.incidenceMap B)).val) =
      Set.range (C.val.subschemeι ≫ A.incidenceSource B) := by
  change Set.range ((C.val.subschemeι ≫ A.incidenceMap B).imageι ≫ pullback.fst f h) = _
  rw [range_image_projection]
  simp only [Category.assoc, incidenceMap_fst]

/-- A proved componentwise source image gives a genuine correspondence generator. -/
noncomputable def incidenceImageGenerator
    (hC : Set.range (C.val.subschemeι ≫ A.incidenceSource B) ∈ irreducibleComponents X) :
    FiniteCorrespondenceGenerator f h :=
  ⟨(C.finiteImage (A.incidenceMap B)).val, (C.finiteImage (A.incidenceMap B)).property,
    A.isFinite_incidenceImage_projection B C,
    (A.range_incidenceImage_projection B C).symm ▸ hC⟩

/-- The resulting generator uses the literal finite-image ideal sheaf. -/
@[simp]
theorem incidenceImageGenerator_val
    (hC : Set.range (C.val.subschemeι ≫ A.incidenceSource B) ∈ irreducibleComponents X) :
    (A.incidenceImageGenerator B C hC).val = (C.finiteImage (A.incidenceMap B)).val := rfl

/-- Surjectivity over the first support suffices for the component condition. -/
noncomputable def incidenceImageGeneratorOfSurjective
    (hC : Function.Surjective (C.val.subschemeι ≫ A.incidenceFst B)) :
    FiniteCorrespondenceGenerator f h := by
  apply A.incidenceImageGenerator B C
  have hr : Set.range (C.val.subschemeι ≫ A.incidenceSource B) =
      Set.range A.projection := by
    change Set.range (A.projection ∘ (C.val.subschemeι ≫ A.incidenceFst B)) = _
    exact hC.range_comp A.projection
  rw [hr]
  exact A.range_projection_mem

/-- A genuine generalizing incidence projection gives admissible images of each
actual reduced integral component, without reducing the incidence scheme. -/
noncomputable def incidenceComponentImageGenerator
    (hA : GeneralizingMap (A.incidenceFst B)) (x : genericPoints (A.incidence B)) :
    FiniteCorrespondenceGenerator f h :=
  A.incidenceImageGeneratorOfSurjective B (IntegralClosedSubscheme.pointClosure x.val)
    (surjective_pointClosure_of_finite_generalizing (A.incidenceFst B) hA x.val x.property)

end Motivic.FiniteCorrespondenceGenerator
