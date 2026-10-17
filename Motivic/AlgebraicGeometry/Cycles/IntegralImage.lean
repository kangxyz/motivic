/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Scheme.ReducedImage
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Integral images under finite morphisms

For a finite map from an integral scheme, its actual scheme-theoretic image
is an integral closed subscheme. The source maps finitely and surjectively
to that image. Its generic point maps to the image's generic point, and the
closed support is literally the set-theoretic image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

variable {X Y : Scheme.{u}}

/-- The factorization through the actual scheme-theoretic image is finite. -/
theorem isFinite_toImage (f : X ⟶ Y) [IsFinite f] : IsFinite f.toImage := by
  have : IsFinite (f.toImage ≫ f.imageι) := by simpa using (inferInstance : IsFinite f)
  exact IsFinite.of_comp f.toImage f.imageι

/-- A finite morphism surjects onto its scheme-theoretic image. -/
theorem surjective_toImage (f : X ⟶ Y) [IsFinite f] : Function.Surjective f.toImage := by
  have := isFinite_toImage f
  apply Set.range_eq_univ.mp
  rw [← f.toImage.isClosedMap.isClosed_range.closure_eq]
  exact IsDominant.denseRange.closure_range

/-- The actual closed image of an integral scheme under a finite map is integral. -/
theorem isIntegral_finiteImage (f : X ⟶ Y) [IsFinite f] [IsIntegral X] :
    IsIntegral f.image := by
  have := isReduced_schemeImage f
  have := (surjective_toImage f).irreducibleSpace f.toImage.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced f.image

/-- The ideal-sheaf support of a finite image is its set-theoretic image. -/
theorem support_finiteImage (f : X ⟶ Y) [IsFinite f] :
    (f.ker.support : Set Y) = Set.range f := by
  rw [f.support_ker, f.isClosedMap.isClosed_range.closure_eq]

/-- The source generic point is the generic point of the actual image. -/
theorem genericPoint_toImage (f : X ⟶ Y) [IsFinite f] [IsIntegral X] :
    letI := isIntegral_finiteImage f
    f.toImage (genericPoint X) = genericPoint f.image := by
  let := isIntegral_finiteImage f
  symm
  apply (genericPoint_spec f.image).eq
  simpa only [Set.image_univ, Set.range_eq_univ.mpr (surjective_toImage f), closure_univ]
    using (genericPoint_spec X).image f.toImage.continuous

/-- The embedded generic point of the actual image is the image of the source generic point. -/
theorem imageι_genericPoint (f : X ⟶ Y) [IsFinite f] [IsIntegral X] :
    letI := isIntegral_finiteImage f
    f.imageι (genericPoint f.image) = f (genericPoint X) := by
  let := isIntegral_finiteImage f
  rw [← genericPoint_toImage f, ← Scheme.Hom.comp_apply, f.toImage_imageι]

/-- The mapped generic point has exactly the actual finite-image support as its closure. -/
theorem isGenericPoint_finiteImage (f : X ⟶ Y) [IsFinite f] [IsIntegral X] :
    IsGenericPoint (f (genericPoint X)) (f.ker.support : Set Y) := by
  rw [f.support_ker]
  simpa only [Set.image_univ] using (genericPoint_spec X).image f.continuous

end Motivic
