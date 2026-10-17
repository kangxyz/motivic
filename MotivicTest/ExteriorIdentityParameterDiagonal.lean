/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityParameterDiagonal
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-!
# Actual exterior coefficient parameter-diagonal consumers

The coefficient parameter map is flat even when the original correspondence
supports are not flat over the intermediate smooth scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open RingTheory.Sequence

universe u

namespace MotivicTest.ExteriorIdentityParameterDiagonal

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom) (n : ℕ)

example : Flat (A.exteriorCoefficientParameterPair (AlgebraicSimplex.smoothSiteObj k n) B) :=
  inferInstance

example : IsClosedImmersion
    (A.exteriorParameterDiagonalInclusion (AlgebraicSimplex.smoothSiteObj k n) B) := inferInstance

example (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
    (z : A.exteriorParameterDiagonal T B) :
    let R := ((A.exteriorIdentityGenerator T).supportProduct
      (B.exteriorIdentityGenerator T)).presheaf.stalk
        (A.exteriorParameterDiagonalInclusion T B z)
    let S := (A.exteriorParameterDiagonal T B).presheaf.stalk z
    let f := ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom
    ∃ t : List R, IsRegular R t ∧ RingHom.ker f = Ideal.ofList t ∧
      ∀ (s : List R) (d : ℕ),
        Module.length R ((Koszul.coefficientComplex (ModuleCat.of R R) (t ++ s)).homology d) =
          Module.length S
            ((Koszul.coefficientComplex (ModuleCat.of S S) (s.map f)).homology d) := by
  dsimp only
  obtain ⟨t, ht, hker⟩ := A.exteriorParameterDiagonal_exists_regular_kernel T B z
  refine ⟨t, ht, hker, fun s d => ?_⟩
  exact Koszul.regularBlockHomology_length
    ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom
    ((A.exteriorParameterDiagonalInclusion T B).stalkMap_surjective z)
    t s hker ht.toIsWeaklyRegular d

end MotivicTest.ExteriorIdentityParameterDiagonal
