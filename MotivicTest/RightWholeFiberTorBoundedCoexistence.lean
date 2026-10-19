/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.Triple.CombinedRegularity
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorBounded

/-!
# Distinct original right-ambient and first-quotient regular kernels coexist

Both original geometries are imported together. The renamed right-first-stage
ambient kernel lives in the original six-factor stalk; the accepted second
sequential kernel lives in the first-diagonal quotient stalk. Their actual
point domains, inclusions, and kernel ideals are retained separately.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorBoundedCoexistence
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  [Flat f] [Flat g] [Smooth h] [IsSeparated h] [Flat i]

/-- The right-first second diagonal has its kernel in the original six-factor ambient. -/
theorem actualRightAmbientKernel (q : correspondenceSecondDiagonalAmbient f g h i) :
    ∃ s : List ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (correspondenceSecondAmbientInclusion f g h i q)),
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (correspondenceSecondAmbientInclusion f g h i q)) s ∧
      RingHom.ker ((correspondenceSecondAmbientInclusion f g h i).stalkMap q).hom =
        Ideal.ofList s :=
  exists_regular_kernel_correspondenceSecondAmbient f g h i q

/-- The accepted sequential second kernel remains in the actual first-diagonal quotient. -/
theorem actualFirstQuotientKernel (q : correspondenceFourfoldProduct f g h i) :
    ∃ s : List ((correspondenceFirstDiagonal f g h i).presheaf.stalk
        (correspondenceSecondDiagonalInclusion f g h i q)),
      IsRegular ((correspondenceFirstDiagonal f g h i).presheaf.stalk
        (correspondenceSecondDiagonalInclusion f g h i q)) s ∧
      RingHom.ker ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom =
        Ideal.ofList s :=
  exists_regular_kernel_correspondenceSecondDiagonal f g h i q

end Motivic.MotivicTest.RightWholeFiberTorBoundedCoexistence
