/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import MotivicTest.RightWholeFiberTorRemainingList
public import MotivicTest.RightWholeFiberTorBoundedCoexistence

/-!
# Actual right whole remaining-list comparison with both regular-kernel APIs

The unchanged actual whole-coefficient comparison is consumed in the same
import environment as both original ambient and sequential quotient kernels.
This checks the complete dependent list closure, not merely its isolated leaf.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorRemainingListCoexistence
open _root_.AlgebraicGeometry.Scheme

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- Original supported Tor and the actual whole coefficient retain their comparison
when the two different regular-kernel APIs and the dependent list closure coexist. -/
def actualOriginalStalkComparison
    (x : {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = V.2.fromSpec p}) (n : ℕ) :
    F.rightFirstStageWholeOriginalStalkModule (S := Spec (.of K)) G H V p x n ≅
      F.rightFirstStageSupportedStalkTor (S := Spec (.of K)) G H x.1 n :=
  F.rightFirstStageWholeOriginalStalkIso (S := Spec (.of K)) G H V p x n

end Motivic.MotivicTest.RightWholeFiberTorRemainingListCoexistence
