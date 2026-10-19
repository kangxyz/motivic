/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.IncidenceTorReduction
public import Motivic.Aglib.AlgebraicGeometry.Simplex.ExteriorGeometry

/-! # Consumers of the actual exterior-incidence Tor reduction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence

universe u

namespace MotivicTest.ExteriorIdentityIncidenceTorReduction
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

example
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.exteriorIncidenceOldMiddlePoint B T w))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.exteriorIncidenceOldMiddlePoint B T w))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.exteriorIncidenceOldMiddlePoint B T w)).hom = Ideal.ofList s) (n : ℕ) :
    Module.length
      ((A.exteriorIdentityGenerator T).incidenceAmbientStalk (B.exteriorIdentityGenerator T) w)
      ((A.exteriorIdentityGenerator T).incidenceTor (B.exteriorIdentityGenerator T) w n) =
    Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk
        (A.exteriorIncidenceToCoefficientQuotient B T w))
      ((_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of ((A.exteriorParameterDiagonal T B).presheaf.stalk
            (A.exteriorIncidenceToCoefficientQuotient B T w))
          ((A.exteriorParameterDiagonal T B).presheaf.stalk
            (A.exteriorIncidenceToCoefficientQuotient B T w)))
        (A.exteriorIncidenceRemainingList B T w s)).homology n) :=
  A.exteriorIncidenceTor_length_eq_remaining B T w s hs hker n

end MotivicTest.ExteriorIdentityIncidenceTorReduction
