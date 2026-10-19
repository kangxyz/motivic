/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.MiddleKoszulLength

/-! # Actual incidence Tor keeps the original middle list in every degree -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme.Products (correspondenceTripleMiddle)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Diagonal (baseChangeStalkMap)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence

universe u

namespace MotivicTest.IncidenceMiddleKoszulLength

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

example (w : A.incidence B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom
        (correspondenceTripleMiddle X.hom Y.hom Z.hom (A.incidenceInclusion B w)))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom
        (correspondenceTripleMiddle X.hom Y.hom Z.hom (A.incidenceInclusion B w)))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (correspondenceTripleMiddle X.hom Y.hom Z.hom (A.incidenceInclusion B w))).hom =
        Ideal.ofList s) (n : ℕ) :
    Module.length (A.incidenceAmbientStalk B w) (A.incidenceTor B w n) =
      Module.length ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w))
        ((_root_.ChainComplex.Koszul.coefficientComplex
          (ModuleCat.of ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w))
            ((A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w)))
          (s.map (baseChangeStalkMap
            (A.originalIncidence_middle_isPullback B) w).hom)).homology n) :=
  A.incidenceTor_length_eq_middleKoszul B w s hs hker n

end MotivicTest.IncidenceMiddleKoszulLength
