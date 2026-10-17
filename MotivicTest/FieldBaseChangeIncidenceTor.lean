/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeIncidenceTor

/-!
# Consumers of the actual field-change component Tor attachment

Every coefficient uses the fixed original middle-diagonal list in the whole
new product stalk and the literal unreduced component-pair immersion. The lift
case retains all actual new generator Tor terms; the no-lift case is zero.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open RingTheory.Sequence

universe u

namespace MotivicTest.FieldBaseChangeIncidenceTor

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (a : genericPoints (A.fieldBaseChangeSupport φ))
  (b : genericPoints (B.fieldBaseChangeSupport φ))

/-- The actual component-generator incidence has the literal whole-incidence square. -/
theorem actualComponentSquare :
    IsPullback (A.fieldBaseChangeComponentIncidenceToWhole φ B a b)
      ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
        (B.fieldBaseChangeComponentGenerator φ b))
      (A.fieldBaseChangeIncidenceToSupportProduct φ B)
      (A.fieldBaseChangeGeneratorPairInclusion φ B a b) :=
  A.fieldBaseChangeComponentIncidence_isPullback φ B a b

/-- The pair product is the original unreduced product, transported only by an isomorphism. -/
theorem actualPairIdeal :
    (A.fieldBaseChangeGeneratorPairInclusion φ B a b).ker =
      (A.fieldBaseChangeComponentPairInclusion φ B a b).ker :=
  A.fieldBaseChangeGeneratorPairInclusion_ker φ B a b

/-- Admissibility supplies genericity, without requiring the source projection to be flat. -/
theorem actualGenericPreservation
    (v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b))) :
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 ∈
      genericPoints (A.fieldBaseChangeIncidence φ B) :=
  A.fieldBaseChangeComponentIncidenceToWhole_generic φ B a b v

example : IsClosedImmersion (A.fieldBaseChangeComponentIncidenceToWhole φ B a b) :=
  inferInstance

variable (w : genericPoints (A.fieldBaseChangeIncidence φ B))
  (s : List ((pullback Y.hom Y.hom).presheaf.stalk
    (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
  (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
    (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s)

include hker in
/-- The finite-homology proof comes from the actual whole-incidence Artinian cut. -/
theorem actualPairFiniteHomology :
    LengthEuler.FiniteHomology (A.fieldBaseChangePairQuotientKoszul φ B a b w.1 s) :=
  A.fieldBaseChangePairQuotientKoszul_finiteHomology φ B a b w s hker

/-- At an actual generic lift, the exact fixed-list Euler is the full signed Tor coefficient. -/
theorem actualPairEulerAtLift
    (v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b)))
    (hv : A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 = w.1)
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))) s) :
    A.fieldBaseChangePairQuotientEuler φ B a b w s hker =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceTorCoefficient (S := Spec (.of L))
        (B.fieldBaseChangeComponentGenerator φ b) v :=
  A.fieldBaseChangePairQuotientEuler_eq_tor φ B a b w v hv s hs hker

/-- No generic lift means zero for the same literal pair quotient and original list. -/
theorem actualPairEulerOffImage
    (hno : ¬ ∃ v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
        (B.fieldBaseChangeComponentGenerator φ b)),
      A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 = w.1) :
    A.fieldBaseChangePairQuotientEuler φ B a b w s hker = 0 :=
  A.fieldBaseChangePairQuotientEuler_eq_zero_of_no_lift φ B a b w hno s hker

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondenceGenerator.fieldBaseChangeComponentSchemeIso,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentPairMap_isIso,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeGeneratorPairInclusion_ker,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentIncidence_isPullback,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentIncidenceToWhole_generic,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentIncidence_exists_generic_iff,
      ``FiniteCorrespondenceGenerator.fieldBaseChangePair_ker_stalk_eq_top_of_no_lift,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeGeneratorPairInclusion_middle,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponent_middle_isPullback,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentMiddleStalkMap,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentMiddleList_eq,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentTor_length_at_oldMiddle,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentMiddleStalkMap_square,
      ``FiniteCorrespondenceGenerator.fieldBaseChangePairQuotientKoszul_finiteHomology,
      ``FiniteCorrespondenceGenerator.fieldBaseChangePairQuotientEuler_eq_zero_of_no_lift,
      ``FiniteCorrespondenceGenerator.fieldBaseChangePairQuotientKoszul_length_at_lift,
      ``FiniteCorrespondenceGenerator.fieldBaseChangePairQuotientEuler_eq_tor,
      ``actualComponentSquare, ``actualPairIdeal, ``actualGenericPreservation,
      ``actualPairFiniteHomology, ``actualPairEulerAtLift, ``actualPairEulerOffImage] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual component-generator field-change Tor uses only standard foundations."

end MotivicTest.FieldBaseChangeIncidenceTor
