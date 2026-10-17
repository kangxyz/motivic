/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeIncidence

/-!
# Consumers of the actual whole-incidence field-change bridge

The extension is arbitrary. The actual full support product and incidence
supply the Cartesian diagrams, Artinian cut, original scalar list, and
closed-fiber multiplier. No component quotient is inserted in the ambient
Artinian-support hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open RingTheory.Sequence

universe u

namespace MotivicTest.FieldBaseChangeIncidence

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The unreduced whole new incidence is genuinely the old incidence's field pullback. -/
theorem actualWholeIncidenceSquare :
    IsPullback (A.fieldBaseChangeIncidenceToOriginal φ B)
      (A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeSupportHom φ)
      (A.incidenceSource B ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) :=
  A.fieldBaseChangeIncidence_isPullback φ B

/-- The original middle diagonal cuts out the full new support-product incidence. -/
theorem actualOriginalMiddleSquare :
    IsPullback
      (A.fieldBaseChangeIncidenceToOriginal φ B ≫ A.incidenceInclusion B ≫
        correspondenceTripleMiddle X.hom Y.hom Z.hom)
      (A.fieldBaseChangeIncidenceToSupportProduct φ B) (pullback.diagonal Y.hom)
      (A.fieldBaseChangeSupportProductToOriginal φ B ≫ A.originalCoefficientMiddlePair B) :=
  A.fieldBaseChangeIncidence_middle_isPullback φ B

/-- No finite-type condition on the field extension is required. -/
example : IsNoetherian (A.fieldBaseChangeSupportProduct φ B) := inferInstance

/-- No reducedness condition on the whole incidence is required. -/
example : IsNoetherian (A.fieldBaseChangeIncidence φ B) := inferInstance

/-- The field projection is flat without requiring the finite source projection to be flat. -/
example : Flat (A.fieldBaseChangeIncidenceToOriginal φ B) := inferInstance

variable (w : genericPoints (A.fieldBaseChangeIncidence φ B))
  (s : List ((pullback Y.hom Y.hom).presheaf.stalk
    (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
  (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
    (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s)

include hker in
/-- The Artinian ring is the same-list quotient of the whole new product stalk. -/
theorem actualArtinianCut :
    IsArtinianRing (((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
      (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1)) ⧸
        (Ideal.ofList (A.fieldBaseChangeMiddleList φ B w.1 s) ⊔ ⊥)) :=
  A.fieldBaseChangeMiddleList_support_isArtinian φ B w s hker

include hker in
/-- Its regular coefficient homology has finite support and lengths from actual geometry. -/
theorem actualFiniteHomology :
    LengthEuler.FiniteHomology (A.fieldBaseChangeMiddleKoszul φ B w.1 s) :=
  A.fieldBaseChangeMiddleKoszul_finiteHomology φ B w s hker

/-- The signed coefficient retains the old higher Tor and the whole closed-fiber length. -/
theorem actualSignedTorMultiplier
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))) s) :
    A.fieldBaseChangeMiddleKoszulCoefficient φ B w s hker =
      A.incidenceTorCoefficient (S := Spec (.of k)) B
        (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
        A.fieldBaseChangeIncidenceFiberMultiplicity φ B w :=
  A.fieldBaseChangeMiddleKoszulCoefficient_eq φ B w s hs hker

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondenceGenerator.fieldBaseChangeSupportProduct_isPullback,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidence_isPullback,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidence_support_isPullback,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidence_middle_isPullback,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleList_ideal,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleList_mem_maximalIdeal,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleListQuotientEquiv,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleList_support_isArtinian,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleStalkMap_comp,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleList_eq,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidence_closedFiber_length,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleKoszul_length,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleKoszulCoefficient_eq,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeSupportProduct_fundamentalCycle,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeMiddleKoszulCoefficient_eq_component_pair_sum,
      ``actualWholeIncidenceSquare, ``actualOriginalMiddleSquare, ``actualArtinianCut,
      ``actualFiniteHomology, ``actualSignedTorMultiplier] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual whole-incidence field change uses only standard foundations."

end MotivicTest.FieldBaseChangeIncidence
