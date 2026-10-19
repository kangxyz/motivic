/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.WholeFiberTorRemainingSupport
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Original smooth-site consumers of remaining-diagonal finite length

Over an arbitrary field, the actual six-factor geometry supplies Noetherianity
and separatedness. At a generic point of the original triple incidence the
constructed whole-fiber Tor coefficient has finite remaining Koszul homology.
All equations come from the original middle diagonal; no finite-length,
coefficient-regularity, or common-dimension premise is supplied.
-/

@[expose] public section

noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite correspondenceSixfoldAmbient_isSeparated
  isLocallyNoetherian_correspondenceSixfoldAmbient)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceFirstDiagonalInclusion
  correspondenceSixfoldAmbient)
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Motivic
open _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace MotivicTest.WholeFiberTorRemainingSupport
open _root_.AlgebraicGeometry.Scheme.Modules

variable (K : Type u) [Field K]
  (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance : (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated (S := Spec (.of K)) X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K)) X.hom Y.hom Z.hom W.hom

/-- Smoothness of the actual middle object supplies a regular list of its
literal diagonal ideal at each original triple-incidence middle point. -/
theorem exists_actualRemainingList (w : F.tripleIncidence G H) :
    ∃ s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w))),
      RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w))) s ∧
        (pullback.diagonal Z.hom).ker.stalk
          (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w)) =
        Ideal.ofList s := by
  have aux (z : Z.left) (p : (pullback Z.hom Z.hom : Scheme.{u}))
      (hp : pullback.diagonal Z.hom z = p) :
      ∃ s : List ((pullback Z.hom Z.hom).presheaf.stalk p),
        RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk p) s ∧
          (pullback.diagonal Z.hom).ker.stalk p = Ideal.ofList s := by
    subst p
    obtain ⟨s, hs, hker⟩ :=
      _root_.AlgebraicGeometry.Scheme.Diagonal.exists_regular_kernel_of_smooth Z.hom z
    exact ⟨s, hs, ((pullback.diagonal Z.hom).ker_stalk z).trans hker⟩
  exact aux _ _ (congrArg (fun k => k w) (F.remainingDiagonal_isPullback G H).w)

variable (U : (F.leftIntermediateImageProduct G H).affineOpens)
  (w : F.tripleIncidence G H)
  (s : List ((pullback Z.hom Z.hom).presheaf.stalk
    (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w))))
  (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w)) =
    Ideal.ofList s)
  (hw : w ∈ genericPoints (F.tripleIncidence G H))
  (hU : F.tripleIncidenceToLeftSupportProduct G H w ∈
    (F.leftIntermediateImageMap G H) ⁻¹ᵁ U)

include hker hw hU in
/-- The original smooth-site hypotheses imply every actual remaining Koszul
homology length is finite, in all first-stage Tor degrees. -/
theorem actualSmoothRemaining_length_ne_top (n m : ℕ) :
    Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk
      (F.tripleIncidenceToLeftSupportProduct G H w))
      ((_root_.ChainComplex.Koszul.coefficientComplex
        (F.leftWholeFiberTorOriginalStalk G H U
          (F.tripleIncidenceToLeftSupportProduct G H w) n)
        (s.map ((F.leftSupportMiddlePair G H).stalkMap
          (F.tripleIncidenceToLeftSupportProduct G H w)).hom)).homology m) ≠ ⊤ :=
  (F.leftWholeFiberTorRemaining_finiteHomology G H U w s hker hw hU n).finite_length m

include hker hw hU in
/-- The actual whole-open coefficient retains finite remaining homology after
the literal open-inclusion scalar map, rather than an abstract stalk equivalence. -/
theorem actualSmoothWholeCoefficientRemaining_finiteHomology (n : ℕ) :
    let x : ((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).toScheme :=
      ⟨F.tripleIncidenceToLeftSupportProduct G H w, hU⟩
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
      (_root_.ChainComplex.Koszul.coefficientComplex
        ((Stalk.functor x).obj
          (wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
            (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
            (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
            (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) U n))
        ((s.map ((F.leftSupportMiddlePair G H).stalkMap
          (F.tripleIncidenceToLeftSupportProduct G H w)).hom).map
            (((F.leftIntermediateImageMap G H) ⁻¹ᵁ U).ι.stalkMap x).hom)) :=
  F.leftWholeFiberTorCoefficientRemaining_finiteHomology G H U w s hker hw hU n

include hw hU in
/-- The list itself is obtained from original smooth geometry. The same list
works for all degrees of the constructed first-stage Tor coefficient. -/
theorem exists_actualSmoothRemaining_finiteHomology :
    ∃ s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w))),
      RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w))) s ∧
        (pullback.diagonal Z.hom).ker.stalk
          (F.leftSupportMiddlePair G H (F.tripleIncidenceToLeftSupportProduct G H w)) =
            Ideal.ofList s ∧
        ∀ n, _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology
          (_root_.ChainComplex.Koszul.coefficientComplex
            (F.leftWholeFiberTorOriginalStalk G H U
              (F.tripleIncidenceToLeftSupportProduct G H w) n)
            (s.map ((F.leftSupportMiddlePair G H).stalkMap
              (F.tripleIncidenceToLeftSupportProduct G H w)).hom)) := by
  obtain ⟨s, hs, hker⟩ := exists_actualRemainingList K X Y Z W F G H w
  exact ⟨s, hs, hker,
    fun n => F.leftWholeFiberTorRemaining_finiteHomology G H U w s hker hw hU n⟩

end MotivicTest.WholeFiberTorRemainingSupport
