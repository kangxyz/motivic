/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.RightWholeFiberTorRemainingSupport
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Motivic.Intersection

universe u

namespace MotivicTest.RightWholeFiberTorRemainingSupport

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
    ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w))),
      RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w))) s ∧
        (pullback.diagonal Y.hom).ker.stalk
          (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w)) =
        Ideal.ofList s := by
  have aux (z : Y.left) (p : (pullback Y.hom Y.hom : Scheme.{u}))
      (hp : pullback.diagonal Y.hom z = p) :
      ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk p),
        RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk p) s ∧
          (pullback.diagonal Y.hom).ker.stalk p = Ideal.ofList s := by
    subst p
    obtain ⟨s, hs, hker⟩ := Diagonal.exists_regular_kernel_of_smooth Y.hom z
    exact ⟨s, hs, ((pullback.diagonal Y.hom).ker_stalk z).trans hker⟩
  exact aux _ _ (congrArg (fun k => k w) (F.rightRemainingDiagonal_isPullback G H).w)

variable (U : (F.rightIntermediateImageProduct G H).affineOpens)
  (w : F.tripleIncidence G H)
  (s : List ((pullback Y.hom Y.hom).presheaf.stalk
    (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w))))
  (hker : (pullback.diagonal Y.hom).ker.stalk
      (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w)) =
    Ideal.ofList s)
  (hw : w ∈ genericPoints (F.tripleIncidence G H))
  (hU : F.tripleIncidenceToRightSupportProduct G H w ∈
    (F.rightIntermediateImageMap G H) ⁻¹ᵁ U)

include hker hw hU in
/-- The original smooth-site hypotheses imply every actual remaining Koszul
homology length is finite, in all first-stage Tor degrees. -/
theorem actualSmoothRemaining_length_ne_top (n m : ℕ) :
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk
      (F.tripleIncidenceToRightSupportProduct G H w))
      ((Koszul.coefficientComplex
        (F.rightWholeFiberTorOriginalStalk G H U
          (F.tripleIncidenceToRightSupportProduct G H w) n)
        (s.map ((F.rightSupportMiddlePair G H).stalkMap
          (F.tripleIncidenceToRightSupportProduct G H w)).hom)).homology m) ≠ ⊤ :=
  (F.rightWholeFiberTorRemaining_finiteHomology G H U w s hker hw hU n).finite_length m

include hker hw hU in
/-- The actual whole-open coefficient retains finite remaining homology after
the literal open-inclusion scalar map, rather than an abstract stalk equivalence. -/
theorem actualSmoothWholeCoefficientRemaining_finiteHomology (n : ℕ) :
    let x : ((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).toScheme :=
      ⟨F.tripleIncidenceToRightSupportProduct G H w, hU⟩
    LengthEuler.FiniteHomology
      (Koszul.coefficientComplex
        ((ModuleStalk.functor x).obj
          (wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
            (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
            (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
            (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) U n))
        ((s.map ((F.rightSupportMiddlePair G H).stalkMap
          (F.tripleIncidenceToRightSupportProduct G H w)).hom).map
            (((F.rightIntermediateImageMap G H) ⁻¹ᵁ U).ι.stalkMap x).hom)) :=
  F.rightWholeFiberTorCoefficientRemaining_finiteHomology G H U w s hker hw hU n

include hw hU in
/-- The list itself is obtained from original smooth geometry. The same list
works for all degrees of the constructed first-stage Tor coefficient. -/
theorem exists_actualSmoothRemaining_finiteHomology :
    ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w))),
      RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w))) s ∧
        (pullback.diagonal Y.hom).ker.stalk
          (F.rightSupportMiddlePair G H (F.tripleIncidenceToRightSupportProduct G H w)) =
            Ideal.ofList s ∧
        ∀ n, LengthEuler.FiniteHomology
          (Koszul.coefficientComplex
            (F.rightWholeFiberTorOriginalStalk G H U
              (F.tripleIncidenceToRightSupportProduct G H w) n)
            (s.map ((F.rightSupportMiddlePair G H).stalkMap
              (F.tripleIncidenceToRightSupportProduct G H w)).hom)) := by
  obtain ⟨s, hs, hker⟩ := exists_actualRemainingList K X Y Z W F G H w
  exact ⟨s, hs, hker,
    fun n => F.rightWholeFiberTorRemaining_finiteHomology G H U w s hker hw hU n⟩

end MotivicTest.RightWholeFiberTorRemainingSupport
