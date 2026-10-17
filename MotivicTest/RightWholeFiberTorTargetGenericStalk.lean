/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorTargetGenericStalk
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Original smooth-site right generic target stalk consumers

These consumers retain the literal finite-pushed whole Tor sheaf at the
original global generic, with the local prime from the accepted exact index.
Relative quasi-coherence and finiteness are derived from the existing actual
coefficient construction and smooth finite-type geometry. These source-only
consumers have not been compiled or audited.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorTargetGenericStalk

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The actual smooth six-factor ambient is locally Noetherian. -/
local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K))
    X.hom Y.hom Z.hom W.hom

/-- The last-pair image is closed in the actual smooth Y-times-W product.
Its product with the original first support is locally finite type over that
image, giving the right target Noetherian hypothesis geometrically. -/
local instance : IsLocallyNoetherian (F.rightIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of K)) Y.hom
  have : IsLocallyNoetherian (pullback Y.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Y.left) (pullback.fst Y.hom W.hom)
  have : IsLocallyNoetherian (G.incidenceMap H).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback Y.hom W.hom)
      (G.incidenceMap H).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (G.incidenceMap H).image)
    (pullback.snd (F.targetProjection ≫ Y.hom)
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom))

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
  (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})

/-- The very same target affine contains the original global generic. -/
theorem actualGenericInOriginalChart : q.1.1 ∈ V.1 :=
  F.rightFirstStagePushforwardGeneric_mem (S := Spec (.of K)) G H V p q

/-- The inverse right target-generic index keeps the literal original local prime. -/
theorem actualOriginalGenericPrime :
    ((F.rightFirstStageTargetGenericEquiv G H V p).symm q).1 =
      (genericStalkLocalizationPrime (F.rightIntermediateImageProduct G H)
        (V.2.fromSpec p) q).asIdeal :=
  F.rightFirstStageTargetGenericEquiv_symm_val G H V p q

/-- The genuine right common-chart germs commute with the original scalar specialization. -/
theorem actualOriginalPushforwardGermSquare :
    ((F.rightIntermediateImageProduct G H).presheaf.stalkSpecializes q.2).hom.comp
        ((F.rightIntermediateImageProduct G H).presheaf.germ V.1 (V.2.fromSpec p)
          (V.2.range_fromSpec.subset (Set.mem_range_self p))).hom =
      ((F.rightIntermediateImageProduct G H).presheaf.germ V.1 q.1.1
        (actualGenericInOriginalChart K X Y Z W F G H V p q)).hom :=
  F.rightFirstStagePushforwardChart_germ_specializes G H V p q

/-- The actual specialization map extends the literal original pushed module. -/
def actualOriginalPushforwardSpecialization (n : ℕ) :
    (ModuleCat.extendScalars
      ((F.rightIntermediateImageProduct G H).presheaf.stalkSpecializes q.2).hom).obj
        (F.rightFirstStagePushforwardCoefficient (S := Spec (.of K)) G H V p n) ≅
      (ModuleStalk.functor q.1.1).obj
        ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
          (F.rightFirstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n)) :=
  F.rightFirstStagePushforwardGenericSpecializationIso (S := Spec (.of K)) G H V p q n

/-- The original specialization comparison follows its actual common affine
presentation, with the scalar-extension square retained explicitly. -/
theorem actualOriginalPushforwardSpecializationSquare (n : ℕ) :
    let T := F.rightIntermediateImageProduct G H
    let x := V.2.fromSpec p
    let hx : x ∈ V.1 := V.2.range_fromSpec.subset (Set.mem_range_self p)
    let hy := actualGenericInOriginalChart K X Y Z W F G H V p q
    let M := F.rightFirstStagePushforwardChartModule (S := Spec (.of K)) G H V n
    (F.rightFirstStagePushforwardGenericSpecializationIso
      (S := Spec (.of K)) G H V p q n).hom ≫
        (F.rightFirstStagePushforwardChartStalkIso
          (S := Spec (.of K)) G H V q.1.1 hy n).hom =
      (ModuleCat.extendScalars (T.presheaf.stalkSpecializes q.2).hom).map
          (F.rightFirstStagePushforwardChartStalkIso
            (S := Spec (.of K)) G H V x hx n).hom ≫
        (ModuleCat.extendScalarsComp (T.presheaf.germ V.1 x hx).hom
          (T.presheaf.stalkSpecializes q.2).hom).inv.app M ≫
        (eqToIso (congrArg (fun a => (ModuleCat.extendScalars a).obj M)
          (actualOriginalPushforwardGermSquare K X Y Z W F G H V p q))).hom :=
  F.rightFirstStagePushforwardSpecialization_chart_square
    (S := Spec (.of K)) G H V p q n

/-- Localizing at the literal inverse index produces the original sheaf stalk,
not a replacement module with an assumed scalar action. -/
def actualOriginalPushforwardGenericIso (n : ℕ) :
    let r := (F.rightFirstStageTargetGenericEquiv G H V p).symm q
    let : r.1.IsPrime := r.2.isPrime
    ModuleCat.of (Localization.AtPrime r.1)
        (LocalizedModule r.1.primeCompl
          (F.rightFirstStagePushforwardCoefficient (S := Spec (.of K)) G H V p n)) ≅
      (ModuleCat.restrictScalars
        (genericStalkLocalizationIso (F.rightIntermediateImageProduct G H)
          (V.2.fromSpec p) q).inv.hom).obj
        ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
            (F.rightFirstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n))) :=
  F.rightFirstStagePushforwardTargetGenericIso (S := Spec (.of K)) G H V p q n

/-- Actual tensor-localized lengths agree at the exact original global generic. -/
theorem actualOriginalPushforwardGenericLength (n : ℕ) :
    let r := (F.rightFirstStageTargetGenericEquiv G H V p).symm q
    let : r.1.IsPrime := r.2.isPrime
    Module.length (Localization.AtPrime r.1)
        (Localization.AtPrime r.1 ⊗[(F.rightIntermediateImageProduct G H).presheaf.stalk
          (V.2.fromSpec p)]
          (F.rightFirstStagePushforwardCoefficient (S := Spec (.of K)) G H V p n)) =
      Module.length ((F.rightIntermediateImageProduct G H).presheaf.stalk q.1.1)
        ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
            (F.rightFirstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n))) :=
  F.rightFirstStagePushforwardTargetGeneric_length (S := Spec (.of K)) G H V p q n

/-- The generic length is finite before conversion to an integer. -/
theorem actualOriginalPushforwardGenericFinite (n : ℕ) :
    Module.length ((F.rightIntermediateImageProduct G H).presheaf.stalk q.1.1)
        ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
            (F.rightFirstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n))) ≠ ⊤ :=
  F.rightFirstStagePushforwardGenericStalk_length_ne_top (S := Spec (.of K)) G H V p q n

/-- The accepted fixed-support weight is the actual original generic stalk length. -/
theorem actualOriginalPushforwardGenericWeight (n : ℕ) :
    F.rightFirstStagePushforwardGenericLength (S := Spec (.of K)) G H V p n
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      LengthEuler.integerLength
        ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
            (F.rightFirstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n)))
        (actualOriginalPushforwardGenericFinite K X Y Z W F G H V p q n) :=
  F.rightFirstStagePushforwardGenericLength_eq_original (S := Spec (.of K)) G H V p q n

/-- The actual smooth Z diagonal gives one module bound for every original
generic pushed stalk, retaining all branches and nonreduced scalar actions. -/
theorem actualOriginalPushforwardGenericBound :
    ∃ b : ℕ, ∀ n, b ≤ n →
      ∀ q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        Subsingleton ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
            (F.rightFirstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n))) :=
  F.rightFirstStagePushforwardGenericStalk_exists_bound (S := Spec (.of K)) G H V p

/-- Actual generic modules have finite full lengths and finite nonzero-degree
support before any signed integer Euler sum is used. -/
theorem actualOriginalPushforwardFiniteLengthSupport :
    LengthEuler.FiniteLengthSupport (fun n => (ModuleStalk.functor q.1.1).obj
      ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
        (F.rightFirstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n))) :=
  F.rightFirstStagePushforwardGenericStalk_finiteLengthSupport
    (S := Spec (.of K)) G H V p q

/-- The accepted right generic outer weight is the genuine signed Euler length
of the original finite-pushed sheaf stalks, at the exact original global generic. -/
theorem actualOriginalPushforwardSignedEuler :
    F.rightFirstStagePushforwardGenericEuler (S := Spec (.of K)) G H V p
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      LengthEuler.signedLengthSum (fun n => (ModuleStalk.functor q.1.1).obj
        ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
          (F.rightFirstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n)))
        (fun n : ℕ => (-1 : ℤ) ^ n)
        (actualOriginalPushforwardFiniteLengthSupport K X Y Z W F G H V p q) :=
  F.rightFirstStagePushforwardGenericEuler_eq_original (S := Spec (.of K)) G H V p q

end Motivic.MotivicTest.RightWholeFiberTorTargetGenericStalk
