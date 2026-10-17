/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorTargetGenericStalk
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Original smooth-site generic target stalk consumers

These consumers retain the literal finite-pushed whole Tor sheaf at the
original global generic, with the local prime from the accepted exact index.
Relative quasi-coherence and finiteness are derived from the existing actual
coefficient construction and smooth finite-type geometry.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.MotivicTest.WholeFiberTorTargetGenericStalk

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The actual smooth six-factor ambient is locally Noetherian. -/
local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K))
    X.hom Y.hom Z.hom W.hom

/-- The target Noetherian hypothesis comes from its actual finite-type geometry. -/
local instance : IsLocallyNoetherian (F.leftIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of K)) X.hom
  have : IsLocallyNoetherian (pullback X.hom Z.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X.left) (pullback.fst X.hom Z.hom)
  have : IsLocallyNoetherian (F.incidenceMap G).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback X.hom Z.hom)
      (F.incidenceMap G).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (F.incidenceMap G).image)
    (pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
      (H.projection ≫ Z.hom))

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
  (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})

/-- The very same target affine contains the original global generic. -/
theorem actualGenericInOriginalChart : q.1.1 ∈ V.1 :=
  F.firstStagePushforwardGeneric_mem (S := Spec (.of K)) G H V p q

/-- The actual specialization map extends the literal original pushed module. -/
def actualOriginalPushforwardSpecialization (n : ℕ) :
    (ModuleCat.extendScalars
      ((F.leftIntermediateImageProduct G H).presheaf.stalkSpecializes q.2).hom).obj
        (F.firstStagePushforwardCoefficient (S := Spec (.of K)) G H V p n) ≅
      (ModuleStalk.functor q.1.1).obj
        ((Scheme.Modules.pushforward (F.leftIntermediateImageMap G H)).obj
          (F.firstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n)) :=
  F.firstStagePushforwardGenericSpecializationIso (S := Spec (.of K)) G H V p q n

/-- Localizing at the literal inverse index produces the original sheaf stalk,
not a replacement module with an assumed scalar action. -/
def actualOriginalPushforwardGenericIso (n : ℕ) :
    let r := (F.firstStageTargetGenericEquiv G H V p).symm q
    let : r.1.IsPrime := r.2.isPrime
    ModuleCat.of (Localization.AtPrime r.1)
        (LocalizedModule r.1.primeCompl
          (F.firstStagePushforwardCoefficient (S := Spec (.of K)) G H V p n)) ≅
      (ModuleCat.restrictScalars
        (genericStalkLocalizationIso (F.leftIntermediateImageProduct G H)
          (V.2.fromSpec p) q).inv.hom).obj
        ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.leftIntermediateImageMap G H)).obj
            (F.firstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n))) :=
  F.firstStagePushforwardTargetGenericIso (S := Spec (.of K)) G H V p q n

/-- Actual tensor-localized lengths agree at the exact original global generic. -/
theorem actualOriginalPushforwardGenericLength (n : ℕ) :
    let r := (F.firstStageTargetGenericEquiv G H V p).symm q
    let : r.1.IsPrime := r.2.isPrime
    Module.length (Localization.AtPrime r.1)
        (Localization.AtPrime r.1 ⊗[(F.leftIntermediateImageProduct G H).presheaf.stalk
          (V.2.fromSpec p)] (F.firstStagePushforwardCoefficient (S := Spec (.of K)) G H V p n)) =
      Module.length ((F.leftIntermediateImageProduct G H).presheaf.stalk q.1.1)
        ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.leftIntermediateImageMap G H)).obj
            (F.firstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n))) :=
  F.firstStagePushforwardTargetGeneric_length (S := Spec (.of K)) G H V p q n

/-- The generic length is finite before conversion to an integer. -/
theorem actualOriginalPushforwardGenericFinite (n : ℕ) :
    Module.length ((F.leftIntermediateImageProduct G H).presheaf.stalk q.1.1)
        ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.leftIntermediateImageMap G H)).obj
            (F.firstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n))) ≠ ⊤ :=
  F.firstStagePushforwardGenericStalk_length_ne_top (S := Spec (.of K)) G H V p q n

/-- The accepted fixed-support weight is the actual original generic stalk length. -/
theorem actualOriginalPushforwardGenericWeight (n : ℕ) :
    F.firstStagePushforwardGenericLength (S := Spec (.of K)) G H V p n
        ((F.firstStageTargetGenericEquiv G H V p).symm q) =
      LengthEuler.integerLength
        ((ModuleStalk.functor q.1.1).obj
          ((Scheme.Modules.pushforward (F.leftIntermediateImageMap G H)).obj
            (F.firstStageWholeAmbientCoefficient (S := Spec (.of K)) G H V n)))
        (actualOriginalPushforwardGenericFinite K X Y Z W F G H V p q n) :=
  F.firstStagePushforwardGenericLength_eq_original (S := Spec (.of K)) G H V p q n

end Motivic.MotivicTest.WholeFiberTorTargetGenericStalk
