/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorTargetReplacement
public import Motivic.AlgebraicGeometry.Modules.RelativeFinitePushforwardGenericStalk

/-!
# Original target generic stalks of the finite-pushed whole Tor coefficient

The local generic coefficient from fixed-zero-support replacement is attached
to the original finite pushforward sheaf at the exact global generic point.
That point belongs to the identical target affine open by specialization. The
actual constructed whole inverse-image Tor coefficient supplies relative
quasi-coherence, hence the genuine common-chart module comparison; global
quasi-coherence of its ambient equalizer is never assumed. Full generic stalk
lengths are preserved, with finiteness proved before integer conversion.
Residue-degree sums and correspondence-cycle comparisons remain separate.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.FiniteCorrespondenceGenerator

open Intersection FiniteSchemeEuler LengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

/-- The original sheaf at the global generic: the finite pushforward of the
same whole Tor ambient equalizer used in the unchanged target coefficient. -/
abbrev firstStagePushforwardGenericStalk
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :=
  (ModuleStalk.functor q.1.1).obj
    ((Scheme.Modules.pushforward (F.leftIntermediateImageMap G H)).obj
      (F.firstStageWholeAmbientCoefficient G H V n))

omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i] in
/-- The exact original target generic and the original target point lie in
the same selected affine open; no second coefficient cover is introduced. -/
theorem firstStagePushforwardGeneric_mem
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    q.1.1 ∈ V.1 :=
  q.2.mem_open V.1.isOpen (V.2.range_fromSpec.subset (Set.mem_range_self p))

/-- The original target coefficient specializes to the original generic stalk
through its actual structure-stalk map and the genuine common whole Tor chart. -/
def firstStagePushforwardGenericSpecializationIso
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    (ModuleCat.extendScalars
      ((F.leftIntermediateImageProduct G H).presheaf.stalkSpecializes q.2).hom).obj
        (F.firstStagePushforwardCoefficient G H V p n) ≅
      F.firstStagePushforwardGenericStalk G H V p q n := by
  let φ := F.leftIntermediateImageMap G H
  let N := F.firstStageWholeAmbientCoefficient G H V n
  have : ((Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).obj N).IsQuasicoherent :=
    wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n
  exact RelativeFinitePushforward.originalPushforwardStalkSpecializationIso φ V N
    (V.2.fromSpec p) q.1.1 (V.2.range_fromSpec.subset (Set.mem_range_self p)) q.2

/-- The literal local prime from the already proved exact target-generic index
localizes the original pushed coefficient to the original global generic stalk.
The scalar action is the inverse canonical generic-stalk localization map. -/
def firstStagePushforwardTargetGenericIso
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    let r := (F.firstStageTargetGenericEquiv G H V p).symm q
    let : r.1.IsPrime := r.2.isPrime
    ModuleCat.of (Localization.AtPrime r.1)
        (LocalizedModule r.1.primeCompl (F.firstStagePushforwardCoefficient G H V p n)) ≅
      (ModuleCat.restrictScalars
        (genericStalkLocalizationIso (F.leftIntermediateImageProduct G H)
          (V.2.fromSpec p) q).inv.hom).obj
        (F.firstStagePushforwardGenericStalk G H V p q n) := by
  let φ := F.leftIntermediateImageMap G H
  let N := F.firstStageWholeAmbientCoefficient G H V n
  have : ((Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).obj N).IsQuasicoherent :=
    wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n
  exact RelativeFinitePushforward.originalPushforwardStalkGenericIso φ V N
    (V.2.fromSpec p) (V.2.range_fromSpec.subset (Set.mem_range_self p)) q

/-- The actual tensor-localized target multiplicity equals the length of the
original full generic pushforward stalk, including its nonreduced action. -/
theorem firstStagePushforwardTargetGeneric_length
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    let r := (F.firstStageTargetGenericEquiv G H V p).symm q
    let : r.1.IsPrime := r.2.isPrime
    Module.length (Localization.AtPrime r.1)
        (Localization.AtPrime r.1 ⊗[(F.leftIntermediateImageProduct G H).presheaf.stalk
          (V.2.fromSpec p)] (F.firstStagePushforwardCoefficient G H V p n)) =
      Module.length ((F.leftIntermediateImageProduct G H).presheaf.stalk q.1.1)
        (F.firstStagePushforwardGenericStalk G H V p q n) := by
  let r := (F.firstStageTargetGenericEquiv G H V p).symm q
  let : r.1.IsPrime := r.2.isPrime
  exact (LocalizedModule.equivTensorProduct r.1.primeCompl
      (F.firstStagePushforwardCoefficient G H V p n)).length_eq.symm.trans
    ((F.firstStagePushforwardTargetGenericIso G H V p q n).toLinearEquiv.length_eq.trans
      (TorComparison.length_restrictScalars_of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (genericStalkLocalizationIso (F.leftIntermediateImageProduct G H)
            (V.2.fromSpec p) q).inv).2 _))

variable [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsLocallyNoetherian (F.leftIntermediateImageProduct G H)]

/-- The original global generic pushforward length is finite, by finiteness of
the actual target coefficient and the proved literal generic comparison. -/
theorem firstStagePushforwardGenericStalk_length_ne_top
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    Module.length ((F.leftIntermediateImageProduct G H).presheaf.stalk q.1.1)
        (F.firstStagePushforwardGenericStalk G H V p q n) ≠ ⊤ := by
  let r := (F.firstStageTargetGenericEquiv G H V p).symm q
  let : r.1.IsPrime := r.2.isPrime
  have := F.firstStagePushforwardCoefficient_finite G H V p n
  rw [← F.firstStagePushforwardTargetGeneric_length G H V p q n]
  exact Module.fixedSupport_localized_length_ne_top
    (F.firstStagePushforwardCoefficient G H V p n) ⊥ bot_le r.1 r.2

/-- The accepted fixed-support generic weight is the finite integer length of
the original global generic finite-pushed Tor sheaf stalk, at the exact index. -/
theorem firstStagePushforwardGenericLength_eq_original
    (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    F.firstStagePushforwardGenericLength G H V p n
        ((F.firstStageTargetGenericEquiv G H V p).symm q) =
      integerLength (F.firstStagePushforwardGenericStalk G H V p q n)
        (F.firstStagePushforwardGenericStalk_length_ne_top G H V p q n) := by
  simp only [firstStagePushforwardGenericLength, Koszul.fixedSupportGenericLength, integerLength]
  rw [F.firstStagePushforwardTargetGeneric_length G H V p q n]

end Motivic.FiniteCorrespondenceGenerator
