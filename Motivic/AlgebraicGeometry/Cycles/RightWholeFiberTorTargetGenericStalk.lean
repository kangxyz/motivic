/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorTargetReplacement
public import Motivic.AlgebraicGeometry.Modules.RelativeFinitePushforwardGenericStalk

/-!
# Original right target generic stalks of the finite-pushed whole Tor coefficient

The local generic coefficient from fixed-zero-support replacement is attached
to the original finite pushforward sheaf at the exact global generic point.
That point belongs to the identical target affine open by specialization. The
actual constructed whole inverse-image Tor coefficient supplies relative
quasi-coherence, hence the genuine common-chart module comparison; global
quasi-coherence of its ambient equalizer is never assumed. Full generic stalk
lengths are preserved, with finiteness proved before integer conversion.
The genuine smooth Z-diagonal bound gives finite degree support before the
signed Euler comparison. Residue-degree sums and correspondence-cycle
comparisons remain separate. This is an uncompiled source-only continuation;
strict checks, full lint, transitive axiom gates and independent review are
not yet run for this module.
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

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- Actual descent proves quasi-coherence on the entire right inverse image;
no global quasi-coherence of the ambient equalizer is assumed. -/
local instance rightTargetGenericWholeRelativeQC (n : ℕ) :
    ((Scheme.Modules.restrictFunctor ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι).obj
      (F.rightFirstStageWholeAmbientCoefficient G H V n)).IsQuasicoherent :=
  wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n

/-- The common target chart module comes from the actual whole right coefficient
and the original finite image-product section map. -/
abbrev rightFirstStagePushforwardChartModule (n : ℕ) :=
  RelativeFinitePushforward.originalPushforwardChartModule
    (F.rightIntermediateImageMap G H) V (F.rightFirstStageWholeAmbientCoefficient G H V n)

/-- One genuine chart presentation gives each original pushed sheaf stalk
through its original section germ. -/
def rightFirstStagePushforwardChartStalkIso
    (x : F.rightIntermediateImageProduct G H) (hx : x ∈ V.1) (n : ℕ) :
    (ModuleStalk.functor x).obj
        ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
          (F.rightFirstStageWholeAmbientCoefficient G H V n)) ≅
      (ModuleCat.extendScalars
        ((F.rightIntermediateImageProduct G H).presheaf.germ V.1 x hx).hom).obj
        (F.rightFirstStagePushforwardChartModule G H V n) :=
  RelativeFinitePushforward.originalPushforwardChartStalkIso
    (F.rightIntermediateImageMap G H) V (F.rightFirstStageWholeAmbientCoefficient G H V n) x hx

/-- The original sheaf at the global generic: the finite pushforward of the
same whole Tor ambient equalizer used in the unchanged target coefficient. -/
abbrev rightFirstStagePushforwardGenericStalk
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :=
  (ModuleStalk.functor q.1.1).obj
    ((Scheme.Modules.pushforward (F.rightIntermediateImageMap G H)).obj
      (F.rightFirstStageWholeAmbientCoefficient G H V n))

omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i] in
/-- The exact original target generic and the original target point lie in
the same selected affine open; no second coefficient cover is introduced. -/
theorem rightFirstStagePushforwardGeneric_mem
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    q.1.1 ∈ V.1 :=
  q.2.mem_open V.1.isOpen (V.2.range_fromSpec.subset (Set.mem_range_self p))

omit [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i] in
/-- The actual right structure-stalk specialization and the two original
section germs form the common-chart scalar square. -/
theorem rightFirstStagePushforwardChart_germ_specializes
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    ((F.rightIntermediateImageProduct G H).presheaf.stalkSpecializes q.2).hom.comp
        ((F.rightIntermediateImageProduct G H).presheaf.germ V.1 (V.2.fromSpec p)
          (V.2.range_fromSpec.subset (Set.mem_range_self p))).hom =
      ((F.rightIntermediateImageProduct G H).presheaf.germ V.1 q.1.1
        (F.rightFirstStagePushforwardGeneric_mem G H V p q)).hom :=
  RelativeFinitePushforward.originalPushforwardChart_germ_specializes V
    (V.2.fromSpec p) q.1.1 (V.2.range_fromSpec.subset (Set.mem_range_self p)) q.2

/-- The original target coefficient specializes to the original generic stalk
through its actual structure-stalk map and the genuine common whole Tor chart. -/
def rightFirstStagePushforwardGenericSpecializationIso
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    (ModuleCat.extendScalars
      ((F.rightIntermediateImageProduct G H).presheaf.stalkSpecializes q.2).hom).obj
        (F.rightFirstStagePushforwardCoefficient G H V p n) ≅
      F.rightFirstStagePushforwardGenericStalk G H V p q n := by
  let φ := F.rightIntermediateImageMap G H
  let N := F.rightFirstStageWholeAmbientCoefficient G H V n
  have : ((Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).obj N).IsQuasicoherent :=
    wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n
  exact RelativeFinitePushforward.originalPushforwardStalkSpecializationIso φ V N
    (V.2.fromSpec p) q.1.1 (V.2.range_fromSpec.subset (Set.mem_range_self p)) q.2

/-- The right specialization comparison is the actual common-chart route:
its scalar-extension square commutes before generic localization. -/
theorem rightFirstStagePushforwardSpecialization_chart_square
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    let T := F.rightIntermediateImageProduct G H
    let x := V.2.fromSpec p
    let hx : x ∈ V.1 := V.2.range_fromSpec.subset (Set.mem_range_self p)
    let hy := F.rightFirstStagePushforwardGeneric_mem G H V p q
    let M := F.rightFirstStagePushforwardChartModule G H V n
    (F.rightFirstStagePushforwardGenericSpecializationIso G H V p q n).hom ≫
        (F.rightFirstStagePushforwardChartStalkIso G H V q.1.1 hy n).hom =
      (ModuleCat.extendScalars (T.presheaf.stalkSpecializes q.2).hom).map
          (F.rightFirstStagePushforwardChartStalkIso G H V x hx n).hom ≫
        (ModuleCat.extendScalarsComp (T.presheaf.germ V.1 x hx).hom
          (T.presheaf.stalkSpecializes q.2).hom).inv.app M ≫
        (eqToIso (congrArg (fun a => (ModuleCat.extendScalars a).obj M)
          (F.rightFirstStagePushforwardChart_germ_specializes G H V p q))).hom :=
  RelativeFinitePushforward.originalPushforwardStalkSpecializationIso_chart_square
    (F.rightIntermediateImageMap G H) V (F.rightFirstStageWholeAmbientCoefficient G H V n)
    (V.2.fromSpec p) q.1.1 (V.2.range_fromSpec.subset (Set.mem_range_self p)) q.2

/-- The literal local prime from the already proved exact target-generic index
localizes the original pushed coefficient to the original global generic stalk.
The scalar action is the inverse canonical generic-stalk localization map. -/
def rightFirstStagePushforwardTargetGenericIso
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    let r := (F.rightFirstStageTargetGenericEquiv G H V p).symm q
    let : r.1.IsPrime := r.2.isPrime
    ModuleCat.of (Localization.AtPrime r.1)
        (LocalizedModule r.1.primeCompl (F.rightFirstStagePushforwardCoefficient G H V p n)) ≅
      (ModuleCat.restrictScalars
        (genericStalkLocalizationIso (F.rightIntermediateImageProduct G H)
          (V.2.fromSpec p) q).inv.hom).obj
        (F.rightFirstStagePushforwardGenericStalk G H V p q n) := by
  let φ := F.rightIntermediateImageMap G H
  let N := F.rightFirstStageWholeAmbientCoefficient G H V n
  have : ((Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).obj N).IsQuasicoherent :=
    wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n
  exact RelativeFinitePushforward.originalPushforwardStalkGenericIso φ V N
    (V.2.fromSpec p) (V.2.range_fromSpec.subset (Set.mem_range_self p)) q

/-- The actual tensor-localized target multiplicity equals the length of the
original full generic pushforward stalk, including its nonreduced action. -/
theorem rightFirstStagePushforwardTargetGeneric_length
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    let r := (F.rightFirstStageTargetGenericEquiv G H V p).symm q
    let : r.1.IsPrime := r.2.isPrime
    Module.length (Localization.AtPrime r.1)
        (Localization.AtPrime r.1 ⊗[(F.rightIntermediateImageProduct G H).presheaf.stalk
          (V.2.fromSpec p)] (F.rightFirstStagePushforwardCoefficient G H V p n)) =
      Module.length ((F.rightIntermediateImageProduct G H).presheaf.stalk q.1.1)
        (F.rightFirstStagePushforwardGenericStalk G H V p q n) := by
  let r := (F.rightFirstStageTargetGenericEquiv G H V p).symm q
  let : r.1.IsPrime := r.2.isPrime
  exact (LocalizedModule.equivTensorProduct r.1.primeCompl
      (F.rightFirstStagePushforwardCoefficient G H V p n)).length_eq.symm.trans
    ((F.rightFirstStagePushforwardTargetGenericIso G H V p q n).toLinearEquiv.length_eq.trans
      (TorComparison.length_restrictScalars_of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (genericStalkLocalizationIso (F.rightIntermediateImageProduct G H)
            (V.2.fromSpec p) q).inv).2 _))

variable [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsLocallyNoetherian (F.rightIntermediateImageProduct G H)]

/-- The original global generic pushforward length is finite, by finiteness of
the actual target coefficient and the proved literal generic comparison. -/
theorem rightFirstStagePushforwardGenericStalk_length_ne_top
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    Module.length ((F.rightIntermediateImageProduct G H).presheaf.stalk q.1.1)
        (F.rightFirstStagePushforwardGenericStalk G H V p q n) ≠ ⊤ := by
  let r := (F.rightFirstStageTargetGenericEquiv G H V p).symm q
  let : r.1.IsPrime := r.2.isPrime
  have := F.rightFirstStagePushforwardCoefficient_finite G H V p n
  rw [← F.rightFirstStagePushforwardTargetGeneric_length G H V p q n]
  exact Module.fixedSupport_localized_length_ne_top
    (F.rightFirstStagePushforwardCoefficient G H V p n) ⊥ bot_le r.1 r.2

/-- The accepted fixed-support generic weight is the finite integer length of
the original global generic finite-pushed Tor sheaf stalk, at the exact index. -/
theorem rightFirstStagePushforwardGenericLength_eq_original
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})
    (n : ℕ) :
    F.rightFirstStagePushforwardGenericLength G H V p n
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      integerLength (F.rightFirstStagePushforwardGenericStalk G H V p q n)
        (F.rightFirstStagePushforwardGenericStalk_length_ne_top G H V p q n) := by
  simp only [rightFirstStagePushforwardGenericLength, Koszul.fixedSupportGenericLength,
    integerLength]
  rw [F.rightFirstStagePushforwardTargetGeneric_length G H V p q n]

variable [Flat f] [Flat g] [Smooth h] [Flat i]

omit [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsLocallyNoetherian (F.rightIntermediateImageProduct G H)] in
/-- One genuine smooth Z-diagonal bound kills every original generic pushed
stalk simultaneously, through the actual whole coefficient and specialization. -/
theorem rightFirstStagePushforwardGenericStalk_exists_bound :
    ∃ b : ℕ, ∀ n, b ≤ n →
      ∀ q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p},
        Subsingleton (F.rightFirstStagePushforwardGenericStalk G H V p q n) := by
  obtain ⟨b, hb⟩ := F.rightFirstStageWholeLocalized_exists_bound G H V p
  refine ⟨b, fun n hn q => ?_⟩
  have := hb n hn
  have := F.rightFirstStagePushforwardCoefficient_subsingleton G H V p n
  have hz := Functor.map_isZero
    (ModuleCat.extendScalars
      ((F.rightIntermediateImageProduct G H).presheaf.stalkSpecializes q.2).hom)
    (ModuleCat.isZero_of_subsingleton (F.rightFirstStagePushforwardCoefficient G H V p n))
  exact ModuleCat.subsingleton_of_isZero
    (hz.of_iso (F.rightFirstStagePushforwardGenericSpecializationIso G H V p q n).symm)

/-- Finite full stalk lengths and genuine module vanishing supply the required
finite-length support before forming the signed Euler sum. -/
theorem rightFirstStagePushforwardGenericStalk_finiteLengthSupport
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    FiniteLengthSupport (F.rightFirstStagePushforwardGenericStalk G H V p q) where
  finite_length n := F.rightFirstStagePushforwardGenericStalk_length_ne_top G H V p q n
  finite_support := by
    obtain ⟨b, hb⟩ := F.rightFirstStagePushforwardGenericStalk_exists_bound G H V p
    apply (Set.finite_Iio b).subset
    intro n hn
    exact Nat.lt_of_not_ge (fun h => by
      have := hb n h q
      exact hn Module.length_eq_zero)

/-- Signed Euler length of the actual original right generic pushed-sheaf
stalks, with actual finite-length support and the original outer Tor signs. -/
def rightFirstStagePushforwardGenericStalkSignedEuler
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) : ℤ :=
  signedLengthSum (F.rightFirstStagePushforwardGenericStalk G H V p q)
    (fun n : ℕ => (-1 : ℤ) ^ n)
    (F.rightFirstStagePushforwardGenericStalk_finiteLengthSupport G H V p q)

/-- The accepted right generic weight's signed outer sum is exactly the finite
signed Euler length of the literal original pushed sheaf at its actual generic. -/
theorem rightFirstStagePushforwardGenericEuler_eq_original
    (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p}) :
    F.rightFirstStagePushforwardGenericEuler G H V p
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      F.rightFirstStagePushforwardGenericStalkSignedEuler G H V p q := by
  unfold rightFirstStagePushforwardGenericEuler rightFirstStagePushforwardGenericStalkSignedEuler
    signedLengthSum
  apply finsum_congr
  intro n
  rw [F.rightFirstStagePushforwardGenericLength_eq_original G H V p q n]

end Motivic.FiniteCorrespondenceGenerator
