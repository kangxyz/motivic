/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FiniteProjectiveBaseRestriction
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Normal compact curves and their unchanged retained opens after affine base restriction -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {N S : Scheme.{u}} (q : N ⟶ S) (T : S.Opens)

/-- The retained open uses the original source and the original base restriction. -/
abbrev retainedBaseOpen (V : N.Opens) := (V.ι ≫ q) ⁻¹ᵁ T

/-- Its inclusion into the actual restricted compactification. -/
def retainedBaseInclusion (V : N.Opens) :
    (retainedBaseOpen q T V).toScheme ⟶ (q ⁻¹ᵁ T).toScheme :=
  V.ι ∣_ q ⁻¹ᵁ T

instance (V : N.Opens) : IsOpenImmersion (retainedBaseInclusion q T V) := by
  dsimp [retainedBaseInclusion]
  infer_instance

@[reassoc]
theorem retainedBaseInclusion_ι (V : N.Opens) :
    retainedBaseInclusion q T V ≫ (q ⁻¹ᵁ T).ι =
      (retainedBaseOpen q T V).ι ≫ V.ι := morphismRestrict_ι _ _

@[reassoc]
theorem retainedBaseInclusion_projection (V : N.Opens) :
    retainedBaseInclusion q T V ≫ q ∣_ T = (V.ι ≫ q) ∣_ T :=
  (morphismRestrict_comp V.ι q T).symm

/-- Normality is transported through the actual stalk isomorphisms of the open immersion. -/
theorem normalStalks_baseRestriction (hN : N.NormalStalks) :
    (q ⁻¹ᵁ T).toScheme.NormalStalks := by
  intro x
  let e := (asIso ((q ⁻¹ᵁ T).ι.stalkMap x)).commRingCatIsoToRingEquiv
  let := (hN ((q ⁻¹ᵁ T).ι x)).1
  let := (hN ((q ⁻¹ᵁ T).ι x)).2
  have : IsDomain ((q ⁻¹ᵁ T).toScheme.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩

/-- A retained point supplies nonemptiness; no surjectivity of the compact curve is assumed. -/
theorem integral_baseRestriction [IsIntegral N] (x : N) (hx : q x ∈ T) :
    IsIntegral (q ⁻¹ᵁ T).toScheme := by
  let : Nonempty (q ⁻¹ᵁ T).toScheme := ⟨⟨x, hx⟩⟩
  exact isIntegral_of_isOpenImmersion (q ⁻¹ᵁ T).ι

/-- All structural properties concern the actual open restriction of the fixed curve. -/
theorem baseRestriction_properties [IsIntegral N] [IsLocallyNoetherian N]
    (hN : N.NormalStalks) [IsProper q] (x : N) (hx : q x ∈ T) :
    IsIntegral (q ⁻¹ᵁ T).toScheme ∧ IsLocallyNoetherian (q ⁻¹ᵁ T).toScheme ∧
      (q ⁻¹ᵁ T).toScheme.NormalStalks ∧ IsProper (q ∣_ T) :=
  ⟨integral_baseRestriction q T x hx, inferInstance,
    normalStalks_baseRestriction q T hN, inferInstance⟩

variable [IsAffine T.toScheme]

/-- The original retained smooth map over the actual ring of the base open. -/
theorem retainedBase_smooth (V : N.Opens) [SmoothOfRelativeDimension 1 (V.ι ≫ q)] :
    SmoothOfRelativeDimension 1
      (retainedBaseInclusion q T V ≫ q ∣_ T ≫ T.toScheme.isoSpec.hom) := by
  rw [← Category.assoc, retainedBaseInclusion_projection]
  have : SmoothOfRelativeDimension 1 ((V.ι ≫ q) ∣_ T) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict (V.ι ≫ q) T).flip inferInstance
  exact smoothOfRelativeDimension_comp (n := 1) (m := 0) _ _

/-- Affineness is retained on the literal preimage, not on a replacement localization model. -/
theorem retainedBase_affine [IsAffine S] (V : N.Opens) [IsAffine V.toScheme] :
    IsAffine (retainedBaseOpen q T V).toScheme :=
  IsAffineOpen.preimage (show IsAffineOpen T from (inferInstance : IsAffine T.toScheme)) (V.ι ≫ q)

omit [IsAffine T.toScheme] in
/-- The original retained point remains literally the same point in both open restrictions. -/
theorem retainedBase_point (V : N.Opens) (x : N) (hxV : x ∈ V) (hxT : q x ∈ T) :
    retainedBaseInclusion q T V ⟨⟨x, hxV⟩, hxT⟩ = ⟨x, hxT⟩ := by
  apply Subtype.ext
  exact congrArg (fun f => f ⟨⟨x, hxV⟩, hxT⟩) (retainedBaseInclusion_ι q T V)

/-- Packaging over the actual affine coordinate ring. The finite projective map and
all identities come from the fixed map, while integrality uses the retained point. -/
theorem finiteProjectiveBaseRestriction_properties
    (R : Type u) [CommRing R] (ι : Type u) [Finite ι]
    {N : Scheme.{u}} [IsIntegral N] [IsLocallyNoetherian N]
    (π : N ⟶ ProjectiveSpace R ι) [IsFinite π]
    (T : (Spec (.of R)).Opens) [IsAffine T.toScheme]
    (hN : N.NormalStalks) (x : N) (hx : (π ≫ ProjectiveSpace.toSpec R ι) x ∈ T) :
    IsIntegral (((π ≫ ProjectiveSpace.toSpec R ι) ⁻¹ᵁ T).toScheme) ∧
    IsLocallyNoetherian (((π ≫ ProjectiveSpace.toSpec R ι) ⁻¹ᵁ T).toScheme) ∧
    (((π ≫ ProjectiveSpace.toSpec R ι) ⁻¹ᵁ T).toScheme).NormalStalks ∧
    IsFinite (finiteProjectiveBaseRestriction R ι π T) ∧
    IsProper (finiteProjectiveBaseRestriction R ι π T ≫
      ProjectiveSpace.toSpec Γ(T.toScheme, ⊤) ι) := by
  exact ⟨integral_baseRestriction _ T x hx, inferInstance,
    normalStalks_baseRestriction _ T hN, inferInstance, inferInstance⟩

/-- The retained smooth map is the restriction of the same finite projective coordinate. -/
theorem finiteProjectiveBaseRestriction_retained_smooth
    (R : Type u) [CommRing R] (ι : Type u) {N : Scheme.{u}}
    (π : N ⟶ ProjectiveSpace R ι) (T : (Spec (.of R)).Opens) [IsAffine T.toScheme]
    (V : N.Opens) [SmoothOfRelativeDimension 1 (V.ι ≫ (π ≫ ProjectiveSpace.toSpec R ι))] :
    SmoothOfRelativeDimension 1
      (retainedBaseInclusion (π ≫ ProjectiveSpace.toSpec R ι) T V ≫
        finiteProjectiveBaseRestriction R ι π T ≫ ProjectiveSpace.toSpec Γ(T.toScheme, ⊤) ι) := by
  rw [finiteProjectiveBaseRestriction_toSpec]
  exact retainedBase_smooth _ T V

end AlgebraicGeometry.Scheme.RelativeCurve
