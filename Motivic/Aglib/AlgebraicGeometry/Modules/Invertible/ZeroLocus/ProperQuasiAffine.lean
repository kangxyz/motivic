/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.ProperQuasiAffine
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Fibrewise
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Field
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts

/-!
# Proper quasi-affine zero loci of invertible modules
-/

@[expose] public noncomputable section

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

namespace Modules.Invertible

variable {X : Scheme.{u}} (K : Type u) [Field K]
variable (p : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
variable (L : LineBundle X)
variable (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)

include p in
/-- Local Artinianity of the actual zero scheme forces every unit-chart scalar
to be regular, hence forces the original line-bundle map to be monic. -/
theorem mono_of_zeroScheme_isLocallyArtinian [IsLocallyArtinian (Hom.zeroScheme φ)] :
    Mono φ := by
  apply mono_of_affine_chart_regular L φ
  intro W e V hV hVW
  let i := Hom.zeroInclusion φ
  let : IsClosedImmersion i := Hom.zeroInclusion_isClosedImmersion φ
  let : IsArtinianRing Γ(Hom.zeroScheme φ, i ⁻¹ᵁ V) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hV.preimage i⟩
  let : SmoothOfRelativeDimension 1 (hV.fromSpec ≫ p) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (hV.fromSpec ≫ p))
  exact Scheme.Hom.smoothField_artinian_principalKernel_isSMulRegular K
    (hV.fromSpec ≫ p) (i.app V) (i.app_surjective V hV) _
    (zeroInclusion_kernel_eq_span_chart L φ W e ⟨V, hV⟩ hVW)

/-- Finiteness of the whole zero scheme over the field proves monicity of the
original line-bundle map on a possibly disconnected smooth curve. -/
theorem mono_of_finite_zeroScheme [IsFinite (Hom.zeroInclusion φ ≫ p)] : Mono φ := by
  let : IsLocallyArtinian (Hom.zeroScheme φ) :=
    IsLocallyArtinian.of_locallyQuasiFinite (Hom.zeroInclusion φ ≫ p)
  exact mono_of_zeroScheme_isLocallyArtinian K p L φ

/-- Properness and quasi-affineness of the actual zero scheme suffice; no
monicity, componentwise nonvanishing, or smooth compactification is assumed. -/
theorem mono_of_proper_quasiAffine_zeroScheme
    [IsProper (Hom.zeroInclusion φ ≫ p)] [(Hom.zeroScheme φ).IsQuasiAffine] : Mono φ := by
  let : IsFinite (Hom.zeroInclusion φ ≫ p) :=
    Scheme.isFinite_of_isProper_of_isQuasiAffine (Hom.zeroInclusion φ ≫ p)
  exact mono_of_finite_zeroScheme K p L φ

/-- Finite actual zero schemes on a smooth relative curve are automatically
relative effective Cartier divisors: monicity and flatness are conclusions. -/
theorem mono_and_flat_of_finite_zeroScheme {C S : Scheme.{u}} (f : C ⟶ S)
    [SmoothOfRelativeDimension 1 f] (E : LineBundle C)
    (a : E.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsFinite (Hom.zeroInclusion a ≫ f)] :
    Mono a ∧ Flat (Hom.zeroInclusion a ≫ f) := by
  let := lineBundle_isLocallyFree C E
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  apply mono_and_flat_zeroInclusion_comp_of_geometricFibreRegular C S f E a
    inferInstance inferInstance
  intro F hF hclosed t
  let q := Limits.pullback.fst f t
  let r := Limits.pullback.snd f t
  let i := Hom.zeroInclusion a
  let : SmoothOfRelativeDimension 1 r := MorphismProperty.pullback_snd f t inferInstance
  let e := Hom.zeroSchemePullbackIso a q ≪≫ Limits.pullbackSymmetry q i ≪≫
    Limits.pullbackRightPullbackFstIso f t i
  have he : e.hom ≫ Limits.pullback.snd (i ≫ f) t =
      Hom.zeroInclusion (Hom.pullbackToUnit a q) ≫ r := by
    simp only [e, q, r, i, Iso.trans_hom, Category.assoc,
      Limits.pullbackRightPullbackFstIso_hom_snd,
      Limits.pullbackSymmetry_hom_comp_snd_assoc,
      Hom.zeroSchemePullbackIso_hom_fst_assoc]
  have : IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit a q) ≫ r) := by
    rw [← he]
    infer_instance
  exact mono_of_finite_zeroScheme F r (pullbackLineBundle q E) (Hom.pullbackToUnit a q)

/-- On a quasi-affine smooth relative curve over an affine base, properness of
 the original zero scheme already forces finiteness, monicity and flatness. -/
theorem finite_mono_flat_of_proper_zeroScheme {C S : Scheme.{u}} (f : C ⟶ S)
    [SmoothOfRelativeDimension 1 f] [C.IsQuasiAffine] [IsAffine S]
    (E : LineBundle C) (a : E.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsProper (Hom.zeroInclusion a ≫ f)] :
    IsFinite (Hom.zeroInclusion a ≫ f) ∧ Mono a ∧ Flat (Hom.zeroInclusion a ≫ f) := by
  let : IsClosedImmersion (Hom.zeroInclusion a) := Hom.zeroInclusion_isClosedImmersion a
  let : CompactSpace (Hom.zeroScheme a) :=
    QuasiCompact.compactSpace_of_compactSpace (Hom.zeroInclusion a)
  let : (Hom.zeroScheme a).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isImmersion (Hom.zeroInclusion a)
  let : IsFinite (Hom.zeroInclusion a ≫ f) :=
    Scheme.isFinite_of_isProper_of_isQuasiAffine (Hom.zeroInclusion a ≫ f)
  exact ⟨inferInstance, mono_and_flat_of_finite_zeroScheme f E a⟩

/-- A section on a proper compactification whose whole zero locus lies in the
quasi-affine smooth curve open yields an actual finite flat Cartier divisor
there. The compactification itself is not required to be smooth. -/
theorem finite_mono_flat_on_open_of_proper {C X S : Scheme.{u}} (p : X ⟶ S)
    [IsProper p] [IsAffine S] (j : C ⟶ X) [IsOpenImmersion j]
    [C.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ p)]
    (E : LineBundle X) (a : E.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : Set.range (Hom.zeroInclusion a) ⊆ Set.range j) :
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ p) ∧
      Mono (Hom.pullbackToUnit a j) ∧
      Flat (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ p) := by
  let := lineBundle_isLocallyFree X E
  let i := Hom.zeroInclusion a
  let : IsClosedImmersion i := Hom.zeroInclusion_isClosedImmersion a
  have hs : Surjective (Limits.pullback.snd j i) := by
    constructor
    intro x
    have hx : x ∈ Set.range (Limits.pullback.snd j i) := by
      rw [Scheme.Pullback.range_snd]
      exact h ⟨x, rfl⟩
    exact hx
  have : IsIso (Limits.pullback.snd j i) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hs⟩
  let e := Hom.zeroSchemePullbackIso a j
  have he : Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ p =
      e.hom ≫ Limits.pullback.snd j i ≫ i ≫ p := by
    rw [← Hom.zeroSchemePullbackIso_hom_fst a j]
    simp only [e, i, Category.assoc, Limits.pullback.condition_assoc]
  have : IsProper (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ (j ≫ p)) := by
    rw [he]
    infer_instance
  exact finite_mono_flat_of_proper_zeroScheme (j ≫ p) (pullbackLineBundle j E)
    (Hom.pullbackToUnit a j)

end Modules.Invertible

end AlgebraicGeometry.Scheme
