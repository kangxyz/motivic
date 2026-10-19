/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Diagrams.OriginalAffineRefinement
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.WholeComplement
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter
/-! # The original full complement through the two native coordinate restrictions

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`RelativeAffineLine.OriginalSectionChoice`, `Nisnevich.NativeCoefficientCover`,
`Nisnevich.NativeCoefficientFieldLifting`, `NativeRefinement.NativeOriginalRefinedSource`,
`Pencils.NativeOriginalRestrictionActions`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme

/-- Reindexing the ambient scheme preserves the exact full complement. -/
theorem range_comp_iso_complement {X X' A Z : Scheme.{u}}
    (e : X ≅ X') (a : A ⟶ X) (z : Z ⟶ X)
    (hz : Set.range z = (Set.range a)ᶜ) :
    Set.range (z ≫ e.hom) = (Set.range (a ≫ e.hom))ᶜ := by
  have mem (Y : Scheme.{u}) (g : Y ⟶ X) (x : X') :
      x ∈ Set.range (g ≫ e.hom) ↔ e.inv x ∈ Set.range g := by
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      change g y = (g ≫ e.hom ≫ e.inv) y
      simp
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change e.hom (g y) = x
      rw [hy]
      change (e.inv ≫ e.hom) x = x
      simp
  ext x
  rw [Set.mem_compl_iff, mem, mem, hz]
  rfl

/-- Restricting the whole target preserves the original full complement. -/
theorem range_morphismRestrict_complement {X A Z : Scheme.{u}}
    (a : A ⟶ X) (z : Z ⟶ X) (V : X.Opens)
    (hz : Set.range z = (Set.range a)ᶜ) :
    Set.range (z ∣_ V) = (Set.range (a ∣_ V))ᶜ := by
  have mem (Y : Scheme.{u}) (g : Y ⟶ X) (x : V.toScheme) :
      x ∈ Set.range (g ∣_ V) ↔ V.ι x ∈ Set.range g := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, (congrArg (fun f => f y) (morphismRestrict_ι g V)).symm⟩
    · rintro ⟨y, hy⟩
      have hym : y ∈ g ⁻¹ᵁ V := by change g y ∈ V; rw [hy]; exact x.property
      refine ⟨⟨y, hym⟩, ?_⟩
      apply V.ι.isOpenEmbedding.injective
      exact (congrArg (fun f => f ⟨y, hym⟩) (morphismRestrict_ι g V)).trans hy
  ext x
  rw [Set.mem_compl_iff, mem, mem, hz]
  rfl

variable (R : Type u) [CommRing R] {T A Z : Scheme.{u}}
  (e : T ≅ Spec (.of (Polynomial R))) (q : T ⟶ Spec (.of R))
  (hq : e.hom ≫ boundaryLineProjection R = q)
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (a : A ⟶ T) (z : Z ⟶ T)

/-- The original puncture is restricted only over the same coefficient open. -/
def originalAffineRefinedNativePuncture : ((a ≫ q) ⁻¹ᵁ O).toScheme ⟶
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  (a ∣_ (q ⁻¹ᵁ O)) ≫ (originalAffineRefinedTargetIso R e q hq O).hom

instance originalAffineRefinedNativePuncture_open [IsOpenImmersion a] :
    IsOpenImmersion (originalAffineRefinedNativePuncture R e q hq O a) := by
  unfold originalAffineRefinedNativePuncture
  infer_instance

/-- The first native reindexing keeps the exact original complement. -/
theorem originalAffineRefinedNative_complement
    (hz : Set.range z = (Set.range a)ᶜ) :
    Set.range (originalAffineRefinedNativeMarked R e q hq O z) =
      (Set.range (originalAffineRefinedNativePuncture R e q hq O a))ᶜ :=
  range_comp_iso_complement (originalAffineRefinedTargetIso R e q hq O)
    (a ∣_ (q ⁻¹ᵁ O)) (z ∣_ (q ⁻¹ᵁ O))
    (range_morphismRestrict_complement a z (q ⁻¹ᵁ O) hz)

include hq in
/-- Affineness of the original puncture survives this same restriction. -/
theorem originalAffineRefinedNativePuncture_affine [IsAffine A] :
    IsAffine ((a ≫ q) ⁻¹ᵁ O).toScheme := by
  rw [← hq]
  exact affineRefinedOpen_affine R e O a

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  {A Z : Scheme.{u}} (a : A ⟶ Spec (.of (Polynomial R)))
  (z : Z ⟶ Spec (.of (Polynomial R)))

instance sourceNativeCoverMap_etale [Etale a] : Etale (sourceNativeCoverMap R O a) := by
  unfold sourceNativeCoverMap boundaryBaseCoverMap
  infer_instance

instance targetNativeMarked_closed [IsClosedImmersion z] :
    IsClosedImmersion (targetNativeMarked R O z) := by
  unfold targetNativeMarked
  infer_instance

instance targetNativeMarked_finite [IsFinite (z ≫ boundaryLineProjection R)] :
    IsFinite (targetNativeMarked R O z ≫ boundaryLineProjection Γ(O.toScheme, ⊤)) := by
  have he : targetNativeMarked R O z ≫ boundaryLineProjection Γ(O.toScheme, ⊤) =
      ((z ≫ boundaryLineProjection R) ∣_ O) ≫ O.toScheme.isoSpec.hom := by
    simp only [targetNativeMarked, Category.assoc, targetAffineOpenIso_inv_projection]
    rw [← Category.assoc, ← morphismRestrict_comp]
  rw [he]
  infer_instance

/-- The second native reindexing also keeps the exact original complement. -/
theorem sourceNativeCoverMap_marked_complement
    (hz : Set.range z = (Set.range a)ᶜ) :
    Set.range (targetNativeMarked R O z) = (Set.range (sourceNativeCoverMap R O a))ᶜ := by
  rw [← boundaryBaseLift_sourceNativeParameterIso R O z]
  exact Scheme.range_comp_iso_complement (sourceNativeParameterIso R O)
    (boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ O)
    (boundaryBaseWholeLift (boundaryLineProjection R) z O)
    (boundaryBaseWholeLift_range (boundaryLineProjection R) a z O hz)

end AlgebraicGeometry.RelativeProjectiveLine
