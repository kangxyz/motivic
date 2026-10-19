/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.MarkedProjectiveSquare
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter

/-! # Native coordinates on the same restricted normalization and marked square

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedMarkedSquare`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.RestrictedThickenedBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

/-- The actual restricted original open embeds over the native whole affine chart.
The compactification is the original pullback, not a second normalization. -/
@[reassoc]
theorem restricted_inclusion_toProjectiveLine :
    boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
        (inclusion R p) (inclusion_projection R p) ⊤ O ≫
      boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O =
    sourceNativeCoverMap R O p ≫ chart Γ(O.toScheme, ⊤) 0 := by
  have : IsOpenImmersion
      (ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R O.ι)
        (ULift.{u} (Fin 2))) := MorphismProperty.of_isPullback
    (ConstantCurve.affineSourceProjectiveSquare R (ULift.{u} (Fin 2)) O.ι).flip
    inferInstance
  apply (cancel_mono
    (ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R O.ι)
      (ULift.{u} (Fin 2)))).mp
  simp only [Category.assoc]
  change _ ≫ (ConstantCurve.affineSourceToProjectiveSpace R _ O.ι
      (toProjectiveLine R p) ≫ _) = _
  rw [ConstantCurve.affineSourceToProjectiveSpace_map]
  rw [← Category.assoc, boundaryBaseCoverInclusion_snd, Category.assoc,
    inclusion_toProjectiveLine, chart_map, ← Category.assoc,
    sourceNativeCoverMap_coordinate_assoc]
  simp only [Category.assoc, show (⟨0⟩ : ULift.{u} (Fin 2)) = 0 from by decide]

omit [IsAffine O.toScheme] in
/-- The retained original open has exactly its original range after coefficient
restriction, including when the normalization is disconnected. -/
theorem mem_range_restricted_inclusion_iff
    (x : boundaryBaseCompactification (projection R p) O) :
    x ∈ Set.range (boundaryBaseCoverInclusion (boundaryLineProjection R) p
      (projection R p) (inclusion R p) (inclusion_projection R p) ⊤ O) ↔
      pullback.snd O.ι (projection R p) x ∈ Set.range (inclusion R p) := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y.val, ?_⟩
    exact (congrArg (fun f => f y)
      (boundaryBaseCoverInclusion_snd (boundaryLineProjection R) p (projection R p)
        (inclusion R p) (inclusion_projection R p) ⊤ O)).symm
  · rintro ⟨y, hy⟩
    have hx : projection R p (pullback.snd O.ι (projection R p) x) ∈ O := by
      have he := congrArg (fun f => f x)
        (pullback.condition (f := O.ι) (g := projection R p))
      change O.ι (pullback.fst O.ι (projection R p) x) =
        projection R p (pullback.snd O.ι (projection R p) x) at he
      rw [← he]
      exact (pullback.fst O.ι (projection R p) x).property
    have hm : y ∈ boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O := by
      refine ⟨trivial, ?_⟩
      change (p ≫ boundaryLineProjection R) y ∈ O
      rw [← inclusion_projection R p]
      change projection R p (inclusion R p y) ∈ O
      rwa [hy]
    refine ⟨⟨y, hm⟩, ?_⟩
    apply (pullback.snd O.ι (projection R p)).isOpenEmbedding.injective
    have he := congrArg (fun f => f ⟨y, hm⟩)
      (boundaryBaseCoverInclusion_snd (boundaryLineProjection R) p (projection R p)
        (inclusion R p) (inclusion_projection R p) ⊤ O)
    exact he.trans hy

/-- The whole original marked scheme, restricted only on the coefficient base,
retains its actual Cartesian square with the restricted finite projective map. -/
theorem restricted_marked_projective_isPullback
    (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y) (hs : s ≫ p = z)
    (H : IsPullback s (𝟙 Z) p z) :
    IsPullback
      (boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
        (fun _ _ => trivial)) (𝟙 _)
      (boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
          (inclusion R p) (inclusion_projection R p) ⊤ O ≫
        boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O)
      (targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0) := by
  rw [restricted_inclusion_toProjectiveLine]
  have hchart : IsPullback (targetNativeMarked R O z) (𝟙 _)
      (chart Γ(O.toScheme, ⊤) 0)
      (targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa only [Category.id_comp] using
    (sourceNativeCoverLift_isPullback R O z p s hs H).paste_vert hchart

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
