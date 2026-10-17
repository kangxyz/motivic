/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.RelativeCurveRefinedLifting
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FixedTargetPencilGeometry
/-! # Original-section lifting from one fixed target presentation

The source compactification and projective map are the actual finite normalization
and its composite with the target map. The retained target is the entire original overlap.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Hom Scheme.EtaleCompactification
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) [Finite ι] (X C : Scheme.{u})
  [IsAffine X] [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsIntegral C] [IsLocallyNoetherian C]
  [∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)]
  {Y A Z D : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ X) [IsOpenImmersion a]
  (j : X ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  (hq : j ≫ (f ≫ toSpec R ι) = q)
  (U : X.Opens) (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme] [IsAffine (boundaryBaseSourceOpen q U V).toScheme]

abbrev fixedTargetPencilAlpha := boundaryBasePencilAlpha k R ι t q p a
  (fixedTargetSourceProjectiveMap R ι X C p j f) (inclusion C (p ≫ j))
  (fixedTargetSource_over R ι X C p j f q hq) U V

abbrev fixedTargetPencilBeta := boundaryBasePencilBeta k R ι t q p a
  (fixedTargetSourceProjectiveMap R ι X C p j f) (inclusion C (p ≫ j))
  (fixedTargetSource_over R ι X C p j f q hq) U V

abbrev fixedTargetPencilGraph :=
  let : SmoothOfRelativeDimension 1 ((pullback.fst p a ≫ inclusion C (p ≫ j)) ≫
      (fixedTargetSourceProjectiveMap R ι X C p j f ≫ toSpec R ι)) :=
    fixedTargetRetained_smooth R ι X C p j f q hq a
  boundaryBasePencilGraph k R ι t q p a
    (fixedTargetSourceProjectiveMap R ι X C p j f) (inclusion C (p ≫ j))
    (fixedTargetSource_over R ι X C p j f q hq) U V
    (pullback.fst p a ≫ inclusion C (p ≫ j)) (𝟙 _) (Category.id_comp _)


/-- CohTh 4.12(2) lifting from one genuine target presentation. The source compactification,
its finite projective map, its full finite boundary, the frames and the sections are all
constructed. The retained target is the original punctured overlap, not the parameter open. -/
theorem exists_fixedTarget_normalized_lifting (m : ℕ) (eι : ι ≃ Fin (m + 1))
    (z : Z ⟶ X) [IsFinite (z ≫ q)] (s : Z ⟶ Y) [IsClosedImmersion s]
    (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
    (ha : Disjoint (Set.range a) (Set.range z))
    (hcover : ∀ x : X, x ∈ Set.range a ∨ x ∈ Set.range z)
    (d : D ⟶ C) [IsFinite (d ≫ (f ≫ toSpec R ι))]
    (hbad : (j ''ᵁ finiteLocusOpen X p : Set C)ᶜ ⊆ Set.range d)
    (x : X) (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      q x ∈ V ∧ (∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U) ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen q U V),
        let : IsAffine (boundaryBaseSourceOpen q U V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (fixedTargetPencilGraph k R ι X C t q p a j f hq U V)
          (fixedTargetPencilBeta k R ι X C t q p a j f hq U V)
          (fixedTargetPencilAlpha k R ι X C t q p a j f hq U V) := by
  let fS := fixedTargetSourceProjectiveMap R ι X C p j f
  let jS := inclusion C (p ≫ j)
  let dS := infinityInclusion C (p ≫ j)
  let vS := pullback.fst p a ≫ jS
  have : SmoothOfRelativeDimension 1 (vS ≫ (fS ≫ toSpec R ι)) :=
    fixedTargetRetained_smooth R ι X C p j f q hq a
  have he : s ≫ p ≫ j ≫ (f ≫ toSpec R ι) = z ≫ q := by
    rw [hq, ← Category.assoc, hs]
  have : IsFinite (s ≫ p ≫ j ≫ (f ≫ toSpec R ι)) := by
    rw [he]
    infer_instance
  have : IsProper (s ≫ (p ≫ j) ≫ (f ≫ toSpec R ι)) := by
    simpa only [Category.assoc] using
      (inferInstance : IsProper (s ≫ p ≫ j ≫ (f ≫ toSpec R ι)))
  have : IsClosedImmersion (s ≫ jS) :=
    originalBoundary_isClosedImmersion C (p ≫ j) s (f ≫ toSpec R ι)
  have hf := finite_full_source_boundary_over_fixed_target X C p j
    (f ≫ toSpec R ι) d hbad s
  have : IsFinite ((coprod.desc dS (s ≫ jS) ≫ fS) ≫ toSpec R ι) := by
    simpa only [fS, dS, jS, boundaryInclusion, fixedTargetSourceProjectiveMap,
      Category.assoc] using hf
  exact exists_refined_relativeCurve_lifting k R ι m eι t q p a fS jS
    (fixedTargetSource_over R ι X C p j f q hq) z s hs H ha dS
    (source_disjoint_infinity X C p j) vS
    (fixedTarget_retained_cover X C p j a z s H hcover)
    (𝟙 _) (Category.id_comp _) x P hP
end AlgebraicGeometry.Scheme.RelativeCurvePencil
