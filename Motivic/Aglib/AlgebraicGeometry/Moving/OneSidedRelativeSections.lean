/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedAffineSections
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedProductGeometry
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryTwistFrames
/-! # Actual one-sided sections from the original target boundary frames

The full divisor frame is constructed with its canonical infinity value. Only
its finite bad-boundary ideal frame and target twist frames remain as inputs.
The smaller parameter Y is never substituted for the original retained X.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.Scheme.Moving

/-- The original graph ideal frame and one full-target twist frame produce the
actual sections and finite-flat homotopy on the larger retained target. -/
theorem exists_oneSidedRelativeSections
    (R : Type u) [CommRing R] (K : Type u) [CommRing K]
    (ι : Type u) (n : ℕ) (eι : ι ≃ Fin (n + 1)) [Finite ι]
    {Y X V C Z D : Scheme.{u}} [IsAffine Y] [IsAffine X] [IsAffine V]
    [IsNoetherianRing Γ(Y, ⊤)]
    (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
    (j : Y ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ (f ≫ toSpec R ι))]
    (bY : Y ⟶ Spec (.of K))
    [IsLocallyNoetherian (pullback (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι))]
    (x : X ⟶ C) [IsOpenImmersion x]
    [SmoothOfRelativeDimension 1 (x ≫ (f ≫ toSpec R ι))]
    (v : V ⟶ X) [IsOpenImmersion v]
    (s : Z ⟶ Y) [IsClosedImmersion (s ≫ j)]
    (d : D ⟶ C) [IsClosedImmersion d]
    (hd : Disjoint (Set.range j) (Set.range d))
    (hX : ∀ c : C, c ∈ Set.range x ∨ c ∈ Set.range d)
    (hV : ∀ c : C, c ∈ Set.range (v ≫ x) ∨
      c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (e : SheafOfModules.unit
      (pullback (j ≫ (f ≫ toSpec R ι)) (s ≫ (j ≫ (f ≫ toSpec R ι)))).ringCatSheaf ≅
        Hom.idealModule (Hom.boundaryGraphTarget (j ≫ (f ≫ toSpec R ι)) s))
    (eFull : ∀ m : ℕ, (Modules.pullback (fullTargetBoundaryMap j s d ≫ f)).obj
      (twistingSheaf R ι (m : ℤ)) ≅ SheafOfModules.unit (D ⨿ Z).ringCatSheaf) :
    let π := f ≫ toSpec R ι
    let q := j ≫ π
    let I := Hom.relativeCompactificationGraphLine π j
    let z := Hom.fullBoundaryProductMap π j d s
    ∃ E : (Modules.pullback z).obj (dualLineBundle _ I).val ≅
        SheafOfModules.unit
          (pullback (pullback.snd q π) d ⨿ pullback q (s ≫ j ≫ π)).ringCatSheaf,
      ∃ T : LineBundle (pullback q π),
        Nonempty (OneSidedSections bY (pullback.fst q π) z coprod.inl
          (retainedProductInclusion q π x)
          (retainedProductInclusion q (x ≫ π) v ≫ retainedProductInclusion q π x)
          I T (Hom.idealInclusion (Hom.compactificationGraph π j)) E) := by
  let π := f ≫ toSpec R ι
  let q := j ≫ π
  let z := Hom.fullBoundaryProductMap π j d s
  let I := Hom.relativeCompactificationGraphLine π j
  have H : IsPullback s (𝟙 Z) (𝟙 Y) s := IsPullback.of_vert_isIso ⟨by simp⟩
  let E := Hom.relativeFullBoundaryFrame q π j (𝟙 Y) (by simp [q])
    s s (by simp) H e d hd
  have hz : IsClosedImmersion z := Hom.fullBoundaryProduct_isClosedImmersion π j d s hd
  have hA := retainedProduct_affine q π x
  have hB := retainedProduct_affine q (x ≫ π) v
  have hAj := retainedProduct_smooth q π x
  have hBj : SmoothOfRelativeDimension 1
      ((retainedProductInclusion q (x ≫ π) v ≫ retainedProductInclusion q π x) ≫
        pullback.fst q π) := by
    rw [Category.assoc, retainedProductInclusion_fst, retainedProductInclusion_fst]
    have : SmoothOfRelativeDimension 1 (v ≫ (x ≫ π)) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
    exact MorphismProperty.pullback_fst _ _ inferInstance
  have hδ : pullbackSectionMap (coprod.inl ≫ z)
      (canonicalDualHom _ I.val (Hom.idealInclusion (Hom.compactificationGraph π j))) ≫
        (compositeBoundaryFrame coprod.inl z (dualLineBundle _ I).val E).hom = 𝟙 _ := by
    apply (compositeBoundaryFrame_coordinate coprod.inl z
      (dualLineBundle _ I).val E
      (canonicalDualHom _ I.val (Hom.idealInclusion (Hom.compactificationGraph π j)))).trans
    exact Hom.relativeFullBoundaryCoordinate_inl q π j (𝟙 Y) (by simp [q])
      s s (by simp) H e d hd
  have hc : ∀ a : (pullback q π : Scheme),
      a ∈ Set.range (retainedProductInclusion q π x) ∨ a ∈ Set.range (coprod.inl ≫ z) := by
    simpa only [z, Hom.fullBoundaryProductMap, coprod.inl_desc] using
      product_missing_cover π j x d hX
  obtain ⟨T, hT⟩ := exists_oneSidedAffineSections R K ι n eι q bY f z coprod.inl
    (lambdaTwistFramesOfFullTargetFrame R ι f j s d eFull)
    (retainedProductInclusion q π x)
    (retainedProductInclusion q (x ≫ π) v ≫ retainedProductInclusion q π x)
    hc (product_good_cover π j x v s d hV) I
    (Hom.idealInclusion (Hom.compactificationGraph π j)) E hδ
  exact ⟨E, T, hT⟩

end AlgebraicGeometry.Scheme.Moving
