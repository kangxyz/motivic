/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.OneSidedSectionProducer
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedRelativeSections
/-! # Actual moving on one original split relative curve

The parameter is a smaller open in X, never a replacement for X. The canonical
original graph and the constructed relative Serre pencil give both endpoints.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Moving Scheme.RelativeCurvePencil
universe u
namespace Motivic.OneSidedMovingEndpoints

/-- Original geometric frames, not sections or correspondences, are the only
splitting data. The compactification itself need not be smooth. -/
theorem exists_moving_endpoints_of_relative_frames
    {k : Type u} [Field k] (R : Type u) [CommRing R]
    (ι : Type u) (n : ℕ) (eι : ι ≃ Fin (n + 1)) [Finite ι]
    {S X V : SmoothSite (Spec (.of k))}
    [IsAffine S.left] [IsAffine X.left] [IsAffine V.left]
    [IsNoetherianRing Γ(S.left, ⊤)] {C Z D : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
    (j : S.left ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ (f ≫ toSpec R ι))]
    [IsLocallyNoetherian (pullback (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι))]
    (x : X.left ⟶ C) [IsOpenImmersion x]
    [SmoothOfRelativeDimension 1 (x ≫ (f ≫ toSpec R ι))]
    (v : V ⟶ X) [IsOpenImmersion v.left]
    (φ : S ⟶ X) (hφ : φ.left ≫ x = j)
    (t : Spec (.of R) ⟶ Spec (.of k))
    (hS : (j ≫ (f ≫ toSpec R ι)) ≫ t = S.hom)
    (hXbase : (x ≫ (f ≫ toSpec R ι)) ≫ t = X.hom)
    (s : Z ⟶ S.left) [IsClosedImmersion (s ≫ j)]
    (d : D ⟶ C) [IsClosedImmersion d]
    (hd : Disjoint (Set.range j) (Set.range d))
    (hX : ∀ c : C, c ∈ Set.range x ∨ c ∈ Set.range d)
    (hV : ∀ c : C, c ∈ Set.range (v.left ≫ x) ∨
      c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (e : SheafOfModules.unit
      (pullback (j ≫ (f ≫ toSpec R ι)) (s ≫ (j ≫ (f ≫ toSpec R ι)))).ringCatSheaf ≅
        Scheme.Hom.idealModule
          (Scheme.Hom.boundaryGraphTarget (j ≫ (f ≫ toSpec R ι)) s))
    (eFull : ∀ m : ℕ, (Scheme.Modules.pullback (fullTargetBoundaryMap j s d ≫ f)).obj
      (twistingSheaf R ι (m : ℤ)) ≅ SheafOfModules.unit (D ⨿ Z).ringCatSheaf) :
    HasMovingEndpoints φ v := by
  let π := f ≫ toSpec R ι
  let q := j ≫ π
  let z := Scheme.Hom.fullBoundaryProductMap π j d s
  let jr := retainedProductInclusion q π x
  let wr := retainedProductInclusion q (x ≫ π) v.left
  let γ := parameterGraph π j x φ.left hφ
  have : IsClosedImmersion (Scheme.Hom.compactificationGraph π j) := by
    dsimp [Scheme.Hom.compactificationGraph]
    infer_instance
  have hA := retainedProduct_affine q π x
  have hB := retainedProduct_affine q (x ≫ π) v.left
  have hj := retainedProduct_smooth q π x
  have hp : Smooth (pullback.fst q (x ≫ π)) := by
    have : Smooth (x ≫ π) := SmoothOfRelativeDimension.smooth 1 _
    infer_instance
  have htotal : Smooth ((jr ≫ pullback.fst q π) ≫ S.hom) := by
    change Smooth ((retainedProductInclusion q π x ≫ pullback.fst q π) ≫ S.hom)
    rw [retainedProductInclusion_fst]
    infer_instance
  have hcover : ∀ a : (pullback q π : Scheme),
      a ∈ Set.range jr ∨ a ∈ Set.range z := by
    intro a
    rcases product_missing_cover π j x d hX a with ha | ⟨b, hb⟩
    · exact Or.inl ha
    · exact Or.inr ⟨(coprod.inl : _ ⟶ _ ⨿ pullback q (s ≫ j ≫ π)) b, by
        change ((coprod.inl : pullback (pullback.snd q π) d ⟶
          pullback (pullback.snd q π) d ⨿ pullback q (s ≫ j ≫ π)) ≫ z) b = a
        simpa only [z, Scheme.Hom.fullBoundaryProductMap, coprod.inl_desc] using hb⟩
  obtain ⟨E, T, ⟨sections⟩⟩ := exists_oneSidedRelativeSections R k ι n eι f j S.hom
    x v.left s d hd hX hV e eFull
  have hb : (jr ≫ pullback.fst q π) ≫ S.hom = pullback.snd q (x ≫ π) ≫ X.hom := by
    rw [hS.symm, ← Category.assoc, retainedProductInclusion_fst, Category.assoc,
      pullback.condition_assoc, hXbase]
  exact exists_moving_endpoints_of_sections (S := S) (X := X) (V := V)
    (pullback.fst q π) z coprod.inl jr wr hcover
    (Scheme.Hom.compactificationGraph π j) γ (parameterGraph_inclusion π j x φ.left hφ)
    (by
      simp only [jr, retainedProductInclusion_fst]
      exact parameterGraph_fst π j x φ.left hφ)
    (Scheme.Hom.relativeCompactificationGraphLine π j).property T E sections
    (pullback.snd q (x ≫ π)) (pullback.snd q (v.left ≫ (x ≫ π))) v
    (retainedProductInclusion_snd q (x ≫ π) v.left) φ
    (parameterGraph_snd π j x φ.left hφ) hb

end Motivic.OneSidedMovingEndpoints
