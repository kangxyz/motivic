/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyNisnevichOverlapShrink
public import Motivic.Cohomology.SheafCohomologyGenericOpen
public import Motivic.Aglib.AlgebraicGeometry.OpenBaseFiberShrinking

/-! # Actual open-base and open-source refinements of ordinary Nisnevich squares -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.SmoothSite
variable {S : Scheme.{u}} [IsNoetherian S] {X Y : SmoothSite S}

/-- Restriction uses the original scheme map, not a newly selected affine model. -/
def ordinaryOpenRestrict (f : Y ⟶ X) (C : X.left.Opens) :
    (opensFunctor Y).obj (f.left ⁻¹ᵁ C) ⟶ (opensFunctor X).obj C :=
  homMk (f.left ∣_ C) (by
    change (f.left ∣_ C) ≫ (C.ι ≫ X.hom) = (f.left ⁻¹ᵁ C).ι ≫ Y.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, MorphismProperty.Over.w])

@[reassoc]
theorem ordinaryOpenRestrict_inclusion (f : Y ⟶ X) (C : X.left.Opens) :
    ordinaryOpenRestrict f C ≫ openInclusion X C =
      openInclusion Y (f.left ⁻¹ᵁ C) ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact morphismRestrict_ι f.left C

instance (f : Y ⟶ X) [IsOpenImmersion f.left] (C : X.left.Opens) :
    IsOpenImmersion (ordinaryOpenRestrict f C).left :=
  inferInstanceAs (IsOpenImmersion (f.left ∣_ C))

/-- The original etale source, restricted both over the base open and inside T. -/
def ordinaryOpenBaseEtaleMap (p : Y ⟶ X) (C : X.left.Opens) (T : Y.left.Opens) :
    (opensFunctor Y).obj ((p.left ⁻¹ᵁ C) ⊓ T) ⟶ (opensFunctor X).obj C :=
  (opensFunctor Y).map (homOfLE inf_le_left) ≫ ordinaryOpenRestrict p C

@[reassoc]
theorem ordinaryOpenBaseEtaleMap_inclusion (p : Y ⟶ X) (C : X.left.Opens)
    (T : Y.left.Opens) :
    ordinaryOpenBaseEtaleMap p C T ≫ openInclusion X C =
      openInclusion Y ((p.left ⁻¹ᵁ C) ⊓ T) ≫ p := by
  apply MorphismProperty.Over.Hom.ext
  change (Y.left.homOfLE inf_le_left ≫ (p.left ∣_ C)) ≫ C.ι =
    ((p.left ⁻¹ᵁ C) ⊓ T).ι ≫ p.left
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

instance (p : Y ⟶ X) [Etale p.left] (C : X.left.Opens) (T : Y.left.Opens) :
    Etale (ordinaryOpenBaseEtaleMap p C T).left :=
  inferInstanceAs (Etale (Y.left.homOfLE inf_le_left ≫ (p.left ∣_ C)))

end Motivic.SmoothSite
namespace Motivic.SheafCohomology
variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : SmoothSite S}
  (j : U ⟶ X) [IsOpenImmersion j.left] (p : Y ⟶ X)
  (C : X.left.Opens) (T : Y.left.Opens)

/-- The new square is the actual categorical pullback of the two restricted original arrows. -/
abbrev ordinaryOpenBaseSquare : Square (SmoothSite S) :=
  ordinaryPullbackSquare (SmoothSite.ordinaryOpenRestrict j C)
    (SmoothSite.ordinaryOpenBaseEtaleMap p C T)

/-- Every component is the original restriction map, including the original overlap map. -/
def ordinaryOpenBaseSquareMap : ordinaryOpenBaseSquare j p C T ⟶ ordinaryPullbackSquare j p where
  τ₂ := SmoothSite.openInclusion U (j.left ⁻¹ᵁ C)
  τ₃ := SmoothSite.openInclusion Y ((p.left ⁻¹ᵁ C) ⊓ T)
  τ₄ := SmoothSite.openInclusion X C
  τ₁ := pullback.lift
    (pullback.fst _ _ ≫ SmoothSite.openInclusion U (j.left ⁻¹ᵁ C))
    (pullback.snd _ _ ≫ SmoothSite.openInclusion Y ((p.left ⁻¹ᵁ C) ⊓ T)) (by
      rw [Category.assoc, ← SmoothSite.ordinaryOpenRestrict_inclusion,
        ← Category.assoc, pullback.condition, Category.assoc,
        SmoothSite.ordinaryOpenBaseEtaleMap_inclusion, ← Category.assoc])
  comm₁₂ := (pullback.lift_fst _ _ _).symm
  comm₁₃ := (pullback.lift_snd _ _ _).symm
  comm₂₄ := SmoothSite.ordinaryOpenRestrict_inclusion j C
  comm₃₄ := SmoothSite.ordinaryOpenBaseEtaleMap_inclusion p C T

private theorem range_morphismRestrict {A B : Scheme.{u}} (f : A ⟶ B) (C : B.Opens) :
    Set.range (f ∣_ C) = C.ι ⁻¹' Set.range f := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, (morphismRestrict_base_coe f C a).symm⟩
  · rintro ⟨a, ha⟩
    let a' : (f ⁻¹ᵁ C).toScheme := ⟨a, by
      change f a ∈ C
      rw [ha]
      exact x.property⟩
    refine ⟨a', ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe f C a').trans ha

/-- The full original complement restricts to the full complement of the new open leg. -/
theorem ordinaryOpenBaseSquare_complement {Z : Scheme.{u}} (z : Z ⟶ X.left)
    (hcomp : Set.range z = (Set.range j.left)ᶜ) :
    Set.range (z ∣_ C) = (Set.range (ordinaryOpenBaseSquare j p C T).f₂₄.left)ᶜ := by
  change Set.range (z ∣_ C) = (Set.range (j.left ∣_ C))ᶜ
  rw [range_morphismRestrict, range_morphismRestrict, hcomp, Set.preimage_compl]

/-- Keeping every original specified fiber point over C retains the complete
scheme-theoretic complement isomorphism, including all nilpotents. -/
theorem ordinaryOpenBaseSquare_iso_complement {Z : Scheme.{u}} (z : Z ⟶ X.left)
    [IsIso (pullback.snd p.left z)]
    (hretain : ∀ y : Y.left, p.left y ∈ Set.range z → p.left y ∈ C → y ∈ T) :
    IsIso (pullback.snd (ordinaryOpenBaseSquare j p C T).f₃₄.left (z ∣_ C)) := by
  let A := (p.left ⁻¹ᵁ C) ⊓ T
  let s := inv (pullback.snd p.left z) ≫ pullback.fst p.left z
  have hs : s ≫ p.left = z := by
    simp only [s, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  apply Scheme.Hom.isIso_pullback_snd_of_open_source_of_mono_base p.left z
    (SmoothSite.ordinaryOpenBaseEtaleMap p C T).left (z ∣_ C)
    A.ι C.ι (z ⁻¹ᵁ C).ι
    (congrArg (fun f => f.left) (SmoothSite.ordinaryOpenBaseEtaleMap_inclusion p C T))
    (morphismRestrict_ι z C)
  rintro y ⟨a, rfl⟩
  change s a.val ∈ Set.range A.ι
  have he : p.left (s a.val) = z a.val := congrArg (fun f => f a.val) hs
  refine ⟨⟨s a.val, ?_, hretain _ ⟨a.val, he.symm⟩ ?_⟩, rfl⟩
  all_goals
    change p.left (s a.val) ∈ C
    rw [he]
    exact a.property

end Motivic.SheafCohomology
