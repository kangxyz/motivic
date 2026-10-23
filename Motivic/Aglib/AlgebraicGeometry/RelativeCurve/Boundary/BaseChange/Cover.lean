/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CanonicalFrame
/-! # The original étale cover on the simultaneous source and base neighborhood -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (U : X.Opens) (V : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U)

/-- The inverse image in the cover of the source open over `V`. -/
abbrev boundaryBaseCoverOpen : Y.Opens := p ⁻¹ᵁ boundaryBaseSourceOpen q U V
/-- The restriction of the cover map to the source open over `V`. -/
abbrev boundaryBaseCoverMap := p ∣_ boundaryBaseSourceOpen q U V

/-- The lift is supplied by the actual source pullback, not a boundary section premise. -/
def boundaryBaseCoverLift : (boundaryBaseClosedOpen q z V).toScheme ⟶
    (boundaryBaseCoverOpen q p U V).toScheme :=
  (isPullback_morphismRestrict p (boundaryBaseSourceOpen q U V)).flip.lift
    ((boundaryBaseClosedOpen q z V).ι ≫ s) (boundaryBaseLift q z U V h)
    (by rw [Category.assoc, hs, boundaryBaseLift_ι])

@[reassoc (attr := simp)]
theorem boundaryBaseCoverLift_ι :
    boundaryBaseCoverLift q p z s hs U V h ≫ (boundaryBaseCoverOpen q p U V).ι =
      (boundaryBaseClosedOpen q z V).ι ≫ s :=
  (isPullback_morphismRestrict p (boundaryBaseSourceOpen q U V)).flip.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem boundaryBaseCoverLift_map :
    boundaryBaseCoverLift q p z s hs U V h ≫ boundaryBaseCoverMap q p U V =
      boundaryBaseLift q z U V h :=
  (isPullback_morphismRestrict p (boundaryBaseSourceOpen q U V)).flip.lift_snd _ _ _

/-- The original full-boundary isomorphism remains literal after this simultaneous shrink. -/
theorem boundaryBaseCoverLift_isPullback (H : IsPullback s (𝟙 Z) p z) :
    IsPullback (boundaryBaseCoverLift q p z s hs U V h)
      (𝟙 (boundaryBaseClosedOpen q z V).toScheme)
      (boundaryBaseCoverMap q p U V) (boundaryBaseLift q z U V h) where
  w := by simp
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t => by
    have hc : (t.fst ≫ (boundaryBaseCoverOpen q p U V).ι) ≫ p =
        (t.snd ≫ (boundaryBaseClosedOpen q z V).ι) ≫ z := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, t.condition,
        Category.assoc, boundaryBaseLift_ι]
      simp only [Category.assoc]
    have he := H.lift_fst (t.fst ≫ (boundaryBaseCoverOpen q p U V).ι)
      (t.snd ≫ (boundaryBaseClosedOpen q z V).ι) hc
    have hi := H.lift_snd (t.fst ≫ (boundaryBaseCoverOpen q p U V).ι)
      (t.snd ≫ (boundaryBaseClosedOpen q z V).ι) hc
    simp only [Category.comp_id] at hi
    rw [hi] at he
    refine ⟨t.snd, ?_, by simp, ?_⟩
    · apply (cancel_mono (boundaryBaseCoverOpen q p U V).ι).mp
      change t.snd ≫ boundaryBaseCoverLift q p z s hs U V h ≫
        (boundaryBaseCoverOpen q p U V).ι = t.fst ≫ (boundaryBaseCoverOpen q p U V).ι
      simpa only [Category.assoc, boundaryBaseCoverLift_ι] using he
    · intro a _ ha
      simpa using ha)⟩

theorem boundaryBaseCoverMap_etale [Etale p] : Etale (boundaryBaseCoverMap q p U V) := by
  dsimp [boundaryBaseCoverMap]
  infer_instance

theorem boundaryBaseCoverOpen_affine [IsAffine X] [IsAffine Y]
    (hW : IsAffineOpen (boundaryBaseSourceOpen q U V)) :
    IsAffineOpen (boundaryBaseCoverOpen q p U V) := hW.preimage p
end AlgebraicGeometry.Scheme.Hom
