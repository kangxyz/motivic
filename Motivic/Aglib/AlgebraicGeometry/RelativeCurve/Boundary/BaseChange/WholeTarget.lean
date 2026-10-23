/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Compactification
/-! # Base change of the unchanged whole target boundary

The target here is the original curve over the smaller base. In particular, the smaller
parameter open used to trivialize the diagonal is not substituted for the retained target:
its complement need not be finite over the base.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S C D Y : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C) (V : S.Opens)

/-- Native identification of the base-changed compactification with its original open. -/
def boundaryBaseCompactificationOpenIso :
    (π ⁻¹ᵁ V).toScheme ≅ boundaryBaseCompactification π V :=
  (isPullback_morphismRestrict π V).isoPullback

/-- The entire original boundary, restricted only on the base. No reduction is taken. -/
def boundaryBaseWholeMap : ((d ≫ π) ⁻¹ᵁ V).toScheme ⟶
    boundaryBaseCompactification π V :=
  (d ∣_ (π ⁻¹ᵁ V)) ≫ (boundaryBaseCompactificationOpenIso π V).hom

@[reassoc (attr := simp)]
theorem boundaryBaseWholeMap_fst :
    boundaryBaseWholeMap π d V ≫ pullback.fst V.ι π = (d ≫ π) ∣_ V := by
  simp only [boundaryBaseWholeMap, Category.assoc, boundaryBaseCompactificationOpenIso,
    IsPullback.isoPullback_hom_fst]
  exact (morphismRestrict_comp d π V).symm

@[reassoc (attr := simp)]
theorem boundaryBaseWholeMap_snd :
    boundaryBaseWholeMap π d V ≫ pullback.snd V.ι π =
      ((d ≫ π) ⁻¹ᵁ V).ι ≫ d := by
  simp only [boundaryBaseWholeMap, Category.assoc, boundaryBaseCompactificationOpenIso,
    IsPullback.isoPullback_hom_snd, morphismRestrict_ι]
  rfl

instance boundaryBaseWholeMap_closed [IsClosedImmersion d] :
    IsClosedImmersion (boundaryBaseWholeMap π d V) := by
  dsimp [boundaryBaseWholeMap]
  infer_instance

/-- Finiteness of the original full boundary survives the same base shrink. -/
theorem boundaryBaseWholeMap_finite [IsFinite (d ≫ π)] :
    IsFinite (boundaryBaseWholeMap π d V ≫ pullback.fst V.ι π) := by
  rw [boundaryBaseWholeMap_fst]
  infer_instance

/-- The retained target is base-changed independently of any smaller parameter open. -/
def boundaryBaseRetainedTarget (j : Y ⟶ C) :
    ((j ≫ π) ⁻¹ᵁ V).toScheme ⟶ boundaryBaseCompactification π V :=
  boundaryBaseWholeMap π j V

instance boundaryBaseRetainedTarget_open (j : Y ⟶ C) [IsOpenImmersion j] :
    IsOpenImmersion (boundaryBaseRetainedTarget π V j) := by
  dsimp [boundaryBaseRetainedTarget, boundaryBaseWholeMap]
  infer_instance

/-- Only the original retained target, never the compactification, must be smooth. -/
theorem boundaryBaseRetainedTarget_smooth (j : Y ⟶ C)
    [SmoothOfRelativeDimension 1 (j ≫ π)] :
    SmoothOfRelativeDimension 1
      (boundaryBaseRetainedTarget π V j ≫ pullback.fst V.ι π) := by
  change SmoothOfRelativeDimension 1 (boundaryBaseWholeMap π j V ≫ _)
  rw [boundaryBaseWholeMap_fst]
  exact MorphismProperty.of_isPullback
    (isPullback_morphismRestrict (j ≫ π) V).flip inferInstance
/-- Exact support base change, with the original scheme structure retained above. -/
theorem mem_range_boundaryBaseWholeMap_iff (x : boundaryBaseCompactification π V) :
    x ∈ Set.range (boundaryBaseWholeMap π d V) ↔
      pullback.snd V.ι π x ∈ Set.range d := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨((d ≫ π) ⁻¹ᵁ V).ι y,
      (congrArg (fun f => f y) (boundaryBaseWholeMap_snd π d V)).symm⟩
  · rintro ⟨y, hy⟩
    have hx : π (pullback.snd V.ι π x) ∈ V := by
      have he := congrArg (fun f => f x) (pullback.condition (f := V.ι) (g := π))
      change V.ι (pullback.fst V.ι π x) = π (pullback.snd V.ι π x) at he
      rw [← he]
      exact (pullback.fst V.ι π x).property
    have hm : (d ≫ π) y ∈ V := by
      change π (d y) ∈ V
      rwa [hy]
    refine ⟨⟨y, hm⟩, ?_⟩
    apply (pullback.snd V.ι π).isOpenEmbedding.injective
    have he := congrArg (fun f => f ⟨y, hm⟩) (boundaryBaseWholeMap_snd π d V)
    exact he.trans hy

/-- The original retained target and full boundary still cover after base change. The
smaller parameter neighborhood does not occur in this assertion. -/
theorem boundaryBaseWholeTarget_cover (j : Y ⟶ C)
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range d)
    (x : boundaryBaseCompactification π V) :
    x ∈ Set.range (boundaryBaseRetainedTarget π V j) ∨
      x ∈ Set.range (boundaryBaseWholeMap π d V) := by
  simpa only [boundaryBaseRetainedTarget, mem_range_boundaryBaseWholeMap_iff] using
    hcover (pullback.snd V.ι π x)
end AlgebraicGeometry.Scheme.Hom
