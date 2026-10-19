/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Coproduct
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryTwistFrames
/-! # The refined source uses the unchanged full target boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (π : C ⟶ S) (j : Y ⟶ C) (hj : j ≫ π = p ≫ q) (d : D ⟶ C)
  (U : X.Opens) (V : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U)

def boundaryBaseSourceBoundaryToFull :
    ((d ≫ π) ⁻¹ᵁ V).toScheme ⨿ (boundaryBaseClosedOpen q z V).toScheme ⟶
      ((coprod.desc d (s ≫ j) ≫ π) ⁻¹ᵁ V).toScheme :=
  coprod.desc
    (IsOpenImmersion.lift ((coprod.desc d (s ≫ j) ≫ π) ⁻¹ᵁ V).ι
      (((d ≫ π) ⁻¹ᵁ V).ι ≫ coprod.inl) (by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Opens.range_ι]
        change (coprod.inl ≫ coprod.desc d (s ≫ j) ≫ π) x.val ∈ V
        simpa only [coprod.inl_desc_assoc, Scheme.Hom.mem_preimage] using x.property))
    (IsOpenImmersion.lift ((coprod.desc d (s ≫ j) ≫ π) ⁻¹ᵁ V).ι
      ((boundaryBaseClosedOpen q z V).ι ≫ coprod.inr) (by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Opens.range_ι]
        change (coprod.inr ≫ coprod.desc d (s ≫ j) ≫ π) x.val ∈ V
        rw [coprod.inr_desc_assoc, Category.assoc, hj, ← Category.assoc, hs]
        exact x.property))

@[reassoc]
theorem boundaryBaseSourceBoundaryToFull_ι :
    boundaryBaseSourceBoundaryToFull q p z s hs π j hj d V ≫
      ((coprod.desc d (s ≫ j) ≫ π) ⁻¹ᵁ V).ι =
    coprod.desc (((d ≫ π) ⁻¹ᵁ V).ι ≫ coprod.inl)
      ((boundaryBaseClosedOpen q z V).ι ≫ coprod.inr) := by
  apply coprod.hom_ext <;> simp [boundaryBaseSourceBoundaryToFull]

/-- The actual refined zero lift and original missing boundary map into the same
base-changed full target boundary. The parameter shrink does not enlarge that boundary. -/
@[reassoc]
theorem boundaryBaseSourceBoundaryToFull_boundary :
    boundaryBaseSourceBoundaryToFull q p z s hs π j hj d V ≫
      boundaryBaseWholeMap π (coprod.desc d (s ≫ j)) V =
    coprod.desc (boundaryBaseWholeMap π d V)
      (boundaryBaseCoverLift q p z s hs U V h ≫
        boundaryBaseCoverInclusion q p π j hj U V) := by
  apply (cancel_mono (pullback.snd V.ι π)).mp
  simp only [Category.assoc, boundaryBaseWholeMap_snd]
  rw [boundaryBaseSourceBoundaryToFull_ι_assoc]
  apply coprod.hom_ext <;> simp
/-- The refined zero is the literal base change of the original closed subscheme in C. -/
theorem boundaryBaseSourceZero_isPullback :
    IsPullback (boundaryBaseClosedOpen q z V).ι
      (boundaryBaseCoverLift q p z s hs U V h ≫
        boundaryBaseCoverInclusion q p π j hj U V)
      (s ≫ j) (pullback.snd V.ι π) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · simp
  · rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι,
      Scheme.Opens.opensRange_ι]
    change (s ≫ j) ⁻¹ᵁ π ⁻¹ᵁ V = (z ≫ q) ⁻¹ᵁ V
    rw [← Scheme.Hom.comp_preimage]
    congr 1
    rw [Category.assoc, hj, ← Category.assoc, hs]

theorem boundaryBaseSourceZero_closed [IsClosedImmersion (s ≫ j)] :
    IsClosedImmersion (boundaryBaseCoverLift q p z s hs U V h ≫
      boundaryBaseCoverInclusion q p π j hj U V) :=
  MorphismProperty.of_isPullback
    (boundaryBaseSourceZero_isPullback q p z s hs π j hj U V h) inferInstance

/-- Finiteness is inherited from the entire original Z, not inferred from its support. -/
theorem boundaryBaseSourceZero_finite [IsFinite (z ≫ q)] :
    IsFinite ((boundaryBaseCoverLift q p z s hs U V h ≫
      boundaryBaseCoverInclusion q p π j hj U V) ≫ pullback.fst V.ι π) := by
  simp only [Category.assoc, boundaryBaseCoverInclusion_fst,
    boundaryBaseCoverLift_map_assoc]
  exact boundaryBaseLift_finite q z U V h
/-- The refined source boundary takes the same original full-target frame. -/
def boundaryBaseSourceBoundaryFrame (M : (boundaryBaseCompactification π V).Modules)
    (e : (Modules.pullback (boundaryBaseWholeMap π (coprod.desc d (s ≫ j)) V)).obj M ≅
      SheafOfModules.unit ((coprod.desc d (s ≫ j) ≫ π) ⁻¹ᵁ V).toScheme.ringCatSheaf) :
    (Modules.pullback (coprod.desc (boundaryBaseWholeMap π d V)
      (boundaryBaseCoverLift q p z s hs U V h ≫
        boundaryBaseCoverInclusion q p π j hj U V))).obj M ≅
      SheafOfModules.unit
        (((d ≫ π) ⁻¹ᵁ V).toScheme ⨿ (boundaryBaseClosedOpen q z V).toScheme).ringCatSheaf :=
  (Modules.pullbackCongr
    (boundaryBaseSourceBoundaryToFull_boundary q p z s hs π j hj d U V h).symm).app M ≪≫
    (Modules.pullbackComp (boundaryBaseSourceBoundaryToFull q p z s hs π j hj d V)
      (boundaryBaseWholeMap π (coprod.desc d (s ≫ j)) V)).symm.app M ≪≫
    (Modules.pullback (boundaryBaseSourceBoundaryToFull q p z s hs π j hj d V)).mapIso e ≪≫
      Modules.pullbackUnitIso (boundaryBaseSourceBoundaryToFull q p z s hs π j hj d V)
/-- The full original zero support, not merely a subset, is retained over the base open. -/
theorem mem_range_boundaryBaseSourceZero_iff (x : boundaryBaseCompactification π V) :
    x ∈ Set.range (boundaryBaseCoverLift q p z s hs U V h ≫
      boundaryBaseCoverInclusion q p π j hj U V) ↔
      pullback.snd V.ι π x ∈ Set.range (s ≫ j) := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t.val, ?_⟩
    simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using
      (congrArg (fun f => f t)
        (show (boundaryBaseCoverLift q p z s hs U V h ≫
          boundaryBaseCoverInclusion q p π j hj U V) ≫ pullback.snd V.ι π =
          (boundaryBaseClosedOpen q z V).ι ≫ s ≫ j by simp)).symm
  · rintro ⟨t, ht⟩
    have hx : π (pullback.snd V.ι π x) ∈ V := by
      have he := congrArg (fun f => f x) (pullback.condition (f := V.ι) (g := π))
      change V.ι (pullback.fst V.ι π x) = π (pullback.snd V.ι π x) at he
      rw [← he]
      exact (pullback.fst V.ι π x).property
    have hm : (z ≫ q) t ∈ V := by
      rw [← hs, Category.assoc, ← hj, ← Category.assoc]
      change π ((s ≫ j) t) ∈ V
      rwa [ht]
    refine ⟨⟨t, hm⟩, ?_⟩
    apply (pullback.snd V.ι π).isOpenEmbedding.injective
    change ((boundaryBaseCoverLift q p z s hs U V h ≫
      boundaryBaseCoverInclusion q p π j hj U V) ≫ pullback.snd V.ι π) ⟨t, hm⟩ = _
    simpa using ht
/-- The original retained target plus the original full boundary covers after refinement. -/
theorem boundaryBaseSourceBoundary_cover {T : Scheme.{u}} (v : T ⟶ C)
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (x : boundaryBaseCompactification π V) :
    x ∈ Set.range (boundaryBaseRetainedTarget π V v) ∨
      x ∈ Set.range (boundaryBaseWholeMap π d V) ∨
      x ∈ Set.range (boundaryBaseCoverLift q p z s hs U V h ≫
        boundaryBaseCoverInclusion q p π j hj U V) := by
  simpa only [boundaryBaseRetainedTarget, mem_range_boundaryBaseWholeMap_iff,
    mem_range_boundaryBaseSourceZero_iff] using hc (pullback.snd V.ι π x)
end AlgebraicGeometry.Scheme.Hom
