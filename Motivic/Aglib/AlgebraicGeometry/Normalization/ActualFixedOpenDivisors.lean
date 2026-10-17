module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualFixedOpenSectionPair
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ConstantRetainedTarget
public import Motivic.Aglib.AlgebraicGeometry.SectionDualDivisor
/-! # Actual fixed-source psi divisors on the original retained target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
private theorem range_coprod_desc {D Z C : Scheme.{u}} (i : D ⟶ C) (j : Z ⟶ C) :
    Set.range (coprod.desc i j) = Set.range i ∪ Set.range j := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y | y, rfl⟩ := (coprodMk D Z).surjective y
    · rw [coprodMk_inl]
      left
      exact ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
    · rw [coprodMk_inr]
      right
      exact ⟨y, by simp [← Scheme.Hom.comp_apply]⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨(coprod.inl : D ⟶ D ⨿ Z) y, by simp [← Scheme.Hom.comp_apply]⟩
    · exact ⟨(coprod.inr : Z ⟶ D ⨿ Z) y, by simp [← Scheme.Hom.comp_apply]⟩


variable (k : Type u) [Field k] {Y A : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ Spec (.of (Polynomial k)))
  (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = Hom.boundaryCoordinateMap k B z)

theorem range_fixedBoundaryMap : Set.range (fixedBoundaryMap k p a B z s hs) =
    (pullback.snd (a ≫ Hom.boundaryLineProjection k) (projection k p)) ⁻¹'
      (Set.range (infinityInclusion k p) ∪ Set.range (s ≫ inclusion k p)) := by
  rw [fixedBoundaryMap, range_coprod_desc, Set.preimage_union]
  congr 1
  · exact Scheme.Pullback.range_fst _ _
  · let H := fixedZeroMap_isPullback k p a B z s hs
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨pullback.snd (a ≫ Hom.boundaryLineProjection k)
        (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k) v,
        congrArg (fun m => m v) H.w⟩
    · rintro ⟨v, hv⟩
      obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback H v x hv
      exact ⟨w, hw⟩

theorem fixedBoundary_retained_cover
    (U : (Spec (.of (Polynomial k))).Opens)
    (H : IsPullback s (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    ∀ x : fixedAmbient k p a,
      x ∈ Set.range (constantRetainedInclusion k p U (a ≫ Hom.boundaryLineProjection k)) ∨
        x ∈ Set.range (fixedBoundaryMap k p a B z s hs) := by
  intro x
  rw [range_constantRetainedInclusion_complement k p U _
    (Hom.boundaryCoordinateMap k B z) s H hz, range_fixedBoundaryMap]
  exact Classical.em _ |>.symm

/-- The actual fixed-source sections give whole finite flat zeros on the original overlap. -/
theorem actualFixedSectionDivisor_finite_mono_flat [IsAffine A]
    (U : (Spec (.of (Polynomial k))).Opens)
    (H : IsPullback s (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ)
    (L : LineBundle (fixedAmbient k p a))
    (t : SheafOfModules.unit (fixedAmbient k p a).ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap (fixedBoundaryMap k p a B z s hs) t)] :
    let q := a ≫ Hom.boundaryLineProjection k
    let j := constantRetainedInclusion k p U q
    let f := Hom.pullbackToUnit (sectionDualFunctional _ L t) j
    IsFinite (Hom.zeroInclusion f ≫ j ≫ pullback.fst q (projection k p)) ∧
      Mono f ∧ Flat (Hom.zeroInclusion f ≫ j ≫ pullback.fst q (projection k p)) := by
  let q := a ≫ Hom.boundaryLineProjection k
  let j := constantRetainedInclusion k p U q
  have := constantRetainedTarget_quasiAffine k p U q
  have : SmoothOfRelativeDimension 1 (j ≫ pullback.fst q (projection k p)) := by
    dsimp only [j]
    rw [constantRetainedInclusion_fst]
    exact constantRetainedTarget_smooth k p U q
  exact sectionDualFunctional_finite_mono_flat_on_open (fixedBoundaryMap k p a B z s hs)
    (pullback.fst q (projection k p)) j L t
    (fixedBoundary_retained_cover k p a B z s hs U H hz)
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
