module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryInclusions
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.CurveGeometry
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FullBoundaryProduct
/-! # The original lambda and psi full boundaries on the actual target products -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A Z C D V : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C) (v : V ⟶ C)

lemma psiZeroInclusion_isPullback :
    IsPullback (pullback.snd (a ≫ q) (z ≫ q)) (psiZeroInclusion q π j p hq a z s hs)
      (s ≫ j) (pullback.snd (a ≫ q) π) := by
  have hz : (s ≫ j) ≫ π = z ≫ q := by rw [Category.assoc, hq, ← Category.assoc, hs]
  have H : IsPullback (pullback.snd (a ≫ q) (z ≫ q))
      (pullback.fst _ _) ((s ≫ j) ≫ π) (a ≫ q) := by
    rw [hz]
    exact (IsPullback.of_hasPullback _ _).flip
  convert H.of_bot' (IsPullback.of_hasPullback (a ≫ q) π).flip using 1
  apply pullback.hom_ext <;> simp [psiZeroInclusion]

lemma psiBoundary_closed [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
    (hd : Disjoint (Set.range j) (Set.range d)) :
    IsClosedImmersion (psiBoundaryInclusion q π j p hq a z s hs d) := by
  have : IsClosedImmersion (psiZeroInclusion q π j p hq a z s hs) :=
    MorphismProperty.of_isPullback (psiZeroInclusion_isPullback q π j p hq a z s hs) inferInstance
  apply isClosedImmersion_coprod_desc
  apply Set.disjoint_left.mpr
  rintro x ⟨u, rfl⟩ ⟨w, hw⟩
  have h1 := congrArg (fun f => f u)
    (pullback.condition (f := pullback.snd (a ≫ q) π) (g := d))
  have h2 := congrArg (fun f => f w) (psiZeroInclusion_isPullback q π j p hq a z s hs).w
  have h3 := congrArg (fun t => (pullback.snd (a ≫ q) π) t) hw
  exact Set.disjoint_iff_forall_ne.mp hd ⟨_, rfl⟩ ⟨_, rfl⟩ (h2.trans (h3.trans h1))

lemma lambdaBoundary_retained_cover
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j)) :
    ∀ x : (pullback (j ≫ π) π : Scheme.{u}),
      x ∈ Set.range (retainedProductInclusion (j ≫ π) π v) ∨
        x ∈ Set.range (Hom.fullBoundaryProductMap π j d s) := by
  intro x
  rcases hc ((pullback.snd (j ≫ π) π) x) with hv | hd | hz
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback (j ≫ π) π v) w x hw
    exact Or.inl ⟨t, ht⟩
  · have hx : x ∈ Set.range (pullback.fst (pullback.snd (j ≫ π) π) d) := by
      rw [Scheme.Pullback.range_fst]
      exact hd
    obtain ⟨w, hw⟩ := hx
    exact Or.inr ⟨(coprod.inl : pullback (pullback.snd (j ≫ π) π) d ⟶
      pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)) w, by
      simpa only [← Scheme.Hom.comp_apply, Hom.fullBoundaryProductMap,
        coprod.inl_desc, Hom.infinityProductMap] using hw⟩
  · obtain ⟨w, hw⟩ := hz
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (Hom.graphBoundaryRestriction_isPullback π j s).flip w x hw
    exact Or.inr ⟨(coprod.inr : pullback (j ≫ π) (s ≫ j ≫ π) ⟶
      pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)) t, by
      simpa only [← Scheme.Hom.comp_apply, Hom.fullBoundaryProductMap,
        coprod.inr_desc] using ht⟩

lemma psiBoundary_retained_cover
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j)) :
    ∀ x : (pullback (a ≫ q) π : Scheme.{u}),
      x ∈ Set.range (retainedProductInclusion (a ≫ q) π v) ∨
        x ∈ Set.range (psiBoundaryInclusion q π j p hq a z s hs d) := by
  intro x
  rcases hc ((pullback.snd (a ≫ q) π) x) with hv | hd | hz
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback (a ≫ q) π v) w x hw
    exact Or.inl ⟨t, ht⟩
  · have hx : x ∈ Set.range (pullback.fst (pullback.snd (a ≫ q) π) d) := by
      rw [Scheme.Pullback.range_fst]
      exact hd
    obtain ⟨w, hw⟩ := hx
    exact Or.inr ⟨(coprod.inl : pullback (pullback.snd (a ≫ q) π) d ⟶
      pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) w, by
      simpa only [← Scheme.Hom.comp_apply, psiBoundaryInclusion, coprod.inl_desc] using hw⟩
  · obtain ⟨w, hw⟩ := hz
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback
      (psiZeroInclusion_isPullback q π j p hq a z s hs) w x hw
    exact Or.inr ⟨(coprod.inr : pullback (a ≫ q) (z ≫ q) ⟶
      pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) t, by
      simpa only [← Scheme.Hom.comp_apply, psiBoundaryInclusion, coprod.inr_desc] using ht⟩
end AlgebraicGeometry.Scheme.RelativeCurvePencil
