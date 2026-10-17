module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualDiagonalSectionPair
/-! # The unchanged fixed-source product with its actual full field boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y A : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ Spec (.of (Polynomial k)))
  (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = Hom.boundaryCoordinateMap k B z)

abbrev fixedAmbient := pullback (a ≫ Hom.boundaryLineProjection k) (projection k p)
abbrev fixedInfinity := pullback (pullback.snd (a ≫ Hom.boundaryLineProjection k)
  (projection k p)) (infinityInclusion k p)
abbrev fixedZero := pullback (a ≫ Hom.boundaryLineProjection k)
  (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)
abbrev fixedBoundary := fixedInfinity k p a ⨿ fixedZero k a B z

/-- The original full Z component, with its unchanged coordinate base map. -/
def fixedZeroMap : fixedZero k a B z ⟶ fixedAmbient k p a :=
  (IsPullback.of_hasPullback (a ≫ Hom.boundaryLineProjection k) (projection k p)).flip.lift
    (pullback.snd _ _ ≫ s ≫ inclusion k p) (pullback.fst _ _) (by
      rw [Category.assoc, Category.assoc, inclusion_projection,
        ← Category.assoc s, hs]
      exact pullback.condition.symm)

omit [IsSeparated p] in
@[reassoc (attr := simp)] theorem fixedZeroMap_snd :
    fixedZeroMap k p a B z s hs ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ s ≫ inclusion k p := (IsPullback.of_hasPullback _ _).flip.lift_fst _ _ _

omit [IsSeparated p] in
@[reassoc (attr := simp)] theorem fixedZeroMap_fst :
    fixedZeroMap k p a B z s hs ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (IsPullback.of_hasPullback _ _).flip.lift_snd _ _ _

omit [IsSeparated p] in
theorem fixedZeroMap_isPullback :
    IsPullback (pullback.snd _ _) (fixedZeroMap k p a B z s hs)
      (s ≫ inclusion k p) (pullback.snd (a ≫ Hom.boundaryLineProjection k) (projection k p)) := by
  have he : (s ≫ inclusion k p) ≫ projection k p =
      Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k := by
    rw [Category.assoc, inclusion_projection, ← Category.assoc, hs]
  let H := (IsPullback.of_hasPullback (a ≫ Hom.boundaryLineProjection k)
    (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)).flip
  have H' : IsPullback (pullback.snd (a ≫ Hom.boundaryLineProjection k)
      (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k))
      (pullback.fst _ _) ((s ≫ inclusion k p) ≫ projection k p)
      (a ≫ Hom.boundaryLineProjection k) := by rw [he]; exact H
  exact H'.of_bot' (IsPullback.of_hasPullback
    (a ≫ Hom.boundaryLineProjection k) (projection k p)).flip

abbrev fixedBoundaryMap : fixedBoundary k p a B z ⟶ fixedAmbient k p a :=
  coprod.desc (pullback.fst _ _) (fixedZeroMap k p a B z s hs)

abbrev fixedFieldBoundaryMap : infinity k p ⨿ Spec (.of B) ⟶ compactification k p :=
  coprod.desc (infinityInclusion k p) (s ≫ inclusion k p)

def fixedBoundaryToField : fixedBoundary k p a B z ⟶ infinity k p ⨿ Spec (.of B) :=
  coprod.map (pullback.snd _ _) (pullback.snd _ _)

@[reassoc] theorem fixedBoundaryToField_fac :
    fixedBoundaryMap k p a B z s hs ≫ pullback.snd _ _ =
      fixedBoundaryToField k p a B z ≫ fixedFieldBoundaryMap k p B s := by
  apply coprod.hom_ext
  · simp only [fixedBoundaryMap, coprod.inl_desc_assoc, fixedBoundaryToField,
      coprod.inl_map_assoc, fixedFieldBoundaryMap, coprod.inl_desc]
    exact pullback.condition
  · simp [fixedBoundaryMap, fixedBoundaryToField, fixedFieldBoundaryMap]

/-- The full nilpotent-sensitive boundary is actually closed on the original product. -/
theorem fixedBoundary_closed [IsClosedImmersion s]
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)] :
    IsClosedImmersion (fixedBoundaryMap k p a B z s hs) := by
  have he : s ≫ (inclusion k p) ≫ projection k p =
      Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k := by
    rw [inclusion_projection, ← Category.assoc, hs]
  have : IsFinite (s ≫ (inclusion k p) ≫ projection k p) := by rw [he]; infer_instance
  have : IsFinite (s ≫ (𝟙 Y ≫ inclusion k p) ≫ projection k p) := by
    simpa only [Category.id_comp] using
      (inferInstance : IsFinite (s ≫ inclusion k p ≫ projection k p))
  have : IsClosedImmersion (s ≫ inclusion k p) := by
    simpa only [Category.id_comp] using diagonalOriginalBoundary_closed k p (𝟙 Y) s
  have : IsClosedImmersion (fixedZeroMap k p a B z s hs) :=
    MorphismProperty.of_isPullback (fixedZeroMap_isPullback k p a B z s hs) inferInstance
  apply isClosedImmersion_coprod_desc
  apply Set.disjoint_left.mpr
  rintro x ⟨v, rfl⟩ ⟨w, hw⟩
  have h1 := congrArg (fun f => f v) (pullback.condition
    (f := pullback.snd (a ≫ Hom.boundaryLineProjection k) (projection k p))
    (g := infinityInclusion k p))
  have h2 := congrArg (fun f => f w) (fixedZeroMap_snd k p a B z s hs)
  have h3 := congrArg (fun t => (pullback.snd (a ≫ Hom.boundaryLineProjection k)
    (projection k p)) t) hw
  exact Set.disjoint_iff_forall_ne.mp (refined_disjoint_infinity k p (𝟙 Y))
    ⟨s (pullback.snd (a ≫ Hom.boundaryLineProjection k)
      (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k) w), rfl⟩
    ⟨pullback.snd (pullback.snd (a ≫ Hom.boundaryLineProjection k) (projection k p))
      (infinityInclusion k p) v, rfl⟩
    (h2.symm.trans (h3.trans h1))

include hs in
theorem fixedFieldBoundary_finite
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)] :
    IsFinite (fixedFieldBoundaryMap k p B s ≫ projection k p) := by
  have he : (s ≫ inclusion k p) ≫ projection k p =
      Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k := by
    rw [Category.assoc, inclusion_projection, ← Category.assoc, hs]
  change IsFinite (coprod.desc _ _ ≫ _)
  rw [coprod.desc_comp, he]
  infer_instance
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
