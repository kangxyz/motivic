module
public import Motivic.Cohomology.WholeAffineLineH1BaseZero
public import Motivic.Cohomology.SheafCohomologyRelativeMonicZeroSquare
public import Motivic.RingTheory.Smooth.Normal
/-! # Whole-line H¹ base vanishing from an actual monic zero square -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.PolynomialOpenQuotient
open AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
universe w u
namespace Motivic.SheafCohomology
open RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

omit [IsDomain R] in
/-- The whole polynomial quotient is the actual complement of its principal open. -/
lemma monic_inclusion_range (f : R[X]) :
    Set.range (AlgebraicGeometry.PolynomialOpenQuotient.inclusion f) =
      (Set.range (principalOpen f).ι)ᶜ := by
  rw [Scheme.Opens.range_ι]
  change Set.range (PrimeSpectrum.comap (AdjoinRoot.mk f)) = _
  rw [range_comap_of_surjective _ _ AdjoinRoot.mk_surjective]
  rw [show RingHom.ker (AdjoinRoot.mk f) = Ideal.span {f} from Ideal.mk_ker,
    PrimeSpectrum.zeroLocus_span]
  ext x
  change ({f} ⊆ (x.asIdeal : Set R[X])) ↔ ¬ f ∉ x.asIdeal
  simp

/-- The original section supplied by the given full-neighborhood isomorphism. -/
def neighborhoodSection {X Y Z : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] : Z ⟶ Y :=
  inv (pullback.snd p z) ≫ pullback.fst p z

lemma neighborhoodSection_comp {X Y Z : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] : neighborhoodSection p z ≫ p = z := by
  simp [neighborhoodSection, pullback.condition]

lemma neighborhoodSection_isPullback {X Y Z : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] : IsPullback (neighborhoodSection p z) (𝟙 Z) p z :=
  (IsPullback.of_hasPullback p z).of_iso (asIso (pullback.snd p z))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [neighborhoodSection])
    (by simp) (by simp) (by simp)

instance neighborhoodSection_closed {X Y Z : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X)
    [IsIso (pullback.snd p z)] [IsClosedImmersion z] :
    IsClosedImmersion (neighborhoodSection p z) := by
  dsimp [neighborhoodSection]
  infer_instance

/-- No extra lifting or compactification hypothesis: the original two zero legs
and the original full monic closed neighborhood are the entire input. -/
local instance relativeMonic_base_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  AffineTorusPolynomialPresentation.baseMap_smooth (k := k) (R := R)
local instance relativeMonic_line_smooth : SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

theorem exists_monic_h_one_base_restriction_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (f : R[X]) (hf : f.Monic)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (lineSite (k := k) (R := R)))
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
    [IsIso (pullback.snd p.left (AlgebraicGeometry.PolynomialOpenQuotient.inclusion f))]
    (hA : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map (openInclusion f).op x = 0)
    (hY : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map p.op x = 0) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      genericPoint (Spec (.of R)) ∈ V ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V),
        let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme := hW
        (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1).map
          (boundaryBaseAmbientRestriction k R
            (Spec.map (CommRingCat.ofHom (algebraMap k R))) (boundaryLineProjection R) ⊤ V).op
          x = 0 := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : IsIntegrallyClosed R := Motivic.isIntegrallyClosed_of_smooth_field k R
  let t := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let : Smooth t := AffineTorusPolynomialPresentation.baseMap_smooth (k := k) (R := R)
  let q := boundaryLineProjection R
  let : SmoothOfRelativeDimension 1 q :=
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  let z := AlgebraicGeometry.PolynomialOpenQuotient.inclusion f
  let s := neighborhoodSection p.left z
  have hs := neighborhoodSection_comp p.left z
  have Hs := neighborhoodSection_isPullback p.left z
  let : IsFinite (boundaryCoordinateMap R (AdjoinRoot f) (AdjoinRoot.mk f) ≫ q) := by
    change IsFinite (z ≫ q)
    rw [show z ≫ q = source f from
      AlgebraicGeometry.PolynomialOpenQuotient.inclusion_projection f]
    exact source_finite f hf
  have hY' : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map
      (originalEtaleArrow k R t q p.left).op x = 0 := by
    let i : originalEtaleSite k R t q p.left ⟶ Y := SmoothSite.homMk (𝟙 _) (by
      change (𝟙 Y.left) ≫ Y.hom = p.left ≫ (lineSite (k := k) (R := R)).hom
      rw [Category.id_comp, MorphismProperty.Over.w])
    have hi : i ≫ p = originalEtaleArrow k R t q p.left := by
      apply MorphismProperty.Over.Hom.ext
      exact Category.id_comp p.left
    rw [← hi, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact (congrArg ((presheaf.{w, u + 1, u, u + 1} _ _ 1).map i.op) hY).trans (map_zero _)
  let : IsAffine (principalOpen f).toScheme :=
    IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R[X]) f
  let : IsClosedImmersion (boundaryCoordinateMap R (AdjoinRoot f) (AdjoinRoot.mk f)) :=
    inferInstanceAs (IsClosedImmersion z)
  exact exists_original_h_one_base_restriction_eq_zero
    k R t p.left (principalOpen f).ι (AdjoinRoot f) (AdjoinRoot.mk f) s hs Hs
    (monic_inclusion_range f) F hF x hA hY'

omit [IsDomain R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- Identity on the original base-restricted line, with its two actual site structures. -/
def monicBaseOpenComparison
    (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme] :
    (SmoothSite.opensFunctor (lineSite (k := k) (R := R))).obj
      (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V) ⟶
      boundaryBaseAmbientSite k R (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (boundaryLineProjection R) ⊤ V :=
  SmoothSite.homMk (𝟙 _) (by
    rw [Category.id_comp, boundaryBaseAmbientSite_hom]
    rfl)

omit [IsDomain R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
lemma monicBaseOpenComparison_comp
    (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme] :
    monicBaseOpenComparison V ≫ boundaryBaseAmbientRestriction k R
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) (boundaryLineProjection R) ⊤ V =
      SmoothSite.openInclusion (lineSite (k := k) (R := R))
        (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V) := by
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

omit [IsDomain R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- Transport the actual ambient restriction to the literal original open inclusion. -/
lemma monic_base_restriction_open_zero
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
    (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
    [IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme]
    (x : P.obj (op (lineSite (k := k) (R := R))))
    (hx : P.map (boundaryBaseAmbientRestriction k R
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (boundaryLineProjection R) ⊤ V).op x = 0) :
    P.map (SmoothSite.openInclusion (lineSite (k := k) (R := R))
      (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V)).op x = 0 := by
  rw [← monicBaseOpenComparison_comp V, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]
  exact (congrArg (P.map (monicBaseOpenComparison V).op) hx).trans (map_zero _)

theorem exists_monic_h_one_base_open_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (f : R[X]) (hf : f.Monic)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (lineSite (k := k) (R := R)))
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
    [IsIso (pullback.snd p.left (AlgebraicGeometry.PolynomialOpenQuotient.inclusion f))]
    (hA : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map (openInclusion f).op x = 0)
    (hY : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map p.op x = 0) :
    ∃ V : (Spec (.of R)).Opens, IsAffineOpen V ∧ genericPoint (Spec (.of R)) ∈ V ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (SmoothSite.openInclusion (lineSite (k := k) (R := R))
          (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V)).op x = 0 := by
  obtain ⟨V, hV, hη, hW, hx⟩ :=
    exists_monic_h_one_base_restriction_zero F hF f hf x p hA hY
  let : IsAffine V.toScheme := hV
  let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme := hW
  exact ⟨V, hV, hη, monic_base_restriction_open_zero _ V x hx⟩

end Motivic.SheafCohomology
