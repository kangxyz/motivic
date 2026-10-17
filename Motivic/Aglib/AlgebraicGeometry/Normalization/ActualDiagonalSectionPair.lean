/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualDiagonalBoundary
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.ActualConstantCurveMap
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FixedFieldBoundarySectionPair

/-! # Actual diagonal section pairs on the constructed compactification -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (s : Z ⟶ S)

abbrev diagonalAmbient := pullback ((r ≫ inclusion k p) ≫ projection k p) (projection k p)
abbrev diagonalBoundary :=
  pullback (pullback.snd ((r ≫ inclusion k p) ≫ projection k p) (projection k p))
      (infinityInclusion k p) ⨿
    pullback ((r ≫ inclusion k p) ≫ projection k p) (s ≫ (r ≫ inclusion k p) ≫ projection k p)
abbrev diagonalBoundaryMap : diagonalBoundary k p r s ⟶ diagonalAmbient k p r :=
  Hom.fullBoundaryProductMap (projection k p) (r ≫ inclusion k p) (infinityInclusion k p) s
abbrev diagonalFieldBoundary := infinity k p ⨿ Z
abbrev diagonalFieldBoundaryMap : diagonalFieldBoundary k p (Z := Z) ⟶ compactification k p :=
  coprod.desc (infinityInclusion k p) (s ≫ (r ≫ inclusion k p))

def diagonalBoundaryToField : diagonalBoundary k p r s ⟶ diagonalFieldBoundary k p (Z := Z) :=
  coprod.map (pullback.snd _ _) (pullback.snd _ _)

omit [IsOpenImmersion r] in
@[reassoc]
theorem diagonalBoundaryToField_fac :
    diagonalBoundaryMap k p r s ≫ pullback.snd _ _ =
      diagonalBoundaryToField k p r s ≫ diagonalFieldBoundaryMap k p r s := by
  apply coprod.hom_ext
  · simp only [diagonalBoundaryMap, Hom.fullBoundaryProductMap,
      coprod.inl_desc_assoc, diagonalBoundaryToField, coprod.inl_map_assoc,
      diagonalFieldBoundaryMap, coprod.inl_desc]
    exact pullback.condition
  · simp [diagonalBoundaryMap, Hom.fullBoundaryProductMap, diagonalBoundaryToField,
      diagonalFieldBoundaryMap, Hom.graphBoundaryRestriction]

/-- Properness of the entire original finite boundary makes its inclusion closed. -/
theorem diagonalOriginalBoundary_closed [IsClosedImmersion s]
    [IsFinite (s ≫ (r ≫ inclusion k p) ≫ projection k p)] :
    IsClosedImmersion (s ≫ (r ≫ inclusion k p)) := by
  have : IsProper ((s ≫ (r ≫ inclusion k p)) ≫ projection k p) := by
    rw [Category.assoc]
    infer_instance
  have : IsProper (s ≫ (r ≫ inclusion k p)) := IsProper.of_comp _ (projection k p)
  exact IsClosedImmersion.of_isPreimmersion _
    (s ≫ (r ≫ inclusion k p)).isClosedMap.isClosed_range

/-- The full boundary needed for Serre is closed on the actual product. -/
theorem diagonalBoundary_closed [IsClosedImmersion s]
    [IsFinite (s ≫ (r ≫ inclusion k p) ≫ projection k p)] :
    IsClosedImmersion (diagonalBoundaryMap k p r s) := by
  have := diagonalOriginalBoundary_closed k p r s
  exact Hom.fullBoundaryProduct_isClosedImmersion (projection k p) (r ≫ inclusion k p)
    (infinityInclusion k p) s (refined_disjoint_infinity k p r)

omit [IsOpenImmersion r] in
/-- The single original field boundary supplies every twist unit for both source legs. -/
theorem diagonalFieldBoundary_finite
    [IsFinite (s ≫ (r ≫ inclusion k p) ≫ projection k p)] :
    IsFinite (diagonalFieldBoundaryMap k p r s ≫ projection k p) := by
  have : IsFinite (s ≫ r ≫ inclusion k p ≫ projection k p) := by
    simpa only [Category.assoc] using
      (inferInstance : IsFinite (s ≫ (r ≫ inclusion k p) ≫ projection k p))
  change IsFinite (coprod.desc _ _ ≫ projection k p)
  rw [coprod.desc_comp]
  simp only [Category.assoc]
  infer_instance

/-- The actual specified diagonal boundary isomorphism chosen together with its canonical
infinity and coordinate restriction equations in `exists_actualFullBoundaryDivisorIso`. -/
def actualBoundaryIso (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    (s : Spec (.of B) ⟶ S)
    (hs : s ≫ (r ≫ p) = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z)) :
    (Modules.pullback (diagonalBoundaryMap k p r s)).obj (actualDivisorLineBundle k p r).val ≅
      SheafOfModules.unit (diagonalBoundary k p r s).ringCatSheaf :=
  Classical.choose (exists_actualFullBoundaryDivisorIso k p r B z s hs H)

/-- The actual original affine source determines the relative finite projective map. -/
def diagonalProjectiveMap {R : Type u} [CommRing R] (r : Spec (.of R) ⟶ Y) :
    diagonalAmbient k p r ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  ConstantCurve.actualToProjectiveSpace ((r ≫ inclusion k p) ≫ projection k p)
    (ULift.{u} (Fin 2)) (toProjectiveLine k p)

/-- Original étale data produces actual numerator and denominator sections for λ, on the
unchanged affine source. The entire specified diagonal boundary and its generating value
are constructed, and the two literal pullback equations are retained. -/
theorem exists_actualDiagonalSectionPair {R : Type u} [CommRing R] [IsNoetherianRing R]
    (r : Spec (.of R) ⟶ Y) [IsOpenImmersion r]
    (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    [IsClosedImmersion (Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)]
    (s : Spec (.of B) ⟶ Spec (.of R))
    (hs : s ≫ (r ≫ p) = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z)) :
    let C := diagonalAmbient k p r
    let W := diagonalBoundary k p r s
    let zD := diagonalBoundaryMap k p r s
    let M := (actualDivisorLineBundle k p r).val
    let E := actualBoundaryIso k p r B z s hs H
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      let L := (Modules.pullback (diagonalProjectiveMap k p r)).obj
        (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (d : ℤ))
      let T := moduleTensorLeftFunctor W ((Modules.pullback zD).obj L)
      ∃ u : SheafOfModules.unit W.ringCatSheaf ⟶
        T.obj ((Modules.pullback zD).obj (SheafOfModules.unit C.ringCatSheaf)),
      IsIso u ∧
      ∃ a : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj M,
      ∃ b : SheafOfModules.unit C.ringCatSheaf ⟶
        (moduleTensorLeftFunctor C L).obj (SheafOfModules.unit C.ringCatSheaf),
        (pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map a ≫ pullbackTensorMap zD L M =
          u ≫ T.map ((pullbackUnitIso zD).hom ≫ E.inv) ∧
        (pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map b ≫
            pullbackTensorMap zD L (SheafOfModules.unit C.ringCatSheaf) = u ∧
        IsIso ((pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map a) ∧
        IsIso ((pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map b) := by
  have : IsClosedImmersion s := MorphismProperty.of_isPullback H.flip inferInstance
  have hsp : s ≫ (r ≫ inclusion k p) ≫ projection k p =
      Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k := by
    simp only [Category.assoc, inclusion_projection]
    simpa only [Category.assoc] using congrArg (fun m => m ≫ Hom.boundaryLineProjection k) hs
  have : IsFinite (s ≫ (r ≫ inclusion k p) ≫ projection k p) := by rw [hsp]; infer_instance
  have := diagonalBoundary_closed k p r s
  let aP := diagonalProjectiveMap k p r
  have : IsFinite aP := inferInstanceAs (IsFinite (ConstantCurve.actualToProjectiveSpace _ _ _))
  have : IsLocallyNoetherian (diagonalAmbient k p r) := LocallyOfFiniteType.isLocallyNoetherian aP
  let M := actualDivisorLineBundle k p r
  let O := SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf
  have := Invertible.finiteLocallyFree_of_isLocallyRankOne M.val M.property
  have hO : Invertible.IsLocallyRankOne (diagonalAmbient k p r) O :=
    Invertible.isLocallyRankOne_of_iso _
      (CategoryTheory.Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => O))
      (Invertible.trivialLineBundle (diagonalAmbient k p r)).property
  have := Invertible.finiteLocallyFree_of_isLocallyRankOne O hO
  let g := diagonalFieldBoundaryMap k p r s ≫ toProjectiveLine k p
  have : IsFinite (g ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin 2))) :=
    diagonalFieldBoundary_finite k p r s
  have ha : (diagonalBoundaryMap k p r s ≫ aP) ≫
      ProjectiveSpace.map (ConstantCurve.coefficientMap
        ((r ≫ inclusion k p) ≫ projection k p)) (ULift.{u} (Fin 2)) =
        diagonalBoundaryToField k p r s ≫ g := by
    dsimp only [aP, diagonalProjectiveMap]
    rw [Category.assoc, ConstantCurve.actualToProjectiveSpace_map]
    simpa only [Category.assoc] using
      congrArg (fun m => m ≫ toProjectiveLine k p) (diagonalBoundaryToField_fac k p r s)
  obtain ⟨N, hN⟩ := CoherentGraph.exists_fixedField_boundary_section_maps k R
    (ConstantCurve.coefficientMap ((r ≫ inclusion k p) ≫ projection k p))
    (ULift.{u} (Fin 2)) 1 Equiv.ulift aP (diagonalBoundaryMap k p r s) g
    (diagonalBoundaryToField k p r s) ha M.val O (coherent_of_finiteLocallyFree _)
    (coherent_of_finiteLocallyFree _) (actualBoundaryIso k p r B z s hs H)
    (pullbackUnitIso (diagonalBoundaryMap k p r s))
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨a, b, ha, hb, hIa, hIb⟩ := hN d hd
  refine ⟨_, inferInstance, a, b, ha, ?_, hIa, hIb⟩
  dsimp only [O] at hb
  erw [Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] at hb
  exact hb
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
