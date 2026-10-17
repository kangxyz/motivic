module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.SerreDivisorPairs
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualDiagonalFiniteFlatPair
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualNormalizedFixedOpenPair
/-! # Actual normalized relative Serre pairs for the signed-pencil domain -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Actual Serre sections realize the specified scalar, with their whole finite-flat zeros. -/
theorem exists_normalized_scalar_divisor_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C W U : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : W ⟶ C) [IsClosedImmersion z]
    (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor W
      ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
          SheafOfModules.unit W.ringCatSheaf)
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ a ≫ toSpec R ι)]
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range z)
    (E : SheafOfModules.unit W.ringCatSheaf ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let T := pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))
      ∃ s t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val,
        pullbackSectionMap z s = E.hom ≫ pullbackSectionMap z t ∧
        IsIso (pullbackSectionMap z s) ∧ IsIso (pullbackSectionMap z t) ∧
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j T s ∧
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j T t := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  have : IsProper (a ≫ toSpec R ι) := inferInstance
  let O := AffineLineEtaleCompactification.actualUnitBundle C
  obtain ⟨B, hB⟩ := exists_prescribed_boundary_divisor_pair R ι n e a z eQ j hcover
    O O ((pullbackUnitIso z) ≪≫ E.symm) (pullbackUnitIso z)
  refine ⟨B, fun d hd => ?_⟩
  obtain ⟨s, t, hs, ht, hsi, hti, _, _⟩ := hB d hd
  let T := pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))
  let s0 := rightNormalizeSection T.val s
  let t0 := rightNormalizeSection T.val t
  have : IsIso (pullbackSectionMap z s) := hsi
  have : IsIso (pullbackSectionMap z t) := hti
  have hs0 : IsIso (pullbackSectionMap z s0) := by
    change IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map
      (s ≫ (tensorSheafRightUnit C T.val).hom))
    rw [Functor.map_comp, ← Category.assoc]
    infer_instance
  have ht0 : IsIso (pullbackSectionMap z t0) := by
    change IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map
      (t ≫ (tensorSheafRightUnit C T.val).hom))
    rw [Functor.map_comp, ← Category.assoc]
    infer_instance
  have ht' : pullbackSectionMap z t ≫ pullbackTensorMap z T.val
      (SheafOfModules.unit C.ringCatSheaf) = (eQ d).inv := by
    change (pullbackUnitIso z).inv ≫ (Modules.pullback z).map t ≫
      pullbackTensorMap z ((Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))) O.val = _
    simpa only [Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] using ht
  have hs' : pullbackSectionMap z s ≫ pullbackTensorMap z T.val
      (SheafOfModules.unit C.ringCatSheaf) = (eQ d).inv ≫
        tensorSheafMap W (𝟙 _) ((pullbackUnitIso z).hom ≫ E.hom ≫ (pullbackUnitIso z).inv) := hs
  refine ⟨s0, t0, ?_, hs0, ht0, ?_, ?_⟩
  · change pullbackSectionMap z (rightNormalizeSection T.val s) =
      E.hom ≫ pullbackSectionMap z (rightNormalizeSection T.val t)
    rw [pullbackSectionMap_rightNormalize, pullbackSectionMap_rightNormalize]
    rw [← Category.assoc, hs', Category.assoc,
      ← Category.assoc (pullbackSectionMap z t), ht']
    exact rightUnit_normalize_conjugate (eQ d).inv (pullbackUnitIso z) E.hom
  · exact sectionDivisorFiniteFlat_of_boundary_unit z (a ≫ toSpec R ι) j hcover T s0
  · exact sectionDivisorFiniteFlat_of_boundary_unit z (a ≫ toSpec R ι) j hcover T t0
end AlgebraicGeometry.Scheme.CoherentGraph
