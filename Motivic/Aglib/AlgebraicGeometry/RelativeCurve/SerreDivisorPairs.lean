module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.PrescribedTwistSectionMaps
public import Motivic.Aglib.AlgebraicGeometry.SectionDualDivisor
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Semilocal
/-! # Actual finite-flat divisors produced by prescribed relative Serre sections -/
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
/-- All properties refer to the original whole zero scheme and its literal restriction. -/
def SectionDivisorFiniteFlat {C U S : Scheme.{u}} (q : C ⟶ S) (j : U ⟶ C)
    (L : LineBundle C) (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val) : Prop :=
  let f := sectionDualFunctional C L s
  IsFinite (Hom.zeroInclusion f ≫ q) ∧ Flat (Hom.zeroInclusion f ≫ q) ∧
    Set.range (Hom.zeroInclusion f) ⊆ Set.range j ∧
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit f j) ≫ j ≫ q) ∧
    Mono (Hom.pullbackToUnit f j) ∧
    Flat (Hom.zeroInclusion (Hom.pullbackToUnit f j) ≫ j ≫ q)

/-- Genuine boundary units produce both whole and retained finite-flat zero schemes. -/
theorem sectionDivisorFiniteFlat_of_boundary_unit {C W U S : Scheme.{u}}
    (z : W ⟶ C) (q : C ⟶ S) [IsProper q] [IsAffine S]
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range z)
    (L : LineBundle C) (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap z s)] : SectionDivisorFiniteFlat q j L s := by
  obtain ⟨hf, ht⟩ := sectionDualFunctional_whole_zero_finite_flat z q j L s hcover
  exact ⟨hf, ht, sectionDualFunctional_zero_range z j L s hcover,
    sectionDualFunctional_finite_mono_flat_on_open z q j L s hcover⟩

/-- Serre constructs the pair; properness and smoothness on the retained open construct
its finite-flat zero divisors. No zero-family, regularity, or cycle premise is supplied. -/
theorem exists_prescribed_boundary_divisor_pair
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
    (M N : LineBundle C)
    (eM : (Modules.pullback z).obj M.val ≅ SheafOfModules.unit W.ringCatSheaf)
    (eN : (Modules.pullback z).obj N.val ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
      let T := moduleTensorLeftFunctor W ((Modules.pullback z).obj L)
      let eQ := eQ d
      ∃ s : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj M.val,
      ∃ t : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj N.val,
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map s ≫ pullbackTensorMap z L M.val =
          eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eM.inv) ∧
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map t ≫ pullbackTensorMap z L N.val =
          eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eN.inv) ∧
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map s) ∧
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map t) ∧
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j
          (tensorLineBundle C (pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))) M) s ∧
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j
          (tensorLineBundle C (pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))) N) t := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  have : IsProper (a ≫ toSpec R ι) := inferInstance
  have := finiteLocallyFree_of_isLocallyRankOne M.val M.property
  have := finiteLocallyFree_of_isLocallyRankOne N.val N.property
  obtain ⟨B, hB⟩ := exists_prescribed_twist_boundary_section_maps R ι n e a z eQ
    M.val N.val (coherent_of_finiteLocallyFree _) (coherent_of_finiteLocallyFree _) eM eN
  refine ⟨B, fun d hd => ?_⟩
  obtain ⟨s, t, hs, ht, hsi, hti⟩ := hB d hd
  have : IsIso (pullbackSectionMap z s) := hsi
  have : IsIso (pullbackSectionMap z t) := hti
  have : SmoothOfRelativeDimension 1 (j ≫ (a ≫ toSpec R ι)) := inferInstance
  refine ⟨s, t, hs, ht, hsi, hti, ?_, ?_⟩
  · exact sectionDivisorFiniteFlat_of_boundary_unit z (a ≫ toSpec R ι) j hcover
      (tensorLineBundle C (pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))) M) s
  · exact sectionDivisorFiniteFlat_of_boundary_unit z (a ≫ toSpec R ι) j hcover
      (tensorLineBundle C (pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))) N) t
end AlgebraicGeometry.Scheme.CoherentGraph
