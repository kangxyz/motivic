module
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.DivisorPairs.Normalized
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.DivisorPairs.NormalizedScalar
/-! # Normalized lambda and psi producers retain actual whole finite-flat zeros -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
example
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
    (M : LineBundle C)
    (E : (Modules.pullback z).obj M.val ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let T := pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))
      ∃ s : SheafOfModules.unit C.ringCatSheaf ⟶ (tensorLineBundle C T M).val,
      ∃ t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val,
        pullbackSectionMap z s ≫ pullbackTensorMap z T.val M.val =
          tensorUnitSection (pullbackSectionMap z t) E.inv ∧
        IsIso (pullbackSectionMap z s) ∧ IsIso (pullbackSectionMap z t) ∧
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j (tensorLineBundle C T M) s ∧
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j T t :=
  exists_normalized_boundary_divisor_pair R ι n e a z eQ j hcover M E
#print axioms exists_normalized_boundary_divisor_pair
example
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
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j T t :=
  exists_normalized_scalar_divisor_pair R ι n e a z eQ j hcover E
#print axioms exists_normalized_scalar_divisor_pair
end AlgebraicGeometry.Scheme.CoherentGraph
