module
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.AffineSourceDivisorPairs
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.SectionDivisorBaseIso
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.NormalizedDivisorPairs
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.NormalizedScalarDivisorPairs
/-! # Direct unchanged-source Serre divisor consumers -/
set_option linter.hashCommand false
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpace Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
  {Y C W U : Scheme.{u}} [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)]
  (b : Y ⟶ Spec (.of R)) (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  [IsLocallyNoetherian (pullback b (f ≫ toSpec R ι))]
  (z : W ⟶ pullback b (f ≫ toSpec R ι)) [IsClosedImmersion z]
  (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor W
    ((Modules.pullback z).obj ((Modules.pullback
      (ConstantCurve.affineSourceToProjectiveSpace R ι b f)).obj
        (twistingSheaf Γ(Y, ⊤) ι (d : ℤ))))).obj
    ((Modules.pullback z).obj
      (SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf)) ≅
        SheafOfModules.unit W.ringCatSheaf)
  (j : U ⟶ pullback b (f ≫ toSpec R ι)) [IsOpenImmersion j] [U.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ pullback.fst b (f ≫ toSpec R ι))]
  (hcover : ∀ x : (Limits.pullback b (f ≫ toSpec R ι) : Scheme.{u}),
    x ∈ Set.range j ∨ x ∈ Set.range z)

include n e eQ hcover in
example
    (M : LineBundle (pullback b (f ≫ toSpec R ι)))
    (E : (Modules.pullback z).obj M.val ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let T := pullbackLineBundle (ConstantCurve.affineSourceToProjectiveSpace R ι b f)
        (twistingLineBundle Γ(Y, ⊤) ι (d : ℤ))
      ∃ s : SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf ⟶
        (tensorLineBundle _ T M).val,
      ∃ t : SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf ⟶ T.val,
        pullbackSectionMap z s ≫ pullbackTensorMap z T.val M.val =
          tensorUnitSection (pullbackSectionMap z t) E.inv ∧
        IsIso (pullbackSectionMap z s) ∧ IsIso (pullbackSectionMap z t) ∧
        SectionDivisorFiniteFlat (pullback.fst b (f ≫ toSpec R ι)) j
          (tensorLineBundle _ T M) s ∧
        SectionDivisorFiniteFlat (pullback.fst b (f ≫ toSpec R ι)) j T t :=
  exists_affineSource_normalized_divisor_pair R ι n e b f z eQ j hcover M E
#print axioms exists_affineSource_normalized_divisor_pair
include n e eQ hcover in
example
    (E : SheafOfModules.unit W.ringCatSheaf ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let T := pullbackLineBundle (ConstantCurve.affineSourceToProjectiveSpace R ι b f)
        (twistingLineBundle Γ(Y, ⊤) ι (d : ℤ))
      ∃ s t : SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf ⟶ T.val,
        pullbackSectionMap z s = E.hom ≫ pullbackSectionMap z t ∧
        IsIso (pullbackSectionMap z s) ∧ IsIso (pullbackSectionMap z t) ∧
        SectionDivisorFiniteFlat (pullback.fst b (f ≫ toSpec R ι)) j T s ∧
        SectionDivisorFiniteFlat (pullback.fst b (f ≫ toSpec R ι)) j T t :=
  exists_affineSource_scalar_divisor_pair R ι n e b f z eQ j hcover E
#print axioms exists_affineSource_scalar_divisor_pair
end AlgebraicGeometry.Scheme.CoherentGraph
