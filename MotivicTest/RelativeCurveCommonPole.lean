module
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.PoleFiniteFlat
/-! # Actual relative pole divisor, retaining all scheme multiplicities -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B Z C D V : Scheme.{u}} [IsAffine S] [IsAffine B] [IsAffine V]
  (q : X ⟶ S) (π : C ⟶ S) [IsProper π] (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C)


example
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a ≫ q) π))
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) bS)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)] :
    let i := retainedProductInclusion (commonProjection π j α) π v
    let f := Hom.pullbackToUnit
      (mixedProductFunctional (commonToLambda π j α)
        (commonToPsi q π j p hq a α β h) T N bS dS) i
    IsFinite (Hom.zeroInclusion f ≫ pullback.fst (commonProjection π j α) (v ≫ π)) ∧
      Mono f ∧ Flat (Hom.zeroInclusion f ≫ pullback.fst (commonProjection π j α) (v ≫ π)) :=
  commonPole_finite_mono_flat q π j p hq a α β h z s hs d v hc T N bS dS

#print axioms commonPole_finite_mono_flat
end AlgebraicGeometry.Scheme.RelativeCurvePencil
