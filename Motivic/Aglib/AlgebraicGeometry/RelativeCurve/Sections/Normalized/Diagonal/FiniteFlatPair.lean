/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.Diagonal.Divisors

/-! # Original étale geometry produces the finite-flat λ section pair -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

def actualUnitBundle (X : Scheme.{u}) : LineBundle X :=
  ⟨SheafOfModules.unit X.ringCatSheaf,
    isLocallyRankOne_of_iso X
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
      (trivialLineBundle X).property⟩

variable (k : Type u) [Field k] {Y S : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]

def diagonalTwistBundle {R : Type u} [CommRing R] (r : Spec (.of R) ⟶ Y) (d : ℕ) :=
  pullbackLineBundle (diagonalProjectiveMap k p r)
    (ProjectiveSpace.twistingLineBundle R (ULift.{u} (Fin 2)) (d : ℤ))

/-- All properties concern the original whole zero scheme on the original overlap product. -/
def RetainedSectionFiniteFlat (r : S ⟶ Y) (U : (Spec (.of (Polynomial k))).Opens)
    (L : LineBundle (diagonalAmbient k p r))
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ L.val) : Prop :=
  let q := (r ≫ inclusion k p) ≫ projection k p
  let j := constantRetainedInclusion k p U q
  let f := Hom.pullbackToUnit (sectionDualFunctional _ L a) j
  IsFinite (Hom.zeroInclusion f ≫ j ≫ pullback.fst q (projection k p)) ∧
    Mono f ∧ Flat (Hom.zeroInclusion f ≫ j ≫ pullback.fst q (projection k p))

/-- The actual λ pair retains its two prescribed boundary equations and has finite flat zeros. -/
theorem exists_actualDiagonalFiniteFlatSectionPair {R : Type u} [CommRing R] [IsNoetherianRing R]
    (r : Spec (.of R) ⟶ Y) [IsOpenImmersion r]
    (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    [IsClosedImmersion (Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)]
    (s : Spec (.of B) ⟶ Spec (.of R))
    (hs : s ≫ (r ≫ p) = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z))
    (U : (Spec (.of (Polynomial k))).Opens)
    (H0 : IsPullback (s ≫ r) (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :
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
        IsIso ((pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map b) ∧
        RetainedSectionFiniteFlat k p r U
          (tensorLineBundle C (diagonalTwistBundle k p r d) (actualDivisorLineBundle k p r)) a ∧
        RetainedSectionFiniteFlat k p r U
          (tensorLineBundle C (diagonalTwistBundle k p r d) (actualUnitBundle C)) b := by
  obtain ⟨N, hN⟩ := exists_actualDiagonalSectionPair k p r B z s hs H
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨u, hu, a, b, ha, hb, hIa, hIb⟩ := hN d hd
  have : IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) a) := hIa
  have : IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) b) := hIb
  refine ⟨u, hu, a, b, ha, hb, hIa, hIb, ?_, ?_⟩
  · exact actualSectionDivisor_finite_mono_flat k p r s U
      (Hom.boundaryCoordinateMap k B z) H0 hz
      (tensorLineBundle _ (diagonalTwistBundle k p r d) (actualDivisorLineBundle k p r)) a
  · exact actualSectionDivisor_finite_mono_flat k p r s U
      (Hom.boundaryCoordinateMap k B z) H0 hz
      (tensorLineBundle _ (diagonalTwistBundle k p r d) (actualUnitBundle _)) b
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
