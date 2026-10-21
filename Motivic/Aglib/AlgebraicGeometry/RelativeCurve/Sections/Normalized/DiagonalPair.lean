/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.Diagonal.FiniteFlatPair
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairNormalization

/-! # The actual normalized λ pair in the signed-pencil domain -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]

/-- Actual original geometry constructs normalized numerator and denominator, their exact
prescribed frame relation, and both whole regular finite-flat zero divisors. -/
theorem exists_actualNormalizedDiagonalPair {R : Type u} [CommRing R] [IsNoetherianRing R]
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
    let zD := diagonalBoundaryMap k p r s
    let M := actualDivisorLineBundle k p r
    let E := actualBoundaryIso k p r B z s hs H
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      let T := diagonalTwistBundle k p r d
      ∃ a : SheafOfModules.unit C.ringCatSheaf ⟶ (tensorLineBundle C T M).val,
      ∃ b : SheafOfModules.unit C.ringCatSheaf ⟶ T.val,
        pullbackSectionMap zD a ≫ pullbackTensorMap zD T.val M.val =
          tensorUnitSection (pullbackSectionMap zD b) E.inv ∧
        IsIso (pullbackSectionMap zD a) ∧ IsIso (pullbackSectionMap zD b) ∧
        RetainedSectionFiniteFlat k p r U (tensorLineBundle C T M) a ∧
        RetainedSectionFiniteFlat k p r U T b := by
  obtain ⟨N, hN⟩ := exists_actualDiagonalSectionPair k p r B z s hs H
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨u, hu, a, b, ha, hb, hIa, hIb⟩ := hN d hd
  let T := diagonalTwistBundle k p r d
  let b0 := rightNormalizeSection T.val b
  have : IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) a) := hIa
  have : IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) b) := hIb
  have hb0 : IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) b0) := by
    change IsIso ((pullbackUnitIso _).inv ≫ (Modules.pullback _).map
      (b ≫ (tensorSheafRightUnit _ T.val).hom))
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
    infer_instance
  refine ⟨a, b0, ?_, hIa, hb0, ?_, ?_⟩
  · exact prescribedPair_normalized (diagonalBoundaryMap k p r s) T.val
      (actualDivisorLineBundle k p r).val (actualBoundaryIso k p r B z s hs H) a b u ha hb
  · exact actualSectionDivisor_finite_mono_flat k p r s U
      (Hom.boundaryCoordinateMap k B z) H0 hz
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)) a
  · exact actualSectionDivisor_finite_mono_flat k p r s U
      (Hom.boundaryCoordinateMap k B z) H0 hz T b0
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
