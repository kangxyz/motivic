module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.FixedOpen.Divisors
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.Diagonal.FiniteFlatPair
/-! # The actual fixed-source psi pair with finite flat zero factors -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y A : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]

def fixedTwistBundle {R : Type u} [CommRing R]
    (a : Spec (.of R) ⟶ Spec (.of (Polynomial k))) (d : ℕ) :=
  pullbackLineBundle (fixedProjectiveMap k p a)
    (ProjectiveSpace.twistingLineBundle R (ULift.{u} (Fin 2)) (d : ℤ))

def FixedRetainedSectionFiniteFlat (a : A ⟶ Spec (.of (Polynomial k)))
    (U : (Spec (.of (Polynomial k))).Opens) (L : LineBundle (fixedAmbient k p a))
    (t : SheafOfModules.unit (fixedAmbient k p a).ringCatSheaf ⟶ L.val) : Prop :=
  let q := a ≫ Hom.boundaryLineProjection k
  let j := constantRetainedInclusion k p U q
  let f := Hom.pullbackToUnit (sectionDualFunctional _ L t) j
  IsFinite (Hom.zeroInclusion f ≫ j ≫ pullback.fst q (projection k p)) ∧
    Mono f ∧ Flat (Hom.zeroInclusion f ≫ j ≫ pullback.fst q (projection k p))

variable {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ Spec (.of (Polynomial k)))
  [IsOpenImmersion a] (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (h : Disjoint (Set.range a) (Set.range (Hom.boundaryCoordinateMap k B z)))

/-- Both actual psi factors are finite flat on the original overlap, with exact boundary values. -/
theorem exists_actualFixedOpenFiniteFlatSectionPair [IsNoetherianRing R]
    [IsClosedImmersion (Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)]
    (s : Spec (.of B) ⟶ Y)
    (hs : s ≫ p = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (U : (Spec (.of (Polynomial k))).Opens)
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    let C := fixedAmbient k p a
    let W := fixedBoundary k p a B z
    let zD := fixedBoundaryMap k p a B z s hs
    let O := SheafOfModules.unit C.ringCatSheaf
    let E := fixedBoundaryUnit k p a B z h
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      let L := (Modules.pullback (fixedProjectiveMap k p a)).obj
        (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (d : ℤ))
      let T := moduleTensorLeftFunctor W ((Modules.pullback zD).obj L)
      ∃ u : SheafOfModules.unit W.ringCatSheaf ⟶ T.obj ((Modules.pullback zD).obj O),
      IsIso u ∧
      ∃ n t : O ⟶ (moduleTensorLeftFunctor C L).obj O,
        (pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map n ≫ pullbackTensorMap zD L O =
          u ≫ T.map ((pullbackUnitIso zD).hom ≫ E.hom ≫ (pullbackUnitIso zD).inv) ∧
        (pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map t ≫ pullbackTensorMap zD L O = u ∧
        IsIso ((pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map n) ∧
        IsIso ((pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map t) ∧
        FixedRetainedSectionFiniteFlat k p a U
          (tensorLineBundle C (fixedTwistBundle k p a d) (actualUnitBundle C)) n ∧
        FixedRetainedSectionFiniteFlat k p a U
          (tensorLineBundle C (fixedTwistBundle k p a d) (actualUnitBundle C)) t := by
  obtain ⟨N, hN⟩ := exists_actualFixedOpenSectionPair k p a B z h s hs H
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨u, hu, n, t, hn, ht, hIn, hIt⟩ := hN d hd
  have : IsIso (pullbackSectionMap (fixedBoundaryMap k p a B z s hs) n) := hIn
  have : IsIso (pullbackSectionMap (fixedBoundaryMap k p a B z s hs) t) := hIt
  refine ⟨u, hu, n, t, hn, ht, hIn, hIt, ?_, ?_⟩
  · exact actualFixedSectionDivisor_finite_mono_flat k p a B z s hs U H hz
      (tensorLineBundle _ (fixedTwistBundle k p a d) (actualUnitBundle _)) n
  · exact actualFixedSectionDivisor_finite_mono_flat k p a B z s hs U H hz
      (tensorLineBundle _ (fixedTwistBundle k p a d) (actualUnitBundle _)) t
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
