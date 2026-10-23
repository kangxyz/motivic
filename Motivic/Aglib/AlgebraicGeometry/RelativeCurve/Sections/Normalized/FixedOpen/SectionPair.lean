/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.FixedOpen.Boundary
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateUnitOnAffineSource
/-! # Actual psi section pairs on the entire fixed affine source -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ Spec (.of (Polynomial k)))
  [IsOpenImmersion a] (B : Type u) [CommRing B] (z : Polynomial k →+* B)
  (h : Disjoint (Set.range a) (Set.range (Hom.boundaryCoordinateMap k B z)))

/-- The actual unit is chosen with its two prescribed component equations. -/
def fixedBoundaryUnit : SheafOfModules.unit (fixedBoundary k p a B z).ringCatSheaf ≅
    SheafOfModules.unit (fixedBoundary k p a B z).ringCatSheaf :=
  Classical.choose (Hom.exists_affineSourceBoundaryUnit k B z a h (fixedInfinity k p a))

theorem fixedBoundaryUnit_infinity :
    (Modules.restrictFunctor (coprod.inl : fixedInfinity k p a ⟶ fixedBoundary k p a B z)).map
      (fixedBoundaryUnit k p a B z h).hom = 𝟙 _ :=
  (Classical.choose_spec
    (Hom.exists_affineSourceBoundaryUnit k B z a h (fixedInfinity k p a))).1

theorem fixedBoundaryUnit_coordinate :
    (Modules.restrictFunctor (coprod.inr : fixedZero k a B z ⟶ fixedBoundary k p a B z)).map
      (fixedBoundaryUnit k p a B z h).hom ≫ (restrictUnitIso _).hom =
      (restrictUnitIso _).hom ≫ Hom.boundaryCoordinateEndomorphism k B z
        (Hom.boundaryProductMap (Hom.boundaryLineProjection k) a
          (Hom.boundaryCoordinateMap k B z)) :=
  (Classical.choose_spec
    (Hom.exists_affineSourceBoundaryUnit k B z a h (fixedInfinity k p a))).2

/-- The finite projective map over the unchanged original affine source. -/
def fixedProjectiveMap : fixedAmbient k p a ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  ConstantCurve.actualToProjectiveSpace (a ≫ Hom.boundaryLineProjection k)
    (ULift.{u} (Fin 2)) (toProjectiveLine k p)

/-- Original etale data, with the full finite boundary, constructs both actual psi lifts.
The numerator has the original coordinate ratio and the denominator has the same unit value.
Neither the source nor the boundary is replaced by a principal open or its reduction. -/
theorem exists_actualFixedOpenSectionPair [IsNoetherianRing R]
    [IsClosedImmersion (Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)]
    (s : Spec (.of B) ⟶ Y)
    (hs : s ≫ p = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) p (Hom.boundaryCoordinateMap k B z)) :
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
        IsIso ((pullbackUnitIso zD).inv ≫ (Modules.pullback zD).map t) := by
  have : IsClosedImmersion s := MorphismProperty.of_isPullback H.flip inferInstance
  have := fixedBoundary_closed k p a B z s hs
  let aP := fixedProjectiveMap k p a
  have : IsFinite aP := inferInstanceAs (IsFinite (ConstantCurve.actualToProjectiveSpace _ _ _))
  have : IsLocallyNoetherian (fixedAmbient k p a) := LocallyOfFiniteType.isLocallyNoetherian aP
  let O := SheafOfModules.unit (fixedAmbient k p a).ringCatSheaf
  have hO : Invertible.IsLocallyRankOne (fixedAmbient k p a) O :=
    Invertible.isLocallyRankOne_of_iso _
      (CategoryTheory.Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => O))
      (Invertible.trivialLineBundle (fixedAmbient k p a)).property
  have := Invertible.finiteLocallyFree_of_isLocallyRankOne O hO
  let g := fixedFieldBoundaryMap k p B s ≫ toProjectiveLine k p
  have : IsFinite (g ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin 2))) :=
    fixedFieldBoundary_finite k p B z s hs
  have ha : (fixedBoundaryMap k p a B z s hs ≫ aP) ≫
      ProjectiveSpace.map (ConstantCurve.coefficientMap (a ≫ Hom.boundaryLineProjection k))
        (ULift.{u} (Fin 2)) = fixedBoundaryToField k p a B z ≫ g := by
    dsimp only [aP, fixedProjectiveMap]
    rw [Category.assoc, ConstantCurve.actualToProjectiveSpace_map]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ toProjectiveLine k p)
      (fixedBoundaryToField_fac k p a B z s hs)
  let zD := fixedBoundaryMap k p a B z s hs
  let eM := pullbackUnitIso zD ≪≫ (fixedBoundaryUnit k p a B z h).symm
  obtain ⟨N, hN⟩ := CoherentGraph.exists_fixedField_boundary_section_maps k R
    (ConstantCurve.coefficientMap (a ≫ Hom.boundaryLineProjection k))
    (ULift.{u} (Fin 2)) 1 Equiv.ulift aP zD g (fixedBoundaryToField k p a B z) ha O O
    (coherent_of_finiteLocallyFree _) (coherent_of_finiteLocallyFree _) eM (pullbackUnitIso zD)
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨n, t, hn, ht, hIn, hIt⟩ := hN d hd
  refine ⟨_, inferInstance, n, t, hn, ?_, hIn, hIt⟩
  erw [Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] at ht
  exact ht
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
