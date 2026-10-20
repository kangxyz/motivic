/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.GraphBoundaryRestriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit

/-! # Specified coordinate trivialization on an étale neighborhood's full boundary -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Polynomial

universe u
namespace AlgebraicGeometry.Scheme.Hom

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)

/-- The projection from the affine line over `R` to `Spec R`. -/
abbrev boundaryLineProjection := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))
/-- The affine scheme morphism induced by the boundary coordinate homomorphism `z`. -/
abbrev boundaryCoordinateMap := Spec.map (CommRingCat.ofHom z)

/-- Exact product identification for the original composed boundary structure map. -/
def boundaryCoordinateProductIso :
    pullback (boundaryLineProjection R) (Spec.map (CommRingCat.ofHom (z.comp C))) ≅
      pullback (boundaryLineProjection R) (boundaryCoordinateMap R B z ≫
        boundaryLineProjection R) :=
  pullback.congrHom rfl (by rw [← Spec.map_comp]; rfl)

@[reassoc] theorem affineCoordinateGraph_product :
    affineCoordinateGraph R z ≫ (boundaryCoordinateProductIso R B z).hom =
      boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z) := by
  apply pullback.hom_ext <;>
    simp [affineCoordinateGraph, boundaryCoordinateProductIso, boundaryGraphTarget,
      pullback.congrHom]

/-- The actual target boundary graph ideal is trivialized by the coordinate difference. -/
def boundaryCoordinateIdealIso :
    SheafOfModules.unit (pullback (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z)) := by
  let e := boundaryCoordinateProductIso R B z
  have h : 𝟙 (Spec (.of B)) ≫ affineCoordinateGraph R z =
      boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z) ≫ e.inv := by
    rw [← affineCoordinateGraph_product]
    simp [e]
  let v := idealPullbackMap (affineCoordinateGraph R z)
    (boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z))
    e.inv (𝟙 _) h
  have : IsIso v := idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact (pullbackUnitIso e.inv).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso (affineCoordinateGraphIdealIso R z) ≪≫ asIso v

/-- The coordinate graph is closed because it is the actual evaluation graph. -/
instance boundaryCoordinateGraph_isClosedImmersion :
    IsClosedImmersion
      (boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z)) := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (z X)))) :=
    IsClosedImmersion.spec_of_surjective _ (fun b ↦ ⟨C b, by simp⟩)
  rw [← affineCoordinateGraph_product, ← evaluation_coordinateProductIso R z]
  infer_instance

/-- The original boundary graph of a flat neighborhood is globally trivialized.
The full Cartesian boundary condition, including nilpotents, is retained. -/
def neighborhoodBoundaryIdealIso {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of R[X])) [Flat p] (s : Spec (.of B) ⟶ Y)
    (h : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z)) :
    SheafOfModules.unit (pullback (p ≫ boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)).ringCatSheaf ≅
    idealModule (boundaryGraphSource (boundaryLineProjection R) p
      (boundaryCoordinateMap R B z) s h) := by
  let e := boundaryCoordinateIdealIso R B z
  let := Scheme.Modules.unit_isLocallyFree (pullback (boundaryLineProjection R)
    (boundaryCoordinateMap R B z ≫ boundaryLineProjection R))
  have : (idealModule (boundaryGraphTarget (boundaryLineProjection R)
      (boundaryCoordinateMap R B z))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso e inferInstance
  have : IsClosedImmersion (boundaryGraphSource (boundaryLineProjection R) p
      (boundaryCoordinateMap R B z) s h) :=
    MorphismProperty.of_isPullback (boundaryGraph_isPullback _ _ _ _ _ H) inferInstance
  let b := boundaryProductMap (boundaryLineProjection R) p (boundaryCoordinateMap R B z)
  let v := idealPullbackMap
    (boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z))
    (boundaryGraphSource (boundaryLineProjection R) p (boundaryCoordinateMap R B z) s h)
    b (𝟙 _) (boundaryGraph_isPullback _ _ _ _ _ H).w
  have : IsIso v := boundaryGraph_idealPullbackMap_isIso _ _ _ _ _ H
  exact (pullbackUnitIso b).symm ≪≫ (Scheme.Modules.pullback b).mapIso e ≪≫ asIso v

/-- A specified boundary trivialization of the ideal induces the actual dual
(divisor bundle) boundary trivialization through canonical evaluation. -/
def dualBoundaryTrivialization {X W : Scheme.{u}} (f : W ⟶ X)
    (L : Invertible.LineBundle X)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj L.val) :
    (Scheme.Modules.pullback f).obj (Invertible.dualLineBundle X L).val ≅
      SheafOfModules.unit W.ringCatSheaf :=
  by
    let D := (Scheme.Modules.pullback f).obj (Invertible.dualLineBundle X L).val
    let I := (Scheme.Modules.pullback f).obj L.val
    let e₁ : D ≅ tensorSheaf W D (SheafOfModules.unit W.ringCatSheaf) :=
      ((SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf).app D).symm
    let e₂ : tensorSheaf W D (SheafOfModules.unit W.ringCatSheaf) ≅ tensorSheaf W D I :=
      tensorSheafIso W (Iso.refl D) e
    let e₃ : tensorSheaf W D I ≅ (Scheme.Modules.pullback f).obj
        (tensorSheaf X (Invertible.dualLineBundle X L).val L.val) :=
      (Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso f
        (Invertible.dualLineBundle X L) L).symm
    exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫
      (Scheme.Modules.pullback f).mapIso (Invertible.dualEvaluationIso X L) ≪≫ pullbackUnitIso f

/-- The original compactification diagonal ideal has its specified coordinate
trivialization on the full affine boundary. Neither the source nor the boundary is shrunk. -/
def compactificationBoundaryIdealIso {C Y : Scheme.{u}}
    (q : C ⟶ Spec (.of R)) [IsSeparated q] (j : Y ⟶ C) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of R[X])) [Flat p]
    (hq : j ≫ q = p ≫ boundaryLineProjection R)
    (s : Spec (.of B) ⟶ Y) (h : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z)) :
    SheafOfModules.unit (pullback (j ≫ q) (s ≫ j ≫ q)).ringCatSheaf ≅
      (Scheme.Modules.pullback (graphBoundaryRestriction q j s)).obj
        (idealModule (compactificationGraph q j)) := by
  let eP : pullback (j ≫ q) (s ≫ j ≫ q) ≅
      pullback (p ≫ boundaryLineProjection R)
        (boundaryCoordinateMap R B z ≫ boundaryLineProjection R) :=
    pullback.congrHom hq (by rw [hq, ← Category.assoc, h])
  have he : 𝟙 (Spec (.of B)) ≫ boundaryGraphSource (boundaryLineProjection R) p
      (boundaryCoordinateMap R B z) s h = restrictedBoundaryGraph q j s ≫ eP.hom := by
    apply pullback.hom_ext <;>
      simp [eP, pullback.congrHom, boundaryGraphSource, restrictedBoundaryGraph]
  let v := idealPullbackMap
    (boundaryGraphSource (boundaryLineProjection R) p (boundaryCoordinateMap R B z) s h)
    (restrictedBoundaryGraph q j s) eP.hom (𝟙 _) he
  have : IsIso v := idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  have : IsClosedImmersion (compactificationGraph q j) := by
    dsimp [compactificationGraph]
    infer_instance
  let w := idealPullbackMap (compactificationGraph q j) (restrictedBoundaryGraph q j s)
    (graphBoundaryRestriction q j s) s (compactificationGraph_boundary_isPullback q j s).w
  have : IsIso w := compactificationGraph_boundaryIdealMap_isIso q j s
  exact (pullbackUnitIso eP.hom).symm ≪≫
    (Scheme.Modules.pullback eP.hom).mapIso (neighborhoodBoundaryIdealIso R B z p s h H) ≪≫
    asIso v ≪≫ (asIso w).symm

/-- The actual divisor line bundle (dual of the original diagonal ideal) carries
the induced coordinate trivialization required by the section producer. -/
def compactificationBoundaryDivisorIso {C Y : Scheme.{u}}
    (q : C ⟶ Spec (.of R)) [IsSeparated q] (j : Y ⟶ C) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of R[X])) [Flat p]
    (hq : j ≫ q = p ≫ boundaryLineProjection R)
    (s : Spec (.of B) ⟶ Y) (h : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z))
    (hI : Invertible.IsLocallyRankOne (pullback (j ≫ q) q)
      (idealModule (compactificationGraph q j))) :
    (Scheme.Modules.pullback (graphBoundaryRestriction q j s)).obj
      (Invertible.dualLineBundle _ ⟨idealModule (compactificationGraph q j), hI⟩).val ≅
        SheafOfModules.unit (pullback (j ≫ q) (s ≫ j ≫ q)).ringCatSheaf :=
  dualBoundaryTrivialization (graphBoundaryRestriction q j s)
    ⟨idealModule (compactificationGraph q j), hI⟩
    (compactificationBoundaryIdealIso R B z q j p hq s h H)

/-- The divisor-boundary trivialization using only the original smooth-open
hypothesis near the graph, with no separate invertible-ideal premise. -/
def compactificationBoundaryDivisorIsoOfSmoothNearGraph {C Y : Scheme.{u}}
    (q : C ⟶ Spec (.of R)) [IsSeparated q] (j : Y ⟶ C) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of R[X])) [Flat p]
    (hq : j ≫ q = p ≫ boundaryLineProjection R)
    (s : Spec (.of B) ⟶ Y) (h : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z))
    (U : (pullback (j ≫ q) q).Opens)
    (hU : Set.range (compactificationGraph q j) ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ pullback.fst (j ≫ q) q)] :=
  compactificationBoundaryDivisorIso R B z q j p hq s h H
    (graph_idealModule_isLocallyRankOne j q U hU)

/-- Deprecated compatibility name for `compactificationBoundaryDivisorIsoOfSmoothNearGraph`. -/
@[deprecated (since := "2026-10-20"), nolint defsWithUnderscore]
alias compactificationBoundaryDivisorIso_of_smooth_near_graph :=
  compactificationBoundaryDivisorIsoOfSmoothNearGraph

end AlgebraicGeometry.Scheme.Hom
