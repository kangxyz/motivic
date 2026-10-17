/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleCoordinateNaturality

/-! # The coordinate difference is a unit on the retained open times the full boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- A flat restriction disjoint from a closed subscheme makes its original ideal map a unit. -/
theorem pullbackIdealInclusion_isIso_of_disjoint {D X W : Scheme.{u}}
    (i : D ⟶ X) [IsClosedImmersion i] [(idealModule i).IsQuasicoherent]
    (b : W ⟶ X) [Flat b] (h : Disjoint (Set.range i) (Set.range b)) :
    IsIso (Modules.Hom.pullbackToUnit (idealInclusion i) b) := by
  have : IsEmpty (pullback (C := Scheme) i b) := Scheme.isEmpty_pullback i b h
  have := idealInclusion_isIso_of_isEmpty (pullback.snd i b)
  have := idealPullbackMap_isIso_of_flat_ambient i (pullback.snd i b) b
    (pullback.fst i b) pullback.condition (IsPullback.of_hasPullback i b)
  change IsIso ((Scheme.Modules.pullback b).map (idealInclusion i) ≫
    SheafOfModules.pullbackObjUnitToUnit b.toRingCatSheafHom)
  rw [← idealPullbackMap_inclusion i (pullback.snd i b) b (pullback.fst i b) pullback.condition]
  infer_instance

/-- Actual unit endomorphism pullback, with the original structure-module comparison. -/
def unitEndomorphismPullback {X W : Scheme.{u}} (f : W ⟶ X)
    (r : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SheafOfModules.unit W.ringCatSheaf ⟶ SheafOfModules.unit W.ringCatSheaf :=
  (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map r ≫ (pullbackUnitIso f).hom

/-- Pullback of the coordinate endomorphism respects actual composition literally. -/
theorem unitEndomorphismPullback_comp {X W V : Scheme.{u}} (f : V ⟶ W) (g : W ⟶ X)
    (r : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    unitEndomorphismPullback f (unitEndomorphismPullback g r) =
      unitEndomorphismPullback (f ≫ g) r := by
  have hu := pullbackUnitIso_comp f g
  have hi : (pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) =
        (pullbackUnitIso (f ≫ g)).inv := by
    apply (cancel_mono (pullbackUnitIso (f ≫ g)).hom).mp
    simp only [Category.assoc, hu]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    simp
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality r
  dsimp only [Functor.comp_map] at hn
  unfold unitEndomorphismPullback
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← hu, ← Category.assoc ((Scheme.Modules.pullback f).map
    ((Scheme.Modules.pullback g).map r)), hn]
  simp only [Category.assoc]
  simpa only [Category.assoc] using congrArg (fun k =>
    k ≫ (Scheme.Modules.pullback (f ≫ g)).map r ≫ (pullbackUnitIso (f ≫ g)).hom) hi

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)

/-- The literal pulled coordinate endomorphism of the structure module. -/
def boundaryCoordinateEndomorphism {W : Scheme.{u}}
    (b : W ⟶ pullback (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)) :
    SheafOfModules.unit W.ringCatSheaf ⟶ SheafOfModules.unit W.ringCatSheaf :=
  (pullbackUnitIso b).inv ≫ (Scheme.Modules.pullback b).map
    ((boundaryCoordinateIdealIso R B z).hom ≫
      idealInclusion (boundaryGraphTarget (boundaryLineProjection R)
        (boundaryCoordinateMap R B z))) ≫ (pullbackUnitIso b).hom

/-- The exact coordinate ratio commutes with all further base changes. -/
theorem boundaryCoordinateEndomorphism_comp {W V : Scheme.{u}} (a : V ⟶ W)
    (b : W ⟶ pullback (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)) :
    boundaryCoordinateEndomorphism R B z (a ≫ b) =
      unitEndomorphismPullback a (boundaryCoordinateEndomorphism R B z b) :=
  (unitEndomorphismPullback_comp a b _).symm

/-- Any actual factorization through U × Z gives the literal pulled ratio, not just
an isomorphism class of its trivialization. -/
theorem boundaryCoordinateEndomorphism_of_factor {W V : Scheme.{u}}
    (a : V ⟶ W) (b : W ⟶ pullback (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R))
    (c : V ⟶ pullback (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)) (h : a ≫ b = c) :
    boundaryCoordinateEndomorphism R B z c =
      unitEndomorphismPullback a (boundaryCoordinateEndomorphism R B z b) := by
  rw [← h, boundaryCoordinateEndomorphism_comp]

/-- Disjointness proves invertibility of the exact coordinate, including nilpotents of B. -/
theorem boundaryCoordinateEndomorphism_isIso {W : Scheme.{u}}
    (b : W ⟶ pullback (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)) [Flat b]
    (h : Disjoint (Set.range (boundaryGraphTarget (boundaryLineProjection R)
      (boundaryCoordinateMap R B z))) (Set.range b)) :
    IsIso (boundaryCoordinateEndomorphism R B z b) := by
  let i := boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z)
  let := Scheme.Modules.unit_isLocallyFree (pullback (boundaryLineProjection R)
    (boundaryCoordinateMap R B z ≫ boundaryLineProjection R))
  have : (idealModule i).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso (boundaryCoordinateIdealIso R B z) inferInstance
  have := pullbackIdealInclusion_isIso_of_disjoint i b h
  unfold boundaryCoordinateEndomorphism
  rw [Functor.map_comp]
  change IsIso ((pullbackUnitIso b).inv ≫
    (Scheme.Modules.pullback b).map (boundaryCoordinateIdealIso R B z).hom ≫
    Modules.Hom.pullbackToUnit (idealInclusion i) b)
  infer_instance

/-- The retained open times Z misses the entire coordinate graph. -/
theorem coordinateGraph_disjoint_openProduct
    (U : (Spec (.of R[X])).Opens)
    (hU : Disjoint (U : Set (Spec (.of R[X]))) (Set.range (boundaryCoordinateMap R B z))) :
    Disjoint (Set.range (boundaryGraphTarget (boundaryLineProjection R)
      (boundaryCoordinateMap R B z)))
      (Set.range (boundaryProductMap (boundaryLineProjection R) U.ι
        (boundaryCoordinateMap R B z))) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨b, rfl⟩ ⟨a, ha⟩
  have he := congrArg (fun v => (pullback.fst (boundaryLineProjection R)
    (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)) v) ha
  have hleft : (pullback.fst (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R))
        (boundaryProductMap (boundaryLineProjection R) U.ι (boundaryCoordinateMap R B z) a) =
      U.ι (pullback.fst (U.ι ≫ boundaryLineProjection R)
        (boundaryCoordinateMap R B z ≫ boundaryLineProjection R) a) := by
    change (boundaryProductMap (boundaryLineProjection R) U.ι (boundaryCoordinateMap R B z) ≫
      pullback.fst _ _) a = _
    rw [boundaryProductMap, pullback.lift_fst]
    rfl
  have hright : (pullback.fst (boundaryLineProjection R)
      (boundaryCoordinateMap R B z ≫ boundaryLineProjection R))
      (boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z) b) =
        boundaryCoordinateMap R B z b := by
    change (boundaryGraphTarget (boundaryLineProjection R) (boundaryCoordinateMap R B z) ≫
      pullback.fst _ _) b = _
    rw [boundaryGraphTarget, pullback.lift_fst]
  exact Set.disjoint_left.mp hU (pullback.fst (U.ι ≫ boundaryLineProjection R)
        (boundaryCoordinateMap R B z ≫ boundaryLineProjection R) a).property
    ⟨b, (hleft.symm.trans (he.trans hright)).symm⟩

/-- The exact coordinate ratio is an actual structure-module automorphism on U × Z. -/
theorem boundaryCoordinateEndomorphism_open_isIso
    (U : (Spec (.of R[X])).Opens)
    (hU : Disjoint (U : Set (Spec (.of R[X]))) (Set.range (boundaryCoordinateMap R B z))) :
    IsIso (boundaryCoordinateEndomorphism R B z
      (boundaryProductMap (boundaryLineProjection R) U.ι (boundaryCoordinateMap R B z))) :=
  boundaryCoordinateEndomorphism_isIso R B z _ (coordinateGraph_disjoint_openProduct R B z U hU)

/-- The canonical compactification section has exactly the pulled coordinate on the
full original Z boundary, including the actual product comparison. -/
theorem compactificationBoundaryDivisorIso_coordinate
    {C Y : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
    (j : Y ⟶ C) [IsOpenImmersion j] (p : Y ⟶ Spec (.of R[X])) [Flat p]
    (hq : j ≫ q = p ≫ boundaryLineProjection R)
    (s : Spec (.of B) ⟶ Y) (h : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z))
    (hI : Invertible.IsLocallyRankOne (pullback (j ≫ q) q)
      (idealModule (compactificationGraph q j))) :
    let eP : pullback (j ≫ q) (s ≫ j ≫ q) ≅
        pullback (p ≫ boundaryLineProjection R)
          (boundaryCoordinateMap R B z ≫ boundaryLineProjection R) :=
      pullback.congrHom hq (by rw [hq, ← Category.assoc, h])
    pullbackCanonicalDualHom (graphBoundaryRestriction q j s)
        ⟨idealModule (compactificationGraph q j), hI⟩
        (idealInclusion (compactificationGraph q j)) ≫
      (compactificationBoundaryDivisorIso R B z q j p hq s h H hI).hom =
      (pullbackUnitIso eP.hom).inv ≫ (Scheme.Modules.pullback eP.hom).map
        (boundaryCoordinateEndomorphism R B z
          (boundaryProductMap (boundaryLineProjection R) p (boundaryCoordinateMap R B z))) ≫
        (pullbackUnitIso eP.hom).hom := by
  dsimp only
  rw [compactificationBoundaryDivisorIso, dualBoundaryTrivialization_canonical,
    compactificationBoundaryIdealIso_coordinate, neighborhoodBoundaryIdealIso_coordinate]
  rfl

end AlgebraicGeometry.Scheme.Hom
