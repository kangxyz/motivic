/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.TwoOpenCover.Transition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Finite open descent data and its actual equalizer sheaf

This development constructs the genuine finite product/equalizer module sheaf
from actual overlap isomorphisms. The finite local inverse and full descent
proof are developed separately below; the equalizer alone is not an effective
descent theorem and does not construct the actual correspondence Tor datum.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover

open Scheme.Modules _root_.AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover

variable {X : Scheme.{u}} {ι : Type u} [Fintype ι]
  (U : ι → X.Opens) (M : ∀ i, (U i).toScheme.Modules)

/-- The actual overlap restriction isomorphism type. -/
abbrev Transition (i j : ι) :=
  (restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).obj (M i) ≅
    (restrictFunctor (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).obj (M j)

/-- Restriction to a smaller common open, with the literal composite-inclusion comparison. -/
def restrictToOverlapIso {W : X.Opens} {i j : ι} (hi : W ≤ U i) (hj : W ≤ U j) :
    (restrictFunctor (X.homOfLE hi)).obj (M i) ≅
      (restrictFunctor (X.homOfLE (le_inf hi hj))).obj
        ((restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).obj (M i)) :=
  (restrictFunctorCongr (show X.homOfLE hi =
    X.homOfLE (le_inf hi hj) ≫ X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) by
      simp)).app _ ≪≫ (restrictFunctorComp _ _).app _

/-- A given transition restricted to any actual smaller common open. -/
def transitionOn (e : ∀ i j, Transition U M i j) {W : X.Opens} (i j : ι)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    (restrictFunctor (X.homOfLE hi)).obj (M i) ≅
      (restrictFunctor (X.homOfLE hj)).obj (M j) :=
  restrictToOverlapIso U M hi hj ≪≫
    (restrictFunctor (X.homOfLE (le_inf hi hj))).mapIso (e i j) ≪≫
    ((restrictFunctorCongr (show X.homOfLE hj =
      X.homOfLE (le_inf hi hj) ≫ X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) by
        simp)).app _ ≪≫ (restrictFunctorComp _ _).app _).symm

/-- Genuine local descent data: specified overlap maps, their identity law,
and their triple-overlap cocycle after every actual common-open restriction. -/
structure Datum where
  /-- The specified isomorphisms on the actual pairwise intersections. -/
  transition : ∀ i j, Transition U M i j
  identity : ∀ i, transition i i = Iso.refl _
  cocycle : ∀ (W : X.Opens) (i j k : ι) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
    transitionOn U M transition i j hi hj ≪≫ transitionOn U M transition j k hj hk =
      transitionOn U M transition i k hi hk

/-- The genuine finite product of the original open pushforwards. -/
abbrev localProduct : X.Modules := ∏ᶜ fun i => (pushforward (U i).ι).obj (M i)

/-- The first member's actual overlap module, pushed into the ambient scheme. -/
abbrev ambientOverlap (ij : ι × ι) : X.Modules :=
  (pushforward (U ij.1).ι).obj
    (overlapModule (a := X.homOfLE (inf_le_left : U ij.1 ⊓ U ij.2 ≤ U ij.1)) (M ij.1))

/-- The genuine finite product of all pairwise overlap modules. -/
abbrev overlapProduct : X.Modules := ∏ᶜ ambientOverlap U M

/-- The first restriction into every actual pairwise overlap. -/
def firstMap : localProduct U M ⟶ overlapProduct U M :=
  Pi.lift fun ij => Pi.π _ ij.1 ≫
    leftOverlapMap (a := X.homOfLE (inf_le_left : U ij.1 ⊓ U ij.2 ≤ U ij.1))
      (f := (U ij.1).ι) (M ij.1)

/-- The second restriction uses precisely the supplied actual overlap transition. -/
def secondMap (d : Datum U M) : localProduct U M ⟶ overlapProduct U M :=
  Pi.lift fun ij => Pi.π _ ij.2 ≫
    rightOverlapMap (isPullback_opens_inf (U ij.1) (U ij.2))
      (M ij.1) (M ij.2) (d.transition ij.1 ij.2)

/-- The genuine module sheaf of compatible local sections. -/
def glued (d : Datum U M) : X.Modules := equalizer (firstMap U M) (secondMap U M d)

/-- The actual projection to the original local open pushforward. -/
def projection (d : Datum U M) (i : ι) : glued U M d ⟶ (pushforward (U i).ι).obj (M i) :=
  equalizer.ι _ _ ≫ Pi.π _ i

set_option backward.isDefEq.respectTransparency false in
/-- Every pair of projections satisfies the supplied overlap relation. -/
theorem projection_condition (d : Datum U M) (i j : ι) :
    projection U M d i ≫
        leftOverlapMap (a := X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))
          (f := (U i).ι) (M i) =
      projection U M d j ≫ rightOverlapMap (isPullback_opens_inf (U i) (U j))
        (M i) (M j) (d.transition i j) := by
  have h := congrArg (fun φ => φ ≫ Pi.π (ambientOverlap U M) (i, j))
    (equalizer.condition (firstMap U M) (secondMap U M d))
  simpa [firstMap, secondMap, projection, ambientOverlap, Category.assoc] using h

/-- The actual local projection, composed with the original open counit. -/
def localProjection (d : Datum U M) (i : ι) :
    (restrictFunctor (U i).ι).obj (glued U M d) ⟶ M i :=
  (restrictFunctor (U i).ι).map (projection U M d i) ≫
    (restrictAdjunction (U i).ι).counit.app (M i)

/-- The local component determined by the original transition on the actual overlap. -/
def localComponent (d : Datum U M) (i j : ι) :
    M i ⟶ (restrictFunctor (U i).ι).obj ((pushforward (U j).ι).obj (M j)) :=
  (restrictAdjunction (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).unit.app (M i) ≫
    (overlapComparison (isPullback_opens_inf (U i) (U j))
      (M i) (M j) (d.transition i j)).inv

set_option backward.isDefEq.respectTransparency false in
/-- Each pairwise compatibility has its literal first-open adjunction mate. -/
theorem localProjection_unit (d : Datum U M) (i j : ι) :
    localProjection U M d i ≫
        (restrictAdjunction (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).unit.app (M i) =
      (restrictFunctor (U i).ι).map (projection U M d j) ≫
        (overlapComparison (isPullback_opens_inf (U i) (U j))
          (M i) (M j) (d.transition i j)).hom := by
  have hc := congrArg (fun φ => (restrictFunctor (U i).ι).map φ ≫
    (restrictAdjunction (U i).ι).counit.app
      (overlapModule (a := X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (M i)))
        (projection_condition U M d i j)
  simp only [Functor.map_comp, Category.assoc] at hc
  have hr : (restrictFunctor (U i).ι).map
      (rightOverlapMap (isPullback_opens_inf (U i) (U j)) (M i) (M j) (d.transition i j)) ≫
        (restrictAdjunction (U i).ι).counit.app
          (overlapModule (a := X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (M i)) =
      (overlapComparison (isPullback_opens_inf (U i) (U j))
        (M i) (M j) (d.transition i j)).hom :=
    ((restrictAdjunction (U i).ι).homEquiv _ _).symm_apply_apply _
  rw [hr] at hc
  have hn := (restrictAdjunction (U i).ι).counit.naturality
    ((restrictAdjunction (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).unit.app (M i))
  change (restrictFunctor (U i).ι).map
      (leftOverlapMap (a := X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))
        (f := (U i).ι) (M i)) ≫
      (restrictAdjunction (U i).ι).counit.app
        (overlapModule (a := X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (M i)) =
    (restrictAdjunction (U i).ι).counit.app (M i) ≫
      (restrictAdjunction (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).unit.app (M i) at hn
  rw [hn] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- After restriction to one member, its local projection determines every
other original pushforward projection through the supplied transition. -/
theorem localProjection_component (d : Datum U M) (i j : ι) :
    localProjection U M d i ≫ localComponent U M d i j =
      (restrictFunctor (U i).ι).map (projection U M d j) := by
  dsimp only [localComponent]
  rw [← Category.assoc, localProjection_unit, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The actual restricted projection is a monomorphism: all other local
coordinates are determined by it through the prescribed transition maps. -/
instance localProjection_mono (d : Datum U M) (i : ι) : Mono (localProjection U M d i) where
  right_cancellation {Z} x y h := by
    apply (cancel_mono ((restrictFunctor (U i).ι).map
      (equalizer.ι (firstMap U M) (secondMap U M d)))).mp
    apply Fan.IsLimit.hom_ext
      (isLimitOfHasProductOfPreservesLimit (restrictFunctor (U i).ι)
        (fun j => (pushforward (U j).ι).obj (M j)))
    intro j
    change x ≫ (restrictFunctor (U i).ι).map (equalizer.ι _ _) ≫
        (restrictFunctor (U i).ι).map (Pi.π _ j) =
      y ≫ (restrictFunctor (U i).ι).map (equalizer.ι _ _) ≫
        (restrictFunctor (U i).ι).map (Pi.π _ j)
    rw [← Functor.map_comp]
    change x ≫ (restrictFunctor (U i).ι).map (projection U M d j) =
      y ≫ (restrictFunctor (U i).ι).map (projection U M d j)
    rw [← localProjection_component U M d i j]
    simpa only [Category.assoc] using congrArg (fun φ => φ ≫ localComponent U M d i j) h

/-- The finite product cone determined by all actual pairwise transitions. -/
def localProductLift (d : Datum U M) (i : ι) :
    M i ⟶ (restrictFunctor (U i).ι).obj (localProduct U M) :=
  Pi.lift (localComponent U M d i) ≫
    inv (piComparison (restrictFunctor (U i).ι) (fun j => (pushforward (U j).ι).obj (M j)))

set_option backward.isDefEq.respectTransparency false in
/-- Every component of the constructed local product cone is the original overlap map. -/
@[reassoc (attr := simp)] theorem localProductLift_π (d : Datum U M) (i j : ι) :
    localProductLift U M d i ≫ (restrictFunctor (U i).ι).map
      (Pi.π (fun j => (pushforward (U j).ι).obj (M j)) j) = localComponent U M d i j := by
  simp [localProductLift]

set_option backward.isDefEq.respectTransparency false in
/-- The first finite overlap-map component is its original pushed restriction unit. -/
@[reassoc (attr := simp)] theorem firstMap_π (i j : ι) :
    firstMap U M ≫ Pi.π (ambientOverlap U M) (i, j) =
      Pi.π (fun j => (pushforward (U j).ι).obj (M j)) i ≫
        leftOverlapMap (a := X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))
          (f := (U i).ι) (M i) := by
  simp [firstMap, ambientOverlap]

set_option backward.isDefEq.respectTransparency false in
/-- The second finite overlap-map component retains the prescribed transition. -/
@[reassoc (attr := simp)] theorem secondMap_π (d : Datum U M) (i j : ι) :
    secondMap U M d ≫ Pi.π (ambientOverlap U M) (i, j) =
      Pi.π (fun j => (pushforward (U j).ι).obj (M j)) j ≫
        rightOverlapMap (isPullback_opens_inf (U i) (U j)) (M i) (M j) (d.transition i j) := by
  simp [secondMap, ambientOverlap]

/-- The precise triple overlap equality required of the actual local components.
Its derivation from Datum.cocycle is a separate coherence step. -/
def ComponentsCompatible (d : Datum U M) (i : ι) : Prop := ∀ j k,
  localComponent U M d i j ≫ (restrictFunctor (U i).ι).map
      (leftOverlapMap (a := X.homOfLE (inf_le_left : U j ⊓ U k ≤ U j))
        (f := (U j).ι) (M j)) =
    localComponent U M d i k ≫ (restrictFunctor (U i).ι).map
      (rightOverlapMap (isPullback_opens_inf (U j) (U k)) (M j) (M k) (d.transition j k))

set_option backward.isDefEq.respectTransparency false in
/-- A proved actual component cocycle makes the constructed cone equalize both maps. -/
theorem localProductLift_condition (d : Datum U M) (i : ι)
    (hc : ComponentsCompatible U M d i) :
    localProductLift U M d i ≫ (restrictFunctor (U i).ι).map (firstMap U M) =
      localProductLift U M d i ≫ (restrictFunctor (U i).ι).map (secondMap U M d) := by
  apply Fan.IsLimit.hom_ext
    (isLimitOfHasProductOfPreservesLimit (restrictFunctor (U i).ι) (ambientOverlap U M))
  rintro ⟨j, k⟩
  change (localProductLift U M d i ≫ (restrictFunctor (U i).ι).map (firstMap U M)) ≫
      (restrictFunctor (U i).ι).map (Pi.π (ambientOverlap U M) (j, k)) =
    (localProductLift U M d i ≫ (restrictFunctor (U i).ι).map (secondMap U M d)) ≫
      (restrictFunctor (U i).ι).map (Pi.π (ambientOverlap U M) (j, k))
  simp only [Category.assoc]
  rw [← Functor.map_comp, firstMap_π, ← Functor.map_comp, secondMap_π]
  simp only [Functor.map_comp, ← Category.assoc, localProductLift_π]
  exact hc j k

/-- The actual equalizer lift obtained from a proved component cocycle. -/
def localLift (d : Datum U M) (i : ι) (hc : ComponentsCompatible U M d i) :
    M i ⟶ (restrictFunctor (U i).ι).obj (glued U M d) :=
  equalizer.lift (localProductLift U M d i) (localProductLift_condition U M d i hc) ≫
    (PreservesEqualizer.iso (restrictFunctor (U i).ι) (firstMap U M) (secondMap U M d)).inv

set_option backward.isDefEq.respectTransparency false in
/-- The actual lifted map has the original component at each original open pushforward. -/
@[reassoc (attr := simp)] theorem localLift_projection (d : Datum U M) (i j : ι)
    (hc : ComponentsCompatible U M d i) :
    localLift U M d i hc ≫ (restrictFunctor (U i).ι).map (projection U M d j) =
      localComponent U M d i j := by
  dsimp only [localLift, projection]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (PreservesEqualizer.iso (restrictFunctor (U i).ι)
    (firstMap U M) (secondMap U M d)).inv, PreservesEqualizer.iso_inv_ι,
    ← Category.assoc, equalizer.lift_ι, localProductLift_π]

/-- The finite local inverse once the actual normalized component cocycle is proved.
No such compatibility is assumed by the eventual descent theorem. -/
def localIsoOfComponentLaws (d : Datum U M) (i : ι)
    (hc : ComponentsCompatible U M d i)
    (hi : localComponent U M d i i ≫ (restrictAdjunction (U i).ι).counit.app (M i) = 𝟙 _) :
    (restrictFunctor (U i).ι).obj (glued U M d) ≅ M i where
  hom := localProjection U M d i
  inv := localLift U M d i hc
  inv_hom_id := by
    rw [localProjection, ← Category.assoc, localLift_projection, hi]
  hom_inv_id := by
    have hinv : localLift U M d i hc ≫ localProjection U M d i = 𝟙 _ := by
      rw [localProjection, ← Category.assoc, localLift_projection, hi]
    apply (cancel_mono (localProjection U M d i)).mp
    rw [Category.assoc, hinv, Category.comp_id, Category.id_comp]

end AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover
