/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorSheafRestriction
public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorRestrictionCoherence
public import Motivic.AlgebraicGeometry.Modules.AffineOpenTildeRestrictionCoherence

/-!
# Coherence of the original closed-intersection Tor chart sheaves

The constructed chart-sheaf transitions obey identity and composition with the
actual whole inverse-image open restrictions. The proof combines the proved
canonical tilde cocycle and the original chart-module equations. No geometric
cocycle or sheaf transition is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.AffineOpenTilde

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Factor the chart-sheaf cocycle through abstract coordinate modules, keeping
large concrete Tor objects out of the categorical rewrite proof. -/
private theorem restrictionMap_comp {X : Scheme.{u}} {U V L : X.affineOpens}
    (h : U ≤ V) (k : V ≤ L)
    {M : ModuleCat.{u} Γ(X, L)} {N : ModuleCat.{u} Γ(X, V)}
    {Q : ModuleCat.{u} Γ(X, U)}
    (f : (ModuleCat.extendScalars (sectionRestriction k).hom).obj M ⟶ N)
    (g : (ModuleCat.extendScalars (sectionRestriction h).hom).obj N ⟶ Q)
    (d : (ModuleCat.extendScalars (sectionRestriction (h.trans k)).hom).obj M ⟶ Q)
    (e : (scalarCompositionIso h k M).hom ≫
      (ModuleCat.extendScalars (sectionRestriction h).hom).map f ≫ g = d) :
    (openCompositionIso (X := X) (U := U.1) (V := V.1) (L := L.1) h k).hom.app
        ((chartTilde L).obj M) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((restrictionIso k).hom.app M ≫ (chartTilde V).map f) ≫
      ((restrictionIso h).hom.app N ≫ (chartTilde U).map g) =
    (restrictionIso (h.trans k)).hom.app M ≫ (chartTilde U).map d := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [restrictionIso_naturality_assoc h f]
  erw [restrictionIso_hom_comp_assoc h k M]
  have hm := congrArg (chartTilde U).map e
  simp only [CategoryTheory.Functor.map_comp] at hm
  exact congrArg (fun φ => (restrictionIso (h.trans k)).hom.app M ≫ φ) hm

end Motivic.AffineOpenTilde

namespace Motivic.Intersection

variable {P T D W : Scheme.{u}} (i : T ⟶ P) (j : D ⟶ P)
  (a : W ⟶ D) (b : W ⟶ T) [IsClosedImmersion i] [IsClosedImmersion j]
  (sq : IsPullback a b j i)

/-- The original module identity is exactly the affine-open scalar unitor. -/
theorem closedIntersectionAffineTorRestrictionIso_hom_scalarIdentity
    (U : P.affineOpens) (n : ℕ) :
    (closedIntersectionAffineTorRestrictionIso i j a b sq (show U ≤ U from le_rfl) n).hom =
      (AffineOpenTilde.scalarIdentityIso (closedIntersectionAffineOpen i a b j sq U)
        (closedIntersectionAffineTor i a b j sq U n)).hom :=
  closedIntersectionAffineTorRestrictionIso_hom_refl i j a b sq U n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original direct module transition equals its two-step transition through the
actual affine-open scalar associator. -/
theorem closedIntersectionAffineTorRestrictionIso_hom_scalarComposition
    {U V L : P.affineOpens} (h : U ≤ V) (k : V ≤ L) (n : ℕ) :
    (AffineOpenTilde.scalarCompositionIso
      (U := closedIntersectionAffineOpen i a b j sq U)
      (V := closedIntersectionAffineOpen i a b j sq V)
      (L := closedIntersectionAffineOpen i a b j sq L)
      ((a ≫ j).preimage_mono h) ((a ≫ j).preimage_mono k)
      (closedIntersectionAffineTor i a b j sq L n)).hom ≫
      (ModuleCat.extendScalars (closedIntersectionAffineRestriction j a h)).map
        (closedIntersectionAffineTorRestrictionIso i j a b sq k n).hom ≫
      (closedIntersectionAffineTorRestrictionIso i j a b sq h n).hom =
    (closedIntersectionAffineTorRestrictionIso i j a b sq (h.trans k) n).hom := by
  simp only [AffineOpenTilde.scalarCompositionIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
  erw [closedIntersectionAffineTorRestrictionIso_hom_comp i j a b sq h k n]
  simp only [← Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original chart-sheaf identity transition is its geometric restriction unitor. -/
theorem closedIntersectionTorSheafRestrictionIso_hom_refl (U : P.affineOpens) (n : ℕ) :
    (closedIntersectionTorSheafRestrictionIso i j a b sq (show U ≤ U from le_rfl) n).hom =
      (AffineOpenTilde.openIdentityIso (X := W)
        (closedIntersectionAffineOpen i a b j sq U).1).hom.app
        (closedIntersectionTorChartSheaf i a b j sq U n) := by
  rw [closedIntersectionTorSheafRestrictionIso_hom,
    closedIntersectionAffineTorRestrictionIso_hom_scalarIdentity]
  exact AffineOpenTilde.restrictionIso_hom_refl _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two original chart-sheaf refinements equal the direct original transition,
using the actual open-inclusion associator. -/
theorem closedIntersectionTorSheafRestrictionIso_hom_comp
    {U V L : P.affineOpens} (h : U ≤ V) (k : V ≤ L) (n : ℕ) :
    (AffineOpenTilde.openCompositionIso (X := W)
      (U := (closedIntersectionAffineOpen i a b j sq U).1)
      (V := (closedIntersectionAffineOpen i a b j sq V).1)
      (L := (closedIntersectionAffineOpen i a b j sq L).1)
      ((a ≫ j).preimage_mono h) ((a ≫ j).preimage_mono k)).hom.app
        (closedIntersectionTorChartSheaf i a b j sq L n) ≫
      (Scheme.Modules.restrictFunctor (W.homOfLE ((a ≫ j).preimage_mono h))).map
        (closedIntersectionTorSheafRestrictionIso i j a b sq k n).hom ≫
      (closedIntersectionTorSheafRestrictionIso i j a b sq h n).hom =
    (closedIntersectionTorSheafRestrictionIso i j a b sq (h.trans k) n).hom := by
  rw [closedIntersectionTorSheafRestrictionIso_hom,
    closedIntersectionTorSheafRestrictionIso_hom,
    closedIntersectionTorSheafRestrictionIso_hom]
  exact AffineOpenTilde.restrictionMap_comp
    (U := closedIntersectionAffineOpen i a b j sq U)
    (V := closedIntersectionAffineOpen i a b j sq V)
    (L := closedIntersectionAffineOpen i a b j sq L)
    (M := closedIntersectionAffineTor i a b j sq L n)
    (N := closedIntersectionAffineTor i a b j sq V n)
    (Q := closedIntersectionAffineTor i a b j sq U n)
    ((a ≫ j).preimage_mono h) ((a ≫ j).preimage_mono k)
    (closedIntersectionAffineTorRestrictionIso i j a b sq k n).hom
    (closedIntersectionAffineTorRestrictionIso i j a b sq h n).hom
    (closedIntersectionAffineTorRestrictionIso i j a b sq (h.trans k) n).hom
    (closedIntersectionAffineTorRestrictionIso_hom_scalarComposition i j a b sq h k n)

end Motivic.Intersection
