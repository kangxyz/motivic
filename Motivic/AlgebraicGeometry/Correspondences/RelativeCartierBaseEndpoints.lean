/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeFiniteFlatSpanEndpoints
public import Motivic.AlgebraicGeometry.Correspondences.RelativeCartierDivisor

/-!
# Arbitrary-target Cartier endpoints over a relative smooth source

A proper flat Cartier divisor in a separated finite-type smooth relative curve
over `X × A¹` is the original finite-flat family. Its boundary-avoiding open is
an actual smooth-site object and supplies a retained joint closed immersion.
Forgetting this coordinate yields the direct original arbitrary-target
endpoint correspondence. Divisor flatness and properness remain explicit;
absolute Cartier divisors are not asserted to be flat.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.Hom
open Motivic.RelativeEndpointDiagram

universe u

namespace Motivic.RelativeCartierDivisor

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  {C U : Scheme.{u}} (p : C ⟶ relativeLine X.hom) [SmoothOfRelativeDimension 1 p]
  [IsSeparated p] [QuasiCompact p] (j : U ⟶ C) [IsOpenImmersion j]

/-- The actual boundary-avoiding open over the relative parameter base is a
smooth-site object; finite type and Noetherianity are derived from the curve. -/
def relativeRetainedOpen : SmoothSite (Spec (.of k)) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : IsNoetherian (relativeLine X.hom) :=
    inferInstanceAs (IsNoetherian (relativeLineSite X).left)
  have : IsNoetherian C := isNoetherian_of_finiteType p
  have : IsNoetherian U := isNoetherian_of_finiteType j
  exact SmoothSite.mk (j ≫ p ≫ relativeLineHom X.hom)

variable {Y : SmoothSite (Spec (.of k))} {D : Scheme.{u}} (i : D ⟶ C)
  [IsClosedImmersion i] (hI : IsLocallyRankOne C (idealModule i))
  [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (hAvoid : Set.range i ⊆ Set.range j) (g : U ⟶ Y.left)
  (hbase : j ≫ p ≫ relativeLineHom X.hom = g ≫ Y.hom)

/-- The original whole relative endpoint divisor, with its original target map. -/
def relativeEndpointCorrespondence (a : k) : Cor.mk X ⟶ Cor.mk Y := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  exact Cor.relativeFiniteFlatSpanEndpoint (X := X) (Y := Y)
    (i ≫ p) (targetMap i j hAvoid g)
    (targetMap_base (X := relativeLineSite X) (Y := Y) p i j hAvoid g hbase) a

/-- Relative endpoint graph compatibility for an arbitrary target, with the
retained embedding supplied by the actual boundary-avoiding smooth curve open. -/
theorem graph_relative_endpoint_correspondence (a : k) :
    (Cor.graphFunctor k).map (endpointMorphism X a) ≫
        correspondence (X := relativeLineSite X) (Y := Y) p i hI j hAvoid g hbase =
      relativeEndpointCorrespondence X p j i hI hAvoid g hbase a := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  let R := relativeRetainedOpen X p j
  let r : D ⟶ R.left := IsOpenImmersion.lift j i hAvoid
  have hr : (i ≫ p) ≫ relativeLineHom X.hom = r ≫ R.hom := by
    change (i ≫ p) ≫ relativeLineHom X.hom =
      IsOpenImmersion.lift j i hAvoid ≫ j ≫ p ≫ relativeLineHom X.hom
    simpa only [Category.assoc] using
      (congrArg (fun e : D ⟶ C ↦ e ≫ p ≫ relativeLineHom X.hom)
        (IsOpenImmersion.lift_fac j i hAvoid)).symm
  have : IsClosedImmersion (r ≫ j) := by
    change IsClosedImmersion (IsOpenImmersion.lift j i hAvoid ≫ j)
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  have : IsClosedImmersion r := IsClosedImmersion.of_comp r j
  have : IsClosedImmersion (pullback.lift (i ≫ p) r hr) := by
    have : IsClosedImmersion (pullback.lift (i ≫ p) r hr ≫
        pullback.snd (relativeLineHom X.hom) R.hom) := by
      rw [pullback.lift_snd]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd _ _)
  let q : R ⟶ Y := SmoothSite.homMk g hbase.symm
  simpa only [correspondence, relativeEndpointCorrespondence, targetMap, r, q,
    SmoothSite.homMk_left] using
    Cor.graph_relative_endpoint_ofFiniteFlatSpan_postcompose (X := X) (Y := R) (Z := Y)
      (i ≫ p) r hr q a

end Motivic.RelativeCartierDivisor
