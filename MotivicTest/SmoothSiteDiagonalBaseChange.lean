/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.DiagonalBaseChange
public import Lean.Util.CollectAxioms

/-! # Consumers of the literal middle-diagonal square under arbitrary field change -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Diagonal (baseChangeStalkMap)
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.SmoothSite
open RingTheory.Sequence

universe u

namespace MotivicTest.SmoothSiteDiagonalBaseChange

variable {S T : Scheme.{u}} (f : T ⟶ S) (Y : SmoothSite S)

/-- No flatness or finiteness is needed for the actual Cartesian square. -/
theorem arbitrary_base_square :
    IsPullback (pullback.fst Y.hom f) (pullback.diagonal ((baseChange f).obj Y).hom)
      (pullback.diagonal Y.hom) (baseChangePairProjection f Y) :=
  baseChangeDiagonal_isPullback f Y

/-- The map is defined by the inverse product comparison and the old pullback projection. -/
theorem literal_pair_projection :
    baseChangePairProjection f Y =
      (baseChangeProductIso f Y Y).inv.left ≫ pullback.fst (product Y Y).hom f := rfl

example [Flat f] : Flat (baseChangePairProjection f Y) := inferInstance

section Fields

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L) (Y : overField k)

/-- The field change is arbitrary: no finite-generation or separability instances occur. -/
theorem arbitrary_field_square :
    IsPullback (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)))
      (pullback.diagonal ((fieldBaseChange φ).obj Y).hom)
      (pullback.diagonal Y.hom) (fieldBaseChangePairProjection φ Y) :=
  fieldBaseChangeDiagonal_isPullback φ Y

example : Flat (fieldBaseChangePairProjection φ Y) := inferInstance

example : fieldBaseChangePairProjection φ Y ≫ pullback.fst Y.hom Y.hom =
    pullback.fst ((fieldBaseChange φ).obj Y).hom ((fieldBaseChange φ).obj Y).hom ≫
      pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) := by simp

example : fieldBaseChangePairProjection φ Y ≫ pullback.snd Y.hom Y.hom =
    pullback.snd ((fieldBaseChange φ).obj Y).hom ((fieldBaseChange φ).obj Y).hom ≫
      pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) := by simp

/-- Point alignment is the existing actual Cartesian stalk map, not a chosen ring map. -/
theorem literal_stalk_map (y : ((fieldBaseChange φ).obj Y).left) :
    fieldBaseChangeDiagonalStalkMap φ Y y =
      baseChangeStalkMap (fieldBaseChangeDiagonal_isPullback φ Y) y := rfl

example (y : ((fieldBaseChange φ).obj Y).left) :
    (fieldBaseChangeDiagonalStalkMap φ Y y).hom.Flat :=
  fieldBaseChangeDiagonalStalkMap_flat φ Y y

/-- The original list survives with its order and full new diagonal kernel unchanged. -/
theorem given_regular_list (y : ((fieldBaseChange φ).obj Y).left)
    (rs : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) y))))
    (hrs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) y))) rs)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) y)).hom = Ideal.ofList rs) :
    IsRegular ((pullback ((fieldBaseChange φ).obj Y).hom
        ((fieldBaseChange φ).obj Y).hom).presheaf.stalk
        (pullback.diagonal ((fieldBaseChange φ).obj Y).hom y))
      (rs.map (fieldBaseChangeDiagonalStalkMap φ Y y).hom) ∧
    RingHom.ker ((pullback.diagonal ((fieldBaseChange φ).obj Y).hom).stalkMap y).hom =
      Ideal.ofList (rs.map (fieldBaseChangeDiagonalStalkMap φ Y y).hom) :=
  fieldBaseChangeDiagonal_regular_kernel φ Y y rs hrs hker

end Fields

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.SmoothSite.baseChangePairProjection,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.baseChangePairProjection_fst,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.baseChangePairProjection_snd,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.baseChangePairProjection_flat,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.baseChangeProductIso_diagonal,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.baseChangeDiagonal_isPullback,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.baseChangeDiagonalStalkMap,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.baseChangeDiagonal_regular_kernel,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangePairProjection,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangePairProjection_fst,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangePairProjection_snd,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangePairProjection_flat,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeDiagonal_isPullback,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeDiagonalStalkMap,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeDiagonalStalkMap_flat,
          ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeDiagonal_regular_kernel,
      ``arbitrary_base_square, ``literal_pair_projection, ``arbitrary_field_square,
      ``literal_stalk_map, ``given_regular_list] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The actual diagonal and regular-list consumers use only standard foundations."

end MotivicTest.SmoothSiteDiagonalBaseChange
