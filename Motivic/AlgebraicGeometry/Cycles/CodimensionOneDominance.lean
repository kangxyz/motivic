/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Motivic.AlgebraicGeometry.Cycles.FiniteResidueDegree
public import Motivic.AlgebraicGeometry.Cycles.GenericDominance

/-!
# Dominance of finite codimension-one supports in smooth relative curves

A closed point of the residue-field fibre has coheight one in that smooth
curve, over an arbitrary residue field. Its strict generalization maps to an
ambient generic point when the original ambient point has coheight one.
Generalization lifting then proves genericity of the base point. No global
Cartier divisor, perfect residue field, or finite-flat support is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

universe u

namespace Motivic

/-- Coheight zero detects the original component generic points. -/
theorem mem_genericPoints_of_coheight_eq_zero {X : Scheme.{u}} {x : X}
    (hx : coheight x = 0) : x ∈ genericPoints X := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro s hs hxs
  have hy : hs.genericPoint ⤳ x :=
    hs.isGenericPoint_genericPoint_closure.specializes
      (subset_closure (hxs (subset_closure (by simp))))
  have hxy : x ⤳ hs.genericPoint := (coheight_eq_zero.mp hx) hy
  have he : hs.genericPoint = x := (hy.antisymm hxy).eq
  rw [← he, hs.genericPoint_closure_eq]
  exact subset_closure

/-- A codimension-one point that is closed in its smooth relative-curve fibre
lies over a genuine generic point of the base, including disconnected bases. -/
theorem image_mem_genericPoints_of_coheight_one_closed_fiber
    {X S : Scheme.{u}} (q : X ⟶ S) [SmoothOfRelativeDimension 1 q]
    (x : X) (hx : coheight x = 1)
    (hc : IsClosed ({q.asFiber x} : Set (q.fiber (q x)))) :
    q x ∈ genericPoints S := by
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  let y := q x
  let a := q.asFiber x
  have : SmoothOfRelativeDimension 1 (q.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have ha : coheight a = 1 := by
    have hd := Scheme.smoothClosedPointDimension (S.residueField y) (q.fiber y)
      (q.fiberToSpecResidueField y) 1 inferInstance a hc
    rw [ringKrullDim_stalk_eq_coheight] at hd
    exact_mod_cast hd
  have hn : ¬ IsMax a := coheight_ne_zero.mp (by rw [ha]; exact one_ne_zero)
  obtain ⟨b, hab⟩ := not_isMax_iff.mp hn
  have hs : StrictMono (q.fiberι y) := by
    intro c d hcd
    have hle : q.fiberι y c ≤ q.fiberι y d := hcd.le.map (q.fiberι y).continuous
    refine ⟨hle, ?_⟩
    intro hdc
    exact hcd.not_ge ((q.fiberι y).isEmbedding.isInducing.specializes_iff.mp hdc)
  have hxb : x < q.fiberι y b := by
    simpa only [a, y, Scheme.Hom.fiberι_asFiber] using hs hab
  have hb : coheight (q.fiberι y b) = 0 :=
    Order.lt_one_iff.mp ((coheight_le_coe_iff.mp hx.le) _ hxb)
  have hgeneric := mem_genericPoints_of_generalizing q (Flat.generalizingMap q)
    (q.fiberι y b) (mem_genericPoints_of_coheight_eq_zero hb)
  have he : q (q.fiberι y b) = q x := by
    have hm : q.fiberι y b ∈ Set.range (q.fiberι y) := ⟨b, rfl⟩
    rw [q.range_fiberι y] at hm
    exact hm
  rwa [he] at hgeneric

/-- Finite residue extension gives closedness in the actual fibre, through its
original residue-field point. The fibre projection is only separated, not finite. -/
theorem isClosed_asFiber_of_finite_residueFieldMap
    {X S : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] (x : X)
    (hf : (q.residueFieldMap x).hom.Finite) :
    IsClosed ({q.asFiber x} : Set (q.fiber (q x))) := by
  have : IsFinite (Spec.map (q.residueFieldMap x)) := (IsFinite.SpecMap_iff _).mpr hf
  have : IsFinite (q.asFiberHom x ≫ q.fiberToSpecResidueField (q x)) := by
    rw [q.asFiberHom_fiberToSpecResidueField]
    infer_instance
  have : IsSeparated (q.fiberToSpecResidueField (q x)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsFinite (q.asFiberHom x) :=
    IsFinite.of_comp (q.asFiberHom x) (q.fiberToSpecResidueField (q x))
  rw [← q.range_asFiberHom x]
  exact (q.asFiberHom x).isClosedMap.isClosed_range

/-- The finite residue-field condition is enough for the actual component
image, without assuming flatness of the closed support. -/
theorem image_mem_genericPoints_of_coheight_one_finite_residue
    {X S : Scheme.{u}} (q : X ⟶ S) [SmoothOfRelativeDimension 1 q] [IsSeparated q]
    (x : X) (hx : coheight x = 1) (hf : (q.residueFieldMap x).hom.Finite) :
    q x ∈ genericPoints S :=
  image_mem_genericPoints_of_coheight_one_closed_fiber q x hx
    (isClosed_asFiber_of_finite_residueFieldMap q x hf)

/-- A whole finite closed support supplies the original ambient residue-field
extension; its residue isomorphism is retained in the comparison. -/
theorem residueFieldMap_finite_of_finite_closed_support
    {D X S : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (q : X ⟶ S) [IsFinite (i ≫ q)] (x : D) :
    (q.residueFieldMap (i x)).hom.Finite := by
  have : IsIso (i.residueFieldMap x) := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(i.residueFieldMap x).hom.injective, residueFieldMap_surjective i x⟩
  have : IsFinite (Spec.map ((i ≫ q).residueFieldMap x)) :=
    (IsFinite.SpecMap_iff _).mpr (residueFieldMap_finite (i ≫ q) x)
  have he : Spec.map (q.residueFieldMap (i x)) =
      inv (Spec.map (i.residueFieldMap x)) ≫ Spec.map ((i ≫ q).residueFieldMap x) := by
    rw [Scheme.residueFieldMap_comp]
    erw [Spec.map_comp, IsIso.inv_hom_id_assoc]
  apply (IsFinite.SpecMap_iff _).mp
  rw [he]
  infer_instance

/-- A finite closed support at a codimension-one point of a smooth relative
curve lies over an actual component generic point. Finiteness, not flatness,
of the support is the geometric input. -/
theorem image_mem_genericPoints_of_coheight_one_finite_closed_support
    {D X S : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (q : X ⟶ S) [SmoothOfRelativeDimension 1 q] [IsSeparated q]
    [IsFinite (i ≫ q)] (x : D) (hx : coheight (i x) = 1) :
    q (i x) ∈ genericPoints S :=
  image_mem_genericPoints_of_coheight_one_finite_residue q (i x) hx
    (residueFieldMap_finite_of_finite_closed_support i q x)

end Motivic
