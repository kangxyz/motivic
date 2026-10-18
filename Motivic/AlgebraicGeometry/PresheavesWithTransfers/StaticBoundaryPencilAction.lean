/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.PolynomialPencilFiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramedSectionTransport
public import Motivic.AlgebraicGeometry.Correspondences.SignedProductPencilEndpoints
public import Motivic.AlgebraicGeometry.Correspondences.PencilA1Endpoints
public import Motivic.Cohomology.A1.Basic

/-!
# Original static divisor actions from a constructed boundary pencil

The compactification and its two functionals are static over the original
source. The literal polynomial base change constructs the homotopy, its
finite-flatness, and its original whole zero/one endpoint cycles. No family,
endpoint identity, or equality of transfer actions is supplied as input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open Motivic.RelativeEndpointDiagram Motivic.SignedProductPencilEndpoints

universe u v

namespace Motivic

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
  {C B U : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ X.left) [IsProper q]
  (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle C)
  (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  [IsIso ((Scheme.Modules.pullback i).map a)]
  (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)

include i hcover in
/-- A static boundary-unit functional has its original finite-flat zero
scheme on the retained open. -/
theorem boundaryFunctional_finite_flat :
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ q) ∧
      Flat (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ q) := by
  have h := Scheme.Modules.Invertible.GlobalBoundaryPencil.pencil_finite_flat_on_open
    i q j L a a 0 rfl hcover
  rw [Scheme.Modules.Invertible.GlobalBoundaryPencil.pencil_zero] at h
  exact ⟨h.1, h.2.2⟩

variable (g : U ⟶ Y.left) (hbase : (j ≫ q) ≫ X.hom = g ≫ Y.hom)

/-- The actual static zero correspondence; all lengths of the original zero
scheme are retained. Its finiteness and flatness come from the compactification. -/
def Cor.boundaryFunctional : Cor.mk X ⟶ Cor.mk Y := by
  have hf := (boundaryFunctional_finite_flat X i q j L a hcover).1
  have ht := (boundaryFunctional_finite_flat X i q j L a hcover).2
  exact Cor.ofFiniteFlatSpan (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ q)
    (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ g)
    (by simpa only [Category.assoc] using
      congrArg (fun z => Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ z) hbase)

/-- An actual coefficient-line isomorphism preserves the original whole zero
correspondence, not merely its reduced support or framed class. -/
theorem Cor.boundaryFunctional_precompIso
    (M : LineBundle C) (e : M.val ≅ L.val)
    [IsIso ((Scheme.Modules.pullback i).map (e.hom ≫ a))] :
    Cor.boundaryFunctional X Y i q j M (e.hom ≫ a) hcover g hbase =
      Cor.boundaryFunctional X Y i q j L a hcover g hbase := by
  have hf := (boundaryFunctional_finite_flat X i q j L a hcover).1
  have ht := (boundaryFunctional_finite_flat X i q j L a hcover).2
  have hf' := (boundaryFunctional_finite_flat X i q j M (e.hom ≫ a) hcover).1
  have ht' := (boundaryFunctional_finite_flat X i q j M (e.hom ≫ a) hcover).2
  have he : Hom.pullbackToUnit (e.hom ≫ a) j =
      (Scheme.Modules.pullback j).map e.hom ≫ Hom.pullbackToUnit a j := by
    simp only [Hom.pullbackToUnit, CategoryTheory.Functor.map_comp, Category.assoc]
  let E : Hom.zeroScheme (Hom.pullbackToUnit (e.hom ≫ a) j) ≅
      Hom.zeroScheme (Hom.pullbackToUnit a j) :=
    eqToIso (congrArg Hom.zeroScheme he) ≪≫
    zeroSchemePrecompIso ((Scheme.Modules.pullback j).mapIso e) (Hom.pullbackToUnit a j)
  have hE : E.hom ≫ Hom.zeroInclusion (Hom.pullbackToUnit a j) =
      Hom.zeroInclusion (Hom.pullbackToUnit (e.hom ≫ a) j) := by
    simp only [E, Iso.trans_hom, Category.assoc, zeroSchemePrecompIso_hom_inclusion,
      CategoryTheory.Functor.mapIso_hom, eqToIso.hom]
    exact zeroScheme_congr_inclusion he
  unfold Cor.boundaryFunctional
  apply PolynomialPencilCycles.span_eq_of_iso E
  · simp only [← Category.assoc, hE]
  · simp only [← Category.assoc, hE]

/-- The original zero correspondence of a section carrying its actual boundary
frame. The canonical dual functional, not a chosen divisor representative, is used. -/
def Cor.boundarySection
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap i s)] : Cor.mk X ⟶ Cor.mk Y := by
  have := sectionDualFunctional_pullback_map_isIso i L s
  exact Cor.boundaryFunctional X Y i q j (dualLineBundle C L)
    (sectionDualFunctional C L s) hcover g hbase

namespace PresheafWithTransfers

/-- Equal actual boundary values produce equal actions of the two original
static zero divisors on every HI presheaf with transfers. -/
theorem transfer_boundaryFunctional_eq
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (b : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map b)]
    (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit b i) :
    transfer P (Cor.boundaryFunctional X Y i q j L a hcover g hbase) =
      transfer P (Cor.boundaryFunctional X Y i q j L b hcover g hbase) := by
  let p : U ⟶ X.left := j ≫ q
  let T : LineBundle U := pullbackLineBundle j L
  let a' : T.val ⟶ SheafOfModules.unit U.ringCatSheaf := Hom.pullbackToUnit a j
  let b' : T.val ⟶ SheafOfModules.unit U.ringCatSheaf := Hom.pullbackToUnit b j
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : Smooth (p ≫ X.hom) := inferInstance
  have : IsSeparated (p ≫ X.hom) := inferInstance
  have : QuasiCompact (p ≫ X.hom) := inferInstance
  obtain ⟨hf, ht⟩ := retained_familySource_finite_flat (S := X.left) X.hom q j i L a b h hcover
  have : IsFinite (familySource p T a' b') := hf
  have : Flat (familySource p T a' b') := ht
  have : IsFinite (Hom.zeroInclusion a' ≫ p) :=
    (boundaryFunctional_finite_flat X i q j L a hcover).1
  have : Flat (Hom.zeroInclusion a' ≫ p) :=
    (boundaryFunctional_finite_flat X i q j L a hcover).2
  have : IsFinite (Hom.zeroInclusion b' ≫ p) :=
    (boundaryFunctional_finite_flat X i q j L b hcover).1
  have : Flat (Hom.zeroInclusion b' ≫ p) :=
    (boundaryFunctional_finite_flat X i q j L b hcover).2
  have he := transfer_homotopy_endpoints P hP X (Cor.mk Y)
    (familyCorrespondence p T a' b' g hbase) 0 1
  rw [← PencilA1Endpoints.endpointMorphism_eq_a1Section,
    ← PencilA1Endpoints.endpointMorphism_eq_a1Section,
    graph_family_zero, graph_family_one] at he
  exact he

/-- A frame-preserving isomorphism of two actual section representatives gives
equality of their original divisor actions. The homotopy is the constructed
polynomial pencil; no correspondence or action comparison is an input. -/
theorem transfer_boundarySection_eq_of_framedIso
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (M : LineBundle C)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    (t : SheafOfModules.unit C.ringCatSheaf ⟶ M.val)
    [IsIso (pullbackSectionMap i s)] [IsIso (pullbackSectionMap i t)]
    (e : BoundaryFramedLineBundle.Iso (BoundaryFramedLineBundle.ofSection i L s)
      (BoundaryFramedLineBundle.ofSection i M t)) :
    transfer P (Cor.boundarySection X Y i q j L hcover g hbase s) =
      transfer P (Cor.boundarySection X Y i q j M hcover g hbase t) := by
  have : IsIso (pullbackSectionMap i (s ≫ e.iso.hom)) := by
    rw [e.pullbackSectionMap_eq]
    infer_instance
  have := sectionDualFunctional_pullback_map_isIso i L s
  have := sectionDualFunctional_pullback_map_isIso i M t
  have := sectionDualFunctional_pullback_map_isIso i M (s ≫ e.iso.hom)
  have : IsIso ((Scheme.Modules.pullback i).map
      ((dualPrecompIso (L := L) (M := M) e.iso).hom ≫ sectionDualFunctional C L s)) := by
    rw [← sectionDualFunctional_postcompIso (L := L) (M := M) e.iso s]
    infer_instance
  have he := transfer_boundaryFunctional_eq X Y i q j (dualLineBundle C M)
    (sectionDualFunctional C M (s ≫ e.iso.hom)) hcover g hbase P hP
    (sectionDualFunctional C M t) e.pullbackToUnit_sectionDualFunctional_eq
  simp only [sectionDualFunctional_postcompIso (L := L) (M := M) e.iso s,
    Cor.boundaryFunctional_precompIso] at he
  exact he

/-- Equality of the already represented framed classes supplies the actual
frame-preserving isomorphism; representative existence is not asserted. -/
theorem transfer_boundarySection_eq_of_class_eq
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (M : LineBundle C)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    (t : SheafOfModules.unit C.ringCatSheaf ⟶ M.val)
    [IsIso (pullbackSectionMap i s)] [IsIso (pullbackSectionMap i t)]
    (he : BoundaryFramedLineBundle.classOf (BoundaryFramedLineBundle.ofSection i L s) =
      BoundaryFramedLineBundle.classOf (BoundaryFramedLineBundle.ofSection i M t)) :
    transfer P (Cor.boundarySection X Y i q j L hcover g hbase s) =
      transfer P (Cor.boundarySection X Y i q j M hcover g hbase t) := by
  obtain ⟨e⟩ := (BoundaryFramedLineBundle.classOf_eq_iff _ _).mp he
  exact transfer_boundarySection_eq_of_framedIso X Y i q j L hcover g hbase P hP M s t e

end PresheafWithTransfers
end Motivic
