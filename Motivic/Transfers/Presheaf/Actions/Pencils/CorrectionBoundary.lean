/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.StaticBoundaryPencilAction
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.SectionDualDivisor
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroLocus.OpenRestriction


/-!
# The original correcting section pair acts trivially after target inclusion

The two original global sections retain their full boundary equations. Their
zero schemes in the smaller retained open are compared with the same zero
schemes in the larger retained open, before applying the actual boundary
pencil. The correction has pole-minus-numerator sign. Neither an integral
compactification nor a supplied correspondence-action equality is required.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u v

namespace Motivic

variable {k : Type u} [Field k]
  (X B Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
  {C Z W U V : Scheme.{u}} (i : Z ⟶ C) (i' : W ⟶ C)
  (q : C ⟶ X.left) [IsProper q]
  (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (v : V ⟶ C) [IsOpenImmersion v] [V.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (v ≫ q)]
  (w : U ⟶ V) (hw : w ≫ v = j)
  (L : LineBundle C) (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  [IsIso ((Scheme.Modules.pullback i).map a)]
  [IsIso ((Scheme.Modules.pullback i').map a)]
  (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
  (hcover' : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range i')
  (g : U ⟶ B.left) (hbase : (j ≫ q) ≫ X.hom = g ≫ B.hom)
  (g' : V ⟶ Y.left) (hbase' : (v ≫ q) ≫ X.hom = g' ≫ Y.hom)
  (u : B ⟶ Y) (hgu : g ≫ u.left = w ≫ g')

include w hw hgu hcover' hbase'

/-- The same original zero divisor is unchanged by enlarging its retained
open and postcomposing its target with the original graph map. -/
theorem Cor.boundaryFunctional_comp_graph_of_open_extension :
    Cor.boundaryFunctional X B i q j L a hcover g hbase ≫ (Cor.graphFunctor k).map u =
      Cor.boundaryFunctional X Y i' q v L a hcover' g' hbase' := by
  let := lineBundle_isLocallyFree C L
  let ha := boundaryFunctional_finite_flat X i q j L a hcover
  let ha' := boundaryFunctional_finite_flat X i' q v L a hcover'
  have : IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ q) := ha.1
  have : Flat (Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ q) := ha.2
  have : IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit a v) ≫ v ≫ q) := ha'.1
  have : Flat (Hom.zeroInclusion (Hom.pullbackToUnit a v) ≫ v ≫ q) := ha'.2
  have hz : Set.range (Hom.zeroInclusion a) ⊆ Set.range j := by
    let := lineBundle_isLocallyFree C L
    let : IsIso (Hom.pullbackToUnit a i) := by
      unfold Hom.pullbackToUnit
      infer_instance
    let : IsEmpty (pullback i (Hom.zeroInclusion a) : Scheme.{u}) :=
      Hom.isEmpty_pullback_zeroInclusion a i
    rintro x ⟨z, rfl⟩
    rcases hcover (Hom.zeroInclusion a z) with hx | hx
    · exact hx
    · have hx' : z ∈ Set.range (pullback.snd i (Hom.zeroInclusion a)) := by
        rw [Scheme.Pullback.range_snd]
        exact hx
      obtain ⟨w, _⟩ := hx'
      exact isEmptyElim w
  have hz' : Set.range (Hom.zeroInclusion a) ⊆ Set.range v := by
    intro x hx
    obtain ⟨y, rfl⟩ := hz hx
    exact ⟨w y, congrArg (fun f => f y) hw⟩
  let eU := Hom.zeroRestrictionIso a j hz
  let eV := Hom.zeroRestrictionIso a v hz'
  let e := eU ≪≫ eV.symm
  have he : e.hom ≫ Hom.zeroInclusion (Hom.pullbackToUnit a v) ≫ v =
      Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j := by
    rw [← Hom.zeroRestrictionIso_hom_inclusion a v hz']
    change (eU.hom ≫ eV.inv) ≫ eV.hom ≫ Hom.zeroInclusion a = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact Hom.zeroRestrictionIso_hom_inclusion a j hz
  have he' : e.hom ≫ Hom.zeroInclusion (Hom.pullbackToUnit a v) =
      Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ w := by
    apply (cancel_mono v).mp
    simpa only [Category.assoc, hw] using he
  unfold Cor.boundaryFunctional
  rw [Cor.ofFiniteFlatSpan_comp_graph]
  apply PolynomialPencilCycles.span_eq_of_iso e
  · simpa only [Category.assoc] using congrArg (fun f => f ≫ q) he
  · rw [← Category.assoc, he', Category.assoc, ← hgu]
    simp only [Category.assoc]

namespace PresheafWithTransfers

/-- Pole minus numerator from the same global boundary-normalized pair acts
by zero after the specified original target inclusion. The source and target
maps, both actual zero schemes, and their signs are retained. -/
theorem transfer_correction_comp_graph_eq_zero
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (b : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map b)]
    [IsIso ((Scheme.Modules.pullback i').map b)]
    (hab : Hom.pullbackToUnit a i' = Hom.pullbackToUnit b i') :
    transfer P
      ((Cor.boundaryFunctional X B i q j L b hcover g hbase -
        Cor.boundaryFunctional X B i q j L a hcover g hbase) ≫
          (Cor.graphFunctor k).map u) = 0 := by
  rw [Preadditive.sub_comp,
    Cor.boundaryFunctional_comp_graph_of_open_extension X B Y i i' q j v w hw L b
      hcover hcover' g hbase g' hbase' u hgu,
    Cor.boundaryFunctional_comp_graph_of_open_extension X B Y i i' q j v w hw L a
      hcover hcover' g hbase g' hbase' u hgu,
    transfer_sub]
  have he := transfer_boundaryFunctional_eq X Y i' q v L a hcover' g' hbase' P hP b hab
  rw [← he, sub_self]

/-- The section form retains the original numerator and denominator themselves,
not merely abstract regular functionals. The boundary equality can be the
literal infinity equality obtained from the simultaneous Serre prescription. -/
theorem transfer_correctionSections_comp_graph_eq_zero
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (N : LineBundle C)
    (nS dS : SheafOfModules.unit C.ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap i nS)] [IsIso (pullbackSectionMap i dS)]
    [IsIso (pullbackSectionMap i' nS)] [IsIso (pullbackSectionMap i' dS)]
    (hnd : pullbackSectionMap i' nS = pullbackSectionMap i' dS) :
    transfer P
      ((Cor.boundarySection X B i q j N hcover g hbase dS -
        Cor.boundarySection X B i q j N hcover g hbase nS) ≫
          (Cor.graphFunctor k).map u) = 0 := by
  have := sectionDualFunctional_pullback_map_isIso i N nS
  have := sectionDualFunctional_pullback_map_isIso i N dS
  have := sectionDualFunctional_pullback_map_isIso i' N nS
  have := sectionDualFunctional_pullback_map_isIso i' N dS
  have he : Hom.pullbackToUnit (sectionDualFunctional C N nS) i' =
      Hom.pullbackToUnit (sectionDualFunctional C N dS) i' := by
    rw [sectionDualFunctional_pullback, sectionDualFunctional_pullback]
    simp only [pulledSectionDualFunctional, hnd]
  exact transfer_correction_comp_graph_eq_zero X B Y i i' q j v w hw
    (dualLineBundle C N) (sectionDualFunctional C N nS) hcover hcover'
    g hbase g' hbase' u hgu P hP (sectionDualFunctional C N dS) he

end PresheafWithTransfers
end Motivic
