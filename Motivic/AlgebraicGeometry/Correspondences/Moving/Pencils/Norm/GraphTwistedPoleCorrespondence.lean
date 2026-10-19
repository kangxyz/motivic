/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.StaticBoundaryPencilAction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.GraphInfinityEquality
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroLocus.OpenRestriction
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.Product.Pullback


/-! # Original graph-twisted pole correspondence

The actual whole zero scheme of the graph-twisted pole gives the original graph
plus the original pole correspondence. The proof keeps all multiplicities and
uses no presheaf action or homotopy-invariance assumption.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
  _root_.AlgebraicGeometry.Scheme.SmoothSite.PolynomialPencil

universe u v

namespace Motivic.Cor

/-- The original graph-twisted pole has exactly the graph plus original pole zero
correspondence. The boundary-unit inputs concern actual sections, not cycle identities. -/
theorem boundarySection_twistedIdeal_eq_graph_add
    {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {C B U : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ X.left) [IsProper q]
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (γ : X.left ⟶ C) [IsClosedImmersion γ]
    (hI : IsLocallyRankOne C (Scheme.Hom.idealModule γ))
    (δ : X.left ⟶ U) (hδ : δ ≫ j = γ) (hq : γ ≫ q = 𝟙 X.left)
    (T : LineBundle C)
    (bS : SheafOfModules.unit C.ringCatSheaf ⟶ T.val)
    [IsIso (pullbackSectionMap i bS)]
    [IsIso ((Scheme.Modules.pullback i).map (Scheme.Hom.idealInclusion γ))]
    [IsIso (pullbackSectionMap i
      (twistedIdealSection C ⟨Scheme.Hom.idealModule γ, hI⟩ T
        (Scheme.Hom.idealInclusion γ) bS))]
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
    (g : U ⟶ Y.left) (φ : X ⟶ Y) (hg : δ ≫ g = φ.left)
    (hbase : (j ≫ q) ≫ X.hom = g ≫ Y.hom) :
    Cor.boundarySection X Y i q j
        (tensorLineBundle C T (dualLineBundle C ⟨Scheme.Hom.idealModule γ, hI⟩))
        hcover g hbase
        (twistedIdealSection C ⟨Scheme.Hom.idealModule γ, hI⟩ T
          (Scheme.Hom.idealInclusion γ) bS) =
      @Add.add (Cor.mk X ⟶ Cor.mk Y) inferInstance
        ((Cor.graphFunctor k).map φ) (Cor.boundarySection X Y i q j T hcover g hbase bS) := by
  let I : LineBundle C := ⟨Scheme.Hom.idealModule γ, hI⟩
  let L := tensorLineBundle C T (dualLineBundle C I)
  let cS := twistedIdealSection C I T (Scheme.Hom.idealInclusion γ) bS
  let c := sectionDualFunctional C L cS
  let b := sectionDualFunctional C T bS
  have := sectionDualFunctional_pullback_map_isIso i L cS
  have := sectionDualFunctional_pullback_map_isIso i T bS
  let p := j ≫ q
  let A := pullbackLineBundle j (dualLineBundle C L)
  let J := pullbackLineBundle j I
  let M := pullbackLineBundle j (dualLineBundle C T)
  let c' := Hom.pullbackToUnit c j
  let b' := Hom.pullbackToUnit b j
  let ε := Hom.pullbackToUnit (Scheme.Hom.idealInclusion γ) j
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : Smooth (p ≫ X.hom) := inferInstance
  have : IsSeparated (p ≫ X.hom) := inferInstance
  have : QuasiCompact (p ≫ X.hom) := inferInstance
  have hf := boundaryFunctional_finite_flat X i q j (dualLineBundle C L) c hcover
  have : IsFinite (Hom.zeroInclusion c' ≫ p) := hf.1
  have : Flat (Hom.zeroInclusion c' ≫ p) := hf.2
  have hb := boundaryFunctional_finite_flat X i q j (dualLineBundle C T) b hcover
  have : IsFinite (Hom.zeroInclusion b' ≫ p) := hb.1
  have : Flat (Hom.zeroInclusion b' ≫ p) := hb.2
  have hε := boundaryFunctional_finite_flat X i q j I (Scheme.Hom.idealInclusion γ) hcover
  have : IsFinite (Hom.zeroInclusion ε ≫ p) := hε.1
  have : Flat (Hom.zeroInclusion ε ≫ p) := hε.2
  have : Mono b' := by
    have hh := Scheme.Modules.Invertible.GlobalBoundaryPencil.pencil_finite_flat_on_open i q j
      (dualLineBundle C T) b b 0 rfl hcover
    rw [Scheme.Modules.Invertible.GlobalBoundaryPencil.pencil_zero] at hh
    exact hh.2.1
  have : Mono ε := by
    have hh := Scheme.Modules.Invertible.GlobalBoundaryPencil.pencil_finite_flat_on_open i q j I
      (Scheme.Hom.idealInclusion γ) (Scheme.Hom.idealInclusion γ) 0 rfl hcover
    rw [Scheme.Modules.Invertible.GlobalBoundaryPencil.pencil_zero] at hh
    exact hh.2.1
  let E : A.val ≅ (tensorLineBundle U J M).val :=
    (Scheme.Modules.pullback j).mapIso (dualTwistedIdealIso C I T).symm ≪≫
      PullbackTensor.Local.pullbackLineBundleTensorIso j I (dualLineBundle C T)
  have hc' : c' = E.hom ≫ Hom.productSection ε b' := by
    have hh : c = (dualTwistedIdealIso C I T).inv ≫ Hom.productSection
        (Scheme.Hom.idealInclusion γ) b := by
      rw [← dualTwistedIdealIso_section C I T (Scheme.Hom.idealInclusion γ) bS,
        Iso.inv_hom_id_assoc]
    simp only [c', hh, Hom.pullbackToUnit, Functor.map_comp, Category.assoc,
      E, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    change (Scheme.Modules.pullback j).map (dualTwistedIdealIso C I T).inv ≫
        Hom.pullbackToUnit (Hom.productSection (Scheme.Hom.idealInclusion γ) b) j =
      (Scheme.Modules.pullback j).map (dualTwistedIdealIso C I T).inv ≫
        (PullbackTensor.Local.pullbackLineBundleTensorIso j I (dualLineBundle C T)).hom ≫
          Hom.productSection (Hom.pullbackToUnit (Scheme.Hom.idealInclusion γ) j)
            (Hom.pullbackToUnit b j)
    exact congrArg (fun f =>
      (Scheme.Modules.pullback j).map (dualTwistedIdealIso C I T).inv ≫ f)
        (Hom.pullbackToUnit_productSection_lineBundle j I (dualLineBundle C T)
          (Scheme.Hom.idealInclusion γ) b)
  let E0 : Hom.zeroScheme c' ≅ Hom.zeroScheme (Hom.productSection ε b') :=
    eqToIso (congrArg Hom.zeroScheme hc') ≪≫
      zeroSchemePrecompIso E (Hom.productSection ε b')
  have hE0 : E0.hom ≫ Hom.zeroInclusion (Hom.productSection ε b') =
      Hom.zeroInclusion c' := by
    simp only [E0, Iso.trans_hom, Category.assoc, zeroSchemePrecompIso_hom_inclusion]
    exact zeroScheme_congr_inclusion hc'
  have hi : Hom.zeroInclusion (Hom.productSection ε b') ≫ p =
      E0.inv ≫ (Hom.zeroInclusion c' ≫ p) := by
    rw [← hE0, Category.assoc, E0.inv_hom_id_assoc]
  have : IsFinite (Hom.zeroInclusion (Hom.productSection ε b') ≫ p) := by
    rw [hi]; infer_instance
  have : Flat (Hom.zeroInclusion (Hom.productSection ε b') ≫ p) := by
    rw [hi]; infer_instance
  have hs : Cor.boundarySection X Y i q j L hcover g hbase cS =
      Cor.ofFiniteFlatSpan (X := X) (Y := Y)
        (Hom.zeroInclusion (Hom.productSection ε b') ≫ p)
        (Hom.zeroInclusion (Hom.productSection ε b') ≫ g)
        (by simp only [Category.assoc, hbase, p]) := by
    unfold Cor.boundarySection Cor.boundaryFunctional
    apply PolynomialPencilCycles.span_eq_of_iso E0
    · simpa only [Category.assoc] using congrArg (· ≫ p) hE0
    · simpa only [Category.assoc] using congrArg (· ≫ g) hE0
  rw [hs, _root_.AlgebraicGeometry.Scheme.Cycles.Divisors.Product.ofFiniteFlatSpan_productSection J
      M ε b' p g hbase]
  let := lineBundle_isLocallyFree C I
  have hz : Set.range (Hom.zeroInclusion (Scheme.Hom.idealInclusion γ)) ⊆ Set.range j := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨δ ((DiagonalZeroCycle.zeroIdealInclusionIso γ).hom z), ?_⟩
    have hh := DiagonalZeroCycle.zeroIdealInclusionIso_hom_inclusion γ
    have hh' : (DiagonalZeroCycle.zeroIdealInclusionIso γ).hom ≫ δ ≫ j =
        Hom.zeroInclusion (Scheme.Hom.idealInclusion γ) := by
      rw [hδ]
      exact hh
    exact congrArg (fun f => f z) hh'
  let Z := Hom.zeroRestrictionIso (Scheme.Hom.idealInclusion γ) j hz ≪≫
    DiagonalZeroCycle.zeroIdealInclusionIso γ
  have hZ : Z.hom ≫ δ = Hom.zeroInclusion ε := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, hδ, Z, Iso.trans_hom,
      DiagonalZeroCycle.zeroIdealInclusionIso_hom_inclusion,
      Hom.zeroRestrictionIso_hom_inclusion]
    rfl
  have hp : δ ≫ p = 𝟙 X.left := by simpa only [p, ← Category.assoc, hδ] using hq
  have hgraph : Cor.ofFiniteFlatSpan (X := X) (Y := Y)
      (Hom.zeroInclusion ε ≫ p) (Hom.zeroInclusion ε ≫ g)
      (by simpa only [p, Category.assoc] using
        congrArg (fun f => Hom.zeroInclusion ε ≫ f) hbase) =
      (Cor.graphFunctor k).map φ := by
    rw [← DiagonalZeroCycle.ofFiniteFlatSpan_id φ]
    apply PolynomialPencilCycles.span_eq_of_iso Z
    · rw [Category.comp_id, ← hZ, Category.assoc, hp, Category.comp_id]
    · rw [← hZ, Category.assoc, hg]
  rw [hgraph]
  rfl

end Motivic.Cor
