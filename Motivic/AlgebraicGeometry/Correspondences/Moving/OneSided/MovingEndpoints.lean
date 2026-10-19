/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Endpoints
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.PolynomialCycles
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.SignedProductEndpoints
/-! # The single diagonal pencil gives genuine dense-open moving correspondences -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.PolynomialPencil
universe u
namespace Motivic.OneSidedMovingEndpoints
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLine

/-- The two literal dense-open moving endpoints on the original affine-line cylinder. -/
def HasMovingEndpoints {k : Type u} [Field k]
    {S X V : SmoothSite (Spec (.of k))} (φ : S ⟶ X) (v : V ⟶ X) : Prop :=
  ∃ β : Cor.mk S ⟶ Cor.mk V,
  ∃ α : Cor.mk (SmoothSite.a1Cylinder (.of k) S) ⟶ Cor.mk X,
    (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) S 0) ≫ α =
      (Cor.graphFunctor k).map φ ∧
    (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) S 1) ≫ α =
      β ≫ (Cor.graphFunctor k).map v

/-- Actual polynomial-family and original divisor spans produce beta and alpha.
The support premises concern the two endpoint zero schemes, not a presumed
correspondence or homotopy. The Serre producer proves these premises geometrically. -/
theorem exists_moving_endpoints {k : Type u} [Field k]
    {S X V : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
    (p : C ⟶ S.left)
    [Smooth (p ≫ S.hom)] [IsSeparated (p ≫ S.hom)] [QuasiCompact (p ≫ S.hom)]
    (δ : S.left ⟶ C) [IsClosedImmersion δ] (hδp : δ ≫ p = 𝟙 _)
    (hI : IsLocallyRankOne C (Scheme.Hom.idealModule δ))
    (M : LineBundle C) (b : M.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono b]
    (a : (tensorLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩ M).val ⟶
      SheafOfModules.unit C.ringCatSheaf)
    (g : C ⟶ X.left) (φ : S ⟶ X) (hδg : δ ≫ g = φ.left)
    (hbase : p ≫ S.hom = g ≫ X.hom)
    (v : V ⟶ X) [IsOpenImmersion v.left]
    (haV : Set.range (Hom.zeroInclusion a ≫ g) ⊆ Set.range v.left)
    (hbV : Set.range (Hom.zeroInclusion b ≫ g) ⊆ Set.range v.left)
    [IsFinite (Hom.zeroInclusion b ≫ p)] [Flat (Hom.zeroInclusion b ≫ p)]
    [IsFinite (familySource p (tensorLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩ M)
      (Hom.productSection (Scheme.Hom.idealInclusion δ) b) a)]
    [Flat (familySource p (tensorLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩ M)
      (Hom.productSection (Scheme.Hom.idealInclusion δ) b) a)] :
    HasMovingEndpoints φ v := by
  let L := tensorLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩ M
  have hff := PolynomialPencilCycles.one_finite_flat S.hom p L
    (Hom.productSection (Scheme.Hom.idealInclusion δ) b) a
  let := hff.1
  let := hff.2
  let ga := IsOpenImmersion.lift v.left (Hom.zeroInclusion a ≫ g) haV
  let gb := IsOpenImmersion.lift v.left (Hom.zeroInclusion b ≫ g) hbV
  have hga : ga ≫ v.left = Hom.zeroInclusion a ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hgb : gb ≫ v.left = Hom.zeroInclusion b ≫ g := IsOpenImmersion.lift_fac _ _ _
  have ba : (Hom.zeroInclusion a ≫ p) ≫ S.hom = ga ≫ V.hom := by
    rw [← MorphismProperty.Over.w v, ← Category.assoc, hga]
    simp only [Category.assoc, hbase]
  have bb : (Hom.zeroInclusion b ≫ p) ≫ S.hom = gb ≫ V.hom := by
    rw [← MorphismProperty.Over.w v, ← Category.assoc, hgb]
    simp only [Category.assoc, hbase]
  let β := Cor.ofFiniteFlatSpan (Hom.zeroInclusion a ≫ p) ga ba -
    Cor.ofFiniteFlatSpan (Hom.zeroInclusion b ≫ p) gb bb
  let α := signedCorrespondence p L (Hom.productSection (Scheme.Hom.idealInclusion δ) b)
    a g hbase b
  refine ⟨β, α, ?_, ?_⟩
  · rw [← Endpoints.endpointMorphism_eq_a1Section]
    exact signed_diagonal_zero p δ hδp hI M b a g φ hδg hbase
  · rw [← Endpoints.endpointMorphism_eq_a1Section]
    change _ = (Cor.ofFiniteFlatSpan _ ga ba - Cor.ofFiniteFlatSpan _ gb bb) ≫ _
    rw [Preadditive.sub_comp, Cor.ofFiniteFlatSpan_comp_graph,
      Cor.ofFiniteFlatSpan_comp_graph]
    simpa only [hga, hgb] using
      signed_one p L (Hom.productSection (Scheme.Hom.idealInclusion δ) b) a g hbase b

end Motivic.OneSidedMovingEndpoints
