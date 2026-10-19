/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormBoundaryRange
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.FactorBoundary
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.UnitDomain
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramed.SectionTransport
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.GraphRatioBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.FunctionalQuotientAffineChart
/-! # The original correction boundary lies in the unchanged unit domain

The original inverse-infinity and residual maps control the whole inverse
boundary. Point supports are used only for open factorization; no function
identity on a closed scheme is inferred from them.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalUnitBoundary`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.NormalizedUnit`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A Z C D : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X) (z : Z ⟶ X)
  (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C)

/-- The exact prescribed correction boundary has the full inverse support. -/
theorem range_psiBoundaryInclusion :
    Set.range (psiBoundaryInclusion q π j p hq a z s hs d) =
      (pullback.snd (a ≫ q) π) ⁻¹' (Set.range d ∪ Set.range (s ≫ j)) := by
  rw [psiBoundaryInclusion, Hom.range_coprod_desc, Set.preimage_union]
  congr 1
  · exact Scheme.Pullback.range_fst _ _
  · exact Scheme.range_snd_eq_preimage_of_isPullback _ _ _ _
      (psiZeroInclusion_isPullback q π j p hq a z s hs)

/-- The product-boundary presentation and original prescribed presentation have
identical support; their scheme structures are not replaced by this equality. -/
theorem range_normFullBoundaryMap_eq_psiBoundaryInclusion :
    Set.range (Hom.normFullBoundaryMap π (a ≫ q) d (s ≫ j)) =
      Set.range (psiBoundaryInclusion q π j p hq a z s hs d) := by
  rw [Hom.range_normFullBoundaryMap, range_psiBoundaryInclusion]

/-- The same original correction sections supply unit loci containing every
point of the actual product boundary. -/
theorem range_normFullBoundaryMap_subset_sectionUnitOpen
    (N : LineBundle (pullback (a ≫ q) π))
    (n : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) n)] :
    Set.range (Hom.normFullBoundaryMap π (a ≫ q) d (s ≫ j)) ⊆
      (zeroSupportUnitOpen (dualLineBundle _ N) (sectionDualFunctional _ N n) :
        Set (pullback (a ≫ q) π : Scheme.{u})) := by
  rw [range_normFullBoundaryMap_eq_psiBoundaryInclusion q π j p hq a z s hs d]
  let := sectionDualFunctional_pullback_map_isIso
    (psiBoundaryInclusion q π j p hq a z s hs d) N n
  exact range_subset_zeroSupportUnitOpen_of_pullback_isIso _ _ _

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The whole inverse target boundary lies in the actual original correction
section's unit open, with the original residual and inverse-infinity factors. -/
theorem normProductMap_preimage_boundary_subset_sectionUnitOpen
    {S X Y A Z C P D I : Scheme.{u}}
    (q : X ⟶ S) (π : P ⟶ S) (f : C ⟶ P) [IsFinite f]
    (j : Y ⟶ C) (p : Y ⟶ X)
    (hq : j ≫ (f ≫ π) = p ≫ q) (a : A ⟶ X)
    (z : Z ⟶ X) (jA : X ⟶ P)
    (s : Z ⟶ Y) (hs : s ≫ p = z) (hsK : (s ≫ j) ≫ f = z ≫ jA)
    (d : D ⟶ C) (i : I ⟶ P)
    (bI : pullback f i ⟶ D) (hbI : bI ≫ d = pullback.fst f i)
    (bE : (Scheme.residualMarkedFiberOpen f j (z ≫ jA) s hsK).toScheme ⟶ D)
    (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j (z ≫ jA) s hsK)
    (N : LineBundle (pullback (a ≫ q) (f ≫ π)))
    (n : SheafOfModules.unit (pullback (a ≫ q) (f ≫ π)).ringCatSheaf ⟶ N.val)
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d) n)] :
    (Hom.normProductMap π f (a ≫ q)) ⁻¹'
        Set.range (Hom.normFullBoundaryMap π (a ≫ q) i (z ≫ jA)) ⊆
      (zeroSupportUnitOpen (dualLineBundle _ N) (sectionDualFunctional _ N n) :
        Set (pullback (a ≫ q) (f ≫ π) : Scheme.{u})) := by
  intro x hx
  exact range_normFullBoundaryMap_subset_sectionUnitOpen q (f ≫ π) j p hq a z s hs d N n
    (Hom.normProductMap_preimage_fullBoundary_subset π f j (z ≫ jA) s hsK
      d i bI hbI bE hbE (a ≫ q) hx)

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The common full boundary has the same full inverse-support description. -/
theorem range_commonBoundaryInclusion
    {S C Y A Z D : Scheme.{u}} (π : C ⟶ S) (j : Y ⟶ C)
    (a : A ⟶ Y) (s : Z ⟶ Y) (d : D ⟶ C) :
    Set.range (commonBoundaryInclusion π j a s d) =
      (pullback.snd (commonProjection π j a) π) ⁻¹'
        (Set.range d ∪ Set.range (s ≫ j)) := by
  rw [commonBoundaryInclusion, Hom.range_coprod_desc, Set.preimage_union]
  congr 1
  · exact Scheme.Pullback.range_fst _ _
  · exact Scheme.range_snd_eq_preimage_of_isPullback _ _ _ _
      (commonZeroInclusion_isPullback π j a s)

private theorem pullback_map_nested_isIso
    {X Y B : Scheme.{u}} (τ : Y ⟶ X) (b : B ⟶ Y) {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (pullbackUnitMap (b ≫ τ) φ)] :
    IsIso ((Modules.pullback b).map (pullbackUnitMap τ φ)) := by
  have hn := pullbackUnitMap_nested_isIso_of_comp τ b φ
  change IsIso ((Modules.pullback b).map (pullbackUnitMap τ φ) ≫
    (pullbackUnitIso b).hom) at hn
  exact IsIso.of_isIso_comp_right _ (pullbackUnitIso b).hom

/-- Disjointness and the original prescribed graph pair make both actual target
functionals units on the entire common boundary. The graph pole is not assumed
invertible over the unrestricted parameter. -/
theorem correctionTargetFunctional_fullBoundary_isIso
    {S X A Z P D : Scheme.{u}}
    (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (π : P ⟶ S) [IsSeparated π] (j : X ⟶ P) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ π)] (hA : j ≫ π = q)
    (a : A ⟶ X) [Flat a] (z : Z ⟶ X)
    (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      Hom.idealModule (Hom.boundaryGraphTarget q z))
    (ha : Disjoint (Set.range a) (Set.range z))
    (d : D ⟶ P) (hd : Disjoint (Set.range j) (Set.range d))
    (L : LineBundle (pullback (j ≫ π) π))
    (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ L.val)
    (hpair :
      let zA :=
        coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j z)
      pullbackSectionMap zA aS ≫ pullbackTensorMap zA L.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
      tensorUnitSection (pullbackSectionMap zA bS)
        (Hom.relativeFullBoundaryFrame q π j (𝟙 X) (hA.trans (Category.id_comp q).symm)
          z z (Category.comp_id z) (IsPullback.id_vert z) e d hd).inv)
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j z)) aS)] :
    let M := tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
    let cS := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) L
      (Hom.idealInclusion (Hom.compactificationGraph π j)) bS
    IsIso ((Modules.pullback (commonBoundaryInclusion π j a z d)).map
      (pullbackUnitMap (commonToLambda π j a) (sectionDualFunctional _ M aS))) ∧
    IsIso ((Modules.pullback (commonBoundaryInclusion π j a z d)).map
      (pullbackUnitMap (commonToLambda π j a) (sectionDualFunctional _ M cS))) := by
  let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j z)
  let v := commonBoundaryToLambda π j a z d
  let M := tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
  let cS := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) L
    (Hom.idealInclusion (Hom.compactificationGraph π j)) bS
  obtain ⟨hc, _, _⟩ := commonGraphRatio_boundary_inverse q π j (𝟙 X)
    (hA.trans (Category.id_comp q).symm)
    a a (𝟙 A) (by simp) z z (Category.comp_id z) (IsPullback.id_vert z) e ha d hd L aS bS hpair
  let := hc
  have han : IsIso (pullbackSectionMap (v ≫ zA) aS) := by
    rw [← pullbackSectionMap_comp]
    have : IsIso (pullbackSectionMap v (pullbackSectionMap zA aS)) := by
      change IsIso ((pullbackUnitIso v).inv ≫ (Modules.pullback v).map (pullbackSectionMap zA aS))
      infer_instance
    infer_instance
  have hb : commonBoundaryInclusion π j a z d ≫ commonToLambda π j a = v ≫ zA :=
    (commonBoundaryToLambda_inclusion π j a z d).symm
  have haφ : IsIso (pullbackUnitMap
      (commonBoundaryInclusion π j a z d ≫ commonToLambda π j a)
      (sectionDualFunctional _ M aS)) := by
    rw [hb]
    exact sectionDualFunctional_pullback_isIso _ M aS
  have hcφ : IsIso (pullbackUnitMap
      (commonBoundaryInclusion π j a z d ≫ commonToLambda π j a)
      (sectionDualFunctional _ M cS)) := by
    rw [hb]
    exact sectionDualFunctional_pullback_isIso _ M cS
  exact ⟨pullback_map_nested_isIso _ _ _, pullback_map_nested_isIso _ _ _⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A Z C P D DA : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] (f : C ⟶ P) [IsFinite f]
  (jB : Y ⟶ C) [IsOpenImmersion jB] (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)] (p : Y ⟶ X)
  (hq : jB ≫ (f ≫ π) = p ≫ q)
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (a : A ⟶ X) [Flat a] (z : Z ⟶ X) [IsClosedImmersion (z ≫ jA)] (s : Z ⟶ Y) (hs : s ≫ p = z)
  (hsK : (s ≫ jB) ≫ f = z ≫ jA)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z))
  (d : D ⟶ C)
  (bE : (Scheme.residualMarkedFiberOpen f jB (z ≫ jA) s hsK).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f jB (z ≫ jA) s hsK)
  (N : LineBundle (pullback (a ≫ q) (f ≫ π)))
  (nS dS : SheafOfModules.unit (pullback (a ≫ q) (f ≫ π)).ringCatSheaf ⟶ N.val)
  (hN : pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) nS =
    (fixedProductBoundaryFrame q (f ≫ π) a z e ha d).hom ≫
      pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) dS)
  (dA : DA ⟶ P) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  (hpairA :
    let zA :=
      coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z)
    pullbackSectionMap zA aA ≫ pullbackTensorMap zA LA.val
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)).val =
    tensorUnitSection (pullbackSectionMap zA bA)
      (Hom.relativeFullBoundaryFrame q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)
  [IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap π jA dA) (Hom.graphBoundaryRestriction π jA z)) aA)]
  [hnBoundary : IsIso (pullbackSectionMap
    (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) nS)]
  [hdBoundary : IsIso (pullbackSectionMap
    (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) dS)]

omit [IsOpenImmersion jB] [IsClosedImmersion (z ≫ jA)] in
include ha hpairA hbE hnBoundary hdBoundary in
/-- The actual full target boundary is retained by the fixed E5 good open.
All four unit loci come from the same original sections; target pole
invertibility is proved from the disjoint parameter and prescribed pair. -/
theorem originalCorrectionNorm_boundary_subset_goodOpen
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA) :
    let F := Hom.normProductMap π f (a ≫ q)
    let τ := Hom.retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
    let M := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let L := pullbackLineBundle τ (dualLineBundle _ M)
    Set.range (Hom.normFullBoundaryMap π (a ≫ q) dA (z ≫ jA)) ⊆
      (Scheme.functionalNormProductUnitDomain F (dualLineBundle _ N) (dualLineBundle _ N)
        (sectionDualFunctional _ N nS) (sectionDualFunctional _ N dS) L L
        (pullbackUnitMap τ (sectionDualFunctional _ M aA))
        (pullbackUnitMap τ (sectionDualFunctional _ M cA)) :
          Set (pullback (a ≫ q) π : Scheme.{u})) := by
  subst q
  let F := Hom.normProductMap π f (a ≫ (jA ≫ π))
  let τ := Hom.retainedNormParameterMap π (a ≫ (jA ≫ π)) jA a rfl
  let M := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
    (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
  let L := pullbackLineBundle τ (dualLineBundle _ M)
  let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
  let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
  obtain ⟨haφ, hcφ⟩ := correctionTargetFunctional_fullBoundary_isIso (jA ≫ π) π jA rfl
    a z e ha dA hdA LA aA bA hpairA
  let := haφ
  let := hcφ
  have hsame : Set.range (Hom.normFullBoundaryMap π (a ≫ (jA ≫ π)) dA (z ≫ jA)) =
      Set.range (commonBoundaryInclusion π jA a z dA) := by
    rw [Hom.range_normFullBoundaryMap, range_commonBoundaryInclusion]
  have hn := normProductMap_preimage_boundary_subset_sectionUnitOpen (jA ≫ π) π f jB p hq
    a z jA s hs hsK d dA bI hbI bE hbE N nS
  have hd := normProductMap_preimage_boundary_subset_sectionUnitOpen (jA ≫ π) π f jB p hq
    a z jA s hs hsK d dA bI hbI bE hbE N dS
  dsimp only
  intro x hx
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact range_subset_zeroSupportUnitOpen_of_pullback_isIso L aφ
      (commonBoundaryInclusion π jA a z dA) (hsame ▸ hx)
  · exact range_subset_zeroSupportUnitOpen_of_pullback_isIso L cφ
      (commonBoundaryInclusion π jA a z dA) (hsame ▸ hx)
  · exact F.subset_finiteDescentOpen
      (zeroSupportUnitOpen (dualLineBundle _ N) (sectionDualFunctional _ N nS) ⊓
        zeroSupportUnitOpen (dualLineBundle _ N) (sectionDualFunctional _ N dS))
      (Set.range (Hom.normFullBoundaryMap π (a ≫ (jA ≫ π)) dA (z ≫ jA)))
      (fun _ h => ⟨hn h, hd h⟩) hx

end AlgebraicGeometry.Scheme.RelativeCurvePencil
