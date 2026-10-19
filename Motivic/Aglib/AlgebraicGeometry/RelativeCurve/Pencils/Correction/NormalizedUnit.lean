/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionNormChart
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalUnitBoundary
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.Unit
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.UnitDomainGeneric
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.AffineBoundaryScalarRestriction
public import Motivic.Aglib.AlgebraicGeometry.Scheme.Sections.CoproductBoundary
/-! # Normalization of the original correction norm product

The fixed good open and its chart units are constructed from the original
sections. Every boundary calculation takes place on the complete scheme fiber.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NormalizedUnit`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.NativeCorrectionNormalizedUnit`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A Z C P D DA : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] (f : C ⟶ P) [IsFinite f]
  (jB : Y ⟶ C) [IsOpenImmersion jB] (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)] (p : Y ⟶ X)
  (hq : jB ≫ (f ≫ π) = p ≫ q)
  (hret : jB ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (a : A ⟶ X) [Flat a] (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
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
  (H : IsPullback s (𝟙 Z) (jB ≫ f) (z ≫ jA))

include hret hpairA hN hbE H in
/-- Every actual free chart of the unchanged good open has value one on both
complete original boundary fibers. All required denominator units are derived
from the chart's membership in the good open. -/
theorem correctionNormChart_boundary_values
    [IsAffineHom (z ≫ jA)] [IsAffineHom dA]
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
    (U : (pullback (a ≫ q) π).Opens) (hU : IsAffineOpen U)
    (hUV : U ≤ functionalNormProductUnitDomain
      (normProductMap π f (a ≫ q)) (dualLineBundle _ N) (dualLineBundle _ N)
      (sectionDualFunctional _ N nS) (sectionDualFunctional _ N dS)
      (pullbackLineBundle (retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm))
        (dualLineBundle _ (tensorLineBundle _ LA
          (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))))
      (pullbackLineBundle (retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm))
        (dualLineBundle _ (tensorLineBundle _ LA
          (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)))))
      (pullbackUnitMap (retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm))
        (sectionDualFunctional _ _ aA))
      (pullbackUnitMap (retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm))
        (sectionDualFunctional _ _ (twistedIdealSection _
          (Hom.relativeCompactificationGraphLine π jA) LA
          (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA)))) :
    let F := normProductMap π f (a ≫ q)
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
    let M := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let L := pullbackLineBundle τ (dualLineBundle _ M)
    let μ := functionalNormProductChart F (dualLineBundle _ N)
      (sectionDualFunctional _ N nS) (sectionDualFunctional _ N dS) L
      (pullbackUnitMap τ (sectionDualFunctional _ M aA))
      (pullbackUnitMap τ (sectionDualFunctional _ M cA)) U hU hUV
    let : Algebra Γ(pullback (a ≫ q) π, U) Γ(pullback F hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(pullback (a ≫ q) π, U) Γ(pullback F hU.fromSpec, ⊤)],
      FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd (normMarkedProductMap π (a ≫ q) dA) hU.fromSpec) μ = 1 ∧
      FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd (normMarkedProductMap π (a ≫ q) (z ≫ jA)) hU.fromSpec) μ = 1 := by
  let F := normProductMap π f (a ≫ q)
  let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
  let M := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
    (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
  let L := pullbackLineBundle τ (dualLineBundle _ M)
  let nφ := sectionDualFunctional _ N nS
  let dφ := sectionDualFunctional _ N dS
  let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
  let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
  have hUrange : Set.range U.ι ⊆
      (functionalNormProductUnitDomain F (dualLineBundle _ N) (dualLineBundle _ N)
        nφ dφ L L aφ cφ : Set (pullback (a ≫ q) π : Scheme.{u})) := by
    rw [Opens.range_ι]
    exact fun _ hx => hUV hx
  have hwrange : Set.range hU.fromSpec ⊆
      (functionalNormProductUnitDomain F (dualLineBundle _ N) (dualLineBundle _ N)
        nφ dφ L L aφ cφ : Set (pullback (a ≫ q) π : Scheme.{u})) := by
    rw [hU.range_fromSpec]
    exact hUV
  have ht := functionalNormProductUnitDomain_target_isIso F _ _ nφ dφ L L aφ cφ U.ι hUrange
  have hw := functionalNormProductUnitDomain_target_isIso F _ _ nφ dφ L L aφ cφ hU.fromSpec hwrange
  have hsource := functionalNormProductUnitDomain_source_isIso F _ _ nφ dφ L L aφ cφ
    hU.fromSpec hwrange
  let := ht.2
  let := hw.2
  let := hsource.2
  let := pullbackUnitMap_comp_isIso_of_nested τ U.ι (sectionDualFunctional _ M cA)
  let := pullbackUnitMap_comp_isIso_of_nested τ hU.fromSpec (sectionDualFunctional _ M cA)
  let : Algebra Γ(pullback (a ≫ q) π, U) Γ(pullback F hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F hU.fromSpec)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  have hmarked := originalCorrectionNormChart_marked_fiber_eq_one q π f jB jA p hq hret hA
    a z s hs hsK e ha d bE hbE N nS dS hN dA hdA LA aA bA hpairA H hU.fromSpec
  have hinfinity := originalCorrectionNormChart_infinity_fiber_eq_one q π f jB jA p hq hA
    a z s hs e ha d N nS dS hN dA hdA LA aA bA hpairA bI hbI hU.fromSpec
  have hc := functionalQuotient_parameter_fromSpec_coefficient τ
    (sectionDualFunctional _ M aA) (sectionDualFunctional _ M cA) U hU
  dsimp only at hmarked hinfinity
  rw [hc] at hmarked hinfinity
  exact ⟨hinfinity, hmarked⟩

include hret hpairA hN hbE H in
/-- The original correction sections construct a unit on the exact good open,
with the entire original boundary factoring through it and having value one.
The free charts are inherited from the original finite compactification map. -/
theorem exists_originalCorrectionNormalizedUnit
    [IsClosedImmersion (z ≫ jA)] [IsAffineHom dA]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) nS)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q (f ≫ π) jB p hq a z s hs d) dS)]
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
    {ι : Type u} (B : ι → CommRingCat.{u}) (w : ∀ i, Spec (B i) ⟶ P)
    [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (w i))
    (hfree : ∀ i,
      let : Algebra (B i) Γ(pullback f (w i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (w i))).toAlgebra
      Module.Free (B i) Γ(pullback f (w i), ⊤)) :
    let T := pullback (a ≫ q) π
    let F := normProductMap π f (a ≫ q)
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
    let M := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let L := pullbackLineBundle τ (dualLineBundle _ M)
    let nφ := sectionDualFunctional _ N nS
    let dφ := sectionDualFunctional _ N dS
    let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
    let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
    let V := functionalNormProductUnitDomain F (dualLineBundle _ N) (dualLineBundle _ N)
      nφ dφ L L aφ cφ
    let E := pullback (a ≫ q) (dA ≫ π) ⨿ pullback (a ≫ q) ((z ≫ jA) ≫ π)
    ∀ [IsIntegral T] [Mono nφ] [Mono dφ] [Mono aφ] [Mono cφ],
      let := functionalNormProductUnitDomain_nonempty F (dualLineBundle _ N)
        (dualLineBundle _ N) nφ dφ L L aφ cφ
      ∃ (r : Γ(T, V)) (β : E ⟶ V.toScheme),
        β ≫ V.ι = normFullBoundaryMap π (a ≫ q) dA (z ≫ jA) ∧ IsUnit r ∧
        T.germToFunctionField V r =
          genericFiberLineRatioNorm (𝟙 T) L aφ cφ *
            genericFiberLineRatioNorm F (dualLineBundle _ N) nφ dφ ∧
        (normFullBoundaryMap π (a ≫ q) dA (z ≫ jA)).app V r = 1 := by
  let T := pullback (a ≫ q) π
  let F := normProductMap π f (a ≫ q)
  let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) hA.symm)
  let M := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
    (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
  let L := pullbackLineBundle τ (dualLineBundle _ M)
  let nφ := sectionDualFunctional _ N nS
  let dφ := sectionDualFunctional _ N dS
  let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
  let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
  let V := functionalNormProductUnitDomain F (dualLineBundle _ N) (dualLineBundle _ N)
    nφ dφ L L aφ cφ
  let E := pullback (a ≫ q) (dA ≫ π) ⨿ pullback (a ≫ q) ((z ≫ jA) ≫ π)
  let b : E ⟶ T := normFullBoundaryMap π (a ≫ q) dA (z ≫ jA)
  dsimp only
  intro hT hn hd haφ hcφ
  let := hT
  let := hn
  let := hd
  let := haφ
  let := hcφ
  let : Nonempty V := functionalNormProductUnitDomain_nonempty F
    (dualLineBundle _ N) (dualLineBundle _ N) nφ dφ L L aφ cφ
  let R := genericFiberLineRatioNorm (𝟙 T) L aφ cφ *
    genericFiberLineRatioNorm F (dualLineBundle _ N) nφ dφ
  choose U hU hxU hUV hfreeU using fun x : V =>
    normProductMap_exists_free_affine_neighborhood_subset π f (a ≫ q)
      B w hcover hfree V x.1 x.2
  have hunion : iSup U = V := by
    apply le_antisymm
    · exact iSup_le hUV
    · intro x hx
      exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  let (x : V) : Nonempty (U x) := ⟨⟨x.1, hxU x⟩⟩
  let μ (x : V) := functionalNormProductChart F (dualLineBundle _ N) nφ dφ L aφ cφ
    (U x) (hU x) (hUV x)
  have hμ (x : V) : IsUnit (μ x) ∧ T.germToFunctionField (U x) (μ x) = R := by
    let : Algebra Γ(T, U x) Γ(pullback F (hU x).fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (hU x).fromSpec)).toAlgebra
    let := hfreeU x
    exact functionalNormProductChart_unit_and_germ F (dualLineBundle _ N) nφ dφ L aφ cφ
      (U x) (hU x) (hUV x)
  have hbμ (x : V) : b.app (U x) (μ x) = 1 := by
    let : Algebra Γ(T, U x) Γ(pullback F (hU x).fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (hU x).fromSpec)).toAlgebra
    let := hfreeU x
    have hv := correctionNormChart_boundary_values q π f jB jA p hq hret hA
      a z s hs hsK e ha d bE hbE N nS dS hN dA hdA LA aA bA hpairA H
      bI hbI (U x) (hU x) (hUV x)
    exact Scheme.coprod_desc_app_eq_one _ _ (U x) (μ x)
      (FiniteSchemeNormBaseChange.app_eq_one_of_affine_pullback_scalar_eq_one
        _ _ (hU x) _ hv.1)
      (FiniteSchemeNormBaseChange.app_eq_one_of_affine_pullback_scalar_eq_one
        _ _ (hU x) _ hv.2)
  have hboundary : Set.range b ⊆ (V : Set T) :=
    originalCorrectionNorm_boundary_subset_goodOpen q π f jB jA p hq hA
      a z s hs hsK e ha d bE hbE N nS dS dA hdA LA aA bA hpairA bI hbI
  have : Nonempty (iSup U : T.Opens) := hunion.symm ▸ (inferInstance : Nonempty V)
  obtain ⟨r, β, hβ, hr, hg, _, hb⟩ := exists_rationalUnit_boundary_gluing b U R μ
    (fun x => (hμ x).1) (fun x => (hμ x).2) hbμ (hunion.symm ▸ hboundary)
  have result : ∀ W : T.Opens, W = iSup U → ∀ [Nonempty W],
      ∃ (r : Γ(T, W)) (β : E ⟶ W.toScheme),
        β ≫ W.ι = b ∧ IsUnit r ∧ T.germToFunctionField W r = R ∧ b.app W r = 1 := by
    rintro W rfl hW
    exact ⟨r, β, hβ, hr, hg, hb⟩
  exact result V hunion.symm

end AlgebraicGeometry.Scheme.RelativeCurvePencil
