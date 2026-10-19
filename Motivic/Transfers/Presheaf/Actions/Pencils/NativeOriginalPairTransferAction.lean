/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Transfers.Presheaf.Actions.Norm.OriginalPair
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalPairNormDictionary
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalTargetLambda
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalPairNormBoundaryUnits
/-! # The actual component two-pair transfer consumer

This intermediate consumer fixes the original scheme maps and the same source/target sections.
It accepts the genuine normalized-unit tuple together, not a correspondence or action equality.
The native caller must still produce that tuple internally and use the literal lambda dictionary.
-/
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom Scheme.RelativeCurvePencil
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open Motivic.Cor
universe u w
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- The site family has literally the unchanged original parameter schemes. -/
def originalComponentPairStructureMap (Y X : SmoothSite (Spec (.of k))) :
    ∀ i, originalNormPairParameter Y.left X.left i ⟶ Spec (.of k) :=
  Fin.twoCases Y.hom X.hom

instance (Y X : SmoothSite (Spec (.of k))) (i : Fin 2) :
    Smooth (originalComponentPairStructureMap Y X i) := by
  fin_cases i
  · change Smooth Y.hom
    infer_instance
  · change Smooth X.hom
    infer_instance

instance (Y X : SmoothSite (Spec (.of k))) (i : Fin 2) :
    IsSeparated (originalComponentPairStructureMap Y X i) := by
  fin_cases i
  · change IsSeparated Y.hom
    infer_instance
  · change IsSeparated X.hom
    infer_instance

instance (Y X : SmoothSite (Spec (.of k))) (i : Fin 2) :
    QuasiCompact (originalComponentPairStructureMap Y X i) := by
  fin_cases i
  · change QuasiCompact Y.hom
    infer_instance
  · change QuasiCompact X.hom
    infer_instance

/-- No transport or replacement of the original parameter objects is made. -/
def originalComponentPairSite (Y X : SmoothSite (Spec (.of k))) (i : Fin 2) :
    SmoothSite (Spec (.of k)) := SmoothSite.mk (originalComponentPairStructureMap Y X i)

/-- The original component map and its composite with the given cover map. -/
def originalComponentPairSiteMap {K Y X : SmoothSite (Spec (.of k))}
    (ι : K ⟶ Y) (p : Y ⟶ X) (i : Fin 2) : K ⟶ originalComponentPairSite Y X i :=
  SmoothSite.homMk (originalNormPairParameterMap ι.left p.left i) (by
    fin_cases i
    · exact ι.w
    · change (ι.left ≫ p.left) ≫ X.hom = K.hom
      have hp : p.left ≫ X.hom = Y.hom := p.w
      have hi : ι.left ≫ Y.hom = K.hom := ι.w
      rw [Category.assoc, hp, hi])

/-- The two original graph target maps are the cover and the identity. -/
def originalComponentPairGraphMap {Y X : SmoothSite (Spec (.of k))}
    (p : Y ⟶ X) (i : Fin 2) : originalComponentPairSite Y X i ⟶ X :=
  SmoothSite.homMk (originalNormPairGraphTarget p.left i) (by
    fin_cases i
    · exact p.w
    · exact Category.id_comp _)

variable {k : Type u} [Field k]
  (Ksite Ysite Xsite Asite Bsite : SmoothSite (Spec (.of k)))
  {S Cbar Pbar Zmark Dsrc Dtgt : Scheme.{u}}
  (qX : Xsite.left ⟶ S) [IsSeparated qX] [SmoothOfRelativeDimension 1 qX]
  (π : Pbar ⟶ S) [IsSeparated π] (F : Cbar ⟶ Pbar) [IsSeparated (F ≫ π)]
  (jB : Ysite.left ⟶ Cbar) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ (F ≫ π))]
  (jA : Xsite.left ⟶ Pbar) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)] [IsSeparated (jA ≫ π)]
  (p : Ysite ⟶ Xsite) [Flat p.left] (ι : Ksite ⟶ Ysite)
  (hA : jA ≫ π = qX)
  (hret : jB ≫ F = p.left ≫ jA)
  (hbase : jB ≫ (F ≫ π) = p.left ≫ qX)
  (a : Asite ⟶ Xsite) [IsOpenImmersion a.left]
  (vB : Bsite ⟶ Ysite) (bA : Bsite ⟶ Asite) (hsmall : vB.left ≫ p.left = bA.left ≫ a.left)
  (z : Zmark ⟶ Xsite.left) (s : Zmark ⟶ Ysite.left)
  (hs : s ≫ p.left = z) (H : IsPullback s (𝟙 _) p.left z)
  (e : SheafOfModules.unit (pullback qX (z ≫ qX)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget qX z))
  (ha : Disjoint (Set.range a.left) (Set.range z))
  (dB : Dsrc ⟶ Cbar) (hdB : Disjoint (Set.range jB) (Set.range dB))
  (dA : Dtgt ⟶ Pbar) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (hsmallCoverB : ∀ x : Cbar, x ∈ Set.range (vB.left ≫ jB) ∨
    x ∈ Set.range dB ∨ x ∈ Set.range (s ≫ jB))
  (hsmallCoverA : ∀ x : Pbar, x ∈ Set.range (a.left ≫ jA) ∨
    x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ jA))
  (source : BoundarySectionData qX (F ≫ π) jB p.left hbase a.left z s hs H e ha dB hdB)
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))).val)
  (bAsec : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  [IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA)]
  [IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bAsec)]
  (hpairA :
    pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA ≫
        pullbackTensorMap (fullBoundaryProductMap π jA dA z) LA.val
          (dualLineBundle _ (relativeCompactificationGraphLine π jA)).val =
      tensorUnitSection (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bAsec)
        (relativeFullBoundaryFrame qX π jA (𝟙 _)
          (hA.trans (Category.id_comp qX).symm) z z (Category.comp_id z)
          (IsPullback.id_vert z) e dA hdA).inv)

local notation "X" => Ksite
local notation "Y" => Xsite
local notation "Z" => Asite
local notation "uMap" => a
local notation "O" => (originalComponentPairSite Ysite Xsite)
local notation "α" => (originalComponentPairSiteMap ι p)
local notation "T" =>
  (pullback (originalNormPairComponentBase π F jB ι.left) π : Scheme)
local notation "V" => (retainedProduct (originalNormPairComponentBase π F jB ι.left) π jA)
local notation "q" => (pullback.fst (originalNormPairComponentBase π F jB ι.left) π)
local notation "jT" => (retainedProductInclusion (originalNormPairComponentBase π F jB ι.left) π
  jA)
local notation "C" => (originalNormPairChangedCompact π F jB ι.left)
local notation "U" => (originalNormPairChangedRetained π F jB ι.left jA)
local notation "B" => (originalNormPairChangedInfinity π F jB ι.left dB dA)
local notation "C₀" => (originalNormPairCompact π F jB jA)
local notation "U₀" => (originalNormPairRetained π F jB jA)
local notation "B₀" => (originalNormPairInfinity π F jB jA dB dA)
local notation "f" => (originalNormPairFiniteMap π F jB ι.left)
local notation "i" => (originalNormPairChangedInfinityInclusion π F jB ι.left dB dA)
local notation "j" => (originalNormPairChangedInclusion π F jB ι.left jA)
local notation "w" => (originalNormPairRetainedFiniteMap π F jB ι.left jA p.left hret)
local notation "q₀" => (originalNormPairProjection π F jB jA)
local notation "i₀" => (originalNormPairInfinityInclusion π F jB jA dB dA)
local notation "j₀" => (originalNormPairRetainedInclusion π F jB jA)
local notation "c" => (originalNormPairCompactMap π F jB ι.left jA p.left hret)
local notation "v" => (originalNormPairRetainedMap π F jB ι.left jA p.left hret)
local notation "γ" => (originalNormPairGraph π F jB jA)
local notation "hI" => (originalNormPairGraph_rankOne π F jB jA)
local notation "δ" => (originalNormPairRetainedGraph π F jB jA)
local notation "M" => (source.originalNormPairLine qX π F jB jA p.left hbase a.left z s hs H e ha dB
  hdB LA)
local notation "aS" => (source.originalNormPairNumerator qX π F jB jA p.left hbase a.left z s hs H e
  ha dB hdB LA aA)
local notation "bS" => (source.originalNormPairPole qX π F jB jA p.left hbase
  a.left z s hs H e ha dB hdB LA bAsec)
local notation "g" => (pullback.snd (originalNormPairComponentBase π F jB ι.left) (jA ≫ π))
local notation "g₀" => (originalNormPairTargetMap π F jB jA p.left)
local notation "φ" => (originalComponentPairGraphMap p)
local notation "U₁" => (![retainedProduct (jB ≫ (F ≫ π)) (F ≫ π) (vB.left ≫ jB),
  retainedProduct (jA ≫ π) π (a.left ≫ jA)] : Fin 2 → Scheme)
local notation "B₁" => (![(pullback (pullback.snd (jB ≫ (F ≫ π)) (F ≫ π)) dB) ⨿ (pullback (jB ≫ (F
  ≫ π)) (s ≫ jB ≫ (F ≫ π))), (pullback (pullback.snd (jA ≫ π) π) dA) ⨿ (pullback (jA ≫ π) (z ≫ jA
  ≫ π))] : Fin 2 → Scheme)
private abbrev componentPairSmallBoundary : ∀ t : Fin 2, B₁ t ⟶ C₀ t :=
  Fin.twoCases (fullBoundaryProductMap (F ≫ π) jB dB s)
    (fullBoundaryProductMap π jA dA z)

private abbrev componentPairSmallInclusion : ∀ t : Fin 2, U₁ t ⟶ C₀ t :=
  Fin.twoCases
    (retainedProductInclusion (jB ≫ (F ≫ π)) (F ≫ π) (vB.left ≫ jB))
    (retainedProductInclusion (jA ≫ π) π (a.left ≫ jA))

private abbrev componentPairSmallMap : ∀ t : Fin 2, U₁ t ⟶ U₀ t :=
  Fin.twoCases
    (retainedSubopenMap (jB ≫ (F ≫ π)) (F ≫ π) jB (vB.left ≫ jB) vB.left rfl)
    (retainedSubopenMap (jA ≫ π) π jA (a.left ≫ jA) a.left rfl)

private abbrev componentPairSmallTarget : ∀ t : Fin 2, U₁ t ⟶ Asite.left :=
  Fin.twoCases
    (pullback.snd (jB ≫ (F ≫ π)) ((vB.left ≫ jB) ≫ (F ≫ π)) ≫ bA.left)
    (pullback.snd (jA ≫ π) ((a.left ≫ jA) ≫ π))

local notation "i₁" => (componentPairSmallBoundary (π := π) (F := F)
  (jB := jB) (jA := jA) (s := s) (z := z) (dB := dB) (dA := dA))
local notation "j₁" => (componentPairSmallInclusion (π := π) (F := F)
  (jB := jB) (jA := jA) (vB := vB) (a := a))
local notation "v₁" => (componentPairSmallMap (π := π) (F := F)
  (jB := jB) (jA := jA) (vB := vB) (a := a))
local notation "g₁" => (componentPairSmallTarget (π := π) (F := F)
  (jB := jB) (jA := jA) (vB := vB) (a := a) (bA := bA))
local notation "V₁" => (retainedProduct
  (originalNormPairComponentBase π F jB ι.left) π (a.left ≫ jA))
local notation "jT₁" => (retainedProductInclusion
  (originalNormPairComponentBase π F jB ι.left) π (a.left ≫ jA))
local notation "vT" => (retainedSubopenMap
  (originalNormPairComponentBase π F jB ι.left) π jA (a.left ≫ jA) a.left rfl)
local notation "gT₁" => (pullback.snd
  (originalNormPairComponentBase π F jB ι.left) ((a.left ≫ jA) ≫ π))

include hA hdA hpairA hsmall in
omit [IsSeparated (jA ≫ π)] in
/-- The actual original section difference is the normalized principal correspondence.
Geometric chart/cover witnesses are intermediate inputs; no Cor relation is assumed. -/
private theorem originalComponentPair_principal
    [IsAffine (X).left]
    [∀ t, IsAffine (O t).left]
    [∀ t, Flat (α t).left]
    [IsIntegral T] [IsNoetherian T]
    [IsProper q] [IsOpenImmersion jT]
    [(V).IsQuasiAffine] [SmoothOfRelativeDimension 1 (jT ≫ q)]
    [∀ t, IsFinite (f t)]
    [∀ t, IsOpenImmersion (j t)] [∀ t, (U t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (j t ≫ (f t ≫ q))]
    [∀ t, IsProper (q₀ t)]
    [∀ t, IsOpenImmersion (j₀ t)] [∀ t, (U₀ t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (j₀ t ≫ q₀ t)]
    [∀ t, Flat (c t)]
    [∀ t, IsClosedImmersion (γ t)]
    [∀ t, Mono (sectionDualFunctional (C₀ t)
      (tensorLineBundle (C₀ t) (M t)
        (dualLineBundle (C₀ t) ⟨Scheme.Hom.idealModule (γ t), hI t⟩)) (aS t))]
    [∀ t, Mono (sectionDualFunctional (C₀ t) (M t) (bS t))]
    (hb : (jT ≫ q) ≫ (X).hom = g ≫ (Y).hom)
    (hb₀ : ∀ t, (j₀ t ≫ q₀ t) ≫ (O t).hom = g₀ t ≫ (Y).hom)
    (hnormal : ∀ (W : (T).Opens), IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(T, W))
    (hfree : ∀ t (x : T), ∃ (W : (T).Opens) (hW : IsAffineOpen W), x ∈ W ∧
      (let : Algebra Γ(T, W) Γ(Limits.pullback (f t) hW.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (f t) hW.fromSpec)).toAlgebra
       Module.Free Γ(T, W) Γ(Limits.pullback (f t) hW.fromSpec, ⊤)))
    (W : (T).Opens) [Nonempty W] (hW : (Set.range jT)ᶜ ⊆ (W : Set T))
    (r : Γ(T, W)) (hr : IsUnit r)
    [∀ t, IsOpenImmersion (j₁ t)]
    [∀ t, (U₁ t).IsQuasiAffine]
    [∀ t, SmoothOfRelativeDimension 1 (j₁ t ≫ q₀ t)]
    (hb₁ : ∀ t, (j₁ t ≫ q₀ t) ≫ (O t).hom = g₁ t ≫ (Z).hom)
    [IsOpenImmersion jT₁]
    [(V₁).IsQuasiAffine] [SmoothOfRelativeDimension 1 (jT₁ ≫ q)]
    (hW₁ : (Set.range jT₁)ᶜ ⊆ (W : Set T))
    (hbT₁ : jT₁ ≫ q ≫ (X).hom = gT₁ ≫ (Z).hom)
    :
    let I := fun t => (⟨Scheme.Hom.idealModule (γ t), hI t⟩ : LineBundle (C₀ t))
    let A := fun t => tensorLineBundle (C₀ t) (M t) (dualLineBundle (C₀ t) (I t))
    let af := fun t => sectionDualFunctional (C₀ t) (A t) (aS t)
    let cf := fun t => sectionDualFunctional (C₀ t) (A t)
      (twistedIdealSection (C₀ t) (I t) (M t) (Scheme.Hom.idealInclusion (γ t)) (bS t))
    let L := fun t => pullbackLineBundle (c t) (dualLineBundle (C₀ t) (A t))
    let ap := fun t => Hom.pullbackToUnit (af t) (c t)
    let cp := fun t => Hom.pullbackToUnit (cf t) (c t)
    let : ∀ t, Mono (Scheme.Hom.idealInclusion (γ t)) := fun t => Scheme.Hom.idealInclusionMono _
    let : ∀ t, Mono (cf t) := fun t => twistedIdealSection_mono
      (C₀ t) (I t) (M t) (Scheme.Hom.idealInclusion (γ t)) (bS t)
    let : ∀ t, Mono (ap t) := fun t => by
      dsimp only [ap, af, A, I, Hom.pullbackToUnit]
      infer_instance
    let : ∀ t, Mono (cp t) := fun t => by
      dsimp only [cp, Hom.pullbackToUnit]
      infer_instance
    (T).germToFunctionField W r = Scheme.genericFiberLineRatioNorm (f 0) (L 0) (ap 0) (cp 0) /
      Scheme.genericFiberLineRatioNorm (f 1) (L 1) (ap 1) (cp 1) →
    let : ∀ t, IsIso (pullbackSectionMap (i₁ t) (aS t)) := by
      intro t
      fin_cases t
      · exact source.a_unit
      · exact inferInstanceAs (IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA))
    let : ∀ t, IsIso (pullbackSectionMap (i₁ t) (bS t)) := by
      intro t
      fin_cases t
      · exact source.b_unit
      · exact inferInstanceAs
          (IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bAsec))
    let hc₁ : ∀ t (x : (C₀ t : Scheme.{u})), x ∈ Set.range (j₁ t) ∨ x ∈ Set.range (i₁ t) := by
      intro t
      fin_cases t <;> intro x
      · exact lambdaBoundary_retained_cover (F ≫ π) jB s dB
          (vB.left ≫ jB) hsmallCoverB x
      · exact lambdaBoundary_retained_cover π jA z dA (a.left ≫ jA) hsmallCoverA x
    let d := fun t => (graphFunctor k).map (α t) ≫
      (boundarySection (O t) Z (i₁ t) (q₀ t) (j₁ t) (A t) (hc₁ t) (g₁ t) (hb₁ t) (aS t) -
        boundarySection (O t) Z (i₁ t) (q₀ t) (j₁ t) (M t) (hc₁ t) (g₁ t) (hb₁ t) (bS t))
    d 0 - d 1 = PrincipalOrderCorrespondence.correspondence
      q jT₁ W hW₁ r hr gT₁ hbT₁ := by
  let : IsIso (pullbackSectionMap
      (coprod.desc (infinityProductMap π jA dA) (graphBoundaryRestriction π jA z)) aA) :=
    inferInstanceAs (IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA))
  let : IsIso (pullbackSectionMap
      (coprod.desc (infinityProductMap π jA dA) (graphBoundaryRestriction π jA z)) bAsec) :=
    inferInstanceAs (IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bAsec))
  let : ∀ t, IsIso (pullbackSectionMap (i₀ t) (aS t)) := by
    intro t
    fin_cases t
    · exact source.originalNumerator_infinity_isIso qX (F ≫ π) jB p.left hbase
        a.left z s hs H e ha dB hdB
    · exact pullbackSectionMap_coprod_left_isIso
        (infinityProductMap π jA dA) (graphBoundaryRestriction π jA z) aA
  let : ∀ t, IsIso (pullbackSectionMap (i₀ t) (bS t)) := by
    intro t
    fin_cases t
    · exact source.originalPole_infinity_isIso qX (F ≫ π) jB p.left hbase
        a.left z s hs H e ha dB hdB
    · exact pullbackSectionMap_coprod_left_isIso
        (infinityProductMap π jA dA) (graphBoundaryRestriction π jA z) bAsec
  let : ∀ t, IsIso (pullbackSectionMap (i₀ t)
      (twistedIdealSection (C₀ t) ⟨idealModule (γ t), hI t⟩ (M t)
        (idealInclusion (γ t)) (bS t))) := by
    intro t
    fin_cases t
    · exact source.originalTwistedPole_infinity_isIso qX (F ≫ π) jB p.left hbase
        a.left z s hs H e ha dB hdB
    · exact graphTwistedSection_infinity_isIso qX π jA (𝟙 _)
        (hA.trans (Category.id_comp qX).symm) z z (Category.comp_id z)
        (IsPullback.id_vert z) e dA hdA LA aA bAsec hpairA
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i₀ t)).map (idealInclusion (γ t))) := by
    intro t
    fin_cases t
    · exact correctionInfinity_pullbackIdealInclusion_isIso (F ≫ π) jB dB hdB
    · exact correctionInfinity_pullbackIdealInclusion_isIso π jA dA hdA
  let : ∀ t, IsIso (pullbackSectionMap (i₁ t) (aS t)) := by
    intro t
    fin_cases t
    · exact source.a_unit
    · exact inferInstanceAs (IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA))
  let : ∀ t, IsIso (pullbackSectionMap (i₁ t) (bS t)) := by
    intro t
    fin_cases t
    · exact source.b_unit
    · exact inferInstanceAs
        (IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bAsec))
  have hcoverB := retained_complement_subset_infinity jB (vB.left ≫ jB) vB.left rfl
    s dB hsmallCoverB
  have hcoverA := retained_complement_subset_infinity jA (a.left ≫ jA) a.left rfl
    z dA hsmallCoverA
  have hc₁ : ∀ t (x : (C₀ t : Scheme.{u})), x ∈ Set.range (j₁ t) ∨ x ∈ Set.range (i₁ t) := by
    intro t
    fin_cases t <;> intro x
    · exact lambdaBoundary_retained_cover (F ≫ π) jB s dB (vB.left ≫ jB) hsmallCoverB x
    · exact lambdaBoundary_retained_cover π jA z dA (a.left ≫ jA) hsmallCoverA x
  have hc := originalNormPairChangedInfinity_cover π F jB ι.left jA dB dA hcoverB hcoverA
  have hc₀ := originalNormPairInfinity_cover π F jB jA dB dA hcoverB hcoverA
  have hw := originalNormPairRetainedFiniteMap_inclusion π F jB ι.left jA p.left hret
  have hv := originalNormPairRetainedMap_inclusion π F jB ι.left jA p.left hret
  have Hp := originalNormPairRetainedMap_isPullback π F jB ι.left jA p.left hret
  have hδ := originalNormPairRetainedGraph_inclusion π F jB jA
  have hq := originalNormPairGraph_projection π F jB jA
  have hgv := originalNormPairRetainedMap_target π F jB ι.left jA p.left hret
  have hφ := originalNormPairRetainedGraph_target π F jB jA p.left
  have hgraphs : α 0 ≫ φ 0 = α 1 ≫ φ 1 := by
    ext1
    exact originalNormPair_graphs ι.left p.left
  have hv₁ : ∀ t, v₁ t ≫ j₀ t = j₁ t := by
    intro t
    fin_cases t
    · exact retainedSubopenMap_inclusion _ _ _ _ _ rfl
    · exact retainedSubopenMap_inclusion _ _ _ _ _ rfl
  have hgu₁ : ∀ t, g₁ t ≫ (uMap).left = v₁ t ≫ g₀ t := by
    intro t
    fin_cases t
    · simpa only [originalNormPairTargetMap, Fin.twoCases_mk_zero, Category.assoc,
        retainedSubopenMap_snd_assoc] using
        congrArg (fun m => pullback.snd (jB ≫ (F ≫ π))
          ((vB.left ≫ jB) ≫ (F ≫ π)) ≫ m) hsmall.symm
    · exact (retainedSubopenMap_snd _ _ _ _ _ rfl).symm
  have hvT : vT ≫ jT = jT₁ := retainedSubopenMap_inclusion _ _ _ _ _ rfl
  have hguT₁ : gT₁ ≫ (uMap).left = vT ≫ g := by simp
  let I := fun t => (⟨idealModule (γ t), hI t⟩ : LineBundle (C₀ t))
  let A := fun t => tensorLineBundle (C₀ t) (M t) (dualLineBundle (C₀ t) (I t))
  let af := fun t => sectionDualFunctional (C₀ t) (A t) (aS t)
  let bf := fun t => sectionDualFunctional (C₀ t) (M t) (bS t)
  let cs := fun t => twistedIdealSection (C₀ t) (I t) (M t) (idealInclusion (γ t)) (bS t)
  let cf := fun t => sectionDualFunctional (C₀ t) (A t) (cs t)
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (Hom.pullbackToUnit (af t) (c t))) :=
    fun t => originalNormPairInfinity_functional_isIso
      π F jB ι.left jA p.left hret dB dA A aS t
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (Hom.pullbackToUnit (cf t) (c t))) :=
    fun t => originalNormPairInfinity_functional_isIso
      π F jB ι.left jA p.left hret dB dA A cs t
  let : ∀ t, IsIso ((Scheme.Modules.pullback (i t)).map (Hom.pullbackToUnit (bf t) (c t))) :=
    fun t => originalNormPairInfinity_functional_isIso
      π F jB ι.left jA p.left hret dB dA M bS t
  exact Cor.originalPair_norm_difference_marked X Y O α q jT
    C U B C₀ U₀ B₀ f i j w hw q₀ i₀ j₀ c v hv Hp γ hI δ hδ hq M aS bS
    hc hc₀ g hb g₀ hb₀ hgv φ hφ hgraphs hnormal hfree W hW r hr Z uMap
    U₁ B₁ i₁ j₁ v₁ hv₁ hc₁ g₁ hb₁ hgu₁ jT₁ vT hvT hW₁ gT₁ hbT₁ hguT₁

end Motivic.PresheafWithTransfers

namespace Motivic.Cor

open Scheme Scheme.RelativeCurvePencil Scheme.Hom
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

variable {k : Type u} [Field k]
  {S C P X Y K A V B Z DB DA : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine K] [IsIntegral K]
  [IsAffine A] [IsAffine V] [IsAffine B]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (qX : X ⟶ S) [IsSeparated qX] [SmoothOfRelativeDimension 1 qX]
  (π : P ⟶ S) [IsProper π] (F : C ⟶ P) [IsFinite F]
  (jB : Y ⟶ C) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ (F ≫ π))]
  (jA : X ⟶ P) [IsOpenImmersion jA]
  [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (α : K ⟶ Y) [Smooth α] [Flat α]
  (hA : jA ≫ π = qX) (hret : jB ≫ F = p ≫ jA)
  (hbase : jB ≫ (F ≫ π) = p ≫ qX)
  (a : A ⟶ X) [IsOpenImmersion a]
  (vB : V ⟶ Y) [IsOpenImmersion vB] (vA : V ⟶ A)
  (hsmall : vB ≫ p = vA ≫ a)
  [SmoothOfRelativeDimension 1 ((vB ≫ jB) ≫ (F ≫ π))]
  [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
  (αorig : B ⟶ Y) [Smooth αorig] (βorig : B ⟶ A) [Flat βorig]
  (horig : αorig ≫ p = βorig ≫ a)
  (φorig : B ⟶ V) (hφorig : φorig ≫ (vB ≫ jB) = αorig ≫ jB)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback qX (z ≫ qX)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget qX z))
  (ha : Disjoint (Set.range a) (Set.range z))
  (dB : DB ⟶ C) (hdB : Disjoint (Set.range jB) (Set.range dB))
  (dA : DA ⟶ P) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (hcoverB : ∀ x : C, x ∈ Set.range (vB ≫ jB) ∨
    x ∈ Set.range dB ∨ x ∈ Set.range (s ≫ jB))
  (hcoverA : ∀ x : P, x ∈ Set.range (a ≫ jA) ∨
    x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ jA))
  (source : BoundarySectionData qX (F ≫ π) jB p hbase a z s hs H e ha dB hdB)
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  [IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA)]
  [IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bA)]
  (hpairA :
    pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA ≫
        pullbackTensorMap (fullBoundaryProductMap π jA dA z) LA.val
          (dualLineBundle _ (relativeCompactificationGraphLine π jA)).val =
      tensorUnitSection (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bA)
        (relativeFullBoundaryFrame qX π jA (𝟙 _)
          (hA.trans (Category.id_comp qX).symm) z z (Category.comp_id z)
          (IsPullback.id_vert z) e dA hdA).inv)

local notation "qK" => (α ≫ (jB ≫ (F ≫ π)))
local notation "T" => (pullback qK π : Scheme)
local notation "siteK" => (relativeCommonSite k t (F ≫ π) jB α)
local notation "siteY" => (lambdaSourceSite k t (F ≫ π) jB)
local notation "siteX" => (lambdaSourceSite k t π jA)
local notation "siteQ" => (relativeTargetSite k t π (a ≫ jA))
local notation "siteV" => (relativeTargetSite k t (F ≫ π) (vB ≫ jB))
local notation "MA" => (tensorLineBundle _ LA
  (dualLineBundle _ (relativeCompactificationGraphLine π jA)))
local notation "MB" => (tensorLineBundle _ source.T
  (dualLineBundle _ (relativeCompactificationGraphLine (F ≫ π) jB)))
local notation "afB" => (sectionDualFunctional _ MB source.aS)
local notation "afA" => (sectionDualFunctional _ MA aA)
local notation "cfB" => (sectionDualFunctional _ MB
  (twistedIdealSection _ (relativeCompactificationGraphLine (F ≫ π) jB) source.T
    (idealInclusion (compactificationGraph (F ≫ π) jB)) source.bS))
local notation "cfA" => (sectionDualFunctional _ MA
  (twistedIdealSection _ (relativeCompactificationGraphLine π jA) LA
    (idealInclusion (compactificationGraph π jA)) bA))
local notation "cB" => (constantSourceMapOfEq α (jB ≫ (F ≫ π)) (F ≫ π) qK rfl)
local notation "cA" => (retainedNormParameterMap π qK jA (α ≫ p)
  (originalNormPairComponentBase_eq π F jB α jA p hret))

local instance : Flat cB := by
  infer_instance
local instance : Flat cA := by
  let : Flat (α ≫ p) := inferInstance
  infer_instance
local instance : IsAffine (siteK).left := by
  change IsAffine K
  infer_instance
local instance : IsIntegral (siteK).left := by
  change IsIntegral K
  infer_instance
local instance : IsAffine (siteY).left := by
  change IsAffine Y
  infer_instance
local instance : IsAffine (siteX).left := by
  change IsAffine X
  infer_instance
local instance : IsAffine (siteQ).left := by
  change IsAffine A
  infer_instance

omit [IsIntegral K] in
include hA hdA hpairA in
/-- The actual original lambda difference is the principal correspondence of
its SAME normalized ratio, before any homotopy-invariant transfer is applied. -/
theorem originalComponentLambda_eq_principal
    [IsIntegral T] [IsNoetherian T]
    [Mono afB] [Mono afA]
    [Mono (sectionDualFunctional _ source.T source.bS)]
    [Mono (sectionDualFunctional _ LA bA)]
    (hnormal : ∀ (U : (T).Opens), IsAffineOpen U → Nonempty U →
      IsIntegrallyClosed Γ(T, U))
    (hfree : ∀ x : T, ∃ (U : (T).Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(T, U) Γ(pullback (normProductMap π F qK) hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (normProductMap π F qK) hU.fromSpec)).toAlgebra
       Module.Free Γ(T, U) Γ(pullback (normProductMap π F qK) hU.fromSpec, ⊤)))
    (W : (T).Opens) [Nonempty W]
    (hW : (Set.range (retainedProductInclusion qK π (a ≫ jA)))ᶜ ⊆ (W : Set T))
    (r : Γ(T, W)) (hr : IsUnit r) :
    let : Mono (idealInclusion (compactificationGraph (F ≫ π) jB)) :=
      idealInclusionMono _
    let : Mono (idealInclusion (compactificationGraph π jA)) := idealInclusionMono _
    let : Mono cfB := twistedIdealSection_mono _
      (relativeCompactificationGraphLine (F ≫ π) jB) source.T
      (idealInclusion (compactificationGraph (F ≫ π) jB)) source.bS
    let : Mono cfA := twistedIdealSection_mono _
      (relativeCompactificationGraphLine π jA) LA
      (idealInclusion (compactificationGraph π jA)) bA
    let : Mono (Hom.pullbackToUnit afB cB) := by
      dsimp only [Hom.pullbackToUnit]
      infer_instance
    let : Mono (Hom.pullbackToUnit cfB cB) := by
      dsimp only [Hom.pullbackToUnit]
      infer_instance
    let : Mono (Hom.pullbackToUnit afA cA) := by
      dsimp only [Hom.pullbackToUnit]
      infer_instance
    let : Mono (Hom.pullbackToUnit cfA cA) := by
      dsimp only [Hom.pullbackToUnit]
      infer_instance
    (T).germToFunctionField W r =
      genericFiberLineRatioNorm (normProductMap π F qK)
        (pullbackLineBundle cB (dualLineBundle _ MB))
        (Hom.pullbackToUnit afB cB) (Hom.pullbackToUnit cfB cB) /
      genericFiberLineRatioNorm (𝟙 T)
        (pullbackLineBundle cA (dualLineBundle _ MA))
        (Hom.pullbackToUnit afA cA) (Hom.pullbackToUnit cfA cA) →
    let pSite : siteY ⟶ siteX := SmoothSite.homMk p (by
      change p ≫ ((jA ≫ π) ≫ t) = (jB ≫ (F ≫ π)) ≫ t
      simpa only [Category.assoc] using
        congrArg (fun m => m ≫ π ≫ t) hret.symm)
    let vASite : siteV ⟶ siteQ := SmoothSite.homMk vA (by
      change vA ≫ (((a ≫ jA) ≫ π) ≫ t) = ((vB ≫ jB) ≫ (F ≫ π)) ≫ t
      rw [Category.assoc, Category.assoc, ← Category.assoc vA a, ← hsmall]
      simpa only [Category.assoc] using
        congrArg (fun m => vB ≫ m ≫ π ≫ t) hret.symm)
    let : IsAffine (retainedProduct qK π (a ≫ jA)) :=
      retainedProduct_affine qK π (a ≫ jA)
    let : SmoothOfRelativeDimension 1
        (retainedProductInclusion qK π (a ≫ jA) ≫ pullback.fst qK π) :=
      retainedProduct_smooth qK π (a ≫ jA)
    let data := source.toData k t qX (F ≫ π) jB p hbase a αorig βorig horig
      z s hs H e ha dB hdB (vB ≫ jB) hcoverB φorig hφorig
    ((graphFunctor k).map (relativeAlpha k t (F ≫ π) jB α) ≫
        (data.lam ≫ (graphFunctor k).map vASite) : Cor.mk siteK ⟶ Cor.mk siteQ) -
      ((graphFunctor k).map (relativeAlpha k t (F ≫ π) jB α ≫ pSite) ≫
        originalTargetLambda k t π jA z dA a hcoverA LA aA bA :
          Cor.mk siteK ⟶ Cor.mk siteQ) =
      PrincipalOrderCorrespondence.correspondence
        (pullback.fst qK π) (retainedProductInclusion qK π (a ≫ jA))
        W hW r hr (pullback.snd qK ((a ≫ jA) ≫ π))
        (by
          change (retainedProductInclusion qK π (a ≫ jA)) ≫
            (pullback.fst qK π) ≫ (qK ≫ t) =
            (pullback.snd qK ((a ≫ jA) ≫ π)) ≫ (((a ≫ jA) ≫ π) ≫ t)
          simpa only [Category.assoc] using retainedProduct_structure qK π (a ≫ jA) t) := by
  let : Mono (idealInclusion (compactificationGraph (F ≫ π) jB)) :=
    idealInclusionMono _
  let : Mono (idealInclusion (compactificationGraph π jA)) := idealInclusionMono _
  let : Mono cfB := twistedIdealSection_mono _
    (relativeCompactificationGraphLine (F ≫ π) jB) source.T
    (idealInclusion (compactificationGraph (F ≫ π) jB)) source.bS
  let : Mono cfA := twistedIdealSection_mono _
    (relativeCompactificationGraphLine π jA) LA
    (idealInclusion (compactificationGraph π jA)) bA
  let : Mono (Hom.pullbackToUnit afB cB) := by
    dsimp only [Hom.pullbackToUnit]
    infer_instance
  let : Mono (Hom.pullbackToUnit cfB cB) := by
    dsimp only [Hom.pullbackToUnit]
    infer_instance
  let : Mono (Hom.pullbackToUnit afA cA) := by
    dsimp only [Hom.pullbackToUnit]
    infer_instance
  let : Mono (Hom.pullbackToUnit cfA cA) := by
    dsimp only [Hom.pullbackToUnit]
    infer_instance
  dsimp only
  intro hg
  let pSite : siteY ⟶ siteX := SmoothSite.homMk p (by
    change p ≫ ((jA ≫ π) ≫ t) = (jB ≫ (F ≫ π)) ≫ t
    simpa only [Category.assoc] using congrArg (fun m => m ≫ π ≫ t) hret.symm)
  let : Flat pSite.left := inferInstanceAs (Flat p)
  let aSite : siteQ ⟶ siteX := SmoothSite.homMk a (by
    change a ≫ ((jA ≫ π) ≫ t) = ((a ≫ jA) ≫ π) ≫ t
    simp only [Category.assoc])
  let : IsOpenImmersion aSite.left := inferInstanceAs (IsOpenImmersion a)
  let vBSite : siteV ⟶ siteY := SmoothSite.homMk vB (by
    change vB ≫ ((jB ≫ (F ≫ π)) ≫ t) = ((vB ≫ jB) ≫ (F ≫ π)) ≫ t
    simp only [Category.assoc])
  let vASite : siteV ⟶ siteQ := SmoothSite.homMk vA (by
    change vA ≫ (((a ≫ jA) ≫ π) ≫ t) = ((vB ≫ jB) ≫ (F ≫ π)) ≫ t
    rw [Category.assoc, Category.assoc, ← Category.assoc vA a, ← hsmall]
    simpa only [Category.assoc] using
      congrArg (fun m => vB ≫ m ≫ π ≫ t) hret.symm)
  let αSite := relativeAlpha k t (F ≫ π) jB α
  let : IsIntegral (pullback (originalNormPairComponentBase π F jB αSite.left) π) := by
    change IsIntegral T
    infer_instance
  let : IsNoetherian (pullback (originalNormPairComponentBase π F jB αSite.left) π) := by
    change IsNoetherian T
    infer_instance
  let O := PresheafWithTransfers.originalComponentPairSite siteY siteX
  let αs := PresheafWithTransfers.originalComponentPairSiteMap αSite pSite
  let : ∀ i, IsAffine (O i).left := by
    intro i
    fin_cases i
    · change IsAffine Y
      infer_instance
    · change IsAffine X
      infer_instance
  let : ∀ i, Flat (αs i).left := by
    intro i
    fin_cases i
    · change Flat α
      infer_instance
    · change Flat (α ≫ p)
      infer_instance
  let : ∀ i, IsClosedImmersion (originalNormPairGraph π F jB jA i) := by
    intro i
    fin_cases i
    · change IsClosedImmersion (compactificationGraph (F ≫ π) jB)
      dsimp only [compactificationGraph]
      infer_instance
    · change IsClosedImmersion (compactificationGraph π jA)
      dsimp only [compactificationGraph]
      infer_instance
  let M := source.originalNormPairLine qX π F jB jA p hbase a z s hs H e ha dB hdB LA
  let aS := source.originalNormPairNumerator qX π F jB jA p hbase a z s hs H e ha dB hdB LA aA
  let bS := source.originalNormPairPole qX π F jB jA p hbase a z s hs H e ha dB hdB LA bA
  let : ∀ i, Mono (sectionDualFunctional _
      (tensorLineBundle _ (M i) (dualLineBundle _ (originalNormPairGraphLine π F jB jA i)))
      (aS i)) := fun i => source.originalNormPairNumerator_mono
        qX π F jB jA p hbase a z s hs H e ha dB hdB LA aA i
  let : ∀ i, Mono (sectionDualFunctional _ (M i) (bS i)) :=
    fun i => source.originalNormPairPole_mono
      qX π F jB jA p hbase a z s hs H e ha dB hdB LA bA i
  have hfreePair : ∀ i (x : T), ∃ (U : (T).Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(T, U)
          Γ(pullback (originalNormPairFiniteMap π F jB α i) hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (originalNormPairFiniteMap π F jB α i) hU.fromSpec)).toAlgebra
       Module.Free Γ(T, U)
         Γ(pullback (originalNormPairFiniteMap π F jB α i) hU.fromSpec, ⊤)) := by
    intro i
    fin_cases i
    · exact hfree
    · exact identity_exists_free_affine_neighborhood
  have hlarge : (Set.range (retainedProductInclusion qK π jA))ᶜ ⊆ (W : Set T) := by
    apply Set.Subset.trans _ hW
    apply Set.compl_subset_compl.mpr
    rintro x ⟨y, rfl⟩
    refine ⟨retainedSubopenMap qK π jA (a ≫ jA) a rfl y, ?_⟩
    exact congrArg (fun m => m y) (retainedSubopenMap_inclusion qK π jA (a ≫ jA) a rfl)
  have hb := retainedProduct_structure qK π jA t
  have hbT := retainedProduct_structure qK π (a ≫ jA) t
  have hb0 : ∀ i,
      (originalNormPairRetainedInclusion π F jB jA i ≫
        originalNormPairProjection π F jB jA i) ≫ (O i).hom =
      originalNormPairTargetMap π F jB jA p i ≫ (siteX).hom := by
    intro i
    fin_cases i
    · exact retainedProduct_structure_factor (jB ≫ (F ≫ π)) (F ≫ π) jB t p
        (siteX).hom (by
          change p ≫ ((jA ≫ π) ≫ t) = (jB ≫ (F ≫ π)) ≫ t
          simpa only [Category.assoc] using congrArg (fun m => m ≫ π ≫ t) hret.symm)
    · exact retainedProduct_structure (jA ≫ π) π jA t
  have hb1B := retainedProduct_structure_factor (jB ≫ (F ≫ π)) (F ≫ π)
    (vB ≫ jB) t vA (siteQ).hom (by
      exact vASite.w)
  have hb1A := retainedProduct_structure (jA ≫ π) π (a ≫ jA) t
  let U1 : Fin 2 → Scheme.{u} :=
    ![retainedProduct (jB ≫ (F ≫ π)) (F ≫ π) (vB ≫ jB),
      retainedProduct (jA ≫ π) π (a ≫ jA)]
  let j1 : ∀ i, U1 i ⟶ originalNormPairCompact π F jB jA i := Fin.twoCases
    (retainedProductInclusion (jB ≫ (F ≫ π)) (F ≫ π) (vB ≫ jB))
    (retainedProductInclusion (jA ≫ π) π (a ≫ jA))
  let g1 : ∀ i, U1 i ⟶ A := Fin.twoCases
    (pullback.snd (jB ≫ (F ≫ π)) ((vB ≫ jB) ≫ (F ≫ π)) ≫ vA)
    (pullback.snd (jA ≫ π) ((a ≫ jA) ≫ π))
  have hb1 : ∀ i, (j1 i ≫ originalNormPairProjection π F jB jA i) ≫ (O i).hom =
      g1 i ≫ (siteQ).hom := by
    intro i
    fin_cases i
    · exact hb1B
    · exact hb1A
  let : ∀ i, IsOpenImmersion (j1 i) := by
    intro i
    fin_cases i <;> dsimp [j1] <;> infer_instance
  let : ∀ i, IsAffine (U1 i) := by
    intro i
    fin_cases i
    · exact retainedProduct_affine (jB ≫ (F ≫ π)) (F ≫ π) (vB ≫ jB)
    · exact retainedProduct_affine (jA ≫ π) π (a ≫ jA)
  let : ∀ i, (U1 i).IsQuasiAffine := fun i => inferInstance
  let : ∀ i, SmoothOfRelativeDimension 1
      (j1 i ≫ originalNormPairProjection π F jB jA i) := by
    intro i
    fin_cases i
    · exact retainedProduct_smooth (jB ≫ (F ≫ π)) (F ≫ π) (vB ≫ jB)
    · exact retainedProduct_smooth (jA ≫ π) π (a ≫ jA)
  let : IsAffine (retainedProduct qK π jA) := retainedProduct_affine qK π jA
  let : IsAffine (retainedProduct qK π (a ≫ jA)) :=
    retainedProduct_affine qK π (a ≫ jA)
  let : SmoothOfRelativeDimension 1
      (retainedProductInclusion qK π jA ≫ pullback.fst qK π) :=
    retainedProduct_smooth qK π jA
  let : SmoothOfRelativeDimension 1
      (retainedProductInclusion qK π (a ≫ jA) ≫ pullback.fst qK π) :=
    retainedProduct_smooth qK π (a ≫ jA)
  let : SmoothOfRelativeDimension 1
      (retainedProductInclusion (originalNormPairComponentBase π F jB αSite.left) π jA ≫
        pullback.fst (originalNormPairComponentBase π F jB αSite.left) π) := by
    change SmoothOfRelativeDimension 1
      (retainedProductInclusion qK π jA ≫ pullback.fst qK π)
    infer_instance
  let : SmoothOfRelativeDimension 1
      (retainedProductInclusion (originalNormPairComponentBase π F jB αSite.left) π
        (aSite.left ≫ jA) ≫
        pullback.fst (originalNormPairComponentBase π F jB αSite.left) π) := by
    change SmoothOfRelativeDimension 1
      (retainedProductInclusion qK π (a ≫ jA) ≫ pullback.fst qK π)
    infer_instance
  let : ∀ i, Flat (originalNormPairCompactMap π F jB αSite.left jA pSite.left hret i) := by
    intro i
    change Flat (originalNormPairCompactMap π F jB α jA p hret i)
    infer_instance
  let : ∀ i, Mono (sectionDualFunctional (originalNormPairCompact π F jB jA i)
      (tensorLineBundle _
        (source.originalNormPairLine qX π F jB jA pSite.left hbase aSite.left
          z s hs H e ha dB hdB LA i)
        (dualLineBundle _ ⟨idealModule (originalNormPairGraph π F jB jA i),
          originalNormPairGraph_rankOne π F jB jA i⟩))
      (source.originalNormPairNumerator qX π F jB jA pSite.left hbase aSite.left
        z s hs H e ha dB hdB LA aA i)) := by
    intro i
    exact source.originalNormPairNumerator_mono
      qX π F jB jA p hbase a z s hs H e ha dB hdB LA aA i
  let : ∀ i, Mono (sectionDualFunctional (originalNormPairCompact π F jB jA i)
      (source.originalNormPairLine qX π F jB jA pSite.left hbase aSite.left
        z s hs H e ha dB hdB LA i)
      (source.originalNormPairPole qX π F jB jA pSite.left hbase aSite.left
        z s hs H e ha dB hdB LA bA i)) := by
    intro i
    exact source.originalNormPairPole_mono
      qX π F jB jA p hbase a z s hs H e ha dB hdB LA bA i
  let : ∀ i, IsOpenImmersion
      (PresheafWithTransfers.componentPairSmallInclusion siteY siteX siteQ siteV
        π F jB jA aSite vBSite i) := by
    intro i
    change IsOpenImmersion (j1 i)
    infer_instance
  let : ∀ i : Fin 2,
      ((![retainedProduct (jB ≫ (F ≫ π)) (F ≫ π) (vBSite.left ≫ jB),
        retainedProduct (jA ≫ π) π (aSite.left ≫ jA)] i : Scheme)).IsQuasiAffine := by
    intro i
    change (U1 i).IsQuasiAffine
    infer_instance
  let : ∀ i, SmoothOfRelativeDimension 1
      (PresheafWithTransfers.componentPairSmallInclusion siteY siteX siteQ siteV
        π F jB jA aSite vBSite i ≫ originalNormPairProjection π F jB jA i) := by
    intro i
    change SmoothOfRelativeDimension 1 (j1 i ≫ originalNormPairProjection π F jB jA i)
    infer_instance
  let : (retainedProduct (originalNormPairComponentBase π F jB αSite.left) π
      (aSite.left ≫ jA)).IsQuasiAffine := by
    change (retainedProduct qK π (a ≫ jA)).IsQuasiAffine
    infer_instance
  let : IsNoetherian (retainedProduct (originalNormPairComponentBase π F jB αSite.left) π
      (aSite.left ≫ jA)) := by
    change IsNoetherian (retainedProduct qK π (a ≫ jA))
    let : IsLocallyNoetherian (retainedProduct qK π (a ≫ jA)) :=
      isLocallyNoetherian_of_isOpenImmersion (retainedProductInclusion qK π (a ≫ jA))
    exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hn := PresheafWithTransfers.originalComponentPair_principal
    (Ksite := siteK) (Ysite := siteY) (Xsite := siteX) (Asite := siteQ) (Bsite := siteV)
    (qX := qX) (π := π) (F := F) (jB := jB) (jA := jA) (p := pSite) (ι := αSite)
    (hA := hA) (hret := hret) (hbase := hbase) (a := aSite)
    (vB := vBSite) (bA := vASite) (hsmall := hsmall)
    (z := z) (s := s) (hs := hs) (H := H) (e := e) (ha := ha)
    (dB := dB) (hdB := hdB) (dA := dA) (hdA := hdA)
    (hsmallCoverB := hcoverB) (hsmallCoverA := hcoverA)
    (source := source) (LA := LA) (aA := aA) (bAsec := bA) (hpairA := hpairA)
    (hb := hb) (hb₀ := hb0) (hnormal := hnormal) (hfree := hfreePair)
    (W := W) (hW := hlarge) (r := r) (hr := hr) (hb₁ := hb1)
    (hW₁ := hW) (hbT₁ := hbT)
  have hdict := source.lam_comp_graph_dictionary k t qX (F ≫ π) jB p hbase a
    αorig βorig horig z s hs H e ha dB hdB (vB ≫ jB) hcoverB φorig hφorig siteQ vASite
  have hαzero : PresheafWithTransfers.originalComponentPairSiteMap αSite pSite 0 =
      αSite := by
    ext1
    rfl
  have hαone : PresheafWithTransfers.originalComponentPairSiteMap αSite pSite 1 =
      αSite ≫ pSite := by
    ext1
    rfl
  have hnFinal := hn hg
  have hgzero := congrArg (fun f : siteK ⟶ siteY => (graphFunctor k).map f) hαzero
  have hgone := congrArg (fun f : siteK ⟶ siteX => (graphFunctor k).map f) hαone
  rw [← hgzero, ← hgone]
  rw [hdict]
  simpa only [ originalTargetLambda, graphFunctor_obj,
    SmoothSite.mk, SmoothSite.homMk, CostructuredArrow.homMk_left,
    MorphismProperty.Over.mk, MorphismProperty.Over.homMk, CategoryTheory.Over.homMk,
    relativeAlpha, lambdaSourceSite, relativeCommonSite, relativeTargetSite, commonProjection,
    originalNormPairBase, originalNormPairParameter,
    originalNormPairComponentBase, fullBoundaryProductMap,
    relativeCompactificationGraphLine, Matrix.cons_val_zero, Matrix.cons_val_one,
    PresheafWithTransfers.originalComponentPairSite,
    PresheafWithTransfers.originalComponentPairStructureMap,
    PresheafWithTransfers.originalComponentPairSiteMap,
    originalNormPairParameterMap, originalNormPairProjection,
    originalNormPairCompact, originalNormPairCompactMap, originalNormPairFiniteMap,
    originalNormPairGraph, originalNormPairGraph_rankOne,
    Fin.twoCases_zero, Fin.twoCases_one,
    BoundarySectionData.originalNormPairLine_zero, BoundarySectionData.originalNormPairLine_one,
    BoundarySectionData.originalNormPairNumerator_zero,
    BoundarySectionData.originalNormPairNumerator_one,
    BoundarySectionData.originalNormPairPole_zero, BoundarySectionData.originalNormPairPole_one,
    M, aS, bS, O, αs, αSite, pSite, aSite, vBSite, vASite]
    using hnFinal

end Motivic.Cor
