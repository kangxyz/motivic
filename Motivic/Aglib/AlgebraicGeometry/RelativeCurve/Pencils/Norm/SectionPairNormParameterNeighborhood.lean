/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairNormNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterChart
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.SchemeIso
/-! # The original norm neighborhood on an integral parameter component

Only the first parameter is changed. The second compactification, its original
section pair, and its graph line remain unchanged. All chart comparisons below
use the literal structural scalar maps, including on nonreduced finite sources.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairNormParameterNeighborhood`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.NativeSectionPairNormalizedUnit`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u



namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The component chart retains exactly the original finite algebra, via the
canonical pullback-pasting isomorphism rather than a replacement source. -/
def sectionPairParameterChartIso {B T T' W : Scheme.{u}}
    (F : B ⟶ T) (ρ : T' ⟶ T) (w : W ⟶ T') :
    pullback (pullback.snd F ρ) w ≅ pullback F (w ≫ ρ) :=
  pullbackLeftPullbackSndIso F ρ w

@[reassoc (attr := simp)]
theorem sectionPairParameterChartIso_hom_fst {B T T' W : Scheme.{u}}
    (F : B ⟶ T) (ρ : T' ⟶ T) (w : W ⟶ T') :
    (sectionPairParameterChartIso F ρ w).hom ≫ pullback.fst F (w ≫ ρ) =
      pullback.fst (pullback.snd F ρ) w ≫ pullback.fst F ρ :=
  pullbackLeftPullbackSndIso_hom_fst F ρ w

@[reassoc (attr := simp)]
theorem sectionPairParameterChartIso_hom_snd {B T T' W : Scheme.{u}}
    (F : B ⟶ T) (ρ : T' ⟶ T) (w : W ⟶ T') :
    (sectionPairParameterChartIso F ρ w).hom ≫ pullback.snd F (w ≫ ρ) =
      pullback.snd (pullback.snd F ρ) w :=
  pullbackLeftPullbackSndIso_hom_snd F ρ w

/-- Original chart freeness transfers to the actual component chart, with the
same scalar ring and the actual finite map to that chart. -/
theorem sectionPairParameterChart_free {R : Type u} [CommRing R]
    {B T T' : Scheme.{u}} (F : B ⟶ T) (ρ : T' ⟶ T) (w : Spec (.of R) ⟶ T') :
    let : Algebra R Γ(pullback F (w ≫ ρ), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (w ≫ ρ))).toAlgebra
    let : Algebra R Γ(pullback (pullback.snd F ρ) w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (pullback.snd F ρ) w)).toAlgebra
    ∀ [Module.Free R Γ(pullback F (w ≫ ρ), ⊤)],
      Module.Free R Γ(pullback (pullback.snd F ρ) w, ⊤) := by
  let : Algebra R Γ(pullback F (w ≫ ρ), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (w ≫ ρ))).toAlgebra
  let : Algebra R Γ(pullback (pullback.snd F ρ) w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (pullback.snd F ρ) w)).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  apply FiniteSchemeNormBaseChange.sections_free_of_iso
    (pullback.snd F (w ≫ ρ)) (pullback.snd (pullback.snd F ρ) w)
    (sectionPairParameterChartIso F ρ w).symm
  rw [← sectionPairParameterChartIso_hom_snd F ρ w]
  exact (sectionPairParameterChartIso F ρ w).inv_hom_id_assoc _

/-- The same original denominator is a unit on the actual component chart. -/
theorem sectionPairParameterChart_unit
    {B T T' W : Scheme.{u}} (F : B ⟶ T) (ρ : T' ⟶ T) (w : W ⟶ T')
    {M : B.Modules} (a : M ⟶ SheafOfModules.unit B.ringCatSheaf)
    [IsIso (pullbackUnitMap (pullback.fst F (w ≫ ρ)) a)] :
    IsIso (pullbackUnitMap
      (pullback.fst (pullback.snd F ρ) w ≫ pullback.fst F ρ) a) := by
  rw [← sectionPairParameterChartIso_hom_fst F ρ w]
  exact pullbackUnitMap_comp_isIso_of_first (pullback.fst F (w ≫ ρ))
    (sectionPairParameterChartIso F ρ w).hom a

/-- Equality of geometric maps preserves the quotient, including its dependent
pullback modules and chosen inverse instances. -/
theorem sectionPairParameter_quotient_eq_of_map_eq
    {B W : Scheme.{u}} (v w : W ⟶ B) (h : v = w) (L : LineBundle B)
    (a c : L.val ⟶ SheafOfModules.unit B.ringCatSheaf)
    [IsIso (pullbackUnitMap v a)] [IsIso (pullbackUnitMap w a)] :
    inv (pullbackUnitMap v a) ≫ pullbackUnitMap v c =
      inv (pullbackUnitMap w a) ≫ pullbackUnitMap w c := by
  subst w
  rfl

/-- The quotient of the literal parameter-pulled functionals has the norm of
exactly the original chart quotient. This is the coherence used by the native
generic germ, not an independently prescribed scalar. -/
theorem sectionPairParameterChart_norm_quotient
    {R : Type u} [CommRing R] {B T T' : Scheme.{u}}
    (F : B ⟶ T) (ρ : T' ⟶ T) (w : Spec (.of R) ⟶ T')
    (L : LineBundle B) (a c : L.val ⟶ SheafOfModules.unit B.ringCatSheaf)
    [IsIso (pullbackUnitMap (pullback.fst F (w ≫ ρ)) a)] :
    let v := pullback.fst F ρ
    let n := pullback.fst (pullback.snd F ρ) w
    let v₀ := pullback.fst F (w ≫ ρ)
    letI := sectionPairParameterChart_unit F ρ w a
    letI := pullbackUnitMap_nested_isIso_of_comp v n a
    let : Algebra R Γ(pullback F (w ≫ ρ), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (w ≫ ρ))).toAlgebra
    let : Algebra R Γ(pullback (pullback.snd F ρ) w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (pullback.snd F ρ) w)).toAlgebra
    Algebra.norm R (show Γ(pullback (pullback.snd F ρ) w, ⊤) from Modules.Hom.app
      (inv (pullbackUnitMap n (pullbackUnitMap v a)) ≫
        pullbackUnitMap n (pullbackUnitMap v c)) ⊤
          (1 : Γ(pullback (pullback.snd F ρ) w, ⊤))) =
      Algebra.norm R (show Γ(pullback F (w ≫ ρ), ⊤) from Modules.Hom.app
        (inv (pullbackUnitMap v₀ a) ≫ pullbackUnitMap v₀ c) ⊤
          (1 : Γ(pullback F (w ≫ ρ), ⊤))) := by
  dsimp only
  let v := pullback.fst F ρ
  let n := pullback.fst (pullback.snd F ρ) w
  let v₀ := pullback.fst F (w ≫ ρ)
  let E := sectionPairParameterChartIso F ρ w
  let : IsIso (pullbackUnitMap (n ≫ v) a) := by
    rw [← sectionPairParameterChartIso_hom_fst F ρ w]
    exact pullbackUnitMap_comp_isIso_of_first v₀ E.hom a
  let := pullbackUnitMap_nested_isIso_of_comp v n a
  let : IsIso (pullbackUnitMap (E.hom ≫ v₀) a) :=
    pullbackUnitMap_comp_isIso_of_first v₀ E.hom a
  let : Algebra R Γ(pullback F (w ≫ ρ), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (w ≫ ρ))).toAlgebra
  let : Algebra R Γ(pullback (pullback.snd F ρ) w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (pullback.snd F ρ) w)).toAlgebra
  rw [functionalQuotient_comp v n c a]
  have hθ := functionalQuotient_pullback v₀ E.hom c a
  have hc := sectionPairParameter_quotient_eq_of_map_eq (E.hom ≫ v₀) (n ≫ v)
    (sectionPairParameterChartIso_hom_fst F ρ w) L a c
  rw [hc] at hθ
  rw [← hθ]
  exact (congrArg
    (fun t : Γ(pullback (pullback.snd F ρ) w, ⊤) => Algebra.norm R t)
    (Hom.unitEndomorphismPullback_app_one E.hom
      (inv (pullbackUnitMap v₀ a) ≫ pullbackUnitMap v₀ c))).trans
    (FiniteSchemeNormBaseChange.norm_appTop_of_iso
      (pullback.snd (pullback.snd F ρ) w) (pullback.snd F (w ≫ ρ)) E
      (sectionPairParameterChartIso_hom_snd F ρ w) _)

/-- The actual component generic norm is computed in the unchanged original
finite chart. Integrality is required only of the new target parameter; the
original parameter and both finite source schemes can be disconnected. -/
theorem sectionPairParameterChart_native_inverse_germ
    {B T T' : Scheme.{u}} (F : B ⟶ T) [IsFinite F]
    (ρ : T' ⟶ T) [IsIntegral T']
    (L : LineBundle B) (a c : L.val ⟶ SheafOfModules.unit B.ringCatSheaf)
    [Mono (pullbackUnitMap (pullback.fst F ρ) a)]
    [Mono (pullbackUnitMap (pullback.fst F ρ) c)]
    (U : T'.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIso (pullbackUnitMap (pullback.fst F (hU.fromSpec ≫ ρ)) a)] :
    let : Algebra Γ(T', U) Γ(pullback F (hU.fromSpec ≫ ρ), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (hU.fromSpec ≫ ρ))).toAlgebra
    ∀ [Module.Free Γ(T', U) Γ(pullback F (hU.fromSpec ≫ ρ), ⊤)],
    (genericFiberLineRatioNorm (pullback.snd F ρ)
      (pullbackLineBundle (pullback.fst F ρ) L)
      (pullbackUnitMap (pullback.fst F ρ) a)
      (pullbackUnitMap (pullback.fst F ρ) c))⁻¹ =
      T'.germToFunctionField U (Algebra.norm Γ(T', U)
        (show Γ(pullback F (hU.fromSpec ≫ ρ), ⊤) from Modules.Hom.app
        (inv (pullbackUnitMap (pullback.fst F (hU.fromSpec ≫ ρ)) a) ≫
          pullbackUnitMap (pullback.fst F (hU.fromSpec ≫ ρ)) c) ⊤
            (1 : Γ(pullback F (hU.fromSpec ≫ ρ), ⊤)))) := by
  let : Algebra Γ(T', U) Γ(pullback F (hU.fromSpec ≫ ρ), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (hU.fromSpec ≫ ρ))).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  let : Algebra Γ(T', U) Γ(pullback (pullback.snd F ρ) hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (pullback.snd F ρ) hU.fromSpec)).toAlgebra
  let := sectionPairParameterChart_free F ρ hU.fromSpec
  let := sectionPairParameterChart_unit F ρ hU.fromSpec a
  let := pullbackUnitMap_nested_isIso_of_comp (pullback.fst F ρ)
    (pullback.fst (pullback.snd F ρ) hU.fromSpec) a
  have h := genericFiberLineRatioNorm_eq_chart_functionalQuotient (pullback.snd F ρ)
    (pullbackLineBundle (pullback.fst F ρ) L)
    (pullbackUnitMap (pullback.fst F ρ) c)
    (pullbackUnitMap (pullback.fst F ρ) a) U hU
  rw [genericFiberLineRatioNorm_swap,
    sectionPairParameterChart_norm_quotient F ρ hU.fromSpec L a c] at h
  exact h

/-- Regularity after changing the parameter retains every point of the
original finite fiber over the new generic point. -/
theorem sectionPairParameter_preimage_generic_units
    {B T T' : Scheme.{u}} (F : B ⟶ T) [IsFinite F]
    (ρ : T' ⟶ T) [IsIntegral T']
    (L : LineBundle B) (a : L.val ⟶ SheafOfModules.unit B.ringCatSheaf)
    [Mono (pullbackUnitMap (pullback.fst F ρ) a)] :
    F ⁻¹' Set.range (T'.fromSpecStalk (genericPoint T') ≫ ρ) ⊆
      (zeroSupportUnitOpen L a : Set B) := by
  let η := T'.fromSpecStalk (genericPoint T')
  let v := pullback.fst F ρ
  let p := pullback.fst (pullback.snd F ρ) η
  let E := sectionPairParameterChartIso F ρ η
  let : IsIso (pullbackUnitMap p (pullbackUnitMap v a)) :=
    genericFiberLineMap_isIso (pullback.snd F ρ) (pullbackLineBundle v L)
      (pullbackUnitMap v a)
  let := pullbackUnitMap_comp_isIso_of_nested v p a
  let := pullbackUnitMap_comp_isIso_of_first (p ≫ v) E.inv a
  have hv : E.inv ≫ p ≫ v = pullback.fst F (η ≫ ρ) := by
    rw [← sectionPairParameterChartIso_hom_fst F ρ η, Iso.inv_hom_id_assoc]
  have : IsIso (pullbackUnitMap (pullback.fst F (η ≫ ρ)) a) := by
    rw [← hv]
    infer_instance
  have : IsIso ((Modules.pullback (pullback.fst F (η ≫ ρ))).map a ≫
      (pullbackUnitIso (pullback.fst F (η ≫ ρ))).hom) := by
    change IsIso (pullbackUnitMap (pullback.fst F (η ≫ ρ)) a)
    infer_instance
  let := IsIso.of_isIso_comp_right
    ((Modules.pullback (pullback.fst F (η ≫ ρ))).map a)
    (pullbackUnitIso (pullback.fst F (η ≫ ρ))).hom
  rw [← Scheme.Pullback.range_fst]
  exact range_subset_zeroSupportUnitOpen_of_pullback_isIso L a _

/-- The parameter preimage of the unchanged original good open is nonempty
from the four actual pulled regular functionals, even when the original target
is disconnected. No boundary nonemptiness assumption is introduced. -/
theorem sectionPairParameter_goodOpen_nonempty
    {B T T' : Scheme.{u}} (F : B ⟶ T) [IsFinite F]
    (ρ : T' ⟶ T) [IsIntegral T']
    (N M : LineBundle B)
    (n : N.val ⟶ SheafOfModules.unit B.ringCatSheaf)
    (d : M.val ⟶ SheafOfModules.unit B.ringCatSheaf)
    (L K : LineBundle T)
    (a : L.val ⟶ SheafOfModules.unit T.ringCatSheaf)
    (c : K.val ⟶ SheafOfModules.unit T.ringCatSheaf)
    [Mono (pullbackUnitMap (pullback.fst F ρ) n)]
    [Mono (pullbackUnitMap (pullback.fst F ρ) d)]
    [Mono (pullbackUnitMap ρ a)] [Mono (pullbackUnitMap ρ c)] :
    Nonempty (ρ ⁻¹ᵁ functionalNormProductUnitDomain F N M n d L K a c) := by
  let η := T'.fromSpecStalk (genericPoint T')
  have hη : ρ (genericPoint T') ∈ Set.range (η ≫ ρ) :=
    ⟨IsLocalRing.closedPoint T'.functionField, by
      rw [Scheme.Hom.comp_apply, T'.fromSpecStalk_closedPoint]⟩
  have hu {J : LineBundle T} (φ : J.val ⟶ SheafOfModules.unit T.ringCatSheaf)
      [Mono (pullbackUnitMap ρ φ)] :
      IsIso ((Modules.pullback (η ≫ ρ)).map φ) := by
    let : IsIso (pullbackUnitMap η (pullbackUnitMap ρ φ)) := by
      have h : IsIso (pullbackUnitMap (pullback.fst (𝟙 T') η) (pullbackUnitMap ρ φ)) :=
        genericFiberLineMap_isIso (𝟙 T') (pullbackLineBundle ρ J) (pullbackUnitMap ρ φ)
      have he : pullback.fst (𝟙 T') η = pullback.snd (𝟙 T') η ≫ η := by
        simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 T') (g := η))
      let := (congrArg (fun k : pullback (𝟙 T') η ⟶ T' =>
        IsIso (pullbackUnitMap k (pullbackUnitMap ρ φ))) he).mp h
      let hcomp := pullbackUnitMap_nested_isIso_of_comp η (pullback.snd (𝟙 T') η)
        (pullbackUnitMap ρ φ)
      have : IsIso ((Modules.pullback (pullback.snd (𝟙 T') η)).map
          (pullbackUnitMap η (pullbackUnitMap ρ φ)) ≫
          (pullbackUnitIso (pullback.snd (𝟙 T') η)).hom) := by
        change IsIso (pullbackUnitMap (pullback.snd (𝟙 T') η)
          (pullbackUnitMap η (pullbackUnitMap ρ φ)))
        infer_instance
      let := IsIso.of_isIso_comp_right
        ((Modules.pullback (pullback.snd (𝟙 T') η)).map
          (pullbackUnitMap η (pullbackUnitMap ρ φ)))
        (pullbackUnitIso (pullback.snd (𝟙 T') η)).hom
      let := Modules.pullback_isEquivalence_of_isIso (pullback.snd (𝟙 T') η)
      exact isIso_of_reflects_iso (pullbackUnitMap η (pullbackUnitMap ρ φ))
        (Modules.pullback (pullback.snd (𝟙 T') η))
    let := pullbackUnitMap_comp_isIso_of_nested ρ η φ
    have : IsIso ((Modules.pullback (η ≫ ρ)).map φ ≫ (pullbackUnitIso (η ≫ ρ)).hom) := by
      change IsIso (pullbackUnitMap (η ≫ ρ) φ)
      infer_instance
    exact IsIso.of_isIso_comp_right ((Modules.pullback (η ≫ ρ)).map φ)
      (pullbackUnitIso (η ≫ ρ)).hom
  let := hu a
  let := hu c
  refine ⟨⟨genericPoint T', ?_⟩⟩
  exact range_subset_functionalNormProductUnitDomain F N M n d L K a c (η ≫ ρ)
    (sectionPairParameter_preimage_generic_units F ρ N n)
    (sectionPairParameter_preimage_generic_units F ρ M d) hη

/-- Scalar value one is transported through associativity as a proposition
about the entire displayed pullback ring, not by identifying points. -/
theorem sectionPairParameter_scalar_assoc
    {R : Type u} [CommRing R] {T P Q D : Scheme.{u}}
    (w : Spec (.of R) ⟶ T) (ρ : T ⟶ P) (t : P ⟶ Q) (d : D ⟶ Q) (μ : R)
    (h : FiniteSchemeNormBaseChange.scalarMap (pullback.snd d ((w ≫ ρ) ≫ t)) μ = 1) :
    FiniteSchemeNormBaseChange.scalarMap (pullback.snd d (w ≫ ρ ≫ t)) μ = 1 :=
  (congrArg (fun k : Spec (.of R) ⟶ Q =>
    FiniteSchemeNormBaseChange.scalarMap (pullback.snd d k) μ = 1)
      (Category.assoc w ρ t)).mp h

/-- The complete marked and infinity boundary after changing only the target
parameter. Both branches are actual scheme pullbacks. -/
def sectionPairParameterBoundary {T P I Z : Scheme.{u}}
    (t : T ⟶ P) (i : I ⟶ P) (z : Z ⟶ P) :
    pullback i t ⨿ pullback z t ⟶ T :=
  coprod.desc (pullback.snd i t) (pullback.snd z t)

/-- Support of the complete parameter boundary. -/
theorem sectionPairParameterBoundary_range {T P I Z : Scheme.{u}}
    (t : T ⟶ P) (i : I ⟶ P) (z : Z ⟶ P) :
    Set.range (sectionPairParameterBoundary t i z) =
      t ⁻¹' (Set.range i ∪ Set.range z) := by
  rw [sectionPairParameterBoundary, Hom.range_coprod_desc,
    Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Set.preimage_union]

/-- The same association unit has value one on the full component boundary,
proved in the actual branch coordinate rings before combining sections. -/
theorem sectionPairParameterBoundary_app_inv_eq_one {T P I Z : Scheme.{u}}
    (t : T ⟶ P) (i : I ⟶ P) (z : Z ⟶ P)
    (U : T.Opens) (hU : IsAffineOpen U) (μ : Γ(T, U)ˣ)
    (hi : FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd i (hU.fromSpec ≫ t)) (μ : Γ(T, U)) = 1)
    (hz : FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd z (hU.fromSpec ≫ t)) (μ : Γ(T, U)) = 1) :
    (sectionPairParameterBoundary t i z).app U (↑(μ⁻¹) : Γ(T, U)) = 1 := by
  have hcomp {D : Scheme.{u}} (d : D ⟶ P)
      (hd : FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd d (hU.fromSpec ≫ t)) (μ : Γ(T, U)) = 1) :
      (pullback.snd d t).app U (↑(μ⁻¹) : Γ(T, U)) = 1 := by
    have hv := FiniteSchemeNormBaseChange.app_eq_one_of_isPullback_affine_scalar_eq_one
      (pullback.snd d t) (pullback.fst d t) d t (IsPullback.of_hasPullback d t)
      U hU (μ : Γ(T, U)) hd
    have hu : Units.map ((pullback.snd d t).app U).hom.toMonoidHom μ = 1 := Units.ext hv
    change (↑((Units.map ((pullback.snd d t).app U).hom.toMonoidHom μ)⁻¹) :
      Γ(pullback d t, (pullback.snd d t) ⁻¹ᵁ U)) = 1
    rw [hu]
    rfl
  exact coprod_desc_app_eq_one (pullback.snd i t) (pullback.snd z t) U _ (hcomp i hi) (hcomp z hz)

variable {S C P X Y : Scheme.{u}} (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) [IsFinite f] (jB : Y ⟶ C) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (hret : jB ≫ f = p ≫ jA)
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  (LB : LineBundle (pullback (jB ≫ f ≫ π) (f ≫ π)))
  (aB : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶
    (tensorLineBundle _ LB (dualLineBundle _
      (Hom.relativeCompactificationGraphLine (f ≫ π) jB))).val)
  (bB : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶ LB.val)

/-- The exact unchanged good open on a new parameter component. -/
def sectionPairNormParameterUnitDomain {T : Scheme.{u}}
    (ρ : T ⟶ pullback (jB ≫ f ≫ π) π) : T.Opens :=
  ρ ⁻¹ᵁ sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB

omit [Flat p] in
/-- A chart of the parameter good open is an original good chart after the
actual parameter inclusion. -/
theorem sectionPairNormParameter_fromSpec_range {T : Scheme.{u}}
    (ρ : T ⟶ pullback (jB ≫ f ≫ π) π)
    (U : T.Opens) (hU : IsAffineOpen U)
    (hUV : U ≤ sectionPairNormParameterUnitDomain π f jB jA p hret LA aA bA LB aB bB ρ) :
    Set.range (hU.fromSpec ≫ ρ) ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _) := by
  rintro _ ⟨x, rfl⟩
  apply hUV
  change hU.fromSpec x ∈ (U : Set T)
  exact hU.range_fromSpec.subset ⟨x, rfl⟩

omit [Flat p] in
/-- The unchanged original finite free cover generates component charts inside
the exact parameter good open. Freeness is also recorded in the original chart
presentation consumed by the section-pair norm-ideal theorem. -/
theorem sectionPairNormParameter_exists_free_chart
    {T : Scheme.{u}} (ρ : T ⟶ pullback (jB ≫ f ≫ π) π)
    {ι : Type u} (A : ι → CommRingCat.{u}) (v : ∀ i, Spec (A i) ⟶ P)
    [∀ i, IsOpenImmersion (v i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (v i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (v i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (v i))).toAlgebra
      Module.Free (A i) Γ(pullback f (v i), ⊤))
    (x : T) (hx : x ∈ sectionPairNormParameterUnitDomain π f jB jA p hret LA aA bA LB aB bB ρ) :
    ∃ (U : T.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      U ≤ sectionPairNormParameterUnitDomain π f jB jA p hret LA aA bA LB aB bB ρ ∧
      (let F := Hom.graphProductMap π f jB
       let : Algebra Γ(T, U) Γ(pullback F (hU.fromSpec ≫ ρ), ⊤) :=
         (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (hU.fromSpec ≫ ρ))).toAlgebra
       Module.Free Γ(T, U) Γ(pullback F (hU.fromSpec ≫ ρ), ⊤)) := by
  let F := Hom.graphProductMap π f jB
  let H := (IsPullback.of_hasPullback F ρ).paste_horiz
    (Hom.normProductMap_isPullback π f (jB ≫ f ≫ π))
  obtain ⟨U, hU, hxU, hUV, hfU⟩ :=
    FiniteSchemeNormBaseChange.exists_free_affine_neighborhood_subset_of_isPullback
      f (pullback.snd F ρ)
      (pullback.fst F ρ ≫ pullback.snd (jB ≫ f ≫ π) (f ≫ π))
      (ρ ≫ pullback.snd (jB ≫ f ≫ π) π) H A v hcover hfree
      (sectionPairNormParameterUnitDomain π f jB jA p hret LA aA bA LB aB bB ρ) x hx
  refine ⟨U, hU, hxU, hUV, ?_⟩
  let : Algebra Γ(T, U) Γ(pullback (pullback.snd F ρ) hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (pullback.snd F ρ) hU.fromSpec)).toAlgebra
  let := hfU
  exact FiniteSchemeNormBaseChange.sections_free_of_iso
    (pullback.snd (pullback.snd F ρ) hU.fromSpec)
    (pullback.snd F (hU.fromSpec ≫ ρ)) (sectionPairParameterChartIso F ρ hU.fromSpec)
    (sectionPairParameterChartIso_hom_snd F ρ hU.fromSpec)

/-- Reassociation changes no original target graph coefficient. -/
theorem sectionPairNormParameter_targetCoefficient_congr {W : Scheme.{u}}
    (v w : W ⟶ pullback (jA ≫ π) π) (hv : v = w)
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LA bA) v)]
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LA bA) w)]
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
      (tensorLineBundle _ LA
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))) aA) v)]
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
      (tensorLineBundle _ LA
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))) aA) w)] :
    sectionPairGraphCoefficient π jA LA aA bA v = sectionPairGraphCoefficient π jA LA aA bA w := by
  subst w
  rfl

omit [Flat p] in
/-- The association equation identifies the original native ratio, not a newly
chosen rational function. The source norm is taken on its whole generic algebra. -/
theorem sectionPairNormParameter_chart_native_germ
    {T' : Scheme.{u}} [IsIntegral T']
    (ρ : T' ⟶ pullback (jB ≫ f ≫ π) π)
    (U : T'.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hUV : U ≤ sectionPairNormParameterUnitDomain π f jB jA p hret LA aA bA LB aB bB ρ) :
    let T := T'
    let F := Hom.graphProductMap π f jB
    let κ := ρ ≫ Hom.retainedParameterProductMap π f jB jA p hret
    let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let MB := tensorLineBundle _ LB
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB
      (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB)) bB
    let afB := sectionDualFunctional _ MB aB
    let cfB := sectionDualFunctional _ MB cB
    let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
    let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
    ∀ [Mono (pullbackUnitMap (pullback.fst F ρ) afB)]
      [Mono (pullbackUnitMap (pullback.fst F ρ) cfB)] [Mono afA] [Mono cfA],
    let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB
      (hU.fromSpec ≫ ρ) (sectionPairNormParameter_fromSpec_range
        π f jB jA p hret LA aA bA LB aB bB ρ U hU hUV)
    letI := h.1
    letI := h.2.1
    letI := h.2.2.1
    letI := h.2.2.2
    let θB : Γ(pullback F (hU.fromSpec ≫ ρ), ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient (f ≫ π) jB LB aB bB (pullback.fst F (hU.fromSpec ≫ ρ))) ⊤
        (1 : Γ(pullback F (hU.fromSpec ≫ ρ), ⊤))
    let θA : Γ(T, U) := (Scheme.ΓSpecIso Γ(T, U)).hom
      (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA
        ((hU.fromSpec ≫ ρ) ≫ Hom.retainedParameterProductMap π f jB jA p hret)) ⊤
        (1 : Γ(Spec Γ(T, U), ⊤)))
    let : Algebra Γ(T, U) Γ(pullback F (hU.fromSpec ≫ ρ), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (hU.fromSpec ≫ ρ))).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback F (hU.fromSpec ≫ ρ), ⊤)] (μ : Γ(T, U)ˣ),
      Algebra.norm Γ(T, U) θB = (μ : Γ(T, U)) * θA →
      genericFiberLineRatioNorm (pullback.snd F ρ)
          (pullbackLineBundle (pullback.fst F ρ) (dualLineBundle _ MB))
          (pullbackUnitMap (pullback.fst F ρ) afB)
          (pullbackUnitMap (pullback.fst F ρ) cfB) /
        genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA =
      T.germToFunctionField U (↑(μ⁻¹) : Γ(T, U)) := by
  dsimp only
  intro hafB hcfB hafA hcfA
  let T := T'
  let F := Hom.graphProductMap π f jB
  let κ := ρ ≫ Hom.retainedParameterProductMap π f jB jA p hret
  let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let MB := tensorLineBundle _ LB
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
    (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
  let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB
    (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB)) bB
  let afB := sectionDualFunctional _ MB aB
  let cfB := sectionDualFunctional _ MB cB
  let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
  let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
  let : Mono (pullbackUnitMap (pullback.fst F ρ) afB) := hafB
  let : Mono (pullbackUnitMap (pullback.fst F ρ) cfB) := hcfB
  let : Mono afA := hafA
  let : Mono cfA := hcfA
  have hw : Set.range (hU.fromSpec ≫ ρ) ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _) :=
    sectionPairNormParameter_fromSpec_range π f jB jA p hret LA aA bA LB aB bB ρ U hU hUV
  let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB
    (hU.fromSpec ≫ ρ) hw
  let := h.1
  let := h.2.1
  let := h.2.2.1
  let := h.2.2.2
  intro hfree μ hμ
  let : Algebra Γ(T, U) Γ(pullback F (hU.fromSpec ≫ ρ), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (hU.fromSpec ≫ ρ))).toAlgebra
  let := hfree
  let : IsIso (pullbackUnitMap (pullback.fst F (hU.fromSpec ≫ ρ)) afB) := by
    change IsIso (Hom.pullbackToUnit afB (pullback.fst F (hU.fromSpec ≫ ρ)))
    exact h.2.1
  have hi := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB (U.ι ≫ ρ)
    (by rintro _ ⟨x, rfl⟩; exact hUV x.property)
  let : IsIso (Hom.pullbackToUnit (sectionDualFunctional _ MA aA) (U.ι ≫ κ)) := by
    exact (congrArg (fun k : U.toScheme ⟶ pullback (jA ≫ π) π =>
      IsIso (Hom.pullbackToUnit (sectionDualFunctional _ MA aA) k))
        (Category.assoc U.ι ρ (Hom.retainedParameterProductMap π f jB jA p hret))).mp hi.2.2.2
  let : IsIso (Hom.pullbackToUnit (sectionDualFunctional _ MA aA) (hU.fromSpec ≫ κ)) := by
    exact (congrArg (fun k : Spec Γ(T, U) ⟶ pullback (jA ≫ π) π =>
      IsIso (Hom.pullbackToUnit (sectionDualFunctional _ MA aA) k))
        (Category.assoc hU.fromSpec ρ
          (Hom.retainedParameterProductMap π f jB jA p hret))).mp h.2.2.2
  let : IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LA bA) (hU.fromSpec ≫ κ)) := by
    exact (congrArg (fun k : Spec Γ(T, U) ⟶ pullback (jA ≫ π) π =>
      IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LA bA) k))
        (Category.assoc hU.fromSpec ρ
          (Hom.retainedParameterProductMap π f jB jA p hret))).mp h.2.2.1
  have hB := sectionPairParameterChart_native_inverse_germ F ρ (dualLineBundle _ MB)
    afB cfB U hU
  have hθB : sectionPairGraphCoefficient (f ≫ π) jB LB aB bB
      (pullback.fst F (hU.fromSpec ≫ ρ)) =
      inv (pullbackUnitMap (pullback.fst F (hU.fromSpec ≫ ρ)) afB) ≫
        pullbackUnitMap (pullback.fst F (hU.fromSpec ≫ ρ)) cfB :=
    sectionPairIdealFrame_graphCoefficient (pullback.fst F (hU.fromSpec ≫ ρ))
      (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB bB aB
      (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB))
  rw [← hθB] at hB
  have hA := sectionPairTarget_genericRatio_inv_eq_chart_germ π jA LA aA bA κ U hU
  have hθA := sectionPairNormParameter_targetCoefficient_congr π jA LA aA bA
    ((hU.fromSpec ≫ ρ) ≫ Hom.retainedParameterProductMap π f jB jA p hret)
    (hU.fromSpec ≫ κ)
    (Category.assoc hU.fromSpec ρ (Hom.retainedParameterProductMap π f jB jA p hret))
  rw [hθA] at hμ
  rw [hμ, map_mul, ← hA] at hB
  have hA0 := genericFiberLineRatioNorm_ne_zero (𝟙 T)
    (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA
  have hinv : T.germToFunctionField U (↑(μ⁻¹) : Γ(T, U)) =
      (T.germToFunctionField U (μ : Γ(T, U)))⁻¹ := by
    exact Units.val_inv_eq_inv_val (Units.map (T.germToFunctionField U).hom.toMonoidHom μ)
  rw [hinv]
  exact normAssociation_ratio_eq_inv _ _ _ hA0 hB

section Marked

variable {Z D DA : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (hA : jA ≫ π = q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  [IsClosedImmersion (z ≫ jA)]
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range jB) (Set.range d))
  (hpairB : pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) aB ≫
      pullbackTensorMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) LB.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB)).val =
    tensorUnitSection (pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) bB)
      (Hom.relativeFullBoundaryFrame q (f ≫ π) jB p
        (Hom.retained_source_structure q π f jB jA p hret hA) z s hs H e d hd).inv)
  (bE : (Scheme.residualMarkedFiberOpen f jB (z ≫ jA) s
    (Hom.retainedSectionPair_marked_map f jB jA p hret z s hs)).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f jB (z ≫ jA) s
    (Hom.retainedSectionPair_marked_map f jB jA p hret z s hs))
  (dA : DA ⟶ P) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (hpairA : pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) aA ≫
      pullbackTensorMap (Hom.fullBoundaryProductMap π jA dA z) LA.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)).val =
    tensorUnitSection (pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) bA)
      (Hom.relativeFullBoundaryFrame q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)

include hpairB hbE hpairA in
/-- The original two section pairs construct a regular unit on their exact good
open. Its native germ is the original norm ratio, and its value on the complete
original boundary scheme is one. The affine family and all its units are built
inside this proof, rather than supplied as a normalization premise. -/
theorem sectionPairNormParameter_exists_normalized_ratio
    {T' : Scheme.{u}} [IsIntegral T']
    (ρ : T' ⟶ pullback (jB ≫ f ≫ π) π) [IsOpenImmersion ρ] [IsAffineHom dA]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) aB)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) bB)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) aA)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) bA)]
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
    {ι : Type u} (A : ι → CommRingCat.{u}) (v : ∀ i, Spec (A i) ⟶ P)
    [∀ i, IsOpenImmersion (v i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (v i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (v i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (v i))).toAlgebra
      Module.Free (A i) Γ(pullback f (v i), ⊤)) :
    let T := T'
    let F := Hom.graphProductMap π f jB
    let κ := ρ ≫ Hom.retainedParameterProductMap π f jB jA p hret
    let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let MB := tensorLineBundle _ LB
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB
      (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB)) bB
    let afB := sectionDualFunctional _ MB aB
    let cfB := sectionDualFunctional _ MB cB
    let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
    let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
    let bfB := sectionDualFunctional _ LB bB
    let bfA := pullbackUnitMap κ (sectionDualFunctional _ LA bA)
    ∀ [Mono (pullbackUnitMap (pullback.fst F ρ) afB)]
      [Mono (pullbackUnitMap (pullback.fst F ρ) cfB)] [Mono afA] [Mono cfA]
      [Mono (pullbackUnitMap (pullback.fst F ρ) bfB)] [Mono bfA],
    let V := sectionPairNormParameterUnitDomain π f jB jA p hret LA aA bA LB aB bB ρ
    let E := sectionPairParameterBoundary (ρ ≫ pullback.snd (jB ≫ f ≫ π) π) dA (z ≫ jA)
    ∃ (hV : Nonempty V) (R : Γ(T, V)) (eV : _ ⟶ V.toScheme),
      eV ≫ V.ι = E ∧ IsUnit R ∧
      (letI := hV
       T.germToFunctionField V R =
        genericFiberLineRatioNorm (pullback.snd F ρ)
          (pullbackLineBundle (pullback.fst F ρ) (dualLineBundle _ MB))
          (pullbackUnitMap (pullback.fst F ρ) afB) (pullbackUnitMap (pullback.fst F ρ) cfB) /
          genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA) ∧
      E.app V R = 1 := by
  dsimp only
  intro hafB hcfB hafA hcfA hbfB hbfA
  let T := T'
  let F := Hom.graphProductMap π f jB
  let κ := ρ ≫ Hom.retainedParameterProductMap π f jB jA p hret
  let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let MB := tensorLineBundle _ LB
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
    (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
  let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB
    (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB)) bB
  let afB := sectionDualFunctional _ MB aB
  let cfB := sectionDualFunctional _ MB cB
  let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
  let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
  let : Mono (pullbackUnitMap (pullback.fst F ρ) afB) := hafB
  let : Mono (pullbackUnitMap (pullback.fst F ρ) cfB) := hcfB
  let : Mono afA := hafA
  let : Mono cfA := hcfA
  let bfB := sectionDualFunctional _ LB bB
  let bfA := pullbackUnitMap κ (sectionDualFunctional _ LA bA)
  let : Mono (pullbackUnitMap (pullback.fst F ρ) bfB) := hbfB
  let : Mono bfA := hbfA
  let V := sectionPairNormParameterUnitDomain π f jB jA p hret LA aA bA LB aB bB ρ
  let E := sectionPairParameterBoundary (ρ ≫ pullback.snd (jB ≫ f ≫ π) π) dA (z ≫ jA)
  let Rnative := genericFiberLineRatioNorm (pullback.snd F ρ)
          (pullbackLineBundle (pullback.fst F ρ) (dualLineBundle _ MB))
          (pullbackUnitMap (pullback.fst F ρ) afB) (pullbackUnitMap (pullback.fst F ρ) cfB) /
    genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA
  have hEV₀ := sectionPairNormUnitDomain_contains_boundary π f jB jA p hret LA aA bA LB aB bB
    z s hs d bE hbE dA bI hbI
  have hEV : Set.range E ⊆ (V : Set T) := by
    intro x hx
    apply hEV₀
    rw [Hom.range_normFullBoundaryMap]
    rw [sectionPairParameterBoundary_range] at hx
    exact hx
  let κ₀ := Hom.retainedParameterProductMap π f jB jA p hret
  have nestedMono (M : (pullback (jA ≫ π) π).Modules)
      (φ : M ⟶ SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf)
      [Mono (pullbackUnitMap (ρ ≫ κ₀) φ)] : Mono (pullbackUnitMap ρ (pullbackUnitMap κ₀ φ)) := by
    rw [← pullbackUnitMap_comp]
    infer_instance
  let := nestedMono _ (sectionDualFunctional _ MA aA)
  let := nestedMono _ (sectionDualFunctional _ LA bA)
  have hV : Nonempty V := sectionPairParameter_goodOpen_nonempty F ρ
    (dualLineBundle _ MB) (dualLineBundle _ LB) afB bfB
    (pullbackLineBundle κ₀ (dualLineBundle _ MA))
    (pullbackLineBundle κ₀ (dualLineBundle _ LA))
    (pullbackUnitMap κ₀ (sectionDualFunctional _ MA aA))
    (pullbackUnitMap κ₀ (sectionDualFunctional _ LA bA))
  let := hV
  choose U hU hx hUV hfreeU using fun x : V =>
    sectionPairNormParameter_exists_free_chart π f jB jA p hret LA aA bA LB aB bB
      ρ A v hcover hfree x.val x.property
  have hunion : iSup U = V := by
    apply le_antisymm
    · exact iSup_le hUV
    · intro x hxV
      exact Opens.mem_iSup.mpr ⟨⟨x, hxV⟩, hx ⟨x, hxV⟩⟩
  let (x : V) : Nonempty (U x) := ⟨⟨x.val, hx x⟩⟩
  have hlocal (x : V) : ∃ μ : Γ(T, U x)ˣ,
      T.germToFunctionField (U x) (↑(μ⁻¹) : Γ(T, U x)) = Rnative ∧
      E.app (U x) (↑(μ⁻¹) : Γ(T, U x)) = 1 := by
    have hw := sectionPairNormParameter_fromSpec_range π f jB jA p hret LA aA bA LB aB bB
      ρ (U x) (hU x) (hUV x)
    let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB
      ((hU x).fromSpec ≫ ρ) hw
    let := h.1
    let := h.2.1
    let := h.2.2.1
    let := h.2.2.2
    let : Algebra Γ(T, U x) Γ(pullback F ((hU x).fromSpec ≫ ρ), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F ((hU x).fromSpec ≫ ρ))).toAlgebra
    let := hfreeU x
    obtain ⟨μ, hμ, hm, hi⟩ := sectionPairNormUnitDomain_chart_boundary_association
      π f jB jA p hret LA aA bA LB aB bB q hA z s hs H e d hd hpairB bE hbE
      dA hdA hpairA bI hbI ((hU x).fromSpec ≫ ρ) hw
    refine ⟨μ, ?_, sectionPairParameterBoundary_app_inv_eq_one
      (ρ ≫ pullback.snd (jB ≫ f ≫ π) π) dA (z ≫ jA)
      (U x) (hU x) μ
      (sectionPairParameter_scalar_assoc (hU x).fromSpec ρ
        (pullback.snd (jB ≫ f ≫ π) π) dA _ hi)
      (sectionPairParameter_scalar_assoc (hU x).fromSpec ρ
        (pullback.snd (jB ≫ f ≫ π) π) (z ≫ jA) _ hm)⟩
    exact (sectionPairNormParameter_chart_native_germ π f jB jA p hret LA aA bA LB aB bB
      ρ (U x) (hU x) (hUV x) μ hμ).symm
  choose μ hμR hμE using hlocal
  have : Nonempty (iSup U : T.Opens) := hunion.symm ▸ hV
  obtain ⟨R, eV, heV, hRunit, hRgerm, _, hRboundary⟩ :=
    Scheme.exists_rationalUnit_boundary_gluing E U Rnative
      (fun x => (↑((μ x)⁻¹) : Γ(T, U x))) (fun x => ((μ x)⁻¹).isUnit)
      hμR hμE (by simpa only [hunion] using hEV)
  have hout : ∃ (hW : Nonempty (iSup U : T.Opens)) (R : Γ(T, iSup U))
      (eW : _ ⟶ (iSup U).toScheme), eW ≫ (iSup U).ι = E ∧ IsUnit R ∧
      (letI := hW; T.germToFunctionField (iSup U) R = Rnative) ∧ E.app (iSup U) R = 1 :=
    ⟨inferInstance, R, eV, heV, hRunit, hRgerm, hRboundary⟩
  have result : ∀ W : T.Opens, W = iSup U →
      ∃ (hW : Nonempty W) (R : Γ(T, W)) (eW : _ ⟶ W.toScheme),
        eW ≫ W.ι = E ∧ IsUnit R ∧
        (letI := hW; T.germToFunctionField W R = Rnative) ∧ E.app W R = 1 := by
    rintro W rfl
    exact hout
  exact result V hunion.symm

end Marked

end AlgebraicGeometry.Scheme.RelativeCurvePencil
