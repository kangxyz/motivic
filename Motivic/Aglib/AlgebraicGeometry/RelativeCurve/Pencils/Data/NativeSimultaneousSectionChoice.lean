/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeBoundarySectionData
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CommonFrames
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.CoherentIdealCoordinate
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeSectionPair

/-! # One simultaneous source and target choice on the fixed common coefficient open

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeSimultaneousSectionChoice`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.NativeSectionChoice`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

local instance {S X Y C : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
    (π : C ⟶ S) (j : Y ⟶ C) [IsOpenImmersion j] (hj : j ≫ π = p ≫ q)
    (U : X.Opens) (V : S.Opens) :
    IsOpenImmersion (boundaryBaseCoverInclusion q p π j hj U V) :=
  boundaryBaseCoverInclusion_open q p π j hj U V

/-- The smoothness instance used in this module. -/
local instance nativeSimultaneousSectionChoiceSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
/-- The relative-dimension instance used in this module. -/
local instance nativeSimultaneousSectionChoiceSmoothRelativeDimension1 (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

/-- The relative-dimension instance used in this module. -/
local instance nativeSimultaneousSectionChoiceSmoothRelativeDimension2
    (R : Type u) [CommRing R] : SmoothOfRelativeDimension 1
    (chart R 0 ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) := by
  simpa only [Category.id_comp, chart_toSpec] using
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) (m : ℕ) (eι : ι ≃ Fin (m + 1)) [Finite ι]
  {Y A Z C D T D₀ T₀ : Scheme.{u}}
  [IsAffine Y] [IsAffine A] [IsAffine T]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] (a : A ⟶ Spec (.of (Polynomial R)))
      [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f] (j : Y ⟶ C) [IsOpenImmersion j]
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ (boundaryLineProjection R))
  (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (H : IsPullback s (𝟙 Z) p z)
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (v : T ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
  (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)
  (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme]


variable [IsFinite (z ≫ boundaryLineProjection R)]
  [IsClosedImmersion (z ≫ chart R 0)]
  (d₀ : D₀ ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsClosedImmersion d₀]
  (hd₀ : Disjoint (Set.range (chart R 0)) (Set.range d₀))
  [IsAffine T₀] (v₀ : T₀ ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  [IsOpenImmersion v₀]
  [SmoothOfRelativeDimension 1 (v₀ ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))))]
  (hc₀ : ∀ x, x ∈ Set.range v₀ ∨ x ∈ Set.range d₀ ∨ x ∈ Set.range (z ≫ chart R 0))

/-- The exact original rich source output, including its coherent ideal-frame equations.
This proposition adds no witness assumptions and contains the existing section record. -/
def NativeSourceBoundarySections : Prop :=
    let e := targetNativeCanonicalFrame R V z
    let π := f ≫ toSpec R ι
    let f' := boundaryBaseProjectiveMap R ι f V
    let j' := boundaryBaseCoverInclusion (boundaryLineProjection R) p π j hj ⊤ V
    let z' := targetNativeMarked R V z
    let s' := boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ V (fun _ _ => trivial)
    let d' := boundaryBaseWholeMap π d V
    ∃ (hqn : j' ≫ (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) =
        sourceNativeCoverMap R V p ≫ boundaryLineProjection Γ(V.toScheme, ⊤))
      (han : Disjoint (Set.range (sourceNativeCoverMap R V a)) (Set.range z'))
      (hdn : Disjoint (Set.range j') (Set.range d')),
      let aI := infinityProductMap (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' d'
      let bI := graphBoundaryRestriction (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' s'
      let I := idealModule (compactificationGraph (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j')
      let E := relativeFullBoundaryIdealFrame (boundaryLineProjection Γ(V.toScheme, ⊤))
        (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' (sourceNativeCoverMap R V p) hqn
        z' s' (sourceNativeCoverLift_map R V z p s hs)
        (sourceNativeCoverLift_isPullback R V z p s hs H) e d' hdn
      ((Modules.restrictFunctor (coprod.inl : _ ⟶ _)).map E.hom ≫
          (restrictUnitIso _).hom = (coprodPullbackRestrictLeft aI bI).hom.app I ≫
            (infinityBoundaryIdealIso (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' d' hdn).inv ∧
        (Modules.restrictFunctor (coprod.inr : _ ⟶ _)).map E.hom ≫
          (restrictUnitIso _).hom = (coprodPullbackRestrictRight aI bI).hom.app I ≫
            (relativeCompactificationBoundaryFrame (boundaryLineProjection Γ(V.toScheme, ⊤))
              (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' (sourceNativeCoverMap R V p) hqn
              z' s' (sourceNativeCoverLift_map R V z p s hs)
              (sourceNativeCoverLift_isPullback R V z p s hs H) e).inv) ∧
      Nonempty (BoundarySectionData (boundaryLineProjection Γ(V.toScheme, ⊤))
        (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' (sourceNativeCoverMap R V p) hqn
        (sourceNativeCoverMap R V a) z' s'
        (sourceNativeCoverLift_map R V z p s hs)
        (sourceNativeCoverLift_isPullback R V z p s hs H) e han d' hdn) ∧
      dualBoundaryTrivialization
        (coprod.desc (infinityProductMap (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' d')
          (graphBoundaryRestriction (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' s'))
        (relativeCompactificationGraphLine (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j')
        (relativeFullBoundaryIdealFrame (boundaryLineProjection Γ(V.toScheme, ⊤))
          (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' (sourceNativeCoverMap R V p) hqn
          z' s' (sourceNativeCoverLift_map R V z p s hs)
          (sourceNativeCoverLift_isPullback R V z p s hs H) e d' hdn).symm =
        relativeFullBoundaryFrame (boundaryLineProjection Γ(V.toScheme, ⊤))
          (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' (sourceNativeCoverMap R V p) hqn
          z' s' (sourceNativeCoverLift_map R V z p s hs)
          (sourceNativeCoverLift_isPullback R V z p s hs H) e d' hdn

/-- The exact original target-pair output, with its independent degree and finite-flat zeros. -/
def NativeTargetBoundarySections : Prop :=
    let e := targetNativeCanonicalFrame R V z
    let πN := ((𝟙 _) ≫ toSpec (Γ(V.toScheme, ⊤)) (ULift.{u} (Fin 2)))
    let jN := (chart (Γ(V.toScheme, ⊤)) 0)
    ∃ degree : ℕ,
      let T := pullbackLineBundle
        (ConstantCurve.affineSourceToProjectiveSpace Γ(V.toScheme, ⊤)
          (ULift.{u} (Fin 2)) (jN ≫ πN) (𝟙 _))
        (twistingLineBundle Γ(Spec (.of (Polynomial (Γ(V.toScheme, ⊤)))), ⊤)
          (ULift.{u} (Fin 2)) (degree : ℤ))
      let M := dualLineBundle _ (relativeCompactificationGraphLine πN jN)
      let zA := fullBoundaryProductMap πN jN
        (targetNativeInfinity R V d₀) (targetNativeMarked R V z)
      let iA := retainedProductInclusion (jN ≫ πN) πN (targetNativeRetained R V v₀)
      ∃ aS : SheafOfModules.unit (pullback (jN ≫ πN) πN).ringCatSheaf ⟶
        (tensorLineBundle _ T M).val,
      ∃ bS : SheafOfModules.unit (pullback (jN ≫ πN) πN).ringCatSheaf ⟶ T.val,
        pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val M.val =
          tensorUnitSection (pullbackSectionMap zA bS)
            (targetFullBoundaryFrame (Γ(V.toScheme, ⊤)) (targetNativeMarked R V z)
              e (targetNativeInfinity R V d₀)
                (targetNativeInfinity_disjoint R V d₀ hd₀)).inv ∧
        IsIso (pullbackSectionMap zA aS) ∧ IsIso (pullbackSectionMap zA bS) ∧
        CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (jN ≫ πN) πN)
          iA (tensorLineBundle _ T M) aS ∧
        CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (jN ≫ πN) πN) iA T bS

include hs H ha hd hc m eι in
omit [IsClosedImmersion (z ≫ chart R 0)] in
/-- Choose the rich source once from the same fixed raw O(1) frame. -/
theorem exists_nativeSourceBoundarySections
    (e₁ : (Modules.restrictFunctor
      ((coprod.desc d (s ≫ j) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).ι).obj
        (pullbackLineBundle (coprod.desc d (s ≫ j) ≫ f) (twistingLineBundle R ι 1)).val ≅
          SheafOfModules.unit
            ((coprod.desc d (s ≫ j) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf)
 :
    NativeSourceBoundarySections (R := R) (ι := ι) (p := p) (a := a)
      (f := f) (j := j) (hj := hj) (z := z) (s := s) (hs := hs) (H := H)
      (d := d) (V := V) := by
  let e := targetNativeCanonicalFrame R V z
  let eF₁ := boundaryBaseCoproductTwistFramesOfUnitIso R ι f d (s ≫ j) V e₁
  obtain ⟨hqn, han, hdn, ⟨source⟩⟩ :=
    exists_boundarySectionData_on_native_base_refinement
      (R := R) (ι := ι) (m := m) (eι := eι) (p := p) (a := a)
      (f := f) (j := j) (hj := hj) (z := z) (s := s) (hs := hs) (H := H)
      (ha := ha) (d := d) (hd := hd) (v := v) (hc := hc) (V := V) e eF₁
  unfold NativeSourceBoundarySections
  with_reducible
    refine ⟨hqn, han, hdn, ?_, ⟨source⟩, ?_⟩
  · with_reducible
      exact relativeFullBoundaryIdealFrame_component_equations _ _ _ _ _ _ _ _ _ _ _ _
  · with_reducible exact relativeFullBoundaryIdealFrame_dual_eq _ _ _ _ _ _ _ _ _ _ _ _

include hd₀ hc₀ in
/-- Choose the target once from its same fixed raw O(1) frame, using its own Serre degree. -/
theorem exists_nativeTargetBoundarySections
    (e₂ : (Modules.restrictFunctor
      ((coprod.desc d₀ (z ≫ chart R 0) ≫
        ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ V).ι).obj
        (pullbackLineBundle (coprod.desc d₀ (z ≫ chart R 0) ≫ 𝟙 _)
          (twistingLineBundle R (ULift.{u} (Fin 2)) 1)).val ≅
          SheafOfModules.unit ((coprod.desc d₀ (z ≫ chart R 0) ≫
            ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ V).toScheme.ringCatSheaf) :
    NativeTargetBoundarySections (R := R) (z := z) (V := V)
      (d₀ := d₀) (hd₀ := hd₀) (v₀ := v₀) := by
  let eF₂ := boundaryBaseCoproductTwistFramesOfUnitIso R (ULift.{u} (Fin 2))
    (𝟙 _) d₀ (z ≫ chart R 0) V e₂
  obtain ⟨bound, hbound⟩ := exists_target_pair_on_native_base_refinement
    R V z d₀ hd₀ v₀ hc₀ eF₂
  unfold NativeTargetBoundarySections
  with_reducible refine ⟨bound, ?_⟩
  with_reducible exact hbound bound le_rfl

include hs H ha hd hc m eι hd₀ hc₀ in
/-- Both original outputs use the same final canonical marked frame and coefficient open.
Each producer is called once. No norm relation or extra normalization is assumed. -/
theorem exists_simultaneous_native_boundary_sections
    (e₁ : (Modules.restrictFunctor
      ((coprod.desc d (s ≫ j) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).ι).obj
        (pullbackLineBundle (coprod.desc d (s ≫ j) ≫ f) (twistingLineBundle R ι 1)).val ≅
          SheafOfModules.unit
            ((coprod.desc d (s ≫ j) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf)
    (e₂ : (Modules.restrictFunctor
      ((coprod.desc d₀ (z ≫ chart R 0) ≫
        ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ V).ι).obj
        (pullbackLineBundle (coprod.desc d₀ (z ≫ chart R 0) ≫ 𝟙 _)
          (twistingLineBundle R (ULift.{u} (Fin 2)) 1)).val ≅
          SheafOfModules.unit ((coprod.desc d₀ (z ≫ chart R 0) ≫
            ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ V).toScheme.ringCatSheaf) :
    NativeSourceBoundarySections (R := R) (ι := ι) (p := p) (a := a)
      (f := f) (j := j) (hj := hj) (z := z) (s := s) (hs := hs) (H := H)
      (d := d) (V := V) ∧
    NativeTargetBoundarySections (R := R) (z := z) (V := V)
      (d₀ := d₀) (hd₀ := hd₀) (v₀ := v₀) := by
  constructor
  · exact exists_nativeSourceBoundarySections
      (R := R) (ι := ι) (m := m) (eι := eι) (p := p) (a := a)
      (f := f) (j := j) (hj := hj) (z := z) (s := s) (hs := hs) (H := H)
      (ha := ha) (d := d) (hd := hd) (v := v) (hc := hc) (V := V) e₁
  · exact exists_nativeTargetBoundarySections
      (R := R) (z := z) (V := V) (d₀ := d₀) (hd₀ := hd₀) (v₀ := v₀) (hc₀ := hc₀) e₂

end AlgebraicGeometry.Scheme.RelativeCurvePencil
