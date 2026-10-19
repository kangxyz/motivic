/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeGeometry
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.BoundarySectionPair
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeCanonicalFrame

/-! # The original target pair on the already chosen common coefficient neighborhood

The marked graph frame is canonical and exposed for the source producer to use
unchanged. The full-boundary twist frames are supplied from the already chosen
common neighborhood. No new neighborhood or full-boundary frame is selected here.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeSectionPair`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeSimultaneousSectionChoice`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  {D Z V : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R)))
  [IsFinite (z ≫ boundaryLineProjection R)]
local notation "π" => (𝟙 _) ≫ toSpec R (ULift (Fin 2))

local instance : SmoothOfRelativeDimension 1 (boundaryLineProjection (Γ(O.toScheme, ⊤))) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one (Γ(O.toScheme, ⊤))

local instance : SmoothOfRelativeDimension 1
    (chart Γ(O.toScheme, ⊤) 0 ≫
      ((𝟙 _) ≫ toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))) := by
  simpa only [Category.id_comp, chart_toSpec] using
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one (Γ(O.toScheme, ⊤))

/-- Produce the actual target pair with its independent degree and complete zero data.
This uses the same final canonical marked frame and the supplied same full twist frames. -/
theorem exists_target_pair_on_native_base_refinement [IsNoetherianRing R]
    [IsClosedImmersion (z ≫ chart R 0)]
    (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsClosedImmersion d]
    (hd : Disjoint (Set.range (chart R 0)) (Set.range d))
    [IsAffine V] (v : V ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ x, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (z ≫ chart R 0))
    (eF : ∀ n : ℕ, (Modules.pullback
      (coprod.desc (boundaryBaseWholeMap π d O)
        (boundaryBaseWholeMap π (z ≫ chart R 0) O) ≫
          (targetProjectiveBaseIso R O.ι).hom)).obj
        (twistingSheaf (Γ(O.toScheme, ⊤)) (ULift.{u} (Fin 2)) (n : ℤ)) ≅
          SheafOfModules.unit
            ((((d ≫ π) ⁻¹ᵁ O).toScheme ⨿
              (((z ≫ chart R 0) ≫ π) ⁻¹ᵁ O).toScheme)).ringCatSheaf) :
    let πN := ((𝟙 _) ≫ toSpec (Γ(O.toScheme, ⊤)) (ULift.{u} (Fin 2)))
    let jN := (chart (Γ(O.toScheme, ⊤)) 0)
    ∃ bound : ℕ, ∀ degree : ℕ, bound ≤ degree →
      let T := pullbackLineBundle
        (ConstantCurve.affineSourceToProjectiveSpace Γ(O.toScheme, ⊤)
          (ULift.{u} (Fin 2)) (jN ≫ πN) (𝟙 _))
        (twistingLineBundle Γ(Spec (.of (Polynomial (Γ(O.toScheme, ⊤)))), ⊤)
          (ULift.{u} (Fin 2)) (degree : ℤ))
      let M := dualLineBundle _ (relativeCompactificationGraphLine πN jN)
      let zA := fullBoundaryProductMap πN jN
        (targetNativeInfinity R O d) (targetNativeMarked R O z)
      let iA := retainedProductInclusion (jN ≫ πN) πN (targetNativeRetained R O v)
      ∃ aS : SheafOfModules.unit (pullback (jN ≫ πN) πN).ringCatSheaf ⟶
        (tensorLineBundle _ T M).val,
      ∃ bS : SheafOfModules.unit (pullback (jN ≫ πN) πN).ringCatSheaf ⟶ T.val,
        pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val M.val =
          tensorUnitSection (pullbackSectionMap zA bS)
            (targetFullBoundaryFrame (Γ(O.toScheme, ⊤)) (targetNativeMarked R O z)
              (targetNativeCanonicalFrame R O z) (targetNativeInfinity R O d)
                (targetNativeInfinity_disjoint R O d hd)).inv ∧
        IsIso (pullbackSectionMap zA aS) ∧ IsIso (pullbackSectionMap zA bS) ∧
        CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (jN ≫ πN) πN)
          iA (tensorLineBundle _ T M) aS ∧
        CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (jN ≫ πN) πN) iA T bS := by
  have : IsNoetherianRing (Γ(O.toScheme, ⊤)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherianRing Γ(Spec (.of (Polynomial (Γ(O.toScheme, ⊤)))), ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let πN := (𝟙 _) ≫ toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))
  let jN := chart Γ(O.toScheme, ⊤) 0
  have : IsLocallyNoetherian (pullback (jN ≫ πN) πN) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (jN ≫ πN) πN)
  have : IsAffine ((v ≫ π) ⁻¹ᵁ O).toScheme :=
    boundaryBaseRetainedOpen_affine O π v
  have : IsClosedImmersion (targetNativeInfinity R O d) :=
    targetNativeInfinity_closed R O d
  have : IsClosedImmersion (targetNativeMarked R O z ≫ jN) :=
    targetNativeMarked_chart_closed R O z
  have : IsOpenImmersion (targetNativeRetained R O v) :=
    targetNativeRetained_open R O v
  have : SmoothOfRelativeDimension 1 (targetNativeRetained R O v ≫ πN) :=
    targetNativeRetained_smooth R O v
  let eFull : ∀ n : ℕ, (Modules.pullback
      (fullTargetBoundaryMap (chart Γ(O.toScheme, ⊤) 0) (targetNativeMarked R O z)
        (targetNativeInfinity R O d) ≫ 𝟙 _)).obj
      (twistingSheaf Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit
          ((((d ≫ π) ⁻¹ᵁ O).toScheme ⨿
            ((z ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme)).ringCatSheaf := fun n => by
    simpa only [Category.comp_id] using targetNativeFullBoundaryFrame R O z d n (eF n)
  have hpair := exists_target_boundary_section_pair Γ(O.toScheme, ⊤)
    (targetNativeMarked R O z) (targetNativeCanonicalFrame R O z)
    (targetNativeInfinity R O d) (targetNativeInfinity_disjoint R O d hd)
    (targetNativeRetained R O v) (targetNative_cover R O z d v hc) eFull
  -- The result is the same existential proposition, with only the local map
  -- abbreviations reduced. Keep the chosen frame opaque during this conversion.
  with_reducible exact hpair

end AlgebraicGeometry.RelativeProjectiveLine
