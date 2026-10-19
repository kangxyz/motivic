/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.MarkedBaseChange
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilSites

/-! # Original target geometry on the common coefficient neighborhood

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeGeometry`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.RestrictedThickenedBoundary`,
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeSectionPair`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme Scheme.Hom
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  {D Z V : Scheme.{u}}
local notation "π" => (𝟙 _) ≫ toSpec R (ULift (Fin 2))

/-- Any original target map is reexpressed by the same native projective iso. -/
@[reassoc]
theorem targetNativeInfinity_coefficient (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) :
    targetNativeInfinity R O d ≫
      ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R O.ι)
        (ULift.{u} (Fin 2)) = ((d ≫ π) ⁻¹ᵁ O).ι ≫ d := by
  unfold targetNativeInfinity
  rw [Category.assoc]
  change boundaryBaseWholeMap π d O ≫
    ConstantCurve.affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) O.ι (𝟙 _) ≫ _ = _
  rw [ConstantCurve.affineSourceToProjectiveSpace_map, Category.comp_id,
    boundaryBaseWholeMap_snd]

/-- Closed whole infinity survives the exact base and coordinate changes. -/
instance targetNativeInfinity_closed (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    [IsClosedImmersion d] : IsClosedImmersion (targetNativeInfinity R O d) := by
  dsimp [targetNativeInfinity]
  infer_instance

/-- The original retained target, only restricted on the coefficient base. -/
def targetNativeRetained (v : V ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) :
    ((v ≫ π) ⁻¹ᵁ O).toScheme ⟶ ProjectiveSpace Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) :=
  boundaryBaseRetainedTarget π O v ≫ (targetProjectiveBaseIso R O.ι).hom

/-- Open retained targets survive without replacing them by smaller parameter opens. -/
instance targetNativeRetained_open (v : V ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    [IsOpenImmersion v] : IsOpenImmersion (targetNativeRetained R O v) := by
  have : IsOpenImmersion (boundaryBaseWholeMap π v O) :=
    inferInstanceAs (IsOpenImmersion (boundaryBaseRetainedTarget π O v))
  dsimp only [targetNativeRetained]
  infer_instance

instance targetNativeRetained_smooth (v : V ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    [SmoothOfRelativeDimension 1 (v ≫ π)] :
    SmoothOfRelativeDimension 1
      (targetNativeRetained R O v ≫ ((𝟙 _) ≫ toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))) := by
  simpa only [targetNativeRetained, targetProjectiveBaseIso, boundaryBaseProjectiveMap,
    asIso_hom, Category.id_comp, Category.assoc] using
    (inferInstance : SmoothOfRelativeDimension 1
      (boundaryBaseRetainedTarget π O v ≫
        (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (𝟙 _) O ≫
          toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)))))

/-- The original marked closed subscheme remains the literal marked closed subscheme. -/
instance targetNativeMarked_chart_closed (z : Z ⟶ Spec (.of (Polynomial R)))
    [IsClosedImmersion (z ≫ chart R 0)] :
    IsClosedImmersion (targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0) := by
  rw [targetNativeMarked_chart]
  infer_instance

/-- Infinity stays disjoint from the whole native affine line. -/
theorem targetNativeInfinity_disjoint (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (hd : Disjoint (Set.range (chart R 0)) (Set.range d)) :
    Disjoint (Set.range (chart Γ(O.toScheme, ⊤) 0)) (Set.range (targetNativeInfinity R O d)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have he := congrArg (fun x =>
    ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R O.ι)
      (ULift.{u} (Fin 2)) x) hb
  simp only [← Scheme.Hom.comp_apply] at he
  rw [targetNativeInfinity_coefficient, chart_map] at he
  exact Set.disjoint_iff_forall_ne.mp hd ⟨_, rfl⟩ ⟨_, rfl⟩ he.symm

/-- The range comparison uses the entire original coefficient inverse image. -/
theorem mem_range_targetNativeInfinity_iff
    (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (x : ProjectiveSpace Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) :
    x ∈ Set.range (targetNativeInfinity R O d) ↔
      pullback.snd O.ι π ((targetProjectiveBaseIso R O.ι).inv x) ∈ Set.range d := by
  rw [← mem_range_boundaryBaseWholeMap_iff π d O]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    change _ = ((targetProjectiveBaseIso R O.ι).hom ≫
      (targetProjectiveBaseIso R O.ι).inv) ((boundaryBaseWholeMap π d O) y)
    simp
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change (targetProjectiveBaseIso R O.ι).hom ((boundaryBaseWholeMap π d O) y) = x
    rw [hy]
    change ((targetProjectiveBaseIso R O.ι).inv ≫
      (targetProjectiveBaseIso R O.ι).hom) x = x
    simp

/-- The retained target, whole infinity and whole marked scheme still cover. -/
theorem targetNative_cover (z : Z ⟶ Spec (.of (Polynomial R)))
    (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (v : V ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (hc : ∀ x, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (z ≫ chart R 0))
    (x : ProjectiveSpace Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) :
    x ∈ Set.range (targetNativeRetained R O v) ∨
      x ∈ Set.range (targetNativeInfinity R O d) ∨
        x ∈ Set.range (targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0) := by
  rcases hc (pullback.snd O.ι π ((targetProjectiveBaseIso R O.ι).inv x)) with hv | hd | hz
  · exact Or.inl ((mem_range_targetNativeInfinity_iff R O v x).mpr hv)
  · exact Or.inr (Or.inl ((mem_range_targetNativeInfinity_iff R O d x).mpr hd))
  · right; right
    obtain ⟨y, hy⟩ := (mem_range_targetNativeInfinity_iff R O (z ≫ chart R 0) x).mpr hz
    refine ⟨(targetMarkedOpenIso R O z).inv y, ?_⟩
    have hchart : targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0 =
        (targetMarkedOpenIso R O z).hom ≫ targetNativeInfinity R O (z ≫ chart R 0) :=
      targetNativeMarked_chart R O z
    rw [hchart, Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply (targetMarkedOpenIso R O z).inv
        (targetMarkedOpenIso R O z).hom y, Iso.inv_hom_id]
    exact hy

end AlgebraicGeometry.RelativeProjectiveLine
