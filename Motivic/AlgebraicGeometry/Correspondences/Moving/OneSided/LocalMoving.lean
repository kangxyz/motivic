/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.Moving.OneSided.RelativeMoving
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Postcomposition
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedRefinedFrames
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedRefinedSites
/-! # Local moving from one given good target curve presentation

All local boundary frames are constructed. The homotopy keeps the original target;
only its base and the parameter neighborhood are shrunk. No presheaf sheafness is used.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Moving Scheme.Hom
open Scheme.RelativeCurvePencil
universe u
namespace Motivic.OneSidedMovingEndpoints
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) (n : ℕ) (eι : ι ≃ Fin (n + 1)) [Finite ι]
  {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine A.left]
  {C Z D : Scheme.{u}} (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  (x : X.left ⟶ C) [IsOpenImmersion x]
  [SmoothOfRelativeDimension 1 (x ≫ (f ≫ toSpec R ι))]
  (a : A ⟶ X) [IsOpenImmersion a.left]
  (t : Spec (.of R) ⟶ Spec (.of k))
  (hbase : (x ≫ (f ≫ toSpec R ι)) ≫ t = X.hom)
  (z : Z ⟶ X.left) [IsClosedImmersion (z ≫ x)]
  (d : D ⟶ C) [IsClosedImmersion d]
  (hd : Disjoint (Set.range x) (Set.range d))
  (hX : ∀ c : C, c ∈ Set.range x ∨ c ∈ Set.range d)
  (hA : ∀ c : C, c ∈ Set.range (a.left ≫ x) ∨
    c ∈ Set.range d ∨ c ∈ Set.range (z ≫ x))
  (U : X.left.Opens) (W : (Spec (.of R)).Opens) [IsAffine W.toScheme]
  [IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme]
  (h : ∀ b : Z, (z ≫ (x ≫ f ≫ toSpec R ι)) b ∈ W → z b ∈ U)

include eι hbase hd hX hA in
private theorem moving_on_refinement
    (e : SheafOfModules.unit
      (pullback (boundaryBaseSpecProjection (x ≫ f ≫ toSpec R ι) U W)
        (boundaryBaseLift (x ≫ f ≫ toSpec R ι) z U W h ≫
          boundaryBaseSpecProjection (x ≫ f ≫ toSpec R ι) U W)).ringCatSheaf ≅
        idealModule (boundaryGraphTarget
          (boundaryBaseSpecProjection (x ≫ f ≫ toSpec R ι) U W)
          (boundaryBaseLift (x ≫ f ≫ toSpec R ι) z U W h)))
    (eF : ∀ m : ℕ, (Scheme.Modules.pullback
      (boundaryBaseWholeMap (f ≫ toSpec R ι) (coprod.desc d (z ≫ x)) W ≫
        boundaryBaseProjectiveMap R ι f W)).obj
      (twistingSheaf Γ(W.toScheme, ⊤) ι (m : ℤ)) ≅
        SheafOfModules.unit
          ((coprod.desc d (z ≫ x) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ W).toScheme.ringCatSheaf) :
    HasMovingEndpoints (refinedSourceToOriginal X (x ≫ f ≫ toSpec R ι) U W) a := by
  let π := f ≫ toSpec R ι
  let q := x ≫ π
  let f' := boundaryBaseProjectiveMap R ι f W
  let j' := refinedParameterInclusion q π x rfl U W
  let x' := boundaryBaseRetainedTarget π W x
  let z' := boundaryBaseLift q z U W h
  let d' := boundaryBaseWholeMap π d W
  let S' := refinedSourceSite X q U W
  let X' := refinedTargetSite X q W
  let A' := refinedGoodSite X q W a
  let φ' := refinedSourceToTarget X q U W
  let a' := refinedGoodToTarget X q W a
  have : IsAffine S'.left :=
    inferInstanceAs (IsAffine (boundaryBaseSourceOpen q U W).toScheme)
  have : IsAffine X'.left := inferInstanceAs (IsAffine (q ⁻¹ᵁ W).toScheme)
  have : IsAffine A'.left := inferInstanceAs (IsAffine ((a.left ≫ q) ⁻¹ᵁ W).toScheme)
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherianRing Γ(S'.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherianRing Γ(W.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsLocallyNoetherian (boundaryBaseCompactification π W) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst W.ι π)
  have : IsLocallyNoetherian (pullback (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι))
      (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
  have hS : (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)) ≫ boundaryBaseFieldMap W t = S'.hom := by
    rw [refinedParameterInclusion_projective]
    simp only [boundaryBaseSpecProjection, boundaryBaseFieldMap, Category.assoc,
      Iso.hom_inv_id_assoc, boundaryBaseSourceProjection_ι_assoc]
    rw [hbase]
    rfl
  have hXt : (x' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)) ≫ boundaryBaseFieldMap W t = X'.hom := by
    rw [boundaryBaseProjectiveMap_toSpec]
    simp only [boundaryBaseFieldMap, Category.assoc, Iso.hom_inv_id_assoc,
      pullback.condition_assoc]
    change boundaryBaseWholeMap π x W ≫ pullback.snd W.ι π ≫ π ≫ t = _
    rw [boundaryBaseWholeMap_snd_assoc]
    rw [← Category.assoc x π, hbase]
    rfl
  have hφ : φ'.left ≫ x' = j' := refinedParameterToTarget_inclusion q π x rfl U W
  have ha : a'.left ≫ x' = boundaryBaseRetainedTarget π W (a.left ≫ x) := by
    apply (cancel_mono (pullback.snd W.ι π)).mp
    change (a.left ∣_ (q ⁻¹ᵁ W)) ≫ x' ≫ pullback.snd W.ι π = _
    simp only [x', boundaryBaseRetainedTarget, boundaryBaseWholeMap_snd]
    exact morphismRestrict_ι_assoc a.left (q ⁻¹ᵁ W) x
  have he : SheafOfModules.unit
      (pullback (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι))
        (z' ≫ (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)))).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)) z') := by
    have hproj : j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι) =
        boundaryBaseSpecProjection q U W :=
      refinedParameterInclusion_projective R ι f q x rfl U W
    rw [hproj]
    exact e
  have hcA : ∀ c : boundaryBaseCompactification π W,
      c ∈ Set.range (a'.left ≫ x') ∨ c ∈ Set.range d' ∨ c ∈ Set.range (z' ≫ j') := by
    rw [ha]
    exact refinedGood_cover q π x rfl U W z h d a.left hA
  have hm := exists_moving_endpoints_of_relative_frames
    (S := S') (X := X') (V := A') Γ(W.toScheme, ⊤) ι n eι f' j' x' a' φ' hφ
    (boundaryBaseFieldMap W t) hS hXt z' d'
    (refinedParameter_disjoint q π x rfl U W d hd)
    (boundaryBaseWholeTarget_cover π d W x hX) hcA he
    (fun m => refinedFullTwistFrame R ι f x U W z h d m (eF m))
  have hm' := hm.postcompose (refinedTargetToOriginal X q W)
    (refinedGoodToOriginal X q W a) a (refinedGoodToTarget_original X q W a)
  simpa only [φ', refinedSourceToTarget_original] using hm'

include eι hbase hd hX hA in
omit [IsAffine W.toScheme]
  [IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme] in
/-- Every parameter point has an actual Zariski neighborhood with a constructed
moving correspondence and homotopy. Only a genuine good curve presentation is
assumed; all boundary frames, sections and zero families are produced internally. -/
theorem exists_local_moving_of_curve_presentation
    [IsFinite (z ≫ (x ≫ f ≫ toSpec R ι))]
    [IsFinite ((coprod.desc d (z ≫ x) ≫ f) ≫ toSpec R ι)] (p : X.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ p ∈ U ∧
    ∃ (W : (Spec (.of R)).Opens) (hW : IsAffineOpen W),
      let : IsAffine W.toScheme := hW
      (x ≫ f ≫ toSpec R ι) p ∈ W ∧
      ∃ hO : IsAffineOpen (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W),
        let : IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme := hO
        HasMovingEndpoints (refinedSourceToOriginal X (x ≫ f ≫ toSpec R ι) U W) a := by
  obtain ⟨U, hU, hpU, W, hW, hpW, h, hO, ⟨e⟩, ⟨eF⟩⟩ :=
    exists_simultaneous_native_boundary_frames R ι (x ≫ f ≫ toSpec R ι)
      z f (coprod.desc d (z ≫ x)) p
  let : IsAffine W.toScheme := hW
  let : IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme := hO
  refine ⟨U, hU, hpU, W, hW, hpW, hO, ?_⟩
  exact moving_on_refinement R ι n eι f x a t hbase z d hd hX hA U W h e eF

end Motivic.OneSidedMovingEndpoints
