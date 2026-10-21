/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.FullBoundarySectionData
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve

/-! # Choose source sections with the same final native marked frame as the target

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeBoundarySectionData`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeSimultaneousSectionChoice`.
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
local instance nativeBoundarySectionDataSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
/-- The relative-dimension instance used in this module. -/
local instance nativeBoundarySectionDataSmoothRelativeDimension (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) (m : ℕ) (eι : ι ≃ Fin (m + 1)) [Finite ι]
  {Y A Z C D T : Scheme.{u}}
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

include hs H ha hd hc m eι in
/-- All affine, Noetherian and marked-square inputs are derived on the original refinement.
The supplied final marked frame and full-boundary frame are used unchanged, once. -/
theorem exists_boundarySectionData_on_native_base_refinement
    (e : SheafOfModules.unit
      (pullback (boundaryLineProjection Γ(V.toScheme, ⊤))
        (targetNativeMarked R V z ≫ boundaryLineProjection Γ(V.toScheme, ⊤))).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (boundaryLineProjection Γ(V.toScheme, ⊤))
        (targetNativeMarked R V z)))
    (eF : ∀ n : ℕ, (Modules.pullback
      (coprod.desc (boundaryBaseWholeMap (f ≫ toSpec R ι) d V)
        (boundaryBaseWholeMap (f ≫ toSpec R ι) (s ≫ j) V) ≫
          boundaryBaseProjectiveMap R ι f V)).obj
      (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≅
        SheafOfModules.unit
          ((((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme ⨿
            (((s ≫ j) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme)).ringCatSheaf) :
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
      Nonempty (BoundarySectionData (boundaryLineProjection Γ(V.toScheme, ⊤))
        (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' (sourceNativeCoverMap R V p) hqn
        (sourceNativeCoverMap R V a) z' s'
        (sourceNativeCoverLift_map R V z p s hs)
        (sourceNativeCoverLift_isPullback R V z p s hs H) e han d' hdn) := by
  let π := f ≫ toSpec R ι
  let f' := boundaryBaseProjectiveMap R ι f V
  let j' := boundaryBaseCoverInclusion (boundaryLineProjection R) p π j hj ⊤ V
  let z' := targetNativeMarked R V z
  let s' := boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ V (fun _ _ => trivial)
  let d' := boundaryBaseWholeMap π d V
  have : IsOpenImmersion j' := boundaryBaseCoverInclusion_open (boundaryLineProjection R) p π j
      hj ⊤ V
  have : IsClosedImmersion (s' ≫ j') :=
    boundaryBaseSourceZero_closed (boundaryLineProjection R) p z s hs π j hj ⊤ V
      (fun _ _ => trivial)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫
      (boundaryLineProjection R))
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian (a ≫
      (boundaryLineProjection R))
  have : IsNoetherianRing
      Γ((boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ V).toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherianRing
      Γ((boundaryBaseCoverOpen (boundaryLineProjection R) a ⊤ V).toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hqn : j' ≫ (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) =
      sourceNativeCoverMap R V p ≫ boundaryLineProjection Γ(V.toScheme, ⊤) := by
    rw [sourceNativeCoverMap_projection]
    exact boundaryBaseCoverInclusion_spec_projection R ι (boundaryLineProjection R) p f j hj ⊤ V
  have han : Disjoint (Set.range (sourceNativeCoverMap R V a)) (Set.range z') := by
    apply Set.disjoint_left.mpr
    rintro x ⟨b, rfl⟩ ⟨c, he⟩
    change (targetNativeMarked R V z) c = (sourceNativeCoverMap R V a) b at he
    rw [← boundaryBaseLift_sourceNativeParameterIso R V z] at he
    have he0 := congrArg (fun x => (sourceNativeParameterIso R V).inv x) he
    change ((boundaryBaseLift (boundaryLineProjection R) z ⊤ V (fun _ _ => trivial) ≫
      (sourceNativeParameterIso R V).hom) ≫ (sourceNativeParameterIso R V).inv) c =
      ((boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V ≫
        (sourceNativeParameterIso R V).hom) ≫ (sourceNativeParameterIso R V).inv) b at he0
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he0
    have he' := congrArg
      (fun x => (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).ι x) he0
    change (boundaryBaseLift (boundaryLineProjection R) z ⊤ V (fun _ _ => trivial) ≫
      (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).ι) c =
      (boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V ≫
        (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).ι) b at he'
    rw [boundaryBaseLift_ι, morphismRestrict_ι] at he'
    exact Set.disjoint_iff_forall_ne.mp ha ⟨_, rfl⟩ ⟨_, rfl⟩ he'.symm
  have hdn : Disjoint (Set.range j') (Set.range d') := by
    apply Set.disjoint_left.mpr
    rintro x ⟨b, rfl⟩ ⟨c, he⟩
    have he' := congrArg (fun x => pullback.snd V.ι π x) he
    change (d' ≫ pullback.snd V.ι π) c = (j' ≫ pullback.snd V.ι π) b at he'
    rw [boundaryBaseWholeMap_snd, boundaryBaseCoverInclusion_snd] at he'
    exact Set.disjoint_iff_forall_ne.mp hd ⟨_, rfl⟩ ⟨_, rfl⟩ he'.symm
  let eFn (n : ℕ) :=
    (Modules.pullbackComp (coprod.desc d' (s' ≫ j')) f').symm.app
        (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≪≫
      boundaryBaseFullMarkedFrame (boundaryLineProjection R) p π j hj z s hs ⊤ V
        (fun _ _ => trivial) d
        ((Modules.pullback f').obj (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)))
        ((Modules.pullbackComp
          (coprod.desc d' (boundaryBaseWholeMap π (s ≫ j) V)) f').app
            (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≪≫ eF n)
  refine ⟨hqn, han, hdn, ?_⟩
  exact exists_boundarySectionData_of_full_target_frame
    (R := Γ(V.toScheme, ⊤)) (ι := ι) (m := m) (eι := eι)
    (q := boundaryLineProjection Γ(V.toScheme, ⊤)) (f := f') (j := j')
    (p := sourceNativeCoverMap R V p)
    (hq := hqn)
    (a := sourceNativeCoverMap R V a) (z := z') (s := s')
    (hs := sourceNativeCoverLift_map R V z p s hs)
    (H := sourceNativeCoverLift_isPullback R V z p s hs H)
    (e := e) (ha := han) (d := d') (hd := hdn)
    (boundaryBaseRetainedTarget π V v)
    (boundaryBaseSourceBoundary_cover (boundaryLineProjection R) p z s hs π j hj d ⊤ V
      (fun _ _ => trivial) v hc) eFn

end AlgebraicGeometry.Scheme.RelativeCurvePencil
