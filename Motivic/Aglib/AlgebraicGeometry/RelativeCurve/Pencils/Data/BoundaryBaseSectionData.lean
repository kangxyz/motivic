/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.FullBoundarySectionData
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.MarkedDiagram
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilSites

/-! # Retain the same global Serre choice on the actual coefficient-restricted diagram

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundaryBaseSectionData`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

local instance {S X Y C : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
    (π : C ⟶ S) (j : Y ⟶ C) [IsOpenImmersion j] (hj : j ≫ π = p ≫ q)
    (U : X.Opens) (V : S.Opens) :
    IsOpenImmersion (boundaryBaseCoverInclusion q p π j hj U V) :=
  boundaryBaseCoverInclusion_open q p π j hj U V

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) (m : ℕ) (eι : ι ≃ Fin (m + 1)) [Finite ι]
  {X Y A Z C D T : Scheme.{u}}
  [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine T]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] (a : A ⟶ X) [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f] (j : Y ⟶ C) [IsOpenImmersion j]
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (v : T ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
  (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)
  (U : X.Opens) (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme] [IsAffine (boundaryBaseSourceOpen q U V).toScheme]
  (h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U)

include hs H ha hd hc m eι in
/-- All affine, Noetherian and marked-square inputs are derived on the original refinement.
The supplied final marked frame and full-boundary frame are used unchanged, once. -/
theorem exists_boundarySectionData_on_base_refinement
    (e : SheafOfModules.unit
      (pullback (boundaryBaseSpecProjection q U V)
        (boundaryBaseLift q z U V h ≫ boundaryBaseSpecProjection q U V)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (boundaryBaseSpecProjection q U V)
        (boundaryBaseLift q z U V h)))
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
    let j' := boundaryBaseCoverInclusion q p π j hj U V
    let z' := boundaryBaseLift q z U V h
    let s' := boundaryBaseCoverLift q p z s hs U V h
    let d' := boundaryBaseWholeMap π d V
    ∃ (han : Disjoint (Set.range (boundaryBaseCoverMap q a U V)) (Set.range z'))
      (hdn : Disjoint (Set.range j') (Set.range d')),
      Nonempty (BoundarySectionData (boundaryBaseSpecProjection q U V)
        (f' ≫ toSpec Γ(V.toScheme, ⊤) ι) j' (boundaryBaseCoverMap q p U V)
        (boundaryBaseCoverInclusion_spec_projection R ι q p f j hj U V)
        (boundaryBaseCoverMap q a U V) z' s'
        (boundaryBaseCoverLift_map q p z s hs U V h)
        (boundaryBaseCoverLift_isPullback q p z s hs U V h H) e han d' hdn) := by
  let π := f ≫ toSpec R ι
  let f' := boundaryBaseProjectiveMap R ι f V
  let j' := boundaryBaseCoverInclusion q p π j hj U V
  let z' := boundaryBaseLift q z U V h
  let s' := boundaryBaseCoverLift q p z s hs U V h
  let d' := boundaryBaseWholeMap π d V
  have : IsOpenImmersion j' := boundaryBaseCoverInclusion_open q p π j hj U V
  have : IsClosedImmersion (s' ≫ j') :=
    boundaryBaseSourceZero_closed q p z s hs π j hj U V h
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫ q)
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian (a ≫ q)
  have : IsNoetherianRing Γ((boundaryBaseCoverOpen q p U V).toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherianRing Γ((boundaryBaseCoverOpen q a U V).toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have han : Disjoint (Set.range (boundaryBaseCoverMap q a U V)) (Set.range z') := by
    apply Set.disjoint_left.mpr
    rintro x ⟨b, rfl⟩ ⟨c, he⟩
    have he' := congrArg (fun x => (boundaryBaseSourceOpen q U V).ι x) he
    change (z' ≫ (boundaryBaseSourceOpen q U V).ι) c =
      (boundaryBaseCoverMap q a U V ≫ (boundaryBaseSourceOpen q U V).ι) b at he'
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
      boundaryBaseFullMarkedFrame q p π j hj z s hs U V h d
        ((Modules.pullback f').obj (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)))
        ((Modules.pullbackComp
          (coprod.desc d' (boundaryBaseWholeMap π (s ≫ j) V)) f').app
            (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≪≫ eF n)
  refine ⟨han, hdn, ?_⟩
  exact exists_boundarySectionData_of_full_target_frame
    (R := Γ(V.toScheme, ⊤)) (ι := ι) (m := m) (eι := eι)
    (q := boundaryBaseSpecProjection q U V) (f := f') (j := j')
    (p := boundaryBaseCoverMap q p U V)
    (hq := boundaryBaseCoverInclusion_spec_projection R ι q p f j hj U V)
    (a := boundaryBaseCoverMap q a U V) (z := z') (s := s')
    (hs := boundaryBaseCoverLift_map q p z s hs U V h)
    (H := boundaryBaseCoverLift_isPullback q p z s hs U V h H)
    (e := e) (ha := han) (d := d') (hd := hdn)
    (boundaryBaseRetainedTarget π V v)
    (boundaryBaseSourceBoundary_cover q p z s hs π j hj d U V h v hc) eFn

end AlgebraicGeometry.Scheme.RelativeCurvePencil
