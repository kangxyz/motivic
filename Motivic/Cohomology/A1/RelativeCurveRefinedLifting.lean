/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.RelativeCurveTargetFrameLifting
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.SimultaneousNativeFrames
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBasePencilMaps
/-! # The constructed same-base refinement in the original-section lifting theorem

The smaller parameter source is never substituted for the original retained target.
All boundary schemes retain their original scheme structures.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
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
private theorem lifting_on_constructed_refinement
    (e : SheafOfModules.unit
      (pullback (boundaryBaseSpecProjection q U V)
        (boundaryBaseLift q z U V h ≫ boundaryBaseSpecProjection q U V)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (boundaryBaseSpecProjection q U V)
        (boundaryBaseLift q z U V h)))
    (eF : ∀ n : ℕ, (Modules.pullback
      (boundaryBaseWholeMap (f ≫ toSpec R ι) (coprod.desc d (s ≫ j)) V ≫
        boundaryBaseProjectiveMap R ι f V)).obj
      (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≅
        SheafOfModules.unit
          ((coprod.desc d (s ≫ j) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    PresheafWithTransfers.HasRestrictionDifferenceLifting P
      (boundaryBasePencilGraph k R ι t q p a f j hj U V v φ hφ)
      (boundaryBasePencilBeta k R ι t q p a f j hj U V)
      (boundaryBasePencilAlpha k R ι t q p a f j hj U V) := by
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
      boundaryBaseSourceBoundaryFrame q p z s hs π j hj d U V h
        ((Modules.pullback f').obj (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)))
        ((Modules.pullbackComp (boundaryBaseWholeMap π (coprod.desc d (s ≫ j)) V) f').app
          (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≪≫ eF n)
  exact exists_relativeCurve_lifting_of_full_target_frame k Γ(V.toScheme, ⊤) ι m eι
    (boundaryBaseFieldMap V t) (boundaryBaseSpecProjection q U V) f' j'
    (boundaryBaseCoverMap q p U V)
    (boundaryBaseCoverInclusion_spec_projection R ι q p f j hj U V)
    (boundaryBaseCoverMap q a U V) (pullback.fst _ _) (pullback.snd _ _) pullback.condition
    z' s' (boundaryBaseCoverLift_map q p z s hs U V h)
    (boundaryBaseCoverLift_isPullback q p z s hs U V h H) e han d' hdn
    (boundaryBaseRetainedTarget π V v)
    (boundaryBaseSourceBoundary_cover q p z s hs π j hj d U V h v hc)
    eFn (boundaryBaseOverlapTarget q p a U V π j hj v φ hφ)
    (boundaryBaseOverlapTarget_inclusion q p a U V π j hj v φ hφ) P hP

include hs H ha hd hc m eι in
/-- Original-section quotient lifting after an actually constructed same-base refinement.
The two boundary frames, all sections and the correcting pencil are constructed internally.
Only the parameter source is shrunk; the target remains the original retained open over `V`.
The hypotheses are genuine finite-curve presentation data, not a presentation existence claim. -/
theorem exists_refined_relativeCurve_lifting
    [IsFinite (z ≫ q)]
    [IsFinite ((coprod.desc d (s ≫ j) ≫ f) ≫ toSpec R ι)]
    (x : X) (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      q x ∈ V ∧
      (∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U) ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen q U V),
        let : IsAffine (boundaryBaseSourceOpen q U V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (boundaryBasePencilGraph k R ι t q p a f j hj U V v φ hφ)
          (boundaryBasePencilBeta k R ι t q p a f j hj U V)
          (boundaryBasePencilAlpha k R ι t q p a f j hj U V) := by
  obtain ⟨U, hU, hx, V, hV, hxV, h, hW, ⟨e⟩, ⟨eF⟩⟩ :=
    exists_simultaneous_native_boundary_frames R ι q z f (coprod.desc d (s ≫ j)) x
  let : IsAffine V.toScheme := hV
  let : IsAffine (boundaryBaseSourceOpen q U V).toScheme := hW
  refine ⟨U, hU, hx, V, hV, hxV, h, hW, ?_⟩
  exact lifting_on_constructed_refinement k R ι m eι t q p a f j hj z s hs H ha d hd
    v hc φ hφ U V h e eF P hP
end AlgebraicGeometry.Scheme.RelativeCurvePencil
