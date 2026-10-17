/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.RelativeCurveTargetFrameLifting
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBasePencilMaps
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryGraphBaseIso
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseTwistFrame
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ProperFiniteFiberFrame
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteBoundaryTwists

/-! # Relative correction with a global diagonal frame and base-only shrinking -/

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
private theorem lifting_on_base_open_with_frames
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
/-- A global diagonal frame preserves the whole parameter curve. All target twist
frames and the actual correcting correspondences are produced after a base-only shrink. -/
theorem exists_baseOnly_relativeCurve_lifting
    (x : Spec (.of R))
    (e₀ : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget q z))
    [IsProper (coprod.desc d (s ≫ j) ≫ (f ≫ toSpec R ι))]
    (hfinite : ((coprod.desc d (s ≫ j) ≫ (f ≫ toSpec R ι)) ⁻¹' {x}).Finite)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      x ∈ V ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen q ⊤ V),
        let : IsAffine (boundaryBaseSourceOpen q ⊤ V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (boundaryBasePencilGraph k R ι t q p a f j hj ⊤ V v φ hφ)
          (boundaryBasePencilBeta k R ι t q p a f j hj ⊤ V)
          (boundaryBasePencilAlpha k R ι t q p a f j hj ⊤ V) := by
  let b := coprod.desc d (s ≫ j) ≫ (f ≫ toSpec R ι)
  let g := coprod.desc d (s ≫ j) ≫ f
  let L := pullbackLineBundle g (twistingLineBundle R ι 1)
  obtain ⟨V₀, hx₀, ⟨e⟩⟩ := exists_base_open_unitIso_of_isProper_finite_fiber b x hfinite L
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset hx₀
  let : IsAffine V.toScheme := hV
  have hW : IsAffineOpen (boundaryBaseSourceOpen q ⊤ V) :=
    boundaryBaseSourceOpen_affine q ⊤ V (isAffineOpen_top _) hV
  let : IsAffine (boundaryBaseSourceOpen q ⊤ V).toScheme := hW
  let h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ (⊤ : X.Opens) := fun _ _ => trivial
  let E := (pullback.fst q (z ≫ q)) ⁻¹ᵁ (⊤ : X.Opens)
  let eTop : (idealModule (boundaryGraphTarget q z)).restrict E.ι ≅
      SheafOfModules.unit E.toScheme.ringCatSheaf :=
    (Modules.restrictFunctor E.ι).mapIso e₀.symm ≪≫ restrictUnitIso E.ι
  have := boundaryBaseSourceProjection_smooth q ⊤ V
  have : IsSeparated (boundaryBaseSourceProjection q ⊤ V) := by
    dsimp [boundaryBaseSourceProjection]
    infer_instance
  let eGraph := boundaryGraphFrame_baseIso _ _ V.toScheme.isoSpec
    (boundaryBaseCanonicalFrame q z ⊤ V h eTop)
  let W := b ⁻¹ᵁ V
  let eW := restrictUnitIsoOfLE L.val
    (show W ≤ b ⁻¹ᵁ V₀ from fun _ ht => hVV ht) e
  let e₁ : (Modules.pullback (W.ι ≫ g)).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι g).symm.app (twistingSheaf R ι 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback g).obj (twistingSheaf R ι 1)) ≪≫ eW
  let en := CoherentGraph.positiveTwistUnitIso R ι (W.ι ≫ g) e₁
  let eFull n := boundaryBaseWholeTwistFrame R ι f (coprod.desc d (s ≫ j)) V n (en n)
  exact ⟨V, hV, hxV, hW, lifting_on_base_open_with_frames k R ι m eι t q p a f j hj
    z s hs H ha d hd v hc φ hφ ⊤ V h eGraph eFull P hP⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
