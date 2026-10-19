/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.Restriction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.OriginalRetainedSourceRestriction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.OriginalOverlapSectionChoice
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeComplement
/-! # E2 and E4 for the unchanged native source section choice

The retained target is the original overlap restricted at the already selected
coefficient open. Its map back to the original source is constructed, not an
extra factorization premise. No target sections are changed or needed here.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom RelativeProjectiveLine
universe u w
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

local instance {X Y : Scheme.{u}} (g : X ⟶ Y) [SmoothOfRelativeDimension 1 g] :
    Smooth g := SmoothOfRelativeDimension.smooth 1 g
local instance (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R
local instance {S X Y C : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
    (π : C ⟶ S) (j : Y ⟶ C) [IsOpenImmersion j] (hq : j ≫ π = p ≫ q)
    (U : X.Opens) (V : S.Opens) :
    IsOpenImmersion (boundaryBaseCoverInclusion q p π j hq U V) :=
  boundaryBaseCoverInclusion_open q p π j hq U V

variable (k : Type u) [Field k] (R : Type u) [CommRing R]
  {Y A Z C D : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p]
  (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j]
  (hj : j ≫ (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) =
    p ≫ boundaryLineProjection R)
  (z : Z ⟶ Spec (.of (Polynomial R))) [IsFinite (z ≫ boundaryLineProjection R)]
  (s : Z ⟶ Y) (hs : s ≫ p = z)
  (H : IsPullback s (𝟙 Z) p z) (d : D ⟶ C)
  (hc : ∀ x : C, x ∈ Set.range (pullback.fst p a ≫ j) ∨
    x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
  (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]

include hj in
omit [IsAffine Y] [IsAffine A] [IsFinite f] [IsOpenImmersion j] in
theorem nativeOriginalRetained_smooth : SmoothOfRelativeDimension 1 ((pullback.fst p a ≫ j) ≫ (f ≫
    ProjectiveSpace.toSpec R (ULift (Fin 2)))) := by
  rw [Category.assoc, hj, ← Category.assoc]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- The original E2/E4 restriction actions of precisely the supplied native c. -/
theorem BoundarySectionData.native_original_restriction_actions
    (hqn : (boundaryBaseCoverInclusion (boundaryLineProjection R) p (f ≫ ProjectiveSpace.toSpec R
        (ULift (Fin 2))) j hj ⊤ V) ≫ (boundaryBaseProjectiveMap R (ULift (Fin 2)) f V ≫
  ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift (Fin 2))) = (sourceNativeCoverMap R V p) ≫
      (boundaryLineProjection Γ(V.toScheme, ⊤)))
    (han : Disjoint (Set.range (sourceNativeCoverMap R V a)) (Set.range (targetNativeMarked R V
        z)))
    (hdn : Disjoint (Set.range (boundaryBaseCoverInclusion (boundaryLineProjection R) p (f ≫
        ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj ⊤ V)) (Set.range (boundaryBaseWholeMap (f ≫
        ProjectiveSpace.toSpec R (ULift (Fin 2))) d V)))
    (c : BoundarySectionData (boundaryLineProjection Γ(V.toScheme, ⊤)) (boundaryBaseProjectiveMap
        R (ULift (Fin 2)) f V ≫
  ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift (Fin 2))) (boundaryBaseCoverInclusion
      (boundaryLineProjection R) p (f ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj ⊤ V)
      (sourceNativeCoverMap R V p) hqn (sourceNativeCoverMap R V a) (targetNativeMarked R V z)
      (boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ V (fun _ _ => trivial))
      (sourceNativeCoverLift_map R V z p s hs)
      (sourceNativeCoverLift_isPullback R V z p s hs H)
      (targetNativeCanonicalFrame R V z) han (boundaryBaseWholeMap (f ≫ ProjectiveSpace.toSpec R
          (ULift (Fin 2))) d V) hdn)
    (Q : SmoothSite (Spec (.of k)))
    (r : lambdaSourceSite k (boundaryBaseFieldMap V t) (boundaryBaseProjectiveMap R (ULift (Fin
        2)) f V ≫
  ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift (Fin 2))) (boundaryBaseCoverInclusion
      (boundaryLineProjection R) p (f ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj ⊤ V) ⟶ Q)
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant) :
    let : SmoothOfRelativeDimension 1
        ((pullback.fst p a ≫ j) ≫ (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) :=
      nativeOriginalRetained_smooth R p a f j hj
    let h₂ : (pullback.fst (boundaryBaseCoverMap (boundaryLineProjection R) p ⊤ V)
  (boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V)) ≫ (sourceNativeCoverMap R V p) =
      (pullback.snd (boundaryBaseCoverMap (boundaryLineProjection R) p ⊤ V)
  (boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V)) ≫ (sourceNativeCoverMap R V a) := by
      simpa only [sourceNativeCoverMap, ← Category.assoc] using
        congrArg (fun g => g ≫ (sourceNativeParameterIso R V).hom)
          (pullback.condition (f := boundaryBaseCoverMap (boundaryLineProjection R) p ⊤ V)
            (g := boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V))
    let hc₂ := boundaryBaseSourceBoundary_cover (boundaryLineProjection R) p z s hs (f ≫
        ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj d ⊤ V
      (fun _ _ => trivial) (pullback.fst p a ≫ j) hc
    let φ₂ := boundaryBaseOverlapTarget (boundaryLineProjection R) p a ⊤ V (f ≫
        ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj
      (pullback.fst p a ≫ j) (𝟙 _) (Category.id_comp _)
    let hφ₂ := boundaryBaseOverlapTarget_inclusion (boundaryLineProjection R) p a ⊤ V (f ≫
        ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj
      (pullback.fst p a ≫ j) (𝟙 _) (Category.id_comp _)
    let u₂ := originalRetainedSourceRestriction (boundaryLineProjection R) p a (f ≫
        ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj V
    let uSite : relativeTargetSite k (boundaryBaseFieldMap V t) (boundaryBaseProjectiveMap R
        (ULift (Fin 2)) f V ≫
  ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift (Fin 2))) (boundaryBaseRetainedTarget (f ≫
      ProjectiveSpace.toSpec R (ULift (Fin 2))) V (pullback.fst p a ≫ j)) ⟶
        lambdaSourceSite k (boundaryBaseFieldMap V t) (boundaryBaseProjectiveMap R (ULift (Fin 2))
            f V ≫
  ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift (Fin 2))) (boundaryBaseCoverInclusion
      (boundaryLineProjection R) p (f ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj ⊤ V) :=
      SmoothSite.homMk u₂ (by
        change u₂ ≫ (((boundaryBaseCoverInclusion (boundaryLineProjection R) p (f ≫
            ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) j hj ⊤ V) ≫ (boundaryBaseProjectiveMap R
            (ULift.{u} (Fin 2)) f V ≫ ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin
            2)))) ≫ (boundaryBaseFieldMap V t)) = ((boundaryBaseRetainedTarget (f ≫
            ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) V (pullback.fst p a ≫ j)) ≫
            (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f V ≫ ProjectiveSpace.toSpec
            Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)))) ≫ (boundaryBaseFieldMap V t)
        simpa only [Category.assoc] using congrArg
          (fun g => g ≫ (boundaryBaseProjectiveMap R (ULift (Fin 2)) f V ≫
  ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift (Fin 2))) ≫ boundaryBaseFieldMap V t)
          (originalRetainedSourceRestriction_inclusion (boundaryLineProjection R) p a (f ≫
              ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj V))
    let data := c.toData k (boundaryBaseFieldMap V t) (boundaryLineProjection Γ(V.toScheme, ⊤))
        (boundaryBaseProjectiveMap R (ULift (Fin 2)) f V ≫
  ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift (Fin 2))) (boundaryBaseCoverInclusion
      (boundaryLineProjection R) p (f ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj ⊤ V)
      (sourceNativeCoverMap R V p) hqn
      (sourceNativeCoverMap R V a) (pullback.fst (boundaryBaseCoverMap (boundaryLineProjection R)
          p ⊤ V)
  (boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V)) (pullback.snd (boundaryBaseCoverMap
      (boundaryLineProjection R) p ⊤ V)
  (boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V)) h₂ (targetNativeMarked R V z)
      (boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ V (fun _ _ => trivial))
      (sourceNativeCoverLift_map R V z p s hs)
      (sourceNativeCoverLift_isPullback R V z p s hs H)
      (targetNativeCanonicalFrame R V z) han (boundaryBaseWholeMap (f ≫ ProjectiveSpace.toSpec R
          (ULift (Fin 2))) d V) hdn (boundaryBaseRetainedTarget (f ≫ ProjectiveSpace.toSpec R
          (ULift (Fin 2))) V (pullback.fst p a ≫ j)) hc₂ φ₂ hφ₂
    PresheafWithTransfers.transfer P (data.lam ≫ (Cor.graphFunctor k).map (uSite ≫ r)) =
        PresheafWithTransfers.transfer P ((Cor.graphFunctor k).map r) ∧
      PresheafWithTransfers.transfer P
        (data.psi ≫ (Cor.graphFunctor k).map (uSite ≫ r)) = 0 := by
  let := nativeOriginalRetained_smooth R p a f j hj
  dsimp only
  exact c.transfer_postcompose_original_restriction k (boundaryBaseFieldMap V t)
    (boundaryLineProjection Γ(V.toScheme, ⊤)) (boundaryBaseProjectiveMap R (ULift (Fin 2)) f V ≫
  ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift (Fin 2))) (boundaryBaseCoverInclusion
      (boundaryLineProjection R) p (f ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj ⊤ V)
      (sourceNativeCoverMap R V p) hqn (sourceNativeCoverMap R V a) (pullback.fst
      (boundaryBaseCoverMap (boundaryLineProjection R) p ⊤ V)
  (boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V)) (pullback.snd (boundaryBaseCoverMap
      (boundaryLineProjection R) p ⊤ V)
  (boundaryBaseCoverMap (boundaryLineProjection R) a ⊤ V)) _ (targetNativeMarked R V z)
      (boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ V (fun _ _ => trivial)) _ _ _
      han (boundaryBaseWholeMap (f ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) d V) hdn
    (boundaryBaseRetainedTarget (f ≫ ProjectiveSpace.toSpec R (ULift (Fin 2))) V (pullback.fst p a
        ≫ j)) _ _ _ (originalRetainedSourceRestriction (boundaryLineProjection R) p a (f ≫
        ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj V)
    (originalRetainedSourceRestriction_inclusion (boundaryLineProjection R) p a (f ≫
        ProjectiveSpace.toSpec R (ULift (Fin 2))) j hj V) Q r P hP

end AlgebraicGeometry.Scheme.RelativeCurvePencil
