/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products
public import Motivic.AlgebraicGeometry.Correspondences.Support.ComponentDominance
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.CorrespondenceCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.ClosedSubscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Exterior support with an identity correspondence

The support of `V × id_T` is the literal scheme `V ×ₖ T`, mapped into
`(X ×ₖ T) ×ₖ (Y ×ₖ T)` with the same parameter in its two factors.
For a geometrically integral smooth parameter this support is integral and
defines an actual finite-correspondence generator. Its signed additive
extension does not yet assert compatibility with correspondence composition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

variable {k : Type u} [Field k]
  {X Y : SmoothSite (Spec (.of k))}
  (V : FiniteCorrespondenceGenerator X.hom Y.hom)
  (T : SmoothSite (Spec (.of k)))

/-- The Noetherian instance used in this module. -/
local instance identityBasicNoetherian : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

/-- The genuine exterior support before assigning any cycle. -/
abbrev exteriorIdentitySupport : Scheme.{u} :=
  pullback (V.projection ≫ X.hom) T.hom

/-- Projection of the exterior support onto its source product. -/
def exteriorIdentitySource : V.exteriorIdentitySupport T ⟶ (SmoothSite.product X T).left :=
  pullback.map _ _ _ _ V.projection (𝟙 T.left) (𝟙 (Spec (.of k))) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem exteriorIdentitySource_fst :
    V.exteriorIdentitySource T ≫ pullback.fst X.hom T.hom =
      pullback.fst (V.projection ≫ X.hom) T.hom ≫ V.projection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIdentitySource_snd :
    V.exteriorIdentitySource T ≫ pullback.snd X.hom T.hom =
      pullback.snd (V.projection ≫ X.hom) T.hom := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The exterior source projection is the actual base change of the original finite map. -/
theorem exteriorIdentitySource_isPullback :
    IsPullback (V.exteriorIdentitySource T)
      (pullback.fst (V.projection ≫ X.hom) T.hom)
      (pullback.fst X.hom T.hom) V.projection := by
  apply IsPullback.flip
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback X.hom T.hom) ?_
    (V.exteriorIdentitySource_fst T).symm
  simpa only [V.exteriorIdentitySource_snd T] using
    (IsPullback.of_hasPullback (V.projection ≫ X.hom) T.hom)

instance exteriorIdentitySource_isFinite : IsFinite (V.exteriorIdentitySource T) :=
  MorphismProperty.of_isPullback (V.exteriorIdentitySource_isPullback T).flip inferInstance

/-- The target map uses the identical parameter point. -/
def exteriorIdentityTarget : V.exteriorIdentitySupport T ⟶ (SmoothSite.product Y T).left :=
  pullback.lift
    (pullback.fst (V.projection ≫ X.hom) T.hom ≫ V.targetProjection)
    (pullback.snd (V.projection ≫ X.hom) T.hom)
    (by rw [Category.assoc, ← V.projection_base, pullback.condition])

@[reassoc (attr := simp)]
theorem exteriorIdentityTarget_fst :
    V.exteriorIdentityTarget T ≫ pullback.fst Y.hom T.hom =
      pullback.fst (V.projection ≫ X.hom) T.hom ≫ V.targetProjection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIdentityTarget_snd :
    V.exteriorIdentityTarget T ≫ pullback.snd Y.hom T.hom =
      pullback.snd (V.projection ≫ X.hom) T.hom :=
  pullback.lift_snd _ _ _

/-- The literal diagonal-parameter support map into the correspondence ambient product. -/
def exteriorIdentityInclusion : V.exteriorIdentitySupport T ⟶
    pullback (SmoothSite.product X T).hom (SmoothSite.product Y T).hom :=
  pullback.lift (V.exteriorIdentitySource T) (V.exteriorIdentityTarget T) (by
    simp only [SmoothSite.product_hom, ← Category.assoc,
      exteriorIdentitySource_fst, exteriorIdentityTarget_fst]
    simpa only [Category.assoc] using
      congrArg (pullback.fst (V.projection ≫ X.hom) T.hom ≫ ·) V.projection_base)

@[reassoc]
theorem exteriorIdentityInclusion_fst :
    V.exteriorIdentityInclusion T ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =
        V.exteriorIdentitySource T := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIdentityInclusion_fst_simp :
    V.exteriorIdentityInclusion T ≫
      pullback.fst (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Y.hom T.hom ≫ Y.hom) =
        V.exteriorIdentitySource T :=
  exteriorIdentityInclusion_fst V T

@[reassoc]
theorem exteriorIdentityInclusion_snd :
    V.exteriorIdentityInclusion T ≫
      pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =
        V.exteriorIdentityTarget T := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem exteriorIdentityInclusion_snd_simp :
    V.exteriorIdentityInclusion T ≫
      pullback.snd (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Y.hom T.hom ≫ Y.hom) =
        V.exteriorIdentityTarget T :=
  exteriorIdentityInclusion_snd V T

instance exteriorIdentityInclusion_isFinite : IsFinite (V.exteriorIdentityInclusion T) := by
  have : IsFinite (V.exteriorIdentityInclusion T ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) := by
    simpa only [exteriorIdentityInclusion_fst] using
      (inferInstance : IsFinite (V.exteriorIdentitySource T))
  exact IsFinite.of_comp _ (pullback.fst _ _)

instance exteriorIdentityInclusion_mono : Mono (V.exteriorIdentityInclusion T) where
  right_cancellation {W} f g h := by
    have hsource := congrArg
      (fun a => a ≫ pullback.fst (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom) h
    have htarget := congrArg
      (fun a => a ≫ pullback.snd (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom) h
    simp only [Category.assoc, exteriorIdentityInclusion_fst] at hsource
    simp only [Category.assoc, exteriorIdentityInclusion_snd] at htarget
    apply pullback.hom_ext
    · apply (cancel_mono V.inclusion).mp
      apply pullback.hom_ext
      · simpa only [Category.assoc, exteriorIdentitySource_fst, projection,
          correspondenceProjection] using
          congrArg (fun a => a ≫ pullback.fst X.hom T.hom) hsource
      · simpa only [Category.assoc, exteriorIdentityTarget_fst] using
          congrArg (fun a => a ≫ pullback.fst Y.hom T.hom) htarget
    · simpa only [Category.assoc, exteriorIdentitySource_snd] using
        congrArg (fun a => a ≫ pullback.snd X.hom T.hom) hsource

instance exteriorIdentityInclusion_isClosedImmersion :
    IsClosedImmersion (V.exteriorIdentityInclusion T) :=
  (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

/-- Normality is used only on the original smooth source, not on the support. -/
theorem exteriorIdentitySource_generalizing : GeneralizingMap (V.exteriorIdentitySource T) :=
  generalizingMap_of_isPullback_component _ _ _ _ (V.exteriorIdentitySource_isPullback T)
    V.range_projection_mem (fun x =>
      ⟨SmoothSite.isDomain_stalk k X x, SmoothSite.isIntegrallyClosed_stalk k X x⟩)

variable [GeometricallyIntegral T.hom]

instance exteriorIdentitySupport_isIntegral : IsIntegral (V.exteriorIdentitySupport T) :=
  inferInstanceAs (IsIntegral (pullback (V.projection ≫ X.hom) T.hom))

/-- The exterior support remains finite and dominant onto an actual source component. -/
theorem exteriorIdentitySource_range_mem :
    Set.range (V.exteriorIdentitySource T) ∈
      irreducibleComponents (SmoothSite.product X T).left := by
  have hg := mem_genericPoints_of_generalizing (V.exteriorIdentitySource T)
    (V.exteriorIdentitySource_generalizing T) (genericPoint (V.exteriorIdentitySupport T))
    (by simp [genericPoints_eq_singleton])
  change closure ({V.exteriorIdentitySource T (genericPoint (V.exteriorIdentitySupport T))} :
    Set (SmoothSite.product X T).left) ∈ irreducibleComponents _ at hg
  rw [← Set.image_singleton,
    (V.exteriorIdentitySource T).isClosedMap.closure_image_eq_of_continuous
      (V.exteriorIdentitySource T).continuous,
    (genericPoint_spec (V.exteriorIdentitySupport T)).def, Set.image_univ] at hg
  exact hg

/-- The original support maps isomorphically onto its actual closed image. -/
instance exteriorIdentityInclusion_toImage_isIso :
    IsIso (V.exteriorIdentityInclusion T).toImage :=
  IsClosedImmersion.instIsIsoSchemeToImage _

omit [GeometricallyIntegral T.hom] in
@[reassoc]
theorem exteriorIdentityInclusion_toImage_source :
    (V.exteriorIdentityInclusion T).toImage ≫
      correspondenceProjection (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (V.exteriorIdentityInclusion T).ker = V.exteriorIdentitySource T := by
  simp only [correspondenceProjection, ← Category.assoc, Scheme.Hom.toImage_imageι,
    exteriorIdentityInclusion_fst]

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem exteriorIdentityInclusion_toImage_source_simp :
    @Scheme.Hom.toImage (V.exteriorIdentitySupport T)
      (pullback (pullback.fst X.hom T.hom ≫ X.hom)
        (pullback.fst Y.hom T.hom ≫ Y.hom)) (V.exteriorIdentityInclusion T) ≫
      correspondenceProjection (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Y.hom T.hom ≫ Y.hom)
        (V.exteriorIdentityInclusion T).ker = V.exteriorIdentitySource T :=
  exteriorIdentityInclusion_toImage_source V T

/-- The image ideal defines the genuine exterior finite-correspondence generator. -/
def exteriorIdentityGenerator :
    FiniteCorrespondenceGenerator (SmoothSite.product X T).hom (SmoothSite.product Y T).hom := by
  refine ⟨(V.exteriorIdentityInclusion T).ker, ?_, ?_, ?_⟩
  · exact isIntegral_finiteImage (V.exteriorIdentityInclusion T)
  · have h : IsFinite ((V.exteriorIdentityInclusion T).toImage ≫
        correspondenceProjection (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
          (V.exteriorIdentityInclusion T).ker) := by
      simpa only [exteriorIdentityInclusion_toImage_source] using
        (inferInstance : IsFinite (V.exteriorIdentitySource T))
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsFinite) (V.exteriorIdentityInclusion T).toImage _).mp h
  · rw [← (surjective_toImage (V.exteriorIdentityInclusion T)).range_comp]
    change Set.range ((V.exteriorIdentityInclusion T).toImage ≫
      correspondenceProjection (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (V.exteriorIdentityInclusion T).ker) ∈ _
    rw [exteriorIdentityInclusion_toImage_source]
    exact V.exteriorIdentitySource_range_mem T

@[simp] theorem exteriorIdentityGenerator_val :
    (V.exteriorIdentityGenerator T).val = (V.exteriorIdentityInclusion T).ker := rfl

instance exteriorIdentitySupport_isNoetherian : IsNoetherian (V.exteriorIdentitySupport T) :=
  isNoetherian_of_finiteType (V.exteriorIdentitySource T)

/-- Its literal unit cycle is the pushed whole fundamental cycle of the exterior support. -/
theorem toIntegralCycle_exteriorIdentityGenerator_cycle :
    FiniteCorrespondence.toIntegralCycle (V.exteriorIdentityGenerator T).cycle =
      IntegralCycle.finitePushforward (V.exteriorIdentityInclusion T)
        (fundamentalCycle (V.exteriorIdentitySupport T)) := by
  let e := V.exteriorIdentityInclusion T
  have : IsNoetherian (pullback (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom) :=
    isNoetherian_of_finiteType (pullback.fst _ _)
  have : IsIntegral e.image := isIntegral_finiteImage e
  change FiniteCorrespondence.toIntegralCycle (V.exteriorIdentityGenerator T).cycle =
    IntegralCycle.finitePushforward e (fundamentalCycle (V.exteriorIdentitySupport T))
  have hpush : IntegralCycle.finitePushforward e =
      (IntegralCycle.finitePushforward e.imageι).comp
        (IntegralCycle.finitePushforward e.toImage) := by
    simpa only [Scheme.Hom.toImage_imageι] using
      (IntegralCycle.finitePushforward_comp e.toImage e.imageι)
  rw [hpush, AddMonoidHom.comp_apply, finitePushforward_fundamentalCycle]
  rw [cycle, FiniteCorrespondence.toIntegralCycle_single]
  change Finsupp.single (V.exteriorIdentityGenerator T).toIntegralClosedSubscheme 1 =
    closedFundamentalCycle e.ker
  rw [closedFundamentalCycle_of_isIntegral]
  rfl

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]
  {X Y : SmoothSite (Spec (.of k))}
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- Exterior product with the identity of a geometrically integral smooth parameter,
on all actual signed correspondence cycles. Composition compatibility is separate. -/
def exteriorIdentity : FiniteCorrespondence X.hom Y.hom →+
    FiniteCorrespondence (SmoothSite.product X T).hom (SmoothSite.product Y T).hom :=
  Finsupp.mapDomain.addMonoidHom (fun V => V.exteriorIdentityGenerator T)

theorem exteriorIdentity_single
    (V : FiniteCorrespondenceGenerator X.hom Y.hom) (n : ℤ) :
    exteriorIdentity (X := X) (Y := Y) T (Finsupp.single V n) =
      Finsupp.single (V.exteriorIdentityGenerator T) n :=
  Finsupp.mapDomain_single

@[simp] theorem exteriorIdentity_single_simp
    (V : FiniteCorrespondenceGenerator X.hom Y.hom) (n : ℤ) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.fst X.hom T.hom ≫ X.hom)
          (pullback.fst Y.hom T.hom ≫ Y.hom))
      _ _ _ (exteriorIdentity (X := X) (Y := Y) T) (Finsupp.single V n) =
      Finsupp.single (V.exteriorIdentityGenerator T) n :=
  exteriorIdentity_single T V n

theorem exteriorIdentity_cycle
    (V : FiniteCorrespondenceGenerator X.hom Y.hom) :
    exteriorIdentity (X := X) (Y := Y) T V.cycle = (V.exteriorIdentityGenerator T).cycle :=
  exteriorIdentity_single (X := X) (Y := Y) T V 1

@[simp] theorem exteriorIdentity_cycle_simp
    (V : FiniteCorrespondenceGenerator X.hom Y.hom) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.fst X.hom T.hom ≫ X.hom)
          (pullback.fst Y.hom T.hom ≫ Y.hom))
      _ _ _ (exteriorIdentity (X := X) (Y := Y) T) V.cycle =
      (V.exteriorIdentityGenerator T).cycle :=
  exteriorIdentity_cycle T V

end Motivic.FiniteCorrespondence
