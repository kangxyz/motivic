/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionChartSupport
public import Motivic.Cohomology.A1.PresheafBoundaryOpenZero
public import Motivic.Cohomology.A1.PointedCylinderLocalEffacement
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinarySupportNaturality
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedPresheafFiber
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-! # Positive supported cohomology on the original marked cylinder diagram

The closed immersion stays fixed while its actual test objects vary. Its
original unit and ordinary edge give the support comparison. Literal closed
BASE change is initial on the full field-valued marks; the whole homotopy
cylinder is introduced only after that base. The only cohomological HI input
is the explicitly displayed positive degree for the contraction coefficient.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite

local instance chartSupportHasExt (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  {E U : SmoothSite (Spec (.of k))}
  (b : E ⟶ SmoothSite.a1Cylinder (.of k) X) [Etale b.left]
  (F : SheafWithTransfers.{u + 1} k) (j : U ⟶ E)
  (q : U ⟶ SmoothSite.torusCylinder (.of k) X)
  (hj : IsPullback q j (SmoothSite.contractionOpen (.of k) X) b)
  (d : X ⟶ E) (hd : IsPullback d (𝟙 X) b (SmoothSite.a1Section (.of k) X 0))
  (hF : F.obj.IsA1Invariant)
  (hE : Epi (contractionToBoundary (SmoothSite.a1Cylinder (.of k) X) F hF))

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "H" => Functor.obj (SheafWithTransfers.toSheaf k)
  (SheafWithTransfers.contraction F hF)
local notation "X₁" => SmoothSite.a1Cylinder (CommRingCat.of k) X
local notation "E₁" => SmoothSite.a1Cylinder (CommRingCat.of k) E
local notation "πX" => SmoothSite.a1Projection (CommRingCat.of k) X
local notation "πE" => SmoothSite.a1Projection (CommRingCat.of k) E
local notation "d₁" => SmoothSite.a1Map (CommRingCat.of k) d
local notation "j₁" => SmoothSite.a1Map (CommRingCat.of k) j
local notation "C₁" => boundaryAmbientCokernel G j₁

/-- The fixed product chart uses the original unit followed by the original
ordinary edge map. No geometric proof witnesses occur in this natural map. -/
def chartProductAmbientSupportComparison (n : ℕ) :
    SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology (E₁).left) C₁ n ⟶
      (baseChange (d₁).left).op ⋙
        SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology (X₁).left) (boundaryCokernel G j₁ d₁) n :=
  ordinarySupportComparison (d₁).left C₁ n

/-- Every component retains the actual unit and the original ordinary edge. -/
theorem chartProductAmbientSupportComparison_apply (n : ℕ) (V : FiniteEtaleSite (E₁).left)
    (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology (E₁).left) C₁ n V) :
    (chartProductAmbientSupportComparison X F j d n).app (op V) x =
      ordinaryEdgeMap (d₁).left V (boundaryCokernel G j₁ d₁) n
        (x.comp (Ext.mk₀ ((imageAdjunction (d₁).left).unit.app C₁))
          (add_zero n)) := rfl

include hj hd in
/-- The original fixed-product support map is invertible by actual support.
Keeping this geometric argument in a theorem prevents proof expansion in Iso data. -/
theorem chartProductAmbientSupportComparison_isIso (n : ℕ) :
    IsIso (chartProductAmbientSupportComparison X F j d n) := by
  have hclosed := (SmoothSite.forgetScheme (Spec (.of k))).map_isPullback
    (SmoothSite.contractionChartProduct_closed_isPullback (.of k) X b d hd)
  change IsPullback (d₁).left (𝟙 (X₁).left)
    (SmoothSite.contractionChartProduct (.of k) X b).left
    (SmoothSite.a1Section (.of k) X₁ 0).left at hclosed
  let : IsClosedImmersion (d₁).left :=
    MorphismProperty.of_isPullback hclosed.flip inferInstance
  have hopen := (SmoothSite.forgetScheme (Spec (.of k))).map_isPullback
    (SmoothSite.contractionChartPunctureProduct_isPullback (.of k) X b j q hj)
  change IsPullback (SmoothSite.contractionChartPunctureProduct (.of k) X q).left
    (j₁).left (SmoothSite.contractionOpen (.of k) X₁).left
    (SmoothSite.contractionChartProduct (.of k) X b).left at hopen
  let : IsOpenImmersion (j₁).left :=
    MorphismProperty.of_isPullback hopen inferInstance
  have hdz : d ≫ b = SmoothSite.a1Section (.of k) X 0 := by
    simpa only [Category.id_comp] using hd.w
  let p := SmoothSite.a1Map (.of k) (b ≫ SmoothSite.a1Projection (.of k) X)
  have hp : (d₁).left ≫ p.left = 𝟙 (X₁).left :=
    congrArg (fun f ↦ f.left)
      (SmoothSite.contractionChartProduct_retraction (.of k) X b d hdz)
  exact ordinarySupportComparison_isIso (d₁).left p.left hp (j₁).left
    (SmoothSite.contractionChartProduct_complement (.of k) X b d hd j q hj)
    C₁ (inverseImage_open_boundaryAmbientCokernel_isZero G j₁) n

/-- The support isomorphism has the original natural map as its literal hom. -/
def chartProductAmbientSupportCohomologyIso (n : ℕ) :
    SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology (E₁).left) C₁ n ≅
      (baseChange (d₁).left).op ⋙
        SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology (X₁).left) (boundaryCokernel G j₁ d₁) n := by
  letI := chartProductAmbientSupportComparison_isIso X b F j q hj d hd n
  exact asIso (chartProductAmbientSupportComparison X F j d n)

variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The existing projection point-fiber theorem supplies the original ordinary
closed-cylinder cohomology germ, with no chart or support hypothesis. -/
private theorem contractionCylinderPoint_isZero_succ
    (Φ : (nisnevichTopology X.left).Point.{u + 1}) (n : ℕ)
    (hH : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
      (n + 1)).IsA1Invariant) :
    IsZero (Φ.presheafFiber.obj ((baseChange (πX).left).op ⋙
      SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology (X₁).left) ((restrict X₁ AddCommGrpCat).obj H) (n + 1))) := by
  have h := projectionPointFiber_isZero_of_cohomology_HI k X Φ
    (SheafWithTransfers.contraction F hF) n hH
  exact h.of_iso (derivedDirectImagePointOrdinaryColimitIso (πX).left Φ
    (injectiveResolution ((restrict X₁ AddCommGrpCat).obj H)) (n + 1)).symm

include hd in
/-- Accepted initiality extends the closed-cylinder germ along the literal
marked BASE change. The only retraction here is the fixed chart retraction. -/
private theorem chartClosedBasePoint_isZero_succ
    (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
    (hH : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
      (n + 1)).IsA1Invariant) :
    IsZero ((relativeFieldPoint (c ≫ d.left) K (𝟙 _)).presheafFiber.obj
      ((baseChange d.left).op ⋙ (baseChange (πX).left).op ⋙
        SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology (X₁).left) ((restrict X₁ AddCommGrpCat).obj H) (n + 1))) := by
  let P := (baseChange (πX).left).op ⋙
    SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology (X₁).left) ((restrict X₁ AddCommGrpCat).obj H) (n + 1)
  have hclosed := (SmoothSite.forgetScheme (Spec (.of k))).map_isPullback hd
  change IsPullback d.left (𝟙 X.left) b.left
    (SmoothSite.a1Section (.of k) X 0).left at hclosed
  let : IsClosedImmersion d.left :=
    MorphismProperty.of_isPullback hclosed.flip inferInstance
  have hdz : d ≫ b = SmoothSite.a1Section (.of k) X 0 := by
    simpa only [Category.id_comp] using hd.w
  let p := b ≫ SmoothSite.a1Projection (.of k) X
  have hp : d.left ≫ p.left = 𝟙 X.left :=
    congrArg (fun f ↦ f.left) (SmoothSite.contractionChart_retraction (.of k) X b d hdz)
  exact (contractionCylinderPoint_isZero_succ X F hF
    (relativeFieldPoint c K (𝟙 _)) n hH).of_iso
      (splitClosedPresheafPointFiberIso d.left p.left hp K c P)

include hd in
/-- The accepted literal iterated-pullback comparison changes test objects only.
It neither changes the fixed closed immersion nor assumes derived continuity. -/
private theorem chartProductContractionPoint_isZero_succ
    (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
    (hH : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
      (n + 1)).IsA1Invariant) :
    IsZero ((relativeFieldPoint (c ≫ d.left) K (𝟙 _)).presheafFiber.obj
      ((baseChange (πE).left).op ⋙ (baseChange (d₁).left).op ⋙
        SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology (X₁).left) ((restrict X₁ AddCommGrpCat).obj H) (n + 1))) := by
  let Q := SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (nisnevichTopology (X₁).left) ((restrict X₁ AddCommGrpCat).obj H) (n + 1)
  exact (chartClosedBasePoint_isZero_succ X b F d hd hF K c n hH).of_iso
    ((relativeFieldPoint (c ≫ d.left) K (𝟙 _)).presheafFiber.mapIso
      (Functor.isoWhiskerRight (NatIso.op (a1PunctureProjectionBaseChangeIso d).symm) Q))

include hj hd hE in
/-- The original canonical boundary map and actual chart excision identify
one fixed coefficient sheaf. No coordinate-independent purity assertion occurs. -/
private theorem chartProductBoundaryPoint_isZero_succ
    (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
    (hH : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
      (n + 1)).IsA1Invariant) :
    IsZero ((relativeFieldPoint (c ≫ d.left) K (𝟙 _)).presheafFiber.obj
      ((baseChange (πE).left).op ⋙ (baseChange (d₁).left).op ⋙
        SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology (X₁).left) (boundaryCokernel G j₁ d₁) (n + 1))) := by
  have hdz : d ≫ b = SmoothSite.a1Section (.of k) X 0 := by
    simpa only [Category.id_comp] using hd.w
  let eC := contractionChartProductBoundaryIso X b F j q hj d hdz hF hE
  exact (chartProductContractionPoint_isZero_succ X b F d hd hF K c n hH).of_iso
    ((relativeFieldPoint (c ≫ d.left) K (𝟙 _)).presheafFiber.mapIso
      (Functor.isoWhiskerLeft ((baseChange (πE).left).op ⋙ (baseChange (d₁).left).op)
        ((SheafCohomology.presheafFunctor.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology (X₁).left) (n + 1)).mapIso eC.symm)))

include hj hd hE in
/-- Lower-degree HI of the contraction kills the original left localization
term on full-K marked BASE neighborhoods, with whole cylinders throughout. -/
theorem chartProductSupportColimit_isZero_succ
    (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
    (hH : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
      (n + 1)).IsA1Invariant) :
    IsZero (colimit (ordinaryPointCohomologyDiagram (πE).left
      (relativeFieldPoint (c ≫ d.left) K (𝟙 _)) (F := C₁) (n + 1))) := by
  exact (chartProductBoundaryPoint_isZero_succ X b F j q hj d hd hF hE K c n hH).of_iso
    ((relativeFieldPoint (c ≫ d.left) K (𝟙 _)).presheafFiber.mapIso
      (Functor.isoWhiskerLeft (baseChange (πE).left).op
        (chartProductAmbientSupportCohomologyIso X b F j q hj d hd (n + 1))))

include hj hd hE in
/-- Vanishing has an actual original marked BASE witness; no refinement of
the homotopy cylinder itself or new retraction on the witness is introduced. -/
theorem exists_pointed_chartProductSupport_restriction_zero
    (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
    (hH : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
      (n + 1)).IsA1Invariant)
    (V : (relativeFieldPoint (c ≫ d.left) K (𝟙 _)).fiber.Elements)
    (s : SheafCohomology.H.{u + 1, u + 1, u, u + 1} (nisnevichTopology (E₁).left)
      C₁ (n + 1) ((baseChange (πE).left).obj V.obj)) :
    ∃ (W : (relativeFieldPoint (c ≫ d.left) K (𝟙 _)).fiber.Elements) (a : W ⟶ V),
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (nisnevichTopology (E₁).left) C₁ (n + 1)).map
          ((baseChange (πE).left).map a.hom).op s = 0 := by
  let D := ordinaryPointCohomologyDiagram (πE).left
    (relativeFieldPoint (c ≫ d.left) K (𝟙 _)) (F := C₁) (n + 1)
  have hzero := chartProductSupportColimit_isZero_succ X b F j q hj d hd hF hE K c n hH
  have hsub : Subsingleton ↑(colimit D) := AddCommGrpCat.subsingleton_of_isZero hzero
  have he : colimit.ι D (op V) s = colimit.ι D (op V) 0 :=
    @Subsingleton.elim ↑(colimit D) hsub _ _
  obtain ⟨W, a, ha⟩ := ((colimit.isColimit D).eq_iff' s 0).mp he
  refine ⟨W.unop, a.unop, ?_⟩
  change D.map a s = 0
  simpa only [map_zero] using ha

end Motivic.FiniteEtaleSite
