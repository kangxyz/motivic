/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Closed.Split.Comap
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.DirectImageOpenSupport
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Marked.PointDetection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageExact

/-! # The actual support unit on a split closed chart

The original unit is checked on native comapped-point representatives, using
its genuine adjunction equation. Only zero kernel and cokernel objects are
transported to the original ambient field points. No object isomorphism is
silently substituted for an equation about the unit map.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsNoetherian Y]
  (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
  (K : Type u) [Field K] (c : Spec (.of K) ⟶ Z)

local notation "Φ" => relativeFieldPoint c K (𝟙 _)
local instance : InitiallySmall.{u + 1} (baseChange i ⋙ (Φ).fiber).Elements :=
  initiallySmall_of_essentiallySmall _
local notation "hcover" => CoverPreserving.of_isContinuous (baseChange i)
  (nisnevichTopology Y) (nisnevichTopology Z)
local notation "Ξ" => GrothendieckTopology.Point.comap
  (relativeFieldPoint c K (𝟙 _)) (baseChange i)
  (CoverPreserving.of_isContinuous (baseChange i) (nisnevichTopology Y) (nisnevichTopology Z))

/-- Direct-image comparison on precisely the native comap index appearing in
the adjunction-unit representative equation. -/
def splitClosedComapDirectImageIso
    (F : Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1}) :
    (Ξ).sheafFiber.obj ((directImage i).obj F) ≅ (Φ).sheafFiber.obj F := by
  letI := splitClosedComapProjection_initial i K c p hip
  exact Functor.Final.colimitIso (splitClosedComapProjection i K c).op
    ((Functor.Elements.π (Φ).fiber).op ⋙ F.obj)

/-- The comap comparison sends each original section to its original source
point-fiber injection on literal closed base change. -/
@[reassoc]
theorem splitClosedComapDirectImageIso_ι
    (F : Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1})
    (V : EtaleSeparatedFiniteType Y) (x : (Ξ).fiber.obj V) :
    (Ξ).toPresheafFiber V x ((directImage i).obj F).obj ≫
        (splitClosedComapDirectImageIso i p hip K c F).hom =
      (Φ).toPresheafFiber ((baseChange i).obj V) x F.obj := by
  let := splitClosedComapProjection_initial i K c p hip
  exact Functor.Final.ι_colimitIso_hom (splitClosedComapProjection i K c).op
    ((Functor.Elements.π (Φ).fiber).op ⋙ F.obj) (op ((Ξ).fiber.elementsMk V x))

/-- Coefficient naturality follows on the original point-fiber injections. -/
@[reassoc]
theorem splitClosedComapDirectImageIso_naturality
    {F G : Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1}} (α : F ⟶ G) :
    (Ξ).sheafFiber.map ((directImage i).map α) ≫
        (splitClosedComapDirectImageIso i p hip K c G).hom =
      (splitClosedComapDirectImageIso i p hip K c F).hom ≫ (Φ).sheafFiber.map α := by
  apply (Ξ).presheafFiber_hom_ext
  intro V x
  dsimp only [GrothendieckTopology.Point.sheafFiber, Functor.comp_map, Functor.comp_obj]
  erw [(Ξ).toPresheafFiber_naturality_assoc, splitClosedComapDirectImageIso_ι,
    splitClosedComapDirectImageIso_ι_assoc, (Φ).toPresheafFiber_naturality]
  rfl

/-- The actual support unit followed by the actual closed-fiber comparison is
exactly the native inverse-image/comap isomorphism. -/
@[reassoc]
theorem splitClosedComap_unit_compare
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) :
    (Ξ).sheafFiber.map ((imageAdjunction i).unit.app G) ≫
        (splitClosedComapDirectImageIso i p hip K c ((inverseImage i).obj G)).hom =
      ((Φ).sheafFiberComapIso (baseChange i) hcover AddCommGrpCat.{u + 1}).hom.app G := by
  apply (Ξ).presheafFiber_hom_ext
  intro V x
  dsimp only [GrothendieckTopology.Point.sheafFiber, Functor.comp_map, Functor.comp_obj]
  erw [(Ξ).toPresheafFiber_naturality_assoc, splitClosedComapDirectImageIso_ι]
  exact (point_comapIso_unit_ι i Φ G V x).symm

include p hip in
/-- The original unit is invertible on every native closed-side comapped point. -/
theorem splitClosedComap_unit_isIso
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) :
    IsIso ((Ξ).sheafFiber.map ((imageAdjunction i).unit.app G)) := by
  have : IsIso ((Ξ).sheafFiber.map ((imageAdjunction i).unit.app G) ≫
      (splitClosedComapDirectImageIso i p hip K c ((inverseImage i).obj G)).hom) := by
    rw [splitClosedComap_unit_compare]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (splitClosedComapDirectImageIso i p hip K c ((inverseImage i).obj G)).hom

omit [IsClosedImmersion i] [AlgebraicGeometry.IsNoetherian Y] in
/-- Transfer a zero object from the native comap fiber to the unchanged actual
ambient field-valued point, using only the genuine inverse-image comparisons. -/
theorem splitClosed_fieldPoint_isZero_of_comap
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})
    (hG : IsZero ((Ξ).sheafFiber.obj G)) :
    IsZero ((relativeFieldPoint (c ≫ i) K (𝟙 _)).sheafFiber.obj G) :=
  (hG.of_iso
    (((Φ).sheafFiberComapIso (baseChange i) hcover AddCommGrpCat.{u + 1}).app G).symm).of_iso
      (fieldPointInverseImageCompositionIso i K c G)

include p hip in
/-- A sheaf zero on the actual open complement is carried isomorphically by
its original adjunction unit to the direct image of its genuine closed inverse
image. This is restricted to a split closed chart with Noetherian ambient. -/
theorem splitClosed_support_unit_isIso
    {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range i = (Set.range j)ᶜ)
    (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})
    (hG : IsZero ((inverseImage j).obj G)) :
    IsIso ((imageAdjunction i).unit.app G) := by
  let η := (imageAdjunction i).unit.app G
  have htest : ∀ (V : EtaleSeparatedFiniteType Y) (z : V.left),
      IsZero ((markedResiduePoint V z).sheafFiber.obj (kernel η)) ∧
      IsZero ((markedResiduePoint V z).sheafFiber.obj (cokernel η)) := by
    intro V z
    let K := V.left.residueField z
    let b : Spec K ⟶ Y := V.left.fromSpecResidueField z ≫ V.hom
    let q : Spec K := IsLocalRing.closedPoint K
    by_cases hb : b q ∈ Set.range i
    · obtain ⟨c, hc⟩ := Scheme.exists_field_lift_of_mem_range i b hb
      let P := relativeFieldPoint c K (𝟙 _)
      let : InitiallySmall.{u + 1} (baseChange i ⋙ (P).fiber).Elements :=
        initiallySmall_of_essentiallySmall _
      let Q := (P).comap (baseChange i)
        (CoverPreserving.of_isContinuous (baseChange i) (nisnevichTopology Y) (nisnevichTopology Z))
      let := splitClosedComap_unit_isIso i p hip K c G
      have hk : IsZero ((Q).sheafFiber.obj (kernel η)) :=
        (isZero_kernel_of_mono ((Q).sheafFiber.map η)).of_iso
          (PreservesKernel.iso (Q).sheafFiber η)
      have hq : IsZero ((Q).sheafFiber.obj (cokernel η)) :=
        (isZero_cokernel_of_epi ((Q).sheafFiber.map η)).of_iso
          (PreservesCokernel.iso (Q).sheafFiber η)
      constructor
      · change IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj (kernel η))
        rw [← hc]
        exact splitClosed_fieldPoint_isZero_of_comap i K c (kernel η) hk
      · change IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj (cokernel η))
        rw [← hc]
        exact splitClosed_fieldPoint_isZero_of_comap i K c (cokernel η) hq
    · have hb' : b q ∈ Set.range j := by
        simpa only [hcomp, Set.mem_compl_iff, not_not] using hb
      have hs := fieldPoint_isZero_of_inverseImage_of_mem_range j K G b q hb' hG
      have ht := fieldPoint_directImage_isZero_of_not_mem_range i j
        ((inverseImage i).obj G) hcomp K b q hb
      let : IsIso ((markedResiduePoint V z).sheafFiber.map η) := hs.isIso ht _
      exact ⟨(isZero_kernel_of_mono ((markedResiduePoint V z).sheafFiber.map η)).of_iso
          (PreservesKernel.iso (markedResiduePoint V z).sheafFiber η),
        (isZero_cokernel_of_epi ((markedResiduePoint V z).sheafFiber.map η)).of_iso
          (PreservesCokernel.iso (markedResiduePoint V z).sheafFiber η)⟩
  let : Mono η := mono_of_isZero_kernel η
    (isZero_of_all_marked_residue_fibers (kernel η) (fun V z => (htest V z).1))
  let : Epi η := epi_of_isZero_cokernel η
    (isZero_of_all_marked_residue_fibers (cokernel η) (fun V z => (htest V z).2))
  change IsIso η
  exact isIso_of_mono_of_epi η

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
