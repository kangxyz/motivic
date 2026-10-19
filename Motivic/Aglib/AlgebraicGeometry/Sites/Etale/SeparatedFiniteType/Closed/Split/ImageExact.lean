/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Closed.Split.SupportUnit

/-! # Exact direct image for an actual split closed immersion

Closed-side fibers use the proved marked cofinality comparison. Open-side
fibers use empty geometric base change. Epimorphisms are detected through the
original cokernel and every marked residue point of every test object.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {Z U Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsNoetherian Y]
  (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
  (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
  (hcomp : Set.range i = (Set.range j)ᶜ)

include p hip j hcomp

/-- The genuine split-closed direct image preserves epimorphisms. No
sectionwise surjectivity or general closed-recollement theorem is assumed. -/
theorem splitClosedDirectImage_preservesEpimorphisms :
    (directImage i).PreservesEpimorphisms := by
  constructor
  intro F G α hα
  apply epi_of_isZero_cokernel
  apply isZero_of_all_marked_residue_fibers
  intro V z
  let K := V.left.residueField z
  let b : Spec K ⟶ Y := V.left.fromSpecResidueField z ≫ V.hom
  let q : Spec K := IsLocalRing.closedPoint K
  by_cases hb : b q ∈ Set.range i
  · obtain ⟨c, hc⟩ := Scheme.exists_field_lift_of_mem_range i b hb
    let Φ := relativeFieldPoint c K (𝟙 _)
    let : InitiallySmall.{u + 1} (baseChange i ⋙ (Φ).fiber).Elements :=
      initiallySmall_of_essentiallySmall _
    let Ξ := (Φ).comap (baseChange i)
      (CoverPreserving.of_isContinuous (baseChange i)
        (nisnevichTopology Y) (nisnevichTopology Z))
    have hepi : Epi ((Ξ).sheafFiber.map ((directImage i).map α)) := by
      apply (epi_comp_iff_of_isIso _ (splitClosedComapDirectImageIso i p hip K c G).hom).mp
      erw [splitClosedComapDirectImageIso_naturality]
      infer_instance
    have hzero : IsZero ((Ξ).sheafFiber.obj (cokernel ((directImage i).map α))) :=
      (isZero_cokernel_of_epi ((Ξ).sheafFiber.map ((directImage i).map α))).of_iso
        (PreservesCokernel.iso (Ξ).sheafFiber ((directImage i).map α))
    change IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj
      (cokernel ((directImage i).map α)))
    rw [← hc]
    exact splitClosed_fieldPoint_isZero_of_comap i K c _ hzero
  · have hpoint : Epi ((markedResiduePoint V z).sheafFiber.map ((directImage i).map α)) :=
      (fieldPoint_directImage_isZero_of_not_mem_range i j G hcomp K b q hb).epi _
    exact (isZero_cokernel_of_epi
      ((markedResiduePoint V z).sheafFiber.map ((directImage i).map α))).of_iso
        (PreservesCokernel.iso (markedResiduePoint V z).sheafFiber ((directImage i).map α))

/-- Exactness concerns the original direct-image functor on ordinary sheaves. -/
theorem splitClosedDirectImage_preservesHomology : (directImage i).PreservesHomology := by
  let := splitClosedDirectImage_preservesEpimorphisms i p hip j hcomp
  exact Functor.preservesHomology_of_preservesEpis_and_kernels (directImage i)

/-- The original split-closed direct image preserves finite colimits as well as
its already available finite-limit preservation. -/
theorem splitClosedDirectImage_preservesFiniteColimits :
    PreservesFiniteColimits (directImage i) := by
  let := splitClosedDirectImage_preservesHomology i p hip j hcomp
  exact Functor.preservesFiniteColimits_of_preservesHomology (directImage i)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
