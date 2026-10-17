/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PrincipalRetainedBoundary
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.DisjointClosedImmersion

/-! # The literal complete retained boundary and original prescribed scheme on the same base open -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The original closed scheme remains a closed immersion into a separated compactification. -/
theorem prescribed_closed_in_compactification {X N Z S : Scheme.{u}}
    (i : X ⟶ N) [IsOpenImmersion i] (q : N ⟶ S) [IsSeparated q]
    (z : Z ⟶ X) [IsClosedImmersion z] [IsProper ((z ≫ i) ≫ q)] :
    IsClosedImmersion (z ≫ i) := by
  have : IsProper (z ≫ i) := IsProper.of_comp _ q
  exact IsClosedImmersion.of_isPreimmersion _ (z ≫ i).isClosedMap.isClosed_range

/-- The full complement and original prescribed scheme are disjoint on the one
base neighborhood supplied by the retained-presentation theorem. -/
theorem retained_prescribed_disjoint_on_base {N Z S : Scheme.{u}}
    (q : N ⟶ S) (V : N.Opens) (z : Z ⟶ N) (T : S.Opens)
    (hz : ∀ x : Z, (z ≫ q) x ∈ T → z x ∈ V) :
    Disjoint (Set.range (retainedBoundaryInclusion V ∣_ q ⁻¹ᵁ T))
      (Set.range (z ∣_ q ⁻¹ᵁ T)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have hnot := (range_retainedBoundaryInclusion V).le ⟨a.val, rfl⟩
  apply hnot
  have he : z b.val = retainedBoundaryInclusion V a.val := by
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hb
  rw [← he]
  exact hz b.val b.property

/-- The actual coproduct keeps every nilpotent of the prescribed scheme and of the
complete boundary; it is closed and finite over exactly the unchanged base restriction. -/
theorem retained_prescribed_boundary_on_base {N Z S : Scheme.{u}}
    (q : N ⟶ S) (V : N.Opens) (z : Z ⟶ N) [IsClosedImmersion z] (T : S.Opens)
    [IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ T)] [IsFinite ((z ≫ q) ∣_ T)]
    (hz : ∀ x : Z, (z ≫ q) x ∈ T → z x ∈ V) :
    IsClosedImmersion (coprod.desc (retainedBoundaryInclusion V ∣_ q ⁻¹ᵁ T)
      (z ∣_ q ⁻¹ᵁ T)) ∧
    IsFinite (coprod.desc (retainedBoundaryInclusion V ∣_ q ⁻¹ᵁ T)
      (z ∣_ q ⁻¹ᵁ T) ≫ (q ∣_ T)) := by
  refine ⟨isClosedImmersion_coprod_desc _ _
    (retained_prescribed_disjoint_on_base q V z T hz), ?_⟩
  rw [coprod.desc_comp, ← morphismRestrict_comp, ← morphismRestrict_comp]
  infer_instance

end AlgebraicGeometry.Scheme.RelativeCurve
