/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.OriginalEtaleSquareBaseChange
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedPrescribedBoundary

/-! # The full original finite prescribed scheme on the actual retained target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {X N Z S : Scheme.{u}} (i : X ⟶ N) [IsOpenImmersion i]
  (q : N ⟶ S) (f : X ⟶ S) (hi : i ≫ q = f)
  (T : S.Opens) (V : N.Opens) (hV : (V : Set N) ⊆ Set.range i)
  (z : Z ⟶ X) (hz : ∀ x : Z, (z ≫ f) x ∈ T → i (z x) ∈ V)

include hi hz

/-- Every point of the full original prescribed scheme over the base neighborhood
lies in the actual retained target, not merely in its schematic support. -/
theorem prescribedBase_range_original :
    Set.range (((z ≫ f) ⁻¹ᵁ T).ι ≫ z) ⊆
      Set.range (retainedBaseToOriginal i q T V hV) := by
  rintro _ ⟨x, rfl⟩
  have hxT : q (i (z x.val)) ∈ T := by
    change (i ≫ q) (z x.val) ∈ T
    rw [hi]
    exact x.property
  exact ⟨⟨⟨i (z x.val), hz x.val x.property⟩, hxT⟩,
    retainedBaseToOriginal_point i q T V hV (z x.val) (hz x.val x.property) hxT⟩

/-- The lift retains the entire original base-restricted scheme structure. -/
def prescribedBaseToRetained : ((z ≫ f) ⁻¹ᵁ T).toScheme ⟶
    (retainedBaseOpen q T V).toScheme :=
  IsOpenImmersion.lift (retainedBaseToOriginal i q T V hV)
    (((z ≫ f) ⁻¹ᵁ T).ι ≫ z) (prescribedBase_range_original i q f hi T V hV z hz)

@[reassoc (attr := simp)]
theorem prescribedBaseToRetained_original :
    prescribedBaseToRetained i q f hi T V hV z hz ≫ retainedBaseToOriginal i q T V hV =
      ((z ≫ f) ⁻¹ᵁ T).ι ≫ z := IsOpenImmersion.lift_fac _ _ _

/-- Its structural map is literally the original prescribed finite map restricted to T. -/
@[reassoc]
theorem prescribedBaseToRetained_projection :
    prescribedBaseToRetained i q f hi T V hV z hz ≫ ((V.ι ≫ q) ∣_ T) =
      ((z ≫ f) ∣_ T) := by
  apply (cancel_mono T.ι).mp
  rw [Category.assoc, morphismRestrict_ι, morphismRestrict_ι]
  calc
    _ = prescribedBaseToRetained i q f hi T V hV z hz ≫
        retainedBaseToOriginal i q T V hV ≫ i ≫ q := by
      rw [retainedBaseToOriginal_comp_assoc]
    _ = _ := by rw [hi, ← Category.assoc, prescribedBaseToRetained_original, Category.assoc]

/-- Finiteness is preserved for the whole original scheme over the unchanged base open. -/
theorem prescribedBaseToRetained_finite [IsFinite (z ≫ f)] :
    IsFinite (prescribedBaseToRetained i q f hi T V hV z hz ≫ ((V.ι ≫ q) ∣_ T)) := by
  rw [prescribedBaseToRetained_projection]
  infer_instance

/-- Closedness is derived from the original closed immersion and its actual finite base map. -/
theorem prescribedBaseToRetained_closed [IsClosedImmersion z] [IsSeparated q]
    [IsFinite (z ≫ f)] :
    IsClosedImmersion (prescribedBaseToRetained i q f hi T V hV z hz) := by
  have : IsPreimmersion (prescribedBaseToRetained i q f hi T V hV z hz ≫
      retainedBaseToOriginal i q T V hV) := by
    rw [prescribedBaseToRetained_original]
    infer_instance
  have : IsPreimmersion (prescribedBaseToRetained i q f hi T V hV z hz) :=
    IsPreimmersion.of_comp _ (retainedBaseToOriginal i q T V hV)
  have := prescribedBaseToRetained_finite i q f hi T V hV z hz
  have : IsProper (prescribedBaseToRetained i q f hi T V hV z hz) :=
    IsProper.of_comp _ ((V.ι ≫ q) ∣_ T)
  exact IsClosedImmersion.of_isPreimmersion _
    (prescribedBaseToRetained i q f hi T V hV z hz).isClosedMap.isClosed_range

end AlgebraicGeometry.Scheme.RelativeCurve
