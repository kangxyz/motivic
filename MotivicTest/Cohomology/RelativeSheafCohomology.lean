/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.RelativeSheafCohomology
public import Motivic.Transfers.DegreeZeroCohomology

/-!
# Actual relative Ext consumers for smooth open immersions

These consumers use the standard Ext instance and the original `u + 1`
coefficient universe of sheaves with transfers. The quotient is the actual
cokernel of the existing free-sheaf map. The two ordinary arrows remain
restrictions along the original open immersion, and the connecting sign is
tested explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Motivic

universe u

namespace MotivicTest.Cohomology.RelativeSheafCohomology

variable {k : Type u} [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

local instance {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X)
    [IsOpenImmersion j.left] : Mono j :=
  Hypercohomology.smoothSite_mono_of_isOpenImmersion j

variable {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) [IsOpenImmersion j.left]
  (F : SheafWithTransfers.{u + 1} k)

omit [IsOpenImmersion j.left] in
/-- The relative source uses the actual free-section map of the open immersion. -/
theorem actual_relative_source :
    SheafCohomology.relativeSource.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j =
      cokernel ((Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))).map j) := rfl

omit [IsOpenImmersion j.left] in
/-- Degree-zero relative Ext injects into the ordinary actual Ext group. -/
theorem actual_relative_zero_injective :
    Function.Injective (SheafCohomology.relativeForget.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) j
      ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) 0) := by
  have := SheafCohomology.relativeForget_zero_mono.{u + 2, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) j
    ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F)
  exact (AddCommGrpCat.mono_iff_injective _).mp this

/-- The six-term sequence tests both original restriction arrows, in every degree. -/
theorem actual_relative_sequence_exact (n : ℕ) :
    (ComposableArrows.mk₅
      (SheafCohomology.relativeForget.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n)
      ((SheafCohomology.presheaf.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n).map j.op)
      (SheafCohomology.relativeConnecting.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n)
      (SheafCohomology.relativeForget.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) (n + 1))
      ((SheafCohomology.presheaf.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) (n + 1)).map j.op)).Exact := by
  rw [← SheafCohomology.relativeSequence_eq.{u + 2, u + 1, u, u + 1}]
  exact SheafCohomology.relativeSequence_exact.{u + 2, u + 1, u, u + 1} _ j _ n

/-- Vanishing under the literal free-sheaf Ext restriction gives an actual relative lift. -/
theorem actual_ext_relative_lift (n : ℕ)
    (x : Ext (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) X)
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n)
    (hx : (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))).map j)).comp x (zero_add n) = 0) :
    ∃ z : Ext (SheafCohomology.relativeSource.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j)
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n,
      (Ext.mk₀ (SheafCohomology.relativeSourceπ.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        j)).comp z (zero_add n) = x :=
  SheafCohomology.relative_lift_of_restriction_zero.{u + 2, u + 1, u, u + 1} _ j _ n x hx

/-- The signed connecting map is exactly the standard Mathlib sign times its Ext class. -/
theorem actual_boundary_sign (n : ℕ)
    (x : SheafCohomology.H.{u + 2, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n U) :
    SheafCohomology.relativeBoundary.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) j
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n x =
      Int.negOnePow (n + 1) •
        (SheafCohomology.relativeExtClass.{u + 2, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) j).comp
          x (Nat.add_comm 1 n) := rfl

/-- A zero standard signed boundary extends the class along the original open immersion. -/
theorem actual_extension_of_boundary_zero (n : ℕ)
    (x : SheafCohomology.H.{u + 2, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n U)
    (hx : SheafCohomology.relativeBoundary.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) j
      ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n x = 0) :
    ∃ y : SheafCohomology.H.{u + 2, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n X,
      (SheafCohomology.presheaf.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n).map j.op y = x :=
  SheafCohomology.restriction_lift_of_relativeBoundary_zero.{u + 2, u + 1, u, u + 1} _ j _ n x hx

/-- A relative class which vanishes ordinarily is an actual standard signed boundary. -/
theorem actual_boundary_of_relative_forget_zero (n : ℕ)
    (z : SheafCohomology.relativeH.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) j
      ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) (n + 1))
    (hz : SheafCohomology.relativeForget.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) j
      ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) (n + 1) z = 0) :
    ∃ x : SheafCohomology.H.{u + 2, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n U,
      SheafCohomology.relativeBoundary.{u + 2, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) j
        ((SheafWithTransfers.toSheaf.{u + 1, u} k).obj F) n x = z :=
  SheafCohomology.relativeBoundary_lift_of_forget_zero.{u + 2, u + 1, u, u + 1} _ j _ n z hz

end MotivicTest.Cohomology.RelativeSheafCohomology
