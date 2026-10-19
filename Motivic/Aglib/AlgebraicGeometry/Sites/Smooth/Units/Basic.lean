/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # The actual Nisnevich sheaf of global units -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

instance _root_.AlgebraicGeometry.Nisnevich.subcanonical : Nisnevich.topology.{u}.Subcanonical :=
  .of_le (Nisnevich.topology_le_etaleTopology.trans Scheme.etaleTopology_le_proetaleTopology)

/-- Global functions tested by a ring are represented by its actual spectrum. -/
def globalFunctionsRepresentable (R : CommRingCat.{u}) :
    Scheme.Γ ⋙ coyoneda.obj (op R) ≅ yoneda.obj (Spec R) :=
  NatIso.ofComponents (fun X =>
    (Equiv.trans (CategoryTheory.opEquiv (op (Scheme.Γ.obj X)) (op R)).symm
      (ΓSpec.adjunction.homEquiv X.unop (op R))).toIso) (by
    intro X Y f
    ext g
    exact ΓSpec.adjunction.homEquiv_naturality_left f.unop g.op)

/-- Global functions satisfy Nisnevich descent, as genuine ring-valued sections. -/
theorem globalFunctions_isSheaf : Presheaf.IsSheaf Nisnevich.topology Scheme.Γ := by
  intro R
  exact Presieve.isSheaf_iso Nisnevich.topology (globalFunctionsRepresentable R).symm
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/-- Multiplicative units in additive notation, without altering their group. -/
def ringUnits : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ commGroupAddCommGroupEquivalence.functor

/-- The ordinary unit presheaf is literally `X ↦ Γ(X,O)ˣ`. -/
def SmoothSite.unitsPresheaf (S : Scheme.{u}) :
    (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (SmoothSite.forgetScheme S).op ⋙ Scheme.Γ ⋙ ringUnits

/-- Unit sections satisfy actual Nisnevich descent on the smooth site. -/
theorem SmoothSite.unitsPresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (SmoothSite.nisnevichTopology S) (SmoothSite.unitsPresheaf S) := by
  let : PreservesLimitsOfSize.{u, u + 1} ringUnits := by
    unfold ringUnits
    infer_instance
  have h := Presheaf.isSheaf_comp_of_isSheaf Nisnevich.topology Scheme.Γ ringUnits
    globalFunctions_isSheaf
  exact (SmoothSite.forgetScheme S).op_comp_isSheaf_of_isSheaf _ _ _ h

/-- The ordinary Nisnevich sheaf Gm, with its original global-unit sections. -/
def SmoothSite.unitsSheaf (S : Scheme.{u}) :
    Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u} :=
  ⟨SmoothSite.unitsPresheaf S, SmoothSite.unitsPresheaf_isSheaf S⟩

/-- Actual sections, not a sheafification whose values still require comparison. -/
def SmoothSite.unitsSheafSections (S : Scheme.{u}) (X : SmoothSite S) :
    (SmoothSite.unitsSheaf S).obj.obj (op X) ≃+ Additive (Γ(X.left, ⊤))ˣ :=
  AddEquiv.refl _

/-- The universe used by the existing ordinary motivic sheaf complex. -/
def SmoothSite.largeUnitsPresheaf (S : Scheme.{u}) :
    (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  SmoothSite.unitsPresheaf S ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- Raising the universe preserves the already-proved genuine sheaf condition. -/
theorem SmoothSite.largeUnitsPresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (SmoothSite.nisnevichTopology S) (SmoothSite.largeUnitsPresheaf S) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SmoothSite.unitsPresheaf_isSheaf S)

/-- Gm in exactly the coefficient universe of `motivicSheafComplex`. -/
def SmoothSite.largeUnitsSheaf (S : Scheme.{u}) :
    Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1} :=
  ⟨SmoothSite.largeUnitsPresheaf S, SmoothSite.largeUnitsPresheaf_isSheaf S⟩

end AlgebraicGeometry.Scheme
