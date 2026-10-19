/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Sheafification
public import Motivic.Transfers.Sheaf.Basic
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Simplex.Basic
public import Motivic.Aglib.Algebra.Homology.Sheafification.Singular
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual smooth Nisnevich site

The tests use actual smooth-site morphisms and the residue-field covering
condition over an arbitrary field. The comparison is tested over arbitrary
affine bases. No connectedness or arbitrary-pullback assumptions are added.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.CategoryTheory.SingularComplex (presheafObj sheafCochainObj sheafCochainXIso)
open _root_.CategoryTheory.SingularComplex.Indexing (singularDegree)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe v u

namespace MotivicTest.SmoothSiteNisnevich
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]

example : (SmoothSite.nisnevichPrecoverage (Spec (.of k))).HasPullbacks := inferInstance

example : (SmoothSite.nisnevichPrecoverage (Spec (.of k))).IsStableUnderBaseChange :=
  inferInstance

/-- The covering condition is exactly étale maps with residue-field lifting. -/
theorem actualCoverCriterion {X : SmoothSite (Spec (.of k))} {ι : Type*}
    {Y : ι → SmoothSite (Spec (.of k))} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X ↔
      (∀ i, Etale (f i).left) ∧ ∀ x : X.left,
        ∃ (i : ι) (y : (Y i).left), (f i).left y = x ∧
          IsIso ((f i).left.residueFieldMap y) :=
  SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff f

/-- The constructed projection is the literal scheme pullback projection. -/
theorem actualEtalePullbackProjection {S : Scheme.{u}} {X Y Z : SmoothSite S}
    (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] :
    (SmoothSite.etalePullbackSnd f g).left = pullback.snd f.left g.left := rfl

example {S : Scheme.{u}} {X Y Z : SmoothSite S} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f.left] : PreservesLimit (cospan f g) (SmoothSite.forgetScheme S) := inferInstance

/-- The family-generated topology agrees with genuine restriction of the big topology. -/
theorem actualTopologyComparison (S : Scheme.{u}) [IsAffine S] :
    SmoothSite.nisnevichTopology S =
      (SmoothSite.forget S).restrictedTopology (Nisnevich.topology.over S) :=
  SmoothSite.nisnevichTopology_eq_restrictedTopology S

/-- The topology also agrees with the continuous induced topology. -/
theorem actualInducedTopologyComparison (S : Scheme.{u}) [IsAffine S] :
    SmoothSite.nisnevichTopology S =
      (SmoothSite.forget S).inducedTopology (Nisnevich.topology.over S) :=
  SmoothSite.nisnevichTopology_eq_inducedTopology S

example (S : Scheme.{u}) [IsAffine S] : (SmoothSite.forget S).IsCocontinuous
    (SmoothSite.nisnevichTopology S) (Nisnevich.topology.over S) := inferInstance

example : Preadditive (SheafWithTransfers.{v} k) := inferInstance

example : (SheafWithTransfers.forget.{v} k).Full := inferInstance

example : (SheafWithTransfers.forget.{v} k).Faithful := inferInstance

example : (SheafWithTransfers.toSheaf.{v} k).Faithful := inferInstance

example : (SheafWithTransfers.toSheaf.{v} k).Additive := inferInstance

/-- Forgetting transfers retains exactly the graph action, without a fullness assertion. -/
theorem underlyingSheafGraphAction (P : SheafWithTransfers.{v} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    ((SheafWithTransfers.toSheaf k).obj P).obj.map f.op =
      PresheafWithTransfers.transfer P.obj ((Cor.graphFunctor k).map f) := rfl

section OrdinarySheafification

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{v}]

/-- Existing ordinary singular sheafification accepts actual graph-restricted transfers,
using the proved products and actual barycentric simplex of the smooth category. -/
def ordinaryNisnevichSingularCochains (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    CochainComplex (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{v}) ℤ :=
  sheafCochainObj (SmoothSite.nisnevichTopology (Spec (.of k)))
    (_root_.AlgebraicSimplex.cosimplicialSmoothSite k) ((PresheafWithTransfers.toPresheaf k).obj P)
        q

/-- Each placed ordinary term is the actual sheafification of its singular presheaf term. -/
example (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (ordinaryNisnevichSingularCochains P q).X (singularDegree q r) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{v}).obj
        ((presheafObj (_root_.AlgebraicSimplex.cosimplicialSmoothSite k)
          ((PresheafWithTransfers.toPresheaf k).obj P)).X r) :=
  sheafCochainXIso _ _ _ q r

end OrdinarySheafification

section RestrictionComparison

variable (S : Scheme.{u}) [IsAffine S]
variable [HasWeakSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{v}]
variable [HasWeakSheafify (Nisnevich.topology.over S) AddCommGrpCat.{v}]
variable [∀ F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{v},
  (SmoothSite.forget S).op.HasPointwiseRightKanExtension F]

/-- The ordinary comparison keeps every sheafification and size hypothesis explicit. -/
example (P : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    toSheafify (SmoothSite.nisnevichTopology S) ((SmoothSite.forget S).op ⋙ P) ≫
      ((SmoothSite.restrictNisnevichSheafificationIso S AddCommGrpCat.{v}).hom.app P).hom =
        Functor.whiskerLeft (SmoothSite.forget S).op
          (toSheafify (Nisnevich.topology.over S) P) :=
  SmoothSite.toSheafify_restrictNisnevichSheafificationIso S AddCommGrpCat.{v} P

end RestrictionComparison

open Lean in
run_cmd do
  let interfaces := #[
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.etalePullbackConeIsLimit,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.mem_nisnevichTopology_iff,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_nisnevich_refinement,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology_eq_restrictedTopology,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology_eq_inducedTopology,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.restrictNisnevichSheaf,
    ``_root_.AlgebraicGeometry.Scheme.SmoothSite.restrictNisnevichSheafificationIso,
    ``toSheafify_restrictNisnevichSheafificationIso,
    ``PresheafWithTransfers.IsNisnevichSheaf,
    ``SheafWithTransfers.toSheaf,
    ``ordinaryNisnevichSingularCochains]
  for interface in interfaces do
    for dependency in ← collectAxioms interface do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "Interface {interface} depends on unsupported assumption {dependency}"
  logInfo "The smooth Nisnevich site uses only standard Lean logical foundations."

end MotivicTest.SmoothSiteNisnevich
