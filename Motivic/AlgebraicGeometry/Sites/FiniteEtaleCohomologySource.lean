module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleNisnevich
public import Motivic.Cohomology.SheafCohomologyRestrictionSource

/-! Actual ordinary cohomology sources for big-to-small Nisnevich restriction. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

/-- The original left adjoint to literal big-to-small restriction. -/
def extend : Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1} ⥤
    Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1} :=
  (toSmoothSite X).sheafPullback _ _ _

/-- This is an actual adjunction, not an acyclicity hypothesis. -/
def extendRestrictAdjunction : extend X ⊣ restrict X AddCommGrpCat.{u + 1} :=
  (toSmoothSite X).sheafAdjunctionContinuous _ _ _

/-- Exact original free abelian sheaf sources under this adjunction. -/
def extendSourceIso (U : FiniteEtaleSite X.left) :
    (extend X).obj
      (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (nisnevichTopology X.left) U) ≅
      Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (SmoothSite.nisnevichTopology B)
        ((toSmoothSite X).obj U) :=
  Hypercohomology.restrictionSourceIso.{u + 1, u, u + 1, u + 1} _ _ (toSmoothSite X) U

end Motivic.FiniteEtaleSite
