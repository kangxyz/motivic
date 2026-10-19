module

public import Motivic.Cohomology.WeightOne.SheafComparison
public import Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Shift
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic

/-! # Weight-one motivic cohomology on all smooth schemes

The comparison uses the original motivic sheaf complex and its actual signed
shift. No affineness, integrality, connectedness, or base-field evaluation
assumption is imposed on the smooth source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe w w' u
namespace Motivic
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf
variable (k : Type u) [Field k]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Weight-one motivic cohomology is naturally the shifted genuine Gm hypercohomology,
in every integer degree and on the entire original smooth Nisnevich site. -/
def weightOneHypercohomologyPresheafIso (p : ℤ) :
    motivicCohomologyPresheaf.{w, u} k p 1 ≅
      Hypercohomology.presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((CochainComplex.singleFunctor _ 0).obj
          (SmoothSite.largeUnitsSheaf (Spec (.of k)))) (p - 1) := by
  let K := (CochainComplex.singleFunctor _ 0).obj
    (SmoothSite.largeUnitsSheaf (Spec (.of k)))
  let e := Hypercohomology.quasiIsoPresheafIso.{w, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) (weightOneSheafComparison k) p ≪≫
      Hypercohomology.shiftPresheafIso.{w, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) K (-1) p
  let h : (-1 : ℤ) + p = p - 1 := by omega
  exact e ≪≫ eqToIso (congrArg (fun i =>
    Hypercohomology.presheaf.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) K i) h)

/-- In ordinary nonnegative sheaf-cohomology degrees, H^(n+1,1)(X) equals H^n_Nis(X,Gm). -/
def weightOneSheafCohomologyEquiv
    [HasExt.{w'}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicCohomology.{w, u} k ((n : ℤ) + 1) 1 X ≃+
      LargeCohomology.H.{w', u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        (SmoothSite.largeUnitsSheaf (Spec (.of k))) n X := by
  have e : AddCommGrpCat.of (motivicCohomology.{w, u} k ((n : ℤ) + 1) 1 X) ≅
      AddCommGrpCat.of (Hypercohomology.H.{w, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((CochainComplex.singleFunctor _ 0).obj
          (SmoothSite.largeUnitsSheaf (Spec (.of k)))) (n : ℤ) X) := by
    let h : (n : ℤ) + 1 - 1 = n := by omega
    exact (weightOneHypercohomologyPresheafIso k ((n : ℤ) + 1)).app (op X) ≪≫
      eqToIso (congrArg (fun i => AddCommGrpCat.of
        (Hypercohomology.H.{w, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((CochainComplex.singleFunctor _ 0).obj
            (SmoothSite.largeUnitsSheaf (Spec (.of k)))) i X)) h)
  exact e.addCommGroupIsoToAddEquiv.trans
    (LargeCohomology.singleComparison.{w', w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      (SmoothSite.largeUnitsSheaf (Spec (.of k))) n X)

end Motivic
