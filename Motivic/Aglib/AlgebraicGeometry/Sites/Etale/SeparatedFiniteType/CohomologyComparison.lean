module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ExtensionExact
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CoverLifting
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-! Ordinary Ext comparison for the actual big and small Nisnevich sites. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w w' u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

instance restrict_isLeftAdjoint : (restrict X AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
  ((toSmoothSite X).sheafAdjunctionCocontinuous _ _ _).isLeftAdjoint

instance restrict_isRightAdjoint : (restrict X AddCommGrpCat.{u + 1}).IsRightAdjoint :=
  (extendRestrictAdjunction X).isRightAdjoint

instance restrict_additive : (restrict X AddCommGrpCat.{u + 1}).Additive := by
  apply Functor.additive_of_preserves_binary_products

instance extend_additive : (extend X).Additive := by
  apply Functor.additive_of_preserves_binary_products

/-- The terminal object of the actual small site over `X`. -/
def identityObject : EtaleSeparatedFiniteType X.left :=
  MorphismProperty.Over.mk ⊤ (𝟙 X.left) (etaleSeparatedFiniteType.id_mem X.left)

/-- The displayed identity object is genuinely terminal. -/
def identityObjectIsTerminal : IsTerminal (identityObject X) :=
  MorphismProperty.Over.mkIdTerminal etaleSeparatedFiniteType X.left

/-- Forgetting the identity étale neighborhood recovers the original smooth object. -/
def identityImageIso : (toSmoothSite X).obj (identityObject X) ≅ X :=
  (Over.forget X).mapIso (terminalImageIso X)

variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{w'} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]

/-- Ordinary cohomology comparison, with both sides using their original free abelian
representing sources. Neither strict A1 invariance nor injective acyclicity is a premise. -/
def cohomologyRestrictionEquiv
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (U : EtaleSeparatedFiniteType X.left) :
    LargeCohomology.H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) F n ((toSmoothSite X).obj U) ≃+
    LargeCohomology.H.{w', u + 1, u, u + 1}
      (nisnevichTopology X.left) ((restrict X AddCommGrpCat).obj F) n U :=
  ((((extFunctor n).mapIso (extendSourceIso X U).op).app F).addCommGroupIsoToAddEquiv).trans
    (extendRestrictAdjunction X).extEquiv

/-- Cohomology of the original smooth object equals cohomology at the genuine
terminal small-site object, for the literal restricted ordinary sheaf. -/
def cohomologyAtBaseEquiv
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1}) (n : ℕ) :
    LargeCohomology.H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B) F n X ≃+
    LargeCohomology.H.{w', u + 1, u, u + 1} (nisnevichTopology X.left)
      ((restrict X AddCommGrpCat).obj F) n (identityObject X) := by
  let e := (Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology B)).mapIso (identityImageIso X)
  exact ((((extFunctor n).mapIso e.op).app F).addCommGroupIsoToAddEquiv).trans
    (cohomologyRestrictionEquiv X F n (identityObject X))

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
