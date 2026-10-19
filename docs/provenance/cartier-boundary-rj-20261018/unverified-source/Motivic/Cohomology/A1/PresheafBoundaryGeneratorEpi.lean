/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.PresheafBoundaryGenerators
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleJacobsonOpenCover

/-! # Epimorphisms detected on locally represented original boundary generators -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B} (j : U ⟶ Y) (i : Z ⟶ Y)

/-- It suffices to lift original punctured-section generators on genuine covering sieves
of their zero fibers. No cofinality or sheafification/direct-image interchange is used. -/
theorem presheafBoundary_epi_of_local_generators
    {C : Sheaf (nisnevichTopology Z.left) AddCommGrpCat.{u + 1}}
    (φ : C ⟶ presheafBoundary P j i)
    (h : ∀ (W : FiniteEtaleSite Y.left)
      (s : P.obj (op ((toSmoothSite U).obj ((baseChange j.left).obj W)))),
      Presheaf.imageSieve φ.hom ((presheafBoundaryGenerator P j i).app (op W) s) ∈
        nisnevichTopology Z.left ((baseChange i.left).obj W)) : Epi φ where
  left_cancellation {G} f g heq := by
    apply presheafBoundary_hom_ext P j i
    ext W s
    let G' := (sheafCompose (nisnevichTopology Z.left) (forget AddCommGrpCat.{u + 1})).obj G
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 G'.property).isSeparated _
      (h W.unop s)).ext
    rintro V t ⟨a, ha⟩
    have h₁ := ConcreteCategory.congr_hom (f.hom.naturality t.op)
      ((presheafBoundaryGenerator P j i).app W s)
    have h₂ := ConcreteCategory.congr_hom (g.hom.naturality t.op)
      ((presheafBoundaryGenerator P j i).app W s)
    have hfg := ConcreteCategory.congr_hom
      (congr_app ((sheafToPresheaf (nisnevichTopology Z.left) _).congr_map heq) (op V)) a
    exact h₁.symm.trans ((congrArg (f.hom.app _) ha.symm).trans
      (hfg.trans ((congrArg (g.hom.app _) ha).trans h₂)))


/-- Over a Jacobson zero scheme, actual open neighborhoods at closed points suffice.
They first form an honest open cover, hence a Nisnevich covering sieve; closed points
are not used as a substitute for arbitrary small-site stalks. -/
theorem presheafBoundary_epi_of_closedPoint_generators [JacobsonSpace Z.left]
    {C : Sheaf (nisnevichTopology Z.left) AddCommGrpCat.{u + 1}}
    (φ : C ⟶ presheafBoundary P j i)
    (h : ∀ (W : FiniteEtaleSite Y.left)
      (s : P.obj (op ((toSmoothSite U).obj ((baseChange j.left).obj W))))
      (w : ((baseChange i.left).obj W).left), IsClosed ({w} : Set _) →
      ∃ (V : FiniteEtaleSite Z.left) (v : V ⟶ (baseChange i.left).obj W),
        IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
        Presheaf.imageSieve φ.hom ((presheafBoundaryGenerator P j i).app (op W) s) v) :
    Epi φ := by
  apply presheafBoundary_epi_of_local_generators P j i φ
  intro W s
  have : JacobsonSpace ((baseChange i.left).obj W).left :=
    LocallyOfFiniteType.jacobsonSpace (Y := Z.left)
      (show ((baseChange i.left).obj W).left ⟶ Z.left from ((baseChange i.left).obj W).hom)
  exact sieve_mem_of_closedPoint_open_neighborhoods _ _ (h W s)


end Motivic.FiniteEtaleSite
