/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.AffinePushforwardStalk
public import Motivic.RingTheory.Localization.FiniteFiberPoints
public import Motivic.Algebra.Homology.LengthEulerFiniteAlgebraModules

/-!
# The whole finite algebra acting on an affine pushforward stalk

The coefficient before restriction is the actual scalar extension to the whole
base-changed algebra. Cancellation of base change is natural in every module,
and therefore compares arbitrary complexes with all their differentials.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.AffinePushforward

section Tensor

variable (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]

/-- Literal scalar extension, with its specified algebra action and tensor maps. -/
def coordinateTensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (R ⊗[A] M)
  map g := ModuleCat.ofHom (g.hom.baseChange R)
  map_id M := by ext; rfl
  map_comp g h := by ext; rfl

instance coordinateTensorFunctor_additive : (coordinateTensorFunctor A R).Additive where
  map_add {M N} {g h} := by
    ext z
    change ((g.hom + h.hom).baseChange R) z =
      g.hom.baseChange R z + h.hom.baseChange R z
    simp only [LinearMap.baseChange_add, LinearMap.add_apply]

/-- The literal tensor functor is naturally the usual categorical scalar extension. -/
def coordinateTensorExtendIso :
    ModuleCat.extendScalars (algebraMap A R) ≅ coordinateTensorFunctor A R :=
  NatIso.ofComponents (fun M => (LengthEuler.finiteAlgebraExtendScalarsEquiv A R M).toModuleIso)
    (fun {M N} g => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul r m => rfl
      | add z w hz hw => simp only [map_add, hz, hw])

variable (B : Type u) [CommRing B] [Algebra A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Cancelling tensor extension over the whole base-changed algebra. -/
def wholeAlgebraTensorEquiv (M : ModuleCat.{u} B) :
    letI := Module.compHom M (algebraMap A B)
    (R ⊗[A] B) ⊗[B] M ≃ₗ[R] R ⊗[A] M := by
  let := Module.compHom M (algebraMap A B)
  have : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  exact Algebra.IsPushout.cancelBaseChange A R B (R ⊗[A] B) M

/-- The inverse sends every pure tensor by the literal base-to-whole-algebra map. -/
@[simp]
theorem wholeAlgebraTensorEquiv_symm_tmul (M : ModuleCat.{u} B) (r : R) (m : M) :
    letI := Module.compHom M (algebraMap A B)
    (wholeAlgebraTensorEquiv A R B M).symm (r ⊗ₜ[A] m) =
      algebraMap R (R ⊗[A] B) r ⊗ₜ[B] m := by
  let := Module.compHom M (algebraMap A B)
  have : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  exact Algebra.IsPushout.cancelBaseChange_symm_tmul A R B (R ⊗[A] B) M r m

/-- The cancellation comparison retains the literal restricted whole-algebra action. -/
def wholeAlgebraTensorModuleIso (M : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars (algebraMap A B) ⋙ coordinateTensorFunctor A R).obj M ≅
      (coordinateTensorFunctor B (R ⊗[A] B) ⋙
        ModuleCat.restrictScalars (algebraMap R (R ⊗[A] B))).obj M := by
  let := Module.compHom M (algebraMap A B)
  have : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  let e := (wholeAlgebraTensorEquiv A R B M).symm
  exact (show R ⊗[A] M ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R (R ⊗[A] B))).obj
        ((coordinateTensorFunctor B (R ⊗[A] B)).obj M) from
    { e.toAddEquiv with
      map_smul' := fun r z => by
        change e (r • z) = algebraMap R (R ⊗[A] B) r • e z
        rw [IsScalarTower.algebraMap_smul (R ⊗[A] B) r (e z)]
        exact e.map_smul r z }).toModuleIso

/-- The whole-algebra comparison is natural, including noninvertible module maps. -/
def wholeAlgebraTensorIso :
    ModuleCat.restrictScalars (algebraMap A B) ⋙ coordinateTensorFunctor A R ≅
      coordinateTensorFunctor B (R ⊗[A] B) ⋙
        ModuleCat.restrictScalars (algebraMap R (R ⊗[A] B)) :=
  NatIso.ofComponents (fun M => wholeAlgebraTensorModuleIso A R B M)
    (fun {M N} g => by
      let := Module.compHom M (algebraMap A B)
      let := Module.compHom N (algebraMap A B)
      ext z
      induction z using TensorProduct.inductionOn with
      | tmul r m =>
        change (wholeAlgebraTensorEquiv A R B N).symm (r ⊗ₜ[A] g m) =
          (g.hom.baseChange (R ⊗[A] B)) ((wholeAlgebraTensorEquiv A R B M).symm (r ⊗ₜ[A] m))
        simp only [wholeAlgebraTensorEquiv_symm_tmul, LinearMap.baseChange_tmul]
      | add z w hz hw => simp only [map_add, hz, hw])

end Tensor

section ActualStalk

variable (A B : CommRingCat.{u}) [Algebra A B] (p : PrimeSpectrum A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The whole base-changed algebra over the actual target structure stalk. -/
abbrev wholeStalkAlgebra := (Spec A).presheaf.stalk p ⊗[A] B

/-- The actual-stalk model is the same whole algebra as the prime-localization model. -/
def wholeStalkAlgebraEquiv : wholeStalkAlgebra A B p ≃ₐ[A] FiniteFiber.localAlgebra A B p :=
  Algebra.TensorProduct.congr (StructureSheaf.stalkIso A p).symm (AlgEquiv.refl : B ≃ₐ[A] B)

/-- The whole-algebra identification keeps the original source coordinate map. -/
@[simp]
theorem wholeStalkAlgebraEquiv_source (b : B) :
    wholeStalkAlgebraEquiv A B p (algebraMap B (wholeStalkAlgebra A B p) b) =
      algebraMap B (FiniteFiber.localAlgebra A B p) b := by
  change wholeStalkAlgebraEquiv A B p (1 ⊗ₜ[A] b) = 1 ⊗ₜ[A] b
  simp [wholeStalkAlgebraEquiv]

/-- Its base square uses the literal isomorphism from the actual target scheme stalk. -/
theorem wholeStalkAlgebraEquiv_base (r : (Spec A).presheaf.stalk p) :
    wholeStalkAlgebraEquiv A B p
        (algebraMap ((Spec A).presheaf.stalk p) (wholeStalkAlgebra A B p) r) =
      algebraMap (Localization.AtPrime p.asIdeal) (FiniteFiber.localAlgebra A B p)
        ((Spec.stalkIso A p).hom r) := by
  rfl

/-- A finite affine map gives a finite whole algebra over the actual target stalk. -/
instance wholeStalkAlgebra_finite [Module.Finite A B] :
    Module.Finite ((Spec A).presheaf.stalk p) (wholeStalkAlgebra A B p) :=
  inferInstance

/-- Actual affine pushforward stalks are restriction of the actual whole-algebra
coefficient modules, naturally in every original source module. -/
def pushforwardStalkWholeAlgebraIso :
    (tilde.functor B ⋙ Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) ⋙
        ModuleStalk.functor (X := Spec A) p ≅
      ModuleCat.extendScalars (algebraMap B (wholeStalkAlgebra A B p)) ⋙
        ModuleCat.restrictScalars
          (algebraMap ((Spec A).presheaf.stalk p) (wholeStalkAlgebra A B p)) :=
  pushforwardStalkIso A p (CommRingCat.ofHom (algebraMap A B)) ≪≫
    wholeAlgebraTensorIso A ((Spec A).presheaf.stalk p) B ≪≫
    Functor.isoWhiskerRight
      (coordinateTensorExtendIso B (wholeStalkAlgebra A B p)).symm _

/-- The comparison intertwines the literal pushforward stalk map with extension
and restriction of the original source-module map. -/
@[reassoc]
theorem pushforwardStalkWholeAlgebraIso_naturality {M N : ModuleCat.{u} B} (g : M ⟶ N) :
    ModuleStalk.map p ((Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map (tilde.map g)) ≫
          (pushforwardStalkWholeAlgebraIso A B p).hom.app N =
      (pushforwardStalkWholeAlgebraIso A B p).hom.app M ≫
        (ModuleCat.restrictScalars
          (algebraMap ((Spec A).presheaf.stalk p) (wholeStalkAlgebra A B p))).map
            ((ModuleCat.extendScalars (algebraMap B (wholeStalkAlgebra A B p))).map g) :=
  (pushforwardStalkWholeAlgebraIso A B p).hom.naturality g

/-- The comparison of arbitrary actual coefficient complexes uses the original
differentials and does not require finite homology or flatness. -/
def pushforwardStalkWholeAlgebraComplexIso {ι : Type*} (c : ComplexShape ι) :
    ((tilde.functor B ⋙ Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) ⋙
        ModuleStalk.functor (X := Spec A) p).mapHomologicalComplex c ≅
      (ModuleCat.extendScalars (algebraMap B (wholeStalkAlgebra A B p)) ⋙
        ModuleCat.restrictScalars
          (algebraMap ((Spec A).presheaf.stalk p)
            (wholeStalkAlgebra A B p))).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (pushforwardStalkWholeAlgebraIso A B p) c

/-- Each component is the literal module comparison on the original degree. -/
theorem pushforwardStalkWholeAlgebraComplexIso_hom_f {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (ModuleCat.{u} B) c) (i : ι) :
    ((pushforwardStalkWholeAlgebraComplexIso A B p c).app K).hom.f i =
      (pushforwardStalkWholeAlgebraIso A B p).hom.app (K.X i) := rfl

/-- Every pair of actual stalk differentials commutes with the whole-algebra comparison. -/
theorem pushforwardStalkWholeAlgebraComplexIso_d {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (ModuleCat.{u} B) c) (i j : ι) :
    ModuleStalk.map p ((Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map (tilde.map (K.d i j))) ≫
          (pushforwardStalkWholeAlgebraIso A B p).hom.app (K.X j) =
      (pushforwardStalkWholeAlgebraIso A B p).hom.app (K.X i) ≫
        (ModuleCat.restrictScalars
          (algebraMap ((Spec A).presheaf.stalk p) (wholeStalkAlgebra A B p))).map
            ((ModuleCat.extendScalars (algebraMap B (wholeStalkAlgebra A B p))).map (K.d i j)) :=
  pushforwardStalkWholeAlgebraIso_naturality A B p (K.d i j)

end ActualStalk

end Motivic.AffinePushforward
