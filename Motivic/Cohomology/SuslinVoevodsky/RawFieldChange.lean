/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.FieldCycleEvaluation
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Composition
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Simplex.BaseChange
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Torus.BaseChange

/-!
# Actual raw motivic complexes under arbitrary field change

The maps use the original signed finite-cycle field change, the literal torus
comparison, and the quotient by every identity axis. The source and target
presheaves are evaluated only on their own finite-type smooth sites.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe u v

section
open _root_.CategoryTheory.SingularComplex

namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The actual field-change functor preserves the whole graph of every map. -/
@[simp]
theorem fieldBaseChange_graph {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (fieldBaseChange φ).map ((graphFunctor k).map f) =
      (graphFunctor L).map ((SmoothSite.fieldBaseChange φ).map f) :=
  FiniteCorrespondence.fieldBaseChange_componentGraphCycleOver φ f

end Motivic.Cor

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- Restriction along actual field change, retaining additivity of all transfers. -/
def fieldChangeRestriction (P : PresheafWithTransfers.{v} L) :
    PresheafWithTransfers.{v} k :=
  AdditiveFunctor.of ((Cor.fieldBaseChange φ).op ⋙ P.obj)

/-- Base change of a torus correspondence, followed by the literal torus comparison. -/
def torusFieldChange (q : ℕ) :
    torusRepresentable k q ⟶ fieldChangeRestriction φ (torusRepresentable L q) :=
  ⟨{
    app X := AddCommGrpCat.ofHom
      { toFun := fun α => ULift.up ((Cor.fieldBaseChange φ).map α.down ≫
          (Cor.graphFunctor L).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom)
        map_zero' := by
          apply ULift.ext
          change (Cor.fieldBaseChange φ).map 0 ≫ _ = 0
          rw [Functor.map_zero, zero_comp]
        map_add' := by
          intro α β
          apply ULift.ext
          change (Cor.fieldBaseChange φ).map (α.down + β.down) ≫ _ = _
          rw [Functor.map_add, Preadditive.add_comp]
          rfl }
    naturality X Y f := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro α
      change ULift.up ((Cor.fieldBaseChange φ).map (f.unop ≫ α.down) ≫ _) =
        ULift.up ((Cor.fieldBaseChange φ).map f.unop ≫
          ((Cor.fieldBaseChange φ).map α.down ≫ _))
      rw [Functor.map_comp, Category.assoc] }⟩

/-- The unreduced map retains the actual signed field-change cycle. -/
@[simp]
theorem torusFieldChange_app_apply (q : ℕ) (X : Cor k)
    (α : X ⟶ Cor.mk (SmoothSite.torusPower (.of k) q)) :
    (torusFieldChange φ q).hom.app (op X) (ULift.up α) =
      ULift.up ((Cor.fieldBaseChange φ).map α ≫ (Cor.graphFunctor L).map
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom) := rfl

/-- The quotient projection after actual base change. -/
def torusFieldChangeToReduced (q : ℕ) :
    torusRepresentable k q ⟶ fieldChangeRestriction φ (reducedTorus L q) :=
  torusFieldChange φ q ≫
    ⟨whiskerLeft (Cor.fieldBaseChange φ).op (toReducedTorus L q).hom⟩

/-- Every original identity axis maps into the corresponding new identity axis. -/
theorem torusFieldChangeToReduced_axis (q : ℕ) (i : Fin q) :
    torusIdentityAxis k q i ≫ torusFieldChangeToReduced φ q = 0 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro α
    change ULift.{u + 1} (X.unop ⟶ Cor.mk (SmoothSite.torusPower (.of k) q)) at α
    have haxis : (SmoothSite.fieldBaseChange φ).map
        (SmoothSite.torusInsertOne (.of k) q i) ≫
          (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) (q + 1)).hom =
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom ≫
          SmoothSite.torusInsertOne (.of L) q i :=
      SmoothSite.torusPowerBaseChangeIso_insertOne (CommRingCat.ofHom φ) q i
    change (toReducedTorus L (q + 1)).hom.app _
      (ULift.up ((Cor.fieldBaseChange φ).map
        (α.down ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) q i)) ≫
          (Cor.graphFunctor L).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) (q + 1)).hom)) = 0
    rw [Functor.map_comp, Cor.fieldBaseChange_graph, Category.assoc,
      ← Functor.map_comp, haxis,
      Functor.map_comp, ← Category.assoc]
    exact congrArg (fun f => f.hom.app (op ((Cor.fieldBaseChange φ).obj X.unop))
      (ULift.up ((Cor.fieldBaseChange φ).map α.down ≫ (Cor.graphFunctor L).map
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom)))
      (torusIdentityAxis_toReducedTorus L (q + 1) i)

/-- Actual arbitrary-field change descends through the full torus identity-axis quotient. -/
def reducedTorusFieldChange (q : ℕ) :
    reducedTorus k q ⟶ fieldChangeRestriction φ (reducedTorus L q) :=
  reducedTorusDesc k q (torusFieldChangeToReduced φ q)
    (torusFieldChangeToReduced_axis φ q)

/-- The descended morphism retains the actual cycle map on every represented section. -/
theorem reducedTorusFieldChange_quotient (q : ℕ) (X : Cor k)
    (α : X ⟶ Cor.mk (SmoothSite.torusPower (.of k) q)) :
    (reducedTorusFieldChange φ q).hom.app (op X)
      ((toReducedTorus k q).hom.app (op X) (ULift.up α)) =
        (toReducedTorus L q).hom.app (op ((Cor.fieldBaseChange φ).obj X))
          (ULift.up ((Cor.fieldBaseChange φ).map α ≫ (Cor.graphFunctor L).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom)) :=
  congrArg (fun f => f.hom.app (op X) (ULift.up α))
    (toReducedTorus_desc k q (torusFieldChangeToReduced φ q)
      (torusFieldChangeToReduced_axis φ q))

end Motivic.PresheafWithTransfers


namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The original base-times-simplex parameter commutes with arbitrary field change. -/
def baseSimplexFieldChangeIso (n : SimplexCategory) :
    (fieldBaseChange φ).obj (product (base (Spec (.of k)))
      ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj n)) ≅
        product (base (Spec (.of L))) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite L).obj n) :=
  baseChangeProductIso (Spec.map (CommRingCat.ofHom φ))
      (base (Spec (.of k))) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj n) ≪≫
    productIso (baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ)))
      ((_root_.AlgebraicSimplex.cosimplicialSmoothSiteBaseChangeIso φ).app n)

/-- Every simplex map, including all faces and degeneracies, respects the parameter comparison. -/
@[reassoc]
theorem baseSimplexFieldChangeIso_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    (fieldBaseChange φ).map (productMap (𝟙 (base (Spec (.of k))))
      ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f)) ≫
        (baseSimplexFieldChangeIso φ n).hom =
      (baseSimplexFieldChangeIso φ m).hom ≫
        productMap (𝟙 (base (Spec (.of L))))
          ((_root_.AlgebraicSimplex.cosimplicialSmoothSite L).map f) := by
  dsimp only [baseSimplexFieldChangeIso, Iso.trans_hom, productIso_hom, fieldBaseChange]
  rw [← Category.assoc]
  rw [baseChangeProductIso_naturality (Spec.map (CommRingCat.ofHom φ))
    (𝟙 (base (Spec (.of k)))) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f)]
  simp only [Category.assoc]
  rw [← productMap_comp, ← productMap_comp,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact congrArg (fun g => (baseChangeProductIso (Spec.map (CommRingCat.ofHom φ))
    (base (Spec (.of k))) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj m)).hom ≫
      productMap (baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom g)
    ((_root_.AlgebraicSimplex.cosimplicialSmoothSiteBaseChangeIso φ).hom.naturality f)

end AlgebraicGeometry.Scheme.SmoothSite

namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The actual base-simplex comparison as an isomorphism of full cosimplicial correspondences. -/
def baseSimplexFieldChangeIso :
    simplexProductCosimplicial (mk (SmoothSite.base (Spec (.of k)))) ⋙ fieldBaseChange φ ≅
      simplexProductCosimplicial (mk (SmoothSite.base (Spec (.of L)))) :=
  NatIso.ofComponents (fun n => (graphFunctor L).mapIso
    (SmoothSite.baseSimplexFieldChangeIso φ n)) (by
      intro m n f
      change (fieldBaseChange φ).map ((graphFunctor k).map _) ≫
        (graphFunctor L).map _ = (graphFunctor L).map _ ≫ (graphFunctor L).map _
      rw [fieldBaseChange_graph, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg ((graphFunctor L).map)
        (SmoothSite.baseSimplexFieldChangeIso_naturality φ f))

end Motivic.Cor

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- All simplex operators act naturally on actual reduced field-change sections. -/
def reducedTorusSimplicialFieldChange (q : ℕ) :
    SingularComplex.simplicial
      (Cor.simplexProductCosimplicial (Cor.mk (SmoothSite.base (Spec (.of k)))))
        (reducedTorus k q).obj ⟶
    SingularComplex.simplicial
      (Cor.simplexProductCosimplicial (Cor.mk (SmoothSite.base (Spec (.of L)))))
        (reducedTorus L q).obj :=
  whiskerLeft (Cor.simplexProductCosimplicial
      (Cor.mk (SmoothSite.base (Spec (.of k))))).op (reducedTorusFieldChange φ q).hom ≫
    (Functor.associator (Cor.simplexProductCosimplicial
      (Cor.mk (SmoothSite.base (Spec (.of k))))).op (Cor.fieldBaseChange φ).op
        (reducedTorus L q).obj).inv ≫
    whiskerRight (Functor.opComp (Cor.simplexProductCosimplicial
      (Cor.mk (SmoothSite.base (Spec (.of k))))) (Cor.fieldBaseChange φ)).inv
        (reducedTorus L q).obj ≫
    whiskerRight (NatTrans.op (Cor.baseSimplexFieldChangeIso φ).inv) (reducedTorus L q).obj

/-- The all-degree chain map on the actual reduced singular cycles at the base field. -/
def reducedTorusSingularFieldChange (q : ℕ) :
    singularObj (reducedTorus k q) (Cor.mk (SmoothSite.base (Spec (.of k)))) ⟶
      singularObj (reducedTorus L q) (Cor.mk (SmoothSite.base (Spec (.of L)))) :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u + 1}).map
    (reducedTorusSimplicialFieldChange φ q)

end Motivic.PresheafWithTransfers

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- Actual signed cycles from the base to the torus change coefficients through
both literal parameter comparisons. -/
def baseTorusCycleFieldChange (q : ℕ) :
    (Cor.mk (SmoothSite.base (Spec (.of k))) ⟶
      Cor.mk (SmoothSite.torusPower (.of k) q)) →+
    (Cor.mk (SmoothSite.base (Spec (.of L))) ⟶
      Cor.mk (SmoothSite.torusPower (.of L) q)) where
  toFun α := (Cor.graphFunctor L).map
    (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
      (Cor.fieldBaseChange φ).map α ≫ (Cor.graphFunctor L).map
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom
  map_zero' := by rw [Functor.map_zero, zero_comp, comp_zero]
  map_add' α β := by
    rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- The corresponding map on actual reduced torus sections at the two base fields. -/
def baseReducedTorusFieldChange (q : ℕ) :
    sections (reducedTorus k q) (Cor.mk (SmoothSite.base (Spec (.of k)))) ⟶
      sections (reducedTorus L q) (Cor.mk (SmoothSite.base (Spec (.of L)))) :=
  (reducedTorusFieldChange φ q).hom.app (op (Cor.mk (SmoothSite.base (Spec (.of k))))) ≫
    transfer (reducedTorus L q) ((Cor.graphFunctor L).map
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).inv)

/-- The base-section quotient map is the quotient of the original signed cycle map. -/
theorem baseReducedTorusFieldChange_quotient (q : ℕ)
    (α : Cor.mk (SmoothSite.base (Spec (.of k))) ⟶
      Cor.mk (SmoothSite.torusPower (.of k) q)) :
    baseReducedTorusFieldChange φ q
      ((toReducedTorus k q).hom.app (op (Cor.mk (SmoothSite.base (Spec (.of k)))))
        (ULift.up α)) =
      (toReducedTorus L q).hom.app (op (Cor.mk (SmoothSite.base (Spec (.of L)))))
        (ULift.up (baseTorusCycleFieldChange φ q α)) := by
  change transfer (reducedTorus L q) _
    ((reducedTorusFieldChange φ q).hom.app _
      ((toReducedTorus k q).hom.app _ (ULift.up α))) = _
  rw [reducedTorusFieldChange_quotient, reducedTorus_transfer_apply]
  rfl

/-- In every singular degree the chain map is the quotient field change followed
by transfer along the inverse literal base-simplex comparison. -/
theorem reducedTorusSingularFieldChange_f (q n : ℕ) :
    (reducedTorusSingularFieldChange φ q).f n =
      (reducedTorusFieldChange φ q).hom.app
        (op (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n)) ≫
      transfer (reducedTorus L q) ((Cor.graphFunctor L).map
        (SmoothSite.baseSimplexFieldChangeIso φ ⦋n⦌).inv) := by
  simp only [reducedTorusSingularFieldChange,
    AlgebraicTopology.alternatingFaceMapComplex_map_f, reducedTorusSimplicialFieldChange,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.associator_inv_app,
    Functor.opComp_inv_app]
  change (reducedTorusFieldChange φ q).hom.app
      (op (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n)) ≫
      𝟙 _ ≫ (reducedTorus L q).obj.map (𝟙 _) ≫
        transfer (reducedTorus L q) ((Cor.graphFunctor L).map
          (SmoothSite.baseSimplexFieldChangeIso φ ⦋n⦌).inv) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun f => (reducedTorusFieldChange φ q).hom.app
    (op (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n)) ≫ f)
      (Category.id_comp (transfer (reducedTorus L q) ((Cor.graphFunctor L).map
        (SmoothSite.baseSimplexFieldChangeIso φ ⦋n⦌).inv)))

/-- Represented singular sections retain the complete signed field-change cycle. -/
theorem reducedTorusSingularFieldChange_quotient (q n : ℕ)
    (α : Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n ⟶
      Cor.mk (SmoothSite.torusPower (.of k) q)) :
    (reducedTorusSingularFieldChange φ q).f n
      ((toReducedTorus k q).hom.app
        (op (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n))
          (ULift.up α)) =
        (toReducedTorus L q).hom.app
          (op (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of L)))) n))
          (ULift.up ((Cor.graphFunctor L).map
            (SmoothSite.baseSimplexFieldChangeIso φ ⦋n⦌).inv ≫
              (Cor.fieldBaseChange φ).map α ≫ (Cor.graphFunctor L).map
                (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom)) := by
  rw [reducedTorusSingularFieldChange_f, ConcreteCategory.comp_apply]
  erw [reducedTorusFieldChange_quotient, reducedTorus_transfer_apply]
  rfl

end Motivic.PresheafWithTransfers

namespace Motivic.RawFieldChange
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- Evaluation on the actual base object, in the raw complex coefficient universe. -/
abbrev baseEvaluationFunctor : PresheafWithTransfers.{u + 1} k ⥤ AddCommGrpCat.{u + 1} :=
  toPresheaf k ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
    (op (SmoothSite.base (Spec (.of k))))

variable {k} {L : Type u} [Field L] (φ : k →+* L)

/-- The actual singular map in occupied degrees and the zero map elsewhere. -/
def component (q : ℕ) : (i : Option ℕ) →
    (baseEvaluationFunctor k).obj
      (HomologicalComplex.extend.X (singularComplex (reducedTorus k q)) i) ⟶
    (baseEvaluationFunctor L).obj
      (HomologicalComplex.extend.X (singularComplex (reducedTorus L q)) i)
  | none => 0
  | some n => (reducedTorusSingularFieldChange φ q).f n

/-- Zero extension retains all original differential equations. -/
theorem component_comm (q : ℕ) (i j : Option ℕ) :
    component φ q i ≫ (baseEvaluationFunctor L).map
        (HomologicalComplex.extend.d (singularComplex (reducedTorus L q)) i j) =
      (baseEvaluationFunctor k).map
        (HomologicalComplex.extend.d (singularComplex (reducedTorus k q)) i j) ≫
          component φ q j := by
  cases i with
  | none => cases j <;> simp [component, HomologicalComplex.extend.d]
  | some i =>
    cases j with
    | none => simp [component, HomologicalComplex.extend.d]
    | some j => exact (reducedTorusSingularFieldChange φ q).comm i j

/-- In an occupied degree the component is the original singular cycle map. -/
theorem component_eq (q n : ℕ) {i : Option ℕ} (h : i = some n) :
    component φ q i =
      (baseEvaluationFunctor k).map
          (HomologicalComplex.extend.XIso (singularComplex (reducedTorus k q)) h).hom ≫
        (reducedTorusSingularFieldChange φ q).f n ≫
          (baseEvaluationFunctor L).map
            (HomologicalComplex.extend.XIso (singularComplex (reducedTorus L q)) h).inv := by
  subst h
  simp only [component, HomologicalComplex.extend.XIso, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv]
  exact (Category.comp_id _).symm

/-- Zero extension of the actual singular chain map, before the canonical signed shift. -/
def unshiftedMap (q : ℕ) :
    ((baseEvaluationFunctor k).mapHomologicalComplex (.up ℤ)).obj
      (singularCochainComplex (reducedTorus k q) 0) ⟶
    ((baseEvaluationFunctor L).mapHomologicalComplex (.up ℤ)).obj
      (singularCochainComplex (reducedTorus L q) 0) where
  f i := component φ q ((ComplexShape.embeddingUpIntLE 0).r i)
  comm' i j _ := component_comm φ q
    ((ComplexShape.embeddingUpIntLE 0).r i) ((ComplexShape.embeddingUpIntLE 0).r j)

end Motivic.RawFieldChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The actual arbitrary-field cochain map on the canonical raw motivic complexes.
It is the genuine signed shift of the full reduced singular cycle map. -/
def _root_.Motivic.motivicRawBaseComplexMap (q : ℕ) :
    _root_.Motivic.motivicRawBaseComplex k q ⟶ _root_.Motivic.motivicRawBaseComplex L q :=
  (shiftFunctor (CochainComplex AddCommGrpCat.{u + 1} ℤ) (-(q : ℤ))).map
    (_root_.Motivic.RawFieldChange.unshiftedMap φ q)

/-- Every differential, including the canonical weight-dependent shift sign,
commutes with the actual field-change map. -/
theorem _root_.Motivic.motivicRawBaseComplexMap_comm (q : ℕ) (i j : ℤ) :
    (_root_.Motivic.motivicRawBaseComplexMap φ q).f i ≫ (_root_.Motivic.motivicRawBaseComplex L q).d
        i j =
      (_root_.Motivic.motivicRawBaseComplex k q).d i j ≫ (_root_.Motivic.motivicRawBaseComplexMap φ
          q).f j :=
  (_root_.Motivic.motivicRawBaseComplexMap φ q).comm i j

/-- In occupied degree `q-r` the raw map is exactly the actual singular cycle map,
through the original term dictionaries, with no alteration of the shift convention. -/
theorem _root_.Motivic.motivicRawBaseComplexMap_f (q r : ℕ) :
    (_root_.Motivic.motivicRawBaseComplexMap φ q).f (Indexing.singularDegree q r) =
      (_root_.Motivic.motivicRawBaseComplexXIso k q r).hom ≫
        (_root_.Motivic.PresheafWithTransfers.reducedTorusSingularFieldChange φ q).f r ≫
          (_root_.Motivic.motivicRawBaseComplexXIso L q r).inv :=
  _root_.Motivic.RawFieldChange.component_eq φ q r
    ((ComplexShape.embeddingUpIntLE 0).r_eq_some (by
      change (0 : ℤ) - r = (q : ℤ) - r + -(q : ℤ)
      omega))

end
