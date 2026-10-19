/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFactorizationRatio
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.GlobalBoundaryPencil
public import Mathlib.RingTheory.Norm.Basic

/-! # Identity generic-fiber norms retain the original section ratio

The actual identity pullback is a rank-one scalar algebra. The original
same-line equation on the specified open identifies its canonical ratio without
introducing another rational-function object or assuming a norm equality.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.IdentityGenericFiberNorm`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLocalRatio`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- The original structure map of an isomorphic affine scheme identifies its
actual scalar algebra with the base ring. -/
def scalarEquivOfIsIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsIso p] :
    let : Algebra R Γ(X, ⊤) := (scalarMap p).toAlgebra
    R ≃ₐ[R] Γ(X, ⊤) := by
  let : Algebra R Γ(X, ⊤) := (scalarMap p).toAlgebra
  let e := (Scheme.ΓSpecIso (.of R)).symm ≪≫ asIso p.appTop
  exact { e.commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }

/-- The determinant norm along the actual isomorphic structure map is rank one. -/
theorem norm_scalarMap_of_isIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsIso p] (a : R) :
    let : Algebra R Γ(X, ⊤) := (scalarMap p).toAlgebra
    Algebra.norm R (scalarMap p a) = a := by
  let : Algebra R Γ(X, ⊤) := (scalarMap p).toAlgebra
  have h := Algebra.norm_eq_of_algEquiv (scalarEquivOfIsIso p) a
  rw [Algebra.norm_self, MonoidHom.id_apply] at h
  convert h using 1
  congr 1


end AlgebraicGeometry.FiniteSchemeNormBaseChange

namespace AlgebraicGeometry.Scheme
open FiniteSchemeNormBaseChange

private theorem genericOpenLift_appTop {T : Scheme.{u}} [IsIntegral T]
    (W : T.Opens) [Nonempty W] (hη : genericPoint T ∈ W) (r : Γ(T, W)) :
    (W.fromSpecStalkOfMem (genericPoint T) hη).appTop (W.topIso.inv r) =
      (ΓSpecIso T.functionField).inv (T.germToFunctionField W r) := by
  have h := congrArg (fun m => (ΓSpecIso Γ(T, W)).inv ≫ m.appTop)
    (W.fromSpecStalkOfMem_toSpecΓ (genericPoint T) hη)
  rw [Hom.comp_appTop, Opens.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id_assoc,
    ← ΓSpecIso_inv_naturality] at h
  exact congrArg (fun m => m r) h

/-- An actual same-line ratio equation on the original nonempty open determines
the identity generic-fiber norm. The denominator's generic invertibility is
derived from its original monomorphism, not supplied as an additional hypothesis. -/
theorem genericFiberLineRatioNorm_id_eq_germ
    {T : Scheme.{u}} [IsIntegral T] (L : LineBundle T)
    (φ ψ : L.val ⟶ SheafOfModules.unit T.ringCatSheaf) [Mono φ] [Mono ψ]
    (W : T.Opens) [Nonempty W] (r : Γ(T, W))
    (h : pullbackUnitMap W.ι ψ ≫ unitMul W.toScheme (W.topIso.inv r) =
      pullbackUnitMap W.ι φ) :
    genericFiberLineRatioNorm (𝟙 T) L φ ψ = T.germToFunctionField W r := by
  let G := pullback (𝟙 T) (T.fromSpecStalk (genericPoint T))
  let q := pullback.snd (𝟙 T) (T.fromSpecStalk (genericPoint T))
  have hη : genericPoint T ∈ W :=
    ((genericPoint_spec T).mem_open_set_iff W.isOpen).mpr (by simpa using ‹Nonempty W›)
  let v := W.fromSpecStalkOfMem (genericPoint T) hη
  let t := q ≫ v
  have ht : t ≫ W.ι = pullback.fst (𝟙 T) (T.fromSpecStalk (genericPoint T)) := by
    simp only [t, v, Category.assoc, Opens.fromSpecStalkOfMem_ι]
    simpa only [Category.comp_id] using
      (pullback.condition (f := 𝟙 T)
        (g := T.fromSpecStalk (genericPoint T))).symm
  have hs : t.appTop (W.topIso.inv r) = scalarMap q (T.germToFunctionField W r) := by
    dsimp only [t]
    rw [Hom.comp_appTop]
    change q.appTop (v.appTop (W.topIso.inv r)) = _
    rw [genericOpenLift_appTop W hη r]
    rfl
  have := genericFiberLineMap_factorization_isIso (𝟙 T) W.ι t ht L ψ
  have hp : pullbackUnitMap t (pullbackUnitMap W.ι ψ) ≫
      unitMul G (t.appTop (W.topIso.inv r)) =
      pullbackUnitMap t (pullbackUnitMap W.ι φ) := by
    have hh := congrArg (pullbackUnitMap t) h
    simpa only [pullbackUnitMap, Functor.map_comp, Category.assoc,
      GlobalBoundaryPencil.pullback_unitMul] using hh
  have hc : pullbackUnitMap t (pullbackUnitMap W.ι ψ) ≫
      (genericFiberLineRatioIso (𝟙 T) L φ ψ).hom =
      pullbackUnitMap t (pullbackUnitMap W.ι φ) := by
    rw [genericFiberLineMap_factorization (𝟙 T) W.ι t ht L ψ,
      genericFiberLineMap_factorization (𝟙 T) W.ι t ht L φ]
    simp only [genericFiberLineRatioIso, Iso.trans_hom, Iso.symm_hom,
      asIso_inv, asIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]
  have he : (genericFiberLineRatioIso (𝟙 T) L φ ψ).hom =
      unitMul G (t.appTop (W.topIso.inv r)) :=
    (cancel_epi (pullbackUnitMap t (pullbackUnitMap W.ι ψ))).mp (hc.trans hp.symm)
  have hv : (genericFiberLineRatioUnit (𝟙 T) L φ ψ : Γ(G, ⊤)) =
      scalarMap q (T.germToFunctionField W r) := by
    change Modules.Hom.app (genericFiberLineRatioIso (𝟙 T) L φ ψ).hom ⊤ (1 : Γ(G, ⊤)) = _
    rw [he]
    erw [unitMul_app]
    change (1 : Γ(G, ⊤)) * (G.presheaf.map (𝟙 _)).hom
      (t.appTop (W.topIso.inv r)) = _
    simpa only [G.presheaf.map_id, CommRingCat.id_apply, one_mul] using hs
  let : Algebra T.functionField Γ(G, ⊤) := (scalarMap q).toAlgebra
  change Algebra.norm T.functionField
    (genericFiberLineRatioUnit (𝟙 T) L φ ψ : Γ(G, ⊤)) = _
  rw [hv]
  exact norm_scalarMap_of_isIso q _

end AlgebraicGeometry.Scheme
