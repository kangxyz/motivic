/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Diagonal.AffineEtale

/-!
# Transporting actual diagonal stalks through open charts

An open chart on the source and a monomorphism on the base induce an open
immersion of self-products. The commuting square of actual diagonal maps gives
an isomorphism of their stalk arrows. A proved ring-theoretic transport lemma
carries a genuine regular list and its kernel equality through any such arrow
isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.Diagonal

set_option backward.isDefEq.respectTransparency false in
/-- An arrow isomorphism transports an existing regular list generating its kernel. -/
theorem exists_regular_kernel_of_arrowIso {A B C D : CommRingCat.{u}}
    {f : A ⟶ B} {g : C ⟶ D} (e : Arrow.mk f ≅ Arrow.mk g)
    (h : ∃ rs : List A, IsRegular A rs ∧ RingHom.ker f.hom = Ideal.ofList rs) :
    ∃ rs : List C, IsRegular C rs ∧ RingHom.ker g.hom = Ideal.ofList rs := by
  obtain ⟨rs, hrs, hker⟩ := h
  let el : A ≃+* C := (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
  let er : B ≃+* D := (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv
  let := RingHomInvPair.of_ringEquiv el
  let := RingHomInvPair.symm (el : A →+* C) (el.symm : C →+* A)
  refine ⟨rs.map el.toRingHom, (el.toSemilinearEquiv.isRegular_congr' rs).mp hrs, ?_⟩
  have hc : (RingHom.ker g.hom).comap el = RingHom.ker f.hom := by
    ext x
    change g.hom (el x) = 0 ↔ f.hom x = 0
    have hw : g.hom (el x) = er (f.hom x) := ConcreteCategory.congr_hom e.hom.w x
    rw [hw]
    exact er.map_eq_zero_iff
  have hm : RingHom.ker g.hom = (RingHom.ker f.hom).map el := by
    rw [← hc, Ideal.map_comap_eq_self_of_equiv]
  rw [hm, hker]
  change (Ideal.ofList rs).map el.toRingHom = _
  exact Ideal.map_ofList _ _

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (h : g ≫ iY = iX ≫ f)

/-- The induced morphism between the actual self-products. -/
abbrev productMap : pullback g g ⟶ pullback f f :=
  pullback.map g g f f iX iX iY h h

set_option backward.isDefEq.respectTransparency false in
/-- The induced self-product morphism intertwines the actual diagonals. -/
theorem diagonal_productMap :
    pullback.diagonal g ≫ productMap f g iX iY h = iX ≫ pullback.diagonal f := by
  apply pullback.hom_ext <;> simp [productMap, pullback.map]

set_option backward.isDefEq.respectTransparency false in
/-- Open source charts over a base monomorphism identify the actual diagonal stalk arrows. -/
def arrowStalkIsoOfOpenChart [IsOpenImmersion iX] [Mono iY] (x : X') :
    Arrow.mk ((pullback.diagonal f).stalkMap (iX x)) ≅
      Arrow.mk ((pullback.diagonal g).stalkMap x) :=
  Arrow.isoMk'
    ((pullback.diagonal f).stalkMap (iX x)) ((pullback.diagonal g).stalkMap x)
    ((pullback f f).presheaf.stalkCongr (.of_eq <| by
      rw [← Scheme.Hom.comp_apply, ← diagonal_productMap f g iX iY h]
      rfl) ≪≫ asIso ((productMap f g iX iY h).stalkMap (pullback.diagonal g x)))
    (asIso (iX.stalkMap x)) (by
      simp only [Iso.trans_hom, asIso_hom, Category.assoc,
        ← Scheme.Hom.stalkMap_comp]
      exact (Scheme.Hom.stalkMap_congr_hom _ _
        (diagonal_productMap f g iX iY h).symm x).symm)

end Motivic.Diagonal
