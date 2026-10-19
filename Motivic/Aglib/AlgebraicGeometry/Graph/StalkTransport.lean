/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.AffineEtale
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.StalkTransport

/-!
# Actual graph stalks through open charts

Open charts on both factors over a monomorphism of bases identify the actual
graph stalk arrows. The construction records the literal ambient product map
and its commutation with the graph, for later same-equation coefficient
transport. No flatness condition is imposed on the graph source.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Graph

variable {X Y S : Scheme.{u}}

/-- The actual graph with a specified compatible structural morphism. -/
def morphism (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a) :
    X ⟶ pullback a b :=
  pullback.lift (𝟙 X) f (by simpa using h.symm)

@[reassoc (attr := simp)]
theorem morphism_fst (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a) :
    morphism a b f h ≫ pullback.fst a b = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem morphism_snd (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a) :
    morphism a b f h ≫ pullback.snd a b = f :=
  pullback.lift_snd _ _ _

variable {X' Y' S' : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a)
  (a' : X' ⟶ S') (b' : Y' ⟶ S') (f' : X' ⟶ Y') (h' : f' ≫ b' = a')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (iS : S' ⟶ S)
  (ha : a' ≫ iS = iX ≫ a) (hb : b' ≫ iS = iY ≫ b) (hf : f' ≫ iY = iX ≫ f)

/-- The actual map between graph ambient products induced by the charts. -/
abbrev productMap : pullback a' b' ⟶ pullback a b :=
  pullback.map a' b' a b iX iY iS ha hb

include hf in
set_option backward.isDefEq.respectTransparency false in
/-- The actual product map intertwines the actual graph morphisms. -/
theorem morphism_productMap :
    morphism a' b' f' h' ≫ productMap a b a' b' iX iY iS ha hb =
      iX ≫ morphism a b f h := by
  apply pullback.hom_ext <;> simp [productMap, pullback.map, hf]

set_option backward.isDefEq.respectTransparency false in
/-- Open factor charts over a base monomorphism identify the actual graph stalk arrows. -/
def arrowStalkIsoOfOpenChart [IsOpenImmersion iX] [IsOpenImmersion iY] [Mono iS] (x : X') :
    Arrow.mk ((morphism a b f h).stalkMap (iX x)) ≅
      Arrow.mk ((morphism a' b' f' h').stalkMap x) :=
  Arrow.isoMk'
    ((morphism a b f h).stalkMap (iX x)) ((morphism a' b' f' h').stalkMap x)
    ((pullback a b).presheaf.stalkCongr (.of_eq <| by
      rw [← Scheme.Hom.comp_apply, ← morphism_productMap a b f h a' b' f' h'
        iX iY iS ha hb hf]
      rfl) ≪≫ asIso ((productMap a b a' b' iX iY iS ha hb).stalkMap
        (morphism a' b' f' h' x)))
    (asIso (iX.stalkMap x)) (by
      simp only [Iso.trans_hom, asIso_hom, Category.assoc, ← Scheme.Hom.stalkMap_comp]
      exact (Scheme.Hom.stalkMap_congr_hom _ _
        (morphism_productMap a b f h a' b' f' h' iX iY iS ha hb hf).symm x).symm)

end AlgebraicGeometry.Scheme.Graph
