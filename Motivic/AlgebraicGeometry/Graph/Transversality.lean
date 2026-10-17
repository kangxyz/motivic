/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Graph.Smooth
public import Motivic.AlgebraicGeometry.Graph.AffineTransversality
public import Motivic.AlgebraicGeometry.Graph.OpenTransversality

/-!
# A common regular diagonal list on every actual smooth-target graph

For an arbitrary map `X → Y`, with `Y → S` smooth, one finite regular list
in the actual diagonal stalk generates its kernel and has regular literal
images in the actual graph ambient stalk. The same smooth polynomial chart
is used for both lists, then simultaneous open-chart transport identifies the
actual stalk maps. Neither the source scheme nor its map to `Y` is assumed
flat, reduced, connected, or Noetherian.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.AffineGraph

set_option backward.isDefEq.respectTransparency false in
/-- Standard-smooth target coordinates give a common diagonal list for every affine graph. -/
theorem exists_common_regular_list_of_isStandardSmooth
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : B →ₐ[R] A)
    (hf : (algebraMap R B).IsStandardSmooth)
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R A))) (p : PrimeSpectrum A) :
    ∃ rs : List ((AffineDiagonal.product R B).presheaf.stalk
      (AffineDiagonal.diagonal R B ((Spec.map (CommRingCat.ofHom f.toRingHom)) p))),
      IsRegular ((AffineDiagonal.product R B).presheaf.stalk
        (AffineDiagonal.diagonal R B ((Spec.map (CommRingCat.ofHom f.toRingHom)) p))) rs ∧
      RingHom.ker ((AffineDiagonal.diagonal R B).stalkMap
        ((Spec.map (CommRingCat.ofHom f.toRingHom)) p)).hom = Ideal.ofList rs ∧
      IsRegular ((product R A B).presheaf.stalk
        (Graph.morphism (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom f.toRingHom)) h p))
        (rs.map (Graph.genericDiagonalStalkMap
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (Spec.map (CommRingCat.ofHom f.toRingHom)) h p).hom) := by
  obtain ⟨n, g, hcomp, hg⟩ := hf.exists_etale_mvPolynomial
  let := g.toAlgebra
  let := (f.toRingHom.comp g).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) B :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq' (by
      symm
      change (f.toRingHom.comp g).comp (algebraMap R (MvPolynomial (Fin n) R)) =
        algebraMap R A
      rw [RingHom.comp_assoc, MvPolynomial.algebraMap_eq, hcomp]
      exact f.comp_algebraMap)
  have : Algebra.Etale (MvPolynomial (Fin n) R) B := hg
  let f' : B →ₐ[MvPolynomial (Fin n) R] A :=
    { __ := f.toRingHom, commutes' _ := rfl }
  have heq : graph R (Fin n) A B f' =
      Graph.morphism (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom f.toRingHom)) h :=
    graph_eq_lift R (Fin n) A B f' _
  have ht := etale_common_regular_list R (Fin n) A B f' h p (List.finRange n)
    (List.nodup_finRange n) List.mem_finRange
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let φ := Spec.map (CommRingCat.ofHom f.toRingHom)
  let q := Graph.middlePair a b φ h
  have hq : AffineDiagonal.diagonal R B (φ p) = q (graph R (Fin n) A B f' p) :=
    (congrArg (fun k : Spec (CommRingCat.of A) ⟶ AffineDiagonal.product R B => k p)
      (graph_middlePair R (Fin n) A B f' h)).symm
  have hq' : AffineDiagonal.diagonal R B (φ p) = q (Graph.morphism a b φ h p) :=
    (congrArg (fun k : Spec (CommRingCat.of A) ⟶ AffineDiagonal.product R B => k p)
      (Graph.morphism_middlePair a b φ h)).symm
  have ht' := Graph.common_regular_list_congr_coefficient_point
    (AffineDiagonal.diagonal R B) q (φ p) (graph R (Fin n) A B f' p)
    (Graph.morphism a b φ h p) (congrArg (fun k => k p) heq) hq hq' (by
      simpa only [a, b, φ, q, f', diagonalStalkMap] using ht)
  simpa only [a, b, φ, q, Graph.genericDiagonalStalkMap, AffineDiagonal.diagonal] using ht'

end Motivic.AffineGraph

namespace Motivic.Graph

set_option backward.isDefEq.respectTransparency false in
/-- One actual regular diagonal-kernel list stays regular on any graph into a smooth target. -/
theorem exists_common_regular_list_of_smooth {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [Smooth g] (x : X) :
    ∃ rs : List ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))) rs ∧
      RingHom.ker ((pullback.diagonal g).stalkMap (f x)).hom = Ideal.ofList rs ∧
      IsRegular ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x))
        (rs.map (diagonalStalkMap f g x).hom) := by
  obtain ⟨U, hU, V, hV, hxV, hVU, hg⟩ := Smooth.exists_isStandardSmooth g (f x)
  obtain ⟨W, hW, hxW, hWV⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ V from hxV)
  obtain ⟨p, hp⟩ : x ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    exact hxW
  let g₀ := (g.appLE U V hVU).hom
  let f₀ := (f.appLE V W hWV).hom
  let := g₀.toAlgebra
  let := (f₀.comp g₀).toAlgebra
  let fA : Γ(Y, V) →ₐ[Γ(S, U)] Γ(X, W) :=
    { __ := f₀, commutes' _ := rfl }
  let a₀ := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) Γ(X, W)))
  let b₀ := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) Γ(Y, V)))
  let φ₀ := Spec.map (CommRingCat.ofHom fA.toRingHom)
  have h₀ : φ₀ ≫ b₀ = a₀ := by
    rw [← Spec.map_comp]
    rfl
  have hb : b₀ ≫ hU.fromSpec = hV.fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hU hV hVU
  have hφ : φ₀ ≫ hV.fromSpec = hW.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV
  have ha : a₀ ≫ hU.fromSpec = hW.fromSpec ≫ (f ≫ g) := by
    rw [← h₀, Category.assoc, hb, ← Category.assoc, hφ, Category.assoc]
  have hlocal := AffineGraph.exists_common_regular_list_of_isStandardSmooth
    Γ(S, U) Γ(X, W) Γ(Y, V) fA hg h₀ p
  have ht := common_regular_list_of_openChart (f ≫ g) g f rfl a₀ b₀ φ₀ h₀
    hW.fromSpec hV.fromSpec hU.fromSpec ha hb hφ p hlocal
  subst x
  simp only [morphism_eq_correspondenceGraph,
    genericDiagonalStalkMap_eq_diagonalStalkMap] at ht
  convert! ht using 1

end Motivic.Graph
