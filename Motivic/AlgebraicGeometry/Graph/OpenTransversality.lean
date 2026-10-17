/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Graph.Pair
public import Motivic.AlgebraicGeometry.Graph.PointTransport

/-!
# Common diagonal equations through graph open charts

The same local diagonal equation list is transported simultaneously through
open charts of the diagonal and graph ambient products. The proof uses the
literal commuting product maps, including their actual stalk point casts.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.Graph

variable {X Y S X' Y' S' : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a)
  (a' : X' ⟶ S') (b' : Y' ⟶ S') (f' : X' ⟶ Y') (h' : f' ≫ b' = a')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (iS : S' ⟶ S)
  (ha : a' ≫ iS = iX ≫ a) (hb : b' ≫ iS = iY ≫ b) (hf : f' ≫ iY = iX ≫ f)

include ha hb hf in
set_option backward.isDefEq.respectTransparency false in
/-- A common regular diagonal list and its graph regularity survive actual open charts. -/
theorem common_regular_list_of_openChart
    [IsOpenImmersion iX] [IsOpenImmersion iY] [Mono iS] (x : X')
    (hlocal : ∃ rs : List ((pullback b' b').presheaf.stalk (pullback.diagonal b' (f' x))),
      IsRegular ((pullback b' b').presheaf.stalk (pullback.diagonal b' (f' x))) rs ∧
      RingHom.ker ((pullback.diagonal b').stalkMap (f' x)).hom = Ideal.ofList rs ∧
      IsRegular ((pullback a' b').presheaf.stalk (morphism a' b' f' h' x))
        (rs.map (genericDiagonalStalkMap a' b' f' h' x).hom)) :
    ∃ rs : List ((pullback b b).presheaf.stalk (pullback.diagonal b (f (iX x)))),
      IsRegular ((pullback b b).presheaf.stalk (pullback.diagonal b (f (iX x)))) rs ∧
      RingHom.ker ((pullback.diagonal b).stalkMap (f (iX x))).hom = Ideal.ofList rs ∧
      IsRegular ((pullback a b).presheaf.stalk (morphism a b f h (iX x)))
        (rs.map (genericDiagonalStalkMap a b f h (iX x)).hom) := by
  let iP := Diagonal.productMap b b' iY iS hb
  let iQ := productMap a b a' b' iX iY iS ha hb
  let p := pullback.diagonal b' (f' x)
  let z := morphism a' b' f' h' x
  have hi : pullback.diagonal b' ≫ iP = iY ≫ pullback.diagonal b :=
    Diagonal.diagonal_productMap b b' iY iS hb
  have hq : middlePair a' b' f' h' ≫ iP = iQ ≫ middlePair a b f h :=
    middlePair_productMap a b f h a' b' f' h' iX iY iS ha hb hf
  have hzq : p = middlePair a' b' f' h' z :=
    (congrArg (fun k : X' ⟶ pullback b' b' => k x) (morphism_middlePair a' b' f' h')).symm
  have hdi' : iP p = pullback.diagonal b (iY (f' x)) :=
    congrArg (fun k : Y' ⟶ pullback b b => k (f' x)) hi
  have hzq' : iP p = middlePair a b f h (iQ z) := by
    rw [hzq]
    exact congrArg (fun k : pullback a' b' ⟶ pullback b b => k z) hq
  have ht := exists_regular_kernel_and_regular_image_of_openCharts
    (pullback.diagonal b) (middlePair a b f h)
    (pullback.diagonal b') (middlePair a' b' f' h') iY iQ iP hi hq
    (f' x) z p rfl hzq hdi' hzq' (by
      simpa only [p, z, genericDiagonalStalkMap, alignedStalkMap_rfl] using hlocal)
  have hy : iY (f' x) = f (iX x) :=
    congrArg (fun k : X' ⟶ Y => k x) hf
  have hp : iP p = pullback.diagonal b (f (iX x)) := hdi'.trans (congrArg _ hy)
  have hz : iQ z = morphism a b f h (iX x) :=
    congrArg (fun k : X' ⟶ pullback a b => k x)
      (morphism_productMap a b f h a' b' f' h' iX iY iS ha hb hf)
  have hzfinal : pullback.diagonal b (f (iX x)) =
      middlePair a b f h (morphism a b f h (iX x)) :=
    (congrArg (fun k : X ⟶ pullback b b => k (iX x)) (morphism_middlePair a b f h)).symm
  have ht' := common_regular_list_congr_points (pullback.diagonal b) (middlePair a b f h)
    (iY (f' x)) (f (iX x)) (iQ z) (morphism a b f h (iX x))
    (iP p) (pullback.diagonal b (f (iX x))) hy hz hp hdi' hzq' rfl hzfinal ht
  simpa only [genericDiagonalStalkMap, alignedStalkMap_rfl] using ht'

end Motivic.Graph
