/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Support.OpenNeighborhoods
public import Motivic.Aglib.AlgebraicGeometry.Intersection.AffineClosedSupportTor

/-!
# Global comparison with the original triple-product support intersection

Over an arbitrary field, the actual diagonal-incidence Tor and the Tor of
both original pulled ideal subschemes in the triple product have the same
length in every degree. The proof restricts the three factors to affine open
neighborhoods, applies the arbitrary-closed-support affine theorem, and
transports the pulled-support Tor back through actual open immersions.

The restricted supports are not asserted to be finite correspondence
 generators. Every stalk comparison uses the original scheme maps. Finite
signed sums require finite-length support explicitly. This comparison is
independent of associativity and does not construct a correspondence category.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.GlobalIncidenceAmbientTorComparison
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Products.OpenNeighborhoods

/-- Tor of the actual coefficient and source stalks at a common ambient point. -/
abbrev stalkTor {D T P : Scheme.{u}} (i : D ⟶ P) (d : D) (j : T ⟶ P)
    (t : T) (hp : i d = j t) (n : ℕ) :=
  ((Tor (ModuleCat (ambientStalk i d)) n).obj
    (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)

/-- The affine closed-support comparison also applies to arbitrary maps from
three spectra to the field spectrum. Their algebra structures are derived
from those exact maps, rather than supplied independently. -/
theorem exists_affineClosedSupportComparison
    (k : Type u) [Field k] (A B C : CommRingCat.{u})
    (f : Spec A ⟶ Spec (.of k)) (g : Spec B ⟶ Spec (.of k))
    (h : Spec C ⟶ Spec (.of k))
    {D E : Scheme.{u}} (a : D ⟶ pullback f g) (b : E ⟶ pullback g h)
    [IsClosedImmersion a] [IsClosedImmersion b]
    (d : correspondenceTripleProduct f g h)
    (t : pullback (C := Scheme.{u}) (a ≫ pullback.snd f g ≫ g) (b ≫ pullback.fst g h ≫ g))
    (hp : correspondenceTripleInclusion f g h d =
      (pullback.map (a ≫ pullback.snd f g ≫ g) (b ≫ pullback.fst g h ≫ g)
        (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)
        a b (𝟙 (Spec (.of k))) (by simp) (by simp)) t) :
    ∃ l : pullback (C := Scheme.{u}) (pullback.fst (pullback.snd f g) (pullback.fst g h)) a,
    ∃ r : pullback (C := Scheme.{u}) (pullback.snd (pullback.snd f g) (pullback.fst g h)) b,
    ∃ hl : pullback.fst (pullback.fst (pullback.snd f g) (pullback.fst g h)) a l = d,
    ∃ hr : pullback.fst (pullback.snd (pullback.snd f g) (pullback.fst g h)) b r = d,
    ∀ n : ℕ,
      Module.length (ambientStalk (correspondenceTripleInclusion f g h) d)
        (stalkTor (correspondenceTripleInclusion f g h) d
          (pullback.map (a ≫ pullback.snd f g ≫ g) (b ≫ pullback.fst g h ≫ g)
            (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)
            a b (𝟙 (Spec (.of k))) (by simp) (by simp)) t hp n) =
      Module.length
        (ambientStalk (pullback.fst (pullback.snd (pullback.snd f g) (pullback.fst g h)) b) r)
        (stalkTor (pullback.fst (pullback.snd (pullback.snd f g) (pullback.fst g h)) b) r
          (pullback.fst (pullback.fst (pullback.snd f g) (pullback.fst g h)) a) l
          (hr.trans hl.symm) n) := by
  rcases A with ⟨A, hA⟩
  rcases B with ⟨B, hB⟩
  rcases C with ⟨C, hC⟩
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  obtain ⟨h, rfl⟩ := Spec.map_surjective h
  rcases f with ⟨f⟩
  rcases g with ⟨g⟩
  rcases h with ⟨h⟩
  let ambientAlgebraA : Algebra k A := f.toAlgebra
  let ambientAlgebraB : Algebra k B := g.toAlgebra
  let ambientAlgebraC : Algebra k C := h.toAlgebra
  exact MiddleDiagonal.ClosedSupport.exists_stalkTor_length_eq_pulled k A B C a b d t hp

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)

/-- The original left ideal support pulled into the original triple product. -/
abbrev leftPulledInclusion :=
  (F.val.comap (pullback.fst (pullback.snd f g) (pullback.fst g h))).subschemeι

/-- The original right ideal support pulled into the original triple product. -/
abbrev rightPulledInclusion :=
  (G.val.comap (pullback.snd (pullback.snd f g) (pullback.fst g h))).subschemeι

/-- The original incidence map to the original left pulled ideal subscheme. -/
def toLeftPulled : F.incidence G ⟶
    (F.val.comap (pullback.fst (pullback.snd f g) (pullback.fst g h))).subscheme :=
  pullback.lift (F.incidenceInclusion G) (F.incidenceFst G) (F.incidenceInclusion_fst G) ≫
    (F.val.comapIso _).inv

/-- The original incidence map to the original right pulled ideal subscheme. -/
def toRightPulled : F.incidence G ⟶
    (G.val.comap (pullback.snd (pullback.snd f g) (pullback.fst g h))).subscheme :=
  pullback.lift (F.incidenceInclusion G) (F.incidenceSnd G) (F.incidenceInclusion_snd G) ≫
    (G.val.comapIso _).inv

@[reassoc (attr := simp)] theorem toLeftPulled_inclusion :
    toLeftPulled F G ≫ leftPulledInclusion F = F.incidenceInclusion G := by
  simp [toLeftPulled, leftPulledInclusion]

@[reassoc (attr := simp)] theorem toRightPulled_inclusion :
    toRightPulled F G ≫ rightPulledInclusion G = F.incidenceInclusion G := by
  simp [toRightPulled, rightPulledInclusion]

/-- The two actual pulled-support points have precisely the same ambient image. -/
theorem pulledPoint_eq (w : F.incidence G) :
    rightPulledInclusion G (toRightPulled F G w) =
      leftPulledInclusion F (toLeftPulled F G w) :=
  (congrArg (fun m ↦ m w) (toRightPulled_inclusion F G)).trans
    (congrArg (fun m ↦ m w) (toLeftPulled_inclusion F G)).symm

/-- The original triple-product Tor, with the left pulled support as coefficient
and the right pulled support as source. No affine chart appears in its definition. -/
abbrev pulledStalkTor (w : F.incidence G) (n : ℕ) :=
  stalkTor (rightPulledInclusion G) (toRightPulled F G w)
    (leftPulledInclusion F) (toLeftPulled F G w) (pulledPoint_eq F G w) n

section OpenNeighborhood

variable {X' Y' Z' : Scheme.{u}}
  (uX : X' ⟶ X) (uY : Y' ⟶ Y) (uZ : Z' ⟶ Z)

/-- The actual local left pulled support, with no finiteness-over-source claim. -/
abbrev openLeftPulled :=
  pullback (pullback.fst (pullback.snd (uX ≫ f) (uY ≫ g))
    (pullback.fst (uY ≫ g) (uZ ≫ h))) (F.openSupportInclusion uX uY)

/-- The actual local right pulled support. -/
abbrev openRightPulled :=
  pullback (pullback.snd (pullback.snd (uX ≫ f) (uY ≫ g))
    (pullback.fst (uY ≫ g) (uZ ≫ h))) (G.openSupportInclusion uY uZ)

/-- The local left pulled support maps to the original ideal subscheme through
its canonical Cartesian comparison. -/
def openLeftPulledMap : openLeftPulled (h := h) F uX uY uZ ⟶
    (F.val.comap (pullback.fst (pullback.snd f g) (pullback.fst g h))).subscheme :=
  pullback.map _ _ _ _ (tripleMap f g h uX uY uZ) (F.openSupportMap uX uY)
    (productMap f g uX uY) (tripleMap_fst f g h uX uY uZ).symm
    (F.openSupport_square uX uY) ≫ (F.val.comapIso _).inv

/-- The local right pulled support retains the original ideal-subscheme inclusion. -/
def openRightPulledMap : openRightPulled (f := f) G uX uY uZ ⟶
    (G.val.comap (pullback.snd (pullback.snd f g) (pullback.fst g h))).subscheme :=
  pullback.map _ _ _ _ (tripleMap f g h uX uY uZ) (G.openSupportMap uY uZ)
    (productMap g h uY uZ) (tripleMap_snd f g h uX uY uZ).symm
    (G.openSupport_square uY uZ) ≫ (G.val.comapIso _).inv

instance [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ] :
    IsOpenImmersion (openLeftPulledMap (h := h) F uX uY uZ) := by
  unfold openLeftPulledMap
  infer_instance

instance [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ] :
    IsOpenImmersion (openRightPulledMap (f := f) G uX uY uZ) := by
  unfold openRightPulledMap
  infer_instance

@[reassoc] theorem openLeftPulledMap_inclusion :
    openLeftPulledMap (h := h) F uX uY uZ ≫ leftPulledInclusion F =
      pullback.fst
        (pullback.fst (pullback.snd (uX ≫ f) (uY ≫ g))
          (pullback.fst (uY ≫ g) (uZ ≫ h))) (F.openSupportInclusion uX uY) ≫
        tripleMap f g h uX uY uZ := by
  simp [openLeftPulledMap, leftPulledInclusion, pullback.map]

@[reassoc] theorem openRightPulledMap_inclusion :
    openRightPulledMap (f := f) G uX uY uZ ≫ rightPulledInclusion G =
      pullback.fst
        (pullback.snd (pullback.snd (uX ≫ f) (uY ≫ g))
          (pullback.fst (uY ≫ g) (uZ ≫ h))) (G.openSupportInclusion uY uZ) ≫
        tripleMap f g h uX uY uZ := by
  simp [openRightPulledMap, rightPulledInclusion, pullback.map]

/-- A point on the local left pulled support over the chosen triple point
maps to the original incidence point of the original pulled ideal subscheme. -/
theorem openLeftPulledMap_point (w : F.incidence G)
    (q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h))
    (hq : tripleMap f g h uX uY uZ q = F.incidenceInclusion G w)
    (l : openLeftPulled (h := h) F uX uY uZ) (hl : pullback.fst
      (pullback.fst (pullback.snd (uX ≫ f) (uY ≫ g))
        (pullback.fst (uY ≫ g) (uZ ≫ h))) (F.openSupportInclusion uX uY) l = q) :
    openLeftPulledMap (h := h) F uX uY uZ l = toLeftPulled F G w := by
  apply (leftPulledInclusion F).isClosedEmbedding.injective
  calc
    leftPulledInclusion F (openLeftPulledMap (h := h) F uX uY uZ l) =
        tripleMap f g h uX uY uZ (pullback.fst
          (pullback.fst (pullback.snd (uX ≫ f) (uY ≫ g))
            (pullback.fst (uY ≫ g) (uZ ≫ h))) (F.openSupportInclusion uX uY) l) :=
      congrArg (fun m ↦ m l) (openLeftPulledMap_inclusion (h := h) F uX uY uZ)
    _ = F.incidenceInclusion G w := by rw [hl, hq]
    _ = leftPulledInclusion F (toLeftPulled F G w) :=
      (congrArg (fun m ↦ m w) (toLeftPulled_inclusion F G)).symm

/-- The corresponding actual point identity for the right support. -/
theorem openRightPulledMap_point (w : F.incidence G)
    (q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h))
    (hq : tripleMap f g h uX uY uZ q = F.incidenceInclusion G w)
    (r : openRightPulled (f := f) G uX uY uZ) (hr : pullback.fst
      (pullback.snd (pullback.snd (uX ≫ f) (uY ≫ g))
        (pullback.fst (uY ≫ g) (uZ ≫ h))) (G.openSupportInclusion uY uZ) r = q) :
    openRightPulledMap (f := f) G uX uY uZ r = toRightPulled F G w := by
  apply (rightPulledInclusion G).isClosedEmbedding.injective
  calc
    rightPulledInclusion G (openRightPulledMap (f := f) G uX uY uZ r) =
        tripleMap f g h uX uY uZ (pullback.fst
          (pullback.snd (pullback.snd (uX ≫ f) (uY ≫ g))
            (pullback.fst (uY ≫ g) (uZ ≫ h))) (G.openSupportInclusion uY uZ) r) :=
      congrArg (fun m ↦ m r) (openRightPulledMap_inclusion (f := f) G uX uY uZ)
    _ = F.incidenceInclusion G w := by rw [hr, hq]
    _ = rightPulledInclusion G (toRightPulled F G w) :=
      (congrArg (fun m ↦ m w) (toRightPulled_inclusion F G)).symm

end OpenNeighborhood

section Field

variable (k : Type u) [Field k]
  {X Y Z : Scheme.{u}} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
  {h : Z ⟶ Spec (.of k)}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)

/-- The original diagonal-incidence and original triple-product pulled-support
Tor have equal lengths in every degree over an arbitrary field. The schemes
need not be affine or smooth, and no finite-length hypothesis is needed. -/
theorem incidenceTor_length_eq_pulled (w : F.incidence G) (n : ℕ) :
    Module.length (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) =
      Module.length (ambientStalk (rightPulledInclusion G) (toRightPulled F G w))
        (pulledStalkTor F G w n) := by
  obtain ⟨A, B, C, uX, uY, uZ, hx, hy, hz, q, hq⟩ :=
    exists_affineTripleNeighborhood f g h (F.incidenceInclusion G w)
  let ambientOpenX := hx
  let ambientOpenY := hy
  let ambientOpenZ := hz
  obtain ⟨t, ht, hp⟩ := F.exists_openSupportProductPoint G uX uY uZ w q hq
  obtain ⟨l, r, hl, hr, hlen⟩ := exists_affineClosedSupportComparison k A B C
    (uX ≫ f) (uY ≫ g) (uZ ≫ h)
    (F.openSupportInclusion uX uY) (G.openSupportInclusion uY uZ) q t hp
  have hleft := openLeftPulledMap_point F G uX uY uZ w q hq l hl
  have hright := openRightPulledMap_point F G uX uY uZ w q hq r hr
  have hPulled := neighborhoodStalkTor_length
    (rightPulledInclusion G) (toRightPulled F G w)
    (leftPulledInclusion F) (toLeftPulled F G w) (pulledPoint_eq F G w)
    (pullback.fst
      (pullback.snd (pullback.snd (uX ≫ f) (uY ≫ g))
        (pullback.fst (uY ≫ g) (uZ ≫ h))) (G.openSupportInclusion uY uZ)) r
    (pullback.fst
      (pullback.fst (pullback.snd (uX ≫ f) (uY ≫ g))
        (pullback.fst (uY ≫ g) (uZ ≫ h))) (F.openSupportInclusion uX uY)) l
    (hr.trans hl.symm)
    (openRightPulledMap (f := f) G uX uY uZ) (openLeftPulledMap (h := h) F uX uY uZ)
    (tripleMap f g h uX uY uZ)
    (openRightPulledMap_inclusion (f := f) G uX uY uZ)
    (openLeftPulledMap_inclusion (h := h) F uX uY uZ) hright.symm hleft.symm n
  exact (F.openIncidenceStalkTor_length G uX uY uZ w q t hq ht hp n).trans
    ((hlen n).trans hPulled.symm)

/-- Genuine finite local lengths and finite degree support transfer in both directions. -/
theorem incidenceTor_finiteLengthSupport_iff_pulled (w : F.incidence G) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport (F.incidenceTor G w) ↔
      _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport (pulledStalkTor F G w) := by
  have hlen := funext (incidenceTor_length_eq_pulled k F G w)
  constructor
  · intro hfin
    refine ⟨?_, ?_⟩
    · intro n
      rw [← incidenceTor_length_eq_pulled k F G w n]
      exact hfin.finite_length n
    · simpa only [hlen] using hfin.finite_support
  · intro hfin
    refine ⟨?_, ?_⟩
    · intro n
      rw [incidenceTor_length_eq_pulled k F G w n]
      exact hfin.finite_length n
    · simpa only [hlen] using hfin.finite_support

/-- Every signed Euler coefficient agrees for the original two ambient models,
with actual finite-length and finite-degree evidence retained. -/
theorem incidenceTor_signedLengthSum_eq_pulled (w : F.incidence G) (sign : ℕ → ℤ)
    (hfin : _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport (F.incidenceTor G w)) :
    _root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum (F.incidenceTor G w) sign hfin =
      _root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum (pulledStalkTor F G w) sign
        ((incidenceTor_finiteLengthSupport_iff_pulled k F G w).mp hfin) := by
  unfold _root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum
  apply finsum_congr
  intro n
  simp only [_root_.HomologicalComplex.ModuleLengthEuler.integerLength,
      incidenceTor_length_eq_pulled k F G w n]

end Field

end Motivic.GlobalIncidenceAmbientTorComparison
