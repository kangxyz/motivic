/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Sheafification.MatchingPairExtension
public import Motivic.Transfers.Presheaf.Sheafification.Image
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.SectionDetection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Projection


/-!
# Whole-cylinder image lifting from explicit middle relations

This assembly consumes, but does not construct, the four simultaneous middle
relations on an actual cover after a further open restriction of the base.
Only the actual sheafification is glued or detected as a sheaf. The image
presheaf section is explicitly obtained by a correspondence action.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- Explicit simultaneous middle identities yield an actual image representative
on the whole cylinder over the further original-base open. The identities and
cover are inputs, not conclusions of this conditional assembly theorem. -/
theorem nisnevichImage_wholeCylinder_lift_of_middle_relations
    (P : PresheafWithTransfers.{u + 1} k)
    {X U U' T A V B A' V' : SmoothSite (Spec (.of k))}
    (j : U ⟶ X) (l : U' ⟶ U) [IsOpenImmersion j.left] [IsOpenImmersion l.left]
    (hne : Nonempty U'.left) (e : T ≅ SmoothSite.a1Cylinder (.of k) U)
    (h : SmoothSite.a1Cylinder (.of k) U' ⟶ T)
    (he : h ≫ e.hom = SmoothSite.a1Map (.of k) l)
    (i : A ⟶ T) (v : V ⟶ T) (bA : B ⟶ A) (bV : B ⟶ V)
    (i' : A' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (v' : V' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (rA : A' ⟶ A) (rV : V' ⟶ V)
    (hi : rA ≫ i = i' ≫ h) (hv : rV ≫ v = v' ≫ h)
    (hcover : Sieve.ofTwoArrows i' v' ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (SmoothSite.a1Cylinder (.of k) U'))
    (lambdaA : Cor.mk (SmoothSite.a1Cylinder (.of k) U') ⟶ Cor.mk A)
    (lambdaB : Cor.mk V' ⟶ Cor.mk B) (ψ : Cor.mk A' ⟶ Cor.mk B)
    (hBu : (nisnevichImage P).transfer (lambdaB ≫ (Cor.graphFunctor k).map bV) =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map rV))
    (hBg : (nisnevichImage P).transfer (lambdaB ≫ (Cor.graphFunctor k).map bA) =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map v' ≫ lambdaA))
    (hψu : (nisnevichImage P).transfer (ψ ≫ (Cor.graphFunctor k).map bV) = 0)
    (hA : (nisnevichImage P).transfer
      (Sub.sub (α := Cor.mk A' ⟶ Cor.mk A)
        ((Cor.graphFunctor k).map i' ≫ lambdaA)
        (ψ ≫ (Cor.graphFunctor k).map bA)) =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map rA))
    (g : ((nisnevichSheafify k).obj P).obj.sections
      (Cor.mk (SmoothSite.a1Cylinder (.of k) X)))
    (sA : (nisnevichImage P).sections (Cor.mk A))
    (sV : (nisnevichImage P).sections (Cor.mk V))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bA) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bV) sV)
    (huA : (nisnevichImageι P).hom.app (op (Cor.mk A)) sA =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (i ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g)
    (huV : (nisnevichImageι P).hom.app (op (Cor.mk V)) sV =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (v ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g) :
    IsOpenImmersion (l ≫ j).left ∧ Nonempty U'.left ∧
      ∃ t : (nisnevichImage P).sections (Cor.mk (SmoothSite.a1Cylinder (.of k) U')),
        (nisnevichImageι P).hom.app (op (Cor.mk (SmoothSite.a1Cylinder (.of k) U'))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) (l ≫ j))) g := by
  let S := nisnevichImage P
  let G := ((nisnevichSheafify k).obj P).obj
  let η := nisnevichImageι P
  let t := S.transfer lambdaA sA
  obtain ⟨htA, htV⟩ := transfer_matchingPair_extension S
    ((Cor.graphFunctor k).map bA) ((Cor.graphFunctor k).map bV)
    ((Cor.graphFunctor k).map i') ((Cor.graphFunctor k).map v')
    ((Cor.graphFunctor k).map rA) ((Cor.graphFunctor k).map rV)
    lambdaA lambdaB ψ hBu hBg hψu hA sA sV hm
  have hrestr {D E : SmoothSite (Spec (.of k))}
      (d : D ⟶ SmoothSite.a1Cylinder (.of k) U') (r : D ⟶ E) (c : E ⟶ T)
      (hr : r ≫ c = d ≫ h) (s : S.sections (Cor.mk E))
      (ht : S.transfer ((Cor.graphFunctor k).map d) t =
        S.transfer ((Cor.graphFunctor k).map r) s)
      (hu : η.hom.app (op (Cor.mk E)) s =
        G.transfer ((Cor.graphFunctor k).map (c ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g) :
      G.transfer ((Cor.graphFunctor k).map d)
          (η.hom.app (op (Cor.mk (SmoothSite.a1Cylinder (.of k) U'))) t) =
        G.transfer ((Cor.graphFunctor k).map d)
          (G.transfer ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) (l ≫ j))) g) := by
    have hn (Q W : SmoothSite (Spec (.of k))) (a : Q ⟶ W)
        (s : S.sections (Cor.mk W)) :
        η.hom.app (op (Cor.mk Q)) (S.transfer ((Cor.graphFunctor k).map a) s) =
          G.transfer ((Cor.graphFunctor k).map a) (η.hom.app (op (Cor.mk W)) s) :=
      η.hom.naturality_apply ((Cor.graphFunctor k).map a).op s
    rw [← hn _ _ d t, ht, hn _ _ r s, hu]
    have hmorph : r ≫ c ≫ e.hom ≫ SmoothSite.a1Map (.of k) j =
        d ≫ SmoothSite.a1Map (.of k) (l ≫ j) := by
      rw [← Category.assoc r, hr, Category.assoc, ← Category.assoc h, he,
        SmoothSite.a1Map_comp]
    have hh := congrArg (fun m => G.transfer ((Cor.graphFunctor k).map m) g) hmorph
    simpa only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] using hh
  have hleft := hrestr i' rA i hi sA htA huA
  have hright := hrestr v' rV v hv sV htV huV
  refine ⟨?_, hne, t, ?_⟩
  · change IsOpenImmersion (l.left ≫ j.left)
    infer_instance
  let F := (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)
  let arrows : ∀ a, pairFunction A' V' a ⟶ SmoothSite.a1Cylinder (.of k) U' :=
    fun a => WalkingPair.casesOn a i' v'
  have hsheaf := ((isSheaf_iff_isSheaf_of_type
    (SmoothSite.nisnevichTopology (Spec (.of k))) _).mp
      ((sheafCompose (SmoothSite.nisnevichTopology (Spec (.of k)))
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F).property).isSheafFor
          (Presieve.ofArrows _ arrows) hcover
  apply hsheaf.isSeparatedFor.ext
  rintro W f ⟨a⟩
  cases a
  · exact hleft
  · exact hright

end Motivic.PresheafWithTransfers
