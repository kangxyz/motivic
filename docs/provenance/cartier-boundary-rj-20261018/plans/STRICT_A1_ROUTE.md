# Strict A1: current proof contracts

Status at 2026-10-18 01:36 UTC. This supplements, rather than rewrites, the
historical research records in `provenance/`. The final strict A1 theorem is
**open**. A compiled conditional interface is not its missing producer.

## Target and scope

For the original HI Nisnevich sheaf with transfers F, identify the actual
projection pullback on every ordinary Nisnevich cohomology group as an
isomorphism. The first intended assembly is over infinite perfect fields.
Finite fields require a separate descent proof; perfectness alone does not
supply infinitude or perfectness of function fields. Coefficient universes
and ordinary `HasExt` inputs remain explicit.

## Inputs already available

- Original ordinary cohomology with transfers, including graph maps.
- Actual finite-etale point fibers as filtered colimits of original
  neighborhood cohomology, retaining the marked point and projection.
- Finite-degree Leray edge interfaces with explicit higher-image hypotheses.
- Actual relative-line generic-base vanishing in every positive degree for
  HI transfer sheaves over any field and smooth domain base. The whole line
  is retained; the base open depends on the original class. The H1 and
  all-positive terminal consumers and standard-foundations audits passed.
- Actual smooth Cartier choice on an affine neighborhood of any
  positive-local-dimension point over a perfect field. It is not a global
  divisor on the original scheme. Its terminal audit passed.
- Lower-rank punctured-fiber vanishing, conditional on the precise lower-rank
  hypothesis and the independently required original restriction monomorphism.

Other inherited inputs retain the scopes recorded in `INTERFACES.md` and the
source. These statements do not imply full strict A1 on their own.

## 1. Rank-zero fiber

1. Transport generic-base vanishing from the affine ring model to the actual
   smooth-site cylinder using the existing affine-coordinate isomorphisms.
   The output must be zero under `a1Map` of the actual open inclusion.
2. For an arbitrary field-valued mark of local rank zero, refine its actual
   etale neighborhood to an integral affine neighborhood whose generic point
   is that mark. Preserve the entire field-valued morphism, not only its image.
3. Kill each original filtered-colimit representative using step 1, without
   changing the original point-index category.
4. Apply the existing actual higher-image fiber comparison.

The model vanishing, actual cylinder transport and original-index rank-zero
join are accepted, including the four unconditional positive-degree endpoints
for arbitrary field-valued marks, residue marks and actual higher-image fibers.
No generic-vanishing family remains as an input to the final rank-zero results.

## 2. Canonical boundary comparison

For a sheaf coefficient F, the target is the genuine closed inverse image of
`coker(F|Y -> j_*F|U)`, and the source is the original contraction sheaf.

- **Mono:** a zero boundary Laurent representative extends on an actual etale
  neighborhood with a residue-field splitting. Rebase the local cylinder to
  that neighborhood, glue across its Nisnevich square, and use separatedness
  of the contraction sheaf. The canonical Mono theorem and its terminal consumer, mechanical transitive
  standard-axiom audit and focused declaration/text/source checks pass over
  every field.
- **Epi for arbitrary HI presheaves P:** first form the original objectwise
  quotient `P(W) / image(P(ambient W))`, then sheafify and take the genuine
  closed inverse image. Original etale local correction and whole-zero base
  shrinking must provide an actual covering image sieve. The final Epi is open.
- **Sheaf specialization:** identify this presheaf-based boundary with the
  sheaf-based boundary for F, using preservation of cokernels by sheafification
  and the sheafification unit isomorphism. This comparison and its exact
  canonical-map square are accepted. Combining it with Mono still requires
  the original-presheaf Epi producer, which is not yet accepted.

Sheafifying P before forming the punctured neighborhood quotient is invalid.
A supplied local-lifting family or a different abstract boundary is insufficient.

## 3. Positive-cohomology boundary vanishing

For positive q, assume precisely the degree-wise induction making the original
`P_q = H^q(-, F)` homotopy invariant.

1. Existing actual torus-model germ vanishing and generic detection should
   imply that the transfer-preserving sheafification of its contraction is zero.
2. Transfer this conclusion to the **small-site ordinary sheafification** of
   the restricted contraction, which is the source of the presheaf boundary map.
   The canonical big ordinary/transfer sheafification comparison already exists
   in `NisnevichSheafification`; the required small-site zero result is now
   accepted using literal small covering families. No unconditional
   restriction/sheafification commutation is assumed.
3. Apply the actual presheaf Epi, then etale excision and the smooth Cartier
   cylinder chart, to obtain the original boundary vanishing.
4. Prefer the smaller actual point-fiber comparison to a new global
   recollement theorem: point fibers preserve the original cokernel,
   sheafification preserves its fibers, ambient positive cohomology germs
   vanish, and the punctured term has the existing ordinary derived-section
   colimit comparison. Pin the isomorphism by its value on every original
   punctured representative. At a closed-support point factor the field mark
   through the actual divisor and use genuine inverse-image composition and
   its point-fiber comparison. On the open side use the actual open lift and
   ordinary local effacement. These joins are still proof obligations, not a
   consequence of a similarly named cokernel definition.

The big contraction zero-sheaf and exact small-source zero consumers are now
accepted over infinite fields, with the current positive-degree HI premise
explicit. The small proof uses literal small covering families. The
actual Cartier/higher-direct-image join is now accepted with original EPI-P
and current-degree HI explicit. The boundary Epi producer remains open.

## 4. Original puncture restriction Mono

The original coefficient restriction F -> j_*j^*F is now proved monic over
infinite fields for actual HI transfer coefficients. Its accepted endpoint
includes actual Cartier-complement density and dense-open detection on etale
test objects followed by F's separatedness. This is not the positive-degree
cohomological restriction Mono.

Then use the sheaf boundary isomorphism, its actual product naturality and the
higher-open-direct-image vanishing from section 3. Work on the actual
Cartier cylinder chart and transport back through marked neighborhoods. The
public Cartier choice only exposes a locally rank-one ideal; a global
untwisted contraction identification would additionally require checked
coordinate/orientation independence. That theorem is not silently assumed. The coefficient induction
must quantify over **all** HI Nisnevich transfer sheaves, including F's
contraction. The degree-one case additionally needs the actual local-point
surjectivity statement; finite-stage global sections are not automatically
exact. Identify the resulting composite with the original puncture restriction
on the unchanged marked-neighborhood colimit.

The LES left coefficient is the actual ambient cokernel C, not automatically
its closed inverse image. The exact split-Noetherian support unit, closed
direct-image exactness and original ordinary-cohomology comparison are now accepted,
including marked-neighborhood initiality and original direct-image point fibers.
Their application to the Cartier pointed system still requires chart/product
naturality, free-source coherence and product-preserving BASE refinement.
Choose the split Cartier chart before multiplying by the homotopy line; an
arbitrary neighborhood inside that line need not retain product shape. A proof
that the original marked relativeForget map is zero would also suffice, but
existing relative lifting and contraction-image/kernel statements do not prove
that assertion.

This is independent of the contraction-to-boundary Mono. Substituting the latter
for this cohomological restriction Mono would leave a gap.

## 5. Rank and degree induction

Smooth stalk dimension has a finite natural-number representative. The actual
open-localization comparison and positive-rank Cartier reduction are now
accepted, with their terminal consumer and focused checks. Positive rank uses
an actual open containing the mark, its chosen Cartier divisor and the original
marked cylinder fibers; the independent restriction Mono is still explicit. Lower-rank
vanishing plus section 4 kills the original class. Rank zero uses section 1.
Then the existing point detection and finite-degree Leray projection comparison
must yield the original global pullback isomorphism, degree by degree.

No abstract group isomorphism, assumed continuity family, supplied purity or
higher-image vanishing may replace these actual-map joins.

## Acceptance and finite fields

Each completed endpoint receives its actual public consumer, mechanical
transitive standard-axiom audit and applicable focused lint/source checks.
Development uses incremental compilation; unchanged dependencies are not
replayed to manufacture new receipts. Source deliveries distinguish accepted
endpoints from candidates.

After the infinite-perfect-field assembly, finite-field descent still needs
actual coprime extension choices, geometry preserving the original selected
point, common base shrinking, finite-transfer trace/degree compatibility and
Bezout descent. No finite-field theorem is inferred from the infinite branch.

## Current production joins awaiting acceptance

- The Epi producer now has a source-level assembly from the actual integral
  whole-zero refinement, polynomial closed point, both HI corrections and
  geometric image sieve to genuine open neighborhoods of each original
  closed point. Its Laurent/cylinder compatibility and downstream consumers
  still require successful compilation. No Epi completion follows from the
  presence of this endpoint source.
- Genuine inverse-image composition on arbitrary full field-valued point
  fibers has production compilation evidence. The original quotient-to-
  higher-direct-image point comparison and open-support consumers are now
  accepted in the actual Cartier/Rj terminal scope. The Cartier boundary-zero consumer keeps canonical Epi explicit.
- The boundary projection/product comparison needed for the degree-one case
  is a separate source candidate. Etale excision alone does not establish
  smooth-projection compatibility.
- The final degree-induction candidate retains the actual cohomological
  restriction Mono theorem family as an explicit input. It is not a proof
  of the requested unconditional strict A1 theorem.

The separately requested full standard-triple lane is governed by
`STANDARD_TRIPLE_PROOF_PLAN_20261018.md`. It reuses existing geometry but targets
the precise simultaneous nullhomotopy, with fixed-parameter section existence
and relative-covering norm compatibility still open. Necessary relative Picard
interfaces are now authorized for parallel development, starting from a bounded
source/consumer audit, not a replacement of the existing strict-A1 route.
