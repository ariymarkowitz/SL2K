A Magma package to recognise finitely generated discrete subgroups of SL(2, K) and PSL(2, K), where K is a non-Archimedean field of characteristic 0.

## Types

`GrpSL2KGen`

A finite generating set for a subgroup of SL(2, K). K is represented by an algebraic number field together with a finite place (embedding into a non-Archimedean local field). This type has the following attributes:

- `field` - The base field.
- `matalg` - The matrix algebra.
- `tree` - The Bruhat-Tits tree corresponding over the field.
- `seq`- Sequence of generators of the group.

The following attributes are initially unset, and are set by `RecognizeDiscreteTorsionFree(gen::GrpSL2KGen)`.
- `has_neg` - True if `psl` is false and the group contains -I.
- `neg_word` - -I as a word in the generators.
- `type` - The type of group. This attribute is one of the following:
  - "un" - Unknown type (only used for intermediate reduction steps).
  - "df" - Discrete and free.
- `witness` - The witness proving that the group is a particular type. For "un", this is a Nielsen-equivalent generating set. For "df", this is a reduced generating set (not including -I).
- `witness_word` - A word corresponding to each element of the witness.

The following attributes are only defined if SL2KGen is determined to be discrete and torsion-free.
- `FPgrp` - A finitely-presented group isomorphic to this group.
- `matgrp` - A matrix group (with reduced generating set) isomorphic to this group.
- `iso` - Isometry from `matgrp` to `FPgrp`.

## Intrinsics

### Discrete and free groups

`SL2KGens(seq::SeqEnum[AlgMatElt[FldNum]], place::PlcNumElt : psl := false) -> GrpSL2KGen`

Create a generating set for a subgroup of SL(2, K). If `psl` is set, then the generators will be considered to be representatives of elements of PSL(2, K).

`RecognizeDiscreteFree(gen::GrpSL2KGen)`

Decide a generating set of SL(2, K) is discrete and free. This adds data to `gen` that records the results of the recognition algorithm.

`IsDiscreteFree(gen::GrpSL2KGen) -> BoolElt`

Return true if the generating set is discrete and free.

`IsElementOf(g::AlgMatElt, gen::GrpSL2KGen) -> BoolElt, GrpFPElt`

Decide whether g is an element of the group, returning the word in the reduced set evaluating to g.

`MapToFundamentalDomain(v::BTTVert, gen::GrpSL2KGen) -> AlgMatElt, GrpFPElt`

Return g (and the corresponding word) such that v*g is in the fundamental domain.
Two points in the same orbit will be mapped to the same orbit representative.

`ReducedGenerators(gen::GrpSL2KGen) -> SeqEnum[AlgMatElt]`

Return a reduced generating set for a discrete free group.

`BaseField(gen::GrpSL2KGen) -> FldNum`

Return the base field of the group.

`HasNegativeOne(gen::GrpSL2KGen) -> FldNum, GrpFPElt`

Return true if the subgroup of SL(2, K) has -I.

`Rank(gen::GrpSL2KGen) -> RngIntElt`

The rank of a discrete free group.

## Discrete groups

`TorsionFreeSubgroup(gen::GrpSL2KGen) -> GrpSL2KGen, SetEnum[AlgMatElt], RngIntElt`

Find a generating set for a torsion-free congruence subgroup.

`IsDiscrete(gen::GrpSL2KGen) -> BoolElt, GrpSL2KGen, SetEnum[AlgMatElt], RngIntElt`

Decide whether a subgroup of SL(2, K) or PSL(2, K) is discrete, returning a finite index subgroup and set of coset representatives if so.

`IsElementOf(g::AlgMatElt, tf_gp::GrpSL2KGen, cosets::SetEnum[AlgMatElt]) -> BoolElt, GrpFPElt, AlgMatElt`

Decide whether g is an element of a subgroup of SL(2, K) or PSL(2, K), given a torsion-free discrete subgroup and a set of coset representatives. If it is, then return (w, s) where s is a coset representative and w is a word in the reduced set such that w*s evaluates to g.