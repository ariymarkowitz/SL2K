Attach("SL2KDiscrete.m");

Q := Rationals();
P<x> := PolynomialRing(Q);
K<a> := NumberField(x^2 - 5);
p := 3;

T := BruhatTitsTree(K, 3);
k<b> := ResidueClassField(Place(T));
v := Origin(T);
assert DistanceToOrigin(v) eq 0;
assert Parent(v) eq T;
assert Value(v) eq 0;
assert Precision(v) eq 0;
assert v eq v;

id := MatrixAlgebra(K, 2)![[1, 0], [0, 1]];

assert v eq v*id;
assert Displacement(id, T) eq 0;

w := BTTVertex(T, 1/27, -2);
x := BTTVertex(T, a/27, -2);
assert DistanceToOrigin(w) eq 4;
assert DistanceToOrigin(x) eq 4;
assert w ne x;
assert [Eltseq(e) : e in EdgeSeq(w)] eq [[0, 1], [0, 1], [0, 1], [1, 1]];
assert [Eltseq(e) : e in EdgeSeq(x)] eq [[0, 1], [0, 1], [0, 1], [1, b^6]];
assert CmpVertices(w, x) eq -1;
assert CmpVertices(x, w) eq 1;
assert halfPath(w) eq halfPath(x);

w := BTTVertex(T, 1/3+3, 2);
x := BTTVertex(T, a/3+2, 2);
assert DistanceToOrigin(w) eq 4;
assert DistanceToOrigin(x) eq 4;
assert w ne x;
assert [Eltseq(e) : e in EdgeSeq(w)] eq [[0, 1], [1, 1], [1, 0], [1, 1]];
assert [Eltseq(e) : e in EdgeSeq(x)] eq [[0, 1], [1, b^6], [1, 1], [1, 0]];
assert CmpVertices(w, x) eq -1;
assert CmpVertices(x, w) eq 1;
assert DistanceToOrigin(halfPath(w)) eq 2;
assert DistanceToOrigin(halfPath(x)) eq 2;
assert halfPath(w) ne halfPath(x);

w := BTTVertex(T, 0, -4);
x := BTTVertex(T, 0, 4);
assert CmpVertices(w, x) eq -1;

M := MatrixAlgebra(K, 2);

m := M![[1, 2], [0, 9]];
n := M![[1, 1+a], [0, 9]];

assert v*m^-1 eq v*n^-1;
assert v*m ne v*n;
assert CmpIsometry(m, n, T) eq -1;

assert IsHyperbolic(m, T);
assert IsHyperbolic(n, T);

assert IsElliptic(M![[1, 3], [0, 2]], T);
assert IsElliptic(M![[1, 5], [1/5, 2]], T);

/* Discreteness tests */

Q := RationalsAsNumberField();
p := 2;
M := MatrixAlgebra(Q, 2);
T := BruhatTitsTree(Q, p);

A := M![1/2, 0, 0, 2];
B := M![1/2, 1, -1/2, 1];

gens := SL2KGens([A*B^-1, B], p);
reduce_step(gens);
assert gens`type eq "un";
assert gens`witness eq [A, B];
F := Universe(gens`witness_word);
assert gens`witness_word eq [F.1*F.2, F.2];

reduce_step(gens);
assert gens`type eq "df";
assert gens`witness eq [A, B];
F := Universe(gens`witness_word);
assert gens`witness_word eq [F.1*F.2, F.2];

gens := SL2KGens([A*B*A^-1, B^2*A^-1, -B^3*A^-1], p);
RecognizeDiscreteFree(gens);
assert IsDiscreteFree(gens);
F := Universe(gens`witness_word);
assert gens`witness_word eq [F.1*F.2^-1*F.1*F.2^-1*F.1, F.2*F.1^-1];
assert ReducedGenerators(gens) eq [A^-1, -B, -One(M)];
assert HasNegativeOne(gens);
assert FreeRank(gens) eq 2;
assert Rank(gens) eq 3;
C := A*B^3*A^-1*B^-2;
b, w := IsElementOf(A*B^3*A^-1*B^-2, gens);
assert b;
G := gens`FPgrp;
assert w eq G.1^-1*G.2^3*G.1*G.2^-2*G.3;
assert Inverse(gens`iso)(w) eq C;
v := BTTVertex(T, 1/2+1+4+16+32+256, 9);
g, word := MapToFundamentalDomain(v, gens);
assert v*g eq BTTVertex(T, 0, 1);
assert word eq G.1^-1*G.2^-1*G.1^-1*G.2^-1*G.1^-2*G.2^-1*G.1;
assert g eq -A*B^-1*A*B^-1*A^2*B^-1*A^-1;

gens := SL2KGens([A*B*A^-1, B^2*A^-1, -B^3*A^-1], p : psl);
RecognizeDiscreteFree(gens);
assert IsDiscreteFree(gens);
assert Rank(gens) eq 2;

gens := SL2KGens([M![[2, 3], [1, 2]]], p);
RecognizeDiscreteFree(gens);
assert not IsDiscreteFree(gens);
assert IsElliptic(gens`witness, gens`tree);

// Discreteness

Q := RationalsAsNumberField();
M := MatrixAlgebra(Q, 2);

A := M![0, 9, -1/9, 1];
B := M![9, 2, 1, 1/3];

G := SL2KGens([A, B], 3);
H, S, p := TorsionFreeSubgroup(G);
assert p eq 5;
assert &and[IsHyperbolic(g, G`tree) or IsOne(g) or IsOne(-g) : g in Generators(H)];