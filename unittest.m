Attach("sl2qp.m");

Q := Rationals();
P<x> := PolynomialRing(Q);
K<a> := NumberField(x^2 - 5);
p := 3;

T := BruhatTitsTree(K, 3);
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
assert CmpVertices(w, x) eq -1;
assert CmpVertices(x, w) eq 1;
assert halfPath(w) eq halfPath(x);

w := BTTVertex(T, 1/3+3, 2);
x := BTTVertex(T, a/3+2, 2);
assert DistanceToOrigin(w) eq 4;
assert DistanceToOrigin(x) eq 4;
assert w ne x;
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
