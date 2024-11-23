Attach("SL2KDiscrete.m");

Q := Rationals();
P<x> := PolynomialRing(Q);
K<a> := NumberField(x^2 - 3);
M := MatrixAlgebra(K, 2);
P := Place(5*Integers(K));
T := BruhatTitsTree(P);

function random_sl2(F, n, l)
  M := MatrixAlgebra(F, 2);
  R := Integers(F);
  result := One(M);
  for i in [1..l] do
    m := M![1, Random(F, n), 0, 1];
    if Random(1) eq 1 then
      m := Transpose(m);
    end if;
    if Random(1) eq 1 then
      m := -m;
    end if;
    result *:= m;
  end for;
  return result;
end function;

function random_gens(F, n, l, gens)
  return [random_sl2(F, n, l) : i in [1..gens]];
end function;

function time_ngens(genslist)
  worst := 0;
  full := Cputime();
  ndiscrete := 0;
  for gens in genslist do
    t := Cputime();
    RecognizeDiscreteFree(gens);
    t := Cputime(t);
    worst := Maximum(t, worst);
    if IsDiscreteFree(gens) then
      ndiscrete +:= 1;
    end if;
  end for;
  full := Cputime(full);
  print "Test complete";
  return <full/#genslist, worst, ndiscrete>;
end function;

function random_point(d, G)
  F := BaseField(G);
  v := Origin(T);
  for i in [1..d] do
    v *:= Random(ReducedGenerators(G));
  end for;
  return v;
end function;

function time_fundamental_domain(genslist, points)
  t := Cputime();
  worst := 0;
  for i -> G in genslist do
    for point in points[i] do
      t2 := Cputime();
      g := MapToFundamentalDomain(point, G);
      t2 := Cputime(t2);
      worst := Maximum(worst, t2);
    end for;
  end for;
  print "Test complete";
  return <Cputime(t)/(&+[#p : p in points]), worst>;
end function;

// Time recognition
params := [<7, 2>, <11, 5>, <15, 10>, <18, 20>];
tests := [[SL2KGens(random_gens(K, 10, p[1], p[2]), P) : i in [1..1000]] : p in params];
results1 := [time_ngens(G) : G in tests];

// Time fundamental domain
good := [G : G in tests[2] | IsDiscreteFree(G)][1..100];
pointslist := [[[random_point(d, G) : i in [1..10]] : G in good] : d in [5, 10, 20, 40]];

results2 := [time_fundamental_domain(good, points) : points in pointslist];

// Discreteness tests

Q := RationalsAsNumberField();
M := MatrixAlgebra(Q, 2);

A := M![0, 9, -1/9, 1];
B := M![9, 2, 1, 1/3];

G := SL2KGens([A, B], 3);
time b, H, S, p := IsDiscrete(G);

x := Q!Random(Integers(Q), 10000);
y := Q!Random(Integers(Q), 10000);
z := Q!Random(Integers(Q), 10000);
w := Q!Random(Integers(Q), 10000);
C := M![1, x, 0, 1] * M![1, 0, y, 1] * M![1, z, 0, 1] * M![1, 0, w, 1];

time b := IsElementOf(C, H, S);
