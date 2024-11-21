/* The minimum valuation of the entries of a matrix. */
function minValuation(M, P)
    return Minimum([Valuation(y, P) : y in Eltseq(M)]);
end function;

declare type BTTree[BTTVert];
declare attributes BTTree:
    place; // Place
declare attributes BTTVert:
    Parent, // Parent vertex
    matrix, // Matrix
    precision; // Precision

/**
 * Tree intrinsics
 */

intrinsic BruhatTitsTree(place::PlcNumElt) -> BTTree
{Returns a BTTree localised at a given place.}
    T := New(BTTree);
    T`place := place;
    assert IsFinite(place);
    return T;
end intrinsic;

intrinsic BruhatTitsTree(field::FldNum, p::RngIntElt) -> BTTree
{Returns a BTTree localised at a given prime.}
    return BruhatTitsTree(Decomposition(field, p)[1][1]);
end intrinsic;

intrinsic Field(T::BTTree) -> FldNum
{Returns the base field of the BTTree.}
    return NumberField(Place(T));
end intrinsic;

intrinsic Place(T::BTTree) -> PlcNumElt
{Returns the place of the BTTree.}
    return T`place;
end intrinsic;

intrinsic UniformizingElement(T::BTTree) -> RngOrdElt
{Returns a uniformizing element of the maximal order at the place.}
    return UniformizingElement(Place(T));
end intrinsic;

intrinsic Integers(T::BTTree) -> FldOrd
{Returns the ring of integers of the BTTree.}
    return MaximalOrder(Field(T));
end intrinsic;

intrinsic Ideal(T::BTTree) -> RngOrdIdl
{Returns the maximal ideal of the BTTree.}
    return Ideal(Place(T));
end intrinsic;

intrinsic LocalRing(T::BTTree) -> RngOrd
{Returns the local ring of the BTTree.}
    return Localization(Integers(T), Ideal(Place(T)));
end intrinsic;

intrinsic 'eq'(T::BTTree, S::BTTree) -> BoolElt
{Returns whether two BTTrees are equal.}
    return Place(T) eq Place(S);
end intrinsic;

intrinsic Print(T::BTTree)
{Prints the BTTree.}
    printf "BTTree over %o-adic localization of %o", MinimalInteger(Ideal(T)), Field(T);
end intrinsic;

/* Vertex intrinsics */

intrinsic BTTVertex(tree::BTTree, matrix::AlgMatElt[FldNum]) -> BTTVert
{Create a vertex of the BTTree.}
    error if Nrows(matrix) ne 2 or Ncols(matrix) ne 2, "Matrix must be 2x2";
    error if Determinant(matrix) eq 0, "Matrix must be invertible";
    v := New(BTTVert);
    v`Parent := tree;
    
    // Put the matrix in Hermite form
    L := LocalRing(tree);
    u := UniformizingElement(tree);
    k := minValuation(matrix, Place(tree));
    matrix := HermiteForm(ChangeRing(matrix*u^(-k), L));
    matrix := ChangeRing(matrix, Field(tree));

    // Normalize the matrix
    matrix /:= matrix[1, 1];
    v`matrix := matrix;
    v`precision := Valuation(matrix[2, 2], Place(tree));
    return v;
end intrinsic;

intrinsic BTTVertex(tree::BTTree, value::FldNumElt, precision::RngIntElt) -> BTTVert
{Create a vertex of the BTTree.}
    v := New(BTTVert);
    v`Parent := tree;
    u := UniformizingElement(tree);
    v`matrix := Matrix(2, [1, value, 0, u^precision]);
    v`precision := precision;
    return v;
end intrinsic;

intrinsic BTTVertex(tree::BTTree, value::RngIntElt, precision::RngIntElt) -> BTTVert
{Create a vertex of the BTTree.}
    return BTTVertex(tree, Field(tree)!value, precision);
end intrinsic;

intrinsic BTTVertex(tree::BTTree, value::FldRatElt, precision::RngIntElt) -> BTTVert
{Create a vertex of the BTTree.}
    return BTTVertex(tree, Field(tree)!value, precision);
end intrinsic;

intrinsic Parent(v::BTTVert) -> BTTree
{Returns the parent of a vertex.}
    return v`Parent;
end intrinsic;

intrinsic Value(v::BTTVert) -> FldNumElt
{Returns the value of a vertex.}
    return v`matrix[1, 2];
end intrinsic;

intrinsic Precision(v::BTTVert) -> RngIntElt
{Returns the precision of a vertex.}
    return Valuation(v`matrix[2, 2], Place(Parent(v)));
end intrinsic;

intrinsic 'eq'(v::BTTVert, w::BTTVert) -> BoolElt
{Returns whether two vertices are equal.}
    u := UniformizingElement(Parent(v));
    return Precision(v) eq Precision(w) and IsIntegral((Value(v) - Value(w))/u^Precision(v));
end intrinsic;

intrinsic '*'(v::BTTVert, M::AlgMatElt[FldNum]) -> BTTVert
{Apply an isometry to a vertex.}
    tree := Parent(v);
    return BTTVertex(tree, v`matrix*M);
end intrinsic;

intrinsic Origin(tree::BTTree) -> BTTVert
{Returns the origin of the BTTree.}
    return BTTVertex(tree, Field(tree)!0, 0);
end intrinsic;

intrinsic Displacement(M::AlgMatElt[FldNum], tree::BTTree) -> RngIntElt
{Returns the displacement of an isometry.}
    return Valuation(Determinant(M), Place(tree)) - 2*minValuation(M, Place(tree));
end intrinsic;

intrinsic DistanceToOrigin(v::BTTVert) -> RngIntElt
{Returns the distance of a vertex to the origin.}
    P := Place(Parent(v));
    return Precision(v) - 2*Minimum(Minimum(Valuation(Value(v), P), Precision(v)), 0);
end intrinsic;

intrinsic CmpVertices(v, w) -> RngIntElt
{Compares two vertices lexicographically.}
    if v eq w then return 0; end if;
    T := Parent(v);

    P := Place(T);
    // Compare the lengths
    l1 := DistanceToOrigin(v);
    l2 := DistanceToOrigin(w);
    if l1 lt l2 then
        return -1;
    elif l1 gt l2 then
        return 1;
    end if;

    // Projection of the paths along the main axis.
    vproj := Minimum(Valuation(Value(v), P), Precision(v));
    wproj := Minimum(Valuation(Value(w), P), Precision(w));
    
    // If has smaller displacement along the main axis, it is smaller.
    if vproj lt wproj then
        return -1;
    elif vproj gt wproj then
        return 1;
    end if;

    // Compare the first edge at which they differ.
    d := Value(v) - Value(w);
    val := Valuation(d, P);

    u := UniformizingElement(T);
    Fp, f := ResidueClassField(Ideal(T));
    e1 := f(Value(v)/u^val);
    e2 := f(Value(w)/u^val);
    if e1 lt e2 then
        return -1;
    elif e1 gt e2 then
        return 1;
    end if;
    error "Unreachable state: vertices were equal but comparison failed";
end intrinsic;

/* The vertex halfway between the origin and v */
function halfPath(v)
    T := Parent(v);
    P := Place(T);

    // Distance to origin = fall + rise.
    fall := -Minimum(Minimum(Valuation(Value(v), P), Precision(v)), 0);
    rise := Precision(v) + fall;

    if fall ge rise then
        return BTTVertex(T, 0, Truncate(-(fall + rise)/2));
    else
        return BTTVertex(T, Value(v), Truncate((rise - 3*fall)/2));
    end if;
end function;

intrinsic CmpIsometry(M::AlgMatElt[FldNum], N::AlgMatElt[FldNum], tree::BTTree) -> RngIntElt
{Compares two isometries.}
    v1 := halfPath(BTTVertex(tree, M));
    v2 := halfPath(BTTVertex(tree, M^-1));
    w1 := halfPath(BTTVertex(tree, N));
    w2 := halfPath(BTTVertex(tree, N^-1));

    if CmpVertices(v1, v2) lt 0 then
        vMin := v1;
        vMax := v2;
    else
        vMin := v2;
        vMax := v1;
    end if;

    if CmpVertices(w1, w2) lt 0 then
        wMin := w1;
        wMax := w2;
    else
        wMin := w2;
        wMax := w1;
    end if;

    cmp := CmpVertices(vMin, wMin);
    return cmp eq 0 select CmpVertices(vMax, wMax) else cmp;
end intrinsic;

intrinsic Print(v::BTTVert)
{Prints a vertex.}
    printf "Vertex with value %o and precision %o", Value(v), Precision(v);
end intrinsic;

/**
 * Other intrinsics
 */

intrinsic IsElliptic(M::AlgMatElt[FldNum], T::BTTree) -> BoolElt
{Returns whether a matrix is elliptic.}
    return 2*Valuation(Trace(M), Place(T)) gt Valuation(Determinant(M), Place(T));
end intrinsic;

/**
 * Discreteness algorithms
 */

/* Evaluate a word (as a list of ids) with a generating set. */
function evaluate_word(word_ids, seq)
    return &*[seq[i] : i in word_ids];
end function;

/* Get the symmetric sequence of generators and inverses. */
symmetrize := function(gens)
  gens_sym := &cat[[x, x^-1] : x in gens];
  if Nresults() eq 1 then return gens_sym; end if;
  S := Sym(#gens_sym);
  invert_perm := S!(&cat[[2*i, 2*i-1] : i in [1 .. #gens]]);
  return gens_sym, invert_perm;
end function;

/* A generating set for a subgroup of SL2 over a non-Archimedean local field. */
declare type GrpSL2pGen;
declare attributes GrpSL2KGen:
    field, // Base field
    matalg, // Matrix Algebra
    tree, // Bruhat-T its tree
    seq, // The original generators
    psl, // Whether the generators should be considered a subgroup of PSL
    has_neg, // True if psl is false and the group contains -I
    neg_word, // -I as a word in the generators
    /**
    * "un" - Unknown type (only used for intermediate reduction steps)
    * "df" - Discrete and free
    * "el" - Contains an elliptic element
    */
    type,
    /**
    * Proof of the type of the group:
    * "un" - Nielsen-equivalent generating set (for intermediate steps)
    * "df" - Reduced generating set (does not include -I)
    * "el" - Elliptic element
    */
    witness,
    witness_word, // A word corresponding to each element of the witness

    // These attributes are only defined if the group is determined to be discrete and free.
    FPgrp, // Finite presentation
    matgrp, // Matrix group (with reduced generating set)
    iso; // Isometry to finitely presented group

intrinsic Print(gen::GrpSL2KGen)
{ Print the generating set. }
list := &*[Sprint(x) * (i lt #gen`seq select "\n\n" else "") : i -> x in gen`seq];
printf "Generators of subgroup of %oSL2 over non-Archimedean field:\n%o", gen`psl select "P" else "", gen`field, list;
end intrinsic;
intrinsic SL2KGens(seq::SeqEnum[AlgMatElt[FldNum]], place::PlcNumElt : psl := false) -> GrpSL2Gen
{ Create a generating set for a subgroup of SL2 over an algebraic number field at a finite place. }
  gen := New(GrpSL2KGen);
  require IsFinite(place): "Place must be finite";
  require Degree(Universe(seq)) eq 2: "Matrix algebra must be degree 2";
  require &and[Determinant(g) eq 1 : g in seq]: "Matrices must have determinant 1";
  require BaseRing(Universe(seq)) eq NumberField(place): "Generators and place must have the same base field";
  gen`seq := seq;
  gen`matalg := Universe(seq);
  gen`field := BaseRing(gen`matalg);
  gen`tree := BruhatTitsTree(place);
  gen`psl := psl;
  gen`has_neg := false;

  gen`type := "un";
  gen`witness := seq;
  gen`witness_word := Setseq(Generators(FreeGroup(#seq)));
  return gen;
end intrinsic;

/* Apply one step of the reduction algorithm. */
procedure reduce_step(gen)
    if gen`type ne "un" then return; end if;

    // Deal with elliptic, I, and -I elements.
    for i -> g in gen`seq do
        if IsOne(g) or IsOne(-g) then
            if IsOne(-g) and not gen`psl and not gen`has_neg then
                gen`has_neg := true;
                gen`neg_word := gen`witness_word[i];
            end if;
            Remove(~gen`witness, i);
            Remove(~gen`witness_word, i);
            return;
        elif is_elliptic(g, tree) then
            gen`type := "el";
            gen`witness := g;
            gen`witness_word := gen`witness_word[i];
            return;
        end if;
    end for;

    // A single non-elliptic element generates a free group.
    if #gen`witness le 1 then
        gen`type := "df";
        gen`FPgrp := FreeGroup(#gen`witness_word);
        if gen`has_neg then
            gen`FPgrp := DirectProduct(gen`FPgrp, CyclicGroup(GrpFP, 2));
        end if;
        return;
    end if;

    gens_sym, inv := symmetrize(gen`witness);
    words_sym := symmetrize(gen`witness_word);
    for i -> x in gens_sym do
        for j -> y in gens_sym do
            if Ceiling(i/2) eq Ceiling(j/2) then continue; end if;
            z := x*y;
            if CmpIsometry(x, z) eq 1 then
                x := z;
                id := Ceiling(i/2);
                gen`witness[id] := z;
                gen`witness_word[id] := words_sym[i]*words_sym[j];
            end if;
        end for;
    end for;

    // The group is discrete and free.
    gen`type := "df";
    gen`FPgrp := FreeGroup(#gen`witness_word);
    if gen`has_neg then
        gen`FPgrp := DirectProduct(gen`FPgrp, CyclicGroup(GrpFP, 2));
    end if;
end procedure;

intrinsic RecognizeDiscreteFree(gen::GrpSL2KGen) -> GrpSL2KGen
{ Decide if a finite subset of SL2 over a non-Archimedean local field is discrete and free.
Modifies the attributes of the input generating set. }
    repeat
        reduce_step(gen);
    until gen`type ne "un";

    // Construct isomorphism between presentation and matrix group.
    if IsDiscreteFree(gen) then
        gen`matgrp := MatrixGroup<2, gen`field | ReducedGenerators(gen)>;
        
        to_mat := hom<gen`FPgrp -> gen`matgrp | [gen`matgrp!g : g in ReducedGenerators(gen)]>;
        to_fp_fn := function(g)
            b, w := IsElementOf(Matrix(g), gen);
            assert b;
            return w;
        end function;

        gen`iso := iso<gen`matgrp -> gen`FPgrp | g :-> to_fp_fn(g), w :-> to_mat(w)>;
    end if;
end intrinsic;

intrinsic IsDiscreteFree(gen::GrpSL2KGen) -> BoolElt
{ Returns whether a finite subset of SL2 over a non-Archimedean local field is discrete and free. }
    error if gen`type eq "un", "The group type is unknown; prepare it using `RecognizeDiscreteFree`";
    return gen`type eq "df";
end intrinsic;

intrinsic ReducedGenerators(gen::GrpSL2KGen) -> SeqEnum[AlgMatElt]
{ Return a reduced generating set for a discrete torsion-free group. }
    error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteFree`";
    error if not IsDiscreteFree(gen), "The group is not discrete and free";
    if (gen`has_neg) then
        return gen`witness cat [-One(BaseField(gen))];
    else
        return gen`witness;
    end if;
end intrinsic;

intrinsic BaseField(gen::GrpSL2KGen) -> FldNum
{ Return the base field of the group. }
     return gen`field;
end intrinsic;

intrinsic HasNegativeOne(gen::GrpSL2KGen) -> FldNum, GrpFPElt
{ Return true if the subgroup of SL(2, K) has -I. }
    error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteFree`";
    error if gen`psl, "The group must be a subgroup of SL(2, K)";
    if gen`has_neg then
        return true, gen`neg_word;
    else
        return false;
    end if;
end intrinsic;

intrinsic Rank(gen::GrpSL2KGen) -> RngIntElt
{ The rank of a discrete free group. }
    error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteFree`";
    error if not IsDiscreteFree(gen), "The group is not discrete and free";
    return gen`has_neg select #gen`witness + 1 else #gen`witness;
end intrinsic

intrinsic IsElementOf(g::AlgMatElt[FldNum], gen::GrpSL2KGen) -> BoolElt, GrpFPElt
{ Check if a matrix is in the group. }
    error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteFree`";
    error if not IsDiscreteFree(gen), "The group is not discrete and free";

    gen_sym := symmetrize(gen`witness);
    G := gen`FPgrp;
    fp_sym := symmetrize(Setseq(Generators(G)));
    g_word := Id(G);
    o := Origin(gen`tree);
    repeat
        finish := true;
        for i -> x in gen_sym do
            h := g*x;
            if CmpVertices(o*h, o*g) eq -1 then
                g_word := g_word*fp_sym[i];
                g := g*x;
                finish := false
                break;
            end if;
        end for;
    until finish;
    if IsOne(g) or (gen`psl and IsOne(-g)) then
        return true, g_word^-1;
    elif gen`has_neg and IsOne(-g) then
        return true, g_word^-1*G.(NumberOfGenerators(G));
    else
        return false, _;
    end if;
end intrinsic;

intrinsic MapToFundamentalDomain(v::BTTVert, gen::GrpSL2KGen) -> BTTVert
{ Return the unique g (and corresponding word) such that v*g is in the fundamental domain.}
    error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteFree`";
    error if not IsDiscreteFree(gen), "The group is not discrete and free";
    error if not Parent(v) eq gen`tree, "The vertex must be in the same tree as the group";

    gen_sym, inv := symmetrize(gen`witness);
    G := gen`FPgrp;
    fp_sym := symmetrize(Setseq(Generators(G)));
    g := One(gen`matalg);
    g_word := Id(G);
    w := v;

    repeat
        finish := true;
        for i -> x in gen_sym do
            w2 := w*x;
            if CmpVertices(w2, w) eq -1 then
                g_word := g_word*fp_sym[i];
                g := g*x;
                w := w2;
                finish := false;
                break;
            end if;
        end for;
    until finish;

    return g, g_word;
end intrinsic;

/**
 * Discreteness algorithms
 */