// The minimum valuation of the entries of a matrix
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

/* Tree intrinsics */

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

    // Projection of the paths along the main axis
    vproj := Minimum(Valuation(Value(v), P), Precision(v));
    wproj := Minimum(Valuation(Value(w), P), Precision(w));
    
    // If has smaller displacement along the main axis, it is smaller
    if vproj lt wproj then
        return -1;
    elif vproj gt wproj then
        return 1;
    end if;

    // Compare the first edge at which they differ
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

// The vertex halfway between the origin and v
function halfPath(v)
    T := Parent(v);
    P := Place(T);

    // Distance to origin = fall + rise
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