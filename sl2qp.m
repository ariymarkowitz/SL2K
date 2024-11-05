// The minimum valuation of the entries of a matrix
function minValuation(M, P)
    return Minimum([Valuation(y, P) : y in Eltseq(M)]);
end function;

declare type BTTree[BTTVert];
declare attributes BTTree:
    field, // Base field
    place, // Place
declare attributes BTTVert:
    Parent, // Parent vertex
    matrix, // Matrix

intrinsic BTTree(field::FldNum, place::PlcNumElt) -> BTTree
{Returns a BTTree.}
    B := New(BTTree);
    B`field := field;
    B`place := place;
    assert IsFinite(place);
    return B;
end intrinsic;

intrinsic Field(B::BTTree) -> FldNum
{Returns the base field of the BTTree.}
    return B`field;
end intrinsic;

intrinsic Place(B::BTTree) -> PlcNumElt
{Returns the place of the BTTree.}
    return B`place;
end intrinsic;

intrinsic UniformizingElement(B::BTree) -> RngOrdElt
{Returns a uniformizing element of the maximal order at the place.}
    return UniformizingElement(Place(B));
end intrinsic;

intrinsic Integers(B::BTTree) -> FldOrd
{Returns the ring of integers of the BTTree.}
    return MaximalOrder(Field(BTTree));
end intrinsic;

intrinsic Ideal(B::BTTree) -> RngOrdIdl
{Returns the maximal ideal of the BTTree.}
    return Ideal(Place(B));
end intrinsic;

intrinsic LocalRing(B::BTTree) -> RngOrd
{Returns the local ring of the BTTree.}
    return Localization(Integers(B), Ideal(Place(B)));
end intrinsic;

intrinsic BTTVert(tree::BTTree, matrix::AlgMatElt[FldNumElt]) -> BTTVert
{Create a vertex of the BTTree.}
    v := New(BTTVert);
    v`Parent := tree;
    
    // Put the matrix in Hermite form
    L := LocalRing(tree);
    u := UniformizingElement(tree);
    k := minValuation(matrix, Place(tree));
    matrix := Transpose(HermiteForm(Transpose(ChangeRing(matrix*u^(-k), L))));
    matrix := ChangeRing(matrix, Field(tree));

    // Normalize the matrix
    matrix /:= matrix[2, 2];
    v`matrix := matrix;
    return v;
end intrinsic;

intrinsic BTTVert(tree::BTTree, value::FldNumElt, precision::RngIntElt) -> BTTVert
{Create a vertex of the BTTree.}
    u := UniformizingElement(tree);
    return BTTVert(tree, Matrix(2, [u^precision, 0, value, 1]));
end intrinsic;

intrinsic Parent(v::BTTVert) -> BTTree
{Returns the parent of a vertex.}
    return v`Parent;
end intrinsic;

intrinsic Value(v::BTTVert) -> FldNumElt
{Returns the value of a vertex.}
    return v`matrix[2, 1];
end intrinsic;

intrinsic Precision(v::BTTVert) -> RngIntElt
{Returns the precision of a vertex.}
    return v`matrix[1, 1];
end intrinsic;

intrinsic Eq(v::BTTVert, w::BTTVert) -> BoolElt
{Returns whether two vertices are equal.}
    u := UniformizingElement(Parent(v));
    return Precision(v) eq Precision(w) and IsIntegral((Value(v) - Value(w))/u^Precision(v));
end intrinsic;

intrinsic '*'(v::BTTVert, M::AlgMatElt[FldNum]) -> BTTVert
{Apply an isometry to a vertex.}
    tree := Parent(v);
    return BTTVert(tree, v`matrix*M);
end intrinsic;

intrinsic Origin(tree::BTTree) -> BTTVert
{Returns the origin of the BTTree.}
    return BTTVert(tree, Field(tree)!0, 0);
end intrinsic;

intrinsic Displacement(M::AlgMatElt[FldNum], tree::BTTree) -> RngIntElt
{Returns the displacement of an isometry.}
    return Valuation(Determinant(M), Place(tree)) - 2*minValuation(M, Place(tree));
end intrinsic;

intrinsic DistanceToOrigin(v::BTTVert) -> RngIntElt
{Returns the distance of a vertex to the origin.}
    P := Place(Parent(v));
    return Precision(v) - 2*Minimum(Valuation(Value(v), P), 0);
    Displacement(v`matrix, Parent(v));
end intrinsic;

intrinsic CmpVertices(v, w)
{Compares two vertices lexicographically.}
    if Eq(v, w) then return 0; end if;

    P := Place(Parent(v));
    // Compare the lengths
    l1 := DistanceToOrigin(v);
    l2 := DistanceToOrigin(w);
    if l1 lt l2 then
        return -1;
    elif l1 gt l2 then
        return 1;
    end if;

    // Projection of the paths along the main axis
    vproj = Minimum(Valuation(Value(v), P), Precision(v));
    wproj = Minimum(Valuation(Value(w), P), Precision(w));
    
    // If has smaller displacement along the main axis, it is smaller
    if vproj lt wproj then
        return -1;
    elif vproj gt wproj then
        return 1;
    end if;

    // Compare the first edge at which they differ
    d = Value(v) - Value(w);
    val := Valuation(d, P);

    u := UniformizingElement(Parent(v));
    Fp, f := ResidueClassField(P);
    e1 := f(Value(v)/u^val);
    e2 := f(Value(w)/u^val);
    if e1 lt e2 then
        return -1;
    elif e1 gt e2 then
        return 1;
    end if;
    error "Code should be unreachable.";
end intrinsic;

// The vertex halfway between the origin and v
function halfPath(v)
    return BTTVert(tree, Value(v), Truncate(Precision(v)/2));
end function;

intrinsic CmpIsometry(M::AlgMatElt[FldNum], N::AlgMatElt[FldNum], tree::BTTree) -> RngIntElt
{Compares two isometries.}
    v1 := halfPath(BTTVert(tree, M));
    v2 := halfPath(BTTVert(tree, M^-1));
    w1 := halfPath(BTTVert(tree, N));
    w2 := halfPath(BTTVert(tree, N^-1));

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