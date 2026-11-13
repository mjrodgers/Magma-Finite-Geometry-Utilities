freeze;

/* -------------------------------------------------------------------------//
// -------------------------------------------------------------------------//
  Provides sone tools for classifying objects based on isomorphism testing.

  CanonicalVertexSet(S::Set, Gr::Grph)
    if S is a vertex subset of the graph Gr, we use Magma's version of nauty
    to provide a canonical vertex labeling, which allows us to obtain
    a canonical vertex set S' associated with S; that is, if S_1 and S_2
    are vertex sets, then S'_1 = S'_2 if and only if there is exists
    and automorphism of Gr sending S_1 to S_2.
  ColumnStabilizer(S::SeqEnum)
  ColumnStabilizer(S::ModTupFldElt)
    given a sequence or vector S of length n, return the stabilizer in Sym(n);
  ColumnStabilizer(M::Mtrx)
    Given an mxn matrix, return the subgroup of Sym(n) obtained from
    projecting AutomorphismGroup(M) from Sym(m)xSym(n) -> Sym(n).
    Optional parameter RSTRCT allows us to 'color' rows and columns
    to give a fixed partition.
  CanonicalSortedMatrix(M)
    Reorders rows and columns of a matrix in a canonical way.
  RemoveIsomorphic(MSET)
  RemoveIsomorphic(~MSET)
    given a collection of matrices, remove isomorphic copies
    to obtain a set of distinct representatives.
// -------------------------------------------------------------------------//
// -------------------------------------------------------------------------*/


intrinsic CanonicalVertexSet(S::Set, Gr::Grph) -> SetEnum
{ Takes a set S of vertices of a graph Gr, returns a canonically isomorphic set of vertices. }
require S subset VertexSet(Gr): "S must be a set of vertices of Gr.";
  AssignLabels(~Gr, {@ v : v in S @}, [1 : i in [1..#S]]);
  Gr2 := CanonicalGraph(Gr);
  _, gamma := IsIsomorphic(Gr2, Gr : IgnoreLabels := true);
  return { gamma(VertexSet(Gr2).i) : i in [1..#S] };
end intrinsic;


intrinsic ColumnStabilizer(S::SeqEnum) -> GrpPerm
{ Takes a sequence of length k, returns the subgroup of Sym(k) leaving that sequence invariant.}
    k := #S;
    Vals := SequenceToSet(S);
    I := [ {i : i in [1..k] | S[i] eq val} : val in Vals];
    G := sub<Sym(k) | [Sym(k)!!Sym(I[i]) : i in [1..#I]]>;
    return G;
end intrinsic;

intrinsic ColumnStabilizer(S::ModTupFldElt) -> GrpPerm
{ Takes a vector of length k, returns the subgroup of Sym(k) leaving that sequence invariant.}
    return ColumnStabilizer(Eltseq(S));
end intrinsic;

// Border entries for a colouring: distinct colours become m, m+1, ...; 0 means one colour.
function _border_colours(Colours, n, m)
  if Colours cmpeq 0 then
    return [m : i in [1..n]];
  end if;
  cs := {@ c : c in Colours @};
  return [m + Index(cs, c) - 1 : c in Colours];
end function;

intrinsic ColumnStabilizer(M::Mtrx : RowColours := 0, ColColours := 0, RSTRCT := 0) -> GrpPerm
{ Takes a matrix with k columns, returns the action on columns of the
  matrix's automorphism group (as a subgroup of Sym(k)).
  RowColours / ColColours are sequences giving a colour for each row / column;
  only automorphisms preserving the colours are used.
  RSTRCT := <RowColours, ColColours> is accepted for backward compatibility. }
  nr := Nrows(M); nc := Ncols(M);
  require RSTRCT cmpeq 0 or (RowColours cmpeq 0 and ColColours cmpeq 0):
    "Give either RSTRCT or RowColours/ColColours, not both.";
  if RSTRCT cmpne 0 then
    RowColours := RSTRCT[1];
    ColColours := RSTRCT[2];
  end if;
  require RowColours cmpeq 0 or #RowColours eq nr: "RowColours must have one entry per row.";
  require ColColours cmpeq 0 or #ColColours eq nc: "ColColours must have one entry per column.";

  if RowColours cmpeq 0 and ColColours cmpeq 0 then
    A := AutomorphismGroup(M);            // rows 1..nr, columns nr+1..nr+nc
    off := nr;
  else
    RNG := CoefficientRing(M);
    require Type(RNG) in {RngInt, FldRat}:
      "With colours, the matrix must be over the integers or rationals.";
    m := Min(Eltseq(M));
    B := HorizontalJoin(Transpose(Matrix(RNG, [[m - 1] cat _border_colours(RowColours, nr, m)])),
                        VerticalJoin(Matrix(RNG, [_border_colours(ColColours, nc, m)]), M));
    A := AutomorphismGroup(B);            // border row is point 1, border column is point nr+2
    off := nr + 2;
  end if;
  return sub< Sym(nc) | [ Sym(nc) | [ (off+j)^g - off : j in [1..nc] ] : g in Generators(A) ] >;
end intrinsic;

// NOTE BUG These can be switched back in once a Magma bug is fixed
// function _colour_classes(Colours, n)
//   if Colours cmpeq 0 then
//     return [1 : i in [1..n]];
//   end if;
//   cs := {@ c : c in Colours @};
//   return [Index(cs, c) : c in Colours];
// end function;
//
// // RowColours / ColColours are sequences giving a colour for each row / column;
// // only automorphisms preserving the colours are used.
// // RSTRCT := <RowColours, ColColours> is accepted for backward compatibility.
// intrinsic ColumnStabilizer(M::Mtrx : RowColours := 0, ColColours := 0, RSTRCT := 0) -> GrpPerm
// {
//   Takes a matrix with k columns, returns the action on columns of the
//   matrix's automorphism group (as a subgroup of Sym(k)).
// }
//   nr := Nrows(M); nc := Ncols(M);
//   require RSTRCT cmpeq 0 or (RowColours cmpeq 0 and ColColours cmpeq 0):
//     "Give either RSTRCT or RowColours/ColColours, not both.";
//   if RSTRCT cmpne 0 then
//     RowColours := RSTRCT[1];
//     ColColours := RSTRCT[2];
//   end if;
//   require RowColours cmpeq 0 or #RowColours eq nr: "RowColours must have one entry per row.";
//   require ColColours cmpeq 0 or #ColColours eq nc: "ColColours must have one entry per column.";
//   A := AutomorphismGroup(M : RowColours := _colour_classes(RowColours, nr),
//                                ColColours := _colour_classes(ColColours, nc));
//   return sub< Sym(nc) | [ Sym(nc) | [ (nr+j)^g - nr : j in [1..nc] ] : g in Generators(A) ] >;
// end intrinsic;


/*-------------------------------------------------------------------------
---------------------------------------------------------------------------*/

// The following gives a method to canonically sort a matrix.
make_graph := function(M, elts, row_colours, r_set, col_colours, c_set)
  local nr, nc, d, nl, colours, edges, i, j, r, c, Gr, base;
  nr := Nrows(M);
  nc := Ncols(M);
  d := nr + nc;
  nl := Ilog(2, #elts);
  if 2^nl lt #elts then
    nl +:= 1;
  end if;
  if d*nl ge 2^30 then
    error "Problem too large for graph construction";
  end if;
  assert 2^nl ge #elts;
  if row_colours cmpeq 0 then
    row_colours := [1: i in [1..nr]];
    base := 1;
  else
    assert #row_colours eq nr;
    row_colours := [Index(r_set, i) : i in row_colours];
    base := #r_set;
  end if;
  if col_colours cmpeq 0 then
  	col_colours := [base+1: i in [1..nc]];
  	ncolours := base + 1;
  else
    assert #col_colours eq nc;
    col_colours := [base+Index(c_set, i) : i in col_colours];
    ncolours := base + #c_set;
  end if;
  colours := row_colours cat col_colours;
  /* build up the edge set */
  edges := {};
  /* vertical edges */
  base :=0;
  for i :=0 to nl-2 do
    for j := 1 to d do
      Include(~edges, {base+j, base+j+d});
    end for;
    base +:=d;
  end for;
  /*
  for i := 0 to nl-2 do
    for j := 1 to d do
      Include(~edges, { i*d+j, (i+1)*d+j} );
    end for;
  end for;
   */
  /* horizontal edges */
  for r := 1 to nr do
    for c := 1 to nc do
      e := Index(elts, M[r,c]) -1;
      base := 0;
      while e gt 0 do
        if IsOdd(e) then
          Include(~edges, { base + r, base + nr + c} );
        end if;
        e := ShiftRight(e,1);
        base +:= d;
      end while;
    end for;
  end for;
  /* Set vertex labels to keep vertices at each level separate,
   * and to keep rows and columns separate.
   */
  Gr := Graph< nl*d | edges >;
  AssignVertexLabels(~Gr, &cat [ [j + i*ncolours : j in colours] : i in [0..nl-1]]);
  return Gr;
end function;

// Okay, so we have a layered graph corresponding to an edge colored graph.
// We need to recover the number of layers so we can determine edge colors.
graph_to_matrix := function(Gr, elts, nr, nc)
  local d, nl, V, M, i, rows, cols, r,c, base;
  V := VertexSet(Gr);
  nl := Ilog(2, #elts);
  if 2^nl lt #elts then
    nl +:= 1;
  end if;
  d := nr+nc;
  assert #V eq d*nl;
  //nr := Minimum({(Index(v) -1) mod d : v in &join{Neighbors(V.(d*i+1)) : i in [0..nl-1]}} diff {0});
  //nc := d - nr;
  /*
  rows := [[r] : r in [1..nr]];
  cols := [[c] : c in [1..nc]];
  base := 0;
  for i in [1..nl-1] do
    base +:= d;
    for r in rows do
      Include(~r, )
  */
  rows := [ [ V.(d*base+s) : base in [0..nl-1]
                | exists(s){s : s in [1..nr]
                      | (base eq 0 and r eq s) or (base ne 0 and Self(base) adj V.(d*base+s)) } ]
            : r in [1..nr] ];
  cols := [ [ V.(d*base +nr + s) : base in [0..nl-1]
                | exists(s){s : s in [1..nc]
                      | (base eq 0 and nr+c eq nr+s) or (base ne 0 and Self(base) adj V.(d*base +nr + s)) } ]
            : c in [1..nc] ];
  M := Matrix( [ [ elts[&+{Integers()|
                       ShiftLeft(1,base-1)
                         : base in [1..nl] | rows[r][base] adj cols[c][base]
                     } +1 ]  : c in [1..nc] ] :r in [1..nr] ] );
  return M;
end function;

/* ---------------- To convert from graph Gr back to matrix M:--------------------
 * For each pair (r,c), put together the list (where V=V(Gr))
 * { k : k in V | V[k*d + r] ~ V[k*d + nr + c] }
 * That can get translated back to an r in [1..#elts],
 * translated again to elts[r]
 */
intrinsic CanonicalSortedMatrix(M::Mtrx : RowColours := 0, ColColours := 0, Al := "Default") -> Mtrx
{Returns a canonically sorted matrix, according to the CanonicalGraph intrinsic}
  R := BaseRing(Parent(M));

  eset := Seqset(Eltseq(M));
  /* Trivial cases */
  if #eset le 1 then
    return M;
  end if;
  if IsFinite(R) then
    elts := {@ x : x in R | x in eset @};          // ring enumeration order
  else
    elts := {@ x : x in Reverse(Sort(Setseq(eset))) @};   // descending, as before
  end if;
  r_set := RowColours cmpeq 0 select 0 else {@ c : c in RowColours @};
  c_set := ColColours cmpeq 0 select 0 else {@ c : c in ColColours @};
  Gr := make_graph(M, elts, RowColours, r_set, ColColours, c_set);
  CGr := CanonicalGraph(Gr);
  CM := graph_to_matrix(CGr, elts, Nrows(M), Ncols(M));
  if CoefficientRing(CM) ne R then
    CM := ChangeRing(CM,R);
  end if;
  return CM;
end intrinsic;


/*-------------------------------------------------------------------------
---------------------------------------------------------------------------*/


intrinsic RemoveIsomorphic(~MSEQ::SeqEnum[Mtrx]
            : RowColours := 0, ColColours := 0, RSTRCT := 0)
{
  Takes a sequence of matrices,
  returns a collection of isomorphism class representatives.
}

  require RSTRCT cmpeq 0 or (RowColours cmpeq 0 and ColColours cmpeq 0):
  "Give either RSTRCT or RowColours/ColColours, not both.";
  if RSTRCT cmpne 0 then
    RowColours := RSTRCT[1];
    ColColours := RSTRCT[2];
  end if;
  i := 1;
  REPS := {};
  while i le #MSEQ do
    A := CanonicalSortedMatrix(MSEQ[i] : RowColours := RowColours, ColColours := ColColours);
    if A in REPS then
      Remove(~MSEQ, i);
    else
      Include(~REPS, A);
      i +:= 1;
    end if;
  end while;
end intrinsic;

intrinsic RemoveIsomorphic(~MSET::SetEnum[Mtrx]
            : RowColours := 0, ColColours := 0, RSTRCT := 0)
{
  Takes a set of matrices,
  returns a collection of isomorphism class representatives.
}
  MSEQ := Setseq(MSET);
  RemoveIsomorphic(~MSEQ: RowColours:=RowColours, ColColours:=ColColours, RSTRCT:=RSTRCT);
  MSET := Seqset(MSEQ);
end intrinsic;
