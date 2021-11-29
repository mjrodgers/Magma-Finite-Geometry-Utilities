freeze;
// Tools for classifying objects based on isomorphism testing.


intrinsic CanonicalVertexSet(S::Set, Gr::Graph) -> SetEnum
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

intrinsic ColumnStabilizer(M::Matrix
                    :  RSTRCT := <[1 : i in [1..Nrows(M)]],
			                            [1 : i in [1..Ncols(M)]]>) -> GrpPerm
{ Takes a matrix with k columns,
returns the column representation of the
matrices automorphism group
(as a subgroup of SYm(k)).}
  RNG := CoefficientRing(M);
  MGRP, _, proj := DirectProduct([Sym(1), Sym(Nrows(M)), Sym(1), Sym(Ncols(M))]);
  A := HorizontalJoin(Transpose(Matrix(RNG, [[-1] cat RSTRCT[1]])),
    VerticalJoin(Matrix(RNG, [RSTRCT[2]]), M));
  return proj[4](AutomorphismGroup(A));
end intrinsic;



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
intrinsic CanonicalSortedMatrix(M::Mtrx : RowColours := 0, ColColours := 0, Al := "Default") -> GrpPerm
{Returns a canonically sorted matrix, according to the CanonicalGraph intrinsic}
  R := BaseRing(Parent(M));
  elts := {R|};
  elts_mset := {*R|*};
  for i := 1 to Nrows(M) do
    elts_i := Eltseq(M[i]);
    elts join:= SequenceToSet(elts_i);
    elts_mset join:= SequenceToMultiset(elts_i);
  end for;
  /* Trivial cases */
  if #elts le 1 then
    return M;
  end if;
  elts := SetToSequence(elts);
  //----------------sort_cmp: Modify it here? Or apply a sorting after?
  /*
  sort_cmp := function(x,y)
    return Multiplicity(elts_mset, y) - Multiplicity(elts_mset, x);
  end function;
   */
  sort_cmp := function(x,y)
    return y-x;
  end function;
  Sort(~elts, sort_cmp);
  elts := {@ x : x in elts @};
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
            : RSTRCT := <[1 : i in [1..Nrows(M)]], [1 : i in [1..Ncols(M)]]
              where M is Rep(MSEQ)>)
{
  Takes a sequence of matrices,
  returns a collection of isomorphism class representatives.
  Optional argument RSTRCT can be used to give labels on rows/columns
  that must be preserved.
}
  i := 1;
  REPS := {};
  while i lt #MSEQ do
    n := #MSEQ;
    A := CanonicalSortedMatrix(MSEQ[i] : RowColours := RSTRCT[1], ColColours := RSTRCT[2]);
    if A in REPS then
      Remove(~MSEQ, i);
    else
      Include(~REPS, A);
      i +:= 1;
    end if;
  end while;
end intrinsic;

intrinsic RemoveIsomorphic(~MSET::SetEnum[Mtrx]
            : RSTRCT := <[1 : i in [1..Nrows(M)]], [1 : i in [1..Ncols(M)]]
              where M is Rep(MSET)>)
{
  Takes a set of matrices,
  returns a collection of isomorphism class representatives.
  Optional argument RSTRCT can be used to give labels on rows/columns
  that must be preserved.
}
  MSEQ := Setseq(MSET);
  RemoveIsomorphic(~MSEQ: RSTRCT := RSTRCT);
  MSET := Setseq(MSEQ);
end intrinsic;
