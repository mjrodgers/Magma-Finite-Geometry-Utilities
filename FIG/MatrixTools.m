freeze;

/* -------------------------------------------------------------------------//
// -------------------------------------------------------------------------//
  Tools for working with incidence matrices.
  Provided intrinsics:
    IncidenceMatrix(S1::SetIndx, S2::SetIndx, I::Map)
    IncidenceMatrix(S1::SetEnum, S2::SetEnum, I::Map)
      I should be a map from S1 x S2 -> Booleans,
      use this map to construct an incidence matrix.
      If S1 and S2 are unordered, we apply an arbitrary ordering and
      return the ordered sets.
    IncidenceMatrix(S::SetIndx, I::Map)
    intrinsic IncidenceMatrix(S::SetEnum, I::Map)
      As above, but we take S1 = S2 = S and return a symmetric matrix.
      TODO: We should catch errors arising from unsupported maps
    TDColSumMatrix(M::Mtrx,P1::SeqEnum[SetEnum],P2::SeqEnum[SetEnum])
    TDColSumMatrix(M::Mtrx,P::SeqEnum[SetEnum])
      Return the #P1 x #P2 column sum matrix C associated with the
      tactical decomposition of M determined by the partition.
      TODO: Ensure P1 and P2 are partitions of the rows and columns.
      TODO: there is no reason that we need P1 and P2 to be ordered, they are simply partitions.
            we can just order them arbitrarily.
// -------------------------------------------------------------------------//
// -------------------------------------------------------------------------*/


// Want 3 possible map types: SxS -> {0,1}, SxS -> {true, false}, (S -> Pow(S) : not implemented)
intrinsic IncidenceMatrix(S1::SetIndx, S2::SetIndx, I::Map) -> AlgMatElt
{ Returns a symmetric 0-1 matrix indexed by elements of S, incidence determined by I. }
  truthy := map< Booleans() -> Integers() | x:-> x select 1 else 0>;
  if Codomain(I) cmpeq Booleans() then
    I := I*truthy;
  end if;
  return Matrix(
      Rationals(),
      [ [ I(S1[i],S2[j]) : j in [1..#S2] ] :  i in [1..#S1] ]
  );
end intrinsic;

intrinsic IncidenceMatrix(S1::SetEnum, S2::SetEnum, I::Map) -> AlgMatElt, SetIndx, SetIndx
{ Returns a symmetric 0-1 matrix indexed by elements of S, incidence determined by I. }
  S1 := SetToIndexedSet(S1);
  S2 := SetToIndexedSet(S2);
  return IncidenceMatrix(S1, S2 ,I), S1, S2;
end intrinsic;


// NOTE : we probably don't want to do this as a symmetric matrix (maybe allow as an optional parameter?)
intrinsic IncidenceMatrix(S::SetIndx, I::Map) -> AlgMatElt
{ Returns a symmetric 0-1 matrix indexed by elements of S, incidence determined by I. }
  truthy := map< Booleans() -> Integers() | x:-> x select 1 else 0>;
  if Codomain(I) cmpeq Booleans() then
    I := I*truthy;
  end if;
  return SymmetricMatrix(
      Rationals(),
      &cat[ [ I(S[i],S[j]) : j in [1..i] ] : i in [1..#S] ]
  );
end intrinsic;


intrinsic IncidenceMatrix(S::SetEnum, I::Map) -> AlgMatElt, SetEnum
{ Returns a symmetric 0-1 matrix indexed by elements of S, incidence determined by I. }
  S := SetToIndexedSet(S);
  return IncidenceMatrix(S,I), S;
end intrinsic;


// TODO: there is no reason that we need P1 and P2 to be ordered, they are simply partitions.
//       we can just order them arbitrarily.
// TODO: We should check that they actually partition the row/column sets though.
intrinsic TDColSumMatrix(M::Mtrx,P1::SeqEnum[SetEnum],P2::SeqEnum[SetEnum]) -> Mtrx, Map
{ P1 partitions the rows, P2 partitions the columns, returns column sum matrix }
  R := CoefficientRing(M);
  V := RSpace(R, Nrows(M));
  CSelMat := Matrix(R, Ncols(M), #P2, [<Rep(P2[i]), i, 1> : i in [1..#P2]]);
  CSumMat := Matrix([CharacteristicVector(V,r) : r in P1]);
  return CSumMat*(M*CSelMat),
          hom< RSpace(R, #P1) -> V | [v*CSumMat : v in Basis(RSpace(R, #P1))]>;
end intrinsic;


intrinsic TDColSumMatrix(M::Mtrx,P::SeqEnum[SetEnum]) -> Mtrx, Map
{ For symmetric matrix M, P a partition of rows/columns, returns column sum matrix }
  return TDColSumMatrix(M,P,P);
end intrinsic;
