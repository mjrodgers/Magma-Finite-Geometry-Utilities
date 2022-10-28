freeze;

/* -------------------------------------------------------------------------//
// -------------------------------------------------------------------------//
  Allows the creation of several Processes to iterate through
  collections of subsets and subspaces.
  These all allow the standard "Process" commands:
    IsEmpty(P)
    Current(P)
    CurrentLabel(P)
    Advance(P)
  The following Process constructors are defined:
    P := SubsetProcess(n::RngIntElt)
      Allows iterating through all subsets of {1..n}, beginning with the empty set.
    P := SubsetProcess(S::SetIndx)
    P := SubsetProcess(S::SetEnum)
      allows iteration through the subsets of S, beginning with the empty set.
    TODO: Multiset version?
    P := SubsetProcess(n::RngIntElt, k::RngIntElt)
    P := SubsetProcess(S::SetIndx, k::RngIntElt)
    P := SubsetProcess(S::SetEnum, k::RngIntElt)
      As above, but only iterates through subsets of size k.
    P := SubspaceProcess(U::ModTupFld, k::RngIntElt)
      allows iteration through all subspaces of a finite vector space U
      having dimension k.
    TODO: For completion, should have a generic version that goes through ALL subspaces.
// -------------------------------------------------------------------------//
// -------------------------------------------------------------------------*/

intrinsic IntToSet(n::RngIntElt) -> SetEnum[RngIntElt]
{ Takes an integer, returns support of binary representation as an integer set }
  SET := {Integers()|};
  i := 0;
  while n ne 0 do
    i +:= 1;
    if (ModByPowerOf2(n,1) eq 1) then
      Include(~SET,i);
    end if;
    n  := ShiftRight(n,1);
  end while;
  return SET;
end intrinsic;

intrinsic InternalSubsetProcessIsEmpty(p::Tup) -> BoolElt
{Returns true iff the transitive group process has passed its last group}
    return (p[2] ge p[1]);
end intrinsic;

intrinsic InternalNextSubset(~p::Tup)
{Moves the subset process tuple p to its next subset}
  error if InternalSubsetProcessIsEmpty(p), "Process finished";
  p[2] +:= 1;
end intrinsic;

intrinsic InternalExtractSubset(p::Tup) -> { }
{Returns the current subset of the transitive group process tuple p}
    error if InternalSubsetProcessIsEmpty(p), "Process finished";
    return { i : i in IntToSet(p[2]) };
end intrinsic;

intrinsic InternalExtractSubsetLabel(p::Tup) -> RngIntElt, SetEnum
{Returns the index of the current subset, along with the parent set.}
    error if InternalSubsetProcessIsEmpty(p), "Process finished";
    return p[2];
end intrinsic;


intrinsic SubsetProcess(n::RngIntElt) -> Process
{Gives a process for iterating through all subsets from a set of size n.}
tup := <2^n, 0>;
P := InternalCreateProcess(
      "Subsets",
      tup,
      InternalSubsetProcessIsEmpty,
      InternalNextSubset,
      InternalExtractSubset,
      InternalExtractSubsetLabel
    );

return P;
end intrinsic;

intrinsic SubsetProcess(S::SetIndx) -> Process
{Gives a process for iterating through all subsets of S.}
  P := SubsetProcess(#S);
  f := func<s | {S[i] : i in s} >;
  return ModifyProcess(P, f);
end intrinsic;

intrinsic SubsetProcess(S::SetEnum) -> Process
{Gives a process for iterating through all subsets of S.}
  return SubsetProcess(SetToIndexedSet(S));
end intrinsic;


intrinsic InternalkSubsetProcessIsEmpty(p::Tup) -> BoolElt
{Returns true iff the transitive group process has passed its last group}
    return p[4];
end intrinsic;

intrinsic InternalNextkSubset(~p::Tup)
{Moves the subset process tuple p to its next subset}
  error if InternalkSubsetProcessIsEmpty(p), "Process finished";
  if p[3] le 0 then
    p[4] := true;
  else
    p[2] := TransversalProcessNext(p[1]);
    p[3] := TransversalProcessRemaining(p[1]);
  end if;
end intrinsic;

intrinsic InternalExtractkSubset(p::Tup) -> { }
{Returns the current subset of the transitive group process tuple p}
    error if InternalkSubsetProcessIsEmpty(p), "Process finished";
    return (p[5])(p[2]);
end intrinsic;

intrinsic InternalExtractkSubsetLabel(p::Tup) -> RngIntElt, SetEnum
{Returns the index of the current subset, along with the parent set.}
    error if InternalkSubsetProcessIsEmpty(p), "Process finished";
    return p[2];
end intrinsic;

// TODO: should create simple workarounds when k=0 or k=n.
// This can probably be modified to be much more efficient by avoiding the use of TransversalProcess
intrinsic SubsetProcess(n::RngIntElt, k::RngIntElt) -> Process
{Gives a process for iterating through all subsets from a set of size n having size k.}
  requirerange k, 0, n;
  P := TransversalProcess(Sym(n), DirectProduct(Sym(k),Sym(n-k)));
  f := func<sigma | {1..k}^(sigma^-1)>;
  info := <P, TransversalProcessNext(P), TransversalProcessRemaining(P), false, f>;
  P := InternalCreateProcess(
        "kSubsets",
        info,
        InternalkSubsetProcessIsEmpty,
        InternalNextkSubset,
        InternalExtractkSubset,
        InternalExtractkSubsetLabel
      );

  return P;
end intrinsic;

intrinsic SubsetProcess(S::SetIndx, k::RngIntElt) -> Process
{Gives a process for iterating through all subsets of S.}
  requirerange k, 0, #S;
  P := SubsetProcess(#S,k);
  f := func<s | {S[i] : i in s} >;
  return ModifyProcess(P, f);
end intrinsic;

intrinsic SubsetProcess(S::SetEnum, k::RngIntElt) -> Process
{Gives a process for iterating through all subsets of S.}
  requirerange k, 0, #S;
  return SubsetProcess(SetToIndexedSet(S), k);
end intrinsic;



// For subspaces:

// Takes an integer Q. returns a sequence of Fq elements.
function qAry(Q,q)
  F := FiniteField(q);
  d := Degree(F);
  p := #BaseField(F);

  // Do we want to allow empty sequence as a result?
  // if not, we should use a do->until
  S := [];
  while Q ne 0 do
    R  := Q mod p;
    Q  := Q div p;
    Append(~S,R);
  end while;

  if (#S mod d) ne 0 then
    S cat:= [0 : i in [1..((-#S) mod d)]];
  end if;

  S2 := [F|];
  for i in [1..(#S div d)] do
    s2 := S[(i-1)*d + 1 .. i*d];
    Append(~S2, F!s2);
  end for;
  return S2;
end function;

function MapFunc(n, q, S)
  F := FiniteField(q);
  k := #S;
  positions := [ [i,j] : i in [1..k], j in [1..n] | j gt S[i] and not j in S];
  function f( u)
    u := qAry(u, q);
    u cat:= [0 : i in [1..#positions - #u]];
    K := Matrix(F, k, n, [<i,j, x >
              where i,j is Explode(positions[c])
                where x is u[c] : c in [1..#positions]]);
    for c in [1..k] do
        K[c,S[c]] := 1;
    end for;

    return RowSpace(K);
  end function;

  return f, q^(#positions)-1;
end function;



intrinsic InternalSubspaceProcessIsEmpty(p::Tup) -> BoolElt
{Returns true iff the transitive group process has passed its last group}
    return IsEmpty(p[2]);
end intrinsic;

intrinsic InternalNextSubspace(~p::Tup)
{Moves the subset process tuple p to its next subset}
  error if InternalSubspaceProcessIsEmpty(p), "Process finished";
  if p[3][2] ge p[3][3] then
    Advance(~(p[2]));
    if IsEmpty(p[2]) then
      p[3][1] := {@ @};
      p[3][2] := 0;
      p[3][3] := -1;
    else
      p[3][1] := Sort(SetToIndexedSet(Current(p[2])));
      p[3][2] := 0;
      f, M := MapFunc(Dimension(p[1]), #CoefficientField(p[1]), p[3][1]);
      p[3][3] := M;
      p[4] := f;
    end if;
  else
    p[3][2] +:= 1;
  end if;
end intrinsic;





intrinsic InternalExtractSubspace(p::Tup) -> { }
{Returns the current subset of the transitive group process tuple p}
    error if InternalSubspaceProcessIsEmpty(p), "Process finished";
    // I will contain ordered pair: k-set, and an integer
    // Do we need to coerce the subspace to be in U?
    // U := p[1];
    // q := #CoefficientField(U);
    I := p[3];
    phi := p[4];

    return phi(I[2]);
end intrinsic;

intrinsic InternalExtractSubspaceLabel(p::Tup) -> RngIntElt, SetEnum
{Returns the index of the current subset, along with the parent set.}
    error if InternalSubspaceProcessIsEmpty(p), "Process finished";
    return p[3];
end intrinsic;



intrinsic SubspaceProcess(U::ModTupFld, k::RngIntElt) -> Process
{Gives a process for iterating through all subsets from a set of size n having size k.}
  require IsFinite(CoefficientField(U)): "Coefficient field must be finite.";
  requirerange k, 0, Dimension(U);
  n := Dimension(U);
  Fq := CoefficientField(U);
  Fp := BaseField(Fq);


  P1 := SubsetProcess(n,k);
  S := Sort(SetToIndexedSet(Current(P1)));
  f, M := MapFunc(n,#Fq, S);
  I := <S, 0, M>;

  info := <U, P1, I, f>;

  P := InternalCreateProcess(
        "Subspace",
        info,
        InternalSubspaceProcessIsEmpty,
        InternalNextSubspace,
        InternalExtractSubspace,
        InternalExtractSubspaceLabel
      );

  return P;
end intrinsic;
