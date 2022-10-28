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
