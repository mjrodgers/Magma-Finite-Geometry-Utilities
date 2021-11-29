freeze;

/* -------------------------------------------------------------------------//
// -------------------------------------------------------------------------//
  Allows creation of a Process P := SubsetProcess(Set::S)
  which allows iteration through the subsets of S,
  beginning with the empty set.
  We also have the standard "Process" commands:
    IsEmpty(P)
    Current(P)
    CurrentLabel(P)
    Advance(P)
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
    return (p[3] eq p[2]);
end intrinsic;

intrinsic InternalNextSubset(~p::Tup)
{Moves the subset process tuple p to its next subset}
  error if InternalSubsetProcessIsEmpty(p), "Process finished";

  p[3] +:= 1;
end intrinsic;

intrinsic InternalExtractSubset(p::Tup) -> { }
{Returns the current subset of the transitive group process tuple p}
    error if InternalSubsetProcessIsEmpty(p), "Process finished";

    return {p[1][i] : i in IntToSet(p[3]) };
end intrinsic;

intrinsic InternalExtractSubsetLabel(p::Tup) -> RngIntElt, SetEnum
{Returns the index of the current subset, along with the parent set.}
    error if InternalSubsetProcessIsEmpty(p), "Process finished";

    return p[3], p[1];
end intrinsic;

intrinsic SubsetProcess(S::SetEnum) -> Process
{Gives a process for iterating through all subsets of S.}
  tup := <SetToIndexedSet(S), 2^#S, 0 >;

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
  tup := < S, 2^#S, 0 >;

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
