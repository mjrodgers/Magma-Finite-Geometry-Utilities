freeze;

intrinsic ObjectFromFile(fname::MonStgElt) -> Any
{ Reads a file written in Magma format,
returns and object defined by that code. }
  try
    s := Read(fname);
    OBJ := eval s;
  catch ERR
    error ERR;
  end try;
  return OBJ;
end intrinsic;


intrinsic qBinom(n::RngIntElt, k::RngIntElt, q::RngIntElt) -> RngIntElt
{ Returns the q-binomial coefficient (n,k)_q }
requirege q, 1;
requirege k, 0;
requirege n, k;
  N := 1;
  for i in [0..(k-1)] do
    N := N*(q^(n-i) -1);
  end for;
  D := 1;
  for i in [1..k] do
    D := D*(q^(i) -1);
  end for;
  return (N div D);
end intrinsic;


intrinsic qBinomPoly(n::RngIntElt, k::RngIntElt) -> RngUPolElt
{ Returns polynomial associated with q-binomial coefficient (n,k)_x }
requirege k, 0;
requirege n, k;
  P := PolynomialRing(Integers());
  x := P.1;
  N :=1;
  for i in [0..(k-1)] do
    N := N*(x^(n-i) -1);
  end for;
  D := 1;
  for i in [1..k] do
    D := D*(x^(i) -1);
  end for;
  return (N div D);
end intrinsic;
