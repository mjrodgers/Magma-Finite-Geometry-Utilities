freeze;

/* -------------------------------------------------------------------------//
// -------------------------------------------------------------------------//
  This just provides some useful intrinsic functions I haven't fit into a more well-named collection.
  ObjectFromFile(fname::MonStgElt)
    this reads a Magma object from a file, created using the PrintFileMagma(O) command,
    and returns the object into the currently running magma process.
    There are a couple of Magma object types that don't write all their data correctly,
    and they may cause problems (associative arrays being one example).
  qBinom(n,k,q)
    returns the q-binomial coefficient (n,k)_q
  qBinomPoly(n,k)
    returns the q-binomial coefficient in polynomial form
// -------------------------------------------------------------------------//
// -------------------------------------------------------------------------*/


intrinsic ObjectFromFile(fname::MonStgElt) -> Any
{
  Reads a file written in Magma format,
  returns an object defined by that code.
}
  return eval Read(fname);
end intrinsic;


intrinsic qBinom(n::RngIntElt, k::RngIntElt, q::RngIntElt) -> RngIntElt
{
  Returns the q-binomial coefficient (n,k)_q
}
requirege q, 1;
// requirege k, 0;
// requirege n, k;
  if (n lt k) or (k lt 0) then
    return 0;
  end if;
  if q eq 1 then
    return Binomial(n, k);
  end if;
  k := Min(k, n-k);
  r := 1;
  for i in [0..(k-1)] do
    r := (r*(q^(n-i) - 1)) div (q^(i+1) - 1);
  end for;
  return r;
end intrinsic;


// REVIEW: Can we use exact divisions at the intermediate steps here,
// as for `qBinom`?
intrinsic qBinomPoly(n::RngIntElt, k::RngIntElt : PRing:=PolynomialRing(Integers())) -> RngUPolElt
{
  Returns polynomial associated with q-binomial coefficient (n,k)_x
}
  if (n lt k) or (k lt 0) then
    return Zero(PRing);
  end if;
  x := PRing.1;
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


intrinsic qPower(q::RngIntElt, x::.) -> FldRatElt
{
  The exact power q^x for an integer or half-integral rational x
  (q must be a square if x is not an integer).
}
  require Type(x) in {RngIntElt, FldRatElt}: "x must be an integer or a rational";
  x := Rationals()!x;
  if Denominator(x) eq 1 then
    return (Rationals()!q)^(Integers()!x);
  end if;
  require Denominator(x) eq 2: "x must lie in (1/2)Z";
  ok, rq := IsSquare(q);
  require ok: "a half-integral exponent needs q to be a square";
  return (Rationals()!rq)^Numerator(x);
end intrinsic;
