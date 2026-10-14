freeze;

// Methods for generating sets corresponding to points and lines
// of a projective space.

// Methods for generating sets corresponding to points and lines
// of a projective space.

// TODO : avoid these &join constructors, one pure set constructor or loop with `Include(~)`

intrinsic Points(U::ModTupFld) -> SetEnum[ModTupFldElt]
{ Return the set of normalized vectors in U. }
require IsFinite(CoefficientField(U)): "Coefficient field must be finite.";
  B := Basis(U);
  n := #B;
  return {B[i] + u : u in sub<U| {B[r] : r in [i+1..n]}>, i in [1..n] };
end intrinsic;


intrinsic LineSubs(U::ModTupFld) -> { }
{ Returns the set of 2-dimensional subspaces of U. }
require IsFinite(CoefficientField(U)): "Coefficient field must be finite.";
  B  := Basis(U);
  n  := Dimension(U);
  LS := {sub<U | B[i]+u, B[j]+v>
                       : u in sub<U| {B[r] : r in [i+1..n] | r ne j}>, i in [1..j-1],
                         v in sub<U| {B[r] : r in [j+1..n]}>, j in [n..2 by -1]};

  return LS;
end intrinsic;
// NOTE to loop over LineSubs in code:
/************************************
for j in [n..2 by -1], v in sub<U| {B[r] : r in [j+1..n]}>, i in [1..j-1], u in sub<U| {B[r] : r in [i+1..n] | r ne j}> do
  ell := sub<U | B[i]+u, B[j]+v>;
  ...
end for;
*************************************/
