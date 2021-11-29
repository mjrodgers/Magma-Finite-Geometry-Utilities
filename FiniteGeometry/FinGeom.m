freeze;
// Methods for generating subspaces of vector spaces.
// Will eventually add methods for generating k-spaces,
// and processes for iterating through these objects.


intrinsic Points(U::ModTupFld) -> SetEnum[ModTupFldElt]
{ Return the set of normalized vectors in U. }
require IsFinite(CoefficientField(U)): "Coefficient field must be finite.";
  B := Basis(U);
  n := #B;
  return &join{ {B[i] + u : u in sub<U| {B[r] : r in [i+1..n]}>}
                : i in [1..n] };
end intrinsic;

intrinsic LineSubs(U::ModTupFld) -> { }
{ Returns the set of 2-dimensional subspaces of U. }
require IsFinite(CoefficientField(U)): "Coefficient field must be finite.";
  F  := BaseField(U);
  B  := Basis(U);
  n  := Dimension(U);
  LS := &join{ {sub<U | B[i]+u, B[j]+v>
                        : u in sub<U| {B[r] : r in [i+1..n] | r ne j}>,
                          v in sub<U| {B[r] : r in [j+1..n]}>
               } : j in [i+1..n], i in [1..(n-1)] };
  return LS;
end intrinsic;
