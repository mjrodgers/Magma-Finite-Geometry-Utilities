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
P := CreateProcess(
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




// For subsets of fixed size k
intrinsic InternalkSubsetProcessIsEmpty(p::Tup) -> BoolElt
{Returns true iff the transitive group process has passed its last group}
    // n, k, state := Explode(p);
    return p[3][1] gt p[1]-p[2]+1;
end intrinsic;

intrinsic InternalNextkSubset(~p::Tup)
{Moves the subset process tuple p to its next subset}
    error if InternalkSubsetProcessIsEmpty(p), "Process finished";
    // n, k, state := Explode(p);
    b := p[1]-p[2];
    for i in [p[2]..1 by -1] do
        p[3][i] +:= 1;
        if p[3][i] gt (b+i) then
            continue;
        end if;
        for j in [i+1..p[2]] do
            p[3][j] := p[3][j-1] +1;
        end for;
        break;
    end for;
end intrinsic;

intrinsic InternalExtractkSubset(p::Tup) -> { }
{Returns the current subset of the transitive group process tuple p}
    error if InternalkSubsetProcessIsEmpty(p), "Process finished";
    return IndexedSet(p[3]);
end intrinsic;

intrinsic InternalExtractkSubsetLabel(p::Tup) -> RngIntElt
{Returns the index of the current subset.}
    error if InternalkSubsetProcessIsEmpty(p), "Process finished";
    if IsOne(p[1]) then
      return p[3][1];
    end if;
    r := Binomial(p[1], p[2]);
    i := 1;
    while i le p[2] do
        r -:= Binomial(p[1] - p[3][i], p[2]-i+1);
        i +:= 1;
        if p[2]-i+1 eq p[1]-p[3][i-1] then
            return r;
        end if;
    end while;
    return r;
end intrinsic;


// TODO: option for indexed set
// This is way slow for <n,k> = <20,10> compared to calling Subsets...
intrinsic SubsetProcess(n::RngIntElt, k::RngIntElt) -> Process
{Gives a process for iterating through all subsets from a set of size n having size k.}
  requirerange k, 0, n;

    if k eq 0 then
        return CreateProcess([{@ Integers()| @}]);
    elif k eq n then
        return CreateProcess([{@i : i in [1..n]@}]);
    elif k eq 1 then
        return CreateProcess([{@i@} : i in [1..n]]);
    end if;

    state := [Min(k-1, i) : i in [1..k]];
    info := <n, k, state>;
    InternalNextkSubset(~info);


    P := CreateProcess(
          "kSubsets",
          info,
          InternalkSubsetProcessIsEmpty,
          InternalNextkSubset,
          InternalExtractkSubset,
          InternalExtractkSubsetLabel
        );

    return P;
end intrinsic;




// TODO this should return an indexed set; but the `SetEnum` version should not.
intrinsic SubsetProcess(S::SetIndx, k::RngIntElt) -> Process
{Gives a process for iterating through all subsets of S.}
  requirerange k, 0, #S;
  P := SubsetProcess(#S, k);
  f := func<s | {S[i] : i in s} >;
  return ModifyProcess(P, f);
end intrinsic;

// TODO is there a way to do this without converting to an indexed set?
intrinsic SubsetProcess(S::SetEnum, k::RngIntElt) -> Process
{Gives a process for iterating through all subsets of S.}
  requirerange k, 0, #S;
  return SubsetProcess(SetToIndexedSet(S), k);
end intrinsic;


// For subspaces:

// Takes an integer Q. returns a sequence of Fq elements.
// function qAry(Q,q)
//   F := FiniteField(q);
//   d := Degree(F);
//   p := #BaseField(F);
//
//   // Do we want to allow empty sequence as a result?
//   // if not, we should use a do->until
//   S := [];
//   while Q ne 0 do
//     R  := Q mod p;
//     Q  := Q div p;
//     Append(~S,R);
//   end while;
//
//   if (#S mod d) ne 0 then
//     S cat:= [0 : i in [1..((-#S) mod d)]];
//   end if;
//
//   S2 := [F|];
//   for i in [1..(#S div d)] do
//     s2 := S[(i-1)*d + 1 .. i*d];
//     Append(~S2, F!s2);
//   end for;
//   return S2;
// end function;





function MapFunc(F, n, k, S, values)
  mat := ZeroMatrix(F, k, n);
  // values := qAry(F, u);
  pos := 1;
  for i in [1..k] do
    mat[i, S[i]] := 1;
    for j in [S[i]+1..n] do
      if j notin S then
        mat[i,j] := values[pos];
        pos +:=1;
      end if;
    end for;
  end for;
  return mat;
end function;



intrinsic SubspaceProcess(U::ModTupFld, k::RngIntElt) -> Process
{Gives a process for iterating through all subspaces of fixed dimension k from U.}
  require IsFinite(CoefficientField(U)): "Coefficient field must be finite.";
  requirerange k, 0, Dimension(U);
  Fq := CoefficientField(U);
  n := Dimension(U);
  B := BasisMatrix(U);

  P := SubspaceMatProcess(Fq, n, k);
  f := func<M | Image(M*B)>;

  return ModifyProcess(P, f);
end intrinsic;









// Generate sequence of Fq values for iterating cleanly
function _Fq_digit_values(Fq)
  q := #Fq;
  a := PrimitiveElement(Fq);
  vals := [ Zero(Fq) ];
  vals cat:= [ a^e : e in [0..q-2] ];
  return vals;
end function;


// Free positions for echelon kxn matrix with pivots given by S.
// This seems stupid...
function _free_positions(n, k, S)
  Is := [];  Js := [];
  ispiv := [ false : i in [1..n] ];
  for i in [1..k] do
    ispiv[Sp[i]] := true;
  end for;
  for i->s in S do
    for j in [s+1..n] do
      if not ispiv[j] then
        Append(~Is, i);  Append(~Js, j);
      end if;
    end for;
  end for;
  return Is, Js;
end function;

// vs. mine
function _create_positions(n, k, S)
  return [<i,j> : j in [s+1..n], i->s in S | j notin S];
end function;

// Initialize matrix (mine)
function _echelon_base(Fq, k, n, S)
  o := One(Fq);
  return Matrix(Fq, k, n, [<i, s, o> : i->s in S]);
end function;









function _echelon_IsEmpty(p)
  return p[7];
end function;


// info := <Fq, n, k, MProcess, SProcess, counter, done_flag>;
procedure _echelon_Advance(~p)
  Advance(~p[4]);
  if IsEmpty(p[4]) then
    Advance(~p[5]);
    if IsEmpty(p[5]) then
      p[7] := true;
      return;
    end if;
    // Need to reinitialize the MatrixSubprocess
    p[4] := SubspaceMatSubProcess(p[1], p[2], p[3], Current(p[5]));
  end if;
  p[6] +:=1;
end procedure;

function _echelon_Extract(p)
  return Current(p[4]);
end function;

function _echelon_Label(p)
  return p[6];
end function;



intrinsic SubspaceMatProcess(Fq::FldFin, n::RngIntElt, k::RngIntElt) -> Process
{Gives a process for iterating through all subspaces of fixed dimension k from U.}
  requirerange k, 0, n;
  if k eq 0 then
    return CreateProcess([ZeroMatrix(Fq, k, n)]);
  elif k eq n then
    return CreateProcess([IdentityMatrix(Fq, n)]);
  end if;

  Sproc := SubsetProcess(n,k);
  Mproc := SubspaceMatSubProcessNew(Fq, n, k, Current(Sproc));
  info := <Fq, n, k, Mproc, Sproc, 1, false>;

  return CreateProcess(
            "Echelon Matrices",
            info,
            _echelon_IsEmpty,
            _echelon_Advance,
            _echelon_Extract,
            _echelon_Label
  );

end intrinsic;








function _echelon_subprocess_IsEmpty(p)
  return p[7];
end function;


// info := < Fq, Fq_values, Matrix, position_list, values, index_counter, done_flag
procedure _echelon_subprocess_Advance(~p)
  q := #p[1];
  for t->pos in p[4] do
    d := p[5][t] + 1;
    i, j := pos[1], pos[2];
    if d lt q then
      p[5][t] := d;
      p[3][i,j] := p[2][d+1];
      p[6] +:=1;
      return;
    end if;
    p[5][t] := 0;
    p[3][i,j] := p[2][1];
  end for;
  p[7] := true;
end procedure;

function _echelon_subprocess_Extract(p)
  return p[3];
end function;

function _echelon_subprocess_Label(p)
  return p[6];
end function;


intrinsic SubspaceMatSubProcess(Fq::FldFin, n::RngIntElt, k::RngIntElt, S::SetIndx) -> Process
{Generate row reduced echelon matrices with fixed set S of pivots.}
  requirerange k, 0, n;
  require #S eq k: "The pivot set must have k elements";
  // npos := n*k - Binomial(k,2) - &+(S);
  Fq_vals := _Fq_digit_values(Fq);
  pos := _create_positions(n, k, S);
  M := _echelon_base(Fq, k, n, S);
  // info := < Fq, Fq_values, Matrix, position_list, values, index_counter, done_flag
  info := <Fq, Fq_vals, M, pos, [0 : i in [1..#pos]], 1, false>;

  return CreateProcess(
            "Echelon Matrices",
            info,
            _echelon_subprocess_IsEmpty,
            _echelon_subprocess_Advance,
            _echelon_subprocess_Extract,
            _echelon_subprocess_Label
  );
end intrinsic;





//---------------- block-materialised subprocess ----------------
// info = <Fq, alpha, zero, one, M, Wlo, block, idx, done, His, Jsh>
//   5:  M     base matrix: pivots + HI free entries, LO entries zero
//   6:  Wlo   subspace spanned by the LO matrix units (dim c)
//   7:  block [ M + w : w in Wlo ]   (length q^c)
//   8:  idx   1-based index into block
//   10/11:    HI free positions (first m-c of the free positions)

function _block_IsEmpty(p)
  return p[9];
end function;

procedure _block_Advance(~p)
  p[8] +:= 1;
  if p[8] le #p[7] then
    return;
  end if;
  // block exhausted: advance the HI odometer on M (field elements, as original)
  alpha := p[2];  z := p[3];  o := p[4];
  t := #p[10];
  while t ge 1 do
    i := p[10][t];
    j := p[11][t];
    if IsZero(p[5][i,j]) then
      p[5][i,j] := o;
      break;
    end if;
    p[5][i,j] *:= alpha;
    if IsOne(p[5][i,j]) then
      p[5][i,j] := z;
      t -:= 1;
    else
      break;
    end if;
  end while;
  if t eq 0 then
    p[9] := true;
    return;
  end if;
  p[7] := [ p[5] + w : w in p[6] ];   // C-level enumeration, one add per matrix
  p[8] := 1;
end procedure;

function _block_Extract(p)
  return p[7][p[8]];
end function;

function _block_Label(p)
  return p[8];
end function;


intrinsic SubspaceMatSubProcessNew(Fq::FldFin, n::RngIntElt, k::RngIntElt, S::SetIndx) -> Process
{RREF k x n matrices over Fq with pivot columns exactly S, in blocks of ~2^12.}
  requirerange k, 0, n;
  require #S eq k: "The pivot set must have k elements";
  q := #Fq;
  pos := _create_positions(n, k, S);

  // what is this for?
  m := #pos;
  c := m;
  // LO dimension: q^c ~ 2^12
  while c gt 0 do
     if q^c * (k*n) le 2^20 then
       break;
     end if;   // ~1M entries per block
    c -:= 1;
  end while;


  MS := KMatrixSpace(Fq, k, n);
  o := One(Fq);
  if c eq 0 then
    Wlo := sub< MS | [ ZeroMatrix(Fq, k, n) ] >;
  else
    units := [ Matrix(Fq, k, n, [<pos[t][1], pos[t][2], o>]) : t in [m-c+1..m] ];
    Wlo := sub< MS | units >;
  end if;


  M := _echelon_base(Fq, k, n, S);
  His := [ pos[t][1] : t in [1..m-c] ];
  Jsh := [ pos[t][2] : t in [1..m-c] ];
  info := <Fq, PrimitiveElement(Fq), Zero(Fq), o, M, Wlo,
           [ M + w : w in Wlo ], 1, false, His, Jsh>;
  return CreateProcess(
          "Echelon Matrices",
          info,
          _block_IsEmpty,
          _block_Advance,
          _block_Extract,
          _block_Label);
end intrinsic;





// TODO : do PointIterator that just generates normalized vectors


//
//
// function _Fq_cart_product_process_IsEmpty(p)
//   return p[3];
// end function;
//
// procedure _Fq_cart_product_process_Next(~p)
//   z, o, alpha := Zero(p[1]), One(p[1]), PrimitiveElement(p[1]);
//   for i in [#p[2]..1 by -1] do
//     if IsZero(p[2][i]) then
//       p[2][i] := o;
//       break;
//     end if;
//     p[2][i] *:= alpha;
//     if IsOne(p[2][i]) then
//       if i eq 1 then
//         p[3] := true;
//         break;
//       end if;
//       p[2][i] := z;
//       continue;
//     else
//       break;
//     end if;
//   end for;
// end procedure;
//
// procedure _Fp_cart_product_process_Next(~p)
//   z, o := Zero(p[1]), One(p[1]);
//   for i in [#p[2]..1 by -1] do
//     p[2][i] +:=1;
//     if IsZero(p[2][i]) then
//       if i eq 1 then
//         p[3] := true;
//         break;
//       end if;
//       continue;
//     else
//       break;
//     end if;
//   end for;
// end procedure;
//
// function _Fq_cart_product_process_Extract(p)
//   return p[2];
// end function;
//
// function _Fp_cart_product_process_ExtractLabel(p)
//   label := 1;
//   pow := 1;
//   q := #p[1];
//   for i in [#p[2]..1 by -1] do
//     if not IsZero(p[2][i]) then
//       label +:= pow * Integers(p[2][i]);
//     end if;
//     pow *:= q;
//   end for;
//   return label;
// end function;
//
// function _Fq_cart_product_process_ExtractLabel(p)
//   label := 1;
//   pow := 1;
//   q := #p[1];
//   for i in [#p[2]..1 by -1] do
//     if not IsZero(p[2][i]) then
//       label +:= pow * (1+Log(p[2][i]));
//     end if;
//     pow *:= q;
//   end for;
//   return label;
// end function;
//
// intrinsic FqCartesianProductProcess(F::FldFin, k::RngIntElt) -> Process
// {Generate k-tuples of integers in 0..M-1}
//   requirege k, 0;
//   if k eq 0 then
//     return CreateProcess([<>]);
//   end if;
//   state := Rep(CartesianPower(F, k));
//
//   // info[3] will be an "is_finished" flag
//   info := <F, state, false>;
//   if IsPrimeField(F) then
//     return CreateProcess(
//           "GF(" cat IntegerToString(#F) cat ")^" cat IntegerToString(k),
//           info,
//           _Fq_cart_product_process_IsEmpty,
//           _Fp_cart_product_process_Next,
//           _Fq_cart_product_process_Extract,
//           _Fp_cart_product_process_ExtractLabel
//     );
//   end if;
//   return CreateProcess(
//         "GF(" cat IntegerToString(#F) cat ")^" cat IntegerToString(k),
//         info,
//         _Fq_cart_product_process_IsEmpty,
//         _Fq_cart_product_process_Next,
//         _Fq_cart_product_process_Extract,
//         _Fq_cart_product_process_ExtractLabel
//   );
// end intrinsic;
