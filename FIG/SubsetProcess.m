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



// Free positions for echelon kxn matrix with pivots given by S.
function _create_positions(n, k, S)
  return [<i,j> : j in [S[i]+1..n], i in [1..k] | j notin S];
end function;


function _echelon_IsEmpty(p)
  return p[7];
end function;

// info := <Fq, n, k, M, positions, SProcess, counter, done_flag>;
procedure _echelon_q_Advance(~p)
  L := #p[5];
  if L eq 0 then
    rollover := true;
  else
    rollover := false;
    for t->pos in p[5] do
      i,j := Explode(pos);
      if IsZero(p[4][i,j]) then
        p[4][i,j] := One(p[1]);
        break;
      end if;
      p[4][i,j] *:= PrimitiveElement(p[1]);
      if IsOne(p[4][i,j]) then
        if t eq L then
          rollover := true;
          break;
        end if;
        p[4][i,j] := Zero(p[1]);
        continue;
      end if;
      break;
    end for;
  end if;

  if rollover then
    Advance(~p[6]);
    if IsEmpty(p[6]) then
      p[8] := true;
      return;
    end if;
    S := Current(p[6]);
    p[5] := _create_positions(p[2], p[3], S);
    p[4] := Matrix(p[1], p[3], p[2], [<i, S[i], One(p[1])> : i in [1..p[3]]]);
  end if;
  p[7] +:=1;
end procedure;


// info := <Fq, n, k, M, positions, SProcess, counter, done_flag>;
procedure _echelon_p_Advance(~p)
  L := #p[5];
  if IsZero(L) then
    rollover := true;
  else
    rollover := false;
    for t->pos in p[5] do
      i,j := Explode(pos);
      p[4][i,j] +:=1;
      if IsZero(p[4][i,j]) then
        if t eq L then
          rollover := true;
          break;
        end if;
        continue;
      end if;
      break;
    end for;
  end if;

  if rollover then
    Advance(~p[6]);
    if IsEmpty(p[6]) then
      p[8] := true;
      return;
    end if;
    S := Current(p[6]);
    p[5] := _create_positions(p[2], p[3], S);
    p[4] := Matrix(p[1], p[3], p[2], [<i, S[i], One(p[1])> : i in [1..p[3]]]);
  end if;
  p[7] +:=1;
end procedure;
//
//
//
//   Advance(~p[4]);
//   if IsEmpty(p[4]) then
//     Advance(~p[5]);
//     if IsEmpty(p[5]) then
//       p[7] := true;
//       return;
//     end if;
//     // Need to reinitialize the MatrixSubprocess
//     p[4] := SubspaceMatSubProcess(p[1], p[2], p[3], Current(p[5]));
//   end if;
//   p[6] +:=1;
// end procedure;

function _echelon_Extract(p)
  return Current(p[4]);
end function;

function _echelon_Label(p)
  return p[6];
end function;


// info := <Fq, n, k, M, positions, SProcess, counter, done_flag>;
intrinsic SubspaceMatProcess(Fq::FldFin, n::RngIntElt, k::RngIntElt) -> Process
{Gives a process for iterating through all subspaces of fixed dimension k from U.}
  requirerange k, 0, n;
  if k eq 0 then
    return CreateProcess([ZeroMatrix(Fq, k, n)]);
  elif k eq n then
    return CreateProcess([IdentityMatrix(Fq, n)]);
  end if;

  Sproc := SubsetProcess(n,k);
  S := Current(Sproc);
  positions := _create_positions(n, k, S);
  M := Matrix(Fq, k, n, [<i, S[i], One(Fq)> : i in [1..k]]);
  info := <Fq, n, k, M, positions, Sproc, 1, false>;

  if IsPrimeField(Fq) then
    return CreateProcess(
              "Echelon Matrices",
              info,
              _echelon_IsEmpty,
              _echelon_p_Advance,
              _echelon_Extract,
              _echelon_Label
    );
  end if;
  return CreateProcess(
            "Echelon Matrices",
            info,
            _echelon_IsEmpty,
            _echelon_q_Advance,
            _echelon_Extract,
            _echelon_Label
  );
end intrinsic;




function _Fq_echelon_subprocess_IsEmpty(p)
  return p[3];
end function;



// procedure _update_Fq_matrix(~M, pos, ~flag)
procedure _update_Fq_matrix(~p)
  if IsEmpty(p[2]) then
    p[3] := true;
  else
    L := #p[2];
    F := CoefficientRing(p[1]);
    z, o, alpha := Zero(F), One(F), PrimitiveElement(F);
    for t->pos in p[2] do
      i, j := Explode(pos);
      if IsZero(p[1][i,j]) then
        p[1][i,j] := o;
        break;
      end if;
      p[1][i,j] *:= alpha;
      if IsOne(p[1][i,j]) then
        if t eq L then
          p[3] := true;
          break;
        end if;
        p[1][i,j] := z;
        continue;
      end if;
      break;
    end for;
  end if;
end procedure;

// procedure _update_Fq_matrix(~M, pos, ~flag)
procedure _update_Fp_matrix(~p)
  if IsEmpty(p[2]) then
    p[3] := true;
  else
    L := #p[2];
    for t->pos in p[2] do
      i, j := Explode(pos);
      p[1][i,j] +:=1;
      if IsZero(p[1][i,j]) then
        if t eq L then
          p[3] := true;
          break;
        end if;
        continue;
      end if;
      break;
    end for;
  end if;
end procedure;

function _Fq_echelon_subprocess_Extract(p)
  return p[1];
end function;

function _Fp_echelon_subprocess_ExtractLabel(p)
  label := 1;
  pow := 1;
  q := #CoefficientRing(p[1]);
  for pos in [#p[2]..1 by -1] do
    i, j := Explode(p[2][pos]);
    if not IsZero(p[1][i,j]) then
      label +:= pow * Integers()!p[1][i,j];
    end if;
    pow *:= q;
  end for;
  return label;
end function;

function _Fq_echelon_subprocess_ExtractLabel(p)
  label := 1;
  pow := 1;
  q := #CoefficientRing(p[1]);
  for pos in [#p[2]..1 by -1] do
    i, j := Explode(p[2][pos]);
    if not IsZero(p[1][i,j]) then
      label +:= pow * (1+Log(p[1][i,j]));
    end if;
    pow *:= q;
  end for;
  return label;
end function;


intrinsic SubspaceMatSubProcess(Fq::FldFin, n::RngIntElt, k::RngIntElt, S::SetIndx) -> Process
{Generate row reduced echelon matrices with fixed set S of pivots.}
  // npos := n*k - Binomial(k,2) - &+(S);
  pos := _create_positions(n,k,S);
  M := ZeroMatrix(Fq, k, n);
  for i in [1..k] do
    M[i, S[i]] := One(Fq);
  end for;
  info := <M, pos, false>;

  if IsPrimeField(Fq) then
    return CreateProcess(
              "Echelon Matrices",
              info,
              _Fq_echelon_subprocess_IsEmpty,
              _update_Fp_matrix,
              _Fq_echelon_subprocess_Extract,
              _Fp_echelon_subprocess_ExtractLabel
    );
  end if;
  return CreateProcess(
            "Echelon Matrices",
            info,
            _Fq_echelon_subprocess_IsEmpty,
            _update_Fq_matrix,
            _Fq_echelon_subprocess_Extract,
            _Fq_echelon_subprocess_ExtractLabel
  );
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
