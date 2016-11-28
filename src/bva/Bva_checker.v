(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller  *                                                  *)
(*     Alain   Mebsout ♯                                                  *)
(*     Burak   Ekici   ♯                                                  *)
(*                                                                        *)
(*    * Inria - École Polytechnique - Université Paris-Sud                *)
(*    ♯ The University of Iowa                                            *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(** A small checker for bit-vectors bit-blasting *)

(*Add Rec LoadPath "." as SMTCoq.*)

Require Import Int63 Int63Properties PArray SMT_classes.

Require Import Misc State SMT_terms BVList Word Psatz.
Require Import Bool List BoolEq NZParity Nnat.  
Require Import BinPos BinNat Pnat Init.Peano.

Require FArray.

Import ListNotations.
Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.
Local Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.


Section Checker.

  Import Atom.

  Variable t_atom : PArray.array atom.
  Variable t_form : PArray.array form.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).

 (** * Bit-blasting a variable:

              x ∈ BV n
       ----------------------- bbVar
        bbT(x, [x₀; ...; xₙ₋₁])
   *)

  Fixpoint check_bb (a: int) (bs: list _lit) (i n: nat) :=
    match bs with
    | nil => Nat_eqb i n                     (* We go up to n *)
    | b::bs =>
      if Lit.is_pos b then
        match get_form (Lit.blit b) with
        | Fatom a' =>
          match get_atom a' with
          | Auop (UO_BVbitOf N p) a' =>
            (* TODO:
               Do not need to check [Nat_eqb l (N.to_nat N)] at every iteration *)
            if (a == a')                     (* We bit blast the right bv *)
                 && (Nat_eqb i p)            (* We consider bits after bits *)
                 && (Nat_eqb n N)            (* The bv has indeed type BV n *)
            then check_bb a bs (S i) n
            else false
          | _ => false
          end
        | _ => false
        end
      else false
    end.

  (** Checker for bitblasting of bitvector variables *)
  Definition check_bbVar lres :=
    if Lit.is_pos lres then
      match get_form (Lit.blit lres) with
      | FbbT a bs =>
        if check_bb a bs O (List.length bs)%N
        then lres::nil
        else C._true
      | _ => C._true
      end
    else C._true.

  (** * Bit-blasting a constant bitvector:

       --------------------------- bbConst
        bbT(#b0010, [0; 1; 0; 0])
   *)

  Fixpoint check_bbc s (w: word s) (bs: list _lit) :=
    match w, bs with
    | WO, nil => true
    | WS v w', b::bs =>
      if Lit.is_pos b then
        match get_form (Lit.blit b), v with
          | Ftrue, true | Ffalse, false => check_bbc w' bs
          | _, _ => false
        end
      else false
    | _, _ => false
    end.

  (** Checker for bitblasting of bitvector constants *)
  Definition check_bbConst lres :=
    if Lit.is_pos lres then
      match get_form (Lit.blit lres) with
        | FbbT a bs =>
          match get_atom a with
            | Acop (CO_Word s w) =>
              if check_bbc w bs
              then lres::nil
              else C._true
            | _ => C._true
          end
        | _ => C._true
      end
    else C._true.

  (** * Bit-blasting bitwise operations: bbAnd, bbOr, ...

        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bbT(a&b, [a0 /\ b0; ...; an /\ bn])
   *)

Fixpoint check_symopp (bs1 bs2 bsres : list _lit) (bvop: binop)  :=
    match bs1, bs2, bsres with
    | nil, nil, nil => true
    | b1::bs1, b2::bs2, bres::bsres =>
      if Lit.is_pos bres then
        let (ires, bvop) := 
        match get_form (Lit.blit bres), bvop with

          | Fand args, BO_BVand n  =>
            ((if PArray.length args == 2 then
                let a1 := args.[0] in
                let a2 := args.[1] in
                ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
              else false), BO_BVand (n-1))

          | For args, BO_BVor n  =>
            ((if PArray.length args == 2 then
                let a1 := args.[0] in
                let a2 := args.[1] in
                ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
              else false), BO_BVor (n-1))

          | Fxor a1 a2, BO_BVxor n =>
             (((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)),
             BO_BVxor (n-1))

          | Fiff a1 a2, (BO_eq (Typ.TWord n))  =>
             (((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)),
             BO_eq (Typ.TWord n))

          | _, _ => (false, bvop)
        end in
        if ires then check_symopp bs1 bs2 bsres bvop
        else false
      else false
    | _, _, _ => false
    end.



  (** Checker for bitblasting of bitwise operators on bitvectors *)
  Definition check_bbOp s pos1 pos2 lres :=
    match (S.get s pos1), (S.get s pos2) with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
          match get_atom a with

          | Abop (BO_BVand n) a1' a2' =>
            if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                 && (@check_symopp bs1 bs2 bsres (BO_BVand n))
                 && (Nat.eqb (length bs1) n)
            then lres::nil
            else C._true

          | Abop (BO_BVor n) a1' a2' =>
             if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                  && (check_symopp bs1 bs2 bsres  (BO_BVor n))
                  && ((length bs1) =? n)%nat
             then lres::nil
             else C._true

          | Abop (BO_BVxor n) a1' a2' =>
             if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                  && (check_symopp bs1 bs2 bsres  (BO_BVxor n))
                  && ((length bs1) =? n)%nat
             then lres::nil
             else C._true

       | _ => C._true
          end
        | _, _, _ => C._true
        end
      else C._true
    | _, _ => C._true
    end.


  (** * Checker for bitblasting of bitvector concatenation *)

  (** * Bitvector Arithmetic *)
 (** Representaion for symbolic carry computations *)
  Inductive carry : Type :=
  | Clit (_:_lit)
  | Cand (_:carry) (_:carry)
  | Cxor (_:carry) (_:carry)
  | Cor (_:carry) (_:carry)
  | Ciff (_:carry) (_:carry)
  .

  (** Check if a symbolic carry computation is equal to a literal
     representation. This function does not account for potential symmetries *)
  (* c should always be a positive literal in carry computations *)
  Fixpoint eq_carry_lit (carry : carry) (c : _lit) :=
    if Lit.is_pos c then
      match carry with
        | Clit l => l == c

        | Cand c1 c2  =>
          match get_form (Lit.blit c) with
          | Fand args =>
            if PArray.length args == 2 then
              (eq_carry_lit c1 (args.[0]) && eq_carry_lit c2 (args.[1]))
              (* || (eq_carry_lit c1 (args.[1]) && eq_carry_lit c2 (args.[0])) *)
            else false
          | _ => false
          end

        | Cxor c1 c2  =>
          match get_form (Lit.blit c) with
            | Fxor a1 a2 =>
              (eq_carry_lit c1 a1 && eq_carry_lit c2 a2)
                (* || (eq_carry_lit c1 a2 && eq_carry_lit c2 a1) *)
            | _ => false
          end

        | Cor c1 c2  =>
          match get_form (Lit.blit c) with
          | For args =>
            if PArray.length args == 2 then
              (eq_carry_lit c1 (args.[0]) && eq_carry_lit c2 (args.[1]))
                (* || (eq_carry_lit c1 (args.[1]) && eq_carry_lit c2 (args.[0])) *)
            else false
          | _ => false
          end

        | Ciff c1 c2  =>
          match get_form (Lit.blit c) with
            | Fiff a1 a2 =>
              (eq_carry_lit c1 a1 && eq_carry_lit c2 a2)
                (* || (eq_carry_lit c1 a2 && eq_carry_lit c2 a1) *)
            | _ => false
          end
      end
    else
      (* c can be negative only when it is literal false *)
      match carry with
        | Clit l => l == c
        | _ => false
      end.

  Fixpoint lit_to_carry (bs: list _lit) : list carry :=
    match bs with
      | nil => []
      | xbs :: xsbs => Clit xbs :: lit_to_carry xsbs
    end.

  Definition check_concat (bs1 bs2 bsres: list _lit) : bool :=
    if (forallb2 eq_carry_lit (lit_to_carry (bs1 ++ bs2)) bsres) then true else false.

  Definition check_bbConcat s pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
      | l1::nil, l2::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
            | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
              match get_atom a with

                | Abop (BO_BVconcat n m) a1' a2' =>
                  if (((a1 == a1') && (a2 == a2')) (* || ((a1 == a2') && (a2 == a1')) *) )
                       && (check_concat bs1 bs2 bsres)
                       && ((length bs1) =? n)%nat
                       && ((length bs2) =? m)%nat
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _, _ => C._true
          end
        else C._true
      | _, _ => C._true
    end.

  (** Checker for unsigned bitvector extension *)
  Fixpoint extend_lit (x: list _lit) (i: nat) (b: _lit) {struct i}: list _lit :=
    match i with
      | O => x
      | S i' =>  b :: extend_lit x i' b
    end.

  Definition zextend_lit (x: list _lit) (i: nat): list _lit :=
    List.rev (extend_lit (List.rev x) i Lit._false).

   Definition lit_of_bool (b: bool) :_lit :=
     if (Bool.eqb b true) then Lit._true
     else Lit._false.

   Definition check_zextend (bs bsres: list _lit) (i: nat) : bool :=
     if (forallb2 eq_carry_lit (lit_to_carry (zextend_lit bs i)) bsres)
    then true else false.

  Definition check_bbZextend s pos lres :=
    match S.get s pos with
      | l1::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit lres) with
            | FbbT a1 bs, FbbT a bsres =>
              match get_atom a with

                | Auop (UO_BVzextn n i) a1' =>
                  if ((a1 == a1') (* || ((a1 == a2') && (a2 == a1')) *) )
                       && (check_zextend bs bsres i)
                       && ((length bs) =? n)%nat
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _ => C._true
          end
        else C._true
      | _ => C._true
end.

 (** Checker for signed bitvector extension *)


  Fixpoint mk_list_lit_false (t: nat) : list _lit :=
    match t with
      | O    => []
      | S t' => Lit._false :: (mk_list_lit_false t')
    end.

  Definition _sextend_lit (x: list _lit) (i: nat): list _lit :=
    match x with
      | []       => mk_list_lit_false i
      | xb :: x' => extend_lit x i xb
    end.

  Definition sextend_lit  (x: list _lit) (i: nat) := List.rev (_sextend_lit (List.rev x) i). 

   Definition check_sextend (bs bsres: list _lit) (i: nat) : bool :=
     if (forallb2 eq_carry_lit (lit_to_carry (sextend_lit bs i)) bsres)
    then true else false.

  Definition check_bbSextend s pos lres :=
    match S.get s pos with
      | l1::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit lres) with
            | FbbT a1 bs, FbbT a bsres =>
              match get_atom a with

                | Auop (UO_BVsextn n i) a1' =>
                  if ((a1 == a1') (* || ((a1 == a2') && (a2 == a1')) *) )
                       && (check_sextend bs bsres i)
                       && ((length bs) =? n)%nat
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _ => C._true
          end
        else C._true
      | _ => C._true
    end.


  (** * Checker for bitblasting of bitvector addition *)


  (** Checks if [bsres] is the result of bvand of bs1 and bs2. The inital
      value for the carry is [false]. *)
  Fixpoint check_add (bs1 bs2 bsres : list _lit) (carry : carry) :=
    match bs1, bs2, bsres with
      | nil, nil, nil => true
      | b1::bs1, b2::bs2, bres::bsres =>
        if Lit.is_pos bres then
          match get_form (Lit.blit bres) with
            | Fxor xab c  =>
             if Lit.is_pos xab then
              match get_form (Lit.blit xab) with
                | Fxor a1 a2  =>
                  (* This is the way LFSC computes carries *)
                  let carry' := Cor (Cand (Clit b1) (Clit b2))
                                    (Cand (Cxor (Clit b1) (Clit b2)) carry) in
                  (((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)))
                    && eq_carry_lit carry c
                    && check_add bs1 bs2 bsres carry'
                | _ => false
              end
            else false
            | _ => false
          end
        else false
      | _, _, _ => false
    end.

  (** * Checker for bitblasting of bitvector addition *)
  Definition check_bbAdd s pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
      | l1::nil, l2::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
            | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
              match get_atom a with

                | Abop (BO_BVadd n) a1' a2' =>
                  if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                       && (check_add bs1 bs2 bsres (Clit Lit._false))
                       && (Nat.eqb (length bs1) n)%nat
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _, _ => C._true
          end
        else C._true
      | _, _ => C._true
    end.


 Fixpoint and_with_bit (a: list _lit) (bt: _lit) : list carry :=
    match a with
      | nil => nil
      | ai :: a' => (Cand (Clit bt) (Clit ai)) :: and_with_bit a' bt 
    end.

  Fixpoint mult_step_k_h (a b: list carry) (c: carry) (k: Z) : list carry :=
    match a, b with
      | nil, _ => []
      | ai :: a', bi :: b' =>
        if (k - 1 <? 0)%Z then
          let carry_out := Cor (Cand ai bi) (Cand (Cxor ai bi) c) in
          let curr := Cxor (Cxor ai bi) c in
          curr :: mult_step_k_h a' b' carry_out (k - 1)
        else
          ai :: mult_step_k_h a' b c (k - 1)
      | ai :: a', nil =>  ai :: mult_step_k_h a' b c k
    end.

  Fixpoint mult_step (a b: list _lit) (res: list carry) (k k': nat) : list carry :=
    let ak := List.firstn (S k') a in
    let b' := and_with_bit ak (nth k b Lit._false) in
    let res' := mult_step_k_h res b' (Clit Lit._false) (Z.of_nat k) in
    match k' with 
      | O => res'
      (* | S O => res' *)
      | S pk' => mult_step a b res' (S k) pk'
    end.

  Definition bblast_bvmult (a b: list _lit) (n: nat) : list carry :=
    let res := and_with_bit a (nth 0 b Lit._false) in
    match n with
      | O => res
      | S O => res
      | S (S k) => mult_step a b res 1 k
    end.

  Fixpoint mkzeros (k: nat) : list carry :=
    match k with
      | O => nil
      | S k => (Clit Lit._false) :: mkzeros k
    end .

  Fixpoint bblast_bvadd (a b: list carry) (c: carry) : list carry :=
    match a, b  with
      | nil, _ | _, nil => nil
      | ai :: a', bi :: b' =>
        let c' := (Cor (Cand ai bi) (Cand (Cxor ai bi) c)) in
        (Cxor (Cxor ai bi) c') :: (bblast_bvadd a' b' c')
    end.

  Fixpoint mult_shift (a b: list _lit) (n: nat) : list carry :=
    match a with
      | nil => mkzeros n
      | ai :: a' =>
        (bblast_bvadd (and_with_bit b ai)
                      (mult_shift a' (Lit._false :: b) n) (Clit Lit._false))
    end.

  Definition check_mult (bs1 bs2 bsres: list _lit) : bool :=
   if Nat_eqb (length bs1) (length bs2)%nat then
    let bvm12 := bblast_bvmult bs1 bs2 (length bs1) in
    forallb2 eq_carry_lit bvm12 bsres
   else false.

  (** * Checker for bitblasting of bitvector multiplication *)
  Definition check_bbMult s pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
      | l1::nil, l2::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
            | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
              match get_atom a with

                | Abop (BO_BVmult n) a1' a2' =>
                  if (((a1 == a1') && (a2 == a2')) (* || ((a1 == a2') && (a2 == a1')) *) )
                       && (check_mult bs1 bs2 bsres)
                       && ((length bs1) =? n)%nat
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _, _ => C._true
          end
        else C._true
      | _, _ => C._true
    end.


   (** * Bit-blasting bitvector equality

        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbEq
         (a = b) <-> ((a0 <-> b0) /\ ... /\ (an <-> bn))
   *)

  Fixpoint check_eq (bs1 bs2 bsres: list _lit) :=
    match bs1, bs2, bsres with
    | nil, nil, nil => true
    | b1::bs1, b2::bs2, bres :: bsres =>
      match bs1, bs2, bsres with
      | _::_, _::_, [] => 
        if Lit.is_pos bres then
          match get_form (Lit.blit bres) with
          | Fand args =>
            match PArray.to_list args with
            | bres :: bsres =>
              if Lit.is_pos bres then
                let ires := 
                    match get_form (Lit.blit bres) with
                    | Fiff a1 a2  =>
                      ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
                    | _ => false
                    end in
                if ires then check_eq bs1 bs2 bsres
                else false
              else false
            | _ => false
            end
          | _ => false
          end
        else false
      | _, _, _ =>
        if Lit.is_pos bres then
          let ires := 
              match get_form (Lit.blit bres) with
              | Fiff a1 a2  =>
                ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
              | _ => false
              end in
          if ires then check_eq bs1 bs2 bsres
          else false
        else false
      end
    | _, _, _ => false
    end.

  (** Checker for bitblasting of equality between bitvector terms  *)
  Definition check_bbEq s pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff leq lbb =>
          if (Bool.eqb (Lit.is_pos leq) (Lit.is_pos lbb)) then
          match get_form (Lit.blit leq), get_form (Lit.blit lbb) with
          | Fatom a, _ (* | _, Fatom a *) =>
            match get_atom a with
            | Abop (BO_eq (Typ.TWord n)) a1' a2' =>
              if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                   && (check_eq bs1 bs2 [lbb])
                   && ((length bs1) =? n)%nat
              then lres::nil
              else C._true
            | _ => C._true
            end
          | _, _ => C._true
          end
          else C._true
        | _, _, _ => C._true
        end
      else C._true
    | _, _ => C._true
    end.

  (** * Checker for bitblasting of bitvector comparison: lt *)

  Fixpoint ult_big_endian_lit_list (bs1 bs2: list _lit) :=
    match bs1, bs2 with
      | nil, _ => Clit (Lit._false)
      | _, nil => Clit (Lit._false)
      | xi :: nil, yi :: nil => (Cand (Clit (Lit.neg xi)) (Clit yi))
      | xi :: x', yi :: y'   =>
        (Cor (Cand (Ciff (Clit xi) (Clit yi)) (ult_big_endian_lit_list x' y'))
             (Cand (Clit (Lit.neg xi)) (Clit yi)))
    end.

  Definition ult_lit_list (x y: list _lit) :=
    ult_big_endian_lit_list (List.rev x) (List.rev y).

  Definition check_ult (bs1 bs2: list _lit) (bsres: _lit) : bool :=
    if Lit.is_pos bsres then
      eq_carry_lit (ult_lit_list bs1 bs2) bsres
    else false.

  Definition check_bbUlt s pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff llt lbb =>
          if (Bool.eqb (Lit.is_pos llt) (Lit.is_pos lbb)) then
          match get_form (Lit.blit llt), get_form (Lit.blit lbb) with
          | Fatom a, _ (* | _, Fatom a *) =>
            match get_atom a with
            | Abop (BO_BVult n) a1' a2' =>
              if ((a1 == a1') && (a2 == a2'))
                   && (check_ult bs1 bs2 lbb)
                   && ((length bs1) =? n)%nat
                   && ((length bs2) =? n)%nat
              then lres::nil
              else C._true
            | _ => C._true
            end
          | _, _ => C._true
          end
          else C._true
        | _, _, _ => C._true
        end
      else C._true
    | _, _ => C._true
    end.


  (** * Bit-blasting bitvector negation ...

           bbT(a, [a0; ...; an])
        ------------------------------ bbNeg
               bbT(-a, [...])
   *)

  (* Helper function for bv_neg *)
  Definition check_neg (bs br : list _lit) :=
    let z := map (fun _ => Lit._false) bs in
    let nbs := map (fun l => Lit.neg l) bs in
    check_add nbs z br (Clit Lit._true).  

  (** Checker for bitblasting of bitvector negation *)
  Definition check_bbNeg s pos lres :=
    match S.get s pos with
    | l::nil =>
      if (Lit.is_pos l) && (Lit.is_pos lres) then
        match get_form (Lit.blit l), get_form (Lit.blit lres) with
        | FbbT a bs, FbbT r br =>
          match get_atom r with
          | Auop (UO_BVneg n) a' =>
            if (a == a') && check_neg bs br &&
               ((length bs) =? n)%nat
            then lres::nil
            else C._true
          | _ => C._true
          end
        | _, _ => C._true
        end
      else C._true
    | _ => C._true
    end.



  (** * Bit-blasting bitvector not ...

           bbT(a, [a0; ...; an])
        ------------------------------ bbNot
         bbT(not a, [~a0; ...; ~an])
   *)

  (* Helper function for bv_not *)
  Fixpoint check_not (bs br : list _lit)  :=
    match bs, br with
    | nil, nil => true
    | b::bs, r::br => (r == Lit.neg b) && check_not bs br
    | _, _ => false
    end.

  (** Checker for bitblasting of bitvector not *)
  Definition check_bbNot s pos lres :=
    match S.get s pos with
    | l::nil =>
      if (Lit.is_pos l) && (Lit.is_pos lres) then
        match get_form (Lit.blit l), get_form (Lit.blit lres) with
        | FbbT a bs, FbbT r br =>
          match get_atom r with
          | Auop (UO_BVnot N) a' =>
            if (a == a') && check_not bs br &&
              ( (length bs) =? N)%nat
            then lres::nil
            else C._true
          | _ => C._true
          end
        | _, _ => C._true
        end
      else C._true
    | _ => C._true
    end.

(* bitwise disequality *)

  Fixpoint List_diseqb (a b: list bool) : bool :=
  match a, b with
    | nil, nil =>  false
    | xa :: xsa, xb :: xsb =>
      if (Bool.eqb xa false) then 
        (if (Bool.eqb xb false) then List_diseqb xsa xsb else  true)
      else (if (Bool.eqb xb true) then List_diseqb xsa xsb else  true)
    | _, _ => true
  end.


  (** Checker for bitvector disequality *)
  Definition check_bbDiseq lres :=
  if negb (Lit.is_pos lres) then
      match get_form (Lit.blit lres) with
          | Fatom f => 
          match (get_atom f) with
            |  Abop (BO_eq (Typ.TWord n)) a b =>
             match (get_atom a), (get_atom b) with
               | (Acop (CO_Word s1 bv1)), (Acop (CO_Word s2 bv2)) =>
                  if List_diseqb (wordToList bv1) (wordToList bv2) && ( s1 =? n)%nat
                     && (s2 =? n)%nat
                  then lres::nil
                  else C._true
               | _, _ => C._true
             end
           | _ => C._true
         end
          | _ => C._true
      end
    else C._true.



  (** Checker for bitvector extraction *)
  Fixpoint extract_lit (x: list _lit) (i j: nat) : list _lit :=
    match x with
      | []         => []
      | bx :: x'   => 
        match i with
          | O      =>
            match j with
              | O    => []
              | S j' => bx :: extract_lit x' i j'
            end
          | S i'   => 
            match j with
              | O    => []
              | S j' => extract_lit x' i' j'
            end
        end
   end.

   Definition check_extract (bs bsres: list _lit) (i j: nat) : bool :=
     if (Nat.ltb (length bs) j) 
     then false
     else
       if (forallb2 eq_carry_lit (lit_to_carry (extract_lit bs i j)) bsres)
       then true
       else false.

  Definition check_extract3 (bs bsres: list _lit) (i j: N) : bool :=
    forallb2 (fun l1 l2 => l1 == l2) (extract_lit bs (nat_of_N i) (nat_of_N j)) bsres.


  (** Checker for bitvector extraction *)
  Fixpoint check_extract2 (x bsres: list _lit) (i j: nat) : bool :=
    match x with
      | [] => match bsres with [] => true | _ => false end
      | bx :: x' => 
        match i with
          | O      =>
            match j, bsres with
            | O, nil => true
            | S j', b :: bsres' => (bx == b) && check_extract2 x' bsres' i j'
            | _, _ => false
            end
          | S i'   => 
            match j, bsres with
              | O, nil => true
              | S j', _ => check_extract2 x' bsres i' j'
              | _, _ => false
            end
        end
   end.

  Definition check_bbExtract s pos lres :=
    match S.get s pos with
      | l1::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit lres) with
            | FbbT a1 bs, FbbT a bsres =>
              match get_atom a with

                | Auop (UO_BVextr i n0 n1) a1' =>
                  if ((a1 == a1') (* || ((a1 == a2') && (a2 == a1')) *) )
                       && (check_extract bs bsres i (n0 + i))
                       && ((length bs) =? n1)%nat
                       && (Nat.leb (n0 + i) n1)
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _ => C._true
          end
        else C._true
      | _ => C._true
    end.

(*

  Variable s : S.t.


  Definition slt_big_endian_lit_list (x y: list _lit) :=
    match x, y with
      | nil, _ => Clit (Lit._false)
      | _, nil => Clit (Lit._false)
      | xi :: nil, yi :: nil => (Cand (Clit xi) (Clit (Lit.neg yi)))
      | xi :: x', yi :: y'   =>
        (Cor (Cand (Ciff (Clit xi) (Clit yi)) (ult_big_endian_lit_list x' y')) 
             (Cand (Clit xi) (Clit (Lit.neg yi))))
    end.

  Definition slt_lit_list (x y: list _lit) :=
    slt_big_endian_lit_list (List.rev x) (List.rev y).

  Definition check_slt (bs1 bs2: list _lit) (bsres: _lit) : bool := 
    if Lit.is_pos bsres then
      eq_carry_lit (slt_lit_list bs1 bs2) bsres
    else false.

  Definition check_bbSlt pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff llt lbb =>
          if (Bool.eqb (Lit.is_pos llt) (Lit.is_pos lbb)) then
          match get_form (Lit.blit llt), get_form (Lit.blit lbb) with
          | Fatom a, _ (* | _, Fatom a *) =>
            match get_atom a with
            | Abop (BO_BVslt n) a1' a2' =>
              if ((a1 == a1') && (a2 == a2'))
                   && (check_slt bs1 bs2 lbb)
                   && (N.of_nat (length bs1) =? n)%N
                   && (N.of_nat (length bs2) =? n)%N
              then lres::nil
              else C._true
            | _ => C._true
            end
          | _, _ => C._true
          end
          else C._true
        | _, _, _ => C._true
        end
      else C._true
    | _, _ => C._true
    end.





*)



 Section Proof.

    Variables (t_i : array typ_compdec)
              (t_func : array (Atom.tval t_i))
              (ch_atom : Atom.check_atom t_atom)
              (ch_form : Form.check_form t_form)
              (wt_t_atom : Atom.wt t_i t_func t_atom).

    Local Notation check_atom :=
      (check_aux t_i t_func (get_type t_i t_func t_atom)).

    Local Notation interp_form_hatom :=
      (Atom.interp_form_hatom t_i t_func t_atom).

    Local Notation interp_form_hatom_word :=
      (Atom.interp_form_hatom_word t_i t_func t_atom).

    Local Notation rho :=
      (Form.interp_state_var interp_form_hatom interp_form_hatom_word t_form).

    Hypothesis Hs : forall s, S.valid rho s.

    Local Notation t_interp := (t_interp t_i t_func t_atom).

    Local Notation interp_atom :=
      (interp_aux t_i t_func (get t_interp)).

    Let wf_t_atom : Atom.wf t_atom.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_atom : default t_atom = Atom.Acop Atom.CO_xH.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_form : default t_form = Form.Ftrue.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_word _ ch_form) as [H _]; destruct H; auto.
    Qed.

    Let wf_t_form : Form.wf t_form.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_word _ ch_form) as [H _]; destruct H; auto.
    Qed.

    Let wf_rho : Valuation.wf rho.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_word _ ch_form); auto.
    Qed.

    (* Lemma lit_interp_true : Lit.interp rho Lit._true = true. *)
    (* Proof. *)
    (*   apply Lit.interp_true. *)
    (*   apply wf_rho. *)
    (* Qed. *)

     Let rho_interp : forall x : int, rho x = Form.interp interp_form_hatom interp_form_hatom_word t_form (t_form.[ x]).
     Proof. intros x;apply wf_interp_form;trivial. Qed.

      Definition wf := PArray.forallbi lt_form t_form.

      Hypothesis wf_t_i : wf.
      Variable interp_wordatom : atom -> forall s, Word.word s.
      Notation atom := int (only parsing).


  Fixpoint interp_carry (c: carry) : bool :=
    match c with
      | Clit l => (Lit.interp rho l)
      | Cand c1 c2 => (interp_carry c1) && (interp_carry c2)
      | Cor c1 c2 => (interp_carry  c1) || (interp_carry c2)
      | Cxor c1 c2 => xorb (interp_carry c1) (interp_carry c2)
      | Ciff c1 c2 => Bool.eqb (interp_carry c1) (interp_carry c2)
    end.


Lemma eq_rec: forall (n: N) (a b: BITVECTOR_LIST.bitvector n), BITVECTOR_LIST.bv a = BITVECTOR_LIST.bv b 
                         ->
                          a = b.
Proof. intros. destruct a, b. 
       unfold BITVECTOR_LIST.bv in H.
       revert wf0.
       rewrite H. intros.
       now rewrite (proof_irrelevance wf0 wf1).
Qed.


Lemma helper0: forall i, ListToword [Lit.interp rho i] 1 = WS (Lit.interp rho i) WO.
Proof. intro i.
       case_eq (Lit.interp rho i); intros; subst; easy.
Qed.

Lemma helper1: (ListToword [] 0) = WO.
Proof. easy. Qed.

Lemma helper2: forall n, (ListToword [] n) = wzero n.
Proof. intros. case_eq n; easy. Qed.

Lemma _helper2: forall n, (_ListToword [] n) = wzero n.
Proof. intros. case_eq n; easy. Qed.


Lemma _helper3: forall n i, _ListToword [Lit.interp rho i] (S n) = WS (Lit.interp rho i) (wzero n).
Proof. intro n.
       induction n; intros.
       - unfold ListToword. simpl. 
         case (Lit.interp rho i); intros. 
         unfold wzero. now simpl. now simpl.
       - case_eq (Lit.interp rho i); intros; simpl.
         unfold ListToword in *. simpl. unfold wzero. now simpl.
         easy.
Qed.

Lemma _helper: forall n l i,
(_ListToword (Lit.interp rho i :: map (Lit.interp rho) l) (S n)) =
WS (Lit.interp rho i) (_ListToword (map (Lit.interp rho) l) n).
Proof. intro n.
       induction n; intros.
       - case (Lit.interp rho i); intros. 
         unfold wzero. now simpl. now simpl.
       - case_eq (Lit.interp rho i); intros; simpl.
         unfold ListToword in *. simpl. unfold wzero. now simpl.
         easy.
Qed.

Lemma _helper_strong: forall n l i,
(_ListToword (i :: l) (S n)) =
WS i (_ListToword l n).
Proof. intro n.
       induction n; intros.
       - case i; intros. 
         unfold wzero. now simpl. now simpl.
       - case_eq i; intros; simpl.
         unfold ListToword in *. simpl. unfold wzero. now simpl.
         easy.
Qed.

Lemma helper: forall l i,
(ListToword (Lit.interp rho i :: map (Lit.interp rho) l) (S (length l))) =
WS (Lit.interp rho i) (ListToword (map (Lit.interp rho) l) (length l)).
Proof. intros. unfold ListToword.
       assert ( Datatypes.length (Lit.interp rho i :: map (Lit.interp rho) l) = S (Datatypes.length l)).
       { simpl. now rewrite map_length. } rewrite H, map_length, !Nat.eqb_refl.
       now rewrite _helper.
Qed.

Lemma helper_strong: forall l i,
(ListToword (i :: l) (S (length l))) =
WS i (ListToword l (length l)).
Proof. intros. unfold ListToword.
       assert ( Datatypes.length (i :: l) = S (Datatypes.length l)) by auto.
       rewrite H, !Nat.eqb_refl.
       now rewrite _helper_strong.
Qed.

Lemma eq_head: forall {A: Type} a b (l: list A), (a :: l) = (b :: l) <-> a = b.
Proof. intros A a b l; split; [intros H; inversion H|intros ->]; auto. Qed.



Lemma id'' a : N.of_nat (N.to_nat a) = a.
Proof.
 destruct a as [ | p]; simpl; trivial.
 destruct (Pos2Nat.is_succ p) as (n,H). rewrite H. simpl. f_equal.
 apply Pos2Nat.inj. rewrite H. apply SuccNat2Pos.id_succ.
Qed.

Lemma inj a a' : N.to_nat a = N.to_nat a' -> a = a'.
Proof.
 intro H. rewrite <- (id'' a), <- (id'' a'). now f_equal.
Qed.

Lemma inj_iff a a' : N.to_nat a = N.to_nat a' <-> a = a'.
Proof.
 split. apply inj. intros; now subst.
Qed.

Lemma id' n : N.to_nat (N.of_nat n) = n.
Proof.
 induction n; simpl; trivial. apply SuccNat2Pos.id_succ.
Qed.


Lemma nth_eq1: forall i a xs,
nth (S i) (a :: xs) 1 = nth i xs 1.
Proof. intros.
       now simpl.
Qed.

Lemma le_le_S_eq : forall (n m: nat), (n <= m)%nat -> (S n <= m)%nat \/ n = m.
Proof le_lt_or_eq.


Lemma prop_checkbb: forall (a: int) (bs: list _lit) (i n: nat),
                    (length bs = (n - i))%nat ->
                    (check_bb a bs i n = true) ->
                    (forall i0, (i <= i0 < n )%nat ->
                    Lit.interp rho (nth (i0 - i) bs 1) = 
                    (@RAWBITVECTOR_LIST.bitOf i0 (wordToList (interp_form_hatom_word a n)))).
Proof. intros a bs.
       revert a.
       induction bs as [ | b ys IHys].
       - intros. simpl in H. 
         cut (i = n). intro Hn. rewrite Hn in H1.
         contradict H1. omega. omega.
       - intros. simpl in H0.
         case_eq (Lit.is_pos b). intros Heq0. rewrite Heq0 in H0.
         case_eq (t_form .[ Lit.blit b] ). intros i1 Heq1. rewrite Heq1 in H0.
         case_eq (t_atom .[ i1]). intros c Heq2. 
         rewrite Heq2 in H0; now contradict H0.
         intros u i2 Heq2. 
         rewrite Heq2 in H0.
         case_eq u; try (intro Heq'; rewrite Heq' in H0; now contradict H0).

         intros. rewrite H2 in H0.
         intros. now contradict H0.
         intros. rewrite H2 in H0. now contradict H0.
         intros. rewrite H2 in H0. now contradict H0.
         intros. rewrite H2 in H0. now contradict H0.
         intros. rewrite H2 in H0.
         case_eq ((a == i2) && Nat_eqb i n1 && Nat_eqb n n0). intros Hif.
         rewrite Hif in H0.
         do 2 rewrite andb_true_iff in Hif. destruct Hif as ((Hif0 & Hif1) & Hif2).
         specialize (@IHys a (S i) n).
         inversion H.
         cut (Datatypes.length ys = (n - S i)%nat). intro HSi.
         specialize (@IHys HSi H0).

         cut (((S i) <= i0 < n)%nat \/ i = i0).
         intro Hd. destruct Hd as [Hd | Hd].
         inversion Hd.
         induction i0 as [ | k IHk].
         now contradict H3.
         specialize (@IHys (S k)).
         cut ((S k - i)%nat = S (k - i)%nat). intro ISk.
         rewrite ISk.
         rewrite (@nth_eq1 (k - i) b ys).
         cut ((S k - S i)%nat = (k - i)%nat). intro ISki.
         specialize (@IHys Hd).
         now rewrite ISki in IHys.
         now simpl. omega.
         rewrite Hd.
         cut ((i0 - i0 = 0)%nat). intro Hi0. rewrite Hi0.
         simpl.

         unfold Lit.interp.
         rewrite Heq0.
         unfold Var.interp.
         rewrite rho_interp.
         rewrite Heq1.

         rewrite Lit.eqb_spec in Hif0.
         rewrite Hif0. rewrite <- Hd.

         generalize wt_t_atom. unfold Atom.wt. unfold is_true.
         rewrite PArray.forallbi_spec;intros.
         assert (i1 < PArray.length t_atom).
         {
           apply PArray.get_not_default_lt.
           rewrite Heq2. now rewrite def_t_atom.
         }

         specialize (@H3 i1 H5).
         rewrite Heq2 in H3. simpl in H3.
         rewrite H2 in H3. simpl in H3.
         rewrite !andb_true_iff in H3.
         decompose [and] H3. clear H3.
         simpl in H7.

         unfold get_type' in H6, H7.
         unfold v_type in H6, H7.
         case_eq (t_interp .[ i1]).
         intros. rewrite H3 in H6. simpl in H6.
         case_eq (v_type0); intros; try (rewrite H8 in H6; now contradict H6).
         simpl.

         unfold Atom.interp_form_hatom_word.
         unfold Atom.interp_form_hatom.
         unfold Atom.interp_hatom.
         rewrite Atom.t_interp_wf; trivial.
         rewrite Heq2.
         simpl.

         rewrite H2. simpl.
         cut (i = n1). intro Hin1. rewrite Hin1.
         cut (n = n0). intro Hnn0.
         rewrite Hnn0.
         case_eq (t_interp .[ i2]).

         intros. rewrite H9 in H7. rewrite <- H9.
         case_eq v_type1; intros; rewrite H10 in H7; try (now contradict H7).
         cut (n2 = n0)%N. intros Hn2n0. rewrite Hn2n0 in H10. 

         rewrite H9. simpl.
         unfold interp_bool.
         case_eq (Typ.cast v_type1 (Typ.TWord n0)).
         (* split *)
         split. rewrite H10.
         simpl.
         rewrite Typ.nat_cast_refl. intros.
         contradict H11. easy.

         apply Typ.eqb_spec in H7. inversion H7. easy.

         now apply Nat.eqb_eq in Hif2.
         now apply Nat.eqb_eq in Hif1.

         omega.
         destruct H1.
         specialize (@le_le_S_eq i i0). intros H11.
         specialize (@H11 H1).
         destruct H11. left. split. exact H5. exact H3.
         right. exact H5.
         omega.
         intro H3. rewrite H3 in H0. now contradict H0.
         intros i3 n0 n1 Heq. rewrite Heq in H0. now contradict H0.
         intros b0 i2 i3 Heq. rewrite Heq in H0. now contradict H0.
         intros n0 i2 i3 i4 Heq. rewrite Heq in H0. now contradict H0.
         intros n0 i3 Heq. rewrite Heq in H0. now contradict H0. 
         intros  i2 i3 Heq. rewrite Heq in H0. now contradict H0.
         intros  Heq. rewrite Heq in H0. now contradict H0.
         intros  Heq. rewrite Heq in H0. now contradict H0.
         intros i1 i2 Heq. rewrite Heq in H0. now contradict H0.
         intros a0 Heq. rewrite Heq in H0. now contradict H0.
         intros a0 Heq. rewrite Heq in H0. now contradict H0.
         intros a0 Heq. rewrite Heq in H0. now contradict H0.
         intros i1 i2 Heq. rewrite Heq in H0. now contradict H0.
         intros i1 i2 Heq. rewrite Heq in H0. now contradict H0.
         intros i1 i2 i3 Heq. rewrite Heq in H0. now contradict H0.
         intros i1 l Heq. rewrite Heq in H0. now contradict H0.
         intros Heq. rewrite Heq in H0. now contradict H0.
Qed.

Lemma prop_checkbb': forall (a: int) (bs: list _lit),
                     (check_bb a bs 0 (length bs) = true) ->
                     (forall i0, (i0 < (length bs) )%nat ->
                     (Lit.interp rho  (nth i0 bs 1)) = 
                     (@RAWBITVECTOR_LIST.bitOf i0 
                     (wordToList (interp_form_hatom_word a (length bs))))).
Proof. intros.
       specialize (@prop_checkbb a bs 0 (length bs)).
       intros Hp.
       cut ((i0 - 0)%nat = i0%nat).
       intro Hc.
       cut (Datatypes.length bs = (Datatypes.length bs - 0)%nat).
       intro Hc2.
       specialize (@Hp Hc2 H i0).
       cut ( (0 <= i0 < Datatypes.length bs)%nat). intro Hc3.
       specialize (@Hp Hc3).
       now rewrite Hc in Hp.
       omega. omega. omega.
Qed.

  Lemma empty_list_length: forall {A: Type} (a: list A), (length a = 0)%nat <-> a = [].
  Proof. intros A a.
         induction a; split; intros; auto; contradict H; easy.
  Qed.


Lemma nth_eq0: forall i a b xs ys,
nth (S i) (a :: xs) false = nth (S i) (b :: ys) false -> nth i xs false = nth i ys false.
Proof. intros.
       now simpl in H.
Qed.

Lemma nth_eq: forall (a b: list bool), (length a) = (length b) -> 
 (forall (i: nat), 
 (i < length a)%nat ->
 nth i a false = nth i b false) -> a = b.
Proof. intros a.
       induction a as [ | a xs IHxs].
       - intros. simpl in *. symmetry in H.
         now rewrite empty_list_length in H.
       - intros [ | b ys] H0.
         + simpl in *. now contradict H0.
         + specialize (@IHxs ys).
           inversion H0. specialize (@IHxs H1).
           intros.         
           pose proof (@H 0%nat). simpl in H2.
           cut ((0 < S (Datatypes.length xs))%nat). intro HS.
           specialize (@H2 HS). rewrite H2; apply f_equal.
           apply IHxs. intros. apply (@nth_eq0 i a b xs ys).
           apply H. simpl. omega. omega.
Qed.

Lemma is_even_0: is_even 0 = true.
Proof. apply refl_equal. Qed.

Lemma rho_1: Lit.interp rho 1 = false.
Proof. unfold Lit.interp.
       unfold Lit.is_pos.
       simpl.
       cut (is_even 1 = false). intro Hev. rewrite Hev.
       unfold Var.interp.
       destruct wf_rho. unfold Lit.blit.
       cut (1 >> 1 = 0). intros Heq0. rewrite Heq0. 
       unfold negb. now rewrite H.
       easy. easy.
Qed.

Lemma rho_false: Lit.interp rho false = true.
Proof. unfold Lit.interp.
       unfold Lit.is_pos.
       simpl.
       cut (is_even 0 = true). intro Hev. rewrite Hev.
       unfold Var.interp.
       destruct wf_rho. simpl. unfold Lit.blit.
       cut (0 >> 1 = 0). intros Heq0. rewrite Heq0. exact H.
       now rewrite lsr_0_l.
       apply is_even_0.
Qed.

Lemma bitOf_of_bitsw: forall a l, 
                               (forall i, 
                               (i < (length l))%nat ->
                               nth i l false = 
                               (@RAWBITVECTOR_LIST.bitOf i (wordToList (interp_form_hatom_word a (length l)) )))
                               ->
                                wordToList (interp_form_hatom_word a (length l)) = l.
Proof. intros. apply nth_eq. now rewrite len_wordToList.
       intros. symmetry. apply H. now rewrite len_wordToList in H0.
Qed.

Lemma valid_check_bbVar lres : C.valid rho (check_bbVar lres).
Proof.
      unfold check_bbVar.
      case_eq (Lit.is_pos lres); intro Heq1; [ |now apply C.interp_true].
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bs Heq0.
      case_eq (check_bb a bs 0 (Datatypes.length bs)); intro Heq2; [ |now apply C.interp_true].
      unfold C.valid. simpl. rewrite orb_false_r.
      unfold Lit.interp. rewrite Heq1.
      unfold Var.interp.
      rewrite wf_interp_form; trivial. rewrite Heq0. simpl.
      rewrite !map_length.
      rewrite weqb_true_iff. apply wordToList_inj.
      rewrite W2L_involutive. specialize (@bitOf_of_bitsw a (map (Lit.interp rho) bs)); intros.
      rewrite map_length in H. apply H.

      intros.
      cut (Lit.interp rho 1 = false). intro Hr. rewrite <- Hr. 
      rewrite map_nth. apply prop_checkbb'. easy. easy.
      apply rho_1. now rewrite map_length.
Qed.


Axiom afold_left_and : forall a, 
      afold_left bool int true andb (Lit.interp rho) a = List.forallb (Lit.interp rho) (to_list a).

  Axiom afold_left_or : forall a,
    afold_left bool int false orb (Lit.interp rho) a =
    C.interp rho (to_list a).

  Axiom afold_left_xor : forall a,
    afold_left bool int false xorb (Lit.interp rho) a =
    C.interp rho (to_list a).

Lemma eqb_spec : forall x y, (x == y) = true <-> x = y.
Proof.
 split;auto using eqb_correct, eqb_complete.
Qed.

Lemma to_list_two: forall {A:Type} (a: PArray.array A), 
       PArray.length a = 2 -> (to_list a) = a .[0] :: a .[1] :: nil.
Proof. intros A a H.
       rewrite to_list_to_list_ntr. unfold to_list_ntr.
       rewrite H.
       cut (0 == 2 = false). intro H1.
       rewrite H1.
       unfold foldi_ntr. rewrite foldi_cont_lt; auto.
       auto.
Qed.

Lemma check_symopp_bvand_nl: forall bs1 bs2 bsres,
  let N := length bsres in
  length bs1 = N ->
  length bs2 = N ->
  check_symopp bs1 bs2 bsres (BO_BVand N) = true ->
bitwp andb (ListToword (map (Lit.interp rho) bs1) N) (ListToword (map (Lit.interp rho) bs2) N) =
ListToword (map (Lit.interp rho) bsres) N.
Proof. intro bs1.
       induction bs1; intros bs2 bsres N Hlbs1 Hlbs2.
       - simpl in *. rewrite <- Hlbs1 in Hlbs2.
         rewrite empty_list_length in Hlbs2. subst.
         symmetry in Hlbs1; rewrite empty_list_length in Hlbs1. subst. intros.
         simpl. now rewrite helper1.
      - case_eq bs2;intros; rewrite H in *; simpl in *.
        now contradict H.
        case_eq bsres; intros; rewrite H1 in *; simpl in *.
        now contradict H.
        case_eq (Lit.is_pos i0); intros; rewrite H2 in H0.
        simpl in H0.
        case_eq (t_form .[ Lit.blit i0]); intros; rewrite H3 in H0; try now contradict H0.
        case_eq (PArray.length a0 == 2); intros; rewrite H4 in H0.
        case_eq ((a0 .[ 0] == a) && (a0 .[ 1] == i) || (a0 .[ 0] == i) && (a0 .[ 1] == a));
          intros; rewrite H5 in H0.
        specialize (IHbs1 l l0). simpl in *.
        case_eq N; intros; subst; simpl. now compute.
        assert (length bs1 = n). { lia. } rewrite <- H.
        rewrite !helper.
        assert (length bs1 = length l). { lia. } rewrite H1.
        rewrite helper.
        assert (length l0 = length l). { now inversion Hlbs2. } rewrite <- H7.
        rewrite helper. rewrite H in H1. rewrite <- H1 in H7.
        rewrite H7 in *.
        rewrite <- IHbs1. simpl.
        apply eqb_spec in H4. apply to_list_two in H4.
        rewrite orb_true_iff in H5; destruct H5 as [ H5 | H5]; rewrite andb_true_iff in H5;
        destruct H5 as (H5a, H5b); apply eqb_spec in H5a; apply eqb_spec in H5b;
        specialize (@rho_interp (Lit.blit i0)); rewrite H3 in rho_interp; simpl in rho_interp;
        rewrite  afold_left_and, H4 in rho_interp; simpl in rho_interp;
        rewrite H5a, H5b, andb_true_r in rho_interp.
          rewrite <- rho_interp.
          now unfold Lit.interp at 3; rewrite H2; unfold Var.interp.
          rewrite andb_comm in rho_interp.
          rewrite <- rho_interp.
          now unfold Lit.interp at 3; rewrite H2; unfold Var.interp.
        easy. easy. rewrite H6 in H0. simpl in H0.
        assert ((n - 0 = n)%nat). { lia. } rewrite H8 in H0. easy.
        now contradict H. 
        now contradict H.
        now contradict H.
Qed.


Lemma check_symopp_bvand_length: forall bs1 bs2 bsres N,
  let n := length bsres in
  check_symopp bs1 bs2 bsres (BO_BVand N) = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 N H.
  induction bsres as [ | r rbsres ].
  intros.
  simpl in H.
  case bs1 in *. simpl in H.
  case bs2 in *. simpl in *. easy. easy.
  case bs2 in *. simpl in *. easy.
  simpl in *. easy.
  intros.
  case bs1 in *.
  case bs2 in *.
  simpl in *. easy.
  simpl in *. easy.
  case bs2 in *. simpl in *. easy.
  set (n' := length rbsres).
  fold n' in n, IHrbsres, H.
  simpl in IHrbsres.
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case (PArray.length a == 2) in H; try easy.
  case ((a .[ 0] == i) && (a .[ 1] == i0) || (a .[ 0] == i0) && (a .[ 1] == i)) in H; try easy.
  specialize (IHrbsres bs1 bs2 (N - 1)%nat H).
  simpl.
  simpl in n.
  fold n' in n.
  unfold n.
  split; apply f_equal. easy. easy.
  easy.
Qed.

Lemma check_symopp_bvor_nl: forall bs1 bs2 bsres,
  let N := length bsres in
  length bs1 = N ->
  length bs2 = N ->
  check_symopp bs1 bs2 bsres (BO_BVor N) = true ->
bitwp orb (ListToword (map (Lit.interp rho) bs1) N) (ListToword (map (Lit.interp rho) bs2) N) =
ListToword (map (Lit.interp rho) bsres) N.
Proof. intro bs1.
       induction bs1; intros bs2 bsres N Hlbs1 Hlbs2.
       - simpl in *. rewrite <- Hlbs1 in Hlbs2.
         rewrite empty_list_length in Hlbs2. subst.
         symmetry in Hlbs1; rewrite empty_list_length in Hlbs1. subst. intros.
         simpl. now rewrite helper1.
      - case_eq bs2;intros; rewrite H in *; simpl in *.
        now contradict H.
        case_eq bsres; intros; rewrite H1 in *; simpl in *.
        now contradict H.
        case_eq (Lit.is_pos i0); intros; rewrite H2 in H0.
        simpl in H0.
        case_eq (t_form .[ Lit.blit i0]); intros; rewrite H3 in H0; try now contradict H0.
        case_eq (PArray.length a0 == 2); intros; rewrite H4 in H0.
        case_eq ((a0 .[ 0] == a) && (a0 .[ 1] == i) || (a0 .[ 0] == i) && (a0 .[ 1] == a));
          intros; rewrite H5 in H0.
        specialize (IHbs1 l l0). simpl in *.
        case_eq N; intros; subst; simpl. now compute.
        assert (length bs1 = n). { lia. } rewrite <- H.
        rewrite !helper.
        assert (length bs1 = length l). { lia. } rewrite H1.
        rewrite helper.
        assert (length l0 = length l). { now inversion Hlbs2. } rewrite <- H7.
        rewrite helper. rewrite H in H1. rewrite <- H1 in H7.
        rewrite H7 in *.
        rewrite <- IHbs1. simpl.
        apply eqb_spec in H4. apply to_list_two in H4.
        rewrite orb_true_iff in H5; destruct H5 as [ H5 | H5]; rewrite andb_true_iff in H5;
        destruct H5 as (H5a, H5b); apply eqb_spec in H5a; apply eqb_spec in H5b;
        specialize (@rho_interp (Lit.blit i0)); rewrite H3 in rho_interp; simpl in rho_interp;
        rewrite  afold_left_or, H4 in rho_interp; simpl in rho_interp;
        rewrite H5a, H5b, orb_false_r in rho_interp.
          rewrite <- rho_interp.
          now unfold Lit.interp at 3; rewrite H2; unfold Var.interp.
          rewrite orb_comm in rho_interp.
          rewrite <- rho_interp.
          now unfold Lit.interp at 3; rewrite H2; unfold Var.interp.
        easy. easy. rewrite H6 in H0. simpl in H0.
        assert ((n - 0 = n)%nat). { lia. } rewrite H8 in H0. easy.
        now contradict H. 
        now contradict H.
        now contradict H.
Qed.

Lemma check_symopp_bvor_length: forall bs1 bs2 bsres N,
  let n := length bsres in
  check_symopp bs1 bs2 bsres (BO_BVor N) = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 N H.
  induction bsres as [ | r rbsres ].
  intros.
  simpl in H.
  case bs1 in *. simpl in H.
  case bs2 in *. simpl in *. easy. easy.
  case bs2 in *. simpl in *. easy.
  simpl in *. easy.
  intros.
  case bs1 in *.
  case bs2 in *.
  simpl in *. easy.
  simpl in *. easy.
  case bs2 in *. simpl in *. easy.
  set (n' := length rbsres).
  fold n' in n, IHrbsres, H.
  simpl in IHrbsres.
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case (PArray.length a == 2) in H; try easy.
  case ((a .[ 0] == i) && (a .[ 1] == i0) || (a .[ 0] == i0) && (a .[ 1] == i)) in H; try easy.
  specialize (IHrbsres bs1 bs2 (N - 1)%nat H).
  simpl.
  simpl in n.
  fold n' in n.
  unfold n.
  split; apply f_equal. easy. easy.
  easy.
Qed.

Lemma check_symopp_bvxor_nl: forall bs1 bs2 bsres,
  let N := length bsres in
  length bs1 = N ->
  length bs2 = N ->
  check_symopp bs1 bs2 bsres (BO_BVxor N) = true ->
bitwp xorb (ListToword (map (Lit.interp rho) bs1) N) (ListToword (map (Lit.interp rho) bs2) N) =
ListToword (map (Lit.interp rho) bsres) N.
Proof. intro bs1.
       induction bs1; intros bs2 bsres N Hlbs1 Hlbs2.
       - simpl in *. rewrite <- Hlbs1 in Hlbs2.
         rewrite empty_list_length in Hlbs2. subst.
         symmetry in Hlbs1; rewrite empty_list_length in Hlbs1. subst. intros.
         simpl. now rewrite helper1.
      - case_eq bs2;intros; rewrite H in *; simpl in *.
        now contradict H.
        case_eq bsres; intros; rewrite H1 in *; simpl in *.
        now contradict H.
        case_eq (Lit.is_pos i0); intros; rewrite H2 in H0.
        simpl in H0.
        case_eq (t_form .[ Lit.blit i0]); intros; rewrite H3 in H0; try now contradict H0.
        case_eq ((i1 == a) && (i2 == i) || (i1 == i) && (i2 == a));
          intros; rewrite H4 in H0.
        specialize (IHbs1 l l0). simpl in *.
        case_eq N; intros; subst; simpl. now compute.
        assert (length bs1 = n). { lia. } rewrite <- H.
        rewrite !helper.
        assert (length bs1 = length l). { lia. } rewrite H1.
        rewrite helper.
        assert (length l0 = length l). { now inversion Hlbs2. } rewrite <- H6.
        rewrite helper. rewrite H in H1. rewrite <- H1 in H6.
        rewrite H6 in *.
        rewrite <- IHbs1. simpl.
        rewrite orb_true_iff in H4; destruct H4 as [ H4 | H4]; rewrite andb_true_iff in H4;
        destruct H4 as (H4a, H4b); apply eqb_spec in H4a; apply eqb_spec in H4b;
        specialize (@rho_interp (Lit.blit i0)); rewrite H3 in rho_interp; simpl in rho_interp;
        rewrite H4a, H4b in rho_interp.
          rewrite <- rho_interp.
          now unfold Lit.interp at 3; rewrite H2; unfold Var.interp.
          rewrite xorb_comm in rho_interp.
          rewrite <- rho_interp.
          now unfold Lit.interp at 3; rewrite H2; unfold Var.interp.
        easy. easy. rewrite H5 in H0. simpl in H0.
        assert ((n - 0 = n)%nat). { lia. } rewrite H7 in H0. easy.
        now contradict H. 
        now contradict H.
Qed.

Lemma check_symopp_bvxor_length: forall bs1 bs2 bsres N,
  let n := length bsres in
  check_symopp bs1 bs2 bsres (BO_BVxor N) = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 N H.
  induction bsres as [ | r rbsres ].
  intros.
  simpl in H.
  case bs1 in *. simpl in H.
  case bs2 in *. simpl in *. easy. easy.
  case bs2 in *. simpl in *. easy.
  simpl in *. easy.
  intros.
  case bs1 in *.
  case bs2 in *.
  simpl in *. easy.
  simpl in *. easy.
  case bs2 in *. simpl in *. easy.
  set (n' := length rbsres).
  fold n' in n, IHrbsres, H.
  simpl in IHrbsres.
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case ((i1 == i) && (i2 == i0) || (i1 == i0) && (i2 == i)) in H; try easy.
  specialize (IHrbsres bs1 bs2 (N - 1)%nat H).
  simpl.
  simpl in n.
  fold n' in n.
  unfold n.
  split; apply f_equal. easy. easy.
  easy.
Qed.



Lemma valid_check_bbOp s pos1 pos2 lres: C.valid rho (check_bbOp s pos1 pos2 lres).
Proof.
      unfold check_bbOp.
      case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | [ A B | A | | | | ]|N | N | N | N | N | | ] a1' a2' Heq9;
        try (intros; now apply C.interp_true).
      (* BVand *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1'));
          simpl; intros Heq10; try (now apply C.interp_true).

        case_eq (
                 check_symopp bs1 bs2 bsres (BO_BVand N) &&
                (Datatypes.length bs1 =? N)); 
        simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        unfold Atom.interp_form_hatom_word at 2, Atom.interp_hatom.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Atom.t_interp_wf; trivial.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. } 
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.
        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop. rewrite Htia1, Htia2.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea).
          intros i j Hv. rewrite Hv in H0. now contradict H0.
          intros i Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros n Hv. rewrite Hv in H0.

        (** n = N **)
        revert v_vala Htia. rewrite Hv.
        intros v_vala Htia.

        generalize (Hs s pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs s pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        revert v_vala1 Htia1 v_vala2 Htia2.
        rewrite H2, H3.
        rewrite Typ.cast_refl.

        intros v_vala1 Htia1 v_vala2 Htia2.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2);
          rewrite Int63Properties.eqb_spec in Heq10a1, Heq10a2.
        rewrite Heq10a1, Heq10a2 in *.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold interp_word.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        rewrite Htia1 in HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2'
        = 
        interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia2 in HSp2.

        apply Word.weqb_true_iff.
        unfold Bval. unfold interp_word.

      (* rewrite (@check_symopp_bvand_nl bs1 bs2 bsres N). *)

        assert (
          H100: ((Datatypes.length (map (Lit.interp rho) bsres)) = N)).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvand_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, <- Heq11a.
       }
        unfold wand.
        rewrite H100, Typ.cast_refl.

       unfold interp_word in HSp1.
        assert (
        H102: ((Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvand_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r. 
          now rewrite !map_length.
        }

        revert HSp1. unfold wzero.
        generalize (natToWord (Datatypes.length (map (Lit.interp rho) bs1)) 0).

        rewrite H102.
        rewrite Typ.cast_refl. intros.

        unfold interp_word in HSp1, HSp2.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits in HSp1, HSp2.

        assert (
          H101: ((Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        { 
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvand_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, Heq11b, <- Heq11a.
        }
        revert HSp2.

        rewrite H101, Typ.cast_refl. intros.
        rewrite HSp1, HSp2. simpl. rewrite <- H100.
        rewrite !map_length.
        rewrite (@check_symopp_bvand_nl bs1 bs2 bsres). reflexivity.
        rewrite !map_length in H100, H101, H102.
        now rewrite H100, H102.
        rewrite !map_length in H100, H101, H102.
        now rewrite H101, H100.
     

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).      
        rewrite !map_length in H100. rewrite H100.
        exact Heq11.

        (** symmetric case *)
        rewrite Heq10a1, Heq10a2 in *.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold interp_word.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' = 
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H4 in HSp1.
        rewrite Htia2 in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1'
        = 
        interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia1 in HSp2.

        apply Word.weqb_true_iff.
        unfold Bval. unfold interp_word.

      (* rewrite (@check_symopp_bvand_nl bs1 bs2 bsres N). *)

        assert (
          H100: ((Datatypes.length (map (Lit.interp rho) bsres)) = N)).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvand_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, <- Heq11a.
       }
        unfold wand.
        rewrite H100, Typ.cast_refl.

       unfold interp_word in HSp1.
        assert (
        H102: ((Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvand_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r. 
          now rewrite !map_length.
        }

        revert HSp1. unfold wzero.
        generalize (natToWord (Datatypes.length (map (Lit.interp rho) bs1)) 0).

        rewrite H102.
        rewrite Typ.cast_refl. intros.

        unfold interp_word in HSp1, HSp2.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits in HSp1, HSp2.

        assert (
          H101: ((Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        { 
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvand_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, Heq11b, <- Heq11a.
        }
        revert HSp2.

        rewrite H101, Typ.cast_refl. intros.
        rewrite HSp1, HSp2. simpl. rewrite <- H100.
        rewrite !map_length.
        rewrite wand_comm. unfold wand.
        rewrite (@check_symopp_bvand_nl bs1 bs2 bsres). reflexivity.
        rewrite !map_length in H100, H101, H102.
        now rewrite H100, H102.
        rewrite !map_length in H100, H101, H102.
        now rewrite H101, H100.
     

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).      
        rewrite !map_length in H100. rewrite H100.
        exact Heq11.

      (* BVor *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1'));
          simpl; intros Heq10; try (now apply C.interp_true).

        case_eq (
                 check_symopp bs1 bs2 bsres (BO_BVor N) &&
                (Datatypes.length bs1 =? N)); 
        simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        unfold Atom.interp_form_hatom_word at 2, Atom.interp_hatom.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Atom.t_interp_wf; trivial.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. } 
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.
        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop. rewrite Htia1, Htia2.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea).
          intros i j Hv. rewrite Hv in H0. now contradict H0.
          intros i Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros n Hv. rewrite Hv in H0.

        (** n = N **)
        revert v_vala Htia. rewrite Hv.
        intros v_vala Htia.

        generalize (Hs s pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs s pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        revert v_vala1 Htia1 v_vala2 Htia2.
        rewrite H2, H3.
        rewrite Typ.cast_refl.

        intros v_vala1 Htia1 v_vala2 Htia2.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2);
          rewrite Int63Properties.eqb_spec in Heq10a1, Heq10a2.
        rewrite Heq10a1, Heq10a2 in *.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold interp_word.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        rewrite Htia1 in HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2'
        = 
        interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia2 in HSp2.

        apply Word.weqb_true_iff.
        unfold Bval. unfold interp_word.

      (* rewrite (@check_symopp_bvand_nl bs1 bs2 bsres N). *)

        assert (
          H100: ((Datatypes.length (map (Lit.interp rho) bsres)) = N)).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, <- Heq11a.
       }
        unfold wand.
        rewrite H100, Typ.cast_refl.

       unfold interp_word in HSp1.
        assert (
        H102: ((Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r. 
          now rewrite !map_length.
        }

        revert HSp1. unfold wzero.
        generalize (natToWord (Datatypes.length (map (Lit.interp rho) bs1)) 0).

        rewrite H102.
        rewrite Typ.cast_refl. intros.

        unfold interp_word in HSp1, HSp2.

        assert (
          H101: ((Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        { 
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, Heq11b, <- Heq11a.
        }
        revert HSp2.

        rewrite H101, Typ.cast_refl. intros.
        rewrite HSp1, HSp2. simpl. rewrite <- H100.
        rewrite !map_length. unfold wor.
        rewrite (@check_symopp_bvor_nl bs1 bs2 bsres). reflexivity.
        rewrite !map_length in H100, H101, H102.
        now rewrite H100, H102.
        rewrite !map_length in H100, H101, H102.
        now rewrite H101, H100.
     

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).      
        rewrite !map_length in H100. rewrite H100.
        exact Heq11.

        (** symmetric case *)
        rewrite Heq10a1, Heq10a2 in *.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold interp_word.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' = 
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H4 in HSp1.
        rewrite Htia2 in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1'
        = 
        interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia1 in HSp2.

        apply Word.weqb_true_iff.
        unfold Bval. unfold interp_word.

        assert (
          H100: ((Datatypes.length (map (Lit.interp rho) bsres)) = N)).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, <- Heq11a.
       }
        unfold wand.
        rewrite H100, Typ.cast_refl.

       unfold interp_word in HSp1.
        assert (
        H102: ((Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r. 
          now rewrite !map_length.
        }

        revert HSp1. unfold wzero.
        generalize (natToWord (Datatypes.length (map (Lit.interp rho) bs1)) 0).

        rewrite H102.
        rewrite Typ.cast_refl. intros.

        unfold interp_word in HSp1, HSp2.

        assert (
          H101: ((Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        { 
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, Heq11b, <- Heq11a.
        }
        revert HSp2.

        rewrite H101, Typ.cast_refl. intros.
        rewrite HSp1, HSp2. simpl. rewrite <- H100.
        rewrite !map_length.
        rewrite wor_comm. unfold wand. unfold wor.
        rewrite (@check_symopp_bvor_nl bs1 bs2 bsres). reflexivity.
        rewrite !map_length in H100, H101, H102.
        now rewrite H100, H102.
        rewrite !map_length in H100, H101, H102.
        now rewrite H101, H100.
     

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).      
        rewrite !map_length in H100. rewrite H100.
        exact Heq11.


      (* BVxor *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1'));
          simpl; intros Heq10; try (now apply C.interp_true).

        case_eq (
                 check_symopp bs1 bs2 bsres (BO_BVxor N) &&
                (Datatypes.length bs1 =? N)); 
        simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        unfold Atom.interp_form_hatom_word at 2, Atom.interp_hatom.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Atom.t_interp_wf; trivial.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. } 
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.
        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop. rewrite Htia1, Htia2.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea).
          intros i j Hv. rewrite Hv in H0. now contradict H0.
          intros i Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros n Hv. rewrite Hv in H0.

        (** n = N **)
        revert v_vala Htia. rewrite Hv.
        intros v_vala Htia.

        generalize (Hs s pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs s pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        revert v_vala1 Htia1 v_vala2 Htia2.
        rewrite H2, H3.
        rewrite Typ.cast_refl.

        intros v_vala1 Htia1 v_vala2 Htia2.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2);
          rewrite Int63Properties.eqb_spec in Heq10a1, Heq10a2.
        rewrite Heq10a1, Heq10a2 in *.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold interp_word.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        rewrite Htia1 in HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2'
        = 
        interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia2 in HSp2.

        apply Word.weqb_true_iff.
        unfold Bval. unfold interp_word.

      (* rewrite (@check_symopp_bvand_nl bs1 bs2 bsres N). *)

        assert (
          H100: ((Datatypes.length (map (Lit.interp rho) bsres)) = N)).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvxor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, <- Heq11a.
       }
        unfold wand.
        rewrite H100, Typ.cast_refl.

       unfold interp_word in HSp1.
        assert (
        H102: ((Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvxor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r. 
          now rewrite !map_length.
        }

        revert HSp1. unfold wzero.
        generalize (natToWord (Datatypes.length (map (Lit.interp rho) bs1)) 0).

        rewrite H102.
        rewrite Typ.cast_refl. intros.

        unfold interp_word in HSp1, HSp2.

        assert (
          H101: ((Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        { 
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvxor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, Heq11b, <- Heq11a.
        }
        revert HSp2.

        rewrite H101, Typ.cast_refl. intros.
        rewrite HSp1, HSp2. simpl. rewrite <- H100.
        rewrite !map_length. unfold wxor.
        rewrite (@check_symopp_bvxor_nl bs1 bs2 bsres). reflexivity.
        rewrite !map_length in H100, H101, H102.
        now rewrite H100, H102.
        rewrite !map_length in H100, H101, H102.
        now rewrite H101, H100.
     

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).      
        rewrite !map_length in H100. rewrite H100.
        exact Heq11.

        (** symmetric case *)
        rewrite Heq10a1, Heq10a2 in *.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold interp_word.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' = 
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H4 in HSp1.
        rewrite Htia2 in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1'
        = 
        interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia1 in HSp2.

        apply Word.weqb_true_iff.
        unfold Bval. unfold interp_word.

        assert (
          H100: ((Datatypes.length (map (Lit.interp rho) bsres)) = N)).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvxor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, <- Heq11a.
       }
        unfold wand.
        rewrite H100, Typ.cast_refl.

       unfold interp_word in HSp1.
        assert (
        H102: ((Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvxor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r. 
          now rewrite !map_length.
        }

        revert HSp1. unfold wzero.
        generalize (natToWord (Datatypes.length (map (Lit.interp rho) bs1)) 0).

        rewrite H102.
        rewrite Typ.cast_refl. intros.

        unfold interp_word in HSp1, HSp2.

        assert (
          H101: ((Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        { 
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvxor_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          apply beq_nat_true in Heq11r.
          now rewrite !map_length, Heq11b, <- Heq11a.
        }
        revert HSp2.

        rewrite H101, Typ.cast_refl. intros.
        rewrite HSp1, HSp2. simpl. rewrite <- H100.
        rewrite !map_length.
        rewrite wxor_comm. unfold wand. unfold wxor.
        rewrite (@check_symopp_bvxor_nl bs1 bs2 bsres). reflexivity.
        rewrite !map_length in H100, H101, H102.
        now rewrite H100, H102.
        rewrite !map_length in H100, H101, H102.
        now rewrite H101, H100.
     

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).      
        rewrite !map_length in H100. rewrite H100.
        exact Heq11.
Qed.

Lemma prop_eq_carry_lit: forall c i, eq_carry_lit c i = true -> interp_carry c = (Lit.interp rho i).
Proof. intro c.
  induction c. 
  - intros. simpl in *. 
    case (Lit.is_pos i0 ) in H; rewrite eqb_spec in H; now rewrite H.
  - intros. simpl. 
    pose proof IHc1. pose proof IHc2.
    simpl in H.
    case_eq ( Lit.is_pos i). intros Hip0.
    rewrite Hip0 in H.
    case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
    case_eq (PArray.length a == 2). intros Hl. rewrite Hl in H.
    (* rewrite orb_true_iff in H; do 2 *) rewrite andb_true_iff in H.

    specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
    simpl in rho_interp.
    rewrite afold_left_and in rho_interp.
    rewrite eqb_spec in Hl.
    apply to_list_two in Hl.
    rewrite Hl in rho_interp.
    simpl in rho_interp.
    rewrite andb_true_r in rho_interp.

    (* destruct H. *)
    + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3.
      unfold Lit.interp at 3. unfold Var.interp.
      rewrite Hip0. now rewrite rho_interp.
    (* + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3. *)
    (*   unfold Lit.interp at 3. unfold Var.interp. *)
    (*   rewrite Hip0. rewrite rho_interp. now rewrite andb_comm. *)
    + intros. rewrite H3 in H. now contradict H.
    + intros. rewrite H2 in H. now contradict H.

  - intros. simpl. 
    pose proof IHc1. pose proof IHc2.
    simpl in H.
    case_eq ( Lit.is_pos i). intros Hip0.
    rewrite Hip0 in H.
    case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
    (* rewrite orb_true_iff in H; do 2 *) rewrite andb_true_iff in H.

    specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
    simpl in rho_interp.

    (* destruct H. *)
    + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3.
      unfold Lit.interp at 3. unfold Var.interp.
      rewrite Hip0. now rewrite rho_interp.
    (* + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3. *)
    (*   unfold Lit.interp at 3. unfold Var.interp. *)
    (*   rewrite Hip0. rewrite rho_interp. now rewrite xorb_comm. *)
    + intros. rewrite H2 in H. now contradict H.

  - intros. simpl. 
    pose proof IHc1. pose proof IHc2.
    simpl in H.
    case_eq ( Lit.is_pos i). intros Hip0.
    rewrite Hip0 in H.
    case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
    case_eq (PArray.length a == 2). intros Hl. rewrite Hl in H.
    (* rewrite orb_true_iff in H; do 2 *) rewrite andb_true_iff in H.

    specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
    simpl in rho_interp.
    rewrite afold_left_or in rho_interp.
    rewrite eqb_spec in Hl.
    apply to_list_two in Hl.
    rewrite Hl in rho_interp.
    simpl in rho_interp.
    rewrite orb_false_r in rho_interp.

    (* destruct H. *)
    + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3.
      unfold Lit.interp at 3. unfold Var.interp.
      rewrite Hip0. now rewrite rho_interp.
    (* + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3. *)
    (*   unfold Lit.interp at 3. unfold Var.interp. *)
    (*   rewrite Hip0. rewrite rho_interp. now rewrite orb_comm. *)
    + intros. rewrite H3 in H. now contradict H.
    + intros. rewrite H2 in H. now contradict H.

  - intros. simpl. 
    pose proof IHc1. pose proof IHc2.
    simpl in H.
    case_eq ( Lit.is_pos i). intros Hip0.
    rewrite Hip0 in H.
    case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
    (* rewrite orb_true_iff in H; do 2 *) rewrite andb_true_iff in H.

    specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
    simpl in rho_interp.

    (* destruct H. *)
    + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3.
      unfold Lit.interp at 3. unfold Var.interp.
      rewrite Hip0. now rewrite rho_interp.
    (* + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3. *)
    (*   unfold Lit.interp at 3. unfold Var.interp. *)
    (*   rewrite Hip0. rewrite rho_interp. *)
    (*   case_eq (Bool.eqb (Lit.interp rho i0) (Lit.interp rho i1)). *)
    (*   intros. apply Bool.eqb_prop in H4. rewrite H4. apply Bool.eqb_reflx. *)
    (*   intros. apply Bool.eqb_false_iff in H4. apply Bool.eqb_false_iff. unfold not in *. intro. symmetry in H5. *)
    (*   apply H4; trivial. *)
    + intros. rewrite H2 in H. now contradict H.
Qed.

Lemma prop_eq_carry_lit2: forall a b, forallb2 eq_carry_lit a b = true -> 
                          (map interp_carry a) = (map (Lit.interp rho) b).
Proof. intro a.
       induction a.
       - intros. simpl in H.
         case b in *. now simpl.
         now contradict H.
       - intros. 
         case b in *.
         now simpl.
         simpl in *. rewrite andb_true_iff in H; destruct H.
         apply prop_eq_carry_lit in H.
         rewrite H. apply f_equal. now apply IHa.
Qed.

Lemma prop_interp_carry3: forall bs2,  map interp_carry (lit_to_carry bs2) = map (Lit.interp rho) bs2.
Proof. intro bs2.
       induction bs2 as [ | xbs2 xsbs2 IHbs2 ].
       - now simpl.
       - simpl. now rewrite IHbs2.
Qed.

Lemma check_concat_map: forall bs1 bs2,
 map (Lit.interp rho) bs1 ++ map (Lit.interp rho) bs2 = map (Lit.interp rho) (bs1 ++ bs2).
Proof. intro bs1.
       induction bs1.
       - intros. now simpl.
       - intros. simpl. now rewrite IHbs1.
Qed.

Lemma concat_nil: forall {A} (a: list A), a ++ [] = a.
Proof. intros A a.
       case a; [ easy | intros; apply app_nil_r ].
Qed.

(* for native-coq compatibility *)
Lemma concat_map : forall (A B : Set) (f : A -> B) (l0 l1 : list A),
  map f (l0 ++ l1) = (map f l0) ++ (map f l1).
Proof.
  induction l0 as [ | xl0 xsl0 IHl0]; intros.
  - now simpl.
  - simpl. now rewrite IHl0.
Qed. 

Lemma concat_word: forall l1 l2,
Word.combine
  (ListToword l1 (length l1)) (ListToword l2 (length l2)) =
ListToword (l1 ++ l2) (length l1 + length l2).
Proof. intro l1.
       induction l1; intros.
       - now simpl.
       - simpl. specialize (@helper_strong (l1 ++ l2) a); intros.
         assert ((Datatypes.length (l1 ++ l2)) =  (Datatypes.length l1 + Datatypes.length l2)%nat).
         { now rewrite app_length. } rewrite H0 in H. rewrite H. rewrite <- IHl1.
         rewrite helper_strong. now simpl.
Qed.

Lemma check_concat_bvconcat: forall bs1 bs2 bsres, 
  check_concat bs1 bs2 bsres = true ->
  (Word.combine (ListToword (map (Lit.interp rho) bs1) (length bs1)) (ListToword (map (Lit.interp rho) bs2) (length bs2))) =
  (ListToword (map (Lit.interp rho) bsres) (length bs1 + length bs2)).
Proof. intros. specialize (concat_word (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)); intros.
       rewrite !map_length in H0. rewrite H0. unfold check_concat in H.
       case_eq (forallb2 eq_carry_lit (lit_to_carry (bs1 ++ bs2)) bsres); intros.
         apply prop_eq_carry_lit2 in H1.
         rewrite prop_interp_carry3 in H1.
         rewrite check_concat_map. now rewrite H1.
       rewrite H1 in H. now contradict H.
Qed.

Lemma check_concat_bvconcat_len: forall bs1 bs2 bsres n m, 
  check_concat bs1 bs2 bsres = true ->
  length bs1 = n -> length bs2 = m ->
  (length bsres = n + m)%nat.
Proof. intro bs1.
       induction bs1; intros.
       - simpl in *; subst. simpl.
         unfold check_concat in H. simpl in H.
         case_eq (forallb2 eq_carry_lit (lit_to_carry bs2) bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         assert ( length (map (Lit.interp rho) bs2) = length (map (Lit.interp rho) bsres) ).
         { now rewrite H0. }  now rewrite !map_length in H1.
         rewrite H0 in H; now contradict H.
       - unfold check_concat in H.
         case_eq (forallb2 eq_carry_lit (lit_to_carry ((a :: bs1) ++ bs2)) bsres); intros.
         apply prop_eq_carry_lit2 in H2.
         rewrite prop_interp_carry3 in H2.
         assert ( length (map (Lit.interp rho) ((a :: bs1) ++ bs2)) = length (map (Lit.interp rho) bsres) ).
         { now rewrite H2. } rewrite !map_length in H3; subst. rewrite <- H3. simpl.
         apply f_equal. now rewrite app_length.
         rewrite H2 in H; now contradict H.
Qed.

Lemma app_length : forall (l1 l2: list bool), (length (l1 ++ l2))%nat = ((length l1) + (length l2))%nat.
Proof.
  induction l1; simpl; auto.
Qed.

Lemma concat_len: forall (bs1 bs2 bsres: list bool), bs1 ++ bs2 = bsres ->
                              ((length bs1) + (length bs2))%nat = (length bsres)%nat.
Proof. intro bs1.
       induction bs1.
       - intros. simpl. simpl in H. now rewrite H.
       - intros. simpl. simpl in H. rewrite <- H. simpl.
         now rewrite app_length.
Qed.


Lemma valid_check_bbConcat s pos1 pos2 lres : C.valid rho (check_bbConcat s pos1 pos2 lres).
Proof.
      unfold check_bbConcat.
      case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | |[ A B | A| | | | ]|N|N|N|N|N |N | ]  a1' a2' Heq9; try (intros; now apply C.interp_true).
      (* BVconcat *)
    - case_eq ((a1 == a1') && (a2 == a2')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (
             check_concat bs1 bs2 bsres &&  ((Datatypes.length bs1) =? N)%nat &&
             ((Datatypes.length bs2) =? n)%nat
        ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply Word.weqb_true_iff.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H4 in H0; try (now contradict H0).
        rename H4 into Hv.

        generalize (Hs s pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs s pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        (** case a1 = a1' and a2 = a2' **)
        rewrite andb_true_iff in Heq10.
        destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2;
        rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_word a = 
                interp_word t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_word. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.

        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite !Typ.cast_refl.
        unfold Bval.

        assert (H100: ((Datatypes.length (map (Lit.interp rho) bsres))) = (N + n)%nat).
        {
          rewrite !andb_true_iff in Heq11.
          destruct Heq11 as ((Heq11, Heq11l) & Heq11r).
          apply  (@check_concat_bvconcat_len bs1 bs2 bsres N n) in Heq11.
          now rewrite !map_length.
          now rewrite Nat.eqb_eq in Heq11l.
          now rewrite Nat.eqb_eq in Heq11r.
        }

        rewrite H100.
        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp1.
        unfold interp_word in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_word in HSp1. 

        revert HSp1.

        assert (H101: ((Datatypes.length (map (Lit.interp rho) bs1))) = N).
        {
          rewrite !andb_true_iff in Heq11.
          destruct Heq11 as ((Heq11, Heq11l) & Heq11r).
          apply  check_concat_bvconcat in Heq11.
          apply Nat.eqb_eq in Heq11l.
          now rewrite map_length.
        }


        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' = 
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H6 in HSp2.
        unfold interp_word in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_word in HSp2. 

        revert HSp2.

        assert (H102: ((Datatypes.length (map (Lit.interp rho) bs2))) = n).
        {
          rewrite !andb_true_iff in Heq11.
          destruct Heq11 as ((Heq11, Heq11l) & Heq11r).
          apply  check_concat_bvconcat in Heq11.
          apply Nat.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        rewrite H102.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp2. simpl.
        remember check_concat_bvconcat.
        specialize (@check_concat_bvconcat bs1 bs2 bsres); intros.
        rewrite <- H101, <- H102.
        rewrite !map_length, H7. reflexivity.


        rewrite !andb_true_iff in Heq11.
        now destruct Heq11 as ((Heq11, Heq11l) & Heq11r).
Qed.

Lemma len_cons: forall {A} (a: list A) c, length (a ++ [c]) = S (length a).
Proof. intros A a.
       induction a; intros.
       - now simpl.
       - simpl. now rewrite IHa.
Qed.

Lemma length_empty_ext: forall i c, (Datatypes.length (extend_lit [] i c)) = i.
Proof. intro i.
       induction i; intros.
       - now simpl.
       - simpl. now rewrite <- (IHi c) at 2.
Qed.

Lemma word_combine_nil: forall a, Word.combine (ListToword a (Datatypes.length a)) WO = ListToword a (Datatypes.length a + 0).
Proof. intro a.
       induction a; intros.
       - unfold ListToword. now simpl.
       - simpl. rewrite helper_strong. simpl. rewrite IHa.
         specialize (@helper_strong a0 a); intros.
         assert (((Datatypes.length a0 + 0) = (Datatypes.length a0))%nat) by lia.
         now rewrite H0, H.
Qed.

Lemma gen: forall {A} (a: list A) i, (length a + S i)%nat = (S (length a + i))%nat.
Proof. intros; lia. Qed.

Lemma ext_len: forall i a c, (length (extend_lit a i c)) =  (length a + i)%nat.
Proof. intro i.
       induction i; intros.
       - simpl. lia.
       - simpl. rewrite IHi. lia.
Qed.

(*
Lemma ext_lit_cons: forall i a c, (extend_lit a (S i) c) = extend_lit a i c ++ [c].
Proof. intro i.
       induction i; intros.
       - now simpl.
       - simpl. now rewrite <- IHi.
Qed.
*)

Lemma wzero0: (wzero 0) = WO.
Proof. now compute. Qed.

Fixpoint _false_list (a: list bool) n :=
  match n with
    | O => a
    | S n' => false :: _false_list a n'
  end.

Definition false_list n := _false_list [] n.

Lemma _flsi: forall i a, _false_list a (S i) = false :: _false_list a i.
Proof. intro i.
       induction i; intros.
       - now simpl.
       - rewrite IHi. now simpl.
Qed. 

Lemma _flsapp: forall i, _false_list [] i ++ [false] = false :: _false_list [] i.
Proof. intro i.
       induction i; intros.
       - now simpl.
       - simpl. now rewrite IHi.
Qed.

Lemma _flslen: forall i a, length (_false_list a i) = ((length a) + i)%nat.
Proof. intro i.
       induction i; intros.
       - simpl. lia.
       - simpl. rewrite IHi. lia.
Qed. 

Lemma _wzeroi: forall i,
map (Lit.interp rho) (extend_lit [] i Lit._false) = false_list i.
Proof. intro i.
       induction i; intros.
       - now simpl.
       - simpl. unfold false_list. simpl.
         assert (Lit.interp rho Lit._false = false).
           { specialize (Lit.interp_false rho wf_rho). intros.
              rewrite <- not_true_iff_false.
              unfold not in *.
              intros. now apply H. }
         rewrite H. rewrite IHi. now unfold false_list.
Qed.

Lemma wzeroi: forall i,
wzero i = ListToword (map (Lit.interp rho) (extend_lit [] i Lit._false)) i.
Proof. intro i.
       induction i; intros.
       - now simpl.
       - simpl. rewrite _wzeroi.
         assert (Lit.interp rho Lit._false = false).
           { specialize (Lit.interp_false rho wf_rho). intros.
              rewrite <- not_true_iff_false.
              unfold not in *.
              intros. now apply H. }
         rewrite H. unfold wzero in *. simpl. rewrite IHi.
         rewrite _wzeroi. simpl. unfold false_list.
         specialize (@helper_strong (_false_list [] i) false); intros.
         rewrite _flslen in H0. simpl in H0. now rewrite H0.
Qed.

(*
Lemma zext_empty: forall l, (zextend_lit l 0) = l.
Proof. intros; unfold zextend_lit; now simpl. Qed.


Lemma zext_lit_cons: forall i a c, (extend_lit a (S i) c) = extend_lit a i c ++ [c].
Proof. intro i.
       induction i; intros.
       - now simpl.
       - simpl. now rewrite <- IHi.
Qed.


Lemma zext_cons: forall i l a, 
                  (map (Lit.interp rho) (zextend_lit (a :: l) i)) = 
                  (Lit.interp rho a) :: (map (Lit.interp rho) (zextend_lit l i)).
Proof. intro i.
       induction i; intros.
       - now rewrite zext_empty.
       - unfold zextend_lit in *. simpl.
         rewrite IHi. simpl.
         rewrite !map_app. simpl. now rewrite IHi.
Qed.
*)

Lemma zext_len: forall a i, (length (zextend_lit a i)) =  (length a + i)%nat.
Proof. intros. unfold zextend_lit. now rewrite rev_length, ext_len, rev_length. Qed.

Lemma zextend_interp_all: forall a i, RAWBITVECTOR_LIST.zextend (map (Lit.interp rho) a) i =
map (Lit.interp rho) (zextend_lit a i).
Proof. intro a.
       induction a as [ | xa xsa IHa].
       - intros. simpl.
         induction i.
         + intros. now simpl.
         + intros. unfold RAWBITVECTOR_LIST.zextend in *.
           simpl in *. rewrite IHi.
           assert (Lit.interp rho Lit._false = false).
           { specialize (Lit.interp_false rho wf_rho). intros.
              rewrite <- not_true_iff_false.
              unfold not in *.
              intros. now apply H. }
           unfold zextend_lit. simpl. rewrite map_app. simpl.
           now rewrite H.
        - intros. 
          induction i.
          + simpl. unfold RAWBITVECTOR_LIST.zextend, zextend_lit in *.
            simpl. rewrite !map_rev, !map_app. simpl. now rewrite map_rev.
          + unfold RAWBITVECTOR_LIST.zextend, zextend_lit in *.
            simpl in *. rewrite map_app. rewrite <- IHi. simpl.
           assert (Lit.interp rho Lit._false = false).
           { specialize (Lit.interp_false rho wf_rho). intros.
              rewrite <- not_true_iff_false.
              unfold not in *.
              intros. now apply H. }
           now rewrite H.
Qed.

Lemma wmsb_b: forall a b,
a <> [] ->
wmsb (ListToword a (Datatypes.length a)) b = true ->
wmsb (ListToword a (Datatypes.length a)) false = true.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now contradict H.
       - simpl in *. rewrite helper_strong in *. now simpl in *.
Qed. 

Lemma wmsb_b2: forall a b,
a <> [] ->
wmsb (ListToword a (Datatypes.length a)) b = false ->
wmsb (ListToword a (Datatypes.length a)) false = false.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now contradict H.
       - simpl in *. rewrite helper_strong in *. now simpl in *.
Qed.

Lemma rev_n: forall n,
((rev (RAWBITVECTOR_LIST.extend [true] n true) ++ [true]) = 
true :: (rev (RAWBITVECTOR_LIST.extend [true] n true))).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. rewrite IHn. simpl. now rewrite <- IHn.
Qed.

Lemma rev_n2: forall n,
((rev (RAWBITVECTOR_LIST.extend [false] n false) ++ [false]) = 
false :: (rev (RAWBITVECTOR_LIST.extend [false] n false))).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. rewrite IHn. simpl. now rewrite <- IHn.
Qed.

Lemma ones_n: forall n,
(wones n)~1 = ListToword (rev (RAWBITVECTOR_LIST.extend [true] n true)) (S n).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. rewrite IHn.
         assert ((rev (RAWBITVECTOR_LIST.extend [true] xn true) ++ [true]) = 
                 true :: (rev (RAWBITVECTOR_LIST.extend [true] xn true))).
         { now rewrite rev_n. }
         rewrite H.
         specialize (RAWBITVECTOR_LIST.length_extend [true] xn true); intros.
         simpl in H0.
         assert ((Datatypes.length (RAWBITVECTOR_LIST.extend [true] xn true)) = 
                (Datatypes.length (rev (RAWBITVECTOR_LIST.extend [true] xn true)))).
         { now rewrite rev_length. }
         rewrite H1 in H0. now rewrite <- H0, helper_strong.
Qed.

Lemma zeros_n: forall n,
(wzero n)~0 = ListToword (rev (RAWBITVECTOR_LIST.extend [false] n false)) (S n).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. unfold wzero in *. simpl. rewrite IHn.
         assert ((rev (RAWBITVECTOR_LIST.extend [false] xn false) ++ [false]) = 
                 false :: (rev (RAWBITVECTOR_LIST.extend [false] xn false))).
         { now rewrite rev_n2. }
         rewrite H.
         specialize (RAWBITVECTOR_LIST.length_extend [false] xn false); intros.
         simpl in H0.
         assert ((Datatypes.length (RAWBITVECTOR_LIST.extend [false] xn false)) = 
                (Datatypes.length (rev (RAWBITVECTOR_LIST.extend [false] xn false)))).
         { now rewrite rev_length. }
         rewrite H1 in H0. now rewrite <- H0, helper_strong.
Qed.


Lemma mk_list_false_eq: forall n,
RAWBITVECTOR_LIST.mk_list_false n ++ [false] = false :: RAWBITVECTOR_LIST.mk_list_false n.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. now rewrite IHn.
Qed.

Lemma rev_mk_list_false_same: forall n,
rev (RAWBITVECTOR_LIST.mk_list_false n) = (RAWBITVECTOR_LIST.mk_list_false n).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. now rewrite IHn, mk_list_false_eq.
Qed.

Lemma wzero_mk_list_false_eq:  forall n,
wzero n = ListToword (RAWBITVECTOR_LIST.mk_list_false n) n.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. unfold wzero in *. simpl in *. rewrite IHn.
         specialize (helper_strong (RAWBITVECTOR_LIST.mk_list_false xn) false); intros.
         rewrite RAWBITVECTOR_LIST.length_mk_list_false in H. now rewrite H.
Qed.

Lemma app_not_nil: forall (a: list bool) b, a ++ [b] <> [].
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros; simpl; easy.
Qed.

Lemma extend_empty: forall n,
rev (RAWBITVECTOR_LIST.extend [] n false) ++ [false] = 
false :: (rev (RAWBITVECTOR_LIST.extend [] n false)). 
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. rewrite IHn. simpl. now rewrite <- IHn.
Qed.

Lemma wzero_zext: forall n,
wzero n = ListToword (rev (RAWBITVECTOR_LIST.extend [] n false)) n.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. unfold wzero in *. simpl. rewrite IHn.
         specialize (RAWBITVECTOR_LIST.length_extend [] xn false); intros.
         simpl in H.
         assert ( ((rev (RAWBITVECTOR_LIST.extend [] xn false) ++ [false])) = 
                  (false :: (rev (RAWBITVECTOR_LIST.extend [] xn false)))   ).
         { now rewrite extend_empty. }
         rewrite H0.

         specialize (helper_strong (rev (RAWBITVECTOR_LIST.extend [] xn false)) false); intros.
         rewrite rev_length in H1.
         rewrite RAWBITVECTOR_LIST.length_extend in H1. simpl in H1.
         now rewrite H1.
Qed.

Lemma zext_eq: forall a n, zext (ListToword a (length a)) n =
                           ListToword (RAWBITVECTOR_LIST.zextend a n) (length a + n).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl. unfold zext. simpl. unfold RAWBITVECTOR_LIST.zextend. simpl.
         now rewrite wzero_zext.
       - simpl. rewrite helper_strong. unfold zext in *. simpl in *.
         rewrite IHa.
         unfold RAWBITVECTOR_LIST.zextend. simpl.

         assert ( (rev (RAWBITVECTOR_LIST.extend (rev xsa ++ [xa]) n false)) = 
                  (xa :: (rev (RAWBITVECTOR_LIST.extend (rev xsa) n false)))   ).
         { induction n; intros. unfold RAWBITVECTOR_LIST.zextend. simpl. rewrite !rev_app_distr, rev_involutive. now simpl.
           simpl. unfold RAWBITVECTOR_LIST.zextend in *. rewrite IHn. now simpl. }
         rewrite H.
         specialize (RAWBITVECTOR_LIST.length_extend (rev xsa) n); intros.
         rewrite rev_length in H0.
         assert (Datatypes.length (RAWBITVECTOR_LIST.extend (rev xsa) n false) = 
                 Datatypes.length (rev (RAWBITVECTOR_LIST.extend (rev xsa) n false))).
         { now rewrite rev_length. }
         specialize (helper_strong (rev (RAWBITVECTOR_LIST.extend (rev xsa) n false)) xa ); intros.
         rewrite rev_length, RAWBITVECTOR_LIST.length_extend, rev_length in H2.
         now rewrite H2.
Qed.

Lemma forallb_eqb_refl: forall a, forallb2 eq_carry_lit (lit_to_carry a) a = true.
Proof. intro a.
       induction a; intros.
       - now simpl.
       - simpl. rewrite IHa. now case_eq (Lit.is_pos a ); rewrite Int63Axioms.eqb_refl.
Qed. 

Lemma zextend_interp_len: forall bs1 bsres (i: nat),
                           check_zextend bs1 bsres i = true ->
                           length bsres = (length bs1 + i)%nat.
Proof. intro bs1.
       induction bs1; intros.
       - simpl in *. unfold check_zextend in H.
         case_eq (forallb2 eq_carry_lit (lit_to_carry (zextend_lit [] i)) bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0. 
         assert (length (map (Lit.interp rho) (zextend_lit [] i)) = length (map (Lit.interp rho) bsres)).
         { now rewrite H0. }
         rewrite !map_length in H1. unfold zextend_lit in H1. 
         rewrite rev_length in H1. simpl in H1.
         now rewrite length_empty_ext in H1.
         rewrite H0 in H; now contradict H.
       - simpl. unfold check_zextend in H.
         case_eq ( forallb2 eq_carry_lit (lit_to_carry (zextend_lit (a :: bs1) i)) bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         assert (length (map (Lit.interp rho) (zextend_lit (a :: bs1) i)) = length (map (Lit.interp rho) bsres)).
         { now rewrite H0. }
         rewrite !map_length in H1. now rewrite zext_len in H1.
         rewrite H0 in H; now contradict H.
Qed.

Lemma zextend_interp_main: forall bs1 bsres (n i: N),
                           check_zextend bs1 bsres (N.to_nat i) = true ->
                           @RAWBITVECTOR_LIST.bv_zextn n i
                             (map (Lit.interp rho) bs1) = map (Lit.interp rho) bsres.
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros. simpl.
         unfold check_zextend in H. simpl in H.
         case_eq (forallb2 eq_carry_lit
          (lit_to_carry (zextend_lit [] (N.to_nat i))) bsres).
         intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         simpl in H0.
         unfold RAWBITVECTOR_LIST.bv_zextn. rewrite <- H0.
         rewrite <- zextend_interp_all. now simpl.
         intros. rewrite H0 in H. now contradict H0.
       - intros. unfold RAWBITVECTOR_LIST.bv_zextn, check_zextend in H.
         case_eq (
          forallb2 eq_carry_lit
          (lit_to_carry
             (zextend_lit (xbs1 :: xsbs1) (N.to_nat i)))
          bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         simpl in H0. simpl.

         unfold RAWBITVECTOR_LIST.bv_zextn in *.
         case_eq (N.to_nat i). intros. rewrite H1 in H0.
         simpl in *. unfold zextend_lit in H0.
         simpl in H0. unfold RAWBITVECTOR_LIST.zextend . simpl.
         rewrite map_rev in H0. rewrite map_app in H0. simpl in H0.
         now rewrite map_rev in H0.
         intros. rewrite H1 in H0.
         rewrite <- H0.
         rewrite <- zextend_interp_all.
         simpl.
         assert (Lit.interp rho Lit._false = false).
         { specialize (Lit.interp_false rho wf_rho). intros.
            rewrite <- not_true_iff_false.
            unfold not in *.
            intros. now apply H2. }
         reflexivity.

         rewrite H0 in H. now contradict H.
Qed.

Lemma valid_check_bbZextend s pos lres : C.valid rho (check_bbZextend s pos lres).
Proof.
      unfold check_bbZextend.
      case_eq (S.get s pos); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq2; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq4.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq5.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | | | | ]  a1'  Heq6; try (intros; now apply C.interp_true).
      (* BVzextend *)
    - case_eq ((a1 == a1')); simpl; intros Heq7; try (now apply C.interp_true).
        case_eq (
            check_zextend bs1 bsres i && ((Datatypes.length bs1) =? n)%nat
        ); simpl; intros Heq8; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq3.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq5. simpl.

        apply Word.weqb_true_iff.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy. }
        specialize (@H0 H1). rewrite Heq6 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H3 in H0; try (now contradict H0).
        rename H0 into Hv.

        generalize (Hs s pos). intros HSp. unfold C.valid in HSp. rewrite Heq1 in HSp.
        unfold C.interp in HSp. unfold existsb in HSp. rewrite orb_false_r in HSp.
        unfold Lit.interp in HSp. rewrite Heq2 in HSp. unfold Var.interp in HSp.
        rewrite rho_interp in HSp. rewrite Heq4 in HSp. simpl in HSp.

        apply Word.weqb_true_iff in HSp.

        unfold get_type' in H2. unfold v_type in H2.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2.

        (** case a1 = a1' **)
        rewrite eqb_spec in Heq7; rewrite Heq7 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_word a = 
                interp_word t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H0. rewrite Heq6. simpl.
        unfold interp_word. unfold apply_unop.

        rewrite !Atom.t_interp_wf; trivial.

        revert v_vala1 Htia1. rewrite H2.
        intros v_vala1 Htia1.
        rewrite Htia1.
        rewrite !Typ.cast_refl.
        unfold Bval.

        assert (H100: ( (Datatypes.length (map (Lit.interp rho) bsres))) = (n + i)%nat). 
        { 
           rewrite andb_true_iff in Heq8.
           destruct Heq8 as (Heq8a, Heq8b).
           rewrite map_length.
           apply zextend_interp_len in Heq8a.
           rewrite Nat.eqb_eq in Heq8b.
           now rewrite Heq8b in Heq8a.
        }

        rewrite H100.
        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp.
        unfold interp_word in HSp.
        rewrite Htia1 in HSp.
        unfold interp_word in HSp. 

        revert HSp.

        assert (H101: ((Datatypes.length (map (Lit.interp rho) bs1))) = n).
        {
           rewrite andb_true_iff in Heq8.
           destruct Heq8 as (Heq8a, Heq8b).
           rewrite map_length.
           now rewrite Nat.eqb_eq in Heq8b.
        }

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp. simpl. unfold zext.
        rewrite andb_true_iff in Heq8.
        destruct Heq8 as (Heq8a, Heq8b).
        rewrite map_length in H101. rewrite <- H101.
        specialize (@zextend_interp_main bs1 bsres (N.of_nat n) (N.of_nat i)); intros.
        rewrite <- H5. simpl. unfold RAWBITVECTOR_LIST.bv_zextn, RAWBITVECTOR_LIST.zextend.
        simpl. rewrite Nat2N.id.
        specialize (zext_eq (map (Lit.interp rho) bs1) i); intros.
        unfold zext in H6. rewrite map_length in H6. rewrite H6.
        unfold RAWBITVECTOR_LIST.zextend. reflexivity. rewrite Nat2N.id.
        easy.
Qed.


(*
Lemma sextend_interp_zero: forall a, RAWBITVECTOR_LIST.sextend (map (Lit.interp rho) a) O =
(map (Lit.interp rho) (sextend_lit a 0)).
Proof. intros.
       unfold RAWBITVECTOR_LIST.sextend.
       case_eq a; intros; now simpl.
Qed.


Let a := [false; true; true; false; false; true].
Compute ListToword (List.rev (RAWBITVECTOR_LIST.sextend (List.rev a) 0)) (length a + 0).
Compute sext (ListToword a (length a)) 0.
*)

Lemma sext_eq: forall a n, sext (ListToword a (length a)) n =
                           ListToword ((RAWBITVECTOR_LIST.sextend a n)) (length a + n).
Proof. Admitted.

(*
Lemma sext_eq: forall a n, sext (ListToword a (length a)) n =
                           ListToword (rev (RAWBITVECTOR_LIST.sextend (rev a) n)) (length a + n).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl. unfold sext. simpl. 
         now rewrite rev_mk_list_false_same, wzero_mk_list_false_eq.
       - simpl. rewrite helper_strong.
         unfold sext in *. simpl in *.
         case_eq (wmsb (ListToword xsa (Datatypes.length xsa)) xa); intros.

         unfold RAWBITVECTOR_LIST.sextend.
         case_eq (rev xsa ++ [xa]); intros. contradict H0.
         apply app_not_nil.

         case_eq xsa; intros. subst. inversion H0.
         subst. simpl in *. rewrite H. now rewrite ones_n.
         rewrite <- H1. apply wmsb_b in H; try rewrite H1; try easy.
         rewrite H in IHa. rewrite <- H1, IHa. simpl.
         unfold RAWBITVECTOR_LIST.sextend. rewrite H1. simpl.
         case_eq (rev l0 ++ [b0]); intros. contradict H2.
         apply app_not_nil.
         rewrite <- H2, <- H0, H1. simpl.
         assert ( (rev (RAWBITVECTOR_LIST.extend ((rev l0 ++ [b0]) ++ [xa]) n b) ) = 
                  (xa :: (rev (RAWBITVECTOR_LIST.extend ((rev l0 ++ [b0])) n b)))).
         { induction n; intros. simpl. rewrite !rev_app_distr, rev_involutive. now simpl.
           simpl. rewrite IHn. now simpl. }
         rewrite H3, H2. simpl.
         rewrite H1 in H0. simpl in H0. rewrite H2 in H0. simpl in H0. inversion H0.
         rewrite <- H5, <- H2.
         specialize (@RAWBITVECTOR_LIST.length_extend (rev l0 ++ [b0]) n b1); intros.
         rewrite app_length, rev_length in H4. simpl in H4.
         assert ((Datatypes.length l0 + 1 + n)%nat = (S (Datatypes.length l0 + n)%nat)). { lia. }
         rewrite H7 in H4.
         assert (Datatypes.length (RAWBITVECTOR_LIST.extend (rev l0 ++ [b0]) n b1) =
                 Datatypes.length (rev (RAWBITVECTOR_LIST.extend (rev l0 ++ [b0]) n b1))).
         { now rewrite rev_length. }
         rewrite H8 in H4. rewrite <- H4. now rewrite helper_strong.

         case_eq xsa; intros. subst. simpl in *. rewrite H. now rewrite zeros_n.
         rewrite <- H0. apply wmsb_b2 in H; try rewrite H0; try easy.
         rewrite H in IHa. rewrite <- H0, IHa. simpl.
         unfold RAWBITVECTOR_LIST.sextend. rewrite H0. simpl.
         case_eq (rev l ++ [b]); intros. contradict H1.
         apply app_not_nil.
         rewrite <- H1, H1. simpl.  rewrite <- !H1. 
         assert ((b0 :: l0 ++ [xa]) = ((b0 :: l0) ++ [xa])). { now simpl. }
         rewrite H2, <- H1.
         assert ( (rev (RAWBITVECTOR_LIST.extend ((rev l ++ [b]) ++ [xa]) n b0) ) = 
                  (xa :: (rev (RAWBITVECTOR_LIST.extend ((rev l ++ [b])) n b0)))).
         { induction n; intros. simpl. rewrite !rev_app_distr, rev_involutive. now simpl.
           simpl. rewrite IHn. now simpl. }
         rewrite H3. simpl.
         specialize (@RAWBITVECTOR_LIST.length_extend (rev l ++ [b]) n b0); intros.
         rewrite app_length, rev_length in H4. simpl in H4.
         assert ((Datatypes.length l + 1 + n)%nat = (S (Datatypes.length l + n)%nat)). { lia. }
         rewrite H5 in H4.
         assert (Datatypes.length (RAWBITVECTOR_LIST.extend (rev l ++ [b]) n b0) =
                 Datatypes.length (rev (RAWBITVECTOR_LIST.extend (rev l ++ [b]) n b0))).
         { now rewrite rev_length. }
         rewrite H6 in H4. rewrite <- H4. now rewrite helper_strong.
Qed.
*)

Lemma sextend_interp_empty: forall i, RAWBITVECTOR_LIST.sextend (map (Lit.interp rho) []) i =
map (Lit.interp rho) (sextend_lit [] i).
Proof. simpl. intro i.
       induction i.
       - intros. now simpl.
       - intros. simpl.
         unfold RAWBITVECTOR_LIST.sextend in *.
         simpl in *. rewrite IHi.
         assert (Lit.interp rho Lit._false = false).
           { specialize (Lit.interp_false rho wf_rho). intros.
              rewrite <- not_true_iff_false.
              unfold not in *.
              intros. now apply H. }
        simpl. unfold sextend_lit. simpl.
        rewrite map_app. simpl. 
        now rewrite H.
 Qed.

Lemma rev_app_cons: forall (a: list bool) b, (rev (a ++ [b]) = (b:: rev a)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. rewrite IHa. now simpl.
Qed.

Lemma sextend_interp_all: forall a i, RAWBITVECTOR_LIST.sextend (map (Lit.interp rho) a) i =
map (Lit.interp rho) (sextend_lit a i).
Proof. intro a.
       induction a as [ | xa xsa IHa].
       - intros. simpl.
         induction i.
         + intros. now simpl.
         + intros. unfold RAWBITVECTOR_LIST.sextend in *.
           simpl in *.  rewrite IHi.
           unfold sextend_lit. simpl.
           assert (Lit.interp rho Lit._false = false).
           { specialize (Lit.interp_false rho wf_rho). intros.
              rewrite <- not_true_iff_false.
              unfold not in *.
              intros. now apply H. }
           rewrite map_app. simpl.
           now rewrite H.
        - intros. 
          induction i.
          + simpl. unfold RAWBITVECTOR_LIST.sextend in *. simpl in *.
            unfold RAWBITVECTOR_LIST._sextend in *.
            case_eq (rev (map (Lit.interp rho) xsa)); intros.
            rewrite H in IHa. simpl. 
            case_eq xsa; intros. now simpl. subst.

            simpl in H. apply app_not_nil in H. now contradict H.
            rewrite H in IHa. specialize (IHa 0%nat). simpl in *.
            unfold sextend_lit in *. simpl in *.
            unfold _sextend_lit in *.
            case_eq (rev xsa); intros.
            rewrite <- map_rev in H. rewrite H0 in H.
            simpl in H. now contradict H.

            rewrite H0 in *. simpl in *.
            rewrite rev_app_cons. simpl.
            rewrite IHa.
            rewrite !map_app, !map_rev, map_app. simpl.
            rewrite rev_app_cons. now simpl.
          + unfold RAWBITVECTOR_LIST.sextend, zextend_lit in *.
            simpl in *.
            unfold RAWBITVECTOR_LIST._sextend  in *.
            case_eq (rev (map (Lit.interp rho) xsa) ++ [Lit.interp rho xa]); intros.
            simpl in H.
            apply app_not_nil in H. now contradict H.
            rewrite H in *. simpl. rewrite IHi.
            unfold sextend_lit, _sextend_lit . simpl.
            case_eq (rev xsa ++ [xa]); intros.
            apply (f_equal (map (Lit.interp rho))) in H0.
            simpl in H0. rewrite map_app in H0. 
            apply app_not_nil in H0. now contradict H0.
            simpl. rewrite <- H0.  simpl. rewrite <- map_rev in H.
            apply (f_equal (map (Lit.interp rho))) in H0.
            simpl in H0. symmetry. rewrite map_app. simpl.
            rewrite map_app in H0. simpl in H0. rewrite H in H0.
            inversion H0. easy.
Qed.



Lemma sextend_interp_main: forall bs1 bsres (n i: N),
                           check_sextend bs1 bsres (N.to_nat i) = true ->
                           @RAWBITVECTOR_LIST.bv_sextn n i
                             (map (Lit.interp rho) bs1) = map (Lit.interp rho) bsres.
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros. simpl.
         unfold check_zextend in H. simpl in H.
         case_eq (forallb2 eq_carry_lit
          (lit_to_carry (sextend_lit [] (N.to_nat i))) bsres).
         intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         simpl in H0.
         unfold RAWBITVECTOR_LIST.bv_sextn.
         now rewrite sextend_interp_empty.
         intros. 
         unfold check_sextend in H.
         rewrite H0 in H. now contradict H0.
       - intros. unfold RAWBITVECTOR_LIST.bv_sextn, check_sextend in H.
         case_eq (
          forallb2 eq_carry_lit
          (lit_to_carry
             (sextend_lit (xbs1 :: xsbs1) (N.to_nat i)))
          bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         simpl in H0.

         unfold RAWBITVECTOR_LIST.bv_sextn in *.
         case_eq (N.to_nat i). intros. rewrite H1 in H0.
         simpl in *.
         unfold RAWBITVECTOR_LIST.sextend, RAWBITVECTOR_LIST._sextend . simpl.
         case_eq (rev (map (Lit.interp rho) xsbs1) ++ [Lit.interp rho xbs1]); intros.
         apply app_not_nil in H2. now contradict H2.
         rewrite <- H0, <- H2. 
         unfold sextend_lit, _sextend_lit. simpl.
         case_eq (rev xsbs1 ++ [xbs1]); intros.
         apply (f_equal (map (Lit.interp rho))) in H3.
         simpl in H3. rewrite map_app in H3.
         apply app_not_nil in H3. now contradict H3.
         rewrite <- H3.
         rewrite <- map_rev. rewrite rev_app_cons.
         rewrite <- map_rev. rewrite rev_involutive.
         rewrite map_rev. 
         rewrite map_app. simpl. rewrite rev_app_cons.
         apply f_equal. now rewrite map_rev, rev_involutive.

         intros. rewrite H1 in H0.
         rewrite <- H0.
         
         rewrite sextend_interp_all.
         now simpl.

         rewrite H0 in H. now contradict H.
Qed.

Lemma valid_check_bbSextend s pos lres : C.valid rho (check_bbSextend s pos lres).
Proof.
      unfold check_bbSextend.
      case_eq (S.get s pos); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq2; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq4.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq5.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | | | | ]  a1'  Heq6; try (intros; now apply C.interp_true).
      (* BVsextend *)
    - case_eq ((a1 == a1')); simpl; intros Heq7; try (now apply C.interp_true).
        case_eq (
            check_sextend bs1 bsres i && ((Datatypes.length bs1) =? n)%nat
        ); simpl; intros Heq8; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq3.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq5. simpl.

        apply weqb_true_iff. 

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy. }
        specialize (@H0 H1). rewrite Heq6 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H3 in H0; try (now contradict H0).
        rename H0 into Hv.

        generalize (Hs s pos). intros HSp. unfold C.valid in HSp. rewrite Heq1 in HSp.
        unfold C.interp in HSp. unfold existsb in HSp. rewrite orb_false_r in HSp.
        unfold Lit.interp in HSp. rewrite Heq2 in HSp. unfold Var.interp in HSp.
        rewrite rho_interp in HSp. rewrite Heq4 in HSp. simpl in HSp.

        apply weqb_true_iff in HSp.

        unfold get_type' in H2. unfold v_type in H2.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2.

        (** case a1 = a1' **)
        rewrite eqb_spec in Heq7; rewrite Heq7 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_word a = 
                interp_word t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H0. rewrite Heq6. simpl.
        unfold interp_word. unfold apply_unop.

        rewrite !Atom.t_interp_wf; trivial.

        revert v_vala1 Htia1. rewrite H2.
        intros v_vala1 Htia1.
        rewrite Htia1.
        rewrite !Typ.cast_refl.
        unfold Bval.

        assert (H100: ((Datatypes.length (map (Lit.interp rho) bsres))) = (i + n)%nat).
        {
           rewrite andb_true_iff in Heq8.
           destruct Heq8 as (Heq8a, Heq8b).
           rewrite map_length.
           specialize (@sextend_interp_main bs1 bsres (N.of_nat n) (N.of_nat i)).
           intros. rewrite Nat2N.id in H4.
           apply H4 in Heq8a.
           unfold RAWBITVECTOR_LIST.bv_sextn in Heq8a.
           assert (length (RAWBITVECTOR_LIST.sextend (map (Lit.interp rho) bs1) i) 
           = length (map (Lit.interp rho) bsres)).
           { rewrite Nat2N.id in Heq8a. now rewrite Heq8a. }
           rewrite RAWBITVECTOR_LIST.length_sextend, !map_length in H5.
          
           rewrite <- H5.
           
           rewrite Nat.eqb_eq in Heq8b.
           rewrite Heq8b. lia.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100. rewrite Nat.add_comm.
        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp.
        unfold interp_word in HSp.
        rewrite Htia1 in HSp.
        unfold interp_word in HSp. 

        revert HSp.

        assert (H101: ((Datatypes.length (map (Lit.interp rho) bs1))) = n).
        {
           rewrite andb_true_iff in Heq8.
           destruct Heq8 as (Heq8a, Heq8b).
           rewrite map_length.
           now rewrite Nat.eqb_eq in Heq8b.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp. simpl.
        unfold BITVECTOR_LIST.bv_sextn.
        specialize (sext_eq (map (Lit.interp rho) bs1) i); intros.
        rewrite map_length in H7.
        rewrite andb_true_iff in Heq8.
        destruct Heq8 as (Heq8a, Heq8b).
        rewrite map_length in H101. rewrite <- H101.
        rewrite H7. 
        specialize (@sextend_interp_main bs1 bsres (N.of_nat n) (N.of_nat i)); intros.
        rewrite <- H8. unfold RAWBITVECTOR_LIST.bv_sextn. now rewrite Nat2N.id.
        rewrite Nat2N.id. easy.
Qed.

Lemma extract_interp_zero: forall a n, RAWBITVECTOR_LIST.extract (map (Lit.interp rho) a) 0 n =
map (Lit.interp rho) (extract_lit a 0 n).
Proof. intro a.
       induction a as [ | xa xsa IHa].
       - intros. now simpl.
       - intros. simpl.
         case_eq n.
         now simpl.
         intros. simpl. apply f_equal.
         now rewrite IHa.
Qed.

Lemma extract_interp_all: forall a m n, RAWBITVECTOR_LIST.extract (map (Lit.interp rho) a) m n =
map (Lit.interp rho) (extract_lit a m n).
Proof. intro a.
       induction a as [ | xa xsa IHa].
       - intros. now simpl.
       - intros. case_eq m.
         intros. apply extract_interp_zero.
         intros. simpl.         
         case_eq n.
         now simpl.
         intros. simpl.
         now rewrite IHa.
Qed.

Lemma N_minus_n_O: forall n, (n - 0)%N = n.
Proof. intros. lia. Qed.

Lemma len_extr: forall n a, 
(Datatypes.length a) >= n ->
(Datatypes.length (RAWBITVECTOR_LIST.extract a 0 n)) = n.
Proof. intros. case_eq n; intros.
       case_eq a; intros; now simpl.
       specialize (@RAWBITVECTOR_LIST.length_extract a (N.of_nat 0) (N.of_nat n)); intros.
       rewrite !Nat2N.id in H1. simpl in H1. rewrite <- H0.
       
       rewrite N_minus_n_O in H1.
       rewrite !Nat2N.id in H1.
       rewrite H1. easy. lia. rewrite H0. lia.
Qed.

Lemma len_extr_lit: forall a n,
(Datatypes.length a) >= n ->
(Datatypes.length (map (Lit.interp rho) (extract_lit a 0 n))) = n.
Proof. intros. 
       rewrite <- extract_interp_all, len_extr. easy.
       rewrite map_length. easy.
Qed.

Lemma extract_interp_main: forall bs1 bsres (i n0: nat),
                  check_extract bs1 bsres i (n0 + i) = true ->
                  wextr (ListToword (map (Lit.interp rho) bs1) (length bs1)) i (i + n0) n0 
                  = ListToword (map (Lit.interp rho) bsres) n0.
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros. simpl. unfold wextr. simpl.
         unfold check_extract in H. simpl in H.
         case_eq ((0 <? n0 + i)); intros.
         rewrite H0 in H. now contradict H.
         rewrite H0 in H.
         case_eq bsres; intros. now simpl.
          intros. rewrite H1 in H. now contradict H.
       - intros. unfold check_extract in H.
         case_eq (((Datatypes.length (xbs1 :: xsbs1)) <? n0 + i)); intros.
         rewrite H0 in H. now contradict H.
         rewrite H0 in H.
         case_eq (
          forallb2 eq_carry_lit
          (lit_to_carry
          (extract_lit (xbs1 :: xsbs1) 
          i ((n0 + i)))) bsres); intros.
         apply prop_eq_carry_lit2 in H1.
         rewrite prop_interp_carry3 in H1.
         simpl in H1. simpl.

         unfold wextr. rewrite W2L_involutive.
         case_eq i; intros; rewrite H2 in H1.
         case_eq (n0)%nat; intros; rewrite H3 in H1.
         simpl in H1.  rewrite <- H1. now simpl.
         simpl in H1. simpl. rewrite plus_0_r in H1.
         specialize (helper_strong (RAWBITVECTOR_LIST.extract (map (Lit.interp rho) xsbs1) 0 n)
                                   (Lit.interp rho xbs1 )); intros.
         rewrite len_extr in H4.
         rewrite H4, <- H1. simpl.
         specialize (helper_strong (map (Lit.interp rho) (extract_lit xsbs1 0 n))
                                   (Lit.interp rho xbs1 )); intros.
         rewrite len_extr_lit in H5.
         rewrite H5. apply f_equal. now rewrite extract_interp_all.
         rewrite <- H2 in H1. simpl in H0. rewrite H2, H3 in H0.
         apply Nat.ltb_ge in H0. lia. rewrite map_length.
         rewrite <- H2 in H1. simpl in H0. rewrite H2, H3 in H0.
         apply Nat.ltb_ge in H0. lia. 

         rewrite <- H2 in H1.
         case_eq ((n0 + i)%nat); intros; rewrite H3 in H1.
         rewrite <- H2. rewrite Nat.add_comm in H3. rewrite H3.
         rewrite <- H1. simpl. case_eq i; easy.
         rewrite <- H2. rewrite Nat.add_comm in H3. rewrite H3.
         simpl. rewrite H2. now rewrite extract_interp_all, H1.
         simpl. now rewrite map_length.
         
         rewrite H1 in H. now contradict H.
Qed.

Lemma inj_ge: forall a b c, (N.of_nat a >= N.of_nat (b + c))%N <-> a >= (b + c).
Proof. intros. lia. Qed.

Lemma res_len: forall a b (i n: nat), check_extract a b i (n + i) = true -> length b = n.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl in H. unfold check_extract in H.
         simpl in H. case_eq (0 <? n + i); intros; rewrite H0 in H.
         now contradict H0.
         case_eq b; intros; rewrite H1 in H.
         case_eq n; intros. now simpl. subst. now contradict H0.
         now contradict H.
       - simpl in H. unfold check_extract in H.
         case_eq (Datatypes.length (xa :: xsa) <? n + i); intros; rewrite H0 in H.
         now contradict H.
         case_eq (forallb2 eq_carry_lit (lit_to_carry (extract_lit (xa :: xsa) i (n + i))) b); intros;
         rewrite H1 in H.
         apply prop_eq_carry_lit2 in H1.
         rewrite prop_interp_carry3 in H1.
         rewrite <- extract_interp_all in H1.
         assert ( length (RAWBITVECTOR_LIST.extract (map (Lit.interp rho) (xa :: xsa)) i (n + i)) =
                  length (map (Lit.interp rho) b)). { now rewrite H1. }
         specialize (@RAWBITVECTOR_LIST.length_extract (map (Lit.interp rho) (xa :: xsa)) (N.of_nat i) (N.of_nat (n + i))); intros.
         rewrite Nat2N.id in H3. assert ((N.to_nat (N.of_nat (n + i))) = (n + i)%nat). { lia. }
         assert (N.to_nat (N.of_nat (n + i) - N.of_nat i) = n). { lia. }
         rewrite H4, H5 in H3. rewrite H3 in H2. now rewrite map_length in H2.
         rewrite map_length. apply Nat.ltb_ge in H0. apply inj_ge. lia. lia.
         now contradict H.
Qed.

  Lemma Npos_dist: forall p p0: positive, (Npos (p + p0))%N = (Npos p + Npos p0)%N.
  Proof. intros. case p in *; case p0 in *; easy. Qed.

  Lemma not_ltb2: forall (n0 n1 i: N), (n1 >= n0 + i)%N -> (n1 <? n0 + i)%N = false.
  Proof. intro n0.
         induction n0.
         intros. simpl in *.
         now apply N.ltb_nlt in H.

         intros. simpl.
         case_eq i.
         intros. subst. simpl in H.
         now apply N.ltb_nlt in H.
         intros. subst.
         apply N.ltb_nlt in H.
         now rewrite Npos_dist.
  Qed.

  Lemma not_ltb3: forall (n0 n1 i: nat), (n1 >= n0 + i)%nat -> (n1 <? n0 + i)%nat = false.
  Proof. intro n0.
         induction n0.
         intros. simpl in *.
         now apply Nat.ltb_ge in H.

         intros. simpl.
         case_eq i.
         intros. subst. simpl in H.
         now apply Nat.ltb_ge in H.
         intros. subst.
         now apply Nat.ltb_ge in H.
  Qed.

Lemma l2w_eq: forall a b n,
(length a = n) -> (length b = n) ->
ListToword a n = ListToword b n -> a = b.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl in H. symmetry in H. rewrite H in H0. now rewrite empty_list_length in H0.
       - simpl in *. case_eq b; intros. subst. now contradict H0.
         rewrite <- H in H1.
         rewrite helper_strong in H1. rewrite H2 in H0.
         rewrite <- H in H0. inversion H0. rewrite <- H4 in H1. rewrite H2 in H1.
         rewrite helper_strong in H1. inversion H1. rewrite H5 in H1.
         apply f_equal. apply IHa with (n - 1)%nat. lia. rewrite <- H.
         lia. assert ((n - 1)%nat = (length l)). { lia. }
         
         rewrite H3. 
         now dependent rewrite -> H6.
Qed.

Lemma valid_check_bbExtract s pos lres : C.valid rho (check_bbExtract s pos lres).
Proof.
      unfold check_bbExtract.
      case_eq (S.get s pos); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq2; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq4.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq5.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | | | | ]  a1'  Heq6; try (intros; now apply C.interp_true).
      (* BVextract *)
    - case_eq ((a1 == a1')); simpl; intros Heq7; try (now apply C.interp_true).
        case_eq (
          check_extract bs1 bsres i (n0 + i) &&
          ( (Datatypes.length bs1) =? n1)%nat && (n0 + i <=? n1)%nat
        ); simpl; intros Heq8; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq3.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq5. simpl.

        apply weqb_true_iff.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy. }
        specialize (@H0 H1). rewrite Heq6 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H3 in H0; try (now contradict H2).
        rename H0 into Hv.

        generalize (Hs s pos). intros HSp. unfold C.valid in HSp. rewrite Heq1 in HSp.
        unfold C.interp in HSp. unfold existsb in HSp. rewrite orb_false_r in HSp.
        unfold Lit.interp in HSp. rewrite Heq2 in HSp. unfold Var.interp in HSp.
        rewrite rho_interp in HSp. rewrite Heq4 in HSp. simpl in HSp.

        apply weqb_true_iff in HSp.

        unfold get_type' in H2. unfold v_type in H2.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2.

        (** case a1 = a1' **)
        rewrite eqb_spec in Heq7; rewrite Heq7 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_word a = 
                interp_word t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H0. rewrite Heq6. simpl.
        unfold interp_word. unfold apply_unop.

        rewrite !Atom.t_interp_wf; trivial.

        revert v_vala1 Htia1. rewrite H2.
        intros v_vala1 Htia1.
        rewrite Htia1.
        rewrite !Typ.cast_refl.
        unfold Bval.

        assert (H100: ((Datatypes.length (map (Lit.interp rho) bsres))) = n0).
        { rewrite map_length. specialize (@res_len bs1 bsres i n0); intros.
          apply H4.
           rewrite !andb_true_iff in Heq8.
           now destruct Heq8 as ((Heq8a, Heq8b), Heq8c).
        }

        rewrite H100.
        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp.
        unfold interp_word in HSp.
        rewrite Htia1 in HSp.
        unfold interp_word in HSp. 

        revert HSp.

        assert (H101: ((Datatypes.length (map (Lit.interp rho) bs1))) = n1).
        {  rewrite !andb_true_iff in Heq8.
           destruct Heq8 as ((Heq8a, Heq8b), Heq8c).
           rewrite map_length.
           now rewrite Nat.eqb_eq in Heq8b.
        }


        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp. simpl.
        unfold wextr.
        rewrite !andb_true_iff in Heq8.
        destruct Heq8 as (Heq8a, Heq8b).
        specialize (@extract_interp_main bs1 bsres i n0).
        intros.
        rewrite map_length in H101.
        rewrite H101 in H5. unfold wextr in H5. now rewrite H5.
Qed.

(** BV ADDITION CHECKER WORDS*)

Lemma check_add_bvadd_length: forall bs1 bs2 bsres c,
  let n := length bsres in
  check_add bs1 bs2 bsres c = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 c H.
  induction bsres as [ | r rbsres ].
  intros.
  simpl in H.
  case bs1 in *. simpl in H.
  case bs2 in *. simpl in *. easy. easy.
  case bs2 in *. simpl in *. easy.
  simpl in *. easy.
  intros.
  case bs1 in *.
  case bs2 in *.
  simpl in *. easy.
  simpl in *. easy.
  case bs2 in *. simpl in *. easy.
  set (n' := length rbsres).
  fold n' in n, IHrbsres, H.
  simpl in IHrbsres.
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case (Lit.is_pos i1) in H.  
  case (t_form .[ Lit.blit i1]) in H; try now contradict H.
  rewrite andb_true_iff in H. destruct H.
  specialize (IHrbsres bs1 bs2 ((Cor (Cand (Clit i) (Clit i0)) (Cand (Cxor (Clit i) (Clit i0)) c))) H0). 
  simpl.
  simpl in n.
  split; apply f_equal. easy. easy.
  easy. easy.
Qed.



Lemma check_add_list:forall bs1 bs2 bsres c, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_add bs1 bs2 bsres c ->
                      (RAWBITVECTOR_LIST.add_list_ingr (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)
                        (interp_carry c))
                        =
                        (map (Lit.interp rho) bsres).
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros. simpl in H1.
         case_eq bs2. intros. rewrite H2 in H1. simpl.
         case_eq bsres. intros. rewrite H3 in H1. now simpl.
         intros. rewrite H3 in H1. now contradict H1.
         intros. rewrite H2 in H1. now contradict H1.
      - intros.
        case_eq bs2. intros. rewrite H2 in H1. simpl in H1. now contradict H1.
        intros. rewrite H2 in H1.
        case_eq bsres. intros. rewrite H3 in H1. simpl in H1. now contradict H1.
        intros. rewrite H3 in H1. simpl in H1.
        case_eq ( Lit.is_pos i0). intros. rewrite H4 in H1.
        case_eq ( t_form .[ Lit.blit i0]); intros; rewrite H5 in H1; try now contradict H.
        case_eq ( Lit.is_pos i1). intros. rewrite H6 in H1.
        case_eq ( t_form .[ Lit.blit i1]); intros; rewrite H7 in H1; try now contradict H.
        unfold is_true in H1.
        rewrite andb_true_iff in H1. destruct H1.
        unfold n in *.
        rewrite H3 in H.
        rewrite H2, H3 in H0.
        inversion H. inversion H0.

        specialize 
        (@IHbs1 l l0 
        ((Cor (Cand (Clit xbs1) (Clit i)) (Cand (Cxor (Clit xbs1) (Clit i)) c)))
        H10 H11 H8).

        simpl in *. unfold RAWBITVECTOR_LIST.of_bits in IHbs1.
        case_eq (RAWBITVECTOR_LIST.add_carry (Lit.interp rho xbs1) (Lit.interp rho i)
        (interp_carry c)). intros r c0 Heqrc.

        (** rho_interp Lit.blit i0 **)
        pose proof (rho_interp (Lit.blit i0)).
        rewrite H5 in H9. simpl in H9.

        (** rho_interp Lit.blit i1 **)
        pose proof (rho_interp (Lit.blit i1)).
        rewrite H7 in H12. simpl in H12.

        unfold Lit.interp at 3.
        rewrite H4. unfold Var.interp. rewrite H9.
        rewrite <- IHbs1.
        simpl.
        cut (r = xorb (Lit.interp rho i1) (Lit.interp rho i2)).
        cut (c0 =  (Lit.interp rho xbs1 && Lit.interp rho i
        || xorb (Lit.interp rho xbs1) (Lit.interp rho i) && interp_carry c)).
        intros. now rewrite H13, H14.

        (* c *)
        case ((Lit.interp rho xbs1)) in *.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc. easy.
        inversion Heqrc. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc. easy.
        inversion Heqrc. easy.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc. easy.
        inversion Heqrc. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc. easy.
        inversion Heqrc. easy.

        (* r *)
        rewrite andb_true_iff in H1.
        destruct H1.
        rewrite orb_true_iff in H1.
        destruct H1; rewrite andb_true_iff in H1; destruct H1.
        rewrite eqb_spec in H1, H14. rewrite H1, H14 in *.

        apply  prop_eq_carry_lit in H13. rewrite <- H13.

        case ((Lit.interp rho xbs1)) in *.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy. 
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.

        rewrite eqb_spec in H1, H14. rewrite H1, H14 in *.

        apply  prop_eq_carry_lit in H13. rewrite <- H13.

        case ((Lit.interp rho xbs1)) in *.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy. 
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.

        (** contradictions **)
        intros. rewrite H6 in H1. now contradict H1.
        intros. rewrite H4 in H1. now contradict H1.
Qed.

Lemma check_add_word:forall bs1 bs2 bsres c, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_add bs1 bs2 bsres c ->
   (ListToword (RAWBITVECTOR_LIST.add_list_ingr (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)
   (interp_carry c)) n)
    =
   (ListToword (map (Lit.interp rho) bsres) n).
Proof. intros. now rewrite (@check_add_list bs1 bs2 bsres). Qed.

Lemma check_add_bvadd: forall bs1 bs2 bsres n, 
  (N.of_nat(length bs1) = n)%N -> 
  (N.of_nat(length bs2) = n)%N -> 
  (N.of_nat(length bsres) = n)%N ->  
  check_add bs1 bs2 bsres (Clit Lit._false) = true ->
  (RAWBITVECTOR_LIST.bv_add (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2) =
   (map (Lit.interp rho) bsres)).
Proof. intros.
       pose proof H as H'. pose proof H0 as H0'. pose proof H1 as H1'.
       rewrite <- H1 in H. apply Nat2N.inj in H.
       rewrite <- H1 in H0. apply Nat2N.inj in H0.
       specialize (@check_add_list bs1 bs2 bsres ( (Clit Lit._false)) H H0 H2). intros.
       unfold RAWBITVECTOR_LIST.bv_add.
       unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits.
       unfold BITVECTOR_LIST.of_bits.
       rewrite !map_length, H, H0.
       rewrite N.eqb_refl.

       assert (  (interp_carry (Clit Lit._false)) = false).
       {
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H4.
         rewrite not_true_iff_false in H4.
         now unfold interp_carry.
       }

       rewrite H4 in H3.
       unfold RAWBITVECTOR_LIST.add_list.
       apply H3.
Qed.


Lemma check_add_addlist: forall bs1 bs2 bsres n, 
  (N.of_nat(length bs1) = n)%N -> 
  (N.of_nat(length bs2) = n)%N -> 
  (N.of_nat(length bsres) = n)%N ->  
  check_add bs1 bs2 bsres (Clit Lit._false) = true ->
  (RAWBITVECTOR_LIST.add_list (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2) =
   (map (Lit.interp rho) bsres)).
Proof. intros.
       pose proof H as H'. pose proof H0 as H0'. pose proof H1 as H1'.
       rewrite <- H1 in H. apply Nat2N.inj in H.
       rewrite <- H1 in H0. apply Nat2N.inj in H0.
       specialize (@check_add_list bs1 bs2 bsres ( (Clit Lit._false)) H H0 H2). intros.
       unfold RAWBITVECTOR_LIST.bv_add.
       unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits.
       unfold BITVECTOR_LIST.of_bits.

       assert (  (interp_carry (Clit Lit._false)) = false).
       {
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H4.
         rewrite not_true_iff_false in H4.
         now unfold interp_carry.
       }

       rewrite H4 in H3.
       unfold RAWBITVECTOR_LIST.add_list.
       apply H3.
Qed.

Fixpoint listToN (l: list bool) : N :=
  match l with
    | [] => 0
    | xl :: xsl =>
    if xl then Nsucc (2* listToN xsl)
    else  (2* listToN xsl)
  end%N.

  Fixpoint listTonat (l: list bool) : nat :=
  match l with
    | [] => O
    | xl :: xsl =>
    if xl then S (2* listTonat xsl)
    else  (2 * listTonat xsl)
  end%nat.
  
Fixpoint mod2 (n : nat) : bool :=
  match n with
    | O => false
    | 1%nat => true
    | S (S n') => mod2 n'
  end.


Require Import Div2.

Fixpoint natTolist (sz n : nat) {struct sz} : list bool :=
  match sz with
    | O => []
    | S sz' => (mod2 n) :: (natTolist sz' (div2 n))
  end.

Fixpoint posToList (n : nat) (p : positive) {struct p} : list bool :=
  match n with
    | 0%nat => []
    | S n' =>
      match p with
        | xI p' => true  :: (posToList n' p')
        | xO p' => false :: (posToList n' p')
        | xH    => true  :: (RAWBITVECTOR_LIST.mk_list_false n')
      end
  end.

Definition NToList (n : N) (sz : nat): list bool :=
  match n with
    | N0     => RAWBITVECTOR_LIST.mk_list_false sz
    | Npos p => posToList sz p
  end.

Lemma len_n2l: forall sz n, length (natTolist sz n) = sz.
Proof. intro sz.
       induction sz as [ | xsz IHsz ]; intros.
       - now simpl.
       - simpl. now rewrite IHsz.
Qed.

Lemma ltN: forall a, (listToN (true :: a)) = Nsucc (2* listToN a).
Proof. intro a.
       case_eq a; intros.
       - now simpl.
       - simpl. case_eq b; intros;
         case_eq (listToN l); intros; now simpl.
Qed.


Lemma empty_total: forall a b: nat,
(a + a + (b + b))%nat = 0%nat
->
(a + b)%nat = 0%nat.
Proof. intro a.
       induction a as [ | xa IHa ]; intros; lia.
Qed.

Lemma empty_total2: forall a b: nat,
(a + b)%nat = 0%nat -> a%nat = 0%nat /\ b%nat = 0%nat .
Proof. intro a.
       induction a as [ | xa IHa ]; intros; lia.
Qed.

Lemma mod2Sn: forall n,
mod2 (n + S n) = true.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. assert ((xn + S (S xn))%nat = (S (xn + (S xn)))%nat) by now simpl.
         now rewrite H.
Qed.

Lemma mod2n: forall n,
mod2 (n + n) = false.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. assert ((xn + (S xn))%nat = (S (xn + (xn)))%nat) by now simpl.
         now rewrite H.
Qed.

Lemma mod2Sn2: forall (a b n: nat),
(a + a + (b + b))%nat = S n ->
mod2 n = true.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - case_eq b; intros.
         + simpl in *. subst.  simpl in *. now contradict H.
         + simpl in *. subst. simpl in *. inversion H.
           assert ((n0 + S n0)%nat = (S (n0 + n0))%nat) by now simpl.
           now rewrite mod2Sn.
       - case_eq n; intros. subst. contradict H. lia.
         rewrite <- H0. 
         apply (IHa (S b)). rewrite <- H. lia.
Qed.

Lemma mod2Sn1: forall (a n: nat),
(a + a)%nat = S n ->
mod2 n = true.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - simpl in *. now contradict H.
       - simpl in *. inversion H.
           assert ((xa + S xa)%nat = (S (xa + xa))%nat) by now simpl.
           now rewrite mod2Sn.
Qed.

Lemma mod2Sn1': forall (a n: nat),
(a + a)%nat = n ->
mod2 n = false.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - simpl in *. rewrite <- H. now simpl.
       - simpl in *. inversion H. simpl.
           assert ((xa + S xa)%nat = (S (xa + xa))%nat) by now simpl.
           rewrite H1.
           now rewrite mod2n.
Qed.

Lemma mod2n2: forall (a b n: nat),
(a + a + (b + b))%nat = n ->
mod2 n = false.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - case_eq b; intros.
         + simpl in *. subst.  simpl in *. easy.
         + simpl in *. subst. simpl in *.
           assert ((n0 + S n0)%nat = (S (n0 + n0))%nat) by now simpl.
           rewrite H.
           now rewrite mod2n.
       - case_eq n; intros. subst. lia.
         rewrite <- H0. 
         apply (IHa (S b)). rewrite <- H. lia.
Qed.


Lemma helper_div: forall a n,
(a + a)%nat = S n ->
a = S (Nat.div2 n).
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - simpl in *. now contradict H.
       - simpl in *. inversion H. apply f_equal. 
         case_eq xa; intros. now simpl.
         simpl. assert ((n0 + S (S n0))%nat = (S (n0 + (S n0)))%nat) by now simpl.
         rewrite H2, <- H0. apply IHa. lia.
Qed.

Lemma helper_div2: forall a b n,
 (a + a + (b + b))%nat = S n
-> 
(a + b)%nat = (S (Nat.div2 n)).
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - simpl in *. now apply helper_div.
       - simpl in *. inversion H.
         case_eq b; intros. subst. simpl in *.
         assert ( (S (xa + 0)) = (xa + S 0)%nat) by now simpl.
         rewrite H0. apply IHa. simpl. lia.
         assert ((S (xa + S n0))%nat =  (xa + (S (S n0)))%nat ) by now simpl.
         rewrite H2. apply IHa. lia.
Qed.

Theorem mod2_S_double : forall n, mod2 (S (2 * n)) = true.
  induction n; simpl; intuition; rethink.
Qed.

Theorem mod2_double : forall n, mod2 (2 * n) = false.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; rethink.
Qed.

Theorem div2_odd' : forall n:nat,
  mod2 n = true
  -> n = S (2 * div2 n).
  induction n using strong; simpl; intuition.

  destruct n; simpl in *; intuition.
    discriminate.
  destruct n; simpl in *; intuition.
  do 2 f_equal.
  replace ((div2 n)%nat + S (div2 n + 0))%nat with (S (div2 n + (div2 n + 0))); auto.
Qed.

Theorem div2_even' : forall n,
  mod2 n = false
  -> (n = 2 * div2 n)%nat.
  induction n using strong; simpl; intuition.

  destruct n; simpl in *; intuition.
  destruct n; simpl in *; intuition.
    discriminate.
  f_equal.
  replace (div2 n + S (div2 n + 0))%nat with (S (div2 n + (div2 n + 0))); auto.
Qed.


Lemma modtf: forall n,
mod2 (2 * n) = false.
Proof. induction n; intros. 
       now simpl. simpl.
       assert ((n + S (n + 0))%nat = (S (n + (n + 0)))%nat ) by now simpl.
       rewrite H. now simpl in IHn.
Qed.

Lemma modStf: forall n,
mod2 (S n) = true -> mod2 n = false.
Proof.  induction n; intuition.
        apply div2_odd' in H. inversion H.
        rewrite plus_0_r. simpl.
        assert ((Nat.div2 n + S (Nat.div2 n))%nat = (S (Nat.div2 n + (Nat.div2 n)))%nat) by now simpl.
        rewrite H0.
        assert ((Nat.div2 n + Nat.div2 n)%nat = (2 * (Nat.div2 n))%nat).
        { simpl. now rewrite plus_0_r. }
        rewrite H2. apply modtf.
Qed.

Lemma modSft: forall n,
mod2 (S n) = false -> mod2 n = true.
Proof.  induction n; intuition.
        apply div2_even' in H. inversion H.
        rewrite plus_0_r in H1. rewrite H1. simpl.
        assert ((Nat.div2 n + S (Nat.div2 n))%nat = (S (Nat.div2 n + (Nat.div2 n)))%nat) by now simpl.
        rewrite H0. simpl.
        case_eq ((Nat.div2 n + Nat.div2 n)%nat ); intros.
        easy. now apply mod2Sn1 in H2.
Qed.

Lemma div2nSn: forall n,
mod2 n = false ->
(Nat.div2 n) = (Nat.div2 (S n)).
Proof. intros. apply div2_even' in H.
       now rewrite H, Nat.div2_succ_double, Nat.div2_double.
Qed.

Lemma div2nSn': forall n,
mod2 n = true ->
S (Nat.div2 n) = (Nat.div2 (S n)).
Proof. intros. apply div2_odd' in H.
       rewrite H. rewrite !Nat.div2_succ_double. simpl.
       apply f_equal. rewrite plus_0_r.
       assert ((Nat.div2 n + Nat.div2 n)%nat = (2 * Nat.div2 n)%nat ) by lia.
       now rewrite H0, Nat.div2_double.
Qed.


Lemma d2: forall a,
Nat.div2 (2 * a) = a.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. rewrite plus_0_r.
         assert ((xa + S xa)%nat = (S (xa + xa))%nat) by now simpl.
         rewrite H.
         assert ((xa + xa)%nat = (2 * xa)%nat).
         { lia. }
         rewrite H0. now rewrite IHa.
Qed.

Lemma m2: forall a,
mod2 (2 * a) = false.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. rewrite plus_0_r.
         assert ((xa + S xa)%nat = (S (xa + xa))%nat) by now simpl.
         rewrite H.
         assert ((xa + xa)%nat = (2 * xa)%nat).
         { lia. }
         rewrite H0. now rewrite IHa.
Qed.

Lemma nmult: forall n: nat,
(n + S n)%nat = S (2 * n).
Proof. induction n; intros. now simpl.
       simpl. rewrite plus_0_r. rewrite  IHn. lia.
Qed.

Lemma mod2_van_l: forall a b,
mod2 (a + a + b) = mod2 b.
Proof. intro a.
       induction a as [ | xa IHa]; intros.
       - now simpl.
       - simpl.
         assert ((xa + S xa + b)%nat = (S (xa + xa + b)%nat)) by lia.
         rewrite H. now rewrite IHa.
Qed.

Lemma mod2_van_r: forall a b,
mod2 (b + (a + a)) = mod2 b.
Proof. intros. now rewrite plus_comm, mod2_van_l. Qed.

Lemma mod2_3n: forall a b,
mod2 (a + a + S (a + a) + (b + b)) = true.
Proof. intros. rewrite plus_comm, !mod2_van_l.
       assert ((a + a)%nat = (2 * a)%nat). { lia. }
       now rewrite H, mod2_S_double.
Qed.

Lemma a2: forall a,
 ((a + a)%nat = (2*a)%nat).
Proof. intro a.
        induction a; intros.
        now simpl. simpl. rewrite plus_comm, plus_0_r. lia.
Qed.

Lemma div42: forall a b,
 Nat.div2 (4 * a + 2 * b) = (2 * a + b)%nat.
Proof. intro a.
       induction a; intros.
       - simpl. case_eq b; intros.
         + now simpl.
         + simpl. assert ((n + S (n + 0))%nat = (S (n + (n + 0)))%nat). { lia. }
           rewrite H0. apply f_equal.
           now rewrite plus_0_r, a2, d2.
       - simpl in *. rewrite !plus_0_r in *.
         assert ((a + S (a + S (a + S a)) + (b + b))%nat
                 = (S (a + (a + S (a + S a)) + (b + b)))%nat). { lia. }
         rewrite H. apply f_equal.
         assert ((a + (a + S (a + S a)) + (b + b))%nat = (S (a + (a + (a + S a)) + (b + b)))%nat).
         { lia. } rewrite H0. simpl.
         assert ((a + (a + (a + S a)) + (b + b))%nat = (S (a + (a + (a + a)) + (b + b)))%nat).
         { lia. } rewrite H1.
         assert ((a + S a + b)%nat = (S (a + a + b))%nat).  { lia. }
         rewrite H2. apply f_equal. specialize (@IHa b). rewrite plus_0_r in IHa.
         now rewrite IHa.
Qed.

Lemma div41: forall n,
Nat.div2 (4 * n + 2) = (2 * n + 1)%nat.
Proof. intro n.
       induction n; intros.
       - now simpl.
       - simpl. assert ((n + S (n + S (n + S (n + 0))) + 2)%nat 
                        = (S (n + (n + S (n + S (n + 0))) + 2))%nat).
         { lia. } rewrite H. apply f_equal. rewrite plus_0_r.
         assert ((n + S n)%nat = (2*n + 1)%nat). { lia. }
         assert ((n + (n + S (n + S n)) + 2)%nat = (4*n + 2 + 2)%nat).
         { lia. } rewrite H1.
         rewrite H0.
         assert ((2 + 2)%nat = (2*2)%nat). { lia. }
         assert ((4 * n + 2 + 2)%nat = ((4 * n) + (2 + 2))%nat). { lia. }
         rewrite H3, H2. rewrite div42. lia.
Qed.


Lemma div44: forall a b,
 Nat.div2 (4 * a + 4 * b) = (2 * a + 2* b)%nat.
Proof. intro a.
       induction a; intros.
       - simpl. case_eq b; intros.
         + now simpl.
         + simpl. assert ((n + S (n + S (n + S (n + 0))))%nat = (S (n + (n + S (n + S (n + 0)))))%nat). { lia. }
           rewrite H0. apply f_equal.
           rewrite plus_0_r.
           assert ((n + (n + S (n + S n)))%nat = (4*n + 2)%nat). { lia. }
           rewrite H1.
           assert ((n + S n)%nat = (2*n + 1)%nat). { lia. }
           rewrite H2. now rewrite div41.
       - simpl. rewrite !plus_0_r.
         assert ((a + S (a + S (a + S a)) + (b + (b + (b + b))))%nat
                 = (S (a + (a + S (a + S a)) + (b + (b + (b + b)))))%nat). { lia. }
         rewrite H. apply f_equal.
         assert ((a + (a + S (a + S a)) + (b + (b + (b + b))))%nat 
                 = (S (a + (a + (a + S a)) + (b + (b + (b + b)))))%nat). { lia. }
         rewrite H0. simpl.
         assert ((a + (a + (a + S a)) + (b + (b + (b + b))))%nat =
                 (S (a + (a + (a + a)) + (b + (b + (b + b)))))%nat). { lia. }
         rewrite H1.
         assert ((a + S a + (b + b))%nat = (S (a + a + (b + b)))%nat). { lia. }
         rewrite H2. apply f_equal. specialize (@IHa b). simpl in IHa. rewrite !plus_0_r in IHa.
         now rewrite IHa.
Qed.


Lemma evSS: forall n,
Even.even (S (S n)) <-> Even.even n.
Proof. induction n; intros. split; intros. apply Even.even_O. apply Even.even_S.
       easy. split. intros.
       inversion H. now inversion H1.
       intros. apply Even.even_S. now apply Even.odd_S.
Qed.

Lemma evnn: forall n,
Even.even (n + n).
Proof. intro n.
       induction n; intros.
       - simpl. apply Even.even_O.
       - simpl. apply Even.even_S.
         assert ((n + S n)%nat = (S (n + n))%nat ).
         { lia. } rewrite H. now apply Even.odd_S.
Qed.

Lemma ev42: forall a b,
Even.even (4 * a + 2 * b).
Proof. intro a.
       induction a; intros.
       - simpl. case_eq b; intros.
         + simpl. apply Even.even_O.
         + simpl. rewrite plus_0_r, <- plus_comm. simpl.
           apply evSS. apply evnn.
       - simpl. rewrite !plus_0_r.
         apply Even.even_S.
         assert ((a + S (a + S (a + S a)) + (b + b))%nat =
                 (S (S (S (a + (a + (a + a)) + (b + b)))))%nat). { lia. }
         rewrite H. apply Even.odd_S. apply Even.even_S. apply Even.odd_S.
         simpl in IHa. specialize (IHa b). now rewrite !plus_0_r in IHa.
Qed.

Lemma divS42: forall a b,
 Nat.div2 (S (4 * a + 2 * b)) = (2 * a + b)%nat.
Proof. intros. rewrite <- even_div2, div42. 
       reflexivity.
       apply ev42.
Qed.


Lemma div2_3': forall a b,
     (Nat.div2
        ((a + a) + S (a + a) + (b + b)))
        =
     (a + a + b)%nat.
Proof. intros.
       assert ( ((a + a) + S (a + a) + (b + b))%nat =  (S ((a + a) + (a + a) + (b + b))) ).
       { lia. } rewrite H, !a2.
       assert ((2 * (2 * a) + 2 * b)%nat = ((4 * a) + (2 * b))%nat). { lia. }
       rewrite H0.
       assert ((a + a)%nat = (2*a)%nat). { lia. }
       now rewrite divS42.
Qed.

Lemma moddiv2:  forall a b,
mod2
     (Nat.div2
        (listTonat a + listTonat a + S (listTonat a + listTonat a) +
         (listTonat b + listTonat b + S (listTonat b + listTonat b))))
= true.
Proof. intros.
       assert ((listTonat a + listTonat a + S (listTonat a + listTonat a) +
        (listTonat b + listTonat b + S (listTonat b + listTonat b)))%nat =
        (S (listTonat a + listTonat a + (listTonat a + listTonat a) +
        (listTonat b + listTonat b + S (listTonat b + listTonat b)))%nat)). { lia. }
       rewrite H. simpl.
       assert (    (listTonat a + listTonat a + (listTonat a + listTonat a) +
         (listTonat b + listTonat b + S (listTonat b + listTonat b)))%nat
          =    (S (listTonat a + listTonat a + (listTonat a + listTonat a) +
         (listTonat b + listTonat b + (listTonat b + listTonat b))))%nat). { lia. }
       rewrite H0. 
       assert ( (listTonat a + listTonat a + (listTonat a + listTonat a) +
         (listTonat b + listTonat b + (listTonat b + listTonat b)))%nat
         = (4 * listTonat a + 4 * listTonat b)%nat). { lia. }
       rewrite H1, div44. simpl. rewrite !plus_0_r.
       case_eq ((listTonat a + listTonat a + (listTonat b + listTonat b))%nat); intros.
       easy. now apply mod2Sn2 in H2.
Qed.

Lemma natdiv2: forall a b,
(Nat.div2
              (Nat.div2
                 (listTonat a + listTonat a + S (listTonat a + listTonat a) +
                  (listTonat b + listTonat b + S (listTonat b + listTonat b)))))
=
(listTonat a + listTonat b)%nat.
Proof. intros.
       assert ( (listTonat a + listTonat a + S (listTonat a + listTonat a) +
                (listTonat b + listTonat b + S (listTonat b + listTonat b)))%nat
                 =
                (S (S (listTonat a + listTonat a + (listTonat a + listTonat a) +
                (listTonat b + listTonat b + (listTonat b + listTonat b)))))). { lia. }
       rewrite H. simpl.
       assert (    (listTonat a + listTonat a + (listTonat a + listTonat a) +
                   (listTonat b + listTonat b + (listTonat b + listTonat b)))% nat = 
                   (4 * listTonat a + 4 * listTonat b)%nat). { lia. }
       rewrite H0, div44.
       case_eq ((2 * listTonat a + 2 * listTonat b)%nat); intros.
       assert ((2 * listTonat a + 2 * listTonat b)%nat = ( listTonat a +  listTonat a + ( listTonat b +  listTonat b))%nat).
       { lia. } rewrite H2 in H1. apply empty_total in H1. easy.
       assert ((2 * listTonat a + 2 * listTonat b)%nat = ( listTonat a +  listTonat a + ( listTonat b +  listTonat b))%nat).
       { lia. }  rewrite H2 in H1. apply helper_div2 in H1. easy.
Qed.

Lemma natmod2:  forall a b,
mod2
  (listTonat a + listTonat a + S (listTonat a + listTonat a) +
   (listTonat b + listTonat b + S (listTonat b + listTonat b)))
= false.
Proof. intros.
       assert ( (listTonat a + listTonat a + S (listTonat a + listTonat a) +
                (listTonat b + listTonat b + S (listTonat b + listTonat b)))%nat
                 =
                (S (S (listTonat a + listTonat a + (listTonat a + listTonat a) +
                (listTonat b + listTonat b + (listTonat b + listTonat b)))))). { lia. }
       rewrite H. simpl. rewrite !mod2_van_l.
       assert ((listTonat b + listTonat b)%nat = (2*listTonat b)%nat ). { lia. }
       now rewrite H0, m2.
Qed.

(** prove *)
Lemma natdiv2': forall a b,
(Nat.div2 (listTonat a + listTonat a + (listTonat b + listTonat b)))
=
(listTonat a + listTonat b)%nat.
Proof. intros. rewrite !a2.
       assert ((2 * listTonat a + 2 * listTonat b)%nat = (2 * (listTonat a + listTonat b))%nat). { lia. }
       now rewrite H, d2.
Qed.

Lemma natmod2':  forall a b,
mod2 (listTonat a + listTonat a + (listTonat b + listTonat b))
= false.
Proof. intros. rewrite !mod2_van_l.
       assert ((listTonat b + listTonat b)%nat = (2*listTonat b)%nat ). { lia. }
       now rewrite H, m2.
Qed.

Lemma natmod2'': forall a b,
 mod2 (listTonat a + listTonat a + S (listTonat b + listTonat b))
= true.
Proof. intros. rewrite !mod2_van_l.
       simpl. case_eq ((listTonat b + listTonat b)%nat); intros.
       easy. now apply mod2Sn1 in H.
Qed. 

Lemma even2t: forall a b,
Even.even (2 * (a + b)).
Proof. intro a.
       induction a; intros.
       - simpl. rewrite plus_0_r.
         now apply evnn.
       - simpl. apply Even.even_S. rewrite plus_0_r.
         assert ((a + b + S (a + b))%nat = (S (a + b + (a + b)))%nat). { lia. }
         rewrite H. apply Even.odd_S.
         assert ((a + b + (a + b))%nat = (2 * (a + b))%nat). { lia. }
         rewrite H0. apply IHa.
Qed.

Lemma natmod2''': forall a b,
(Nat.div2 (listTonat a + listTonat a + S (listTonat b + listTonat b)))
=
(listTonat a + listTonat b)%nat.
Proof. intros.
       assert ((listTonat a + listTonat a + S (listTonat b + listTonat b))%nat
              = (S (listTonat a + listTonat a + (listTonat b + listTonat b))%nat)). { lia. }
       rewrite H, <- even_div2. apply natdiv2'.
       rewrite !a2.
       assert ((2 * listTonat a + 2 * listTonat b)%nat = (2 * (listTonat a + listTonat b))%nat). { lia. }
       rewrite H0. apply even2t.
Qed.


Lemma nlf: forall a: list bool,
natTolist (Datatypes.length a) 0 = RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)%nat.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. now rewrite IHa.
Qed.

Lemma lnf: forall a: list bool,
listTonat a = 0%nat ->
a = RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)%nat.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq xa; intros.
         + subst. now contradict H.
         + rewrite IHa, RAWBITVECTOR_LIST.length_mk_list_false. 
           reflexivity.
           inversion H. rewrite H0 in *. rewrite H2. lia.
Qed.

Lemma mlf: forall n,
RAWBITVECTOR_LIST.add_list_ingr (RAWBITVECTOR_LIST.mk_list_false n)
  (RAWBITVECTOR_LIST.mk_list_false n) false =
  (RAWBITVECTOR_LIST.mk_list_false n).
Proof. intro n.
       induction n as [ | xn IHn]; intros.
       - now simpl.
       - simpl. now rewrite IHn.
Qed.

Lemma helper_conv_tf: forall a n,
RAWBITVECTOR_LIST.add_list_ingr a
  (natTolist n 0) true 
=
RAWBITVECTOR_LIST.add_list_ingr a
  (natTolist n 1) false.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - case_eq xa ;intros; try now simpl.
         case_eq n; intros. now simpl.
         now simpl.
         case_eq n; intros. now simpl.
         now simpl.
Qed.


Lemma helper_conv_tf2: forall a b,
(length a = length b) ->
RAWBITVECTOR_LIST.add_list_ingr a b true
=
RAWBITVECTOR_LIST.add_list_ingr a
  (RAWBITVECTOR_LIST.add_list_ingr b 
    (natTolist (Datatypes.length a) 1) false) false.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - case_eq b; intros.
         + subst. now contradict H.
         + case_eq xa; case_eq b0; intros.
           simpl. apply f_equal.
           specialize (helper_conv_tf l); intros.
           rewrite H0 in H. inversion H. rewrite H5, H3.
           now rewrite <- H5, IHa.
           simpl. apply f_equal. rewrite nlf, RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r.
           reflexivity. rewrite H0 in H. inversion H. lia.
           simpl. apply f_equal.
           specialize (helper_conv_tf l); intros.
           rewrite H0 in H. inversion H. rewrite H5, H3.
           now rewrite <- H5, IHa.
           simpl. apply f_equal. rewrite nlf, RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r.
           reflexivity. rewrite H0 in H. inversion H. lia.
Qed.


Lemma helper_conv_f2: forall a b,
(length a = length b) ->
RAWBITVECTOR_LIST.add_list_ingr (natTolist (Datatypes.length a) (listTonat a + listTonat b))
  (natTolist (Datatypes.length a) 1) false =
natTolist (Datatypes.length a) (S (listTonat a + listTonat b)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - case_eq b; intros. subst. now contradict H.
         case_eq xa; case_eq b0; intros.
         + simpl. rewrite !plus_0_r.
           assert ( (listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat
                   =
                    S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat) by now simpl.
           rewrite H3, natmod2', natdiv2'. simpl.
           case_eq ( (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
           apply f_equal.
           rewrite nlf,  RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r.
           apply empty_total in H4. now rewrite H4.
           rewrite len_n2l; lia.
           
           assert (mod2 n  = true).
           { now apply (@mod2Sn2 (listTonat xsa) (listTonat l)). } 
           rewrite H5. apply f_equal.
           rewrite nlf, RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r.
           apply helper_div2 in H4. now rewrite H4.
           rewrite len_n2l; lia.
         + simpl. rewrite !plus_0_r.
           case_eq ( (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
           simpl. apply f_equal.
           rewrite helper_conv_tf, nlf, RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_l.
           reflexivity. rewrite len_n2l; lia.
           assert (mod2 (S n)  = false).
           { now apply mod2n2 in H3. }
           rewrite H4. simpl.
           assert (mod2 n  = true).
           { now apply mod2Sn2 in H3. }
           rewrite H5. simpl.
           apply f_equal.
           case_eq n; intros. subst. now contradict H3.
           specialize (helper_conv_tf (natTolist (Datatypes.length xsa) (S (Nat.div2 (S n0))))
                      (Datatypes.length xsa)); intros.
           rewrite H0 in H. inversion H. rewrite H7.
           apply helper_div2 in H3. rewrite H6 in H3. rewrite <- H3.
           rewrite IHa, H3.
           assert (mod2 n0 = false).
           { rewrite H6 in H5. now apply modStf in H5. }
           apply div2nSn in H8. now rewrite H8. easy.
         + simpl. rewrite !plus_0_r, natmod2''. simpl.
           assert ((listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat
                   =
                  S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat) by now simpl.
           rewrite H3, natmod2'. apply f_equal.
           rewrite <- H3, natmod2''', natdiv2'.
           rewrite helper_conv_tf, IHa. reflexivity.
           now rewrite H0 in H; simpl in H; inversion H.
         + simpl. rewrite !plus_0_r, natmod2', natdiv2'. simpl.
           case_eq ((listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
           apply f_equal.
           apply empty_total in H3. now rewrite H3, nlf, mlf.
           assert (mod2 n  = true).
           { now apply mod2Sn2 in H3. }
           rewrite H4. simpl.
           apply f_equal.
           rewrite nlf, RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r.
           apply helper_div2 in H3. now rewrite H3.
           rewrite len_n2l; lia.
Qed.

Lemma helper_conv_f: forall a b,
(length a = length b) ->
RAWBITVECTOR_LIST.add_list_ingr a b false =
natTolist (length a) (listTonat a + listTonat b). 
Proof.
    intro a.
    induction a as [ | xa xsa IHa ]; intros.
    - now simpl.
    - case_eq b; intros. subst. now contradict H.
      simpl. rewrite !plus_0_r.
      case_eq xa; case_eq b0; intros; simpl.
      assert ((listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat =
              S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat)
      by now simpl. rewrite H3.
      rewrite natmod2'. apply f_equal.
      rewrite H0 in H. simpl in H. inversion H.
      specialize (IHa l H5). rewrite natdiv2'.
      rewrite helper_conv_tf2.
      rewrite <- (@RAWBITVECTOR_LIST.add_list_carry_assoc 
         xsa l (natTolist (Datatypes.length xsa) 1) false false false false).
      rewrite IHa. simpl.
      now rewrite helper_conv_f2. easy. now inversion H.
      specialize (IHa l). rewrite IHa.
      case_eq ((listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
      apply f_equal.
      assert ((listTonat xsa + listTonat l)%nat = 0)%nat.
      { now apply empty_total in H3. }
      now rewrite H4.
      assert (mod2 n = true).
      { now apply mod2Sn2 in H3. } 
      rewrite H4. apply f_equal.
 
      assert ((S (Nat.div2 n)) = (listTonat xsa + listTonat l)%nat).
      { now apply helper_div2 in H3. } 
      now rewrite H5. rewrite H0 in H. simpl in H. now inversion H.
      rewrite natmod2''. apply f_equal.
      rewrite H0 in H. simpl in H. inversion H.
      specialize (IHa l H4). 
      now rewrite natmod2'''.
      rewrite natmod2'. apply f_equal.
      rewrite H0 in H. simpl in H. inversion H.
      specialize (IHa l H4). 
      now rewrite natdiv2'.
Qed.

Lemma helper_conv_t: forall a b,
(length a = length b) ->
RAWBITVECTOR_LIST.add_list_ingr a b true =
natTolist (Datatypes.length a) (S (listTonat a + listTonat b)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - case_eq b; intros. subst. now contradict H.
         simpl. rewrite !plus_0_r.
      case_eq xa; case_eq b0; intros; simpl.
      rewrite natmod2''. apply f_equal.
      rewrite H0 in H. simpl in H. inversion H.
      specialize (IHa l H4). now rewrite natmod2'''.
      specialize (IHa l). rewrite IHa.
      case_eq ((listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
      apply f_equal.
      assert ((listTonat xsa + listTonat l)%nat = 0)%nat.
      { now apply empty_total in H3. }
      now rewrite H4.
      assert (mod2 (S n) = false).
      { now apply mod2n2 in H3. } 
      rewrite H4. apply f_equal.
 
      assert ((Nat.div2 (S n)) = (listTonat xsa + listTonat l)%nat).
      { apply helper_div2 in H3. rewrite H3. now apply div2nSn. }
      now rewrite H5. rewrite H0 in H. simpl in H. now inversion H.
      assert ((listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat
              =
              S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat)
      by now simpl. rewrite H3.
      rewrite natmod2'. apply f_equal.
      rewrite H0 in H. simpl in H. inversion H.
      specialize (IHa l H5). 
      now rewrite natdiv2'.
      case_eq ((listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
      apply f_equal.
      apply empty_total in H3. rewrite nlf.
      apply empty_total2 in H3. destruct H3 as (H3a, H3b).
      apply lnf in H3a. apply lnf in H3b.
      rewrite H3a, H3b. rewrite H0 in H. inversion H. 
      now rewrite H4, mlf, RAWBITVECTOR_LIST.length_mk_list_false.

      assert (mod2 n = true).
      { now apply mod2Sn2 in H3. }
      rewrite H4. apply f_equal.
      assert ( (S (Nat.div2 n)) = (listTonat xsa + listTonat l)%nat).
      { apply helper_div2 in H3. now rewrite H3. } 
      rewrite H5.
      rewrite H0 in H. simpl in H. inversion H.
      specialize (IHa l H7).
      now rewrite helper_conv_f.
Qed.

Lemma helper_conv_tt_tt: forall a b,
(length a = length b) ->
RAWBITVECTOR_LIST.add_list (true :: true :: a) (true :: true :: b) =
false :: true :: natTolist (length a) (S (listTonat a + listTonat b)).
Proof. 
    intro a. 
    induction a as [ | xa xsa IHa ]; intros.
    - simpl in *. now compute.
    - simpl. case_eq b ;intros. subst. now contradict H.
      simpl. case_eq xa;  case_eq b0; intros. simpl. rewrite !plus_0_r, natmod2''.
      specialize (IHa l). unfold RAWBITVECTOR_LIST.add_list in *. simpl in *.
      repeat apply f_equal. rewrite H0 in H. simpl in H. inversion H.
      specialize (IHa H4). inversion IHa. now rewrite natmod2'''.
      rewrite !plus_0_r. simpl.
       unfold RAWBITVECTOR_LIST.add_list in *. simpl in *.
       rewrite natmod2'. repeat apply f_equal.
       specialize (IHa l). rewrite H0 in H. simpl in H. inversion H.
      specialize (IHa H4). inversion IHa. now rewrite natdiv2'.
       rewrite !plus_0_r. simpl.
       assert ((listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat
              =
              S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat) by now simpl.
       rewrite H3. rewrite natmod2', natdiv2'.
       unfold RAWBITVECTOR_LIST.add_list in *. simpl in *.
       repeat apply f_equal. 
       rewrite H0 in H. simpl in H. inversion H.
       now specialize (IHa l H5); inversion IHa.
       rewrite !plus_0_r.
       case_eq ((listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
       unfold RAWBITVECTOR_LIST.add_list in *. simpl in *.
       repeat apply f_equal. rewrite H0 in H. simpl in H. inversion H.
       specialize (IHa l H5). inversion IHa.
       assert ((listTonat xsa + listTonat l)%nat = O).
       { now apply empty_total in H3. }
       rewrite H4 in H6.
       assert (xsa = RAWBITVECTOR_LIST.mk_list_false (length xsa)).
       { apply empty_total in H3. apply empty_total2 in H3.
         destruct H3 as (H3a, H3b). now apply lnf in H3a. }
       rewrite H7, H5.
       assert (l = RAWBITVECTOR_LIST.mk_list_false (length l)).
       { apply empty_total in H3. apply empty_total2 in H3.
         destruct H3 as (H3a, H3b). now apply lnf in H3b. }
       rewrite H8.
       rewrite !RAWBITVECTOR_LIST.length_mk_list_false. now rewrite nlf, mlf.
       unfold RAWBITVECTOR_LIST.add_list in *. simpl in *.
       assert (mod2 n = true).
       { now apply mod2Sn2 in H3. } 
       rewrite H4. repeat apply f_equal. rewrite H0 in H. simpl in H. inversion H.
       specialize (IHa l H6). inversion IHa.
       assert ((S (Nat.div2 n)) = (listTonat xsa + listTonat l)%nat).
       { apply helper_div2 in H3. now rewrite H3. }
       rewrite H5.
       now rewrite helper_conv_f.
Qed.


Lemma mod2_3: forall a b,
mod2 (listTonat a + listTonat a + S (listTonat a + listTonat a) + (listTonat b + listTonat b))
= true.
Proof. intros. now rewrite mod2_3n. Qed.

Lemma div2_3: forall a b,
     (Nat.div2
        (listTonat a + listTonat a + S (listTonat a + listTonat a) + (listTonat b + listTonat b)))
        =
     (listTonat a + listTonat a + listTonat b)%nat.
Proof. intros. now rewrite div2_3'. Qed.

Lemma mod2_4: forall a b,
mod2 (listTonat a + listTonat a + (listTonat a + listTonat a) + (listTonat b + listTonat b))
= false.
Proof. intros. rewrite mod2_van_l. 
       assert ( (listTonat b + listTonat b)%nat = (2* listTonat b)%nat). { lia. }
       now rewrite H, m2.
Qed. 

Lemma div2_4: forall a b,
     (Nat.div2
        (listTonat a + listTonat a + (listTonat a + listTonat a) + (listTonat b + listTonat b)))
        =
     (listTonat a + listTonat a + listTonat b)%nat.
Proof. intros. rewrite !a2.
       assert ((2 * (2 * listTonat a) + 2 * listTonat b)%nat = 
              ((4 * listTonat a) + 2 * listTonat b)%nat). { lia. }
       now rewrite H, div42.
Qed.

Lemma div2_5: forall a b,
(Nat.div2
                 (listTonat a + listTonat a + (listTonat a + listTonat a) +
                  (listTonat b + listTonat b + (listTonat b + listTonat b))))
=
(listTonat a + listTonat a + (listTonat b + listTonat b))%nat.
Proof. intros. rewrite !a2.
       assert ((2 * (2 * listTonat a) + 2 * (2 * listTonat b))%nat 
              = ( (4 * listTonat a) + (4 * listTonat b))%nat). { lia. }
       now rewrite H, div44.
Qed.

Lemma mod2_5: forall a b,
mod2
  (listTonat a + listTonat a + (listTonat a + listTonat a) +
   (listTonat b + listTonat b + (listTonat b + listTonat b)))
= false.
Proof. intros. rewrite !mod2_van_l.
       assert ((listTonat b + listTonat b)%nat = (2* listTonat b)%nat). { lia. }
       now rewrite H, m2.
Qed.


Lemma mod2_6: forall a b,
mod2
  (S
     (listTonat a + listTonat a + (listTonat a + listTonat a) +
      (listTonat b + listTonat b + S (listTonat b + listTonat b))))
= false.
Proof. intros.
       assert (  (S
        (listTonat a + listTonat a + (listTonat a + listTonat a) +
        (listTonat b + listTonat b + S (listTonat b + listTonat b))))%nat 
         =
        (S (S
        (listTonat a + listTonat a + (listTonat a + listTonat a) +
        (listTonat b + listTonat b + (listTonat b + listTonat b)))))%nat). { lia. }
       rewrite H. simpl.
       rewrite !mod2_van_l.
       assert ((listTonat b + listTonat b)%nat = (2* listTonat b)%nat). { lia. }
       now rewrite H0, m2.
Qed.

Lemma div2_6: forall a b,
     Nat.div2
       (S
          (listTonat a + listTonat a + (listTonat a + listTonat a) +
           (listTonat b + listTonat b + S (listTonat b + listTonat b))))
= (listTonat a + listTonat a + S ((listTonat b + listTonat b)))%nat.
Proof. intros.
       assert (       (S
          (listTonat a + listTonat a + (listTonat a + listTonat a) +
           (listTonat b + listTonat b + S (listTonat b + listTonat b))))%nat =
          
       (S (S
          (listTonat a + listTonat a + (listTonat a + listTonat a) +
           (listTonat b + listTonat b + (listTonat b + listTonat b)))))%nat). { lia. }
       rewrite H. simpl.
       assert ((listTonat a + listTonat a + S (listTonat b + listTonat b))%nat =
               (S (listTonat a + listTonat a + (listTonat b + listTonat b)))%nat). { lia. }
       rewrite H0. apply f_equal. apply div2_5.
Qed.


Lemma mod2_7: forall a,
mod2 ((S (listTonat a + listTonat a)))
= true.
Proof. intros.
       assert ((S (listTonat a + listTonat a))%nat = ((listTonat a + listTonat a) + 1)%nat).
       { lia. } rewrite H, mod2_van_l. now compute.
Qed. 

Lemma div2_7: forall a,
(Nat.div2 (S (listTonat a + listTonat a)))
= listTonat a%nat.
Proof. intros. rewrite <- even_div2.
       assert ( (listTonat a + listTonat a)%nat = (2* listTonat a)%nat). { lia. }
       now rewrite H, d2.
       apply evnn.
Qed.

Lemma mod2_8: forall a,
mod2 (((listTonat a + listTonat a)))
= false.
Proof. intros. 
       assert ( (listTonat a + listTonat a)%nat = (2* listTonat a)%nat). { lia. }
       now rewrite H, m2.
Qed.

Lemma div2_8: forall a,
(Nat.div2 ((listTonat a + listTonat a)))
= listTonat a%nat.
Proof. intros. 
       assert ( (listTonat a + listTonat a)%nat = (2* listTonat a)%nat). { lia. }
       now rewrite H, d2.
Qed.


Lemma helper_conv_tt: forall a b,
(length a = length b) ->
RAWBITVECTOR_LIST.add_list (true :: a) (true :: b) =
mod2 (listTonat a + listTonat a + (listTonat b + listTonat b))
:: natTolist (Datatypes.length a)
     (S (Nat.div2 (listTonat a + listTonat a + (listTonat b + listTonat b)))).
Proof. 
    intro a.
    induction a  as [ | xa xsa IHa ]; intros.
    - simpl in *. symmetry in H. rewrite empty_list_length in H; subst. now simpl.
    - case_eq b; intros.
      + subst. now contradict H.
      + case_eq xa; case_eq b0; intros.
        rewrite helper_conv_tt_tt. simpl.
        assert (  (listTonat xsa + (listTonat xsa + 0) + S (listTonat xsa + (listTonat xsa + 0)) +
                  S (listTonat l + (listTonat l + 0) + S (listTonat l + (listTonat l + 0))))%nat
               = 
                 S (listTonat xsa + (listTonat xsa + 0) + S (listTonat xsa + (listTonat xsa + 0)) +
                  (listTonat l + (listTonat l + 0) + S (listTonat l + (listTonat l + 0))))%nat) 
        by now simpl.
        rewrite H3. now rewrite !plus_0_r, moddiv2, natdiv2, natmod2 in *.
        rewrite H0 in H. simpl in H. now inversion H.
       
        unfold RAWBITVECTOR_LIST.add_list in *. simpl in *.
        rewrite !plus_0_r.
        assert (  (listTonat xsa + listTonat xsa + S (listTonat xsa + listTonat xsa) +
                  (listTonat l + listTonat l + (listTonat l + listTonat l)))%nat
                  =
                  (S (listTonat xsa + listTonat xsa + (listTonat xsa + listTonat xsa) +
                  (listTonat l + listTonat l + (listTonat l + listTonat l))))%nat).
        { lia. }
        rewrite H3, div2_5, natdiv2', natmod2', mod2_5, IHa.
        now rewrite natmod2', natdiv2'.
        rewrite H0 in H. simpl in H. now inversion H.

        unfold RAWBITVECTOR_LIST.add_list in *. simpl in *.
        rewrite !plus_0_r.
        assert (  (listTonat xsa + listTonat xsa + (listTonat xsa + listTonat xsa) +
                  S (listTonat l + listTonat l + S (listTonat l + listTonat l)))%nat
                  =
                  (S (listTonat xsa + listTonat xsa + (listTonat xsa + listTonat xsa) +
                  (listTonat l + listTonat l + S (listTonat l + listTonat l))))%nat).
        { lia. }
        rewrite H3, mod2_6, div2_6.
        assert ((listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat
                =
                (S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat)) by now simpl.
        rewrite H4, natdiv2', natmod2', IHa.
        now rewrite natmod2', natdiv2'.
        rewrite H0 in H. simpl in H. now inversion H.

        unfold RAWBITVECTOR_LIST.add_list in *. simpl in *.
        rewrite !plus_0_r.
        rewrite mod2_5, div2_5.
        case_eq ((listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
        apply empty_total in H3. apply empty_total2 in H3.
        destruct H3 as (H3a, H3b). apply lnf in H3a. apply lnf in H3b.
        rewrite H3a, H3b.
        rewrite H0 in H. simpl in H. inversion H. rewrite H4.
        now rewrite mlf, RAWBITVECTOR_LIST.length_mk_list_false, nlf.
        pose proof H3 as H3p.
        apply mod2Sn2 in H3. rewrite H3. apply helper_div2 in H3p.
        rewrite helper_conv_f, H3p. reflexivity.
        rewrite H0 in H. simpl in H. now inversion H.
Qed.


Lemma empty_total3: forall a b: nat,
(a + a + (a + a) + (b + b))%nat = 0%nat
->
(a + a + b)%nat = 0%nat.
Proof. intro a.
       induction a as [ | xa IHa ]; intros; lia.
Qed.

Lemma helper_div2_3: forall a b n,
 (a + a + (a + a) + (b + b))%nat = S n
-> 
(a + a + b)%nat = (S (Nat.div2 n)).
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - simpl in *. now apply helper_div.
       - simpl in *. inversion H.
         case_eq b; intros. subst. simpl in *.
         assert ( (S (xa + S xa + 0)) = ( (xa + xa + 2))%nat).
         { rewrite plus_0_r. lia. }
         rewrite H0. rewrite plus_0_r. apply IHa. simpl. lia.
         assert ((S (xa + S xa + S n0))%nat =  (xa + xa + (S (S (S n0))))%nat ).
         { simpl. lia. }
         rewrite H2. apply IHa. lia.
Qed.



Lemma mod2Sn3: forall (a b n: nat),
(a + a + (a + a) + (b + b))%nat = S n ->
mod2 n = true.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - case_eq b; intros.
         + simpl in *. subst.  simpl in *. now contradict H.
         + simpl in *. subst. simpl in *. inversion H.
           assert ((n0 + S n0)%nat = (S (n0 + n0))%nat) by now simpl.
           now rewrite mod2Sn.
       - case_eq n; intros. subst. contradict H. lia.
         rewrite <- H0. 
         apply (IHa (S ( S b))). rewrite <- H. lia.
Qed.


Lemma ntl_t: forall (a b: list bool) n,
true :: natTolist n (listTonat a + listTonat b) =
natTolist (S n) (S (listTonat a + listTonat a + (listTonat b + listTonat b))).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl.
         case_eq ((listTonat b + listTonat b)%nat); intros.
         apply empty_total2 in H. destruct H as (Ha, Hb).
         now rewrite Ha.
         pose proof H as Hp.
         apply helper_div in H. rewrite H.
         apply mod2Sn1 in Hp. rewrite Hp; auto.
       - case_eq xa; intros. simpl. rewrite !plus_0_r.
         rewrite mod2_3. apply f_equal. now rewrite div2_3.
         simpl. rewrite !plus_0_r.
         case_eq (  (listTonat xsa + listTonat xsa + (listTonat xsa + listTonat xsa) + (listTonat b + listTonat b))%nat); intros.
         apply empty_total3 in H0. now rewrite H0.
         pose proof H0 as H0p.
         apply helper_div2_3 in H0. rewrite H0.
         apply mod2Sn3 in H0p. now rewrite H0p.
Qed.

Lemma ntl_f: forall (a b: list bool) n,
false :: natTolist n (listTonat a + listTonat b) =
natTolist (S n) (listTonat a + listTonat a + (listTonat b + listTonat b)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl.
         case_eq ((listTonat b + listTonat b)%nat); intros.
         apply empty_total2 in H. destruct H as (Ha, Hb).
         now rewrite Ha.
         pose proof H as Hp.
         apply helper_div in H. rewrite H.
         apply mod2Sn1' in Hp. rewrite Hp.
         apply modSft in Hp.
         apply div2nSn' in Hp. now rewrite Hp.
       - case_eq xa; intros. simpl. rewrite !plus_0_r.
         assert ((listTonat xsa + listTonat xsa + S (listTonat xsa + listTonat xsa) + (listTonat b + listTonat b))%nat
                 =
               (S (listTonat xsa + listTonat xsa + (listTonat xsa + listTonat xsa) + (listTonat b + listTonat b)))%nat).
         { lia. } rewrite H0.
         rewrite mod2_4. apply f_equal. now rewrite div2_4.
         simpl. rewrite !plus_0_r.
         now rewrite mod2_4, div2_4.
Qed.

Lemma toListsame: forall (a b: list bool) n,
(length a = n) -> (length b = n) ->
RAWBITVECTOR_LIST.add_list a b = natTolist n ((listTonat a) + (listTonat b)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl in *. rewrite <- H in *. rewrite empty_list_length in H0; subst.
         simpl. now rewrite RAWBITVECTOR_LIST.add_list_empty_r.
       - case_eq b; intros. subst. now contradict H0.
         simpl.
         case_eq xa; case_eq b0; intros; simpl.
         assert ( (listTonat xsa + 0)%nat =  (listTonat xsa)).
         { now rewrite plus_n_O. }
          assert ( (listTonat l + 0)%nat =  (listTonat l)).
         { now rewrite plus_n_O. }
         rewrite H4, H5.
         case_eq n; intros. subst. now contradict H6.
         simpl.
         case_eq ( (listTonat xsa%nat + listTonat xsa + 
         S (listTonat l + listTonat l))%nat); intros.
         simpl. contradict H7. lia.
         rewrite helper_conv_tt.
         assert ( (listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat
                  =
                   (S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat)) by now simpl.
         rewrite H8 in H7. inversion H7. rewrite H10.
         rewrite H6 in H. inversion H. now rewrite H11.
         subst. now inversion H0.
         rewrite RAWBITVECTOR_LIST.add_list_carry_tf_t.
         rewrite (IHa l (n-1)%nat), !plus_0_r.
         rewrite ntl_t.
         assert ((S (n - 1)) = n) .
         { case_eq n; intros. subst. now contradict H4. lia. }
         now rewrite H4.
         simpl in H. rewrite <- H. simpl. lia.
         rewrite H1 in H0. 
         simpl in H0. rewrite <- H0. simpl. lia.

         rewrite RAWBITVECTOR_LIST.add_list_carry_ft_t.
         rewrite (IHa l (n-1)%nat), !plus_0_r.
         rewrite ntl_t.
         assert ((S (n - 1)) = n) .
         { case_eq n; intros. subst. now contradict H4. lia. }
         rewrite H4.
         assert ( (listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat
                  =
                (S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l)))) by now simpl.
         now rewrite H5.
         simpl in H. rewrite <- H. simpl. lia.
         rewrite H1 in H0. 
         simpl in H0. rewrite <- H0. simpl. lia.

         rewrite RAWBITVECTOR_LIST.add_list_carry_ff_f.
         rewrite (IHa l (n-1)%nat), !plus_0_r.
         rewrite ntl_f.
         assert ((S (n - 1)) = n) .
         { case_eq n; intros. subst. now contradict H4. lia. }
         now rewrite H4.
         simpl in H. rewrite <- H. simpl. lia.
         rewrite H1 in H0. 
         simpl in H0. rewrite <- H0. simpl. lia.
Qed.

(** prove *)
Lemma _equiv_ltnatN: forall a,
natTolist (length a) (listTonat a) = NToList (listToN a) (length a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq xa; intros.
         rewrite !plus_0_r, div2_7, mod2_7, IHa.
         case_eq (listToN xsa); intros; now simpl.
         rewrite !plus_0_r, div2_8, mod2_8, IHa.
         case_eq (listToN xsa); intros; now simpl.
Qed.

Lemma ltnN: forall a,
(listTonat a) = nat_of_N (listToN a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. rewrite plus_0_r. case_eq xa; intros. rewrite IHa. 
         case_eq (listToN xsa); intros; lia.
         rewrite IHa. 
         case_eq (listToN xsa); intros; lia.
Qed.

Lemma ltNn: forall a,
(listToN a) = N.of_nat (listTonat a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. rewrite plus_0_r. case_eq xa; intros.
         rewrite IHa. 
         case_eq (N.of_nat (listTonat xsa)); intros; lia.
         rewrite IHa. 
         case_eq (N.of_nat (listTonat xsa)); intros; lia.
Qed.

Lemma nlf2: forall n,
natTolist n 0 = RAWBITVECTOR_LIST.mk_list_false n%nat.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. now rewrite IHn.
Qed.

Lemma ptlz: forall p,
posToList 0%nat p = [].
Proof. intro p.
       induction p; intros; now simpl.
Qed.

Lemma div2np: forall p,
(Nat.div2 (Pos.to_nat p~0))%nat = Pos.to_nat p.
Proof. intros. rewrite <- Pos.add_diag, Pos2Nat.inj_add.
       assert ((Pos.to_nat p + Pos.to_nat p)%nat = (2* (Pos.to_nat p))%nat).
       { lia. } now rewrite H, d2.
Qed.

Lemma mod2np: forall p,
mod2 (Pos.to_nat p~0) = false.
Proof. intros. rewrite <- Pos.add_diag, Pos2Nat.inj_add.
       assert ((Pos.to_nat p + Pos.to_nat p)%nat = (2* (Pos.to_nat p))%nat).
       { lia. } now rewrite H, m2.
Qed.

Lemma positerF: forall p,
Pos.iter_op Init.Nat.add p 2%nat = 0%nat -> False.
Proof. intro p.
       induction p; intros. 
       - simpl in *. apply IHp. rewrite <- H. lia.
       - apply IHp. rewrite <- Pos.add_diag in H. rewrite ZL6 in H.
         apply empty_total2 in H. rewrite Pmult_nat_mult.
         assert ((Pos.to_nat p * 2)%nat = Pos.to_nat (p + p)).
         { lia. } rewrite H0. easy.
       - simpl in H. now contradict H.
Qed.

Lemma positerF4: forall p,
Pos.iter_op Init.Nat.add p 4%nat = 0%nat -> False.
Proof. intro p.
       induction p; intros. 
       - simpl in *. apply IHp. rewrite <- H. lia.
       - apply IHp. rewrite <- Pos.add_diag in H. 
         rewrite Pmult_nat_mult in *. lia.
       - simpl in H. now contradict H.
Qed.

Lemma npz: forall p,
((Pos.to_nat p)%nat * 4)%nat = 0%nat -> False.
Proof. intros. 
       rewrite <- Pmult_nat_mult in H.
       apply positerF4 in H. easy.
Qed.


Lemma positerS: forall p n,
Pos.iter_op Init.Nat.add p 2%nat = S n ->
Pos.to_nat p = (S (Nat.div2 n)).
Proof. intros. rewrite ZL6 in H. now apply helper_div in H. Qed. 

Lemma mod2positerS: forall p n,
Pos.iter_op Init.Nat.add p 2%nat = S n ->
mod2 n = true.
Proof. intros. rewrite ZL6 in H. now apply mod2Sn1 in H. Qed. 

Lemma nl2pl: forall n p,
natTolist n (Pos.to_nat p) =
posToList n p.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - simpl. now rewrite ptlz.
       - simpl. case_eq p; intros.
         + simpl. case_eq (Pos.iter_op Init.Nat.add p0 2%nat ); intros.
           ++ rewrite <- IHn. apply positerF in H0. now contradict H0.
           ++ pose proof H0 as H0p.
              apply positerS in H0.
              apply (f_equal (Pos.of_nat)) in H0. rewrite Pos2Nat.id in H0.
              rewrite H0. apply mod2positerS in H0p. rewrite H0p.
              apply f_equal. now rewrite <- IHn, Nat2Pos.id.
         + simpl. rewrite <- IHn. now rewrite div2np, mod2np.
         + simpl. now rewrite nlf2.
Qed.

Lemma equiv_ltnatN: forall a b,
(length a = length b) ->
natTolist (length a) (listTonat a + listTonat b) = NToList (listToN a + listToN b) (length a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl. simpl in H. symmetry in H. rewrite empty_list_length in H. rewrite H.
         now simpl.
       - case_eq b; intros.
         + subst. now contradict H.
         + case_eq xa; case_eq b0; intros. simpl.
           rewrite !plus_0_r.
           assert ((listTonat xsa + listTonat xsa + S (listTonat l + listTonat l))%nat
                   =
                   (S (listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat) ) by now simpl.
           rewrite H3, natdiv2', natmod2'.
           case_eq ( listToN xsa ); case_eq (listToN l); intros.
           simpl. case_eq (Datatypes.length xsa); intros. now simpl.
           simpl. rewrite ltNn in H4, H5.
           apply (f_equal (N.to_nat)) in H4.
           apply (f_equal (N.to_nat)) in H5.
           rewrite Nat2N.id in H4, H5. rewrite H4, H5. simpl.
           now rewrite nlf2.
           simpl. rewrite ltNn in H4, H5.
           apply (f_equal (N.to_nat)) in H4.
           apply (f_equal (N.to_nat)) in H5.
           rewrite Nat2N.id in H4, H5. rewrite H4, H5. simpl. 
           specialize (nl2pl (Datatypes.length xsa) (Pos.succ p)). intros.
           rewrite <- H6.
           assert ((S (Pos.to_nat p)) = (Pos.to_nat (Pos.succ p))). { lia. }
           now rewrite H7.
           simpl. rewrite ltNn in H4, H5.
           apply (f_equal (N.to_nat)) in H4.
           apply (f_equal (N.to_nat)) in H5.
           rewrite Nat2N.id in H4, H5. rewrite H4, H5. simpl.
           assert ((Pos.to_nat p + 0)%nat = (Pos.to_nat p)%nat) by lia.
           rewrite H6.
           specialize (nl2pl (Datatypes.length xsa) (Pos.succ p)). intros.
           rewrite <- H7.
           assert ((S (Pos.to_nat p)) = (Pos.to_nat (Pos.succ p))). { lia. }
           now rewrite H8.
           simpl.
           simpl. rewrite ltNn in H4, H5.
           apply (f_equal (N.to_nat)) in H4.
           apply (f_equal (N.to_nat)) in H5.
           rewrite Nat2N.id in H4, H5. rewrite H4, H5. simpl.
           specialize (nl2pl (Datatypes.length xsa)  (Pos.add_carry p0 p)). intros.
           rewrite <- H6.


           assert ((S (Pos.to_nat p0 + Pos.to_nat p)) = (Pos.to_nat (Pos.add_carry p0 p))).
           { rewrite Pos.add_carry_spec. lia. }
           now rewrite H7. 

           simpl. rewrite !plus_0_r.
           case_eq ((listTonat xsa + listTonat xsa + (listTonat l + listTonat l))%nat); intros.
           case_eq ( listToN xsa ); case_eq (listToN l); intros.
           simpl. now rewrite nlf2.
           simpl. apply empty_total in H3. apply empty_total2 in H3.
           destruct H3 as (H3a, H3b). rewrite ltnN in H3b.
           apply (f_equal (N.of_nat)) in H3b. rewrite N2Nat.id in H3b.
           rewrite H3b in H4. now contradict H4.
           simpl. apply empty_total in H3. apply empty_total2 in H3.
           destruct H3 as (H3a, H3b). rewrite ltnN in H3a.
           apply (f_equal (N.of_nat)) in H3a. rewrite N2Nat.id in H3a.
           rewrite H3a in H5. now contradict H5.
           simpl. apply empty_total in H3. apply empty_total2 in H3.
           destruct H3 as (H3a, H3b). rewrite ltnN in H3a.
           apply (f_equal (N.of_nat)) in H3a. rewrite N2Nat.id in H3a.
           rewrite H3a in H5. now contradict H5.

           case_eq ( listToN xsa ); case_eq (listToN l); intros.
           simpl. rewrite ltNn in H4, H5.
           apply (f_equal (N.to_nat)) in H4.
           apply (f_equal (N.to_nat)) in H5.
           rewrite Nat2N.id in H4, H5. rewrite H4, H5 in H3. simpl in H3.
           now contradict H3.

           simpl. pose proof H3 as H3p.
           apply mod2Sn2 in H3. rewrite H3. apply helper_div2 in H3p.
           rewrite ltNn in H4, H5.
           apply (f_equal (N.to_nat)) in H4.
           apply (f_equal (N.to_nat)) in H5.
           rewrite Nat2N.id in H4, H5. rewrite H4, H5 in H3p. simpl in H3p.
           now rewrite <- H3p, <- nl2pl.
           
           simpl. pose proof H3 as H3p.
           apply mod2Sn2 in H3. rewrite H3. apply helper_div2 in H3p.
           rewrite ltNn in H4, H5.
           apply (f_equal (N.to_nat)) in H4.
           apply (f_equal (N.to_nat)) in H5.
           rewrite Nat2N.id in H4, H5. rewrite H4, H5 in H3p. simpl in H3p.
           rewrite <- H3p, <- nl2pl.
           assert ((Pos.to_nat p + 0)%nat = (Pos.to_nat p)%nat) by lia.
           now rewrite H6.
            
           simpl.  pose proof H3 as H3p.
           apply mod2Sn2 in H3. rewrite H3. apply helper_div2 in H3p.
           rewrite ltNn in H4, H5.
           apply (f_equal (N.to_nat)) in H4.
           apply (f_equal (N.to_nat)) in H5.
           rewrite Nat2N.id in H4, H5. rewrite H4, H5 in H3p. simpl in H3p.
           rewrite <- H3p, <- nl2pl.
           assert ((Pos.to_nat p0 + Pos.to_nat p)%nat = (Pos.to_nat (p0 + p)) ).
           { lia. } now rewrite H6.

           simpl. rewrite !plus_0_r, natmod2''', natmod2''.
           rewrite IHa.
           case_eq ( listToN xsa); case_eq ( listToN l); intros; now simpl.
           rewrite H0 in H. simpl in H. now inversion H.
           simpl. rewrite !plus_0_r, natmod2', natdiv2'.
           rewrite IHa.
           case_eq ( listToN xsa); case_eq ( listToN l); now simpl.
           rewrite H0 in H. simpl in H. now inversion H.
Qed.


Lemma _toWordsame: forall n (a b: list bool),
(length a = n) -> (length b = n) ->
RAWBITVECTOR_LIST.add_list a b = NToList (Nplus (listToN a) (listToN b)) n.
Proof. intros. specialize (@toListsame a b n H H0); intros. 
       rewrite H1, <- H. rewrite equiv_ltnatN. reflexivity.
       subst. easy.
Qed.

Lemma toWordsame2: forall n (a b: list bool),
(length a = n) -> (length b = n) ->
ListToword (RAWBITVECTOR_LIST.add_list a b) n = ListToword (NToList (Nplus (listToN a) (listToN b)) n) n.
Proof. intros. rewrite (@_toWordsame n a b); easy. Qed.

Lemma asd: forall a,
(wordToN (ListToword a (length a)))
=
listToN a.
Proof. intro a.
       induction a as [ | xa xsa IHa]; intros.
       - now simpl.
       - simpl. case_eq xa; intros.
         simpl. specialize (helper_strong xsa true); intros.
         rewrite H0. simpl. rewrite IHa.
         case_eq (listToN xsa ); intros; easy.
         specialize (helper_strong xsa false); intros.
         rewrite H0. simpl. rewrite IHa.
         case_eq (listToN xsa ); intros; easy.
Qed.

Lemma wlf: forall n,
wzero' n = ListToword (RAWBITVECTOR_LIST.mk_list_false n) n.
Proof. intro n.
       induction n as [ | xn IHn]; intros.
       - simpl. now compute.
       - simpl. specialize (helper_strong (RAWBITVECTOR_LIST.mk_list_false xn) false); intros.
         rewrite RAWBITVECTOR_LIST.length_mk_list_false in H.
         rewrite H. now rewrite <- IHn.
Qed.

Lemma length_pos: forall p n,
(Datatypes.length (posToList n p)) = n.
Proof. intro p.
       induction p; intros.
       - simpl. case_eq n; intros.
         + easy.
         + simpl. now rewrite IHp. 
       - simpl. case_eq n; intros.
         + easy.
         + simpl. now rewrite IHp.
       - simpl. case_eq n; intros.
         + easy.
         + simpl. now rewrite RAWBITVECTOR_LIST.length_mk_list_false.
Qed.

Lemma wzmlf: forall n,
(wzero' n) = (ListToword (RAWBITVECTOR_LIST.mk_list_false n) n).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - simpl. now compute.
       - simpl. rewrite IHn.
         specialize (helper_strong ( RAWBITVECTOR_LIST.mk_list_false xn) false); intros.
         rewrite RAWBITVECTOR_LIST.length_mk_list_false in H. now rewrite H.
Qed.

Lemma wlp: forall n a,
posToWord n a = ListToword (posToList n a) n.
Proof. intro n.
       induction n; intros.
       - simpl. case_eq a; intros. simpl. now compute.
         simpl. now compute. simpl. now compute.
       - case_eq a; intros.
         + simpl. specialize (helper_strong (posToList n p) true); intros.
           assert ((Datatypes.length (posToList n p)) = n).
           { now rewrite length_pos. } 
           rewrite H1 in H0. rewrite H0. now rewrite <- IHn.
         + simpl. specialize (helper_strong (posToList n p) false); intros.
           assert ((Datatypes.length (posToList n p)) = n).
           { now rewrite length_pos. } 
           rewrite H1 in H0. rewrite H0. now rewrite <- IHn.
         + simpl. specialize (helper_strong (RAWBITVECTOR_LIST.mk_list_false n) true); intros.
           rewrite RAWBITVECTOR_LIST.length_mk_list_false in H0.
           now rewrite H0, wzmlf.
Qed.

Lemma word_same: forall a n,
NToWord n a = ListToword (NToList a n) n.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl. now rewrite wlf.
       - simpl. now rewrite wlp.
Qed. 

Lemma toWordsame3: forall (a b: list bool) n,
(length a = n) -> (length b = n) ->
Word.wplus (ListToword a n) (ListToword b n)  = ListToword (RAWBITVECTOR_LIST.add_list a b) n.
Proof. intros. unfold Word.wplus, wordBin.
       rewrite toWordsame2. 
       rewrite <- !asd, word_same. now rewrite H, H0.
       easy. easy.
Qed.


Lemma ltw_same: forall a b n,
a = b ->
ListToword a n =
ListToword b n. 
Proof. intros. now rewrite H. Qed.

Lemma check_add_wplus:forall bs1 bs2 bsres, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_add bs1 bs2 bsres (Clit Lit._false) ->
    (Word.wplus (ListToword (map (Lit.interp rho) bs1) n) (ListToword (map (Lit.interp rho) bs2) n))
    =
    (ListToword (map (Lit.interp rho) bsres) n).
Proof. intros. rewrite toWordsame3.
       rewrite <- H in H0. rewrite <- H. apply ltw_same.
       specialize (@check_add_addlist bs1 bs2 bsres (N.of_nat n)); intros.
       apply H2. now rewrite H.
       now rewrite H0, H.
       apply check_add_bvadd_length in H1.
       destruct H1 as (H1a, H1b). rewrite H in H1a. now rewrite <- H1a.
       easy.
       rewrite map_length; easy. rewrite map_length; easy.
Qed.

Lemma valid_check_bbAdd s pos1 pos2 lres : C.valid rho (check_bbAdd s pos1 pos2 lres).
Proof.
      unfold check_bbAdd.
      case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | |[ A B | A| | | | ]|N|N|N| | | | ] a1' a2' Heq9;
        try (intros; now apply C.interp_true).

      (* BVadd *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1'));
            simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (
                 check_add bs1 bs2 bsres (Clit Lit._false) &&
                 ((Datatypes.length bs1) =? n)%nat
        ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply Word.weqb_true_iff.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H4 in H0; try (now contradict H0).
        rename H4 into Hv.

        generalize (Hs s pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs s pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2
        ;rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_word a = 
                interp_word t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_word. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval.

        assert (H100: ((Datatypes.length (map (Lit.interp rho) bsres))) = n).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite Nat.eqb_eq in Heq11r.
          rewrite Heq11a in Heq11r.
          now rewrite map_length.
        }

        rewrite H100.

        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }
        rewrite H5 in HSp1.
        unfold interp_word in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_word in HSp1. 

        revert HSp1.

        assert (H101: (Datatypes.length (map (Lit.interp rho) bs1)) = n).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite Nat.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' = 
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }
        rewrite H6 in HSp2.
        unfold interp_word in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_word in HSp2. 

        revert HSp2.

        assert (H102:(Datatypes.length (map (Lit.interp rho) bs2)) = n).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite Heq11a, <- Heq11b in Heq11r.
          rewrite Nat.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        rewrite H102.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp2.

        pose proof Heq11.
        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11 & Heq11r).
        rewrite Nat.eqb_eq in Heq11r.
 
        specialize (@check_add_wplus bs1 bs2 bsres); intros.
        unfold wplus in *.
        assert (length bsres = n). 
        { apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b). now rewrite Heq11r in Heq11a. }
        rewrite H9 in H8.
        rewrite H8. reflexivity.

        now rewrite map_length in H100. now rewrite map_length in H102.
        exact Heq11. 

        (** symmetic case **)


        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_word a = 
                interp_word t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_word. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval.

        assert (H100: ((Datatypes.length (map (Lit.interp rho) bsres))) = n).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite Nat.eqb_eq in Heq11r.
          rewrite Heq11a in Heq11r.
          now rewrite map_length.
        }

        rewrite H100.

        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_word in HSp2.
        rewrite Htia1 in HSp2.
        unfold interp_word in HSp2.

        revert HSp2.

        assert (H102:(Datatypes.length (map (Lit.interp rho) bs2)) = n).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite Heq11a, <- Heq11b in Heq11r.
          rewrite Nat.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        rewrite H102.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp2.


        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' = 
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H6 in HSp1.
        unfold interp_word in HSp1.
        rewrite Htia2 in HSp1.
        unfold interp_word in HSp1.

        revert HSp1.

        assert (H101: (Datatypes.length (map (Lit.interp rho) bs1)) = n).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite Nat.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp1.

        pose proof Heq11.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11 & Heq11r).
        rewrite Nat.eqb_eq in Heq11r.

        rewrite wplus_comm.

        pose proof Heq11.

        specialize (@check_add_wplus bs1 bs2 bsres); intros.
        unfold wplus in *.
        assert (length bsres = n). 
        { apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b). now rewrite Heq11r in Heq11a. }
        rewrite H10 in H9.
        rewrite H9. reflexivity.

        now rewrite map_length in H100. now rewrite map_length in H102.
        exact Heq11.
Qed.

(** END OF BV ADDITION CHECKER WORDS*)


(** BV EQUALITY CHECKER WORDS*)

Lemma bool_eqb_comm: forall ibs1 ibs2,  Bool.eqb ibs1 ibs2 = Bool.eqb ibs2 ibs1.
Proof. intros. case_eq ibs1. intros. case_eq ibs2. intros. easy. intros. easy. intros. easy. Qed.

Lemma check_symopp_eq': forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres n,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_eq (Typ.TWord n)) = true ->
      Bool.eqb (Lit.interp rho ibs1) (Lit.interp rho ibs2) = Lit.interp rho ibsres.
Proof. intros.
       simpl in H.
       case_eq (Lit.is_pos ibsres). intros. rewrite H0 in H.
       case_eq (t_form .[ Lit.blit ibsres]); intros; rewrite H1 in H; try (now contradict H).
       specialize (@rho_interp ( Lit.blit ibsres)).
       rewrite H1 in rho_interp. simpl in rho_interp.
       case_eq ((i == ibs1) && (i0 == ibs2) || (i == ibs2) && (i0 == ibs1)).
       intros. rewrite orb_true_iff in H2. destruct H2.
       rewrite andb_true_iff in H2. destruct H2. rewrite eqb_spec in H2, H3.
       rewrite H2, H3 in rho_interp.
       rewrite <- rho_interp. unfold Lit.interp. rewrite H0. now unfold Var.interp.
       intros. rewrite andb_true_iff in H2. destruct H2. rewrite eqb_spec in H2, H3.
       rewrite H2, H3 in rho_interp. rewrite bool_eqb_comm in rho_interp.
       rewrite <- rho_interp. unfold Lit.interp. rewrite H0. now unfold Var.interp.
       intros. rewrite H2 in H. now contradict H.
       intros. rewrite H0 in H. now contradict H.
Qed.


Lemma check_symopp_eq: forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres n,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_eq (Typ.TWord n)) = true ->
      check_symopp xbs1 ybs2 zbsres (BO_eq (Typ.TWord n))  = true.
Proof. intros.
       simpl in H. 
       case (Lit.is_pos ibsres) in H.
       case (t_form .[ Lit.blit ibsres]) in H; try (contradict H; easy).
       case ((i == ibs1) && (i0 == ibs2) || (i == ibs2) && (i0 == ibs1)) in H.
       exact H.
       now contradict H.
       now contradict H.
Qed.

(*

Lemma dsa: forall l l0 i i0 j n,
Bool.eqb (Lit.interp rho i) (Lit.interp rho i0) = Lit.interp rho j
->
weqb (ListToword (Lit.interp rho i :: map (Lit.interp rho) l) n)
  (ListToword (Lit.interp rho i0 :: map (Lit.interp rho) l0) n) =
Lit.interp rho j &&
weqb (ListToword (map (Lit.interp rho) l) n) (ListToword (map (Lit.interp rho) l0) n).
Proof. intro l.
       induction l as [ | xl xsl IHl ]; intros.
       - simpl. case_eq l0; intros. simpl.
         

*)

Theorem weqb_refl: forall sz x,
  @weqb sz x x = true.
Proof. intros. 
       induction x; intros.
       - now simpl.
       - simpl. rewrite Bool.eqb_reflx. now rewrite IHx.
Qed.

Lemma prop_check_eq: forall bs1 bs2 bsres,
      (length bs1) = (length bs2) ->
      check_eq bs1 bs2 bsres = true ->
      forallb2 Bool.eqb (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2) =
      forallb (Lit.interp rho) bsres.
Proof. intro bs1.
  induction bs1 as [ | x1 bs1 IHbs1 ].
  - intros bs2 bsres Hlen Hcheck.
    case bs2 in *.
    + case bsres in *.
      * now simpl.
      * contradict Hcheck; now simpl.
    + contradict Hcheck; now simpl.
  - intros bs2 bsres Hlen Hcheck.
    symmetry.
    case bs2 in *.
    + case bsres in *; contradict Hcheck; now simpl.
    + case bsres in *.
      * contradict Hcheck; now simpl.
      * simpl.
        rename i into x2. rename i0 into r1.
        simpl in Hlen. inversion Hlen.
        rename H0 into Hlen'.

        case bsres in *.
        (*--*) simpl in Hcheck.
           case_eq (Lit.is_pos r1); intros; rewrite H in Hcheck;
           try (case bs1 in *; try (now contradict Hcheck); case bs2 in *;
                try (now contradict Hcheck));
           rename H into Hposr1;
           case_eq (t_form .[ Lit.blit r1]);intros; rewrite H in Hcheck; try (now contradict Hcheck); 
           rename H into Hform_r1;
           generalize (rho_interp (Lit.blit r1)); rewrite Hform_r1; simpl;
           intro Hi.
           (*++*) rename i into arg1; rename i0 into arg2.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi. repeat (rewrite andb_true_r).
              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
              (* ** *) intros Hif.
                 rewrite orb_true_iff in Hif.
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). now rewrite Hx1, Hx2.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                     now rewrite bool_eqb_comm.
             (* ** *)intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.

           (* ++ *)
             case_eq (to_list a);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Ha, i1 into a1, l into rargs.
              case_eq (Lit.is_pos a1);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Hposa1.
              case_eq (t_form .[ Lit.blit a1]);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Hform_a1.
              rename i into x1', i0 into x2', i1 into arg1, i2 into arg2.
              generalize (rho_interp (Lit.blit a1)). rewrite Hform_a1. simpl.
              intro Heqx1x2.
              rewrite afold_left_and in Hi.
              rewrite Ha in Hi. simpl in Hi.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi. repeat (rewrite andb_true_r).
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposa1. rewrite Heqx1x2.

              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
              (* ** *) intros Hif.
                 rewrite Hif in Hcheck.
                 apply (@IHbs1 _ _ Hlen') in Hcheck.
                 simpl in Hcheck. rewrite Hcheck.
                 repeat (rewrite orb_true_iff in Hif).
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). now rewrite Hx1, Hx2.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                     now rewrite bool_eqb_comm.
              (* ** *) intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.

       (* -- *) simpl in Hcheck.
           case_eq (Lit.is_pos r1); intros; rewrite H in Hcheck;
           try (case bs1 in *; try (now contradict Hcheck); case bs2 in *;
                try (now contradict Hcheck));
           rename H into Hposr1;
           case_eq (t_form .[ Lit.blit r1]);intros; rewrite H in Hcheck; try (now contradict Hcheck); 
           rename H into Hform_r1;
           generalize (rho_interp (Lit.blit r1)); rewrite Hform_r1; simpl;
           intro Hi.
          (* ++ *) contradict Hcheck. simpl.
              case ((i0 == x1) && (i1 == x2) || (i0 == x2) && (i1 == x1)); easy.
          (* ++ *) rename i0 into x1', i1 into x2', i2 into arg1, i3 into arg2.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi.
              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
             (* ** *) intros Hif. rewrite Hif in Hcheck.
                 apply (@IHbs1 _ _ Hlen') in Hcheck.
                 simpl in Hcheck. rewrite Hcheck.
                 repeat (rewrite orb_true_iff in Hif).
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). now rewrite Hx1, Hx2.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                     now rewrite bool_eqb_comm.
            (*  ** *) intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.
Qed.


Lemma length_check_eq: forall bs1 bs2 bsres,
  check_eq bs1 bs2 bsres = true -> length bs1 = length bs2.
Proof.
  intro bs1.
  induction bs1.
  + intros. case bs2 in *. trivial.
    simpl in H. now contradict H.
  + intros.
    case bs2 in *.
    - simpl in H. now contradict H.
    - simpl. apply f_equal.
      simpl in H.
      revert H.
      case bsres. easy.
      intros r rl.
      case rl.
      case (Lit.is_pos r).
      case (t_form .[ Lit.blit r]); try easy.
      intro a0.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      intros i1 l a0.
      case (to_list a0); try easy.
      intros i2 l0.
      case (Lit.is_pos i2); try easy.
      case (t_form .[ Lit.blit i2]); try easy.
      intros i3 i4.
      case ((i3 == a) && (i4 == i) || (i3 == i) && (i4 == a)).
      apply IHbs1.
      easy.
      intros _ _ i2 l0 a0.
      case (to_list a0); try easy.
      intros i1 l.
      case (Lit.is_pos i1); try easy.
      case (t_form .[ Lit.blit i1]); try easy.
      intros i3 i4.
      case ((i3 == a) && (i4 == i) || (i3 == i) && (i4 == a)).
      apply IHbs1.
      easy.
      intros i2 l0 a0.
      case (to_list a0); try easy.
      intros i9 l.
      case (Lit.is_pos i9); try easy.
      case (t_form .[ Lit.blit i9]); try easy.
      intros i3 i4.
      case ((i3 == a) && (i4 == i) || (i3 == i) && (i4 == a)).
      apply IHbs1.
      easy.
      intros _ _ i2 l0 a0.
      case (to_list a0); try easy.
      intros i9 l.
      case (Lit.is_pos i9); try easy.
      case (t_form .[ Lit.blit i9]); try easy.
      intros i3 i4.
      case ((i3 == a) && (i4 == i) || (i3 == i) && (i4 == a)).
      apply IHbs1.
      easy.
      case bs1; try easy; case bs2; easy.
      case bs1; try easy; case bs2; easy.
      case bs1; try easy; case bs2; easy.
      case bs1; try easy; case bs2.

      simpl. easy.

      intros i0 l i1 i2.
      case ((i1 == a) && (i2 == i) || (i1 == i) && (i2 == a)); easy.
      simpl.
      intros _ l i1 i2.
      case ((i1 == a) && (i2 == i) || (i1 == i) && (i2 == a)); easy.
      easy.
      case bs1 in *; try easy; case bs2; easy.
      case bs1 in *; try easy; case bs2; easy.
      case bs1 in *; try easy; case bs2; easy.
      case bs1 in *; try easy; case bs2; try easy.
      case (Lit.is_pos r); try easy.
      case (t_form .[ Lit.blit r]); try easy.
      simpl. intros x y. case ((x == a) && (y == i) || (x == i) && (y == a)); easy.
      case (Lit.is_pos r); try easy.
      case (t_form .[ Lit.blit r]); try easy.
      simpl. intros x y. case ((x == a) && (y == i) || (x == i) && (y == a)); easy.
      case (Lit.is_pos r); try easy.
      case (t_form .[ Lit.blit r]); try easy.
      intros x y. case ((x == a) && (y == i) || (x == i) && (y == a)).
      intros x2 rbs2 xr rbrs.
      apply IHbs1. easy.
Qed.

Lemma beqb_w:forall a,
(ListToword [Lit.interp rho a] 1) =  WS (Lit.interp rho a) WO.
Proof. intro a.
       induction (Lit.interp rho a); intros; now compute.
Qed.

Lemma beqb_w2:forall a b,
Bool.eqb (Lit.interp rho a) (Lit.interp rho b) =
weqb (ListToword [Lit.interp rho a] 1) (ListToword [Lit.interp rho b] 1).
Proof. intros. rewrite !beqb_w. simpl.
       case_eq (Bool.eqb (Lit.interp rho a) (Lit.interp rho b)); intros; easy.
Qed.

Lemma prop_check_eqw: forall bs1 bs2 bsres,
      (length bs1) = (length bs2) ->
      check_eq bs1 bs2 bsres = true ->
      Word.weqb (ListToword (map (Lit.interp rho) bs1) (length bs1)) 
                (ListToword (map (Lit.interp rho) bs2) (length bs1)) =
      forallb (Lit.interp rho) bsres.
Proof. intro bs1.
  induction bs1 as [ | x1 bs1 IHbs1 ].
  - intros bs2 bsres Hlen Hcheck.
    case bs2 in *.
    + case bsres in *.
      * now simpl.
      * contradict Hcheck; now simpl.
    + contradict Hcheck; now simpl.
  - intros bs2 bsres Hlen Hcheck.
    symmetry.
    case bs2 in *.
    + case bsres in *; contradict Hcheck; now simpl.
    + case bsres in *.
      * contradict Hcheck; now simpl.
      * simpl.
        rename i into x2. rename i0 into r1.
        simpl in Hlen. inversion Hlen.
        rename H0 into Hlen'.

        case bsres in *.
        (*--*) simpl in Hcheck.
           case_eq (Lit.is_pos r1); intros; rewrite H in Hcheck;
           try (case bs1 in *; try (now contradict Hcheck); case bs2 in *;
                try (now contradict Hcheck));
           rename H into Hposr1;
           case_eq (t_form .[ Lit.blit r1]);intros; rewrite H in Hcheck; try (now contradict Hcheck); 
           rename H into Hform_r1;
           generalize (rho_interp (Lit.blit r1)); rewrite Hform_r1; simpl;
           intro Hi.
           (*++*) rename i into arg1; rename i0 into arg2.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi. repeat (rewrite andb_true_r).
              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
              (* ** *) intros Hif.
                 rewrite orb_true_iff in Hif.
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). rewrite Hx1, Hx2. now rewrite beqb_w2.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                        rewrite bool_eqb_comm. now rewrite beqb_w2.
             (* ** *)intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.

           (* ++ *)
             case_eq (to_list a);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Ha, i1 into a1, l into rargs.
              case_eq (Lit.is_pos a1);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Hposa1.
              case_eq (t_form .[ Lit.blit a1]);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Hform_a1.
              rename i into x1', i0 into x2', i1 into arg1, i2 into arg2.
              generalize (rho_interp (Lit.blit a1)). rewrite Hform_a1. simpl.
              intro Heqx1x2.
              rewrite afold_left_and in Hi.
              rewrite Ha in Hi. simpl in Hi.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi. repeat (rewrite andb_true_r).
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposa1. rewrite Heqx1x2.

              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
              (* ** *) intros Hif.
                 rewrite Hif in Hcheck.
                 apply (@IHbs1 _ _ Hlen') in Hcheck.
                 simpl in Hcheck.
                 specialize (helper_strong (Lit.interp rho x1' :: map (Lit.interp rho) bs1) (Lit.interp rho x1)); intros.
                 simpl in H. rewrite map_length in H. rewrite H.
                 specialize (helper_strong (Lit.interp rho x2' :: map (Lit.interp rho) bs2) (Lit.interp rho x2)); intros.
                 simpl in H0. rewrite map_length in H0. inversion Hlen.
                 rewrite H2, H0. simpl. rewrite <- H2, Hcheck.
                 repeat (rewrite orb_true_iff in Hif).
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). rewrite Hx1, Hx2.
                          case_eq (Bool.eqb (Lit.interp rho x1) (Lit.interp rho x2));
                          case_eq (forallb (Lit.interp rho) rargs); intros; easy.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                          rewrite bool_eqb_comm.
                          case_eq (Bool.eqb (Lit.interp rho x1) (Lit.interp rho x2));
                          case_eq (forallb (Lit.interp rho) rargs); intros; easy.
              (* ** *) intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.

       (* -- *) simpl in Hcheck.
           case_eq (Lit.is_pos r1); intros; rewrite H in Hcheck;
           try (case bs1 in *; try (now contradict Hcheck); case bs2 in *;
                try (now contradict Hcheck));
           rename H into Hposr1;
           case_eq (t_form .[ Lit.blit r1]);intros; rewrite H in Hcheck; try (now contradict Hcheck); 
           rename H into Hform_r1;
           generalize (rho_interp (Lit.blit r1)); rewrite Hform_r1; simpl;
           intro Hi.
          (* ++ *) contradict Hcheck. simpl.
              case ((i0 == x1) && (i1 == x2) || (i0 == x2) && (i1 == x1)); easy.
          (* ++ *) rename i0 into x1', i1 into x2', i2 into arg1, i3 into arg2.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi.
              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
             (* ** *) intros Hif. rewrite Hif in Hcheck.
                 apply (@IHbs1 _ _ Hlen') in Hcheck.
                 simpl in Hcheck.
                 specialize (helper_strong (Lit.interp rho x1' :: map (Lit.interp rho) bs1) (Lit.interp rho x1)); intros.
                 simpl in H. rewrite map_length in H. rewrite H.
                 specialize (helper_strong (Lit.interp rho x2' :: map (Lit.interp rho) bs2) (Lit.interp rho x2)); intros.
                 simpl in H0. rewrite map_length in H0. inversion Hlen.
                 rewrite H2, H0. simpl. rewrite <- H2, Hcheck.
                 repeat (rewrite orb_true_iff in Hif).
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). rewrite Hx1, Hx2.
                          case_eq (Bool.eqb (Lit.interp rho x1) (Lit.interp rho x2));
                          case_eq ((Lit.interp rho i && forallb (Lit.interp rho) bsres)); intros; easy.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                          rewrite bool_eqb_comm.
                          case_eq (Bool.eqb (Lit.interp rho x1) (Lit.interp rho x2));
                          case_eq ((Lit.interp rho i && forallb (Lit.interp rho) bsres)); intros; easy.
            (*  ** *) intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.
Qed.

Lemma weqb_comm: forall sz (x y: word sz),
Word.weqb x y = Word.weqb y x.
Proof.
  induction x; intro y; rewrite (shatter_word y).
  easy. simpl.
  case_eq (Bool.eqb b (whd y)); intros.
  apply Bool.eqb_prop in H. rewrite H. rewrite Bool.eqb_reflx.
  case_eq (weqb x (wtl y) ); intros.
  specialize (IHx (wtl y)). rewrite H0 in IHx. rewrite <- IHx. easy.
  specialize (IHx (wtl y)). rewrite H0 in IHx. rewrite <- IHx. easy.
  
  case_eq (Bool.eqb (whd y) b ); intros. apply Bool.eqb_prop in H0. rewrite H0 in H.
  contradict H. rewrite Bool.eqb_reflx. easy.
  easy.
Qed.

Lemma valid_check_bbEq s pos1 pos2 lres : C.valid rho (check_bbEq s pos1 pos2 lres).
  Proof.
       unfold check_bbEq.
       case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
       case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
       case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
       case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
       case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
       case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true). intros a bsres Heq8.
       case_eq (Bool.eqb (Lit.is_pos a) (Lit.is_pos bsres)); try (intros; now apply C.interp_true). intros Heq12.
       case_eq (t_form .[ Lit.blit a]); try (intros; now apply C.interp_true). intros a3 Heq10.
       case_eq (t_atom .[ a3]); try (intros; now apply C.interp_true).

       intros [ | | | | | | | [ A B | A | | | | ]|N|N|N|N|N | | ]; 
          try (intros; now apply C.interp_true).

       intros n0 a1' a2' Heq9.
       case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); 
         simpl; intros Heq15; try (now apply C.interp_true).

       case_eq (check_eq bs1 bs2 [bsres] &&
       ( (Datatypes.length bs1) =? n0)%nat); 
       simpl; intros Heq16; try (now apply C.interp_true).

       unfold C.valid. simpl.
       rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a3).
       assert (a3 < PArray.length t_atom).
       { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
       specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
       rewrite !andb_true_iff in H0. destruct H0. destruct H0.

       unfold get_type' in H0. unfold v_type in H0.
       case_eq (t_interp .[ a3]).
       intros v_typea3 v_vala3 Htia3. rewrite Htia3 in H0.

       case_eq (v_typea3); intros; rewrite H4 in H0; try (now contradict H0).
       rename H4 into Hv.

       generalize (Hs s pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
       unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
       unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
       rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

       generalize (Hs s pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
       unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
       unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
       rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

       unfold get_type' in H2, H3. unfold v_type in H2, H3.
       case_eq (t_interp .[ a1']).
         intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
       case_eq (t_interp .[ a2']).
         intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
       simpl in v_vala2, v_vala2.

       apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

       (** case a1 = a1' and a2 = a2' **)
       rewrite orb_true_iff in Heq15.
       do 2 rewrite andb_true_iff in Heq15.
       destruct Heq15 as [Heq15 | Heq15];
       destruct Heq15 as (Heq15a1 & Heq15a2); rewrite eqb_spec in Heq15a1, Heq15a2
       ;rewrite Heq15a1, Heq15a2 in *.

        (* interp_form_hatom_bv a1' =  
                 interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' =
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia1; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        unfold interp_word in HSp1.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp1.
        unfold interp_word in HSp1.

        (* interp_form_hatom_bv a2' =  
                 interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' =
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia2; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_word in HSp2.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp2.
        unfold interp_word in HSp2.

        generalize dependent v_vala1. generalize dependent v_vala2.

        rewrite H2, H3.

        assert (
        H100: ((Datatypes.length (map (Lit.interp rho) bs2))) = n0
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as (Heq16, Heq16r).
          rewrite Nat.eqb_eq in Heq16r.
          apply length_check_eq in Heq16.
          rewrite Heq16 in Heq16r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H100.
        rewrite Typ.cast_refl.

        assert (
        H101: ((Datatypes.length (map (Lit.interp rho) bs1))) = n0
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as (Heq16, Heq16r).
          rewrite Nat.eqb_eq in Heq16r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite !Typ.cast_refl. intros.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.
        apply (@Bool.eqb_true_iff (Lit.interp rho a) (Lit.interp rho bsres)).

        unfold Lit.interp, Var.interp.
        rewrite rho_interp.
        rewrite Heq10. simpl.

        unfold Atom.interp_form_hatom.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1, Htia2. simpl.
        rewrite Typ.nat_cast_refl. simpl.

        rewrite Form.wf_interp_form; trivial.
        simpl.
        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        rewrite HSp1, HSp2.
        simpl.

        rewrite Typ.i_eqb_t. simpl.

        case_eq (Lit.is_pos bsres).
        intros Hpos.

        rewrite andb_true_iff in Heq16.
        destruct Heq16 as (Heq16 & Heq16r).
        rewrite Nat.eqb_eq in Heq16r. simpl.
        pose proof Heq16 as Heq16p.

        apply length_check_eq in Heq16.
        rewrite <- Heq16r.
        rewrite  (@prop_check_eqw _ _ [bsres]). simpl.
        rewrite andb_true_r. unfold Lit.interp, Var.interp.
        generalize (rho_interp (Lit.blit bsres)). simpl.
        intro Hbres. rewrite Hbres. simpl.
        rewrite Hpos.
        simpl. now unfold Atom.interp_form_hatom, interp_hatom.
        exact Heq16.

        exact Heq16p.

        intros Hpos.
        rewrite andb_true_iff in Heq16.
        destruct Heq16 as (Heq16 & Heq16r).

        contradict Heq16.
        case bs1 in *; try now simpl; case bs2 in *; now simpl.
        case bs2 in *. simpl. easy.
        simpl. rewrite Hpos. case bs1; intros; auto; case bs2; auto.

        pose proof Heq16 as Heq16'.

        rewrite andb_true_iff in Heq16.
        destruct Heq16 as (Heq16 & Heq16r).
        apply length_check_eq in Heq16; auto.

       (** case symmetry **)


        (* interp_form_hatom_bv a1' = 
                 interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' =
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia1; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp2.
        unfold interp_word in HSp2.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp2.
        unfold interp_word in HSp2.

        (* interp_form_hatom_bv a2' =
                 interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' =
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia2; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp1.
        unfold interp_word in HSp1.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp1.
        unfold interp_word in HSp1.

        generalize dependent v_vala1. generalize dependent v_vala2.

        rewrite H2, H3.

        assert (
        H100: ((Datatypes.length (map (Lit.interp rho) bs1))) = n0
        ).
        {
          rewrite Nat.eqb_eq in Heq16r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H100.
        rewrite !Typ.cast_refl.

        assert (
        H101: ((Datatypes.length (map (Lit.interp rho) bs2))) = n0
        ).
        {
          rewrite Nat.eqb_eq in Heq16r.
          rewrite Heq16 in Heq16r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H101.
        rewrite Typ.cast_refl.

        intros.
        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.
        apply (@Bool.eqb_true_iff (Lit.interp rho a) (Lit.interp rho bsres)).

        unfold Lit.interp, Var.interp.
        rewrite rho_interp.
        rewrite Heq10. simpl.

        unfold Atom.interp_form_hatom.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1, Htia2. simpl.
        rewrite Typ.nat_cast_refl. simpl.

        rewrite Form.wf_interp_form; trivial.
        simpl.
        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        rewrite HSp1, HSp2.
        simpl.

        rewrite Typ.i_eqb_t. simpl.

        case_eq (Lit.is_pos bsres).
        intros Hpos.
        rewrite Nat.eqb_eq in Heq16r.
        rewrite <- Heq16r.
        rewrite weqb_comm.

        rewrite (@prop_check_eqw _ _ [bsres]). simpl.
        rewrite andb_true_r. unfold Lit.interp, Var.interp.
        generalize (rho_interp (Lit.blit bsres)). simpl.
        intro Hbres. rewrite Hbres.

        rewrite andb_true_iff in Heq16'.
        destruct Heq16' as (Heq16' & Heq16'r).
        rewrite Hpos.
        now unfold Atom.interp_form_hatom, interp_hatom.
        intros. exact Heq16.

        rewrite andb_true_iff in Heq16'.
        destruct Heq16' as (Heq16' & Heq16'r).
        exact Heq16'.

        intros Hpos.
        contradict Heq16'.
        case bs1 in *; try now simpl; case bs2 in *; now simpl.
        case bs2 in *; try now simpl; case bs2 in *; now simpl.
        simpl. easy.
        simpl.
        case bs1 in *; try now simpl; case bs2 in *; now simpl.
        rewrite Hpos.
        case bs2 in *; try now simpl; case bs2 in *; now simpl.
        now rewrite andb_false_l.

        case bs2 in *; rewrite Hpos; simpl; easy.
Qed.


Fixpoint Natpow2 (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => 2 * Natpow2 n'
  end%nat.

Definition wnegNat sz (x : word sz) : word sz :=
  natToWord sz (Natpow2 sz - wordToNat x).

Lemma ltwz: forall a, 
(ListToword a 0) = WO.
Proof. induction a as [ | xa xsa IHa ]; intros.
       - now rewrite helper1.
       - unfold ListToword. simpl. now compute.
Qed.

Lemma m0: forall a: nat , (a - 0)%nat = a%nat.
Proof. intro a.
       induction a as [ | xa IHa ]; intros; now simpl.
Qed.

Lemma div2S: forall a:nat, 
Nat.div2 (S (2 * a)) = a.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. rewrite plus_0_r.
         assert ( (xa + S xa)%nat =  (S (2 * xa)%nat)). { lia. }
         now rewrite H, IHa.
Qed.

Lemma div2e: forall a:nat, 
Nat.div2 (2 * a) = a.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. rewrite plus_0_r.
         assert ( (xa + S xa)%nat =  (S (2 * xa)%nat)). { lia. }
         now rewrite H, IHa.
Qed.

Lemma diff: forall a b, Nat.div2 (2 * a - (S (2 * b))) = (a - b - 1)%nat.
Proof. intro a.
       induction a as [ | xa IHa]; intros.
       - now simpl.
       - case_eq b; intros. simpl. rewrite plus_0_r. rewrite !m0.
         assert ((xa + S xa)%nat = (S (2* xa)) ). { lia. }
         now rewrite H0, div2S.
         simpl. rewrite !plus_0_r.
         assert (xa + S xa = S (xa + xa))%nat. { lia. }
         rewrite H0. simpl. assert ((xa + xa = 2 * xa)%nat ). { lia. }
         assert (((n + S n) = S (2 * n))%nat). { lia. }
         now rewrite H1, H2, IHa.
Qed.

Lemma diff2: forall a b, Nat.div2 ((2 * a - (S (2 * b))) - 1) = (a - b - 1)%nat.
Proof. intro a.
       induction a as [ | xa IHa]; intros.
       - now simpl.
       - case_eq b; intros. simpl. rewrite plus_0_r, !m0.
         assert ( (xa + S xa - 1)%nat = (2 * xa)%nat ). { lia. }
         now rewrite H0, div2e.
         simpl. rewrite !plus_0_r.
         assert (xa + S xa = S (xa + xa))%nat. { lia. }
         rewrite H0. simpl. assert ((xa + xa = 2 * xa)%nat ). { lia. }
         assert (((n + S n) = S (2 * n))%nat). { lia. }
         now rewrite H1, H2, IHa.
Qed.

Lemma diff3: forall a b, Nat.div2 ((2 * a - (2 * b)) - 1) = (a - b - 1)%nat.
Proof. intro a.
       induction a as [ | xa IHa]; intros.
       - now simpl.
       - case_eq b; intros. simpl. rewrite plus_0_r, !m0.
         assert ((xa + S xa)%nat = (S (2* xa)) ). { lia. }
         now rewrite H0, div2S.
         simpl. rewrite !plus_0_r.
         assert (xa + S xa = S (xa + xa))%nat. { lia. }
         rewrite H0. simpl. assert ((xa + xa = 2 * xa)%nat ). { lia. }
         assert (((n + S n) = S (2 * n))%nat). { lia. }
         now rewrite H1, H2, IHa.
Qed.

Lemma diff4: forall a b, Nat.div2 ((2 * a)- (2 * b)) = (a - b)%nat.
Proof. intro a.
       induction a as [ | xa IHa]; intros.
       - now simpl.
       - case_eq b; intros. simpl. rewrite plus_0_r.
         assert ((xa + S xa)%nat = (S (2* xa)) ). { lia. } 
         now rewrite H0, div2e.
         simpl. rewrite !plus_0_r.
         assert (xa + S xa = S (xa + xa))%nat. { lia. }
         rewrite H0. simpl. assert ((xa + xa = 2 * xa)%nat ). { lia. }
         assert (((n + S n) = S (2 * n))%nat). { lia. }
         now rewrite H1, H2, IHa.
Qed.

Lemma mf: forall a b,
 Word.mod2 ((2 * a) - (S (b * 2)) - 1) = false.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. rewrite !plus_0_r. 
         assert ((xa + S xa)%nat = (S (2 * xa))%nat). { lia. }
         rewrite H. assert ( (S (2 * xa) - (b * 2) - 1)%nat =  ((2 * xa) - (b + b))%nat). { lia. }
         rewrite H0. assert ((2 * xa - (b + b))%nat = (2 * (xa - b))%nat). { lia. }
         now rewrite H1, m2.
Qed.

Lemma mt: forall a b, a > b ->
(Word.mod2 (a + a - b * 2 - 1)) = true.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now contradict H.
       - simpl. case_eq ((b * 2)%nat); intros.
         simpl. now rewrite m0, mod2Sn.
         case_eq b; intros. subst. now contradict H0.
         subst. inversion H0.
         assert ((xa + S xa - S (n0 * 2) - 1)%nat = (xa + xa - (n0 * 2) - 1)%nat ). { lia. }
         rewrite H1. rewrite IHa. easy. lia.
Qed.

Lemma mt2: forall a b, 
a > b ->
Word.mod2 (a + a - S (b * 2)) = true.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now contradict H.
       - simpl. case_eq b; intros. 
         simpl. now rewrite m0, mod2Sn.
         assert ((xa + S xa - S n * 2)%nat = (xa + xa - S (n * 2))%nat ). { lia. }
         rewrite H1, IHa. easy. subst. lia.
Qed.

Lemma mf2: forall a b, Word.mod2 (a + a - b * 2) = false.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. case_eq ((b * 2)%nat); intros.
         + simpl. assert ((xa + S xa)%nat = (S (2 * xa))%nat). { lia. }
           now rewrite H0, m2.
         + assert (n = ((b * 2) - 1)%nat). { lia. }
           rewrite H0. assert ((xa + S xa - (b * 2 - 1))%nat = (S xa + S xa - (b * 2))%nat). { lia. }
           rewrite H1. specialize (IHa (b - 1)%nat).
           assert ((xa + xa - (b - 1) * 2)%nat = (S xa + S xa - (b * 2))%nat). { lia. }
           rewrite H2 in IHa. now rewrite IHa.
Qed.

Lemma n2pg0: forall n,
Natpow2 n > 0.
Proof. intro n.
       induction n as  [ | xn IHn ]; intros. simpl. lia.
       simpl. lia.
Qed.

Lemma n2pg0l: forall a,
Natpow2 (Datatypes.length a) > wordToNat (ListToword a (Datatypes.length a)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl. lia.
       - simpl. rewrite plus_0_r. rewrite helper_strong.
         simpl. case_eq xa; intros. simpl. lia.
         lia.
Qed.

Lemma neq_eq1: forall a,
natToWord (Datatypes.length a)
  (Natpow2 (Datatypes.length a) - wordToNat (ListToword a (Datatypes.length a)) - 1) =
ListToword (map negb a) (Datatypes.length a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl. now rewrite !ltwz.
       - simpl. rewrite !plus_0_r. rewrite helper_strong. simpl.
         case_eq xa; intros. simpl.
         assert (  (Natpow2 (Datatypes.length xsa) + Natpow2 (Datatypes.length xsa))%nat =
                   (2 * Natpow2 (Datatypes.length xsa))%nat ) . { lia. }
         rewrite H0, mf.
         specialize (helper_strong (map negb xsa) false); intros.
         simpl in H1. rewrite map_length in H1. rewrite H1. apply f_equal.
         assert (((Natpow2 (Datatypes.length xsa) + Natpow2 (Datatypes.length xsa) -
                 S (wordToNat (ListToword xsa (Datatypes.length xsa)) * 2) - 1))%nat = 
                ((2* (Natpow2 (Datatypes.length xsa))) -
                (S (2 * (wordToNat (ListToword xsa (Datatypes.length xsa))))) - 1)%nat ). { lia. }
         assert ((wordToNat (ListToword xsa (Datatypes.length xsa)) * 2)%nat =
                 (2 * (wordToNat (ListToword xsa (Datatypes.length xsa))))%nat) as Ha. { lia. }
         
         now rewrite Ha, diff2, IHa.
         
         simpl.
         assert (  (Word.mod2
                (Natpow2 (Datatypes.length xsa) + Natpow2 (Datatypes.length xsa) -
                wordToNat (ListToword xsa (Datatypes.length xsa)) * 2 - 1) ) = true). { rewrite mt. easy.
         apply n2pg0l. }
         rewrite H0.
         specialize (helper_strong (map negb xsa) true); intros.
         simpl in H1. rewrite map_length in H1. rewrite H1. apply f_equal.
         assert (((Natpow2 (Datatypes.length xsa) + Natpow2 (Datatypes.length xsa) -
                  wordToNat (ListToword xsa (Datatypes.length xsa)) * 2 - 1) =
                  ( (2 * (Natpow2 (Datatypes.length xsa))) -
                  (2 * wordToNat (ListToword xsa (Datatypes.length xsa))) - 1))%nat). { lia. }
         now rewrite H2, diff3, IHa.
Qed.

Lemma divn1: forall a b: nat,
 (Nat.div2 (a + a - S b * 2)%nat = (a - b - 1)%nat).
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros.
         simpl. rewrite m0. assert ((xa + S xa - 1)%nat = (2 * xa)%nat). { lia. }
         now rewrite H0, d2.
         assert ((xa + S xa - S (S n * 2))%nat = (xa + xa - (S n * 2))%nat ). { lia. }
         now rewrite H0, IHa.
Qed.

Lemma div2Sn: forall a, Nat.div2 (a + S a) = a.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. assert ((xa + S (S xa))%nat = (S (xa + (S xa)))%nat). { lia. }
         now rewrite H, IHa.
Qed.

Lemma divn2: forall a b: nat,
Nat.div2 (a + a - S (b * 2)) = (a - b - 1)%nat.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros.
         simpl. now rewrite !m0, div2Sn.
         assert ((xa + S xa - S n * 2)%nat = (xa + xa - S (n * 2))%nat ). { lia. }
         now rewrite H0, IHa.
Qed.


Lemma neq_eq: forall a,
wnegNat (ListToword a (length a)) = ListToword (RAWBITVECTOR_LIST.twos_complement a) (length a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl. now rewrite !ltwz.
       - simpl. rewrite helper_strong. simpl.
         case_eq xa; intros. simpl. unfold wnegNat, RAWBITVECTOR_LIST.twos_complement in *.
         simpl. rewrite !plus_0_r.
         rewrite RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r.

         assert (   (Nat.div2
          (Natpow2 (Datatypes.length xsa) + Natpow2 (Datatypes.length xsa) -
          S (wordToNat (ListToword xsa (Datatypes.length xsa)) * 2))) =
          (Natpow2 (Datatypes.length xsa) - wordToNat (ListToword xsa (Datatypes.length xsa)) - 1)%nat).
         { now rewrite divn2. }

         rewrite H0.
         specialize (helper_strong (map negb xsa) true); intros.
         simpl in H1. rewrite map_length in H1. rewrite H1.
         assert (  (Word.mod2
                   (Natpow2 (Datatypes.length xsa) + Natpow2 (Datatypes.length xsa) -
                   S (wordToNat (ListToword xsa (Datatypes.length xsa)) * 2))) = true).
         { rewrite mt2. easy. apply n2pg0l. }
 
         rewrite H2. apply f_equal. now rewrite neq_eq1. 
         rewrite map_length; lia.

         unfold wnegNat, RAWBITVECTOR_LIST.twos_complement in *.
         simpl. rewrite plus_0_r.

         assert (  (Word.mod2
                   (Natpow2 (Datatypes.length xsa) + Natpow2 (Datatypes.length xsa) -
                   wordToNat (ListToword xsa (Datatypes.length xsa)) * 2)) = false).
         { now rewrite mf2. }

         rewrite H0. 
         specialize (helper_strong (RAWBITVECTOR_LIST.add_list_ingr (map negb xsa)
                    (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length xsa)) true) false); intros.
         simpl in H1. specialize (@RAWBITVECTOR_LIST.add_list_carry_length_eq
                                 (map negb xsa)
                                 (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length xsa)) true); intros.
         rewrite <- H2 in H1. rewrite map_length in H1. rewrite H1. apply f_equal.
         assert (     (Natpow2 (Datatypes.length xsa) + Natpow2 (Datatypes.length xsa) -
                      wordToNat (ListToword xsa (Datatypes.length xsa)) * 2)%nat =
                      (2 * (Natpow2 (Datatypes.length xsa)) -
                      (2 * wordToNat (ListToword xsa (Datatypes.length xsa))))%nat). { lia. }
         now rewrite H3, diff4, IHa.
         now rewrite RAWBITVECTOR_LIST.length_mk_list_false, map_length.
Qed.

Lemma eq_toW: forall a,
wordToNat (ListToword a (Datatypes.length a)) =
N.to_nat (wordToN   (ListToword a (Datatypes.length a))).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. rewrite helper_strong. 
         simpl. case_eq xa ;intros.
         case_eq ( wordToN (ListToword xsa (Datatypes.length xsa))); intros.
         rewrite H0 in IHa. rewrite IHa. now simpl.
         rewrite H0 in IHa. rewrite IHa. simpl. lia.
         case_eq ( wordToN (ListToword xsa (Datatypes.length xsa))); intros.
         rewrite H0 in IHa. rewrite IHa. now simpl.
         rewrite H0 in IHa. rewrite IHa. simpl. lia.
Qed.

Lemma eq_pow2: forall n: nat,
  Natpow2 n = N.to_nat (Npow2 n).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. rewrite plus_0_r.
         case_eq (Npow2 xn); intros.
         rewrite H in IHn. rewrite IHn. now simpl.
         rewrite H in IHn. rewrite IHn. simpl. lia.
Qed.

Lemma Ntonatm: forall a b,
(N.to_nat a - N.to_nat b)%nat = N.to_nat (a - b).
Proof. intro a.
       induction a; intros.
       - now simpl.
       - case_eq b; intros.
         + simpl. lia.
         + simpl. case_eq (Pos.sub_mask p p0); intros.
           apply Pos.sub_mask_nul_iff in H0. rewrite H0. simpl. lia.
           apply Pos.sub_mask_pos_iff in H0. inversion H0. simpl. lia.
           apply Pos.sub_mask_neg_iff in H0. inversion H0. simpl. lia.
Qed.


Lemma ntw0: forall n,
natToWord n 0 = wzero' n.
Proof. intro n.
       induction n as [ | xn IHn ]; intros; try now simpl.
       simpl. now rewrite IHn.
Qed.

Lemma len_ntl: forall n m,
length (natTolist n m) = n.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. now rewrite IHn.
Qed.

Lemma ntwl: forall n m,
natToWord n m = ListToword (natTolist n m) n.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. 
         specialize (helper_strong (natTolist xn (Nat.div2 m)) (mod2 m)); intros.
         rewrite len_ntl in H. rewrite H. apply f_equal. now rewrite IHn.
Qed.

Lemma toW_Eq: forall m n,
natToWord n (N.to_nat m) =
NToWord   n m.
Proof. intro m.
       induction m as [ | xm IHm ]; intros.
       - simpl. now rewrite ntw0.
       - simpl. now rewrite wlp, <- nl2pl, ntwl.
Qed.

Lemma wneq_eq: forall a,
wnegNat (ListToword a (length a)) = Word.wneg (ListToword a (length a)).
Proof. intros.  unfold wnegNat, Word.wneg in *.
       rewrite eq_toW, eq_pow2, Ntonatm.
       now rewrite toW_Eq.
Qed.

Lemma neq_eq0: forall a,
wneg (ListToword a (length a)) = ListToword (RAWBITVECTOR_LIST.twos_complement a) (length a).
Proof. intros.
       now rewrite <- wneq_eq, neq_eq.
Qed.

Lemma mk_list_false_eq2: forall bs, (map (fun _ : int => Lit.interp rho Lit._false) bs) =
 (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length bs)).
Proof. intro bs.
       induction bs as [ | xbs xsbs IHbs ].
       - now simpl.
       - simpl. rewrite IHbs. specialize (@Lit.interp_false rho wf_rho).
        intros. unfold is_true in H. apply not_true_is_false in H.
        now rewrite H.
Qed. 

Lemma map_interp_neg: forall bs, (map (fun x : int => negb (Lit.interp rho x)) bs) =
  (map (fun x : int => Lit.interp rho (Lit.neg x)) bs).
Proof. intro bs. 
       induction bs as [ | xbs xsbs IHbs ].
       - now simpl.
       - simpl. rewrite IHbs.
         now rewrite Lit.interp_neg.
Qed.

Lemma prop_check_neg: forall bs bsres n, 
  (N.of_nat(length bs) = n)%N -> 
  (N.of_nat(length bsres) = n)%N ->  
  check_neg bs bsres = true ->
  RAWBITVECTOR_LIST.bv_neg (map (Lit.interp rho) bs) = map (Lit.interp rho) bsres.
Proof. intros.

       unfold check_neg in H1.
       specialize (@check_add_list (map (fun l : int => Lit.neg l) bs)
       (map (fun _ : int => Lit._false) bs) bsres (Clit Lit._true)).

       intros. simpl in H2.
       cut ( Datatypes.length (map (fun l : int => Lit.neg l) bs) =
       Datatypes.length bsres ). intros.
       cut (Datatypes.length (map (fun _ : int => Lit._false) bs) =
       Datatypes.length bsres). intros.
       specialize (H2 H3 H4 H1).
       unfold BITVECTOR_LIST.bv_neg, RAWBITVECTOR_LIST.bv_neg.
       unfold RAWBITVECTOR_LIST.twos_complement.

       rewrite !map_map in H2.
       rewrite !map_map.
       rewrite mk_list_false_eq2 in H2.
       rewrite <- map_interp_neg in H2.
       rewrite Lit.interp_true in H2.
       rewrite <- H2.
       now rewrite map_length.

       easy.

       rewrite map_length. 
       apply (f_equal (N.to_nat)) in H.
       apply (f_equal (N.to_nat)) in H0.
       rewrite Nat2N.id in H, H0.
       now rewrite H, H0.

       rewrite map_length. 
       apply (f_equal (N.to_nat)) in H.
       apply (f_equal (N.to_nat)) in H0.
       rewrite Nat2N.id in H, H0.
       now rewrite H, H0.
Qed.

Lemma check_neg_length: forall bs bsres,
  check_neg bs bsres = true -> (length bs = length bsres)%nat.
Proof. intros.
       unfold check_neg in H.
       specialize (@check_add_bvadd_length  (map (fun l : int => Lit.neg l) bs)
       (map (fun _ : int => Lit._false) bs) bsres  (Clit Lit._true)).
       intros. simpl in H0.
       specialize (H0 H).
       destruct H0. now rewrite map_length in H0.
Qed.

Lemma valid_check_bbNeg s pos lres : C.valid rho (check_bbNeg s pos lres).
Proof.
      unfold check_bbNeg.
      case_eq (S.get s pos); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | | | | ] a1' Heq9; try now apply C.interp_true.

      case_eq ((a1 == a1') && check_neg bs1 bsres &&
      ((Datatypes.length bs1) =? n)%nat); 
      simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl.  rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply Word.weqb_true_iff.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea); intros; rewrite H3 in H0; try (now contradict H0).
        rename H3 into Hv.

        generalize (Hs s pos). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        apply Word.weqb_true_iff in HSp1.

        unfold get_type' in H2. unfold v_type in H2.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2.

        (** case a1 = a1' **)
        do 2 rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq10, Heq11).
        destruct Heq10 as (Heq10a1 & Heq10a2). 
        rewrite Int63Properties.eqb_spec in Heq10a1; rewrite Heq10a1 in *.

       (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_word a = 
                interp_word t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H3. rewrite Heq9. simpl.
        unfold interp_word. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H2. intros.
        rewrite Htia1.
        unfold apply_unop.
        rewrite Typ.cast_refl.
        unfold Bval.

        assert (H100: ((Datatypes.length (map (Lit.interp rho) bsres))) = n).
        {
          apply check_neg_length in Heq10a2.
          rewrite Nat.eqb_eq in Heq11.
          rewrite Heq10a2 in Heq11.
          now rewrite map_length.
        }

       rewrite H100.

        rewrite Typ.cast_refl. 
        intros.
        unfold Word.wneg.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        unfold interp_word in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_word in HSp1.

        revert HSp1.

        assert (H101: ((Datatypes.length (map (Lit.interp rho) bs1))) = n).
        {
          rewrite Nat.eqb_eq in Heq11.
          now rewrite map_length.
        }

        rewrite H101.

        rewrite Typ.cast_refl. 
        intros.
        rewrite HSp1. simpl.

        specialize(@prop_check_neg bs1 bsres).
        intros. unfold RAWBITVECTOR_LIST.bv_neg in H5.
        rewrite <- H5 with (N.of_nat n). simpl.
        specialize (neq_eq0 (map (Lit.interp rho) bs1)); intros.
        rewrite map_length in H6, H101. rewrite H101 in H6.
        now rewrite <- H6.
        rewrite map_length in H101. now rewrite H101.


        pose proof Heq10a2 as Heq10a3.
        apply check_neg_length in Heq10a3.
        rewrite <- Heq10a3.
        rewrite map_length in H101. now rewrite H101.

        easy.
Qed.


Lemma not_eq: forall a,
wnot (ListToword a (length a)) = ListToword (map negb a) (length a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. rewrite helper_strong.
         simpl. specialize (helper_strong (map negb xsa) (negb xa)); intros.
         rewrite map_length in H. now rewrite H, IHa.
Qed.

Lemma prop_check_not:
  forall bs br, length bs = length br ->
           check_not bs br = true ->
           map (Lit.interp rho) br = map (fun l => negb (Lit.interp rho l)) bs.
Proof.
  intro bs; induction bs; intros br Hlen Hcheck.
  - simpl in Hlen. symmetry in Hlen. apply empty_list_length in Hlen. rewrite Hlen; now simpl.
  - case br in *.
    + simpl in Hcheck; now contradict Hcheck.
    + simpl in Hlen. inversion Hlen as [Hlen'].
      simpl in Hcheck. rewrite andb_true_iff in Hcheck; destruct Hcheck as (Hcheck1, Hcheck2).
      apply Int63Properties.eqb_spec in Hcheck1; rewrite Hcheck1.
      simpl. rewrite Lit.interp_neg. apply f_equal.
      apply IHbs; auto.
Qed.

Lemma check_not_length:
  forall bs br, check_not bs br = true -> length bs = length br.
Proof.
  intro bs; induction bs; intros br Hcheck.
  - case br in *.
    + auto.
    + simpl in Hcheck; now contradict Hcheck.
  - case br in *.
    + simpl in Hcheck; now contradict Hcheck.
    + simpl in *.
      rewrite andb_true_iff in Hcheck.
      destruct Hcheck as (_, Hcheck').
      apply IHbs in Hcheck'; auto.
Qed.

Lemma prop_check_notw: forall a,
ListToword (map (fun l : int => negb (Lit.interp rho l)) a) (length a) =
wnot (ListToword (map (Lit.interp rho) a) (length a)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. specialize (helper_strong (map (fun l : int => negb (Lit.interp rho l)) xsa) 
                                          (negb (Lit.interp rho xa))); intros.
         rewrite map_length in H. rewrite H.
         specialize (helper_strong ( map (Lit.interp rho) xsa) (Lit.interp rho xa)); intros.
         rewrite map_length in H0. rewrite H0.
         simpl. now rewrite IHa.
Qed.

Lemma valid_check_bbNot s pos lres : C.valid rho (check_bbNot s pos lres).
Proof.
  unfold check_bbNot.
  case_eq (S.get s pos); [ (intros; now apply C.interp_true) | ].
  intros l ls Hpos.
  case_eq ls; [ | (intros; now apply C.interp_true) ].
  intro Hnil.
  case_eq (Lit.is_pos l && Lit.is_pos lres); [ | (intros; now apply C.interp_true) ].
  intro Hpos'.
  case_eq (t_form .[ Lit.blit l]); try (intros; now apply C.interp_true).
  intros a bs HBl.
  case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
  intros r br HBr.
  case_eq (t_atom .[ r]); try (intros; now apply C.interp_true).
  intros u a'.
  case_eq u; try (intros; now apply C.interp_true).
  intros n Huot Hr.
  case_eq ((a == a')
             && check_not bs br
             && ((Datatypes.length bs) =? n)%nat);
    try (intros; now apply C.interp_true).
  intro Hc.
  rewrite !andb_true_iff in Hc.
  destruct Hc as ((Ha, Hcheck), Hlen).
  rewrite Nat.eqb_eq in Hlen.
  apply Int63Properties.eqb_spec in Ha.
  generalize (Hs s pos).
  rewrite Hpos, Hnil.
  unfold C.valid, C.interp; simpl; rewrite !orb_false_r.
  unfold Lit.interp, Var.interp.
  rewrite andb_true_iff in Hpos'.
  destruct Hpos' as (Hposl, Hposlres).
  rewrite Hposl, Hposlres.
  rewrite !rho_interp. rewrite HBl, HBr. simpl.

  intro Heqa.
  apply Word.weqb_true_iff in Heqa.
  apply Word.weqb_true_iff.


  generalize wt_t_atom. unfold Atom.wt. unfold is_true.
  rewrite PArray.forallbi_spec;intros.

  pose proof (H r). 
  assert (r < PArray.length t_atom).
  {
    apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Hr. easy.
  }

  specialize (@H0 H1). rewrite Hr in H0. simpl in H0.
  rewrite !andb_true_iff in H0. destruct H0.

  unfold get_type' in H0. unfold v_type in H0.
  case_eq (t_interp .[ r]).
  intros v_typer v_valr Htir. rewrite Htir in H0.
  case_eq (v_typer); intros; rewrite H3 in H0; try (now contradict H1).
  rename H3 into Hv.

  (* interp_form_hatom_bv r = 
          interp_bv t_i (interp_atom (t_atom .[r])) *)
  assert (interp_form_hatom_word r = 
          interp_word t_i (interp_atom (t_atom .[r]))).
  {
    unfold Atom.interp_form_hatom_word.
    unfold Atom.interp_hatom.
    rewrite !Atom.t_interp_wf; trivial.
  }

  rewrite H3, Hr. simpl.
  unfold interp_word.
  apply Typ.eqb_spec in H2.
  unfold get_type' in H2.
  unfold v_type in H2.
  case_eq (t_interp .[ a']).
  intros. rewrite H4 in H2. simpl.

  revert v_val0 H4.  
  rewrite H2. intros.
  rewrite Typ.cast_refl.
  simpl.

  assert ( ( (Datatypes.length (map (Lit.interp rho) br))) = n).
  {
    apply check_not_length in Hcheck. rewrite Hcheck in Hlen.
    now rewrite map_length.
  }

  rewrite H5.
  intros.
  rewrite Typ.nat_cast_refl.

  rewrite <- Ha in *.

   (* interp_form_hatom_bv a = 
          interp_bv t_i (interp_atom (t_atom .[a])) *)
  assert (interp_form_hatom_word a = 
          interp_word t_i (interp_atom (t_atom .[a]))).
  {
    unfold Atom.interp_form_hatom_word.
    unfold Atom.interp_hatom.
    rewrite !Atom.t_interp_wf; trivial.
  }

  rewrite H6 in Heqa.
  unfold interp_atom in Heqa.
  rewrite Atom.t_interp_wf in H4; trivial. unfold interp_atom in H4.
  rewrite H4 in Heqa.
  revert Heqa . 

  assert ( ((Datatypes.length (map (Lit.interp rho) bs))) = n).
  {
    now rewrite map_length.
  }

  rewrite H7. unfold interp_word.
  rewrite Typ.cast_refl. intros.
  rewrite Heqa. simpl.

  specialize (@prop_check_not bs br). intros.
  symmetry.
  unfold RAWBITVECTOR_LIST.bits.
  rewrite H8; auto. now rewrite <- H7, map_length, prop_check_notw.

  now apply check_not_length in Hcheck.

Qed.

Lemma diseq_neg_eq: forall (la lb: list bool),
      List_diseqb la lb = true -> negb (RAWBITVECTOR_LIST.beq_list la lb) = true.
Proof. intro la.
       induction la.
       - intros. simpl in H. case lb in *.
           now contradict H.
           now simpl.
       - intros.
         simpl in *.
         case lb in *.
          easy.
          case_eq (Bool.eqb a false).
          intros. rewrite H0 in H.
          case_eq (Bool.eqb b false).
          intros. rewrite H1 in H.
          case a in *. now contradict H0.
          case b in *. now contradict H1.
          simpl.
          apply IHla. easy.
          case a in *. now contradict H0.
          case b in *. intros.
          now simpl.
          intros. simpl.
          apply IHla.
          simpl in H. easy.
          intros. rewrite H0 in H.
          case_eq (Bool.eqb b true ). intros.
          case a in *. 
          case b in *. simpl.
          apply IHla. simpl in H. easy.
          now simpl.
          now contradict H0.
          intros.
          case a in *.
          case b in *. simpl in *. now contradict H1.
          now simpl in *.
          case b in *. now simpl in *.
          simpl in *. now contradict H.
Qed.


Lemma diseq_neg_eqw': forall s (x y: word s),
      List_diseqb (wordToList x) (wordToList y) = true -> 
      negb (Word.weqb x y) = true.
Proof. intros s x.
       induction x; intros.
       - simpl in *.  specialize (WOz y); intros. rewrite H0 in H. simpl in H. easy.
       - simpl. rewrite (shatter_word y) in *. simpl in *.
         case_eq b; case_eq (whd y); intros; rewrite H0, H1 in H; simpl in H.
         + simpl. apply IHx in H. 
           case_eq ((weqb x (wtl y))); intros; rewrite H2 in H; easy.
         + now simpl.
         + now simpl.
         + simpl. apply IHx in H. 
           case_eq ((weqb x (wtl y))); intros; rewrite H2 in H; easy.
Qed.

Lemma diseq_neg_eqw: forall (a b: list bool),
      length a = length b ->
      List_diseqb a b = true -> 
      negb (Word.weqb (ListToword a (length a)) (ListToword b (length a))) = true.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl in *. symmetry in H. rewrite empty_list_length in H. now rewrite H in H0.
       - simpl. case_eq b; intros. subst. now contradict H0.
         rewrite helper_strong. specialize (helper_strong l b0); intros.
         rewrite H1 in H. inversion H. rewrite H4, H2. simpl.
         case_eq (Bool.eqb xa b0); intros.
         case_eq (weqb (ListToword xsa (Datatypes.length l)) (ListToword l (Datatypes.length l))); intros.
         specialize (IHa l H4). rewrite <- H4 in H5.
         rewrite H5 in IHa. apply IHa.
         pose proof H0 as H0p.
         rewrite H1 in H0. simpl in H0. 
         case_eq (Bool.eqb xa false); intros. rewrite H6 in H0.
         case_eq xa; intros. rewrite H7 in H6. simpl in H6. now contradict H6.
         rewrite H7 in H3. case_eq b0; intros. rewrite H8 in H3. simpl in H3. now contradict H3.
         rewrite H8 in H0. now simpl in H0.
         case_eq xa; intros. rewrite H7 in H0. simpl in H0.
         rewrite H7 in H3. case_eq b0; intros. rewrite H8 in H0. now simpl in H0.
         rewrite H8 in H3. now contradict H3.
         rewrite H7 in H6. simpl in H6. now contradict H6.
         easy. easy.
Qed.


Lemma valid_check_bbDiseq lres : C.valid rho (check_bbDiseq lres).
Proof. 
      unfold check_bbDiseq.
      case_eq (Lit.is_pos lres); intro Heq; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
        intros f Heq2.
      case_eq (t_atom .[ f]); try (intros; now apply C.interp_true).

      intros [ | | | | | | |[ A B | A| | |  | ]|N|N|N|N|N|N|N];
         try (intros; now apply C.interp_true). intros n a b Heq3.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros c Heq4.
      case_eq c; try (intros; now apply C.interp_true).
      intros s0 la Heq5.
      case_eq (t_atom .[ b]); try (intros; now apply C.interp_true).
      intros c0 Heq6.
      case_eq c0; try (intros; now apply C.interp_true).
      intros s1 lb Heq7.
      case_eq (List_diseqb (wordToList la) (wordToList lb) && (s0=? n)%nat
              &&  (s1 =? n))%nat;
         try (intros; now apply C.interp_true). intros Heq8.

      unfold C.valid. simpl. rewrite orb_false_r.
      unfold Lit.interp. rewrite Heq.
      unfold Var.interp.
      rewrite wf_interp_form; trivial. rewrite Heq2. simpl.
      unfold Atom.interp_form_hatom, interp_hatom.
      rewrite Atom.t_interp_wf; trivial.
      rewrite Heq3. simpl.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite Heq4, Heq6. simpl.
      rewrite Heq5, Heq7. simpl.

        rewrite !andb_true_iff in Heq8.
        destruct Heq8 as (Heq8, Ha).
        destruct Heq8 as (Heq8, Hb).
        rewrite Nat.eqb_eq in Ha, Hb.
        generalize dependent n. intros n Heq3 Ha Hb. subst.

        rewrite Typ.nat_cast_refl. simpl.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        (* a *)
        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq4. easy. }
        specialize (@H0 H1). rewrite Heq4 in H0. simpl in H0.
        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Heq4 in Htia. simpl in Htia.
        unfold Bval in Htia.
        inversion Htia.

        generalize dependent v_vala.
        rewrite <- H3. intros.

        (* b *)
        pose proof (H b). 
        assert (b < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy. }
        specialize (@H2 H4). rewrite Heq6 in H2. simpl in H2.
        unfold get_type' in H2. unfold v_type in H2.
        case_eq (t_interp .[ b]).
        intros v_typeb v_valb Htib. rewrite Htib in H2.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        unfold Bval in Htib.
        inversion Htib.

        generalize dependent v_valb.
        rewrite <- H6. intros.

        (* f *)
        pose proof (H f). 
        assert (f < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq3. easy. }
        specialize (@H5 H7). rewrite Heq3 in H5. simpl in H5.
        unfold get_type' in H5. unfold v_type in H5.
        case_eq (t_interp .[ f]).
        intros v_typef v_valf Htif. rewrite Htif in H5.
        rewrite Atom.t_interp_wf in Htif; trivial.
        rewrite Heq3 in Htif. simpl in Htif.
        rewrite !Atom.t_interp_wf in Htif; trivial.
        rewrite Heq4, Heq6 in Htif.
        simpl in Htif.
        rewrite Typ.nat_cast_refl in Htif.
        unfold Bval in Htif.
        rewrite !andb_true_iff in H5.
        destruct H5. destruct H5.

        inversion Htif.

        generalize dependent v_valf.
        rewrite <- H11. intros.

        unfold Typ.i_eqb, Typ.interp_compdec. simpl.
        apply diseq_neg_eqw'. 
        easy.
Qed.

Lemma check_bbc_len: forall s (w: word s) (bs: list _lit),
 check_bbc w bs = true -> length (map (Lit.interp rho) bs) = s.
Proof. intros s w.
       induction w; intros.
       - simpl in H. case_eq bs; intros; subst; easy.
       - simpl in H. case_eq bs; intros; rewrite H0 in H.
         now contradict H.
         case_eq ( Lit.is_pos i); case_eq (t_form .[ Lit.blit i]); intros; rewrite H1, H2 in H;
         try now contradict H.
         case_eq b; intros. rewrite H3 in H.
         apply IHw in H. rewrite map_length in *. simpl. now rewrite H.
         rewrite H3 in H. now contradict H.
         case_eq b; intros. rewrite H3 in H. now contradict H.
         rewrite H3 in H. apply IHw in H. rewrite map_length in *. simpl. now rewrite H.
Qed.

Lemma check_bbc': forall s (w: word s) (bs: list _lit),
 length bs = s ->
 check_bbc w bs = true -> weqb w (ListToword (map (Lit.interp rho) bs) s) = true.
Proof. intros s w.
       induction w; intros.
       - now simpl.
       - simpl. case_eq bs; intros. rewrite H1 in *. simpl in *. now contradict H.
         simpl. rewrite H1 in H. simpl in H0.
         case_eq ( Lit.is_pos i); case_eq (t_form .[ Lit.blit i]); intros; rewrite H1, H2, H3 in H0;
         try now contradict H0.
         simpl in H. inversion H.
         specialize (helper_strong (map (Lit.interp rho) l) (Lit.interp rho i)); intros.
         rewrite map_length in H4. rewrite H5 in H4. rewrite H4.
         simpl.
         case_eq b; case_eq ((Lit.interp rho i)); intros.
         simpl. rewrite IHw. easy. easy. rewrite H7 in H0. easy.
         simpl. unfold Lit.interp in H6. rewrite H3 in H6. unfold Var.interp in H6.
         specialize (rho_interp (Lit.blit i)). rewrite H2 in rho_interp.
         simpl in rho_interp. rewrite rho_interp in H6. easy.
         simpl. rewrite H7 in H0. easy.
         simpl. rewrite H7 in H0. easy.

         simpl in H. inversion H.
         specialize (helper_strong (map (Lit.interp rho) l) (Lit.interp rho i)); intros.
         rewrite map_length in H4. rewrite H5 in H4. rewrite H4.
         simpl.
         case_eq b; case_eq ((Lit.interp rho i)); intros.
         simpl. rewrite IHw. easy. easy. rewrite H7 in H0. easy.
         simpl. rewrite H7 in H0. easy.
         simpl. unfold Lit.interp in H6. rewrite H3 in H6. unfold Var.interp in H6.
         specialize (rho_interp (Lit.blit i)). rewrite H2 in rho_interp.
         simpl in rho_interp. rewrite rho_interp in H6. easy.
         simpl. rewrite IHw. easy. easy. rewrite H7 in H0. easy.
Qed.

Lemma valid_check_bbConst lres : C.valid rho (check_bbConst lres).
Proof.
  unfold check_bbConst.
  case_eq (Lit.is_pos lres); intro Heq1; [ |now apply C.interp_true].
  case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
  intros a bs Heq0.
  case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
  intros c Ha.
  case_eq c; try (intros; now apply C.interp_true).
  intros s l Hc.
  case_eq (check_bbc l bs 
     (* && (N.of_nat (Datatypes.length l) =? N)%N*) );
  try (intros; now apply C.interp_true).
  intro Hcheck.
  unfold C.valid. simpl. rewrite orb_false_r.
  unfold Lit.interp. rewrite Heq1.
  unfold Var.interp.
  rewrite wf_interp_form; trivial. rewrite Heq0. simpl.

  assert (Hinterpa:
            (interp_form_hatom_word a = interp_word t_i (interp_atom (t_atom .[a])))).
  {
    unfold Atom.interp_form_hatom_word.
    unfold Atom.interp_hatom.
    rewrite !Atom.t_interp_wf; trivial.
  }
    rewrite Hinterpa.
    rewrite Ha, Hc. simpl.

 unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

 assert (((Datatypes.length (map (Lit.interp rho) bs))) = s).
  { pose proof Hcheck as Hcheck1.
    now apply check_bbc_len in Hcheck.
  }


 rewrite H.
 intros.

 rewrite Typ.nat_cast_refl.

 rewrite check_bbc'. easy. now rewrite map_length in H.
 easy.
Qed.


Lemma prop_check_ult: forall a b, 
  length a = length b ->
    Word.wltbNat (ListToword a (length a)) (ListToword b (length a))
    = 
    RAWBITVECTOR_LIST.ult_list a b. 
Proof. intros. rewrite wltbNat_true_iff. rewrite W2L_involutive.
       rewrite H, W2L_involutive. reflexivity. easy. easy.
Qed.


Lemma prop_check_ult2: forall bs1 bs2 bsres,
length bs1 = length bs2 ->
check_ult bs1 bs2 bsres = true ->
interp_carry (ult_big_endian_lit_list (rev bs1) (rev bs2)) = Lit.interp rho bsres.
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros.
         case bs2 in *.
         unfold check_ult in H0.
         simpl in *.
         case_eq (Lit.is_pos bsres). intros Hbsres.
         rewrite Hbsres in H0.
         case (Lit.is_pos bsres) in H0; rewrite eqb_spec in H0; now rewrite H0.
         intros. rewrite H1 in H0. now contradict H0.

         now contradict H.

       - intros.
         case bs2 in *.
         now contradict H.
         simpl.
         unfold check_ult,ult_lit_list in H0.
         simpl in H0.
         case_eq (Lit.is_pos bsres). intros Hbsres.
         rewrite Hbsres in H0.

         now apply prop_eq_carry_lit.

         intros. rewrite H1 in H0. now contradict H0.
Qed.


Lemma prop_check_ult3: forall bs1 bs2, 
  length bs1 = length bs2 ->
  RAWBITVECTOR_LIST.ult_list_big_endian
    (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)
  = interp_carry (ult_big_endian_lit_list bs1 bs2).
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1 ].
       - intros. simpl in *. 
         symmetry in H; rewrite empty_list_length in H.
         specialize (Lit.interp_false rho wf_rho).
         intros. unfold is_true in H0; now rewrite not_true_iff_false in H0.
       - intros.
         case_eq bs2. intros. rewrite H0 in *. now contradict H.
         intros. rewrite H0 in *.
         inversion H.
         rewrite !map_cons.
         simpl.
         case xsbs1 in *. simpl.
         case l in *. simpl. now rewrite Lit.interp_neg.
         now contradict H2.
         case l in *. simpl.
         now contradict H2. 
         rewrite !map_cons.
         unfold interp_carry.
         fold interp_carry.
         specialize (@IHbs1 (i1 :: l)).
         rewrite !map_cons in IHbs1.
         rewrite Lit.interp_neg.
         now rewrite IHbs1.
Qed.

(*
Lemma prop_check_slt: forall bs1 bs2, 
  length bs1 = length bs2 ->
  RAWBITVECTOR_LIST.slt_list_big_endian
    (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)
  = interp_carry (slt_big_endian_lit_list bs1 bs2).
Proof. intros.
       case bs1 in *. simpl.
       specialize (Lit.interp_false rho wf_rho).
         intros. unfold is_true in H0; now rewrite not_true_iff_false in H0.
       case bs2 in *.
         now contradict H.
         rewrite !map_cons.
         case bs1 in *. simpl.
         case bs2 in *. simpl. now rewrite Lit.interp_neg. 
         now contradict H.
         case bs2 in  *.
           now contradict H.
           unfold slt_big_endian_lit_list.
           unfold RAWBITVECTOR_LIST.slt_list_big_endian.
           rewrite !map_cons.
           unfold interp_carry.
           fold interp_carry.
           rewrite <- !map_cons.
           rewrite Lit.interp_neg.
           rewrite prop_check_ult.
           now apply f_equal.
           simpl.
           now inversion H.
Qed.

Lemma prop_check_slt2: forall bs1 bs2 bsres,
length bs1 = length bs2 ->
check_slt bs1 bs2 bsres = true ->
interp_carry (slt_big_endian_lit_list (rev bs1) (rev bs2)) = Lit.interp rho bsres.
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros.
         case bs2 in *.
         unfold check_slt in H0.
         simpl in *.
         case_eq (Lit.is_pos bsres). intros Hbsres.
         rewrite Hbsres in H0.
         case (Lit.is_pos bsres) in H0; rewrite eqb_spec in H0; now rewrite H0.
         intros. rewrite H1 in H0. now contradict H0.

         now contradict H.

       - intros.
         case bs2 in *.
         now contradict H.
         simpl.
         unfold check_slt, slt_lit_list in H0.
         simpl in H0.
         case_eq (Lit.is_pos bsres). intros Hbsres.
         rewrite Hbsres in H0.
         now apply prop_eq_carry_lit.

         intros. rewrite H1 in H0. now contradict H0.
Qed.
*)



Lemma prop_lit: forall bsres, 
Lit.is_pos bsres = true ->
Lit.interp 
  (interp_state_var (fun a0 : int => interp_bool t_i (t_interp .[ a0]))
     interp_form_hatom_word t_form) bsres =
Form.interp (fun a0 : int => interp_bool t_i (t_interp .[ a0]))
  interp_form_hatom_word t_form (t_form .[ Lit.blit bsres]).
Proof. intros.
       rewrite <- rho_interp.
       simpl.
       unfold Lit.interp, Var.interp.
       rewrite H.
       simpl. easy.
Qed.

Lemma prop_lit2: forall bsres, 
Lit.is_pos bsres = false ->
Lit.interp 
  (interp_state_var (fun a0 : int => interp_bool t_i (t_interp .[ a0]))
     interp_form_hatom_word t_form) bsres =
negb (Form.interp (fun a0 : int => interp_bool t_i (t_interp .[ a0]))
  interp_form_hatom_word t_form (t_form .[ Lit.blit bsres])).
Proof. intros.
       rewrite <- rho_interp.
       simpl.
       unfold Lit.interp, Var.interp.
       rewrite H.
       simpl. easy.
Qed.


Lemma valid_check_bbUlt s pos1 pos2 lres : C.valid rho (check_bbUlt s pos1 pos2 lres).
Proof.
      unfold check_bbUlt.
       case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
       case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
       case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
       case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
       case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
       case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true). intros a bsres Heq8.
       case_eq (Bool.eqb (Lit.is_pos a) (Lit.is_pos bsres)); try (intros; now apply C.interp_true). intros Heq12.
       case_eq (t_form .[ Lit.blit a]); try (intros; now apply C.interp_true). intros a3 Heq10.
       case_eq (t_atom .[ a3]); try (intros; now apply C.interp_true).

       intros [ | | | | | | | [ A B | A | | | | ]|N|N|N|N|N|N|N]; 
         try (intros; now apply C.interp_true).

       intros a1' a2' Heq9.
         case_eq ((a1 == a1') && (a2 == a2')); simpl; intros Heq15; try (now apply C.interp_true).

       case_eq (check_ult bs1 bs2 bsres &&
          ((Datatypes.length bs1) =? N)%nat &&
          ((Datatypes.length bs2) =? N)%nat); 
       simpl; intros Heq16; try (now apply C.interp_true).

       unfold C.valid. simpl.

       rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a3).
       assert (a3 < PArray.length t_atom).
       { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
       specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
       rewrite !andb_true_iff in H0. destruct H0. destruct H0.

       unfold get_type' in H0. unfold v_type in H0.
       case_eq (t_interp .[ a3]).
       intros v_typea3 v_vala3 Htia3. rewrite Htia3 in H0.
       case_eq (v_typea3);  intros; rewrite H4 in H0; try (now contradict H0).
       rename H4 into Hv.

       generalize (Hs s pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
       unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
       unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
       rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

       generalize (Hs s pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
       unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
       unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
       rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

       unfold get_type' in H2, H3. unfold v_type in H2, H3.
       case_eq (t_interp .[ a1']).
         intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
       case_eq (t_interp .[ a2']).
         intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
       simpl in v_vala2, v_vala2.

       apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

       (** case a1 = a1' and a2 = a2' **)
       rewrite andb_true_iff in Heq15.
       destruct Heq15 as (Heq15a1 & Heq15a2); rewrite eqb_spec in Heq15a1, Heq15a2
       ;rewrite Heq15a1, Heq15a2 in *.


        (* interp_form_hatom_bv a1' =
                 interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' =
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia1; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        unfold interp_word in HSp1.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp1.
        unfold interp_word in HSp1.

        (* interp_form_hatom_bv a2' =
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' =
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia2; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_word in HSp2.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp2.
        unfold interp_word in HSp2.

        generalize dependent v_vala1. generalize dependent v_vala2.

        rewrite H2, H3.

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (
        H100: ((Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        { 
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as ((Heq16a, Heq16b), Heq16c).
          rewrite Nat.eqb_eq in Heq16c.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H100.

        assert (
        H101: ((Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        { 
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as ((Heq16a, Heq16b), Heq16c).
          rewrite Nat.eqb_eq in Heq16b.
          now rewrite map_length.
        }
        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.

        rewrite Typ.cast_refl in *.

        intros.
        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.
        apply (@Bool.eqb_true_iff (Lit.interp rho a) (Lit.interp rho bsres)).

        unfold Lit.interp, Var.interp.
        rewrite rho_interp.
        rewrite Heq10. simpl.

        unfold Atom.interp_form_hatom.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1, Htia2. simpl.

        rewrite Form.wf_interp_form; trivial.
        simpl.
        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        rewrite HSp1, HSp2.

        case_eq (Lit.is_pos bsres).
        intros Hpos.

        rewrite !Typ.nat_cast_refl. simpl.
        rewrite !andb_true_iff in Heq16.
        destruct Heq16 as ((Heq16 & Heq16l) & Heq16r).
        rewrite <- H101.
        rewrite prop_check_ult.
        intros. unfold RAWBITVECTOR_LIST.ult_list.
        rewrite <- !map_rev.


        specialize (@prop_check_ult2  bs1 bs2 bsres); intros.
        specialize (@prop_check_ult3  (rev bs1) (rev bs2)); intros.
        rewrite H9, H8.
        unfold Atom.interp_form_hatom, interp_form_hatom_word.
        now rewrite prop_lit.
        rewrite map_length in H100, H101. now rewrite H100, H101.
        exact Heq16.
        rewrite map_length in H100, H101. rewrite !rev_length.
        now rewrite H100, H101.
        rewrite map_length in H100, H101. rewrite !map_length.
        now rewrite H100, H101.

        intros.

        contradict Heq16.
        unfold check_ult. rewrite H8. easy.
Qed.

(** incorporated down here *)


(*
Lemma prop_check_slt: forall a b, 
  length a = length b ->
    Word.wsltbZ (ListToword a (length a)) (ListToword b (length a))
    = 
    RAWBITVECTOR_LIST.slt_list a b. 
Proof. intros. rewrite <- wsltZ_true_iff. rewrite W2L_involutive.
       rewrite H, W2L_involutive. reflexivity. easy. easy.
Qed.

*)


(*


Let a : list bool := [true; false; true; false; true; true; true; true].
Let b : list bool := [true; true; false; true; true; false; true; true].

Let c : list bool := [false; true; false; true; false; true; false; true; true; false; false; false ;true; false; false ].
Let d : list bool := [true; true; false; false; false; true; true; true; false; false ;true; false; true; false; true ].
Let n := (length b)%nat.
Let n1 := (n - 1)%nat.
Let m: Z := Z.of_nat(length a).
Let k := (length d)%nat.

Compute
    Word.wltb (ListToword a (length a)) (ListToword b (length a))
    = 
    RAWBITVECTOR_LIST.ult_list a b. 

Compute
(posToWord (Datatypes.length a) 100)~1 = posToWord (S (Datatypes.length a)) (Pos.pred_double 100).

Compute
natToWord (Datatypes.length a)
  (Natpow2 (Datatypes.length a) - wordToNat (ListToword a (Datatypes.length a)) - 1) =
ListToword (map negb a) (Datatypes.length a).

Compute
wnegNat (ListToword a (length a)) = ListToword (RAWBITVECTOR_LIST.twos_complement a) (length a).

Compute
Word.wneg (ListToword a (length a)) = ListToword (RAWBITVECTOR_LIST.twos_complement a) (length a).

Compute
RAWBITVECTOR_LIST.ult_list_big_endian (rev a) (rev b) =
RAWBITVECTOR_LIST.ult_list_big_endian ((rev a) ++ c) ((rev b) ++ c).

Compute
(wordToN (ListToword a n) <?
 wordToN (ListToword b n))%N = RAWBITVECTOR_LIST.ult_list_big_endian (rev a) (rev b).

Compute
RAWBITVECTOR_LIST.ult_list_big_endian (rev (true :: a)) (rev (true :: b)) =
RAWBITVECTOR_LIST.ult_list_big_endian (rev a) (rev b).

Compute
RAWBITVECTOR_LIST.ult_list_big_endian (rev (true :: true :: a)) (rev (true :: true :: b)) =
RAWBITVECTOR_LIST.ult_list_big_endian (rev a) (rev b).

Compute
RAWBITVECTOR_LIST.mult_bool_step_k_h a (false :: a) true 0 =
RAWBITVECTOR_LIST.mult_bool_step_k_h a (false :: removelast a) true 0.

Compute
(RAWBITVECTOR_LIST.add_list_ingr a a false) = false :: (removelast a).

Compute
RAWBITVECTOR_LIST.mult_bool_step_k_h a (false :: a) false 0 =
RAWBITVECTOR_LIST.mult_bool_step_k_h a (RAWBITVECTOR_LIST.mult_bool_step_k_h a a false 0) false 0.



Compute
RAWBITVECTOR_LIST.mult_bool_step (true :: a) (true :: b)
  (true :: RAWBITVECTOR_LIST.add_list_ingr a (true :: a) false) 2
  (Datatypes.length a) =
RAWBITVECTOR_LIST.mult_bool_step (true :: a) (true :: b) (true :: a) 1
  (Datatypes.length a).


Compute
           (RAWBITVECTOR_LIST.mult_bool_step a b a 1
              (Datatypes.length a)) =
           (RAWBITVECTOR_LIST.mult_bool_step a b (RAWBITVECTOR_LIST.mk_list_false (length a)) 0
              (Datatypes.length a)).


Compute
RAWBITVECTOR_LIST.mult_bool_step (true :: true :: a) (true :: b)
  (true :: false :: RAWBITVECTOR_LIST.add_list_ingr a (true :: a) true) 2
  (Datatypes.length a) =
true
:: RAWBITVECTOR_LIST.add_list b
     (RAWBITVECTOR_LIST.mult_bool_step (true :: a) (true :: b) (true :: a) 1
        (Datatypes.length a)).

Compute
RAWBITVECTOR_LIST.mult_bool_step_k_h a
                 (true :: a) true 0  = 
RAWBITVECTOR_LIST.add_list_ingr a
                 (true :: a) true.


Compute
RAWBITVECTOR_LIST.mult_bool_step (true :: true :: a) (false :: b)
  (false :: true :: match a with
                    | [] => []
                    | _ :: _ => true :: removelast a
                    end) 2 (Datatypes.length a) =
false
:: RAWBITVECTOR_LIST.add_list b
     (RAWBITVECTOR_LIST.mult_bool_step (true :: a) (false :: b)
        (false :: RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) 1
        (Datatypes.length a)).

Compute
RAWBITVECTOR_LIST.mult_bool_step_k_h (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a))
  (false :: a) false 0 = removelast (false :: a).

Compute
RAWBITVECTOR_LIST.add_list_ingr (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a))
  (false :: a) false = removelast (false :: a).

Compute
RAWBITVECTOR_LIST.mult_bool_step_k_h
           (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) 
           (true :: a) false 0 =
RAWBITVECTOR_LIST.add_list_ingr
           (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) 
           (true :: a) false.

Compute
RAWBITVECTOR_LIST.mult_bool_step (true :: a) (false :: b)
  (false :: RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) 1 (Datatypes.length a) =
false :: RAWBITVECTOR_LIST.add_list b (RAWBITVECTOR_LIST.mult_list_carry a (false :: b) (Datatypes.length a)).


Let n2 := ((listTonat a + listTonat a + (listTonat b + listTonat b) * S (listTonat a + listTonat a)) - 1)%nat.

Compute n2.

Eval simpl in RAWBITVECTOR_LIST.mult_bool_step (true :: b) (true :: a)
  (true :: RAWBITVECTOR_LIST.and_with_bool b true) 1 n1 =
mod2 n2 :: natTolist (S n1) (S (Nat.div2 n2)).

Compute Word.wmult (ListToword a n) (ListToword b n) = 
ListToword (RAWBITVECTOR_LIST.bvmult_bool a b n) n.
*)



(** BV MULTIPLICATION CHECKER WORDS*)
Lemma prop_forallb2: forall {A B} {f: A -> B -> bool} l1 l2, 
forallb2 f l1 l2 = true -> length l1 = length l2. 
Proof. intros A B f l1.
       induction l1 as [ | xl1 xsl1 IHl1].
       - intros. simpl in H.
         case l2 in *. easy.
         now contradict H.
       - intros. simpl in H.
         case l2 in *.
         now contradict H.
         simpl.
         rewrite andb_true_iff in H. destruct H.
         apply IHl1 in H0. now rewrite H0.
Qed.

Lemma prop_and_with_bit: forall a b, map interp_carry (and_with_bit a b) = 
                          RAWBITVECTOR_LIST.and_with_bool (map (Lit.interp rho) a) (Lit.interp rho b).
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. now simpl in *.
       - intros. simpl in *. now rewrite IHa.
Qed.

Lemma prop_mult_step_k_h: forall a b c k, 
                          map interp_carry (mult_step_k_h a b c k) = 
                          RAWBITVECTOR_LIST.mult_bool_step_k_h
                            (map interp_carry a) (map interp_carry b)
                            (interp_carry c) k.
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. case b.
         now simpl.
         intros. now simpl.
       - intros. case b in *. simpl.
         rewrite IHa. now simpl.
         intros. simpl.
         case (k - 1 <? 0)%Z.
         simpl. apply f_equal.
         apply IHa.
         rewrite <- map_cons. simpl. apply f_equal.
         apply IHa.
Qed.

Lemma prop_interp_firstn: forall xk' a, map (Lit.interp rho) (List.firstn xk' a) = (List.firstn xk' (map (Lit.interp rho) a)).
Proof.   intro xk'0.
          induction xk'0.
           + intros. now simpl. 
           + intros. simpl.
             case a. now simpl.
             intros. simpl. apply f_equal. apply IHxk'0.
Qed.

Lemma map_firstn: forall A B n (l: list A) (f:A -> B), firstn n (map f l) = map f (firstn n l). 
Proof.
  intros A B n.
  induction n; intro l; induction l; try now simpl.
  intros. simpl. apply f_equal. apply IHn.
Qed.

Lemma prop_mult_step: forall a b res k k',
      (map interp_carry (mult_step a b res k k')) = 
      RAWBITVECTOR_LIST.mult_bool_step (map (Lit.interp rho) a) (map (Lit.interp rho) b)
                                       (map interp_carry res) k k'.
Proof. intros. revert a b res k.
       assert (false = (Lit.interp rho (Lit._false))) as Ha.
       {
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H. rewrite not_true_iff_false in H.
         now rewrite H.
       }

       assert (false = interp_carry (Clit Lit._false)).
       {
         unfold interp_carry.
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H. rewrite not_true_iff_false in H.
         now rewrite H.
       }

       assert ([] = map (interp_carry) []). { now simpl. }

       induction k' as [ | xk' xsk' IHk' ].
       - intros.
         case a. simpl. rewrite H; apply prop_mult_step_k_h.
         intros. simpl. rewrite H. rewrite prop_mult_step_k_h. simpl. now rewrite map_nth.
       - intros. simpl.
         rewrite xsk', prop_mult_step_k_h, prop_and_with_bit.
         rewrite <- map_nth, <- Ha, <- H.
         case a. now simpl. simpl. intros.
         case l. now simpl. simpl. intros.
         case xk'. now simpl. intros. now rewrite map_firstn.
Qed.

Lemma prop_bblast_bvmult: forall a b n,
                          (map interp_carry (bblast_bvmult a b n)) =
                          RAWBITVECTOR_LIST.bvmult_bool (map (Lit.interp rho) a)  
                                                        (map (Lit.interp rho) b)
                                                        n.
Proof. intros.
       revert a b.
       induction n.
       - intros. simpl. rewrite prop_and_with_bit.
         rewrite <- map_nth.
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H. rewrite not_true_iff_false in H.
         now rewrite H.
       - intros. simpl.
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H. rewrite not_true_iff_false in H.
         case n in *.
         rewrite prop_and_with_bit; rewrite <- map_nth; now rewrite H.
         rewrite prop_mult_step; rewrite prop_and_with_bit; rewrite <- map_nth; now rewrite H.
Qed.

Lemma prop_mult_step_k_h_len: forall a b c k,
length (mult_step_k_h a b c k) = length a .
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. simpl. easy.
       - intros.
         case b in *. simpl. rewrite IHa. simpl. omega.
         simpl. case (k - 1 <? 0)%Z; simpl; now rewrite IHa.
Qed.

Lemma prop_mult_step3: forall k' a b res k, 
                         length (mult_step a b res k k') = (length res)%nat.
Proof. intro k'.
       induction k'.
       - intros. simpl. rewrite prop_mult_step_k_h_len. simpl. omega.
       - intros. simpl.
         rewrite IHk'. rewrite prop_mult_step_k_h_len. simpl; omega.
Qed.

Lemma prop_and_with_bit2: forall bs1 b, length (and_with_bit bs1 b) = length bs1.
Proof. intros bs1.
       induction bs1.
       - intros. now simpl.
       - intros. simpl. now rewrite IHbs1.
Qed.

Lemma check_bvmult_length: forall bs1 bs2,
  let bsres0 := bblast_bvmult bs1 bs2 (length bs1) in
  length bs1 = length bs2 -> length bs1 = length bsres0.
Proof. intros. unfold bblast_bvmult in bsres0.
       case_eq (length bs1). intros. unfold bsres0.
       rewrite H0.
       specialize (@prop_and_with_bit2 bs1 (nth 0 bs2 Lit._false)). intros.
       now rewrite H1.
       intros. unfold bsres0. rewrite H0.
       case n in *.
       simpl. rewrite prop_and_with_bit2. auto.
       rewrite prop_mult_step3. rewrite prop_and_with_bit2. auto.
Qed.

Lemma check_bvmult_length2: forall bs1 bs2 bsres,
  check_mult bs1 bs2 bsres = true -> length bs1 = length bs2 .
Proof. intros bs1.
       induction bs1.
       - intros. case bs2 in *.
         + easy.
         + unfold check_mult in H.
           now contradict H.
       - intros. unfold check_mult in H.
         case_eq (Nat_eqb (Datatypes.length (a :: bs1)) ((Datatypes.length bs2))).
         intros. now apply Nat.eqb_eq in H0.
         intros. rewrite H0 in H. now contradict H.
Qed.

Lemma prop_main: forall bs1 bs2 bsres,
                 check_mult bs1 bs2 bsres = true ->
                 map interp_carry (bblast_bvmult bs1 bs2 (Datatypes.length (map (Lit.interp rho) bs1))) =
                 map (Lit.interp rho) bsres.
Proof. intros. unfold check_mult in H.
       case_eq (Nat_eqb (Datatypes.length bs1) (Datatypes.length bs2)). intros.
       rewrite H0 in H. apply prop_eq_carry_lit2 in H.
       rewrite map_length.
       now rewrite H.
       intros. rewrite H0 in H. now contradict H.
Qed.



Lemma mbs_invol1: forall (a: list bool) m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a [] false m = a.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. now rewrite IHa.
Qed.

Lemma mbs_invol1t: forall (a: list bool) m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a [] true m = a.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. now rewrite IHa.
Qed.

Lemma mbs_invol3: forall (a: list bool) m,
 RAWBITVECTOR_LIST.mult_bool_step_k_h a [false] false m = a.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq ((m - 1 <? 0)%Z); intros.
         case_eq xa; intros. simpl. now rewrite mbs_invol1.
         simpl. now rewrite mbs_invol1.
         now rewrite IHa.
Qed.

Lemma mbs_invol5: forall (a: list bool),
RAWBITVECTOR_LIST.mult_bool_step_k_h a [true] false
  (Z.of_nat (Datatypes.length a)) = a.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq (Pos.of_succ_nat (Datatypes.length xsa)); intros.
         + simpl. admit.
         + simpl. admit.
         + simpl. admit.
Admitted.

Lemma mbs_invol4: forall (a: list bool),
RAWBITVECTOR_LIST.mult_bool_step_k_h a [] true (Z.of_nat (length a)) =
RAWBITVECTOR_LIST.mult_bool_step_k_h a [true] false (Z.of_nat (length a)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - now rewrite mbs_invol1t, mbs_invol5.
Qed. 

Lemma mklfS: forall n,
(false :: RAWBITVECTOR_LIST.mk_list_false n) =
(RAWBITVECTOR_LIST.mk_list_false (S n)%nat).
Proof. intro n.
       induction n; now simpl.
Qed.

Lemma add_mklfS: forall n,
RAWBITVECTOR_LIST.add_list_ingr (RAWBITVECTOR_LIST.mk_list_false n)
        (RAWBITVECTOR_LIST.mk_list_false (S n)) false =
(RAWBITVECTOR_LIST.mk_list_false n).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl in *. now rewrite IHn.
Qed.


Lemma mbs_invol2: forall a n m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a (RAWBITVECTOR_LIST.mk_list_false n) false m = a.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq n; intros. simpl. now rewrite mbs_invol1.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         case_eq xa; intros. simpl. apply f_equal.
         specialize (IHa (n0)%nat (m-1)%Z). now rewrite IHa.
         simpl. apply f_equal. now rewrite IHa.
         apply f_equal. rewrite mklfS. now rewrite IHa.
Qed.

Lemma mbs_invol: forall (a b: list bool) m,
(RAWBITVECTOR_LIST.mult_bool_step_k_h b (natTolist (Datatypes.length a) 0) false m) = b.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl. now rewrite mbs_invol1.
       - simpl. case_eq b; intros.
         now simpl.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         case_eq b0; intros. simpl. apply f_equal.
         now rewrite IHa.
         simpl. apply f_equal. now rewrite IHa.
         apply f_equal. specialize (IHa l).
         rewrite nlf in *. simpl. rewrite mklfS.
         now rewrite mbs_invol2.
Qed.

Lemma add_eq_empty_ft: forall a m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a [] false m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a [] true m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. now rewrite IHa.
Qed.


Lemma add_eq_tf_ff_ft0: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (true :: RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) false) false 
  m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (false :: RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) false) true 
  m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros. simpl.
         case_eq ((m - 1 <? 0)%Z); intros.
         case_eq xa; intros. simpl. now apply f_equal.
         simpl. easy.
         specialize (IHa []). simpl in IHa. now rewrite IHa.
         case_eq ((m - 1 <? 0)%Z); intros.
         case_eq xa; case_eq b0; intros. simpl. now apply f_equal.
         now simpl. now simpl. now simpl. now rewrite IHa.
Qed.

Lemma add_eq_f_t0: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (false :: RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) true) false
  m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (true :: RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) false) true
  m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros. simpl.
         case_eq ((m - 1 <? 0)%Z); intros.
         case_eq xa; intros. simpl. apply f_equal.
         now rewrite add_eq_empty_ft.
         simpl. now rewrite add_eq_empty_ft.
         specialize (IHa []). simpl in IHa. now rewrite IHa.
         case_eq ((m - 1 <? 0)%Z); intros.
         case_eq xa; case_eq b0; intros. simpl. apply f_equal.
         now rewrite IHa.
         simpl. apply f_equal. now rewrite add_eq_tf_ff_ft0.
         simpl. now rewrite IHa.
         simpl. apply f_equal. now rewrite add_eq_tf_ff_ft0.
         now rewrite IHa.
Qed.


Lemma add_eq_tf_ft0: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) true) false 
  m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) false) true 
  m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - case_eq b; intros. simpl. specialize (IHa [] m). simpl in IHa.
         now rewrite IHa.
         simpl. case_eq xa; case_eq b0; intros.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         apply f_equal. now rewrite IHa.
         apply f_equal. now rewrite add_eq_f_t0.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         easy. now rewrite add_eq_tf_ff_ft0.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         now rewrite IHa.
         simpl. now rewrite add_eq_f_t0.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         easy. now rewrite add_eq_tf_ff_ft0.
Qed.

Lemma helper_conv_tf21: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) true) false 
  m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) false) true 
  m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - case_eq b; intros. simpl. rewrite (IHa []). now simpl.
         case_eq xa; case_eq b0; intros.
         + simpl. case_eq ((m - 1 <? 0)%Z); intros.
           now rewrite IHa. 
           simpl. apply f_equal.
           now rewrite add_eq_f_t0.
         + simpl. case_eq ((m - 1 <? 0)%Z); intros. easy.
           simpl. apply f_equal.
           now rewrite add_eq_tf_ff_ft0.
         + simpl. case_eq ((m - 1 <? 0)%Z); intros.
           now rewrite IHa.
           simpl. apply f_equal.
           now rewrite add_eq_f_t0.
         + simpl. case_eq (m - 1 <? 0)%Z; intros.
           easy.
           now rewrite add_eq_tf_ff_ft0.
Qed.


Lemma helper_conv_tf22: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a b true m
=
RAWBITVECTOR_LIST.mult_bool_step_k_h a 
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 1) false) false m.
Proof. intro a.
       induction a as [  | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros.
         simpl. rewrite IHa. now simpl.
         simpl. 
         case_eq ((m - 1 <? 0)%Z); intros.
         case_eq xa; case_eq b0; intros.
         simpl. apply f_equal. rewrite IHa, helper_conv_tf. reflexivity.
         simpl. apply f_equal. rewrite IHa. rewrite <- helper_conv_tf.
         now rewrite helper_conv_tf21.
         simpl. apply f_equal. rewrite IHa. rewrite <- helper_conv_tf.
         now rewrite helper_conv_tf21.
         simpl. apply f_equal. rewrite nlf.
         rewrite RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity.
         lia.

         simpl.
         case_eq xa; case_eq b0; intros.
         simpl. apply f_equal. rewrite IHa. now simpl. 

         simpl. apply f_equal. rewrite IHa. now simpl.
         simpl. apply f_equal. rewrite IHa. now simpl.
         simpl. apply f_equal. rewrite IHa. now simpl.
Qed.

Lemma add_eq_ff_tf10: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 1) false) false 
  m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) true) false 
  m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros. now simpl.
         simpl. case_eq xa; case_eq b0; intros.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         now rewrite add_eq_tf_ft0.
         easy.
         simpl. case_eq ((m - 1 <? 0)%Z); intros; easy.
         simpl. case_eq ((m - 1 <? 0)%Z); intros; easy.
         simpl. case_eq ((m - 1 <? 0)%Z); intros; easy.
Qed.

Lemma add_eq_ff_ft10: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 1) false) false 
  m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 0) false) true 
  m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros. simpl. now rewrite add_eq_empty_ft.
         simpl. case_eq xa; case_eq b0; intros.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         now rewrite add_eq_tf_ft0.
         now rewrite add_eq_f_t0.
         simpl. case_eq ((m - 1 <? 0)%Z); intros. easy.
         simpl. now rewrite add_eq_tf_ff_ft0.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         now rewrite helper_conv_tf21.
         now rewrite add_eq_f_t0.
         simpl. case_eq ((m - 1 <? 0)%Z); intros.
         easy. now rewrite add_eq_tf_ff_ft0.
Qed.

Lemma f_int1: forall m:Z,
(m <=? 0)%Z = true -> ((m-1) <=? 0)%Z = true.
Proof. intro m.
       induction m; intros.
       - simpl. auto.
       - apply Zle_is_le_bool in H.
         apply Zle_is_le_bool. lia.
       - apply Zle_is_le_bool. apply Zle_is_le_bool in H. lia.
Qed.

Lemma f_int2: forall m:Z,
(m - 1 - 1 <? 0)%Z = true ->
(m - 1 <? 0)%Z = false -> m = 1%Z.
Proof. intro m.
       induction m ; intros.
       - simpl in *. now contradict H0.
       - apply Zlt_is_lt_bool in H. 
         simpl in *. case_eq p; intros.
         subst. simpl in *. now contradict H.
         subst. rewrite Pos.pred_double_spec in H.
         contradict H. simpl. case_eq (Pos.pred_double p0); intros.
         lia. lia. lia. easy.
      - apply Zlt_is_lt_bool in H. 
         simpl in *. now contradict H0.
Qed.

Lemma add_eq_f: forall a b m,
(m <=? 0)%Z = true ->
RAWBITVECTOR_LIST.mult_bool_step_k_h a b false (m - 1) =
RAWBITVECTOR_LIST.mult_bool_step_k_h a b false m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros.
         now rewrite IHa.
         case_eq  (m - 1 - 1 <? 0)%Z; intros.
         case_eq (m - 1 <? 0)%Z; intros.
         case_eq xa; case_eq b0; intros. simpl. 
         rewrite !helper_conv_tf22. rewrite IHa. reflexivity. now apply f_int1 in H.
         simpl. rewrite IHa. reflexivity. now apply f_int1 in H.
         simpl. rewrite IHa. reflexivity. now apply f_int1 in H.
         simpl. rewrite IHa. reflexivity. now apply f_int1 in H.
         specialize (f_int2 H1 H2); intros. subst. simpl in *.
         now contradict H. 
         case_eq (m - 1 <? 0)%Z; intros.
         specialize (Zle_cases m 0); intros. rewrite H in H3.
           case_eq m; intros.
           + subst. now contradict H2.
           + subst. now contradict H2.
           + subst. now contradict H.
           + case_eq m; intros.
             ++ subst. now contradict H2.
             ++ subst. now contradict H2.
             ++ subst. now contradict H.
Qed.

Lemma add_eq_t: forall a b m,
(m <=? 0)%Z = true ->
RAWBITVECTOR_LIST.mult_bool_step_k_h a b true (m - 1) =
RAWBITVECTOR_LIST.mult_bool_step_k_h a b true m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros.
         now rewrite IHa.
         case_eq  (m - 1 - 1 <? 0)%Z; intros.
         case_eq (m - 1 <? 0)%Z; intros.
         case_eq xa; case_eq b0; intros. simpl. 
         simpl. rewrite IHa. reflexivity. now apply f_int1 in H.
         simpl. rewrite IHa. reflexivity. now apply f_int1 in H.
         simpl. rewrite IHa. reflexivity. now apply f_int1 in H.
         simpl. rewrite add_eq_f. reflexivity. now apply f_int1 in H.

         specialize (f_int2 H1 H2); intros. subst. simpl in *.
         now contradict H. 
         case_eq (m - 1 <? 0)%Z; intros.
         specialize (Zle_cases m 0); intros. rewrite H in H3.
           case_eq m; intros.
           + subst. now contradict H2.
           + subst. now contradict H2.
           + subst. now contradict H.
           + case_eq m; intros.
             ++ subst. now contradict H2.
             ++ subst. now contradict H2.
             ++ subst. now contradict H.
Qed.


Lemma add_eq_f_f_f: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr (true :: b) (natTolist (S (Datatypes.length b)) 1) false)
  false m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (false :: RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 1) false)
  false m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - case_eq b; intros. simpl.
         case_eq ((m - 1 <? 0)%Z); intros; now simpl.

         simpl. case_eq ((m - 1 <? 0)%Z); intros. 
         case_eq xa; case_eq b0; intros; now simpl.
         easy.
Qed.

(*
Lemma add_eq_f_f_f: forall a b m,
(length a = S (length b)) ->
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr (true :: b) (natTolist (Datatypes.length a) 1) false)
  false m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (false :: RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 1) false)
  false m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - case_eq b; intros. simpl.
         case_eq ((m - 1 <? 0)%Z); intros; now simpl.

         simpl. case_eq ((m - 1 <? 0)%Z); intros;
         rewrite H0 in H; inversion H; rewrite H3; now simpl.
Qed.
*)

Lemma add_eq_f_f: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a b false m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b 
  (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length b)) false) false m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros.
         now simpl.
         case_eq ((m - 1 <? 0)%Z); intros.
         case_eq xa; case_eq b0; intros.
         simpl. apply f_equal. 
         rewrite RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity. lia.
         simpl. apply f_equal. now rewrite IHa.
         simpl. apply f_equal. now rewrite IHa.
         simpl. apply f_equal. now rewrite IHa.
         case_eq xa; case_eq b0; intros;
         simpl; apply f_equal; rewrite IHa; now simpl.
Qed.


Lemma add_eq_f_t: forall a b m,
(length a = S (length b)) ->
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr (false :: b) (natTolist (Datatypes.length a) 1) false) false m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (true
   :: RAWBITVECTOR_LIST.add_list_ingr b (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) false) false m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl.
         case_eq ( (m - 1 <? 0)%Z); intros.
         case_eq xa; intros. simpl. apply f_equal.
         rewrite mklfS, nlf.
         rewrite !RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity.
         inversion H. rewrite H3. lia.
         inversion H. lia.
         simpl. apply f_equal.
         rewrite mklfS, nlf.
         rewrite !RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity.
         inversion H. rewrite H3. lia.
         inversion H. lia.
         simpl. apply f_equal.
         rewrite mklfS, nlf.
         rewrite !RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity.
         inversion H. rewrite H2. lia.
         inversion H. lia.
Qed.

Lemma add_eq_f_f_t: forall a b m,
(length a > length b)%nat ->
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr (false :: b) (natTolist (Datatypes.length a) 0) true)
  false m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (true :: RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length a) 0) false)
  false m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl.
         case_eq ( (m - 1 <? 0)%Z); intros.
         case_eq xa; intros. simpl. apply f_equal.
         rewrite nlf, mklfS.
         rewrite !RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity.
         inversion H. rewrite H3. lia.
         inversion H. lia.  inversion H5. lia. lia. inversion H. lia. lia. 
         simpl. apply f_equal.
         rewrite nlf, mklfS.
         rewrite !RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity.
         inversion H. rewrite H3. lia.
         inversion H. lia. lia. inversion H. lia. lia.
         simpl. apply f_equal.
         rewrite nlf, mklfS.
         rewrite !RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity.
         inversion H. rewrite H2. lia.
         inversion H. lia.
         lia. inversion H. lia. lia.
Qed.

Lemma add_eq1: forall a b m,
RAWBITVECTOR_LIST.mult_bool_step_k_h a b true m =
RAWBITVECTOR_LIST.mult_bool_step_k_h a
  (RAWBITVECTOR_LIST.add_list_ingr b (natTolist (Datatypes.length b) 1) false) false m.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros. subst. simpl. now rewrite add_eq_empty_ft. 
         case_eq (m - 1 <? 0)%Z; intros. simpl. 
         case_eq xa; case_eq b0; intros. simpl.
         apply f_equal. now rewrite IHa, add_eq_ff_tf10.
         simpl. apply f_equal. now rewrite IHa, add_eq_ff_ft10.
         simpl. apply f_equal. now rewrite IHa, add_eq_ff_tf10.
         simpl. apply f_equal.
         rewrite nlf.
         rewrite !RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_r. reflexivity. lia.
         case_eq xa; case_eq b0; intros; simpl;
         apply f_equal; rewrite IHa; now simpl.
Qed.

Lemma add_eq: forall a b,
(length a = length b)%nat ->
RAWBITVECTOR_LIST.mult_bool_step_k_h a b false 0 =
RAWBITVECTOR_LIST.add_list_ingr a b false.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq b; intros. subst. now contradict H.
         simpl. case_eq xa; case_eq b0; intros.
         simpl. apply f_equal.
         rewrite helper_conv_tf2. rewrite <- IHa.
         simpl. rewrite add_eq1. assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H3, add_eq_f. rewrite H0 in H. inversion H. reflexivity.
         apply Zle_is_le_bool. lia.
         remember (@RAWBITVECTOR_LIST.add_list_carry_length_eq l (natTolist (Datatypes.length xsa) 1) false).
         rewrite H0 in H. inversion H. rewrite H4 at 1.
         apply e. rewrite len_n2l. easy.        
         rewrite H0 in H. inversion H. easy.
         simpl. rewrite <- IHa. apply f_equal. 
         assert ((0-1)%Z = (-1)%Z). { lia. } rewrite <- H3.
         now rewrite add_eq_f.
         rewrite H0 in H. inversion H. easy.
         simpl. apply f_equal. rewrite <- IHa.
         assert ((0-1)%Z = (-1)%Z). { lia. } rewrite <- H3.
         now rewrite add_eq_f.
         rewrite H0 in H. inversion H. easy.
         simpl. apply f_equal. rewrite <- IHa.
         assert ((0-1)%Z = (-1)%Z). { lia. } rewrite <- H3.
         now rewrite add_eq_f.
         rewrite H0 in H. inversion H. easy.
Qed.

Lemma awb_t: forall a,
RAWBITVECTOR_LIST.and_with_bool a true = a.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. now rewrite IHa.
Qed.

Lemma awb_f: forall a,
RAWBITVECTOR_LIST.and_with_bool a false = RAWBITVECTOR_LIST.mk_list_false (length a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. now rewrite IHa.
Qed.

Lemma fn_eq: forall n (a: list bool),
n = length a ->
firstn n a = a.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - simpl in *. symmetry in H. now rewrite empty_list_length in H.
       - simpl. case_eq a; intros.
         + easy.
         + rewrite IHn. easy.
           rewrite H0 in H. now inversion H.
Qed.


Lemma len_fst: forall n: nat,
(@firstn bool n []) = [].
Proof. intro n.
       induction n as [ | xn IHn ]; intros; now simpl.
Qed.

Lemma fstn_ge: forall (a: list bool) (n: nat),
n > (length a) ->
(@firstn bool n a) = a.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now rewrite len_fst.
       - case_eq n; intros. subst. now contradict H.
         simpl. rewrite IHa. reflexivity.
         subst. simpl in H. inversion H. lia. lia.
Qed.


Lemma mbs_mlf: forall n m,
RAWBITVECTOR_LIST.mult_bool_step_k_h (RAWBITVECTOR_LIST.mk_list_false n)
        (false :: RAWBITVECTOR_LIST.mk_list_false m) false 0
= RAWBITVECTOR_LIST.mk_list_false n.
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl. apply f_equal.
         specialize (IHn (m - 1)%nat).
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H, add_eq_f.
         rewrite mklfS in IHn.
         case_eq m; intros. simpl. now rewrite mbs_invol1.
         assert ((S (m - 1)) = m%nat). { lia. }
         rewrite H1 in IHn. now rewrite <- H0.
         apply Zle_is_le_bool. lia.
Qed.

Lemma and_t_eq: forall a,
(RAWBITVECTOR_LIST.and_with_bool a true) = a.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. now rewrite IHa.
Qed.


Lemma add_eq_fta: forall a,
RAWBITVECTOR_LIST.add_list_ingr a (false :: a) true =
RAWBITVECTOR_LIST.add_list_ingr a (true :: a) false.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq xa; intros; now simpl.
Qed.


Lemma add_eq_fta2: forall a,
RAWBITVECTOR_LIST.mult_bool_step_k_h a (true :: a) false 0 =
RAWBITVECTOR_LIST.mult_bool_step_k_h a (false :: a) true 0.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq xa; intros; now simpl.
Qed.


Lemma mult_f_eq2_1_1_1: forall a,
RAWBITVECTOR_LIST.add_list_ingr (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a))
  (true :: a) false = match a with
                      | [] => []
                      | _ :: _ => true :: removelast a
                      end.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq xa; intros. now rewrite IHa.
         apply f_equal. case_eq xsa; intros. now simpl.
         case_eq b; intros. simpl. subst. simpl in *.
         inversion IHa. now rewrite H0.
         subst. simpl in *. inversion IHa. now rewrite H0.
Qed.

Lemma mult_f_eq2_1_1: forall a,
RAWBITVECTOR_LIST.add_list_ingr (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a))
  (false :: a) false = removelast (false :: a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. apply f_equal.
         case_eq xsa; intros. now simpl.
         case_eq xa; case_eq b; intros. simpl. rewrite mult_f_eq2_1_1_1.
         easy. simpl. subst. simpl in *. now inversion IHa.
         simpl. subst. simpl in *. easy.
         simpl. subst. simpl in *. easy.
Qed.

Lemma mult_f_eq2_2_1_1: forall a,
RAWBITVECTOR_LIST.mult_bool_step_k_h (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a))
  (true :: a) false 0 = match a with
                          | [] => []
                          | _ :: _ => true :: removelast a
                          end.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. case_eq xa; intros. 
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H0, add_eq_f. now rewrite IHa.
         apply Zle_is_le_bool. lia.
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H0, add_eq_f. apply f_equal.
         case_eq xsa; intros. now simpl.
         case_eq b; intros. subst. simpl in *.
         inversion IHa. rewrite H1.
         apply f_equal. easy.
         subst. simpl in *. apply f_equal.
         inversion IHa. rewrite H1. easy.
         apply Zle_is_le_bool. lia.
Qed.

Lemma mult_f_eq2_2_1: forall a,
RAWBITVECTOR_LIST.mult_bool_step_k_h (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a))
  (false :: a) false 0 = removelast (false :: a).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. apply f_equal.
         case_eq xa; intros. subst. simpl in *. 
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H, add_eq_f. rewrite mult_f_eq2_2_1_1. easy.
         apply Zle_is_le_bool. lia.
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H0, add_eq_f. rewrite IHa. easy.
         apply Zle_is_le_bool. lia.
Qed.


Lemma mult_f_eq2_1: forall a,
RAWBITVECTOR_LIST.mult_bool_step_k_h
           (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) 
           (true :: a) false 0 =
RAWBITVECTOR_LIST.add_list_ingr
           (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) 
           (true :: a) false.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - now simpl.
       - simpl. assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H, add_eq_f. 
         case_eq xa; intros. now rewrite IHa.
         apply f_equal. simpl. rewrite mult_f_eq2_1_1, mult_f_eq2_2_1.
         easy.
         apply Zle_is_le_bool. lia.
Qed.


Lemma mult_f_eq1: forall a b,
(length b >= length a) ->
RAWBITVECTOR_LIST.mult_bool_step (true :: a) (true :: b) (true :: a) 1 (Datatypes.length a) =
true :: RAWBITVECTOR_LIST.add_list b (RAWBITVECTOR_LIST.mult_list_carry a (true :: b) (Datatypes.length a)).
Admitted.


Lemma mult_f_eq2: forall a b,
(length b >= length a) ->
RAWBITVECTOR_LIST.mult_bool_step (true :: a) (false :: b)
  (false :: RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) 1 (Datatypes.length a) =
false :: RAWBITVECTOR_LIST.add_list b (RAWBITVECTOR_LIST.mult_list_carry a (false :: b) (Datatypes.length a)).
Admitted.

Lemma mult_f_eq3: forall a b,
(length b >= length a) ->
RAWBITVECTOR_LIST.mult_bool_step (false :: a) (true :: b) (false :: a) 1 (Datatypes.length a) =
false :: RAWBITVECTOR_LIST.mult_list_carry a (true :: b) (Datatypes.length a).
Admitted.

Lemma mult_f_eq4: forall a b,
(length b >= length a) ->
RAWBITVECTOR_LIST.mult_bool_step (false :: a) (false :: b)
  (false :: RAWBITVECTOR_LIST.mk_list_false (Datatypes.length a)) 1 (Datatypes.length a) =
false :: RAWBITVECTOR_LIST.mult_list_carry a (false :: b) (Datatypes.length a).
Admitted.

Lemma mult_f_eq: forall a b n,
(n = length a) -> (n = length b) ->
RAWBITVECTOR_LIST.mult_bool_step a b (RAWBITVECTOR_LIST.mk_list_false n) 0 n =
RAWBITVECTOR_LIST.mult_list_carry a b n.
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl in H. rewrite H in H0. symmetry in H0. rewrite empty_list_length in H0; rewrite H, H0.
         now simpl.
       - simpl. case_eq b; intros. subst. now contradict H0.
         case_eq xa; case_eq b0; intros. simpl.
         simpl in H.  rewrite H.
         rewrite RAWBITVECTOR_LIST.mult_list_carry_f_f_2.
         rewrite RAWBITVECTOR_LIST.add_list_carry_tf_t.
         simpl. case_eq xsa; intros. subst. inversion H0.
         symmetry in H1. rewrite empty_list_length in H1; rewrite H1.
         now simpl. rewrite fstn_ge, awb_t, <- H4.
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H5, add_eq_f, add_eq.
         rewrite RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_l.

         rewrite mult_f_eq1. reflexivity.
         rewrite H, H1 in H0. simpl in H0. inversion H0.
         lia. lia. now rewrite RAWBITVECTOR_LIST.length_mk_list_false.
         apply Zle_is_le_bool. lia. simpl. lia.

         simpl in H.  rewrite H.
         rewrite RAWBITVECTOR_LIST.mult_list_carry_f_f_2.
         rewrite RAWBITVECTOR_LIST.add_list_carry_ff_f.
         simpl. case_eq xsa; intros. subst. inversion H0.
         symmetry in H1. rewrite empty_list_length in H1; rewrite H1.
         now simpl. rewrite fstn_ge, awb_f, <- H4.
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H5, add_eq_f, add_eq.
         rewrite RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_l.


         rewrite mult_f_eq2. reflexivity.
         rewrite H, H1 in H0. simpl in H0. inversion H0.
         lia. rewrite RAWBITVECTOR_LIST.length_mk_list_false. lia.
         easy. apply Zle_is_le_bool. lia. simpl. lia.

         simpl in H.  rewrite H.
         rewrite RAWBITVECTOR_LIST.mult_list_carry_f_f_2.
         simpl. case_eq xsa; intros. subst. inversion H0.
         symmetry in H1. rewrite empty_list_length in H1; rewrite H1.
         now simpl. rewrite fstn_ge, awb_t, <- H4.
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H5, add_eq_f, add_eq.
         rewrite RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_l.

         rewrite mult_f_eq3. reflexivity.
         rewrite H, H1 in H0. simpl in H0. inversion H0.
         lia. lia. rewrite RAWBITVECTOR_LIST.length_mk_list_false. lia.
         easy. simpl. lia.

         simpl in H.  rewrite H.
         rewrite RAWBITVECTOR_LIST.mult_list_carry_f_f_2.
         simpl. case_eq xsa; intros. subst. inversion H0.
         symmetry in H1. rewrite empty_list_length in H1; rewrite H1.
         now simpl. rewrite fstn_ge, awb_f, <- H4.
         assert ((0-1)%Z = (-1)%Z). { lia. }
         rewrite <- H5, add_eq_f, add_eq.
         rewrite RAWBITVECTOR_LIST.add_list_carry_empty_neutral_n_l.

         rewrite mult_f_eq4. reflexivity.
         rewrite H, H1 in H0. simpl in H0. inversion H0.
         lia. rewrite RAWBITVECTOR_LIST.length_mk_list_false. lia.
         easy. apply Zle_is_le_bool. lia. simpl. lia.
Admitted.

Lemma toListsame_mult_t_t: forall a b n,
(length a = (S n)) -> (length b = (S n)) ->
let n2 := ((listTonat b + listTonat b + (listTonat a + listTonat a) * S (listTonat b + listTonat b)))%nat in
n2 > 0 ->
RAWBITVECTOR_LIST.mult_bool_step (true :: a) (true :: b)
  (true :: RAWBITVECTOR_LIST.and_with_bool a true) 1 n =
mod2 (n2 - 1) :: natTolist (S n) (S (Nat.div2 (n2 - 1))).
Admitted.


Lemma toListsame_mult_t_f: forall a b n,
(length a = n) -> (length b = n) ->
RAWBITVECTOR_LIST.bvmult_bool (true :: a) (false :: b) (S n) =
natTolist (S n) (listTonat b + listTonat b + (listTonat a + listTonat a) * (listTonat b + listTonat b)).
Admitted.

Lemma toListsame_mult_f_t: forall a b n,
(length a = n) -> (length b = n) ->
RAWBITVECTOR_LIST.bvmult_bool (false :: a) (true :: b) (S n) =
natTolist (S n) ((listTonat a + listTonat a) * S (listTonat b + listTonat b)).
Admitted.

Lemma toListsame_mult_f_f: forall a b n,
(length a = n) -> (length b = n) ->
RAWBITVECTOR_LIST.bvmult_bool (false :: a) (false :: b) (S n) =
natTolist (S n) ((listTonat a + listTonat a) * (listTonat b + listTonat b)).
Admitted.

Lemma multoz: forall a,
(a * 1 = 0)%nat -> (a = 0)%nat.
Proof. intros. lia. Qed.

Lemma multz: forall a b,
 (a + a + (b + b) * S (a + a))%nat = 0%nat -> (a + a + (b + b))%nat = 0%nat.
Proof. intro a.
       induction a as [ | xa IHa ]; intros.
       - simpl in *. now apply multoz in H.
       - lia.
Qed.

Lemma toListsame_mult_mkf: forall n,
RAWBITVECTOR_LIST.mult_bool_step (true :: RAWBITVECTOR_LIST.mk_list_false (S n))
  (true :: RAWBITVECTOR_LIST.mk_list_false (S n))
  (true :: RAWBITVECTOR_LIST.and_with_bool (RAWBITVECTOR_LIST.mk_list_false (S n)) true) 1 n =
true :: RAWBITVECTOR_LIST.bvmult_bool (RAWBITVECTOR_LIST.mk_list_false (S n))
                                      (RAWBITVECTOR_LIST.mk_list_false (S n)) (S n).
Proof. intro n.
       induction n as [ | xn IHn ]; intros.
       - now simpl.
       - simpl in IHn. case_eq xn; intros.
        subst. now simpl.
        subst. simpl.
Admitted. 

 
Lemma toListsame_mult: forall (a b: list bool) n,
(length a = n) -> (length b = n) ->
RAWBITVECTOR_LIST.bvmult_bool a b n = natTolist n ((listTonat a) * (listTonat b)).
Proof. intro a.
       induction a as [ | xa xsa IHa ]; intros.
       - simpl in *. rewrite <- H in *. rewrite empty_list_length in H0; subst.
         now simpl.
       - case_eq b; intros. subst. now contradict H0.
         simpl.
         case_eq xa; case_eq b0; intros; simpl.
         assert ( (listTonat xsa + 0)%nat =  (listTonat xsa)).
         { now rewrite plus_n_O. }
          assert ( (listTonat l + 0)%nat =  (listTonat l)).
         { now rewrite plus_n_O. }
         rewrite H4, H5.
         case_eq n; intros. subst. now contradict H6.
         simpl.
         case_eq n0; intros. simpl.
         case_eq ( (listTonat l + listTonat l + (listTonat xsa + listTonat xsa) * S (listTonat l + listTonat l))%nat); intros.
         subst. inversion H6. rewrite empty_list_length in H1.
         rewrite H1. now simpl.
         subst. inversion H6. rewrite empty_list_length in H1.
         rewrite H1. simpl. subst.  simpl in *. rewrite plus_0_r in H8.
         apply mod2Sn1 in H8. now rewrite H8.

         case_eq (  (listTonat l + listTonat l + (listTonat xsa + listTonat xsa) * S (listTonat l + listTonat l))%nat); intros.
         apply multz in H8. apply empty_total in H8.
         apply empty_total2 in H8. destruct H8 as (H8a, H8b).
         specialize (IHa l n0). rewrite H8a, H8b in IHa. simpl in IHa.
         apply lnf in H8a. apply lnf in H8b. rewrite H8a, H8b.
         rewrite <- H7, <- IHa.
         rewrite H1, H6 in H0. simpl in H0. inversion H0. rewrite H9.
         rewrite H6 in H. simpl in H. inversion H. rewrite H10.
         rewrite H7, toListsame_mult_mkf. now rewrite <- H7, H8a, H8b, H9, H10.
         rewrite H6 in H. simpl in H. now inversion H.
         rewrite H6, H1 in H0. simpl in H0. now inversion H0.

         rewrite toListsame_mult_t_t. rewrite H8.
         case_eq n2 ;intros. now simpl.
         assert ((S (S n3) - 1)%nat = (S n3)%nat). { lia. } now rewrite H10.
         simpl in H. subst. now inversion H6.
         rewrite H1 in H0. subst. rewrite H6 in H0. now inversion H0. rewrite H8. lia.

         rewrite !plus_0_r.
         case_eq n; intros. subst. now contradict H4.
         rewrite toListsame_mult_t_f. reflexivity.
         subst. simpl in H4. now inversion H4.
         rewrite H1 in H0. subst. rewrite H4 in H0. simpl in H0. now inversion H0.

         rewrite !plus_0_r.
         case_eq n; intros. subst. now contradict H4.
         rewrite toListsame_mult_f_t. reflexivity.
         subst. simpl in H4. now inversion H4.
         rewrite H1 in H0. subst. rewrite H4 in H0. simpl in H0. now inversion H0.

         rewrite !plus_0_r.
         case_eq n; intros. subst. now contradict H4.
         rewrite toListsame_mult_f_f. reflexivity.
         subst. simpl in H4. now inversion H4.
         rewrite H1 in H0. subst. rewrite H4 in H0. simpl in H0. now inversion H0.
Qed.


Lemma equiv_ltnatN_mult: forall a b,
(length a = length b) ->
natTolist (length a) (listTonat a * listTonat b) = NToList (listToN a * listToN b) (length a).
Admitted.

Lemma _toWordsame_mult: forall n (a b: list bool),
(length a = n) -> (length b = n) ->
RAWBITVECTOR_LIST.bvmult_bool a b n = NToList (Nmult (listToN a) (listToN b)) n.
Proof. intros. specialize (@toListsame_mult a b n H H0); intros. 
       rewrite H1, <- H. rewrite equiv_ltnatN_mult. reflexivity.
       subst. easy.
Qed.


Lemma toWordsame2_mult: forall n (a b: list bool),
(length a = n) -> (length b = n) ->
ListToword (RAWBITVECTOR_LIST.bvmult_bool a b n) n = ListToword (NToList (Nmult (listToN a) (listToN b)) n) n.
Proof. intros. rewrite (@_toWordsame_mult n a b); easy. Qed.

Lemma toWordsame3_mult: forall (a b: list bool) n,
(length a = n) -> (length b = n) ->
Word.wmult (ListToword a n) (ListToword b n)  = ListToword (RAWBITVECTOR_LIST.bvmult_bool a b n) n.
Proof. intros. unfold Word.wmult, wordBin.
       rewrite toWordsame2_mult. 
       rewrite <- !asd, word_same. now rewrite H, H0.
       easy. easy.
Qed.

Lemma check_mult_wmult:forall bs1 bs2 bsres, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_mult bs1 bs2 bsres ->
    (Word.wmult (ListToword (map (Lit.interp rho) bs1) n) (ListToword (map (Lit.interp rho) bs2) n))
    =
    (ListToword (map (Lit.interp rho) bsres) n).
Proof. intros. rewrite toWordsame3_mult.
       rewrite <- H in H0. rewrite <- H. apply ltw_same.
       rewrite <- prop_bblast_bvmult. specialize (@prop_main bs1 bs2 bsres); intros.
       rewrite map_length in H2. apply H2. easy.
       now rewrite map_length. now rewrite map_length.
Qed.


Lemma valid_check_bbMult s pos1 pos2 lres : C.valid rho (check_bbMult s pos1 pos2 lres).
Proof.  
      unfold check_bbMult.
      case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | |[ A B | A| | | | ]|N|N|N|N|N|N|N | ] a1' a2' Heq9; try (intros; now apply C.interp_true).
      (* BVmult *)
      - case_eq ((a1 == a1') && (a2 == a2') (* || (a1 == a2') && (a2 == a1')*) );
            simpl; intros Heq10; try (now apply C.interp_true).

        case_eq ( 
                 check_mult bs1 bs2 bsres &&
                 ((Datatypes.length bs1) =? N)%nat
                ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl.  rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply Word.weqb_true_iff.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H4 in H0; try (now contradict H0).
        rename H4 into Hv.

        generalize (Hs s pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs s pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        apply Word.weqb_true_iff in HSp2.
        apply Word.weqb_true_iff in HSp1.

        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.


        (** case a1 = a1' and a2 = a2' **)
        rewrite andb_true_iff in Heq10.
        destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2;
        rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_word a = 
                interp_word t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_word. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval.

        assert (H100: ((Datatypes.length (map (Lit.interp rho) bsres))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          pose proof Heq11 as Heq11'.
          apply prop_main in Heq11.
          rewrite <- Heq11. rewrite !map_length.
          specialize (@check_bvmult_length bs1 bs2).
          intros. simpl in H5. rewrite <- H5.
          now rewrite Nat.eqb_eq in Heq11r.
          now apply check_bvmult_length2 in Heq11'.
        }

        rewrite H100.

        rewrite Typ.cast_refl.
        intros.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_word a1' = 
                interp_word t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp1.
        unfold interp_word in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_word in HSp1.

        revert HSp1.

        assert (H101: ((Datatypes.length (map (Lit.interp rho) bs1))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite Nat.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        rewrite H101.

        rewrite Typ.cast_refl.
        intros.

        rewrite HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_word a2' = 
                interp_word t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_word.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H6 in HSp2.
        unfold interp_word in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_word in HSp2.

        revert HSp2. 
        assert (H102: ((Datatypes.length (map (Lit.interp rho) bs2))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite Nat.eqb_eq in Heq11r.
          apply check_bvmult_length2 in Heq11.
          rewrite Heq11 in Heq11r.
          now rewrite map_length.
        }

        rewrite H102.

        rewrite Typ.cast_refl.
        intros. rewrite HSp2.

        pose proof Heq11.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11 & Heq11r).
        rewrite Nat.eqb_eq in Heq11r.

        rewrite map_length in H100. rewrite <- H100.
        rewrite <- (@check_mult_wmult bs1 bs2). reflexivity.
        rewrite Heq11r. easy.
        apply check_bvmult_length2 in Heq11.
        rewrite Heq11 in Heq11r.
        rewrite Heq11r. easy.

        easy.
Qed.



Lemma sext_empty: forall l, (sextend_lit l 0) = l.
Proof. intros; now unfold sextend_lit. Qed.

Lemma _flsi_lit: forall i a, _false_list_lit a (S i) = Lit._false :: _false_list_lit a i.
Proof. intro i.
       induction i; intros.
       - now simpl.
       - rewrite IHi. now simpl.
Qed. 

Lemma _flsapp_lit: forall i, _false_list_lit [] i ++ [Lit._false] = Lit._false :: _false_list_lit [] i.
Proof. intro i.
       induction i; intros.
       - now simpl.
       - simpl. now rewrite IHi.
Qed.

Lemma _flslen_lit: forall i a, length (_false_list_lit a i) = ((length a) + i)%nat.
Proof. intro i.
       induction i; intros.
       - simpl. lia.
       - simpl. rewrite IHi. lia.
Qed. 

Lemma eqsext: forall i, (extend_lit [] i Lit._false) = (false_list_lit i).
Proof. intro i.
       induction i; simpl.
       - now compute.
       - rewrite IHi. simpl. unfold false_list_lit. now rewrite _flsapp_lit.
Qed.

Lemma sext_cons_f: forall i l,
                  (map (Lit.interp rho) (sextend_lit (Lit._false :: l) i)) = 
                  (Lit.interp rho (Lit._false)) :: (map (Lit.interp rho) (sextend_lit l i)).
Proof. intro i.
       induction i; intros.
       - unfold sextend_lit. now simpl.
       - unfold sextend_lit in *. simpl.
         specialize (IHi l). simpl in *.
         case_eq l; intros; subst. rewrite map_app, IHi. simpl.
         admit.
         rewrite map_app.
         now rewrite IHi, map_app.
Admitted.


Lemma sext_cons: forall i l a,
                  l <> [] ->
                  (map (Lit.interp rho) (sextend_lit (a :: l) i)) = 
                  (Lit.interp rho a) :: (map (Lit.interp rho) (sextend_lit l i)).
Proof. intro i.
       induction i; intros.
       - unfold sextend_lit. now simpl.
       - unfold sextend_lit in *. simpl.
         specialize (IHi l a). simpl in *.
         case_eq l; intros; subst. now contradict H.
         rewrite map_app.
         now rewrite IHi, map_app.
Qed.


Lemma len_lit: forall i, length (false_list_lit i) = i.
Proof. intro i.
       induction i; simpl.
       - now simpl.
      - unfold false_list_lit in IHi. now rewrite IHi.
Qed. 

Lemma sext_len: forall a i, (length (sextend_lit a i)) =  (length a + i)%nat.
Proof. intros. unfold sextend_lit. 
       case_eq a; intros; now rewrite ext_len.
Qed.

Lemma sextend_interp_len: forall bs1 bsres (i: nat),
                           check_sextend bs1 bsres i = true ->
                           length bsres = (length bs1 + i)%nat.
Proof. intro bs1.
       induction bs1; intros.
       - simpl in *. unfold check_sextend in H.
         case_eq (forallb2 eq_carry_lit (lit_to_carry (sextend_lit [] i)) bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0. 
         assert (length (map (Lit.interp rho) (sextend_lit [] i)) = length (map (Lit.interp rho) bsres)).
         { now rewrite H0. }
         rewrite !map_length in H1. unfold sextend_lit in H1.
         simpl in H1. now rewrite ext_len in H1.
         rewrite H0 in H; now contradict H.
       - simpl. unfold check_sextend in H.
         case_eq ( forallb2 eq_carry_lit (lit_to_carry (sextend_lit (a :: bs1) i)) bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         assert (length (map (Lit.interp rho) (sextend_lit (a :: bs1) i)) = length (map (Lit.interp rho) bsres)).
         { now rewrite H0. }
         rewrite !map_length in H1. now rewrite sext_len in H1.
         rewrite H0 in H; now contradict H.
Qed.

Lemma asd: forall a,
wmsb (ListToword a (Datatypes.length a)) false = true -> a <> [].
Proof. intro a.
       induction a; intros.
       - simpl in H. now contradict H.
       - easy.
Qed.

Lemma last_cons: forall a i, last (i :: a) false = false -> last a false = false.
Proof. intro a.
       induction a; intros.
       - now simpl.
       - simpl in *. case_eq a0; intros; now subst.
Qed.

Lemma asd2: forall xl a, wmsb (ListToword [a; xl] 2) false = false -> xl = false.
Proof. intros. case_eq a; case_eq xl; intros; subst; simpl in H; easy. Qed.

Lemma asd2': forall xl a, wmsb (ListToword [(Lit.interp rho a); (Lit.interp rho xl)] 2) 
false = false -> (Lit.interp rho xl) = false.
Proof. intros. case_eq (Lit.interp rho a); case_eq (Lit.interp rho xl); intros; subst; simpl in H; try easy.
rewrite H0, H1 in H. simpl in H. now contradict H.
rewrite H0, H1 in H. simpl in H. now contradict H.
Qed.

Lemma asd3: forall xsl xl a,
wmsb (ListToword (a :: xl :: xsl) (Datatypes.length (a :: xl :: xsl))) false = false ->
wmsb (ListToword (xl :: xsl) (Datatypes.length (xl :: xsl))) false = false.
Proof. intros. simpl in *.
       specialize (@helper_strong (xl :: xsl) a); intros. simpl in H0.
       rewrite H0 in H. simpl in H.
       specialize (@helper_strong xsl xl); intros. simpl in H1.
       rewrite H1 in *. now simpl in *.
Qed.

Lemma asd4: forall l a,
 wmsb (ListToword (a :: l) (Datatypes.length (a :: l))) false = false ->
 (last l false) = false.
Proof. intro l.
       induction l as [ | xl xsl IHl ]; intros.
       - easy.
       - simpl. case_eq xsl; intros; rewrite H0 in H. now apply asd2 in H.
         rewrite <- H0 in *. apply (IHl xl). now apply asd3 in H.
Qed.


Lemma last_cons': forall {A} (xsl: list A) a xl c, last (a :: xl :: xsl) c  = last (xl :: xsl) c.
Proof. intros A xsl.
       case_eq xsl; intros.
       - now simpl.
       - simpl. case_eq l; intros; easy.
Qed.

Lemma wmsb1: forall a, wmsb (ListToword [Lit.interp rho a] 1) false = false ->
Lit.interp rho a = false.
Proof. intros.
       specialize (@helper_strong [] (Lit.interp rho a)); intros. simpl in H0.
       rewrite H0 in H. now simpl in H.
Qed.

Lemma asd5: forall l a,
 wmsb (ListToword (map (Lit.interp rho) (a :: l)) (Datatypes.length (a :: l))) false = false ->
 (last (a :: l) Lit._false) = Lit._false.
Proof. intro l.
       induction l as [ | xl xsl IHl ]; intros.
       - simpl in *. admit.
       - rewrite !map_cons in H. 
         specialize (@asd3  (map (Lit.interp rho) xsl) (Lit.interp rho xl) (Lit.interp rho a)).
         intros. simpl in H0. rewrite !map_length in H0.
         apply H0 in H.
         rewrite <- map_cons in H. specialize (IHl xl).
         assert ((Datatypes.length (xl :: xsl)) = (S (Datatypes.length xsl))) by auto.
         rewrite H1 in IHl. apply IHl in H. now rewrite (@last_cons' _lit xsl a xl (Lit._false)).
Admitted.


Lemma asd6': forall a,
      wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) false = false ->
      (last (map (Lit.interp rho) a) false) = false.
Proof. intro a.
       induction a; intros.
       - now simpl.
       - case_eq a0; intros; rewrite H0 in *. simpl in *.
         now apply wmsb1 in H.
Admitted.

Lemma asd6: forall a,
      a <> [] -> 
      wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) false = false ->
      (last a (Lit._false)) = Lit._false.
Proof. intro a.
       induction a; intros.
       - now contradict H.
       - now apply asd5 in H0.
Qed.

Lemma appsame: forall {A} (a: list A) c d, a ++ [c] = a ++ [d] -> c = d.
Proof. intros A a.
       induction a; intros.
       - simpl in H. now inversion H.
       - simpl in H. apply IHa. now inversion H.
Qed.

Lemma appsame2: forall {A} (a: list A) c d, (a ++ [c]) ++ [c] = (a ++ [d]) ++ [d]-> c = d.
Proof. intros A a.
       induction a; intros.
       - simpl in H. now inversion H.
       - simpl in H. apply IHa. now inversion H.
Qed.

Lemma appsame3: forall {A} (a: list A) c d, ((a ++ [c]) ++ [c]) ++ [c] = ((a ++ [d]) ++ [d]) ++ [d] -> c = d.
Proof. intros A a.
       induction a; intros.
       - simpl in H. now inversion H.
       - simpl in H. apply IHa. now inversion H.
Qed.

Lemma rlast: forall {A} (a b: list A), a = b -> removelast a = removelast b.
Proof. intros A a.
       induction a; intros; now subst.
Qed.

Lemma extlitcd3: forall i a c d,
 ((extend_lit a i c ++ [c]) ++ [c]) ++ [c] = ((extend_lit a i d ++ [d]) ++ [d]) ++ [d] ->
(extend_lit a i c ++ [c]) ++ [c] = (extend_lit a i d ++ [d]) ++ [d].
Proof. intro i.
       induction i; intros.
       - simpl in *. now apply appsame3 in H; subst.
       - simpl in *.
         assert (
         (removelast ((((extend_lit a i c ++ [c]) ++ [c]) ++ [c]) ++ [c])) =
         (removelast ((((extend_lit a i d ++ [d]) ++ [d]) ++ [d]) ++ [d])) ) .
         { specialize (@rlast _ ((((extend_lit a i c ++ [c]) ++ [c]) ++ [c]) ++ [c])
                           ((((extend_lit a i d ++ [d]) ++ [d]) ++ [d]) ++ [d])).
           intros. apply H0 in H. exact H. } rewrite !removelast_app in H0. simpl in H0.
           now rewrite !app_nil_r in H0. easy. easy.
Qed.


Lemma extlitcd2: forall i a c d, 
(extend_lit a i c ++ [c]) ++ [c] = (extend_lit a i d ++ [d]) ++ [d] ->
(extend_lit a i c ++ [c]) = (extend_lit a i d ++ [d]).
Proof. intro i.
       induction i; intros.
       - simpl in *. case_eq a; intros; subst; simpl in *; inversion H; try easy.
         apply appsame2 in H1; now subst.
       - simpl in *. now apply extlitcd3 in H.
Qed.

Lemma extlitcd: forall i a c d, extend_lit a (S i) c = extend_lit a (S i) d -> c = d.
Proof. intro i.
       induction i; intros.
       - simpl in H. now apply (@appsame _ a).
       - simpl in *. specialize (IHi a c d). apply extlitcd2 in H.
         now apply IHi in H.
Qed.

Lemma extsamene: forall i a, i <> O -> 
zextend_lit a i = sextend_lit a i ->
zextend_lit a (S i) = sextend_lit a (S i).
Proof. intros. unfold sextend_lit, zextend_lit in *. simpl in *.
       induction i; intros.
       - now contradict H.
       - unfold sextend_lit, zextend_lit in *. simpl in *.
         specialize (@extlitcd i a Lit._false  (last a Lit._false)); intros.
         apply H1 in H0; now rewrite <- H0.
Qed.

Lemma wmsbne: forall a,
      wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) false = false ->
      (last (map (Lit.interp rho) a) false) = false.
Proof. intro a.
       induction a; intros.
       - now simpl.
       - case_eq a0; intros. subst. simpl in *. now apply wmsb1 in H.
         rewrite H0 in H. rewrite !map_cons in H. 
         specialize (@asd3 (map (Lit.interp rho) l) (Lit.interp rho i) (Lit.interp rho a));
           intros. simpl in H1, H. rewrite !map_length in H1. apply H1 in H.
           rewrite <- map_cons in H. rewrite <- H0 in H.
           assert ((S (Datatypes.length l)) =  (Datatypes.length a0)). 
           { rewrite H0. now simpl. } rewrite H2 in H.
           apply IHa in H. rewrite !map_cons.
           rewrite (@last_cons' _ 
             (map (Lit.interp rho) l) (Lit.interp rho a) (Lit.interp rho i) false).
           now rewrite <- map_cons, <- H0.
Qed.

Fixpoint _ListToword_lit (a: list _lit) (n: nat): word n.
Proof. case_eq a; intros.
         case_eq n; intros.
         + exact WO.
         + exact (wzero (S n0)).
         + case_eq n; intros.
           - exact WO.
           - case_eq (i == Lit._true); case_eq (i == Lit._false); intros.
             exact (wzero (S n0)).
             exact (@WS true _ (_ListToword_lit l n0)).
             exact (@WS false _ (_ListToword_lit l n0)).
             exact (@WS (Lit.interp rho i) _ (_ListToword_lit l n0)).
Defined.

Definition ListToword_lit (a: list _lit) (n: nat): word n :=
  if Nat.eqb (length a) n then _ListToword_lit a n
  else wzero n.
  
Fixpoint wmsb_lit sz (w : word sz) (a : _lit) : _lit :=
  match w with
    | WO => a
    | @WS false _ x => wmsb_lit x Lit._false
    | @WS true _ x => wmsb_lit x Lit._true
  end.

 Definition xx := [0; 1; 0; 1; 3].
 Check xx.

(*Compute ListToword_lit xx 5.*)

Lemma _helper_strong_lit: forall n l i,
(_ListToword_lit (i :: l) (S n)) =
WS (Lit.interp rho i) (_ListToword_lit l n).
Proof. intro n.
       induction n; intros.
       - case_eq (i == Lit._true); intros. simpl. rewrite H.
         rewrite eqb_spec in H. rewrite H.
         assert (Lit.interp rho Lit._true = true).
         { specialize (Lit.interp_true rho wf_rho). intros.
           apply H0. } now rewrite H0.
         case_eq (i == Lit._false); intros.
         simpl. rewrite H, H0.
         rewrite eqb_spec in H0. rewrite H0.
         assert (Lit.interp rho Lit._false = false).
           { specialize (Lit.interp_false rho wf_rho). intros.
              rewrite <- not_true_iff_false.
              unfold not in *.
              intros. now apply H1. } now rewrite H1.
         simpl. rewrite H, H0.
         assert ( (_ListToword_lit l 0) = WO).
         { case_eq l; intros; now simpl. }
         now rewrite H1.
       - case_eq (i == Lit._true); intros. simpl. rewrite H.
         rewrite eqb_spec in H. rewrite H. simpl.
         assert (Lit.interp rho Lit._true = true).
         { specialize (Lit.interp_true rho wf_rho). intros.
           apply H0. } now rewrite H0.
         case_eq (i == Lit._false); intros.
         simpl. rewrite H, H0.
         rewrite eqb_spec in H0. rewrite H0.
         assert (Lit.interp rho Lit._false = false).
           { specialize (Lit.interp_false rho wf_rho). intros.
              rewrite <- not_true_iff_false.
              unfold not in *.
              intros. now apply H1. } now rewrite H1.
         simpl. now rewrite H, H0.
Qed.

Lemma helper_strong_lit: forall l i,
(ListToword_lit (i :: l) (S (length l))) =
WS (Lit.interp rho i) (ListToword_lit l (length l)).
Proof. intros. unfold ListToword_lit. rewrite !Nat.eqb_refl.
       now rewrite _helper_strong_lit.
Qed.

Lemma interp_correct: forall a,
(ListToword_lit a (Datatypes.length a)) =
(ListToword (map (Lit.interp rho) a) (Datatypes.length a)).
Proof. intro a.
       induction a as [ | xa xsa IHa]; intros.
       - now simpl.
       - rewrite helper_strong_lit.
         specialize (@helper_strong (map (Lit.interp rho) xsa) 
         (Lit.interp rho xa) ); intros. rewrite !map_length in H. simpl. 
         rewrite H. now rewrite IHa.
Qed.


Lemma asd62: forall a,
      wmsb (ListToword_lit a (Datatypes.length a)) false = false ->
      (last a (Lit._false)) = Lit._false.
Proof. intro a.
       induction a; intros.
       - now simpl in *.
       - 
       
       now apply asd5 in H0.
Qed.

Lemma wmsb_interp_correct_f: forall a,
wmsb_lit (ListToword_lit a (Datatypes.length a)) false = false ->
wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) 
(Lit.interp rho (Lit._false)) = (Lit.interp rho (Lit._false)).
Proof. intros. rewrite <- interp_correct. admit.
Admitted. 

Lemma ltwlitf: forall a, wmsb_lit (ListToword_lit [a] 1) false = (Lit._false) ->
a = Lit._false.
Proof. intros. simpl in H.
       rewrite helper_strong_lit in H. simpl in H.
       case_eq (Lit.interp rho a); intros; rewrite H0 in H. now contradict H.
 apply wmsb_interp_correct_f in H.
       induction a; intros. simpl in *. unfold Lit._false. simpl. rewrite H.
        
     

Lemma asd52: forall l a,
 wmsb (ListToword_lit (a :: l) (Datatypes.length (a :: l))) false = false ->
 (last (a :: l) Lit._false) = Lit._false.
Proof. intro l.
       induction l as [ | xl xsl IHl ]; intros.
       - simpl in *. admit.
       - rewrite !map_cons in H. 
         specialize (@asd3  (map (Lit.interp rho) xsl) (Lit.interp rho xl) (Lit.interp rho a)).
         intros. simpl in H0. rewrite !map_length in H0.
         apply H0 in H.
         rewrite <- map_cons in H. specialize (IHl xl).
         assert ((Datatypes.length (xl :: xsl)) = (S (Datatypes.length xsl))) by auto.
         rewrite H1 in IHl. apply IHl in H. now rewrite (@last_cons' _lit xsl a xl (Lit._false)).
Admitted.



Lemma extsame: forall i a,
wmsb (ListToword_lit a (Datatypes.length a)) false = false -> 
zextend_lit a i = sextend_lit a i.
Proof. intro i.
       induction i; intros.
       - unfold zextend_lit, sextend_lit. now simpl.
       - case_eq a; intros.  unfold zextend_lit, sextend_lit. now simpl.
         apply asd6' in H. rewrite <- H0. unfold zextend_lit,sextend_lit.
         simpl. now rewrite H.
         now rewrite H0.
Qed.

  
Lemma extsame: forall i a,
wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) false = false -> 
zextend_lit a i = sextend_lit a i.
Proof. intro i.
       induction i; intros.
       - unfold zextend_lit, sextend_lit. now simpl.
       - case_eq a; intros.  unfold zextend_lit, sextend_lit. now simpl.
         apply asd6' in H. rewrite <- H0. unfold zextend_lit,sextend_lit.
         simpl. now rewrite H.
         now rewrite H0.
Qed.



Lemma extsame: forall a i,
wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) false = false -> 
zextend_lit a i = sextend_lit a i.
Proof. intro a.
       induction a as [ | xa xsa IHa]; intros.
       - unfold zextend_lit, sextend_lit in *. now simpl.
       - case_eq xsa; intros.
         + unfold zextend_lit, sextend_lit in *. 
           rewrite H0 in *. simpl in *. apply wmsb1 in H.
           
         +  
 apply extsamene; try easy.
       unfold zextend_lit, sextend_lit in *. simpl.
        
       induction i as [ | xi IHi ]; intros.
       - unfold zextend_lit, sextend_lit. now simpl.
       - simpl. case_eq a; intros. unfold zextend_lit, sextend_lit. now simpl.
         apply IHi in H. unfold zextend_lit, sextend_lit in *. 
         rewrite <- H0. simpl.
         spe extlitcd in H.
         
          apply extsamene. easy. case_eq a; intros.  unfold zextend_lit, sextend_lit. now simpl.
         apply IHi in H. unfold zextend_lit,sextend_lit in *. simpl.
         
          simpl.
         apply asd6 in H. rewrite <- H0. unfold zextend_lit,sextend_lit.
         simpl. now rewrite H.
         now rewrite H0.
Qed.


Lemma extsame: forall i a,
wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) false = false -> 
zextend_lit a i = sextend_lit a i.
Proof. intro i.
       induction i; intros.
       - unfold zextend_lit, sextend_lit. now simpl.
       - case_eq a; intros.  unfold zextend_lit, sextend_lit. now simpl.
         apply asd6 in H. rewrite <- H0. unfold zextend_lit,sextend_lit.
         simpl. now rewrite H.
         now rewrite H0.
Qed.

Lemma asd7: forall a i,
zextend_lit a i = sextend_lit a i ->
wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) false = false.
Proof.
    intro a.
    induction a; intros.
    - now simpl.
    - simpl. unfold zextend_lit, sextend_lit in H.
Admitted.


Lemma exts: forall i a, zextend_lit a (S i) = sextend_lit a (S i) -> zextend_lit a i = sextend_lit a i.
Proof. intros. apply extsame. now apply asd7 in H. Qed.


Lemma extsame_cons: forall i a a0,
zextend_lit a i = sextend_lit a i ->
zextend_lit (a0 :: a) i = sextend_lit (a0 :: a) i.
Proof. intro i.
       induction i; intros.
       - unfold zextend_lit, sextend_lit. now simpl.
       - apply extsame. apply exts in H. apply (@asd7 (a0 :: a) i). now apply IHi.
Qed.

Lemma wmsb_cons: forall a i c,
wmsb (ListToword (Lit.interp rho i :: map (Lit.interp rho) a) (S (Datatypes.length a))) c =
true -> wmsb (ListToword (map (Lit.interp rho) a) (Datatypes.length a)) (Lit.interp rho i) = true.
Proof. intros.
         specialize (@helper_strong (map (Lit.interp rho) a) 
         (Lit.interp rho i) ); intros. rewrite !map_length in H0. rewrite H0 in H.
         simpl in H. easy.
Qed.



Lemma sextend_interp_main: forall bs1 bsres (i: nat),
                           check_sextend bs1 bsres i = true ->
                           Word.sext (ListToword (map (Lit.interp rho) bs1) (length bs1)) i  =
                           ListToword (map (Lit.interp rho) bsres) ((length bs1) + i).
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros. simpl.
         unfold check_sextend in H. simpl in H.
         case_eq (forallb2 eq_carry_lit
          (lit_to_carry  (sextend_lit [] i)) bsres).
         intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         simpl in H0. unfold sext. rewrite <- H0. simpl. unfold sextend_lit in *.
         now rewrite wzeroi, !eqsext.

         intros. rewrite H0 in H; now contradict H.
       - intros. unfold sext, check_sextend in H.
         case_eq (
          forallb2 eq_carry_lit
          (lit_to_carry
             (sextend_lit (xbs1 :: xsbs1) i))
          bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0. simpl.

         unfold sext in *.         

         case_eq (wmsb (ListToword (Lit.interp rho xbs1 :: 
                 map (Lit.interp rho) xsbs1) (S (Datatypes.length xsbs1))) false); intros.
         
         specialize (@helper_strong (map (Lit.interp rho) xsbs1) 
         (Lit.interp rho xbs1) ); intros. rewrite !map_length in H2. rewrite H2. simpl.

         rewrite <- H0.
         assert (wmsb (ListToword (Lit.interp rho xbs1 :: map (Lit.interp rho) xsbs1)
           (S (Datatypes.length xsbs1))) false = true -> 
           wmsb (ListToword (map (Lit.interp rho) xsbs1) (Datatypes.length xsbs1)) false 
           = true).
         { intros. admit. } apply H3 in H1. rewrite H1 in IHbs1. rewrite sext_cons.

         rewrite (@IHbs1 (sextend_lit  xsbs1 i) i).
         specialize (@helper_strong (map (Lit.interp rho) (sextend_lit xsbs1 i)) 
         (Lit.interp rho xbs1) ); intros. rewrite !map_length in H4. rewrite sext_len in H4.
         now rewrite H4. 

         unfold check_sextend. now rewrite forallb_eqb_refl.
         specialize (@asd (map (Lit.interp rho) xsbs1)); intros Hn. rewrite !map_length in Hn.
         apply Hn in H1. case_eq xsbs1; intros; subst; try now contradict H1.

         rewrite <- H0.
         assert (wmsb (ListToword (Lit.interp rho xbs1 :: map (Lit.interp rho) xsbs1)
           (S (Datatypes.length xsbs1))) false = false -> 
           wmsb (ListToword (map (Lit.interp rho) xsbs1) (Datatypes.length xsbs1)) false = false).
         { admit. } apply H2 in H1. rewrite H1 in IHbs1.

         specialize (@helper_strong (map (Lit.interp rho) xsbs1) 
         (Lit.interp rho xbs1) ); intros. rewrite !map_length in H3. rewrite H3.
         
         assert (Word.combine
                (WS (Lit.interp rho xbs1) 
                (ListToword (map (Lit.interp rho) xsbs1) (Datatypes.length xsbs1)))
                (wzero i)
                =
                WS (Lit.interp rho xbs1)
                (Word.combine (ListToword (map (Lit.interp rho) xsbs1)
                (Datatypes.length xsbs1)) (wzero i))). { now simpl. }
        rewrite H4.

         rewrite (@IHbs1 (sextend_lit  xsbs1 i) i). simpl. apply (extsame i) in H1.
         rewrite <- H1.
         specialize (@extsame_cons i xsbs1 xbs1); intros.
         apply H5 in H1. rewrite <- H1. rewrite zext_cons.
         specialize (@helper_strong (map (Lit.interp rho) (zextend_lit xsbs1 i)) 
         (Lit.interp rho xbs1) ); intros. rewrite !map_length in H6. rewrite zext_len in H6.
         now rewrite H6.
         unfold check_sextend. now rewrite forallb_eqb_refl.
         rewrite H0 in H; now contradict H.
Admitted.










Lemma map_cons T U (f: T -> U) (h: T) (l: list T): map f (h :: l) = f h :: map f l.
Proof. auto. Qed.



Lemma valid_check_bbSlt pos1 pos2 lres : C.valid rho (check_bbSlt pos1 pos2 lres).
Proof.
      unfold check_bbSlt.
       case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
       case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
       case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
       case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
       case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
       case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true). intros a bsres Heq8.
       case_eq (Bool.eqb (Lit.is_pos a) (Lit.is_pos bsres)); try (intros; now apply C.interp_true). intros Heq12.
       case_eq (t_form .[ Lit.blit a]); try (intros; now apply C.interp_true). intros a3 Heq10.
       case_eq (t_atom .[ a3]); try (intros; now apply C.interp_true).

       intros [ | | | | | | | [ A B | A | | | | ]|N|N|N|N|N|N|N|N|N| | ] a1' a2' Heq9; 
          try (intros; now apply C.interp_true).

       case_eq ((a1 == a1') && (a2 == a2')); simpl; intros Heq15; try (now apply C.interp_true).

       case_eq (check_slt bs1 bs2 bsres &&
          (N.of_nat (Datatypes.length bs1) =? N)%N &&
          (N.of_nat (Datatypes.length bs2) =? N)%N); 
       simpl; intros Heq16; try (now apply C.interp_true).

       unfold C.valid. simpl.

       rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a3).
       assert (a3 < PArray.length t_atom).
       { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
       specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
       rewrite !andb_true_iff in H0. destruct H0. destruct H0.

       unfold get_type' in H0. unfold v_type in H0.
       case_eq (t_interp .[ a3]).
       intros v_typea3 v_vala3 Htia3. rewrite Htia3 in H0.
       case_eq (v_typea3);  intros; rewrite H4 in H0; try (now contradict H0).
       rename H4 into Hv.

       generalize (Hs pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
       unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
       unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
       rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

       generalize (Hs pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
       unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
       unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
       rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

       unfold get_type' in H2, H3. unfold v_type in H2, H3.
       case_eq (t_interp .[ a1']).
         intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
       case_eq (t_interp .[ a2']).
         intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
       simpl in v_vala2, v_vala2.

       apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

       (** case a1 = a1' and a2 = a2' **)
       rewrite andb_true_iff in Heq15.
       destruct Heq15 as (Heq15a1 & Heq15a2); rewrite eqb_spec in Heq15a1, Heq15a2
       ;rewrite Heq15a1, Heq15a2 in *.


        (* interp_form_hatom_bv a1' =
                 interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' =
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia1; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1.

        (* interp_form_hatom_bv a2' =
                 interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' =
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia2; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2.

        generalize dependent v_vala1. generalize dependent v_vala2.
        rewrite H2, H3. 

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (
        H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as ((Heq16a, Heq16b), Heq16c).
          rewrite N.eqb_eq in Heq16c.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H100.

        assert (
        H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as ((Heq16a, Heq16b), Heq16c).
          rewrite N.eqb_eq in Heq16b.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).       

        rewrite H101.

        rewrite Typ.cast_refl in *.

        intros.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.
        apply (@Bool.eqb_true_iff (Lit.interp rho a) (Lit.interp rho bsres)).

        unfold Lit.interp, Var.interp.
        rewrite rho_interp.
        rewrite Heq10. simpl.

        unfold Atom.interp_form_hatom.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1, Htia2. simpl.

        rewrite Form.wf_interp_form; trivial.
        simpl.
        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        rewrite HSp1, HSp2.

        case_eq (Lit.is_pos bsres).
        intros Hpos.

        unfold BITVECTOR_LIST.bv_slt.
        unfold RAWBITVECTOR_LIST.bv_slt, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        simpl.
        unfold RAWBITVECTOR_LIST.size.
        simpl.

        rewrite !Typ.N_cast_refl.
        rewrite !andb_true_iff in Heq16.
        destruct Heq16 as ((Heq16 & Heq16l) & Heq16r).
        rewrite N.eqb_eq in Heq16r, Heq16l.
        rewrite map_length, Heq16l.
        rewrite H100.
        rewrite N.eqb_compare. rewrite N.compare_refl.

        unfold RAWBITVECTOR_LIST.slt_list.
        specialize (@prop_check_slt (List.rev bs1) (List.rev bs2)).
        intros.

        cut ( Datatypes.length (List.rev bs1) = Datatypes.length (List.rev bs2)).
        intros. specialize (H6 H7).
        do 2 rewrite <- List.map_rev.
        rewrite H6.

        pose proof (rho_interp).
        specialize (H8 (Lit.blit a)).
        rewrite Heq10 in H8.
        simpl in H8.

        rewrite !rev_length in H7.
        specialize (@prop_check_slt2 bs1 bs2 bsres H7 Heq16).
        intros.
        rewrite H9.
        simpl.
        unfold Atom.interp_form_hatom, interp_hatom.
        simpl.
        now rewrite prop_lit.

        rewrite !rev_length.
        apply (f_equal nat_of_N) in Heq16l.
        apply (f_equal nat_of_N) in Heq16r.
        rewrite Nat2N.id in Heq16l, Heq16r.
        now rewrite Heq16l, Heq16r.

        intros.
        rewrite !andb_true_iff in Heq16.
        destruct Heq16 as ((Heq16 & Heq16l) & Heq16r).
        rewrite N.eqb_eq in Heq16r, Heq16l.

        contradict Heq16.
        unfold check_slt.
        rewrite H6. easy.
Qed.



Lemma check_add_bvadd: forall bs1 bs2 bsres n, 
  (N.of_nat(length bs1) = n)%N -> 
  (N.of_nat(length bs2) = n)%N -> 
  (N.of_nat(length bsres) = n)%N ->  
  check_add bs1 bs2 bsres (Clit Lit._false) = true ->
  (RAWBITVECTOR_LIST.bv_add (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2) =
   (map (Lit.interp rho) bsres)).
Proof. intros.
       pose proof H as H'. pose proof H0 as H0'. pose proof H1 as H1'.
       rewrite <- H1 in H. apply Nat2N.inj in H.
       rewrite <- H1 in H0. apply Nat2N.inj in H0.
       specialize (@check_add_list bs1 bs2 bsres ( (Clit Lit._false)) H H0 H2). intros.
       unfold RAWBITVECTOR_LIST.bv_add.
       unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits.
       unfold BITVECTOR_LIST.of_bits.
       rewrite !map_length, H, H0.
       rewrite N.eqb_refl.

       assert (  (interp_carry (Clit Lit._false)) = false).
       {
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H4.
         rewrite not_true_iff_false in H4.
         now unfold interp_carry.
       }

       rewrite H4 in H3.
       unfold RAWBITVECTOR_LIST.add_list.
       apply H3.
Qed.

Lemma valid_check_bbAdd pos1 pos2 lres : C.valid rho (check_bbAdd pos1 pos2 lres).
Proof.
      unfold check_bbAdd.
      case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | |[ A B | A| | | | ]|N|N|N|N|N|N|N|N|N| | ] a1' a2' Heq9;
        try (intros; now apply C.interp_true).

      (* BVadd *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1'));
            simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (
                 check_add bs1 bs2 bsres (Clit Lit._false) &&
                 (N.of_nat (Datatypes.length bs1) =? N)%N
        ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply BITVECTOR_LIST.bv_eq_reflect.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H4 in H0; try (now contradict H0).
        rename H4 into Hv.

        generalize (Hs pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.

        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2
        ;rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_bv. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval.

        assert (H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bsres))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite N.eqb_eq in Heq11r.
          rewrite Heq11a in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100.

        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. 

        revert HSp1.

        assert (H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }
        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. 

        revert HSp2.

        assert (H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite Heq11a, <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H102.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp2.

        pose proof Heq11.
        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11 & Heq11r).
        rewrite N.eqb_eq in Heq11r.

        apply check_add_bvadd_length in Heq11.

        unfold BITVECTOR_LIST.bv_add. simpl.
        apply eq_rec.
        simpl.

        specialize (@check_add_bvadd bs1 bs2 bsres N).

        intros. apply H8.
        exact Heq11r.
        destruct Heq11 as (Heq11a & Heq11b).
        rewrite <- Heq11b in Heq11a.
        rewrite Heq11a in Heq11r. easy.
        destruct Heq11 as (Heq11a & Heq11b).
        rewrite Heq11a in Heq11r. easy.
        rewrite andb_true_iff in H7.
        destruct H7 as (H7 & H7r).
        exact H7.

        (** symmetic case **)


        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_bv. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval.

        assert (H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bsres))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite N.eqb_eq in Heq11r.
          rewrite Heq11a in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100.
        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2.

        revert HSp2.

        assert (H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite Heq11a, <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H102.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp2.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H6 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1.

        revert HSp1.

        assert (H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp1.

        pose proof Heq11.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11 & Heq11r).
        rewrite N.eqb_eq in Heq11r.

        apply check_add_bvadd_length in Heq11.

        unfold BITVECTOR_LIST.bv_add. simpl.
        apply eq_rec.
        simpl.

        specialize (@RAWBITVECTOR_LIST.bv_add_comm N).
        intros. rewrite H8.

        specialize (@check_add_bvadd bs1 bs2 bsres N).

        intros. apply H9.
        exact Heq11r.
        destruct Heq11 as (Heq11a & Heq11b).
        rewrite <- Heq11b in Heq11a.
        rewrite Heq11a in Heq11r. easy.
        destruct Heq11 as (Heq11a & Heq11b).
        rewrite Heq11a in Heq11r. easy.

        rewrite andb_true_iff in H7.
        destruct H7 as (H7 & H7r).
        exact H7.

        unfold RAWBITVECTOR_LIST.size.
        destruct Heq11 as (Heq11a, Heq11b).
        rewrite <- Heq11a in Heq11b.
        rewrite <- Heq11b in Heq11r.
        now rewrite map_length.

        unfold RAWBITVECTOR_LIST.size.
        now rewrite map_length.
Qed.



Lemma sextend_interp_main: forall bs1 bsres (n i: N),
                           check_sextend bs1 bsres i = true ->
                           @RAWBITVECTOR_LIST.bv_sextn n i
                             (map (Lit.interp rho) bs1) = map (Lit.interp rho) bsres.
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros. simpl.
         unfold check_zextend in H. simpl in H.
         case_eq (forallb2 eq_carry_lit
          (lit_to_carry (sextend_lit [] (N.to_nat i))) bsres).
         intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         simpl in H0.
         unfold RAWBITVECTOR_LIST.bv_sextn.
         now rewrite sextend_interp_empty.
         intros. 
         unfold check_sextend in H.
         rewrite H0 in H. now contradict H0.
       - intros. unfold RAWBITVECTOR_LIST.bv_sextn, check_sextend in H.
         case_eq (
          forallb2 eq_carry_lit
          (lit_to_carry
             (sextend_lit (xbs1 :: xsbs1) (N.to_nat i)))
          bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         simpl in H0.

         unfold RAWBITVECTOR_LIST.bv_sextn in *.
         case_eq (N.to_nat i). intros. rewrite H1 in H0.
         now simpl in *.
         intros. rewrite H1 in H0.
         rewrite <- H0.
         
         rewrite sextend_interp_all.
         now simpl.

         rewrite H0 in H. now contradict H.
Qed.

Lemma valid_check_bbSextend pos lres : C.valid rho (check_bbSextend pos lres).
Proof.
      unfold check_bbSextend.
      case_eq (S.get s pos); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq2; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq4.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq5.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | | | | ]  a1'  Heq6; try (intros; now apply C.interp_true).
      (* BVsextend *)
    - case_eq ((a1 == a1')); simpl; intros Heq7; try (now apply C.interp_true).
        case_eq (
            check_sextend bs1 bsres i && (N.of_nat (Datatypes.length bs1) =? n)%N
        ); simpl; intros Heq8; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq3.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq5. simpl.

        apply BITVECTOR_LIST.bv_eq_reflect.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy. }
        specialize (@H0 H1). rewrite Heq6 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H3 in H0; try (now contradict H0).
        rename H0 into Hv.

        generalize (Hs pos). intros HSp. unfold C.valid in HSp. rewrite Heq1 in HSp.
        unfold C.interp in HSp. unfold existsb in HSp. rewrite orb_false_r in HSp.
        unfold Lit.interp in HSp. rewrite Heq2 in HSp. unfold Var.interp in HSp.
        rewrite rho_interp in HSp. rewrite Heq4 in HSp. simpl in HSp.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp.

        unfold get_type' in H2. unfold v_type in H2.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2.

        (** case a1 = a1' **)
        rewrite eqb_spec in Heq7; rewrite Heq7 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H0. rewrite Heq6. simpl.
        unfold interp_bv. unfold apply_unop.

        rewrite !Atom.t_interp_wf; trivial.

        revert v_vala1 Htia1. rewrite H2.
        intros v_vala1 Htia1.
        rewrite Htia1.
        rewrite !Typ.cast_refl.
        unfold Bval.

        assert (H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bsres))) = (i + n)%N).
        {
           rewrite andb_true_iff in Heq8.
           destruct Heq8 as (Heq8a, Heq8b).
           rewrite map_length.
           specialize (@sextend_interp_main bs1 bsres n i).
           intros.
           apply H4 in Heq8a.
           unfold RAWBITVECTOR_LIST.bv_sextn in Heq8a.
           assert (length (RAWBITVECTOR_LIST.sextend (map (Lit.interp rho) bs1) (N.to_nat i)) 
           = length (map (Lit.interp rho) bsres)).
           { now rewrite Heq8a. }
           rewrite RAWBITVECTOR_LIST.length_sextend, !map_length in H5.
           apply (f_equal (N.of_nat)) in H5.
           rewrite <- H5.
           
           rewrite N.eqb_eq in Heq8b.
           apply (f_equal (N.to_nat)) in Heq8b.
           rewrite Nat2N.id in Heq8b.
           rewrite Heq8b. lia.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100.
        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp.
        unfold interp_bv in HSp.
        rewrite Htia1 in HSp.
        unfold interp_bv in HSp. 

        revert HSp.

        assert (H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = n).
        {
           rewrite andb_true_iff in Heq8.
           destruct Heq8 as (Heq8a, Heq8b).
           rewrite map_length.
           now rewrite N.eqb_eq in Heq8b.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp. simpl.
        unfold BITVECTOR_LIST.bv_sextn.
        apply eq_rec. simpl.
        rewrite andb_true_iff in Heq8.
        destruct Heq8 as (Heq8a, Heq8b).
        now apply sextend_interp_main.
Qed.


  End Proof.

End Checker.


(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)
