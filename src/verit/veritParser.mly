%{

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand    *                                                *)
(*     Benjamin Grégoire *                                                *)
(*     Chantal Keller    *                                                *)
(*     Alain Mebsout     ♯                                                *)
(*     Burak Ekici       ♯                                                *)
(*                                                                        *)
(*     * Inria - École Polytechnique - Université Paris-Sud               *)
(*     ♯ The University of Iowa                                           *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


  open SmtAtom
  open SmtForm
  open VeritSyntax



  let parse_bv s =
    let l = ref [] in
    for i = 2 to String.length s - 1 do
      match s.[i] with
      | '0' -> l := false :: !l
      | '1' -> l := true :: !l
      | _ -> assert false
    done;
    !l
    
%}


/*
  définition des lexèmes
*/

%token EOL SAT
%token COLON
%token LPAR RPAR LBRACKET RBRACKET
%token NOT XOR ITE EQ LT LEQ GT GEQ PLUS MINUS MULT OPP LET DIST BBT BITOF BVAND BVOR BVXOR BVADD BVMUL BVULT BVSLT BVULE BVSLE BVCONC BVEXTR BVZEXT BVSEXT BVNOT BVNEG SELECT STORE DIFF BVSHL BVSHR
%token INPU DEEP TRUE FALS ANDP ANDN ORP ORN XORP1 XORP2 XORN1 XORN2 IMPP IMPN1 IMPN2 EQUP1 EQUP2 EQUN1 EQUN2 ITEP1 ITEP2 ITEN1 ITEN2 EQRE EQTR EQCO EQCP DLGE LAGE LATA DLDE LADE FINS EINS SKEA SKAA QNTS QNTM RESO WEAK AND NOR OR NAND XOR1 XOR2 NXOR1 NXOR2 IMP NIMP1 NIMP2 EQU1 EQU2 NEQU1 NEQU2 ITE1 ITE2 NITE1 NITE2 TPAL TLAP TPLE TPNE TPDE TPSA TPIE TPMA TPBR TPBE TPSC TPPP TPQT TPQS TPSK SUBP FLAT HOLE BBVA BBCONST BBEXTR BBZEXT BBSEXT BBEQ BBDIS BBOP BBADD BBMUL BBULT BBSLT BBNOT BBNEG BBCONC ROW1 ROW2 EXTE BBSHL BBSHR
%token <int> INT SHARPINT
%token <Big_int.big_int> BIGINT
%token <string> VAR BINDVAR BITV

/* type de "retour" du parseur : une clause */
%type <int> line
%start line


%%

line:
  | SAT                                                    { raise Sat }
  | INT COLON LPAR typ clause                   RPAR EOL   { mk_clause ($1,$4,$5,[]) }
  | INT COLON LPAR typ clause clause_ids_params RPAR EOL   { mk_clause ($1,$4,$5,$6) }
;

typ:
  | INPU                                                   { Inpu  }
  | DEEP                                                   { Deep  }
  | TRUE                                                   { True  }
  | FALS                                                   { Fals  }
  | ANDP                                                   { Andp  }
  | ANDN                                                   { Andn  }
  | ORP                                                    { Orp   }
  | ORN                                                    { Orn   }
  | XORP1                                                  { Xorp1 }
  | XORP2                                                  { Xorp2 }
  | XORN1                                                  { Xorn1 }
  | XORN2                                                  { Xorn2 }
  | IMPP                                                   { Impp  }
  | IMPN1                                                  { Impn1 }
  | IMPN2                                                  { Impn2 }
  | EQUP1                                                  { Equp1 }
  | EQUP2                                                  { Equp2 }
  | EQUN1                                                  { Equn1 }
  | EQUN2                                                  { Equn2 }
  | ITEP1                                                  { Itep1 }
  | ITEP2                                                  { Itep2 }
  | ITEN1                                                  { Iten1 }
  | ITEN2                                                  { Iten2 }
  | EQRE                                                   { Eqre  }
  | EQTR                                                   { Eqtr  }
  | EQCO                                                   { Eqco  }
  | EQCP                                                   { Eqcp  }
  | DLGE                                                   { Dlge  }
  | LAGE                                                   { Lage  }
  | LATA                                                   { Lata  }
  | DLDE                                                   { Dlde  }
  | LADE                                                   { Lade  }
  | FINS                                                   { Fins  }
  | EINS                                                   { Eins  }
  | SKEA                                                   { Skea  }
  | SKAA                                                   { Skaa  }
  | QNTS                                                   { Qnts  }
  | QNTM                                                   { Qntm  }
  | RESO                                                   { Reso  }
  | WEAK                                                   { Weak  }
  | AND                                                    { And   }
  | NOR                                                    { Nor   }
  | OR                                                     { Or    }
  | NAND                                                   { Nand  }
  | XOR1                                                   { Xor1  }
  | XOR2                                                   { Xor2  }
  | NXOR1                                                  { Nxor1 }
  | NXOR2                                                  { Nxor2 }
  | IMP                                                    { Imp   }
  | NIMP1                                                  { Nimp1 }
  | NIMP2                                                  { Nimp2 }
  | EQU1                                                   { Equ1  }
  | EQU2                                                   { Equ2  }
  | NEQU1                                                  { Nequ1 }
  | NEQU2                                                  { Nequ2 }
  | ITE1                                                   { Ite1  }
  | ITE2                                                   { Ite2  }
  | NITE1                                                  { Nite1 }
  | NITE2                                                  { Nite2 }
  | TPAL                                                   { Tpal  }
  | TLAP                                                   { Tlap  }
  | TPLE                                                   { Tple  }
  | TPNE                                                   { Tpne  }
  | TPDE                                                   { Tpde  }
  | TPSA                                                   { Tpsa  }
  | TPIE                                                   { Tpie  }
  | TPMA                                                   { Tpma  }
  | TPBR                                                   { Tpbr  }
  | TPBE                                                   { Tpbe  }
  | TPSC                                                   { Tpsc  }
  | TPPP                                                   { Tppp  }
  | TPQT                                                   { Tpqt  }
  | TPQS                                                   { Tpqs  }
  | TPSK                                                   { Tpsk  }
  | SUBP                                                   { Subp  }
  | FLAT                                                   { Flat  }
  | HOLE                                                   { Hole  }
  | BBVA                                                   { Bbva  }
  | BBCONST                                                { Bbconst }
  | BBEQ                                                   { Bbeq  }
  | BBDIS                                                  { Bbdis }
  | BBOP                                                   { Bbop  }
  | BBADD                                                  { Bbadd }
  | BBMUL                                                  { Bbmul }
  | BBULT                                                  { Bbult }
  | BBSLT                                                  { Bbslt }
  | BBNOT                                                  { Bbnot }
  | BBNEG                                                  { Bbneg }
  | BBCONC                                                 { Bbconc }
  | BBEXTR                                                 { Bbextr }
  | BBZEXT                                                 { Bbzext }
  | BBSEXT                                                 { Bbsext }
  | BBSHL                                                  { Bbshl }
  | BBSHR                                                  { Bbshr }
  | ROW1                                                   { Row1  }
  | ROW2                                                   { Row2  }
  | EXTE                                                   { Exte  }
;

clause:
  | LPAR          RPAR                                     { [] }
  | LPAR lit_list RPAR                                     { $2 }
;

lit_list:
  | lit                                                    { [$1] }
  | lit lit_list                                           { $1::$2 }
;

lit:   /* returns a SmtAtom.Form.t */
  | name_term                                              { lit_of_atom_form_lit rf $1 }
  | LPAR NOT lit RPAR                                      { Form.neg $3 }
;

name_term:   /* returns a SmtAtom.Form.pform or a SmtAtom.hatom */
  | SHARPINT                                              { get_solver $1 }
  | SHARPINT COLON LPAR term RPAR                         { let res = $4 in add_solver $1 res; res }
  | BITV                                                   { Atom (Atom.mk_bvconst ra (parse_bv $1)) }
  | TRUE                                                   { Form Form.pform_true }
  | FALS                                                   { Form Form.pform_false }
  | VAR                                                    { Atom (Atom.get ra (Aapp (get_fun $1,[||]))) }
  | BINDVAR                                                { Hashtbl.find hlets $1 }
  | INT                                                    { Atom (Atom.hatom_Z_of_int ra $1) }
  | BIGINT                                                 { Atom (Atom.hatom_Z_of_bigint ra $1) }

;

term:   /* returns a SmtAtom.Form.pform or a SmtAtom.hatom */
  | LPAR term RPAR                                         { $2 }

  /* Formulae */
  | TRUE                                                   { Form Form.pform_true }
  | FALS                                                   { Form Form.pform_false }
  | AND lit_list                                           { Form (Fapp (Fand, Array.of_list $2)) }
  | OR lit_list                                            { Form (Fapp (For, Array.of_list $2)) }
  | IMP lit_list                                           { Form (Fapp (Fimp, Array.of_list $2)) }
  | XOR lit_list                                           { Form (Fapp (Fxor, Array.of_list $2)) }
  | ITE lit_list                                           { Form (Fapp (Fite, Array.of_list $2)) }
  | BBT name_term LBRACKET lit_list RBRACKET               { match $2 with | Atom a -> Form (FbbT (a, $4)) | _ -> assert false }

  /* Atoms */
  | INT                                                    { Atom (Atom.hatom_Z_of_int ra $1) }
  | BIGINT                                                 { Atom (Atom.hatom_Z_of_bigint ra $1) }
  | BITV                                                   { Atom (Atom.mk_bvconst ra (parse_bv $1)) }
  | LT name_term name_term                                 { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_lt ra h1 h2) | _,_ -> assert false }
  | LEQ name_term name_term                                { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_le ra h1 h2) | _,_ -> assert false }
  | GT name_term name_term                                 { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_gt ra h1 h2) | _,_ -> assert false }
  | GEQ name_term name_term                                { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_ge ra h1 h2) | _,_ -> assert false }
  | PLUS name_term name_term                               { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_plus ra h1 h2) | _,_ -> assert false }
  | MULT name_term name_term                               { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_mult ra h1 h2) | _,_ -> assert false }
  | MINUS name_term name_term                              { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_minus ra h1 h2) | _,_ -> assert false }
  | MINUS name_term                                        { match $2 with | Atom h -> Atom (Atom.mk_opp ra h) | _ -> assert false }
  | OPP name_term                                          { match $2 with | Atom h -> Atom (Atom.mk_opp ra h) | _ -> assert false }
  | DIST args                                              { let a = Array.of_list $2 in Atom (Atom.mk_distinct ra (Atom.type_of a.(0)) a) }
  | BITOF INT name_term
    { match $3 with
      | Atom h -> (match Atom.type_of h with
                   | TBV s -> Atom (Atom.mk_bitof ra s $2 h)
                   | _ -> assert false)
      | _ -> assert false }
    
  | BVNOT name_term
    { match $2 with
      | Atom h -> (match Atom.type_of h with
                   | TBV s -> Atom (Atom.mk_bvnot ra s h)
                   | _ -> assert false)
      | _ -> assert false }
    
  | BVAND name_term name_term
    { match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvand ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false }
    
  | BVOR name_term name_term {
    match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvor ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false
    }
  | BVXOR name_term name_term {
    match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvxor ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false
    }
  | BVNEG name_term
    { match $2 with
      | Atom h -> (match Atom.type_of h with
                   | TBV s -> Atom (Atom.mk_bvneg ra s h)
                   | _ -> assert false)
      | _ -> assert false }
  | BVADD name_term name_term {
    match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvadd ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false
    }         
  | BVMUL name_term name_term {
    match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvmult ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false
    }        
  | BVULT name_term name_term {
    match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvult ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false
    }        
  | BVSLT name_term name_term {
    match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvslt ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false
    }        
  | BVULE name_term name_term {
    match $2,$3 with
    | Atom h1, Atom h2 ->
       (match Atom.type_of h1 with
        | TBV s ->
           let a = Atom (Atom.mk_bvult ra s h2 h1) in
           Lit (Form.neg (lit_of_atom_form_lit rf a))
        | _ -> assert false)
    | _,_ -> assert false
    }        
  | BVSLE name_term name_term {
    match $2,$3 with
    | Atom h1, Atom h2 ->
       (match Atom.type_of h1 with
        | TBV s ->
           let a = Atom (Atom.mk_bvslt ra s h2 h1) in
           Lit (Form.neg (lit_of_atom_form_lit rf a))
        | _ -> assert false)
    | _,_ -> assert false
    }        
  | BVSHL name_term name_term {
    match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvshl ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false
    }        
  | BVSHR name_term name_term {
    match $2,$3 with
      | Atom h1, Atom h2 -> (match Atom.type_of h1 with
                             | TBV s -> Atom (Atom.mk_bvshr ra s h1 h2)
                             | _ -> assert false)
      | _,_ -> assert false
    }        
  | BVCONC name_term name_term {
    match $2,$3 with
    | Atom h1, Atom h2 ->
       (match Atom.type_of h1, Atom.type_of h2 with
        | TBV s1, TBV s2 -> Atom (Atom.mk_bvconcat ra s1 s2 h1 h2)
        | _ -> assert false)
    | _,_ -> assert false
    }
  | BVEXTR INT INT name_term
    { let j, i = $2, $3 in
      match $4 with
      | Atom h -> (match Atom.type_of h with
                   | TBV s -> Atom (Atom.mk_bvextr ra ~s ~i ~n:(j-i+1) h)
                   | _ -> assert false)
      | _ -> assert false }
  | BVZEXT INT name_term
    { let n = $2 in
      match $3 with
      | Atom h -> (match Atom.type_of h with
                   | TBV s -> Atom (Atom.mk_bvzextn ra ~s ~n h)
                   | _ -> assert false)
      | _ -> assert false }
  | BVSEXT INT name_term
    { let n = $2 in
      match $3 with
      | Atom h -> (match Atom.type_of h with
                   | TBV s -> Atom (Atom.mk_bvsextn ra ~s ~n h)
                   | _ -> assert false)
      | _ -> assert false }
  | SELECT name_term name_term {
    match $2,$3 with
    | Atom h1, Atom h2 ->
       (match Atom.type_of h1 with
        | TFArray (ti,te) -> Atom (Atom.mk_select ra ti te h1 h2)
        | _ -> assert false)
    | _,_ -> assert false
    }        
  | DIFF name_term name_term {
    match $2,$3 with
    | Atom h1, Atom h2 ->
       (match Atom.type_of h1 with
        | TFArray (ti,te) -> Atom (Atom.mk_diffarray ra ti te h1 h2)
        | _ -> assert false)
    | _,_ -> assert false
    }        
  | STORE name_term name_term name_term {
    match $2,$3,$4 with
    | Atom h1, Atom h2, Atom h3 ->
       (match Atom.type_of h1 with
        | TFArray (ti,te) -> Atom (Atom.mk_store ra ti te h1 h2 h3)
        | _ -> assert false)
    | _ -> assert false
    }        
  | VAR                                                    { Atom (Atom.get ra (Aapp (get_fun $1, [||]))) }
  | VAR args                                               { Atom (Atom.get ra (Aapp (get_fun $1, Array.of_list $2))) }

  /* Both */
  | EQ name_term name_term                                 { let t1 = $2 in let t2 = $3 in match t1,t2 with | Atom h1, Atom h2 when (match Atom.type_of h1 with | Tbool -> false | _ -> true) -> Atom (Atom.mk_eq ra (Atom.type_of h1) h1 h2) | _, _ -> Form (Fapp (Fiff, [|lit_of_atom_form_lit rf t1; lit_of_atom_form_lit rf t2|])) }
  /* This rule introduces lots of shift/reduce conflicts */
  | EQ lit lit                                             { let t1 = $2 in let t2 = $3 in Form (Fapp (Fiff, [|t1; t2|])) }
  | LET LPAR bindlist RPAR name_term                       { $3; $5 }
  | BINDVAR                                                { Hashtbl.find hlets $1 }
;

bindlist:
  | LPAR BINDVAR name_term RPAR                            { Hashtbl.add hlets $2 $3 }
  | LPAR BINDVAR lit RPAR                                  { Hashtbl.add hlets $2 (Lit $3) }
  | LPAR BINDVAR name_term RPAR bindlist                   { Hashtbl.add hlets $2 $3; $5 }
  | LPAR BINDVAR lit RPAR bindlist                         { Hashtbl.add hlets $2 (Lit $3); $5 }

args:
  | name_term                                              { match $1 with Atom h -> [h] | _ -> assert false }
  | name_term args                                         { match $1 with Atom h -> h::$2 | _ -> assert false }
;

clause_ids_params:
  | int_list                                               { $1 }
;

int_list:
  | INT                                                    { [$1] }
  | INT int_list                                           { let x1 = $1 in let x2 = $2 in x1::x2 }
;
