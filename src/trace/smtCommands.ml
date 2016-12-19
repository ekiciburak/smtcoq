(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Entries
open Declare
open Decl_kinds

open SmtMisc
open CoqTerms
open SmtForm
open SmtAtom
open SmtTrace
open SmtCertif


let euf_checker_modules = [ ["SMTCoq";"Trace";"Euf_Checker"; "Word"] ]
let certif_ops args = CoqTerms.make_certif_ops euf_checker_modules args
let cCertif = gen_constant euf_checker_modules "Certif"
let ccertif = gen_constant euf_checker_modules "certif"
let cchecker = gen_constant euf_checker_modules "checker"
let cchecker_correct = gen_constant euf_checker_modules "checker_correct"
let cchecker_b_correct =
  gen_constant euf_checker_modules "checker_b_correct"
let cchecker_b = gen_constant euf_checker_modules "checker_b"
let cchecker_eq_correct =
  gen_constant euf_checker_modules "checker_eq_correct"
let cchecker_eq = gen_constant euf_checker_modules "checker_eq"


(* Given an SMT-LIB2 file and a certif, build the corresponding objects *)

let compute_roots roots last_root =
  let r = ref last_root in
  while (has_prev !r) do
    r := prev !r
  done;

  let rec find_root i root = function
    | [] -> assert false
    | t::q -> if Form.equal t root then i else find_root (i+1) root q in

  let rec used_roots acc r =
    if isRoot r.kind then
      match r.value with
        | Some [root] ->
           let j = find_root 0 root roots in
           used_roots (j::acc) (next r)
        | _ -> assert false
    else acc
  in

  used_roots [] !r


let interp_uf t_i ta tf c =
  let rec interp = function
    | [] -> Lazy.force cfalse
    | [l] -> Form.interp_to_coq (Atom.interp_to_coq t_i ta) tf l
    | l::c -> mklApp corb [|Form.interp_to_coq (Atom.interp_to_coq t_i ta) tf l; interp c|] in
  interp c

let interp_conseq_uf t_i (prem, concl) =
  let ta = Hashtbl.create 17 in
  let tf = Hashtbl.create 17 in
  let rec interp = function
    | [] -> mklApp cis_true [|interp_uf t_i ta tf concl|]
    | c::prem -> Term.mkArrow (mklApp cis_true [|interp_uf t_i ta tf c|]) (interp prem) in
  interp prem


let string_coq_constr t =
  let rec fix rf x = rf (fix rf) x in
  let pr = fix
      Ppconstr.modular_constr_pr Pp.mt Structures.ppconstr_lsimpleconstr in
  Pp.string_of_ppcmds (pr (Structures.constrextern_extern_constr t))

  
let print_assm ty =
  Printf.printf "WARNING: assuming the following hypothesis:\n%s\n@."
    (string_coq_constr ty)


let parse_certif t_i t_func t_atom t_form root used_root trace (rt, ro, ra, rf, roots, max_id, confl) =

  let t_i' = make_t_i rt in
  let ce5 = Structures.mkUConst t_i' in
  let ct_i = Term.mkConst (declare_constant t_i (DefinitionEntry ce5, IsDefinition Definition)) in

  let t_func' = make_t_func ro ct_i in
  let ce6 = Structures.mkUConst t_func' in
  let ct_func = Term.mkConst (declare_constant t_func (DefinitionEntry ce6, IsDefinition Definition)) in

  let t_atom' = Atom.interp_tbl ra in
  let ce1 = Structures.mkUConst t_atom' in
  let ct_atom = Term.mkConst (declare_constant t_atom (DefinitionEntry ce1, IsDefinition Definition)) in

  let t_form' = snd (Form.interp_tbl rf) in
  let ce2 = Structures.mkUConst t_form' in
  let ct_form = Term.mkConst (declare_constant t_form (DefinitionEntry ce2, IsDefinition Definition)) in

  let (tres, last_root, cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i))
      (interp_conseq_uf ct_i) (certif_ops (Some [|ct_i; ct_func; ct_atom; ct_form|])) confl in
  List.iter (fun (v,ty) ->
    let _ = Structures.declare_new_variable v ty in
    print_assm ty
  ) cuts;

  let used_roots = compute_roots roots last_root in
  let roots =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Structures.mkArray (Lazy.force cint, res) in
  let used_roots =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Structures.mkArray (Lazy.force cint, res)|] in
  let ce3 = Structures.mkUConst roots in
  let _ = declare_constant root (DefinitionEntry ce3, IsDefinition Definition) in
  let ce3' = Structures.mkUConst used_roots in
  let _ = declare_constant used_root (DefinitionEntry ce3', IsDefinition Definition) in

  let certif =
    mklApp cCertif [|ct_i; ct_func; ct_atom; ct_form; mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in
  let ce4 = Structures.mkUConst certif in
  let _ = declare_constant trace (DefinitionEntry ce4, IsDefinition Definition) in

  ()


(* Given an SMT-LIB2 file and a certif, build the corresponding theorem *)

let interp_roots t_i roots =
  let interp = Form.interp_to_coq (Atom.interp_to_coq t_i (Hashtbl.create 17)) (Hashtbl.create 17) in
  match roots with
    | [] -> Lazy.force ctrue
    | f::roots -> List.fold_left (fun acc f -> mklApp candb [|acc; interp f|]) (interp f) roots

let theorem name (rt, ro, ra, rf, roots, max_id, confl) =
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in
  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in
  let nused_roots = mkName "used_roots" in
  let nd = mkName "d" in

  let v = Term.mkRel in

  let t_i = make_t_i rt in
  let t_func = make_t_func ro (v 1 (*t_i*)) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in

  let (tres,last_root,cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i))
      (interp_conseq_uf t_i)
      (certif_ops (Some [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *)|])) confl in
  List.iter (fun (v,ty) ->
    let _ = Structures.declare_new_variable v ty in
    print_assm ty
  ) cuts;

  let certif =
    mklApp cCertif [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let used_roots = compute_roots roots last_root in
  let used_rootsCstr =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Structures.mkArray (Lazy.force cint, res)|] in
  let rootsCstr =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Structures.mkArray (Lazy.force cint, res) in

  let theorem_concl = mklApp cnot [|mklApp cis_true [|interp_roots t_i roots|]|] in
  let theorem_proof =
   Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
   Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
   Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
   Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
   Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
   Term.mkLetIn (nused_roots, used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|],
   Term.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
   mklApp cchecker_correct
     [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*);
	vm_cast_true
	  (mklApp cchecker [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|])|]))))))) in

  let ce = Structures.mkTConst theorem_proof theorem_concl in
  let _ = declare_constant name (DefinitionEntry ce, IsDefinition Definition) in
  ()


(* Given an SMT-LIB2 file and a certif, call the checker *)

let checker (rt, ro, ra, rf, roots, max_id, confl) =
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in
  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in
  let nused_roots = mkName "used_roots" in
  let nd = mkName "d" in

  let v = Term.mkRel in

  let t_i = make_t_i rt in
  let t_func = make_t_func ro (v 1 (*t_i*)) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in

  let (tres,last_root,cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i))
      (interp_conseq_uf t_i)
      (certif_ops (Some [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *)|])) confl in
  List.iter (fun (v,ty) ->
    let _ = Structures.declare_new_variable v ty in
    print_assm ty
  ) cuts;

  let certif =
    mklApp cCertif [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let used_roots = compute_roots roots last_root in
  let used_rootsCstr =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Structures.mkArray (Lazy.force cint, res)|] in
  let rootsCstr =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Structures.mkArray (Lazy.force cint, res) in

  let tm =
   Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
   Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
   Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
   Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
   Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
   Term.mkLetIn (nused_roots, used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|],
   Term.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
   mklApp cchecker [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|]))))))) in

  let res = Vnorm.cbv_vm (Global.env ()) tm (Lazy.force CoqTerms.cbool) in
  Format.eprintf "     = %s\n     : bool@."
    (if Term.eq_constr res (Lazy.force CoqTerms.ctrue) then
        "true" else "false")


(* Tactic *)

let build_body rt ro ra rf l b (max_id, confl) =
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in
  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in

  let v = Term.mkRel in

  let t_i = make_t_i rt in
  let t_func = Structures.lift 1 (make_t_func ro (v 0 (*t_i - 1*))) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let (tres,_,cuts) = SmtTrace.to_coq Form.to_coq
      (interp_conseq_uf t_i)
      (certif_ops (Some [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|])) confl in
  let certif =
    mklApp cCertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let proof =
    Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
    Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1 (*t_i*)|]|],
    Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
    Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
    Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
    mklApp cchecker_b_correct
      [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l; b; v 1 (*certif*);
	vm_cast_true (mklApp cchecker_b [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l; b; v 1 (*certif*)|])|])))))
  in

  (proof, cuts)


let build_body_eq rt ro ra rf l1 l2 l (max_id, confl) =
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in
  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in

  let v = Term.mkRel in

  let t_i = make_t_i rt in
  let t_func = Structures.lift 1 (make_t_func ro (v 0 (*t_i*))) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let (tres,_,cuts) = SmtTrace.to_coq Form.to_coq
      (interp_conseq_uf t_i)
      (certif_ops (Some [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|])) confl in
  let certif =
    mklApp cCertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let proof =
    Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
    Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1 (*t_i*)|]|],
    Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
    Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
    Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
    mklApp cchecker_eq_correct
      [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l1; l2; l; v 1 (*certif*);
	vm_cast_true (mklApp cchecker_eq [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l1; l2; l; v 1 (*certif*)|])|])))))
  in

  (proof, cuts)


let get_arguments concl =
  let f, args = Term.decompose_app concl in
  match args with
  | [ty;a;b] when (Term.eq_constr f (Lazy.force ceq)) && (Term.eq_constr ty (Lazy.force cbool)) -> a, b
  | [a] when (Term.eq_constr f (Lazy.force cis_true)) -> a, Lazy.force ctrue
  | _ -> failwith ("Verit.tactic: can only deal with equality over bool")


let make_proof call_solver env rt ro ra rf l =
  let root = SmtTrace.mkRootV [l] in
  call_solver env rt ro ra rf (root,l)


let tactic call_solver rt ro ra rf env sigma t =
  let (forall_let, concl) = Term.decompose_prod_assum t in
  let env = Environ.push_rel_context forall_let env in
  let a, b = get_arguments concl in
  let (body, cuts) =
    if ((Term.eq_constr b (Lazy.force ctrue)) ||
        (Term.eq_constr b (Lazy.force cfalse))) then
      let l = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf a in
      let l' =
        if (Term.eq_constr b (Lazy.force ctrue)) then Form.neg l else l in
      let max_id_confl = make_proof call_solver env rt ro ra rf l' in
      build_body rt ro ra rf (Form.to_coq l) b max_id_confl
    else
      let l1 = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf a in
      let l2 = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf b in
      let l = Form.neg (Form.get rf (Fapp(Fiff,[|l1;l2|]))) in
      let max_id_confl = make_proof call_solver env rt ro ra rf l in
      build_body_eq rt ro ra rf (Form.to_coq l1) (Form.to_coq l2)
        (Form.to_coq l) max_id_confl in
  let compose_lam_assum forall_let body =
    List.fold_left (fun t rd -> Term.mkLambda_or_LetIn rd t) body forall_let in
  let quantify_assum forall_let body =
    List.fold_left (fun t rd -> Term.mkProd_or_LetIn rd t) body forall_let in
  let res = compose_lam_assum forall_let body in
  let tac =
    List.fold_right (fun (eqn, eqt) tac ->
      Structures.tclTHENLAST
        (Structures.assert_before (Names.Name eqn) eqt)
        tac
    ) (Btype.get_cuts rt) (Structures.vm_cast_no_check res)
  in
  List.fold_left (fun tac (n, t) ->
    let t = quantify_assum forall_let t in
      Structures.tclTHENLAST
        (Structures.assert_before (Names.Name n) t)
        tac
    ) tac cuts



open SExpr
open Smtlib2_genConstr
open Format

let get_rel_dec_name (n, _, _) = n  

let vstring_i env cf =
  if Term.isRel cf then
    let dbi = Term.destRel cf in
    let s =
      Environ.lookup_rel dbi env
      |> get_rel_dec_name
      |> function
      | Names.Name id -> Names.string_of_id id
      | Names.Anonymous -> "?" in
    s, dbi
  else string_coq_constr cf, 0

let smt2_id_to_coq_string env t_i ra rf name =
  try
    Scanf.sscanf name "op_%d" SmtAtom.Atom.get_coq_term_op
    |> vstring_i env
  with _ -> name, 0


let op_to_coq_string op = match op with
  | "=" | "+" | "-" | "*" | "/" -> op
  | "or" -> "||"
  | "and" -> "&&"
  | "xor" -> "xorb"
  | "=>" -> "implb"
  | _ -> op


let coq_bv_string s =
  let rec aux acc = function
    | true :: r -> aux (acc ^ "|1") r 
    | false :: r -> aux (acc ^ "|0") r 
    | [] -> "#b" ^ acc ^ "|"
  in
  if String.length s < 3 ||
     not (s.[0] = '#' && s.[1] = 'b') then failwith "not bv";
  aux "" (parse_smt2bv s)


let is_bvint bs = 
  try Scanf.sscanf bs "bv%d" (fun _ -> true)
  with _ -> false


let rec smt2_sexpr_to_coq_string env t_i ra rf =
  let open SExpr in function
  | Atom "true" -> "true"
  | Atom "false" -> "false"
  | Atom s ->
    (try ignore (int_of_string s); s
     with Failure _ ->
     try coq_bv_string s
     with Failure _ ->
     try fst (smt2_id_to_coq_string env t_i ra rf s)
     with _ -> s)
  | List [Atom "as"; s; _] -> smt2_sexpr_to_coq_string env t_i ra rf s
  | List [Atom "_"; Atom bs; Atom s] when is_bvint bs ->
    Scanf.sscanf bs "bv%d" (fun i ->
        coq_bv_string (int_bv i (int_of_string s)))
  | List [Atom "-"; Atom _ as s] ->
    sprintf "-%s"
      (smt2_sexpr_to_coq_string env t_i ra rf s)
  | List [Atom "-"; s] ->
    sprintf "(- %s)"
      (smt2_sexpr_to_coq_string env t_i ra rf s)
  | List [Atom (("+"|"-"|"*"|"/"|"or"|"and"|"=") as op); s1; s2] ->
    sprintf "%s %s %s"
      (smt2_sexpr_to_coq_string env t_i ra rf s1)
      (op_to_coq_string op)
      (smt2_sexpr_to_coq_string env t_i ra rf s2)
  | List [Atom (("xor"|"=>"|"") as op); s1; s2] ->
    sprintf "(%s %s %s)"
      (op_to_coq_string op)
      (smt2_sexpr_to_coq_string env t_i ra rf s1)
      (smt2_sexpr_to_coq_string env t_i ra rf s2)
  | List [Atom "select"; a; i] ->
    sprintf "%s[%s]"
      (smt2_sexpr_to_coq_string env t_i ra rf a)
      (smt2_sexpr_to_coq_string env t_i ra rf i)
  | List [Atom "store"; a; i; v] ->
    sprintf "%s[%s <- %s]"
      (smt2_sexpr_to_coq_string env t_i ra rf a)
      (smt2_sexpr_to_coq_string env t_i ra rf i)
      (smt2_sexpr_to_coq_string env t_i ra rf v)
  | List [Atom "ite"; c; s1; s2] ->
    sprintf "if %s then %s else %s"
      (smt2_sexpr_to_coq_string env t_i ra rf c)
      (smt2_sexpr_to_coq_string env t_i ra rf s1)
      (smt2_sexpr_to_coq_string env t_i ra rf s2)
  | List l ->
    sprintf "(%s)"
      (String.concat " " (List.map (smt2_sexpr_to_coq_string env t_i ra rf) l))


let str_contains s1 s2 =
  let re = Str.regexp_string s2 in
  try ignore (Str.search_forward re s1 0); true
  with Not_found -> false

let lambda_to_coq_string l s =
  Format.sprintf "fun %s => %s"
    (String.concat " "
       (List.map (function
            | List [Atom v; _] ->
              if str_contains s v then v else "_"
            | _ -> assert false) l))
    s

let model_item env rt ro ra rf =
  let t_i = make_t_i rt in
  function
  | List [Atom "define-fun"; Atom n; List []; _; expr] ->
    (smt2_id_to_coq_string env t_i ra rf n,
     smt2_sexpr_to_coq_string env t_i ra rf expr)
    
  | List [Atom "define-fun"; Atom n; List l; _; expr] ->
    (smt2_id_to_coq_string env t_i ra rf n,
     lambda_to_coq_string l
       (smt2_sexpr_to_coq_string env t_i ra rf expr))
    
  | _ -> Structures.error ("Could not reconstruct model")


let model env rt ro ra rf = function
  | List (Atom "model" :: l) ->
    List.map (model_item env rt ro ra rf) l
    |> List.sort (fun ((_ ,i1), _) ((_, i2), _) -> i2 - i1)
  | _ -> Structures.error ("No model")
    

let model_string env rt ro ra rf s =
  String.concat "\n"
    (List.map (fun ((x, _) ,v) -> Format.sprintf "%s := %s" x v)
       (model env rt ro ra rf s))
