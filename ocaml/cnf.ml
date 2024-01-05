(* SAT encoding of TA for termination checking *)
open Format
open Util
open Term
open Trs
open Bta

(* literals *)
type 'pvar lit =
  | PLit of 'pvar
  | NLit of 'pvar
let pp_lit pp_v ppf = function
  | PLit v -> fprintf ppf "PLit(@[%a@])" pp_v v
  | NLit v -> fprintf ppf "NLit(@[%a@])" pp_v v

type 'pvar clause = 'pvar lit list
let pp_clause pp_v = pp_list (pp_lit pp_v)

(* encoding variables *)
type encvar =
  | Final of state
  | Trans of symbol * state list * state
  | HasSt of term * state VarMap.t * state
  | Conjc of encvar list
  | StRel of state * state

let rec pp_encvar ppf = function
  | Final q -> fprintf ppf "Final(@[%a@])" pp_state q
  | Trans(f, qs, q) -> fprintf ppf "Trans(@[%a@], @[%a@], @[%a@])"
                         pp_symbol f (pp_list pp_state) qs pp_state q
  | HasSt(t, vmap, q) -> fprintf ppf "HasSt(@[%a@], @[%a@], @[%a@])"
                           pp_term t (pp_var_map pp_state) vmap pp_state q
  | Conjc(vs) -> fprintf ppf "Conjc @[%a@]" (pp_list pp_encvar) vs
  | StRel(q, p) -> fprintf ppf "StRel(@[%a@], @[%a@])"
                     pp_state q pp_state p

module CNF = Set.Make(struct
  type t = encvar clause
  let compare = compare
end)

let (=>) u v : 'pvar clause = [NLit u; PLit v]

let (&&=>) vs v : 'pvar clause =
  for_each vs (fun u -> cons (NLit u)) [PLit v]

let (=>||) v vs : 'pvar clause =
  for_each vs (fun u -> cons (PLit u)) [NLit v]

(* (v1 /\ .. /\ vN) <-> v , where vs = [v1 .. vN] *)
let add_cnf_conjc_equiv vs v cnf : CNF.t =
  CNF.add (vs &&=> v) (for_each vs (fun u -> CNF.add (v => u)) cnf)

(* (v1 \/ .. \/ vN) <-> v , where vs = [v1 .. vN] *)
let add_cnf_disjc_equiv vs v cnf : CNF.t =
  CNF.add (v =>|| vs) (for_each vs (fun u -> CNF.add (u => v)) cnf)

let add_cnf_final_non_empty states : CNF.t -> CNF.t =
  CNF.add (List.rev_map (fun state -> PLit (Final state)) states)

(* introduction of an additional variable 
   equivalent to a conjunction of variables *)
let add_cnf_conjc_var (vs : encvar list) : CNF.t -> CNF.t =
  add_cnf_conjc_equiv vs (Conjc vs)

(* fold_left for states *) 
(* The list "states" is assumed to be ordered *)
let lower_states_for_each states step acc =
  fst (for_each states (fun state (acc, lowers) ->
         (step lowers state acc, state :: lowers)) (acc, []))

(* prop vars for reachability: states must be ordered *)
let add_cnf_reachability (arity : arity) states : CNF.t -> CNF.t =
  lower_states_for_each states (fun lowers state ->
    CNF.add (for_each_symbol arity (fun f n ->
            for_each (lowers *^ n) (fun qs ->
              cons (PLit(Trans(f, qs, state))))) []))

(* CNF clauses of closure under rewriting  *)
let restrict_vmap t vmap = 
  VarSet.fold (fun v ->
    match VarMap.find_opt v vmap with
    | None -> invalid_arg "restrict_vmap"
    | Some q -> VarMap.add v q) (find_vars t) VarMap.empty

let has_st t vmap q = HasSt(t, restrict_vmap t vmap, q)

let rec add_cnf_closure_each_term
          (arity : arity) vmap states t (cnf : CNF.t) : CNF.t =
  match t with
  | Var x ->
     let q_x = VarMap.find x vmap in
     for_each states (fun q ->
       let ev = has_st t vmap q in
       CNF.add [if q_x = q then PLit ev else NLit ev]) cnf
  | Sym(f, ts) ->
     let n = List.length ts in
     assert (n = SymbolMap.find f arity
             || invalid_arg "A term is inconsistent with the given arity");
     for_each states (fun state cnf ->
         let (cnf, cnjs) =
           for_each (states *^ n) (fun qs (cnf, cnjs) ->
             let vs =
               for_each2 ts qs (fun t q -> cons (has_st t vmap q))
                 [Trans(f, qs, state)] in
             (add_cnf_conjc_var vs cnf, Conjc vs :: cnjs)) (cnf, []) in
         (* var_parent <-> var_children *)
         add_cnf_disjc_equiv cnjs (has_st t vmap state) cnf)
       (for_each ts (add_cnf_closure_each_term arity vmap states) cnf)

let all_vmaps (vars : var list) states =
  for_each (states *^ List.length vars) (fun qs ->
    cons (for_each2 vars qs VarMap.add VarMap.empty)) []

let add_cnf_closure_each_rule (arity : arity) states lhs rhs : CNF.t -> CNF.t =
  let lhs_vars = find_vars lhs in
  let rhs_vars = find_vars rhs in
  if not (VarSet.subset rhs_vars lhs_vars) then
    invalid_arg"cnf_closure_each_rule: invalid rhs";
  let vars = VarSet.elements lhs_vars in
  for_each (all_vmaps vars states) (fun vmap cnf ->
    add_cnf_closure_each_term arity vmap states lhs
      (add_cnf_closure_each_term arity vmap states rhs
         (for_each states (fun q ->
            CNF.add (HasSt(lhs, vmap, q) => HasSt(rhs, vmap, q))) cnf)))

type rule_info = {
  lhs0: term;
  rhs0: term;
  rhss: term list; (* list of rhs terms after n steps from the lhs term *)
  vars: var list;
}

let make_rule_info n rules {lhs; rhs} : rule_info =
  let lhs_vars = find_vars lhs in
  assert (VarSet.subset (find_vars rhs) lhs_vars);
  { lhs0 = lhs;
    rhs0 = rhs;
    rhss = TermSet.elements (add_reduce_at_most n rules [rhs]);
    vars = VarSet.elements lhs_vars }

(* Remark 15 and Remark 17 *)
let add_cnf_closure (arity : arity) states rules : CNF.t -> CNF.t =
  for_each rules (fun {lhs0; rhss; vars} ->
    for_each (all_vmaps vars states) (fun vmap cnf ->
      for_each rhss
        (add_cnf_closure_each_term arity vmap states)
        (add_cnf_closure_each_term arity vmap states lhs0
           (for_each states (fun q ->
              CNF.add (HasSt(lhs0, vmap, q) =>||
                         List.rev_map (fun rhs -> HasSt(rhs, vmap, q)) rhss))
              cnf))))

let clause_state_rel_each_node f qs q ps p : encvar clause =
  let cls =
  for_each2 qs ps (fun qi pi -> cons (NLit(StRel(qi, pi))))
    (Trans(f, qs, q) => StRel(q, p))
  in (* printf "cls = %a@." (pp_clause pp_encvar) cls *) cls


(* Presence of redex,
   [states] is a list of states of the reduction closure tree automaton
    (not of the dbta accepting ground terms having the redex)  *)
let add_cnf_having_redex (arity : arity) states nf_dbta cnf : CNF.t =
  let nf_states = StateSet.elements (dtrans_qset nf_dbta.dtrans) in
  for_each_symbol arity (fun f n ->
    for_each (nf_states *^ n) (fun ps ->
      let p = StateTrans.find (f, ps) nf_dbta.dtrans in
      for_each (states *^ n) (fun qs ->
        for_each states (fun q ->
          CNF.add (clause_state_rel_each_node f qs q ps p)))))
    (for_each states (fun qf ->
       StateSet.fold (fun pf ->
         CNF.add [NLit(Final qf); NLit(StRel(qf, pf))]) nf_dbta.dfinal) cnf)

let make_cnf arity states rules nf_dbta =
  let cnf = add_cnf_final_non_empty states CNF.empty in
  let cnf = add_cnf_reachability arity states cnf in 
  let cnf = add_cnf_closure arity states rules cnf in
  let cnf = add_cnf_having_redex arity states nf_dbta cnf in
  cnf

(*  
let arity =
  for_each rules (fun {lhs; rhs} symap ->
    update_arity lhs (update_arity rhs symap)) SymbolMap.empty in
*)

module EncodeVarMap =
  Map.Make (struct
      type t = encvar
      let compare = compare
      (* compare (restrict_vmap t1) (restrict_vmap t2) *)
    end)

type encode_map =
  { to_nat : int EncodeVarMap.t; 
    of_nat : encvar IntMap.t;
    next : int }

let empty_encode_map =
  { to_nat = EncodeVarMap.empty;
    of_nat = IntMap.empty;
    next = 1 }

let rec update_encode_map v encmap =
  let encmap =
    match EncodeVarMap.find_opt v encmap.to_nat with
    | None ->
       let n = encmap.next in
       { to_nat = EncodeVarMap.add v n encmap.to_nat;
         of_nat = IntMap.add n v encmap.of_nat;
         next = n + 1 }
    | Some _ -> encmap in
  match v with
  | Conjc evs -> for_each evs update_encode_map encmap
  | _ -> encmap

let find_update_encode_map v encmap =
  let encmap = update_encode_map v encmap in
  (encmap, EncodeVarMap.find v encmap.to_nat)

let encode_lit lit encmap =
  match lit with
  | PLit v -> find_update_encode_map v encmap 
  | NLit v -> let (encmap, n) = find_update_encode_map v encmap in (encmap, -n)
   
let encode_cnf (cnf : CNF.t) =
  CNF.fold (fun cls (encmap, cnf) ->
    let (encmap, cls) = 
      for_each cls (fun lit (encmap, cls) ->
        let (encmap, i) = encode_lit lit encmap in
        (encmap, i :: cls)) (encmap, []) in
    (encmap, cls :: cnf)) cnf (empty_encode_map, [])

let pp_dimacs_cnf ppf int_cnf =
  List.iter (fprintf ppf "%a 0@." (pp_seq ~sep:"" pp_int)) int_cnf

(* extract a solution from SAT solvers:
     for "z3 input.cnf"
     for "minisat -verb=0 input.cnf /dev/stdout"
   Some xs gives a solution xs as a list of integers;
   None means unsatisfiable. *)
let extract_intlist_rev ic : int list option =
  let rec loop ic acc =
    let s = Scanf.bscanf ic "%s " (fun s -> s) in
    if s = "" then None
    else match int_of_string_opt s with
         | Some i -> if i = 0 then Some acc else loop ic (i :: acc)
         | None -> loop ic acc in
  loop ic []

let extract_solution ic {of_nat} =
  match extract_intlist_rev ic with
  | None -> None
  | Some xs ->
     Some (for_each xs (fun x ->
             if x > 0 then EncodeVarMap.add (IntMap.find x of_nat) true
             else EncodeVarMap.add (IntMap.find (-x) of_nat) false)
             EncodeVarMap.empty)

let encvar_map_nbta evmap =
  EncodeVarMap.fold (fun ev b nbta ->
    if b then match ev with
              | Final q -> { nbta with nfinal = StateSet.add q nbta.nfinal }
              | Trans(f, qs, q) ->
                 { nbta with ntrans = add_nbta_trans (f, qs) q nbta.ntrans }
              | _ -> nbta
    else nbta)
    evmap { nfinal = StateSet.empty; ntrans = StateTrans.empty } 

let run_z3 () = Unix.open_process "z3 -in -dimacs"

let test_z3 () =
  let (ic, oc) = run_z3 () in
  fprintf (formatter_of_out_channel oc) "0@.";
  close_out oc;
  if input_line ic = "s UNSATISFIABLE" then begin
    eprintf "z3 is ready.@.";
    close_in ic
  end else failwith "Unsupported z3"

let try_disprove (arity : arity) states rules nf_dbta =
  let cnf = make_cnf arity states rules nf_dbta in
  let (encmap, ecnf) = encode_cnf cnf in
  printf "#vars = %d, #clauses = %d@."
    (EncodeVarMap.cardinal encmap.to_nat) (CNF.cardinal cnf);
  let (ic, oc) = run_z3 () in
  pp_dimacs_cnf (formatter_of_out_channel oc) ecnf;
  close_out oc;
  let ic = Scanf.Scanning.from_channel ic in
  match extract_solution ic encmap with
  | None -> None
  | Some evmap ->
     let nbta = encvar_map_nbta evmap in
     let inv_min (f, qs) (g, ps) =
       let q = List.fold_left max 0 qs in
       let p = List.fold_left max 0 ps in
       if q < p
          || q = p
             && List.fold_left (+) 0 qs < List.fold_left (+) 0 ps
       then (f, qs)
       else (g, ps) in
     let inv_trans =
       StateTrans.fold (fun f_qs ->
         StateSet.fold (fun q inv ->
           match StateMap.find_opt q inv with
           | None -> StateMap.add q f_qs inv
           | Some g_ps -> StateMap.add q (inv_min g_ps f_qs) inv))
       nbta.ntrans StateMap.empty in
     let rec build q =
       let (f, qs) = StateMap.find q inv_trans in
       Sym(f, List.map build qs) in
     Some(nbta, build (StateSet.min_elt nbta.nfinal))
