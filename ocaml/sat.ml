(* SAT encoding of TA for termination checking *)
open Format
open Util
open Term
open Trs
open Bta

type 'pvar lit =
  | PLit of 'pvar
  | NLit of 'pvar

type 'pvar clause = 'pvar lit list
type 'pvar cnf = 'pvar clause list

let neg_lit = function
  | PLit v -> NLit v
  | NLit v -> PLit v

let (=>) u v : 'pvar clause = [NLit u; PLit v]

let (&&=>) vs v : 'pvar clause =
  for_each vs (fun u -> cons (NLit u)) [PLit v]

let (=>||) v vs : 'pvar clause =
  for_each vs (fun u -> cons (PLit u)) [NLit v]

(* (v1 /\ .. /\ vN) <-> v , where vs = [v1 .. vN] *)
let add_cnf_conjc_equiv vs v (cls: 'pvar cnf) : 'pvar cnf =
  (vs &&=> v) :: for_each vs (fun u -> cons (v => u)) cls

(* (v1 \/ .. \/ vN) <-> v , where vs = [v1 .. vN] *)
let add_cnf_disjc_equiv vs v (cls: 'pvar cnf) : 'pvar cnf =
  (v =>|| vs) :: for_each vs (fun u -> cons (u => v)) cls

(* encoding variable *)
type encvar =
  | Final of state
  | Trans of symbol * state list * state
  | Reduc of term * state VarMap.t * state
  | Conjc of encvar list
  | StRel of state * state

let add_cnf_final_non_empty states : encvar cnf -> encvar cnf =
  cons (List.rev_map (fun state -> PLit (Final state)) states)

(* introduction of an additional variable 
   equivalent to a conjunction of variables *)
let add_cnf_conjc_var (vs : encvar list) : encvar cnf -> encvar cnf =
  add_cnf_conjc_equiv vs (Conjc vs)


(* fold_left for states *) 
(* The list "states" is assumed to be ordered *)
let lower_states_for_each states step acc =
  fst (for_each states (fun state (acc, lowers) ->
         (step lowers state acc, state :: lowers)) (acc, []))

(* prop vars for reachability: states must be ordered *)
let add_cnf_reachability (arity : arity) states : encvar cnf -> encvar cnf =
  lower_states_for_each states (fun lowers state ->
    cons (for_each_symbol arity (fun f n ->
            for_each (lowers *^ n) (fun qs ->
              cons (PLit(Trans(f, qs, state))))) []))

(* CNF clauses of closure under rewriting  *)
let rec add_cnf_closure_each_term (arity : arity) vmap states t
          (cls : encvar cnf) : encvar cnf =
  match t with
  | Var x ->
     [PLit(Reduc(t, vmap, VarMap.find x vmap))] :: cls
  | Sym(f, ts) ->
     let n = List.length ts in
     assert (n = SymbolMap.find f arity);
     for_each states (fun state cls ->
         let (cls, cnjs) =
           for_each (states *^ n) (fun qs (cls, cnjs) ->
             let vs =
               for_each2 ts qs (fun t q ->
                 cons (Reduc(t, vmap, q))) [Trans(f, qs, state)] in
             (add_cnf_conjc_var vs cls, Conjc vs :: cnjs)) (cls, []) in
         (* var_parent <-> var_children *)
         add_cnf_disjc_equiv cnjs (Reduc(t, vmap, state)) cls) cls
                      
let all_vmaps (vars : var list) states =
  for_each (states *^ List.length vars) (fun qs ->
    cons (for_each2 vars qs VarMap.add VarMap.empty)) []

let add_cnf_closure_each_rule (arity : arity) states lhs rhs
  : encvar cnf -> encvar cnf =
  let lhs_vars = find_vars lhs in
  let rhs_vars = find_vars rhs in
  if not (VarSet.subset rhs_vars lhs_vars) then
    invalid_arg"cnf_closure_each_rule: invalid rhs";
  let vars = VarSet.elements lhs_vars in
  for_each (all_vmaps vars states) (fun vmap cls ->
    add_cnf_closure_each_term arity vmap states lhs
      (add_cnf_closure_each_term arity vmap states rhs
         (for_each states (fun q ->
            cons (Reduc(lhs, vmap, q) => Reduc(rhs, vmap, q))) cls)))

(* Remark 15 and Remark 17 *)
let add_cnf_closure (arity : arity) states n rules : encvar cnf -> encvar cnf =
  for_each rules (fun {lhs; rhs} ->
    let lhs_vars = find_vars lhs in
    assert (VarSet.subset (find_vars rhs) lhs_vars);
    let vars = VarSet.elements lhs_vars in
    let rhss = (* list of rhs terms after n steps from the lhs term *)
      TermSet.elements (add_reduce_at_most n rules [rhs] TermSet.empty) in
    for_each (all_vmaps vars states) (fun vmap cls ->
      for_each rhss
        (add_cnf_closure_each_term arity vmap states)
        (add_cnf_closure_each_term arity vmap states lhs
           (for_each states (fun q ->
              cons (Reduc(lhs, vmap, q) =>||
                      List.rev_map (fun rhs -> Reduc(rhs, vmap, q)) rhss))
              cls))))

let clause_state_rel_each_node f qs q ps p : encvar clause =
  for_each2 qs ps (fun qi pi -> cons (NLit(StRel(qi, pi))))
    (Trans(f, qs, q) => StRel(q, p))

(* Presence of redex,
   [states] is a list of states of the reduction closure tree automaton
    (not of the dbta accepting ground terms having the redex)  *)
let add_cnf_having_redex (arity : arity) states rules (cnf : encvar cnf)
    : encvar cnf =
  let pats = List.rev_map (fun {lhs} -> lhs) rules in
  let nf_dbta = no_pattern_dbta arity pats in (* dbta for normal forms *)
  let nf_states = StateSet.elements (dtrans_qset nf_dbta.dtrans) in
  for_each_symbol arity (fun f n ->
    for_each (nf_states *^ n) (fun ps ->
      let p = StateTrans.find (f, ps) nf_dbta.dtrans in
      for_each (states *^ n) (fun qs ->
        for_each states (fun q ->
          cons (clause_state_rel_each_node f qs q ps p)))))
    (for_each states (fun qf ->
       StateSet.fold (fun pf ->
         cons [NLit(Final qf); NLit(StRel(qf, pf))]) nf_dbta.dfinal) cnf)

let make_cnf arity states n rules =
  let cnf = add_cnf_final_non_empty states [] in
  let cnf = add_cnf_reachability arity states cnf in 
  let cnf = add_cnf_closure arity states n rules cnf in
  let cnf = add_cnf_having_redex arity states rules cnf in
  cnf
(*  
let arity =
  for_each rules (fun {lhs; rhs} symap ->
    update_arity lhs (update_arity rhs symap)) SymbolMap.empty in
*)

let rec restrict_vmap = function
  | Reduc(t, vmap, q) ->
     let vmap =
       VarSet.fold (fun v ->
         match VarMap.find_opt v vmap with
         | None -> invalid_arg "restrict_vmap"
         | Some q -> VarMap.add v q) (find_vars t) VarMap.empty in
     Reduc(t, vmap, q)
  | Conjc evs -> Conjc (List.map restrict_vmap evs)
  | other -> other

module EncodeVarMap =
  Map.Make (struct
      type t = encvar
      let compare t1 t2 =
        compare (restrict_vmap t1) (restrict_vmap t2)
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
   
let encode_cnf cnf =
  snd (for_each cnf (fun cls (encmap, cnf) ->
         let (encmap, cls) = 
           for_each cls (fun lit (encmap, cls) ->
             let (encmap, i) = encode_lit lit encmap in
             (encmap, i :: cls)) (encmap, []) in
         (encmap, cls :: cnf)) (empty_encode_map, []))

let pp_dimacs_cnf ppf int_cnf =
  List.iter (fprintf ppf "%a 0@." (pp_seq ~sep:"" pp_int)) int_cnf

(* extract a solution from SAT solvers:
     for "z3 input.cnf"
     for "minisat -verb=0 input.cnf /dev/stdout"
   Some xs gives a solution xs as a list of integers;
   None means unsatisfiable. *)
let extract_solution ic : int list option =
  let rec loop ic acc =
    let s = Scanf.bscanf ic "%s " (fun s -> s) in
    if s = "" then None
    else match int_of_string_opt s with
         | Some i -> if i = 0 then Some(List.rev acc) else loop ic (i :: acc)
         | None -> loop ic acc in
  loop ic []










