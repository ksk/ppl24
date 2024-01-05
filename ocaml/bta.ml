(* Bottom-up Tree Automata *)
open Format
open Util
open Term

type state = int
let min_state : state = 1
let next_state (st : state) : state = st + 1
let pp_state ppf (q : state) = fprintf ppf "q%d" q

module StateSet = Set.Make(struct
  type t = state
  let compare = compare                    
end)
module StateMap = Map.Make(struct
  type t = state
  let compare = compare                    
end)
module StateTrans = Map.Make(struct
  type t = symbol * state list
  let compare = compare
end)
module StateSetSet = Set.Make(struct
  type t = StateSet.t
  let compare = compare
end)

let pp_state_set ppf qset =
  fprintf ppf "{ @[%a@] } " (pp_seq pp_state) (StateSet.elements qset)

let pp_state_set_set ppf qsets =
  fprintf ppf "{ @[%a@] }" (pp_seq pp_state_set) (StateSetSet.elements qsets)

let pp_state_trans_aux ~pp_sym pp_a ppf st_trans =
  fprintf ppf "{ @[";
  let pp_trans ppf ((f, qs), q) =
    fprintf ppf "%a(%a) -> %a" pp_sym f (pp_seq pp_state) qs pp_a q in
  pp_seq pp_trans ppf (StateTrans.bindings st_trans);
  fprintf ppf "@] }"

let pp_state_trans pp_a = pp_state_trans_aux ~pp_sym:pp_symbol pp_a

type dbta = {
  dfinal : StateSet.t;
  dtrans : state StateTrans.t;
}
type nbta = {
  nfinal : StateSet.t;
  ntrans : StateSet.t StateTrans.t;
}

let dtrans_qset dtrans = 
  StateTrans.fold (fun _ -> StateSet.add) dtrans StateSet.empty

let ntrans_qset ntrans = 
  StateTrans.fold (fun _ -> StateSet.union) ntrans StateSet.empty

let pp_dbta_aux ~pp_sym ppf {dfinal; dtrans} =
  fprintf ppf "states = %a;@;" pp_state_set (dtrans_qset dtrans);
  fprintf ppf "dfinal = %a;@;" pp_state_set dfinal;
  fprintf ppf "dtrans = %a" (pp_state_trans_aux ~pp_sym pp_state) dtrans

let pp_dbta = pp_dbta_aux ~pp_sym:pp_symbol

let pp_nbta_aux ~pp_sym ppf {nfinal; ntrans} =
  fprintf ppf "states = %a;@;" pp_state_set (ntrans_qset ntrans);
  fprintf ppf "nfinal = %a;@;" pp_state_set nfinal;
  fprintf ppf "ntrans = %a" (pp_state_trans_aux ~pp_sym pp_state_set) ntrans

let pp_nbta = pp_nbta_aux ~pp_sym:pp_symbol

(*
let pp_dbta ppf {dfinal; dtrans} =
  fprintf ppf "states = %a;@;" pp_state_set (dtrans_qset dtrans);
  fprintf ppf "dfinal = %a;@;" pp_state_set dfinal;
  fprintf ppf "dtrans = %a" (pp_state_trans pp_state) dtrans

let pp_nbta ppf {nfinal; ntrans} =
  fprintf ppf "states = %a;@;" pp_state_set (ntrans_qset ntrans);
  fprintf ppf "nfinal = %a;@;" pp_state_set nfinal;
  fprintf ppf "ntrans = %a" (pp_state_trans pp_state_set) ntrans
*)

(* To make BTA recognizing an occurrence of a pattern *)
(* assing a state for each node of the pattern *)

type state_assignment = {
  term2st : state TermMap.t;
  all_sts : StateSet.t;
  next_st : state;
}
let init_sa = {
  term2st = TermMap.empty;
  all_sts = StateSet.empty;
  next_st = min_state;
}
let update_sa t q_any {term2st; all_sts; next_st} =
  match t with
  | Var x -> { term2st = TermMap.add t q_any term2st;
               all_sts = StateSet.add q_any all_sts;
               next_st = next_st; }
  | Sym _ -> {
      term2st = TermMap.add t next_st term2st;
      all_sts = StateSet.add next_st all_sts;
      next_st = next_state next_st;
    }

let rec assign_state q_any (pat : term) sa =
  let sa = update_sa pat q_any sa in
  match pat with
  | Var _ -> sa
  | Sym(f, ts) -> for_each ts (assign_state q_any) sa

let add_nbta_trans
      (f_qs : symbol * state list) (q : state) trans =
  match StateTrans.find_opt f_qs trans with
  | None -> StateTrans.add f_qs (StateSet.singleton q) trans
  | Some ps -> StateTrans.add f_qs (StateSet.add q ps) trans

let rec add_trans_all_nodes sa (pat : term) trans =
  match pat with
  | Var _ -> trans
  | Sym(f, ts) ->
     let q = TermMap.find pat sa.term2st in
     let qs = List.map (fun u -> TermMap.find u sa.term2st) ts in
     for_each ts (add_trans_all_nodes sa) (add_nbta_trans (f, qs) q trans)

let pattern_nbta (arity : arity) (pat : term) : nbta =
  let q_any = min_state in
  let init_sa = { term2st = TermMap.empty;
                  all_sts = StateSet.empty;
                  next_st = next_state min_state } in
  let sa = assign_state q_any pat init_sa in
  let ntrans = add_trans_all_nodes sa pat StateTrans.empty in
  let nfinal = StateSet.singleton (TermMap.find pat sa.term2st) in
  let states = StateSet.elements sa.all_sts in
  let q_root = TermMap.find pat sa.term2st in
  { nfinal = nfinal;
    ntrans = for_each_symbol arity (fun f n trans ->
               for_each (states *^ n) (fun qs ->
                 let f_qs = (f, qs) in
                 if List.mem q_root qs then add_nbta_trans f_qs q_root
                 else id)
                 (add_nbta_trans (f, repeat q_any n) q_any trans)) ntrans }

module StateSetTrans = Map.Make(struct
  type t = symbol * StateSet.t list
  let compare = compare
end)
module StateSetMap = Map.Make(struct
  type t = StateSet.t
  let compare = compare
end)

type determinize_info = {
  pow_trans : StateSet.t StateSetTrans.t;
  st_sets : StateSetSet.t;
}

let product_st_sets qss =
  for_each (List.rev qss) (fun qset prev_qss ->
    StateSet.fold (fun q ->
      for_each prev_qss (fun qs ->
          cons (q :: qs))) qset []) [[]]

let powerset_trans ({ntrans} : nbta) (arity : arity)
      (st_sets : StateSetSet.t) : determinize_info =
  let init = { pow_trans = StateSetTrans.empty; st_sets } in
  let qsets = StateSetSet.elements st_sets in
  for_each_symbol arity (fun f n ->
    for_each (qsets *^ n) (fun qss dinfo ->
      let qset = 
        for_each (product_st_sets qss) (fun qs ->
          match StateTrans.find_opt (f, qs) ntrans with
          | None -> id
          | Some qset -> StateSet.union qset) StateSet.empty in
      { pow_trans = StateSetTrans.add (f, qss) qset dinfo.pow_trans;
        st_sets = StateSetSet.add qset dinfo.st_sets })) init  

let remove_unreachable (arity : arity) {dfinal; dtrans} =
  let rec loop qset =
    let c = StateSet.cardinal qset in
    let states = StateSet.elements qset in
    let qset = 
      for_each_symbol arity (fun f n ->
        for_each (states *^ n) (fun qs ->
          match StateTrans.find_opt (f, qs) dtrans with
          | None -> id
          | Some q -> StateSet.add q)) qset in
    if c = StateSet.cardinal qset then qset else loop qset in
  let qset = loop StateSet.empty in
  { dfinal = StateSet.inter dfinal qset;
    dtrans =
      StateTrans.fold (fun (f, qs) q ->
        if List.for_all (fun p -> StateSet.mem p qset) qs then
          StateTrans.add (f, qs) q
        else id) dtrans StateTrans.empty }

(* --- BEGIN for minimization -- *)
type equiv_states = {
  st_eqs : StateSetSet.t;
  st_eqinv : StateSet.t StateMap.t;
}

let make_equiv_states st_eqs =
  let st_eqinv =
    StateSetSet.fold (fun qset ->
      StateSet.fold (fun q ->
        StateMap.add q qset) qset) st_eqs StateMap.empty in
  { st_eqs; st_eqinv }
    
let add_eqst (q_eqs : StateSet.t) (q : state) eqs_map =
  let qset = match StateSetMap.find_opt q_eqs eqs_map with
    | None -> StateSet.singleton q
    | Some qset -> StateSet.add q qset in
  StateSetMap.add q_eqs qset eqs_map

let refine_by_codom eqs_map st_eqs =
  StateSetSet.fold (fun q_eqs ->
    StateSetMap.fold (fun _ eqs ->
      let refined = StateSet.inter q_eqs eqs in
      if StateSet.is_empty refined then id
      else StateSetSet.add refined) eqs_map) st_eqs
    StateSetSet.empty 

let dbta_states {dtrans} =
  StateTrans.fold (fun _ -> StateSet.add) dtrans StateSet.empty

module CompleteDBTA : sig
  type complete_dbta
  val make_complete_dbta : arity -> dbta -> complete_dbta
  val c_final : complete_dbta -> StateSet.t
  val c_trans : complete_dbta -> state StateTrans.t SymbolMap.t
  val c_states : complete_dbta -> state list
  val complement : arity -> dbta -> complete_dbta
end = struct
  type complete_dbta = {
    cstates : state list;
    cfinal : StateSet.t;
    ctrans : state StateTrans.t SymbolMap.t;
  }
  let make_complete_dbta (arity : arity) dbta =
    let cstates = StateSet.elements (dbta_states dbta) in
    let cfinal = dbta.dfinal in
    let ctrans =
      for_each_symbol arity (fun f n ->
        SymbolMap.add f 
          (for_each (cstates *^ n) (fun qs ->
             let f_qs = (f, qs) in
             (* checking completeness here *)
             match StateTrans.find_opt f_qs dbta.dtrans with
             | None -> invalid_argf "No transition rule for %s(%s)"
                         (string_of pp_symbol f)
                         (string_of (pp_seq pp_state) qs) ()
             | Some q -> StateTrans.add f_qs q) StateTrans.empty))
        SymbolMap.empty in
    {cstates; cfinal; ctrans}

  let c_final (ta : complete_dbta) = ta.cfinal
  let c_trans (ta : complete_dbta) = ta.ctrans
  let c_states (ta : complete_dbta) = ta.cstates

  let complement (arity : arity) (dbta : dbta) : complete_dbta =
    let qset = dtrans_qset dbta.dtrans in
    let dfinal = StateSet.diff qset dbta.dfinal in
    let dbta = { dbta with dfinal } in
    make_complete_dbta arity dbta
end
open CompleteDBTA

let minimize (arity : arity) {dfinal; dtrans} =
  let { dfinal; dtrans } = remove_unreachable arity { dfinal; dtrans } in
  let qset = dtrans_qset dtrans in
  let states = StateSet.elements qset in
  let init_st_eqs =
    StateSetSet.of_list [ dfinal; StateSet.diff qset dfinal ] in
  let init_eqst = make_equiv_states init_st_eqs in
  let rec loop ({st_eqs; st_eqinv} as eqst) =
    let c = StateSetSet.cardinal st_eqs in
    let st_eqs = 
      for_each_symbol arity (fun f n ->
        for_each (states *^ (n-1)) (fun qs ->
          for_each (list_splits qs) (fun (ls, rs) ->
            let inv_trans =
              for_each states (fun q ->
                let qs = List.rev_append ls (q :: rs) in
                let p = StateTrans.find (f, qs) dtrans in
                let p_eqs = StateMap.find p st_eqinv in
                add_eqst p_eqs q) StateSetMap.empty in
            refine_by_codom inv_trans))) st_eqs in
    if c = StateSetSet.cardinal st_eqs then eqst
    else loop (make_equiv_states st_eqs) in
  let {st_eqs; st_eqinv} = loop init_eqst in
  let rename q = StateSet.min_elt (StateMap.find q st_eqinv) in
  let dfinal =
    StateSet.fold (fun q -> StateSet.add (rename q)) dfinal StateSet.empty in
  let dtrans =
    StateTrans.fold (fun (f, qs) q ->
      StateTrans.add (f, List.map rename qs) (rename q))
      dtrans StateTrans.empty in
  remove_unreachable arity { dfinal; dtrans }
(* --- END for minimization -- *)

let determinize (arity : arity) ({nfinal; ntrans} as nbta) : dbta =
  let st_sets =
    StateTrans.fold (fun _ -> StateSetSet.add) ntrans StateSetSet.empty in
  let rec loop st_sets =
    let c = StateSetSet.cardinal st_sets in
    let di = powerset_trans nbta arity st_sets in
    if c = StateSetSet.cardinal di.st_sets then di
    else loop di.st_sets in
  let {pow_trans; st_sets} = loop st_sets in
  (* numbering *)
  let (_, stsmap) = 
    StateSetSet.fold (fun sts (i, map) ->
        (i + 1, StateSetMap.add sts i map)) st_sets (1, StateSetMap.empty) in
  let dtrans =
    StateSetTrans.fold (fun (f, qss) qs ->
      StateTrans.add (f, List.map (fun qs -> StateSetMap.find qs stsmap) qss)
        (StateSetMap.find qs stsmap)) pow_trans StateTrans.empty in
  let dfinal =
    StateSetMap.fold (fun sts i set ->
      if StateSet.is_empty (StateSet.inter nfinal sts) then set
      else StateSet.add i set) stsmap StateSet.empty in
  let dbta = remove_unreachable arity {dtrans; dfinal} in
  minimize arity dbta

module StateList = struct
  type t = state list
  let compare = compare
end
module StateListMap = Map.Make(StateList)

type states_map = {
  to_one : state StateListMap.t;
  next : state;
}

let empty_states_map = {
  to_one = StateListMap.empty;
  next = 1;
}

let find_update_states_map states states_map : states_map * state =
  match StateListMap.find_opt states states_map.to_one with
  | None ->
     let st = states_map.next in
     let states_map = { to_one = StateListMap.add states st states_map.to_one;
                        next = next_state st } in
     (states_map, st)
  | Some st -> 
     (states_map, st)

let dbta_product (final_unit : bool) (final_op: bool -> bool -> bool)
      (arity : arity) (dbtas : dbta list) : dbta =
  let dnum = List.length dbtas in
  let cdbtas = List.map (make_complete_dbta arity) dbtas in
  let statess = List.map c_states cdbtas in
  let all_ps = list_product_unordered statess in
  let (stsmap, dtrans) =
    for_each_symbol arity (fun f n ->
      for_each (all_ps *^ n) (fun pss (stsmap, trans) ->
        let qss = match transpose pss with
          | [] -> List.init dnum (fun _ -> [])
          | qss -> qss in
        let (stsmap, qs) =
          for_each (List.rev pss) (fun ps (stsmap, qs) ->
            let (stsmap, q) = find_update_states_map ps stsmap in
            (stsmap, q :: qs)) (stsmap, []) in
        let ps = List.rev (for_each2 qss dbtas (fun qs dbta ->
                             cons (StateTrans.find (f, qs) dbta.dtrans)) []) in
        let (stsmap, q) = find_update_states_map ps stsmap in
        (stsmap, StateTrans.add (f, qs) q trans)))
      (empty_states_map, StateTrans.empty) in
  let dfinal =
    StateListMap.fold (fun ps q ->
      if for_each2 ps dbtas (fun p dbta ->
           final_op (StateSet.mem p dbta.dfinal)) final_unit then
        StateSet.add q 
      else id) stsmap.to_one StateSet.empty in
  { dfinal; dtrans }

let dbta_union arity dbtas : dbta = dbta_product false (||) arity dbtas
let dbta_inter arity dbtas : dbta = dbta_product true (&&) arity dbtas

let no_pattern_dbta (arity : arity) (pats : term list) : dbta =
  let dbtas = for_each pats (fun pat ->
                let nbta = pattern_nbta arity pat in
                let { dfinal; dtrans } = determinize arity nbta in
                let qset = dtrans_qset dtrans in
                cons { dfinal = StateSet.diff qset dfinal; dtrans }) [] in
  let dbta = dbta_inter arity dbtas in
  minimize arity dbta

module DBTASet = Set.Make(struct
  type t = dbta
  let compare = compare
end)

module DBTAMap = Map.Make(struct
  type t = dbta
  let compare = compare
end)


