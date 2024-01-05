(* Term rewriting system *)
open Util
open Term
type trs_rule = { lhs : term; rhs : term }

let make_rule ?(linear=false) lhs rhs =
  let lhs_vars = find_vars ~linear lhs in
  let rhs_vars = find_vars rhs in
  if not (VarSet.subset rhs_vars lhs_vars) then
    invalid_arg"make_rule: rhs contains variables not in lhs";
  { lhs; rhs }

let reduce_root {lhs;rhs} t =
  match unify lhs t with
  | None -> None
  | Some vmap -> Some (subst vmap rhs)

(* list of terms after reducion, lhs assumed not to be variable alone *)
let rec reduce_once rule t : term list =
  match t with
  | Var x -> []
  | Sym(f, ts) ->
     let (red_ts, _) =
       for_each ts (fun u (red_sibs, sibs) ->
         (for_each (reduce_once rule u) (fun red_u ->
            cons (red_u :: sibs)) (List.rev_map (cons u) red_sibs),
          u :: sibs)) ([], []) in
     let red_t = List.rev_map (fun us -> Sym(f, List.rev us)) red_ts in
     match reduce_root rule t with
     | None -> red_t
     | Some r -> r :: red_t

let rec add_reduce_at_most_aux n rules (ts : term list) terms =
  if ts = [] || n < 1 then terms
  else
    let new_ts =
      for_each ts (fun t -> 
        for_each rules (fun rule->
          for_each (reduce_once rule t) (fun u ->
            cons u))) [] in
    add_reduce_at_most_aux (n-1) rules new_ts
      (for_each new_ts TermSet.add terms)

let add_reduce_at_most n rules (ts : term list) =
  add_reduce_at_most_aux n rules ts (for_each ts TermSet.add TermSet.empty)
