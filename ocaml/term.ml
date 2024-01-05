(* terms *)
open Format
open Util

type symbol = int
let pp_symbol ppf (sym : symbol) = fprintf ppf "s%d" sym

module SymbolMap = Map.Make(struct
  type t = symbol
  let compare = compare
end)

type var = int
let pp_var ppf x = fprintf ppf "x%d" x

module VarSet = Set.Make(struct
  type t = var
  let compare = compare
end)
module VarMap = Map.Make (struct
  type t = var
  let compare = compare
end)

let pp_var_map pp_a ppf t =
  fprintf ppf "{ @[%a@] }"
    (pp_seq ~sep:","
       (fun ppf (v, a) -> fprintf ppf "@[@[%a@] => @[%a@]@]" pp_var v pp_a a))
    (VarMap.bindings t)

type term =
  | Var of var
  | Sym of symbol * term list

let rec pp_term ppf = function
  | Var x -> pp_var ppf x
  | Sym(f, ts) ->
     fprintf ppf "%a(@[" pp_symbol f;
     begin match ts with
     | [] -> ()
     | u :: us -> pp_term ppf u;
                  List.iter (fprintf ppf ",@,%a" pp_term) us end;
     fprintf ppf ")@]"

let string_of_term t = string_of pp_term t

module TermSet = Set.Make(struct
  type t = term
  let compare = compare
end)

module TermMap = Map.Make(struct
  type t = term
  let compare = compare
end)

type arity = int SymbolMap.t

(* update the arity map by a term with arity checking *)
let rec update_arity t (arity : arity) : arity =
  match t with
  | Var _ -> arity
  | Sym(f, ts) ->
     let n = List.length ts in
     let arity = match SymbolMap.find_opt f arity with
       | None -> SymbolMap.add f n arity
       | Some m -> if m = n then arity
                   else failwith(sprintf "invalid arity: symbol %d" f) in
     for_each ts update_arity arity

let add_var ~linear x vars =
  if linear && VarSet.mem x vars then
    invalid_arg (string_of pp_var x ^ " occurs more than once.")
  else VarSet.add x vars

let rec add_all_vars ~linear t vars =
  match t with
  | Var x -> add_var ~linear x vars
  | Sym(f, ts) -> for_each ts (add_all_vars ~linear) vars
  
let find_vars ?(linear=false) t = add_all_vars ~linear t VarSet.empty

(* all substitution *)                      
let all_vmaps (vset : VarSet.t) codom =
  let vars = VarSet.elements vset in
  for_each (codom *^ List.length vars) (fun ys ->
    cons (for_each2 vars ys VarMap.add VarMap.empty)) []

exception VarMapMergeConflict
let vmap_merge op1 op2 : 'a VarMap.t option =
  match (op1, op2) with
  | None, _ | _, None -> None
  | Some vmap1, Some vmap2 ->
     try Some (VarMap.union (fun _ x1 x2 ->
                   if x1 = x2 then Some x1
                   else raise VarMapMergeConflict) vmap1 vmap2) with
       VarMapMergeConflict -> None

let rec unify pat t : term VarMap.t option =
  match pat with
  | Var x -> Some (VarMap.singleton x t)
  | Sym(f, pats) ->
     match t with
     | Sym(g, ts) when f = g ->
        for_each2 pats ts
          (fun pat t -> vmap_merge (unify pat t)) (Some VarMap.empty)
     | _ -> None

let rec subst vmap = function
  | Var x -> VarMap.find x vmap
  | Sym(f, ts) -> Sym(f, List.map (subst vmap) ts)

let for_each_symbol arity step init =
  SymbolMap.fold step arity init
  
