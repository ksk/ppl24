open Format
open Util
open Term
open Trs
open Bta
open Cnf

let arity : arity = 
  for_each [(2,2);(0,0)] (fun (f, n) -> SymbolMap.add f n) SymbolMap.empty

let ($) x y = Sym(2, [x; y])
and f = Sym(0, [])
and x = Var 1
and y = Var 2
and z = Var 3
and w = Var 4
and v = Var 5
and w1 = Var 4
and w2 = Var 5

let rec pp_cterm paren symstr ppf = function
  | Var _ -> invalid_arg "Unexpected Var"
  | Sym(f, []) -> fprintf ppf "%s" symstr
  | Sym(f, [x; y]) ->
     if paren then
       fprintf ppf "(@[%a@] @[%a@])"
         (pp_cterm false symstr) x (pp_cterm true symstr) y
     else
       fprintf ppf "@[%a@] @[%a@]"
         (pp_cterm false symstr) x (pp_cterm true symstr) y
  | _ -> invalid_arg "pp_cterm: Unexpected Sym"

let rec pp_aterm symstr ppf = function
  | Var i -> pp_var ppf i
  | Sym(0, []) ->
     fprintf ppf "%s()" symstr
  | Sym(2, [x; y]) ->
     fprintf ppf "a(@[%a@], @[%a@])"
       (pp_aterm symstr) x (pp_aterm symstr) y
  | _ -> invalid_arg "pp_aterm: Unexpected Sym"

let pp_asym symstr ppf = function
  | 0 -> fprintf ppf "%s" symstr
  | 2 -> fprintf ppf "a"
  | _ -> invalid_arg "pp_asym: Unexpected Sym"

let rec upto n acc =
  if n < 1 then acc else upto (n-1) (n :: acc)
let upto n = upto n []

(* n : number of states *)
let try_combinator symstr (rule : rule_info) nf_dbta (n : int) =
  printf "------------------------------------------------ @.";
  printf "With %d-state non-deterministic tree automata ...@." n;
  let stime = Unix.gettimeofday () in
  match try_disprove arity (upto n) [rule] nf_dbta with
  | None ->
     printf "==> Failed! (%.3f sec)@." (Unix.gettimeofday () -. stime);
     false
  | Some(nbta, t) ->
     printf "==> Success! (%.3f sec)@." (Unix.gettimeofday () -. stime);
     printf "Disproving NBTA:@.  @[%a@]@."
       (pp_nbta_aux ~pp_sym:(pp_asym symstr)) nbta;
     set_max_indent 12;
     printf "Term: @[%a@]@." (pp_cterm false symstr) t;
     true

(* m .. n : range of numbers of states *)
let try_combinator_upto symstr rule m n =
  let stime = Unix.gettimeofday () in
  printf "Trying to disprove the termination of %s.@." symstr;
  let {lhs0=lhs; rhss; vars} as ri = make_rule_info 10 [rule] rule in
  printf "LHS: %a@." (pp_aterm symstr) lhs;
  printf "Expaneded RHSs: %a@." (pp_list (pp_aterm symstr)) rhss;
  let pats = List.rev_map (fun {lhs} -> lhs) [rule] in
  let nf_dbta = no_pattern_dbta arity pats in
  printf "Normal form DBTA:@.  @[%a@]@."
    (pp_dbta_aux ~pp_sym:(pp_asym symstr)) nf_dbta;
  let rec loop k =
    if k <= n && not (try_combinator symstr ri nf_dbta k) then loop (k+1) in
  loop m;
  printf "Elapsed time in total: %.3f sec.@." (Unix.gettimeofday () -. stime)
  

module StringMap = Map.Make(String)
let combinators = [
    "S", { lhs = f $ x $ y $ z;			(* success with 5 *)
           rhs = x $ z $ (y $ z) };
    "O", { lhs = f $ x $ y ;			(* success with 3 *)
           rhs = y $ (x $ y) };
    "P", { lhs = f $ x $ y $ z;			(* success with 4 *)
           rhs = z $ (x $ y $ z) };
    "Th4", { lhs = f $ x $ y $ z $ w;		(* success with 5 *)
             rhs = w $ (x $ y $ z $ w) };
    "P3", { lhs = f $ x $ y $ z;		(* success with 6 *)
            rhs = y $ (x $ z $ y) };
    "Phi", { lhs = f $ x $ y $ z $ w;		(* success with 7 *)
             rhs = x $ (y $ w) $ (z $ w) };
    "Phi2", { lhs = f $ x $ y $ z $ w1 $ w2;	(* failure with <= 8 *)
             rhs = x $ (y $ w1 $ w2) $ (z $ w1 $ w2) };
    "S1", { lhs = f $ x $ y $ z $ w;		(* success with 7 *)
            rhs = x $ y $ w $ (z $ w) };
    "S2", { lhs = f $ x $ y $ z $ w;		(* success with 6 *)
            rhs = x $ z $ w $ (y $ z $ w) };
    "S3", { lhs = f $ x $ y $ z $ w $ v;	(* failure with <= 8 *)
            rhs = x $ y $ (z $ v) $ (w $ v) };
    "S4", { lhs = f $ x $ y $ z $ w $ v;	(* failure with <= 8 *)
            rhs = z $ (x $ w $ v) $ (y $ w $ v) };
    "D1", { lhs = f $ x $ y $ z $ w;		(* success with 6 *)
            rhs = x $ z $ (y $ w) $ (x $ z) };
    "D2", { lhs = f $ x $ y $ z $ w;		(* success with 6 *)
            rhs = x $ w $ (y $ z) $ (x $ w) };
  ]
let comb_rule=
  for_each combinators
    (fun (name, rule) -> StringMap.add name rule) StringMap.empty

let () =
  if Array.length Sys.argv < 3 then
    invalid_arg "Combinator and maximum of #states must be given."
  else
    let symstr = Sys.argv.(1) in
    let rule =
      match StringMap.find_opt symstr comb_rule with
      | None -> invalid_argf "Unknown combinator: %S" symstr ()
      | Some rule -> rule in
    let n = match int_of_string_opt Sys.argv.(2) with
      | None -> invalid_argf "Invalid number of states: %S" Sys.argv.(2) ()
      | Some n -> n in
    test_z3 ();
    try_combinator_upto symstr rule 2 n
    
    

