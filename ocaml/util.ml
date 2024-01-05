(* Utilities *)
open Format

let failwithf    fmt = ksprintf (fun s () -> failwith s) fmt
let invalid_argf fmt = ksprintf (fun s () -> invalid_arg s) fmt

let id x = x
let cons x xs = x :: xs

(* Re-definition of fold_left *) 
let for_each xs fcons fnil =
  List.fold_left (fun acc x -> fcons x acc) fnil xs

let rec for_each2 xs ys fcons fnil =
  match xs with
  | [] -> if ys = [] then fnil else invalid_arg "for_each2 [] (_::_) _ _"
  | x :: xs -> match ys with
               | [] -> invalid_arg "for_each2 (_::_) [] _ _"
               | y :: ys -> for_each2 xs ys fcons (fcons x y fnil)

let string_of (pp : Format.formatter -> 'a -> unit) (x : 'a) =
  pp str_formatter x;
  flush_str_formatter ()

let pp_bool = pp_print_bool
let pp_int = pp_print_int

let pp_pair pp_a pp_b ppf (a, b) =
  fprintf ppf "(@[%a@], @,@[%a@])" pp_a a pp_b b

let pp_seq ?(sep=",") pp_a ppf = function
  | [] -> ()
  | x :: xs ->
     fprintf ppf "@[@[%a@]" pp_a x;
     List.iter (fprintf ppf "%s @,@[%a@]" sep pp_a) xs;
     fprintf ppf "@]"

let pp_list pp_a ppf xs =
  fprintf ppf "[ %a ]" (pp_seq ~sep:";" pp_a) xs

let repeat x n =
  let rec loop n acc =
    if n = 0 then acc else loop (n-1) (x :: acc) in
  loop n []

let rec list_power_aux xs n ps =
  if n < 0 then []
  else if n = 0 then ps
  else
    list_power_aux xs (n-1)
      (for_each xs (fun x ->
         for_each ps (fun p -> cons (x :: p))) [])
let ( *^ ) xs n = list_power_aux xs n [[]]

(* list_splits [x1; x2; x3; ...; xN] = 
   [([], [x1; x2; x3; ...; xN]);
    ([x1], [x2; x3; ...; xN]);
    ([x2; x1], [x3; ...; xN]);
     ...                     ;
    ([xN; ...; x3; x2; x1], [])] *)
let list_splits xs =
  let rec loop ls rs lrs =
    let lrs = (ls, rs) :: lrs in
    match ls with
    | [] -> lrs
    | l :: ls' -> loop ls' (l :: rs) lrs in
  let ls = List.rev xs in
  loop ls [] []

module IntMap = Map.Make(Int)

(* transpose [[1;2;3];[4;5;6]] = [[1;4];[2;5];[3;6]] *)
let transpose (mat: 'a list list) =
  match List.rev mat with
  | [] -> []
  | hs :: mat ->
     for_each mat (fun xs xss ->
       (List.rev (for_each2 xs xss (fun x xs -> cons (x :: xs)) [])))
       (List.map (fun x -> [x]) hs)

(* list_product_unordered [[1;2];[3;4;5];[6]] =
   permutation of [[1;3;6];[1;4;6]; ... ;[2;5;6]] *)
let list_product_unordered (xss: 'a list list) =
  for_each (List.rev xss) (fun xs pss ->
    for_each xs (fun x ->
      for_each pss (fun ps -> cons (x :: ps))) []) [[]]



