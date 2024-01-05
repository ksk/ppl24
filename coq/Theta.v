From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
Set Implicit Arguments. Unset Strict Implicit.

Lemma dec_sval_inj [A: Type] (P: A -> bool): injective (aT:={ x : A | P x }) sval.
Proof.
  move=> [a1 p1] [a2 p2] /= ?; subst a1.
  by have->: p1 = p2 by apply eq_irrelevance.
Qed.

Ltac rcons_ind xs := pattern xs; apply: {xs} last_ind.
Notation "xs ::< x" := (rcons xs x) (at level 60).
Section RCons.
  Context [T: eqType].

  Lemma in_rcons (y: T) (s: seq T) (x: T):
    (x \in s ::< y) = (x == y) || (x \in s).
  Proof.
    elim: s=> //= z s IH.
    rewrite (in_cons z (s ::< y) x) IH (in_cons z s x).
    by move: (x == z) (x == y)=> [] [].
  Qed.
End RCons.

Lemma nseqSr {T: Type} n (x: T):
  nseq n.+1 x = nseq n x ::< x.
Proof. by elim: n=>[//|n /= ->]. Qed.

Lemma size_take_le (n : nat) [T : Type] (s : seq T):
  size (take n s) = (if n <= size s then n else size s).
Proof.
  rewrite size_take; move: (leqVgt n (size s)); rewrite leq_eqVlt -orbA=> /or3P[].
  - by move=> /eqP=> ->; rewrite ltnn eq_refl.
  - by move=> ->; rewrite orbT.
  - by rewrite ltn_neqAle=> /andP[] /negPf; rewrite eq_sym leqNgt=> -> /negPf->.
Qed.

Lemma all_take [T: Type] (a: pred T) (n: nat) (s: seq T):
  all a s -> all a (take n s).
Proof.
  by elim: s n=> [|x s IH] //= [|n] //= /andP[] -> /IH ->.
Qed.

Lemma all_cons {A: Type} (p: A -> bool) x xs:
  all p (x :: xs) = p x && all p xs.
Proof. by []. Qed.

Lemma nseqS {T: Type} n (x: T):
  nseq n.+1 x = x :: nseq n x.
Proof. by []. Qed.

Lemma head_nseq {T: Type} n (x y: T):
  head x (nseq n y) = x \/ head x (nseq n y) = y.
Proof.
  case: n=> [|n]; first by left.
  by right; rewrite nseqS. 
Qed.

Lemma last_nseq {T: Type} n (x y: T):
  last x (nseq n y) = x \/ last x (nseq n y) = y.
Proof.
  elim: n x=> [|n IH] x; first by left.
  by rewrite nseqS last_cons; move: (IH y)=> []->; right.
Qed.

Section SafeNth.
  Context [A: Type].
  
  Definition safe_nth: forall (xs: seq A) (n: nat), n < size xs -> A.
    refine (fix safe_nth xs n ok :=
              match xs as s return xs = s -> A with
              | [::] => fun E => _
              | y :: ys => fun E => match n as m return n = m -> A with
                                | 0 => fun _ => y
                                | m.+1 => fun En => safe_nth ys m _
                                end erefl
              end erefl).
    by move: E ok=> ->.
    by move: E En ok=> -> -> /=; rewrite ltnS.
  Defined.

  Definition nth_safe (d: A) (xs: seq A) (n: nat) (ok: n < size xs):
    safe_nth (xs:=xs) ok = nth d xs n.
  Proof.
    by elim: xs n ok=> [|y ys IH] [|m] ok //=.
  Qed.
End SafeNth.
Arguments safe_nth [A] xs n ok.


Section BTree.
  Context {A: eqType}.
  Context {p: A -> bool}.
  Inductive btree: Type :=
  | Tip: { a | p a } -> btree
  | Bin: btree -> btree -> btree.

  Notation "# a" := (Tip (@exist _ _ a _)) (at level 10).
  Notation "x @ y" := (Bin x y) (at level 50, left associativity).

  Fixpoint btree_eq (t1 t2: btree): bool :=
    match (t1, t2) with
    | (Tip s1, Tip s2) => s1 == s2
    | (l1 @ r1, l2 @ r2) => btree_eq l1 l2 && btree_eq r1 r2
    | _ => false
    end.

  Lemma btree_eqP: Equality.axiom btree_eq.
  Proof.
    elim=> [o1|l1 IHl r1 IHr] [o2|l2 r2] /=.
    - case: eqP; constructor; first by subst. 
      by move=> [].
    - by constructor.
    - by constructor.
    - by apply: (equivP andP); split=> [] [] /IHl -> /IHr ->.
  Qed.

  HB.instance Definition _ := hasDecEq.Build btree btree_eqP.

  Fixpoint leftmost_tip (t: btree): A :=
    match t with
    | # a => a
    | l @ _ => leftmost_tip l
    end.

  Definition is_bin (t: btree): bool :=
    if t is # _ then false else true.

End BTree.
Arguments btree {A} p.
Arguments Tip {A p}.
Arguments Bin {A p} l r.
Notation "# a" := (Tip (@exist _ _ a _)) (at level 10).
Notation "l @ r" := (Bin l r) (at level 50, left associativity).


Section BinSeq.
  Context [A: eqType] [p: A -> bool].
  Notation "'btree'" := (btree p) (at level 1).

  Fixpoint bins (f: btree) (args: seq btree) :=
    match args with
    | [::] => f
    | t :: ts => bins (f @ t) ts
    end.
  Notation "f @* xs" := (bins f xs) (at level 40).

  Lemma bins_rcons x ys y: x @* rcons ys y = x @* ys @ y.
  Proof. by elim: ys x=> //=. Qed.

  Lemma bins_cat x xs ys: x @* (xs ++ ys) = x @* xs @* ys.
  Proof.
    by elim: xs x=> [//|z zs IH] x; rewrite cat_cons /= IH.
  Qed.
End BinSeq.
Notation "f @* xs" := (bins f xs) (at level 40).


Section BTreeMap.
  Context [A B: eqType] [p: A -> bool] [q: B -> bool].

  Fixpoint bt_map (f : {a : A | p a} -> btree q) (t: btree p): btree q :=
    match t with
    | Tip x => f x
    | l @ r => bt_map f l @ bt_map f r
    end.

  Lemma bt_map_tip f (x: { a : A | p a }):
    bt_map f (Tip x) = f x.
  Proof. by []. Qed.

  Lemma bt_map_bin f (l r: btree p):
    bt_map f (l @ r) = bt_map f l @ bt_map f r.
  Proof. by []. Qed.

  Lemma bt_map_bins f (t: btree p) (ts: seq (btree p)):
    bt_map f (t @* ts) = bt_map f t @* [seq bt_map f u | u <- ts].
  Proof. by elim: ts t=> [|v vs IH] t /=. Qed.
End BTreeMap.


Section Size.
  Context [A: eqType] [T: A -> bool].
  Notation "'btree'" := (btree T) (at level 1).
  
  Fixpoint btree_size (t: btree) :=
    match t with
    | Tip _ => 0
    | l @ r => (btree_size l + btree_size r).+1 
    end.
  Notation "| t |" := (btree_size t) (at level 10).

  Lemma bin_neR (r t: btree): r != t @ r.
  Proof.
    apply /negP=> /eqP /(f_equal btree_size) /=; lia.
  Qed.

  Lemma size_bins (t: btree) (ts: seq btree):
    | t @* ts | = | t | + sumn [seq | s | | s <- ts] + size ts.
  Proof.
    rcons_ind ts=> /= [|us u IH]; first by lia.
    by rewrite bins_rcons size_rcons map_rcons sumn_rcons /= IH; lia.
  Qed.
End Size.
Notation "| t |" := (btree_size t) (at level 10).


Section AllTip.
  Context {A: eqType}.
  Variable (p q: A -> bool).
  Notation "'btree'" := (btree p) (at level 1).

  Fixpoint all_tip (t: btree): bool :=
    match t with
    | # a => q a
    | l @ r => all_tip l && all_tip r
    end.

  Lemma all_tip_bins (t: btree) (ts: seq btree):
    all_tip (t @* ts) = all_tip t && all all_tip ts.
  Proof.
    elim: ts t=> [|u us IH] t /=; first by rewrite andbT.
    by rewrite IH /=; lia.
  Qed.
End AllTip.


Section Sub.
  Context {A: eqType} {p: A -> bool}.
  Notation "'btree'" := (btree p) (at level 1).

  Fixpoint sub (s t: btree): bool :=
    match t with
    | Tip _ => s == t
    | l @ r => [|| s == t, sub s l | sub s r ]
    end.
  Notation "s ⊑ t" := (sub s t) (at level 70).

  Lemma sub_le (s t: btree): s ⊑ t -> | s | <= | t |.
  Proof.
    elim: t=> /= [a |l IHl r IHr]; first by move=> /eqP->.
    by move=> /or3P [/eqP->|/IHl|/IHr] /=;  lia.
  Qed.

  Lemma sub_lt s t: s ⊑ t -> (s == t) || (| s | < | t |).
  Proof.
    elim: t=> [a|l IHl r IHr] /=; first by move=> ->.
    by move=> /or3P [->|/IHl|/IHr] // /orP [/eqP->|]; lia.
  Qed.

  Lemma sub_refl (t: btree): t ⊑ t.
  Proof.
    by case: t=> /= [?|??]; rewrite eq_refl.
  Qed.

  Lemma sub_asym (s t: btree): s ⊑ t -> t ⊑ s -> s = t.
  Proof.
    by move=> /sub_lt/orP[/eqP|?] // /sub_lt/orP[/eqP|?] //; lia.
  Qed.

  Lemma sub_neL (l t: btree): ~~ (l @ t ⊑ t).
  Proof. by apply /negP=> /sub_le /=; lia. Qed.

  Lemma sub_neR (r t: btree): ~~ (t @ r ⊑ t).
  Proof. by apply /negP=> /sub_le /=; lia. Qed.

  Lemma sub_all_tip (q: A -> bool) (s t: btree):
    s ⊑ t -> all_tip q t -> all_tip q s.
  Proof.
    elim: t=> [a|l IHl r IHr]=> /=; first by move=> /eqP-> /=.
    move=> /or3P[]; first by move=> /eqP-> /andP[] /= -> ->.
    - by move=> /IHl H /andP[] /H.
    - by move=> /IHr H /andP[] _ /H.
  Qed.
  
End Sub.
Notation "s ⊑ t" := (sub s t) (at level 70).


Section RightSub.
  Context {A: eqType} {p: A -> bool}.
  Notation "'btree'" := (btree p) (at level 1).

  Fixpoint rsub (s t: btree): bool :=
    match t with
    | Tip _ => s == t
    | l @ r => [|| s == t, (s != l) && rsub s l | rsub s r ]
    end.
  Notation "s ⪯ t" := (rsub s t) (at level 70).

  Lemma rsub_sub (s t: btree): s ⪯ t -> s ⊑ t.
  Proof.
    by elim: t=> [o|l IHl r IHr] //= /or3P[|/andP[] _ /IHl|/IHr]-> //=;
       rewrite !orbT.
  Qed.

  Lemma rsub_refl (t: btree): t ⪯ t.
  Proof.
    by case: t=> [o|l r] //=; rewrite eq_refl.
  Qed.

  Lemma rsub_asym (s t: btree): s ⪯ t -> t ⪯ s -> s = t.
  Proof.
    by move=> /rsub_sub ? /rsub_sub ?; apply: sub_asym.
  Qed.

  Lemma rsub_trans (s t u: btree): s ⪯ t -> t ⪯ u -> s ⪯ u.
  Proof.
    move=> st.
    elim: u=> [o|l IHl r IHr] /=.
    - by move=> to; move: to st=> /eqP-> /=.
    - move=> /or3P[].
      + by move=> tlr; move: tlr st=> /eqP-> /=.
      + move=> /andP[] netl sbtl.
        suff->: s != l by rewrite (IHl sbtl) orbT.
        apply /negP=> /eqP E.
        by move: E netl st=> -> /negP ? /(rsub_asym sbtl) /eqP.
    - by move=> /IHr->; rewrite !orbT.
  Qed.

  Lemma rsub_neL (l t: btree): ~~ (l @ t ⪯ t).
  Proof. by apply /negP=> /rsub_sub; apply /negP; apply: sub_neL. Qed.

  Lemma rsub_neR (r t: btree): ~~ (t @ r ⪯ t).
  Proof. by apply /negP=> /rsub_sub; apply /negP; apply: sub_neR. Qed.

  Lemma rsub_all_tip (q: A -> bool) (s t: btree):
    s ⪯ t -> all_tip q t -> all_tip q s.
  Proof.
    by move=> /rsub_sub; apply sub_all_tip.
  Qed.

  Fixpoint all_rsubs (t: btree): seq btree :=
    match t with
    | # _ => [:: t]
    | l @ r => [:: t] ++ [seq x <- all_rsubs l | x != l] ++ all_rsubs r
    end.

  Lemma mem_all_rsubs (s t: btree):
    s \in all_rsubs t = (s ⪯ t).
  Proof.
    elim: t=> [[a pa]|l IHl r IHr] /=.
    - by rewrite mem_seq1.
    - by rewrite in_cons mem_cat mem_filter IHl IHr.
  Qed.

  Lemma all_rsubs_is (t: btree):
    all_rsubs t = t :: [seq u <- all_rsubs t | u != t].
  Proof.
    move: t=> [[a pa]|l r] /=; rewrite eq_refl //= filter_cat; do 2 f_equal.
    - by rewrite -filter_predI; apply: eq_in_filter=> v;
         rewrite mem_all_rsubs /predI /=;
         case E: (v == l @ r)=> //; move/eqP: E (rsub_neR r l)=> -> /negP.
    - by apply: esym; apply /all_filterP /allP=> t; rewrite mem_all_rsubs;
         case E: (t == l @ r)=> //; move/eqP: E (rsub_neL l r)=> -> /negP.
  Qed.

  Lemma all_rsub_bins (t: btree) (ts: seq btree):
    all_rsubs (t @* ts) = (t @* ts) ::
                            [seq u <- all_rsubs t | u != t] ++
                            flatten [seq all_rsubs u | u <- ts].
  Proof.
    rcons_ind ts=> [|us u IH] /=.
    - by rewrite cats0 -all_rsubs_is.
    - rewrite bins_rcons /= map_rcons flatten_rcons catA; do 2 f_equal.
      rewrite IH /= eq_refl /= filter_cat -filter_predI; f_equal.
      + apply: eq_in_filter=> v {IH u}; rewrite mem_all_rsubs /=.
        move: us=> [|u us] /=; first by case: (v == t).
        by case E: (v == (t @ u) @* us)=> //; 
           move/eqP: E=> -> /rsub_sub /sub_le; rewrite size_bins /=;
           move: (sumn _) (size us)=> x y; lia.
      + apply /all_filterP /allP=> /=v /flattenP; apply: ex2_ind=> /=vs /mapP.
        apply: {u} ex2_ind=> /=u u_us ->; rewrite mem_all_rsubs.
        have sz_u: | u | <= sumn [seq | s | | s <- us]
          by elim: us u_us {IH}=> [//|x xs IH]; 
             rewrite in_cons=> /orP[/eqP->|/IH]/=; lia.
        by move=> /rsub_sub /sub_le sz_v; apply /negP=> /eqP E; subst v;
           move: {IH} sz_u sz_v; rewrite size_bins; move: (sumn _)=> x;
           move: us u_us=> [|w ws]//=; move: (size ws)=> y; lia.
  Qed.

  Lemma rsub_bins (s t: btree) (ts: seq btree):
    s ⪯ t @* ts = [|| s == t @* ts,
                      (s != t) && (s ⪯ t) |
                      has (fun u => s ⪯ u) ts ].
  Proof.
    rcons_ind ts=> [|us u IH] /=.
    - case st: (s ⪯ t); case: eqP=> // ?; subst t.
      by move: st; rewrite rsub_refl.
    - rewrite bins_rcons /= IH has_rcons.
      case su: (s ⪯ u); rewrite ?orbT //= ?orbF.
      case E: (s == t @* us)=> //=; move: E=> /eqP->.
      case: eqP=> //= _; case: us {u IH su}=> [|u us] /=.
      + by rewrite eq_refl.
      + have->: (t @ u) @* us ⪯ t = false
          by apply /negP=> /rsub_sub /sub_le; rewrite size_bins /=; lia.
        have->: (t @ u) @* us ⪯ u = false
          by apply /negP=> /rsub_sub /sub_le; rewrite size_bins /=; lia.
        rewrite andbF /=. apply: sym_eq; do 2 apply /negP; rewrite -all_predC.
        apply /allP=> v /= v_us; apply /negP=> /rsub_sub /sub_le.
        have v_sz: | v | <= sumn [seq | u | | u <- us]
          by elim: us v_us {s t u}=> //= t ts IH; 
             rewrite in_cons=> /orP [/eqP->|/IH]; lia.
        by rewrite size_bins /=; lia.
  Qed.


End RightSub.
Notation "s ⪯ t" := (rsub s t) (at level 70).
Arguments rsub_refl {A p t}.

Section DecomposeRights.
  Context {A: eqType} {p: A -> bool}.
  Notation "'btree'" := (btree p) (at level 1).

  Definition deargs (t: btree): seq btree :=
    (fix rec t rs :=
       match t with 
       | # _ => rs
       | l @ r => rec l (r :: rs)
       end) t [::].

  Lemma deargs_tip (x: { a: A | p a }):
    deargs (Tip x) = [::].
  Proof. by case: x. Qed.

  Lemma deargs_bin (s t: btree):
    deargs (s @ t) = deargs s ::< t.
  Proof.
    rewrite /deargs; match goal with |- ?f s [:: t] = _ => set rec := f end.
    rewrite -[[:: t]]cat0s. move: {1 3}[::]=> ts.
    elim: s ts=> [[a pa]|l IH r _] ts //=.
    - by rewrite cats1.
    - by rewrite -cat_cons IH.
  Qed.

  Lemma deargs_bins (t: btree) (ts: seq btree):
    deargs (t @* ts) = deargs t ++ ts.
  Proof.
    rcons_ind ts=> /= [|us u IH]; first by rewrite cats0.
    by rewrite bins_rcons deargs_bin IH rcons_cat.
  Qed.

  Lemma bins_deargs (t: btree) plt:
    Tip (exist _  (leftmost_tip t) plt) @* deargs t = t.
  Proof.
    elim: t plt=> [[x ?]|l IH r _] /= plt.
    - by f_equal; apply dec_sval_inj.
    - by rewrite deargs_bin bins_rcons IH.
  Qed.

  Lemma deargs_rsub (t s: btree):
    s \in deargs t -> s ⪯ t.
  Proof.
    move=> s_t; apply: (proj2 (A:=(s != t))); apply /andP.
    elim: t s_t=> [[x ?]|l IH r _] //=.
    rewrite deargs_bin in_rcons=> /orP[/eqP->|/IH].
    - by rewrite bin_neR rsub_refl !orbT.
    - move=> /andP[]-> s_l; apply /andP; split.
      + by apply /eqP=> s_lr; move: s_lr s_l=> ->; apply /negP; apply: rsub_neR.
      + by rewrite s_l orbT.
  Qed.
End DecomposeRights.
Arguments bins_deargs {A p} t _.
Arguments deargs_rsub {A p} t s _. 


Section Growing.
  Context {A: eqType} {p: A -> bool}.
  Notation "'btree'" := (btree p) (at level 1).

  Fixpoint growing_seq (ts: seq btree): bool :=
    match ts with
    | [::] => true
    | u :: us => match us with
               | [::] => true
               | v :: vs => (u ⪯ v) && growing_seq us end end.

  Lemma growing_seq_cons (t: btree) (ts: seq btree):
    growing_seq (t :: ts) = (t ⪯ head t ts) && growing_seq ts.
  Proof.
    by case: ts=> [|u us] //=; rewrite andbT rsub_refl.
  Qed.

  Lemma growing_seq_rcons (ts: seq btree) (t: btree):
    growing_seq (ts ::< t) = (last t ts ⪯ t) && growing_seq ts.
  Proof.
    elim: ts=> [/=|u [/=|v vs] IH]; first by rewrite rsub_refl.
    - by rewrite andbT.
    - by rewrite !rcons_cons growing_seq_cons (growing_seq_cons u);
         move: rcons_cons IH=> -> ->; rewrite /head !last_cons; lia.
  Qed.

  Lemma growing_seq_cat (t u: btree) (ts us: seq btree):
    last t ts ⪯ head u us ->
    growing_seq ts -> growing_seq us -> growing_seq (ts ++ us).
  Proof.
    elim: ts t=> [//=|t [|v ts] IH] w.
    - rewrite (growing_seq_cons t us)=> /=.
      by move: us {IH}=> [_ _ ->|z zs->_->//]; rewrite rsub_refl.
    - by rewrite last_cons cat_cons growing_seq_cons 
                 (growing_seq_cons t) {1}cat_cons=> /IH {IH}=> IH /andP[]->.
  Qed.

  Lemma growing_seq_catL (ts us: seq btree):
    growing_seq (ts ++ us) -> growing_seq ts.
  Proof.
    rcons_ind us=> [//=|us u IH]; first by rewrite cats0.
    by rewrite -rcons_cat growing_seq_rcons=> /andP[] _ /IH.
  Qed.

  Lemma growing_seq_nseq (n: nat)(t: btree):
    growing_seq (nseq n t).
  Proof.
    elim: n=> [//|n IH]; rewrite nseqS growing_seq_cons IH andbT.
    move: (head_nseq n t t)=> []->; apply: rsub_refl.
  Qed.

  Definition growing (t: btree): bool := growing_seq (deargs t).

  Lemma growing_bin (u s t: btree):
    (last u (deargs s)) ⪯ t -> growing s -> growing (s @ t).
  Proof.
    case: s=> [a|l r]; rewrite /growing /= !deargs_bin.
    - by rewrite deargs_tip.
    - by rewrite last_rcons=> rt g_lr; 
         rewrite growing_seq_rcons last_rcons rt g_lr.
  Qed.

  Lemma growing_bins (t: btree) (ts: seq btree):
    growing_seq (t :: ts) -> growing t -> growing (t @* ts).
  Proof.
    rewrite growing_seq_cons /growing deargs_bins=> /andP[] t_ts g_ts g_da.
    apply: (@growing_seq_cat t t)=> //.
    move: t_ts {g_ts g_da}; apply: rsub_trans.
    case E: (deargs t)=> [|u us]; first by rewrite rsub_refl.
    by apply: deargs_rsub; rewrite E last_cons mem_last.
  Qed.
End Growing.


(* Combinators and Terms *)
Section CombinatorTerm.

  Record combinator: Type := { arity : nat;
                               rhs   : btree (fun i => i < arity) }.
  
  Definition combinator_eq (c1 c2: combinator): bool :=
    let '{|arity := n1; rhs := t1|} := c1 in
    let '{|arity := n2; rhs := t2|} := c2 in
    (if n1 == n2 as b return n1 == n2 = b -> bool then
       fun E => eq_rect n1 _ (fun t => t1 == t) n2 (elimTF eqP E) t2
     else
       fun _ => false) erefl.

  Lemma combinator_eqP: Equality.axiom combinator_eq.
  Proof.
    case=> [n1 c1] [n2 c2]; rewrite /combinator_eq.
    case: eqP=> [E1|?]; last by constructor; case.
    subst n2; rewrite [elimTF _ _]eq_irrelevance.
    rewrite -Eqdep_dec.eq_rect_eq_dec; last by apply: PeanoNat.Nat.eq_dec.
    case: eqP; constructor; first by subst c2.
    by case=> /(Eqdep_dec.inj_pair2_eq_dec nat _ _ _ _ _)
           => /(_ PeanoNat.Nat.eq_dec).
  Qed.
 
  HB.instance Definition _ := hasDecEq.Build combinator combinator_eqP.
  
  Tactic Notation "by" "rule" constr(arity) uconstr(rhs) :=
      by refine (Build_combinator (arity:=arity) rhs).

  Example S: combinator. by rule 3 (#0 @ #2 @ (#1 @ #2)). Defined.
  Example K: combinator. by rule 2 (#0).                  Defined.
  Example B: combinator. by rule 3 (#0 @ (#1 @ #2)).      Defined.
  Example O: combinator. by rule 2 (#1 @ (#0 @ #1)).      Defined.
  Example P: combinator. by rule 3 (#2 @ (#0 @ #1 @ #2)). Defined.

  Definition cterm: eqType := btree (fun c: combinator => true).
  Notation "' c" := (Tip (exist _ c is_true_true)) (at level 1, format "' c").

  Example SKK: cterm := 'S @ 'K @ 'K.
  Example BOP: cterm := 'B @ 'O @ 'P.

  Definition pure (c: combinator) (t: cterm): bool := all_tip (eq_op c) t.

  Lemma pure_combinator (c: combinator) (t: cterm):
    pure c t -> c = leftmost_tip t.
  Proof.
    elim: t=> [[x ?]|l IH r _] /=; first by move=> /eqP.
    by move=> /andP[] /IH.
  Qed.
    
End CombinatorTerm.
Notation "' c" := (Tip (exist _ c is_true_true)) (at level 1, format "' c").


Section Reduction.

  Definition _substitute (arity: nat) (args: seq cterm)
    (ari: arity = size args) (rhs: btree (fun i => i < arity)): cterm.
    refine (bt_map (fun '(exist n pn)=> safe_nth args n _) rhs).
    by rewrite -ari.
  Defined.

  Definition substitute
    (c: combinator) (args: seq cterm) (ari: arity c = size args): cterm :=
    _substitute ari (rhs c).

  Inductive Reduce: cterm -> cterm -> Prop :=
  | RJust (c: combinator) (args: seq cterm) (ari: arity c = size args):
      Reduce ('c @* args) (substitute ari)
  | RAppL l1 l2 r: Reduce l1 l2 -> Reduce (l1 @ r) (l2 @ r)
  | RAppR l r1 r2: Reduce r1 r2 -> Reduce (l @ r1) (l @ r2).

  Lemma Reduce_bins s t xs:
    Reduce s t -> Reduce (s @* xs) (t @* xs).
  Proof.
    by move=> s_t; rcons_ind xs=> [//|xs x IH]; rewrite !bins_rcons; apply: RAppL.
  Qed.

  Lemma pure_substutute c args (ari: arity c = size args):
    all (pure c) args -> pure c (substitute ari).
  Proof.
    move: c (c) ari=> c0 []/= n t ari;
    rewrite /substitute /_substitute /= => p_args.
    match goal with |- context[bt_map ?e _] => set f := e end.
    move: {2}t; elim=>[[i pi]|l IHl r IHr] /=; last by rewrite IHl IHr.
    by rewrite (nth_safe 'c0); move: {f} p_args=> /all_nthP /(_ i); subst n; apply.
  Qed.

  Lemma Reduce_pure c s t:
    Reduce s t -> pure c s -> pure c t.
  Proof.
    elim=> [x args ari|l1 l2 r _ IH|l r1 r2 _ IH] /=.
    - by rewrite /pure all_tip_bins=> /andP[] /eqP ->; apply: pure_substutute.
    - by move=> /andP[] /IH-> ->.
    - by move=> /andP[] -> /IH->.
  Qed.
End Reduction.

Ltac _solve_rule t rs :=
  match t with
  | '?c => refine (RJust (c:=c) (args:=rs) _)
  | ?l @ ?r => _solve_rule l (r :: rs)
  end.

Tactic Notation "by" "reduction" :=
  match goal with
    |- Reduce ?t _ => _solve_rule t ([::]: seq cterm); done
  end.

Section ReduceCombinator.

  Fact rule_S x y z : Reduce ('S @ x @ y @ z) (x @ z @ (y @ z)).
  Proof. by reduction. Qed.

  Fact rule_K x y   : Reduce ('K @ x @ y) x.
  Proof. by reduction. Qed.

  Fact rule_B x y z : Reduce ('B @ x @ y @ z) (x @ (y @ z)).
  Proof. by reduction. Qed.

  Fact rule_O x y  : Reduce ('O @ x @ y) (y @ (x @ y)).
  Proof. by reduction. Qed.

  Fact rule_P x y z: Reduce ('P @ x @ y @ z) (z @ (x @ y @ z)).
  Proof. by reduction. Qed.
  
End ReduceCombinator.


Section ThetaCombinator.

  Definition iota_lt u: forall m n, m + n <= u -> seq { i | i < u }.
    refine (fix rec m n :=
              match n with
              | 0 => fun _ => [::]
              | k.+1 => fun H => exist _ m _ :: rec m.+1 k _
              end).
    by apply (leq_ltn_trans (leq_addr k m)); rewrite -addnS.
    by rewrite addSnnS.
  Defined.

  Lemma PI_iota_lt u m1 n1 p1 m2 n2 p2:
    m1 = m2 -> n1 = n2 -> @iota_lt u m1 n1 p1 = @iota_lt u m2 n2 p2.
  Proof.
    move=> ? ?; subst m2 n2.
    by have->: p1 = p2 by apply eq_irrelevance.
  Qed.

  Lemma size_iota_lt u m n (mn_u: m + n <= u):
    size (iota_lt mn_u) = n.
  Proof.
    by elim: n m mn_u=> [|n IH]//= m mn_u; rewrite IH.
  Qed.

  Lemma nth_iota_lt u m n (mn_u: m + n <= u) i d p:
    i < n -> nth d (iota_lt mn_u) i = exist _ (m + i) p.
  Proof.
    elim: n u d m mn_u i p=> [|n IH] u d m mn_u [|i] p //=.
    - by move=> _; apply: dec_sval_inj; rewrite /=addn0.
    - rewrite ltnS=> /IH->; first by rewrite addSnnS.
      by move=> ?; apply: dec_sval_inj; rewrite /=addSnnS.
  Qed.

  Definition rhs_Theta_succ (m: nat): btree (fun i => i < m.+1).
    refine (Tip (exist _ m (ltnSn m)) @
              # 0 @* [seq Tip (exist _ i _)|'(exist i pi) <- @iota_lt m.+1 1 m _]).
    exact: ltn0Sn.
    exact: pi.
    by rewrite add1n.
  Defined.

  Definition Theta_succ (m: nat): combinator :=
    {| arity := m.+1; rhs := rhs_Theta_succ m |}.

  (* Θ(n) is appropriately defined only when n>0. Θ(0) is defined as Θ(1). *)
  Notation "'Θ' n" := (Theta_succ n.-1) (at level 10).

  Fact rule_Theta n x xs:
    n = size (x :: xs) ->
    Reduce ('(Θ n) @* (x :: xs)) (last x (x :: xs) @ x @* xs).
  Proof.
    move=> ?; subst n.
    have ari: arity (Θ(size (x :: xs))) = size (x :: xs) by [].
    suff->: (last x (x :: xs) @ x @* xs =
               substitute ari) by apply: RJust.
    move: ari=> /=; rewrite /Theta_succ /substitute /rhs /rhs_Theta_succ.
    have p: 1 + size xs <= (size xs).+1 by rewrite add1n.
    rewrite (PI_iota_lt _ p erefl erefl) /_substitute=> ari;
    rewrite bt_map_bin /arity; f_equal.
    - by rewrite bt_map_tip (nth_safe x) (last_nth x).
    - rewrite bt_map_bins -map_comp /comp; f_equal.
      apply: (@eq_from_nth _ x).
      + by rewrite size_map size_iota_lt.
      + move=> i. 
        have x0: { n | n < (size xs).+1 } by exists 0.
        move=> pi; rewrite (nth_map x0 x); last by rewrite size_iota_lt.
        by rewrite nth_iota_lt // bt_map_tip (nth_safe x) add1n.
  Qed.
  
  Corollary rule_Theta2 x y: Reduce ('(Θ 2) @ x @ y) (y @ (x @ y)).
  Proof. by reduction. Qed.

  Corollary rule_Theta3 x y z:
    Reduce ('(Θ 3) @ x @ y @ z) (z @ (x @ y @ z)).
  Proof. by reduction. Qed.

End ThetaCombinator.
Notation "'Θ' n" := (Theta_succ n.-1) (at level 10).

Section k_Growing.
  Variable k: nat.
  Variable pk: 0 < k.
  
  Definition k_arity (t: cterm): bool := k %| size (deargs t).

  Lemma k_arity_bins (t: cterm) (ts: seq cterm):
    k = size ts -> k_arity t -> k_arity (t @* ts).
  Proof.
    by rewrite /k_arity deargs_bins size_cat=> ->; rewrite dvdn_addl.
  Qed.

  Definition kth_arg (t: cterm): bool :=
    (size (deargs t) <= k) || is_bin (nth t (deargs t) k).

  Lemma kth_arg_bins (t: cterm) (ts: seq cterm):
    k = size ts -> k_arity t -> kth_arg t ->
    growing_seq (t :: ts) -> kth_arg (t @* ts).
  Proof.
    move=> sz; have ts_ne: ts <> [::] by move=> ts_is; move: ts_is sz pk=> -> ->.
    rewrite /k_arity /kth_arg deargs_bins size_cat=> ari; case: leqP.
    - move: ari=> /dvdnP[][|m];
        first by case da_t: (deargs t)=> ->; rewrite mul0n add0n sz leqnn.
      move:m => [|m->?]; last by lia.
      rewrite mul1n=> sz_da.
      have b_t: is_bin t.
        by rewrite -(bins_deargs t)=> //= p; move: (deargs t) sz_da pk=> rs;
           rcons_ind rs=> [<-|rs r] //=; rewrite bins_rcons.
      rewrite nth_cat sz_da ltnn subnn growing_seq_cons=> _ _ /andP[] sb_t.
      by move: ts orbT sz ts_ne sb_t b_t=> [//|[[n pn]|l r]] us /= // _ _ _ /eqP ->.
    - by rewrite nth_cat=> sz_da; rewrite sz_da /= => b_kth _;
         rewrite (set_nth_default t (t @* ts) sz_da) b_kth orbT.
  Qed.

  Definition k_growing (t: cterm) :=
    all (fun s => [&& k_arity s, growing s & kth_arg s]) (all_rsubs t).

  Lemma rsub_k_growing (s t: cterm):
    s ⪯ t -> k_growing t -> k_growing s.
  Proof.
    by move=> sbst /allP k_t; apply /allP=> u;
       rewrite mem_all_rsubs=> /rsub_trans /(_ sbst);
       rewrite -mem_all_rsubs=> /k_t.
  Qed.

  Lemma rsub_k_growing_at (s t: cterm):
    s ⪯ t -> k_growing t -> [/\ k_arity s, growing s & kth_arg s].
  Proof.
    by rewrite -mem_all_rsubs=> sbst /allP /(_ s sbst) /and3P.
  Qed.

  Lemma k_growing_bins t ts:
    k = size ts -> growing_seq (t :: ts) -> all k_growing (t :: ts) ->
    k_growing (t @* ts).
  Proof.
    rewrite all_cons; move=> sz g_tts /andP[] k_t k_ts.
    apply /allP=> u; rewrite mem_all_rsubs rsub_bins=> /or3P[/eqP->|/andP[_]|].
    - move: k_t=> /allP /(_ t); rewrite mem_all_rsubs
        => /(_ rsub_refl)/and3P[] ari_t grw_t kth_t; apply /and3P; split.
      + by apply: k_arity_bins.
      + by apply: growing_bins.
      + by apply: kth_arg_bins.
    - by move: k_t=> /allP /(_ u); rewrite mem_all_rsubs.
    - by move=> /hasP; apply: ex2_ind=> /= v v_ts;
         move: k_ts=> /allP /(_ v v_ts)=> /allP /(_ u); rewrite mem_all_rsubs.
  Qed.
End k_Growing.

Definition Theta_invariant n t :=
  pure (Θ n) t /\
  exists xs xn ys,
    [/\ t = '(Θ n) @* (xs ++ xn :: ys),
        n = (size xs).+1,
        growing_seq (xs ::< xn),
        is_bin xn &
        all (k_growing n.-1) (xs ::< xn)].

Lemma Theta_invariant_instance n: 1 < n ->
  let c := '(Θ n) in
  Theta_invariant n (c @* (nseq n.-1 c) @ c @* (nseq n.-1 c)).
Proof.
  case: n=> [|[|k]] // _; rewrite -pred_Sn /=;
  set c := '(Θ k.+2); set cs := nseq k c.
  have p_ccs: pure (Θ k.+2) ((c @ c) @* cs)
    by rewrite /pure all_tip_bins /= eq_refl all_nseq; apply /orP; right=> /=.
  split; rewrite -/c; first by move=> /=; rewrite p_ccs.
  exists (c :: cs), (c @* cs @ c), [::]; split=> //.
  - by rewrite /= cats1 -(bins_rcons c) -nseqSr bins_rcons.
  - by rewrite /= size_nseq.
  - rewrite growing_seq_rcons last_cons growing_seq_cons /=.
    have->: last c cs = c by move: (last_nseq k c c)=> [].
    have->: head c cs = c by move: (head_nseq k c c)=> [].
    by rewrite eq_refl !orbT rsub_refl /= growing_seq_nseq.
  - rewrite -pred_Sn all_rcons all_cons all_nseq /= orbT andbT.
    have {p_ccs} k_c: k_growing k.+1 c by [].
    apply /allP=> t; rewrite mem_all_rsubs /= -/c=> /or3P[/eqP| |/eqP->//].
    + move=> t_is; have sz_da: size (deargs t) = k.+1.
        by rewrite t_is deargs_bin deargs_bins size_rcons size_cat add0n size_nseq.
        apply /and3P; split.
      * by rewrite /k_arity sz_da dvdnn.
      * by rewrite /growing t_is deargs_bin deargs_bins cat0s -nseqSr 
                   growing_seq_nseq.
      * by rewrite /kth_arg sz_da ltnSn.
    + move=> /andP[] /= /negbTE; rewrite rsub_bins=> -> /= /orP[].
      * by move=> /andP[]/eqP ? /eqP.
      * by move=> /hasP; apply: ex2_ind=> u;
           rewrite mem_nseq=> /andP[] _ /eqP-> /= /eqP->.
Qed.    

Theorem Theta_invariant_exists n:
  1 < n -> exists t, Theta_invariant n t.
Proof.
  move=> /Theta_invariant_instance /=.
  by match goal with |- _ _ ?t -> _ => move=> ?; exists t end.
Qed.

Theorem Theta_invariant_preserved n:
  1 < n -> forall t, Theta_invariant n t ->
               exists u, Reduce t u /\ Theta_invariant n u.
Proof.
  move: n=> [|[|k]] // _ t [] p_t [[|x xs]][xn][ys][t_is][//sz_xs]g_xsn b_xn.
  move: t_is; rewrite -cat_rcons rcons_cons bins_cat -pred_Sn=> t_is k_xsn.
  exists ((xn @ x @* (xs ::< xn)) @* ys).
  match goal with |- ?P /\ _ =>
     have red_t: P 
       by move: (@rule_Theta k.+2 x (xs ::< xn)); 
          rewrite /=last_rcons size_rcons -sz_xs t_is /= => /(_ erefl);
          apply: Reduce_bins
  end; split=> //; split; first by exact: Reduce_pure red_t p_t.
  move: k_xsn; rewrite all_cons all_rcons=> /and3P[]=> k_x k_xn k_xs.
  move: (k_xn)=> /allP /(_ xn); 
  rewrite mem_all_rsubs=> /(_ rsub_refl)=> /and3P[] ari_xn grw_xn kth_xn.
  case da_xn: (deargs xn)=> [|v vs];
    first by move: da_xn (bins_deargs xn) b_xn=> -> <-.
  move: (deargs_rsub xn)=> sb_da; move: (sb_da); rewrite da_xn=> /allP.
  rewrite all_cons=> /andP[] v_xn /allP vs_xn.
  move: (rsub_k_growing v_xn k_xn)=> k_v.
  have k_vs: all (k_growing k.+1) vs
    by apply /allP; move=> u /vs_xn /rsub_k_growing /(_ k_xn).
  have is_xn: ' (Θ k.+2) @* deargs xn = xn
     by rewrite -{2}(bins_deargs xn) // => ?; do 2 f_equal; 
        apply: dec_sval_inj=> /=; move: t_is p_t => ->; 
        rewrite -rcons_cons bins_rcons /pure all_tip_bins /= 
          => /andP[]/andP[]/=_ /pure_combinator.
  move: ari_xn=> /dvdnP[[|[|m]]]; rewrite da_xn ?mul0n ?mul1n; first by [].
  - move=> sz_vvs; have {sz_vvs} sz_vs: k = size vs by move: sz_vvs=> /=[] <-.
    exists (v :: vs), (x @* (xs ::< xn)), ys; move: grw_xn.
    rewrite bins_cat -{1 3}da_xn is_xn /= -sz_vs bins_rcons k_v all_rcons k_vs 
            /= growing_seq_rcons /growing=> ->; rewrite !andbT; split=> //.
    + by rewrite da_xn last_cons; move: (mem_last v vs); rewrite -da_xn=> /sb_da;
         move=> /rsub_trans; apply; rewrite /= rsub_refl !orbT.
    + move: g_xsn; rewrite rcons_cons=> /(@k_growing_bins k.+1 (ltn0Sn _)).
      by rewrite size_rcons -sz_xs bins_rcons all_cons all_rcons k_x k_xn k_xs 
                 /=; apply.
  - move=> sz_vvs; have sz_tk: size (take k vs) = k
      by move: sz_vvs=> /=; rewrite size_take_le; move: (size vs)=> z; 
         case: leqP; clear; lia.
    have sz_dr: 0 < size (drop k vs)
      by move: sz_vvs; rewrite /= size_drop subn_gt0 -ltnS=> ->; clear; lia.
    case d_vs: (drop k vs)=> [|z zs]; first by move: d_vs sz_dr=> ->.
    exists (v :: take k vs), z, (zs ::< x @* (xs ::< xn) ++ ys).
    rewrite -cat_cons -rcons_cons -d_vs cat_rcons catA cat_cons cat_take_drop 
            -da_xn bins_cat is_xn -pred_Sn.
    have->: ((v :: take k vs) ::< z) = take k.+2 (deargs xn)
      by rewrite da_xn rcons_cons /= -{2}(cat_take_drop k vs) d_vs -cat_rcons 
                 take_cat size_rcons sz_tk ltnn subnn take0 cats0.
    rewrite /= sz_tk; split=> //.
    + by move: grw_xn; rewrite /growing -{1}(cat_take_drop k.+2 (deargs xn));
         apply: growing_seq_catL.
    + move: kth_xn; rewrite /kth_arg da_xn -{2}(cat_take_drop k vs) /= nth_cat 
                            sz_tk ltnn subnn d_vs /= => /orP[] //.
      move: sz_vvs=> /= ->; clear; lia.
    + by move: k_v k_vs; rewrite da_xn -{1}(cat_take_drop k.+1 vs) all_cat /= 
           => -> /andP[]->.
Qed.
