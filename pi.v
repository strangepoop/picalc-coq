From Coq Require Import Lists.List.
Import ListNotations.


(* Helper funcs *)

Fixpoint map {X Y} (f : X -> Y) (xs : list X) : list Y :=
 match xs with
  | [] => []
  | (h :: t) => (f h) :: (map f t)
end.

Lemma map_distr_app {X Y} : forall (f : X -> Y) (x y : list X),

map f (x ++ y) = (map f x) ++ (map f y).

Proof. intros. induction x.
 - replace (map f []) with ([] : list Y). 
   rewrite app_nil_l. rewrite app_nil_l. reflexivity. 
   unfold map. reflexivity.
 - rewrite <- app_comm_cons. destruct x eqn : Heqn.
    + unfold map. reflexivity.
    + unfold map in *. rewrite IHx. reflexivity.
Qed.

Fixpoint foldr {X Y} (f : X -> Y -> Y) (y : Y) (xs : list X) : Y :=
 match xs with
  | [] => y
  | (h :: t) => f h (foldr f y t)
end.

Lemma foldr_nil {X Y} : forall (f : X -> Y -> Y) e, foldr f e [] = e.
Proof. unfold foldr. reflexivity. Qed.

Lemma foldr_one {X Y} : forall (f: X -> Y -> Y) e a xs, 
foldr f e (a::xs) = f a (foldr f e xs).
Proof. unfold foldr. reflexivity. Qed.

(*
Class monoid (X : Type) := {
  unit : X;
  func : X -> X -> X;
  monoid_unit_l : forall x, func unit x = x;
  monoid_unit_r : forall x, func x unit = x;
  monoid_assoc  : forall x y z, func (func x y) z = func x (func y z)
}. *)

Lemma foldr_monoid_helper {X}: forall (f : X -> X -> X) (x e : X) (xs : list X),
(forall a b c, f (f a b) c = f a (f b c)) ->
(forall a, f a e = a) -> (forall a, f e a = a) ->
f (foldr f e xs) x = foldr f e (xs ++ [x]).
Proof. intros. induction xs.
 - unfold app. unfold foldr. rewrite H0. rewrite H1. reflexivity.
 - rewrite <- app_comm_cons. rewrite foldr_one. rewrite foldr_one.
   rewrite <- IHxs. apply H.
Qed.

Lemma foldr_monoid {X}: forall (f : X -> X -> X) (x e : X) (xs ys: list X),
(forall a b c, f (f a b) c = f a (f b c)) ->
(forall a, f a e = a) -> (forall a, f e a = a) ->
f (foldr f e xs ) (foldr f e ys) = foldr f e (xs ++ ys).
Proof. intros. generalize xs. induction ys.
- intros. rewrite app_nil_r. rewrite foldr_nil. apply H0.
- intros. rewrite foldr_one. replace (a :: ys) with ([a] ++ ys).
  rewrite app_assoc. rewrite <- H. rewrite foldr_monoid_helper. apply IHys.
  apply H. apply H0. apply H1. rewrite <- app_comm_cons. apply app_nil_l.
Qed.


(* not really modeled yet *)
Inductive name : Set := (*a | b | c | a' | b' | c'*) name1 | name2.


Inductive prefix : Type :=
 | Inn : name -> prefix
 | Out : name -> prefix
 | Tau : prefix.

Inductive proc : Type :=
 | pi   : prefix -> proc -> proc
 | plus : proc -> proc -> proc
 | zero : proc
 | par  : proc -> proc -> proc
 | new  : list name -> proc -> proc.

Notation "a * P" := (pi (Inn a) P).
Notation "a ^ P" := (pi (Out a) P).
Definition t (P : proc) := pi Tau P.

Notation "P + Q" := (plus P Q).
Notation "P / Q" := (par P Q).
Notation "0" := zero.

Definition foldsum := foldr plus 0.
Definition foldpar := foldr par 0.

Definition uncurried_pi (p : prefix * proc) : proc :=
 pi (fst p) (snd p).

Definition sigmands := list (prefix * proc).

Definition sigma (l : sigmands) : proc :=
 foldsum (map uncurried_pi l).


(* Ideally should've done it like this, and separately defined ~ as an equivalance relation.

Definition cong (p : proc) (q : proc) := Prop.
Notation "P ~ Q" := (cong P Q) (at level 80).

Axiom comm_sum : forall P Q, (P + Q) ~ (Q + P).
Axiom assoc_sum : forall P Q R, (P + (Q + R)) ~ ((P + Q) + R).
Axiom comm_par : forall P Q, (P | Q) ~ (Q | P).
Axiom assoc_par : forall P Q R, (P | (Q | R)) ~ ((P | Q) | R).
Axiom unit_sum : forall P, P + 0 ~ P.
Axiom unit_par : forall P, P | 0 ~ P.
...
*)

Axiom comm_sum : forall P Q, (P + Q) = (Q + P).
Axiom assoc_sum : forall P Q R, ((P + Q) + R) = (P + (Q + R)).

Axiom comm_par : forall P Q, (P / Q) = (Q / P).
Axiom assoc_par : forall P Q R, ((P / Q) / R) = (P / (Q / R)).

Axiom unit_sum : forall P, P + 0 = P.
Axiom unit_par : forall P, P / 0 = P.

Axiom app_new : forall a b P, (new a) (new b P) = (new (a ++ b) P).
Axiom app_new_flip : forall a b P, (new b) (new a P) = (new (a ++ b) P).
Axiom unit_new : forall a, new a 0 = 0.


(* tautological definition *)
Definition notfree (x : list name) (Q : proc) := True.

Axiom alpha_new_sum : forall x P Q, notfree x Q -> (new x P) + Q = new x (P + Q).
Axiom alpha_new_par : forall x P Q, notfree x Q -> (new x P) / Q = new x (P / Q).

(* Assume that alpha conversion is done automatically,
even though someone has to do the work of tracking fn's *)


Lemma auto_alpha_new_sum : forall x P Q, (new x P) + Q = new x (P + Q).
Proof. intros. apply alpha_new_sum. unfold notfree. auto. Qed.
Lemma auto_alpha_new_par : forall x P Q, (new x P) / Q = new x (P / Q).
Proof. intros. apply alpha_new_par. unfold notfree. auto. Qed.



(* Helper lemmas *)
Ltac unfoldall :=
   try unfold map; try unfold sigma; try unfold foldsum; try unfold map;
   try unfold foldpar; try unfold foldr; try unfold uncurried_pi;
   try unfold fst; try unfold snd.


Lemma sig_triv_0 : 0 = sigma [].
Proof. unfoldall. reflexivity. Qed.
Lemma sig_triv_1 : forall a P, pi a P = sigma [(a,P)].
Proof. intros. unfoldall. symmetry. apply unit_sum. Qed.



Lemma auto_gen_new : forall x P, P = new x P.

Proof. intros. replace (P = new x P) with (P / 0 = new x P).
 replace 0 with (new x 0).
 rewrite comm_par. rewrite auto_alpha_new_par.
 rewrite comm_par. rewrite unit_par. reflexivity.
 apply unit_new. rewrite unit_par. reflexivity.
Qed.


Lemma auto_app_new_par : forall x y P Q, (new x P) / (new y Q) = new (x ++ y) (P / Q).

Proof. intros. rewrite auto_alpha_new_par.
rewrite comm_par. rewrite auto_alpha_new_par.
rewrite app_new. rewrite comm_par. reflexivity.
Qed.


Lemma auto_app_new_sum : forall x y P Q, (new x P) + (new y Q) = new (x ++ y) (P + Q).

Proof. intros. rewrite auto_alpha_new_sum.
rewrite comm_sum. rewrite auto_alpha_new_sum.
rewrite app_new. rewrite comm_sum. reflexivity.
Qed.


Lemma foldpar_distr_par : forall l1 l2, (foldpar l1) / foldpar (l2) = foldpar (l1 ++ l2).

Proof. unfold foldpar. intros. apply foldr_monoid.
apply 0. apply assoc_par. apply unit_par.
intros. rewrite comm_par. apply unit_par.
Qed.

(*
intros. generalize l1. induction l2.
 - intros. rewrite app_nil_r. replace (foldpar []) with 0.
   rewrite unit_par. reflexivity. unfold foldpar.
   unfold foldr. reflexivity.
 - intros. unfold foldpar. replace (foldr par 0 (a :: l2)) with (a / (foldr par 0 l2)).
   rewrite <- assoc_par. fold foldpar. replace (a :: l2) with ([a] ++ l2).
   rewrite app_assoc. rewrite <- IHl2.
   replace (foldpar (l0 ++ [a])) with (foldpar l0 / a). reflexivity.
   + induction l0.
    * unfold app. unfold foldpar. unfold foldr. apply comm_par.
    * unfold foldpar. apply foldr_monoid.
      apply assoc_par. apply unit_par.
      intros. rewrite comm_par. apply unit_par.
   + unfold app. reflexivity.
   + unfold foldr. reflexivity.
Qed.
*)


(* workaround for unguarded sum *)
Lemma wrong : forall l1 l2, foldpar (map sigma l1) + foldpar (map sigma l2)
 = foldpar (map sigma (l1 ++ l2)).
Proof. Admitted.



Theorem normal : forall (P : proc),
  (exists ns l,
    P = new ns (foldpar (map sigma l))
  ).
(* P = new a (M | N | ...)  where M = \sigma a.P, ... *)

Proof. intros. induction P.
 - exists []. exists [[(p, P)]].
   rewrite <- auto_gen_new. (* P = new a P *)
   unfoldall.
   rewrite unit_sum. rewrite unit_par.
   reflexivity.
 - destruct IHP1 as [ns1 [l1 H1]].
   destruct IHP2 as [ns2 [l2 H2]].
   exists (ns1 ++ ns2).
   exists (l1 ++ l2). rewrite <- wrong. (* WRONG: that's not the list I want!*)
   rewrite <- auto_app_new_sum.
   rewrite H1. rewrite H2. reflexivity.
 - exists []. exists [[]]. unfoldall.
   rewrite unit_par. rewrite unit_new. (* 0 = new a 0 *)
   reflexivity.
 - destruct IHP1 as [ns1 [l1 H1]].
   destruct IHP2 as [ns2 [l2 H2]].
   exists (ns1 ++ ns2). exists (l1 ++ l2).
   rewrite H1. rewrite H2. rewrite auto_app_new_par. (* new "distributes" over par*)
   rewrite foldpar_distr_par. rewrite map_distr_app. reflexivity. (* other distributive things *)
 - destruct IHP as [ns [l1 H]].
   exists (l ++ ns). exists l1. rewrite H. apply app_new.
Qed.

(* P -- Q for linking. will need substitution formalized (and so dependent types? Vect. of same size) *)
(* (P -- Q) -- R = P -- (Q --r)*)


(* Reaction Rules *)

Reserved Notation "x '~>' y" (at level 80).

Inductive reaction : proc -> proc -> Prop :=
 | TAU (P : proc) (M : sigmands) :
    (t P + sigma M) ~> P

 | REACT (a : name) (P Q M N: proc) (Ms Ns : sigmands) (*(Heq : a = b)*)
    (Hsig : M = sigma Ms /\ N = sigma Ns) :

    (a*P + M) / (a^Q + N) ~>(P / Q)

 | PAR (P P' Q : proc) 

    (H : P ~> P') :
    (P / Q) ~> (P' / Q)

 | RES (P P' : proc) (ns : list name) 

    (H : P ~> P') :
    new ns P ~> new ns P'

where "x ~> y" := (reaction x y).
 (* struct is an equality lol! *)

 (* have to do substitutions in react *)


Example page34 : forall Q1 Q2 R1 R2 a a' b,
 new [a'] ((a'*Q1 + b*Q2) / a'^0) / (b^R1 + a^R2) ~>
 (new [a'] Q1) / (b^R1 + a^R2).
Proof. intros.

  eapply PAR.
  eapply RES.

(* make it readable to REACT *)
replace (a'^0) with (a'^0 + 0).
replace Q1 with (Q1 / 0). replace (a'*(Q1 / 0)) with (a'* Q1).

  eapply REACT.

(* wind up with implicit STRUCT *)
rewrite sig_triv_1. rewrite sig_triv_0. auto.
rewrite unit_par. reflexivity. apply unit_par. apply unit_sum.
Qed.


Example ex_4_14 : forall Q1 Q2 R1 R2 a a' b,
 new [a'] ( (a'*Q1 + b*Q2) / (b^R1 + a^R2) / a^0) ~>
 new [a'] (Q2 / R1 / a^0).
Proof. intros.

  eapply RES.
  eapply PAR.

rewrite comm_sum.

  eapply REACT.

rewrite sig_triv_1. rewrite sig_triv_1. auto.
Qed.


Example eg_4_15_lottery : forall
A B C A0 B0 C0 A1 B1 C1 A2 B2 C2 L0 L1 L2 L0b L1b L2b a0 a1 a2 b0 b1 b2,

(forall x y z, A x y z = x^(C x y z) ) /\
(forall x y z, C x y z = (t (B x y z) + z*(A x y z))) /\
(forall x y z, B x y z = y*(C x y z)) ->

 A0 = A a0 b0 a1 /\
 B0 = B a0 b0 a1 /\
 C0 = C a0 b0 a1 ->

 A1 = A a1 b1 a2 /\
 B1 = B a1 b1 a2 /\
 C1 = C a1 b1 a2 ->

 A2 = A a2 b2 a0 /\
 B2 = B a2 b2 a0 /\
 C2 = C a2 b2 a0 -> 

 L0 = new [a0;a1;a2] (C0 / A1 / A2) /\
 L1 = new [a0;a1;a2] (A0 / C1 / A2) /\
 L2 = new [a0;a1;a2] (A0 / A1 / C2) ->

 L0b = new [a0;a1;a2] (B0 / A1 / A2) /\
 L1b = new [a0;a1;a2] (A0 / B1 / A2) /\
 L2b = new [a0;a1;a2] (A0 / A1 / B2) ->


(L0 ~> L1) /\ (L0 ~> L0b) /\ (L0b / b0^0 ~> L0).

Proof. intros A B C A0 B0 C0 A1 B1 C1 A2 B2 C2 L0 L1 L2 L0b L1b L2b a0 a1 a2 b0 b1 b2.
intros [DefA [DefC DefB]].
intros [DefA0 [DefB0 DefC0]].
intros [DefA1 [DefB1 DefC1]].
intros [DefA2 [DefB2 DefC2]].
intros [DefL0 [DefL1 DefL2]].
intros [DefL0b [DefL1b DefL2b]].

split. +

rewrite DefL0. rewrite DefL1.

  eapply RES.
  eapply PAR.

rewrite DefC0. rewrite DefC. rewrite <- DefB0. rewrite <- DefA0.
rewrite DefA1. rewrite DefA. rewrite <- DefC1.

rewrite comm_sum.
replace (t B0) with (sigma [(Tau,B0)]).
replace (a1 ^ C1) with (a1 ^ C1 + sigma []).

  eapply REACT.

auto. rewrite <- sig_triv_0. apply unit_sum.
unfold t. symmetry. apply sig_triv_1.

+split. -

rewrite DefL0. rewrite DefL0b.

  eapply RES.
  eapply PAR.
  eapply PAR.

rewrite DefC0. rewrite DefC. rewrite <- DefA0.
rewrite <- DefB0. rewrite sig_triv_1.

  eapply TAU.

-

rewrite DefL0b. rewrite DefL0.
rewrite auto_alpha_new_par.

  eapply RES.

rewrite comm_par. rewrite <-assoc_par. rewrite <-assoc_par.

  eapply PAR.
  eapply PAR.

rewrite DefB0. rewrite DefB. rewrite <- DefC0.

rewrite comm_par. rewrite <- unit_par.
replace (b0*C0) with (b0*C0 + sigma []).
replace (b0^0) with (b0^0 + sigma []).

  eapply REACT.

auto.
rewrite <-sig_triv_0. apply unit_sum.
rewrite <-sig_triv_0. apply unit_sum.
Qed.




(** Full Pi Calculus 


Inductive fprefix : Type :=
 | finn (n : name) (n : name)
 | fout (n : name) (n : name)
 | ftau.

Inductive fproc : Type :=
 | fsum (l : list (fprefix * fproc))
 | fpar (P : fproc) (Q : fproc)
 | fnew (ns : list name)
 | frep (P : fproc).

Notation "a .* P" := ((finn a, P)) (at level 60).
Notation "a .^ P" := ((fout a, P)) (at level 60).
Notation "x .+ y" := (fsum [x;y]) (at level 61).
Definition ft (P : fproc) := fsum [(ftau, P)].


Notation "P ./ Q" := (par P Q) (at level 62).
Notation "00" := (fsum []).

**)


