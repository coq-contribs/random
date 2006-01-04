(** * Bernouilli.v: Simulating Bernouilli distribution *)
Require Export Prog.
Set Implicit Arguments.

Module Bernouilli (Univ:Universe).
Module RP := (Rules Univ).
(* begin hide *)
Import Univ.
Import RP.
Import RP.PP.
Import RP.PP.MP.
Import RP.PP.MP.UP.
(* end hide *)
(** ** Program for computing a Bernouilli distribution
       bernouilli p gives true with probability p 
       and false with probability (1-p)
<<
let rec bernouilli x = if flip then 
        if x < 1/2 then false else bernouilli (2 p - 1)
        else if x < 1/2 then bernouilli (2 p) else true
>>*)
Hypothesis dec_demi : forall x : U, {x < [1/2]}+{[1/2] <= x}. 

Definition Fbern (f: U -> (distr bool)) (p:U) := 
    Mif Flip 
       (if dec_demi p then (Munit false) else (f (p & p)))
       (if dec_demi p then (f (p + p)) else (Munit true)).

Lemma Fbern_mon : forall f g : U -> distr bool, 
 (forall n, le_distr (f n) (g n)) -> forall n, le_distr (Fbern f n) (Fbern g n).
unfold Fbern; intros.
apply Mif_mon; case (dec_demi n); auto.
Save.

Definition bernouilli : U -> (distr bool) := Mfix Fbern Fbern_mon.

(** ** Properties of the Bernouilli program *)

(** *** Definition of the invariant 
    $q(p)(n) = p - \frac{1}{2^n}$ *)

Definition q (p:U) (n:nat) :=  p - ([1/2]^n).

Add Morphism q : q_eq_compat.
unfold q; auto.
Save.

(** *** Properties of the invariant *)
Lemma q_esp_S : forall p n, q (p & p) n == q p (S n) & q p (S n).
unfold q at 1; intros.
setoid_rewrite (half_exp n).
setoid_rewrite (Uesp_minus_distr p p ([1/2]^(S n)) ([1/2]^(S n))); auto.
Save.

Lemma q_esp_le : forall p n,  (q p (S n)) <= [1/2] * (q (p & p) n) + [1/2].
intros; setoid_rewrite (q_esp_S p n); auto.
Save.

Lemma q_plus_eq :  forall p n, (p <= [1/2]) -> (q p (S n)) == [1/2] * (q (p + p) n).
intros; unfold q at 2.
setoid_rewrite (Uminus_distr_right [1/2] (p + p) ([1/2]^n)).
setoid_rewrite (half_twice H); auto.
Save.

Lemma q_0 : forall p:U, q p O == 0.
unfold q; simpl; auto.
Save.

Lemma p_le : forall (p:U) (n:nat), p - ([1/]1+n) <= q p n.
unfold q; intros.
apply Uminus_le_compat_right.
induction n; simpl; intros; auto.
apply Ule_trans with ([1/2] * ([1/]1+n)); auto.
Save.

Hint Resolve p_le.

Lemma lim_q_p : forall p, p <= lub (q p).
intro; apply Ule_lt_lim; intros.
assert (exists n : nat, t <= p - [1/]1+n).
apply Ult_le_nth; trivial.
case H0; intros n H1.
apply Ule_trans with (p - [1/]1+n); auto.
apply Ule_trans with (q p n); auto.
Save.

Hint Resolve lim_q_p.
    
(** *** Proof of main results *)

(** Property : $\forall p, \ok{p}{\mathrm{bernouilli}~p}{\mathbf{result}=\mathrm{true}}$ *)

Definition q1 (b:bool) := if b then 1 else 0.

Lemma bernouilli_true :   okfun (fun p => p) bernouilli q1.
unfold bernouilli; intros.
apply okfun_le_compat with (fun p => lub (q p)) q1; auto.
apply fixrule with (p:= fun p => (q p)); auto; intros.
apply q_0.
red; simpl; intros.
unfold Fbern.
red.
setoid_rewrite 
 (Mif_eq Flip 
   (if dec_demi x then Munit false else f (x & x))
   (if dec_demi x then f (x + x) else Munit true) q1); simpl.
case (dec_demi x); simpl; intros.
(* Case x < 1/2 *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ((q (x + x) i) * [1/2]).
assert (x<= [1/2]); auto.
setoid_rewrite (q_plus_eq i H0).
Usimpl; trivial.
Usimpl; apply H; auto.
(* Case 1/2 <= x *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ((q (x & x) i) * [1/2] + [1/2]).
apply Ule_trans with (1:=(q_esp_le x i)); auto.
repeat Usimpl; apply H; auto.
Save.

(** Property : $\forall p, \ok{1-p}{\mathrm{bernouilli}~p}{\mathbf{result}=\mathrm{false}} $ *)

Definition q2 (b:bool) := if b then 0 else 1.

Lemma bernouilli_false :  okfun (fun p => [1-] p) bernouilli q2.
unfold bernouilli; intros.
apply okfun_le_compat with (fun p => lub (q ([1-] p))) q2; auto.
apply fixrule with (p:= fun p => (q ([1-] p))); auto; intros.
apply q_0.
red; simpl; intros.
unfold Fbern.
red.
setoid_rewrite 
 (Mif_eq Flip 
   (if dec_demi x then Munit false else f (x & x))
   (if dec_demi x then f (x + x) else Munit true) q2); simpl.
case (dec_demi x); simpl; intros.
(* Case x < 1/2 *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ([1/2] + (q ([1-] (x + x)) i) * [1/2]).
apply Ule_trans with (1:=q_esp_le ([1-] x) i).
setoid_rewrite (Uinv_plus_esp x x).
repeat Usimpl; trivial.
repeat Usimpl; apply H; auto.
(* Case 1/2 <= x *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ((q ([1-] (x & x)) i) * [1/2]).
setoid_rewrite (Uinv_esp_plus x x).
assert ([1-] x <= [1/2]); auto.
setoid_rewrite (q_plus_eq i H0).
repeat Usimpl; trivial.
repeat Usimpl; apply H; auto.
Save.

(** Probability for the result of $(\mathrm{bernouilli}~p)$ to be true is exactly $p$ *)

Lemma q1_q2_inv : forall b:bool, q1 b == [1-] (q2 b).
intros; case b; simpl; auto.
Save.

Lemma bernouilli_eq :  forall p, mu (bernouilli p) q1 == p.
intros; apply Ule_antisym.
apply Ule_trans with (mu (bernouilli p) (fun b => [1-] (q2 b))).
apply (mu_monotonic (bernouilli p)).
repeat red; intros.
setoid_rewrite (q1_q2_inv x); auto.
apply Ule_trans with ([1-] (mu (bernouilli p) q2)).
exact (mu_stable_inv (bernouilli p) q2).
apply Uinv_le_perm_left.
apply (bernouilli_false p).
apply (bernouilli_true p).
Save.

End Bernouilli.
