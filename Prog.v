(** * Prog.v: Composition of distributions *)

Require Export Probas.
Set Implicit Arguments.

Module Rules (Univ:Universe).
Module PP := (Proba Univ).
(* begin hide *)
Import Univ.
Import PP.
Import PP.MP.
Import PP.MP.UP.
(* end hide *)
(** ** Conditional *)
Definition Mif (A:Type) (b:distr bool) (m1 m2: distr A) 
    := Mlet b (fun x:bool => if x then m1 else m2).

Lemma Mif_mon : forall (A:Type) (b b':distr bool) (m1 m2 m1' m2': distr A),
    le_distr b b' -> le_distr m1 m1' -> le_distr m2 m2'
    -> le_distr (Mif b m1 m2) (Mif b' m1' m2').
intros; unfold Mif; apply Mlet_mon; auto.
destruct x; auto.
Save. 

(** ** Fixpoints *)
Section Fixpoints.
(** *** Hypotheses *)
Variables A B : Type.

Variable F : (A -> (distr B)) -> A -> (distr B).

Hypothesis F_mon : forall f g : A -> (distr B), 
  (forall x, le_distr (f x) (g x)) -> forall x, (le_distr (F f x) (F g x)).

(** *** Iteration of the functional $F$ from the $0$-distribution *)
Fixpoint iter (n:nat) : A -> (distr B)
:= match n with | O => fun x => (distr_null B)
                | S n => fun x => F (iter n) x
   end.

Definition Flift (dn:A->nat->distr B)(x:A)(n:nat):(distr B):= F (fun x => dn x n) x.

Lemma Flift_mon : forall dn : A -> nat -> distr B,
(forall (x:A) (n m:nat), (n <= m)%nat ->le_distr (dn x n) (dn x m))
 -> forall (x:A) (n m:nat), (n <= m)%nat ->le_distr (Flift dn x n) (Flift dn x m).
unfold Flift; red; intros.
apply F_mon; auto.
Save.

Hypothesis F_continuous : forall (dn:A->nat->distr B)
  (dnmon : forall x n m,(n <= m)%nat ->le_distr (dn x n) (dn x m))
  (x:A),
  (le_distr (F (fun x => mu_lub (dn x) (dnmon x)) x) 
               (mu_lub (Flift dn x) (Flift_mon dn dnmon x))).

Let muf (x:A) (n:nat) := (iter n x).

Lemma muf_mon_succ :  forall (n:nat) (x:A), le_distr (muf x n) (muf x (S n)).
induction n; unfold muf, le_distr; simpl; intros.
auto.
apply F_mon; auto.
Save.

Lemma muf_mon :  forall (x:A) (n m:nat), (n <= m)%nat -> le_distr (muf x n) (muf x m).
induction 1; auto.
apply le_distr_trans with (muf x m); auto.
apply muf_mon_succ.
Save.

(** *** Definition *)
Definition Mfix (x:A) := mu_lub (fun n => iter n x) (muf_mon x).
(** *** Properties *)
Lemma Mfix_le_iter :  forall (x : A) (n:nat), le_distr (iter n x) (Mfix x).
red; intros; unfold Mfix.
apply mu_lub_le with (muf:=fun n0:nat => iter n0 x); trivial.
Save.
Hint Resolve Mfix_le_iter.

Lemma Mfix_le : forall x : A, le_distr (Mfix x) (F Mfix x).
unfold Mfix at 1; red; intros.
apply mu_lub_sup; trivial.
destruct n; simpl; auto.
Save.

Lemma Mfix_sup : forall x : A, le_distr (F Mfix x) (Mfix x).
unfold Mfix.
intro x.
pose (dn:=fun (x0:A) (n:nat) => iter n x0).
apply le_distr_trans with 
  (mu_lub (Flift dn x) (Flift_mon dn muf_mon x)).
apply F_continuous with 
 (dn:=fun (x0:A) (n:nat) => iter n x0) (dnmon:=muf_mon) (x:=x).
red; auto.
unfold Flift, dn.
intros; apply mu_lub_sup; intros.
apply le_distr_trans with (iter (S n) x); auto.
red; simpl; intros.
apply F_mon; auto.
apply mu_lub_le with (muf:=fun n0:nat => iter n0 x); auto.
Save.

Lemma Mfix_eq : forall x : A, eq_distr (Mfix x) (F Mfix x).
red; intros; apply Ule_antisym.
apply Mfix_le; trivial.
apply Mfix_sup; trivial.
Save.

End Fixpoints.

(** * Prog.v: An axiomatic semantics for randomized programs *)
(** ** Definition of correctness judgement 
 $\ok{p}{e}{q}$ is defined as $p \leq \mu(e)(q)$ *)

Definition ok (A:Type) (p:U) (e:distr A) (q:A->U) := p <= (mu e q).

Definition okfun (A B:Type)(p:A->U)(e:A->distr B)(q:B->U) 
  := forall x:A, (ok (p x) (e x) q).

(** ** Stability properties *)
Lemma ok_le_compat : forall (A:Type) (p p':U) (e:distr A) (q q':A->U),
    p' <= p -> fle q q' -> ok p e q -> ok p' e q'.
unfold ok; intros.
apply Ule_trans with p; auto.
apply Ule_trans with (mu e q); auto.
apply (mu_monotonic e); auto.
Save.

Lemma ok_eq_compat : forall (A:Type) (p p':U) (e e':distr A) (q q':A->U),
    p' == p ->  (feq q q') -> eq_distr e e' -> ok p e q -> ok p' e' q'.
unfold ok; intros.
apply Ule_trans with p; auto.
apply Ule_trans with (mu e q); auto.
apply Ule_trans with (mu e' q); auto.
apply (mu_monotonic e'); auto.
Save.

Lemma okfun_le_compat : forall (A B:Type) (p p':A -> U) (e:A -> distr B) (q q':B->U),
    fle p' p -> fle q q' -> okfun p e q -> okfun p' e q'.
unfold okfun; intros.
apply ok_le_compat with (p x) q; auto.
Save.

Lemma okfun_eq_compat : forall (A B:Type) (p p':U) (e e':distr A) (q q':A->U),
    p' == p ->  (feq q q') -> eq_distr e e' -> ok p e q -> ok p' e' q'.
unfold ok; intros.
apply Ule_trans with p; auto.
apply Ule_trans with (mu e q); auto.
apply Ule_trans with (mu e' q); auto.
apply (mu_monotonic e'); auto.
Save.

Lemma ok_mult : forall (A:Type)(k p:U)(e:distr A)(f : A -> U), ok p e f -> ok (k*p) e (fmult k f).
unfold ok; intros A k p e f oka.
rewrite (mu_stable_mult e k f).
apply Umult_le_compat_right; trivial.
Save.

Lemma ok_inv :   forall (A:Type)(p:U)(e:distr A)(f : A -> U), ok p e f -> (mu e (finv f)) <= [1-]p.
unfold ok; intros A p e f oka.
apply Ule_trans with ([1-](mu e f)); auto.
apply mu_stable_inv.
Save.

(** ** Basic rules *)
(** *** Rule for application 
 $\bfrac{\ok{r}{a}{p}~~~\forall x, \ok{p(x)}{f(x)}{q}}{\ok{r}{f(a)}{q}}$*)

Lemma apply_rule : forall (A B:Type)(a:(distr A))(f:A->distr B)(r:U)(p:A->U)(q:B->U),
 (ok r a p) -> (okfun p f q) -> (ok r (Mlet a f) q).
unfold ok,okfun,Mlet; simpl; intros. 
apply Ule_trans with (mu a p); auto.
unfold star.
apply mu_monotonic; red; auto.
Save.

(** *** Rule for abstraction *)
Lemma lambda_rule : forall (A B:Type)(f:A->distr B)(p:A->U)(q:B->U),
 (forall x:A, (ok (p x) (f x) q)) -> (okfun p f q).
trivial.
Save.

(** *** Rule for conditional
  $ \bfrac{\ok{p_1}{e_1}{q}~~~\ok{p_2}{e_2}{q}}
           {\ok{p_1\times \mu(e_1)(1_{true}) + p_2\times \mu(e_2)(1_{false})}
               {if~b~then~e_1~else~e_2}{q}}$
*)

Lemma ifok : forall f1 f2, fplusok (fmult f1 ctrue) (fmult f2 cfalse).
unfold fplusok, fmult, ctrue, cfalse, fle, finv; intros.
case x.
setoid_rewrite (Umult_zero_right f2); auto.
setoid_rewrite (Umult_zero_right f1); auto.
Save.
Hint Resolve ifok.

Lemma Mif_eq : forall (A:Type)(b:(distr bool))(f1 f2:distr A)(q:A->U),
	(mu (Mif b f1 f2) q) == (mu f1 q) * (mu b ctrue) + (mu f2 q) * (mu b cfalse).
intros.
apply Ueq_trans with (mu b (fplus (fmult (mu f1 q) ctrue) (fmult (mu f2 q) cfalse))).
intros; unfold Mif,Mlet,star; simpl.
apply (mu_stable_eq b); red; intro.
unfold fplus,fmult;destruct x; simpl.
setoid_rewrite (Umult_one_right (mu f1 q)); 
setoid_rewrite (Umult_zero_right (mu f2 q)); 
auto.
setoid_rewrite (Umult_zero_right (mu f1 q)); 
setoid_rewrite (Umult_one_right (mu f2 q)); 
auto.
setoid_rewrite (mu_stable_plus b (f:=(fmult (mu f1 q) ctrue))
                                (g:=(fmult (mu f2 q) cfalse))
                (ifok (mu f1 q) (mu f2 q))).
setoid_rewrite (mu_stable_mult b (mu f1 q) ctrue).
setoid_rewrite (mu_stable_mult b (mu f2 q) cfalse); trivial.
Save.

Lemma ifrule : 
  forall (A:Type)(b:(distr bool))(f1 f2:distr A)(p1 p2:U)(q:A->U),
       (ok p1 f1 q)->(ok p2 f2 q)
       ->(ok ((p1 * (mu b ctrue)) + (p2 * (mu b cfalse))) (Mif b f1 f2) q).
unfold ok; intros.
setoid_rewrite (Mif_eq b f1 f2 q).
apply Uplus_le_compat.
apply Umult_le_compat_left; auto.
apply Umult_le_compat_left; auto.
Save.

(** *** Properties of [Flip] *)
Lemma Flip_ctrue : mu Flip ctrue == [1/2].
unfold Flip; auto.
Save.

Lemma Flip_cfalse : mu Flip cfalse == [1/2].
unfold Flip; auto.
Save.

(** *** Rule for fixpoints 
with $\phi(x)=F(\phi)(x)$, $p_i$ an increasing sequence of functions starting from $0$

$\bfrac{\forall f~i, (\forall x, \ok{p_i(x)}{f}{q}) \Ra \forall x, \ok{p_{i+1}(x)}{F(f)(x)}{q}}%
     {\forall x, \ok{\bigcup_i p_i~x}{\phi(x)}{q}}$
*)
Section Fixrule.
Variables A B : Type.

Variable F : (A -> (distr B)) -> A -> distr B.

Hypothesis F_mon : forall f g : A -> (distr B), 
  (forall x, le_distr (f x) (g x)) -> forall x, le_distr (F f x) (F g x).

Variable p : A -> nat -> U.
Hypothesis pmon : forall x:A, mon_seq Ule (p x).
Hypothesis p0 : forall x:A, p x O == 0.
Variable q : B -> U.
Lemma fixrule : 
   (forall (i:nat) (f:A->(distr B)), 
           (okfun (fun x => (p x i)) f q)
           -> okfun (fun x => (p x (S i)))  (fun x => F f x) q)
           -> okfun (fun x => lub (p x)) (Mfix F F_mon) q.
red; intros.
assert (forall n:nat, 
        (okfun (fun x => (p x n)) 
        (fun x => (iter F n x)) q)).
induction n; simpl; auto.
repeat red; intros; auto.
red; intros.
apply lub_le; auto.
intro n; apply Ule_trans with (mu (iter F n x) q).
apply (H0 n).
apply Mfix_le_iter; auto.
Save.

End Fixrule.

(** *** Rule for [flip] *)
Lemma ok_flip :   forall q : bool -> U, ok ([1/2] * q true + [1/2] * q false) Flip q.
red; unfold Flip, flip; simpl; auto.
Save.

End Rules.
