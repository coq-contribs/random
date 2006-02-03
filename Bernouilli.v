(** * Bernouilli.v: Simulating Bernouilli distribution *)
Require Export Prog.
Require Export Prelude.
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

Definition qtrue (b:bool) := if b then 1 else 0.
Definition qfalse (b:bool) := if b then 0 else 1.

Lemma bernouilli_true :   okfun (fun p => p) bernouilli qtrue.
unfold bernouilli; intros.
apply okfun_le_compat with (fun p => lub (q p)) qtrue; auto.
apply fixrule with (p:= fun p => (q p)); auto; intros.
apply q_0.
red; simpl; intros.
unfold Fbern.
red.
setoid_rewrite 
 (Mif_eq Flip 
   (if dec_demi x then Munit false else f (x & x))
   (if dec_demi x then f (x + x) else Munit true) qtrue); simpl.
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

Lemma bernouilli_false :  okfun (fun p => [1-] p) bernouilli qfalse.
unfold bernouilli; intros.
apply okfun_le_compat with (fun p => lub (q ([1-] p))) qfalse; auto.
apply fixrule with (p:= fun p => (q ([1-] p))); auto; intros.
apply q_0.
red; simpl; intros.
unfold Fbern.
red.
setoid_rewrite 
 (Mif_eq Flip 
   (if dec_demi x then Munit false else f (x & x))
   (if dec_demi x then f (x + x) else Munit true) qfalse); simpl.
case (dec_demi x); simpl; intros.
(* Case x < 1/2 *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ([1/2] + (q ([1-] (x + x)) i) * [1/2]).
apply Ule_trans with (1:=q_esp_le ([1-] x) i).
setoid_rewrite (Uinv_plus_esp x x).
Usimpl; auto.
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

Lemma qtrue_qfalse_inv : forall b:bool, qtrue b == [1-] (qfalse b).
intros; case b; simpl; auto.
Save.

Lemma bernouilli_eq_true :  forall p, mu (bernouilli p) qtrue == p.
intros; apply Ule_antisym.
apply Ule_trans with (mu (bernouilli p) (fun b => [1-] (qfalse b))).
apply (mu_monotonic (bernouilli p)).
repeat red; intros.
setoid_rewrite (qtrue_qfalse_inv x); auto.
apply Ule_trans with ([1-] (mu (bernouilli p) qfalse)).
exact (mu_stable_inv (bernouilli p) qfalse).
apply Uinv_le_perm_left.
apply (bernouilli_false p).
apply (bernouilli_true p).
Save.

Lemma bernouilli_eq_false :  forall p, mu (bernouilli p) qfalse == [1-]p.
intros; apply Ule_antisym.
apply Ule_trans with (mu (bernouilli p) (fun b => [1-] (qtrue b))).
apply (mu_monotonic (bernouilli p)).
repeat red; intros.
setoid_rewrite (qtrue_qfalse_inv x); auto.
apply Ule_trans with ([1-] (mu (bernouilli p) qtrue)).
exact (mu_stable_inv (bernouilli p) qtrue).
apply Uinv_le_perm_left; Usimpl.
apply (bernouilli_true p).
apply (bernouilli_false p).
Save.

Lemma bernouilli_eq :  forall p f, mu (bernouilli p) f == p * f true + ([1-]p) * f false.
intros; apply Ueq_trans with (mu (bernouilli p) (fun b => f true * qtrue b + f false * qfalse b)).
apply mu_stable_eq.
unfold feq,qtrue,qfalse.
destruct x; repeat Usimpl; auto.
rewrite (mu_stable_plus (bernouilli p) (f:=fun b => f true * qtrue b) (g:=fun b => f false * qfalse b)).
repeat red; unfold fle,finv,qtrue,qfalse; destruct x; repeat Usimpl; auto.
rewrite (mu_stable_mult (bernouilli p) (f true) qtrue).
rewrite (mu_stable_mult (bernouilli p) (f false) qfalse).
rewrite bernouilli_eq_true; rewrite bernouilli_eq_false.
apply Uplus_eq_compat; auto.
Save.

Lemma bernouilli_total : forall p , mu (bernouilli p) (f_one bool)==1.
intros; rewrite bernouilli_eq; unfold f_one; repeat Usimpl; auto.
Save.

(** * Binomial distribution :
         (binomial~p~n)  gives k with probability $C_k^n p^k(1-p)^{n-k}$ *)

Fixpoint comb (k n:nat) {struct n} : nat := 
         match n with O => match k with O => (1%nat) | (S l) => O end
                | (S m) => match k with O => (1%nat)
                                                    | (S l) => ((comb l m) + (comb k m))%nat end
         end.

Lemma comb_0_n : forall n, comb 0 n = (1%nat).
destruct n; trivial.
Save.

Lemma comb_not_le : forall n k, (le (S n) k) -> (comb k n)=0%nat.
induction n; destruct k; simpl; auto with zarith; intros.
rewrite (IHn k); auto with zarith.
rewrite (IHn (S k)); auto with zarith.
Save.

Lemma comb_Sn_n : forall n, (comb (S n) n)=0%nat.
intro; apply comb_not_le; auto.
Save.

Lemma comb_n_n : forall n, comb n n = (1%nat).
induction n; simpl; auto.
rewrite comb_Sn_n; auto with zarith.
Save.

Lemma comb_1_Sn : forall n, comb 1 (S n) = (S n).
induction n; auto.
replace (comb 1 (S (S n))) with (((comb 0 (S n))+(comb 1 (S n)))%nat); auto.
rewrite comb_0_n; omega.
Save.

Lemma comb_inv : forall n k, (k<=n)%nat -> comb k n = comb (n-k) n.
induction n; destruct k; simpl; auto with zarith; intros.
rewrite comb_Sn_n; rewrite comb_n_n; auto.
assert (Hle : (k<=n)%nat); auto with zarith.
case (le_lt_or_eq k n Hle); intros.
assert (Heq:(n-k)%nat=(S (n-(S k)))); auto with zarith.
pattern ((n-k)%nat) at 1; rewrite Heq.
rewrite (IHn (S k)); auto.
rewrite (IHn k); auto with zarith.
subst.
rewrite comb_Sn_n; rewrite comb_n_n; rewrite <- minus_n_n; trivial.
Save.

Lemma comb_n_Sn : forall n, comb n (S n) = (S n).
intros; transitivity (comb (S n - n) (S n)).
apply comb_inv; auto.
rewrite <- minus_Sn_m; auto.
rewrite <- minus_n_n.
apply comb_1_Sn.
Save.

Definition fc (p:U)(n k:nat) :=  (comb k n) */ (p^k * ([1-]p)^(n-k)).

Lemma fcp_0 : forall p n, fc p n O == ([1-]p)^n.
intros; unfold fc; rewrite comb_0_n; repeat Usimpl.
rewrite <- minus_n_O; auto.
Save.

Lemma fcp_n : forall p n, fc p n n == p^n.
intros; unfold fc; rewrite comb_n_n; repeat Usimpl.
rewrite <- minus_n_n; auto.
Save.

Lemma fcp_not_le : forall p n k, (S n <= k)%nat -> fc p n k == 0.
unfold fc; intros; rewrite comb_not_le; auto.
Save.

Lemma fc0 : forall n k, fc 0 n (S k) == 0.
intros; unfold fc; repeat Usimpl; auto.
Save.
Hint Resolve fc0.

Add Morphism fc : fc_eq_compat.
unfold fc; intros; rewrite H; auto.
Save.

Hint Resolve fc_eq_compat.

Lemma sigma_fc0 : forall n k,  sigma (fc 0 n) (S k) ==1.
intros; rewrite sigma_S_lift.
rewrite fcp_0; rewrite sigma_zero; repeat Usimpl; auto.
Save.
 
Lemma retract_class : forall f n, class (retract f n).
unfold retract; red; intros.
apply Ule_class; red; intros.
apply H; intro; auto.
Save.
Hint Resolve retract_class.

Lemma fc_retract : 
     forall p n, ([1-]p^n == sigma (fc p n) n) -> retract (fc p n) (S n).
intros; apply (Ueq_orc p 0); intros; auto.
red; intros.
destruct k; simpl.
rewrite sigma_0; repeat Usimpl; auto.
apply Ule_trans with 0; auto.
rewrite H0; auto.
apply retractS_intro; auto.
apply retract_lt.
apply Ule_lt_trans with ([1-]p^n); auto.
apply Ule_trans with (p^n); auto.
rewrite fcp_n; auto.
Save.
Hint Resolve fc_retract.

Lemma fc_Nmult_def : 
     forall p n k, ([1-]p^n == sigma (fc p n) n) -> Nmult_def (comb k n) (p^k * ([1-]p) ^(n-k)).
intros p n k Heq; destruct k.
rewrite comb_0_n; auto.
apply (Ueq_orc p 0); intros; auto.
(* case p == 0 *)
rewrite H; repeat Usimpl; auto.
(* case p <> 0 *)
assert (Hk:(S k < n \/n=S k\/ n < S k)%nat); try omega.
decompose sum Hk; clear Hk; intros.
(* S k < n *)
apply Nmult_def_lt.
apply Ule_lt_trans with (sigma (fc p n) n).
apply sigma_le with (k:=S k) (f:=fc p n); auto.
apply Ule_lt_trans with ([1-](p^n)); auto.
(* n=S k *)
subst.
rewrite comb_n_n; auto.
rewrite comb_not_le; auto with arith.
Save.
Hint Resolve fc_Nmult_def.

Lemma fcp_S : 
    forall p n k, ([1-]p^n == sigma (fc p n) n) -> fc p (S n) (S k) == p * (fc p n k) + ([1-]p) * (fc p n (S k)).
intros;
assert (Hcase : (k<n \/ n=k \/ (S n)<=k)%nat); try omega. 
decompose sum Hcase.
unfold fc; simpl.
rewrite plus_Nmult_distr.
rewrite <- Umult_assoc.
rewrite Nmult_Umult_assoc_right; auto.
repeat Usimpl.
rewrite <- Nmult_Umult_assoc_right; auto.
exact (fc_Nmult_def p n (S k) H).
apply Nmult_eq_compat.
repeat rewrite  Umult_assoc.
rewrite (Umult_sym ([1-]p) p).
rewrite <-  (Umult_assoc p ([1-]p)).
rewrite (Umult_sym ([1-]p) (p^k)); auto.
repeat rewrite  <- Umult_assoc; auto.
replace (n-k)%nat with (S (n-S k)); auto; omega.
subst; repeat rewrite fcp_n.
rewrite fcp_not_le; repeat Usimpl; auto.
repeat (rewrite fcp_not_le; auto with arith).
repeat Usimpl; auto.
Save.

Lemma sigma_fc_1 : forall p n, ([1-]p^n == sigma (fc p n) n) ->1==sigma (fc p n) (S n).
intros; rewrite sigma_S.
rewrite <- H; rewrite fcp_n; auto.
Save.
Hint Resolve sigma_fc_1.

Lemma Uinv_exp : forall p n,  [1-](p^n)==sigma (fc p n) n.
induction n; auto.
(* case S n *)
apply (Ueq_orc p 0); intros; auto.
(* case p == 0 *)
rewrite sigma_S_lift.
rewrite fcp_0; rewrite sigma_zero; intros;
rewrite H; repeat Usimpl; auto.
(* case p <> 0 *)
assert (Hr:retract (fc p n) (S n)); auto.
(* main property *)
rewrite sigma_S_lift.
rewrite fcp_0.
apply Ueq_trans with (([1-] p) ^ S n + sigma (fun k : nat => p * fc p n k + ([1-]p) * fc p n (S k)) n).
rewrite (sigma_plus (fun k => p * fc p n k) (fun k => [1-] p * fc p n (S k))).
rewrite sigma_mult; auto.
rewrite <-IHn.
apply Ueq_trans with (p * [1-] p ^ n + (([1-] p) ^ S n + sigma (fun k : nat => [1-] p * fc p n (S k)) n));auto.
apply Ueq_trans with (p * [1-] p ^ n + (sigma (fun k : nat => [1-] p * fc p n k) (S n))).
rewrite sigma_mult; auto.
rewrite <- sigma_fc_1;auto; repeat Usimpl;apply Uexp_inv_S.
rewrite sigma_S_lift; repeat Usimpl; rewrite fcp_0; auto.
repeat Usimpl.
apply sigma_eq_compat; intros.
apply Ueq_sym; apply fcp_S; auto.
Save.

Hint Resolve Uinv_exp.

Lemma Nmult_comb : forall p n k, Nmult_def (comb k n) (p ^ k * ([1-] p) ^ (n - k)).
auto.
Save.
Hint Resolve Nmult_comb.

Definition qk (k n:nat) : U := if eq_nat_dec k n then 1 else 0.

Fixpoint binomial (p:U)(n:nat) {struct n}: (distr nat) := 
    match n with O => (Munit O)
                     | S m => Mlet (binomial p m) 
                                     (fun x => Mif (bernouilli p) (Munit (S x)) (Munit x))
    end.

Lemma binomial_eq_k : 
   forall p n k, mu (binomial p n) (qk k) == fc p n k.
induction n; intros.
(* case n = 0 *)
simpl; destruct k; unfold unit,qk; auto.
rewrite fcp_0; auto.
(* cas n<>0 *)
simpl binomial.
simpl mu.
apply Ueq_trans with 
(star (mu (binomial p n))
  (fun x : nat =>
   star (mu (bernouilli p))
     (fun x0 : bool => mu (if x0 then Munit (S x) else Munit x))) (qk k));
auto.
unfold star.
apply Ueq_trans with 
 (mu (binomial p n)
  (fun x : nat => p * (qk k (S x)) + ([1-]p) * (qk k x))).
apply mu_stable_eq; red; intros.
rewrite bernouilli_eq; unfold Munit; simpl; auto.
destruct k.
(* case k = 0 *)
apply Ueq_trans with (mu (binomial p n) (fun x => [1-] p * qk 0 x)).
apply mu_stable_eq; red; unfold qk at 1; intros.
rewrite if_else; auto; repeat Usimpl; auto.
rewrite (mu_stable_mult (binomial p n) ([1-]p) (qk 0)).
rewrite IHn; simpl; repeat Usimpl; auto.
repeat rewrite fcp_0; auto.
(* Case S k *)
apply Ueq_trans with  (mu (binomial p n) (fun x : nat => p * qk k x + [1-] p * qk (S k) x)).
apply mu_stable_eq; red; intro; repeat Usimpl.
unfold qk; intros.
case (eq_nat_dec k x); intro.
rewrite if_then; auto.
rewrite if_else; auto.
rewrite (mu_stable_plus (binomial p n) (f:=fun x : nat => p * qk k x) (g:=fun x : nat => [1-] p * qk (S k) x)).
(* fplusok *)
repeat red; unfold finv,qk; intros.
case (eq_nat_dec k x); intro; auto.
(* *)
rewrite (mu_stable_mult (binomial p n) p (qk k)).
rewrite (mu_stable_mult (binomial p n) ([1-]p) (qk (S k))).
rewrite IHn.
rewrite IHn.
rewrite fcp_S; auto.
Save.

End Bernouilli.
