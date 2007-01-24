(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(** * Uprop.v : Properties of operators on [[0,1]] *)
Set Implicit Arguments.
Require Export Ubase.
Require Export Arith.
Require Export Omega.
Module Univ_prop (Univ:Universe).
Import Univ.

Hint Resolve Ueq_refl.
Hint Resolve Upos Unit Udiff_0_1 Unth_prop Ueq_le.
Hint Resolve Uplus_sym Uplus_assoc Umult_sym Umult_assoc.
Hint Resolve Uinv_one Uinv_opp_left Uinv_plus_left.
Hint Resolve Uplus_zero_left Umult_one_left Udistr_plus_right Udistr_inv_right.
Hint Resolve Uplus_le_compat_left Umult_le_compat_left Uinv_le_compat.
Hint Resolve lub_le le_lub lub_eq_mult lub_eq_plus_cte_right.
Hint Resolve Ule_total Ule_class.
Hint Immediate Ueq_sym Ule_antisym.
Open Scope nat_scope.
Open Scope U_scope.

(** ** Direct consequences of axioms  *)

Lemma Ueq_class : forall x y, class (x==y).
red; intros.
apply Ule_antisym;
apply Ule_class; intuition.
Save.

Lemma Ueq_double_neg : forall x y : U, ~ ~x == y -> x == y.
exact Ueq_class.
Save.
Hint Resolve Ueq_class.
Hint Immediate Ueq_double_neg.

Lemma Ule_orc : forall x y, orc (x<=y) (~ x<=y).
auto.
Save.
Implicit Arguments Ule_orc [].

Lemma Ueq_orc : forall x y, orc (x==y) (~ x==y).
auto.
Save.
Implicit Arguments Ueq_orc [].

Lemma Ule_0_1 : 0 <= 1.
auto.
Save.

Lemma Ule_refl : forall x:U,x <= x.
auto.
Save.
Hint Resolve Ule_refl.

(** ** Properties of == derived from properties of $\le$ *)

Lemma Ueq_trans : forall x y z:U, x == y -> y == z -> x == z.
intros; apply Ule_antisym; apply Ule_trans with y; auto.
Save.
Hint Resolve Ueq_trans.

Lemma Uplus_eq_compat_left : forall x y z:U, x == y -> (x + z) == (y + z).
intros; apply Ule_antisym; auto.
Save.

Hint Resolve Uplus_eq_compat_left.

Lemma Uplus_eq_compat_right : forall x y z:U, x == y -> (z + x) == (z + y).
intros; apply Ueq_trans with (x + z); auto.
apply Ueq_trans with (y + z); auto.
Save.

Lemma Umult_eq_compat_left : forall x y z:U, x == y -> (x * z) == (y * z).
intros;  apply Ule_antisym; auto.
Save.
Hint Resolve Umult_eq_compat_left.

Lemma Umult_eq_compat_right :  forall x y z:U, x == y -> (z * x) == (z * y).
intros; apply Ueq_trans with (x * z); auto.
apply Ueq_trans with (y * z); auto.
Save.

Hint Resolve Uplus_eq_compat_right Umult_eq_compat_right.

Lemma Uinv_opp_right : forall x, x + [1-] x == 1.
intros; apply Ueq_trans with ([1-] x + x); auto.
Save.
Hint Resolve Uinv_opp_right.

(** ** [U] is a setoid *)

Lemma Usetoid : Setoid_Theory U Ueq.
split; auto.
exact Ueq_trans.
Qed.

Add Setoid U Ueq Usetoid as U_setoid.

Add Morphism Uplus : Uplus_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Ueq_trans with (x1+x4); auto.
Qed.

Add Morphism Umult : Umult_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Ueq_trans with (x1 * x4); auto.
Qed.

Add Morphism Uinv : Uinv_eq_compat.
intros; apply Ule_antisym; auto.
Qed.

Add Morphism Ule : Ule_eq_compat_iff.
intros x1 x2 eq1 x3 x4 eq2; split; intro Hle.
apply Ule_trans with x1; auto.
apply Ule_trans with x3; auto.
apply Ule_trans with x2; auto.
apply Ule_trans with x4; auto.
Save.

Lemma Ule_eq_compat : 
forall x1 x2 : U, x1 == x2 -> forall x3 x4 : U, x3 == x4 -> x1 <= x3 -> x2 <= x4.
intros x1 x2 eq1 x3 x4 eq2; elim (Ule_eq_compat_iff eq1 eq2); auto.
Save.

(** ** Definition and properties of $x<y$ *)
Definition Ult (r1 r2:U) : Prop := ~ (r2 <= r1).

Infix "<" := Ult : U_scope.

Hint Unfold Ult.


Add Morphism Ult : Ult_eq_compat_iff.
unfold Ult, not; intros x1 x2 eq1 x3 x4 eq2.
generalize (Ule_eq_compat_iff eq2 eq1); intuition.
Save.

Lemma Ult_eq_compat : 
forall x1 x2 : U, x1 == x2 -> forall x3 x4 : U, x3 == x4 -> x1 < x3 -> x2 < x4.
intros x1 x2 eq1 x3 x4 eq2; elim (Ult_eq_compat_iff eq1 eq2); auto.
Save.

Lemma Ult_class : forall x y, class (x<y).
unfold Ult; auto.
Save.
Hint Resolve Ult_class.

(* begin hide *)
(** Tactic for left normal form with respect to associativity *)
Ltac norm_assoc_left := 
     match goal with 
      | |- context [(Uplus ?X1 (Uplus ?X2 ?X3))] 
        => (setoid_rewrite (Uplus_assoc X1 X2 X3))
     end.

Ltac norm_assoc_right := 
     match goal with 
      | |- context [(Uplus (Uplus ?X1 ?X2) ?X3)] 
        => (setoid_rewrite <- (Uplus_assoc X1 X2 X3))
     end.
(* end hide *)

(** *** Properties of $x \leq y$ *)

Lemma Ule_zero_eq :  forall x, x <= 0 -> x == 0.
intros; apply Ule_antisym; auto.
Save.

Lemma Uge_one_eq : forall x, 1 <= x -> x == 1.
intros; apply Ule_antisym; auto.
Save.

Hint Immediate Ule_zero_eq Uge_one_eq.

(** *** Properties of $x < y$ *)

Lemma Ult_neq : forall x y:U, x < y -> ~x == y.
unfold Ult; red; auto.
Save.

Lemma Ult_neq_rev : forall x y:U, x < y -> ~y == x.
unfold Ult; red; auto.
Save.

Lemma Ult_trans : forall x y z, x<y -> y<z -> x <z.
repeat red; intros.
apply (Ule_total y z); intros; auto.
apply H; apply Ule_trans with z; auto.
Save.

Lemma Ult_le : forall x y:U, x < y -> x <= y.
unfold Ult; intros; apply Ule_class; repeat red; intros.
assert (x < x).
apply Ult_trans with y; auto.
apply H1; auto. 
Save.

Lemma Ule_diff_lt : forall x y : U,  x <= y -> ~x==y -> x < y.
red; intuition.
Save.

Hint Immediate Ult_neq Ult_neq_rev Ult_le.
Hint Resolve Ule_diff_lt.

Lemma Ult_neq_zero : forall x, ~0 == x -> 0 < x.
auto.
Save.

Hint Resolve Ule_total Ult_neq_zero.

(** ** Properties of $+$ and $\times$  *)

Lemma Udistr_plus_left :  forall x y z, y <= [1-] z -> (x * (y + z)) == (x * y + x * z).
intros.
setoid_rewrite (Umult_sym x (y+z)); setoid_rewrite (Umult_sym x y); 
setoid_rewrite (Umult_sym x z);auto.
Save.

Lemma Udistr_inv_left :  forall x y, [1-](x * y) == (x * ([1-] y)) + [1-] x.
intros.
setoid_rewrite (Umult_sym x y).
setoid_rewrite (Udistr_inv_right y x); auto.
Save.

Hint Resolve Uinv_eq_compat Udistr_plus_left Udistr_inv_left.

Lemma Uplus_perm2 : forall x y z:U, x + (y + z) == y + (x + z).
intros; setoid_rewrite (Uplus_assoc x y z).
setoid_rewrite (Uplus_sym x y); auto.
Save.

Lemma Umult_perm2 : forall x y z:U, x * (y * z) == y * (x * z).
intros; setoid_rewrite (Umult_assoc x y z).
setoid_rewrite (Umult_sym x y); auto.
Save.

Lemma Uplus_perm3 : forall x y z : U, (x + (y + z)) == z + (x + y).
intros; setoid_rewrite (Uplus_assoc x y z); auto.
Save.

Lemma Umult_perm3 : forall x y z : U, (x * (y * z)) == z * (x * y).
intros; setoid_rewrite (Umult_assoc x y z); auto.
Save.

Hint Resolve Uplus_perm2 Umult_perm2 Uplus_perm3 Umult_perm3.

Lemma Uplus_le_compat_right : forall x y z:U, (x <= y) -> (z + x <= z + y).
intros; setoid_rewrite (Uplus_sym z x);
setoid_rewrite (Uplus_sym z y);auto.
Save.

Hint Resolve Uplus_le_compat_right.

Lemma Uplus_le_compat : forall x y z t:U, x <= y -> z <= t -> (x + z <= y + t).
intros; apply Ule_trans with (y + z); auto.
Save.
Hint Immediate Uplus_le_compat.

Lemma Uplus_zero_right : forall x:U, x + 0 == x.
intros; setoid_rewrite (Uplus_sym x 0); auto.
Save.
Hint Resolve Uplus_zero_right.

(* ** Properties of [1-] *)

Lemma Uinv_zero : [1-] 0 == 1.
apply Ueq_trans with (([1-] (0 + 0))+0); auto.
apply Ueq_trans with ([1-] (0 + 0)); auto.
setoid_rewrite (Uplus_zero_right 0); auto.
Save.
Hint Resolve Uinv_zero.


Lemma Uinv_inv : forall x : U, [1-] [1-] x == x.
intros; apply Ueq_trans with ([1-] (x + [1-] x) + x); auto.
apply Ueq_sym; auto.
setoid_rewrite (Uinv_opp_right x); setoid_rewrite Uinv_one; auto.
Save.
Hint Resolve Uinv_inv.

Lemma Uinv_simpl :  forall x y : U, [1-] x == [1-] y -> x == y.
intros; setoid_rewrite <- (Uinv_inv x); 
 setoid_rewrite <- (Uinv_inv y); auto.
Save.

Hint Immediate Uinv_simpl.

(** ** More properties on [+] and [*]  and [Uinv] *)

Lemma Umult_le_compat_right :  forall x y z: U,  x <= y -> (z * x) <= (z * y).
intros; setoid_rewrite (Umult_sym z x); setoid_rewrite (Umult_sym z y).
apply Umult_le_compat_left; trivial.
Save.

Hint Resolve Umult_le_compat_right.

Lemma Umult_one_right : forall x:U, (x * 1) == x.
intros; setoid_rewrite (Umult_sym x 1); auto.
Save.
Hint Resolve Umult_one_right.


Lemma Udistr_plus_left_le :  forall x y z : U, x * (y + z) <= x * y + x * z.
intros; apply (Ule_total y ([1-]z)); intros; auto.
setoid_replace (y+z) with ([1-]z+z); auto.
rewrite Udistr_plus_left; auto.
apply Ule_antisym; auto.
rewrite Uinv_opp_left; auto.
Save.

Lemma Uplus_eq_simpl_right : 
forall x y z:U, z <= [1-] x -> z <= [1-] y -> (x + z) == (y + z) -> x == y.
intros; apply Ule_antisym.
apply Uplus_le_simpl_right with z; auto.
apply Uplus_le_simpl_right with z; auto.
Save.

Lemma Ule_plus_right : forall x y, x <= x + y.
intros; apply Ule_eq_compat with (x + 0) (x + y); auto.
Save.

Lemma Ule_plus_left : forall x y, y <= x + y.
intros; apply Ule_eq_compat with (0 + y) (x + y); auto.
Save.
Hint Resolve Ule_plus_right Ule_plus_left.

Lemma Ule_mult_right : forall x y, x * y <= x .
intros; apply Ule_eq_compat with (x * y) (x * 1); auto.
Save.

Lemma Ule_mult_left : forall x y, x * y <= y.
intros; apply Ule_eq_compat with (x * y) (1 * y); auto.
Save.
Hint Resolve Ule_mult_right Ule_mult_left.

Lemma Uinv_le_perm_right : forall x y:U, x <= [1-] y -> y <= [1-] x.
intros; apply Ule_trans with ([1-] ([1-] y)); auto.
Save.
Hint Resolve Uinv_le_perm_right.

Lemma Uinv_le_perm_left :  forall x y:U, [1-] x <= y -> [1-] y <= x.
intros; apply Ule_trans with ([1-] ([1-] x)); auto.
Save.
Hint Resolve Uinv_le_perm_left.

Lemma Uinv_eq_perm_left :  forall x y:U, x == [1-] y -> [1-] x == y.
intros; apply Ueq_trans with ([1-] ([1-] y)); auto.
Save.
Hint Immediate Uinv_eq_perm_left.

Lemma Uinv_eq_perm_right :  forall x y:U, [1-] x == y ->  x == [1-] y.
intros; apply Ueq_trans with ([1-] ([1-] x)); auto.
Save.

Hint Immediate Uinv_eq_perm_right.

Lemma Uinv_plus_right : forall x y, y <= [1-] x -> [1-] (x + y) + y == [1-] x.
intros; setoid_rewrite (Uplus_sym x y); auto.
Save.
Hint Resolve Uinv_plus_right.

Lemma Uplus_eq_simpl_left : 
forall x y z:U, x <= [1-] y -> x <= [1-] z -> (x + y) == (x + z) -> y == z.
intros x y z H1 H2; setoid_rewrite (Uplus_sym x y); setoid_rewrite (Uplus_sym x z); auto.
intros; apply Uplus_eq_simpl_right with x; auto.
Save.

Lemma Uplus_eq_zero_left : forall x y:U, x <= [1-] y -> (x + y) == y -> x == 0.
intros; apply Uplus_eq_simpl_right with y; auto.
setoid_rewrite H0; auto.
Save.

Lemma Uinv_le_trans : forall x y z t, x <= [1-] y -> z<=x -> t<=y -> z<=[1-] t.
intros; apply Ule_trans with x; auto.
apply Ule_trans with ([1-] y); auto.
Save.

(** ** Disequality *)

Lemma neq_sym : forall x y, ~x==y -> ~y==x.
red; intros; apply H; auto.
Save.
Hint Immediate neq_sym.

Lemma Uinv_neq_compat : forall x y, ~x == y -> ~ [1-] x == [1-] y.
red; intros; apply H; auto.
Save.

Lemma Uinv_neq_simpl : forall x y, ~ [1-] x == [1-] y-> ~x == y.
red; intros; apply H; auto.
Save.

Hint Resolve Uinv_neq_compat.
Hint Immediate Uinv_neq_simpl.

Lemma Uinv_neq_left : forall x y, ~x == [1-] y -> ~ [1-] x == y.
red; intros; apply H; auto.
Save.

Lemma Uinv_neq_right : forall x y, ~ [1-] x == y -> ~x == [1-] y.
red; intros; apply H; auto.
Save.

(** *** Properties of [<]  *)

Lemma Ult_antirefl : forall x:U, ~x < x.
unfold Ult; intuition.
Save.

Lemma Ult_0_1 : (0 < 1).
red; intuition.
Save.

Lemma Ule_lt_trans : forall x y z:U, x <= y -> y < z -> x < z.
unfold Ult; intuition.
apply H0; apply Ule_trans with x; trivial.
Save.

Lemma Ult_le_trans : forall x y z:U, x < y -> y <= z -> x < z.
unfold Ult; intuition.
apply H; apply Ule_trans with z; trivial.
Save.

Hint Resolve Ult_0_1 Ult_antirefl.


Lemma Uplus_neq_zero_left : forall x y, ~0 == x -> ~0 == x+y.
intros; apply Ult_neq.
apply Ult_le_trans with x; auto.
Save.

Lemma Uplus_neq_zero_right : forall x y, ~0 == y -> ~0 == x+y.
intros; apply Ult_neq.
apply Ult_le_trans with y; auto.
Save.

Lemma not_Ult_le : forall x y, ~x < y -> y <= x.
intros; apply Ule_class; auto.
Save.

Lemma Ule_not_lt : forall x y, x <= y -> ~y < x.
repeat red; intros.
apply H0; auto.
Save.

Hint Immediate not_Ult_le Ule_not_lt.

Theorem Uplus_le_simpl_left : forall x y z : U, z <= [1-] x -> z + x <= z + y -> x <= y.
intros.
apply Uplus_le_simpl_right with z; auto.
apply Ule_trans with (z + x); auto.
apply Ule_trans with (z + y); auto.
Save.


Lemma Uplus_lt_compat_left : forall x y z:U, z <= [1-] y -> x < y -> (x + z) < (y + z).
unfold Ult; intuition.
apply H0; apply Uplus_le_simpl_right with z; trivial.
Save.


Lemma Uplus_lt_compat_right : forall x y z:U, z <= [1-] y -> x < y -> (z + x) < (z + y).
intros; setoid_rewrite (Uplus_sym z x).
intros; setoid_rewrite (Uplus_sym z y).
apply Uplus_lt_compat_left; auto.
Save.

Hint Resolve Uplus_lt_compat_right Uplus_lt_compat_left.

Lemma Uplus_lt_compat :
forall x y z t:U, z <= [1-] x -> t <= [1-] y -> x < y -> z < t -> (x + z) < (y + t).
intros; apply Ult_trans with (y + z); auto.
apply Uplus_lt_compat_left; auto.
apply Ule_trans with t; auto.
Save.

Hint Immediate Uplus_lt_compat.

Lemma Uplus_lt_simpl_left : forall x y z:U, z <= [1-] y -> (z + x) < (z + y) -> x < y.
unfold lt; repeat red; intros.
apply H0; auto.
Save.

Lemma Uplus_lt_simpl_right : forall x y z:U, z <= [1-] y -> (x + z) < (y + z) -> x < y.
unfold lt; repeat red; intros.
apply H0; auto.
Save.

Lemma Uplus_one_le : forall x y, x + y == 1 -> [1-] y <= x.
intros; apply Ule_class; red; intros.
assert (x < [1-] y); auto.
assert (x + y < [1-] y + y); auto.
assert (x + y < 1); auto.
setoid_rewrite <- (Uinv_opp_left y); auto. 
Save.
Hint Immediate Uplus_one_le.

Theorem Uplus_eq_zero : forall x, x <= [1-] x -> (x + x) == x -> x == 0.
intros x H1 H2; apply Uplus_eq_simpl_left with x; auto.
setoid_rewrite H2; auto.
Save.

Lemma Umult_zero_left : forall x, 0 * x == 0.
intros; apply Uinv_simpl.
setoid_rewrite (Udistr_inv_right 0 x); auto.
setoid_rewrite Uinv_zero.
setoid_rewrite (Umult_one_left x); auto.
Save.
Hint Resolve Umult_zero_left.

Lemma Umult_zero_right : forall x, (x * 0) == 0.
intros; setoid_rewrite (Umult_sym x 0); auto.
Save.
Hint Resolve Uplus_eq_zero Umult_zero_right.

(** *** Compatibility of operations with respect to order. *)

Lemma Umult_le_simpl_right : forall x y z, ~0 == z -> (x * z) <= (y * z) -> x <= y.
intros; apply Umult_le_simpl_left with z; auto.
setoid_rewrite (Umult_sym z x); 
setoid_rewrite (Umult_sym z y);trivial.
Save.
Hint Resolve Umult_le_simpl_right.

Lemma Umult_simpl_right : forall x y z, ~0 == z -> (x * z) == (y * z) -> x == y.
intros; apply Ule_antisym; auto.
apply Umult_le_simpl_right with z; auto.
apply Umult_le_simpl_right with z; auto.
Save.

Lemma Umult_simpl_left : forall x y z, ~0 == x -> (x * y) == (x * z) -> y == z.
intros; apply Ule_antisym; auto.
apply Umult_le_simpl_left with x; auto.
apply Umult_le_simpl_left with x; auto.
Save.

Lemma Umult_lt_compat_left : forall x y z, ~0 == z-> x < y -> (x * z) < (y * z).
unfold Ult,not;intros.
apply H0; apply Umult_le_simpl_right with z; auto.
Save.

Lemma Umult_lt_compat_right : forall x y z, ~0 == z -> x < y -> (z * x) < (z * y).
unfold Ult,not;intros.
apply H0; apply Umult_le_simpl_left with z; auto.
Save.


Lemma Umult_lt_simpl_right : forall x y z, ~0 == z -> (x * z) < (y * z) -> x < y.
unfold Ult,not;intros.
apply H0; auto.
Save.

Lemma Umult_lt_simpl_left : forall x y z, ~0 == z -> (z * x) < (z * y) -> x < y.
unfold Ult,not;intros.
apply H0; auto.
Save.

Hint Resolve Umult_lt_compat_left Umult_lt_compat_right.

Lemma Umult_zero_simpl_right : forall x y, 0 == x*y -> ~0 == x -> 0 == y.
intros.
apply Umult_simpl_left with x; auto.
rewrite (Umult_zero_right x); trivial.
Save.

Lemma Umult_zero_simpl_left : forall x y, 0 == x*y -> ~0 == y -> 0 == x.
intros.
apply Umult_simpl_right with y; auto.
rewrite (Umult_zero_left y); trivial.
Save.


Lemma Umult_neq_zero : forall x y, ~0 == x -> ~0 == y -> ~0 == x*y.
red; intros.
apply H0; apply Umult_zero_simpl_right with x; trivial.
Save.
Hint Resolve Umult_neq_zero.

Lemma Umult_lt_zero : forall x y, 0 < x -> 0 < y -> 0 < x*y.
auto.
Save.
Hint Resolve Umult_lt_zero.

Lemma Umult_lt_compat : forall x y z t, x < y -> z < t -> x * z < y * t.
intros.
assert (0<y); auto.
apply Ule_lt_trans with x; auto.
assert (0<t); auto.
apply Ule_lt_trans with z; auto.
apply (Ueq_orc 0 z); auto; intros.
rewrite <- H3.
rewrite Umult_zero_right; auto.
apply Ult_trans with (y * z); auto.
Save.

(** *** More Properties *)

Lemma Uplus_one : forall x y, [1-] x <= y -> x + y == 1.
intros; apply Ule_antisym; auto.
apply Ule_trans with (x + [1-] x); auto.
Save.
Hint Resolve Uplus_one.

Lemma Uplus_one_right : forall x, x + 1 == 1.
auto.
Save.

Lemma Uplus_one_left : forall x:U, 1 + x == 1.
auto.
Save.
Hint Resolve Uplus_one_right Uplus_one_left. 

Lemma Uinv_mult_simpl : forall x y z t, x <= [1-] y -> (x * z) <= [1-] (y * t).
intros; apply Ule_trans with x; auto.
intros; apply Ule_trans with ([1-] y); auto.
Save.
Hint Resolve Uinv_mult_simpl.

Lemma Umult_inv_plus :   forall x y, x * [1-] y + y == x + y * [1-] x.
intros; apply Ueq_trans with (x * [1-] y + y * ([1-] x + x)).
setoid_rewrite (Uinv_opp_left x); auto.
assert (H:[1-] x <= [1-] x); auto.
setoid_rewrite (Udistr_plus_left y H).
apply Ueq_trans with (x * [1-] y + y * x + y * [1-] x).
norm_assoc_right; auto.
setoid_rewrite (Umult_sym y x).
assert (H1:[1-] y <= [1-] y); auto.
setoid_rewrite <- (Udistr_plus_left x H1).
setoid_rewrite (Uinv_opp_left y); auto.
Save.
Hint Resolve Umult_inv_plus.

Lemma Umult_inv_plus_le : forall x y z, y <= z -> x * [1-] y + y <= x * [1-] z + z.
intros.
setoid_rewrite (Umult_inv_plus x y); 
setoid_rewrite (Umult_inv_plus x z); auto.
Save.
Hint Resolve Umult_inv_plus_le.

Lemma Uplus_lt_Uinv :   forall x y, x+y < 1 -> x <= [1-] y.
intros; apply (Ule_total x ([1-]y)); intro; auto.
case H.
rewrite Uplus_one; auto. 
Save.

Lemma Uinv_lt_perm_left: forall x y : U, [1-] x < y -> [1-] y < x.
unfold Ult; intuition.
Save.

Lemma Uinv_lt_perm_right: forall x y : U, x < [1-] y -> y < [1-] x.
unfold Ult; intuition.
Save.

Hint Immediate Uinv_lt_perm_left Uinv_lt_perm_right.

Lemma Uinv_lt_one : forall x, 0 < x -> [1-]x < 1.
intro; setoid_replace 0 with ([1-]1); auto.
Save.

Lemma Uinv_lt_zero : forall x, x < 1 -> 0 < [1-]x.
intro; setoid_replace 1 with ([1-]0); auto.
Save.

Hint Resolve Uinv_lt_one Uinv_lt_zero.

Lemma Umult_lt_right : forall p q, p <1 -> 0 < q -> p * q < q.
intros.
apply Ult_le_trans with (1 * q); auto.
Save.

Lemma Umult_lt_left : forall p q, 0 < p -> q < 1 -> p * q < p.
intros.
apply Ult_le_trans with (p * 1); auto.
Save.

Hint Resolve Umult_lt_right Umult_lt_left.

(** ** Definition of $x^n$ *)
Fixpoint Uexp (x:U) (n:nat) {struct n} : U :=
   match n with 0 => 1 | (S p) => x * Uexp x p end.

Infix "^" := Uexp : U_scope.

Lemma Uexp_1 : forall x, x^1==x.
simpl; auto.
Save.

Lemma Uexp_0 : forall x, x^0==1.
simpl; auto.
Save.

Lemma Uexp_zero : forall n, (0<n)%nat -> 0^n==0.
destruct n; simpl; intro; auto.
casetype False; omega.
Save.

Lemma Uexp_one : forall n, 1^n==1.
induction n; simpl; auto.
rewrite IHn; auto.
Save.

Lemma Uexp_le_compat : 
      forall x n m, (n<=m)%nat -> x^m <= x^n.
induction 1; simpl; auto.
apply Ule_trans with (x^m); auto.
Save.

Lemma Uexp_Ule_compat : 
      forall x y n,  x<=y -> x^n <= y^n.
induction n; simpl; intros; auto.
apply Ule_trans with (x * (y^n)); auto.
Save.

Add Morphism Uexp : Uexp_eq_compat.
intros; apply Ule_antisym; apply Uexp_Ule_compat; auto.
Save.

Lemma Uexp_inv_S : forall x n, ([1-]x^(S n))==x*([1-]x^n)+[1-]x.
simpl; auto.
Save.

Lemma Uexp_lt_compat : forall p q n, (O<n)%nat->(p<q)->(p^n<q^n).
induction n; simpl; intros; auto.
casetype False; omega.
destruct n; auto.
apply Umult_lt_compat; auto with arith.
Save.

Hint Resolve Uexp_lt_compat.

Lemma Uexp_lt_zero : forall p n, (0<p)->(0<p^n).
destruct n; intros; auto.
rewrite <- (Uexp_zero (n:=S n)); auto with arith.
Save.
Hint Resolve Uexp_lt_zero.

Lemma Uexp_lt_one : forall p n, (0<n)%nat->(p<1)->(p^n<1).
intros; rewrite <- (Uexp_one n); auto with arith.
Save.
Hint Resolve Uexp_lt_one.

Lemma Uexp_lt_antimon: forall p n m, (n<m)%nat-> 0<p -> p < 1 -> p^m < p^n.
induction 1; simpl; intros; auto with arith. 
apply Ult_trans with (p*p^n); auto with arith. 
Save.
Hint Resolve Uexp_lt_antimon.

(** ** Definition and properties of $x \& y$
   A conjonction operation which coincides with min and mult 
   on 0 and 1, see Morgan & McIver *)

Definition Uesp (x y:U) := [1-] ([1-] x + [1-] y).

Infix "&" := Uesp  (left associativity, at level 40) : U_scope.

Lemma Uinv_plus_esp : forall x y, [1-] (x + y) == [1-] x & [1-] y.
unfold Uesp; intros.
setoid_rewrite (Uinv_inv x); setoid_rewrite (Uinv_inv y); auto.
Save.
Hint Resolve Uinv_plus_esp.

Lemma Uinv_esp_plus : forall x y, [1-] (x & y) == [1-] x + [1-] y.
unfold Uesp; intros.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)); trivial.
Save.
Hint Resolve Uinv_esp_plus.


Lemma Uesp_sym : forall x y : U, x & y == y & x.
intros; unfold Uesp; auto.
Save.

Lemma Uesp_one_right : forall x : U, x & 1 == x.
intro; unfold Uesp.
setoid_rewrite Uinv_one.
setoid_rewrite (Uplus_zero_right ([1-] x)); auto.
Save.

Lemma Uesp_zero : forall x y, x <= [1-] y -> x & y == 0.
intros; unfold Uesp.
setoid_rewrite <- Uinv_one; auto.
Save.

Hint Resolve Uesp_sym Uesp_one_right Uesp_zero.

Lemma Uesp_zero_right : forall x : U, x & 0 == 0.
auto.
Save.

Lemma Uesp_zero_left : forall x : U, 0 & x == 0.
auto.
Save.

Hint Resolve Uesp_zero_right Uesp_zero_left.

(** ** Definition and properties of $x - y $ *)

Definition Uminus (x y:U) := [1-] ([1-] x + y).

Infix "-" := Uminus : U_scope.

Lemma Uminus_le_compat_left : forall x y z, x <= y -> x - z <= y - z.
unfold Uminus; auto.
Save.

Lemma Uminus_le_compat_right :  forall x y z, y <= z -> x - z <= x - y.
unfold Uminus; auto.
Save.

Hint Resolve Uminus_le_compat_left Uminus_le_compat_right.

Add Morphism Uminus : Uminus_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Ule_antisym;
apply Ule_trans with (x1-x4); auto.
Save.
Hint Immediate Uminus_eq_compat.

Lemma Uminus_zero_right : forall x, x - 0 == x.
unfold Uminus; intros.
setoid_rewrite (Uplus_zero_right ([1-] x)); auto.
Save.

Lemma Uminus_one_left : forall x, 1 - x == [1-] x.
unfold Uminus; intros.
setoid_rewrite Uinv_one; auto.
Save.

Lemma Uminus_le_zero : forall x y, x <= y -> x - y == 0.
unfold Uminus; intros.
setoid_rewrite <- Uinv_one.
apply Uinv_eq_compat.
apply Ule_antisym; auto.
apply Ule_trans with ([1-] y + y); auto.
Save.

Hint Resolve Uminus_zero_right Uminus_one_left Uminus_le_zero.

Lemma Uminus_plus_simpl : forall x y, y <= x -> (x - y) + y == x.
unfold Uminus; intros.
assert (H1:y <= [1-] ([1-] x)); auto.
setoid_rewrite (Uinv_plus_right H1); auto.
Save.

Lemma Uminus_plus_zero : forall x y, x <= y -> (x - y) + y == y.
intros; setoid_rewrite (Uminus_le_zero H); auto.
Save.

Hint Resolve Uminus_plus_simpl Uminus_plus_zero.


Lemma Uesp_minus_distr_left : forall x y z, (x & y) - z  == (x - z) & y.
unfold Uesp, Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)).
setoid_rewrite (Uinv_inv (([1-] x) + z)).
repeat norm_assoc_right; auto.
Save.

Lemma Uesp_minus_distr_right : forall x y z, (x & y) - z  == x & (y - z).
intros; setoid_rewrite (Uesp_sym x y); 
setoid_rewrite (Uesp_sym x (y - z)); 
apply Uesp_minus_distr_left.
Save.

Hint Resolve Uesp_minus_distr_left Uesp_minus_distr_right.

Lemma Uesp_minus_distr : forall x y z t, (x & y) - (z + t) == (x - z) & (y - t).
unfold Uesp, Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)).
setoid_rewrite (Uinv_inv ([1-] x + z)).
setoid_rewrite (Uinv_inv ([1-] y + t)).
repeat norm_assoc_right; auto.
Save.
Hint Resolve Uesp_minus_distr.

(** ** Definition and properties of max *)

Definition max (x y : U) : U := (x - y) + y.

Lemma max_le_right : forall x y : U, y <= x -> (max x y) == x.
unfold max; auto.
Save.

Lemma max_le_left : forall x y : U, x <= y -> (max x y) == y.
unfold max; auto.
Save.

Hint Resolve max_le_right max_le_left.

Lemma max_le_case : forall x y : U, (orc (max x y == x) (max x y == y)).
intros; apply (Ule_total x y); auto.
Save.

Add Morphism max : max_eq_compat.
unfold max; intros.
apply Uplus_eq_compat; auto.
Save.

(** ** Other properties *)
Lemma Uplus_minus_simpl_right : forall x y, y <= [1-] x -> (x + y) - y == x.
unfold Uminus; intros.
setoid_rewrite (Uinv_plus_right H); auto.
Save.
Hint Resolve Uplus_minus_simpl_right.

Lemma Uplus_minus_simpl_left : forall x y, y <= [1-] x -> (x + y) - x == y.
intros; setoid_rewrite (Uplus_sym x y); auto.
Save.

Lemma Uminus_assoc_left : forall x y z, (x - y) - z == x - (y + z).
unfold Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
Save.

Hint Resolve Uminus_assoc_left.

Lemma Uminus_le_perm_left : forall x y z, y <= x -> x - y <= z -> x <= z + y.
intros; setoid_rewrite <- (Uminus_plus_simpl H); auto.
Save.

Lemma Uplus_le_perm_left : forall x y z, y <= x -> x <= y + z  -> x - y <= z.
intros; apply Uplus_le_simpl_left with y.
unfold Uminus; setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
setoid_rewrite (Uplus_sym y (x-y)); setoid_rewrite (Uminus_plus_simpl H); auto.
Save.

Lemma Uminus_eq_perm_left : forall x y z, y <= x -> x - y == z -> x == z + y.
intros; setoid_rewrite <- (Uminus_plus_simpl H); auto.
Save.

Lemma Uplus_eq_perm_left : forall x y z, y <= [1-] z -> x == y + z  -> x - y == z.
intros; setoid_rewrite H0; auto.
setoid_rewrite (Uplus_sym y z); auto.
Save.

Hint Resolve Uminus_le_perm_left Uminus_eq_perm_left.
Hint Resolve Uplus_le_perm_left Uplus_eq_perm_left.

Lemma Uminus_le_perm_right : forall x y z, z <= y -> x <= y - z -> x + z <= y.
intros; setoid_rewrite <- (Uminus_plus_simpl H); auto.
Save.

Lemma Uplus_le_perm_right : forall x y z, z <= [1-] x -> x + z <= y  -> x <= y - z.
intros; apply Uplus_le_simpl_right with z; auto.
Save.
Hint Resolve Uminus_le_perm_right Uplus_le_perm_right.

Lemma Uminus_le_perm : forall x y z, z <= y -> x <= [1-] z -> x <= y - z -> z <= y - x.
intros; apply Uplus_le_perm_right; auto.
setoid_rewrite (Uplus_sym z x); auto.
Save.
Hint Resolve Uminus_le_perm.

Lemma Uminus_eq_perm_right : forall x y z, z <= y -> x == y - z -> x + z == y.
intros; apply Ueq_trans with (y - z + z); auto.
Save.
Hint Resolve Uminus_eq_perm_right.


Lemma Uminus_zero_le : forall x y, x - y == 0 -> x <= y.
intros x y; unfold Uminus; intros.
setoid_rewrite <- (Uinv_inv x).
apply Uplus_one_le.
setoid_rewrite <- Uinv_zero; auto.
setoid_rewrite <- H; auto.
setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
Save.

Lemma Uminus_lt_non_zero : forall x y, x < y -> ~y - x == 0.
red; intros.
apply H; auto.
apply Uminus_zero_le; auto.
Save.
Hint Immediate Uminus_zero_le Uminus_lt_non_zero.

Lemma Ult_le_nth : forall x y, x < y -> (exists n, x <= y - [1/]1+n).
intros; elim (archimedian (x:=(y - x))); intros; auto.
exists x0.
apply Uminus_le_perm; auto.
apply Ule_trans with (y - x); auto. 
apply Ule_trans with (1 - x); auto.
Save.

Lemma Uminus_distr_left : forall x y z, (x - y) * z == (x * z) - (y * z).
intros; apply (Ule_total x y); intros; auto.
(* first case x <= y, left and right hand side equal 0 *)
setoid_rewrite (Uminus_le_zero H).
setoid_rewrite (Umult_zero_left z).
assert (x * z <= y * z); auto.
setoid_rewrite (Uminus_le_zero H0); auto.
(* second case y <= x, use simplification *)
unfold Uminus; intros; auto.
apply Uplus_eq_simpl_right with (y * z); auto.
assert ([1-] ([1-] x + y) <= [1-] y); auto.
setoid_rewrite <- (Udistr_plus_right z H0); auto.
assert (y <= [1-] ([1-] x)); auto.
setoid_rewrite (Uinv_plus_right H1).
setoid_rewrite (Uinv_inv x); auto.
Save.

Hint Resolve Uminus_distr_left.

Lemma Uminus_distr_right : forall x y z,  x * (y - z) == (x * y) - (x * z).
intros; setoid_rewrite (Umult_sym x y).
setoid_rewrite (Umult_sym x z).
setoid_rewrite (Umult_sym x (y - z)); auto.
Save.

Hint Resolve Uminus_distr_right.


Lemma Uminus_assoc_right :  forall x y z, y <= x -> z <= y -> x - (y - z) == (x - y) + z.
intros.
apply Uplus_eq_perm_left; auto.
unfold Uminus at 1; apply Uinv_le_compat.
apply Ule_trans with (1 - y + z); auto.
apply Ueq_trans with ((y - z) + z + (x - y)).
setoid_rewrite (Uminus_plus_simpl H0).
setoid_rewrite (Uplus_sym y (x - y)); auto.
norm_assoc_right; auto.
Save.

(** ** Definition and properties of generalized sums *)

Definition sigma (alpha : nat -> U) (n:nat) := comp Uplus 0 alpha n.

Lemma sigma_0 : forall (f : nat -> U), sigma f 0 == 0.
trivial.
Save.

Lemma sigma_S : forall (f :nat -> U) (n:nat), sigma f (S n) = (f n) + (sigma f n).
trivial.
Save.

Lemma sigma_1 : forall (f : nat -> U), sigma f (S 0) == f O.
intros; rewrite sigma_S; auto.
Save.

Lemma sigma_S_lift : forall (f :nat -> U) (n:nat), 
          sigma f (S n) == (f O) + (sigma (fun k => f (S k)) n).
intros f n; generalize f; induction n; simpl; intros; auto.
rewrite sigma_S.
rewrite IHn.
rewrite sigma_S.
rewrite Uplus_assoc.
rewrite (Uplus_sym (f0 (S n)) (f0 O)); auto.
Save.

Lemma sigma_incr : forall (f : nat -> U) (n m:nat), (n <= m)%nat -> (sigma f n) <= (sigma f m).
intros f n m H; induction H; auto.
intros; rewrite sigma_S.
apply Ule_trans with (1:=IHle); auto.
Save.

Hint Resolve sigma_incr.

Lemma sigma_eq_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k == g k) -> (sigma f n) == (sigma g n).
induction n; auto.
intros; repeat rewrite sigma_S.
apply Ueq_trans with (g n + sigma f n); auto with arith.
Save.

Lemma sigma_le_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k <= g k) -> (sigma f n) <= (sigma g n).
induction n; auto.
intros; repeat rewrite sigma_S.
apply Ule_trans with (g n + sigma f n); auto with arith.
Save.

Lemma sigma_zero : forall f n, (forall k, (k<n)%nat -> f k ==0)->(sigma f n)==0.
induction n; simpl; intros; auto.
rewrite sigma_S.
rewrite (H n); auto.
rewrite IHn; auto.
Save.

Lemma sigma_not_zero : forall f n k, (k<n)%nat -> 0 < f k -> 0 < sigma f n.
induction n; simpl; intros; auto.
casetype False; omega.
rewrite sigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H1; intros; subst; auto.
apply Ult_le_trans with (sigma f n); auto.
apply (IHn k); auto.
apply Ult_le_trans with (f n); auto.
Save.

Lemma sigma_zero_elim : forall f n, (sigma f n)==0->forall k, (k<n)%nat -> f k ==0.
intros; apply Ueq_class; red; intros.
assert (0 < sigma f n); auto.
apply sigma_not_zero with k; auto.
Save.

Hint Resolve sigma_eq_compat sigma_le_compat sigma_zero.

Lemma sigma_le : forall f n k, (k<n)%nat -> f k <= sigma f n.
induction n; simpl; intros.
casetype False; omega.
rewrite sigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H0; intros; subst; auto.
apply Ule_trans with (sigma f n); auto.
Save.

(** ** Properties of [Unth] *)
Lemma Unth_zero : [1/]1+0 == 1.
setoid_rewrite (Unth_prop 0); auto.
Save.

Notation "[1/2]" := (Unth 1).

Lemma Unth_one : [1/2] == [1-] [1/2].
apply Ueq_trans with (1:=Unth_prop 1); simpl; auto.
Save.

Hint Resolve Unth_zero Unth_one.

Lemma Unth_one_plus : [1/2] + [1/2] == 1.
apply Ueq_trans with  ([1/2] + [1-][1/2]); auto.
Save.
Hint Resolve Unth_one_plus.

Lemma Unth_not_null : forall n, ~ (0 == [1/]1+n).
red; intros.
apply Udiff_0_1.
apply Ueq_trans with ([1/]1+n); auto.
apply Ueq_trans with ([1-] (sigma (fun k => [1/]1+n) n)).
apply (Unth_prop n).
apply Ueq_trans with ([1-] (sigma (fun k => 0) n)).
apply Uinv_eq_compat.
apply sigma_eq_compat; auto.
apply Ueq_trans with ([1-] 0); auto.
Save.
Hint Resolve Unth_not_null.

Lemma Unth_lt_zero : forall n, 0 < [1/]1+n.
auto.
Save.
Hint Resolve Unth_lt_zero.

Lemma Unth_inv_lt_one : forall n, [1-][1/]1+n<1.
intro; setoid_replace 1 with ([1-]0); auto.
Save.
Hint Resolve Unth_inv_lt_one.

Lemma Unth_not_one : forall n, ~ (1 == [1-][1/]1+n).
auto.
Save.
Hint Resolve Unth_not_one.

Lemma Unth_prop_sigma : forall n, [1/]1+n == [1-] (sigma (fun k => [1/]1+n) n).
exact Unth_prop.
Save.
Hint Resolve Unth_prop_sigma.

Lemma Unth_sigma_n : forall n : nat, ~ (1 == sigma (fun k => [1/]1+n) n).
intros; apply Uinv_neq_simpl.
setoid_rewrite Uinv_one.
setoid_rewrite <- (Unth_prop_sigma n); auto.
Save.

Lemma Unth_sigma_Sn : forall n : nat, 1 == sigma (fun k => [1/]1+n) (S n).
intros; rewrite sigma_S.
apply Ueq_trans with 
([1-] (sigma (fun k => [1/]1+n) n) + (sigma (fun k => [1/]1+n) n));auto.
Save.

Hint Resolve Unth_sigma_n Unth_sigma_Sn.


Lemma Unth_decr : forall n, [1/]1+(S n) < [1/]1+n.
repeat red; intros.
apply (Unth_sigma_n (S n)).
apply Ule_antisym; auto.
apply Ule_trans with (sigma (fun _ : nat => [1/]1+n) (S n)); auto.
Save.
Hint Resolve Unth_decr.

Lemma Unth_anti_mon : 
forall n m, (n <= m)%nat -> [1/]1+m <= [1/]1+n.
induction 1; auto.
apply Ule_trans with ([1/]1+m); auto.
Save.
Hint Resolve Unth_anti_mon.

Lemma Unth_le_half : forall n, [1/]1+(S n) <= [1/2].
auto with arith.
Save.
Hint Resolve Unth_le_half.

(** *** Mean of two numbers : $\frac{1}{2}x+\frac{1}{2}y$*)
Definition mean (x y:U) := [1/2] * x + [1/2] * y.

Lemma mean_eq : forall x:U, mean x x ==x.
unfold mean; intros.
assert (H : ([1/2] <= [1-] ([1/2]))); auto.
setoid_rewrite <- (Udistr_plus_right x H); auto.
setoid_rewrite Unth_one_plus; auto.
Save.

Lemma mean_le_compat_right : forall x y z, y <= z -> mean x y <= mean x z.
unfold mean; intros.
apply Uplus_le_compat_right; auto.
Save.

Lemma mean_le_compat_left : forall x y z, x <= y -> mean x z <= mean y z.
unfold mean; intros.
apply Uplus_le_compat_left; auto.
Save.

Hint Resolve mean_eq mean_le_compat_left mean_le_compat_right.

Lemma mean_lt_compat_right : forall x y z, y < z -> mean x y < mean x z.
unfold mean; intros.
apply Uplus_lt_compat_right; auto.
Save.

Lemma mean_lt_compat_left : forall x y z, x < y -> mean x z < mean y z.
unfold mean; intros.
apply Uplus_lt_compat_left; auto.
Save.

Hint Resolve mean_eq mean_le_compat_left mean_le_compat_right.
Hint Resolve mean_lt_compat_left mean_lt_compat_right.

Lemma mean_le_up : forall x y, x <= y -> mean x y <= y.
intros; apply Ule_trans with (mean y y); auto. 
Save.

Lemma mean_le_down : forall x y, x <= y -> x <= mean x y.
intros; apply Ule_trans with (mean x x); auto. 
Save.

Lemma mean_lt_up : forall x y, x < y -> mean x y < y.
intros; apply Ult_le_trans with (mean y y); auto. 
Save.

Lemma mean_lt_down : forall x y, x < y -> x < mean x y.
intros; apply Ule_lt_trans with (mean x x); auto. 
Save.

Hint Resolve mean_le_up mean_le_down mean_lt_up mean_lt_down.

(** *** Properties of $\frac{1}{2}$ *)

Lemma le_half_inv : forall x, x <= [1/2] -> x <= [1-] x.
intros; apply Ule_trans with ([1/2]); auto.
setoid_rewrite Unth_one; auto.
Save.

Hint Immediate le_half_inv.

Lemma ge_half_inv : forall x, [1/2] <= x  -> [1-] x <= x.
intros; apply Ule_trans with ([1/2]); auto.
setoid_rewrite Unth_one; auto.
Save.

Hint Immediate ge_half_inv.

Lemma Uinv_le_half_left : forall x, x <= [1/2] -> [1/2] <= [1-] x.
intros; setoid_rewrite Unth_one; auto.
Save.

Lemma Uinv_le_half_right : forall x, [1/2] <= x -> [1-] x <= [1/2].
intros; setoid_rewrite Unth_one; auto.
Save.

Hint Resolve Uinv_le_half_left Uinv_le_half_right.

Lemma half_twice : forall x,  (x <= [1/2]) -> ([1/2]) * (x + x) == x.
intros; assert (H1 : x <= [1-] x); auto. 
setoid_rewrite (Udistr_plus_left ([1/2]) H1).
exact (mean_eq x).
Save.

Lemma half_twice_le : forall x, ([1/2]) * (x + x) <= x.
intros; apply (Ule_total x ([1/2])); intros; auto.
setoid_rewrite (half_twice H); trivial.
assert (x+x==1); auto.
setoid_rewrite H0.
setoid_rewrite (Umult_one_right ([1/2])); auto.
Save.

Lemma Uinv_half : forall x, ([1/2]) * ([1-] x)  + ([1/2]) == [1-] (([1/2]) * x).
intros; setoid_rewrite (Udistr_inv_left ([1/2]) x).
setoid_rewrite Unth_one; auto.
Save.

Lemma half_esp : 
forall x, ([1/2] <= x) -> ([1/2]) * (x & x) + [1/2] == x.
intros; unfold Uesp.
setoid_rewrite (Uinv_half ([1-] x + [1-] x)).
assert (H1:[1-] x <= [1/2]).
setoid_rewrite Unth_one; auto.
setoid_rewrite (half_twice H1); auto.
Save.

Lemma half_esp_le : forall x, x <= ([1/2]) * (x & x) + [1/2].
intros; apply (Ule_total ([1/2]) x); intros; auto.
setoid_rewrite (half_esp H); trivial.
assert (x & x == 0); auto.
setoid_rewrite H0.
setoid_rewrite (Umult_zero_right ([1/2])).
setoid_rewrite (Uplus_zero_left ([1/2])); auto.
Save.
Hint Resolve half_esp_le.


Lemma half_le : forall x y, y <= [1-] y -> x <= y + y -> ([1/2]) * x <= y.
intros.
apply not_Ult_le; red; intros.
assert (y + y < x); auto.
setoid_replace x with (mean x x); auto.
unfold mean; apply Uplus_lt_compat; auto.
Save.

Lemma half_Unth: forall n, ([1/2])*([1/]1+n) <= [1/]1+(S n).
intros; apply half_le; auto.
setoid_rewrite (Unth_prop_sigma n).
apply Ule_trans with ([1-] (sigma (fun _ : nat => [1/]1+(S n)) n)).
apply Uinv_le_compat.
apply sigma_le_compat; auto.
apply Ule_trans with 
([1-] (sigma (fun _ : nat => [1/]1+(S n)) (S n)) + [1/]1+(S n)); auto.
rewrite sigma_S.
assert (sigma (fun _ : nat => [1/]1+(S n)) n <= [1-] ([1/]1+(S n))).
apply Ule_trans with (sigma (fun _ : nat => [1/]1+(S n)) (S n)); auto.
setoid_rewrite (Uinv_plus_left H); auto.
Save.
Hint Resolve half_le half_Unth.

Lemma half_exp : forall n, [1/2]^n == [1/2]^(S n) + [1/2]^(S n).
intros; simpl; apply Ueq_sym; exact (mean_eq ([1/2]^n)).
Save.

(** ** Density *)
Lemma Ule_lt_lim : forall x y,  (forall t, t < x -> t <= y) -> x <= y.
intros; apply Ule_class; red; intros.
pose (z:= mean y x).
assert (y < z); unfold z; auto.
apply H1; apply H; unfold z; auto.
Save.

(** ** Properties of least upper bounds *)

Section lubs.

Lemma lub_le_stable : forall f g, (forall n, f n <= g n) -> lub f <= lub g.
intros; apply lub_le; intros.
apply Ule_trans with (g n); auto.
Save.

Hint Resolve lub_le_stable.

Lemma lub_eq_stable : forall f g, (forall n, f n == g n) -> lub f == lub g.
intros; apply Ule_antisym; auto.
Save.

Hint Resolve lub_eq_stable.

Lemma lub_zero : (lub (fun n => 0)) == 0.
apply Ule_antisym; auto.
Save.

Lemma lub_un : (lub (fun n => 1)) == 1.
apply Ule_antisym; auto.
apply le_lub with (f:=fun _ : nat => 1) (n:=O); auto.
Save.

Lemma lub_cte : forall c:U, (lub (fun n => c)) == c.
intro; apply Ueq_trans with (lub (fun n => c * 1)); auto.
apply Ueq_trans with (c * (lub (fun n => 1))); auto.
(* Become useless with pattern-unification
apply lub_eq_mult with (f:=fun (n:nat) => 1); auto. 
*)
setoid_rewrite lub_un; auto.
Save.

Hint Resolve lub_zero lub_un lub_cte.

Lemma lub_eq_plus_cte_left : forall (f : nat -> U) (k:U), lub (fun n => k + (f n)) == k + (lub f).
intros; apply Ueq_trans with ((lub f)+k); auto.
apply Ueq_trans with (lub (fun n => (f n) + k)); auto.
Save.
Hint Resolve lub_eq_plus_cte_left.


Variables f g : nat -> U.

Hypothesis monf : (mon_seq Ule f).
Hypothesis mong : (mon_seq Ule g).


Lemma lub_lift : forall n,  (lub f) == (lub (fun k => f (n+k)%nat)).
intro; apply Ule_antisym; auto.
apply lub_le_stable; auto with arith.
Save.

Hint Resolve lub_lift.

Let sum := fun n => f n + g n.

Lemma mon_sum : mon_seq Ule sum.
unfold mon_seq,sum in *; intros; apply Uplus_le_compat; auto.
Save.

Hint Resolve mon_sum.

Lemma lub_eq_plus : lub (fun n => (f n) + (g n)) == (lub f) + (lub g).
apply Ule_antisym.
apply lub_le; auto.
apply Ule_trans with (lub (fun n => lub f + g n)); auto.
apply lub_le; intros.
apply Ule_trans with (lub (fun m => f (n+m)) + g n); auto.
setoid_rewrite <- (lub_eq_plus_cte_right (fun m : nat => f (n + m)) (g n)).
apply lub_le; intros.
apply Ule_trans with (f (n + n0) + g (n + n0)); auto with arith.
apply le_lub with (f:=fun n : nat => f n + g n) (n:=(n+n0)%nat).
Save.
Hint Resolve lub_eq_plus.

Variables k : U.
Let prod := fun n => k * f n.

Lemma mon_prod : mon_seq Ule prod.
unfold mon_seq,prod in *; intros.
apply Umult_le_compat_right; auto.
Save.

Let inv:= fun n => [1-] (g n).

Lemma lub_inv : (forall n, f n <= inv n) -> lub f <= [1-] (lub g).
unfold inv; intros.
apply Uinv_le_perm_right.
apply lub_le; intros.
apply Uinv_le_perm_right.
apply Ule_trans with (lub (fun k => f (n+k)%nat)); auto.
apply lub_le; intros.
apply Ule_trans with ([1-] (g (n+n0))); auto with arith.
Save.

End lubs.

(** ** Properties of barycenter of two points *)
Section Barycenter.
Variables a b : U.
Hypothesis sum_le_one : a <= [1-] b.

Lemma Uinv_bary : 
   forall x y : U, [1-] (a * x + b * y) == a * [1-] x + b * [1-] y + [1-] (a + b).
intros.
apply Uplus_eq_simpl_left with (a * x); auto.
apply Uinv_le_perm_right.
setoid_rewrite (Udistr_inv_left a x).
repeat norm_assoc_right.
apply Uplus_le_compat_right.
apply Ule_trans with (b + [1-] (a + b)); auto.
apply Ule_trans with ([1-] (a + b) + b); auto.
apply Ueq_trans with ([1-] (b * y)).
apply Ueq_trans with 
   ([1-] (a * x + b * y) + a * x); auto.
setoid_rewrite (Udistr_inv_left b y); auto.
apply Ueq_trans with  
 ((a * x + a * [1-] x) + b * [1-] y + [1-] (a + b)).
assert (x <= ([1-] ([1-] x))); auto.
setoid_rewrite <- (Udistr_plus_left a H); auto.
setoid_rewrite (Uinv_opp_right x).
setoid_rewrite (Umult_one_right a).
apply Ueq_trans with (b * [1-] y + ([1-] (a + b) + a)).
assert (b <= ([1-] a)); auto.
setoid_rewrite (Uinv_plus_left H0); auto.
setoid_rewrite (Uplus_sym a (b * [1-] y)); auto.
apply Ueq_trans with 
(b * [1-] y + (a + [1-] (a + b))); auto.
apply Ueq_trans with 
(((a * x + a * [1-] x) + (b * [1-] y + [1-] (a + b)))); auto.
apply Ueq_trans with 
(((a * x + (a * [1-] x + (b * [1-] y + [1-] (a + b)))))); auto.
Save.
End Barycenter.

(** ** Properties of generalized sums [sigma] *)
Lemma sigma_plus : 
  forall (f g : nat -> U) (n:nat), (sigma (fun k => (f k) + (g k)) n) == (sigma f n) + (sigma g n).
intros; induction n; simpl; auto.
repeat rewrite sigma_S; setoid_rewrite IHn.
repeat norm_assoc_right; apply Uplus_eq_compat_right.
setoid_rewrite (Uplus_sym (g n) ((sigma f n) + (sigma g n))).
repeat norm_assoc_right; apply Uplus_eq_compat_right; auto.
Save.


Definition retract (f : nat -> U) (n : nat) := forall k, (k < n)%nat -> (f k) <= [1-] (sigma f k).

Lemma retract0 : forall (f : nat -> U), retract f 0.
red; intros; absurd (k < O)%nat; auto with arith.
Save.

Lemma retract_pred : forall (f : nat -> U) (n : nat), retract f (S n) -> retract f n.
unfold retract; auto with arith.
Save.

Lemma retractS: forall (f : nat -> U) (n : nat), retract f (S n) -> f n <= [1-] (sigma f n).
unfold retract; auto with arith.
Save.

Lemma retractS_intro: forall (f : nat -> U) (n : nat), 
   retract f n -> f n <= [1-] (sigma f n)->retract f (S n).
unfold retract; intros.
assert ((k<n)%nat \/ k=n); try omega; intuition; subst; auto.
Save.

Hint Resolve retract0 retractS_intro.
Hint Immediate retract_pred retractS.

Lemma retract_lt : forall (f : nat -> U) (n : nat),  (sigma f n) < 1 -> retract f n.
induction n; simpl; auto.
rewrite sigma_S.
intros;assert ((sigma f n)<1).
apply Ule_lt_trans with (f n + sigma f n); auto.
assert (f n <= [1-](sigma f n)); auto.
apply Uplus_lt_Uinv; auto.
Save.

Lemma sigma_mult : 
  forall (f : nat -> U) n c, retract f n -> (sigma (fun k => c * (f k)) n) == c * (sigma f n).
intros; induction n; simpl; auto.
repeat rewrite sigma_S.
assert (H1: retract f n); auto.
setoid_rewrite (IHn H1).
setoid_rewrite (Udistr_plus_left c (retractS H)); auto.
Save.
Hint Resolve sigma_mult.

Lemma sigma_prod_maj :  forall (f g : nat -> U) n, 
   (sigma (fun k => (f k) * (g k)) n) <= (sigma f n).
auto.
Save.

Hint Resolve sigma_prod_maj.

Lemma sigma_prod_le :  forall (f g : nat -> U) (c:U), 
 (forall k, (f k) <= c) -> forall n, (retract g n) -> (sigma (fun k => (f k) * (g k)) n) <= c * (sigma g n).
induction n; simpl; intros; auto.
repeat rewrite sigma_S.
apply Ule_trans with ((f n) * (g n) + (c * sigma g n)); auto.
apply Ule_trans with ( c * (g n) + (c * sigma g n)); auto.
setoid_rewrite (Udistr_plus_left c (retractS H0)); auto.
Save.

Lemma sigma_prod_ge :  forall (f g : nat -> U) (c:U), (forall k, c <= (f k)) 
 -> forall n, (retract g n) -> c * (sigma g n) <= (sigma (fun k => (f k) * (g k)) n).
induction n; simpl; intros; auto.
repeat rewrite sigma_S.
setoid_rewrite (Udistr_plus_left c (retractS H0)); auto.
apply Ule_trans with (c * (g n) + sigma (fun k : nat => f k * g k) n); auto.
Save.

Hint Resolve sigma_prod_maj sigma_prod_le  sigma_prod_ge.

Lemma sigma_inv : forall (f g : nat -> U) (n:nat), (retract f n) ->
  [1-] (sigma (fun k => (f k) * (g k)) n) == (sigma (fun k => (f k) * [1-] (g k)) n) + [1-] (sigma f n).
intros; induction n; simpl; repeat rewrite sigma_S; auto.
apply Uplus_eq_simpl_right with ((f n) * (g n)).
setoid_rewrite 
 (Uinv_inv (f n * g n + sigma (fun k : nat => f k * g k) n));auto.
apply Uinv_le_perm_right.
setoid_rewrite (Udistr_inv_left (f n) (g n)).
repeat norm_assoc_right; apply Uplus_le_compat_right.
apply Ule_trans with 
  (sigma f n + [1-] (f n + sigma f n)); auto.
assert (sigma f n <= [1-] (f n)); auto.
setoid_rewrite <- (Uinv_plus_right H0); auto.

assert (sigma (fun k : nat => f k * g k) n <= [1-] (f n * g n)).
apply Ule_trans with (sigma f n); auto.
apply Ule_trans with ([1-] (f n)); auto.
setoid_rewrite (Uinv_plus_left H0).
apply Ueq_trans with (1:=IHn (retract_pred H)).
setoid_rewrite (Uplus_sym (f n * [1-] (g n))
                          (sigma (fun k : nat => f k * [1-] (g k)) n)).
repeat norm_assoc_right; apply Uplus_eq_compat_right.
setoid_rewrite (Uplus_sym  ([1-] (f n + sigma f n)) (f n * g n)).
repeat norm_assoc_left.
assert ([1-] (g n) <= [1-] (g n)); auto.

setoid_rewrite <- (Udistr_plus_left (f n) H1).
setoid_rewrite (Uinv_opp_left (g n)).
setoid_rewrite (Umult_one_right (f n)); auto.
setoid_rewrite (Uplus_sym (f n) ([1-] (f n + sigma f n))).
apply Ueq_sym; apply Uinv_plus_left; auto.
Save.


(** ** Product by an integer *)

Fixpoint Nmult (n: nat) (x : U) {struct n} : U := 
   match n with O => 0 | (S O) => x | S p => x + (Nmult p x) end.

(** Condition for [n */ x] to be exact *)
Definition Nmult_def (n: nat) (x : U) := 
   match n with O => True | S p => x <= [1/]1+p end.

Lemma Nmult_def_O : forall x, Nmult_def O x.
simpl; auto.
Save.
Hint Resolve Nmult_def_O.

Lemma Nmult_def_1 : forall x, Nmult_def (S O) x.
simpl; intro; rewrite Unth_zero; auto.
Save.
Hint Resolve Nmult_def_1.

Lemma Nmult_def_intro : forall n x , x <= [1/]1+n -> Nmult_def (S n) x.
destruct n; simpl; auto.
Save.
Hint Resolve Nmult_def_intro.

Lemma Nmult_def_Unth: forall n , Nmult_def (S n) ([1/]1+n).
auto.
Save.
Hint Resolve Nmult_def_Unth.

Lemma Nmult_def_pred : forall n x, Nmult_def (S n) x -> Nmult_def n x.
intros n x; case n; simpl; intros; auto.
apply Ule_trans with ([1/]1+(S n0)); auto.
Save.

Hint Immediate Nmult_def_pred.

Lemma Nmult_defS : forall n x, Nmult_def (S n) x -> x <= [1/]1+n.
destruct n; simpl; intros; auto.
Save.
Hint Immediate Nmult_defS.

Lemma Nmult_def_class : forall n p, class (Nmult_def n p).
unfold class; destruct n; intuition.
Save.
Hint Resolve Nmult_def_class.

Add Morphism Nmult_def : Nmult_def_eq_compat.


Infix "*/" := Nmult (at level 60) : U_scope.
unfold Nmult_def; destruct x; intuition.
rewrite <- H; auto.
rewrite H; auto.
Save.

Lemma Nmult_def_zero : forall n, Nmult_def n 0.
destruct n; auto.
Save.
Hint Resolve Nmult_def_zero.

Lemma Nmult_0 : forall (x:U), (O*/x) = 0.
trivial.
Save.

Lemma Nmult_1 : forall (x:U), ((S O)*/x) = x.
trivial.
Save.

Lemma Nmult_zero : forall n, n */ 0 == 0.
induction n; simpl; auto.
destruct n; auto.
rewrite IHn; auto.
Save.

Lemma Nmult_SS : forall (n:nat) (x:U), (S (S n) */x) = x + (S n */ x).
destruct n; simpl; auto.
Save.

Lemma Nmult_2 : forall (x:U), (2*/x) = x + x.
trivial.
Save.

Lemma Nmult_S : forall (n:nat) (x:U), (S n */ x) == x + (n*/x).
destruct n; simpl; auto.
Save.

Hint Resolve Nmult_1 Nmult_SS Nmult_2 Nmult_S.

Add Morphism Nmult : Nmult_eq_compat.
intros n x1 x2 eq1; induction n; simpl; auto; intros.
destruct n; repeat rewrite Nmult_SS; trivial.
apply Uplus_eq_compat; auto.
Save.
Hint Resolve Nmult_eq_compat.

Lemma Nmult_eq_compat_right : forall (n m:nat) (x:U), (n = m)%nat -> (n */ x) == (m */ x).
intros; subst n; trivial.
Save.
Hint Resolve Nmult_eq_compat_right.

Lemma Nmult_le_compat_right :  forall n x y, (x <= y) -> (n */ x) <= (n */ y).
intros; induction n; auto.
rewrite (Nmult_S n x); rewrite (Nmult_S n y);auto.
Save.

Lemma Nmult_le_compat_left : forall n m x, (n <= m)%nat -> (n */ x) <= (m */ x).
induction 1; trivial.
rewrite (Nmult_S m x); auto.
apply Ule_trans with (m */ x); auto.
Save.

Lemma Nmult_sigma : forall (n:nat) (x:U), n */ x == sigma (fun k => x) n.
intros n x; induction n; simpl; auto.
destruct n; auto.
unfold sigma; simpl; auto.
rewrite IHn; auto.
Save.

Hint Resolve Nmult_eq_compat_right Nmult_le_compat_right 
Nmult_le_compat_left Nmult_sigma.

Lemma Nmult_Unth_prop : forall n:nat, [1/]1+n == [1-] (n*/ ([1/]1+n)).
intro.
rewrite (Nmult_sigma n ([1/]1+n)).
exact (Unth_prop n).
Save.
Hint Resolve Nmult_Unth_prop.

Lemma Nmult_n_Unth: forall n:nat, (n */ [1/]1+n) == [1-] ([1/]1+n).
intro; apply Uinv_eq_perm_right; auto.
Save.

Lemma Nmult_Sn_Unth: forall n:nat, (S n */ [1/]1+n) == 1.
intro; rewrite (Nmult_S n ([1/]1+n)).
rewrite (Nmult_n_Unth n); auto.
Save.

Hint Resolve Nmult_n_Unth Nmult_Sn_Unth.

Lemma Nmult_ge_Sn_Unth: forall n k, (S n <= k)%nat -> (k */ [1/]1+n) == 1.
induction 1; auto.
rewrite (Nmult_S m ([1/]1+n)); rewrite IHle; auto.
Save.

Lemma Nmult_le_n_Unth: forall n k, (k <= n)%nat -> (k */ [1/]1+n) <= [1-] ([1/]1+n).
intros; apply Ule_trans with (n */ [1/]1+n); auto.
Save.

Hint Resolve Nmult_ge_Sn_Unth Nmult_le_n_Unth.


Lemma Nmult_Umult_assoc_left : forall n x y, (Nmult_def n x) -> (n*/(x*y)) == (n*/x)*y.
intros n x y; induction n; auto; intros.
destruct n; auto.
repeat rewrite Nmult_SS.
assert(Nmult_def (S n) x); auto.
setoid_rewrite (IHn H0).
assert (x <= [1-] ((S n) */ x)). 
apply Uinv_le_perm_right.
apply Ule_trans with ([1-] ([1/]1+(S n))); auto.
apply Ule_trans with ((S n) */ ([1/]1+(S n))); auto.
apply Ueq_sym; auto.
Save.

Hint Resolve Nmult_Umult_assoc_left.

Lemma Nmult_Umult_assoc_right : forall n x y, (Nmult_def n y) -> (n*/(x*y)) == (x*(n*/y)).
intros; rewrite (Umult_sym x y); rewrite (Nmult_Umult_assoc_left n y x H); auto.
Save.

Hint Resolve Nmult_Umult_assoc_right.

Lemma plus_Nmult_distr : forall n m x, (n + m */ x)== (n */ x) + (m */ x).
intros n m x; induction n; auto; intros.
rewrite plus_Sn_m.
rewrite (Nmult_S (n + m) x).
setoid_rewrite IHn.
rewrite (Nmult_S n x); auto.
Save.

Lemma Nmult_Uplus_distr : forall n x y, (n */ x + y)== (n */ x) + (n */ y).
intros n x y; induction n.
simpl; auto.
rewrite (Nmult_S n (x+y)).
rewrite IHn.
norm_assoc_right.
rewrite (Uplus_perm2 y (n */ x) (n */ y)).
rewrite <- (Nmult_S n y).
norm_assoc_left.
apply Uplus_eq_compat; auto.
Save.

Lemma Nmult_mult_assoc : forall n m x, (n * m */ x)== (n */ (m */ x)).
intros n m x; induction n; intros; auto.
simpl mult.
rewrite (plus_Nmult_distr m (n * m) x).
rewrite IHn; auto.
Save.

Lemma Nmult_Unth_simpl_left : forall n x, (S n) */ ([1/]1+n * x) == x.
intros.
rewrite (Nmult_Umult_assoc_left (S n) ([1/]1+n) x (Nmult_def_Unth n)).
rewrite (Nmult_Sn_Unth n); auto.
Save.

Lemma Nmult_Unth_simpl_right : forall n x, (S n) */ (x * [1/]1+n) == x.
intros.
rewrite (Nmult_Umult_assoc_right (S n) x ([1/]1+n) (Nmult_def_Unth n)).
rewrite (Nmult_Sn_Unth n); auto.
Save.

Hint Resolve Nmult_Unth_simpl_left Nmult_Unth_simpl_right.

Lemma Uinv_Nmult : forall k n, [1-] (k */ [1/]1+n) == ((S n) - k)  */ [1/]1+n.
intros k n; case (le_lt_dec (S n) k); intro.
rewrite (Nmult_ge_Sn_Unth l).
replace (S n - k)%nat with O; auto.
omega.
induction k; intros.
rewrite Nmult_0; rewrite Uinv_zero.
replace (S n - O)%nat with (S n); auto with arith.
rewrite (Nmult_S k ([1/]1+n)).
apply Uplus_eq_simpl_right with ([1/]1+n); auto.
apply Uinv_le_perm_right.
apply Nmult_le_n_Unth.
omega.
apply Ueq_trans with (((S n - S k) + (S O)) */ [1/]1+n).
replace ((S n - S k) + (S O))%nat with (S n - k)%nat.
apply Ueq_trans with ([1-] (k */ [1/]1+n)); auto with arith.
apply Uinv_plus_left.
apply Nmult_le_n_Unth; omega.
omega.
rewrite (plus_Nmult_distr (S n - S k) (S O) ([1/]1+n)); auto.
Save.

Lemma Nmult_neq_zero : forall n x, ~0==x -> ~0==S n */ x.
intros; rewrite (Nmult_S n x); auto.
apply Uplus_neq_zero_left; trivial.
Save.
Hint Resolve Nmult_neq_zero.


Lemma Nmult_le_simpl :  forall (n:nat) (x y:U), 
   (Nmult_def (S n) x) -> (Nmult_def (S n) y) -> (S n */ x) <= (S n */ y) -> x <= y.
intros; apply Umult_le_simpl_left with (S n */ [1/]1+n).
auto.
assert (Nmult_def (S n) ([1/]1+n)); auto.
rewrite <- (Nmult_Umult_assoc_left (S n) ([1/]1+n) x H2).
rewrite <- (Nmult_Umult_assoc_left (S n) ([1/]1+n) y H2).
rewrite (Nmult_Umult_assoc_right (S n) ([1/]1+n) y H0).
rewrite (Nmult_Umult_assoc_right (S n) ([1/]1+n) x H).
apply Ule_trans with ([1/]1+n * (S n */ x)); auto.
Save.

Lemma Nmult_Unth_le : forall (n1 n2 m1 m2:nat), 
   (n2 * S n1<= m2 * S m1)%nat -> (n2 */ [1/]1+m1 <= m2 */ [1/]1+n1).
intros.
apply Ule_trans with ((n2 * S n1) */ ([1/]1+m1 * [1/]1+n1)).
rewrite (Nmult_mult_assoc n2 (S n1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_le_compat_right.
rewrite (Nmult_Unth_simpl_right n1 ([1/]1+m1)); auto.
apply Ule_trans with ((m2 * S m1) */ [1/]1+m1 * [1/]1+n1); auto.
rewrite (Nmult_mult_assoc m2 (S m1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_le_compat_right.
rewrite (Nmult_Unth_simpl_left m1 ([1/]1+n1)); auto.
Save.

Lemma Nmult_Unth_eq : 
   forall (n1 n2 m1 m2:nat), 
   (n2 * S n1= m2 * S m1)%nat -> (n2 */ [1/]1+m1 == m2 */ [1/]1+n1).
intros.
apply Ueq_trans with ((n2 * S n1) */ ([1/]1+m1 * [1/]1+n1)).
rewrite (Nmult_mult_assoc n2 (S n1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_eq_compat.
rewrite (Nmult_Unth_simpl_right n1 ([1/]1+m1)); auto.
rewrite H.
rewrite (Nmult_mult_assoc m2 (S m1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_eq_compat.
rewrite (Nmult_Unth_simpl_left m1 ([1/]1+n1)); auto.
Save.

Hint Resolve Nmult_Unth_le Nmult_Unth_eq.

Lemma Nmult_def_lt : forall n x, n */ x <1 -> Nmult_def n x.
red; destruct n; intros; auto.
apply (Ule_total x ([1/]1+n)); intros; auto.
case H.
apply Ule_trans with (S n */ [1/]1+n); auto.
Save.

Hint Immediate Nmult_def_lt.

(** ** Tactic for simplification of goals *)

Ltac Usimpl :=  match goal with 
    |- context [(Uplus 0 ?x)]     => setoid_rewrite (Uplus_zero_left x)
 |  |- context [(Uplus ?x 0)]     => setoid_rewrite (Uplus_zero_right x)
 |  |- context [(Uplus 1 ?x)]     => setoid_rewrite (Uplus_one_left x)
 |  |- context [(Uplus ?x 1)]     => setoid_rewrite (Uplus_one_right x)
 |  |- context [(Umult 0 ?x)]     => setoid_rewrite (Umult_zero_left x)
 |  |- context [(Umult ?x 0)]     => setoid_rewrite (Umult_zero_right x)
 |  |- context [(Umult 1 ?x)]     => setoid_rewrite (Umult_one_left x)
 |  |- context [(Umult ?x 1)]     => setoid_rewrite (Umult_one_right x)
 |  |- context [(Uminus 0 ?x)]    => setoid_rewrite (Uminus_le_zero 0 x); 
                                        [apply (Upos x)| idtac]
 |  |- context [(Uminus ?x 0)]    => setoid_rewrite (Uminus_zero_right x)
 |  |- context [(Uminus ?x 1)]    => setoid_rewrite (Uminus_le_zero x 1);
                                        [apply (Unit x)| idtac]
 |  |- context [([1-] ([1-] ?x))] => setoid_rewrite (Uinv_inv x)
 |  |- context [([1-] 1)] => setoid_rewrite Uinv_one
 |  |- context [([1-] 0)] => setoid_rewrite Uinv_zero
 |  |- context [([1/]1+O)]        => setoid_rewrite Unth_zero
 |  |- context [?x^O] => setoid_rewrite (Uexp_0 x)
 |  |- context [?x^(S O)] => setoid_rewrite (Uexp_1 x)
 |  |- context [0^(?n)] => setoid_rewrite Uexp_zero; [omega|idtac]
 |  |- context [U1^(?n)] => setoid_rewrite Uexp_one
 |  |- context [(Nmult 0 ?x)]     => setoid_rewrite (Nmult_0 x)
 |  |- context [(Nmult 1 ?x)]     => setoid_rewrite (Nmult_1 x)
 |  |- context [(Nmult ?n 0)]     => setoid_rewrite (Nmult_zero n)
 |  |- context [(sigma ?f O)]     => setoid_rewrite (sigma_0 f)
 |  |- context [(sigma ?f (S O))]     => setoid_rewrite (sigma_1 f)
 |  |- (Ule (Uplus ?x ?y) (Uplus ?x ?z)) => apply Uplus_le_compat_right
 |  |- (Ule (Uplus ?x ?z) (Uplus ?y ?z)) => apply Uplus_le_compat_left
 |  |- (Ule (Uplus ?x ?z) (Uplus ?z ?y)) => setoid_rewrite (Uplus_sym z y); 
					      apply Uplus_le_compat_left
 |  |- (Ule (Uplus ?x ?y) (Uplus ?z ?x)) => setoid_rewrite (Uplus_sym x y); 
                                              apply Uplus_le_compat_left
 |  |- (Ule (Uinv ?y) (Uinv ?x)) => apply Uinv_le_compat
 |  |- (Ule (Uminus ?x ?y) (Uplus ?x ?z)) => apply Uminus_le_compat_right
 |  |- (Ule (Uminus ?x ?z) (Uplus ?y ?z)) => apply Uminus_le_compat_left
 |  |- (Ueq (Uinv ?x) (Uinv ?y)) => apply Uinv_eq_compat
 |  |- (Ueq (Uplus ?x ?y) (Uplus ?x ?z)) => apply Uplus_eq_compat_right
 |  |- (Ueq (Uplus ?x ?z) (Uplus ?y ?z)) => apply Uplus_eq_compat_left
 |  |- (Ueq (Uplus ?x ?z) (Uplus ?z ?y)) => setoid_rewrite (Uplus_sym z y); 
                                             apply Uplus_eq_compat_left
 |  |- (Ueq (Uplus ?x ?y) (Uplus ?z ?x)) => setoid_rewrite (Uplus_sym x y); 
					     apply Uplus_eq_compat_left
 |  |- (Ueq (Uminus ?x ?y) (Uplus ?x ?z)) => apply Uminus_eq_compat;[apply Ueq_refl|idtac]
 |  |- (Ueq (Uminus ?x ?z) (Uplus ?y ?z)) => apply Uminus_eq_compat;[idtac|apply Ueq_refl]
 |  |- (Ule (Umult ?x ?y) (Umult ?x ?z)) => apply Umult_le_compat_right
 |  |- (Ule (Umult ?x ?z) (Umult ?y ?z)) => apply Umult_le_compat_left
 |  |- (Ule (Umult ?x ?z) (Umult ?z ?y)) => setoid_rewrite (Umult_sym z y); 
                                             apply Umult_le_compat_left
 |  |- (Ule (Umult ?x ?y) (Umult ?z ?x)) => setoid_rewrite (Umult_sym x y); 
                                             apply Umult_le_compat_left
 |  |- (Ueq (Umult ?x ?y) (Umult ?x ?z)) => apply Umult_eq_compat_right
 |  |- (Ueq (Umult ?x ?z) (Umult ?y ?z)) =>  apply Umult_eq_compat_left
 |  |- (Ueq (Umult ?x ?z) (Umult ?z ?y)) => setoid_rewrite (Umult_sym z y); 
                                             apply Umult_eq_compat_left
 |  |- (Ueq (Umult ?x ?y) (Umult ?z ?x)) => setoid_rewrite (Umult_sym x y); 
                                             apply Umult_eq_compat_left
end.

End Univ_prop.

