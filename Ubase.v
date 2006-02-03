(** * Ubase.v: Specification of $U$, interval $[0,1]$ *)

Require Export Setoid.
Require Export Prelude.
Set Implicit Arguments.

(** ** Specification of $U$ *)
(** - Constants : $0$ and $1$
    - Constructor : [Unth] $n (\equiv \frac{1}{n+1})$
    - Operations : $x+y~(\equiv min (x+y,1))$, $x*y$, [inv] $x~(\equiv 1 -x)$
    - Relations : $x\leq y$, $x==y$
*)
Module Type Universe.
Parameter U : Type.
Bind Scope U_scope with U.
Delimit Scope U_scope with U.

Parameters Ueq Ule : U -> U -> Prop.
Parameters U0 U1 : U.
Parameters Uplus Umult : U -> U -> U.
Parameter Uinv : U -> U.
Parameter Unth : nat -> U.

Infix "+" := Uplus  : U_scope.
Infix "*" := Umult  : U_scope.
Infix "==" := Ueq (at level 70) : U_scope.
Infix "<=" := Ule : U_scope.
Notation "[1-]  x" := (Uinv x)  (at level 35, right associativity) : U_scope.
Notation "0" := U0 : U_scope.
Notation "1" := U1 : U_scope.
Notation "[1/]1+ n" := (Unth n) (at level 35, right associativity) : U_scope.
Open Local Scope U_scope.

(** *** Properties *)
Hypothesis Ueq_refl : forall x:U, x == x.
Hypothesis Ueq_sym : forall x y:U, x == y -> y == x.

Hypothesis Udiff_0_1 : ~0 == 1.
Hypothesis Upos : forall x:U, 0 <= x.
Hypothesis Unit : forall x:U, x <= 1.

Hypothesis Uplus_sym : forall x y:U, (x + y) == (y + x).
Hypothesis Uplus_assoc : forall x y z:U, (x + (y + z)) == (x + y + z).
Hypothesis Uplus_zero_left : forall x:U, (0 + x) == x.

Hypothesis Umult_sym : forall x y:U, (x * y) == (y * x).
Hypothesis Umult_assoc : forall x y z:U, (x * (y * z)) == (x * y * z).
Hypothesis Umult_one_left : forall x:U, (1 * x) == x.

Hypothesis Uinv_one : [1-] 1 == 0. 
Hypothesis Uinv_opp_left : forall x, [1-] x + x == 1.

(** Property  : $1 - (x+y) + x=1-y$ holds when $x+y$ does not overflow *)
Hypothesis Uinv_plus_left : forall x y, y <= [1-] x -> [1-] (x + y) + x == [1-] y.

(** Property  : $(x + y) \times z  = x \times z + y \times z$ 
    holds when $x+y$ does not overflow *)
Hypothesis Udistr_plus_right : forall x y z, x <= [1-] y -> (x + y) * z == (x * z + y * z).

(** Property  : $1 - (x \times y) = (1 - x)\times y + (1-y)$ *)
Hypothesis Udistr_inv_right : forall x y:U,  [1-] (x * y) == ([1-] x) * y + [1-] y.

(** The relation $x\leq y$ is reflexive, transitive and anti-symmetric *)
Hypothesis Ueq_le : forall x y:U, x == y -> x <= y.

Hypothesis Ule_trans : forall x y z:U, (x <= y) -> (y <= z) -> (x <= z).

Hypothesis Ule_antisym : forall x y:U, (x <= y) -> (y <= x) -> (x == y).

(** Totality of the order *)
Hypothesis Ule_class : forall x y : U, class (x <= y).

Hypothesis Ule_total : forall x y : U, orc (x<=y) (y<=x).
Implicit Arguments Ule_total [].

(** The relation $x\leq y$ is compatible with operators *)
Hypothesis Uplus_le_compat_left : forall x y z:U, x <= y -> (x + z) <= (y + z).

Hypothesis Umult_le_compat_left : forall x y z:U, x <= y -> (x * z) <= (y * z).

Hypothesis Uinv_le_compat : forall x y:U, x <= y -> [1-] y <= [1-] x.

(** Properties of simplification in case there is no overflow *)
Hypothesis Uplus_le_simpl_right : forall x y z, z <= [1-] x -> (x + z) <= (y + z) -> x <= y.

Hypothesis Umult_le_simpl_left : forall x y z: U, ~0 == z -> (z * x) <= (z * y) -> x <= y .

(** Property [Unth] $\frac{1}{n+1} == 1 - n \times \frac{1}{n+1}$ *)
Hypothesis Unth_prop : forall n, [1/]1+n == [1-](comp Uplus 0 (fun k => [1/]1+n) n).

(** *** Archimedian property *)
Hypothesis archimedian : forall x, ~x == 0 -> exists n, [1/]1+n <= x.

(** *** Least upper bound, corresponds to limit for increasing sequences *)
Variable lub : (nat -> U) -> U.

Hypothesis le_lub : forall (f : nat -> U) (n:nat), (f n) <= (lub f).
Hypothesis lub_le : forall (f : nat -> U) (x:U), (forall n, f n <= x) -> (lub f) <= x.

(** *** Stability properties of lubs with respect to [+] and [*] *)
Hypothesis lub_eq_plus_cte_right : forall (f:nat->U) (k:U), lub (fun n => (f n) + k) == (lub f) + k.

Hypothesis lub_eq_mult : forall (k:U) (f:nat->U), lub (fun n => (k * (f n))) ==  k * lub f.

End Universe.

