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


Set Implicit Arguments.

(** * Preliminaries *)
(** ** Definition of iterator [comp]
   [comp f u n x] is defined as $(f~(u~(n-1)).. (f (u~ 0)~x))$ *)

Fixpoint comp (A:Type) (f : A -> A -> A) (x : A) (u : nat -> A) (n:nat) {struct n}: A := 
   match n with O => x| (S p) => f (u p) (comp f x u p) end.
      
Lemma comp0 : forall (A:Type) (f : A -> A -> A) (x : A) (u : nat -> A), comp f x u 0 = x.
trivial.
Save.

Lemma compS : forall (A:Type) (f : A -> A -> A) (x : A) (u : nat -> A) (n:nat),
              comp f x u (S n) = f (u n) (comp f x u n).
trivial.
Save.

(** ** Monotonicity of sequences for an arbitrary relation *)
Definition mon_seq (A:Type) (le : A -> A -> Prop) (f:nat ->A) 
  :=  forall n m, (n <= m) -> (le (f n) (f m)).

Definition decr_seq (A:Type) (le : A -> A -> Prop) (f:nat ->A) 
  :=  forall n m, (n <= m) -> (le (f m) (f n)).


(** ** Reducing if constructs *)

Lemma if_then : forall (P:Prop) (b:{P}+{~P})(A:Type)(p q:A),P->(if b then p else q) =p.
destruct b; simpl; intuition.
Save.

Lemma if_else : forall (P:Prop) (b:{P}+{~P})(A:Type)(p q:A),~P->(if b then p else q) =q.
destruct b; simpl; intuition.
Save.

(** ** Classical reasoning *)

Definition class (A:Prop) := ~ ~ A -> A.

Lemma class_neg : forall A:Prop, class (~A).
unfold class; intuition.
Save.

Lemma class_false : class False.
unfold class; intuition.
Save.
Hint Resolve class_neg class_false.

Definition orc (A B:Prop) := forall C:Prop, class C -> (A ->C)->(B->C)->C.

Lemma orc_left : forall A B:Prop, A -> (orc A B).
red;intuition.
Save.

Lemma orc_right : forall A B:Prop, B -> (orc A B).
red;intuition.
Save.

Hint Resolve orc_left orc_right.

Lemma class_orc : forall A B, class (orc A B).
repeat red; intros.
apply H0; red; intro.
apply H; red; intro. 
apply H3; apply H4; auto.
Save.

Lemma class_and : forall A B, class A -> class B -> class (A /\ B).
unfold class; intuition.
Save.

Lemma excluded_middle : forall A, orc A (~A).
red; intros.
apply H; red; intro.
intuition.
Save.

Hint Resolve class_orc class_and excluded_middle.
