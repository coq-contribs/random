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


(** * Monads.v: Monads for randomized constructions *)

Set Implicit Arguments.
Require Export Uprop.

Module Monad (Univ:Universe).
Module UP := (Univ_prop Univ).
(* begin hide *)
Import Univ.
Import UP.
(* end hide *)
(** ** Definition of monadic operators *)
Definition M (A:Type) := (A -> U) -> U.

Definition unit (A:Type) (x:A) : M A := fun f => f x.

Definition star (A B:Type) (a:M A) (F:A -> M B) : M B := fun f => a (fun x => F x f).

(** ** Properties of monadic operators *)
Lemma law1 : forall (A B:Type) (x:A) (F:A -> M B) (f:B -> U), star (unit x) F f = F x f.
trivial.
Qed.

Lemma law2 :
 forall (A:Type) (a:M A) (f:A -> U), star a (fun x:A => unit x) f = a (fun x:A => f x).
trivial.
Qed.

Lemma law3 :
 forall (A B C:Type) (a:M A) (F:A-> M B) (G:B-> M C) 
   (f:C->U), star (star a F) G f = star a (fun x:A => star (F x) G) f.
trivial.
Qed.

(** ** Properties of distributions *)
(** *** Extension to functions of basic operations *)
Definition fle (A:Type) (f g:A->U) : Prop := forall x:A, (f x) <=  (g x).
Definition feq (A:Type) (f g:A->U) : Prop := forall x:A, (f x) ==  (g x).
Hint Unfold fle feq.
Definition fplus (A:Type) (f g:A->U) (x:A) : U := (f x) + (g x).
Definition finv (A:Type) (f:A->U) (x:A) : U := Uinv (f x).
Definition fmult (A:Type) (k:U) (f:A->U) (x:A) : U := k * (f x).
Definition f_one (A:Type) (x : A) : U := U1.
Definition f_zero (A:Type) (x : A) : U := U0.
Definition f_cte (A:Type) (c:U) (x : A) : U := c.

Implicit Arguments f_one [].
Implicit Arguments f_zero [].
Implicit Arguments f_cte [].

(** *** Expected properties of measures *)
Definition monotonic (A:Type) (m:M A) : Prop := forall f g:A->U, fle f g -> (m f) <= (m g).

Definition stable_eq (A:Type) (m:M A) : Prop :=  forall f g:A->U, feq f g -> (m f) == (m g).

Definition stable_inv (A:Type) (m:M A) : Prop := forall f :A->U, m (finv f) <= Uinv (m f).

Definition fplusok (A:Type) (f g : A -> U) := fle f (finv g).
Hint Unfold fplusok.

Definition stable_plus (A:Type) (m:M A) : Prop :=
  forall f g:A->U, fplusok f g -> m (fplus f g) == (m f) + (m g).

Definition stable_mult (A:Type) (m:M A) : Prop :=
  forall (k:U) (f:A -> U), m (fmult k f) == Umult k (m f).

(** *** Monotonicity *)
Lemma unit_monotonic : forall (A:Type) (x:A), monotonic (unit x).
red in |- *; unfold unit, fle in |- *; auto.
Qed.

Lemma star_monotonic : forall (A B:Type) (m:M A) (F:A -> M B),
   monotonic m -> (forall a:A, monotonic (F a)) -> monotonic (star m F).
unfold monotonic, star in |- *; intros.
apply H.
red in |- *; auto.
Qed.

(** *** Stability for equality *)
Lemma monotonic_stable_eq : forall (A:Type) (m:M A), (monotonic m) -> (stable_eq m).
red; unfold monotonic, fle.
intros; apply Ule_antisym; auto.
Save.
Hint Resolve monotonic_stable_eq.

Lemma unit_stable_eq : forall (A:Type) (x:A), stable_eq (unit x).
intros; apply monotonic_stable_eq.
apply unit_monotonic; auto.
Qed.

Lemma star_stable_eq : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_eq m -> (forall a:A, stable_eq (F a)) -> stable_eq (star m F).
unfold stable_eq, star in |- *; auto.
Qed.

(** *** Stability for inversion *)
Lemma unit_stable_inv : forall (A:Type) (x:A), stable_inv (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_stable_inv : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_inv m ->  monotonic m 
   -> (forall a:A, stable_inv (F a)) -> (forall a:A, monotonic (F a))
   -> stable_inv (star m F).
unfold stable_inv in |- *; intros.
unfold star in |- *.
apply Ule_trans with (m (finv (fun x:A => F x f))); trivial.
apply H0.
intros x; apply (H1 x f).
Save.

(** *** Stability for addition *)
Lemma unit_stable_plus : forall (A:Type) (x:A), stable_plus (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_stable_plus : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_plus m -> stable_eq m -> 
   (forall a:A, forall f g, fplusok f g -> (F a f) <= Uinv (F a g))
   -> (forall a:A, stable_plus (F a)) -> stable_plus (star m F).
unfold stable_plus in |- *; intros.
unfold star in |- *.
apply Ueq_trans with (m (fplus (fun x:A => F x f) (fun x:A => F x g))); trivial.
apply H0.
intros x; apply (H2 x f g H3).
apply H.
repeat red.
unfold finv; intros; auto.
Qed.

(** *** Stability for product *)
Lemma unit_stable_mult : forall (A:Type) (x:A), stable_mult (unit x).
red in |- *; intros.
unfold unit in |- *; auto.
Qed.

Lemma star_stable_mult : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_mult m -> stable_eq m -> (forall a:A, stable_mult (F a)) -> stable_mult (star m F).
unfold stable_mult in |- *; intros.
unfold star in |- *.
apply Ueq_trans with (m (fmult k (fun x:A => F x f))); trivial.
apply H0.
intro.
unfold fmult at 2 in |- *; trivial.
Qed.

End Monad.

