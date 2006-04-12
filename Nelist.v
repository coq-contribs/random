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


(** * Nelist.v: A general theory of non empty lists on Type *)

Set Implicit Arguments.
Set Strict Implicit.

Section NELIST.

Variable A : Type.

Inductive nelist : Type := 
    singl : A -> nelist | add : A -> nelist -> nelist.

Definition hd (l:nelist) : A := 
     match l with (singl a) => a | (add a _) => a end.

Fixpoint app (l m : nelist) {struct l} : nelist := 
    match l with (singl a) => add a m | (add a l1) => add a (app l1 m) end.

Fixpoint rev_app (l m : nelist) {struct l} : nelist := 
    match l with (singl a) => add a m | (add a l1) => rev_app l1 (add a m) end.

Definition rev (l:nelist) : nelist := 
   match l with (singl a) => l | (add a l1) => rev_app l1 (singl a) end.

Lemma app_assoc : forall l1 l2 l3, app l1 (app l2 l3) = app (app l1 l2) l3.
intros; induction l1; simpl; auto.
rewrite IHl1; auto.
Save.

Hint Resolve app_assoc.

Lemma rev_app_rev : forall l m, rev_app l m = app (rev l) m.
induction l; simpl; intros; auto.
rewrite IHl.
rewrite IHl.
rewrite <- app_assoc; trivial.
Save.

Hint Resolve rev_app_rev.

Lemma rev_app_app_rev : forall l m, rev (rev_app l m) = app (rev m) l.
induction l; intros;simpl; auto.
rewrite IHl; simpl.
rewrite rev_app_rev.
rewrite <- app_assoc; trivial.
Save.

Lemma rev_rev : forall l, rev (rev l) = l.
destruct l; simpl; intros; auto.
rewrite rev_app_app_rev; trivial.
Save.

Lemma rev_app_distr : forall l m, rev (app l m) = app (rev m) (rev l).
induction l; intros;simpl; auto.
rewrite rev_app_rev.
rewrite rev_app_rev.
rewrite IHl; auto.
Save.

Hint Resolve rev_rev rev_app_distr.

Lemma hd_app : forall l m, hd (app l m) = hd l.
destruct l; simpl; auto.
Save.

Hint Resolve hd_app.

Lemma hd_rev_add : forall a l, hd (rev (add a l)) = hd (rev l).
simpl; intros.
rewrite rev_app_rev; auto.
Save.
Hint Resolve hd_rev_add.

End NELIST.

