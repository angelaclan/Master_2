Require Import Arith.

Fixpoint add (m n : nat) : nat := 
match m with
| 0 => n
| S m' => add m' (S n)
end.

(*
Pour simplfier une expression :
cbn. = call by name

Pour prouver un but de la forme  t = t :
reflexivity

Pour utiliser une égalité  H :
rewrite H
rewrite <- H

Si vous avec une égalité  H : S t1 = S t2  vous pouvez en déduire  t1 = t2 en
utilisant la tactique  injection H (parceque les constructeurs dans les
définitions inductives sont injectifs).

Pour faire une analyse de cas sur une expression  e :
destruct e
case_eq e
case e

Pour faire une preuve par récurrence sur un entier naturel  n :
induction n as [ | n' IH]

Pour remplacer un terme par un autre terme égal (par simplification) :
Exemple : change (0 + x) with x

Pour remplacer un terme  t1  par un terme  t2
et générer un nouveau but  t1 = t2 :
replace t1 with t2

Si il y a la variable  x  dans le contexte,  revert x  permet de la mettre dans
le but. C'est parfois utile pour généraliser un but avant d'appeler  induction
et ainsi obtenir une hypothèse d'induction plus forte.
*)

Lemma add_S_r : forall m n, add m (S n) = S (add m n).
Proof.
induction m as [ | m' IH].
- intro n.
  cbn.
  reflexivity.
- intro n1.
  cbn.
  apply IH.
Qed.

(* Prouver les lemmes suivants. Pour prouver chaque lemme, vous pouvez
   réutiliser les lemmes que vous avez prouvés précédemment. *)

Lemma add_0_r : forall n, add n 0 = n.
Proof.
induction n as [ | n' IH].
- cbn.
  reflexivity.
- cbn.
  rewrite add_S_r.
  rewrite IH.
  reflexivity.
Qed.


Lemma add_comm : forall m n, add m n = add n m.
Proof.
induction m as [ | m' IH].
- cbn.
  intro n1.
  rewrite add_0_r.
  reflexivity.
- intro n2.
  apply IH.
Qed.

Lemma add_assoc : forall m n p, add m (add n p)= add (add m n) p.
Proof.
induction m as [ | m' IH].
- intros n1 p.
  cbn.
  reflexivity.
- intros n p.
  cbn.
  rewrite add_S_r. 
  rewrite add_S_r.
  cbn.
  rewrite add_S_r.
  rewrite IH.
  reflexivity.
Qed.

Lemma add_plus : forall m n, add m n = m + n.
Proof.
induction m as [ | m' IH].
- intro n.
  cbn.
  reflexivity.
- intro n.
  cbn.
  rewrite add_S_r.
  rewrite IH.
reflexivity.
Qed.


(*
A partir de ce point, nous utilisons l'addition de la librairie standard de Coq:
plus (notée '+')
 *)

Require Import List ZArith.

Fixpoint multiplicity (n : Z) (l : list Z) : nat := 
match l with 
| nil => 0
| m::l' => if Z.eqb n m then S (multiplicity n l') else multiplicity n l' 
end.

Compute multiplicity 0 (1::2::3::nil)%Z.


Definition is_perm (l l':list Z) : Prop :=
forall n, multiplicity n l = multiplicity n l'.

Check is_perm (2::3::2::nil)%Z (1::2::3::nil)%Z.


Lemma multiplicity_app (n : Z) (l1 l2 : list Z) :
multiplicity n (l1++l2) = multiplicity n l1 + multiplicity n l2.
Proof. 
(* revert = take elem from hypothesis to goal *)
revert n l2.
induction l1.
- cbn.
  reflexivity.
- intros n l2.
  cbn. 
  destruct (n =? a)%Z.
  + rewrite IHl1.
    cbn.
    reflexivity.
  + apply IHl1.
Qed.

(* reverse list gives the same result *)
Lemma multiplicity_rev : forall n l, multiplicity n (rev l) = multiplicity n l.
Proof.
intros n l.
revert n.
induction l.
- cbn.
  reflexivity.
- cbn.
  intro n.
  case_eq (n =? a)%Z.
  + intro H.
    rewrite multiplicity_app.
    cbn.
    rewrite H.
    rewrite <- IHl.
    rewrite <- add_plus.
    rewrite add_S_r.
    rewrite add_0_r.
    reflexivity.


Admitted.

Require Import Lia. (* Ajoute la tactique  lia  permettant de prouver
                       automatiquement certains buts arithmétiques. *)

Lemma is_perm_transpose :
forall x y l1 l2 l3, is_perm (l1++x::l2++y::l3) (l1++y::l2++x::l3).
Proof.
Admitted.

(* Que fait cette fonction ? *)
Fixpoint mask {A : Type} (m : list bool) (s : list A) {struct m} :=
match m, s with
| b :: m', x :: s' => if b then x :: mask m' s' else mask m' s'
| _, _ => nil
end.

Lemma mask_cat A m1 (s1 : list A) :
length m1 = length s1 ->
forall m2 s2, mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
Proof.
Admitted.
