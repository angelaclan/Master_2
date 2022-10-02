(* David Nowak *)

(* Quand le but est de la forme ... utiliser la tactique ...

P /\ Q
split

P \/ Q
left
right

P -> Q
intro H

P <-> Q
split

~P
intro H
contradict H

but déja dans les hypothèses
exact H (où H est le nom de l'hypothèse)
assumption

False
contradict H (où H est une hypothèse contradictoire)

True
trivial

forall x, P
intro x

exists x, P
exists t
*)

(* Pour utiliser une hypothèse H de la forme ... utiliser la tactique ...

P /\ Q
destruct H as [H1 H2]

P \/ Q
destruct H as [H1 | H2]

P -> Q
apply H

P <-> Q
apply H
destruct H as [H1 H2]

~P
apply H

False
destruct H
contradiction

True
clear H (car inutile)

forall x, P
apply H

exists x, P
destruct H as [x H]

t = u
rewrite H
rewrite <- H
*)

(* La tactique  assert  permet de poser un résultat intermédiaire. *)

(* Prouver les lemmes suivants en utilisant les tactiques élémentaires décrites
   ci-dessus. *)

Section MinimalPropositionalLogic.

Variables P Q R S : Prop.

Lemma imp_dist : (P -> (Q -> R)) -> (P -> Q) -> P -> R.
Proof.
intros H1 H2 p.
apply H1.
- exact p.
- apply H2.
  assumption.
Show Proof.
Qed.

Lemma imp_dist' : (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
intros H1 H2 p.
apply H1; [exact p | apply H2; assumption].
Show Proof.
Qed.

Definition imp_dist'' : (P -> Q -> R) -> (P -> Q) -> P -> R :=
fun (H1 : P -> Q -> R) (H2 : P -> Q) (p : P) => H1 p (H2 p).

Lemma id_P : P -> P.
Proof.
intros H.
apply H.
Qed.

Lemma id_PP : (P -> P) -> P -> P.
Proof.
intros H1 p.
exact p.
Qed.


Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
intros H1 H2 p.
apply H2.
apply H1.
- exact p.
Qed.


Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
Proof.
intros H1 q p.
apply H1.
- exact p.
- exact q.
Qed.


Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
intros H1 p q.
apply H1.
- exact p.
Qed.


Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
intros H1 p.
apply H1.
- exact p.
- assumption.
Qed.

Lemma delta_impR : (P -> Q) -> P -> P -> Q.
Proof.
intros H1 p q.
apply H1.
exact p.
Qed.


Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
intros H1 H2 H3 p.
apply H3.
- apply H1.
exact p.
- apply H2.
assumption.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
intros H1.
apply H1.
intros H2.
apply H2.
intros p.
apply H1.
intros H3.
apply p.
Qed.

Check weak_peirce.

End MinimalPropositionalLogic.

Check weak_peirce.

Section PropositionalLogic.

Variables P Q R S T : Prop.

Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
intros H1.
destruct H1.
destruct H0.
split.
split.
apply H.
apply H0.
apply H1.
Qed.
(*split is for goals; destruct is for hypothesis *)



Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
Proof.
intros H1.
destruct H1.
split.
apply H.
destruct H1.
apply H1.
apply H0.
destruct H1.
apply H2.
Qed.

Lemma not_contrad :  ~(P /\ ~P).
Proof.
intros H.
destruct H.
contradict H0.
apply H.
Qed.

Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
Proof.
intros H1.
destruct H1.
destruct H as [H2 | H1].
contradiction.
apply H1.
Qed.


Lemma not_not_exm : ~ ~ (P \/ ~ P).
Proof.
intros H.
apply H.
right.
intros p.
apply H.
left.
apply p.
Qed.



Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
Proof.
intros H.
split.
intros p.
apply H.
left.
apply p.
intros q.
apply H.
right.
apply q.
Qed.

Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
Proof.
intros H.
intros H1.
destruct H as [h1 h2].
destruct H1 as [h3 | h4].
apply h1.
apply h3.
apply h2.
apply h4.
Qed.

Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
Proof.
intros H.
intros H1.
destruct H as [h1 | h2].
destruct H1 as [h3 h4].
apply h1.
apply h3.
apply h2.
destruct H1.
apply H0.
Qed.


Lemma or_to_imp : P \/ Q -> ~ P -> Q.
Proof.
intros H H1.
destruct H.
contradiction.
(*in hypothesis, contradiction can be applied*)
apply H.
Qed.


Lemma imp_to_not_not_or : (P -> Q) -> ~~(~P \/ Q).
Proof.
tauto.
Qed.


Lemma contraposition : (P -> Q) -> (~Q -> ~P).
Proof.
intros H.
intros H1.
intros p.
destruct H1.
apply H.
apply p.
Qed.

Lemma contraposition' : (~P -> ~Q) <-> (~~Q -> ~~P).
Proof.
(* the left part *)
(*split.
intros H.
intros H1 p.
contradict H1.
apply H.
apply p.*)
(* the right part *)
Admitted.



Lemma contraposition'' : (~P -> ~Q) <-> ~~(Q -> P).
Proof.
split.
intros H H1.
destruct H.
intros p .
contradict p.
intros H2.
apply H1.
contradict H1.
intros q.
Admitted.

Section S0.

Hypothesis HPR : P -> R.

Hypothesis HnPR : ~P -> R.

Lemma weak_exm : ~~R.
Proof.
Admitted.

End S0.

End PropositionalLogic.
