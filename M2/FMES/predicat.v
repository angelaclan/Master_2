Require Import ZArith List.

Open Scope Z_scope.

(* Quelques exemples de propositions et prédicats *)

Check 1 + 1 = 2.

Compute 1 + 1 = 2.

Check 2 = 3.

Compute 2 = 3.

Check False.

Check True.

Check lt.

Check Z.lt.

Check Z.lt 5 3.
Check 5 < 3.

Check Z.ltb.

Compute Z.ltb 5 3.

Fail Definition Zmax n p := if n < p then p else n.

Definition Zmax n p := if Z.ltb n p then p else n.

Compute Zmax 5 3.

Check 5 <= Zmax 5 3.

Check forall n : Z, 0 <= n * n.

Check exists n : Z, n * n = 8.

Check forall n : Z, exists p : Z, n < p.

Check forall n : Z, n^2 <= 2^n.

Check forall n : Z, ~ n < n.

Check forall n : Z, ~In n nil.

Check ~exists n : Z, In n nil.

Check  forall n : Z, 0 <= n \/ n < 0.

Check 1 < 3 /\ 7 < 5.

Check exists n p : Z, n < p /\ p <= n.

Check forall l : list Z, l = nil \/ exists a l', l = a :: l'.

Check forall n m : Z, n < m <-> Z.ltb n m = true.
(*math relation = program comperation *)
Check forall l1 l2 : list Z, forall z:Z, In z (l1 ++ l2) <-> In z l1 \/ In z l2.

Definition is_square_root (n r : Z) := r * r <= n < (r+1)*(r+1).

Check is_square_root 9 3.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
match l with
| nil => False
| y :: l' => y = x \/ In x l'
end.

(* 1 : Définir les prédicats suivants

  Par défaut, les nombres sont de type  Z  et les listes de type  list Z

  Pour les listes, vous pouvez utiliser les fonction prédéfinies telles que
  length,  rev,  nth, etc. Attention à l'argument additionnel de  nth
  fournissant une valeur par défaut. *)

(* 1a) Le nombre  b  est un diviseur du nombre  a. *)

Definition divides (b a : Z) : Prop := 
exists z:Z, a = b * z.

Check divides 10 5.
Compute divides 10 5.

(* 1b) n  est un nombre premier. *)

Definition is_prime (n : Z) : Prop := n >=2 -> forall m , divides m n -> (m = 1 \/ m = n).


(* 1c) d  est le plus petit diviseur premier de  n. ex: 69 -> 3, 44 -> 2 *)

Definition least_prime_divisor (d n : Z) : Prop :=
is_prime d /\ divides d n /\ (forall z:Z, is_prime z /\ divides z n /\ d <= z).


(* 1d) La racine carrée de  n  est rationnelle (c.-à-d. une fration). *)

Definition rational_sqrt (n : Z) : Prop :=
exists a b :Z, ~a = 0 /\ ~b = 0 /\ n*a*a = b*b.


(* 1e) La liste  l  est un palindrome (c.-à-d. égale à son inverse).
       En donner deux définitions :
       une utilisant  rev, l'autre utilisant  nth. *)

Definition palindromic_v1 (l : list Z) : Prop := l = rev l.

Check nth.

Definition palindromic_v2 (l : list Z) : Prop := 
forall i:nat, (i < length l)%nat -> nth i l  0 = nth (length l-i-1) l 0.
(* %nat means everything declared in the () is transformed to nat *)


(* 1f) La liste  l  est triée.
       En donner trois définitions :
       * une non-récursive en utilisant  nth,
       * une non-récursive sans utiliser  nth,
       * une récursive. *)

Definition sorted_v1 (l:list Z) : Prop :=
forall i:nat, (i < length l)%nat -> nth i l 0 <= nth (i + 1) l 0.

Definition sorted_v2 (l:list Z) : Prop :=
forall l' l'' : list Z, forall a b : Z, l = (l' ++ a::b ::l'') /\ a <= b.
(* a::b::nil  and  l' ++ l'' *)

Fixpoint sorted_v3 (l:list Z) : Prop := 
match l with a::(b::l' as l'') =>
a <= b /\ sorted_v3 l''
| _ => True end.

(*1g) x  est plus petit que ou égal à chaque élément de la liste  l *)

Definition less_than_all (x : Z) (l : list Z) : Prop :=
forall a : Z, In a l -> x <= a.

(*    Puis utiliser ce prédicat pour définir une nouvelle version récursive de
      sorted *)

Definition sorted_v4 (l:list Z) : Prop.


(* 1h) La liste  l  est la décomposition en facteurs premiers de  n
       En donner deux versions :
       * une non-récursive utilisant une fonction  product  qui  calcule le
         produit des éléments d'une liste,
         l'autre récursive n'utilisant pas  product. ex: 2*3*5 = 30 *)

Definition product (l : list Z) : Z.


Definition prime_decomp_v1 (n : Z) (l : list Z) : Prop.
Admitted.

Definition prime_decomp_v2 (n : Z) (l : list Z) : Prop.
Admitted.

(* 2 : Traduire en Coq les énoncés suivants
       S'ils sont ambiguës ou incomplets, précisez-les. *)

(* 2a) Tout entier a une unique décomposition en facteurs premiers *)

Definition exist_unique_prime_decomp : Prop.
Admitted.

(* 2b) La conjecture de Goldbach : Tout nombre pair plus grand que 3 est la
       somme de deux nombres premiers *)

Definition goldbach : Prop.
Admitted.

(* 2c) Une liste palindrome triée est la répétition du même nombre *)

Definition sorted_palindrom_constant : Prop.
Admitted.

(* 3 Spécification d'une fonction *)

(* 3a) La liste  l  n'a pas d'éléments dupliqués. *)
Definition NoDuplicate (l : list Z) : Prop.
Admitted.

(* 3b) La fonction f enlève les éléments dupliqués d'une liste. *)
Definition DeduplicateSpec (f : list Z -> list Z) : Prop.
Admitted.

(* 4 La suite de Syracuse *)

(* Considérons la fonction :
   Step(x) = x/2 si x est pair
           = 3x+1 si x est impair.
  Elle calcule la valeur suivant de la liste.
  Par exemple en partant de 3 :
  3, 10, 5, 16, 8, 4, 2, 1, 4, 2, 1, ... *)

(* 4a) Définir le prédicat  SyracuseStep  tel que
       SyracuseStep x y  signifie que
       * y  est la moitié de  x  quand  x est pair, ou
       * y vaut 3x+1 quand x est impair. *)

Open Scope nat_scope.

Definition SyracuseStep (x y : nat) : Prop.
Admitted.

(* 4b) Définir le prédicat  SyracuseSequence  tel que 
       SyracuseSequence f  signifie  que  f n  vaut la n-ième valeur de la 
       séquence, c.-à-d. f 1 = Step (f 0), f 2 = Step (f 1), etc. *)

Definition SyracuseSequence (f : nat -> nat) : Prop.
Admitted.

(* 4c) Ecrire la conjecture de Syracuse : Partant d'un nombre strictement
       positif, la séquence finit par atteindre 1. *)

Definition SyracuseConjecture : Prop.
Admitted.
