Require Import Arith List.
Import Bool Nat.

Check 3.

Check 2 + 3.

Check (2 + 3) + 4.

Check 2 + (3 + 4).

(* La fonction suivante prend deux arguments  x  et  y  de type  nat
   et retourne  a * a + 2 * a * b + b * b. *)
Definition f_ex (a b : nat) := a * a + 2 * a * b + b * b.

Check f_ex.

Check f_ex 5.

Compute f_ex 1 2.

(* Le filtrage par motif permet d'accéder aux composants d'une paire. *)
Definition somme_paire (p : nat * nat) :=
match p with (x, y) => x + y end.

Compute somme_paire (3 , 7).

(* Définir une fonction qui prend deux entiers naturels en arguments et
   retourne la somme de leurs carrés *)
Definition somme_carre (a b : nat) :nat :=
match a with 0 => 
  match b with 0 => 0
  | _ => b * b end
| _ => a * a + b * b end.

Compute somme_carre 2 3.

(* Définir une fonction qui prend cinq entiers naturels en arguments et
   retourne leur somme *)
Definition somme_five (a b c d e : nat) :nat :=
a + b + c + d + e.

Compute somme_five 5 6 8 2 3.

(* Définir une fonction qui ajoute 3 à son argument *)
Definition add3 (x : nat) : nat :=
match x with 0 => 3
| n => n + 3 end.

Compute add3 0.
Compute add3 889.
(* La commande suivante devrait afficher 10 *)
Compute add3 7.

(* Les commandes suivantes permettent de chercher des fonctions pré-définies. *)
Search nat.
Search bool.

(* Définir une fonction  swap  qui échange les deux premiers éléments d'une
   liste, c'est-à-dire telle que
   swap (a::b::l) = (b::a::l)  et
   swap l = l  si  l'  a moins de deux éléments. *)
Definition swap (l : list nat) : list nat :=
match l with (a::b::l') => (b::a::l')
| _ => l end.
  
Compute swap (1::2::3::4::nil).

(* Définir une fonction  secondPlus3  qui ajoute 3 au deuxième élément d'une
   liste et le retourne, c'est-à-dire telle que
   secondPlus3 (a::b::l) = b + 3  et
   secondPlus3 l = 0  if  l  a moins de deux éléments.
   length: forall A : Type, list A -> nat
 *)
Definition secondPlus3 (l : list nat) : nat :=
match l with(a::b::l') => b + 3
| _ => 0 end.

Compute secondPlus3 (5::8::nil).
Compute secondPlus3 (5::8::1::2::3::4::nil).
Compute secondPlus3 (5::nil).
Compute secondPlus3 (5::0::1::2::3::4::nil).

(* Définir une fonction qui ajoute 2 à tous les éléments d'une liste *)
Fixpoint list_add2 (l : list nat) : list nat :=
match l with (a::l') => (a + 2)::list_add2 l'
| _ => l end.

Compute list_add2 (5::8::1::2::3::4::nil).
Compute list_add2 (5::nil).

(* Définir une fonction qui teste su une liste est triée par ordre croissant *)
Fixpoint sorted (l : list nat) : bool :=
match l with (a::l') => 
  match l' with (b::l'') => (a <=? b) && sorted l'
  | _ => true end 
| _ => true end.

Compute sorted (5::8::1::2::3::4::nil).
Compute sorted (1::2::3::4::nil).
Compute sorted (0::1::2::3::4::nil).

(* Définir une fonction  power2  telle que  power2 n = 2 ^ n *)
Fixpoint power2 (n : nat) : nat :=
match n with 0 => 1
| S n' => 2 * power2 n' end.

Compute power2 4.
Compute power2 0.
Compute power2 8.

(* Définir une fonction  salt  telle que
   salt x n = x^n - x^(n-1) + x^(n-2) - ... (+ ou -) 1
   Par exemple :
   salt x 3 = x^3 - x^2 + x - 1
   salt x 4 = x^4 - x^3 + x^2 - x + 1
   salt 2 3 = 5

   Indice : Vous pourriez avoir besoin d'une fonction intermédiaire. *)
Fixpoint even ( a : nat) : bool :=
match a with 0 => false
| 1 => true
| S (S b) => even b end.

Fixpoint powerX (x n : nat) : nat :=
match n with 0 => 1
| S n' => x * powerX x n' end.

Fixpoint salt (x n : nat) : nat :=
match n with 0 => 1
| S n' => x ^ n - salt x n'
end.
 
Compute salt 2 4.


(* Arbres binaires *)
Inductive tree : Type := leaf | node (n : nat) (t1 t2 : tree).

Example myTree :=
node 8
  (node 3
    (node 1
      leaf
      leaf
    )
    (node 6
      (node 4
        leaf
        leaf
      )
      (node 7
        leaf
        leaf
      )
    )
  )
  (node 10
    leaf
    (node 14
      (node 13
        leaf
        leaf
      )
      leaf
    )
  ).

(* Définir une fonction qui renvoie la listes des étiquettes d'un arbre
   binaire
   Indice : vous pouvez utiliser la fonction  app qui concaténe deux listes. *)

Fixpoint labels (t : tree) : list nat:=
match t with leaf => nil
| _ => node n leaf leaf =>

end.

(* Définir une fonction qui teste si elle a affaire à un arbre binaire de
   recherche. *)
Definition searchTree (t : tree) : bool.
Admitted.

Compute searchTree myTree.
