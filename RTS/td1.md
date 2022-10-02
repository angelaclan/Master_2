- [Analyse d'ordonnançement temps réel](#org87bffd7)
  - [Fixed priority et Hyperplanes](#orgc7fe985)
  - [Calcul du temps de reponse](#org1819930)
- [Programmation temps-réel](#orgc01a837)
  - [Code optionnel](#orgb91e455)



<a id="org87bffd7"></a>

# Analyse d'ordonnançement temps réel


<a id="orgc7fe985"></a>

## Fixed priority et Hyperplanes

Considérez le système temps réel suivante (ordonnanceur: *Fixed Priority* avec *Deadline Monotonic*)

| Task     | C | T  | D  |
|-------- |--- |--- |--- |
| $\tau_1$ | 1 | 5  | 5  |
| $\tau_2$ | 2 | 8  | 8  |
| $\tau_3$ | 4 | 18 | 12 |
| $\tau_4$ | 4 | 30 | 24 |

1.  Calculez l'utilisation totale de l'ensemble de tache. Est-il supérieur à la borne $U_{\text{lub}}$ ?

2.  Calculez le temps de réponse de la tâche $\tau_3$ et $\tau_4$. Est-ce que le système est ordonnançable ?

3.  Comment on peut réduire le temps de réponse de $\tau_3$ ?

4.  Utiliser la méthode des <span class="underline">Hyperplanes</span> pour établir l'ordonnaçabilité

5.  Comment on peut augmenter le temps de calcul de la tache $\tau_3$ en gardant l'ordonnançabilité de toutes les tâches?

6.  En supposant que $C_4 = 8$, calculez combien on doit incrémenter la vitesse du processeur pour maintenir la tache $\tau_4$ ordonnançable.


<a id="org1819930"></a>

## Calcul du temps de reponse

Écrivez un programme (dans le langage de votre choix, Python, C++, Java &#x2026;) pour calculer le temps de reponse d'une ensemble de taches ordonnancés par Fixed Priority sur un système mono-processeur.

Le programme prends en entrée les parametres d'un nombre N de taches (C, D, T et priorité) et calcule le temps de reponse de chaque tache en utilisant la méthode itérative vue en cours.

**Question optionnelle** : écrivez une fonction du programme pour calculer la variation maximale du temps de calcul de chaque tache en utilisant la méthode des hyperplanes.


<a id="orgc01a837"></a>

# Programmation temps-réel


<a id="orgb91e455"></a>

## Code optionnel

Un système temps-réel consiste de 3 tâches periodiques $\tau_1, \tau_2, \tau_3$. Chaque job de chaque tache contient une première partie obligatoire et une deuxième partie optionnelle. Les trois tâches sont gérées par Fixed Priority : $\tau_1$ a la priorité plus élevée, $\tau_2$ la moyenne, $\tau_3$ la moins élevée.

Normalement, chaque tâche exécute ses deux parties, obligatoire et optionnelle. Si la tâche $\tau_i$ rate son échéance, elle suspends l'exécution de la partie optionnelle pour les prochains $N_i$ *jobs* (le paramètre $N_i$ peut être configuré par le développeur). Si, après le $N_i$ -ème *job*, il y a encore une échéance raté, le programme se termine avec un erreur ; inversement, si la dernière échéance est respecté, la tâche reprenne à exécuter la partie optionnelle à partir du prochain job.

1.  Écrire le pseudo-code de la i-ème tâche de manière générique, en utilisant l'interface RT POSIX ;

2.  Expliquez les conditions où une telle méthode n'est pas suffisante à corriger le problème de la surcharge. Démontrez-le avec un exemple numérique :
    -   choisissez les périodes est les temps de calculs des les 3 tâches
    -   montrez que, après $N_i$ *jobs*, il y a encore une échéance ratée.