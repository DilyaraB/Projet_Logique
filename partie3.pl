/* Règles :
    - Existe
    - ET
    - Pour tout
    - OU

If nouvelle assertion, vérifier si clash, si oui fermer, sinon continuer
If toutes les branches fermées, insatisfiable et proposition initiale démontrée
Voir arbre

*/

compteur(1).
troisieme_etape(Abi,Abr) :-
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    resolution(Lie,Lpt,Li,Lu,Ls,Abr),
    nl,
    write('Youpiiiiii, on a demontre la proposition initiale !!!').

tri_Abox

resolution
complete_some(Lie,Lpt,Li,Lu,Ls,Abr)
transformation_and(Lie,Lpt,Li,Lu,Ls,Abr)
deduction_all(Lie,Lpt,Li,Lu,Ls,Abr)
transformation_or(Lie,Lpt,Li,Lu,Ls,Abr)

evolue(A, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1)
affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2)

/*
Annexe

member(X,L)
concat(L1,L2,L3)
enleve(X,L1,L2)
genere(Nom)
flatten(Liste1,Liste2)
*/
