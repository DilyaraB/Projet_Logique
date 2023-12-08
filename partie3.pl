/* Règles :
    - Existe
    - ET
    - Pour tout
    - OU

If nouvelle assertion, vérifier si clash, si oui fermer, sinon continuer
If toutes les branches fermées, insatisfiable et proposition initiale démontrée
Voir arbre

*/

/*

TBox

[(sculpteur,and(personne,some(aCree,sculpture))),
(auteur,and(personne,some(aEcrit,livre))),
(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))),
(parent,and(personne,some(aEnfant,anything)))]

ABox

[(michelAnge,personne), (david,sculpture), (sonnets,livre),(vinci,personne), (joconde,objet)]
[(michelAnge,and(auteur,some(aEcrit,livre)), (david,some(aEnfant,anything))]

Roles

[(michelAnge, david, aCree), (michelAnge, sonnet, aEcrit),(vinci,joconde, aCree)]

*/

compteur(1).
troisieme_etape(Abi,Abr) :-
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    resolution(Lie,Lpt,Li,Lu,Ls,Abr),
    nl,
    write('Youpiiiiii, on a demontre la proposition initiale !!!').

/* tri_Abox */

tri_Abox([], [], [], [], [], []).

tri_Abox([(I, some(R, C))|L], [(I, some(R, C))|Lie], Lpt, Li, Lu, Ls) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls).

tri_Abox([(I, all(R, C))|L], Lie, [(I, all(R, C))|Lpt], Li, Lu, Ls) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls).

tri_Abox([(I, and(C1, C2))|L], Lie, Lpt, [(I, and(C1, C2))|Li], Lu, Ls) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls).

tri_Abox([(I, or(C1, C2))|L], Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Ls) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls).

tri_Abox([(I, C)|L], Lie, Lpt, Li, Lu, [(I, C)|Ls]) :-
    setof(X, cnamea(X), Lca),
    member(C, Lca),
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls).

tri_Abox([(I, not(C))|L], Lie, Lpt, Li, Lu, [(I, not(C))|Ls]) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls).

/* resolution */


/*resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
    complete_some(Lie,Lpt,Li,Lu,Ls,Abr),
    transformation_and(Lie,Lpt,Li,Lu,Ls,Abr),
    deduction_all(Lie,Lpt,Li,Lu,Ls,Abr),
    transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).*/

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
    is_clash(Abr),
    complete_some(Lie,Lpt,Li,Lu,Ls,Abr).

is_clash(Abr) :-
    member((I, C), Abr),
    member((I, not(C)), Abr).

is_clash(Abr) :-
    member((I1, I2, R), Abr),
    member((I1, I2, not(R)), Abr).

complete_some([],Lpt,Li,Lu,Ls,Abr) :-
    transformation_and([],Lpt,Li,Lu,Ls,Abr).

complete_some([(I, some(R, C))|Lie],Lpt,Li,Lu,Ls,Res) :-
    setof(X, iname(X), Linst),
    member(I2, Linst),
    concat([(I, I2, R)], _, Abr2),
    concat([(I2, R)], Abr2, Res),
    \+ is_clash(Res),
    resolution([(I, some(R, C))|Lie],Lpt,Li,Lu,Ls,Res).

complete_some([(I, some(R, C))|_],_,_,_,_,Res) :-
    setof(X, iname(X), Linst),
    member(I2, Linst),
    concat([(I, I2, R)], _, Abr2),
    concat([(I2, C)], Abr2, Res),
    is_clash(Res).

transformation_and(Lie,Lpt,[],Lu,Ls,Abr) :-
    deduction_all(Lie,Lpt,[],Lu,Ls,Abr).

transformation_and(Lie,Lpt,[(I, and(C1, C2))|Li],Lu,Ls,Res) :-
    concat([(I, C1)], _, Abr2),
    concat([(I, C1)], Abr2, Res),
    \+ is_clash(Res),
    resolution(Lie,Lpt,[(I, and(C1, C2))|Li],Lu,Ls,Res).

transformation_and(_,_,[(I, and(C1, C2))|_],_,_,Res) :-
    concat([(I, C1)], _, Abr2),
    concat([(I, C2)], Abr2, Res),
    is_clash(Res).

deduction_all(Lie,[],Li,Lu,Ls,Abr) :-
    transformation_or(Lie,[],Li,Lu,Ls,Abr).

deduction_all(Lie,[(I, all(R, C))|Lpt],Li,Lu,Ls,Res) :-
    enleve((I, all(R, C)), _, Abr2),
    concat([(I, C)], Abr2, Res),
    \+ is_clash(Res),
    resolution(Lie,Lpt,Li,Lu,Ls,Res).

deduction_all(_,[(I, all(R, C))|_],_,_,_,Res) :-
    enleve((I, all(R, C)), _, Abr2),
    concat([(I, C)], Abr2, Res),
    is_clash(Res).

transformation_or(_,_,_,[],_,Abr) :-
    is_clash(Abr).

transformation_or(Lie,Lpt,Li,[(I, or(C1, C2))|Lu],Ls,Abr) :-
    enleve((I, or(C1, C2)), Abr, Abr2),
    concat([(I, C1)], Abr2, Res1),
    concat([(I, C2)], Abr2, Res2),
    resolution(Lie,Lpt,Li,Lu,Ls,Res1),
    resolution(Lie,Lpt,Li,Lu,Ls,Res2).


/*
resolution correspond à une branche

evolue(A, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1)
affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2)
*/

/*
Annexe

member(X,L)
concat(L1,L2,L3)
enleve(X,L1,L2)
genere(Nom)
flatten(Liste1,Liste2)
*/
