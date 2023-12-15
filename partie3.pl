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

Noms 

Lie : Liste Il Existe
Lpt : Liste Pour Tout
Li : Liste Intersection
Lu : Liste Union
Ls : Liste ?

*/

compteur(1).
troisieme_etape(Abi,Abr) :-
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    resolution(Lie,Lpt,Li,Lu,Ls,Abr),
    nl,
    write('Youpiiiiii, on a demontre la proposition initiale !!!'),!.

/* tri_Abox */

tri_Abox([], [], [], [], [], []).

tri_Abox([(I, some(R, C))|L], [(I, some(R, C))|Lie], Lpt, Li, Lu, Ls) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls),!.

tri_Abox([(I, all(R, C))|L], Lie, [(I, all(R, C))|Lpt], Li, Lu, Ls) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls),!.

tri_Abox([(I, and(C1, C2))|L], Lie, Lpt, [(I, and(C1, C2))|Li], Lu, Ls) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls),!.

tri_Abox([(I, or(C1, C2))|L], Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Ls) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls),!.

tri_Abox([(I, C)|L], Lie, Lpt, Li, Lu, [(I, C)|Ls]) :-
    setof(X, cnamea(X), Lca),
    member(C, Lca),
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls),!.

tri_Abox([(I, not(C))|L], Lie, Lpt, Li, Lu, [(I, not(C))|Ls]) :-
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls),!.

/* resolution */

resolution([],[],[],[],[],[]).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
    complete_some(Lie,Lpt,Li,Lu,Ls,Abr).

/* 1. clash ? oui ! */
is_clash(_,_,_,_,Ls,_) :-
    setof(X, rname(X), Lr),
    member(R, Lr),
    member((I1, I2, R), Ls),
    member((I1, I2, not(R)), Ls).

/* 2. clash ? oui ! */
is_clash(_,_,_,_,Ls,_) :-
    member((I, C), Ls),
    member((I, not(C)), Ls).

/* 3. clash ? non ! */
is_clash(Lie,Lpt,Li,Lu,Ls,Abr) :-
    evolue(Abr, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    resolution(Lie1,Lpt1,Li1,Lu1,Ls1,[]).

/* 4. ∃ non fait */
complete_some([],Lpt,Li,Lu,Ls,[]) :-
    transformation_and([],Lpt,Li,Lu,Ls,[]).

/* 5. ∃ fait */
complete_some([(I, some(R, C))|Lie],Lpt,Li,Lu,Ls,Abr) :-
    setof(X, iname(X), Linst),
    member(I2, Linst),
    concat([(I, I2, R), (I2, C)], Abr, Res),
    is_clash([(I, some(R, C))|Lie],Lpt,Li,Lu,Ls,Res).

/* 6. ⊓ non fait */
transformation_and(Lie,Lpt,[],Lu,Ls,[]) :-
    deduction_all(Lie,Lpt,[],Lu,Ls,[]).

/* 7. ⊓ fait */
transformation_and(Lie,Lpt,[(I, and(C1, C2))|Li],Lu,Ls,Abr) :-
    concat([(I, C1), (I, C2)], Abr, Res),
    is_clash(Lie,Lpt,[(I, and(C1, C2))|Li],Lu,Ls,Res).

/* 8. ∀ non fait */
deduction_all(Lie,[],Li,Lu,Ls,[]) :-
    transformation_or(Lie,[],Li,Lu,Ls,[]).

/* 9. ∀ fait */
deduction_all(Lie,[(I, all(R, C))|Lpt],Li,Lu,Ls,Abr) :-
    enleve((I, all(R, C)), Abr, Abr2),
    concat([(I, C)], Abr2, Res),
    is_clash(Lie,[(I, all(R, C))|Lpt],Li,Lu,Ls,Res).

/* 10. ⊔ non fait (rien car on doit retourner false) */

/* 11.1. ⊔ fait */
transformation_or(Lie,Lpt,Li,[(I, or(C1, C2))|Lu],Ls,Res1) :-
    enleve((I, or(C1, C2)), _, Abr2),
    concat([(I, C1)], Abr2, Res1),
    is_clash(Lie,Lpt,Li,[(I, or(C1, C2))|Lu],Ls,Res1).

/* 11.2. ⊔ fait */
transformation_or(Lie,Lpt,Li,[(I, or(C1, C2))|Lu],Ls,Res2) :-
    enleve((I, or(C1, C2)), _, Abr2),
    concat([(I, C2)], Abr2, Res2),
    is_clash(Lie,Lpt,Li,[(I, or(C1, C2))|Lu],Ls,Res2).

/* evolue */

evolue([], Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls).

evolue([(I, some(R, C))|L], Lie, Lpt, Li, Lu, Ls, [(I, some(R, C))|Lie1], Lpt1, Li1, Lu1, Ls1) :-
    evolue(L, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),!.

evolue([(I, all(R, C))|L], Lie, Lpt, Li, Lu, Ls, Lie1, [(I, all(R, C))|Lpt1], Li1, Lu1, Ls1) :-
    evolue(L, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),!.

evolue([(I, and(C1, C2))|L], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, [(I, and(C1, C2))|Li1], Lu1, Ls1) :-
    evolue(L, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),!.

evolue([(I, or(C1, C2))|L], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, [(I, or(C1, C2))|Lu1], Ls1) :-
    evolue(L, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),!.

evolue([(I, C)|L], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, [(I, C)|Ls1]) :-
    setof(X, cnamea(X), Lca),
    member(C, Lca),
    evolue(L, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),!.

evolue([(I, not(C))|L], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, [(I, not(C))|Ls1]) :-
    evolue(L, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),!.

/* affiche_evolution_Abox */

/*
prop_car([], '').
prop_car([], '') :-


some_car(_).
all_car(_).
and_car(_).
or_car(_).

affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
    nl,
    write('Youpiiiiii, on a demontre la proposition initiale !!!'),!.
*/

/*
Annexe

member(X,L)
concat(L1,L2,L3)
enleve(X,L1,L2)
genere(Nom)
flatten(Liste1,Liste2)
*/
