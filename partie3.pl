/*

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
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, [], [], [], [], [], []),
    resolution(Lie,Lpt,Li,Lu,Ls,Abr),
    nl,
    write('Youpiiiiii, on a demontre la proposition initiale !!!'),!.

/*  ----------------------
         tri_Abox 
    ---------------------- */

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
    cnamea(C),
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls),!.

tri_Abox([(I, not(C))|L], Lie, Lpt, Li, Lu, [(I, not(C))|Ls]) :-
    cnamea(C),
    tri_Abox(L, Lie, Lpt, Li, Lu, Ls),!.

/*  ----------------------
         Résolution
    ---------------------- */

resolution([],[],[],[],[],[]).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
    complete_some(Lie,Lpt,Li,Lu,Ls,Abr).

/* 1. clash ? oui ! */
is_clash(Lie, Lpt, Li, Lu, Ls, Abr) :-
    member((I1, I2, R), Abr),
    member((I1, I2, not(R)), Abr),
    write("clash !"), nl,
    affiche_evolution_Abox([], [], [], [], [], [], Ls, Lie, Lpt, Li, Lu, Abr).

/* 2. clash ? oui ! */
is_clash(Lie, Lpt, Li, Lu, Ls, Abr) :-
    member((I, C), Ls),
    member((I, not(C)), Ls),
    write("clash !"), nl,
    affiche_evolution_Abox([], [], [], [], [], [], Ls, Lie, Lpt, Li, Lu, Abr).

/* 3. clash ? non ! */
is_clash(Lie,Lpt,Li,Lu,Ls,Abr) :-
    resolution(Lie,Lpt,Li,Lu,Ls,Abr).

/* 4. ∃ non fait */
complete_some([],Lpt,Li,Lu,Ls,Abr) :-
    transformation_and([],Lpt,Li,Lu,Ls,Abr).

/* 5. ∃ fait */
complete_some([(I, some(R, C))|Lie],Lpt,Li,Lu,Ls,Abr) :-
    write("Regle \u2203"), nl,
    iname(I2),
    concat([(I, I2, R)], Abr, Abr1),
    evolue((I2, C), [(I, some(R, C))|Lie], Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    affiche_evolution_Abox(Ls, [(I, some(R, C))|Lie], Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
    is_clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr1).

/* 6. ⊓ non fait */
transformation_and(Lie,Lpt,[],Lu,Ls,Abr) :-
    deduction_all(Lie,Lpt,[],Lu,Ls,Abr).

/* 7. ⊓ fait */
transformation_and(Lie,Lpt,[(I, and(C1, C2))|Li],Lu,Ls,Abr) :-
    write("Regle \u2A05"), nl,
    evolue((I, C1), Lie, Lpt, [(I, and(C1, C2))|Li], Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    evolue((I, C2), Lie1, Lpt1, Li1, Lu1, Ls1, Lie2, Lpt2, Li2, Lu2, Ls2),
    affiche_evolution_Abox(Ls, Lie, Lpt, [(I, and(C1, C2))|Li], Lu, Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
    is_clash(Lie2,Lpt2,Li2,Lu2,Ls2,Abr).

/* 8. ∀ non fait */
deduction_all(Lie,[],Li,Lu,Ls,Abr) :-
    transformation_or(Lie,[],Li,Lu,Ls,Abr).

/* 9. ∀ fait */
deduction_all(Lie,[(I, all(R, C))|Lpt],Li,Lu,Ls,Abr) :-
    write("Regle \u2200"), nl,
    evolue((I, C), Lie, [(I, all(R, C))|Lpt], Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    affiche_evolution_Abox(Ls, Lie, [(I, all(R, C))|Lpt], Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
    is_clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).

/* 10. ⊔ non fait (rien car on doit retourner false) */

/* 11.1. ⊔ fait */
transformation_or(Lie,Lpt,Li,[(I, or(C1, C2))|Lu],Ls,Abr) :-
    write("Regle \u2A06 (branche 1)"), nl,
    evolue((I, C1), Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
    is_clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).

/* 11.2. ⊔ fait */
transformation_or(Lie,Lpt,Li,[(I, or(C1, C2))|Lu],Ls,Abr) :-
    write("Regle \u2A06 (branche 2)"), nl,
    evolue((I, C2), Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
    is_clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).

/*  ----------------------
         Evolue
    ---------------------- */

evolue((I, some(R, C)), Lie, Lpt, Li, Lu, Ls, [(I, some(R, C))|Lie], Lpt, Li, Lu, Ls).

evolue((I, all(R, C)), Lie, Lpt, Li, Lu, Ls, Lie, [(I, all(R, C))|Lpt], Li, Lu, Ls).

evolue((I, and(C1, C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, [(I, and(C1, C2))|Li], Lu, Ls).

evolue((I, or(C1, C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Ls).

evolue((I, C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(I, C)|Ls]) :-
    cnamea(C).

evolue((I, not(C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(I, not(C))|Ls]) :-
    cnamea(C).

/*  ---------------------------
         Affiche évolution
    --------------------------- */

affiche_concept(some(R, C)) :-
    write("\u2203"), 
    write(R), write("."), 
    affiche_concept(C).

affiche_concept(all(R, C)) :-
    write("\u2200"), 
    write(R), write("."), 
    affiche_concept(C).

affiche_concept(and(C1, C2)) :-
    affiche_concept(C1), 
    write(" \u2A05 "), 
    affiche_concept(C2).

affiche_concept(or(C1, C2)) :-
    affiche_concept(C1), 
    write(" \u2A06 "), 
    affiche_concept(C2).

affiche_concept(not(C)) :-
    write("\u00AC("),
    affiche_concept(C),
    write(")").

affiche_concept(C) :-
    cnamea(C),
    write(C).

affiche_assertion([]).

affiche_assertion([(I, C)|L]) :-
	write("| "), write(I), write(' : '), affiche_concept(C), nl,
	affiche_assertion(L).

affiche_role([]).
affiche_role([(I1, I2, R)|L]) :-
    write("| "), write(I1), write(", "), write(I2), write(' : '), write(R), nl,
	affiche_role(L).

affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
    write(" ________________________________________"), nl,
    write("/                                        \\"), nl,
    affiche_assertion(Ls1),
    affiche_assertion(Lie1),
    affiche_assertion(Lpt1),
    affiche_assertion(Li1),
    affiche_assertion(Lu1),
    affiche_role(Abr1),
    write("|----------------------------------------"), nl,
    affiche_assertion(Ls2),
    affiche_assertion(Lie2),
    affiche_assertion(Lpt2),
    affiche_assertion(Li2),
    affiche_assertion(Lu2),
    affiche_role(Abr2),
    write("\\________________________________________/"), nl, nl.
