
/* Forme normale négative */
nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)):- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),Y):- nnf(X,Y),!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).

/* Vérifie la correction syntaxique et sémantique des identificateurs, de la Tbox, de la Abox */

instance(I) :- iname(I). % Vérification des identificateurs dinstance
role(R) :- rname(R). % Vérification des identificateurs de rôle.

concept(C) :- cnamea(C). % Vérification des concepts atomique
concept(CG) :- cnamena(CG). % Vérification des concepts non atomique
concept(not(C)) :- concept(C).
concept(and(C1, C2)) :- concept(C1), concept(C2).
concept(or(C1, C2)) :- concept(C1), concept(C2).
concept(some(R, C)) :- role(R), concept(C).
concept(all(R, C)) :- role(R), concept(C).

concept(Tbox) :-
    verify_tbox(Tbox).

concept(Abox) :-
    verify_abox(Abox).

% Verify Tbox
verify_tbox([]).
verify_tbox([(C1, C2)|Rest]) :-
    cnamena(C1),
    concept(C2),
    verify_tbox(Rest).

% Verify Abox
verify_abox([]).

verify_abox([(I, C)|Rest]) :-
    instance(I),
    concept(C),
    verify_abox(Rest).

verify_abox([(I1, I2, R) | Rest]) :- 
    instance(I1),
    instance(I2),
    role(R),
    verify_abox(Rest).


/* Remarque 1 */

pas_autoref(Concept) :-
    replace_concept(Concept, _, []), !.

/* Remarque 3,4 */

/* si le concept est atomique alors concept simplifie est lui meme */
replace_concept(AtomicC, AtomicC, _) :- cnamea(AtomicC).

replace_concept(ComplexC, SimplifiedC, Visited) :-
    /* on trouve equivalence de concept non atomique, on verifie bien s'il est en ce Tbox, apres on continue recursivement remplacer les autres concepts non atomique dans la definition */ 
    \+ member(ComplexC, Visited), % pour eviter boucle infini
    equiv(ComplexC, Def),
    replace_concept(Def, SimplifiedC, [ComplexC|Visited]).

replace_concept(not(C), not(SimplifiedC), Visited) :-
    replace_concept(C, SimplifiedC, Visited).

replace_concept(and(C1, C2), and(S1, S2), Visited) :-
    replace_concept(C1, S1, Visited),
    replace_concept(C2, S2, Visited).

replace_concept(or(C1, C2), or(S1, S2), Visited) :-
    replace_concept(C1, S1, Visited),
    replace_concept(C2, S2, Visited).

replace_concept(some(R, C), some(R, SimplifiedC), Visited) :-
    replace_concept(C, SimplifiedC, Visited).

replace_concept(all(R, C), all(R, SimplifiedC), Visited) :-
    replace_concept(C, SimplifiedC, Visited).

/* traitement_box prend en parametre tbox/abox et tbox/abox simplifie Pour simplifier les concepts il utilise le predicat replace_concept et il utilise apres le predicat nnf pour mettre le concept simplifie en forme normale negative  */
traitement_box([], []).
traitement_box([(X, Concept) | Rest], [(X, NewConcept) | Result]) :-
    replace_concept(Concept, Atomique, []),
    nnf(Atomique, NewConcept),
    traitement_box(Rest, Result), !.