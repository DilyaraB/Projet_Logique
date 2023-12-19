
/*  -------------------------------------------------------
    Salwa     MUJAHID		28711288
    Dilyara   BABANAZAROVA 	28709428
    ------------------------------------------------------- */

/*  -------------------------------------------------------
    Mise sous forme normale négative d'une expression
    ------------------------------------------------------- */

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


/*  -------------------------------------------------------
    ANNEXE
    ------------------------------------------------------- */
compteur(1).

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

genere(Nom) :- compteur(V),nombre(V,L1),
    concat([105,110,115,116],L1,L2),
    V1 is V+1,
    dynamic(compteur/1),
    retract(compteur(V)),
    dynamic(compteur/1),
    assert(compteur(V1)),nl,nl,nl,
    name(Nom,L2).

nombre(0,[]).
nombre(X,L1) :-
    R is (X mod 10),
    Q is ((X-R)//10),
    chiffre_car(R,R1),
    char_code(R1,R2),
    nombre(Q,L),
    concat(L,[R2],L1).
    
chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').

/*  ========================================================================
    Jeux de tests
    ======================================================================== */

/* TBox */
equiv(sculpteur,and(personne,some(aCree,sculpture))).
equiv(auteur,and(personne,some(aEcrit,livre))).
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))).
equiv(parent,and(personne,some(aEnfant,anything))).

/* Concepts atomiques */
cnamea(personne).
cnamea(livre).
cnamea(objet).
cnamea(sculpture).
cnamea(anything).
cnamea(nothing).

/* Concepts non-atomiques */
cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).

/* Instances */
iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).

/* Rôles */
rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).

/* ABox a : c */
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).

/* ABox a, b : c */
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).

/*  ========================================================================
    Partie 1 - Verification de la Tbox et la Abox
    ======================================================================== */

/*  -------------------------------------------------------
    Vérifie la correction syntaxique et sémantique des 
    expressions
    ------------------------------------------------------- */

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

/*  -------------------------------------------------------
    Vérifie la correction syntaxique et sémantique de la 
    Tbox et de la Abox
    ------------------------------------------------------- */

verify_tbox([]).
verify_tbox([(C1, C2)|Rest]) :-
    cnamena(C1),
    concept(C2),
    verify_tbox(Rest).

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

/*  -------------------------------------------------------
    Remarque 1 du sujet : 
    Vérifie l'inexistence des concepts circulaires dans la 
    Tbox
    ------------------------------------------------------- */

pas_autoref(Concept) :-
    replace_concept(Concept, _, []), !.

/*  -------------------------------------------------------
    Remarques 3, 4 du sujet : 
    Remplace les concepts complexes par leurs definitions
    atomiques dans la Tbox et Abox
    ------------------------------------------------------- */

/* si le concept est atomique alors concept simplifie est lui meme */
replace_concept(AtomicC, AtomicC, _) :- cnamea(AtomicC).

replace_concept(ComplexC, SimplifiedC, Visited) :-
    /* on verifie bien si le concept est visité deja pour eviter boucle infini, on trouve sa definiton, apres on continue recursivement remplacer les autres concepts non atomique dans la definition */ 
    \+ member(ComplexC, Visited), 
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

traitement_box([], []).
traitement_box([(X, Concept) | Rest], [(X, NewConcept) | Result]) :-
    replace_concept(Concept, Atomique, []),
    nnf(Atomique, NewConcept),
    traitement_box(Rest, Result), !.

/*  ========================================================================
    Partie 2 - Saisie de la proposition à demontrer
    ======================================================================== */

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
    nl,
    write('Entrez le numero du type de proposition que vous voulez demontrer :'), nl,
    write('1 Une instance donnee appartient a un concept donne.'), nl,
    write("2 Deux concepts n'ont pas d'elements en commun (ils ont une intersection vide)."), nl, 
    read(R), 
    suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :-
    acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :-
    acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(R,Abi,Abi1,Tbox) :-
    nl,write('Cette reponse est incorrecte.'),nl,
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

/*  -------------------------------------------------------
    1er cas - (I : C) : 
    Ajoute dans la Abox I : ¬C
    ------------------------------------------------------- */

acquisition_prop_type1(Abi, Abi1, Tbox) :-
    write('Entrez l\'identificateur de l\'instance (par exemple, michelAnge) : '), read(Instance),
    write('Entrez le concept (par exemple, personne) : '), 
    read(Concept),
    /* Vérifier si l''instance et concept existent */
    (instance(Instance), concept(Concept)  ->
        /* Processus de traitement de la proposition */
        process_prop_type1(Instance, Concept, Abi, Abi1);
        nl, write("L'instance ou le concept n'existe pas. Veuillez réessayer."), nl, acquisition_prop_type1(Abi, Abi1, Tbox)
    ).

process_prop_type1(Instance, Concept, Abi, Abi1) :-
    replace_concept(not(Concept), SimplifiedConcept, []),
    nnf(SimplifiedConcept, NormalizedConcept),
    append(Abi, [(Instance, NormalizedConcept)], Abi1).

/*  -------------------------------------------------------
    2e cas - (C1 ⊓ C2 ⊑ ⊥) : 
    Ajoute dans la Abox ∃ inst, inst : C1 ⊓ C2
    ------------------------------------------------------- */

acquisition_prop_type2(Abi, Abi1, Tbox) :-
    write('Entrez le premier concept (par exemple, personne) : '), read(Concept1),
    write('Entrez le deuxieme concept (par exemple, livre) : '), read(Concept2),
    (concept(and(Concept1, Concept2))  ->
        /* Processus de traitement de la proposition */
        process_prop_type2(Concept1, Concept2, Abi, Abi1);
        nl, write('L\'un ou/et deux de concepts n\'existe pas. Veuillez réessayer.'), nl,
        acquisition_prop_type2(Abi, Abi1, Tbox)
    ).

process_prop_type2(Concept1, Concept2, Abi, Abi1) :-
    genere(I),
    replace_concept(and(Concept1, Concept2), and(SimplifiedC1, SimplifiedC2), []),
    nnf(SimplifiedC1, NormalizedConcept1),
    nnf(SimplifiedC2, NormalizedConcept2),
    append(Abi, [(I, and(NormalizedConcept1, NormalizedConcept2))], Abi1).

/*  ========================================================================
    Partie 3 - Demonstration de la proposition saisie
    ======================================================================== */

/*
    - Lie : Liste Il Existe
    - Lpt : Liste Pour Tout
    - Li : Liste Intersection
    - Lu : Liste Union
    - Ls : Liste des assertions du type (I, C) ou (I, not(C)) avec C atomique.

    - On a suivi l'arbre de démonstration 
    - evolue correspond à un noeud (sauf si deux fois à la suite) 
*/

/*  -------------------------------------------------------
    Permet de trier les assertions de concept
    ------------------------------------------------------- */

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

/*  -------------------------------------------------------
    Application de la méthode des tableaux
    ------------------------------------------------------- */

resolution([],[],[],[],[],[]).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
    complete_some(Lie,Lpt,Li,Lu,Ls,Abr).

resolution([], [], [], [], Ls, Abr):-
	is_clash([], [], [], [], Ls, Abr), !.

resolution([], [], [], [], Ls, Abr):-
	\+ is_clash([], [], [], [], Ls, Abr), !, 
    write("On ne peut rien conclure..."), nl, nl,
    !, fail.

/* 2. clash ? oui ! */
is_clash(Lie, Lpt, Li, Lu, [(I, C) | Ls], Abr) :-
    nnf(not(C), NC),
    (member((I, NC), Ls) ->
        write("clash !"), nl,
        affiche_assertion([(I, C), (I, NC)]),
        affiche_evolution_Abox([], [], [], [], [], [], [(I, C) | Ls], Lie, Lpt, Li, Lu, Abr)
    ;
        is_clash(Lie, Lpt, Li, Lu, Ls, Abr)
    ), !.

/*  _______________________________________                
    COMPLETE_SOME : Règle ∃
    _______________________________________

    On génère une nouvelle instance 
    _______________________________________
*/

/* 4. ∃ non fait */
complete_some([],Lpt,Li,Lu,Ls,Abr) :-
    transformation_and([],Lpt,Li,Lu,Ls,Abr),!.

/* 5. ∃ fait */
complete_some([(I, some(R, C))|Lie],Lpt,Li,Lu,Ls,Abr) :-
    genere(I2),!,
    write("Regle \u2203 "), nl,
    affiche_assertion([(I, some(R, C))]), write("| --> "), nl,
    affiche_role([(I, I2, R)]),
    affiche_assertion([(I2, C)]),

    concat([(I, I2, R)], Abr, Abr1),
    evolue((I2, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    affiche_evolution_Abox(Ls, [(I, some(R, C))|Lie], Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
    (is_clash(Lie1, Lpt1, Li1, Lu1, Ls1, Abr1) -> true ; 
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr1)).

/*  _______________________________________
    TRANSFORMATION_AND : Règle ⊓
    _______________________________________

    Transformation d'une assertion contenant le 'and' en deux assertions
    _______________________________________
*/

/* 6. ⊓ non fait */
transformation_and(Lie,Lpt,[],Lu,Ls,Abr) :-
    deduction_all(Lie,Lpt,[],Lu,Ls,Abr),!.

/* 7. ⊓ fait */
transformation_and(Lie,Lpt,[(I, and(C1, C2))|Li],Lu,Ls,Abr) :-
    write("Regle \u2A05 "), nl,
    affiche_assertion([(I, and(C1, C2))]), write("| --> "), nl,
    affiche_assertion([(I, C1), (I, C2)]),

    evolue((I, C1), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    evolue((I, C2), Lie1, Lpt1, Li1, Lu1, Ls1, Lie2, Lpt2, Li2, Lu2, Ls2),
    affiche_evolution_Abox(Ls, Lie, Lpt, [(I, and(C1, C2))|Li], Lu, Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
    ( is_clash(Lie2,Lpt2,Li2,Lu2,Ls2,Abr) -> true
    ;
    resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr)
    ).

/*  _______________________________________
    DEDUCTION_ALL : Règle ∀
    _______________________________________

    On a besoin de parcourir toutes les assertions de role de Abr
    pour insérer les assertions de concepts reliés.
    Note : Lorsqu'on ne trouve pas de nouvelles instances et qu'on n'a pas de feuille fermée,
            le programme affiche deux fois "On ne peut rien conclure...", mais la recherche 
            de nouvelles instances n'en n'est pas la cause.
    _______________________________________
*/

/* 8. ∀ non fait */
deduction_all(Lie,[],Li,Lu,Ls,Abr) :-
    transformation_or(Lie,[],Li,Lu,Ls,Abr),!.

/* 9. ∀ fait */
deduction_all(Lie,[(I, all(R, C))|Lpt],Li,Lu,Ls,Abr) :-

    (setof((I2, C),  member((I, I2, R), Abr), L) -> 
		write("Regle \u2200 "), nl,
        affiche_assertion([(I, all(R, C))]), write("| --> "), nl,
        affiche_assertion([(I2, C)]), 
		nl
	),

    verif_new_abox(L, Ls),
    evolue_list(L, Lie, [(I, all(R, C))|Lpt], Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    affiche_evolution_Abox(Ls, Lie, [(I, all(R, C))|Lpt], Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
    ( is_clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr) -> true
    ;
    resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr)
    ).

/* 8. ∀ non fait (Un autre cas lorsqu'il n'y a pas de nouvelles instances) */
deduction_all(Lie,[(I, all(R, C))|Lpt],Li,Lu,Ls,Abr) :-
    transformation_or(Lie,[(I, all(R, C))|Lpt],Li,Lu,Ls,Abr),!.


/*  -------------------------------------------------------
    Vérifie si il existe de nouvelles instances, pour éviter d'avoir une boucle infinie
    On essaiera la règle du OR si il n'existe de nouvelles assertions
    ------------------------------------------------------- */

verif_new_abox([], _) :-
    write("Il n'y a pas de nouvelles instances pour \u2200."), nl,
    !, fail.
verif_new_abox([X|_], Ls) :-
    \+ member(X, Ls),!.
verif_new_abox([X|L], Ls) :-
    member(X, Ls),
    verif_new_abox(L, Ls),!.

/*  _______________________________________
    TRANSFORMATION_OR : Règle ⊔
    _______________________________________

    On découpe en deux branches, donc on a deux noeuds partant d'une même base.
    Lorsqu'on ne peut plus démontrer une branche, on abandonne
    On doit avoir les deux branches fermées pour pouvoir démontrer la proposition initiale.
    _______________________________________
*/

/* 10. ⊔ non fait (pas besoin) */

/* 11. ⊔ fait */

transformation_or(Lie,Lpt,Li,[(I, or(C1, C2))|Lu],Ls,Abr) :-
    write("Regle \u2A06 (branche 1) "), nl,
    affiche_assertion([(I, or(C1, C2))]), write("| --> "), nl,
    affiche_assertion([(I, C1)]),

    evolue((I, C1), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
    ( is_clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr) -> true
    ;
    resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr)
    ),

    write("Regle \u2A06 (branche 2) "), nl,
    affiche_assertion([(I, or(C1, C2))]), write("| --> "), nl,
    affiche_assertion([(I, C2)]),

    evolue((I, C2), Lie, Lpt, Li, Lu, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
    (is_clash(Lie2,Lpt2,Li2,Lu2,Ls2,Abr) -> true
    ;
    resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr)
    ).


/*  -------------------------------------------------------
    Permet d'ajouter des assertions dans un noeud
    ------------------------------------------------------- */

evolue((I, some(R, C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
    member((I, some(R, C)), Lie).
evolue((I, some(R, C)), Lie, Lpt, Li, Lu, Ls, [(I, some(R, C))|Lie], Lpt, Li, Lu, Ls).

evolue((I, all(R, C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
    member((I, all(R, C)), Lpt).
evolue((I, all(R, C)), Lie, Lpt, Li, Lu, Ls, Lie, [(I, all(R, C))|Lpt], Li, Lu, Ls).

evolue((I, and(C1, C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
    member((I, and(C1, C2)), Li).
evolue((I, and(C1, C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, [(I, and(C1, C2))|Li], Lu, Ls).

evolue((I, or(C1, C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
    member((I, or(C1, C2)), Lu).
evolue((I, or(C1, C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, [(I, or(C1, C2))|Lu], Ls).

evolue((I, C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
    cnamea(C),
    member((I, C), Ls).
evolue((I, C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(I, C)|Ls]) :-
    cnamea(C).

evolue((I, not(C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
    cnamea(C),
    member((I, not(C)), Ls).
evolue((I, not(C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(I, not(C))|Ls]) :-
    cnamea(C).

/* evolue_list pour les insertions par liste */
evolue_list([], Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls).
evolue_list([X|L], Lie, Lpt, Li, Lu, Ls, Lie2, Lpt2, Li2, Lu2, Ls2) :-
    evolue(X, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    evolue_list(L, Lie1, Lpt1, Li1, Lu1, Ls1, Lie2, Lpt2, Li2, Lu2, Ls2),!.

/*  -------------------------------------------------------
    Permet d'afficher les étapes de résolution
    ------------------------------------------------------- */

/* Afficher un concept : Ces prédicats permettront d'afficher les symboles de façon récursive */
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

/* Afficher des assertions : On affiche une liste d'assertions de concepts donnée */
affiche_assertion([]).
affiche_assertion([(I, C)|L]) :-
	write("| "), write(I), write(' : '), affiche_concept(C), nl,
	affiche_assertion(L).

/* Afficher des roles : On affiche une liste d'assertions de roles donnée */
affiche_role([]).
affiche_role([(I1, I2, R)|L]) :-
    write("| "), write(I1), write(", "), write(I2), write(' : '), write(R), nl,
	affiche_role(L).

/* Afficher l'évolution : On affiche un noeud dans lequel on applique une règle spécifique 
                          sur les assertions avant la séparation pour obtenir les assertions 
                          après la séparation.
                          Permet de voir les modifications AVANT - APRES

   Note : Ce prédicat ne permet que d'afficher le changement sur les assertions, les règles 
   et les changements effectués sont affichées entre les deux noeuds lors de leurs applications,
   mais le code d'affichage est écrit sur les prédicats des règles correspondants */

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


/*  ========================================================================
    MAIN
    ======================================================================== */

/* Partie 1 de l'énoncé */
premiere_etape(LTBox, LABox, LRoles) :- 
    verify_tbox(LTBox), 
    verify_abox(LABox), 
    verify_abox(LRoles),
    setof(X, cnamena(X), Lcno),
    pas_autoref(Lcno),
    traitement_box(LTBox),
    traitement_box(LABox).

/* Partie 2 de l'énoncé */
/* Abi = liste des assertions de concepts initiales,
   Abi1 = liste des asstions de concepts completee */
deuxieme_etape(Abi, Abi1, Tbox) :- 
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

/* Partie 3 de l'énoncé */
troisieme_etape(Abi,Abr) :-
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, Lu, Abr, [], [], [], [], [], []),
    resolution(Lie,Lpt,Li,Lu,Ls,Abr),
    nl,
    write('Youpiiiiii, on a demontre la proposition initiale !!!'),!. 

programme :-
    premiere_etape(Tbox, Abi, Abr),
    deuxieme_etape(Abi,Abi1,Tbox),
    troisieme_etape(Abi1,Abr), nl,
    write('Fin !').

programme.