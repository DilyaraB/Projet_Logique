
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

concept(Tbox, Abox) :-
    /* Vérifie la correction syntaxique et sémantique des identificateurs, de la Tbox, de la Abox */
    verify_concepts(cnamea),
    verify_concepts(cnamena),
    verify_concepts(iname),
    verify_concepts(rname),

    verify_tbox(Tbox, SimplifiedTbox),

    verify_abox(Abox, SimplifiedAbox).

/* Vérifie la correction syntaxique et sémantique de la Tbox */
verify_tbox(Tbox, SimplifiedTbox) :-
    write('Vérification de la Tbox...'), nl,
    /* Appliquer nnf à chaque équivalence dans la Tbox, vérifier l'absence de concepts auto-référents */
    maplist(nnf_equivalence, Tbox, SimplifiedTbox),
    maplist(check_auto_ref, SimplifiedTbox).

/* Vérifie la correction syntaxique et sémantique de la Abox */
verify_abox(Abox, SimplifiedAbox) :-
    write('Vérification de la Abox...'), nl,
    /* Partitionner Abox en assertions de concepts et de rôles, Appliquer nnf aux assertions de concepts et de roles, Réassembler les assertions de concepts et de rôles, Vérifier l'absence de concepts auto-référents dans la Abox */
    partition(assertion_concept, Abox, ConceptAssertions, RoleAssertions),
    
    maplist(nnf_assertion, ConceptAssertions, SimplifiedConceptAssertions),

    maplist(nnf_assertion, RoleAssertions, SimplifiedRoleAssertions),
    
    append(SimplifiedConceptAssertions, SimplifiedRoleAssertions, SimplifiedAbox),

    maplist(check_auto_ref, SimplifiedAbox).

/* Remarque 1 */

pas_autoref(Concept, Expression) :-
    /* Obtient la liste des identificateurs de concepts complexes dans l'expression et Vérifie si Concept n'est pas dans la liste des concepts complexes */
    setof(ComplexConcept, get_complex_concepts(Expression), ComplexConcepts),
    member(Concept, ComplexConcepts).

/* Obtient la liste des identificateurs de concepts complexes dans une expression */
get_complex_concepts(and(C1, C2), Concepts) :-
    get_complex_concepts(C1, Concepts1),
    get_complex_concepts(C2, Concepts2),
    append(Concepts1, Concepts2, Concepts).

get_complex_concepts(or(C1, C2), Concepts) :-
    get_complex_concepts(C1, Concepts1),
    get_complex_concepts(C2, Concepts2),
    append(Concepts1, Concepts2, Concepts).

get_complex_concepts(not(C), Concepts) :-
    get_complex_concepts(C, Concepts).

get_complex_concepts(some(_, C), Concepts) :-
    get_complex_concepts(C, Concepts).

get_complex_concepts(all(_, C), Concepts) :-
    get_complex_concepts(C, Concepts).

get_complex_concepts(Concept, [Concept]) :-
    cnamena(Concept).  

/* Remarque 3 */
traitement_Tbox(Tbox, SimplifiedTbox) :-
    write('Traitement de la Tbox...'), nl,
    /* Appliquer nnf à chaque équivalence dans la Tbox */
    maplist(nnf_equivalence, Tbox, SimplifiedTbox).

/* Appliquer nnf à une équivalence (Tuple) dans la Tbox */
nnf_equivalence((Concept, Expression), (Concept, SimplifiedExpression)) :-
    nnf(Expression, SimplifiedExpression).

/* Remarque 4 */
traitement_Abox(Abox, SimplifiedAbox) :-
    write('Traitement de la Abox...'), nl,
    /* Partitionner Abox en assertions de concepts et de rôles, appliquer nnf aux assertions de concepts et de roles et tout a la fin réassembler les assertions de concepts et de rôles */
    partition(assertion_concept, Abox, ConceptAssertions, RoleAssertions),

    maplist(nnf_assertion, ConceptAssertions, SimplifiedConceptAssertions),
    
    maplist(nnf_assertion, RoleAssertions, SimplifiedRoleAssertions),
    
    append(SimplifiedConceptAssertions, SimplifiedRoleAssertions, SimplifiedAbox).

/* Appliquer nnf à une assertion dans la Abox */
nnf_assertion((X, Y, Z), (X, Y, SimplifiedZ)) :-
    nnf(Z, SimplifiedZ).

/* Vérifier si une assertion est de concept */
assertion_concept((_, _, Concept)) :-
    cnamena(Concept).