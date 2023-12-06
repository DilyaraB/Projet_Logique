
programme :- premiere_etape(Tbox,Abi,Abr),
            deuxieme_etape(Abi,Abi1,Tbox),
            troisieme_etape(Abi1,Abr).

/* Partie 1 de l'énoncé */
premiere_etape(LTBox, LABox, LRoles, Res)
/* Partie 2 de l'énoncé (partiellement complété) */
deuxieme_etape(Abi, Abi1, TBox) :- saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).
/* Partie 3 de l'énoncé */
troisieme_etape(LABox2, LRoles)

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
    nl,
    write('Entrez le numero du type de proposition que vous voulez demontrer :'), nl,
    write('1 Une instance donnee appartient a un concept donne.'), nl,
    write("2 Deux concepts n'ont pas d'elements en commun(ils ont une intersection vide)."), nl, 
    read(R), 
    suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(R,Abi,Abi1,Tbox) :- 
    nl, 
    write('Cette reponse est incorrecte.'), 
    nl, 
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

/* 1er cas */
acquisition_prop_type1(Abi, Abi1, Tbox) :-
    write('Entrez l"identificateur de l"instance (par exemple, michelAnge) : '), read(Instance),
    write('Entrez le concept (par exemple, personne) : '), read(Concept),
    %Vérifier si l''instance et concept existent
    (instance(Instance), concept(Concept)  ->
        % Processus de traitement de la proposition
        process_prop_type1(Instance, Concept, Abi, Abi1);
        nl, write('L\'instance ou le concept n\'existe pas. Veuillez réessayer.'), nl
    ).

process_prop_type1(Instance, Concept, Abi, Abi1) :-
    replace_concept(not(Concept), SimplifiedConcept, []),
    nnf(SimplifiedConcept, NormalizedConcept),
    append(Abi, [(Instance, NormalizedConcept)], Abi1).

/* 2e cas */ 
acquisition_prop_type2(Abi, Abi1, Tbox) :-
    write('Entrez le premier concept (par exemple, personne) : '), read(Concept1),
    write('Entrez le deuxieme concept (par exemple, livre) : '), read(Concept2),
    (concept(and(Concept1, Concept2))  ->
        % Processus de traitement de la proposition
        process_prop_type2(Concept1, Concept2, Abi, Abi1);
        nl, write('L\'un ou/et deux de concepts n\'existe pas. Veuillez réessayer.'), nl
    ).

:- dynamic compteur/1.

% Initialiser le compteur
init_compteur :- assert(compteur(1)).

% Prédicat pour générer une nouvelle instance pour la quantification existentielle
generate_new_instance(Instance) :-
    retract(compteur(Counter)),
    NewCounter is Counter + 1,
    assert(compteur(NewCounter)),
    atom_concat('inst_', NewCounter, Instance).

process_prop_type2(Concept1, Concept2, Abi, Abi1) :-
    generate_new_instance(I),
    replace_concept(and(Concept1, Concept2), and(SimplifiedC1, SimplifiedC2), []),
    nnf(SimplifiedC1, NormalizedConcept1),
    nnf(SimplifiedC2, NormalizedConcept2),
    append(Abi, [(I, and(NormalizedConcept1, NormalizedConcept2))], Abi1).