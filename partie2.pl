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
acquisition_prop_type1
/* 2e cas */ 
acquisition_prop_type2

% Acquisition et traitement d''une proposition de type 1 
acquisition_prop_type1(Abi, Abi1, Tbox) :-
    write('Entrez l"identificateur de l"instance (par exemple, michelAnge) : '), read(Instance),
    write('Entrez le concept (par exemple, personne) : '), read(Concept),
    process_prop_type1(Instance, Concept, Abi, Abi1, Tbox).

process_prop_type1(Instance, Concept, Abi, Abi1, Tbox) :-
    nnf(not(Concept), NegatedConcept),
    traitement_Tbox,
    traitement_Abox,
    nnf_assertion((Instance, Concept), SimplifiedAssertion),
    nnf_assertion((Instance, NegatedConcept), SimplifiedNegatedAssertion),
    append([SimplifiedAssertion, SimplifiedNegatedAssertion], Abi, Abi1).

% Acquisition et traitement d''une proposition de type 2
acquisition_prop_type2(Abi, Abi1, Tbox) :-
    write('Entrez le premier concept (par exemple, personne) : '), read(Concept1),
    write('Entrez le deuxieme concept (par exemple, livre) : '), read(Concept2),
    process_prop_type2(Concept1, Concept2, Abi, Abi1, Tbox).

process_prop_type2(Concept1, Concept2, Abi, Abi1, Tbox) :-
    nnf(and(Concept1, Concept2), IntersectedConcept),
    traitement_Tbox,
    traitement_Abox,
    nnf_assertion((anything, IntersectedConcept), SimplifiedAssertion),
    append([SimplifiedAssertion], Abi, Abi1).