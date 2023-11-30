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

/* TBox */

[(sculpteur,and(personne,some(aCree,sculpture))),
(auteur,and(personne,some(aEcrit,livre))),
(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))), 
(parent,and(personne,some(aEnfant,anything)))]

/* ABox */

[(michelAnge,personne), (david,sculpture), (sonnets,livre),
(vinci,personne), (joconde,objet)]

/* Rôles */

[(michelAnge, david, aCree), (michelAnge, sonnet, aEcrit),(vinci,
joconde, aCree)]
