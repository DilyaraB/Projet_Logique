/* Jeu de Test2 */

/* TBOX */

equiv(femme, and (personne, femelle)).
equiv(homme, and (personne, not(femelle))).
equiv(mere, and (femme, some(aEnfant, personne))).
equiv(pere, and (homme, some(aEnfant, personne))).
equiv(parent, or(pere, mere)).
equiv(grandmere, and(mere, some(aEnfant, parent))).
equiv(mereSansFile, or(mere, all(aEnfant, not(femme)))).
equiv(epouse, and(femme, some(aCommeMari, homme))).

/* ABOX */

inst(marie, mereSansFile).
inst(pierre, pere).
inst(alice, femme).

instR(marie, pierre, aEnfant).
instR(marie, paul).
instR(pierre, alice).

/* Concepts atomiques */

cnamea(femelle).
cnamea(personne).

/* Concepts non-atomiques */

cnamena(femme).
cnamena(homme).
cnamena(mere).
cnamena(pere).
cnamena(parent).
cnamena(grandmere).
cnamena(mereSansFile).
cnamena(epouse).

/* Instances */

iname(marie).
iname(pierre).
iname(alice).
iname(paul).

/* Roles */

rname(aCommeMari).
rname(aEnfant).


