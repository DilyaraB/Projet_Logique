/* jeu de Test1 : exercice3 td4 */


/* TBOX */
equiv(attiranceExcHomme, all(amant, homme)).
equiv(femmeHetero, and(femme, attiranceExcHomme)).
equiv(femme, not(homme)).
equiv(travesti, and(not(femme), habilleEnFemme)).

/* ABOX */
inst(elisabeth, femmeHetero).
inst(eon, habilleEnFemme).

instR(elisabeth, eon, amant).

/* Concepts atomiques */

cnamea(homme).
cnamea(habilleEnFemme).

/* Concepts non-atomiques */

cnamena(attiranceExcHomme).
cnamena(femmeHetero).
cnamena(femme).
cnamena(travesti).

/* Instances */

iname(elisabeth).
iname(eon).

/* Rôles */

rname(amant).
