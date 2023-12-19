programme :-
    load_files('donnees.pl'),
    load_files('partie1.pl'),
    load_files('partie2.pl'),
    load_files('partie3.pl'),
    
    premiere_etape(Tbox, Abi, Abr),
    deuxieme_etape(Abi,Abi1,Tbox),
    troisieme_etape(Abi1,Abr), nl,
    write('Fin !').
    
programme.