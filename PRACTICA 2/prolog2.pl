:- module(_,_,[classic,assertions,regtypes,dynamic]).

:- dynamic memo/2.

:- doc(title, "Practica 2 - COMPRESION DE SECUENCIAS").
:- doc(subtitle, "ISO-Prolog").

:- doc(author,"David de Frutos, B190372").

:- doc(module, "Este modulo define los predicados de la practica 2 para la que se quiere realizar la compresion de una secuencia de caracter").

:- prop alumno_prode/4 #"Datos del alumno que realiza la entrega. @includedef{alumno_prode/4}".
alumno_prode('De Frutos', 'Zafra', 'David', 'B190372').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%% PRELIMINARES %%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- pred comprimir(Inicial,Comprimida) #"donde @var{Inicial} es la secuencia original de caracteres y @var{Comprimida} es el resultado de aplicar las operaciones necesarias a la cadena @var{Inicial} para comprimirla. @includedef{comprimir/2}".

comprimir(Inicial,Comprimida) :-
    limpia_memo,
    compresion_recursiva(Inicial,Comprimida).

:- pred limpia_memo #"es el encargado de limpiar los lemas almacenados en la memoria. @includedef{limpia_memo/0}".

limpia_memo :-
    retractall(memo(_,_)).

:- pred compresion_recursiva(Inicial,Comprimida) #"es el predicado al que se llama para realizar la compresion de manera recursiva. @includedef{compresion_recursiva/2}".

compresion_recursiva(Inicial,Comprimida) :-
    mejor_compresion_memo(Inicial,Comprimida).


:- pred partir(Todo,Parte1,Parte2) #"este predicado se verifica si @var{Parte1} y @var{Parte2} son dos subsecuencias no vacias que concatenadas forman la secuencia @var{Todo}. @includedef{partir/3}".

partir(Todo,Parte1,Parte2) :-
    append(Parte1,Parte2,Todo),
    length(Parte1,N1),
    length(Parte2,N2),
    N1>0,
    N2>0.


:- pred parentesis(Parte,Num,ParteNum) #"donde @var{ParteNum} es la lista de caracteres resultado de componer la lista @var{Parte} con el numero de repeticiones @var{Num}, añadiendo parentesis solamente si @var{Parte} tiene 2 elementos o mas. @includedef{parentesis/3}".

parentesis(Parte,Num,ParteNum) :-
    integer(Num),
    length(Parte,N1),
    (N1<2 ->
        append(Parte,[Num],ParteNum)
    ;  
        append(['('|Parte],[')',Num],ParteNum)
    ),
    !.

:- pred se_repite(Cs,Parte,Num0,Num) #"tiene exito si @var{Cs} se obtiene por repetir N veces la secuencia @var{Parte}. El argumento @var{Num} incrementa @var{Num0} en N. @includedef{se_repite/4}".

se_repite([],_,Num0,Num0).

se_repite(Cs,Cs,Num0,Num) :-
    Num is Num0+1,
    !.
    
se_repite(Cs,Parte,Num0,Num) :-
    append(Parte,Rest,Cs),
    se_repite(Rest,Parte,Num0,N),
    Num is N+1,
    !.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%% FASE A %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred repeticion(Inicial,Comprimida) #"basandose en los predicados partir/3 y se_repite/4 debe identificar un prefijo (o parte) que por repeticion permita obtener la secuencia inicial. Esta parte sera posteriormente comprimida. @includedef{repeticion/2}".

repeticion(Inicial,ParteNum) :-
    partir(Inicial,Parte1,_Parte2),
    se_repite(Inicial,Parte1,0,Num),
    compresion_recursiva(Parte1,Comprimida),
    parentesis(Comprimida,Num,ParteNum),
    !.
    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%% FASE B %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred compresion(Inicial,Comprimida) #"tendra dos alternativas: llamar a repeticion/2 o a division/2 para obtener todas las posibles compresiones por backtracking, tanto optimas como no optimas. @includedef{compresion/2}".

compresion(Inicial,Comprimida) :-
    repeticion(Inicial,Comprimida).

compresion(Inicial,Comprimida) :-
    division(Inicial,Comprimida).


:- pred division(Inicial,Comprimida) #"debe partir la lista inicial en dos partes y llamar a compresion_recursiva/2 de forma recursivas con cada una de ellas para finalmente concatenar los resultados. Esto dara mas posibilidad a encontrar repeticiones @includedef{division/2}".
division(Inicial,Final) :-
    partir(Inicial,Parte1,Parte2),
    compresion_recursiva(Parte1,Comprimida1),
    compresion_recursiva(Parte2,Comprimida2),
    append(Comprimida1,Comprimida2,Final).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%% FASE C %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- pred mejor_compresion(Inicial,Comprimida) #"intentara encontrar compresiones que reduzcan el tamano, es decir, el resultado final de @var{Comprimida} sera la que tenga el menor tamaño, la solucion mas optima @includedef{mejor_compresion/2}".

mejor_compresion([X],[X]).

mejor_compresion(Inicial,Comprimida) :-
    findall(LComp,compresion(Inicial,LComp),LAcum),
    sol_optima(LAcum,Comprimida).

:- pred sol_optima(Posible_sol,Mejor) #"debe encontrar la solucion con la menor longitud entre una serie de soluciones obtenidas con la llamada al predicado findall @var{Posible_sol} es la lista en la que se han ido almacenando las diferentes listas comprimidas @includedef{sol_optima/2}".

sol_optima([X],X).

sol_optima([X|Xs],Mejor) :-
    sol_optima(Xs,Mejor1),
    length(X,N1),
    length(Mejor1,N2),
    (N1<N2 ->
        Mejor=X
    ;
        Mejor=Mejor1
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%% FASE D %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred mejor_compresion_memo(Inicial,Comprimida) #"debe obtener la compresion mas optima posible, utilizando la memorizacion de lemas, lo que hara esta solucion aun mas eficiente al poder recordar aquellas que ya ha comprobado @includedef{mejor_compresion_memo/2}".

mejor_compresion_memo(Inicial,Comprimida) :-
    memo(Inicial,Comprimida),!.

mejor_compresion_memo(Inicial,Comprimida) :-
    mejor_compresion(Inicial,Comprimida),
    assert(memo(Inicial,Comprimida)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%% TESTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- test partir(Todo,Parte1,Parte2) : (Todo = [1,2,3,4]) => (Parte1 = [1], Parte2 = [2,3,4]; Parte1 = [1,2], Parte2 = [3,4]) + not_fails #"Prueba 1 - Se divide en dos listas no vacias que son subsecuencias.".

:- test parentesis(Parte,Num,ParteNum) : (Parte = [a,b,c], Num = 3) => (ParteNum = ['(',a,b,c,')',3]) + not_fails #"Prueba 2 - Parte contiene 3 elementos.".

:- test parentesis(Parte,Num,ParteNum) : (Parte = [a], Num = 2) => (ParteNum = [a,2]) + not_fails #"Prueba 3 - Parte contiene 1 elemento.".

:- test se_repite(Cs,Parte,Num0,Num) : (Cs = [a,b,c], Parte = [a,b,c], Num0 = 0) => (R = 1) + not_fails #"Prueba 4 - [a,b,c] se repite una vez en [a,b,c].".

:- test se_repite(Cs,Parte,Num0,Num) : (Cs = [a,b,c,a,b,c,a,b,c], Parte = [a,b,c], Num0 = 0) => (R = 3) + not_fails #"Prueba 5 - [a,b,c,a,b,c,a,b,c] se repite tres veces en [a,b,c].".

:- test se_repite(Cs,Parte,Num0,Num) : (Cs = [a,b,c,a,c,a,b,c], Parte = [a,b,c], Num0 = 0) => (R = 0) + fails #"Prueba 6 - [a,b,c,a,c,a,b,c] no se puede obtener repitiendo [a,b,c].".

:- test se_repite(Cs,Parte,Num0,Num) : (Cs = [], Parte = [a,b,c], Num0 = 0) => (R = 0) + not_fails #"Prueba 7 - [] se obtiene repitiendo 0 veces [a,b,c].".

:- test repeticion(Inicial,ParteNum) : (Inicial = [a,a,a,a,a,a,a]) => (R = [a,7]) + not_fails #"Prueba 8 - [a,a,a,a,a,a,a] se obtiene repitiendo 7 veces [a].".

:- test repeticion(Inicial,ParteNum) : (Inicial = [a,b,a,b,a,b]) => (R = ['(',a,b,')',3]) + not_fails #"Prueba 9 - [a,b,a,b,a,b] se obtiene repitiendo 3 veces [a,b].".

:- test repeticion(Inicial,ParteNum) : (Inicial = [a,b,a,b,a]) => (R = 0) + fails #"Prueba 10 - [a,b,a,b,a] no se puede obtener repitiendo ninguna secuencia.".

:- test mejor_compresion(Inicial,Comprimida) : (Inicial = [a,b,a,b,a,b]) => (Comprimida=['(',a,b,')',3]) + not_fails #"Prueba 11 - se obtiene la mejor compresion posible de [a,b,a,b,a,b].".

:- test sol_optima(Posible_sol,Mejor) : (Posible_sol = [[a,b]]) => (Mejor=[a,b]) + not_fails #"Prueba 12 - La solucion optima entre las posibles soluciones ([a,b]) es [a,b].".

:- test sol_optima(Posible_sol,Mejor) : (Posible_sol = [[a,b],[a,b,c],[a,b,c,d],[a]]) => (Mejor=[a]) + not_fails #"Prueba 13 - La solucion optima entre las posibles soluciones ([[a,b],[a,b,c],[a,b,c,d],[a]) es [a].".