%% -*- mode: prolog; coding: utf-8 -*-

%% GNU Prolog défini `new_atom`, mais SWI Prolog l'appelle `gensym`.
genatom(X, A) :-
    (predicate_property(new_atom/2, built_in);    % Older GNU Prolog
     predicate_property(new_atom(_,_), built_in)) % Newer GNU Prolog
    -> new_atom(X, A);
    gensym(X, A).

%% type(+T)
%% Prédicat qui décrit la forme d'un type d'une valeur dans Cat.
type(int).
type(bool).
type(list(T)) :- type(T).
type((T1 -> T2)) :- stype(T1), stype(T2).
type(var(X)) :- atom(X).                        % A type variable.
type(forall(X, T)) :- atom(X), type(T).         % A polymorphic type.

%% stype(+ST)
%% Prédicat qui décrit la forme d'un type d'une pile dans Cat.
stype(nil).
stype(H^T) :- type(H), stype(T).

%% value(+V)
%% Prédicat qui décrit la forme d'une valeur dans Cat.
value(Num) :- number(Num).
value(true).
value(false).
value(nil).                             % An empty list.
value(X^Xs) :- value(X), value(Xs).     % A single-linked list node.
value(Fun) :- function(Fun).

%% stack(+S)
%% Prédicat qui décrit la forme d'une pile dans Cat.
stack(nil).
stack(V^VS) :- value(V), stack(VS).

%% functions(+Ops)
%% Prédicat qui décrit la forme d'une function dans Cat.
function([]).
function([Op | Ops]) :- oper(Op), function(Ops).

%% oper(+Op)
%% Prédicat qui décrit la forme d'une opération dans Cat.
oper(dup).                              % Duplique le ToS.
oper(swap).                             % Échange les deux ToS.
oper(pop).                              % Enlève l'élément au ToS.
oper(get(N)) :- integer(N), N >= 0.     % Cherche le Nième élément de la pile.
oper(set(N)) :- integer(N), N >= 0.     % Change le Nième élément de la pile.
oper(Val) :- value(Val).                % Ajoute la constante Val sur ToS.
oper(add).                              % Fait la somme des 2 éléments au ToS.
oper(if).                               % Teste le booléen au ToS.
oper(cons).                             % Crée un nouvel élément de liste.
oper(emptyp).                           % Teste si la liste au ToS est vide.
oper(car).                              % Retourne la tête de la liste au ToS.
oper(cdr).                              % Retourne la queue de la liste au ToS.
oper(apply).                            % Appelle une fonction.
oper(papply).                           % Construit une fermeture.
oper(Op:Type) :- oper(Op), type(Type).  % Annotation de type explicite.

%% Prédicats auxiliaires.

%% stack_get_nth(+N, +S, -V)
%% Renvoie le Nième élément de la pile S.
stack_get_nth(0, H^_, H) :- !.
stack_get_nth(N, _^T, V) :- Next is N-1, stack_get_nth(Next, T, V).

%% stack_set_nth(+N, +V, +S1, -S2)
%% Renvoie une pile S2 identique à S1 sauf pour le Nième élément,
%% remplacé par V.
stack_set_nth(0, V, _^T, V^T) :- !.
stack_set_nth(N, V, H^T, H^Rest) :-
  Next is N-1, stack_set_nth(Next, V, T, Rest).

%%% Polymorphisme paramétrique  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% type_subst(+T1, +X, +T2, -T3)
%% Renvoie T3 = T1[T2/X].
%% I.e. T3 est le résultat de la substitution de X par T2 dans T1.
%% Utile pour implémenter la règle d'élimination du polymorphisme.
type_subst(T1, _, _, T2) :- var(T1), !, T1 = T2.
type_subst(var(Y), X, T1, T2) :- X = Y -> T2 = T1; T2 = var(Y).
type_subst(int, _, _, int).
type_subst(bool, _, _, bool).
type_subst(list(T1), X, T, list(T2)) :- type_subst(T1, X, T, T2).
type_subst((T11 -> T12), X, T, (T21 -> T22)) :-
        type_subst(T11, X, T, T21), type_subst(T12, X, T, T22).
type_subst(forall(X1, T1), X, T, forall(X2, T2)) :-
        % utilisé pour les fonctions curried (\x -> \y -> ...)
        %% Fait une étape de renommage α pour éviter la capture de nom.
        genatom(X1, X2), type_subst(T1, X1, var(X2), T12),
        type_subst(T12, X, T, T2).
type_subst(nil, _, _, nil).
type_subst(H1^T1, X, T, H2^T2) :-
        type_subst(H1, X, T, H2), type_subst(T1, X, T, T2).

%% type_instantiate(+T1, ?T2)
%% T2 est une instantiation de T1.
type_instantiate(T, T).
type_instantiate(forall(X, T1), T3) :-
    type_subst(T1, X, _, T2), type_instantiate(T2, T3).

%% type_uiv(+T, -XS) // uiv = uninstanciated variable
%% Cherche les variables Prolog non instanciées dans le type T, les instancie
%% par `var(X)` avec un X instancié à un atome tout frais, et
%% renvoie la liste des atomes frais ainsi créés.
%% Utile pour implémenter la règle d'introduction du polymorphisme.
type_uiv(var(X), []) :- atom(X), !.
type_uiv(var(X), [X]) :- genatom(t, X), !.
type_uiv(int, []).
type_uiv(bool, []).
type_uiv(list(T), VS) :- type_uiv(T, VS).
type_uiv(X^Xs, VS) :- type_uiv(X,V1),type_uiv(Xs,RestOfVS),
  append(V1,RestOfVS,VS).
type_uiv((X->Y), VS) :- type_uiv(X,V1), type_uiv(Y,V2), append(V1,V2,VS).


%%% Inférence de types  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% typeof_val(+V, -T)
%% Infère le type T de la valeur V.  Équivalent à "⊢ V : T".
%% Si V est une fonction, renvoie un type T aussi polymorphe que possible.
%% Pour trouver le polymorphisme, utiliser `type_uiv`.
typeof_val(Num, int) :- number(Num).
typeof_val(true, bool).
typeof_val(false, bool).
typeof_val(nil, list(T)) :- type(T), !.
% TODO Cut pour pas avoir des List de List à l'infini ?
typeof_val(X^Xs, list(T)) :- typeof_val(X, T), typeof_val(Xs, list(T)), !.
typeof_val(X^Xs, TS) :- typeof_val(X, T1), typeof_val(Xs, T2),
    TS = T1^T2.
typeof_val([], forall(T,(var(T)->var(T)))) :- type_uiv(_,[T]), !.
%faire en sorte que ST->ST renvoie juste t1 -> t1 pour avoir
% forall(t1, var(t1) -> var(t1))
typeof_val(V, Type) :-
    var(Type),
    typeof(V,Input,Output),
    FunctionType = (Input->Output),
    type_uiv(FunctionType,Variables),
    polymorph_me(Variables, FunctionType, Type).

polymorph_me([], FunctionType, FunctionType).
polymorph_me([Head|Tail], FunctionType, forall(Head, X)) :-
  polymorph_me(Tail, FunctionType, X).


%% typeof_op(+Op, ?ST1, ?ST2)
%% Si l'opération Op est exécutée avec une pile de type ST1, le résultat est
%% une pile de type ST2.  Équivalent à "⊢ Op : ST1 ⇒ ST2".
typeof_op(dup, T^ST, T^T^ST).
typeof_op(swap, T1^T2^ST, T2^T1^ST).
typeof_op(pop, _^ST, ST).
typeof_op(get(_), T0^MID^TN^ST, TN^T0^MID^TN^ST).
typeof_op(set(_), T^T0^MID^_^ST, T0^MID^T^ST).
typeof_op(add, int^int^ST, int^ST).
typeof_op(if, bool^T^T^ST, T^ST).
typeof_op(cons, T^list(T)^ST, list(T)^ST).
typeof_op(emptyp, list(_)^ST, bool^ST).
typeof_op(car, list(T)^ST, T^ST).
typeof_op(cdr, list(T)^ST, list(T)^ST).
typeof_op(apply, (ST1->ST2)^ST1, ST2).
typeof_op(papply, ((T^ST1)->ST2)^T^ST3, (ST1->ST2)^ST3).
typeof_op(Op:T, ST, T^ST) :- typeof_op(Op, ST, T^ST).
typeof_op(Val, ST, T^ST) :- typeof_val(Val, T).

%% typeof(+Ops, ?ST1, ?ST2)
%% Si les opération Ops sont exécutées avec une pile de type ST1, le résultat
%% est une pile de type ST2.
typeof([], S, S).
typeof([Op | Ops], S1, S3) :- typeof_op(Op, S1, S2), typeof(Ops, S2, S3).

%%% Evaluation  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% eval(+Ops, +S1, -S2)
%% Évalue les opértions Ops avec S1 comme pile de départ.
%% Renvoie la pile résultante S2.
eval([], S, S) :- !.
% On cut à chaque clause pour éviter que les fonctions se fassent interpréter
% comme des valeurs (si jamais argument invalide, ex: get(4) sur un stack
% de taille 4 (car on commence à compter à 0))
eval(dup, Elem_1^S, Elem_1^Elem_1^S) :- !.
eval(swap, Elem_1^Elem_2^S, Elem_2^Elem_1^S) :- !.
eval(pop, _^S, S) :- !.
eval(get(N), S, Nth_elem^S) :- !,
    stack_get_nth(N,S,Nth_elem).
eval(set(N), V^S, Result) :- !,
    stack_set_nth(N,V,S,Result).
eval(add, A^B^S, C^S) :- !,
    typeof_val(A,X),
    typeof_val(B,Y),
    typeof_val(S,Z),
    typeof([add],X^Y^Z,_), C is A + B.
eval(if, Cond^Then^Else^S,Result^S) :- !,
    typeof_val(Cond,X),
    typeof_val(Then,Y),
    typeof_val(Else,Z),
    typeof_val(S, W),
    typeof([if],X^Y^Z^W,_),
    (Cond -> Result = Then ; Result = Else).
eval(cons, H^T^S, MyCons^S) :- !,
    typeof_val(H,X),
    typeof_val(T,Y),
    typeof_val(S,Z),
    typeof([cons],X^Y^Z,_),
    MyCons = (H^T).
eval(emptyp, L^S, Bool^S) :- !,
    typeof_val(L,X),
    typeof_val(S,Y),
    typeof([emptyp],X^Y,_),
    (L = (nil) -> Bool = true; Bool = false).
eval(car, L^S, H^S) :- !,
    typeof_val(L,X),
    typeof_val(S,Y),
    typeof([car],X^Y,_),
    L = H^_.
eval(cdr,L^S, T^S) :- !,
    typeof_val(L,X),
    typeof_val(S,Y),
    typeof([cdr],X^Y,_),
    L = _^T.
eval(apply, Function^Arg, Result) :- eval(Function,Arg,Result), !.
eval(papply, Function^Arg^S, Result) :- !,
    ( Function = [_|_] -> true; Function = []),
    Result = [Arg|Function]^S.
eval([ [] | Ops], S1, S2) :- !, eval(Ops,[]^S1,S2).
eval([ [Func|Tion] | Ops], S1, S2) :- !, eval(Ops,[Func|Tion]^S1,S2).
eval([Op | Ops], S1, S2) :- !, eval(Op,S1,S3), eval(Ops,S3,S2).
eval(Val,S,Val^S) :- !.
