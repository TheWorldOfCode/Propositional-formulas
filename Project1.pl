/*
** ---------
** Task 1.1
** ---------
** A propositional symbol is represented as p(N), where N is a positive integer,
** this is done by defining a integer bigger than 0.
** Then the propositional functions are defined as follows,
** neg/1, impl/2, and/2, or/2, equiv/2 and xor/2, with this in mind af wff tells os
** if it is a propositional formula.
*/
wff(p(N))       :-  integer(N), N>0.
wff(neg(X))     :-  wff(X).
wff(impl(X,Y))  :-  wff(X) , wff(Y).
wff(and(X,Y))   :-  wff(X) , wff(Y).
wff(or(X,Y))    :-  wff(X) , wff(Y).
wff(equiv(X,Y)) :-  wff(X) , wff(Y).
wff(xor(X,Y))   :-  wff(X) , wff(Y).
/*
** ---------
** Task 1.2
** ---------
** This predicate gives a True or False value, when a valuation and a propositional formula,
** are given. The predicate checks if the formula holds under the given valuation.
*/
satisfies(V,p(F))         :-  member(F,V).
satisfies(V, neg(X))      :-  not(satisfies(V,X)).

satisfies(V, impl(X,_))   :-  not(satisfies(V,X)), !.
satisfies(V, impl(_,Y))   :-  satisfies(V,Y).

satisfies(V, and(X,Y))    :-  satisfies(V,X)  , satisfies(V,Y).

satisfies(V,  or(_,Y))    :-  satisfies(V,Y), !.
satisfies(V,  or(X,_))    :-  satisfies(V,X).

satisfies(V, equiv(X,Y))  :-  satisfies(V,X)      , satisfies(V,Y), !.
satisfies(V, equiv(X,Y))  :-  not(satisfies(V,X)) , not(satisfies(V,Y)).

satisfies(V, xor(X,Y))    :-  satisfies(V,X)       , not(satisfies(V,Y)), !.
satisfies(V, xor(X,Y))    :-  not(satisfies(V,X))  , satisfies(V,Y).
/*
** ---------
** Task 1.3
** ---------
** find_val_tt finds all valuation that makes the formula retrun True.
*/
find_val_tt(F, V)               :- find_all_p(F,Z) , get_subset(Z,V) , satisfies(V,F).
/*
** As a sub predicate to find_val_tt there is defined a predicate find_all_p/2.
** This predicate finds all p(N) in a propositional formula,
** returns them in a list.
*/
find_all_p(p(N), [N]).
find_all_p(neg(X), Z)           :- find_all_p(X,P) , append(P,[],Z).
find_all_p(impl(X,Y), Z)        :- find_all_p(X,P) , find_all_p(Y,Q) , append(P,Q,Z).
find_all_p(and(X,Y), Z)         :- find_all_p(X,P) , find_all_p(Y,Q) , append(P,Q,Z).
find_all_p(or(X,Y), Z)          :- find_all_p(X,P) , find_all_p(Y,Q) , append(P,Q,Z).
find_all_p(equiv(X,Y), Z)       :- find_all_p(X,P) , find_all_p(Y,Q) , append(P,Q,Z).
find_all_p(xor(X,Y), Z)         :- find_all_p(X,P) , find_all_p(Y,Q) , append(P,Q,Z).
/*
** As the last sub predicate to find_val_tt, this finds all subsets of a list.
** get_subset/2
*/
get_subset([], []).
get_subset([X|Tail1], [X|Tail2]) :- get_subset(Tail1, Tail2).
get_subset([_|Tail1], Tail2)     :- get_subset(Tail1, Tail2).
/*
** ---------
** Task 1.4
** ---------
** taut_tt uses find_val_tt to find out if a propositional formula is a tautology.
*/
taut_tt(F)   :- not(find_val_tt(neg(F),_)).
/*
** sat_tt uses find_val_tt to find out if a propositional formula is satisfiable.
*/
sat_tt(F)    :- find_val_tt(F,_).
/*
** unsat_tt uses find_val_tt to find out if a propositional formula is unsatisfiable.
*/
unsat_tt(F)  :- not(find_val_tt(F,_)).
/*
** ---------
** Task 2.5
** ---------
** This predicate takes the propositional formula and break down the formula into leafs.
** Which returns in list for ever step.
*/
tableau(p(N), [p(N)]).
tableau(neg(p(N)), [neg(p(N))]).
tableau(neg(neg(X)),  N)    :- tableau(X, N).

tableau(impl(X,_),  N)      :- tableau(neg(X),N).
tableau(impl(_,Y),  N)      :- tableau(Y,N).
tableau(neg(impl(X,Y)), N)  :- tableau(X,Q)      , tableau(neg(Y),B) , append(Q,B,N).

tableau(and(X,Y), N)        :- tableau(X,Q)      , tableau(Y,B)      , append(Q,B,N).
tableau(neg(and(X,_)), N)   :- tableau(neg(X),N).
tableau(neg(and(_,Y)), N)   :- tableau(neg(Y),N).

tableau(or(X,_),  N)        :- tableau(X,N).
tableau(or(_,Y),  N)        :- tableau(Y,N).
tableau(neg(or(X,Y)), N)    :- tableau(neg(X),Q) , tableau(neg(Y),B) , append(Q,B,N).

tableau(equiv(X,Y), N)      :- tableau(X,Q)      , tableau(Y,B)      , append(Q,B,N).
tableau(equiv(X,Y), N)      :- tableau(neg(X),K) , tableau(neg(Y),P) , append(K,P,N).

tableau(neg(equiv(X,Y)), N) :- tableau(X,Q)      , tableau(neg(Y),B) , append(Q,B,N).
tableau(neg(equiv(X,Y)), N) :- tableau(neg(X),K) , tableau(Y,P)      , append(K,P,N).

tableau(xor(X,Y), N)         :- tableau(X,Q)      , tableau(neg(Y),B) , append(Q,B,N).
tableau(xor(X,Y), N)         :- tableau(neg(X),K) , tableau(Y,P)      , append(K,P,N).

tableau(neg(xor(X,Y)), N)    :- tableau(X,Q)      , tableau(Y,B)      , append(Q,B,N).
tableau(neg(xor(X,Y)), N)    :- tableau(neg(X),K) , tableau(neg(Y),P) , append(K,P,N).
/*
** ---------
** Task 2.6
** ---------
** find_val_tab/2 finds all valuation that makes the formula retrun True.
*/
find_val_tab(F, V)                  :-  tableau(F,M), remove_all(M,V) , satisfies(V,F).
/*
** As a sub predicate to find_val_tab there is defined a predicate remove_all/2.
** This predicate removes all unnecessary symbols such as p() and neg(),
** in other terms it extracts N.
*/
remove_all([],[]).
remove_all([p(X)|Tail1],[X|Tail2])  :- remove_all(Tail1,Tail2).
remove_all([neg(p(_))|Tail1],Tail2) :- remove_all(Tail1,Tail2).
/*
** ---------
** Task 2.7
** ---------
** taut_tab uses find_val_tab to find out if a propositional formula is a tautology.
*/
taut_tab(F)   :- not(find_val_tab(neg(F),_)).
/*
** sat_tab uses find_val_tab to find out if a propositional formula is a satisfiable.
*/
sat_tab(F)    :- find_val_tab(F,_).
/*
** unsat_tab uses find_val_tab to find out if a propositional formula is a unsatisfiable.
*/
unsat_tab(F)  :- not(find_val_tab(F,_)).
