:- use_module(library(matrix)).
:- use_module(assoc).
:- use_module(code).

/* 

  Support for matrix expressions

  TODO:
  - implement the derivative predicates

 */

%===============================================================================
% Grammar
%===============================================================================

matrix_expr(lit(_)). % TODO: check matrix
matrix_expr(var(_)).
matrix_expr(add(E1,E2)) :-
  matrix_expr(E1),
  matrix_expr(E2).
matrix_expr(mul(E1,E2)) :-
  matrix_expr(E1),
  matrix_expr(E2).
matrix_expr(hadamard(E1,E2)) :-
  matrix_expr(E1),
  matrix_expr(E2).
matrix_expr(transpose(E)) :-
  matrix_expr(E).
matrix_expr(map(F,E)) :- % TODO: F should be an expression with only 1 variable
  expr(F),
  matrix_expr(E). 
matrix_expr(vec2vec(_Pred,E)) :-
  matrix_expr(E).
  

% %===============================================================================
% % Dimension
% %===============================================================================
% 
% dim(lit(N),X,Y).
% dim(var(v(_,X,Y)),X,Y).
% dim(add(E1,E2),X,Y) :-
%   dim(E1,X,Y),
%   dim(E2,X,Y).
% dim(mul(E1,E2),X,Y) :-
%   dim(E1,X,Z),
%   dim(E2,Z,Y).
% dim(transpose(E),X,Y) :-
%   dim(E,Y,X).
% dim(exp(E),X,Y) :-
%   dim(E,X,Y).
% dim(negate(E),X,Y) :-
%   dim(E,X,Y).
% dim(invert(E),X,Y) :-
%   dim(E,Env,N1),
%   matrix_inversion(N1,N).

%===============================================================================
% Evaluation
%===============================================================================

matrix_eval(lit(N),_Env,N).
matrix_eval(var(X),Env,N) :-
  lookup(X,Env,N).
matrix_eval(add(E1,E2),Env,N) :-
  matrix_eval(E1,Env,N1),
  matrix_eval(E2,Env,N2),
  matrix_sum(N1,N2,N).
matrix_eval(mul(E1,E2),Env,N) :-
  matrix_eval(E1,Env,N1),
  matrix_eval(E2,Env,N2),
  matrix_multiply(N1,N2,N).
matrix_eval(hadamard(E1,E2),Env,N) :-
  matrix_eval(E1,Env,N1),
  matrix_eval(E2,Env,N2),
  matrix_hadamard(N1,N2,N).
matrix_eval(transpose(E),Env,N) :-
  matrix_eval(E,Env,N1),
  matrix_transpose(N1,N). 
matrix_eval(map(F,E),Env,N) :-
  matrix_eval(E,Env,N1),
  maplist(maplist(matrix_element_eval(F)),N1,N).
matrix_eval(vec2vec(Pred,E),Env,N) :-
  matrix_eval(E,Env,N1),
  maplist(maplist(mklit),N1,N2),
  call(Pred,N2,N3),
  maplist(maplist(eval_varfree),N3,N).

matrix_element_eval(E,V,R) :-
  eval(E,env(V),R).

mklit(X,lit(X)).
mkadd(E1,E2,add(E1,E2)).
 
eval_varfree(E,N) :-
  eval(E,noenv,N).
 
%===============================================================================
% Symbolic Differentiation
%===============================================================================

matrix_symbad(lit(N),_X,lit(Zero)) :-
  maplist(maplist(zero),N,Zero).
% matrix_symbad(var(Y),X,lit(DF)) :-
%   ( X == Y -> DF = 1 ; DF = 0).
matrix_symbad(add(E1,E2),X,add(DF1,DF2)) :-
  matrix_symbad(E1,X,DF1),
  matrix_symbad(E2,X,DF2).
matrix_symbad(mul(E1,E2),X,DF) :-
  matrix_symbad(E1,X,DF1),
  matrix_symbad(E2,X,DF2),
  DF = add(mul(E2,DF1),mul(E1,DF2)).
matrix_symbad(hadamard(E1,E2),X,add(hadamard(DF1,E2),hadamard(E1,DF2))) :-
  matrix_symbad(E1,X,DF1),
  matrix_symbad(E2,X,DF2).
matrix_symbad(transpose(E),X,transpose(DF)) :-
  matrix_symbad(E,X,DF).
matrix_symbad(map(F,E),X,hadamard(map(F1,E),DF)) :-
  symbad(F,1,F1),
  matrix_symbad(E). 

zero(_,0).

% %===============================================================================
% % Symbolic Differentiation with Expression Reconstruction
% %===============================================================================
% 
% symbad(lit(N),_X,lit(N),lit(0)).
% symbad(var(Y),X,var(Y),lit(DF)) :-
%   ( X == Y -> DF = 1 ; DF = 0).
% symbad(add(E1,E2),X,add(F1,F2),add(DF1,DF2)) :-
%   symbad(E1,X,F1,DF1),
%   symbad(E2,X,F2,DF2).
% symbad(mul(E1,E2),X,mul(F1,F2),DF) :-
%   symbad(E1,X,F1,DF1),
%   symbad(E2,X,F2,DF2),
%   DF = add(mul(F2,DF1),mul(F1,DF2)).
% 
% test_symbad2 :-
%   X = 1,
%   Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(X)),
%   symbad(Expr,X,Expr2,R),
%   pretty(R),writeln(' = B * (B * 0 + 2 * 1 + 0) + (2 * B + 1) * 1 ?'),
%   pretty(Expr2),write(' = '), pretty(Expr), writeln(' ? ').
% 
% %===============================================================================
% % Forward-Mode Automatic Differentiation Specification
% %===============================================================================
% 
% ad_spec(E,X,Env,N,DN) :-
%   symbad(E,X,F,DF),
%   eval(F,Env,N),
%   eval(DF,Env,DN).
% 
% %===============================================================================
% % Forward-Mode Automatic Differentiation
% %===============================================================================
% 
% fwdad(lit(N),_X,_Env,F,DF) :-
%   F  = N,
%   DF = 0.
% fwdad(var(Y),X,Env,F,DF) :-
%   lookup(Y,Env,F),
%   ( X == Y -> DF = 1 ; DF = 0).
% fwdad(add(E1,E2),X,Env,F,DF) :-
%   fwdad(E1,X,Env,F1,DF1),
%   fwdad(E2,X,Env,F2,DF2),
%   F is F1 + F2,
%   DF is DF1 + DF2.
% fwdad(mul(E1,E2),X,Env,F,DF) :-
%   fwdad(E1,X,Env,F1,DF1),
%   fwdad(E2,X,Env,F2,DF2),
%   F is F1 * F2,
%   DF is F2 * DF1 + F1 * DF2.
% 
% test_fwdad :-
%   X = 1,
%   Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(X)),
%   Env = env(5),
%   fwdad(Expr,X,Env,F1,DF1),
%   ad_spec(Expr,X,Env,F2,DF2),
%   pretty(Expr),nl,
%   write(F1),write(' = '),write(F2),writeln(' ?'),
%   write(DF1),write(' = '),write(DF2),writeln(' ?').
% 
% %===============================================================================
% % Forward-Mode Automatic Differentiation for Gradients
% %===============================================================================
% 
% fwdadgrad(lit(N),_Env,F,DF) :-
%   F = N,
%   empty_assoc(DF).
% fwdadgrad(var(Y),Env,F,DF) :-
%   lookup(Y,Env,F),
%   singleton_assoc(Y,1,DF).
% fwdadgrad(add(E1,E2),Env,F,DF) :-
%   fwdadgrad(E1,Env,F1,DF1),
%   fwdadgrad(E2,Env,F2,DF2),
%   F is F1 + F2,
%   union_with_assoc(plus,DF1,DF2,DF).
% fwdadgrad(mul(E1,E2),Env,F,SDF) :-
%   fwdadgrad(E1,Env,F1,DF1),
%   fwdadgrad(E2,Env,F2,DF2),
%   F is F1 * F2,
%   map_assoc(times(F2),DF1,SDF1),
%   map_assoc(times(F1),DF2,SDF2),
%   union_with_assoc(plus,SDF1,SDF2,SDF).
% 
% /*
% plus(A,B,C) :- C is A + B.
% times(A,B,C) :- C is A * B.
% */
% 
% test_fwdadgrad :-
%   X = 1,
%   Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(X)),
%   Env = env(5),
%   fwdadgrad(Expr,Env,F1,DF1),
%   assoc_to_list(DF1,L1),
%   ad_spec(Expr,X,Env,F2,DF2),
%   pretty(Expr),nl,
%   write(F1),write(' = '),write(F2),writeln(' ?'),
%   write(L1),write(' = '),write([X-DF2]),writeln(' ?').
% 
% test_fwdadgrad2 :-
%   X = 1,
%   Y = 2,
%   Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(Y)),
%   Env = env(5,3),
%   fwdadgrad(Expr,Env,F1,DF1),
%   assoc_to_list(DF1,L1),
%   ad_spec(Expr,X,Env,F2,DF2),
%   ad_spec(Expr,Y,Env,F2,DF3),
%   pretty(Expr),nl,
%   write(F1),write(' = '),write(F2),writeln(' ?'),
%   write(L1),write(' = '),write([X-DF2,Y-DF3]),writeln(' ?').
% 
% %===============================================================================
% % Scalar Multipliers
% %===============================================================================
% 
% revad1(E,Env,F,DF) :-
%   revad1(E,Env,1,F,DF).
% 
% revad1(lit(N),_Env,_M,F,DF) :-
%   F = N,
%   empty_assoc(DF).
% revad1(var(Y),Env,M,F,DF) :-
%   lookup(Y,Env,F),
%   singleton_assoc(Y,M,DF).
% revad1(add(E1,E2),Env,M,F,DF) :-
%   revad1(E1,Env,M,F1,DF1),
%   revad1(E2,Env,M,F2,DF2),
%   F is F1 + F2,
%   union_with_assoc(plus,DF1,DF2,DF).
% revad1(mul(E1,E2),Env,M,F,DF) :-
%   times(M,F2,M1),
%   times(M,F1,M2),
%   revad1(E1,Env,M1,F1,DF1),
%   revad1(E2,Env,M2,F2,DF2),
%   F is F1 * F2,
%   union_with_assoc(plus,DF1,DF2,DF).
% 
% plus(A,B,C) :- freeze(A,freeze(B,C is A + B)).


% 
% test_revad1 :-
%   X = 1,
%   Y = 2,
%   Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(Y)),
%   pretty(Expr),nl,
%   Env = env(5,3),
%   revad1(Expr,Env,F1,DF1),
%   assoc_to_list(DF1,L1),
%   ad_spec(Expr,X,Env,F2,DF2),
%   ad_spec(Expr,Y,Env,F2,DF3),
%   write(F1),write(' = '),write(F2),writeln(' ?'),
%   write(L1),write(' = '),write([X-DF2,Y-DF3]),writeln(' ?').
% 
% %===============================================================================
% % Gradient Threading
% %===============================================================================
% 
% revad2(E,Env,F,DF) :-
%   empty_assoc(DF0),
%   revad2(E,Env,1,F,DF0,DF).
% 
% revad2(lit(N),_Env,_M,F) -->
%   { F = N }.
% revad2(var(Y),Env,M,F) -->
%   { lookup(Y,Env,F) },
%   insert_with_assoc(plus,Y,M).
% revad2(add(E1,E2),Env,M,F) -->
%   revad2(E1,Env,M,F1),
%   revad2(E2,Env,M,F2),
%   { F is F1 + F2 }.
% revad2(mul(E1,E2),Env,M,F) -->
%   { times(M,F2,M1) },
%   { times(M,F1,M2) },
%   revad2(E1,Env,M1,F1),
%   revad2(E2,Env,M2,F2),
%   { F is F1 * F2 }.
% 
% test_revad2 :-
%   X = 1,
%   Y = 2,
%   Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(Y)),
%   pretty(Expr),nl,
%   Env = env(5,3),
%   revad2(Expr,Env,F1,DF1),
%   assoc_to_list(DF1,L1),
%   ad_spec(Expr,X,Env,F2,DF2),
%   ad_spec(Expr,Y,Env,F2,DF3),
%   write(F1),write(' = '),write(F2),writeln(' ?'),
%   write(L1),write(' = '),write([X-DF2,Y-DF3]),writeln(' ?').
% 
% insert_with_assoc(Pred,K,V,A0,A1) :-
%   put_with_assoc(Pred,K,A0,V,A1).
% 
% %===============================================================================
% % Reverse-Mode AD, Destructively
% %===============================================================================
% 
% empty_array(N,Arr) :-
%   findall(0,between(1,N,_),List),
%   Arr =.. [grad|List].
% 
% insert_with_array(Pred,Var,Value,Arr) :-
%   arg(Var,Arr,OldValue),
%   call(Pred,OldValue,Value,NewValue),
%   setarg(Var,Arr,NewValue).
% 
% revad(E,Env,F,DF) :-
%   functor(Env,_,N),
%   empty_array(N,DF),
%   revad(E,Env,1,F,DF).
% 
% revad(lit(N),_Env,_M,F,_DF) :-
%   F = N.
% revad(var(Y),Env,M,F,DF) :-
%   lookup(Y,Env,F),
%   insert_with_array(plus,Y,M,DF).
% revad(add(E1,E2),Env,M,F,DF) :-
%   revad(E1,Env,M,F1,DF),
%   revad(E2,Env,M,F2,DF),
%   F is F1 + F2.
% revad(mul(E1,E2),Env,M,F,DF) :-
%   times(M,F2,M1),
%   times(M,F1,M2),
%   revad(E1,Env,M1,F1,DF),
%   revad(E2,Env,M2,F2,DF),
%   F is F1 * F2.
% revad(neg(E1),Env,M,F,DF) :-
%   freeze(M,freeze(F1,M1 is M * -F1)),
%   revad(E1,Env,M1,F1,DF),
%   F is -F1.
% revad(neg(E1),Env,M,F,DF) :-
%   freeze(M,freeze(F1,M1 is M * cos(F1))),
%   revad(E1,Env,M1,F1,DF),
%   F is sin(F1).
% revad(cos(E1),Env,M,F,DF) :-
%   freeze(M,freeze(F1,M1 is M * -sin(F1))),
%   revad(E1,Env,M1,F1,DF),
%   F is cos(F1).
% revad(exp(E1),Env,M,F,DF) :-
%   freeze(M,freeze(F1,M1 is M * exp(F1))),
%   revad(E1,Env,M1,F1,DF),
%   F is exp(F1).
% 
% test_revad :-
%   X = 1,
%   Y = 2,
%   Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(Y)),
%   pretty(Expr),nl,
%   Env = env(5,3),
%   revad(Expr,Env,F1,DF1),
%   ad_spec(Expr,X,Env,F2,DF2),
%   ad_spec(Expr,Y,Env,F2,DF3),
%   write(F1),write(' = '),write(F2),writeln(' ?'),
%   write(DF1),write(' = '),write(grad(DF2,DF3)),writeln(' ?').

%===============================================================================
% Auxiliary Matrix Operations
%===============================================================================

matrix_transpose(Ls, Ts) :-
  lists_transpose(Ls, Ts).

lists_transpose([], []).
lists_transpose([L|Ls], Ts) :-
  foldl(transpose_, L, Ts, [L|Ls], _).

transpose_(_, Fs, Lists0, Lists) :-
  maplist(list_first_rest, Lists0, Fs, Lists).

list_first_rest([L|Ls], L, Ls).

matrix_hadamard([],[],[]).
matrix_hadamard([R1|R1s],[R2|R2s],[R|Rs]) :-
  maplist(times,R1,R2,R),
  matrix_hadamard(R1s,R2s,Rs).
  
%===============================================================================
% Fabrizio's Example
%===============================================================================

logistic_expr(reciprocal(add(lit(1),exp(negate(var(1)))))).
soft_max_vec_expr([V],[W]) :-
  foldl(sum_exp_expr,V,lit(0),Det),
  maplist(soft_max_expr(Det),V,W).

sum_exp_expr(X,S0,add(S0,exp(X))).

soft_max_expr(Det,X,mul(exp(X),reciprocal(Det))).

l2_loss_expr(U,[V],[[L]]) :-
  maplist(l2_expr,U,V,W),
  foldl(mkadd,W,lit(0),L).
 
l1_expr(Y,Yhat,abs(add(lit(Y),mul(lit(-1),Yhat)))).
l2_expr(Y,Yhat,pow(add(lit(Y),mul(lit(-1),Yhat)),2)).
 
% weights for the 3 layers: neurons 3-4-4-3
w_1([[2,-1,1,4],[-1,2,-3,1],[3,-2,-1,5]]). 
w_2([[3,1,-2,1],[-2,4,1,-4],[-1,-3,2,-5],[3,1,1,1]]).
w_3([[-1,3,-2],[1,-1,-3],[3,-2,2],[1,2,1]]).

test_example :-
  X = var(1),
  w_1(W1), w_2(W2), w_3(W3),
  logistic_expr(Logistic),
  E = vec2vec(soft_max_vec_expr,mul(map(Logistic,mul(map(Logistic,mul(X,lit(W1))),lit(W2))),lit(W3))),
  x_in(1, V),
  Env = env(V),
  matrix_eval(E,Env,R),
  writeln(R).

x_in(1, [[0.5,0.8,0.2]]).

% Original code

logistic(X,Sigma_X):- Sigma_X is 1/(1+exp(-X)).

soft_max_vec(X,SM):-
    foldl(sum_exp,X,0,Det),
    maplist(soft_max(Det),X,SM).

soft_max(Det,X,SM):-
    SM is exp(X)/Det.
    
sum_exp(X,S0,S):-
    S is S0+exp(X).


% training set: input matrix, 3 inputs, 7 examples
x_mat_in([[0.5,0.8,0.2],[0.1,0.9,0.6],[0.2,0.2,0.3],
          [0.6,0.1,0.9],[0.5,0.5,0.4],[0.9,0.1,0.9],[0.1,0.8,0.7]]).

% neural network output
nn_out(O):-
    x_mat_in(X_mat_in),
    w_1(W_1),
    w_2(W_2),
    w_3(W_3),
    matrix_multiply(X_mat_in,W_1,Z_1),
    maplist(maplist(logistic),Z_1,A_1),
    writeln(Z_1),
    writeln(A_1),
    matrix_multiply(A_1,W_2,Z_2),
    maplist(maplist(logistic),Z_2,A_2),
    writeln(Z_2),
    writeln(A_2),
    matrix_multiply(A_2,W_3,Z_3),
    writeln(Z_3),
    maplist(soft_max_vec,Z_3,O).
    
