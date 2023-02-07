:- module(code, [expr/1, eval/3, lookup/3, myplus/3, times/3, revad1/4, revad/4]).
:- use_module(assoc).
:- use_module(spll).

%===============================================================================
% Grammar
%===============================================================================

expr(lit(N)) :- number(N).
expr(var(_)).
expr(add(E1,E2)) :-
  expr(E1),
  expr(E2).
expr(mul(E1,E2)) :-
  expr(E1),
  expr(E2).
expr(negate(E)) :-
  expr(E).
expr(reciprocal(E)) :-
  expr(E).
expr(exp(E)) :-
  expr(E).
expr(log(E)) :-
  expr(E).
expr(pow(E,N)) :-
  number(N),
  expr(E).
expr(abs(E)) :-
  expr(E).
expr(subtract(E1,E2)) :-
  expr(E1),
  expr(E2).
expr(divide(E1,E2)) :-
  expr(E1),
  expr(E2).
expr(plus_infinity).
expr(minus_infinity).
expr(phiU(E)) :-
  expr(E).
expr(phiN(E)) :-
  expr(E).
expr(integral(_X,L,H,_B)) :-
  expr(L),
  expr(H).

%===============================================================================
% Evaluation
%===============================================================================

eval(lit(N),_Env,N).
eval(plus_infinity,_Env,N) :- N is inf.
eval(minus_infinity,_Env,N) :- N is -inf.
eval(var(X),Env,N) :-
  lookup(X,Env,N).
eval(add(E1,E2),Env,N) :-
  eval(E1,Env,N1),
  eval(E2,Env,N2),
  N is N1 + N2.
eval(mul(E1,E2),Env,N) :-
  eval(E1,Env,N1),
  eval(E2,Env,N2),
  N is N1 * N2.
eval(negate(E),Env,N) :-
  eval(E,Env,N1),
  N is -N1.
eval(reciprocal(E),Env,N) :-
  eval(E,Env,N1),
  N is 1 / N1.
eval(exp(E),Env,N) :-
  eval(E,Env,N1),
  N is exp(N1).
eval(pow(E,K),Env,N) :-
  eval(E,Env,N1),
  eval(K,Env,K1),
  N is N1**K1.
eval(abs(E),Env,N) :-
  eval(E,Env,N1),
  N is abs(N1).
eval(subtract(E1,E2),Env,N) :-
  eval(E1,Env,N1),
  eval(E2,Env,N2),
  N is N1 - N2.
eval(log(E),Env,N) :-
  eval(E,Env,N1),
  N is log(N1).
eval(integral(X,EL,EH,phiU(X)),Env,N) :-
  eval(EL,Env,NL),
  eval(EH,Env,NH),
  uniform_cpd(NL,NH,N).
eval(integral(X,EL,EH,phiN(X)),Env,N) :-
  eval(EL,Env,NL),
  eval(EH,Env,NH),
  normal_cpd(NL,NH,N).

lookup(X,Env,N) :- arg(X,Env,N).


test_eval :-
  Expr = mul(add(mul(lit(2),var(1)),lit(1)),var(1)),
  Env = env(5),
  eval(Expr,Env,R),
  write(R),writeln(' = 55 ?').

uniform_cpd(FL,FH,F) :-
  ( FH < 0 ->
     F = 0
  ; FL > 1 ->
     F = 0
  ;
     F is min(FH,1) - max(FL,0)
  ).

normal_cpd(L,H,F) :-
  normal_Phi(L,FL),
  normal_Phi(H,FH),
  F is FH - FL.
normal_Phi(X,F) :-
  ( X =:= 1.0Inf ->
      F = 1
  ; X =:= -1.0Inf ->
      F = 0
  ;
     F is 	(1 + erf(X / sqrt(2))) / 2
  ).

normal_pdf(X,F) :-
  ( X =:= 1.0Inf ->
      F = 0
  ; X =:= -1.0Inf ->
      F = 0
  ;
      F is exp(-(X**2)/2) / sqrt(2 * pi)
  ).

%===============================================================================
% Symbolic Differentiation
%===============================================================================

symbad(lit(_N),_X,lit(0)).
symbad(plus_infinity,_X,lit(0)).
symbad(minus_infinity,_X,lit(0)).
symbad(var(Y),X,lit(DF)) :-
  ( X == Y -> DF = 1 ; DF = 0).
symbad(add(E1,E2),X,add(DF1,DF2)) :-
  symbad(E1,X,DF1),
  symbad(E2,X,DF2).
symbad(mul(E1,E2),X,DF) :-
  symbad(E1,X,DF1),
  symbad(E2,X,DF2),
  DF = add(mul(E2,DF1),mul(E1,DF2)).
symbad(subtract(E1,E2),X,subtract(DF1,DF2)) :-
  symbad(E1,X,DF1),
  symbad(E2,X,DF2).
symbad(negate(E),X,negate(DF)) :-
  symbad(E,X,DF).
symbad(log(E),X,mul(reciprocal(E),DF)) :-
  symbad(E,X,DF).
symbad(exp(E),X,mul(exp(E),DF)) :-
  symbad(E,X,DF).
symbad(reciprocal(E),X,negate(divide(DF,pow(E,lit(2))))) :-
  symbad(E,X,DF).

test_symbad :-
  X = 1,
  Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(X)),
  symbad(Expr,X,R),
  pretty(R),writeln(' = B * (B * 0 + 2 * 1 + 0) + (2 * B + 1) * 1 ?').

%===============================================================================
% Symbolic Differentiation with Expression Reconstruction
%===============================================================================

symbad(lit(N),_X,lit(N),lit(0)).
symbad(plus_infinity,_X,plus_infinity,lit(0)).
symbad(minus_infinity,_X,minus_infinity,lit(0)).
symbad(var(Y),X,var(Y),lit(DF)) :-
  ( X == Y -> DF = 1 ; DF = 0).
symbad(add(E1,E2),X,add(F1,F2),add(DF1,DF2)) :-
  symbad(E1,X,F1,DF1),
  symbad(E2,X,F2,DF2).
symbad(mul(E1,E2),X,mul(F1,F2),DF) :-
  symbad(E1,X,F1,DF1),
  symbad(E2,X,F2,DF2),
  DF = add(mul(F2,DF1),mul(F1,DF2)).
symbad(subtract(E1,E2),X,subtract(F1,F2),subtract(DF1,DF2)) :-
  symbad(E1,X,F1,DF1),
  symbad(E2,X,F2,DF2).
symbad(negate(E),X,negate(F),negate(DF)) :-
  symbad(E,X,F,DF).
symbad(log(E),X,log(F),mul(reciprocal(F),DF)) :-
  symbad(E,X,F,DF).
symbad(exp(E),X,exp(F),mul(exp(E),DF)) :-
  symbad(E,X,F,DF).
symbad(reciprocal(E),X,reciprocal(F),negate(divide(DF,pow(F,lit(2))))) :-
  symbad(E,X,F,DF).

test_symbad2 :-
  X = 1,
  Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(X)),
  symbad(Expr,X,Expr2,R),
  pretty(R),writeln(' = B * (B * 0 + 2 * 1 + 0) + (2 * B + 1) * 1 ?'),
  pretty(Expr2),write(' = '), pretty(Expr), writeln(' ? ').

%===============================================================================
% Forward-Mode Automatic Differentiation Specification
%===============================================================================

ad_spec(E,X,Env,N,DN) :-
  symbad(E,X,F,DF),
  eval(F,Env,N),
  eval(DF,Env,DN).

%===============================================================================
% Forward-Mode Automatic Differentiation
%===============================================================================

fwdad(lit(N),_X,_Env,F,DF) :-
  F  = N,
  DF = 0.
fwdad(plus_infinity,_X,_Env,F,DF) :-
  F is inf,
  DF = 0.
fwdad(minus_infinity,_X,_Env,F,DF) :-
  F is -inf,
  DF = 0.
fwdad(var(Y),X,Env,F,DF) :-
  lookup(Y,Env,F),
  ( X == Y -> DF = 1 ; DF = 0).
fwdad(add(E1,E2),X,Env,F,DF) :-
  fwdad(E1,X,Env,F1,DF1),
  fwdad(E2,X,Env,F2,DF2),
  F is F1 + F2,
  DF is DF1 + DF2.
fwdad(mul(E1,E2),X,Env,F,DF) :-
  fwdad(E1,X,Env,F1,DF1),
  fwdad(E2,X,Env,F2,DF2),
  F is F1 * F2,
  DF is F2 * DF1 + F1 * DF2.
fwdad(subtract(E1,E2),X,Env,F,DF) :-
  fwdad(E1,X,Env,F1,DF1),
  fwdad(E2,X,Env,F2,DF2),
  F is F1 - F2,
  DF is DF1 - DF2.
fwdad(negate(E),X,Env,F,DF) :-
  fwdad(E,X,Env,F1,DF1),
  F is -F1,
  DF is -DF1.
fwdad(log(E),X,Env,F,DF) :-
  fwdad(E,X,Env,F1,DF1),
  F is log(F1),
  DF is DF1 / F1.
fwdad(exp(E),X,Env,F,DF) :-
  fwdad(E,X,Env,F1,DF1),
  F is exp(F1),
  DF is exp(F1) * DF1.
fwdad(reciprocal(E),X,F,DF) :-
  fwdad(E,X,F1,DF1),
  F is 1 / F1,
  DF is -(DF1 / (F1**2)).

test_fwdad :-
  X = 1,
  Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(X)),
  Env = env(5),
  fwdad(Expr,X,Env,F1,DF1),
  ad_spec(Expr,X,Env,F2,DF2),
  pretty(Expr),nl,
  write(F1),write(' = '),write(F2),writeln(' ?'),
  write(DF1),write(' = '),write(DF2),writeln(' ?').

%===============================================================================
% Forward-Mode Automatic Differentiation for Gradients
%===============================================================================

fwdadgrad(lit(N),_Env,F,DF) :-
  F = N,
  empty_assoc(DF).
fwdadgrad(plus_infinity,_Env,F,DF) :-
  F is inf,
  empty_assoc(DF).
fwdadgrad(minus_infinity,_Env,F,DF) :-
  F is -inf,
  empty_assoc(DF).
fwdadgrad(var(Y),Env,F,DF) :-
  lookup(Y,Env,F),
  singleton_assoc(Y,1,DF).
fwdadgrad(add(E1,E2),Env,F,DF) :-
  fwdadgrad(E1,Env,F1,DF1),
  fwdadgrad(E2,Env,F2,DF2),
  F is F1 + F2,
  union_with_assoc(myplus,DF1,DF2,DF).
fwdadgrad(mul(E1,E2),Env,F,SDF) :-
  fwdadgrad(E1,Env,F1,DF1),
  fwdadgrad(E2,Env,F2,DF2),
  F is F1 * F2,
  map_assoc(times(F2),DF1,SDF1),
  map_assoc(times(F1),DF2,SDF2),
  union_with_assoc(myplus,SDF1,SDF2,SDF).
fwdadgrad(integral(X,L,H,phiU(X)),Env,F,DF) :-
  fwdadgrad(L,Env,FL,DFL),
  fwdadgrad(H,Env,FH,DFH),
  ( 0 =< FL, FL =< 1 ->
      DF1 = DFL
  ;   empty_assoc(DF1)
  ),
  ( 0 =< FH, FH =< 1 ->
      DF2 = DFH
  ;   empty_assoc(DF2)
  ),
  map_assoc(times(-1),DF1,DF11),
  union_with_assoc(myplus,DF2,DF11,DF),
  uniform_cpd(FL,FH,F).
fwdadgrad(integral(X,L,H,phiN(X)),Env,F,DF) :-
  fwdadgrad(L,Env,FL,DFL),
  fwdadgrad(H,Env,FH,DFH),
  normal_pdf(FL,Factor1),
  normal_pdf(FH,Factor2),
  map_assoc(times(-Factor1),DFL,DF1),
  map_assoc(times(Factor2),DFH,DF2),
  union_with_assoc(myplus,DF2,DF1,DF),
  normal_cpd(FL,FH,F).
fwdadgrad(plus_infinity,_Env,F,DF) :-
  F is inf,
  DF = 0.
fwdadgrad(minus_infinity,_Env,F,DF) :-
  F is -inf,
  DF = 0.
fwdadgrad(negate(E),Env,F,DF) :-
  fwdadgrad(E,Env,F1,DF1),
  F is -F1,
  Factor is -1,
  map_assoc(times(Factor),DF1,DF).
fwdadgrad(log(E),Env,F,DF) :-
  fwdadgrad(E,Env,F1,DF1),
  F is log(F1),
  Factor is 1 / F1,
  map_assoc(times(Factor),DF1,DF).
fwdadgrad(exp(E),Env,F,DF) :-
  fwdadgrad(E,Env,F1,DF1),
  F is exp(F1),
  map_assoc(times(F),DF1,DF).
fwdadgrad(subtract(E1,E2),Env,F,DF) :-
  fwdadgrad(E1,Env,F1,DF1),
  fwdadgrad(E2,Env,F2,DF2),
  F is F1 - F2,
  map_assoc(times(-1),DF2,DF21),
  union_with_assoc(myplus,DF1,DF21,DF).
fwdadgrad(negate(E),Env,F,DF) :-
  fwdadgrad(E,Env,F1,DF1),
  F is -F1,
  map_assoc(times(-1),DF1,DF).
fwdadgrad(reciprocal(E),Env,F,DF) :-
  fwdadgrad(E,Env,F1,DF1),
  F is 1 / F1,
  Factor is -(1 / (F1**2)),
  map_assoc(times(Factor),DF1,DF).



/*
myplus(A,B,C) :- C is A + B.
times(A,B,C) :- C is A * B.
*/

test_fwdadgrad :-
  X = 1,
  Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(X)),
  Env = env(5),
  fwdadgrad(Expr,Env,F1,DF1),
  assoc_to_list(DF1,L1),
  ad_spec(Expr,X,Env,F2,DF2),
  pretty(Expr),nl,
  write(F1),write(' = '),write(F2),writeln(' ?'),
  write(L1),write(' = '),write([X-DF2]),writeln(' ?').

test_fwdadgrad2 :-
  X = 1,
  Y = 2,
  Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(Y)),
  Env = env(5,3),
  fwdadgrad(Expr,Env,F1,DF1),
  assoc_to_list(DF1,L1),
  ad_spec(Expr,X,Env,F2,DF2),
  ad_spec(Expr,Y,Env,F2,DF3),
  pretty(Expr),nl,
  write(F1),write(' = '),write(F2),writeln(' ?'),
  write(L1),write(' = '),write([X-DF2,Y-DF3]),writeln(' ?').

%===============================================================================
% Scalar Multipliers
%===============================================================================

revad1(E,Env,F,DF) :-
  revad1(E,Env,1,F,DF).

revad1(lit(N),_Env,_M,F,DF) :-
  F = N,
  empty_assoc(DF).
revad1(plus_infinity,_Env,_M,F,DF) :-
  F is inf,
  empty_assoc(DF).
revad1(minus_infinity,_Env,_M,F,DF) :-
  F is -inf,
  empty_assoc(DF).
revad1(var(Y),Env,M,F,DF) :-
  lookup(Y,Env,F),
  singleton_assoc(Y,M,DF).
revad1(add(E1,E2),Env,M,F,DF) :-
  revad1(E1,Env,M,F1,DF1),
  revad1(E2,Env,M,F2,DF2),
  F is F1 + F2,
  union_with_assoc(myplus,DF1,DF2,DF).
revad1(mul(E1,E2),Env,M,F,DF) :-
  times(M,F2,M1),
  times(M,F1,M2),
  revad1(E1,Env,M1,F1,DF1),
  revad1(E2,Env,M2,F2,DF2),
  F is F1 * F2,
  union_with_assoc(myplus,DF1,DF2,DF).
revad1(subtract(E1,E2),Env,M,F,DF) :-
  revad1(E1,Env,M,F1,DF1),
  freeze(M,M1 is -M),
  revad1(E2,Env,M1,F2,DF2),
  F is F1 - F2,
  union_with_assoc(myplus,DF1,DF2,DF).
revad1(negate(E),Env,M,F,DF) :-
  freeze(M,M1 is -M),
  revad1(E,Env,M1,F1,DF),
  F is -F1.
revad1(log(E),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is M/F1)),
  revad1(E,Env,M1,F1,DF),
  F is log(F1).
revad1(integral(X,L,H,phiU(X)),Env,M,F,DF) :-
  freeze(M,M1 is -M),
  revad1(L,Env,M1,FL,DFL),
  revad1(H,Env,M,FH,DFH),
  ( 0 =< FL, FL =< 1 ->
      DF1 = DFL
  ;   empty_assoc(DF1)
  ),
  ( 0 =< FH, FH =< 1 ->
      DF2 = DFH
  ;   empty_assoc(DF2)
  ),
  union_with_assoc(myplus,DF2,DF1,DF),
  uniform_cpd(FL,FH,F).
revad1(integral(X,L,H,phiU(X)),Env,M,F,DF) :-
  freeze(M,(freeze(FL,(normal_pdf(FL,PDL),M1 is -M * PDL)))),
  freeze(M,(freeze(FH,(normal_pdf(FH,PDH),M2 is M * PDH)))),
  revad1(L,Env,M1,FL,DFL),
  revad1(H,Env,M2,FH,DFH),
  union_with_assoc(myplus,DFH,DFL,DF),
  normal_cpd(FL,FH,F).
revad1(exp(E),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is M * exp(F1))),
  revad1(E,Env,M1,F1,DF),
  F is exp(F1).
revad1(reciprocal(E),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is  -(M / (F1**2)))),
  revad1(E,Env,M1,F1,DF),
  F is 1 / F1.

myplus(A,B,C) :- freeze(A,freeze(B,C is A + B)).
times(A,B,C) :- freeze(A,freeze(B,C is A * B)).

test_revad1 :-
  X = 1,
  Y = 2,
  Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(Y)),
  pretty(Expr),nl,
  Env = env(5,3),
  revad1(Expr,Env,F1,DF1),
  assoc_to_list(DF1,L1),
  ad_spec(Expr,X,Env,F2,DF2),
  ad_spec(Expr,Y,Env,F2,DF3),
  write(F1),write(' = '),write(F2),writeln(' ?'),
  write(L1),write(' = '),write([X-DF2,Y-DF3]),writeln(' ?').

%===============================================================================
% Gradient Threading
%===============================================================================

revad2(E,Env,F,DF) :-
  empty_assoc(DF0),
  revad2(E,Env,1,F,DF0,DF).

revad2(lit(N),_Env,_M,F) -->
  { F = N }.
revad2(plus_infinity,_Env,_M,F) -->
  { F is inf }.
revad2(minus_infinity,_Env,_M,F) -->
  { F is -inf }.
revad2(var(Y),Env,M,F) -->
  { lookup(Y,Env,F) },
  insert_with_assoc(myplus,Y,M).
revad2(add(E1,E2),Env,M,F) -->
  revad2(E1,Env,M,F1),
  revad2(E2,Env,M,F2),
  { F is F1 + F2 }.
revad2(mul(E1,E2),Env,M,F) -->
  { times(M,F2,M1) },
  { times(M,F1,M2) },
  revad2(E1,Env,M1,F1),
  revad2(E2,Env,M2,F2),
  { F is F1 * F2 }.
revad2(subtract(E1,E2),Env,M,F) -->
  revad2(E1,Env,M,F1),
  { freeze(M, M1 is -M) },
  revad2(E2,Env,M1,F2),
  { F is F1 - F2 }.
revad2(negate(E),Env,M,F) -->
  { freeze(M, M1 is -M) },
  revad2(E,Env,M1,F1),
  { F is -F1 }.
revad2(log(E),Env,M,F) -->
  { freeze(M, freeze(F1, M1 is M/F1)) },
  revad2(E,Env,M1,F1),
  { F is log(F1) }.
revad2(integral(X,L,H,phiU(X)),Env,M,F) -->
  { freeze(M,freeze(FL,(when_in_unit(FL,M,M1a),M1 is -M1a))) },
  revad2(L,Env,M1,FL),
  { freeze(FH,when_in_unit(FH,M,M2)) },
  revad2(H,Env,M2,FH),
  { uniform_cpd(FL,FH,F) }.
revad2(integral(X,L,H,phiN(X)),Env,M,F) -->
  { freeze(M,(freeze(FL,(normal_pdf(FL,PDL),M1 is -M * PDL)))) },
  { freeze(M,(freeze(FH,(normal_pdf(FH,PDH),M2 is M * PDH)))) },
  revad2(L,Env,M1,FL),
  revad2(H,Env,M2,FH),
  { normal_cpd(FL,FH,F) }.
revad2(exp(E),Env,M,F) -->
  { freeze(M, freeze(F1, M1 is M * exp(F1))) },
  revad2(E,Env,M1,F1),
  { F is exp(F1) }.
revad2(reciprocal(E),Env,F) -->
  { freeze(M,freeze(F1,M1 is  -(M / (F1**2)))) },
  revad2(E,Env,M1,F1),
  { F is 1 / F1 }.

when_in_unit(F,X,Y) :-
  ( 0 =< F, F =< 1 ->
      Y = X
  ;
      Y = 0
  ).

test_revad2 :-
  X = 1,
  Y = 2,
  Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(Y)),
  pretty(Expr),nl,
  Env = env(5,3),
  revad2(Expr,Env,F1,DF1),
  assoc_to_list(DF1,L1),
  ad_spec(Expr,X,Env,F2,DF2),
  ad_spec(Expr,Y,Env,F2,DF3),
  write(F1),write(' = '),write(F2),writeln(' ?'),
  write(L1),write(' = '),write([X-DF2,Y-DF3]),writeln(' ?').

insert_with_assoc(Pred,K,V,A0,A1) :-
  put_with_assoc(Pred,K,A0,V,A1).

%===============================================================================
% Reverse-Mode AD, Destructively
%===============================================================================

empty_array(N,Arr) :-
  findall(cell(0),between(1,N,_),List),
  Arr =.. [grad|List].

insert_with_array(Pred,Var,Value,Arr) :-
  arg(Var,Arr,cell(OldValue)),
  call(Pred,OldValue,Value,NewValue),
  setarg(Var,Arr,cell(NewValue)).

revad(E,Env,F,DF) :-
  functor(Env,_,N),
  empty_array(N,DF),
  revad(E,Env,1,F,DF).

revad(lit(N),_Env,_M,F,_DF) :-
  F = N.
revad(plus_infinity,_Env,_M,F,_DF) :-
  F is inf.
revad(minus_infinity,_Env,_M,F,_DF) :-
  F is -inf.
revad(var(Y),Env,M,F,DF) :-
  lookup(Y,Env,F),
  insert_with_array(myplus,Y,M,DF).
revad(add(E1,E2),Env,M,F,DF) :-
  revad(E1,Env,M,F1,DF),
  revad(E2,Env,M,F2,DF),
  F is F1 + F2.
revad(mul(E1,E2),Env,M,F,DF) :-
  times(M,F2,M1),
  times(M,F1,M2),
  revad(E1,Env,M1,F1,DF),
  revad(E2,Env,M2,F2,DF),
  F is F1 * F2.
revad(negate(E1),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is -M)),
  revad(E1,Env,M1,F1,DF),
  F is -F1.
revad(sin(E1),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is M * cos(F1))),
  revad(E1,Env,M1,F1,DF),
  F is sin(F1).
revad(cos(E1),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is M * -sin(F1))),
  revad(E1,Env,M1,F1,DF),
  F is cos(F1).
revad(exp(E1),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is M * exp(F1))),
  revad(E1,Env,M1,F1,DF),
  F is exp(F1).
revad(abs(E1),Env,M,F,DF) :-
  freeze(M,freeze(F1,derabs(M,F1,M1))),
  revad(E1,Env,M1,F1,DF),
  F is abs(F1).
revad(subtract(E1,E2),Env,M,F,DF) :-
  revad(E1,Env,M,F1,DF),
  freeze(M, M1 is -M),
  revad(E2,Env,M1,F2,DF),
  F is F1 - F2.
revad(log(E1),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is M / F1)),
  revad(E1,Env,M1,F1,DF),
  F is log(F1).
revad(integral(X,L,H,phiU(X)),Env,M,F,DF) :-
  freeze(FL,freeze(M,(M1a is -M, when_in_unit(FL,M1a,M1)))),
  revad(L,Env,M1,FL,DF),
  freeze(FH,when_in_unit(FH,M,M2)),
  revad(H,Env,M2,FH,DF),
  uniform_cpd(FL,FH,F).
revad(integral(X,L,H,phiN(X)),Env,M,F,DF) :-
  freeze(M,(freeze(FL,(normal_pdf(FL,PDL),M1 is -M * PDL)))),
  freeze(M,(freeze(FH,(normal_pdf(FH,PDH),M2 is M * PDH)))),
  revad(L,Env,M1,FL,DF),
  revad(H,Env,M2,FH,DF),
  normal_cpd(FL,FH,F).
revad(reciprocal(E),Env,M,F,DF) :-
  freeze(M,freeze(F1,M1 is  -(M / (F1**2)))),
  revad(E,Env,M1,F1,DF),
  F is 1 / F1.
revad(pow(E1,E2),Env,M,F,DF) :-
  freeze(M,freeze(F1,freeze(F2,
      M1 is M * F2 * F1**(F2 - 1)))),
  freeze(M,freeze(F1,freeze(F2,
      M2 is M * (F1**F2) * log(F1)))),
  revad(E1,Env,M1,F1,DF),
  revad(E2,Env,M2,F2,DF),
  F is F1**F2.

derabs(M,F1,M1) :-
  ( F1 > 0   -> M1 = M
  ; F1 =:= 0 -> M1 = 0
  ; F1 < 0   -> M1 is -M
  ).

test_revad :-
  X = 1,
  Y = 2,
  Expr = mul(add(mul(lit(2),var(X)),lit(1)),var(Y)),
  pretty(Expr),nl,
  Env = env(5,3),
  revad(Expr,Env,F1,DF1),
  ad_spec(Expr,X,Env,F2,DF2),
  ad_spec(Expr,Y,Env,F2,DF3),
  write(F1),write(' = '),write(F2),writeln(' ?'),
  write(DF1),write(' = '),write(grad(DF2,DF3)),writeln(' ?').

%===============================================================================
% Pretty
%===============================================================================
pretty(Expr) :-
  pretty_go(Expr,0).

pretty_go(lit(N),_) :- write(N).
pretty_go(var(X),_) :- write('$VAR'(X)).
pretty_go(add(E1,E2),P) :- open_parens(P), pretty_go(E1,0),write(' + '), pretty_go(E2,0), close_parens(P).
pretty_go(mul(E1,E2),_) :- pretty_go(E1,1),write(' * '), pretty_go(E2,1).
pretty_go(subtract(E1,E2),P) :- open_parens(P), pretty_go(E1,0),write(' - '), pretty_go(E2,0), close_parens(P).
pretty_go(negate(E),P) :- write(' - '), open_parens(P), pretty_go(E,0),close_parens(P).

open_parens(0).
open_parens(1) :- write('(').

close_parens(0).
close_parens(1) :- write(')').


%===============================================================================
% Learning
%===============================================================================

/*
Environment: env(0.5)
Environment: env(0.33999999999999997)
Environment: env(0.30434937611408197)
Environment: env(0.3002407808050711)
Environment: env(0.30001157081194685)
Environment: env(0.3000005512339056)
Environment: env(0.3000000262497848)
Environment: env(0.300000001249991)
Environment: env(0.3000000000595233)
Environment: env(0.30000000000283444)
Environment: env(0.300000000000135)
Environment: env(0.3000000000000064)
Environment: env(0.3000000000000003)
Environment: env(0.3000000000000001)
*/

problem(1,Etrue,Ftrue,Efalse,Ffalse,Lambda) :-
  Etrue  = integral(_A, var(1), plus_infinity, phiU(_A)), % integral(_6720,var(1),plus_infinity,phiU(_6720)),
  Ftrue  = 7,
  Efalse = subtract(lit(1), integral(_A, var(1), plus_infinity, phiU(_A))), % subtract(lit(1), integral(_6706, var(1), plus_infinity, phiU(_6706))),
  Ffalse  = 3,
  Lambda = 0.02.
problem(2,Etrue,Ftrue,Efalse,Ffalse,Lambda) :-
  Etrue  = reciprocal(add(lit(1), exp(negate(subtract(lit(0.5), var(1)))))),
  Ftrue  = 1,
  Efalse = subtract(lit(1), reciprocal(add(lit(1), exp(negate(subtract(lit(0.5), var(1))))))),
  Ffalse  = 0,
  Lambda = 0.02.
problem(3,Etrue,Ftrue,Efalse,Ffalse,Lambda) :-
  Etrue  = integral(_6720,var(1),plus_infinity,phiN(_6720)),
  Ftrue  = 5,
  Efalse = subtract(lit(1), integral(_6706, var(1), plus_infinity, phiN(_6706))),
  Ffalse  = 5,
  Lambda = 0.02.

test_learn(Problem,N) :-
  problem(Problem,Etrue,Ftrue,Efalse,Ffalse,Lambda),
  Env0 = env(0.5), % initial guess
  L = add(mul(lit(Ffalse),negate(log(Efalse))),mul(lit(Ftrue),negate(log(Etrue)))),
  learning_loop(N,L,Env0,Lambda,_NEnv).

problem_multi(Enull,Fnull,Etrue,Ftrue,Efalse,Ffalse,Lambda) :-
  % []
  Enull   = add(mul(integral(_A1, var(1), plus_infinity, phiU(_A1)), add(mul(integral(_B1, var(2), plus_infinity, phiU(_B1)), lit(1)), mul(subtract(lit(1), integral(_C1, var(2), plus_infinity, phiU(_C1))), lit(0)))), mul(subtract(lit(1), integral(_D1, var(1), plus_infinity, phiU(_D1))), lit(0))),
  Fnull   = 3,
  % [true]
  Etrue   = add(mul(integral(_A2, var(1), plus_infinity, phiU(_A2)), add(mul(integral(_B2, var(2), plus_infinity, phiU(_B2)), lit(0)), mul(subtract(lit(1), integral(_C2, var(2), plus_infinity, phiU(_C2))), mul(lit(1), lit(1))))), mul(subtract(lit(1), integral(_D2, var(1), plus_infinity, phiU(_D2))), mul(lit(0), lit(1)))),
  Ftrue   = 3,
  % [false]
  Efalse  = add(mul(integral(_A3, var(1), plus_infinity, phiU(_A3)), add(mul(integral(_B3, var(2), plus_infinity, phiU(_B3)), lit(0)), mul(subtract(lit(1), integral(_C3, var(2), plus_infinity, phiU(_C3))), mul(lit(0), lit(1))))), mul(subtract(lit(1), integral(_D3, var(1), plus_infinity, phiU(_D3))), mul(lit(1), lit(1)))),
  Ffalse  = 3,
  Lambda  = 0.02.

test_learn_multi(N) :-
  problem_multi(Enull,Fnull,Etrue,Ftrue,Efalse,Ffalse,Lambda),
  Env0 = env(0.5,0.5), % initial guess
  L = add(add(mul(lit(Fnull),negate(log(Enull))),mul(lit(Ftrue),negate(log(Etrue)))),mul(lit(Ffalse),negate(log(Efalse)))),
  learning_loop(N,L,Env0,Lambda,NEnv),
  NEnv =.. [_|Vals],
  time(Vals).

/*
N = 10
revad:     2,857 inferences, 0.001 CPU in 0.001 seconds (84% CPU, 3940690 Lips)
revad2:    2,857 inferences, 0.003 CPU in 0.003 seconds (90% CPU, 1075273 Lips)
revad1:    2,857 inferences, 0.006 CPU in 0.006 seconds (96% CPU, 462223 Lips)
fwdadgrad: 2,857 inferences, 0.001 CPU in 0.001 seconds (81% CPU, 3607323 Lips)

N = 100
revad:  2,857 inferences, 0.002 CPU in 0.002 seconds (96% CPU, 1242714 Lips)
revad2: 2,857 inferences, 0.013 CPU in 0.014 seconds (93% CPU, 216292 Lips)
revad1: 2,857 inferences, 0.026 CPU in 0.027 seconds (97% CPU, 109564 Lips)
fwdadgrad: 2,857 inferences, 0.001 CPU in 0.001 seconds (81% CPU, 3607323 Lips)

25 loops, N = 100
revad:     25,671,403 inferences, 1.233 CPU in 1.252 seconds (99% CPU, 20815956 Lips)
revad2:    25,163,903 inferences, 1.416 CPU in 1.459 seconds (97% CPU, 17764920 Lips)
revad1:    29,813,902 inferences, 2.070 CPU in 2.338 seconds (89% CPU, 14399429 Lips)
fwdadgrad: 28,031,377 inferences, 2.056 CPU in 2.484 seconds (83% CPU, 13630710 Lips)

100 loops, N = 100
revad:     102,685,603 inferences, 4.828 CPU in 4.909 seconds (98% CPU, 21267440 Lips)
revad2:    100,655,603 inferences, 5.656 CPU in 5.768 seconds (98% CPU, 17795028 Lips)
revad1:    119,255,602 inferences, 6.839 CPU in 9.098 seconds (75% CPU, 17438079 Lips)
fwdadgrad: 112,125,502 inferences, 7.510 CPU in 9.346 seconds (80% CPU, 14930053 Lips)
*/

benchmark :-
  time(loop(100,Env)).

loop(N,Env) :-
  ( N > 0 ->
     benchmark(100),
     N1 is N - 1,
     loop(N1,Env)
  ;
     Env = true
  ).

benchmark(N) :-
  example(6,Defs,Expr),
  Thetas = thetas(0.5,0.5,0.5,0.5,0.5,0.5),
  prob([],Expr,Thetas,Defs,EN),
  FN    = 3,
  prob([true],Expr,Thetas,Defs,ET),
  FT    = 3,
  prob([false],Expr,Thetas,Defs,EF),
  FF    = 3,
  prob([true,true],Expr,Thetas,Defs,ETT),
  FTT   = 3,
  prob([true,false],Expr,Thetas,Defs,ETF),
  FTF   = 3,
  prob([false,true],Expr,Thetas,Defs,EFT),
  FFT   = 3,
  prob([false,false],Expr,Thetas,Defs,EFF),
  FFF   = 3,
  Lambda  = 0.02,
  Env0 = env(0.5,0.25,0.25,0.25,0.25,0.25), % initial guess
  neg_loglikelihood([(FN,EN),(FT,ET),(FF,EF),(FTT,ETT),(FTF,ETF),(FFT,EFT),(FFF,EFF)],L),
  learning_loop(N,L,Env0,Lambda,NEnv).
  % NEnv =.. [_|Vals],
  % time(Vals).

neg_loglikelihood([],lit(0)).
neg_loglikelihood([(F,E)|NN],add(L,R)) :-
  L = mul(lit(F),negate(log(E))),
  neg_loglikelihood(NN,R).

learning_loop(N,E,Env,Lambda,NEnv) :-
  % write('Environment: '), writeln(Env),
  ( N > 0 ->
     iteration_fwdadgrad(E,Env,Lambda,Env1),
     N1 is N - 1,
     learning_loop(N1,E,Env1,Lambda,NEnv)
  ;
     NEnv = Env
  ).

iteration_fwdadgrad(E,Env,Lambda,NEnv) :-
  fwdadgrad(E,Env,_F,DF),
  assoc_to_values(DF,List),
  Env =.. [N|Vals],
  maplist(adjust(Lambda),List,Vals,NVals),
  NEnv =.. [N|NVals].

iteration_revad1(E,Env,Lambda,NEnv) :-
  revad1(E,Env,_F,DF),
  assoc_to_values(DF,List),
  Env =.. [N|Vals],
  maplist(adjust(Lambda),List,Vals,NVals),
  NEnv =.. [N|NVals].

iteration_revad2(E,Env,Lambda,NEnv) :-
  revad2(E,Env,_F,DF),
  assoc_to_values(DF,List),
  Env =.. [N|Vals],
  maplist(adjust(Lambda),List,Vals,NVals),
  NEnv =.. [N|NVals].

iteration_revad(E,Env,Lambda,NEnv) :-
  revad(E,Env,_F,DF),
  DF =.. [_|Cells],
  maplist(uncell,Cells,List),
  Env =.. [N|Vals],
  maplist(adjust(Lambda),List,Vals,NVals),
  NEnv =.. [N|NVals].

uncell(cell(X),X).

adjust(Lambda,DX,X,NX) :-
  NX is X - Lambda * DX.
