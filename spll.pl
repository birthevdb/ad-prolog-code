:- module(spll, [example/3, prob/5]).
:- use_module(library(random)).

%---------%
% Grammar %
%---------%

spll(if(C,A,B)) :-
  spll(A),
  spll(B),
  spll(C).
spll(uniform).
spll(normal).
spll(constant(_Y)).
spll(theta(_N)).
spll(mul(A,B)) :-
  spll(A),
  spll(B).
spll(add(A,B)) :-
  spll(A),
  spll(B).
spll(null).
spll(cons(A,B)) :-
  spll(A),
  spll(B).
spll(ge(A,B)) :-
  spll(A),
  spll(B).

%---------------%
% Deterministic %
%---------------%

is_det(if(C,A,B)) :-
  is_det(A),
  is_det(B),
  is_det(C).
is_det(constant(_Y)).
is_det(theta(_N)).
is_det(mul(A,B)) :-
  is_det(A),
  is_det(B).
is_det(add(A,B)) :-
  is_det(A),
  is_det(B).
is_det(null).
is_det(cons(A,B)) :-
  is_det(A),
  is_det(B).
is_det(ge(A,B)) :-
  is_det(A),
  is_det(B).

%----------------------%
% Generative Semantics %
%----------------------%

generate(if(C,A,B),Thetas,Defs,R) :-
  generate(C,Thetas,Defs,RC),
  ( RC == true ->
      generate(A,Thetas,Defs,R)
  ;
      generate(B,Thetas,Defs,R)
  ).
generate(uniform,_Thetas,_Defs,R) :-
  random(R).
generate(normal,_Thetas,_Defs,R) :-
  random_normal(R).
generate(constant(Y),_Thetas,_Defs,Y).
generate(theta(N),Thetas,_Defs,R) :-
  arg(N,Thetas,R).
generate(mul(A,B),Thetas,Defs,R) :-
  generate(A,Thetas,Defs,RA),
  generate(B,Thetas,Defs,RB),
  R is RA * RB.
generate(add(A,B),Thetas,Defs,R) :-
  generate(A,Thetas,Defs,RA),
  generate(B,Thetas,Defs,RB),
  R is RA + RB.
generate(null,_Thetas,_Defs,[]).
generate(cons(A,B),Thetas,Defs,[RA|RB]) :-
  generate(A,Thetas,Defs,RA),
  generate(B,Thetas,Defs,RB).
generate(ge(A,B),Thetas,Defs,R) :-
  generate(A,Thetas,Defs,RA),
  generate(B,Thetas,Defs,RB),
  ( RA >= RB -> R = true ; R = false ).
generate(call(F),Thetas,Defs,R) :-
  memberchk(F=A,Defs),
  generate(A,Thetas,Defs,R).

random_normal(N) :-
    % Box-Muller transform
    % https://en.wikipedia.org/wiki/Box%E2%80%93Muller_transform
    random(U1), random(U2),
    N is sqrt(-2 * log(U1)) * cos(2*pi*U2).
    % N is sqrt(-2 * log(U1)) * sin(2*pi*U2).

%-------------------------------%
% Symbolic Generative Semantics %
%-------------------------------%

% TODO: sigmoid
% symbolic_generate(if(C,A,B),Defs,R) :-
%   symbolic_generate(C,Defs,RC),
%   ( RC == true ->
%       symbolic_generate(A,Defs,R)
%   ;
%       symbolic_generate(B,Defs,R)
%   ).
symbolic_generate(constant(Y),_Defs,lit(Y)).
symbolic_generate(theta(N),_Defs,var(N)).
symbolic_generate(mul(A,B),Defs,mul(RA,RB)) :-
  symbolic_generate(A,Defs,RA),
  symbolic_generate(B,Defs,RB).
symbolic_generate(add(A,B),Defs,add(RA,RB)) :-
  symbolic_generate(A,Defs,RA),
  symbolic_generate(B,Defs,RB).
symbolic_generate(null,_Defs,[]).
symbolic_generate(cons(A,B),Defs,[RA|RB]) :-
  symbolic_generate(A,Defs,RA),
  symbolic_generate(B,Defs,RB).
% TODO: sigmoid
% symbolic_generate(ge(A,B),Defs,R) :-
%   symbolic_generate(A,Defs,RA),
%   symbolic_generate(B,Defs,RB),
%   ( RA >= RB -> R = true ; R = false ).
symbolic_generate(call(F),Defs,R) :-
  memberchk(F=A,Defs),
  symbolic_generate(A,Defs,R).

det(A,Defs,R) :-
  is_det(A), % TODO: should also allow calls...
  symbolic_generate(A,Defs,R).


%-------------------------%
% Probabilistic Semantics %
%-------------------------%

prob(X,if(C,A,B),Thetas,Defs,add(mul(PC1,PA),mul(PC2,PB))) :-
  prob(true,C,Thetas,Defs,PC1),
  prob(false,C,Thetas,Defs,PC2),
  prob(X,A,Thetas,Defs,PA),
  prob(X,B,Thetas,Defs,PB).
prob(X,uniform,_Thetas,_Defs,phiU(X)).
prob(X,normal,_Thetas,_Defs,phiN(X)).
prob(X,constant(Y),_Thetas,_Defs,P) :-
  (X = Y -> P = lit(1) ; P = lit(0)).
prob(X,theta(N),Thetas,_Defs,P) :-
  arg(N,Thetas,Y),
  (X = Y -> P = lit(1) ; P = lit(0)).
prob(X,mul(A,B),Thetas,Defs,P) :-
  ( det(A,Defs,Y) ->
      X1 = divide(X,Y),
      P = mul(P1,Y),
      prob(X1,B,Thetas,Defs,P1)
  ;  det(B,Defs,Y) ->
      X1 = divide(X,Y),
      P = mul(P1,Y),
      prob(X1,A,Thetas,Defs,P1)
  ).
prob(X,add(A,B),Thetas,Defs,P) :-
  ( det(A,Defs,Y) ->
      X1 = subtract(X,Y),
      prob(X1,B,Thetas,Defs,P)
  ;  det(B,Defs,Y) ->
      X1 = subtract(X,Y),
      prob(X1,A,Thetas,Defs,P)
  ).
prob(X,null,_Thetas,_Defs,P) :-
  ( X = [] -> P = lit(1) ; P = lit(0) ).
prob(X,cons(A,B),Thetas,Defs,P) :-
  ( X = [] ->
      P = lit(0)
  ;
      X = [Y|Ys],
      P = mul(P1,P2),
      prob(Y,A,Thetas,Defs,P1),
      prob(Ys,B,Thetas,Defs,P2)
  ).
prob(X,call(F),Thetas,Defs,P) :-
  memberchk(F=A,Defs),
  prob(X,A,Thetas,Defs,P).
prob(X,ge(A,B),Thetas,Defs,P) :-
  ( X = true ->
    ( det(A,Defs,EA), det(B,Defs,EB) ->
        sigmoid(subtract(EA,EB),P)
    ; det(A,Defs,C) ->
        prob(Y,B,Thetas,Defs,PB),
        P = integral(Y,minus_infinity,C,PB)
    ; det(B,Defs,C) ->
        prob(Y,A,Thetas,Defs,PA),
        P = integral(Y,C,plus_infinity,PA)
    )
  ; X = false ->
    ( det(A,Defs,EA), det(B,Defs,EB) ->
        sigmoid(subtract(EA,EB),ES),
        P = subtract(lit(1),ES)
    ; det(A,Defs,C) ->
        prob(Y,B,Thetas,Defs,PB),
        P = subtract(lit(1),integral(Y,minus_infinity,C,PB))
    ; det(B,Defs,C) ->
        prob(Y,A,Thetas,Defs,PA),
        P = subtract(lit(1),integral(Y,C,plus_infinity,PA))
    )
  ).

sigmoid(X,S) :-
  S = reciprocal(add(lit(1),exp(negate(X)))).

%----------%
% Examples %
%----------%

/*
   if uniform <= 0.3 then  gaussian(2,1)+ gaussian(0.5,1.5) else gaussian(3,1)+gaussian(0.5,1.5)
   if uniform <= theta1 then  gaussian(theta2,theta3)+ gaussian(theta4,theta5) else gaussian(theta6,theta7)+gaussian(theta4,theta5)
 */

example([main =
  if(ge(theta(1), uniform)
    ,add(G1,G2)
    ,add(G3,G4)
    )], call(main)) :-
  gaussian(theta(2),theta(3),G1),
  gaussian(theta(4),theta(5),G2),
  gaussian(theta(6),theta(7),G3),
  gaussian(theta(8),theta(9),G4).

gaussian(Mu,Sigma,add(mul(normal,Sigma),Mu)).

test(R,P) :-
  example(Defs,A),
  Theta = theta(0.5,0,1,0,1,0,1,0,1),
  generate(A,Theta,Defs,R),
  prob(X,A,Theta,Defs,P).

example(1,
  [main = add(mul(normal,theta(2)),theta(1))],
  call(main)
).
example(2,
  [main = ge(uniform,theta(1))],
  call(main)
).

example(3,
  [main = ge(constant(0.5),theta(1))],
  call(main)
).

example(4,
  [main = ge(normal,theta(1))],
  call(main)
).

example(5,
  [main = if(ge(uniform,theta(1)),
             if(ge(uniform,theta(2)),
                null,
                cons(constant(true),null)),
             cons(constant(false),null))
  ],
  call(main)
).

example(6,
  [main = if(ge(uniform,theta(1)),
             if(ge(uniform,theta(2)),
                if(ge(uniform,theta(3)),
                   null,
                   cons(constant(true),null)),
                if(ge(uniform,theta(4)),
                   cons(constant(false),null),
                   cons(constant(true),cons(constant(true),null)))),
             if(ge(uniform,theta(5)),
                if(ge(uniform,theta(6)),
                   cons(constant(true),cons(constant(false),null)),
                   cons(constant(false),cons(constant(true),null))),
                cons(constant(false),cons(constant(false),null)))
             )
  ],
  call(main)
).
