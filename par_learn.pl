

:-use_module(code).

p(X,
log(
add(
  mul(reciprocal(add(lit(1),exp(negate(var(1))))),
   mul(reciprocal(mul(lit(2.50662827463),add(exp(var(5)),exp(var(7))))),
     exp(mul(lit(-0.5),pow(mul(abs(subtract(lit(X),add(var(2),var(4)))),reciprocal(add(exp(var(5)),exp(var(7))))),lit(2)))))),
  mul(subtract(lit(1),reciprocal(add(lit(1),exp(negate(var(1)))))),
   mul(reciprocal(mul(lit(2.50662827463),add(exp(var(6)),exp(var(7))))),
     exp(mul(lit(-0.5),pow(mul(abs(subtract(lit(X),add(var(3),var(4)))),reciprocal(add(exp(var(6)),exp(var(7))))),lit(2))))))
   ))
).
% expr=x*N(x;mu1+mu3,s1+s3)+(1-x)*N(x;m2+mu3,s2+s3)
  
:-include(data). % best LL -15408.246077

test(E,E1,D):-
  p(X,Expr),
  X=1,
  Env=      var(0.3, 2,  3,  0.5,1, 1, 0.1),
              % pa   mu1 mu2 mu3 s1 s2 s3 
              % 1    2   3   4   5  6  7   
  D=grad(0,0,0,0,0,0,0),
  eval(Expr,Env,E),
  revad(Expr,Env,1,E1,D).


gd(Par,LL):-
  data(D),
  init_gd_par(7,0.5,ParList),
  gd(0.00000001,0.00000001,100,ParList,-1e10,D,ParList1,LL),
  ParList1=[WA,Mu1,Mu2,Mu3,W1,W2,W3],
  logistic(WA,PA),
  S1 is exp(W1)^2,
  S2 is exp(W2)^2,
  S3 is exp(W3)^2,
  Par=..[grad,PA,Mu1,Mu2,Mu3,S1,S2,S3].

logistic(X,Sigma_X):-
  Sigma_X is 1/(1+exp(-X)).
gd(_EA,_ER,0,Par,LL,_D,Par,LL):-!.

gd(EA,ER,Iter0,Par0,LL0,D,Par,LL):-
  format("Iteration ~d~nLog Likelihood ~f~n",[Iter0,LL0]),
  compute_gradient_gd(D,Par0,G,LL1),
  format("New Log Likelihood ~f~n",[LL1]),
  Iter is Iter0-1,
  Diff is LL1-LL0,
  Fract is -LL0*ER,
  (( Diff<EA;Diff<Fract)->
    LL=LL1,
    Par=Par0
  ;
    update_parameters(Par0,G,Par1,0.00005),
%    maplist(update_par(0.02),Par0,G,Par1),
    gd(EA,ER,Iter,Par1,LL1,D,Par,LL)
  ).

update_parameters([_WA,_Mu1,_Mu2,Mu3,_,_,WS3],[_GA,_G1,_G2,G3,_,_,GS3],[-0.84729786038,2.0,3,Mu31,0,0,WS31],Eta):-
%  WA1 is WA+Eta*GA,
 % Mu11 is Mu1+Eta*G1,
  WS31 is WS3+Eta*GS3,
%  Mu21 is Mu2+Eta*G2.
  Mu31 is Mu3+Eta*G3.

compute_gradient_gd(D,ParList,G,LL):-
  Par=..[par|ParList],
  length(ParList,NP),
  maplist(eval_grad(Par,NP),D,L,GL),
  sum_list(L,LL),
  findall(0,between(1,NP,_),G0),
  foldl(sum,GL,G0,G).

sum(L,G0,G):-
  maplist(addition,L,G0,G).

addition(A,B,C):-
  C is A+B.

eval_grad(Env,NP,X,L,GL):-
  p(X,Expr),
  findall(0,between(1,NP,_),GL0),
  G=..[grad|GL0],
  revad(Expr,Env,1,L,G),
  G=..[grad|GL].

update_par(Eta,Par0,G,Par1):-
  Par1 is Par0+Eta*G.

init_gd_par(_,Max,[-0.84729786038,2,3,Mu3,0,0,WS3]):-
% -0.84729786038= sigma^-1(0.3)
%-2.30258509299 = ln(0.1)
%  WA is -Max+random_float*2*Max,
%  Mu1 is -Max+random_float*2*Max.
%  Mu2 is -Max+random_float*2*Max.
  Mu3 is -Max+random_float*2*Max,
  WS3 is -Max+random_float*2*Max.
  

/*
init_gd_par(0,_Max,[]):-!.

init_gd_par(I,Max,[W|TW]):-
  I1 is I-1,
  W is -Max+random_float*2*Max,
  init_gd_par(I1,Max,TW).
*/