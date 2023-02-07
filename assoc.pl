/*  Part of SWI-Prolog

    Author:        R.A.O'Keefe, L.Damas, V.S.Costa, Glenn Burgess,
                   Jiri Spitz and Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2004-2018, various people and institutions
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(myassoc,
          [ empty_assoc/1,              % ?Assoc
            singleton_assoc/3,          % ?Assoc
            union_assoc/3,              % +Assoc, +Assoc, ?Assoc
            union_with_assoc/4,         % :Goal, +Assoc, +Assoc, ?Assoc
            assoc_to_list/2,            % +Assoc, -Pairs
            is_assoc/1,                 % +Assoc
            assoc_to_keys/2,            % +Assoc, -List
            assoc_to_values/2,          % +Assoc, -List
            gen_assoc/3,                % ?Key, +Assoc, ?Value
            get_assoc/3,                % +Key, +Assoc, ?Value
            get_assoc/5,                % +Key, +Assoc0, ?Val0, ?Assoc, ?Val
            list_to_assoc/2,            % +List, ?Assoc
            map_assoc/2,                % :Goal, +Assoc
            map_assoc/3,                % :Goal, +Assoc0, ?Assoc
            max_assoc/3,                % +Assoc, ?Key, ?Value
            min_assoc/3,                % +Assoc, ?Key, ?Value
            ord_list_to_assoc/2,        % +List, ?Assoc
            put_assoc/4,                % +Key, +Assoc0, +Value, ?Assoc
            put_with_assoc/5            % :Goal, +Key, +Assoc0, +Value, ?Assoc
%             del_assoc/4,                % +Key, +Assoc0, ?Value, ?Assoc
%             del_min_assoc/4,            % +Assoc0, ?Key, ?Value, ?Assoc
%             del_max_assoc/4             % +Assoc0, ?Key, ?Value, ?Assoc
          ]).
% % :- autoload(library(error),[must_be/2,domain_error/2]).
% 
% 
% /** <module> Binary associations
% 
% Assocs are Key-Value associations implemented as  a balanced binary tree
% (AVL tree).
% 
% __Warning: instantiation of keys__
% 
% AVL  trees  depend  on    the   Prolog   _standard  order  of  terms_ to
% organize the keys as a (balanced)  binary   tree.  This implies that any
% term may be used as a key. The   tree may produce wrong results, such as
% not being able to find a key, if  the ordering of keys changes after the
% key has been inserted into the tree.   The user is responsible to ensure
% that variables used as keys or appearing in  a term used as key that may
% affect ordering are not  unified,  with   the  exception  of unification
% against new fresh variables. For this   reason,  _ground_ terms are safe
% keys. When using non-ground terms, either make sure the variables appear
% in places that do not affect the   standard order relative to other keys
% in the tree or make sure to not unify against these variables as long as
% the tree is being used.
% 
% @see            library(pairs), library(rbtrees)
% @author         R.A.O'Keefe, L.Damas, V.S.Costa and Jan Wielemaker
% */
% 
:- meta_predicate
    map_assoc(1, ?),
    map_assoc(2, ?, ?).
 
%!  empty_assoc(?Assoc) is semidet.
%
%   Is true if Assoc is the empty association list.

empty_assoc(t).

singleton_assoc(K,V,t(K,V,1,=,t,t)).

height_assoc(t,0).
height_assoc(t(_,_,H,_,_,_),H).

/*

function Union(t1, t2):
    if t1 = nil:
        return t2
    if t2 = nil:
        return t1
    (t<, b, t>) = Split(t2, t1.root)
    return Join(Union(left(t1), t<), t1.root, Union(right(t1), t>))

 */

union_assoc(T1,T2,T) :-
  union_assoc(first,T1,T2,T).

first(A,_B,A).
second(_A,B,B).

union_with_assoc(_,t, T2, T2) :- !.
union_with_assoc(_,T1,t, T1) :- !.
union_with_assoc(Pred,t(K,V,_,_,T1l,T1r),T2,T5) :-
  split_assoc(T2,K,T2less,MaybeV,T2more),
  maybe_apply(Pred,MaybeV,V,V1),
  union_with_assoc(Pred,T1l,T2less,T3),
  union_with_assoc(Pred,T1r,T2more,T4),
  join_assoc(T3,K,V1,T4,T5).

maybe_apply(_Pred,no,V2,V2) :- !.
maybe_apply( Pred,yes(V1),V2,V) :- call(Pred,V1,V2,V).

/* 
function Split(T,k)
    if (T = nil) return (nil,false,nil)
    (L,m,R) = expose(T)
    if (k = m) return (L,true,R)
    if (k<m) 
       (L',b,R') = Split(L,k)
       return (L',b,Join(R',m,R))
    if (k>m) 
       (L',b,R') = Split(R,k)
       return (Join(L,m,L'),b,R')) 
*/

split_assoc(t,_,t,no,t).
split_assoc(t(K,V,_,_,T1,T2),Ks,Tless,B,Tmore) :-
  ( Ks == K ->
    Tless = T1,
    B = yes(V),
    Tmore = T2
  ; Ks @< K ->
    split_assoc(T1,Ks,Tless,B,R1),
    join_assoc(R1,K,V,T2,Tmore)
  ; /* Ks @> K */
    split_assoc(T2,Ks,L2,B,Tmore),
    join_assoc(T1,K,V,L2,Tless)
  ).

node(L,K,V,R,T) :-
  height_assoc(L,Hl),
  height_assoc(R,Hr),
  H is max(Hl,Hr) + 1,
  balance_from_heights(Hl,Hr,B),
  T = t(K,V,H,B,L,R). 


/*
function Join(TL, k, TR)
    if (Height(TL)>Height(TR)+1) return JoinRightAVL(TL, k, TR)
    if (Height(TR)>Height(TL)+1) return JoinLeftAVL(TL, k, TR)
    return Node(TL,k,TR)
*/

join_assoc(Tl,K,V,Tr,T) :-
  height_assoc(Tl,Hl),
  height_assoc(Tr,Hr),
  ( Hl > Hr + 1 ->
    join_right_assoc(Tl,K,V,Tr,T)
  ; Hr > Hl + 1 ->
    join_left_assoc(Tl,K,V,Tr,T)
  ; /* | Hl - Hr| <= 1 */
    node(Tl,K,V,Tr,T)
  ).

balance_from_heights(Hl,Hr,B) :-
    ( Hl > Hr ->
      B = >
    ; Hl == Hr ->
      B = =
    ; /* Hl < Hr */
      B = <
    ).

/* 

function JoinRightAVL(TL, k, TR)
    (l,k',c) = expose(TL)
    if (Height(c) <= Height(TR)+1)
       T' = Node(c,k,TR)
       if (Height(T') <= Height(l)+1) then return Node(l,k',T')
       else return rotateLeft(Node(l,k',rotateRight(T')))
    else 
        T' = JoinRightAVL(c,k,TR)
        T'' = Node(l,k',T')
        if (Height(T') <= Height(l)+1) return T''
        else return rotateLeft(T'')

*/

/* The height of the left tree
   is `much` larger than that of the right tree. 
*/
join_right_assoc(t(Kl,Vl,_Hl,_Bl,L,C),K,V,Tr,T) :-
  height_assoc(C,Hc),
  height_assoc(Tr,Hr),
  ( Hc =< Hr + 1 ->      % the height of C is compatible with that of Tr
    node(C,K,V,Tr,T1),     % combine them into a new tree T1
    height_assoc(L,HL),
    height_assoc(T1,H1),
    ( H1 =< HL + 1 ->      % the height of T1 is compatible with that of L
      node(L,Kl,Vl,T1,T)     % combine them into a new tree T
    ;                      % H1 =:= Hl + 2  because Hc =:= Hl + 1
      rotate_right(T1,T2),   
      node(L,Kl,Vl,T2,T3),
      rotate_left(T3,T)
    )
  ;
    join_right_assoc(C,K,V,Tr,T1),
    node(L,Kl,Vl,T1,T2),
    height_assoc(T1,H1),
    height_assoc(L,HL),
    ( H1 =< HL + 1 ->
      T = T2
    ; 
      rotate_left(T2,T)
    )
  ).
   
   
/* The height of the right tree
   is `much` larger than that of the left tree. 
*/
join_left_assoc(Tl,K,V,t(Kr,Vr,_Hr,_Br,C,R),T) :-
  height_assoc(C,Hc),
  height_assoc(Tl,Hl),
  ( Hc =< Hl + 1 ->      % the height of C is compatible with that of Tl
    node(Tl,K,V,C,T1),     % combine them into a new tree T1
    height_assoc(R,HR),
    height_assoc(T1,H1),
    ( H1 =< HR + 1 ->      % the height of T1 is compatible with that of R
      node(T1,Kr,Vr,R,T)     % combine them into a new tree T
    ;                      % H1 =:= HL + 2  because Hc =:= HL + 1
      rotate_left(T1,T2),   
      node(T2,Kr,Vr,R,T3),
      rotate_right(T3,T)
    )
  ;
    join_leftt_assoc(Tl,K,V,C,T1),
    node(T1,Kr,Vr,R,T2),
    height_assoc(T1,H1),
    height_assoc(R,HR),
    ( H1 =< HR + 1 ->
      T = T2
    ; 
      rotate_right(T2,T)
    )
  ).

rotate_left(t(Kx,Vx,_,_,T1,t(Kz,Vz,_,_,T23,T4)),T) :-
  node(T1,Kx,Vx,T23,Tx),
  node(Tx,Kz,Vz,T4,T).

rotate_right(t(Kx,Vx,_,_,t(Kz,Vz,_,_,T4,T23),T1),T) :-
  node(T23,Kx,Vx,T1,Tx),
  node(T4,Kz,Vz,Tx,T).

%!  assoc_to_list(+Assoc, -Pairs) is det.
%
%   Translate Assoc to a list Pairs  of   Key-Value  pairs.  The keys in
%   Pairs are sorted in ascending order.

assoc_to_list(Assoc, List) :-
    assoc_to_list(Assoc, List, []).

assoc_to_list(t(Key,Val,_,_,L,R), List, Rest) :-
    assoc_to_list(L, List, [Key-Val|More]),
    assoc_to_list(R, More, Rest).
assoc_to_list(t, List, List).


%!  assoc_to_keys(+Assoc, -Keys) is det.
%
%   True if Keys is the list of keys   in  Assoc. The keys are sorted in
%   ascending order.

assoc_to_keys(Assoc, List) :-
    assoc_to_keys(Assoc, List, []).

assoc_to_keys(t(Key,_,_,_,L,R), List, Rest) :-
    assoc_to_keys(L, List, [Key|More]),
    assoc_to_keys(R, More, Rest).
assoc_to_keys(t, List, List).


%!  assoc_to_values(+Assoc, -Values) is det.
%
%   True if Values is the list of values in Assoc. Values are ordered in
%   ascending order of the key to which they were associated. Values may
%   contain duplicates.

assoc_to_values(Assoc, List) :-
    assoc_to_values(Assoc, List, []).

assoc_to_values(t(_,Value,_,_,L,R), List, Rest) :-
    assoc_to_values(L, List, [Value|More]),
    assoc_to_values(R, More, Rest).
assoc_to_values(t, List, List).

%!  is_assoc(+Assoc) is semidet.
%
%   True if Assoc is an association list. This predicate checks that the
%   structure is valid, elements are in order,   and tree is balanced to
%   the extent guaranteed by AVL trees.   I.e., branches of each subtree
%   differ in depth by at most  1.   Does  _not_  validate that keys are
%   sufficiently instantiated to ensure the tree  remains valid if a key
%   is further instantiated.

is_assoc(Assoc) :-
    nonvar(Assoc),
    is_assoc(Assoc, _Min, _Max, _Depth).

is_assoc(t,X,X,0) :- !.
is_assoc(t(K,_,1,=,t,t),K,K,1) :- !.
is_assoc(t(K,_,2,>,t,t(RK,_,1,=,t,t)),K,RK,2) :-
    !, K @< RK.
is_assoc(t(K,_,2,<,t(LK,_,1,=,t,t),t),LK,K,2) :-
    !, LK @< K.
is_assoc(t(K,_,Depth,B,L,R),Min,Max,Depth) :-
    is_assoc(L,Min,LMax,LDepth),
    is_assoc(R,RMin,Max,RDepth),
    % Ensure Balance matches depth
    compare(B,RDepth,LDepth),
    % Ensure ordering
    LMax @< K,
    K @< RMin,
    Depth is max(LDepth, RDepth)+1.

% gen_assoc(?Key, +Assoc, ?Value) is nondet.
%
%   True if Key-Value is an  association   in  Assoc. Enumerates keys in
%   ascending order on backtracking.
%
%   @see get_assoc/3.

gen_assoc(Key, Assoc, Value) :-
    (   ground(Key)
    ->  get_assoc(Key, Assoc, Value)
    ;   gen_assoc_(Key, Assoc, Value)
    ).

gen_assoc_(Key, t(Key0,Val0,_,_,L,R), Val) :-
    gen_assoc_(Key, Key0,Val0,L,R, Val).
gen_assoc_(_Key, t, _Val) :-
    fail.

gen_assoc_(Key, _,_,L,_, Val) :-
    gen_assoc_(Key, L, Val).
gen_assoc_(Key, Key,Val0,_,_, Val) :-
    Val = Val0.
gen_assoc_(Key, _,_,_,R, Val) :-
    gen_assoc_(Key, R, Val).


%!  get_assoc(+Key, +Assoc, -Value) is semidet.
%
%   True if Key-Value is an association in Assoc.

:- if(current_predicate('$btree_find_node'/5)).
get_assoc(Key, Tree, Val) :-
    Tree \== t,
    '$btree_find_node'(Key, Tree, 0x010405, Node, =),
    arg(2, Node, Val).
:- else.
get_assoc(Key, t(K,V,_,_,L,R), Val) :-
    compare(Rel, Key, K),
    get_assoc(Rel, Key, V, L, R, Val).
get_assoc(_, t, _) :-
    fail.

get_assoc(=, _, Val, _, _, Val).
get_assoc(<, Key, _, Tree, _, Val) :-
    get_assoc(Key, Tree, Val).
get_assoc(>, Key, _, _, Tree, Val) :-
    get_assoc(Key, Tree, Val).
:- endif.


%!  get_assoc(+Key, +Assoc0, ?Val0, ?Assoc, ?Val) is semidet.
%
%   True if Key-Val0 is in Assoc0 and Key-Val is in Assoc.

get_assoc(Key, t(K,V,H,B,L,R), Val, Assoc, NVal) :-
    Assoc = t(K,NV,H,B,NL,NR),
    compare(Rel, Key, K),
    get_assoc(Rel, Key, V, L, R, Val, NV, NL, NR, NVal).
get_assoc(_Key, t, _Val, _, _) :-
    fail.

get_assoc(=, _, Val, L, R, Val, NVal, L, R, NVal).
get_assoc(<, Key, V, L, R, Val, V, NL, R, NVal) :-
    get_assoc(Key, L, Val, NL, NVal).
get_assoc(>, Key, V, L, R, Val, V, L, NR, NVal) :-
    get_assoc(Key, R, Val, NR, NVal).


%!  list_to_assoc(+Pairs, -Assoc) is det.
%
%   Create an association from a  list   Pairs  of Key-Value pairs. List
%   must not contain duplicate keys.
%
%   @error domain_error(unique_key_pairs, List) if List contains duplicate keys

list_to_assoc(List, Assoc) :-
    (   List == []
    ->  Assoc = t
    ;   keysort(List, Sorted),
        (  ord_pairs(Sorted)
        -> length(Sorted, N),
           list_to_assoc(N, Sorted, [], _, Assoc)
        ;  domain_error(unique_key_pairs, List)
        )
    ).
 
list_to_assoc(1, [K-V|More], More, 1, t(K,V,1,=,t,t)) :- !.
list_to_assoc(2, [K1-V1,K2-V2|More], More, 2, t(K2,V2,2,<,t(K1,V1,1,=,t,t),t)) :- !.
list_to_assoc(N, List, More, Depth, t(K,V,Depth,Balance,L,R)) :-
    N0 is N - 1,
    RN is N0 div 2,
    Rem is N0 mod 2,
    LN is RN + Rem,
    list_to_assoc(LN, List, [K-V|Upper], LDepth, L),
    list_to_assoc(RN, Upper, More, RDepth, R),
    Depth is LDepth + 1,
    compare(B, RDepth, LDepth), balance(B, Balance).

%!  ord_list_to_assoc(+Pairs, -Assoc) is det.
%
%   Assoc is created from an ordered list  Pairs of Key-Value pairs. The
%   pairs must occur in strictly ascending order of their keys.
%
%   @error domain_error(key_ordered_pairs, List) if pairs are not ordered.

ord_list_to_assoc(Sorted, Assoc) :-
    (   Sorted == []
    ->  Assoc = t
    ;   (  ord_pairs(Sorted)
        -> length(Sorted, N),
           list_to_assoc(N, Sorted, [], _, Assoc)
        ;  domain_error(key_ordered_pairs, Sorted)
        )
    ).

%!  ord_pairs(+Pairs) is semidet
%
%   True if Pairs is a list of Key-Val pairs strictly ordered by key.

ord_pairs([K-_V|Rest]) :-
    ord_pairs(Rest, K).
ord_pairs([], _K).
ord_pairs([K-_V|Rest], K0) :-
    K0 @< K,
    ord_pairs(Rest, K).
 
%!  map_assoc(:Pred, +Assoc) is semidet.
%
%   True if Pred(Value) is true for all values in Assoc.

map_assoc(Pred, T) :-
    map_assoc_(T, Pred).

map_assoc_(t, _) :-
    true.
map_assoc_(t(_,Val,_,_,L,R), Pred) :-
    map_assoc_(L, Pred),
    call(Pred, Val),
    map_assoc_(R, Pred).

%!  map_assoc(:Pred, +Assoc0, ?Assoc) is semidet.
%
%   Map corresponding values. True if Assoc  is Assoc0 with Pred applied
%   to all corresponding pairs of of values.

map_assoc(Pred, T0, T) :-
    map_assoc_(T0, Pred, T).

map_assoc_(t, _, Assoc) :-
    Assoc = t.
map_assoc_(t(Key,Val,H,B,L0,R0), Pred, Assoc) :-
    Assoc = t(Key,Ans,H,B,L1,R1),
    map_assoc_(L0, Pred, L1),
    call(Pred, Val, Ans),
    map_assoc_(R0, Pred, R1).


%!  max_assoc(+Assoc, -Key, -Value) is semidet.
%
%   True if Key-Value is in Assoc and Key is the largest key.

max_assoc(t(K,V,_,_,_,R), Key, Val) :-
    max_assoc(R, K, V, Key, Val).
max_assoc(t, _, _) :-
    fail.

max_assoc(t, K, V, K, V).
max_assoc(t(K,V,_,_,_,R), _, _, Key, Val) :-
    max_assoc(R, K, V, Key, Val).


%!  min_assoc(+Assoc, -Key, -Value) is semidet.
%
%   True if Key-Value is in assoc and Key is the smallest key.

min_assoc(t(K,V,_,_,L,_), Key, Val) :-
    min_assoc(L, K, V, Key, Val).
min_assoc(t, _, _) :-
    fail.

min_assoc(t, K, V, K, V).
min_assoc(t(K,V,_,_,L,_), _, _, Key, Val) :-
    min_assoc(L, K, V, Key, Val).


%!  put_assoc(+Key, +Assoc0, +Value, -Assoc) is det.
%
%   Assoc is Assoc0, except that Key is  associated with Value. This can
%   be used to insert and change associations.

put_assoc(Key, A0, Value, A) :-
  put_with_assoc(second, Key, A0, Value, A).

put_with_assoc(Pred,Key, A0, Value, A) :-
    insert(A0, Pred, Key, Value, A, _).

insert(t, _Pred, Key, Val, Assoc, Changed) :-
    Assoc = t(Key,Val,1,=,t,t),
    Changed = yes.
insert(t(Key,Val,H,B,L,R), Pred, K, V, NewTree, WhatHasChanged) :-
    compare(Rel, K, Key),
    insert(Rel, t(Key,Val,H,B,L,R), Pred, K, V, NewTree, WhatHasChanged).

insert(=, t(Key,W,H,B,L,R), Pred, _, V, t(Key,U,H,B,L,R), no) :-
    call(Pred,W,V,U).
insert(<, t(Key,Val,H,B,L,R), Pred, K, V, NewTree, WhatHasChanged) :-
    insert(L, Pred, K, V, NewL, LeftHasChanged),
    adjust(LeftHasChanged, t(Key,Val,H,B,NewL,R), left, NewTree, WhatHasChanged).
insert(>, t(Key,Val,H,B,L,R), Pred, K, V, NewTree, WhatHasChanged) :-
    insert(R, Pred, K, V, NewR, RightHasChanged),
    adjust(RightHasChanged, t(Key,Val,H,B,L,NewR), right, NewTree, WhatHasChanged).

adjust(no, Oldree, _, Oldree, no).
adjust(yes, t(Key,Val,H0,B0,L,R), LoR, NewTree, WhatHasChanged) :-
    table(B0, LoR, B1, WhatHasChanged, ToBeRebalanced, H0, H1),
    rebalance(ToBeRebalanced, t(Key,Val,H1,B0,L,R), B1, NewTree, _, _).

adjust_height(no,H0,H0).
adjust_height(yes,H0,H1) :- H1 is H0 + 1.

%     balance  where     balance  whole tree  to be
%     before   inserted  after    increased   rebalanced
table(=      , left    , <      , yes       , no        , H, H1) :- !, H1 is H + 1.
table(=      , right   , >      , yes       , no        , H, H1) :- !, H1 is H + 1.
table(<      , left    , =      , no        , yes       , H, H1) :- !, H1 is H + 1.
table(<      , right   , =      , no        , no        , H, H) :- !.
table(>      , left    , =      , no        , no        , H, H) :- !.
table(>      , right   , =      , no        , yes       , H, H1) :- !, H1 is H + 1.

% %!  del_min_assoc(+Assoc0, ?Key, ?Val, -Assoc) is semidet.
% %
% %   True if Key-Value is in Assoc0 and Key is the smallest key. Assoc is
% %   Assoc0 with Key-Value removed. Warning: This  will succeed with _no_
% %   bindings for Key or Val if Assoc0 is empty.
% 
% del_min_assoc(Tree, Key, Val, NewTree) :-
%     del_min_assoc(Tree, Key, Val, NewTree, _DepthChanged).
% 
% del_min_assoc(t(Key,Val,_B,t,R), Key, Val, R, yes) :- !.
% del_min_assoc(t(K,V,B,L,R), Key, Val, NewTree, Changed) :-
%     del_min_assoc(L, Key, Val, NewL, LeftChanged),
%     deladjust(LeftChanged, t(K,V,B,NewL,R), left, NewTree, Changed).
% 
% %!  del_max_assoc(+Assoc0, ?Key, ?Val, -Assoc) is semidet.
% %
% %   True if Key-Value is in Assoc0 and Key is the greatest key. Assoc is
% %   Assoc0 with Key-Value removed. Warning: This  will succeed with _no_
% %   bindings for Key or Val if Assoc0 is empty.
% 
% del_max_assoc(Tree, Key, Val, NewTree) :-
%     del_max_assoc(Tree, Key, Val, NewTree, _DepthChanged).
% 
% del_max_assoc(t(Key,Val,_B,L,t), Key, Val, L, yes) :- !.
% del_max_assoc(t(K,V,B,L,R), Key, Val, NewTree, Changed) :-
%     del_max_assoc(R, Key, Val, NewR, RightChanged),
%     deladjust(RightChanged, t(K,V,B,L,NewR), right, NewTree, Changed).
% 
% %!  del_assoc(+Key, +Assoc0, ?Value, -Assoc) is semidet.
% %
% %   True if Key-Value is  in  Assoc0.   Assoc  is  Assoc0 with
% %   Key-Value removed.
% 
% del_assoc(Key, A0, Value, A) :-
%     delete(A0, Key, Value, A, _).
% 
% % delete(+Subtree, +SearchedKey, ?SearchedValue, ?SubtreeOut, ?WhatHasChanged)
% delete(t(Key,Val,B,L,R), K, V, NewTree, WhatHasChanged) :-
%     compare(Rel, K, Key),
%     delete(Rel, t(Key,Val,B,L,R), K, V, NewTree, WhatHasChanged).
% delete(t, _, _, _, _) :-
%     fail.
% 
% % delete(+KeySide, +Subtree, +SearchedKey, ?SearchedValue, ?SubtreeOut, ?WhatHasChanged)
% % KeySide is an operator {<,=,>} indicating which branch should be searched for the key.
% % WhatHasChanged {yes,no} indicates whether the NewTree has changed in depth.
% delete(=, t(Key,Val,_B,t,R), Key, Val, R, yes) :- !.
% delete(=, t(Key,Val,_B,L,t), Key, Val, L, yes) :- !.
% delete(=, t(Key,Val,>,L,R), Key, Val, NewTree, WhatHasChanged) :-
%     % Rh tree is deeper, so rotate from R to L
%     del_min_assoc(R, K, V, NewR, RightHasChanged),
%     deladjust(RightHasChanged, t(K,V,>,L,NewR), right, NewTree, WhatHasChanged),
%     !.
% delete(=, t(Key,Val,B,L,R), Key, Val, NewTree, WhatHasChanged) :-
%     % Rh tree is not deeper, so rotate from L to R
%     del_max_assoc(L, K, V, NewL, LeftHasChanged),
%     deladjust(LeftHasChanged, t(K,V,B,NewL,R), left, NewTree, WhatHasChanged),
%     !.
% 
% delete(<, t(Key,Val,B,L,R), K, V, NewTree, WhatHasChanged) :-
%     delete(L, K, V, NewL, LeftHasChanged),
%     deladjust(LeftHasChanged, t(Key,Val,B,NewL,R), left, NewTree, WhatHasChanged).
% delete(>, t(Key,Val,B,L,R), K, V, NewTree, WhatHasChanged) :-
%     delete(R, K, V, NewR, RightHasChanged),
%     deladjust(RightHasChanged, t(Key,Val,B,L,NewR), right, NewTree, WhatHasChanged).
% 
% deladjust(no, OldTree, _, OldTree, no).
% deladjust(yes, t(Key,Val,B0,L,R), LoR, NewTree, RealChange) :-
%     deltable(B0, LoR, B1, WhatHasChanged, ToBeRebalanced),
%     rebalance(ToBeRebalanced, t(Key,Val,B0,L,R), B1, NewTree, WhatHasChanged, RealChange).
% 
% %     balance  where     balance  whole tree  to be
% %     before   deleted   after    changed   rebalanced
% deltable(-      , right   , <      , no        , no    ) :- !.
% deltable(-      , left    , >      , no        , no    ) :- !.
% deltable(<      , right   , -      , yes       , yes   ) :- !.
% deltable(<      , left    , -      , yes       , no    ) :- !.
% deltable(>      , right   , -      , yes       , no    ) :- !.
% deltable(>      , left    , -      , yes       , yes   ) :- !.
% It depends on the tree pattern in avl_geq whether it really decreases.
 
% Single and double tree rotations - these are common for insert and delete.
/* The patterns (>)-(>), (>)-( <), ( <)-( <) and ( <)-(>) on the LHS
   always change the tree height and these are the only patterns which can
   happen after an insertion. That's the reason why we can use a table only to
   decide the needed changes.

   The patterns (>)-( =) and ( <)-( =) do not change the tree height. After a
   deletion any pattern can occur and so we return yes or no as a flag of a
   height change.  */

 
rebalance(no, t(K,V,H,_,L,R), B, t(K,V,H,B,L,R), Changed, Changed).
rebalance(yes, OldTree, _, NewTree, _, RealChange) :-
    avl_geq(OldTree, NewTree, RealChange).

avl_geq(t(A,VA,HA,>,Alpha,t(B,VB,HB,>,Beta,Gamma)),
        t(B,VB,HB1,=,t(A,VA,HA1,=,Alpha,Beta),Gamma), yes) :- !,
        HA1 is HA - 2,
        HB1 =  HB.
avl_geq(t(A,VA,HA,>,Alpha,t(B,VB,HB,=,Beta,Gamma)),
        t(B,VB,HB1,<,t(A,VA,HA1,>,Alpha,Beta),Gamma), no) :- !,
        HA1 =  HB,
        HB1 =  HA.
avl_geq(t(B,VB,HB,<,t(A,VA,HA,<,Alpha,Beta),Gamma),
        t(A,VA,HA1,=,Alpha,t(B,VB,HB1,=,Beta,Gamma)), yes) :- !,
        HA1 =  HA,
        HB1 is HB - 2.
avl_geq(t(B,VB,HB,<,t(A,VA,HA,-,Alpha,Beta),Gamma),
        t(A,VA,HA1,>,Alpha,t(B,VB,HB1,<,Beta,Gamma)), no) :- !,
        HA1 =  HB,
        HB1 =  HA.
avl_geq(t(A,VA,HA,>,Alpha,t(B,VB,HB,<,t(X,VX,HX,B1,Beta,Gamma),Delta)),
        t(X,VX,HX1,=,t(A,VA,HA1,B2,Alpha,Beta),t(B,VB,HB1,B3,Gamma,Delta)), yes) :-
    !,
    table2(B1, B2, B3, HA, HB, HX, HA1, HB1, HX1).
avl_geq(t(B,VB,HB,<,t(A,VA,HA,>,Alpha,t(X,VX,HX,B1,Beta,Gamma)),Delta),
        t(X,VX,HX1,=,t(A,VA,HA1,B2,Alpha,Beta),t(B,VB,HB1,B3,Gamma,Delta)), yes) :-
    !,
    table2(B1, B2, B3, HB, HA, HX, HB1, HA1, HX1).
  
table2(< ,= ,>, HA, HB, HX, HA1, HB1, HX1 ) :- HA1 is HA - 2, HB1 is HB - 1, HX1 is HX + 1.
table2(> ,< ,=, HA, HB, HX, HA1, HB1, HX1 ) :- HA1 is HA - 2, HB1 is HB - 1, HX1 is HX + 1.
table2(= ,= ,=, HA, HB, HX, HA1, HB1, HX1 ) :- HA1 is HA - 2, HB1 is HB - 1, HX1 is HX + 1.



                 /*******************************
                 *            ERRORS            *
                 *******************************/

:- multifile
    error:has_type/2.

error:has_type(assoc, X) :-
    (   X == t
    ->  true
    ;   compound(X),
        compound_name_arity(X, t, 6)
    ).
