/*
Run the following to test this ontology:
[diagnose,repair,util,reform,revise,utilRevise,stepmother,upgrade,unblock].


subtract(
[[(-[parent, [camilla], [...]], [-[parent, [...]|...]])]],
[(-[parent, [camilla], [bill]], [-[parent, [camilla], [...]]])],
[[(-[parent, [camilla], [...]], [-[parent, [...]|...]])]])


fact([parent2(x,y,cstep)]).
fact([parent(camilla,bill)]).
% fact([parent(liza,bill)]).


fact([+stepmum(camilla,william)]).
fact([-stepmum($x,$z),+parent($x,$z)]).
fact([-parent2(camilla,william,step)]).


fact([+parent2($x,$y,cstep)]).
fact([-parent(camilla,bill)]).


[ +[equal,[diana],[camilla]],
  +[equal,[camilla],[diana]],
  +[equal,[diana],[diana]],
  +[mum,[diana],[bill]],
  +[equal,[camilla],[camilla]],
  +[mum,[camilla],[bill]],
  +[equal,[diana],[camilla]]]

[-[mum,vble(x),[bill]],+[equal,vble(x),[diana]]]

[[-[parent2,[camilla],[william],[step]]],+[parent,vble(x),vble(z)]]
*/

fact([+parent2($x,$y,cstep)]).
fact([-parent(camilla,bill)]).


fact1([parent2(x,y,cstep)]).
fact1([parent(camilla,bill)]).


/*
test:-

([parent2, vble(x), vble(y), [cstep]],
[parent, [camilla], [bill]], _G12897)

test([1],X):-
    X=22,    print(22), test(22,[4],[]).
test(22,[4],X):- member(Z,X),print(Z).


AfterOnt
[([-[cap_of,vble(x),vble(y)],-[cap_of,vble(z),vble(y)],+[==,vble(x),vble(z)]],[])]


[([-[cap_of,vble(z),[britain]],+[==,[edinburgh],vble(z)]],([+[cap_of,[edinburgh],[britain]]],[]),1,([-[cap_of,vble(x),vble(y)],-[cap_of,vble(z),vble(y)],+[==,vble(x),vble(z)]],[]),1),
 ([-[cap_of,vble(x),[britain]],+[==,vble(x),[edinburgh]]],([+[cap_of,[edinburgh],[britain]]],[]),1,([-[cap_of,vble(x),vble(y)],-[cap_of,vble(z),vble(y)],+[==,vble(x),vble(z)]],[]),2),
 ([-[cap_of,vble(z),[britain]],+[==,[london],vble(z)]],([+[cap_of,[london],[britain]]],[]),1,([-[cap_of,vble(x),vble(y)],-[cap_of,vble(z),vble(y)],+[==,vble(x),vble(z)]],[]),1),
 ([-[cap_of,vble(x),[britain]],+[==,vble(x),[london]]],([+[cap_of,[london],[britain]]],[]),1,([-[cap_of,vble(x),vble(y)],-[cap_of,vble(z),vble(y)],+[==,vble(x),vble(z)]],[]),2),
 ([+[cap_of,[london],[britain]]],[]),([+[cap_of,[edinburgh],[britain]]],[]),([-[cap_of,vble(x),vble(y)],-[cap_of,vble(z),vble(y)],+[==,vble(x),vble(z)]],[])]
*/

test():- 1=2.
 grade(1).
grade(2).
