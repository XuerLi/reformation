/*
STEP1: Load these files to test this ontology:
[diagnose,repair,util,reform,revise,utilRevise,stepmother,upgrade,unblock].
STEP2: Run upgrade.
upgrade.


fact1([parent2(x,y,cstep)]).
fact1([parent(camilla,bill)]).

fact([+stepmum(camilla,william)]).
fact([-stepmum($x,$z),+parent($x,$z)]).
fact([-parent2(camilla,william,step)]).


fact([+parent2($x,$y,cstep), +test(x)]).
fact([-parent(camilla,bill), -test(x)]).


fact([+parent2($x,$y,cstep)]).
fact([-parent(camilla,bill)]).

*/



fact([+stepmum(camilla,william)]).
fact([-stepmum($x,$z),+parent($x,$z)]).
fact([-parent2(camilla,william,step)]).
