all: libs basic bridge wf le obs niexp ni

LOADPATH = -I lib/ -R lib/cpdt/src/ "Cpdt" 
clean:
	rm *.vo *.glob

libs:
	coqc lib/SfLib.v lib/LibTactics.v lib/InductionPrinciple.v 
basic:
	coqc $(LOADPATH)  Identifier.v Environment.v  Imperative.v UtilTactics.v 
bridge:
	coqc $(LOADPATH) BridgeSteps.v
wf: 
	coqc $(LOADPATH) WellFormedness.v
le:
	coqc $(LOADPATH) LowEq.v
obs:
	coqc $(LOADPATH) ObsLowEq.v
niexp:
	coqc $(LOADPATH) NIexp.v
ni: 
	coqc $(LOADPATH) NI.v
