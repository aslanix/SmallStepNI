all: libs basic augmented wf le niexp bridgeall highpcsteps nibridge

LOADPATH = -I lib/ -I lib/cpdt/

BASICFILES = Identifier.v Environment.v Imperative.v Types.v UtilTactics.v

clean:
	rm *.vo *.glob
libs:
	coqc lib/SfLib.v lib/LibTactics.v lib/InductionPrinciple.v

basic: $(BASICFILES)
	coqc $(LOADPATH)  $(BASICFILES)

augmented:basic Augmented.v
	coqc $(LOADPATH) Augmented.v

bridge:augmented Bridge.v
	coqc $(LOADPATH) Bridge.v

bridgetactics:
	coqc $(LOADPATH) BridgeTactics.v

bridgeproperties:
	coqc $(LOADPATH) BridgeProperties.v	

highpcsteps:
	coqc $(LOADPATH) HighPCSteps.v

bridgeall:bridge bridgetactics bridgeproperties

wf:
	coqc $(LOADPATH) WellFormedness.v

le:
	coqc $(LOADPATH) LowEq.v

obs:
	coqc $(LOADPATH) ObsLowEq.v

niexp:
	coqc $(LOADPATH) NIexp.v

nibridge:
	coqc $(LOADPATH) NIBridge.v
