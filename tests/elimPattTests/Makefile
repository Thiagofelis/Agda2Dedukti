all:
	rm -f elimPattTest.dk
	stack exec -- Agda2Dedukti-exe --dk --ignore-interfaces --no-projection-like -v toDk.elimPattMatch:20 -v toDk:3 elimPattTest.agda

test2:
	rm -f elimPattTest2.dk
	stack exec -- Agda2Dedukti-exe --dk --ignore-interfaces --no-projection-like -v toDk.elimPattMatch:20 -v toDk:3 elimPattTest2.agda
