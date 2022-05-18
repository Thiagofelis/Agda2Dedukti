all:
	rm -f elimPattTest.dk
	rm -f Agda__Builtin__Nat.dk
	rm -f Agda__Builtin__Bool.dk
	rm -f Agda__Builtin__Equality.dk
	stack exec -- Agda2Dedukti-exe --dk --ignore-interfaces --no-projection-like -v toDk.elimPattMatch:20 -v toDk:3 elimPattTest.agda
	dkcheck -e -I ../../theory/dk/noEta/ Agda__Builtin__Bool.dk 
	dkcheck -e -I ../../theory/dk/noEta/ Agda__Builtin__Equality.dk
	dkcheck -e -I ../../theory/dk/noEta/ Agda__Builtin__Nat.dk
	dkcheck -e -I ../../theory/dk/noEta/ elimPattTest.dk

test2:
	rm -f elimPattTest2.dk
	rm -f Agda__Builtin__Unit.dk
	rm -f Agda__Builtin__Equality.dk
	stack exec -- Agda2Dedukti-exe --dk --ignore-interfaces --no-projection-like -v toDk.elimPattMatch:20 -v toDk:3 elimPattTest2.agda
	dkcheck -e -I ../../theory/dk/noEta/ Agda__Builtin__Equality.dk
	dkcheck -e -I ../../theory/dk/noEta/ Agda__Builtin__Unit.dk
	dkcheck -e -I ../../theory/dk/noEta/ elimPattTest2.dk
