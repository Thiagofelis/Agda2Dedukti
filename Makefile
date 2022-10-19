STDLIBPATH=agda/std-lib

all: compile

compile:
	stack build --fast

theory-objects:
	cd theory/dk/noEta && rm -f *.dko ; dkcheck -e nat.dk && dkcheck -e univ.dk && dkcheck -e Agda.dk
	cd theory/lp/AgdaTheory && make clean && make install

# all tests
test: theory-objects 
	cd tests && bash test.sh "1 3 5"

# all tests, in verbose mode
test-verbose: theory-objects
	cd tests && bash test.sh "1 3 5" -v

# only dk tests
test-dk: theory-objects
	cd tests && bash test.sh "1"

# only lp tests
test-lp: theory-objects
	cd tests && bash test.sh "3"

test-elimPattMatch: theory-objects
	cd tests && bash test.sh "5"

# change STDLIBPATH accordingly to the std-lib path
std-lib: theory-objects
	mkdir -p std-lib-out
	cd agda/std-lib/src && stack exec -- Agda2Dedukti-exe --dk Everything.agda --outDir=../../../std-lib-out/


std-lib2: theory-objects
	mkdir -p std-lib-out
	cd agda/std-lib/src && stack exec -- Agda2Dedukti-exe --dk Algebra.agda -i Algebra --outDir=../../../std-lib-out/
