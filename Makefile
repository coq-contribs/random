all: build

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

build: CoqMakefile
	make -f CoqMakefile

clean: CoqMakefile
	make -f CoqMakefile clean
	rm CoqMakefile
