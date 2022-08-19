EXE := ad.exe stack_ad.exe multivar_ad.exe promises.exe invert.exe ref.exe test.exe

all: $(EXE)

multivar_ad.exe: dim.ml vector.mli vector.ml multivar_ad.ml
	dune build multivar_ad.exe

%.exe: %.ml
	dune build $@

clean:
	dune clean
	rm -f *.exe
	rm -rf dune-project

.PHONY: clean
