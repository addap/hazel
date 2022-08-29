EXE := ad.exe multivar_ad.exe promises.exe invert.exe ref.exe test.exe

all: $(EXE)

multivar_ad.exe: dim.ml vector.mli vector.ml multivar_ad.ml
	dune build multivar_ad.exe

%.exe: %.ml
	dune build $@

test:
	dune build ad.exe
	_build/4.12.0+domains+effects/ad.exe

clean:
	dune clean

.PHONY: clean test all
