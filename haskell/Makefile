.PHONY: default build

default: build

build: 
	@echo == Compiling project ==
	mkdir -p build
	agda2hs -o build src/InternalAgda.agda

haskell: build
	@echo == Checking project ==
	ghc -fno-code build/InternalAgda.hs

install: build
	@echo == Installing project ==
	cp build/InternalAgda.hs ../haskell/src/Data/QuadTree/InternalAgda.hs
