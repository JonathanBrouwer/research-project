.PHONY: default build

default: build

build: 
	@echo == Compiling project ==
	mkdir -p build
	agda2hs -o build src/Data/QuadTree/InternalAgda.agda

haskell: build
	@echo == Checking project ==
	ghc -fno-code build/Data/QuadTree/InternalAgda.hs

install: build
	@echo == Installing project ==
	cp build/Data/QuadTree/InternalAgda.hs src/Data/QuadTree/InternalAgda.hs
