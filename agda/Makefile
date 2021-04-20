.PHONY: default build

default: build

build: 
	mkdir -p build
	@echo == Compiling project ==
	agda2hs -o build src/Project.agda

haskell: build
	ghc -fno-code build/Project.hs
