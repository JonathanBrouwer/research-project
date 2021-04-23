.PHONY: default build

default: build

build: 
	@echo == Compiling project ==
	mkdir -p build
	agda2hs -o build src/Data/QuadTree/InternalAgda.agda

install: build
	@echo == Installing project ==
	yes | cp -i build/Data/QuadTree/*.hs src/Data/QuadTree/
	@echo 

haskell: build
	@echo == Checking project ==
	ghc -fno-code build/Data/QuadTree/*.hs
	@echo == Finished. ==

