.PHONY: default build

default: build

build: 
	@echo == Compiling project ==
	mkdir -p build
	agda2hs -o build src/Data/QuadTree/InternalAgda.agda
	@echo == Installing project ==
	yes | cp -i build/Data/QuadTree/*.hs src/Data/QuadTree/
	@echo 
	@echo == Checking project ==
	stack ghc -- -fno-code src/Data/QuadTree/*.hs
	@echo == Finished. ==
