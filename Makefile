.PHONY: default build

default: build

build: 
	@echo == Compiling project ==
	mkdir -p build
	agda2hs -o build src/Data/QuadTree/InternalAgda.agda
	@echo == Installing project ==
	yes | cp -i build/Data/QuadTree/*.hs src/Data/QuadTree/
	yes | cp -i build/Data/Lens/*.hs src/Data/Lens/
	yes | cp -i build/Data/*.hs src/Data/
	@echo 
	@echo == Checking project ==
	stack ghc -- -fno-code src/Data/*/*.hs src/Data/*.hs
	@echo == Finished. ==
