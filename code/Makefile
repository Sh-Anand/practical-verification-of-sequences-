.PHONY: default build

default: build

build: 
	mkdir build
	@echo == Compiling project ==
	agda2hs -o build src/Project.agda

haskell: build
	ghc -fno-code build/Project.hs
