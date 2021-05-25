# Practical verification of QuadTrees

## What is this?
//TODO add abstract + link to research paper here

## How to explore?
Each directory in the sources has an explanation as to what each file is for.
[Click here to start exploring!](https://github.com/JonathanBrouwer/research-project/tree/master/src/Data)

## How to install and run
- Make sure Haskell and Agda are installed via Stack
- Download and install my fork of agda2hs, available at https://github.com/JonathanBrouwer/agda2hs (This compiles Nats in a different way)
- `git clone https://github.com/JonathanBrouwer/research-project.git`
- `cd research-project`
- `make` (no arguments to the make needed)
- It should now have compiled all agda files to haskell
- To run Haskell quickcheck, run `stack test`
