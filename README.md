# Practical verification of QuadTrees

## What is this?
Agda2hs is a program which compiles a subset of Agda to Haskell. In this paper, an implementation of the Haskell library QuadTree is created and verified in this subset of Agda, such that Agda2hs can then produce a verified Haskell implementation. To aid with this verification, a number of techniques have been proposed which are used to prove invariants, preconditions and post-conditions of the QuadTree library. Using these techniques, the properties of the library have been proven. Additionally, recommendations are made to reduce the time needed for verification.
The full paper is available [here.](https://github.com/JonathanBrouwer/research-project/blob/master/paper/research_paper.pdf)

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
a