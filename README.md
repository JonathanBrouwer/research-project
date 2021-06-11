# Practical verification of QuadTrees

## What is this?
Agda2hs is a project which compiles a subset of Agda to Haskell. This paper aims to implement and verify the Haskell library QuadTree in this subset of Agda, so Agda2hs can then produce a verified Haskell implementation. Techniques are developed for proving invariants, preconditions, and post-conditions, and are applied in order to implement and verify the QuadTree library. Additionally, recommendations are made to reduce the time needed for verification.
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
