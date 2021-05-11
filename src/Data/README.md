# src/Data
- [Lens/](https://github.com/JonathanBrouwer/research-project/tree/master/src/Data/Lens) - The implementation and verification of Lenses.
- [QuadTree/](https://github.com/JonathanBrouwer/research-project/tree/master/src/Data/QuadTree) - The implementation and verification of QuadTrees. Most of the interesting code is in here.
- [Logic.agda](https://github.com/JonathanBrouwer/research-project/blob/master/src/Data/Logic.agda) - In here I proved a lot of general purpose properties, and defined equational reasoning. 
- [Nat.hs](https://github.com/JonathanBrouwer/research-project/blob/master/src/Data/Nat.hs) - In here I provide a Haskell implementation of natural numbers, which agda2hs can compile Agda natural numbers to. This is so I can use pattern matching.
- [QuadTree.hs](https://github.com/JonathanBrouwer/research-project/blob/master/src/Data/QuadTree.hs) - This is the public interface of the haskell library that agda2hs will produce for us. This is what the tests are also written for.
