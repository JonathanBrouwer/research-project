# [PLEASE READ]
# A practical verification of QuadTree

## How to install and run
- Make sure Haskell and Agda are installed via Stack
- Download and install my fork of agda2hs, available at https://github.com/JonathanBrouwer/agda2hs (This adds a fix for Nats and for instance arguments)
- `git clone https://github.com/JonathanBrouwer/research-project.git`
- `cd research-project`
- `make` (no arguments to the make needed)
- It should now have compiled all agda files to haskell
- To run Haskell quickcheck, run `stack test`
