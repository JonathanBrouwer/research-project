# Practical Verification of Functional Libraries Template

## Dependencies

You need to have [Agda] and [agda2hs] installed.
To build agda2hs, install `cabal` and run the following commands:

```
git clone git@github.com:agda/agda2hs.git
cd agda2hs
make install
```

The binary `agda2hs` should now be available in `~/.cabal/bin/`. Make sure this
directory is in your `$PATH` environment variable. You can add the following in
your shell config (`~/.zshrc` or `.bashrc`:

```
export PATH=~/.cabal/bin:$PATH
```

In order to use the Haskell prelude of `agda2hs` from your Agda code, you need
to tell Agda where to locate the library. Inside the file `~/.agda/libraries`,
add the following line:

```
/your/path/to/agda2hs/agda2hs.agda-lib
```

## Development

You should be good to go. Open any file in the `src/` directory inside emacs and
you should be able to use the prelude in your code without any issue. Make sure
that agda2hs was compiled with the same version of Agda that you have installed.
(Should be 2.6.1.3 by default).

## Generating Haskell code

Any definition called `someThing` in your Agda code followed by the following
pragma `{-# COMPILE AGDA2HS someThing #-}` will be translated into Haskell code
when compiling.

```
make
```

[Agda]:    https://github.com/agda/Agda
[agda2hs]: https://github.com/agda/agda2hs

## Typechecking the generated Haskell code

To make sure that the generated Haskell code does typecheck, you can run `make haskell`.
It simply launches `ghc -fno-code src/Project.hs`, you can modify this command for your purposes at will.
