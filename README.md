# DirichletCharacters`

Mathematica code for handling Dirichlet Characters properly.

Uses Conrey's notation, as on the LMFDB. Allows for multiplying characters, raising characters to powers, computing properties (even, odd, primitive, equal), finding inducing characters and lifting characters, character tables, switching notation between Conrey and Mathematica. Also has rigorously computed zeros of L-series with conductor up to 934. Will compute more zeros nonrigorously.

The zeros, guaranteed correct with 2*10^{-12}, were computed by Andrew Rechnitzer as part of our work "Counting Zeros of Dirichlet L-Functions" (https://arxiv.org/abs/2005.02989).

## Metadata
      Author: Kevin O'Bryant
      Date:   July 24, 2018
      License:Feel free to use and reuse however, noncommercially, but I'd appreciate a citation if you have one to give. And prior permission for commercial use.

## Getting Started
Put DirichletCharacters.wl in the directory FileNameJoin[{$UserBaseDirectory, "Applications"}]
Put dataset.mx (if you want to use the precomputed zeros of L-series) in the directory FileNameJoin[{$UserBaseDirectory, "ApplicationData","DirichletCharacters"}]

Use "<< DirichletCharacters`" (without the double-quotes, but with the backward quote) to load the package.

Examples are in the DCExamples.nb file.

Unit tests are in the CharacterUnitTest.nb file.
