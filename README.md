# CoprimeReduction

This repository contains Magma code to accompany the article "On the Density of Coprime Reductions of Elliptic Curves" by [Asimina S. Hamakiotes](https://asiminah.github.io/), [Jacob Mayle](https://www.jacobmayle.com/), [Sung Min Lee](https://www.johnsungminlee.com/), and [Tian Wang](https://sites.google.com/uic.edu/twang/home).

## Description of Files

- `DeltaGroup.m` Contains code for working with the group $$\Delta(\mathbb{Z}/n\mathbb{Z})$$.

- `Examples.m` Contains code associated with the examples in Section 7 of the article.

- `Proposition 34.m` Contains the code needed for the proof of Proposition 34.

- `SerrePairs.m` Contains code related to Serre pairs, including `IsSerrePair.m`, which checks whether a pair of Serre curves forms an Serre pair. The result is rigorous when true and heuristic when false. This file also includes code related to the coprimality constant for Serre pairs.

## Notes
 
To run parts of this code, you must install David Zywina's OpenImage repository, available [here](https://github.com/davidzywina/OpenImage/tree/master). It is essential to use an up-to-date version of Magma for this to run (we used Magma V2.28-21). 

If you have any questions, comments, or suggestions, please contact us.
