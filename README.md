**MOVED:** The `FVect` datatype can be found in the [containers](https://github.com/idris-community/idris2-containers) package going forward. This package will no longer be maintained aside from potentially making changes to keep it compiling against the latest Idris2 builds. Even that is not a guarantee.

# FVect

An Idris 2 FVect (Fin-based Vect) type and its utility functions.

The idea is to have a Vect type that knows not only how long it currently is but also the longest it ever could be. One reasonable interpretation of the latter is "capacity."

For example, it can be useful to create an FVect with a certain length and equal maximum capacity and know without additional work that filtering the values of the vector produces an equal-or-smaller number of values. FVect encodes the proof that the filtered FVect has size that is `LTE` the original size (i.e. capacity).
