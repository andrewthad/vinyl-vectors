# vinyl-vectors

This library provides vectors of vinyl records stored as a structure of arrays.
The design was heavily influenced by the `Data.Frames.InCore` module 
of Anthony Cowley's [`Frames` library](http://hackage.haskell.org/package/Frames)
and by Edward Kmett's 
[`hybrid-vectors` library](http://hackage.haskell.org/package/hybrid-vectors).

If you would like to try this out to see how to use it, you can run 
the example as follows:

    git clone https://github.com/andrewthad/vinyl-vectors
    stack build --flag vinyl-vectors:examples && stack exec sorting

You can edit the example file at `examples/sorting.hs` and to try things out.

