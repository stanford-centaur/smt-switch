# Issues to Consider

## Hashing
* If we rely on the solver to traverse terms and wrap the resulting terms, we need to rely on the equality operator for the underlying objects
* If everything is a shared_ptr, this might be counterintuitive, because you can use == but it won't do quite what you think
  * it sounds like it does compare the underlying data, but even that might not be good enough
  * Imagine you have two versions of an AbsTerm implementation, one from when it was created and one that was supplied by the solver when traversing
    * There's no way to tell if they're the same or different, without comparing the underlying solver term that is pointed to

## Models
* in Boolector, assignments are returned as strings. 
  * We can then turn these back into bit-vectors, but there's no way to recover the value once it's a node again
  * Additionally, for arrays, there's no boolector structure for this. We'll need to have a representation for this
  * CVC4 has it's stores on a constant array structure, but maybe we should have a common representation for all solvers
  * a map with a default value would be most convenient
  
## Sorts
* It would be useful to be able to query the sort from boolector - two options
  * reconstruct a sort object using calls to boolector functions <-- I think this one is better
    * but, whenever possible, don't reconstruct a sort object
    * for example, in get_value, can do everything with raw BoolectorSorts
  * store it explicitly -- this would require knowing what sort an op produces
