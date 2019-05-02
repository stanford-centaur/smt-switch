# Issues to Consider

## Hashing
* If we rely on the solver to traverse terms and wrap the resulting terms, we need to rely on the equality operator for the underlying objects
* If everything is a shared_ptr, this might be counterintuitive, because you can use == but it won't do quite what you think
  * it sounds like it does compare the underlying data, but even that might not be good enough
  * Imagine you have two versions of an AbsTerm implementation, one from when it was created and one that was supplied by the solver when traversing
    * There's no way to tell if they're the same or different, without comparing the underlying solver term that is pointed to
