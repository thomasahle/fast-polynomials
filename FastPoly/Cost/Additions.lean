import FastPoly.Cost.Additions.Final

/-!
# Share-aware addition counts for the paper's schedules

Compatibility wrapper for the public addition-accounting API.  The implementation is
split by dependency layer:

* `Additions.T` contains the primitive and shared-T recurrences;
* `Additions.Gadgets` contains the auxiliary odd-gadget ledgers;
* `Additions.Final` contains the compatible-pair and complete-polynomial bounds.

Importing this module continues to expose every pre-split declaration.
-/
