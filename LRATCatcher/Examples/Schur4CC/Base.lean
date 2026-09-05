import LRATCatcher.Cover
import LRATCatcher.Showcases.Schur

open Std.Sat LRATCatcher

namespace LRATCatcher.Examples.Schur4CC

def base : CNF Nat := LRATCatcher.Schur.encodeK 4 45

def cubes : List Cube := LRATCatcher.parseICnf "a 1 2 3 0
a 1 2 -3 0
a 1 -2 3 0
a 1 -2 -3 0
a -1 2 3 0
a -1 2 -3 0
a -1 -2 3 0
a -1 -2 -3 0
"

end LRATCatcher.Examples.Schur4CC
