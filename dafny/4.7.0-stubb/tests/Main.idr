||| Module    : Main.idr
||| Copyright : (c) CONTRIBUTORS.md
||| License   : see LICENSE
|||
||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Data.List

import Test.Golden

%default total

covering
main : IO ()
main
  = runner [ !(testsInDir "misc" "Miscellaneous")
           ]




-- [ EOF ]
