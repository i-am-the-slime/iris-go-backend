module Main where

import Unsafe.Reference (reallyUnsafeRefEq)

main :: Array Boolean
main = [ reallyUnsafeRefEq 1 "one", reallyUnsafeRefEq [ 1 ] { one: 1 } ]
