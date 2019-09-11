/-
An executable specification
of the standard Fibonacci function. Takes one
natural number, n, as an argument, and
returns the n'th Fibonacci number (fib n).
-/

def fib: nat → nat 
| 0 := 0
| 1 := 1
| (n' + 2) := fib n' + fib (n'+1)
