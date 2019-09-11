'''
Specification of Fibonacci function.
Requires value of n to be a natural number.
Guarantees return value is fib(n), where
fib(n) is the n'th Fibonacci number. This
definition directly reflects the recursive
mathematical definition of this function.
But it's very slow to evaluate for large x.
'''
def fib_spec(x) :
    if x==0: 
        return 0
    if x==1:
        return 1
    else: 
        return fib_spec(x-2)+ fib_spec(x-1)

'''
Implementation of the Fibonacci function.
Requires value of n to be a natural number.
Guarantees that for all n, fib_impl(n) = 
fib_spec(n), and thus equal to Fib(n),
where Fib is the mathematical function.
This implementation is NOT clear, but it
has the crucial benefit of being fast,
even for very large n.
'''
def fib_impl(n): 
    f2 = 0
    f1 = 1 
    if n == 0: 
        return f2
    if n == 1:
        return f1
    i = 2
    while (i <= n):
        t = f2 + f1
        f2 = f1
        f1 = t
        i = i + 1
    return f1

print(fib_impl(6))

