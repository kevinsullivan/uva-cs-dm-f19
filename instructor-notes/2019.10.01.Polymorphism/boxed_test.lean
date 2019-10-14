import .boxed
open boxed_adt
open boxed_adt.boxed 

def b1 : boxed nat := box 3
def b2 : boxed bool := box tt
def b3 : boxed string := box "I love polymorphism"

def b1' := box 3

#check b1'

def b2' := box tt

#check b2'

#reduce unbox b1
#reduce unbox b2
#eval unbox b3

#reduce @unbox nat b1
#reduce @unbox bool b2
#eval @unbox string b3
