import .boxed

#check boxed

open boxed

def b2 : boxed nat := box 3
def b3 := box 3
def b4 := box tt
def b5 := box "I love polymorphism"

#check b3
#check b4
#check b5

#eval unbox b3
#eval unbox b4
#eval unbox b5