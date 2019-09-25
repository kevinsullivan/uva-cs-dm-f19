

namespace mylogic


inductive tool : Type
| T
| F
| D

open tool

def tand : tool → tool → tool
| T T := T
| T D := D
| D T := D
| D D := D
| _ _ := F

#check tool

#check tand
#check (tand T)
#check (tand T) D

end mylogic



namespace mynat


inductive mnat : Type
| zero
| succ : mnat → mnat

open mnat 

def inc : mnat → mnat :=
    λ n : mnat, succ n

def inc' (n : mnat) : mnat :=
    succ n

def is_zero : mnat → bool
| zero := tt
| _ := ff

#reduce is_zero zero
#reduce is_zero (succ (succ (succ zero)))


def pred : mnat → mnat 
| zero := zero
| (succ m) := m

#reduce pred zero
#reduce pred (succ (succ (succ zero)))
#reduce pred (succ zero)



def eq_mnat : mnat → mnat → bool
| zero zero := tt 
| zero (succ m) := ff
| (succ m) zero := ff
| (succ m) (succ n) := eq_mnat m n


def add_mnat : mnat → mnat → mnat
| zero m := m
| (succ n') m := succ (add_mnat n' m)

end mynat




























namespace mylogic

-- a three-valued logic

inductive tool : Type
| ttt
| fff
| dk

open tool

-- by cases
def tand : tool → tool → tool 
| ttt ttt := ttt
| ttt dk := dk
| ttt fff := fff
| dk ttt := dk
| dk dk := dk
| _ _ := fff

end mylogic



namespace mynat

inductive mnat : Type
| zero
| succ : mnat → mnat

open mnat

-- convenient names
def one := succ zero
def two := succ (succ zero)
def two' := succ one
def three := succ two
def four := succ three

def zero_mnat : mnat → mnat
| _ := zero

def is_zero : mnat → bool
| zero := tt
| _ := ff

#reduce is_zero zero
#reduce is_zero four


-- 
def pred : mnat → mnat
| zero := zero
| (succ n') := n'



#reduce pred (succ (succ zero))
#eval pred (succ (succ zero))


def eq_mnat : mnat → mnat → bool
| zero zero := tt
| zero (succ n') := ff
| (succ n') zero := ff
| (succ n') (succ m') := eq_mnat n' m'

end mynat