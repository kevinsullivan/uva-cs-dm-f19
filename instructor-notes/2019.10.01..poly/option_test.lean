import .option

open myoption

def o1 := moption.some 3
def o2 := moption.none nat

def o3 := moption.some tt
def o4 := moption.none bool

def o5 := moption.some "Hello Lean"
def o6 := moption.none string

def just_zero : ℕ → moption ℕ 
| 0 := moption.some 0
| _ := moption.none nat

#reduce just_zero 0
#reduce just_zero 3
#reduce just_zero 1
#reduce just_zero 17

