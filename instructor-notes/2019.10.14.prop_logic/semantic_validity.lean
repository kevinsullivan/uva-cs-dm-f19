import .prop_logic 

open prop_logic
open prop_logic.var
open prop_logic.unOp
open prop_logic.binOp
open prop_logic.pExp


def isModel (i: var → bool) (e : pExp) :=
    pEval e i = tt

def valid (e : pExp) :=
    ∀ (i : var → bool), 
        isModel i e


def unsatisfiable (e : pExp) :=
    ∀ (i : var → bool),
        ¬ isModel i e

def satisfiable (e : pExp) :=
    ∃ (i : var → bool), 
        isModel i e


def satisfiable' (e : pExp) :=
    ∃ (i : var → bool), 
        isModel i e

