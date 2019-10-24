namespace prop_logic

/-
    *** SYNTAX ***
-/

inductive var : Type 
| mkVar : ℕ → var

inductive unOp : Type
| notOp

inductive binOp : Type
| andOp
| orOp
| xorOp
| implOp
| iffOp

inductive pExp : Type
| litExp : bool → pExp
| varExp : var → pExp
| unOpExp : unOp → pExp → pExp
| binOpExp : binOp → pExp → pExp → pExp

open var
open pExp
open unOp
open binOp

-- Shorthand notations
def pTrue := litExp tt
def pFalse := litExp ff
def pNot := unOpExp notOp
def pAnd := binOpExp andOp
def pOr := binOpExp orOp
def pXor := binOpExp xorOp
def pImpl := binOpExp implOp
def pIff := binOpExp iffOp

-- conventional notation

notation e1 ∧ e2 :=  pAnd e1 e2
notation e1 ∨ e2 :=  pOr e1 e2
notation ¬ e := pNot e
notation e1 ⇒ e2 := pImpl e1 e2
notation e1 ⊕ e2 := pXor e1 e2
notation e1 ↔ e2 := pIff e1 e2

/-
    *** SEMANTICS ***
-/

def interpUnOp : unOp → (bool → bool) 
| notOp := bnot

def bimpl : bool → bool → bool
| tt ff := ff
| _ _ := tt

def biff : bool → bool → bool
| tt tt := tt
| ff ff := tt
| _ _ := ff

def interpBinOp : binOp → (bool → bool → bool) 
| andOp := band
| orOp := bor
| xorOp := bxor
| implOp := bimpl
| iffOp := biff

/-
Given a pExp and an interpretation
for the variables, evaluate the pExp
to determine its Boolean truth value.
-/
def pEval : pExp → (var → bool) → bool 
| (litExp b) i := b
| (varExp v) i := i v
| (unOpExp op e) i := 
    (interpUnOp op) (pEval e i)
| (binOpExp op e1 e2) i := 
     (interpBinOp op)
        (pEval e1 i) 
        (pEval e2 i)


end prop_logic

