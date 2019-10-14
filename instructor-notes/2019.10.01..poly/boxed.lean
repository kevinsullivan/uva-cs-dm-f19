inductive boxed (T : Type) : Type
| box : T → boxed

def unbox {T : Type} : boxed T → T
| (boxed.box n) := n
