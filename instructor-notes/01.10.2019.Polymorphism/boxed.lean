namespace boxed_adt

inductive boxed (T : Type) : Type
| box : T → boxed

def unbox {T : Type} : boxed T → T
| (boxed.box t) := t

end boxed_adt