def mcompose {α γ β : Type} : (β → γ) → (α → β) → (α → γ)
| g f := λ (n : α), g (f n)