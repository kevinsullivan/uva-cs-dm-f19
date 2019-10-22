import ..src.functions

def is_str_ev_len : string → bool := 
    mcompose 
    (λ n, n % 2 = 0)
    (λ s, string.length s)

#eval is_str_ev_len "Hello There"