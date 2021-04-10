Level : Agda.Term (Agda.set (univ.s univ.zero)) (Agda.code (Agda.set univ.zero));
rule Agda.Term _ Level ↪ univ.Lvl;
symbol lzero : Agda.Term (Agda.set univ.zero) Level;
rule lzero ↪ univ.zero;
symbol lsuc : Agda.Term (Agda.set univ.zero) (Agda.prod (Agda.set univ.zero) (Agda.set univ.zero) Level (λ  {|ℓ|} ,  Level));
rule lsuc ↪ univ.s;
symbol {|_⊔_|} : Agda.Term (Agda.set univ.zero) (Agda.prod (Agda.set univ.zero) (Agda.set univ.zero) Level (λ  {|ℓ₁|} ,  Agda.prod (Agda.set univ.zero) (Agda.set univ.zero) Level (λ  {|ℓ₂|} ,  Level)));
rule {|_⊔_|} ↪ univ.max;
symbol {|Setω|} : Agda.Term (Agda.axiom (Agda.axiom Agda.sortOmega)) (Agda.code (Agda.axiom Agda.sortOmega));
