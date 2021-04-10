symbol TYPE__r : TYPE;
symbol r : Agda.Term (Agda.set (univ.s (univ.s univ.zero))) (Agda.code (Agda.set (univ.s univ.zero)));
rule Agda.Term _ r ↪ TYPE__r;
symbol r__A : Agda.Term (Agda.set (univ.s univ.zero)) (Agda.proj_prod (Agda.set (univ.s univ.zero)) (Agda.set (univ.s univ.zero)) r (λ r , Agda.code (Agda.set univ.zero)));
symbol r__b : Agda.Term (Agda.set (univ.s univ.zero)) (Agda.proj_prod (Agda.set (univ.s univ.zero)) (Agda.set univ.zero) r (λ r , r__A r));
symbol r__cons : Agda.Term (Agda.set (univ.s univ.zero)) (Agda.prod (Agda.set (univ.s univ.zero)) (Agda.set (univ.s univ.zero)) (Agda.code (Agda.set univ.zero)) (λ A , Agda.prod (Agda.set univ.zero) (Agda.set (univ.s univ.zero)) A (λ b , r)));
rule Agda.etaExpand _ r $y ↪ r__cons (r__A $y) (Agda.etaExpand univ.zero (r__A $y) (r__b $y));
rule r__A (r__cons $A $b) ↪ $A;
rule r__b (r__cons $A $b) ↪ Agda.etaExpand univ.zero $A $b;
