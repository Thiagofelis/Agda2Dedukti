symbol TYPE__X : TYPE;
symbol X : Agda.Term (Agda.set (univ.s univ.zero)) (Agda.code (Agda.set univ.zero));
rule Agda.Term _ X ↪ TYPE__X;
symbol X__arr : Agda.Term (Agda.set univ.zero) (Agda.prod (Agda.set univ.zero) (Agda.set univ.zero) X (λ _0 , Agda.prod (Agda.set univ.zero) (Agda.set univ.zero) X (λ _0 , X)));
rule Agda.etaExpand _ X (X__arr $x0 $x) ↪ X__arr (Agda.etaExpand univ.zero X $x0) (Agda.etaExpand univ.zero X $x);
