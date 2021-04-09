require theory.univ as univ;

// Sorts
constant symbol Sort : TYPE;
constant symbol set  : univ.Lvl → Sort;
constant symbol prop : univ.Lvl → Sort;
constant symbol sortOmega : Sort;

// Universe successors
symbol axiom : Sort → Sort;
rule axiom (set $i)  ↪ set (univ.s $i)
with axiom (prop $i) ↪ set (univ.s $i);

// Universe product rules
symbol sortRule : Sort → Sort → Sort;
rule   sortRule (set $i)  (set $j)   ↪ set  (univ.max $i $j)
with   sortRule (set $i)  (prop $j)  ↪ prop (univ.max $i $j)
with   sortRule (prop $i) (set $j)   ↪ set  (univ.max $i $j)
with   sortRule (prop $i) (prop $j)  ↪ prop (univ.max $i $j)
with   sortRule _         sortOmega  ↪ sortOmega;

// Types and terms

constant symbol Univ : Sort → TYPE;
symbol Term : Π (s : Sort), Univ s → TYPE;

constant symbol code : Π (s : Sort), Univ (axiom s);
constant symbol prod : Π (s1 : Sort) (s2 : Sort) (A : Univ s1), (Term s1 A → Univ s2) → Univ (sortRule s1 s2);
constant symbol proj_prod : Π (s1 : Sort) (s2 : Sort) (A : Univ s1), (Term s1 A → Univ s2) → Univ (sortRule s1 s2);

constant symbol qLevel : Π (f : univ.Lvl → Sort), (Π (l : univ.Lvl), Univ (f l)) → Univ sortOmega;

rule Term _ (code $s)      ↪ Univ $s;
rule Term _ (qLevel $f $t) ↪ Π (l : univ.Lvl), Term ($f l) ($t l);

symbol etaExpand : Π (l : univ.Lvl) (A : Univ (set l)), Term (set l) A → Term (set l) A;

rule Term _ (prod (set $a) $b $A $B)  ↪ Π (x : Term (set $a) $A), Term $b ($B (etaExpand $a $A x));
rule Term _ (prod (prop $a) $b $A $B) ↪ Π (x : Term (prop $a) $A), Term $b ($B x);
rule Term _ (proj_prod $a $b $A $B)   ↪ Π (x : Term $a $A), Term $b ($B x);

rule etaExpand _ _ (etaExpand $l $A $x) ↪ etaExpand $l $A $x;
rule etaExpand _ (code _) $x            ↪ $x;

rule etaExpand _ (prod (set  $a) (set $b) $A $B) $f ↪ λ (x : Term (set $a) $A), etaExpand $b ($B (etaExpand $a $A x)) ($f (etaExpand $a $A x));
rule etaExpand _ (prod (prop $a) (set $b) $A $B) $f ↪ λ (x : Term (prop $a) $A), etaExpand $b ($B x) ($f x);
rule etaExpand _ (proj_prod $a   (set $b) $A $B) $f ↪ λ (x : Term $a $A), etaExpand $b ($B x) ($f x);
