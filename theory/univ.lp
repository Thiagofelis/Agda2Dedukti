// The usual encoding of Natural Number (Peano like)
symbol Nat : TYPE;

symbol 0_N : Nat;
symbol s_N : Nat → Nat;
symbol 1_N ≔ s_N 0_N;

symbol max_N : Nat → Nat → Nat;
rule max_N 0_N      $y       ↪ $y
with max_N $x       0_N      ↪ $x
with max_N (s_N $x) (s_N $y) ↪ s_N (max_N $x $y);

// The function plus is not in the grammar, however it is required to compute.

symbol plus_N : Nat → Nat → Nat;
rule plus_N 0_N      $y ↪ $y
with plus_N (s_N $x) $y ↪ s_N (plus_N $x $y);

// The type of level and an intermediary type encoding (somehow) a set of levels.

symbol Lvl : TYPE;
symbol LvlSet : TYPE;

// The grammar we are interested in is
//     t,u ::= x | 0 | s t | max t u
// with x a variable. 

// Nothing is definable, since it is purely syntax. ? ?
symbol zero : Lvl;
symbol s : Lvl → Lvl;
symbol max : Lvl → Lvl → Lvl;

// The "constructor" of Lvl (between quotation marks, because it is a defined function, since some computation must be performed under a Max).
// A Lvl in normal form is Max i {Plus j1 x1, Plus j2 x2,...} with i >= jk for all k. 
symbol Max : Nat → LvlSet → Lvl;

// Encoding of sets of level
// Empty set
symbol Empty : LvlSet;
// A singleton
symbol Plus : Nat → Lvl → LvlSet;
// More elements
associative commutative symbol Union : LvlSet → LvlSet → LvlSet;

rule Union $x           Empty        ↪ $x;
rule Union Empty $x                  ↪ $x; //added by me
rule Union (Plus $i $l) (Plus $j $l) ↪ Plus (max_N $i $j) $l;

symbol mapPlus : Nat → LvlSet → LvlSet;
rule   mapPlus $i Empty           ↪ Empty
with   mapPlus $i (Plus $j $l)    ↪  Plus (plus_N $i $j) $l
with   mapPlus $i (Union $l1 $l2) ↪ Union (mapPlus $i $l1) (mapPlus $i $l2);

rule Max $i   (Plus $j (Max $k $l))             ↪ Max (max_N $i (plus_N $j $k)) (mapPlus $j $l)
with Max $i   (Union (Plus $j (Max $k $l)) $tl) ↪ Max (max_N $i (plus_N $j $k)) (Union (mapPlus $j $l) $tl)
with Max $i   (Union $tl (Plus $j (Max $k $l))) ↪ Max (max_N $i (plus_N $j $k)) (Union (mapPlus $j $l) $tl) //added by me
with Max 0_N  (Plus 0_N $x)                     ↪ $x;



// The reflection of the syntax on Lvl.
rule zero      ↪ Max 0_N Empty;
rule s $x      ↪ Max 1_N (Plus 1_N $x);
rule max $x $y ↪ Max 0_N (Union (Plus 0_N $x) (Plus 0_N $y));

