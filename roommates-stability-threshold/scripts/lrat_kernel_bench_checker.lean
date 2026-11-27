/-- Binary trie keyed by Nat (bits from least significant). -/
inductive Trie where
  | leaf : Trie
  | node : Trie → Option (List Nat) → Trie → Trie

def Trie.find : Trie → Nat → Option (List Nat)
  | .leaf, _ => none
  | .node l v r, k => if k == 0 then v else if k % 2 == 0 then l.find (k / 2) else r.find (k / 2)

def Trie.ins : Nat → Trie → Nat → List Nat → Trie
  | 0, t, _, _ => t
  | f + 1, .leaf, k, c => if k == 0 then .node .leaf (some c) .leaf
      else if k % 2 == 0 then .node (Trie.ins f .leaf (k / 2) c) none .leaf
      else .node .leaf none (Trie.ins f .leaf (k / 2) c)
  | f + 1, .node l v r, k, c => if k == 0 then .node l (some c) r
      else if k % 2 == 0 then .node (Trie.ins f l (k / 2) c) v r else .node l v (Trie.ins f r (k / 2) c)

def Trie.insert (t : Trie) (k : Nat) (c : List Nat) : Trie := Trie.ins 20 t k c

def isTrue (A l : Nat) : Bool := (A >>> l) % 2 == 1

/-- result: 0 = conflict, l+1 = unit literal l, or failure marker. -/
def evalClause (A : Nat) : List Nat → Option Nat → Option (Option Nat)
  | [], u => some u
  | l :: ls, u =>
    if isTrue A (l ^^^ 1) then evalClause A ls u
    else if isTrue A l then none
    else match u with
      | none => evalClause A ls (some l)
      | some _ => none

def rup (db : Trie) : Nat → List Nat → Bool
  | _, [] => false
  | A, h :: hs =>
    match db.find h with
    | none => false
    | some c =>
      match evalClause A c none with
      | some none => true
      | some (some l) => rup db (A ||| (1 <<< l)) hs
      | none => false

def negAll : List Nat → Nat → Nat
  | [], A => A
  | l :: ls, A => negAll ls (A ||| (1 <<< (l ^^^ 1)))

def buildDB : List (List Nat) → Nat → Trie → Trie
  | [], _, t => t
  | c :: cs, i, t => buildDB cs (i + 1) (t.insert i c)

def checkSteps : Trie → List (Nat × List Nat × List Nat) → Bool
  | _, [] => true
  | db, (i, c, h) :: rest => rup db (negAll c 0) h && checkSteps (db.insert i c) rest

def checkAll (cnf : List (List Nat)) (steps : List (Nat × List Nat × List Nat)) : Bool :=
  checkSteps (buildDB cnf 1 .leaf) steps
