// Main term type
type ltl<a>
  Assert{ p : a }
  Not{ x : ltl<a> }
  Or{ x : ltl<a>; y : ltl<a> }
  And{ x : ltl<a>; y : ltl<a> }
  NextX{ x : ltl<a> }
  Release{ x : ltl<a>; y : ltl<a> }
  Until{ x : ltl<a>; y : ltl<a> }
  Ite{ p : a; t : ltl<a>; f : ltl<a> }

// Effect definition for Effective Boolean Algebras (EBA) on characters
effect eba<a>
  ctl eba-true() : a
  ctl eba-false() : a
  ctl eba-not(p : a) : a
  ctl eba-and(p : a, q : a) : a
  ctl eba-equal(p : a, q : a) : bool
  ctl eba-leq(p : a, q : a) : bool
  ctl eba-singleton(c : char) : a
  ctl eba-contains(p : a, c : char) : bool
  ctl eba-show(p : a) : string

fun (==)(x1 : ltl<a>, x2 : ltl<a>) : <div,eba<a>> bool
  match (x1, x2)
    (Assert(p1), Assert(p2)) -> eba-equal(p1, p2)
    (Not(y1), Not(y2)) -> y1 == y2
    (Or(y1, z1), Or(y2, z2)) -> y1 == y2 && z1 == z2
    (And(y1, z1), And(y2, z2)) -> y1 == y2 && z1 == z2
    (NextX(y1), NextX(y2)) -> y1 == y2
    (Release(y1, z1), Release(y2, z2)) -> y1 == y2 && z1 == z2
    (Until(y1, z1), Until(y2, z2)) -> y1 == y2 && z1 == z2
    (Ite(p1, t1, f1), Ite(p2, t2, f2)) -> eba-equal(p1, p2) && t1 == t2 && f1 == f2
    _ -> False

// Ordering for LTL formulas to canonicalize conjunctions and disjunctions
fun (<=)(x1 : ltl<a>, x2 : ltl<a>) : <div,eba<a>> bool
  match (x1, x2)
    (Assert(p1), Assert(p2)) -> eba-leq(p1, p2)
    (Not(y1), Not(y2)) -> y1 <= y2
    (Or(y1, z1), Or(y2, z2)) -> y1 <= y2 && (!(y2 <= y1) || z1 <= z2)
    (And(y1, z1), And(y2, z2)) -> y1 <= y2 && (!(y2 <= y1) || z1 <= z2)
    (NextX(y1), NextX(y2)) -> y1 <= y2
    (Release(y1, z1), Release(y2, z2)) -> y1 <= y2 && (!(y2 <= y1) || z1 <= z2)
    (Until(y1, z1), Until(y2, z2)) -> y1 <= y2 && (!(y2 <= y1) || z1 <= z2)
    (Ite(p1, t1, f1), Ite(p2, t2, f2)) -> eba-leq(p1, p2) && (!eba-leq(p2, p1) || (t1 <= t2 && (!(t2 <= t1) || f1 <= f2)))
    _ -> match x1
      Assert(_) -> True
      Not(_) -> is-assert(x2)
      Or(_, _) -> is-assert(x2) || is-not(x2)
      And(_, _) -> is-assert(x2) || is-not(x2) || is-or(x2)
      NextX(_) -> is-assert(x2) || is-not(x2) || is-or(x2) || is-and(x2)
      Until(_, _) -> is-assert(x2) || is-not(x2) || is-or(x2) || is-and(x2) || is-nextX(x2)
      Release(_, _) -> is-assert(x2) || is-not(x2) || is-or(x2) || is-and(x2) || is-nextX(x2) || is-until(x2)
      Ite(_, _, _) -> is-assert(x2) || is-not(x2) || is-or(x2) || is-and(x2) || is-nextX(x2) || is-until(x2) || is-release(x2)

// Constructors for LTL terms that apply simplifications

fun true() : eba<a> ltl<a> -> Assert(eba-true())
fun is-true(x : ltl<a>) : eba<a> bool
  match x
    (Assert(p)) -> eba-equal(p, eba-true())
    _ -> False

fun false() : eba<a> ltl<a> -> Assert(eba-false())
fun is-false(x : ltl<a>) : eba<a> bool
  match x
    (Assert(p)) -> eba-equal(p, eba-false())
    _ -> False

// Not constructor that applies negation normal form
fun not(x : ltl<a>) : <div,eba<a>> ltl<a>
  match x
    Assert(p) -> Assert(eba-not(p)) // Push not into the algebra
    Not(y) -> y
    Or(y, z) -> and(not(y), not(z)) // Push not into disjunctions
    And(y, z) -> or(not(y), not(z))
    NextX(y) -> next(not(y))
    Release(y, z) -> until(not(y), not(z))
    Until(y, z) -> release(not(y), not(z))
    Ite(p, t, f) -> ite(p, not(t), not(f))

fun assert(p : a) : ltl<a> -> Assert(p)

fun simplify-or(x : ltl<a>, y : ltl<a>) : <div,eba<a>> maybe<ltl<a>>
  if x == false() then Just(y)
  else if x == true() then Just(true())
  else if x == y then Just(x)
  else match x
    Or(x1, x2) -> if x1 == y || x2 == y then Just(x) else Nothing
    Ite(p, t, f) -> Just(ite(p, or(t, y), or(f, y)))
    _ -> Nothing

fun or(x : ltl<a>, y : ltl<a>) : <div,eba<a>> ltl<a>
  match simplify-or(x, y)
    Just(x') -> x'
    Nothing -> match simplify-or(y, x)
      Just(y') -> y'
      Nothing -> match x
        Or(x1, x2) -> or(x1, or(x2, y))
        _ -> if x <= y then Or(x, y) else Or(y, x)

fun simplify-and(x : ltl<a>, y : ltl<a>) : <div,eba<a>> maybe<ltl<a>>
  if x == true() then Just(y)
  else if x == false() then Just(false())
  else if x == y then Just(x)
  else match x
    And(x1, x2) -> if x1 == y || x2 == y then Just(x) else Nothing
    Or(x1, x2) -> Just(or(and(x1, y), and(x2, y)))
    Ite(p, t, f) -> Just(ite(p, and(t, y), and(f, y)))
    _ -> Nothing

fun and(x : ltl<a>, y : ltl<a>) : <div,eba<a>> ltl<a>
  match simplify-and(x, y)
    Just(x') -> x'
    Nothing -> match simplify-and(y, x)
      Just(y') -> y'
      Nothing -> match x
        And(x1, x2) -> and(x1, and(x2, y))
        _ -> if x <= y then And(x, y) else And(y, x)

fun implies(x : ltl<a>, y : ltl<a>) : <div,eba<a>> ltl<a> -> or(not(x), y)

fun next(x : ltl<a>) : <div,eba<a>> ltl<a>
  match x
    Or(y, z) -> or(next(y), next(z))
    And(y, z) -> and(next(y), next(z))
    _ -> NextX(x)

fun release(x : ltl<a>, y : ltl<a>) : ltl<a> -> Release(x, y)

fun until(x : ltl<a>, y : ltl<a>) : ltl<a> -> Until(x, y)

fun prune-ite(x : ltl<a>, p : a) : <div,eba<a>> ltl<a>
  match x
    Ite(q, t, f) ->
      val qT = eba-and(q, p)
      val qF = eba-and(eba-not(q), p)
      val t' = prune-ite(t, qT)
      val f' = prune-ite(f, qF)
      if eba-equal(qT, p) then t'
      else if eba-equal(qF, p) then f'
      else Ite(q, t', f')
    _ -> x

fun simplify-ite(p : a, t : ltl<a>, f : ltl<a>) : <div,eba<a>> maybe<ltl<a>>
  if t == f then Just(t)
  else match t
    Ite(q, t', f') ->
      if f' == f then Just(ite(eba-and(p, q), t', f))
      else if t' == f then Just(ite(eba-and(p, eba-not(q)), f', f))
      else Nothing
    _ -> Nothing

fun ite(p : a, t : ltl<a>, f : ltl<a>) : <div,eba<a>> ltl<a>
  match simplify-ite(p, t, f) // Apply syntactic simplifications
    Just(x') -> x'
    Nothing -> match simplify-ite(eba-not(p), f, t) // Apply syntactic simplifications
      Just(y') -> y'
      Nothing -> prune-ite(Ite(p, t, f), eba-true()) // Prune branches based on satisfiability

fun globally(x : ltl<a>) : <div,eba<a>> ltl<a> -> release(false(), x)
fun match-globally(x : ltl<a>) : <div,eba<a>> maybe<ltl<a>>
  match x
    Release(y, z) -> if is-false(y) then Just(z) else Nothing
    _ -> Nothing

fun eventually(x : ltl<a>) : <div,eba<a>> ltl<a> -> until(true(), x)
fun match-eventually(x : ltl<a>) : <div,eba<a>> maybe<ltl<a>>
  match x
    Until(y, z) -> if is-true(y) then Just(z) else Nothing
    _ -> Nothing

// Finally, the actual derivative definition
fun deriv(x : ltl<a>) : <div,eba<a>> ltl<a>
  match x
    Assert(p) -> ite(p, true(), false())
    Not(y) -> not(deriv(y))
    Or(y, z) -> or(deriv(y), deriv(z))
    And(y, z) -> and(deriv(y), deriv(z))
    NextX(y) -> y
    Release(y, z) -> and(deriv(z), or(deriv(y), x))
    Until(y, z) -> or(deriv(z), and(deriv(y), x))
    _ -> false()

// Fixpoint function for exploring all states arising from derivatives

fun deriv-fixpoint-impl(work : list<ltl<a>>, seen : list<ltl<a>>) : <div,eba<a>> list<ltl<a>>
  match work.head
    Nothing -> seen
    Just(x) ->
      val dx = deriv(x)
      val targetStates = transition-states(dx)
      val newStates = set-minus(targetStates, seen)
      val work' = work.tail ++ newStates
      val seen' = seen ++ newStates
      deriv-fixpoint-impl(work', seen')

// Function for breaking up formulas into states
// Pushes conjunction/disjunction into states when possible (eliminates alternation/non-determinism)
fun transition-states(x : ltl<a>) : <div,eba<a>> list<ltl<a>>
  if is-state(x) then [x]
  else match x
    Or(y, z) -> set-union(transition-states(y), transition-states(z))
    And(y, z) -> set-union(transition-states(y), transition-states(z))
    Ite(_, t, f) -> set-union(transition-states(t), transition-states(f))
    _ -> [x] // unreachable

fun is-state(x : ltl<a>) : <div,eba<a>> bool -> is-state-impl(x) || is-state-impl(not(x))

fun is-state-impl(x : ltl<a>) : <div,eba<a>> bool
  match x
    Or(_, _) -> False
    And(y, z) -> is-state(y) && is-state(z) && (!has-release(y) || !has-release(z))
    Ite(_, _, _) -> False
    _ -> True

fun has-release(x : ltl<a>) : <div,eba<a>> bool
  match x
    Assert(_) -> False
    Not(y) -> has-release(y)
    Or(y, z) -> has-release(y) || has-release(z)
    And(y, z) -> has-release(y) || has-release(z)
    NextX(y) -> has-release(y)
    Release(_, _) -> True
    Until(y, z) -> has-release(y) || has-release(z)
    Ite(_, t, f) -> has-release(t) || has-release(f)

// Condition for states being accepting in the resulting Buchi automata
fun is-accepting(x : ltl<a>) : <div,eba<a>> bool
  if is-true(x) || is-release(x) then True
  else match x
    Or(y, z) -> is-accepting(y) || is-accepting(z)
    And(y, z) -> is-accepting(y) && is-accepting(z)
    _ -> False

// Helpers for using lists as sets

fun set-minus(xs : list<ltl<a>>, ys : list<ltl<a>>) : <div,eba<a>> list<ltl<a>>
  match ys
    Nil -> xs
    Cons(y, ys') -> set-minus(set-remove(xs, y), ys')

fun set-remove(xs : list<ltl<a>>, y : ltl<a>) : <div,eba<a>> list<ltl<a>>
  match xs
    Nil -> Nil
    Cons(x, xs') -> if x == y then set-remove(xs', y) else Cons(x, set-remove(xs', y))

fun set-contains(xs : list<ltl<a>>, y : ltl<a>) : <div,eba<a>> bool
  match xs
    Nil -> False
    Cons(x, xs') -> if x == y then True else set-contains(xs', y)

fun set-union(xs : list<ltl<a>>, ys : list<ltl<a>>) : <div,eba<a>> list<ltl<a>>
  match xs
    Nil -> ys
    Cons(x, xs') -> if set-contains(ys, x) then set-union(xs', ys) else Cons(x, set-union(xs', ys))

// fun deriv-fixpoint(work : list<ltl<a>>) : <div,eba<a>> list<ltl<a>> -> deriv-fixpoint-impl(work, work)

fun precedence(x : ltl<a>) : <div,eba<a>> int
  match x.match-globally
      Just(_) -> 4
      Nothing -> match x.match-eventually
        Just(_) -> 4
        Nothing -> match x
          Assert(_) -> 4
          Not(_) -> 4
          Or(_, _) -> 2
          And(_, _) -> 2
          NextX(_) -> 4
          Release(_, _) -> 2
          Until(_, _) -> 2
          Ite(_, _, _) -> 0

fun context-precedence(x : ltl<a>) : <div,eba<a>> int
  val modifier = match x.match-globally
      Just(_) -> 0
      Nothing -> match x.match-eventually
        Just(_) -> 0
        Nothing -> match x
          Or(_, _) -> 1
          And(_, _) -> 1
          Release(_, _) -> 1
          Until(_, _) -> 1
          _ -> 0
  precedence(x) + modifier

fun parenthesize(x : string, needsParentheses : bool) : string
  if needsParentheses then "(" ++ x ++ ")" else x

fun show-impl(x : ltl<a>, parentPre : int) : <div,eba<a>> string
  val pre = precedence(x)
  val ctxPre = context-precedence(x)
  val str = match x.match-globally
    Just(y) -> "G" ++ show-impl(y, ctxPre)
    Nothing -> match x.match-eventually
      Just(y) -> "E" ++ show-impl(y, ctxPre)
      Nothing -> match x
        Assert(p) -> eba-show(p)
        Not(y) -> "~" ++ show-impl(y, ctxPre)
        Or(y, z) -> show-impl(y, ctxPre) ++ "∨" ++ show-impl(z, ctxPre)
        And(y, z) -> show-impl(y, ctxPre) ++ "∧" ++ show-impl(z, ctxPre)
        NextX(y) -> "X" ++ show-impl(y, ctxPre)
        Release(y, z) -> show-impl(y, ctxPre) ++ "R" ++ show-impl(z, ctxPre)
        Until(y, z) -> show-impl(y, ctxPre) ++ "U" ++ show-impl(z, ctxPre)
        Ite(p, t, f) -> "ite(" ++ eba-show(p) ++ ", " ++ show-impl(t, ctxPre) ++ ", " ++ show-impl(f, ctxPre) ++ ")"
  parenthesize(str, pre < parentPre)

fun show(x : ltl<a>) : <div,eba<a>> string -> show-impl(x, 0)

// Build a simple interval algebra over chars

val interval-algebra = handler
  ctl eba-true() -> resume([('\u0000', '\uFFFF')])
  ctl eba-false() -> resume([])
  ctl eba-not(p : list<(char,char)>) -> resume(interval-not(p))
  ctl eba-and(p : list<(char,char)>, q : list<(char,char)>) -> resume(interval-and(p, q))
  ctl eba-equal(p : list<(char,char)>, q : list<(char,char)>) -> resume(p == q)
  ctl eba-leq(p : list<(char,char)>, q : list<(char,char)>) -> resume(p <= q)
  ctl eba-singleton(c : char) -> resume([(c, c)])
  ctl eba-contains(p : list<(char,char)>, c : char) -> resume(p.any(fn(x) -> c >= x.fst && c <= x.snd))
  ctl eba-show(p : list<(char,char)>) ->
    match show-interval-shorthand(p)
      Just(s) -> resume(s)
      Nothing -> match show-interval-shorthand(interval-not(p))
        Just(s) -> resume("¬" ++ s)
        Nothing ->
          val result = "[" ++ p.map(fn(x) -> show-char(x.fst) ++ "-" ++ show-char(x.snd)).join("") ++ "]"
          resume(result)

fun show-char(c : char) -> trim-left(trim-right(show(c), "'"), "'")

fun show-interval-shorthand(p : list<(char,char)>) : maybe<string>
  match p
    Nil -> Just("⊥")
    [(x, y)] | x == '\u0000' && y == '\uFFFF' -> Just("⊤")
    [(x, y)] | x == y -> Just(show-char(x))
    _ ->
      if p.all(fn(x) -> x.fst == x.snd)
      then Just("(" ++ p.map(fn(x) -> show-char(x.fst)).join("∨") ++ ")")
      else Nothing

fun interval-not(p : list<(char,char)>) : div list<(char,char)>
  var p' := p
  var low := '\u0000'
  var result : list<(char,char)> := []
  while { p' != Nil }
    val (x, y) = p'.head(('a','a'))
    if x > low then
      result := result ++ [(low, x - char(1))]
    low := y + char(1)
    p' := p'.tail
  if low <= '\uFFFF' then
    result := result ++ [(low, '\uFFFF')]
  result

fun interval-and(p : list<(char,char)>, q : list<(char,char)>) : div list<(char,char)>
  var p' := p
  var q' := q
  var result : list<(char,char)> := []
  while { p' != Nil && q' != Nil }
    val (pLow, pHigh) = p'.head(('a','a'))
    val (qLow, qHigh) = q'.head(('a','a'))
    if pLow > qHigh then
      q' := q'.tail
    else if qLow > pHigh then
      p' := p'.tail
    else
      val low = if pLow > qLow then pLow else qLow
      val high = if pHigh < qHigh then pHigh else qHigh
      result := result ++ [(low, high)]
      if pHigh > qHigh then
        q' := q'.tail
      else
        p' := p'.tail
  result

fun (==)(xs : list<(char,char)>, ys : list<(char,char)>) : <div> bool
  if (xs.length == ys.length) then xs.zip(ys).all(fn((x, y)) -> x.fst == y.fst && x.snd == y.snd) else False

fun (!=)(xs : list<(char,char)>, ys : list<(char,char)>) : <div> bool -> !(xs == ys)

fun (<=)(xs : list<(char,char)>, ys : list<(char,char)>) : <div> bool
  xs.length < ys.length || (xs.length == ys.length && xs.zip(ys).all(fn((x, y)) -> x.fst < y.fst && (x.fst == y.fst && x.snd <= y.snd)))

// Function for printing all states of an automaton for a given formula
fun show-derivatives(formula : ltl<a>) : <console,div,eba<a>> ()
  println("Automaton arising from " ++ show(formula))
  val initial = transition-states(formula)
  with x <- deriv-fixpoint-impl(initial,initial).foreach
  var line := "δ(" ++ show(x) ++ ") = " ++ show(deriv(x))
  if is-accepting(x) then
    line := line ++ "  (accepting)"
  if set-contains(initial, x) then
    line := line ++ "  (initial)"
  println(line)

fun show-gep()
  val gep = globally(eventually(assert(eba-singleton('a'))))
  show-derivatives(gep)

fun show-egp()
  val egp = eventually(globally(assert(eba-singleton('b'))))
  show-derivatives(egp)

// ~(GEp => G(~p => Er))
fun show-antichain()
  val p = assert(eba-singleton('p'))
  val r = assert(eba-singleton('r'))
  val antichain = not(implies(globally(eventually(p)), globally(implies(not(p), eventually(r)))))
  show-derivatives(antichain)

fun main()
  with interval-algebra
  show-gep()
  println("")
  show-egp()
  println("")
  show-antichain()