import Base
import ./LAWS.bend as Laws
import ../abnf/LAWS.bend as ABNF
# Imported only so the ABNF laws are filled; nothing here names it.
import ../abnf/PROOF.bend as AP
import ../base-extra/LAWS.bend as Extra
import ../base-extra/PROOF.bend as EP

# Base lemmas
# ===========
#
# General facts about Bool, Nat, Char and String, the same as in abnf/PROOF.bend.

# The number of characters from lo to hi.

def rcount(lo: Char, hi: Char) -> Nat:
  Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo)))

# Whether c lies between lo and hi.

def inR(lo: Char, hi: Char, +c: Char) -> Bool:
  Bool.and(U32.is_le(Char.to_u32(lo), Char.to_u32(c)), U32.is_le(Char.to_u32(c), Char.to_u32(hi)))

def bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : bdisc(_)
  Unit{}

def either(a, b, -A: Kind(a), -B: Kind(b), -C: Type, e: Either<a, b, A, B>, f: A -> C, g: B -> C) -> C:
  match e:
    case Inl{x}:
      f(x)
    case Inr{y}:
      g(y)

def tt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {b == True{} : Bool}) -> {a == True{} : Bool}:
  Equal.trans(Bool, a, b, True{}, e, h)

def tt.sym(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool}) -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def or_l(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, false_ne_true(h))
    case True{}:
      {==}

def or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      {==}

def or_elim(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool})
  -> Either<&2, &2, {a == True{} : Bool}, {b == True{} : Bool}>:
  match a:
    case False{}:
      Inr{h}
    case True{}:
      Inl{{==}}

def and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))
    case True{}:
      {==}

def and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(h))
    case True{}:
      h

def and_intro(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool})
  -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, false_ne_true(ha))
    case True{}:
      hb

# Strings
# =======

def cons_eq(-c: Char, -a: String, -b: String, e: {a == b : String}) -> {SCon{c, a} == SCon{c, b} : String}:
  %e : {SCon{c, a} == SCon{c, _} : String}
  {==}

def append_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      cons_eq(c, String.append(t, SNil{}), t, append_nil(t))

# Matching
# ========

def contra(-x: Bool, h1: {x == True{} : Bool}, h2: {x == False{} : Bool}) -> Empty:
  false_ne_true(Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, h2), h1))

def bcase(-C: Type, b: Bool, f: {b == True{} : Bool} -> C, g: {b == False{} : Bool} -> C) -> C:
  match b:
    case True{}:
      f({==})
    case False{}:
      g({==})

def or_false_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      {==}

def or_false_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      h

# Numbers
# =======

def le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n b:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      le(p, q)

def eqn(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      False{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      eqn(p, q)

def succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def plus_zero_r(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      succ_cong(Nat.add(p, 0n), p, plus_zero_r(p))

def plus_succ_r(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      succ_cong(Nat.add(p, 1n+b), 1n+Nat.add(p, b), plus_succ_r(p, b))

def le_refl(a: Nat) -> {le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_succ_r(a: Nat, b: Nat, h: {le(a, b) == True{} : Bool}) -> {le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      Empty.absurd({le(1n+p, 1n) == True{} : Bool}, false_ne_true(h))
    case 1n+p 1n+q:
      le_succ_r(p, q, h)

def le_trans(a: Nat, b: Nat, c: Nat, h1: {le(a, b) == True{} : Bool}, h2: {le(b, c) == True{} : Bool})
  -> {le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      {==}
    case 1n+p 0n c:
      Empty.absurd({le(1n+p, c) == True{} : Bool}, false_ne_true(h1))
    case 1n+p 1n+q 0n:
      Empty.absurd({le(1n+p, 0n) == True{} : Bool}, false_ne_true(h2))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, h1, h2)

def le_add_l(a: Nat, +b: Nat) -> {le(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      le_refl(b)
    case 1n+ +p:
      le_succ_r(b, Nat.add(p, b), le_add_l(p, b))

def succ_le_absurd(a: Nat, h: {le(1n+a, a) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      false_ne_true(h)
    case 1n+p:
      succ_le_absurd(p, h)

def app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      cons_eq(h, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), app_assoc(t, b, c))

def app_congl(-c: String, -a: String, -b: String, e: {a == b : String}) -> {String.append(c, a) == String.append(c, b) : String}:
  %e : {String.append(c, a) == String.append(c, _) : String}
  {==}

def app_congr(-c: String, -a: String, -b: String, e: {a == b : String}) -> {String.append(a, c) == String.append(b, c) : String}:
  %e : {String.append(a, c) == String.append(_, c) : String}
  {==}

# Sub(w, s): w occurs in s.

def Sub(-w: String, -s: String) -> Type:
  &x: String -> &y: String -> {String.append(x, String.append(w, y)) == s : String}

def ncmp(a: Nat, b: Nat) -> Cmp:
  match a b:
    case 0n 0n:
      EQ{}
    case 0n 1n+q:
      LT{}
    case 1n+p 0n:
      GT{}
    case 1n+p 1n+q:
      ncmp(p, q)

def bitv(h: Bool, a: Nat) -> Nat:
  match h:
    case False{}:
      Nat.double(a)
    case True{}:
      1n+Nat.double(a)

def ncmp_bits(a: Nat, b: Nat, ha: Bool, hb: Bool) -> {ncmp(bitv(ha, a), bitv(hb, b)) == Word.cmp.fin(ha, hb, ncmp(a, b)) : Cmp}:
  match a b ha hb:
    case 0n 0n False{} False{}:
      {==}
    case 0n 0n False{} True{}:
      {==}
    case 0n 0n True{} False{}:
      {==}
    case 0n 0n True{} True{}:
      {==}
    case 0n 1n+q False{} False{}:
      {==}
    case 0n 1n+q False{} True{}:
      {==}
    case 0n 1n+q True{} False{}:
      {==}
    case 0n 1n+q True{} True{}:
      {==}
    case 1n+p 0n False{} False{}:
      {==}
    case 1n+p 0n False{} True{}:
      {==}
    case 1n+p 0n True{} False{}:
      {==}
    case 1n+p 0n True{} True{}:
      {==}
    case 1n+p 1n+q False{} False{}:
      ncmp_bits(p, q, False{}, False{})
    case 1n+p 1n+q False{} True{}:
      ncmp_bits(p, q, False{}, True{})
    case 1n+p 1n+q True{} False{}:
      ncmp_bits(p, q, True{}, False{})
    case 1n+p 1n+q True{} True{}:
      ncmp_bits(p, q, True{}, True{})

def wcmp.con(+p: Nat, ha: Bool, +at: Word(p), hb: Bool, +bt: Word(p), e: {Word.cmp(p, at, bt) == ncmp(Word.to_nat(p, at), Word.to_nat(p, bt)) : Cmp})
  -> {Word.cmp.fin(ha, hb, Word.cmp(p, at, bt)) == ncmp(bitv(ha, Word.to_nat(p, at)), bitv(hb, Word.to_nat(p, bt))) : Cmp}:
  %Equal.sym(Cmp, Word.cmp(p, at, bt), ncmp(Word.to_nat(p, at), Word.to_nat(p, bt)), e) : {Word.cmp.fin(ha, hb, _) == ncmp(bitv(ha, Word.to_nat(p, at)), bitv(hb, Word.to_nat(p, bt))) : Cmp}
  Equal.sym(Cmp, ncmp(bitv(ha, Word.to_nat(p, at)), bitv(hb, Word.to_nat(p, bt))), Word.cmp.fin(ha, hb, ncmp(Word.to_nat(p, at), Word.to_nat(p, bt))),
    ncmp_bits(Word.to_nat(p, at), Word.to_nat(p, bt), ha, hb))

# Comparing words compares their numbers.

def wcmp(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == ncmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          wcmp.con(p, False{}, at, False{}, bt, wcmp(p, at, bt))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          wcmp.con(p, False{}, at, True{}, bt, wcmp(p, at, bt))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          wcmp.con(p, True{}, at, False{}, bt, wcmp(p, at, bt))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          wcmp.con(p, True{}, at, True{}, bt, wcmp(p, at, bt))

def ncmp_le(a: Nat, b: Nat) -> {Cmp.is_le(ncmp(a, b)) == le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ncmp_le(p, q)

def ncmp_eq(a: Nat, b: Nat) -> {Cmp.is_eq(ncmp(a, b)) == eqn(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ncmp_eq(p, q)

def add_zero_f(p: Nat, a: Word(p)) -> {Word.adc(p, a, Word.zero(p), False{}, False{}) == a : Word(p)}:
  match p:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+q:
      match a:
        case WCon{False{}, +at}:
          %add_zero_f(q, at) : {WCon{False{}, Word.adc(q, at, Word.zero(q), False{}, False{})} == WCon{False{}, _} : Word(1n+q)}
          {==}
        case WCon{True{}, +at}:
          %add_zero_f(q, at) : {WCon{True{}, Word.adc(q, at, Word.zero(q), False{}, False{})} == WCon{True{}, _} : Word(1n+q)}
          {==}

def add_zero_t(p: Nat, a: Word(p)) -> {Word.adc(p, a, Word.zero(p), False{}, True{}) == Word.inc(p, a) : Word(p)}:
  match p:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+ +q:
      match a:
        case WCon{False{}, +at}:
          %add_zero_f(q, at) : {WCon{True{}, Word.adc(q, at, Word.zero(q), False{}, False{})} == WCon{True{}, _} : Word(1n+q)}
          {==}
        case WCon{True{}, +at}:
          %add_zero_t(q, at) : {WCon{False{}, Word.adc(q, at, Word.zero(q), False{}, True{})} == WCon{False{}, _} : Word(1n+q)}
          {==}

# Adding the word 1 is Word.inc.

def add1_inc(+p: Nat, a: Word(1n+p)) -> {Word.adc(1n+p, a, WCon{True{}, Word.zero(p)}, False{}, False{}) == Word.inc(1n+p, a) : Word(1n+p)}:
  match a:
    case WCon{False{}, +at}:
      %add_zero_f(p, at) : {WCon{True{}, Word.adc(p, at, Word.zero(p), False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
      {==}
    case WCon{True{}, +at}:
      %add_zero_t(p, at) : {WCon{False{}, Word.adc(p, at, Word.zero(p), False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
      {==}

def le_half(a: Nat, b: Nat, h: {le(1n+1n+Nat.double(a), Nat.double(b)) == True{} : Bool}) -> {le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({le(1n, 0n) == True{} : Bool}, false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({le(1n+1n+p, 0n) == True{} : Bool}, false_ne_true(h))
    case 1n+p 1n+q:
      le_half(p, q, h)

def le_half1(a: Nat, b: Nat, h: {le(1n+1n+Nat.double(a), 1n+Nat.double(b)) == True{} : Bool}) -> {le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({le(1n, 0n) == True{} : Bool}, false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({le(1n+1n+p, 0n) == True{} : Bool}, false_ne_true(h))
    case 1n+p 1n+q:
      le_half1(p, q, h)

def inc_nat.dbl(-x: Nat, -y: Nat, e: {x == 1n+y : Nat}) -> {Nat.double(x) == 1n+1n+Nat.double(y) : Nat}:
  %Equal.sym(Nat, x, 1n+y, e) : {Nat.double(_) == 1n+1n+Nat.double(y) : Nat}
  {==}

# Below another word, adding 1 adds 1 to the number.

def inc_nat(n: Nat, a: Word(n), b: Word(n), h: {le(1n+Word.to_nat(n, a), Word.to_nat(n, b)) == True{} : Bool})
  -> {Word.to_nat(n, Word.inc(n, a)) == 1n+Word.to_nat(n, a) : Nat}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          Empty.absurd({0n == 1n : Nat}, false_ne_true(h))
    case 1n+ +p:
      match a b:
        case WCon{False{}, at} WCon{hb, bt}:
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt}:
          inc_nat.dbl(Word.to_nat(p, Word.inc(p, at)), Word.to_nat(p, at),
            inc_nat(p, at, bt, le_half(Word.to_nat(p, at), Word.to_nat(p, bt), h)))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          inc_nat.dbl(Word.to_nat(p, Word.inc(p, at)), Word.to_nat(p, at),
            inc_nat(p, at, bt, le_half1(Word.to_nat(p, at), Word.to_nat(p, bt), h)))

# Characters as numbers.

def nv(x: Char) -> Nat:
  U32.to_nat(Char.to_u32(x))

def ch_le(x: Char, y: Char) -> {U32.is_le(Char.to_u32(x), Char.to_u32(y)) == le(nv(x), nv(y)) : Bool}:
  match x y:
    case Chr{U32{+a}} Chr{U32{+b}}:
      %Equal.sym(Cmp, Word.cmp(32n, a, b), ncmp(Word.to_nat(32n, a), Word.to_nat(32n, b)), wcmp(32n, a, b)) : {Cmp.is_le(_) == le(Word.to_nat(32n, a), Word.to_nat(32n, b)) : Bool}
      ncmp_le(Word.to_nat(32n, a), Word.to_nat(32n, b))

def ch_eq(x: Char, y: Char) -> {Char.is_eq(x, y) == eqn(nv(x), nv(y)) : Bool}:
  match x y:
    case Chr{U32{+a}} Chr{U32{+b}}:
      %Equal.sym(Cmp, Word.cmp(32n, a, b), ncmp(Word.to_nat(32n, a), Word.to_nat(32n, b)), wcmp(32n, a, b)) : {Cmp.is_eq(_) == eqn(Word.to_nat(32n, a), Word.to_nat(32n, b)) : Bool}
      ncmp_eq(Word.to_nat(32n, a), Word.to_nat(32n, b))

def nv_next.go(+a: Word(32n), b: Word(32n), h: {le(1n+Word.to_nat(32n, a), Word.to_nat(32n, b)) == True{} : Bool})
  -> {Word.to_nat(32n, Word.adc(32n, a, WCon{True{}, Word.zero(31n)}, False{}, False{})) == 1n+Word.to_nat(32n, a) : Nat}:
  %Equal.sym(Word(32n), Word.adc(32n, a, WCon{True{}, Word.zero(31n)}, False{}, False{}), Word.inc(32n, a), add1_inc(31n, a)) : {Word.to_nat(32n, _) == 1n+Word.to_nat(32n, a) : Nat}
  inc_nat(32n, a, b, h)

# Below another character, the next character is one more.

def nv_next(x: Char, hi: Char, h: {le(1n+nv(x), nv(hi)) == True{} : Bool}) -> {nv(Chr{(Char.to_u32(x) + 1 : U32)}) == 1n+nv(x) : Nat}:
  match x hi:
    case Chr{U32{a}} Chr{U32{b}}:
      nv_next.go(a, b, h)

# Equal words, characters and strings: a comparison that answers EQ means
# the two sides are the same.

def fin_eq.b(a: Bool, b: Bool, h: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case True{} True{}:
      {==}

def fin_eq.t(-ab: Bool, -bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) -> {Cmp.is_eq(t) == True{} : Bool}:
  match t:
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, false_ne_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, false_ne_true(h))

def fin_eq.h(ab: Bool, bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) -> {ab == bb : Bool}:
  match t:
    case LT{}:
      Empty.absurd({ab == bb : Bool}, false_ne_true(h))
    case EQ{}:
      fin_eq.b(ab, bb, h)
    case GT{}:
      Empty.absurd({ab == bb : Bool}, false_ne_true(h))

def wcon_eq(-p: Nat, -a: Bool, -b: Bool, -at: Word(p), -bt: Word(p), e1: {a == b : Bool}, e2: {at == bt : Word(p)})
  -> {WCon{a, at} == WCon{b, bt} : Word(1n+p)}:
  %e1 : {WCon{a, at} == WCon{_, bt} : Word(1n+p)}
  %e2 : {WCon{a, at} == WCon{a, _} : Word(1n+p)}
  {==}

def wcmp_eq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          wcon_eq(p, ab, bb, at, bt, fin_eq.h(ab, bb, Word.cmp(p, at, bt), h),
            wcmp_eq(p, at, bt, fin_eq.t(ab, bb, Word.cmp(p, at, bt), h)))

def u32_eq(x: U32, y: U32, h: {Cmp.is_eq(U32.cmp(x, y)) == True{} : Bool}) -> {x == y : U32}:
  match x y:
    case U32{+a} U32{+b}:
      %wcmp_eq(32n, a, b, h) : {U32{a} == U32{_} : U32}
      {==}

def char_eq(x: Char, y: Char, h: {Char.is_eq(x, y) == True{} : Bool}) -> {x == y : Char}:
  match x y:
    case Chr{+a} Chr{+b}:
      %u32_eq(a, b, h) : {Chr{a} == Chr{_} : Char}
      {==}

def scon_eq(-x: Char, -y: Char, -t1: String, -t2: String, e1: {x == y : Char}, e2: {t1 == t2 : String}) -> {SCon{x, t1} == SCon{y, t2} : String}:
  %e1 : {SCon{x, t1} == SCon{_, t2} : String}
  %e2 : {SCon{x, t1} == SCon{x, _} : String}
  {==}

def ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def succ_ne_zero(-p: Nat, e: {1n+p == 0n : Nat}) -> Empty:
  %e : ndisc(_)
  Unit{}

def eqn_le(a: Nat, b: Nat) -> {eqn(a, b) == Bool.and(le(a, b), le(b, a)) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      eqn_le(p, q)

def and_le_lt(a: Nat, b: Nat) -> {Bool.and(le(a, b), le(1n+b, a)) == False{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      and_le_lt(p, q)

def or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# x is c, or x+1 <= c < k, exactly when x <= c < k (for x < k).

def between_step(x: Nat, c: Nat, k: Nat, hk: {le(1n+x, k) == True{} : Bool})
  -> {Bool.or(eqn(x, c), Bool.and(le(1n+x, c), le(1n+c, k))) == Bool.and(le(x, c), le(1n+c, k)) : Bool}:
  match x c k:
    case 0n 0n k:
      %Equal.sym(Bool, le(1n, k), True{}, hk) : {True{} == Bool.and(True{}, _) : Bool}
      {==}
    case 0n 1n+q k:
      {==}
    case 1n+p 0n k:
      {==}
    case 1n+p 1n+q 0n:
      Empty.absurd({Bool.or(eqn(1n+p, 1n+q), Bool.and(le(1n+1n+p, 1n+q), le(1n+1n+q, 0n))) == Bool.and(le(1n+p, 1n+q), le(1n+1n+q, 0n)) : Bool}, false_ne_true(hk))
    case 1n+p 1n+q 1n+r:
      between_step(p, q, r, hk)

def sub_zero_le(a: Nat, b: Nat, e: {Nat.sub(a, b) == 0n : Nat}) -> {le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      Empty.absurd({le(1n+p, 0n) == True{} : Bool}, succ_ne_zero(p, e))
    case 1n+p 1n+q:
      sub_zero_le(p, q, e)

def sub_succ(a: Nat, b: Nat, +q: Nat, e: {Nat.sub(a, b) == 1n+q : Nat}) -> {Nat.add(1n+q, b) == a : Nat}:
  match a b:
    case 0n b:
      Empty.absurd({Nat.add(1n+q, b) == 0n : Nat}, succ_ne_zero(q, Equal.sym(Nat, 0n, 1n+q, e)))
    case 1n+p 0n:
      Equal.trans(Nat, 1n+Nat.add(q, 0n), 1n+q, 1n+p, succ_cong(Nat.add(q, 0n), q, plus_zero_r(q)), Equal.sym(Nat, 1n+p, 1n+q, e))
    case 1n+p 1n+ +r:
      Equal.trans(Nat, Nat.add(1n+q, 1n+r), 1n+Nat.add(1n+q, r), 1n+p, plus_succ_r(1n+q, r), succ_cong(Nat.add(1n+q, r), p, sub_succ(p, r, q, e)))

# memb(c, n, x): c is one of the n characters from x on.

def memb(+c: Char, n: Nat, +x: Char) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      Bool.or(Char.is_eq(x, c), memb(c, p, Chr{(Char.to_u32(x) + 1 : U32)}))

def ch_eqX(+x: Char, +c: Char, -X: Nat, ex: {nv(x) == X : Nat}) -> {Char.is_eq(x, c) == eqn(X, nv(c)) : Bool}:
  %ex : {Char.is_eq(x, c) == eqn(_, nv(c)) : Bool}
  ch_eq(x, c)

def le_tr(-a: Nat, -b: Nat, -k: Nat, e: {a == b : Nat}, h: {le(a, k) == True{} : Bool}) -> {le(b, k) == True{} : Bool}:
  %e : {le(_, k) == True{} : Bool}
  h

# Without wrapping past hi, the n characters from x on are those in [x, x+n).

def membL(n: Nat, +x: Char, +c: Char, +hi: Char, +X: Nat, +ex: {nv(x) == X : Nat}, +h: {le(Nat.add(n, X), 1n+nv(hi)) == True{} : Bool})
  -> {memb(c, n, x) == Bool.and(le(X, nv(c)), le(1n+nv(c), Nat.add(n, X))) : Bool}:
  match n:
    case 0n:
      Equal.sym(Bool, Bool.and(le(X, nv(c)), le(1n+nv(c), X)), False{}, and_le_lt(X, nv(c)))
    case 1n+p:
      match p:
        case 0n:
          %Equal.sym(Bool, Bool.or(Char.is_eq(x, c), False{}), Char.is_eq(x, c), or_false(Char.is_eq(x, c))) : {_ == Bool.and(le(X, nv(c)), le(nv(c), X)) : Bool}
          %Equal.sym(Bool, Char.is_eq(x, c), eqn(X, nv(c)), ch_eqX(x, c, X, ex)) : {_ == Bool.and(le(X, nv(c)), le(nv(c), X)) : Bool}
          eqn_le(X, nv(c))
        case 1n+ +q:
          %Equal.sym(Bool, memb(c, 1n+q, Chr{(Char.to_u32(x) + 1 : U32)}), Bool.and(le(1n+X, nv(c)), le(1n+nv(c), Nat.add(1n+q, 1n+X))),
            membL(1n+q, Chr{(Char.to_u32(x) + 1 : U32)}, c, hi, 1n+X,
              Equal.trans(Nat, nv(Chr{(Char.to_u32(x) + 1 : U32)}), 1n+nv(x), 1n+X,
                nv_next(x, hi, le_trans(1n+nv(x), 1n+Nat.add(q, nv(x)), nv(hi), le_add_l(q, nv(x)), le_tr(Nat.add(1n+1n+q, X), Nat.add(1n+1n+q, nv(x)), 1n+nv(hi),
                  Equal.cong(Nat, Nat, y => Nat.add(1n+1n+q, y), X, nv(x), Equal.sym(Nat, nv(x), X, ex)), h))),
                succ_cong(nv(x), X, ex)),
              le_tr(Nat.add(1n+1n+q, X), Nat.add(1n+q, 1n+X), 1n+nv(hi), Equal.sym(Nat, Nat.add(1n+q, 1n+X), 1n+Nat.add(1n+q, X), plus_succ_r(1n+q, X)), h)))
            : {Bool.or(Char.is_eq(x, c), _) == Bool.and(le(X, nv(c)), le(1n+nv(c), Nat.add(1n+1n+q, X))) : Bool}
          %Equal.sym(Bool, Char.is_eq(x, c), eqn(X, nv(c)), ch_eqX(x, c, X, ex)) : {Bool.or(_, Bool.and(le(1n+X, nv(c)), le(1n+nv(c), Nat.add(1n+q, 1n+X)))) == Bool.and(le(X, nv(c)), le(1n+nv(c), Nat.add(1n+1n+q, X))) : Bool}
          %Equal.sym(Nat, Nat.add(1n+q, 1n+X), 1n+Nat.add(1n+q, X), plus_succ_r(1n+q, X)) : {Bool.or(eqn(X, nv(c)), Bool.and(le(1n+X, nv(c)), le(1n+nv(c), _))) == Bool.and(le(X, nv(c)), le(1n+nv(c), Nat.add(1n+1n+q, X))) : Bool}
          between_step(X, nv(c), Nat.add(1n+1n+q, X), le_add_l(1n+q, X))

def range_empty.f(-a: Bool, -b: Bool, k: {a == False{} : Bool}) -> {False{} == Bool.and(a, b) : Bool}:
  %Equal.sym(Bool, a, False{}, k) : {False{} == Bool.and(_, b) : Bool}
  {==}

def range_empty.ff(-a: Bool, -b: Bool, k: {a == True{} : Bool}, k2: {b == False{} : Bool}) -> {False{} == Bool.and(a, b) : Bool}:
  %Equal.sym(Bool, a, True{}, k) : {False{} == Bool.and(_, b) : Bool}
  %Equal.sym(Bool, b, False{}, k2) : {False{} == Bool.and(True{}, _) : Bool}
  {==}

def range_empty(+l: Nat, +c: Nat, +h: Nat, +hl: {le(1n+h, l) == True{} : Bool}) -> {False{} == Bool.and(le(l, c), le(c, h)) : Bool}:
  bcase({False{} == Bool.and(le(l, c), le(c, h)) : Bool}, le(l, c),
    +k => bcase({False{} == Bool.and(le(l, c), le(c, h)) : Bool}, le(c, h),
      k2 => Empty.absurd({False{} == Bool.and(le(l, c), le(c, h)) : Bool},
        succ_le_absurd(h, le_trans(1n+h, l, h, hl, le_trans(l, c, h, k, k2)))),
      k2 => range_empty.ff(le(l, c), le(c, h), k, k2)),
    k => range_empty.f(le(l, c), le(c, h), k))

def rangeB.go(n: Nat, +lo: Char, +c: Char, +hi: Char, +e: {Nat.sub(1n+nv(hi), nv(lo)) == n : Nat})
  -> {memb(c, n, lo) == Bool.and(le(nv(lo), nv(c)), le(nv(c), nv(hi))) : Bool}:
  match n:
    case 0n:
      range_empty(nv(lo), nv(c), nv(hi), sub_zero_le(1n+nv(hi), nv(lo), e))
    case 1n+ +q:
      %sub_succ(1n+nv(hi), nv(lo), q, e) : {memb(c, 1n+q, lo) == Bool.and(le(nv(lo), nv(c)), le(1n+nv(c), _)) : Bool}
      membL(1n+q, lo, c, hi, nv(lo), {==}, le_tr(1n+nv(hi), Nat.add(1n+q, nv(lo)), 1n+nv(hi),
        Equal.sym(Nat, Nat.add(1n+q, nv(lo)), 1n+nv(hi), sub_succ(1n+nv(hi), nv(lo), q, e)), le_refl(1n+nv(hi))))

# The characters of a range are those between its ends.

def rangeB(+lo: Char, +hi: Char, +c: Char) -> {memb(c, rcount(lo, hi), lo) == inR(lo, hi, c) : Bool}:
  %Equal.sym(Bool, U32.is_le(Char.to_u32(lo), Char.to_u32(c)), le(nv(lo), nv(c)), ch_le(lo, c)) : {memb(c, rcount(lo, hi), lo) == Bool.and(_, U32.is_le(Char.to_u32(c), Char.to_u32(hi))) : Bool}
  %Equal.sym(Bool, U32.is_le(Char.to_u32(c), Char.to_u32(hi)), le(nv(c), nv(hi)), ch_le(c, hi)) : {memb(c, rcount(lo, hi), lo) == Bool.and(le(nv(lo), nv(c)), _) : Bool}
  rangeB.go(rcount(lo, hi), lo, c, hi, {==})

# Overview
# ========
#
# A JSON value is a Raw tree checked by wf: numbers and strings keep the text
# they were written with, so that dump can write them back as they were. load
# is a recursive descent parser (pv). The proofs show that it accepts exactly
# the texts the grammar matches, and what it builds from each shape.

# Logic
# =====

def sel(-A: Type, b: Bool, x: Unit -> A, y: Unit -> A) -> A:
  match b:
    case True{}:
      x(Unit{})
    case False{}:
      y(Unit{})

def IsTrue(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def istrue(-b: Bool, e: {b == True{} : Bool}) -> IsTrue(b):
  %Equal.sym(Bool, b, True{}, e) : IsTrue(_)
  Unit{}

def andT1(a: Bool, -b: Bool, h: IsTrue(Bool.and(a, b))) -> IsTrue(a):
  match a:
    case True{}:
      Unit{}
    case False{}:
      Empty.absurd(IsTrue(False{}), h)

def andT2(a: Bool, -b: Bool, h: IsTrue(Bool.and(a, b))) -> IsTrue(b):
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd(IsTrue(b), h)

# Characters
# ==========
#
# Each test is written the way the grammar's rule for one character unfolds.

def isws(+c: Char) -> Bool:
  Bool.or(Char.is_eq(Chr{32}, c), Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))))

def isdig(+c: Char) -> Bool:
  inR('0', '9', c)

def is19(+c: Char) -> Bool:
  inR('1', '9', c)

def isnum0(+c: Char) -> Bool:
  Bool.or(Char.is_eq('-', c), Bool.or(Char.is_eq('0', c), is19(c)))

def ise(+c: Char) -> Bool:
  Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{}))

def issign(+c: Char) -> Bool:
  Bool.or(Char.is_eq('-', c), Bool.or(Char.is_eq('+', c), False{}))

def isunesc(+c: Char) -> Bool:
  Bool.or(inR(Chr{32}, Chr{33}, c), Bool.or(inR(Chr{35}, Chr{91}, c), Bool.or(inR(Chr{93}, Chr{1114111}, c), False{})))

def issimple(+c: Char) -> Bool:
  Bool.or(Char.is_eq('"', c), Bool.or(Char.is_eq('\\', c), Bool.or(Char.is_eq('/', c), Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{}))))))))

def ishex(+c: Char) -> Bool:
  Bool.or(inR('0', '9', c), Bool.or(Bool.or(Char.is_eq('a', c), Bool.or(Char.is_eq('A', c), False{})), Bool.or(Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('B', c), False{})), Bool.or(Bool.or(Char.is_eq('c', c), Bool.or(Char.is_eq('C', c), False{})), Bool.or(Bool.or(Char.is_eq('d', c), Bool.or(Char.is_eq('D', c), False{})), Bool.or(Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{})), Bool.or(Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), False{})))))))

# Scanning
# ========

def skip_ws(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sel(String, isws(c), u => skip_ws(t), u => SCon{c, t})

# A scan answers the text it read and the rest.
type SP is Data:
  SP{a: String, t: String}

def spa(p: SP) -> String:
  match p:
    case SP{a, t}:
      a

def spt(p: SP) -> String:
  match p:
    case SP{a, t}:
      t

def prepS(+c: Char, +p: SP) -> SP:
  SP{SCon{c, spa(p)}, spt(p)}

def prepM(+c: Char, m: Maybe<&2, SP>) -> Maybe<&2, SP>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{prepS(c, p)}

def appM(a: String, m: Maybe<&2, SP>) -> Maybe<&2, SP>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      Some{SP{String.append(a, spa(p)), spt(p)}}

# Numbers: each scanner reads one part of `number`, longest first.

def digits(s: String) -> SP:
  match s:
    case SNil{}:
      SP{SNil{}, SNil{}}
    case SCon{+c, +t}:
      sel(SP, isdig(c), u => prepS(c, digits(t)), u => SP{SNil{}, SCon{c, t}})

def dig1(p: SP) -> Maybe<&2, SP>:
  match p:
    case SP{a, t}:
      match a:
        case SNil{}:
          None{}
        case SCon{x, y}:
          Some{SP{SCon{x, y}, t}}

def nsign(s: String) -> Maybe<&2, SP>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sel(Maybe<&2, SP>, issign(c), u => prepM(c, dig1(digits(t))), u => dig1(digits(SCon{c, t})))

def nexp(s: String) -> Maybe<&2, SP>:
  match s:
    case SNil{}:
      Some{SP{SNil{}, SNil{}}}
    case SCon{+c, +t}:
      sel(Maybe<&2, SP>, ise(c), u => prepM(c, nsign(t)), u => Some{SP{SNil{}, SCon{c, t}}})

def nfrac2(m: Maybe<&2, SP>) -> Maybe<&2, SP>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      appM(spa(p), nexp(spt(p)))

def nfrac(s: String) -> Maybe<&2, SP>:
  match s:
    case SNil{}:
      Some{SP{SNil{}, SNil{}}}
    case SCon{+c, +t}:
      sel(Maybe<&2, SP>, Char.is_eq('.', c), u => prepM(c, nfrac2(dig1(digits(t)))), u => nexp(SCon{c, t}))

def nint2(+p: SP) -> Maybe<&2, SP>:
  appM(spa(p), nfrac(spt(p)))

def nint(s: String) -> Maybe<&2, SP>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sel(Maybe<&2, SP>, Char.is_eq('0', c), u => prepM(c, nfrac(t)), u => sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}))

def num_scan(s: String) -> Maybe<&2, SP>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sel(Maybe<&2, SP>, Char.is_eq('-', c), u => prepM(c, nint(t)), u => nint(SCon{c, t}))

# Strings: str_scan reads up to the closing quote. SN reads a char, SE what
# follows a backslash, SH{n} the last n+1 digits of a \uXXXX.

type SS is Data:
  SN{}
  SE{}
  SH{n: Nat}

def hnext(n: Nat) -> SS:
  match n:
    case 0n:
      SN{}
    case 1n+p:
      SH{p}

def str_scan(s: String, st: SS) -> Maybe<&2, SP>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      match st:
        case SN{}:
          sel(Maybe<&2, SP>, Char.is_eq('"', c), u => Some{SP{SNil{}, t}}, u => sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})))
        case SE{}:
          sel(Maybe<&2, SP>, issimple(c), u => prepM(c, str_scan(t, SN{})), u => sel(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}))
        case SH{n}:
          sel(Maybe<&2, SP>, ishex(c), u => prepM(c, str_scan(t, hnext(n))), u => None{})

def okend(m: Maybe<&2, SP>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      String.is_empty(spt(p))

def numok(s: String) -> Bool:
  okend(num_scan(s))

def strok(s: String) -> Bool:
  okend(str_scan(String.append(s, "\""), SN{}))

# Values
# ======

type Raw is Data:
  RNull{}
  RBool{b: Bool}
  RNum{s: String}
  RStr{s: String}
  RArr{xs: List<&2, Raw>}
  RObj{ms: List<&2, RMem>}

type RMem is Data:
  RMem{k: String, v: Raw}

# A number holds its text, a string the text between its quotes.
def wf(r: Raw) -> Bool:
  match r:
    case RNull{}:
      True{}
    case RBool{b}:
      True{}
    case RNum{s}:
      numok(s)
    case RStr{s}:
      strok(s)
    case RArr{xs}:
      match xs:
        case []:
          True{}
        case x <> rest:
          Bool.and(wf(x), wf(RArr{rest}))
    case RObj{ms}:
      match ms:
        case []:
          True{}
        case RMem{k, v} <> rest:
          Bool.and(strok(k), Bool.and(wf(v), wf(RObj{rest})))

type Js is Data:
  J{r: Raw, h: IsTrue(wf(r))}

# Decoding
# ========
#
# dec reads a string's text. DE follows a backslash, DU{acc} a \u with the
# digits acc so far. p holds a high surrogate until we know whether a low
# one follows it.

type DS is Data:
  DN{}
  DE{}
  DU{acc: String}

def emit(p: Maybe<&2, U32>, s: String) -> String:
  match p:
    case None{}:
      s
    case Some{h}:
      SCon{Chr{h}, s}

def hi(+v: U32) -> Bool:
  (v >= 55296 : U32) && (v <= 56319 : U32)

def lo(+v: U32) -> Bool:
  (v >= 56320 : U32) && (v <= 57343 : U32)

def pair(+h: U32, +l: U32) -> U32:
  (65536 + (h - 55296) * 1024 + (l - 56320) : U32)

# A \uXXXX of value v, after the pending surrogate p: what to write (pre),
# and what is pending afterwards (np).
def fpre(+v: U32) -> String:
  sel(String, hi(v), u => SNil{}, u => SCon{Chr{v}, SNil{}})

def fnp(+v: U32) -> Maybe<&2, U32>:
  sel(Maybe<&2, U32>, hi(v), u => Some{v}, u => None{})

def pre(+v: U32, p: Maybe<&2, U32>) -> String:
  match p:
    case None{}:
      fpre(v)
    case Some{+h}:
      sel(String, lo(v), u => SCon{Chr{pair(h, v)}, SNil{}}, u => SCon{Chr{h}, fpre(v)})

def np(+v: U32, p: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match p:
    case None{}:
      fnp(v)
    case Some{h}:
      sel(Maybe<&2, U32>, lo(v), u => None{}, u => fnp(v))

def esc(c: Char) -> Char:
  match c:
    case 'b':
      Chr{8}
    case 'f':
      Chr{12}
    case 'n':
      Chr{10}
    case 'r':
      Chr{13}
    case 't':
      Chr{9}
    case x:
      x

def dec(s: String, st: DS, +p: Maybe<&2, U32>) -> String:
  match s:
    case SNil{}:
      match st:
        case DN{}:
          emit(p, SNil{})
        case DE{}:
          emit(p, "\\")
        case DU{acc}:
          emit(p, String.append("\\u", acc))
    case SCon{+c, +t}:
      match st:
        case DN{}:
          sel(String, Char.is_eq(c, '\\'), u => dec(t, DE{}, p), u => emit(p, SCon{c, dec(t, DN{}, None{})}))
        case DE{}:
          sel(String, issimple(c), u => emit(p, SCon{esc(c), dec(t, DN{}, None{})}), u => sel(String, Char.is_eq(c, 'u'), u => dec(t, DU{SNil{}}, p), u => emit(p, SCon{'\\', SCon{c, dec(t, DN{}, None{})}})))
        case DU{acc}:
          match acc:
            case SCon{+a, SCon{+b, SCon{+d, SNil{}}}}:
              sel(String, Extra.is_hex(SCon{a, SCon{b, SCon{d, SCon{c, SNil{}}}}}), u => String.append(pre(EP.hexv(SCon{a, SCon{b, SCon{d, SCon{c, SNil{}}}}}, 0), p), dec(t, DN{}, np(EP.hexv(SCon{a, SCon{b, SCon{d, SCon{c, SNil{}}}}}, 0), p))), u => emit(p, SCon{'\\', SCon{'u', String.append(SCon{a, SCon{b, SCon{d, SCon{c, SNil{}}}}}, dec(t, DN{}, None{}))}}))
            case +acc:
              dec(t, DU{String.append(acc, SCon{c, SNil{}})}, p)

# Parsing
# =======

type PR is Data:
  PR{r: Raw, t: String}

def prr(p: PR) -> Raw:
  match p:
    case PR{r, t}:
      r

def prt(p: PR) -> String:
  match p:
    case PR{r, t}:
      t

def lit(+p: String, +t: String, r: Raw) -> Maybe<&2, PR>:
  sel(Maybe<&2, PR>, String.starts_with(t, p), u => Some{PR{r, String.drop(t, String.length(p))}}, u => None{})

def numv(m: Maybe<&2, SP>) -> Maybe<&2, PR>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case SP{a, t}:
          Some{PR{RNum{a}, t}}

def strv(m: Maybe<&2, SP>) -> Maybe<&2, PR>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case SP{a, t}:
          Some{PR{RStr{a}, t}}

# brk: after an opening bracket, either its closing one or the elements.
def brk(+c: Char, u: String, kc: String -> Maybe<&2, PR>, ko: String -> Maybe<&2, PR>) -> Maybe<&2, PR>:
  match u:
    case SNil{}:
      ko(SNil{})
    case SCon{+x, +w}:
      sel(Maybe<&2, PR>, Char.is_eq(c, x), z => kc(w), z => ko(SCon{x, w}))

# sep: after an element, either the closing bracket or a comma.
def sep(+c: Char, u: String, kc: String -> Maybe<&2, PR>, kn: String -> Maybe<&2, PR>) -> Maybe<&2, PR>:
  match u:
    case SNil{}:
      None{}
    case SCon{+x, +w}:
      sel(Maybe<&2, PR>, Char.is_eq(c, x), z => kc(w), z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => kn(w), z => None{}))

def colon(u: String, k: String -> Maybe<&2, PR>) -> Maybe<&2, PR>:
  match u:
    case SNil{}:
      None{}
    case SCon{+x, +w}:
      sel(Maybe<&2, PR>, Char.is_eq(':', x), z => k(w), z => None{})

def acons1(x: Raw, r: Raw) -> Raw:
  match r:
    case RArr{xs}:
      RArr{x <> xs}
    case _:
      RArr{[x]}

def acons(x: Raw, m: Maybe<&2, PR>) -> Maybe<&2, PR>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      Some{PR{acons1(x, prr(p)), prt(p)}}

def ocons1(k: String, v: Raw, r: Raw) -> Raw:
  match r:
    case RObj{ms}:
      RObj{RMem{k, v} <> ms}
    case _:
      RObj{[RMem{k, v}]}

def ocons(k: String, v: Raw, m: Maybe<&2, PR>) -> Maybe<&2, PR>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      Some{PR{ocons1(k, v, prr(p)), prt(p)}}

# The modes: MV reads a value; MA what follows an array's element; MM an
# object's member, after its opening quote's position; MO what follows a member.
type Md is Data:
  MV{}
  MA{}
  MM{}
  MO{}

# Every call reads at least one character before calling itself again, so a
# fuel above the input's length is enough.
def pv(f: Nat, m: Md, s: String) -> Maybe<&2, PR>:
  match f:
    case 0n:
      None{}
    case 1n+ +g:
      match m:
        case MV{}:
          match s:
            case SNil{}:
              None{}
            case SCon{+c, +t}:
              sel(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u =>
              sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u =>
              sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u =>
              sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u =>
              sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u =>
              sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u =>
              sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u =>
              None{})))))))
        case MA{}:
          sep(']', s, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))))
        case MM{}:
          match s:
            case SNil{}:
              None{}
            case SCon{+c, +t}:
              sel(Maybe<&2, PR>, Char.is_eq('"', c), u => Maybe.bind(&2, SP, PR, str_scan(t, SN{}), +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))))), u => None{})
        case MO{}:
          sep('}', s, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, skip_ws(w)))

def pvc(m: Md, +s: String) -> Maybe<&2, PR>:
  pv(1n+String.length(s), m, s)

# Loading and dumping
# ===================

def mk(+r: Raw, b: Bool, e: {wf(r) == b : Bool}) -> Maybe<Js>:
  match b:
    case True{}:
      Some{J{r, istrue(wf(r), e)}}
    case False{}:
      None{}

def fin2(+r: Raw, b: Bool) -> Maybe<Js>:
  match b:
    case True{}:
      mk(r, wf(r), {==})
    case False{}:
      None{}

def fin(m: Maybe<&2, PR>) -> Maybe<Js>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      fin2(prr(p), String.is_empty(skip_ws(prt(p))))

type PM is Data:
  PTop{}
  PTail{}

def wrapT(m: PM, o: String, a: String, b: String) -> String:
  match m:
    case PTop{}:
      String.append(o, String.append(a, b))
    case PTail{}:
      String.append(",", String.append(a, b))

def endT(m: PM, o: String, c: String) -> String:
  match m:
    case PTop{}:
      String.append(o, c)
    case PTail{}:
      c

# pr(r, PTop) writes r; pr(RArr{xs}, PTail) writes what follows an element.
def pr(r: Raw, m: PM) -> String:
  match r:
    case RNull{}:
      "null"
    case RBool{b}:
      Bool.pick(String, b, "true", "false")
    case RNum{s}:
      s
    case RStr{s}:
      String.append("\"", String.append(s, "\""))
    case RArr{xs}:
      match xs:
        case []:
          endT(m, "[", "]")
        case x <> rest:
          wrapT(m, "[", pr(x, PTop{}), pr(RArr{rest}, PTail{}))
    case RObj{ms}:
      match ms:
        case []:
          endT(m, "{", "}")
        case RMem{k, v} <> rest:
          wrapT(m, "{", String.append("\"", String.append(k, String.append("\":", pr(v, PTop{})))), pr(RObj{rest}, PTail{}))

# Projections
# ===========

def wrapL(xs: List<&2, Raw>, +h: IsTrue(wf(RArr{xs}))) -> List<&2, Js>:
  match xs:
    case []:
      []
    case +x <> +rest:
      J{x, andT1(wf(x), wf(RArr{rest}), h)} <> wrapL(rest, andT2(wf(x), wf(RArr{rest}), h))

def wrapO(ms: List<&2, RMem>, +h: IsTrue(wf(RObj{ms}))) -> List<&2, Sigma<&2, &2, String, _ => Js>>:
  match ms:
    case []:
      []
    case RMem{+k, +v} <> +rest:
      (dec(k, DN{}, None{}), J{v, andT1(wf(v), wf(RObj{rest}), andT2(strok(k), Bool.and(wf(v), wf(RObj{rest})), h))}) <> wrapO(rest, andT2(wf(v), wf(RObj{rest}), andT2(strok(k), Bool.and(wf(v), wf(RObj{rest})), h)))

def nullP(r: Raw) -> Maybe<Unit>:
  match r:
    case RNull{}:
      Some{Unit{}}
    case _:
      None{}

def boolP(r: Raw) -> Maybe<Bool>:
  match r:
    case RBool{b}:
      Some{b}
    case _:
      None{}

def numP(r: Raw) -> Maybe<String>:
  match r:
    case RNum{s}:
      Some{s}
    case _:
      None{}

def strP(r: Raw) -> Maybe<String>:
  match r:
    case RStr{s}:
      Some{dec(s, DN{}, None{})}
    case _:
      None{}

def arrP(r: Raw, h: IsTrue(wf(r))) -> Maybe<List<&2, Js>>:
  match r:
    case RArr{xs}:
      Some{wrapL(xs, h)}
    case _:
      None{}

def objP(r: Raw, h: IsTrue(wf(r))) -> Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>:
  match r:
    case RObj{ms}:
      Some{wrapO(ms, h)}
    case _:
      None{}

def lk(ms: List<&2, Sigma<&2, &2, String, _ => Js>>, +key: String) -> Maybe<Js>:
  match ms:
    case []:
      None{}
    case (k, v) <> rest:
      sel(Maybe<Js>, String.eq(k, key), u => Some{v}, u => lk(rest, key))

def fieldM(m: Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, key: String) -> Maybe<Js>:
  match m:
    case None{}:
      None{}
    case Some{ms}:
      lk(ms, key)

def Laws.grammar():
  [
    ("JSON-text", ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")])),
    ("begin-array", ABNF.seq([ABNF.ref("ws"), ABNF.char('['), ABNF.ref("ws")])),
    ("begin-object", ABNF.seq([ABNF.ref("ws"), ABNF.char('{'), ABNF.ref("ws")])),
    ("end-array", ABNF.seq([ABNF.ref("ws"), ABNF.char(']'), ABNF.ref("ws")])),
    ("end-object", ABNF.seq([ABNF.ref("ws"), ABNF.char('}'), ABNF.ref("ws")])),
    ("name-separator", ABNF.seq([ABNF.ref("ws"), ABNF.char(':'), ABNF.ref("ws")])),
    ("value-separator", ABNF.seq([ABNF.ref("ws"), ABNF.char(','), ABNF.ref("ws")])),
    ("ws", ABNF.rep.any(ABNF.alt([ABNF.char(Chr{32}), ABNF.char(Chr{9}), ABNF.char(Chr{10}), ABNF.char(Chr{13})]))),
    ("value", ABNF.alt([ABNF.ref("false"), ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")])),
    ("false", ABNF.string.case_sensitive("false")),
    ("null", ABNF.string.case_sensitive("null")),
    ("true", ABNF.string.case_sensitive("true")),
    ("object", ABNF.seq([ABNF.ref("begin-object"), ABNF.opt(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(ABNF.seq([ABNF.ref("value-separator"), ABNF.ref("member")]))])), ABNF.ref("end-object")])),
    ("member", ABNF.seq([ABNF.ref("string"), ABNF.ref("name-separator"), ABNF.ref("value")])),
    ("array", ABNF.seq([ABNF.ref("begin-array"), ABNF.opt(ABNF.seq([ABNF.ref("value"), ABNF.rep.any(ABNF.seq([ABNF.ref("value-separator"), ABNF.ref("value")]))])), ABNF.ref("end-array")])),
    ("number", ABNF.seq([ABNF.opt(ABNF.ref("minus")), ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp"))])),
    ("decimal-point", ABNF.char('.')),
    ("digit1-9", ABNF.range('1', '9')),
    ("e", ABNF.alt([ABNF.char('e'), ABNF.char('E')])),
    ("exp", ABNF.seq([ABNF.ref("e"), ABNF.opt(ABNF.alt([ABNF.ref("minus"), ABNF.ref("plus")])), ABNF.rep.at_least(1n, ABNF.core.digit)])),
    ("frac", ABNF.seq([ABNF.ref("decimal-point"), ABNF.rep.at_least(1n, ABNF.core.digit)])),
    ("int", ABNF.alt([ABNF.ref("zero"), ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(ABNF.core.digit)])])),
    ("minus", ABNF.char('-')),
    ("plus", ABNF.char('+')),
    ("zero", ABNF.char('0')),
    ("string", ABNF.seq([ABNF.ref("quotation-mark"), ABNF.rep.any(ABNF.ref("char")), ABNF.ref("quotation-mark")])),
    ("char", ABNF.alt([ABNF.ref("unescaped"), ABNF.seq([ABNF.ref("escape"), ABNF.alt([ABNF.char('"'), ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), ABNF.seq([ABNF.char('u'), ABNF.rep.exactly(4n, ABNF.core.hexdig)])])])])),
    ("escape", ABNF.char('\\')),
    ("quotation-mark", ABNF.char('"')),
    ("unescaped", ABNF.alt([ABNF.range(Chr{32}, Chr{33}), ABNF.range(Chr{35}, Chr{91}), ABNF.range(Chr{93}, Chr{1114111})]))
  ]

def Laws.grammar.ok(name, s):
  {==}

def Laws.JSON():
  Js

def Laws.null(j):
  match j:
    case J{r, h}:
      nullP(r)

def Laws.bool(j):
  match j:
    case J{r, h}:
      boolP(r)

def Laws.number(j):
  match j:
    case J{r, h}:
      numP(r)

def Laws.string(j):
  match j:
    case J{r, h}:
      strP(r)

def Laws.array(j):
  match j:
    case J{r, h}:
      arrP(r, h)

def Laws.object(j):
  match j:
    case J{r, h}:
      objP(r, h)

def Laws.field(j, key):
  fieldM(Laws.object(j), key)

def Laws.lookup(ms, key):
  lk(ms, key)

def Laws.load(s):
  fin(pvc(MV{}, skip_ws(s)))

def Laws.dump(j):
  match j:
    case J{r, h}:
      pr(r, PTop{})

def Laws.decode(x):
  dec(x, DN{}, None{})

# Proofs: logic
# =============

def beq(a: Bool, b: Bool, f: {a == True{} : Bool} -> {b == True{} : Bool}, g: {b == True{} : Bool} -> {a == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(f({==})))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(g({==})))
    case False{} False{}:
      {==}

def or_cong(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool, +e1: {a == a2 : Bool}, +e2: {b == b2 : Bool}) -> {Bool.or(a, b) == Bool.or(a2, b2) : Bool}:
  %e1 : {Bool.or(a, b) == Bool.or(_, b2) : Bool}
  %e2 : {Bool.or(a, b) == Bool.or(a, _) : Bool}
  {==}

def mdisc(a, -A: Kind(a), m: Maybe<a, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_ne_some(a, -A: Kind(a), -x: A, +e: {None{} == Some{x} : Maybe<a, A>}) -> Empty:
  %e : mdisc(a, A, _)
  Unit{}

def mget(a, -A: Kind(a), m: Maybe<a, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def some_inj(a, -A: Kind(a), -x: A, -y: A, +e: {Some{x} == Some{y} : Maybe<a, A>}) -> {x == y : A}:
  %e : {mget(a, A, Some{x}, x) == mget(a, A, _, x) : A}
  {==}

def irr(b: Bool, p: IsTrue(b), q: IsTrue(b)) -> {p == q : IsTrue(b)}:
  match b:
    case True{}:
      match p q:
        case Unit{} Unit{}:
          {==}
    case False{}:
      match p:

def j_irr(+r: Raw, +p: IsTrue(wf(r)), +q: IsTrue(wf(r))) -> {J{r, p} == J{r, q} : Js}:
  %irr(wf(r), p, q) : {J{r, p} == J{r, _} : Js}
  {==}

def ofTrue(b: Bool, h: IsTrue(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match h:

def word_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_cmp_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_cmp_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}

def str_refl(a: String) -> {String.eq(a, a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{U32{+w}}, +t}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_refl(32n, w)) : {Cmp.is_eq(String.order.go(t, t, _)) == True{} : Bool}
      str_refl(t)

def char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{U32{+w}}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# Strings
# =======

def app3(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  app_assoc(a, b, c)

def str_tl(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      t

def str_hd(s: String, d: Char) -> Char:
  match s:
    case SNil{}:
      d
    case SCon{c, t}:
      c

def scon_tl(-c: Char, -d: Char, -a: String, -b: String, +e: {SCon{c, a} == SCon{d, b} : String}) -> {a == b : String}:
  Equal.cong(String, String, str_tl, SCon{c, a}, SCon{d, b}, e)

def scon_hd(+c: Char, -d: Char, -a: String, -b: String, +e: {SCon{c, a} == SCon{d, b} : String}) -> {c == d : Char}:
  %e : {str_hd(SCon{c, a}, c) == str_hd(_, c) : Char}
  {==}

def sdisc(s: String) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{c, t}:
      Empty

def nil_ne_con(-c: Char, -t: String, +e: {SNil{} == SCon{c, t} : String}) -> Empty:
  %e : sdisc(_)
  Unit{}

def snoc_ne(t: String, -c: Char, +e: {String.append(t, SCon{c, SNil{}}) == SNil{} : String}) -> Empty:
  match t:
    case SNil{}:
      nil_ne_con(c, SNil{}, Equal.sym(String, SCon{c, SNil{}}, SNil{}, e))
    case SCon{x, r}:
      nil_ne_con(x, String.append(r, SCon{c, SNil{}}), Equal.sym(String, SCon{x, String.append(r, SCon{c, SNil{}})}, SNil{}, e))

# x ++ [c] == y ++ [c] gives x == y.
def snoc_cancel(x: String, y: String, -c: Char, +e: {String.append(x, SCon{c, SNil{}}) == String.append(y, SCon{c, SNil{}}) : String}) -> {x == y : String}:
  match x y:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{d, t}:
      Empty.absurd({SNil{} == SCon{d, t} : String}, snoc_ne(t, c, Equal.sym(String, SNil{}, String.append(t, SCon{c, SNil{}}), scon_tl(c, d, SNil{}, String.append(t, SCon{c, SNil{}}), e))))
    case SCon{d, t} SNil{}:
      Empty.absurd({SCon{d, t} == SNil{} : String}, snoc_ne(t, c, scon_tl(d, c, String.append(t, SCon{c, SNil{}}), SNil{}, e)))
    case SCon{+d, +t} SCon{+d2, +t2}:
      scon_eq(d, d2, t, t2, scon_hd(d, d2, String.append(t, SCon{c, SNil{}}), String.append(t2, SCon{c, SNil{}}), e), snoc_cancel(t, t2, c, scon_tl(d, d2, String.append(t, SCon{c, SNil{}}), String.append(t2, SCon{c, SNil{}}), e)))

# Grammar
# =======

def BK() -> ABNF.Book:
  ABNF.full(Laws.grammar)

def LB(d: Nat) -> ABNF.Book:
  ABNF.limit(d, Laws.grammar)

def WSC() -> ABNF.Rule:
  ABNF.alt([ABNF.char(Chr{32}), ABNF.char(Chr{9}), ABNF.char(Chr{10}), ABNF.char(Chr{13})])

def TOK(c: Char) -> ABNF.Rule:
  ABNF.seq([ABNF.ref("ws"), ABNF.char(c), ABNF.ref("ws")])

def DIG() -> ABNF.Rule:
  ABNF.core.digit

def AL1() -> ABNF.Rule:
  ABNF.rep.at_least(1n, ABNF.core.digit)

def SIGN() -> ABNF.Rule:
  ABNF.alt([ABNF.ref("minus"), ABNF.ref("plus")])

def B_value() -> ABNF.Rule:
  ABNF.alt([ABNF.ref("false"), ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")])

def ITEM() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("value-separator"), ABNF.ref("value")])

def MITEM() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("value-separator"), ABNF.ref("member")])

def ELEMS() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("value"), ABNF.rep.any(ITEM)])

def MEMBS() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM)])

def B_array() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("begin-array"), ABNF.opt(ELEMS), ABNF.ref("end-array")])

def B_object() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("begin-object"), ABNF.opt(MEMBS), ABNF.ref("end-object")])

def B_member() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("string"), ABNF.ref("name-separator"), ABNF.ref("value")])

def B_number() -> ABNF.Rule:
  ABNF.seq([ABNF.opt(ABNF.ref("minus")), ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp"))])

def B_int() -> ABNF.Rule:
  ABNF.alt([ABNF.ref("zero"), ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(ABNF.core.digit)])])

def B_frac() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("decimal-point"), ABNF.rep.at_least(1n, ABNF.core.digit)])

def B_exp() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("e"), ABNF.opt(SIGN), ABNF.rep.at_least(1n, ABNF.core.digit)])

def B_string() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("quotation-mark"), ABNF.rep.any(ABNF.ref("char")), ABNF.ref("quotation-mark")])

def HEX() -> ABNF.Rule:
  ABNF.core.hexdig

def UESC() -> ABNF.Rule:
  ABNF.seq([ABNF.char('u'), ABNF.rep.exactly(4n, ABNF.core.hexdig)])

def ESCT() -> ABNF.Rule:
  ABNF.alt([ABNF.char('"'), ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC])

def B_char() -> ABNF.Rule:
  ABNF.alt([ABNF.ref("unescaped"), ABNF.seq([ABNF.ref("escape"), ESCT])])

def B_unesc() -> ABNF.Rule:
  ABNF.alt([ABNF.range(Chr{32}, Chr{33}), ABNF.range(Chr{35}, Chr{91}), ABNF.range(Chr{93}, Chr{1114111})])

def CHARS() -> ABNF.Rule:
  ABNF.rep.any(ABNF.ref("char"))

# Generic lemmas
# ==============

def alt2(k: ABNF.Book, r: ABNF.Rule, rs: List<ABNF.Rule>, s: String, -x: Bool, -y: Bool, +e1: {ABNF.check(k, r, s) == x : Bool}, +e2: {ABNF.check(k, ABNF.alt(rs), s) == y : Bool})
  -> {ABNF.check(k, ABNF.alt(r <> rs), s) == Bool.or(x, y) : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.alt(r <> rs), s), Bool.or(ABNF.check(k, r, s), ABNF.check(k, ABNF.alt(rs), s)), Bool.or(x, y),
    ABNF.alt.con(k, r, rs, s), or_cong(ABNF.check(k, r, s), x, ABNF.check(k, ABNF.alt(rs), s), y, e1, e2))

def altS(+k: ABNF.Book, +r: ABNF.Rule, +s: String) -> {ABNF.check(k, ABNF.alt([r]), s) == ABNF.check(k, r, s) : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.alt([r]), s), Bool.or(ABNF.check(k, r, s), False{}), ABNF.check(k, r, s),
    alt2(k, r, [], s, ABNF.check(k, r, s), False{}, {==}, ABNF.alt.nil(k, s)), or_false(ABNF.check(k, r, s)))

def chk1(+k: ABNF.Book, n: Nat, +x: Char, +c: Char) -> {ABNF.check(k, ABNF.alt(ABNF.chars(n, x)), SCon{c, SNil{}}) == memb(c, n, x) : Bool}:
  match n:
    case 0n:
      %Equal.sym(List<ABNF.Rule>, ABNF.chars(0n, x), [], ABNF.chars.nil(x)) : {ABNF.check(k, ABNF.alt(_), SCon{c, SNil{}}) == False{} : Bool}
      ABNF.alt.nil(k, SCon{c, SNil{}})
    case 1n+ +p:
      %Equal.sym(List<ABNF.Rule>, ABNF.chars(1n+p, x), ABNF.char(x) <> ABNF.chars(p, Chr{(Char.to_u32(x) + 1 : U32)}), ABNF.chars.con(p, x)) : {ABNF.check(k, ABNF.alt(_), SCon{c, SNil{}}) == memb(c, 1n+p, x) : Bool}
      alt2(k, ABNF.char(x), ABNF.chars(p, Chr{(Char.to_u32(x) + 1 : U32)}), SCon{c, SNil{}}, Char.is_eq(x, c), memb(c, p, Chr{(Char.to_u32(x) + 1 : U32)}), ABNF.char.one(k, x, c), chk1(k, p, Chr{(Char.to_u32(x) + 1 : U32)}, c))

def chk0(+k: ABNF.Book, n: Nat, +x: Char) -> {ABNF.check(k, ABNF.alt(ABNF.chars(n, x)), SNil{}) == False{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(List<ABNF.Rule>, ABNF.chars(0n, x), [], ABNF.chars.nil(x)) : {ABNF.check(k, ABNF.alt(_), SNil{}) == False{} : Bool}
      ABNF.alt.nil(k, SNil{})
    case 1n+ +p:
      %Equal.sym(List<ABNF.Rule>, ABNF.chars(1n+p, x), ABNF.char(x) <> ABNF.chars(p, Chr{(Char.to_u32(x) + 1 : U32)}), ABNF.chars.con(p, x)) : {ABNF.check(k, ABNF.alt(_), SNil{}) == False{} : Bool}
      alt2(k, ABNF.char(x), ABNF.chars(p, Chr{(Char.to_u32(x) + 1 : U32)}), SNil{}, False{}, False{}, ABNF.char.nil(k, x), chk0(k, p, Chr{(Char.to_u32(x) + 1 : U32)}))

def chk2(+k: ABNF.Book, n: Nat, +x: Char, +a: Char, +b: Char, +t: String) -> {ABNF.check(k, ABNF.alt(ABNF.chars(n, x)), SCon{a, SCon{b, t}}) == False{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(List<ABNF.Rule>, ABNF.chars(0n, x), [], ABNF.chars.nil(x)) : {ABNF.check(k, ABNF.alt(_), SCon{a, SCon{b, t}}) == False{} : Bool}
      ABNF.alt.nil(k, SCon{a, SCon{b, t}})
    case 1n+ +p:
      %Equal.sym(List<ABNF.Rule>, ABNF.chars(1n+p, x), ABNF.char(x) <> ABNF.chars(p, Chr{(Char.to_u32(x) + 1 : U32)}), ABNF.chars.con(p, x)) : {ABNF.check(k, ABNF.alt(_), SCon{a, SCon{b, t}}) == False{} : Bool}
      alt2(k, ABNF.char(x), ABNF.chars(p, Chr{(Char.to_u32(x) + 1 : U32)}), SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(k, x, a, b, t), chk2(k, p, Chr{(Char.to_u32(x) + 1 : U32)}, a, b, t))

# A range matches one character between its ends.
def rg1(+k: ABNF.Book, +lo: Char, +hi: Char, +c: Char) -> {ABNF.check(k, ABNF.range(lo, hi), SCon{c, SNil{}}) == inR(lo, hi, c) : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.range(lo, hi), SCon{c, SNil{}}), ABNF.check(k, ABNF.alt(ABNF.chars(Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo))), lo)), SCon{c, SNil{}}), inR(lo, hi, c), ABNF.range.ok(k, lo, hi, SCon{c, SNil{}}),
    Equal.trans(Bool, ABNF.check(k, ABNF.alt(ABNF.chars(Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo))), lo)), SCon{c, SNil{}}), memb(c, Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo))), lo), inR(lo, hi, c), chk1(k, Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo))), lo, c), rangeB(lo, hi, c)))

def rg0(+k: ABNF.Book, +lo: Char, +hi: Char) -> {ABNF.check(k, ABNF.range(lo, hi), SNil{}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.range(lo, hi), SNil{}), ABNF.check(k, ABNF.alt(ABNF.chars(Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo))), lo)), SNil{}), False{}, ABNF.range.ok(k, lo, hi, SNil{}), chk0(k, Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo))), lo))

def rg2(+k: ABNF.Book, +lo: Char, +hi: Char, +a: Char, +b: Char, +t: String) -> {ABNF.check(k, ABNF.range(lo, hi), SCon{a, SCon{b, t}}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.range(lo, hi), SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.alt(ABNF.chars(Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo))), lo)), SCon{a, SCon{b, t}}), False{}, ABNF.range.ok(k, lo, hi, SCon{a, SCon{b, t}}), chk2(k, Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo))), lo, a, b, t))

# core.digit matches what the range 0-9 matches.
def cd1(+k: ABNF.Book, +c: Char) -> {ABNF.check(k, DIG, SCon{c, SNil{}}) == inR('0', '9', c) : Bool}:
  Equal.trans(Bool, ABNF.check(k, DIG, SCon{c, SNil{}}), ABNF.check(k, ABNF.range('0', '9'), SCon{c, SNil{}}), inR('0', '9', c), ABNF.core.digit.ok(k, SCon{c, SNil{}}), rg1(k, '0', '9', c))

def cd0(+k: ABNF.Book) -> {ABNF.check(k, DIG, SNil{}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(k, DIG, SNil{}), ABNF.check(k, ABNF.range('0', '9'), SNil{}), False{}, ABNF.core.digit.ok(k, SNil{}), rg0(k, '0', '9'))

def cd2(+k: ABNF.Book, +a: Char, +b: Char, +t: String) -> {ABNF.check(k, DIG, SCon{a, SCon{b, t}}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(k, DIG, SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.range('0', '9'), SCon{a, SCon{b, t}}), False{}, ABNF.core.digit.ok(k, SCon{a, SCon{b, t}}), rg2(k, '0', '9', a, b, t))

# A rule that matches only single characters.
def one(-C: Type, +k: ABNF.Book, +r: ABNF.Rule, s: String, +h: {ABNF.check(k, r, s) == True{} : Bool},
  z: {ABNF.check(k, r, SNil{}) == False{} : Bool},
  m: @a: Char -> @b: Char -> @t: String -> {ABNF.check(k, r, SCon{a, SCon{b, t}}) == False{} : Bool},
  f: @c: Char -> {SCon{c, SNil{}} == s : String} -> {ABNF.check(k, r, SCon{c, SNil{}}) == True{} : Bool} -> C) -> C:
  match s:
    case SNil{}:
      Empty.absurd(C, contra(ABNF.check(k, r, SNil{}), h, z))
    case SCon{c, SNil{}}:
      f(c, {==}, h)
    case SCon{a, SCon{b, t}}:
      Empty.absurd(C, contra(ABNF.check(k, r, SCon{a, SCon{b, t}}), h, m(a, b, t)))

def emptyE(+k: ABNF.Book, s: String, +h: {ABNF.check(k, ABNF.empty, s) == True{} : Bool}) -> {s == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{a, t}:
      Empty.absurd({SCon{a, t} == SNil{} : String}, contra(ABNF.check(k, ABNF.empty, SCon{a, t}), h, ABNF.empty.con(k, a, t)))

def seqE.go(-C: Type, -k: ABNF.Book, -r: ABNF.Rule, -rs: List<ABNF.Rule>, -s: String,
  p: &s1: String -> &s2: String -> {String.append(s1, s2) == s : String} & {ABNF.check(k, r, s1) == True{} : Bool} & {ABNF.check(k, ABNF.seq(rs), s2) == True{} : Bool},
  f: @s1: String -> @s2: String -> {String.append(s1, s2) == s : String} -> {ABNF.check(k, r, s1) == True{} : Bool} -> {ABNF.check(k, ABNF.seq(rs), s2) == True{} : Bool} -> C) -> C:
  (s1, s2, e, h1, h2) = p
  f(s1, s2, e, h1, h2)

def seqE(-C: Type, k: ABNF.Book, r: ABNF.Rule, rs: List<ABNF.Rule>, s: String, +h: {ABNF.check(k, ABNF.seq(r <> rs), s) == True{} : Bool},
  f: @s1: String -> @s2: String -> {String.append(s1, s2) == s : String} -> {ABNF.check(k, r, s1) == True{} : Bool} -> {ABNF.check(k, ABNF.seq(rs), s2) == True{} : Bool} -> C) -> C:
  seqE.go(C, k, r, rs, s, ABNF.seq.con.elim(k, r, rs, s, h), f)

def seq1E.go(+k: ABNF.Book, -r: ABNF.Rule, -s: String, +s1: String, s2: String, +e: {String.append(s1, s2) == s : String}, +h1: {ABNF.check(k, r, s1) == True{} : Bool}, +h2: {ABNF.check(k, ABNF.empty, s2) == True{} : Bool})
  -> {ABNF.check(k, r, s) == True{} : Bool}:
  %Equal.sym(String, s, s1, Equal.trans(String, s, String.append(s1, s2), s1, Equal.sym(String, String.append(s1, s2), s, e),
    Equal.trans(String, String.append(s1, s2), String.append(s1, SNil{}), s1, app_congl(s1, s2, SNil{}, emptyE(k, s2, h2)), append_nil(s1)))) : {ABNF.check(k, r, _) == True{} : Bool}
  h1

def seq1E(+k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.seq([r]), s) == True{} : Bool}) -> {ABNF.check(k, r, s) == True{} : Bool}:
  seqE({ABNF.check(k, r, s) == True{} : Bool}, k, r, [], s, h, +s1 => +s2 => +e => h1 => h2 => seq1E.go(k, r, s, s1, s2, e, h1, tt.sym(ABNF.check(k, ABNF.seq([]), s2), ABNF.check(k, ABNF.empty, s2), ABNF.seq.nil(k, s2), h2)))

def seq1I(+k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, r, s) == True{} : Bool}) -> {ABNF.check(k, ABNF.seq([r]), s) == True{} : Bool}:
  %append_nil(s) : {ABNF.check(k, ABNF.seq([r]), _) == True{} : Bool}
  ABNF.seq.con.intro(k, r, [], s, SNil{}, h, tt(ABNF.check(k, ABNF.seq([]), SNil{}), ABNF.check(k, ABNF.empty, SNil{}), ABNF.seq.nil(k, SNil{}), ABNF.empty.nil(k)))

def seqI2(+k: ABNF.Book, +a: ABNF.Rule, +b: ABNF.Rule, +s1: String, +s2: String, +h1: {ABNF.check(k, a, s1) == True{} : Bool}, +h2: {ABNF.check(k, b, s2) == True{} : Bool})
  -> {ABNF.check(k, ABNF.seq([a, b]), String.append(s1, s2)) == True{} : Bool}:
  ABNF.seq.con.intro(k, a, [b], s1, s2, h1, seq1I(k, b, s2, h2))

def seqI3(+k: ABNF.Book, +a: ABNF.Rule, +b: ABNF.Rule, +c: ABNF.Rule, +s1: String, +s2: String, +s3: String,
  h1: {ABNF.check(k, a, s1) == True{} : Bool}, +h2: {ABNF.check(k, b, s2) == True{} : Bool}, +h3: {ABNF.check(k, c, s3) == True{} : Bool})
  -> {ABNF.check(k, ABNF.seq([a, b, c]), String.append(s1, String.append(s2, s3))) == True{} : Bool}:
  ABNF.seq.con.intro(k, a, [b, c], s1, String.append(s2, s3), h1, seqI2(k, b, c, s2, s3, h2, h3))

def seqI4(+k: ABNF.Book, +a: ABNF.Rule, +b: ABNF.Rule, +c: ABNF.Rule, +d: ABNF.Rule, +s1: String, +s2: String, +s3: String, +s4: String,
  h1: {ABNF.check(k, a, s1) == True{} : Bool}, +h2: {ABNF.check(k, b, s2) == True{} : Bool}, +h3: {ABNF.check(k, c, s3) == True{} : Bool}, +h4: {ABNF.check(k, d, s4) == True{} : Bool})
  -> {ABNF.check(k, ABNF.seq([a, b, c, d]), String.append(s1, String.append(s2, String.append(s3, s4)))) == True{} : Bool}:
  ABNF.seq.con.intro(k, a, [b, c, d], s1, String.append(s2, String.append(s3, s4)), h1, seqI3(k, b, c, d, s2, s3, s4, h2, h3, h4))

def seqE2(-C: Type, +k: ABNF.Book, +a: ABNF.Rule, +b: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.seq([a, b]), s) == True{} : Bool},
  f: @s1: String -> @s2: String -> {String.append(s1, s2) == s : String} -> {ABNF.check(k, a, s1) == True{} : Bool} -> {ABNF.check(k, b, s2) == True{} : Bool} -> C) -> C:
  seqE(C, k, a, [b], s, h, s1 => +s2 => +e => h1 => h2 => f(s1, s2, e, h1, seq1E(k, b, s2, h2)))

def seqE3(-C: Type, +k: ABNF.Book, +a: ABNF.Rule, +b: ABNF.Rule, +c: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.seq([a, b, c]), s) == True{} : Bool},
  f: @s1: String -> @s2: String -> @s3: String -> {String.append(s1, String.append(s2, s3)) == s : String} -> {ABNF.check(k, a, s1) == True{} : Bool} -> {ABNF.check(k, b, s2) == True{} : Bool} -> {ABNF.check(k, c, s3) == True{} : Bool} -> C) -> C:
  seqE(C, k, a, [b, c], s, h, +s1 => +t => +e => h1 => h2 =>
    seqE2(C, k, b, c, t, h2, +s2 => +s3 => e2 => h3 => h4 =>
      f(s1, s2, s3, Equal.trans(String, String.append(s1, String.append(s2, s3)), String.append(s1, t), s, app_congl(s1, String.append(s2, s3), t, e2), e), h1, h3, h4)))

def seqE4(-C: Type, +k: ABNF.Book, +a: ABNF.Rule, +b: ABNF.Rule, +c: ABNF.Rule, +d: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.seq([a, b, c, d]), s) == True{} : Bool},
  f: @s1: String -> @s2: String -> @s3: String -> @s4: String -> {String.append(s1, String.append(s2, String.append(s3, s4))) == s : String} -> {ABNF.check(k, a, s1) == True{} : Bool} -> {ABNF.check(k, b, s2) == True{} : Bool} -> {ABNF.check(k, c, s3) == True{} : Bool} -> {ABNF.check(k, d, s4) == True{} : Bool} -> C) -> C:
  seqE(C, k, a, [b, c, d], s, h, +s1 => +t => +e => h1 => h2 =>
    seqE3(C, k, b, c, d, t, h2, +s2 => +s3 => +s4 => e2 => h3 => h4 => h5 =>
      f(s1, s2, s3, s4, Equal.trans(String, String.append(s1, String.append(s2, String.append(s3, s4))), String.append(s1, t), s, app_congl(s1, String.append(s2, String.append(s3, s4)), t, e2), e), h1, h3, h4, h5)))

def exZi(+k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.empty, s) == True{} : Bool}) -> {ABNF.check(k, ABNF.rep.exactly(0n, r), s) == True{} : Bool}:
  tt(ABNF.check(k, ABNF.rep.exactly(0n, r), s), ABNF.check(k, ABNF.empty, s), ABNF.rep.exactly.zero(k, r, s), h)

def exZe(+k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.rep.exactly(0n, r), s) == True{} : Bool}) -> {ABNF.check(k, ABNF.empty, s) == True{} : Bool}:
  tt.sym(ABNF.check(k, ABNF.rep.exactly(0n, r), s), ABNF.check(k, ABNF.empty, s), ABNF.rep.exactly.zero(k, r, s), h)

def exSi(+k: ABNF.Book, +n: Nat, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.seq([r, ABNF.rep.exactly(n, r)]), s) == True{} : Bool}) -> {ABNF.check(k, ABNF.rep.exactly(1n+n, r), s) == True{} : Bool}:
  tt(ABNF.check(k, ABNF.rep.exactly(1n+n, r), s), ABNF.check(k, ABNF.seq([r, ABNF.rep.exactly(n, r)]), s), ABNF.rep.exactly.succ(k, n, r, s), h)

def exSe(+k: ABNF.Book, +n: Nat, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.rep.exactly(1n+n, r), s) == True{} : Bool}) -> {ABNF.check(k, ABNF.seq([r, ABNF.rep.exactly(n, r)]), s) == True{} : Bool}:
  tt.sym(ABNF.check(k, ABNF.rep.exactly(1n+n, r), s), ABNF.check(k, ABNF.seq([r, ABNF.rep.exactly(n, r)]), s), ABNF.rep.exactly.succ(k, n, r, s), h)

def starNil(+k: ABNF.Book, +r: ABNF.Rule) -> {ABNF.check(k, ABNF.rep.any(r), SNil{}) == True{} : Bool}:
  ABNF.rep.any.intro(k, 0n, r, SNil{}, exZi(k, r, SNil{}, ABNF.empty.nil(k)))

def starCons.go(+k: ABNF.Book, +r: ABNF.Rule, +a: String, +b: String, +ha: {ABNF.check(k, r, a) == True{} : Bool}, p: &m: Nat -> {ABNF.check(k, ABNF.rep.exactly(m, r), b) == True{} : Bool})
  -> {ABNF.check(k, ABNF.rep.any(r), String.append(a, b)) == True{} : Bool}:
  (+m, hm) = p
  ABNF.rep.any.intro(k, 1n+m, r, String.append(a, b), exSi(k, m, r, String.append(a, b), seqI2(k, r, ABNF.rep.exactly(m, r), a, b, ha, hm)))

def starCons(+k: ABNF.Book, +r: ABNF.Rule, +a: String, +b: String, +ha: {ABNF.check(k, r, a) == True{} : Bool}, +hb: {ABNF.check(k, ABNF.rep.any(r), b) == True{} : Bool})
  -> {ABNF.check(k, ABNF.rep.any(r), String.append(a, b)) == True{} : Bool}:
  starCons.go(k, r, a, b, ha, ABNF.rep.any.elim(k, r, b, hb))

def starCase.m(-C: Type, +k: ABNF.Book, +r: ABNF.Rule, +s: String, m: Nat, +hm: {ABNF.check(k, ABNF.rep.exactly(m, r), s) == True{} : Bool},
  fn: {s == SNil{} : String} -> C,
  fc: @a: String -> @b: String -> {String.append(a, b) == s : String} -> {ABNF.check(k, r, a) == True{} : Bool} -> {ABNF.check(k, ABNF.rep.any(r), b) == True{} : Bool} -> C) -> C:
  match m:
    case 0n:
      fn(emptyE(k, s, exZe(k, r, s, hm)))
    case 1n+ +m1:
      seqE2(C, k, r, ABNF.rep.exactly(m1, r), s, exSe(k, m1, r, s, hm), a => +b => +e => ha => hb => fc(a, b, e, ha, ABNF.rep.any.intro(k, m1, r, b, hb)))

def starCase.go(-C: Type, +k: ABNF.Book, +r: ABNF.Rule, +s: String, p: &m: Nat -> {ABNF.check(k, ABNF.rep.exactly(m, r), s) == True{} : Bool},
  fn: {s == SNil{} : String} -> C,
  fc: @a: String -> @b: String -> {String.append(a, b) == s : String} -> {ABNF.check(k, r, a) == True{} : Bool} -> {ABNF.check(k, ABNF.rep.any(r), b) == True{} : Bool} -> C) -> C:
  (m, hm) = p
  starCase.m(C, k, r, s, m, hm, fn, fc)

# A repetition is empty, or one more and a repetition.
def starCase(-C: Type, +k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.rep.any(r), s) == True{} : Bool},
  fn: {s == SNil{} : String} -> C,
  fc: @a: String -> @b: String -> {String.append(a, b) == s : String} -> {ABNF.check(k, r, a) == True{} : Bool} -> {ABNF.check(k, ABNF.rep.any(r), b) == True{} : Bool} -> C) -> C:
  starCase.go(C, k, r, s, ABNF.rep.any.elim(k, r, s, h), fn, fc)

def optE(-C: Type, +k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.opt(r), s) == True{} : Bool},
  fn: {s == SNil{} : String} -> C, fs: {ABNF.check(k, r, s) == True{} : Bool} -> C) -> C:
  either(&2, &2, {ABNF.check(k, ABNF.empty, s) == True{} : Bool}, {ABNF.check(k, ABNF.alt([r]), s) == True{} : Bool}, C,
    or_elim(ABNF.check(k, ABNF.empty, s), ABNF.check(k, ABNF.alt([r]), s), tt.sym(ABNF.check(k, ABNF.opt(r), s), Bool.or(ABNF.check(k, ABNF.empty, s), ABNF.check(k, ABNF.alt([r]), s)), Equal.trans(Bool, ABNF.check(k, ABNF.opt(r), s), ABNF.check(k, ABNF.alt([ABNF.empty, r]), s), Bool.or(ABNF.check(k, ABNF.empty, s), ABNF.check(k, ABNF.alt([r]), s)), ABNF.opt.ok(k, r, s), ABNF.alt.con(k, ABNF.empty, [r], s)), h)),
    +he => fn(emptyE(k, s, he)),
    +hr => fs(tt.sym(ABNF.check(k, ABNF.alt([r]), s), ABNF.check(k, r, s), altS(k, r, s), hr)))

def optN(+k: ABNF.Book, +r: ABNF.Rule) -> {ABNF.check(k, ABNF.opt(r), SNil{}) == True{} : Bool}:
  tt(ABNF.check(k, ABNF.opt(r), SNil{}), Bool.or(ABNF.check(k, ABNF.empty, SNil{}), ABNF.check(k, ABNF.alt([r]), SNil{})), Equal.trans(Bool, ABNF.check(k, ABNF.opt(r), SNil{}), ABNF.check(k, ABNF.alt([ABNF.empty, r]), SNil{}), Bool.or(ABNF.check(k, ABNF.empty, SNil{}), ABNF.check(k, ABNF.alt([r]), SNil{})), ABNF.opt.ok(k, r, SNil{}), ABNF.alt.con(k, ABNF.empty, [r], SNil{})),
    or_l(ABNF.check(k, ABNF.empty, SNil{}), ABNF.check(k, ABNF.alt([r]), SNil{}), ABNF.empty.nil(k)))

def optS(+k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, r, s) == True{} : Bool}) -> {ABNF.check(k, ABNF.opt(r), s) == True{} : Bool}:
  tt(ABNF.check(k, ABNF.opt(r), s), Bool.or(ABNF.check(k, ABNF.empty, s), ABNF.check(k, ABNF.alt([r]), s)), Equal.trans(Bool, ABNF.check(k, ABNF.opt(r), s), ABNF.check(k, ABNF.alt([ABNF.empty, r]), s), Bool.or(ABNF.check(k, ABNF.empty, s), ABNF.check(k, ABNF.alt([r]), s)), ABNF.opt.ok(k, r, s), ABNF.alt.con(k, ABNF.empty, [r], s)),
    or_r(ABNF.check(k, ABNF.empty, s), ABNF.check(k, ABNF.alt([r]), s), tt(ABNF.check(k, ABNF.alt([r]), s), ABNF.check(k, r, s), altS(k, r, s), h)))

# References
# ==========

def ufA.go(d: Nat, +N: String, +s: String, +h: {ABNF.check(LB(d), ABNF.ref(N), s) == True{} : Bool}) -> {ABNF.check(BK, ABNF.lookup(Laws.grammar, N), s) == True{} : Bool}:
  match d:
    case 0n:
      Empty.absurd({ABNF.check(BK, ABNF.lookup(Laws.grammar, N), s) == True{} : Bool}, contra(ABNF.check(LB(0n), ABNF.ref(N), s), h, ABNF.ref.zero(Laws.grammar, N, s)))
    case 1n+ +d1:
      ABNF.full.intro(d1, Laws.grammar, ABNF.lookup(Laws.grammar, N), s,
        tt.sym(ABNF.check(LB(1n+d1), ABNF.ref(N), s), ABNF.check(LB(d1), ABNF.lookup(Laws.grammar, N), s), ABNF.ref.succ(d1, Laws.grammar, N, s), h))

def ufA(+N: String, +s: String, p: &d: Nat -> {ABNF.check(ABNF.limit(d, Laws.grammar), ABNF.ref(N), s) == True{} : Bool}) -> {ABNF.check(BK, ABNF.lookup(Laws.grammar, N), s) == True{} : Bool}:
  (d, h) = p
  ufA.go(d, N, s, h)

def ufB(+N: String, +s: String, p: &d: Nat -> {ABNF.check(ABNF.limit(d, Laws.grammar), ABNF.lookup(Laws.grammar, N), s) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref(N), s) == True{} : Bool}:
  (+d, h) = p
  ABNF.full.intro(1n+d, Laws.grammar, ABNF.ref(N), s,
    tt(ABNF.check(LB(1n+d), ABNF.ref(N), s), ABNF.check(LB(d), ABNF.lookup(Laws.grammar, N), s), ABNF.ref.succ(d, Laws.grammar, N, s), h))

def unfold1(+N: String, +s: String) -> {ABNF.check(BK, ABNF.ref(N), s) == ABNF.check(BK, ABNF.lookup(Laws.grammar, N), s) : Bool}:
  beq(ABNF.check(BK, ABNF.ref(N), s), ABNF.check(BK, ABNF.lookup(Laws.grammar, N), s),
    +h => ufA(N, s, ABNF.full.elim(Laws.grammar, ABNF.ref(N), s, h)),
    +h => ufB(N, s, ABNF.full.elim(Laws.grammar, ABNF.lookup(Laws.grammar, N), s, h)))

# The grammar as Data, so a proof can walk it more than once.
type GL is Data:
  GNil{}
  GCons{k: String, r: ABNF.Rule, rest: GL}

def toList(gl: GL) -> List<(String & ABNF.Rule)>:
  match gl:
    case GNil{}:
      []
    case GCons{k, r, rest}:
      (k, r) <> toList(rest)

def GRAMMAR() -> GL:
  GCons{"JSON-text", ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]),
    GCons{"begin-array", ABNF.seq([ABNF.ref("ws"), ABNF.char('['), ABNF.ref("ws")]),
    GCons{"begin-object", ABNF.seq([ABNF.ref("ws"), ABNF.char('{'), ABNF.ref("ws")]),
    GCons{"end-array", ABNF.seq([ABNF.ref("ws"), ABNF.char(']'), ABNF.ref("ws")]),
    GCons{"end-object", ABNF.seq([ABNF.ref("ws"), ABNF.char('}'), ABNF.ref("ws")]),
    GCons{"name-separator", ABNF.seq([ABNF.ref("ws"), ABNF.char(':'), ABNF.ref("ws")]),
    GCons{"value-separator", ABNF.seq([ABNF.ref("ws"), ABNF.char(','), ABNF.ref("ws")]),
    GCons{"ws", ABNF.rep.any(ABNF.alt([ABNF.char(Chr{32}), ABNF.char(Chr{9}), ABNF.char(Chr{10}), ABNF.char(Chr{13})])),
    GCons{"value", ABNF.alt([ABNF.ref("false"), ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")]),
    GCons{"false", ABNF.string.case_sensitive("false"),
    GCons{"null", ABNF.string.case_sensitive("null"),
    GCons{"true", ABNF.string.case_sensitive("true"),
    GCons{"object", ABNF.seq([ABNF.ref("begin-object"), ABNF.opt(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(ABNF.seq([ABNF.ref("value-separator"), ABNF.ref("member")]))])), ABNF.ref("end-object")]),
    GCons{"member", ABNF.seq([ABNF.ref("string"), ABNF.ref("name-separator"), ABNF.ref("value")]),
    GCons{"array", ABNF.seq([ABNF.ref("begin-array"), ABNF.opt(ABNF.seq([ABNF.ref("value"), ABNF.rep.any(ABNF.seq([ABNF.ref("value-separator"), ABNF.ref("value")]))])), ABNF.ref("end-array")]),
    GCons{"number", ABNF.seq([ABNF.opt(ABNF.ref("minus")), ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp"))]),
    GCons{"decimal-point", ABNF.char('.'),
    GCons{"digit1-9", ABNF.range('1', '9'),
    GCons{"e", ABNF.alt([ABNF.char('e'), ABNF.char('E')]),
    GCons{"exp", ABNF.seq([ABNF.ref("e"), ABNF.opt(ABNF.alt([ABNF.ref("minus"), ABNF.ref("plus")])), ABNF.rep.at_least(1n, ABNF.core.digit)]),
    GCons{"frac", ABNF.seq([ABNF.ref("decimal-point"), ABNF.rep.at_least(1n, ABNF.core.digit)]),
    GCons{"int", ABNF.alt([ABNF.ref("zero"), ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(ABNF.core.digit)])]),
    GCons{"minus", ABNF.char('-'),
    GCons{"plus", ABNF.char('+'),
    GCons{"zero", ABNF.char('0'),
    GCons{"string", ABNF.seq([ABNF.ref("quotation-mark"), ABNF.rep.any(ABNF.ref("char")), ABNF.ref("quotation-mark")]),
    GCons{"char", ABNF.alt([ABNF.ref("unescaped"), ABNF.seq([ABNF.ref("escape"), ABNF.alt([ABNF.char('"'), ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), ABNF.seq([ABNF.char('u'), ABNF.rep.exactly(4n, ABNF.core.hexdig)])])])]),
    GCons{"escape", ABNF.char('\\'),
    GCons{"quotation-mark", ABNF.char('"'),
    GCons{"unescaped", ABNF.alt([ABNF.range(Chr{32}, Chr{33}), ABNF.range(Chr{35}, Chr{91}), ABNF.range(Chr{93}, Chr{1114111})]),
    GNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

# gsel(gl, N): the rules named N in gl, in order.
def gselC(b: Bool, r: ABNF.Rule, t: List<ABNF.Rule>) -> List<ABNF.Rule>:
  match b:
    case True{}:
      r <> t
    case False{}:
      t

def gsel(gl: GL, +name: String) -> List<ABNF.Rule>:
  match gl:
    case GNil{}:
      []
    case GCons{k, r, rest}:
      gselC(String.eq(String.to_lower(k), String.to_lower(name)), r, gsel(rest, name))

# galt(book, L, s): whether s matches one of the rules L.
def galt(+book: ABNF.Book, L: List<ABNF.Rule>, +s: String) -> Bool:
  match L:
    case []:
      False{}
    case r <> t:
      Bool.or(ABNF.check(book, r, s), galt(book, t, s))

def lkStep(+book: ABNF.Book, b: Bool, +r: ABNF.Rule, -L: List<ABNF.Rule>, +s: String, -X: Bool, +ih: {X == galt(book, L, s) : Bool})
  -> {Bool.or(Bool.and(b, ABNF.check(book, r, s)), X) == galt(book, gselC(b, r, L), s) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, X, galt(book, L, s), ih) : {Bool.or(ABNF.check(book, r, s), _) == galt(book, r <> L, s) : Bool}
      {==}
    case False{}:
      ih

def lookupEqG(+book: ABNF.Book, +gl: GL, +name: String, +s: String) -> {ABNF.check(book, ABNF.lookup(toList(gl), name), s) == galt(book, gsel(gl, name), s) : Bool}:
  match gl:
    case GNil{}:
      ABNF.lookup.nil(book, name, s)
    case GCons{+k, +r, +rest}:
      Equal.trans(Bool, ABNF.check(book, ABNF.lookup((k, r) <> toList(rest), name), s), Bool.or(Bool.and(String.eq(String.to_lower(k), String.to_lower(name)), ABNF.check(book, r, s)), ABNF.check(book, ABNF.lookup(toList(rest), name), s)), galt(book, gsel(GCons{k, r, rest}, name), s),
        ABNF.lookup.con(book, k, r, toList(rest), name, s),
        lkStep(book, String.eq(String.to_lower(k), String.to_lower(name)), r, gsel(rest, name), s, ABNF.check(book, ABNF.lookup(toList(rest), name), s), lookupEqG(book, rest, name, s)))

# Matching a lookup in the grammar is matching one of the rules it finds.
def lookupEq(+book: ABNF.Book, +name: String, +s: String) -> {ABNF.check(book, ABNF.lookup(Laws.grammar, name), s) == galt(book, gsel(GRAMMAR, name), s) : Bool}:
  lookupEqG(book, GRAMMAR, name, s)

# MB(N, body): matching the rule N is matching its body.
def MB(+N: String, +body: ABNF.Rule, +s: String, +e: {gsel(GRAMMAR, N) == [body] : List<ABNF.Rule>}) -> {ABNF.check(BK, ABNF.ref(N), s) == ABNF.check(BK, body, s) : Bool}:
  Equal.trans(Bool, ABNF.check(BK, ABNF.ref(N), s), ABNF.check(BK, ABNF.lookup(Laws.grammar, N), s), ABNF.check(BK, body, s), unfold1(N, s),
    Equal.trans(Bool, ABNF.check(BK, ABNF.lookup(Laws.grammar, N), s), galt(BK, gsel(GRAMMAR, N), s), ABNF.check(BK, body, s), lookupEq(BK, N, s),
      Equal.trans(Bool, galt(BK, gsel(GRAMMAR, N), s), galt(BK, [body], s), ABNF.check(BK, body, s),
        Equal.cong(List<ABNF.Rule>, Bool, L => galt(BK, L, s), gsel(GRAMMAR, N), [body], e), or_false(ABNF.check(BK, body, s)))))

def MBe(+N: String, +body: ABNF.Rule, +s: String, +e: {gsel(GRAMMAR, N) == [body] : List<ABNF.Rule>}, +h: {ABNF.check(BK, ABNF.ref(N), s) == True{} : Bool}) -> {ABNF.check(BK, body, s) == True{} : Bool}:
  tt.sym(ABNF.check(BK, ABNF.ref(N), s), ABNF.check(BK, body, s), MB(N, body, s, e), h)

def MBi(+N: String, +body: ABNF.Rule, +s: String, +e: {gsel(GRAMMAR, N) == [body] : List<ABNF.Rule>}, +h: {ABNF.check(BK, body, s) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref(N), s) == True{} : Bool}:
  tt(ABNF.check(BK, ABNF.ref(N), s), ABNF.check(BK, body, s), MB(N, body, s, e), h)

def refL(+d: Nat, +N: String, +body: ABNF.Rule, +s: String, +e: {gsel(GRAMMAR, N) == [body] : List<ABNF.Rule>}) -> {ABNF.check(LB(1n+d), ABNF.ref(N), s) == ABNF.check(LB(d), body, s) : Bool}:
  Equal.trans(Bool, ABNF.check(LB(1n+d), ABNF.ref(N), s), ABNF.check(LB(d), ABNF.lookup(Laws.grammar, N), s), ABNF.check(LB(d), body, s), ABNF.ref.succ(d, Laws.grammar, N, s),
    Equal.trans(Bool, ABNF.check(LB(d), ABNF.lookup(Laws.grammar, N), s), galt(LB(d), gsel(GRAMMAR, N), s), ABNF.check(LB(d), body, s), lookupEq(LB(d), N, s),
      Equal.trans(Bool, galt(LB(d), gsel(GRAMMAR, N), s), galt(LB(d), [body], s), ABNF.check(LB(d), body, s),
        Equal.cong(List<ABNF.Rule>, Bool, L => galt(LB(d), L, s), gsel(GRAMMAR, N), [body], e), or_false(ABNF.check(LB(d), body, s)))))

# A match at some depth is a match.
def toBK(+d: Nat, +r: ABNF.Rule, +s: String, +h: {ABNF.check(LB(d), r, s) == True{} : Bool}) -> {ABNF.check(BK, r, s) == True{} : Bool}:
  ABNF.full.intro(d, Laws.grammar, r, s, h)

# A law's matches is a check against the grammar.
def mt(+N: String, +s: String, +h: {ABNF.matches(Laws.grammar, N, s) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref(N), s) == True{} : Bool}:
  tt.sym(ABNF.matches(Laws.grammar, N, s), ABNF.check(BK, ABNF.ref(N), s), ABNF.matches.ok(Laws.grammar, N, s), h)

# Choices
# =======

def selT(-A: Type, b: Bool, -x: Unit -> A, -y: Unit -> A, +h: {b == True{} : Bool}) -> {sel(A, b, x, y) == x(Unit{}) : A}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({sel(A, False{}, x, y) == x(Unit{}) : A}, false_ne_true(h))

def selF(-A: Type, b: Bool, -x: Unit -> A, -y: Unit -> A, +h: {b == False{} : Bool}) -> {sel(A, b, x, y) == y(Unit{}) : A}:
  match b:
    case True{}:
      Empty.absurd({sel(A, True{}, x, y) == y(Unit{}) : A}, false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      {==}

# Whitespace
# ==========

def wsall(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(isws(c), wsall(t))

def wsp(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sel(String, isws(c), u => SCon{c, wsp(t)}, u => SNil{})

def wsc1(+k: ABNF.Book, +c: Char) -> {ABNF.check(k, WSC, SCon{c, SNil{}}) == isws(c) : Bool}:
  alt2(k, ABNF.char(Chr{32}), [ABNF.char(Chr{9}), ABNF.char(Chr{10}), ABNF.char(Chr{13})], SCon{c, SNil{}}, Char.is_eq(Chr{32}, c), Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))), ABNF.char.one(k, Chr{32}, c),
    alt2(k, ABNF.char(Chr{9}), [ABNF.char(Chr{10}), ABNF.char(Chr{13})], SCon{c, SNil{}}, Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})), ABNF.char.one(k, Chr{9}, c),
      alt2(k, ABNF.char(Chr{10}), [ABNF.char(Chr{13})], SCon{c, SNil{}}, Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}), ABNF.char.one(k, Chr{10}, c),
        alt2(k, ABNF.char(Chr{13}), [], SCon{c, SNil{}}, Char.is_eq(Chr{13}, c), False{}, ABNF.char.one(k, Chr{13}, c), ABNF.alt.nil(k, SCon{c, SNil{}})))))

def wsc0(+k: ABNF.Book) -> {ABNF.check(k, WSC, SNil{}) == False{} : Bool}:
  alt2(k, ABNF.char(Chr{32}), [ABNF.char(Chr{9}), ABNF.char(Chr{10}), ABNF.char(Chr{13})], SNil{}, False{}, False{}, ABNF.char.nil(k, Chr{32}),
    alt2(k, ABNF.char(Chr{9}), [ABNF.char(Chr{10}), ABNF.char(Chr{13})], SNil{}, False{}, False{}, ABNF.char.nil(k, Chr{9}),
      alt2(k, ABNF.char(Chr{10}), [ABNF.char(Chr{13})], SNil{}, False{}, False{}, ABNF.char.nil(k, Chr{10}),
        alt2(k, ABNF.char(Chr{13}), [], SNil{}, False{}, False{}, ABNF.char.nil(k, Chr{13}), ABNF.alt.nil(k, SNil{})))))

def wsc2(+k: ABNF.Book, +a: Char, +b: Char, +t: String) -> {ABNF.check(k, WSC, SCon{a, SCon{b, t}}) == False{} : Bool}:
  alt2(k, ABNF.char(Chr{32}), [ABNF.char(Chr{9}), ABNF.char(Chr{10}), ABNF.char(Chr{13})], SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(k, Chr{32}, a, b, t),
    alt2(k, ABNF.char(Chr{9}), [ABNF.char(Chr{10}), ABNF.char(Chr{13})], SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(k, Chr{9}, a, b, t),
      alt2(k, ABNF.char(Chr{10}), [ABNF.char(Chr{13})], SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(k, Chr{10}, a, b, t),
        alt2(k, ABNF.char(Chr{13}), [], SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(k, Chr{13}, a, b, t), ABNF.alt.nil(k, SCon{a, SCon{b, t}})))))

def wsE.step(+c: Char, -b: String, -w: String, +e: {String.append(SCon{c, SNil{}}, b) == w : String}, +hc: {ABNF.check(BK, WSC, SCon{c, SNil{}}) == True{} : Bool}, +hb: {wsall(b) == True{} : Bool})
  -> {wsall(w) == True{} : Bool}:
  %e : {wsall(_) == True{} : Bool}
  and_intro(isws(c), wsall(b), tt.sym(ABNF.check(BK, WSC, SCon{c, SNil{}}), isws(c), wsc1(BK, c), hc), hb)

def wsE.m(m: Nat, +w: String, +h: {ABNF.check(BK, ABNF.rep.exactly(m, WSC), w) == True{} : Bool}) -> {wsall(w) == True{} : Bool}:
  match m:
    case 0n:
      %Equal.sym(String, w, SNil{}, emptyE(BK, w, exZe(BK, WSC, w, h))) : {wsall(_) == True{} : Bool}
      {==}
    case 1n+ +m1:
      seqE2({wsall(w) == True{} : Bool}, BK, WSC, ABNF.rep.exactly(m1, WSC), w, exSe(BK, m1, WSC, w, h), +a => +b => +e => +ha => hb =>
        one({wsall(w) == True{} : Bool}, BK, WSC, a, ha, wsc0(BK), x => y => z => wsc2(BK, x, y, z), c => ec => hc =>
          wsE.step(c, b, w, Equal.trans(String, String.append(SCon{c, SNil{}}, b), String.append(a, b), w, app_congr(b, SCon{c, SNil{}}, a, ec), e), hc, wsE.m(m1, b, hb))))

def wsE.go(+w: String, p: &m: Nat -> {ABNF.check(BK, ABNF.rep.exactly(m, WSC), w) == True{} : Bool}) -> {wsall(w) == True{} : Bool}:
  (m, h) = p
  wsE.m(m, w, h)

def wsE(+w: String, +h: {ABNF.check(BK, ABNF.ref("ws"), w) == True{} : Bool}) -> {wsall(w) == True{} : Bool}:
  wsE.go(w, ABNF.rep.any.elim(BK, WSC, w, MBe("ws", ABNF.rep.any(WSC), w, {==}, h)))

def wsI.star(w: String, +h: {wsall(w) == True{} : Bool}) -> {ABNF.check(BK, ABNF.rep.any(WSC), w) == True{} : Bool}:
  match w:
    case SNil{}:
      starNil(BK, WSC)
    case SCon{+c, +t}:
      starCons(BK, WSC, SCon{c, SNil{}}, t, tt(ABNF.check(BK, WSC, SCon{c, SNil{}}), isws(c), wsc1(BK, c), and_l(isws(c), wsall(t), h)), wsI.star(t, and_r(isws(c), wsall(t), h)))

def wsI(+w: String, +h: {wsall(w) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("ws"), w) == True{} : Bool}:
  MBi("ws", ABNF.rep.any(WSC), w, {==}, wsI.star(w, h))

# skip_ws drops a whitespace prefix.
def WE(w: String, -t: String, +h: {wsall(w) == True{} : Bool}) -> {skip_ws(String.append(w, t)) == skip_ws(t) : String}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +w1}:
      Equal.trans(String, skip_ws(SCon{c, String.append(w1, t)}), skip_ws(String.append(w1, t)), skip_ws(t),
        selT(String, isws(c), u => skip_ws(String.append(w1, t)), u => SCon{c, String.append(w1, t)}, and_l(isws(c), wsall(w1), h)),
        WE(w1, t, and_r(isws(c), wsall(w1), h)))

def skipF(+c: Char, -t: String, +h: {isws(c) == False{} : Bool}) -> {skip_ws(SCon{c, t}) == SCon{c, t} : String}:
  selF(String, isws(c), u => skip_ws(t), u => SCon{c, t}, h)

def WI.t(+c: Char, +t: String, +h: {isws(c) == True{} : Bool}, +ih: {String.append(wsp(t), skip_ws(t)) == t : String}) -> {String.append(wsp(SCon{c, t}), skip_ws(SCon{c, t})) == SCon{c, t} : String}:
  %Equal.sym(String, wsp(SCon{c, t}), SCon{c, wsp(t)}, selT(String, isws(c), u => SCon{c, wsp(t)}, u => SNil{}, h)) : {String.append(_, skip_ws(SCon{c, t})) == SCon{c, t} : String}
  %Equal.sym(String, skip_ws(SCon{c, t}), skip_ws(t), selT(String, isws(c), u => skip_ws(t), u => SCon{c, t}, h)) : {String.append(SCon{c, wsp(t)}, _) == SCon{c, t} : String}
  cons_eq(c, String.append(wsp(t), skip_ws(t)), t, ih)

def WI.f(+c: Char, +t: String, +h: {isws(c) == False{} : Bool}) -> {String.append(wsp(SCon{c, t}), skip_ws(SCon{c, t})) == SCon{c, t} : String}:
  %Equal.sym(String, wsp(SCon{c, t}), SNil{}, selF(String, isws(c), u => SCon{c, wsp(t)}, u => SNil{}, h)) : {String.append(_, skip_ws(SCon{c, t})) == SCon{c, t} : String}
  skipF(c, t, h)

# A string is its whitespace prefix, then what skip_ws leaves.
def WI(s: String) -> {String.append(wsp(s), skip_ws(s)) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      bcase({String.append(wsp(SCon{c, t}), skip_ws(SCon{c, t})) == SCon{c, t} : String}, isws(c), +h => WI.t(c, t, h, WI(t)), +h => WI.f(c, t, h))

def WIa.t(+c: Char, +t: String, +h: {isws(c) == True{} : Bool}, +ih: {wsall(wsp(t)) == True{} : Bool}) -> {wsall(wsp(SCon{c, t})) == True{} : Bool}:
  %Equal.sym(String, wsp(SCon{c, t}), SCon{c, wsp(t)}, selT(String, isws(c), u => SCon{c, wsp(t)}, u => SNil{}, h)) : {wsall(_) == True{} : Bool}
  and_intro(isws(c), wsall(wsp(t)), h, ih)

def WIa.f(+c: Char, +t: String, +h: {isws(c) == False{} : Bool}) -> {wsall(wsp(SCon{c, t})) == True{} : Bool}:
  %Equal.sym(String, wsp(SCon{c, t}), SNil{}, selF(String, isws(c), u => SCon{c, wsp(t)}, u => SNil{}, h)) : {wsall(_) == True{} : Bool}
  {==}

def WIa(s: String) -> {wsall(wsp(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      bcase({wsall(wsp(SCon{c, t})) == True{} : Bool}, isws(c), +h => WIa.t(c, t, h, WIa(t)), +h => WIa.f(c, t, h))

def SKA.f(+a: Char, -r: String, -t: String, -c: Char, -y: String, +h: {isws(a) == False{} : Bool}, +e: {skip_ws(SCon{a, r}) == SCon{c, y} : String})
  -> {skip_ws(SCon{a, String.append(r, t)}) == SCon{c, String.append(y, t)} : String}:
  %Equal.sym(String, skip_ws(SCon{a, String.append(r, t)}), SCon{a, String.append(r, t)}, skipF(a, String.append(r, t), h)) : {_ == SCon{c, String.append(y, t)} : String}
  Equal.cong(String, String, z => String.append(z, t), SCon{a, r}, SCon{c, y}, Equal.trans(String, SCon{a, r}, skip_ws(SCon{a, r}), SCon{c, y}, Equal.sym(String, skip_ws(SCon{a, r}), SCon{a, r}, skipF(a, r, h)), e))

# When skip_ws leaves something, more text after it stays.
def SKA(x: String, +t: String, +c: Char, +y: String, +e: {skip_ws(x) == SCon{c, y} : String}) -> {skip_ws(String.append(x, t)) == SCon{c, String.append(y, t)} : String}:
  match x:
    case SNil{}:
      Empty.absurd({skip_ws(t) == SCon{c, String.append(y, t)} : String}, nil_ne_con(c, y, e))
    case SCon{+a, +r}:
      bcase({skip_ws(SCon{a, String.append(r, t)}) == SCon{c, String.append(y, t)} : String}, isws(a),
        +h => Equal.trans(String, skip_ws(SCon{a, String.append(r, t)}), skip_ws(String.append(r, t)), SCon{c, String.append(y, t)},
          selT(String, isws(a), u => skip_ws(String.append(r, t)), u => SCon{a, String.append(r, t)}, h),
          SKA(r, t, c, y, Equal.trans(String, skip_ws(r), skip_ws(SCon{a, r}), SCon{c, y}, Equal.sym(String, skip_ws(SCon{a, r}), skip_ws(r), selT(String, isws(a), u => skip_ws(r), u => SCon{a, r}, h)), e))),
        +h => SKA.f(a, r, t, c, y, h, e))

def tokb2(+ch: Char, x: String) -> Bool:
  match x:
    case SNil{}:
      False{}
    case SCon{c, y}:
      Bool.and(Char.is_eq(ch, c), wsall(y))

def tokb(+ch: Char, b: String) -> Bool:
  tokb2(ch, skip_ws(b))

# Tokens
# ======
#
# tokb(c, b): b is whitespace, c, whitespace, as in begin-array.

def tokE.ws(+ch: Char, +x: Char, +hch: {isws(ch) == False{} : Bool}, +hx: {ABNF.check(BK, ABNF.char(ch), SCon{x, SNil{}}) == True{} : Bool}) -> {isws(x) == False{} : Bool}:
  %char_eq(ch, x, tt.sym(ABNF.check(BK, ABNF.char(ch), SCon{x, SNil{}}), Char.is_eq(ch, x), ABNF.char.one(BK, ch, x), hx)) : {isws(_) == False{} : Bool}
  hch

def tokE.go(+ch: Char, -b: String, +w1: String, +x: Char, +w2: String, +eb: {String.append(w1, SCon{x, w2}) == b : String},
  +hw1: {wsall(w1) == True{} : Bool}, +hw2: {wsall(w2) == True{} : Bool}, +hch: {isws(ch) == False{} : Bool}, +hx: {ABNF.check(BK, ABNF.char(ch), SCon{x, SNil{}}) == True{} : Bool})
  -> {tokb(ch, b) == True{} : Bool}:
  %eb : {tokb(ch, _) == True{} : Bool}
  %Equal.sym(String, skip_ws(String.append(w1, SCon{x, w2})), skip_ws(SCon{x, w2}), WE(w1, SCon{x, w2}, hw1)) : {tokb2(ch, _) == True{} : Bool}
  %Equal.sym(String, skip_ws(SCon{x, w2}), SCon{x, w2}, skipF(x, w2, tokE.ws(ch, x, hch, hx))) : {tokb2(ch, _) == True{} : Bool}
  and_intro(Char.is_eq(ch, x), wsall(w2), tt.sym(ABNF.check(BK, ABNF.char(ch), SCon{x, SNil{}}), Char.is_eq(ch, x), ABNF.char.one(BK, ch, x), hx), hw2)

def tokE(+N: String, +ch: Char, +b: String, +e: {gsel(GRAMMAR, N) == [TOK(ch)] : List<ABNF.Rule>}, +hch: {isws(ch) == False{} : Bool}, +h: {ABNF.check(BK, ABNF.ref(N), b) == True{} : Bool})
  -> {tokb(ch, b) == True{} : Bool}:
  seqE3({tokb(ch, b) == True{} : Bool}, BK, ABNF.ref("ws"), ABNF.char(ch), ABNF.ref("ws"), b, MBe(N, TOK(ch), b, e, h), +w1 => +cs => +w2 => +eb => +h1 => +h2 => +h3 =>
    one({tokb(ch, b) == True{} : Bool}, BK, ABNF.char(ch), cs, h2, ABNF.char.nil(BK, ch), x => y => z => ABNF.char.many(BK, ch, x, y, z), +x => +ex => +hx =>
      tokE.go(ch, b, w1, x, w2, Equal.trans(String, String.append(w1, SCon{x, w2}), String.append(w1, String.append(cs, w2)), b, app_congl(w1, SCon{x, w2}, String.append(cs, w2), app_congr(w2, SCon{x, SNil{}}, cs, ex)), eb),
        wsE(w1, h1), wsE(w2, h3), hch, hx)))

def tokI.go(+N: String, +ch: Char, +b: String, x: String, +ex: {skip_ws(b) == x : String}, +e: {gsel(GRAMMAR, N) == [TOK(ch)] : List<ABNF.Rule>}, +h: {tokb2(ch, x) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.ref(N), b) == True{} : Bool}:
  match x:
    case SNil{}:
      Empty.absurd({ABNF.check(BK, ABNF.ref(N), b) == True{} : Bool}, false_ne_true(h))
    case SCon{+c, +y}:
      %Equal.sym(String, b, String.append(wsp(b), SCon{c, y}), Equal.trans(String, b, String.append(wsp(b), skip_ws(b)), String.append(wsp(b), SCon{c, y}), Equal.sym(String, String.append(wsp(b), skip_ws(b)), b, WI(b)), app_congl(wsp(b), skip_ws(b), SCon{c, y}, ex))) : {ABNF.check(BK, ABNF.ref(N), _) == True{} : Bool}
      MBi(N, TOK(ch), String.append(wsp(b), SCon{c, y}), e,
        seqI3(BK, ABNF.ref("ws"), ABNF.char(ch), ABNF.ref("ws"), wsp(b), SCon{c, SNil{}}, y, wsI(wsp(b), WIa(b)),
          tt(ABNF.check(BK, ABNF.char(ch), SCon{c, SNil{}}), Char.is_eq(ch, c), ABNF.char.one(BK, ch, c), and_l(Char.is_eq(ch, c), wsall(y), h)),
          wsI(y, and_r(Char.is_eq(ch, c), wsall(y), h))))

def tokI(+N: String, +ch: Char, +b: String, +e: {gsel(GRAMMAR, N) == [TOK(ch)] : List<ABNF.Rule>}, +h: {tokb(ch, b) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.ref(N), b) == True{} : Bool}:
  tokI.go(N, ch, b, skip_ws(b), {==}, e, h)

def tokU.go(+ch: Char, +b: String, +t: String, x: String, +ex: {skip_ws(b) == x : String}, +h: {tokb2(ch, x) == True{} : Bool})
  -> {skip_ws(String.append(b, t)) == SCon{ch, String.append(str_tl(x), t)} : String}:
  match x:
    case SNil{}:
      Empty.absurd({skip_ws(String.append(b, t)) == SCon{ch, String.append(SNil{}, t)} : String}, false_ne_true(h))
    case SCon{+c, +y}:
      %Equal.sym(Char, ch, c, char_eq(ch, c, and_l(Char.is_eq(ch, c), wsall(y), h))) : {skip_ws(String.append(b, t)) == SCon{_, String.append(y, t)} : String}
      SKA(b, t, c, y, ex)

# After a token, the text continues with its character and some whitespace.
def tokU(+ch: Char, +b: String, +t: String, +h: {tokb(ch, b) == True{} : Bool}) -> {skip_ws(String.append(b, t)) == SCon{ch, String.append(str_tl(skip_ws(b)), t)} : String}:
  tokU.go(ch, b, t, skip_ws(b), {==}, h)

def tokW.go(+ch: Char, x: String, +h: {tokb2(ch, x) == True{} : Bool}) -> {wsall(str_tl(x)) == True{} : Bool}:
  match x:
    case SNil{}:
      Empty.absurd({wsall(SNil{}) == True{} : Bool}, false_ne_true(h))
    case SCon{+c, +y}:
      and_r(Char.is_eq(ch, c), wsall(y), h)

def tokW(+ch: Char, +b: String, +h: {tokb(ch, b) == True{} : Bool}) -> {wsall(str_tl(skip_ws(b))) == True{} : Bool}:
  tokW.go(ch, skip_ws(b), h)

# Literals
# ========

def csE.go(+c: Char, -t: String, +x: Char, -a: String, +b: String, -s: String, +e: {String.append(a, b) == s : String}, +ex: {SCon{x, SNil{}} == a : String},
  +hx: {Char.is_eq(c, x) == True{} : Bool}, +hb: {b == t : String}) -> {s == SCon{c, t} : String}:
  %Equal.sym(String, s, SCon{x, b}, Equal.trans(String, s, String.append(a, b), SCon{x, b}, Equal.sym(String, String.append(a, b), s, e), app_congr(b, a, SCon{x, SNil{}}, Equal.sym(String, SCon{x, SNil{}}, a, ex)))) : {_ == SCon{c, t} : String}
  %char_eq(c, x, hx) : {SCon{_, b} == SCon{c, t} : String}
  cons_eq(c, b, t, hb)

def csE(+k: ABNF.Book, lit: String, +s: String, +h: {ABNF.check(k, ABNF.string.case_sensitive(lit), s) == True{} : Bool}) -> {s == lit : String}:
  match lit:
    case SNil{}:
      emptyE(k, s, tt.sym(ABNF.check(k, ABNF.string.case_sensitive(SNil{}), s), ABNF.check(k, ABNF.empty, s), ABNF.string.case_sensitive.nil(k, s), h))
    case SCon{+c, +t}:
      seqE2({s == SCon{c, t} : String}, k, ABNF.char(c), ABNF.string.case_sensitive(t), s, tt.sym(ABNF.check(k, ABNF.string.case_sensitive(SCon{c, t}), s), ABNF.check(k, ABNF.seq([ABNF.char(c), ABNF.string.case_sensitive(t)]), s), ABNF.string.case_sensitive.con(k, c, t, s), h), +a => +b => +e => +ha => +hb =>
        one({s == SCon{c, t} : String}, k, ABNF.char(c), a, ha, ABNF.char.nil(k, c), x => y => z => ABNF.char.many(k, c, x, y, z), +x => +ex => +hx =>
          csE.go(c, t, x, a, b, s, e, ex, tt.sym(ABNF.check(k, ABNF.char(c), SCon{x, SNil{}}), Char.is_eq(c, x), ABNF.char.one(k, c, x), hx), csE(k, t, b, hb))))

def csI(+k: ABNF.Book, lit: String) -> {ABNF.check(k, ABNF.string.case_sensitive(lit), lit) == True{} : Bool}:
  match lit:
    case SNil{}:
      tt(ABNF.check(k, ABNF.string.case_sensitive(SNil{}), SNil{}), ABNF.check(k, ABNF.empty, SNil{}), ABNF.string.case_sensitive.nil(k, SNil{}), ABNF.empty.nil(k))
    case SCon{+c, +t}:
      tt(ABNF.check(k, ABNF.string.case_sensitive(SCon{c, t}), SCon{c, t}), ABNF.check(k, ABNF.seq([ABNF.char(c), ABNF.string.case_sensitive(t)]), SCon{c, t}), ABNF.string.case_sensitive.con(k, c, t, SCon{c, t}),
        seqI2(k, ABNF.char(c), ABNF.string.case_sensitive(t), SCon{c, SNil{}}, t, tt(ABNF.check(k, ABNF.char(c), SCon{c, SNil{}}), Char.is_eq(c, c), ABNF.char.one(k, c, c), char_refl(c)), csI(k, t)))

# Single characters
# =================

def charM.go(+ch: Char, -s: String, +x: Char, +ex: {SCon{x, SNil{}} == s : String}, +hx: {ABNF.check(BK, ABNF.char(ch), SCon{x, SNil{}}) == True{} : Bool}) -> {s == SCon{ch, SNil{}} : String}:
  %Equal.sym(String, s, SCon{x, SNil{}}, Equal.sym(String, SCon{x, SNil{}}, s, ex)) : {_ == SCon{ch, SNil{}} : String}
  %char_eq(ch, x, tt.sym(ABNF.check(BK, ABNF.char(ch), SCon{x, SNil{}}), Char.is_eq(ch, x), ABNF.char.one(BK, ch, x), hx)) : {SCon{_, SNil{}} == SCon{ch, SNil{}} : String}
  {==}

# A rule that is one character matches exactly that character.
def charM(+N: String, +ch: Char, +s: String, +e: {gsel(GRAMMAR, N) == [ABNF.char(ch)] : List<ABNF.Rule>}, +h: {ABNF.check(BK, ABNF.ref(N), s) == True{} : Bool}) -> {s == SCon{ch, SNil{}} : String}:
  one({s == SCon{ch, SNil{}} : String}, BK, ABNF.char(ch), s, MBe(N, ABNF.char(ch), s, e, h), ABNF.char.nil(BK, ch), x => y => z => ABNF.char.many(BK, ch, x, y, z), +x => +ex => +hx => charM.go(ch, s, x, ex, hx))

def unesc1(+k: ABNF.Book, +c: Char) -> {ABNF.check(k, B_unesc, SCon{c, SNil{}}) == isunesc(c) : Bool}:
  alt2(k, ABNF.range(Chr{32}, Chr{33}), [ABNF.range(Chr{35}, Chr{91}), ABNF.range(Chr{93}, Chr{1114111})], SCon{c, SNil{}}, inR(Chr{32}, Chr{33}, c), Bool.or(inR(Chr{35}, Chr{91}, c), Bool.or(inR(Chr{93}, Chr{1114111}, c), False{})), rg1(k, Chr{32}, Chr{33}, c),
    alt2(k, ABNF.range(Chr{35}, Chr{91}), [ABNF.range(Chr{93}, Chr{1114111})], SCon{c, SNil{}}, inR(Chr{35}, Chr{91}, c), Bool.or(inR(Chr{93}, Chr{1114111}, c), False{}), rg1(k, Chr{35}, Chr{91}, c),
      alt2(k, ABNF.range(Chr{93}, Chr{1114111}), [], SCon{c, SNil{}}, inR(Chr{93}, Chr{1114111}, c), False{}, rg1(k, Chr{93}, Chr{1114111}, c), ABNF.alt.nil(k, SCon{c, SNil{}}))))

def unesc0(+k: ABNF.Book) -> {ABNF.check(k, B_unesc, SNil{}) == False{} : Bool}:
  alt2(k, ABNF.range(Chr{32}, Chr{33}), [ABNF.range(Chr{35}, Chr{91}), ABNF.range(Chr{93}, Chr{1114111})], SNil{}, False{}, False{}, rg0(k, Chr{32}, Chr{33}),
    alt2(k, ABNF.range(Chr{35}, Chr{91}), [ABNF.range(Chr{93}, Chr{1114111})], SNil{}, False{}, False{}, rg0(k, Chr{35}, Chr{91}),
      alt2(k, ABNF.range(Chr{93}, Chr{1114111}), [], SNil{}, False{}, False{}, rg0(k, Chr{93}, Chr{1114111}), ABNF.alt.nil(k, SNil{}))))

def unesc2(+k: ABNF.Book, +a: Char, +b: Char, +t: String) -> {ABNF.check(k, B_unesc, SCon{a, SCon{b, t}}) == False{} : Bool}:
  alt2(k, ABNF.range(Chr{32}, Chr{33}), [ABNF.range(Chr{35}, Chr{91}), ABNF.range(Chr{93}, Chr{1114111})], SCon{a, SCon{b, t}}, False{}, False{}, rg2(k, Chr{32}, Chr{33}, a, b, t),
    alt2(k, ABNF.range(Chr{35}, Chr{91}), [ABNF.range(Chr{93}, Chr{1114111})], SCon{a, SCon{b, t}}, False{}, False{}, rg2(k, Chr{35}, Chr{91}, a, b, t),
      alt2(k, ABNF.range(Chr{93}, Chr{1114111}), [], SCon{a, SCon{b, t}}, False{}, False{}, rg2(k, Chr{93}, Chr{1114111}, a, b, t), ABNF.alt.nil(k, SCon{a, SCon{b, t}}))))

# An unescaped character is not a backslash.
def unesc_bs(+c: Char, +h: {isunesc(c) == True{} : Bool}) -> {Char.is_eq(c, '\\') == False{} : Bool}:
  bcase({Char.is_eq(c, '\\') == False{} : Bool}, Char.is_eq(c, '\\'),
    +k => Empty.absurd({Char.is_eq(c, '\\') == False{} : Bool}, false_ne_true(Equal.trans(Bool, False{}, isunesc(c), True{}, Equal.cong(Char, Bool, z => isunesc(z), '\\', c, Equal.sym(Char, c, '\\', char_eq(c, '\\', k))), h))),
    +k => k)

def unescM(-C: Type, +u: String, +h: {ABNF.check(BK, ABNF.ref("unescaped"), u) == True{} : Bool}, f: @c: Char -> {SCon{c, SNil{}} == u : String} -> {isunesc(c) == True{} : Bool} -> C) -> C:
  one(C, BK, B_unesc, u, MBe("unescaped", B_unesc, u, {==}, h), unesc0(BK), x => y => z => unesc2(BK, x, y, z), +c => +ec => +hc => f(c, ec, tt.sym(ABNF.check(BK, B_unesc, SCon{c, SNil{}}), isunesc(c), unesc1(BK, c), hc)))

# Comparisons
# ===========

def cmp_out(c1: Cmp, c2: Cmp, +h: {Bool.or(Cmp.is_lt(c1), Cmp.is_gt(c2)) == True{} : Bool}) -> {Bool.and(Cmp.is_ge(c1), Cmp.is_le(c2)) == False{} : Bool}:
  match c1 c2:
    case LT{} c2:
      {==}
    case EQ{} LT{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case EQ{} EQ{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case EQ{} GT{}:
      {==}
    case GT{} LT{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case GT{} EQ{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case GT{} GT{}:
      {==}

# Lookup and decoding laws
# ========================

def Laws.lookup.nil(key):
  {==}

def Laws.lookup.hit(key, v, rest):
  %Equal.sym(Bool, String.eq(key, key), True{}, str_refl(key)) : {sel(Maybe<Js>, _, u => Some{v}, u => lk(rest, key)) == Some{v} : Maybe<Js>}
  {==}

def Laws.lookup.miss(k, v, rest, key, h):
  %Equal.sym(Bool, String.eq(k, key), False{}, h) : {sel(Maybe<Js>, _, u => Some{v}, u => lk(rest, key)) == lk(rest, key) : Maybe<Js>}
  {==}

def Laws.field.none(j, key, h):
  %Equal.sym(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, Laws.object(j), None{}, h) : {fieldM(_, key) == None{} : Maybe<Js>}
  {==}

def Laws.field.some(j, key, ms, h):
  %Equal.sym(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, Laws.object(j), Some{ms}, h) : {fieldM(_, key) == lk(ms, key) : Maybe<Js>}
  {==}

def Laws.decode.nil():
  {==}

def dec_unesc(+c: Char, -t: String, +h: {isunesc(c) == True{} : Bool}) -> {dec(SCon{c, t}, DN{}, None{}) == SCon{c, dec(t, DN{}, None{})} : String}:
  selF(String, Char.is_eq(c, '\\'), u => dec(t, DE{}, None{}), u => emit(None{}, SCon{c, dec(t, DN{}, None{})}), unesc_bs(c, h))

def decU(+c: Char, -u: String, -t: String, +ec: {SCon{c, SNil{}} == u : String}, +hc: {isunesc(c) == True{} : Bool}) -> {dec(String.append(u, t), DN{}, None{}) == String.append(u, dec(t, DN{}, None{})) : String}:
  %ec : {dec(String.append(_, t), DN{}, None{}) == String.append(_, dec(t, DN{}, None{})) : String}
  dec_unesc(c, t, hc)

def unescMM(-C: Type, +u: String, +h: {ABNF.matches(Laws.grammar, "unescaped", u) == True{} : Bool}, f: @c: Char -> {SCon{c, SNil{}} == u : String} -> {isunesc(c) == True{} : Bool} -> C) -> C:
  unescM(C, u, mt("unescaped", u, h), f)

def charMM(+N: String, +ch: Char, +s: String, +e: {gsel(GRAMMAR, N) == [ABNF.char(ch)] : List<ABNF.Rule>}, +h: {ABNF.matches(Laws.grammar, N, s) == True{} : Bool}) -> {s == SCon{ch, SNil{}} : String}:
  charM(N, ch, s, e, mt(N, s, h))

def Laws.decode.unescaped(u, t, h):
  unescMM({dec(String.append(u, t), DN{}, None{}) == String.append(u, dec(t, DN{}, None{})) : String}, u, h, +c => +ec => +hc => decU(c, u, t, ec, hc))

def is4(n: Nat) -> Bool:
  Nat.is_eq(n, 4n)

def fpreT(+v: U32, +h: {hi(v) == True{} : Bool}) -> {fpre(v) == SNil{} : String}:
  selT(String, hi(v), u => SNil{}, u => SCon{Chr{v}, SNil{}}, h)

def fpreF(+v: U32, +h: {hi(v) == False{} : Bool}) -> {fpre(v) == SCon{Chr{v}, SNil{}} : String}:
  selF(String, hi(v), u => SNil{}, u => SCon{Chr{v}, SNil{}}, h)

def fnpT(+v: U32, +h: {hi(v) == True{} : Bool}) -> {fnp(v) == Some{v} : Maybe<&2, U32>}:
  selT(Maybe<&2, U32>, hi(v), u => Some{v}, u => None{}, h)

def fnpF(+v: U32, +h: {hi(v) == False{} : Bool}) -> {fnp(v) == None{} : Maybe<&2, U32>}:
  selF(Maybe<&2, U32>, hi(v), u => Some{v}, u => None{}, h)

# After \uXXXX, dec writes pre and keeps np pending.
def decX(+a: Char, +b: Char, +c: Char, +d: Char, -t: String, +p: Maybe<&2, U32>, +hx: {Extra.is_hex(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}) == True{} : Bool})
  -> {dec(SCon{'\\', SCon{'u', SCon{a, SCon{b, SCon{c, SCon{d, t}}}}}}, DN{}, p) == String.append(pre(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), p), dec(t, DN{}, np(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), p))) : String}:
  selT(String, Extra.is_hex(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}), u => String.append(pre(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), p), dec(t, DN{}, np(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), p))), u => emit(p, SCon{'\\', SCon{'u', String.append(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, dec(t, DN{}, None{}))}}), hx)

def escM(+e: String, +he: {ABNF.check(BK, ABNF.ref("escape"), e) == True{} : Bool}) -> {SCon{'\\', SNil{}} == e : String}:
  Equal.sym(String, e, SCon{'\\', SNil{}}, charM("escape", '\\', e, {==}, he))

def escMM(+e: String, +he: {ABNF.matches(Laws.grammar, "escape", e) == True{} : Bool}) -> {SCon{'\\', SNil{}} == e : String}:
  escM(e, mt("escape", e, he))

def Laws.decode.quotation_mark(e, q, t, he, hq):
  %escMM(e, he) : {dec(String.append(_, String.append(q, t)), DN{}, None{}) == String.append(q, dec(t, DN{}, None{})) : String}
  %Equal.sym(String, q, SCon{'"', SNil{}}, charMM("quotation-mark", '"', q, {==}, hq)) : {dec(SCon{'\\', String.append(_, t)}, DN{}, None{}) == String.append(_, dec(t, DN{}, None{})) : String}
  {==}

def Laws.decode.escape(e, t, he):
  %escMM(e, he) : {dec(String.append(_, String.append(_, t)), DN{}, None{}) == String.append(_, dec(t, DN{}, None{})) : String} & {dec(String.append(_, String.append("/", t)), DN{}, None{}) == String.append("/", dec(t, DN{}, None{})) : String} & {dec(String.append(_, String.append("b", t)), DN{}, None{}) == SCon{Chr{8}, dec(t, DN{}, None{})} : String} & {dec(String.append(_, String.append("f", t)), DN{}, None{}) == SCon{Chr{12}, dec(t, DN{}, None{})} : String} & {dec(String.append(_, String.append("n", t)), DN{}, None{}) == SCon{Chr{10}, dec(t, DN{}, None{})} : String} & {dec(String.append(_, String.append("r", t)), DN{}, None{}) == SCon{Chr{13}, dec(t, DN{}, None{})} : String} & {dec(String.append(_, String.append("t", t)), DN{}, None{}) == SCon{Chr{9}, dec(t, DN{}, None{})} : String}
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

def decu.go(+a: Char, +b: Char, +c: Char, +d: Char, -t: String, +hx: {Extra.is_hex(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}) == True{} : Bool}, +hs: {hi(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)) == False{} : Bool})
  -> {dec(SCon{'\\', SCon{'u', SCon{a, SCon{b, SCon{c, SCon{d, t}}}}}}, DN{}, None{}) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}:
  %Equal.sym(String, dec(SCon{'\\', SCon{'u', SCon{a, SCon{b, SCon{c, SCon{d, t}}}}}}, DN{}, None{}), String.append(pre(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), None{}), dec(t, DN{}, np(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), None{}))), decX(a, b, c, d, t, None{}, hx)) : {_ == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}
  %Equal.sym(String, fpre(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)), SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, SNil{}}, fpreF(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), hs)) : {String.append(_, dec(t, DN{}, fnp(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)))) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}
  %Equal.sym(Maybe<&2, U32>, fnp(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)), None{}, fnpF(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), hs)) : {String.append(SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, SNil{}}, dec(t, DN{}, _)) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}
  {==}

def decu(+e: String, +a: Char, +b: Char, +c: Char, +d: Char, -t: String, +he: {ABNF.check(BK, ABNF.ref("escape"), e) == True{} : Bool}, +hx: {Extra.is_hex(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}) == True{} : Bool}, +hs: {hi(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)) == False{} : Bool})
  -> {dec(String.append(e, String.append("u", String.append(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, t))), DN{}, None{}) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}:
  %escM(e, he) : {dec(String.append(_, String.append("u", String.append(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, t))), DN{}, None{}) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}
  decu.go(a, b, c, d, t, hx, hs)

def len4(-C: Type, x: String, +lx: {String.length(x) == 4n : Nat}, f: @a: Char -> @b: Char -> @c: Char -> @d: Char -> {SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}} == x : String} -> C) -> C:
  match x:
    case SNil{}:
      Empty.absurd(C, false_ne_true(Equal.cong(Nat, Bool, is4, String.length(SNil{}), 4n, lx)))
    case SCon{a, SNil{}}:
      Empty.absurd(C, false_ne_true(Equal.cong(Nat, Bool, is4, String.length(SCon{a, SNil{}}), 4n, lx)))
    case SCon{a, SCon{b, SNil{}}}:
      Empty.absurd(C, false_ne_true(Equal.cong(Nat, Bool, is4, String.length(SCon{a, SCon{b, SNil{}}}), 4n, lx)))
    case SCon{a, SCon{b, SCon{c, SNil{}}}}:
      Empty.absurd(C, false_ne_true(Equal.cong(Nat, Bool, is4, String.length(SCon{a, SCon{b, SCon{c, SNil{}}}}), 4n, lx)))
    case SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}:
      f(a, b, c, d, {==})
    case SCon{a, SCon{b, SCon{c, SCon{d, SCon{e, r}}}}}:
      Empty.absurd(C, false_ne_true(Equal.cong(Nat, Bool, is4, String.length(SCon{a, SCon{b, SCon{c, SCon{d, SCon{e, r}}}}}), 4n, lx)))

def decu2(+e: String, -x: String, -t: String, +a: Char, +b: Char, +c: Char, +d: Char, +ex: {SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}} == x : String}, +he: {ABNF.matches(Laws.grammar, "escape", e) == True{} : Bool},
  +hx: {Extra.is_hex(x) == True{} : Bool}, +hs: {Bool.or(U32.is_lt(EP.hexv(x, 0), 55296), U32.is_gt(EP.hexv(x, 0), 56319)) == True{} : Bool})
  -> {dec(String.append(e, String.append("u", String.append(x, t))), DN{}, None{}) == SCon{Chr{EP.hexv(x, 0)}, dec(t, DN{}, None{})} : String}:
  %ex : {dec(String.append(e, String.append("u", String.append(_, t))), DN{}, None{}) == SCon{Chr{EP.hexv(_, 0)}, dec(t, DN{}, None{})} : String}
  decu(e, a, b, c, d, t, mt("escape", e, he), Equal.trans(Bool, Extra.is_hex(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}), Extra.is_hex(x), True{}, Equal.cong(String, Bool, z => Extra.is_hex(z), SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, x, ex), hx),
    cmp_out(U32.cmp(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), 55296), U32.cmp(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), 56319), Equal.trans(Bool, Bool.or(U32.is_lt(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), 55296), U32.is_gt(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), 56319)), Bool.or(U32.is_lt(EP.hexv(x, 0), 55296), U32.is_gt(EP.hexv(x, 0), 56319)), True{}, Equal.cong(String, Bool, z => Bool.or(U32.is_lt(EP.hexv(z, 0), 55296), U32.is_gt(EP.hexv(z, 0), 56319)), SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, x, ex), hs)))

def Laws.decode.u(e, x, t, he, hx, lx, hs):
  len4({dec(String.append(e, String.append("u", String.append(x, t))), DN{}, None{}) == SCon{Chr{EP.hexv(x, 0)}, dec(t, DN{}, None{})} : String}, x, lx,
    +a => +b => +c => +d => +ex => decu2(e, x, t, a, b, c, d, ex, he, hx, hs))

def decp(+e: String, +a1: Char, +b1: Char, +c1: Char, +d1: Char, +a2: Char, +b2: Char, +c2: Char, +d2: Char, -t: String, +he: {ABNF.check(BK, ABNF.ref("escape"), e) == True{} : Bool},
  +hx1: {Extra.is_hex(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}) == True{} : Bool}, +hx2: {Extra.is_hex(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}) == True{} : Bool}, +hs1: {hi(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)) == True{} : Bool}, +hs2: {lo(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)) == True{} : Bool})
  -> {dec(String.append(e, String.append("u", String.append(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, String.append(e, String.append("u", String.append(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, t)))))), DN{}, None{}) == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, None{})} : String}:
  %escM(e, he) : {dec(String.append(_, String.append("u", String.append(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, String.append(_, String.append("u", String.append(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, t)))))), DN{}, None{}) == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, None{})} : String}
  %Equal.sym(String, dec(SCon{'\\', SCon{'u', SCon{a1, SCon{b1, SCon{c1, SCon{d1, SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}}}}}}}, DN{}, None{}), String.append(pre(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), None{}), dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, np(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), None{}))), decX(a1, b1, c1, d1, SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, None{}, hx1)) : {_ == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, None{})} : String}
  %Equal.sym(String, fpre(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)), SNil{}, fpreT(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), hs1)) : {String.append(_, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, fnp(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)))) == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, None{})} : String}
  %Equal.sym(Maybe<&2, U32>, fnp(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, fnpT(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), hs1)) : {String.append(SNil{}, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, _)) == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, None{})} : String}
  %Equal.sym(String, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}), String.append(pre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}), dec(t, DN{}, np(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}))), decX(a2, b2, c2, d2, t, Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, hx2)) : {_ == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, None{})} : String}
  %Equal.sym(String, pre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}), SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, SNil{}}, selT(String, lo(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)), u => SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, SNil{}}, u => SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, fpre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, hs2)) : {String.append(_, dec(t, DN{}, np(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}))) == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, None{})} : String}
  %Equal.sym(Maybe<&2, U32>, np(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}), None{}, selT(Maybe<&2, U32>, lo(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)), u => None{}, u => fnp(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)), hs2)) : {String.append(SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, SNil{}}, dec(t, DN{}, _)) == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, None{})} : String}
  {==}

def decp2(+e: String, -x1: String, -x2: String, -t: String, +a1: Char, +b1: Char, +c1: Char, +d1: Char, +ex1: {SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}} == x1 : String}, +a2: Char, +b2: Char, +c2: Char, +d2: Char, +ex2: {SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}} == x2 : String},
  +he: {ABNF.matches(Laws.grammar, "escape", e) == True{} : Bool}, +hx1: {Extra.is_hex(x1) == True{} : Bool}, +hx2: {Extra.is_hex(x2) == True{} : Bool},
  +hs1: {Bool.and(U32.is_ge(EP.hexv(x1, 0), 55296), U32.is_le(EP.hexv(x1, 0), 56319)) == True{} : Bool}, +hs2: {Bool.and(U32.is_ge(EP.hexv(x2, 0), 56320), U32.is_le(EP.hexv(x2, 0), 57343)) == True{} : Bool})
  -> {dec(String.append(e, String.append("u", String.append(x1, String.append(e, String.append("u", String.append(x2, t)))))), DN{}, None{}) == SCon{Chr{pair(EP.hexv(x1, 0), EP.hexv(x2, 0))}, dec(t, DN{}, None{})} : String}:
  %ex1 : {dec(String.append(e, String.append("u", String.append(_, String.append(e, String.append("u", String.append(x2, t)))))), DN{}, None{}) == SCon{Chr{pair(EP.hexv(_, 0), EP.hexv(x2, 0))}, dec(t, DN{}, None{})} : String}
  %ex2 : {dec(String.append(e, String.append("u", String.append(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, String.append(e, String.append("u", String.append(_, t)))))), DN{}, None{}) == SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(_, 0))}, dec(t, DN{}, None{})} : String}
  decp(e, a1, b1, c1, d1, a2, b2, c2, d2, t, mt("escape", e, he), Equal.trans(Bool, Extra.is_hex(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}), Extra.is_hex(x1), True{}, Equal.cong(String, Bool, z => Extra.is_hex(z), SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, x1, ex1), hx1), Equal.trans(Bool, Extra.is_hex(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}), Extra.is_hex(x2), True{}, Equal.cong(String, Bool, z => Extra.is_hex(z), SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, x2, ex2), hx2),
    Equal.trans(Bool, Bool.and(U32.is_ge(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), 55296), U32.is_le(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), 56319)), Bool.and(U32.is_ge(EP.hexv(x1, 0), 55296), U32.is_le(EP.hexv(x1, 0), 56319)), True{}, Equal.cong(String, Bool, z => Bool.and(U32.is_ge(EP.hexv(z, 0), 55296), U32.is_le(EP.hexv(z, 0), 56319)), SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, x1, ex1), hs1), Equal.trans(Bool, Bool.and(U32.is_ge(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), 56320), U32.is_le(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), 57343)), Bool.and(U32.is_ge(EP.hexv(x2, 0), 56320), U32.is_le(EP.hexv(x2, 0), 57343)), True{}, Equal.cong(String, Bool, z => Bool.and(U32.is_ge(EP.hexv(z, 0), 56320), U32.is_le(EP.hexv(z, 0), 57343)), SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, x2, ex2), hs2))

def Laws.decode.pair(e, x1, x2, t, he, hx1, lx1, hx2, lx2, hs1, hs2):
  len4({dec(String.append(e, String.append("u", String.append(x1, String.append(e, String.append("u", String.append(x2, t)))))), DN{}, None{}) == SCon{Chr{pair(EP.hexv(x1, 0), EP.hexv(x2, 0))}, dec(t, DN{}, None{})} : String}, x1, lx1,
    +a1 => +b1 => +c1 => +d1 => +ex1 =>
      len4({dec(String.append(e, String.append("u", String.append(x1, String.append(e, String.append("u", String.append(x2, t)))))), DN{}, None{}) == SCon{Chr{pair(EP.hexv(x1, 0), EP.hexv(x2, 0))}, dec(t, DN{}, None{})} : String}, x2, lx2,
        +a2 => +b2 => +c2 => +d2 => +ex2 => decp2(e, x1, x2, t, a1, b1, c1, d1, ex1, a2, b2, c2, d2, ex2, he, hx1, hx2, hs1, hs2)))

def pendF(+c: Char, -t1: String, +v: U32, +k: {Char.is_eq(c, '\\') == False{} : Bool}) -> {dec(SCon{c, t1}, DN{}, Some{v}) == SCon{Chr{v}, dec(SCon{c, t1}, DN{}, None{})} : String}:
  %Equal.sym(String, dec(SCon{c, t1}, DN{}, Some{v}), emit(Some{v}, SCon{c, dec(t1, DN{}, None{})}), selF(String, Char.is_eq(c, '\\'), u => dec(t1, DE{}, Some{v}), u => emit(Some{v}, SCon{c, dec(t1, DN{}, None{})}), k)) : {_ == SCon{Chr{v}, dec(SCon{c, t1}, DN{}, None{})} : String}
  %Equal.sym(String, dec(SCon{c, t1}, DN{}, None{}), emit(None{}, SCon{c, dec(t1, DN{}, None{})}), selF(String, Char.is_eq(c, '\\'), u => dec(t1, DE{}, None{}), u => emit(None{}, SCon{c, dec(t1, DN{}, None{})}), k)) : {emit(Some{v}, SCon{c, dec(t1, DN{}, None{})}) == SCon{Chr{v}, _} : String}
  {==}

def pendU(+c2: Char, -t2: String, +h: {String.starts_with.go.if(SNil{}, t2, Char.is_eq(c2, 'u')) == False{} : Bool}) -> {Char.is_eq(c2, 'u') == False{} : Bool}:
  bcase({Char.is_eq(c2, 'u') == False{} : Bool}, Char.is_eq(c2, 'u'),
    +k => Empty.absurd({Char.is_eq(c2, 'u') == False{} : Bool}, false_ne_true(Equal.trans(Bool, False{}, String.starts_with.go.if(SNil{}, t2, Char.is_eq(c2, 'u')), True{}, Equal.sym(Bool, String.starts_with.go.if(SNil{}, t2, Char.is_eq(c2, 'u')), False{}, h), Equal.cong(Bool, Bool, z => String.starts_with.go.if(SNil{}, t2, z), Char.is_eq(c2, 'u'), True{}, k)))),
    +k => k)

def pendE.s(+c2: Char, -t2: String, +v: U32, +ks: {issimple(c2) == True{} : Bool}) -> {dec(SCon{c2, t2}, DE{}, Some{v}) == SCon{Chr{v}, dec(SCon{c2, t2}, DE{}, None{})} : String}:
  %Equal.sym(String, dec(SCon{c2, t2}, DE{}, Some{v}), emit(Some{v}, SCon{esc(c2), dec(t2, DN{}, None{})}), selT(String, issimple(c2), u => emit(Some{v}, SCon{esc(c2), dec(t2, DN{}, None{})}), u => sel(String, Char.is_eq(c2, 'u'), u => dec(t2, DU{SNil{}}, Some{v}), u => emit(Some{v}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}})), ks)) : {_ == SCon{Chr{v}, dec(SCon{c2, t2}, DE{}, None{})} : String}
  %Equal.sym(String, dec(SCon{c2, t2}, DE{}, None{}), emit(None{}, SCon{esc(c2), dec(t2, DN{}, None{})}), selT(String, issimple(c2), u => emit(None{}, SCon{esc(c2), dec(t2, DN{}, None{})}), u => sel(String, Char.is_eq(c2, 'u'), u => dec(t2, DU{SNil{}}, None{}), u => emit(None{}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}})), ks)) : {emit(Some{v}, SCon{esc(c2), dec(t2, DN{}, None{})}) == SCon{Chr{v}, _} : String}
  {==}

def pendE.o(+c2: Char, -t2: String, +v: U32, +ks: {issimple(c2) == False{} : Bool}, +hu: {Char.is_eq(c2, 'u') == False{} : Bool}) -> {dec(SCon{c2, t2}, DE{}, Some{v}) == SCon{Chr{v}, dec(SCon{c2, t2}, DE{}, None{})} : String}:
  %Equal.sym(String, dec(SCon{c2, t2}, DE{}, Some{v}), sel(String, Char.is_eq(c2, 'u'), u => dec(t2, DU{SNil{}}, Some{v}), u => emit(Some{v}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}})), selF(String, issimple(c2), u => emit(Some{v}, SCon{esc(c2), dec(t2, DN{}, None{})}), u => sel(String, Char.is_eq(c2, 'u'), u => dec(t2, DU{SNil{}}, Some{v}), u => emit(Some{v}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}})), ks)) : {_ == SCon{Chr{v}, dec(SCon{c2, t2}, DE{}, None{})} : String}
  %Equal.sym(String, dec(SCon{c2, t2}, DE{}, None{}), sel(String, Char.is_eq(c2, 'u'), u => dec(t2, DU{SNil{}}, None{}), u => emit(None{}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}})), selF(String, issimple(c2), u => emit(None{}, SCon{esc(c2), dec(t2, DN{}, None{})}), u => sel(String, Char.is_eq(c2, 'u'), u => dec(t2, DU{SNil{}}, None{}), u => emit(None{}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}})), ks)) : {sel(String, Char.is_eq(c2, 'u'), u => dec(t2, DU{SNil{}}, Some{v}), u => emit(Some{v}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}})) == SCon{Chr{v}, _} : String}
  %Equal.sym(Bool, Char.is_eq(c2, 'u'), False{}, hu) : {sel(String, _, u => dec(t2, DU{SNil{}}, Some{v}), u => emit(Some{v}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}})) == SCon{Chr{v}, sel(String, _, u => dec(t2, DU{SNil{}}, None{}), u => emit(None{}, SCon{'\\', SCon{c2, dec(t2, DN{}, None{})}}))} : String}
  {==}

def pendBS(t1: String, +v: U32, +h: {String.starts_with(SCon{'\\', t1}, "\\u") == False{} : Bool}) -> {dec(t1, DE{}, Some{v}) == SCon{Chr{v}, dec(t1, DE{}, None{})} : String}:
  match t1:
    case SNil{}:
      {==}
    case SCon{+c2, +t2}:
      bcase({dec(SCon{c2, t2}, DE{}, Some{v}) == SCon{Chr{v}, dec(SCon{c2, t2}, DE{}, None{})} : String}, issimple(c2),
        +ks => pendE.s(c2, t2, v, ks),
        +ks => pendE.o(c2, t2, v, ks, pendU(c2, t2, h)))

def pendT(+c: Char, +t1: String, +v: U32, +k: {Char.is_eq(c, '\\') == True{} : Bool}, +h: {String.starts_with(SCon{c, t1}, "\\u") == False{} : Bool}) -> {dec(SCon{c, t1}, DN{}, Some{v}) == SCon{Chr{v}, dec(SCon{c, t1}, DN{}, None{})} : String}:
  %Equal.sym(Char, c, '\\', char_eq(c, '\\', k)) : {dec(SCon{_, t1}, DN{}, Some{v}) == SCon{Chr{v}, dec(SCon{_, t1}, DN{}, None{})} : String}
  pendBS(t1, v, Equal.trans(Bool, String.starts_with(SCon{'\\', t1}, "\\u"), String.starts_with(SCon{c, t1}, "\\u"), False{}, Equal.cong(Char, Bool, z => String.starts_with(SCon{z, t1}, "\\u"), '\\', c, Equal.sym(Char, c, '\\', char_eq(c, '\\', k))), h))

# A pending high surrogate is written as is, unless a \u follows.
def pend(t: String, +v: U32, +h: {String.starts_with(t, "\\u") == False{} : Bool}) -> {dec(t, DN{}, Some{v}) == SCon{Chr{v}, dec(t, DN{}, None{})} : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +t1}:
      bcase({dec(SCon{c, t1}, DN{}, Some{v}) == SCon{Chr{v}, dec(SCon{c, t1}, DN{}, None{})} : String}, Char.is_eq(c, '\\'),
        +k => pendT(c, t1, v, k, h),
        +k => pendF(c, t1, v, k))

def dech(+e: String, +a: Char, +b: Char, +c: Char, +d: Char, +t: String, +he: {ABNF.check(BK, ABNF.ref("escape"), e) == True{} : Bool},
  +hx: {Extra.is_hex(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}) == True{} : Bool}, +hs: {hi(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)) == True{} : Bool}, +ht: {String.starts_with(t, String.append(e, "u")) == False{} : Bool})
  -> {dec(String.append(e, String.append("u", String.append(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, t))), DN{}, None{}) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}:
  %escM(e, he) : {dec(String.append(_, String.append("u", String.append(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, t))), DN{}, None{}) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}
  %Equal.sym(String, dec(SCon{'\\', SCon{'u', SCon{a, SCon{b, SCon{c, SCon{d, t}}}}}}, DN{}, None{}), String.append(pre(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), None{}), dec(t, DN{}, np(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), None{}))), decX(a, b, c, d, t, None{}, hx)) : {_ == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}
  %Equal.sym(String, fpre(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)), SNil{}, fpreT(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), hs)) : {String.append(_, dec(t, DN{}, fnp(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)))) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}
  %Equal.sym(Maybe<&2, U32>, fnp(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)), Some{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, fnpT(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), hs)) : {String.append(SNil{}, dec(t, DN{}, _)) == SCon{Chr{EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0)}, dec(t, DN{}, None{})} : String}
  pend(t, EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), Equal.trans(Bool, String.starts_with(t, "\\u"), String.starts_with(t, String.append(e, "u")), False{}, Equal.cong(String, Bool, z => String.starts_with(t, String.append(z, "u")), SCon{'\\', SNil{}}, e, escM(e, he)), ht))

def dech2(+e: String, -x: String, +t: String, +a: Char, +b: Char, +c: Char, +d: Char, +ex: {SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}} == x : String}, +he: {ABNF.matches(Laws.grammar, "escape", e) == True{} : Bool},
  +hx: {Extra.is_hex(x) == True{} : Bool}, +hs: {Bool.and(U32.is_ge(EP.hexv(x, 0), 55296), U32.is_le(EP.hexv(x, 0), 56319)) == True{} : Bool}, +ht: {String.starts_with(t, String.append(e, "u")) == False{} : Bool})
  -> {dec(String.append(e, String.append("u", String.append(x, t))), DN{}, None{}) == SCon{Chr{EP.hexv(x, 0)}, dec(t, DN{}, None{})} : String}:
  %ex : {dec(String.append(e, String.append("u", String.append(_, t))), DN{}, None{}) == SCon{Chr{EP.hexv(_, 0)}, dec(t, DN{}, None{})} : String}
  dech(e, a, b, c, d, t, mt("escape", e, he), Equal.trans(Bool, Extra.is_hex(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}), Extra.is_hex(x), True{}, Equal.cong(String, Bool, z => Extra.is_hex(z), SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, x, ex), hx), Equal.trans(Bool, Bool.and(U32.is_ge(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), 55296), U32.is_le(EP.hexv(SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, 0), 56319)), Bool.and(U32.is_ge(EP.hexv(x, 0), 55296), U32.is_le(EP.hexv(x, 0), 56319)), True{}, Equal.cong(String, Bool, z => Bool.and(U32.is_ge(EP.hexv(z, 0), 55296), U32.is_le(EP.hexv(z, 0), 56319)), SCon{a, SCon{b, SCon{c, SCon{d, SNil{}}}}}, x, ex), hs), ht)

def Laws.decode.high(e, x, t, he, hx, lx, hs, ht):
  len4({dec(String.append(e, String.append("u", String.append(x, t))), DN{}, None{}) == SCon{Chr{EP.hexv(x, 0)}, dec(t, DN{}, None{})} : String}, x, lx,
    +a => +b => +c => +d => +ex => dech2(e, x, t, a, b, c, d, ex, he, hx, hs, ht))

def dechu(+e: String, +a1: Char, +b1: Char, +c1: Char, +d1: Char, +a2: Char, +b2: Char, +c2: Char, +d2: Char, -t: String, +he: {ABNF.check(BK, ABNF.ref("escape"), e) == True{} : Bool},
  +hx1: {Extra.is_hex(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}) == True{} : Bool}, +hx2: {Extra.is_hex(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}) == True{} : Bool}, +hs1: {hi(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)) == True{} : Bool}, +hs2: {lo(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)) == False{} : Bool})
  -> {dec(String.append(e, String.append("u", String.append(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, String.append(e, String.append("u", String.append(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, t)))))), DN{}, None{}) == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(String.append(e, String.append("u", String.append(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, t))), DN{}, None{})} : String}:
  %escM(e, he) : {dec(String.append(_, String.append("u", String.append(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, String.append(_, String.append("u", String.append(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, t)))))), DN{}, None{}) == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(String.append(_, String.append("u", String.append(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, t))), DN{}, None{})} : String}
  %Equal.sym(String, dec(SCon{'\\', SCon{'u', SCon{a1, SCon{b1, SCon{c1, SCon{d1, SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}}}}}}}, DN{}, None{}), String.append(pre(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), None{}), dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, np(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), None{}))), decX(a1, b1, c1, d1, SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, None{}, hx1)) : {_ == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, None{})} : String}
  %Equal.sym(String, fpre(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)), SNil{}, fpreT(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), hs1)) : {String.append(_, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, fnp(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)))) == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, None{})} : String}
  %Equal.sym(Maybe<&2, U32>, fnp(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, fnpT(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), hs1)) : {String.append(SNil{}, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, _)) == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, None{})} : String}
  %Equal.sym(String, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}), String.append(pre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}), dec(t, DN{}, np(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}))), decX(a2, b2, c2, d2, t, Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, hx2)) : {_ == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, None{})} : String}
  %Equal.sym(String, pre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}), SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, fpre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, selF(String, lo(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)), u => SCon{Chr{pair(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, SNil{}}, u => SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, fpre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, hs2)) : {String.append(_, dec(t, DN{}, np(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}))) == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, None{})} : String}
  %Equal.sym(Maybe<&2, U32>, np(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), Some{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}), fnp(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)), selF(Maybe<&2, U32>, lo(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)), u => None{}, u => fnp(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)), hs2)) : {String.append(SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, fpre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, _)) == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, None{})} : String}
  %Equal.sym(String, dec(SCon{'\\', SCon{'u', SCon{a2, SCon{b2, SCon{c2, SCon{d2, t}}}}}}, DN{}, None{}), String.append(pre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), None{}), dec(t, DN{}, np(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), None{}))), decX(a2, b2, c2, d2, t, None{}, hx2)) : {String.append(SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, fpre(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0))}, dec(t, DN{}, fnp(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0)))) == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, _} : String}
  {==}

def dechu2(+e: String, -x1: String, -x2: String, -t: String, +a1: Char, +b1: Char, +c1: Char, +d1: Char, +ex1: {SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}} == x1 : String}, +a2: Char, +b2: Char, +c2: Char, +d2: Char, +ex2: {SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}} == x2 : String},
  +he: {ABNF.matches(Laws.grammar, "escape", e) == True{} : Bool}, +hx1: {Extra.is_hex(x1) == True{} : Bool}, +hx2: {Extra.is_hex(x2) == True{} : Bool},
  +hs1: {Bool.and(U32.is_ge(EP.hexv(x1, 0), 55296), U32.is_le(EP.hexv(x1, 0), 56319)) == True{} : Bool}, +hs2: {Bool.or(U32.is_lt(EP.hexv(x2, 0), 56320), U32.is_gt(EP.hexv(x2, 0), 57343)) == True{} : Bool})
  -> {dec(String.append(e, String.append("u", String.append(x1, String.append(e, String.append("u", String.append(x2, t)))))), DN{}, None{}) == SCon{Chr{EP.hexv(x1, 0)}, dec(String.append(e, String.append("u", String.append(x2, t))), DN{}, None{})} : String}:
  %ex1 : {dec(String.append(e, String.append("u", String.append(_, String.append(e, String.append("u", String.append(x2, t)))))), DN{}, None{}) == SCon{Chr{EP.hexv(_, 0)}, dec(String.append(e, String.append("u", String.append(x2, t))), DN{}, None{})} : String}
  %ex2 : {dec(String.append(e, String.append("u", String.append(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, String.append(e, String.append("u", String.append(_, t)))))), DN{}, None{}) == SCon{Chr{EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0)}, dec(String.append(e, String.append("u", String.append(_, t))), DN{}, None{})} : String}
  dechu(e, a1, b1, c1, d1, a2, b2, c2, d2, t, mt("escape", e, he), Equal.trans(Bool, Extra.is_hex(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}), Extra.is_hex(x1), True{}, Equal.cong(String, Bool, z => Extra.is_hex(z), SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, x1, ex1), hx1), Equal.trans(Bool, Extra.is_hex(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}), Extra.is_hex(x2), True{}, Equal.cong(String, Bool, z => Extra.is_hex(z), SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, x2, ex2), hx2),
    Equal.trans(Bool, Bool.and(U32.is_ge(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), 55296), U32.is_le(EP.hexv(SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, 0), 56319)), Bool.and(U32.is_ge(EP.hexv(x1, 0), 55296), U32.is_le(EP.hexv(x1, 0), 56319)), True{}, Equal.cong(String, Bool, z => Bool.and(U32.is_ge(EP.hexv(z, 0), 55296), U32.is_le(EP.hexv(z, 0), 56319)), SCon{a1, SCon{b1, SCon{c1, SCon{d1, SNil{}}}}}, x1, ex1), hs1),
    cmp_out(U32.cmp(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), 56320), U32.cmp(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), 57343), Equal.trans(Bool, Bool.or(U32.is_lt(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), 56320), U32.is_gt(EP.hexv(SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, 0), 57343)), Bool.or(U32.is_lt(EP.hexv(x2, 0), 56320), U32.is_gt(EP.hexv(x2, 0), 57343)), True{}, Equal.cong(String, Bool, z => Bool.or(U32.is_lt(EP.hexv(z, 0), 56320), U32.is_gt(EP.hexv(z, 0), 57343)), SCon{a2, SCon{b2, SCon{c2, SCon{d2, SNil{}}}}}, x2, ex2), hs2)))

def Laws.decode.high_u(e, x1, x2, t, he, hx1, lx1, hx2, lx2, hs1, hs2):
  len4({dec(String.append(e, String.append("u", String.append(x1, String.append(e, String.append("u", String.append(x2, t)))))), DN{}, None{}) == SCon{Chr{EP.hexv(x1, 0)}, dec(String.append(e, String.append("u", String.append(x2, t))), DN{}, None{})} : String}, x1, lx1,
    +a1 => +b1 => +c1 => +d1 => +ex1 =>
      len4({dec(String.append(e, String.append("u", String.append(x1, String.append(e, String.append("u", String.append(x2, t)))))), DN{}, None{}) == SCon{Chr{EP.hexv(x1, 0)}, dec(String.append(e, String.append("u", String.append(x2, t))), DN{}, None{})} : String}, x2, lx2,
        +a2 => +b2 => +c2 => +d2 => +ex2 => dechu2(e, x1, x2, t, a1, b1, c1, d1, ex1, a2, b2, c2, d2, ex2, he, hx1, hx2, hs1, hs2)))

# Numbers
# =======

# NS(m, s, R): if the scan m of s succeeds, it split s, and its text matches R.
def NS(m: Maybe<&2, SP>, s: String, R: ABNF.Rule) -> Type:
  match m:
    case None{}:
      Unit
    case Some{p}:
      {String.append(spa(p), spt(p)) == s : String} & {ABNF.check(BK, R, spa(p)) == True{} : Bool}

def NSmap(+c: Char, m: Maybe<&2, SP>, -t: String, -R2: ABNF.Rule, -R: ABNF.Rule, ns: NS(m, t, R2), f: @a: String -> {ABNF.check(BK, R2, a) == True{} : Bool} -> {ABNF.check(BK, R, SCon{c, a}) == True{} : Bool})
  -> NS(prepM(c, m), SCon{c, t}, R):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      (e, h) = ns
      (cons_eq(c, String.append(spa(p), spt(p)), t, e), f(spa(p), h))

def NSw(m: Maybe<&2, SP>, -s: String, -R2: ABNF.Rule, -R: ABNF.Rule, ns: NS(m, s, R2), f: @a: String -> {ABNF.check(BK, R2, a) == True{} : Bool} -> {ABNF.check(BK, R, a) == True{} : Bool})
  -> NS(m, s, R):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      (e, h) = ns
      (e, f(spa(p), h))

def NSapp(+d: String, m: Maybe<&2, SP>, -r: String, -s: String, -R2: ABNF.Rule, -R: ABNF.Rule, ns: NS(m, r, R2), +e: {String.append(d, r) == s : String},
  f: @a: String -> {ABNF.check(BK, R2, a) == True{} : Bool} -> {ABNF.check(BK, R, String.append(d, a)) == True{} : Bool}) -> NS(appM(d, m), s, R):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      (e2, h) = ns
      (Equal.trans(String, String.append(String.append(d, spa(p)), spt(p)), String.append(d, r), s,
        Equal.trans(String, String.append(String.append(d, spa(p)), spt(p)), String.append(d, String.append(spa(p), spt(p))), String.append(d, r), app3(d, spa(p), spt(p)), app_congl(d, String.append(spa(p), spt(p)), r, e2)), e),
       f(spa(p), h))

def digS1.t(+c: Char, +t: String, +h: {isdig(c) == True{} : Bool}, +ih: {String.append(spa(digits(t)), spt(digits(t))) == t : String}) -> {String.append(spa(digits(SCon{c, t})), spt(digits(SCon{c, t}))) == SCon{c, t} : String}:
  %Equal.sym(SP, digits(SCon{c, t}), prepS(c, digits(t)), selT(SP, isdig(c), u => prepS(c, digits(t)), u => SP{SNil{}, SCon{c, t}}, h)) : {String.append(spa(_), spt(_)) == SCon{c, t} : String}
  cons_eq(c, String.append(spa(digits(t)), spt(digits(t))), t, ih)

def digS1.f(+c: Char, +t: String, +h: {isdig(c) == False{} : Bool}) -> {String.append(spa(digits(SCon{c, t})), spt(digits(SCon{c, t}))) == SCon{c, t} : String}:
  %Equal.sym(SP, digits(SCon{c, t}), SP{SNil{}, SCon{c, t}}, selF(SP, isdig(c), u => prepS(c, digits(t)), u => SP{SNil{}, SCon{c, t}}, h)) : {String.append(spa(_), spt(_)) == SCon{c, t} : String}
  {==}

def digS1(s: String) -> {String.append(spa(digits(s)), spt(digits(s))) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      bcase({String.append(spa(digits(SCon{c, t})), spt(digits(SCon{c, t}))) == SCon{c, t} : String}, isdig(c),
        +h => digS1.t(c, t, h, digS1(t)),
        +h => digS1.f(c, t, h))

def dig1C(+c: Char, +h: {isdig(c) == True{} : Bool}) -> {ABNF.check(BK, DIG, SCon{c, SNil{}}) == True{} : Bool}:
  tt(ABNF.check(BK, DIG, SCon{c, SNil{}}), inR('0', '9', c), cd1(BK, c), h)

def digS2.t(+c: Char, +t: String, +h: {isdig(c) == True{} : Bool}, +ih: {ABNF.check(BK, ABNF.rep.any(DIG), spa(digits(t))) == True{} : Bool}) -> {ABNF.check(BK, ABNF.rep.any(DIG), spa(digits(SCon{c, t}))) == True{} : Bool}:
  %Equal.sym(SP, digits(SCon{c, t}), prepS(c, digits(t)), selT(SP, isdig(c), u => prepS(c, digits(t)), u => SP{SNil{}, SCon{c, t}}, h)) : {ABNF.check(BK, ABNF.rep.any(DIG), spa(_)) == True{} : Bool}
  starCons(BK, DIG, SCon{c, SNil{}}, spa(digits(t)), dig1C(c, h), ih)

def digS2.f(+c: Char, +t: String, +h: {isdig(c) == False{} : Bool}) -> {ABNF.check(BK, ABNF.rep.any(DIG), spa(digits(SCon{c, t}))) == True{} : Bool}:
  %Equal.sym(SP, digits(SCon{c, t}), SP{SNil{}, SCon{c, t}}, selF(SP, isdig(c), u => prepS(c, digits(t)), u => SP{SNil{}, SCon{c, t}}, h)) : {ABNF.check(BK, ABNF.rep.any(DIG), spa(_)) == True{} : Bool}
  starNil(BK, DIG)

def digS2(s: String) -> {ABNF.check(BK, ABNF.rep.any(DIG), spa(digits(s))) == True{} : Bool}:
  match s:
    case SNil{}:
      starNil(BK, DIG)
    case SCon{+c, +t}:
      bcase({ABNF.check(BK, ABNF.rep.any(DIG), spa(digits(SCon{c, t}))) == True{} : Bool}, isdig(c),
        +h => digS2.t(c, t, h, digS2(t)),
        +h => digS2.f(c, t, h))

def chkTr(+k: ABNF.Book, +R: ABNF.Rule, -s: String, -s2: String, +e: {s == s2 : String}, +h: {ABNF.check(k, R, s) == True{} : Bool}) -> {ABNF.check(k, R, s2) == True{} : Bool}:
  %e : {ABNF.check(k, R, _) == True{} : Bool}
  h

def le1(m: Nat) -> {(1n <= 1n+m : Nat) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def atl1I.go(+k: ABNF.Book, +r: ABNF.Rule, +a: String, +b: String, -s: String, +e: {String.append(a, b) == s : String}, +ha: {ABNF.check(k, r, a) == True{} : Bool}, p: &m: Nat -> {ABNF.check(k, ABNF.rep.exactly(m, r), b) == True{} : Bool})
  -> {ABNF.check(k, ABNF.rep.at_least(1n, r), s) == True{} : Bool}:
  (+m, hm) = p
  chkTr(k, ABNF.rep.at_least(1n, r), String.append(a, b), s, e, ABNF.rep.at_least.intro(k, 1n, 1n+m, le1(m), r, String.append(a, b), exSi(k, m, r, String.append(a, b), seqI2(k, r, ABNF.rep.exactly(m, r), a, b, ha, hm))))

# One or more repetitions are one, then any number.
def atl1I(+k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.seq([r, ABNF.rep.any(r)]), s) == True{} : Bool}) -> {ABNF.check(k, ABNF.rep.at_least(1n, r), s) == True{} : Bool}:
  seqE2({ABNF.check(k, ABNF.rep.at_least(1n, r), s) == True{} : Bool}, k, r, ABNF.rep.any(r), s, h, +a => +b => +e => +ha => +hb => atl1I.go(k, r, a, b, s, e, ha, ABNF.rep.any.elim(k, r, b, hb)))

def atl1E.m(+k: ABNF.Book, +r: ABNF.Rule, +s: String, m: Nat, +hle: {(1n <= m : Nat) == True{} : Bool}, +hm: {ABNF.check(k, ABNF.rep.exactly(m, r), s) == True{} : Bool}) -> {ABNF.check(k, ABNF.seq([r, ABNF.rep.any(r)]), s) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({ABNF.check(k, ABNF.seq([r, ABNF.rep.any(r)]), s) == True{} : Bool}, false_ne_true(hle))
    case 1n+ +m1:
      seqE2({ABNF.check(k, ABNF.seq([r, ABNF.rep.any(r)]), s) == True{} : Bool}, k, r, ABNF.rep.exactly(m1, r), s, exSe(k, m1, r, s, hm), +a => +b => +e => +ha => +hb =>
        chkTr(k, ABNF.seq([r, ABNF.rep.any(r)]), String.append(a, b), s, e, seqI2(k, r, ABNF.rep.any(r), a, b, ha, ABNF.rep.any.intro(k, m1, r, b, hb))))

def atl1E.go(+k: ABNF.Book, +r: ABNF.Rule, +s: String, p: &m: Nat -> {(1n <= m : Nat) == True{} : Bool} & {ABNF.check(k, ABNF.rep.exactly(m, r), s) == True{} : Bool}) -> {ABNF.check(k, ABNF.seq([r, ABNF.rep.any(r)]), s) == True{} : Bool}:
  (m, hle, hm) = p
  atl1E.m(k, r, s, m, hle, hm)

def atl1E(+k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.rep.at_least(1n, r), s) == True{} : Bool}) -> {ABNF.check(k, ABNF.seq([r, ABNF.rep.any(r)]), s) == True{} : Bool}:
  atl1E.go(k, r, s, ABNF.rep.at_least.elim(k, 1n, r, s, h))

def altL(+k: ABNF.Book, +r: ABNF.Rule, rs: List<ABNF.Rule>, +s: String, +h: {ABNF.check(k, r, s) == True{} : Bool}) -> {ABNF.check(k, ABNF.alt(r <> rs), s) == True{} : Bool}:
  tt(ABNF.check(k, ABNF.alt(r <> rs), s), Bool.or(ABNF.check(k, r, s), ABNF.check(k, ABNF.alt(rs), s)), ABNF.alt.con(k, r, rs, s), or_l(ABNF.check(k, r, s), ABNF.check(k, ABNF.alt(rs), s), h))

def altR(+k: ABNF.Book, +r: ABNF.Rule, rs: List<ABNF.Rule>, +s: String, +h: {ABNF.check(k, ABNF.alt(rs), s) == True{} : Bool}) -> {ABNF.check(k, ABNF.alt(r <> rs), s) == True{} : Bool}:
  tt(ABNF.check(k, ABNF.alt(r <> rs), s), Bool.or(ABNF.check(k, r, s), ABNF.check(k, ABNF.alt(rs), s)), ABNF.alt.con(k, r, rs, s), or_r(ABNF.check(k, r, s), ABNF.check(k, ABNF.alt(rs), s), h))

# refC(N, ch): the rule N is the character ch.
def refC(+N: String, +ch: Char, +c: Char, +e: {gsel(GRAMMAR, N) == [ABNF.char(ch)] : List<ABNF.Rule>}) -> {ABNF.check(BK, ABNF.ref(N), SCon{c, SNil{}}) == Char.is_eq(ch, c) : Bool}:
  Equal.trans(Bool, ABNF.check(BK, ABNF.ref(N), SCon{c, SNil{}}), ABNF.check(BK, ABNF.char(ch), SCon{c, SNil{}}), Char.is_eq(ch, c), MB(N, ABNF.char(ch), SCon{c, SNil{}}, e), ABNF.char.one(BK, ch, c))

def refCi(+N: String, +ch: Char, +c: Char, +e: {gsel(GRAMMAR, N) == [ABNF.char(ch)] : List<ABNF.Rule>}, +h: {Char.is_eq(ch, c) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref(N), SCon{c, SNil{}}) == True{} : Bool}:
  tt(ABNF.check(BK, ABNF.ref(N), SCon{c, SNil{}}), Char.is_eq(ch, c), refC(N, ch, c, e), h)

def sign1(+c: Char) -> {ABNF.check(BK, SIGN, SCon{c, SNil{}}) == issign(c) : Bool}:
  alt2(BK, ABNF.ref("minus"), [ABNF.ref("plus")], SCon{c, SNil{}}, Char.is_eq('-', c), Bool.or(Char.is_eq('+', c), False{}), refC("minus", '-', c, {==}),
    alt2(BK, ABNF.ref("plus"), [], SCon{c, SNil{}}, Char.is_eq('+', c), False{}, refC("plus", '+', c, {==}), ABNF.alt.nil(BK, SCon{c, SNil{}})))

def eref1(+c: Char) -> {ABNF.check(BK, ABNF.ref("e"), SCon{c, SNil{}}) == ise(c) : Bool}:
  Equal.trans(Bool, ABNF.check(BK, ABNF.ref("e"), SCon{c, SNil{}}), ABNF.check(BK, ABNF.alt([ABNF.char('e'), ABNF.char('E')]), SCon{c, SNil{}}), ise(c),
    MB("e", ABNF.alt([ABNF.char('e'), ABNF.char('E')]), SCon{c, SNil{}}, {==}),
    alt2(BK, ABNF.char('e'), [ABNF.char('E')], SCon{c, SNil{}}, Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{}), ABNF.char.one(BK, 'e', c),
      alt2(BK, ABNF.char('E'), [], SCon{c, SNil{}}, Char.is_eq('E', c), False{}, ABNF.char.one(BK, 'E', c), ABNF.alt.nil(BK, SCon{c, SNil{}}))))

def d19C(+c: Char, +h: {is19(c) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("digit1-9"), SCon{c, SNil{}}) == True{} : Bool}:
  MBi("digit1-9", ABNF.range('1', '9'), SCon{c, SNil{}}, {==}, tt(ABNF.check(BK, ABNF.range('1', '9'), SCon{c, SNil{}}), inR('1', '9', c), rg1(BK, '1', '9', c), h))

def SGN2() -> ABNF.Rule:
  ABNF.seq([ABNF.opt(SIGN), AL1])

def AE() -> ABNF.Rule:
  ABNF.seq([AL1, ABNF.opt(ABNF.ref("exp"))])

def FE() -> ABNF.Rule:
  ABNF.seq([ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp"))])

def DFE() -> ABNF.Rule:
  ABNF.seq([ABNF.rep.any(DIG), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp"))])

def IFE() -> ABNF.Rule:
  ABNF.seq([ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp"))])

def dig1S.t(+c: Char, +t: String, +h: {isdig(c) == True{} : Bool}) -> NS(dig1(digits(SCon{c, t})), SCon{c, t}, AL1):
  %Equal.sym(SP, digits(SCon{c, t}), prepS(c, digits(t)), selT(SP, isdig(c), u => prepS(c, digits(t)), u => SP{SNil{}, SCon{c, t}}, h)) : NS(dig1(_), SCon{c, t}, AL1)
  (cons_eq(c, String.append(spa(digits(t)), spt(digits(t))), t, digS1(t)), atl1I(BK, DIG, SCon{c, spa(digits(t))}, seqI2(BK, DIG, ABNF.rep.any(DIG), SCon{c, SNil{}}, spa(digits(t)), dig1C(c, h), digS2(t))))

def dig1S.f(+c: Char, +t: String, +h: {isdig(c) == False{} : Bool}) -> NS(dig1(digits(SCon{c, t})), SCon{c, t}, AL1):
  %Equal.sym(SP, digits(SCon{c, t}), SP{SNil{}, SCon{c, t}}, selF(SP, isdig(c), u => prepS(c, digits(t)), u => SP{SNil{}, SCon{c, t}}, h)) : NS(dig1(_), SCon{c, t}, AL1)
  Unit{}

def dig1S(s: String) -> NS(dig1(digits(s)), s, AL1):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      bcase(NS(dig1(digits(SCon{c, t})), SCon{c, t}, AL1), isdig(c), +h => dig1S.t(c, t, h), +h => dig1S.f(c, t, h))

def nsignS.t(+c: Char, +t: String, +h: {issign(c) == True{} : Bool}) -> NS(nsign(SCon{c, t}), SCon{c, t}, SGN2):
  %Equal.sym(Maybe<&2, SP>, nsign(SCon{c, t}), prepM(c, dig1(digits(t))), selT(Maybe<&2, SP>, issign(c), u => prepM(c, dig1(digits(t))), u => dig1(digits(SCon{c, t})), h)) : NS(_, SCon{c, t}, SGN2)
  NSmap(c, dig1(digits(t)), t, AL1, SGN2, dig1S(t), +a => +ha => seqI2(BK, ABNF.opt(SIGN), AL1, SCon{c, SNil{}}, a, optS(BK, SIGN, SCon{c, SNil{}}, tt(ABNF.check(BK, SIGN, SCon{c, SNil{}}), issign(c), sign1(c), h)), ha))

def nsignS.f(+c: Char, +t: String, +h: {issign(c) == False{} : Bool}) -> NS(nsign(SCon{c, t}), SCon{c, t}, SGN2):
  %Equal.sym(Maybe<&2, SP>, nsign(SCon{c, t}), dig1(digits(SCon{c, t})), selF(Maybe<&2, SP>, issign(c), u => prepM(c, dig1(digits(t))), u => dig1(digits(SCon{c, t})), h)) : NS(_, SCon{c, t}, SGN2)
  NSw(dig1(digits(SCon{c, t})), SCon{c, t}, AL1, SGN2, dig1S(SCon{c, t}), +a => +ha => seqI2(BK, ABNF.opt(SIGN), AL1, SNil{}, a, optN(BK, SIGN), ha))

def nsignS(s: String) -> NS(nsign(s), s, SGN2):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      bcase(NS(nsign(SCon{c, t}), SCon{c, t}, SGN2), issign(c), +h => nsignS.t(c, t, h), +h => nsignS.f(c, t, h))

def expA.go(+c: Char, -a: String, +s1: String, +s2: String, +e: {String.append(s1, s2) == a : String}, +hc: {ise(c) == True{} : Bool}, +h1: {ABNF.check(BK, ABNF.opt(SIGN), s1) == True{} : Bool}, +h2: {ABNF.check(BK, AL1, s2) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.ref("exp"), SCon{c, a}) == True{} : Bool}:
  %Equal.sym(String, a, String.append(s1, s2), Equal.sym(String, String.append(s1, s2), a, e)) : {ABNF.check(BK, ABNF.ref("exp"), SCon{c, _}) == True{} : Bool}
  MBi("exp", B_exp, SCon{c, String.append(s1, s2)}, {==}, seqI3(BK, ABNF.ref("e"), ABNF.opt(SIGN), AL1, SCon{c, SNil{}}, s1, s2, tt(ABNF.check(BK, ABNF.ref("e"), SCon{c, SNil{}}), ise(c), eref1(c), hc), h1, h2))

def expA(+c: Char, +a: String, +hc: {ise(c) == True{} : Bool}, +h: {ABNF.check(BK, SGN2, a) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("exp"), SCon{c, a}) == True{} : Bool}:
  seqE2({ABNF.check(BK, ABNF.ref("exp"), SCon{c, a}) == True{} : Bool}, BK, ABNF.opt(SIGN), AL1, a, h, +s1 => +s2 => +e => +h1 => +h2 => expA.go(c, a, s1, s2, e, hc, h1, h2))

def nexpS.t(+c: Char, +t: String, +h: {ise(c) == True{} : Bool}) -> NS(nexp(SCon{c, t}), SCon{c, t}, ABNF.opt(ABNF.ref("exp"))):
  %Equal.sym(Maybe<&2, SP>, nexp(SCon{c, t}), prepM(c, nsign(t)), selT(Maybe<&2, SP>, ise(c), u => prepM(c, nsign(t)), u => Some{SP{SNil{}, SCon{c, t}}}, h)) : NS(_, SCon{c, t}, ABNF.opt(ABNF.ref("exp")))
  NSmap(c, nsign(t), t, SGN2, ABNF.opt(ABNF.ref("exp")), nsignS(t), +a => +ha => optS(BK, ABNF.ref("exp"), SCon{c, a}, expA(c, a, h, ha)))

def nexpS.f(+c: Char, +t: String, +h: {ise(c) == False{} : Bool}) -> NS(nexp(SCon{c, t}), SCon{c, t}, ABNF.opt(ABNF.ref("exp"))):
  %Equal.sym(Maybe<&2, SP>, nexp(SCon{c, t}), Some{SP{SNil{}, SCon{c, t}}}, selF(Maybe<&2, SP>, ise(c), u => prepM(c, nsign(t)), u => Some{SP{SNil{}, SCon{c, t}}}, h)) : NS(_, SCon{c, t}, ABNF.opt(ABNF.ref("exp")))
  ({==}, optN(BK, ABNF.ref("exp")))

def nexpS(s: String) -> NS(nexp(s), s, ABNF.opt(ABNF.ref("exp"))):
  match s:
    case SNil{}:
      ({==}, optN(BK, ABNF.ref("exp")))
    case SCon{+c, +t}:
      bcase(NS(nexp(SCon{c, t}), SCon{c, t}, ABNF.opt(ABNF.ref("exp"))), ise(c), +h => nexpS.t(c, t, h), +h => nexpS.f(c, t, h))

def nfrac2S(m: Maybe<&2, SP>, -s: String, ns: NS(m, s, AL1)) -> NS(nfrac2(m), s, AE):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      (e, h) = ns
      NSapp(spa(p), nexp(spt(p)), spt(p), s, ABNF.opt(ABNF.ref("exp")), AE, nexpS(spt(p)), e, +a => +ha => seqI2(BK, AL1, ABNF.opt(ABNF.ref("exp")), spa(p), a, h, ha))

def fracA.go(+c: Char, -a: String, +s1: String, +s2: String, +e: {String.append(s1, s2) == a : String}, +hc: {Char.is_eq('.', c) == True{} : Bool}, +h1: {ABNF.check(BK, AL1, s1) == True{} : Bool}, +h2: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), s2) == True{} : Bool})
  -> {ABNF.check(BK, FE, SCon{c, a}) == True{} : Bool}:
  %Equal.sym(String, a, String.append(s1, s2), Equal.sym(String, String.append(s1, s2), a, e)) : {ABNF.check(BK, FE, SCon{c, _}) == True{} : Bool}
  seqI2(BK, ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), SCon{c, s1}, s2,
    optS(BK, ABNF.ref("frac"), SCon{c, s1}, MBi("frac", B_frac, SCon{c, s1}, {==}, seqI2(BK, ABNF.ref("decimal-point"), AL1, SCon{c, SNil{}}, s1, refCi("decimal-point", '.', c, {==}, hc), h1))), h2)

def fracA(+c: Char, +a: String, +hc: {Char.is_eq('.', c) == True{} : Bool}, +h: {ABNF.check(BK, AE, a) == True{} : Bool}) -> {ABNF.check(BK, FE, SCon{c, a}) == True{} : Bool}:
  seqE2({ABNF.check(BK, FE, SCon{c, a}) == True{} : Bool}, BK, AL1, ABNF.opt(ABNF.ref("exp")), a, h, +s1 => +s2 => +e => +h1 => +h2 => fracA.go(c, a, s1, s2, e, hc, h1, h2))

def nfracS.t(+c: Char, +t: String, +h: {Char.is_eq('.', c) == True{} : Bool}) -> NS(nfrac(SCon{c, t}), SCon{c, t}, FE):
  %Equal.sym(Maybe<&2, SP>, nfrac(SCon{c, t}), prepM(c, nfrac2(dig1(digits(t)))), selT(Maybe<&2, SP>, Char.is_eq('.', c), u => prepM(c, nfrac2(dig1(digits(t)))), u => nexp(SCon{c, t}), h)) : NS(_, SCon{c, t}, FE)
  NSmap(c, nfrac2(dig1(digits(t))), t, AE, FE, nfrac2S(dig1(digits(t)), t, dig1S(t)), +a => +ha => fracA(c, a, h, ha))

def nfracS.f(+c: Char, +t: String, +h: {Char.is_eq('.', c) == False{} : Bool}) -> NS(nfrac(SCon{c, t}), SCon{c, t}, FE):
  %Equal.sym(Maybe<&2, SP>, nfrac(SCon{c, t}), nexp(SCon{c, t}), selF(Maybe<&2, SP>, Char.is_eq('.', c), u => prepM(c, nfrac2(dig1(digits(t)))), u => nexp(SCon{c, t}), h)) : NS(_, SCon{c, t}, FE)
  NSw(nexp(SCon{c, t}), SCon{c, t}, ABNF.opt(ABNF.ref("exp")), FE, nexpS(SCon{c, t}), +a => +ha => seqI2(BK, ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), SNil{}, a, optN(BK, ABNF.ref("frac")), ha))

def nfracS(s: String) -> NS(nfrac(s), s, FE):
  match s:
    case SNil{}:
      ({==}, seqI2(BK, ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), SNil{}, SNil{}, optN(BK, ABNF.ref("frac")), optN(BK, ABNF.ref("exp"))))
    case SCon{+c, +t}:
      bcase(NS(nfrac(SCon{c, t}), SCon{c, t}, FE), Char.is_eq('.', c), +h => nfracS.t(c, t, h), +h => nfracS.f(c, t, h))

def intZ(+c: Char, +hc: {Char.is_eq('0', c) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("int"), SCon{c, SNil{}}) == True{} : Bool}:
  MBi("int", B_int, SCon{c, SNil{}}, {==}, altL(BK, ABNF.ref("zero"), [ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])], SCon{c, SNil{}}, refCi("zero", '0', c, {==}, hc)))

def intNZ(+c: Char, +d: String, +hc: {is19(c) == True{} : Bool}, +hd: {ABNF.check(BK, ABNF.rep.any(DIG), d) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("int"), SCon{c, d}) == True{} : Bool}:
  MBi("int", B_int, SCon{c, d}, {==}, altR(BK, ABNF.ref("zero"), [ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])], SCon{c, d},
    altL(BK, ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)]), [], SCon{c, d}, seqI2(BK, ABNF.ref("digit1-9"), ABNF.rep.any(DIG), SCon{c, SNil{}}, d, d19C(c, hc), hd))))

def int0A.go(+c: Char, -a: String, +s1: String, +s2: String, +e: {String.append(s1, s2) == a : String}, +hc: {Char.is_eq('0', c) == True{} : Bool}, +h1: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), s1) == True{} : Bool}, +h2: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), s2) == True{} : Bool})
  -> {ABNF.check(BK, IFE, SCon{c, a}) == True{} : Bool}:
  %Equal.sym(String, a, String.append(s1, s2), Equal.sym(String, String.append(s1, s2), a, e)) : {ABNF.check(BK, IFE, SCon{c, _}) == True{} : Bool}
  seqI3(BK, ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), SCon{c, SNil{}}, s1, s2, intZ(c, hc), h1, h2)

def int0A(+c: Char, +a: String, +hc: {Char.is_eq('0', c) == True{} : Bool}, +h: {ABNF.check(BK, FE, a) == True{} : Bool}) -> {ABNF.check(BK, IFE, SCon{c, a}) == True{} : Bool}:
  seqE2({ABNF.check(BK, IFE, SCon{c, a}) == True{} : Bool}, BK, ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), a, h, +s1 => +s2 => +e => +h1 => +h2 => int0A.go(c, a, s1, s2, e, hc, h1, h2))

def int19A.go(+c: Char, -a: String, +d: String, +s1: String, +s2: String, +e: {String.append(d, String.append(s1, s2)) == a : String}, +hc: {is19(c) == True{} : Bool},
  +hd: {ABNF.check(BK, ABNF.rep.any(DIG), d) == True{} : Bool}, +h1: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), s1) == True{} : Bool}, +h2: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), s2) == True{} : Bool})
  -> {ABNF.check(BK, IFE, SCon{c, a}) == True{} : Bool}:
  %Equal.sym(String, a, String.append(d, String.append(s1, s2)), Equal.sym(String, String.append(d, String.append(s1, s2)), a, e)) : {ABNF.check(BK, IFE, SCon{c, _}) == True{} : Bool}
  seqI3(BK, ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), SCon{c, d}, s1, s2, intNZ(c, d, hc, hd), h1, h2)

def int19A(+c: Char, +a: String, +hc: {is19(c) == True{} : Bool}, +h: {ABNF.check(BK, DFE, a) == True{} : Bool}) -> {ABNF.check(BK, IFE, SCon{c, a}) == True{} : Bool}:
  seqE3({ABNF.check(BK, IFE, SCon{c, a}) == True{} : Bool}, BK, ABNF.rep.any(DIG), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), a, h, +d => +s1 => +s2 => +e => +hd => +h1 => +h2 => int19A.go(c, a, d, s1, s2, e, hc, hd, h1, h2))

def nint2S.go(+t: String, -a: String, +s1: String, +s2: String, +e: {String.append(s1, s2) == a : String}, +h1: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), s1) == True{} : Bool}, +h2: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), s2) == True{} : Bool})
  -> {ABNF.check(BK, DFE, String.append(spa(digits(t)), a)) == True{} : Bool}:
  %Equal.sym(String, a, String.append(s1, s2), Equal.sym(String, String.append(s1, s2), a, e)) : {ABNF.check(BK, DFE, String.append(spa(digits(t)), _)) == True{} : Bool}
  seqI3(BK, ABNF.rep.any(DIG), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), spa(digits(t)), s1, s2, digS2(t), h1, h2)

def nint2S(+t: String) -> NS(nint2(digits(t)), t, DFE):
  NSapp(spa(digits(t)), nfrac(spt(digits(t))), spt(digits(t)), t, FE, DFE, nfracS(spt(digits(t))), digS1(t),
    +a => +ha => seqE2({ABNF.check(BK, DFE, String.append(spa(digits(t)), a)) == True{} : Bool}, BK, ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), a, ha, +s1 => +s2 => +e => +h1 => +h2 => nint2S.go(t, a, s1, s2, e, h1, h2)))

def nintS.t(+c: Char, +t: String, +h: {Char.is_eq('0', c) == True{} : Bool}) -> NS(nint(SCon{c, t}), SCon{c, t}, IFE):
  %Equal.sym(Maybe<&2, SP>, nint(SCon{c, t}), prepM(c, nfrac(t)), selT(Maybe<&2, SP>, Char.is_eq('0', c), u => prepM(c, nfrac(t)), u => sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}), h)) : NS(_, SCon{c, t}, IFE)
  NSmap(c, nfrac(t), t, FE, IFE, nfracS(t), +a => +ha => int0A(c, a, h, ha))

def nintS.ft(+c: Char, +t: String, +h: {Char.is_eq('0', c) == False{} : Bool}, +h2: {is19(c) == True{} : Bool}) -> NS(nint(SCon{c, t}), SCon{c, t}, IFE):
  %Equal.sym(Maybe<&2, SP>, nint(SCon{c, t}), sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}), selF(Maybe<&2, SP>, Char.is_eq('0', c), u => prepM(c, nfrac(t)), u => sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}), h)) : NS(_, SCon{c, t}, IFE)
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}), prepM(c, nint2(digits(t))), selT(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}, h2)) : NS(_, SCon{c, t}, IFE)
  NSmap(c, nint2(digits(t)), t, DFE, IFE, nint2S(t), +a => +ha => int19A(c, a, h2, ha))

def nintS.ff(+c: Char, +t: String, +h: {Char.is_eq('0', c) == False{} : Bool}, +h2: {is19(c) == False{} : Bool}) -> NS(nint(SCon{c, t}), SCon{c, t}, IFE):
  %Equal.sym(Maybe<&2, SP>, nint(SCon{c, t}), sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}), selF(Maybe<&2, SP>, Char.is_eq('0', c), u => prepM(c, nfrac(t)), u => sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}), h)) : NS(_, SCon{c, t}, IFE)
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}), None{}, selF(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(t))), u => None{}, h2)) : NS(_, SCon{c, t}, IFE)
  Unit{}

def nintS(s: String) -> NS(nint(s), s, IFE):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      bcase(NS(nint(SCon{c, t}), SCon{c, t}, IFE), Char.is_eq('0', c), +h => nintS.t(c, t, h),
        +h => bcase(NS(nint(SCon{c, t}), SCon{c, t}, IFE), is19(c), +h2 => nintS.ft(c, t, h, h2), +h2 => nintS.ff(c, t, h, h2)))

def numA.go(+c: Char, -a: String, +i: String, +s1: String, +s2: String, +e: {String.append(i, String.append(s1, s2)) == a : String}, +hc: {Char.is_eq('-', c) == True{} : Bool},
  +hi: {ABNF.check(BK, ABNF.ref("int"), i) == True{} : Bool}, +h1: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), s1) == True{} : Bool}, +h2: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), s2) == True{} : Bool})
  -> {ABNF.check(BK, B_number, SCon{c, a}) == True{} : Bool}:
  %Equal.sym(String, a, String.append(i, String.append(s1, s2)), Equal.sym(String, String.append(i, String.append(s1, s2)), a, e)) : {ABNF.check(BK, B_number, SCon{c, _}) == True{} : Bool}
  seqI4(BK, ABNF.opt(ABNF.ref("minus")), ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), SCon{c, SNil{}}, i, s1, s2, optS(BK, ABNF.ref("minus"), SCon{c, SNil{}}, refCi("minus", '-', c, {==}, hc)), hi, h1, h2)

def numA(+c: Char, +a: String, +hc: {Char.is_eq('-', c) == True{} : Bool}, +h: {ABNF.check(BK, IFE, a) == True{} : Bool}) -> {ABNF.check(BK, B_number, SCon{c, a}) == True{} : Bool}:
  seqE3({ABNF.check(BK, B_number, SCon{c, a}) == True{} : Bool}, BK, ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), a, h, +i => +s1 => +s2 => +e => +hi => +h1 => +h2 => numA.go(c, a, i, s1, s2, e, hc, hi, h1, h2))

def numB.go(-a: String, +i: String, +s1: String, +s2: String, +e: {String.append(i, String.append(s1, s2)) == a : String},
  +hi: {ABNF.check(BK, ABNF.ref("int"), i) == True{} : Bool}, +h1: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), s1) == True{} : Bool}, +h2: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), s2) == True{} : Bool})
  -> {ABNF.check(BK, B_number, a) == True{} : Bool}:
  %Equal.sym(String, a, String.append(i, String.append(s1, s2)), Equal.sym(String, String.append(i, String.append(s1, s2)), a, e)) : {ABNF.check(BK, B_number, _) == True{} : Bool}
  seqI4(BK, ABNF.opt(ABNF.ref("minus")), ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), SNil{}, i, s1, s2, optN(BK, ABNF.ref("minus")), hi, h1, h2)

def numB(+a: String, +h: {ABNF.check(BK, IFE, a) == True{} : Bool}) -> {ABNF.check(BK, B_number, a) == True{} : Bool}:
  seqE3({ABNF.check(BK, B_number, a) == True{} : Bool}, BK, ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), a, h, +i => +s1 => +s2 => +e => +hi => +h1 => +h2 => numB.go(a, i, s1, s2, e, hi, h1, h2))

def numS.t(+c: Char, +t: String, +h: {Char.is_eq('-', c) == True{} : Bool}) -> NS(num_scan(SCon{c, t}), SCon{c, t}, B_number):
  %Equal.sym(Maybe<&2, SP>, num_scan(SCon{c, t}), prepM(c, nint(t)), selT(Maybe<&2, SP>, Char.is_eq('-', c), u => prepM(c, nint(t)), u => nint(SCon{c, t}), h)) : NS(_, SCon{c, t}, B_number)
  NSmap(c, nint(t), t, IFE, B_number, nintS(t), +a => +ha => numA(c, a, h, ha))

def numS.f(+c: Char, +t: String, +h: {Char.is_eq('-', c) == False{} : Bool}) -> NS(num_scan(SCon{c, t}), SCon{c, t}, B_number):
  %Equal.sym(Maybe<&2, SP>, num_scan(SCon{c, t}), nint(SCon{c, t}), selF(Maybe<&2, SP>, Char.is_eq('-', c), u => prepM(c, nint(t)), u => nint(SCon{c, t}), h)) : NS(_, SCon{c, t}, B_number)
  NSw(nint(SCon{c, t}), SCon{c, t}, IFE, B_number, nintS(SCon{c, t}), +a => +ha => numB(a, ha))

# What num_scan reads is a number.
def numS(s: String) -> NS(num_scan(s), s, B_number):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      bcase(NS(num_scan(SCon{c, t}), SCon{c, t}, B_number), Char.is_eq('-', c), +h => numS.t(c, t, h), +h => numS.f(c, t, h))

# Strings
# =======

def STR(st: SS) -> ABNF.Rule:
  match st:
    case SN{}:
      CHARS
    case SE{}:
      ABNF.seq([ESCT, CHARS])
    case SH{n}:
      ABNF.seq([ABNF.rep.exactly(1n+n, HEX), CHARS])

# SNS(m, s, R): if the scan m of s succeeds, s is its text, a quote, and the rest.
def SNS(m: Maybe<&2, SP>, s: String, R: ABNF.Rule) -> Type:
  match m:
    case None{}:
      Unit
    case Some{p}:
      {String.append(spa(p), SCon{'"', spt(p)}) == s : String} & {ABNF.check(BK, R, spa(p)) == True{} : Bool}

def SNSmap(+c: Char, m: Maybe<&2, SP>, -t: String, -R2: ABNF.Rule, -R: ABNF.Rule, ns: SNS(m, t, R2), f: @a: String -> {ABNF.check(BK, R2, a) == True{} : Bool} -> {ABNF.check(BK, R, SCon{c, a}) == True{} : Bool})
  -> SNS(prepM(c, m), SCon{c, t}, R):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      (e, h) = ns
      (cons_eq(c, String.append(spa(p), SCon{'"', spt(p)}), t, e), f(spa(p), h))

def seqEmpty(+k: ABNF.Book, +X: ABNF.Rule, +s: String) -> {ABNF.check(k, ABNF.seq([X, ABNF.empty]), s) == ABNF.check(k, X, s) : Bool}:
  beq(ABNF.check(k, ABNF.seq([X, ABNF.empty]), s), ABNF.check(k, X, s),
    +h => seqE2({ABNF.check(k, X, s) == True{} : Bool}, k, X, ABNF.empty, s, h, +s1 => +s2 => +e => +h1 => +h2 =>
      chkTr(k, X, s1, s, Equal.trans(String, s1, String.append(s1, s2), s, Equal.trans(String, s1, String.append(s1, SNil{}), String.append(s1, s2), Equal.sym(String, String.append(s1, SNil{}), s1, append_nil(s1)), app_congl(s1, SNil{}, s2, Equal.sym(String, s2, SNil{}, emptyE(k, s2, h2)))), e), h1)),
    +h => chkTr(k, ABNF.seq([X, ABNF.empty]), String.append(s, SNil{}), s, append_nil(s), seqI2(k, X, ABNF.empty, s, SNil{}, h, ABNF.empty.nil(k))))

def ci1(+k: ABNF.Book, +lo: Char, +up: Char, +c: Char) -> {ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(lo), ABNF.char(up)]), ABNF.empty]), SCon{c, SNil{}}) == Bool.or(Char.is_eq(lo, c), Bool.or(Char.is_eq(up, c), False{})) : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(lo), ABNF.char(up)]), ABNF.empty]), SCon{c, SNil{}}), ABNF.check(k, ABNF.alt([ABNF.char(lo), ABNF.char(up)]), SCon{c, SNil{}}), Bool.or(Char.is_eq(lo, c), Bool.or(Char.is_eq(up, c), False{})),
    seqEmpty(k, ABNF.alt([ABNF.char(lo), ABNF.char(up)]), SCon{c, SNil{}}),
    alt2(k, ABNF.char(lo), [ABNF.char(up)], SCon{c, SNil{}}, Char.is_eq(lo, c), Bool.or(Char.is_eq(up, c), False{}), ABNF.char.one(k, lo, c),
      alt2(k, ABNF.char(up), [], SCon{c, SNil{}}, Char.is_eq(up, c), False{}, ABNF.char.one(k, up, c), ABNF.alt.nil(k, SCon{c, SNil{}}))))

def ci0(+k: ABNF.Book, +lo: Char, +up: Char) -> {ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(lo), ABNF.char(up)]), ABNF.empty]), SNil{}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(lo), ABNF.char(up)]), ABNF.empty]), SNil{}), ABNF.check(k, ABNF.alt([ABNF.char(lo), ABNF.char(up)]), SNil{}), False{},
    seqEmpty(k, ABNF.alt([ABNF.char(lo), ABNF.char(up)]), SNil{}),
    alt2(k, ABNF.char(lo), [ABNF.char(up)], SNil{}, False{}, False{}, ABNF.char.nil(k, lo),
      alt2(k, ABNF.char(up), [], SNil{}, False{}, False{}, ABNF.char.nil(k, up), ABNF.alt.nil(k, SNil{}))))

def ci2(+k: ABNF.Book, +lo: Char, +up: Char, +a: Char, +b: Char, +t: String) -> {ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(lo), ABNF.char(up)]), ABNF.empty]), SCon{a, SCon{b, t}}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(lo), ABNF.char(up)]), ABNF.empty]), SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.alt([ABNF.char(lo), ABNF.char(up)]), SCon{a, SCon{b, t}}), False{},
    seqEmpty(k, ABNF.alt([ABNF.char(lo), ABNF.char(up)]), SCon{a, SCon{b, t}}),
    alt2(k, ABNF.char(lo), [ABNF.char(up)], SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(k, lo, a, b, t),
      alt2(k, ABNF.char(up), [], SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(k, up, a, b, t), ABNF.alt.nil(k, SCon{a, SCon{b, t}}))))

def seqCiNil(+k: ABNF.Book, +X: ABNF.Rule, +s: String) -> {ABNF.check(k, ABNF.seq([X, ABNF.string.case_insensitive(SNil{})]), s) == ABNF.check(k, ABNF.seq([X, ABNF.empty]), s) : Bool}:
  beq(ABNF.check(k, ABNF.seq([X, ABNF.string.case_insensitive(SNil{})]), s), ABNF.check(k, ABNF.seq([X, ABNF.empty]), s),
    +h => seqE2({ABNF.check(k, ABNF.seq([X, ABNF.empty]), s) == True{} : Bool}, k, X, ABNF.string.case_insensitive(SNil{}), s, h, +s1 => +s2 => +e => +h1 => +h2 =>
      chkTr(k, ABNF.seq([X, ABNF.empty]), String.append(s1, s2), s, e, seqI2(k, X, ABNF.empty, s1, s2, h1, tt.sym(ABNF.check(k, ABNF.string.case_insensitive(SNil{}), s2), ABNF.check(k, ABNF.empty, s2), ABNF.string.case_insensitive.nil(k, s2), h2)))),
    +h => seqE2({ABNF.check(k, ABNF.seq([X, ABNF.string.case_insensitive(SNil{})]), s) == True{} : Bool}, k, X, ABNF.empty, s, h, +s1 => +s2 => +e => +h1 => +h2 =>
      chkTr(k, ABNF.seq([X, ABNF.string.case_insensitive(SNil{})]), String.append(s1, s2), s, e, seqI2(k, X, ABNF.string.case_insensitive(SNil{}), s1, s2, h1, tt(ABNF.check(k, ABNF.string.case_insensitive(SNil{}), s2), ABNF.check(k, ABNF.empty, s2), ABNF.string.case_insensitive.nil(k, s2), h2)))))

# A one-letter case-insensitive string is either case of the letter.
def ciL(+k: ABNF.Book, +L: Char, +s: String) -> {ABNF.check(k, ABNF.string.case_insensitive(SCon{L, SNil{}}), s) == ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(Char.to_lower(L)), ABNF.char(Char.to_upper(L))]), ABNF.empty]), s) : Bool}:
  Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive(SCon{L, SNil{}}), s), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(Char.to_lower(L)), ABNF.char(Char.to_upper(L))]), ABNF.string.case_insensitive(SNil{})]), s), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char(Char.to_lower(L)), ABNF.char(Char.to_upper(L))]), ABNF.empty]), s),
    ABNF.string.case_insensitive.con(k, L, SNil{}, s), seqCiNil(k, ABNF.alt([ABNF.char(Char.to_lower(L)), ABNF.char(Char.to_upper(L))]), s))

def hex1(+k: ABNF.Book, +c: Char) -> {ABNF.check(k, HEX, SCon{c, SNil{}}) == ishex(c) : Bool}:
  Equal.trans(Bool, ABNF.check(k, HEX, SCon{c, SNil{}}), ABNF.check(k, ABNF.alt([ABNF.core.digit, ABNF.string.case_insensitive("A"), ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")]), SCon{c, SNil{}}), ishex(c), ABNF.core.hexdig.ok(k, SCon{c, SNil{}}),
    alt2(k, ABNF.core.digit, [ABNF.string.case_insensitive("A"), ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{c, SNil{}}, inR('0', '9', c), Bool.or(Bool.or(Char.is_eq('a', c), Bool.or(Char.is_eq('A', c), False{})), Bool.or(Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('B', c), False{})), Bool.or(Bool.or(Char.is_eq('c', c), Bool.or(Char.is_eq('C', c), False{})), Bool.or(Bool.or(Char.is_eq('d', c), Bool.or(Char.is_eq('D', c), False{})), Bool.or(Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{})), Bool.or(Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), False{})))))), cd1(k, c), alt2(k, ABNF.string.case_insensitive("A"), [ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{c, SNil{}}, Bool.or(Char.is_eq('a', c), Bool.or(Char.is_eq('A', c), False{})), Bool.or(Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('B', c), False{})), Bool.or(Bool.or(Char.is_eq('c', c), Bool.or(Char.is_eq('C', c), False{})), Bool.or(Bool.or(Char.is_eq('d', c), Bool.or(Char.is_eq('D', c), False{})), Bool.or(Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{})), Bool.or(Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), False{}))))), Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("A"), SCon{c, SNil{}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('a'), ABNF.char('A')]), ABNF.empty]), SCon{c, SNil{}}), Bool.or(Char.is_eq('a', c), Bool.or(Char.is_eq('A', c), False{})), ciL(k, 'A', SCon{c, SNil{}}), ci1(k, 'a', 'A', c)), alt2(k, ABNF.string.case_insensitive("B"), [ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{c, SNil{}}, Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('B', c), False{})), Bool.or(Bool.or(Char.is_eq('c', c), Bool.or(Char.is_eq('C', c), False{})), Bool.or(Bool.or(Char.is_eq('d', c), Bool.or(Char.is_eq('D', c), False{})), Bool.or(Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{})), Bool.or(Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), False{})))), Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("B"), SCon{c, SNil{}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('b'), ABNF.char('B')]), ABNF.empty]), SCon{c, SNil{}}), Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('B', c), False{})), ciL(k, 'B', SCon{c, SNil{}}), ci1(k, 'b', 'B', c)), alt2(k, ABNF.string.case_insensitive("C"), [ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{c, SNil{}}, Bool.or(Char.is_eq('c', c), Bool.or(Char.is_eq('C', c), False{})), Bool.or(Bool.or(Char.is_eq('d', c), Bool.or(Char.is_eq('D', c), False{})), Bool.or(Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{})), Bool.or(Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), False{}))), Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("C"), SCon{c, SNil{}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('c'), ABNF.char('C')]), ABNF.empty]), SCon{c, SNil{}}), Bool.or(Char.is_eq('c', c), Bool.or(Char.is_eq('C', c), False{})), ciL(k, 'C', SCon{c, SNil{}}), ci1(k, 'c', 'C', c)), alt2(k, ABNF.string.case_insensitive("D"), [ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{c, SNil{}}, Bool.or(Char.is_eq('d', c), Bool.or(Char.is_eq('D', c), False{})), Bool.or(Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{})), Bool.or(Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), False{})), Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("D"), SCon{c, SNil{}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('d'), ABNF.char('D')]), ABNF.empty]), SCon{c, SNil{}}), Bool.or(Char.is_eq('d', c), Bool.or(Char.is_eq('D', c), False{})), ciL(k, 'D', SCon{c, SNil{}}), ci1(k, 'd', 'D', c)), alt2(k, ABNF.string.case_insensitive("E"), [ABNF.string.case_insensitive("F")], SCon{c, SNil{}}, Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{})), Bool.or(Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), False{}), Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("E"), SCon{c, SNil{}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('e'), ABNF.char('E')]), ABNF.empty]), SCon{c, SNil{}}), Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{})), ciL(k, 'E', SCon{c, SNil{}}), ci1(k, 'e', 'E', c)), alt2(k, ABNF.string.case_insensitive("F"), [], SCon{c, SNil{}}, Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("F"), SCon{c, SNil{}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('f'), ABNF.char('F')]), ABNF.empty]), SCon{c, SNil{}}), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('F', c), False{})), ciL(k, 'F', SCon{c, SNil{}}), ci1(k, 'f', 'F', c)), ABNF.alt.nil(k, SCon{c, SNil{}})))))))))

def hex0(+k: ABNF.Book) -> {ABNF.check(k, HEX, SNil{}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(k, HEX, SNil{}), ABNF.check(k, ABNF.alt([ABNF.core.digit, ABNF.string.case_insensitive("A"), ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")]), SNil{}), False{}, ABNF.core.hexdig.ok(k, SNil{}),
    alt2(k, ABNF.core.digit, [ABNF.string.case_insensitive("A"), ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SNil{}, False{}, False{}, cd0(k), alt2(k, ABNF.string.case_insensitive("A"), [ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SNil{}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("A"), SNil{}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('a'), ABNF.char('A')]), ABNF.empty]), SNil{}), False{}, ciL(k, 'A', SNil{}), ci0(k, 'a', 'A')), alt2(k, ABNF.string.case_insensitive("B"), [ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SNil{}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("B"), SNil{}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('b'), ABNF.char('B')]), ABNF.empty]), SNil{}), False{}, ciL(k, 'B', SNil{}), ci0(k, 'b', 'B')), alt2(k, ABNF.string.case_insensitive("C"), [ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SNil{}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("C"), SNil{}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('c'), ABNF.char('C')]), ABNF.empty]), SNil{}), False{}, ciL(k, 'C', SNil{}), ci0(k, 'c', 'C')), alt2(k, ABNF.string.case_insensitive("D"), [ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SNil{}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("D"), SNil{}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('d'), ABNF.char('D')]), ABNF.empty]), SNil{}), False{}, ciL(k, 'D', SNil{}), ci0(k, 'd', 'D')), alt2(k, ABNF.string.case_insensitive("E"), [ABNF.string.case_insensitive("F")], SNil{}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("E"), SNil{}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('e'), ABNF.char('E')]), ABNF.empty]), SNil{}), False{}, ciL(k, 'E', SNil{}), ci0(k, 'e', 'E')), alt2(k, ABNF.string.case_insensitive("F"), [], SNil{}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("F"), SNil{}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('f'), ABNF.char('F')]), ABNF.empty]), SNil{}), False{}, ciL(k, 'F', SNil{}), ci0(k, 'f', 'F')), ABNF.alt.nil(k, SNil{})))))))))

def hex2(+k: ABNF.Book, +a: Char, +b: Char, +t: String) -> {ABNF.check(k, HEX, SCon{a, SCon{b, t}}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(k, HEX, SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.alt([ABNF.core.digit, ABNF.string.case_insensitive("A"), ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")]), SCon{a, SCon{b, t}}), False{}, ABNF.core.hexdig.ok(k, SCon{a, SCon{b, t}}),
    alt2(k, ABNF.core.digit, [ABNF.string.case_insensitive("A"), ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{a, SCon{b, t}}, False{}, False{}, cd2(k, a, b, t), alt2(k, ABNF.string.case_insensitive("A"), [ABNF.string.case_insensitive("B"), ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{a, SCon{b, t}}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("A"), SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('a'), ABNF.char('A')]), ABNF.empty]), SCon{a, SCon{b, t}}), False{}, ciL(k, 'A', SCon{a, SCon{b, t}}), ci2(k, 'a', 'A', a, b, t)), alt2(k, ABNF.string.case_insensitive("B"), [ABNF.string.case_insensitive("C"), ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{a, SCon{b, t}}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("B"), SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('b'), ABNF.char('B')]), ABNF.empty]), SCon{a, SCon{b, t}}), False{}, ciL(k, 'B', SCon{a, SCon{b, t}}), ci2(k, 'b', 'B', a, b, t)), alt2(k, ABNF.string.case_insensitive("C"), [ABNF.string.case_insensitive("D"), ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{a, SCon{b, t}}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("C"), SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('c'), ABNF.char('C')]), ABNF.empty]), SCon{a, SCon{b, t}}), False{}, ciL(k, 'C', SCon{a, SCon{b, t}}), ci2(k, 'c', 'C', a, b, t)), alt2(k, ABNF.string.case_insensitive("D"), [ABNF.string.case_insensitive("E"), ABNF.string.case_insensitive("F")], SCon{a, SCon{b, t}}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("D"), SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('d'), ABNF.char('D')]), ABNF.empty]), SCon{a, SCon{b, t}}), False{}, ciL(k, 'D', SCon{a, SCon{b, t}}), ci2(k, 'd', 'D', a, b, t)), alt2(k, ABNF.string.case_insensitive("E"), [ABNF.string.case_insensitive("F")], SCon{a, SCon{b, t}}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("E"), SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('e'), ABNF.char('E')]), ABNF.empty]), SCon{a, SCon{b, t}}), False{}, ciL(k, 'E', SCon{a, SCon{b, t}}), ci2(k, 'e', 'E', a, b, t)), alt2(k, ABNF.string.case_insensitive("F"), [], SCon{a, SCon{b, t}}, False{}, False{}, Equal.trans(Bool, ABNF.check(k, ABNF.string.case_insensitive("F"), SCon{a, SCon{b, t}}), ABNF.check(k, ABNF.seq([ABNF.alt([ABNF.char('f'), ABNF.char('F')]), ABNF.empty]), SCon{a, SCon{b, t}}), False{}, ciL(k, 'F', SCon{a, SCon{b, t}}), ci2(k, 'f', 'F', a, b, t)), ABNF.alt.nil(k, SCon{a, SCon{b, t}})))))))))

def esctS(+c: Char, +h: {issimple(c) == True{} : Bool}) -> {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}:
  either(&2, &2, {Char.is_eq('"', c) == True{} : Bool}, {Bool.or(Char.is_eq('\\', c), Bool.or(Char.is_eq('/', c), Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{}))))))) == True{} : Bool}, {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, or_elim(Char.is_eq('"', c), Bool.or(Char.is_eq('\\', c), Bool.or(Char.is_eq('/', c), Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{}))))))), h), +h0 => altL(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, tt(ABNF.check(BK, ABNF.char('"'), SCon{c, SNil{}}), Char.is_eq('"', c), ABNF.char.one(BK, '"', c), h0)), +g0 => either(&2, &2, {Char.is_eq('\\', c) == True{} : Bool}, {Bool.or(Char.is_eq('/', c), Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{})))))) == True{} : Bool}, {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, or_elim(Char.is_eq('\\', c), Bool.or(Char.is_eq('/', c), Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{})))))), g0), +h1 => altR(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altL(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, tt(ABNF.check(BK, ABNF.char('\\'), SCon{c, SNil{}}), Char.is_eq('\\', c), ABNF.char.one(BK, '\\', c), h1))), +g1 => either(&2, &2, {Char.is_eq('/', c) == True{} : Bool}, {Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{}))))) == True{} : Bool}, {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, or_elim(Char.is_eq('/', c), Bool.or(Char.is_eq('b', c), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{}))))), g1), +h2 => altR(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altL(BK, ABNF.char('/'), [ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, tt(ABNF.check(BK, ABNF.char('/'), SCon{c, SNil{}}), Char.is_eq('/', c), ABNF.char.one(BK, '/', c), h2)))), +g2 => either(&2, &2, {Char.is_eq('b', c) == True{} : Bool}, {Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{})))) == True{} : Bool}, {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, or_elim(Char.is_eq('b', c), Bool.or(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{})))), g2), +h3 => altR(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('/'), [ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altL(BK, ABNF.char('b'), [ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, tt(ABNF.check(BK, ABNF.char('b'), SCon{c, SNil{}}), Char.is_eq('b', c), ABNF.char.one(BK, 'b', c), h3))))), +g3 => either(&2, &2, {Char.is_eq('f', c) == True{} : Bool}, {Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{}))) == True{} : Bool}, {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, or_elim(Char.is_eq('f', c), Bool.or(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{}))), g3), +h4 => altR(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('/'), [ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('b'), [ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altL(BK, ABNF.char('f'), [ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, tt(ABNF.check(BK, ABNF.char('f'), SCon{c, SNil{}}), Char.is_eq('f', c), ABNF.char.one(BK, 'f', c), h4)))))), +g4 => either(&2, &2, {Char.is_eq('n', c) == True{} : Bool}, {Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{})) == True{} : Bool}, {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, or_elim(Char.is_eq('n', c), Bool.or(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{})), g4), +h5 => altR(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('/'), [ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('b'), [ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('f'), [ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altL(BK, ABNF.char('n'), [ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, tt(ABNF.check(BK, ABNF.char('n'), SCon{c, SNil{}}), Char.is_eq('n', c), ABNF.char.one(BK, 'n', c), h5))))))), +g5 => either(&2, &2, {Char.is_eq('r', c) == True{} : Bool}, {Bool.or(Char.is_eq('t', c), False{}) == True{} : Bool}, {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, or_elim(Char.is_eq('r', c), Bool.or(Char.is_eq('t', c), False{}), g5), +h6 => altR(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('/'), [ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('b'), [ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('f'), [ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('n'), [ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altL(BK, ABNF.char('r'), [ABNF.char('t'), UESC], SCon{c, SNil{}}, tt(ABNF.check(BK, ABNF.char('r'), SCon{c, SNil{}}), Char.is_eq('r', c), ABNF.char.one(BK, 'r', c), h6)))))))), +g6 => either(&2, &2, {Char.is_eq('t', c) == True{} : Bool}, {False{} == True{} : Bool}, {ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, or_elim(Char.is_eq('t', c), False{}, g6), +h7 => altR(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('/'), [ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('b'), [ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('f'), [ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('n'), [ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, SNil{}}, altR(BK, ABNF.char('r'), [ABNF.char('t'), UESC], SCon{c, SNil{}}, altL(BK, ABNF.char('t'), [UESC], SCon{c, SNil{}}, tt(ABNF.check(BK, ABNF.char('t'), SCon{c, SNil{}}), Char.is_eq('t', c), ABNF.char.one(BK, 't', c), h7))))))))), +g7 => Empty.absurd({ABNF.check(BK, ESCT, SCon{c, SNil{}}) == True{} : Bool}, false_ne_true(g7))))))))))

def unesc_ne(+x: Char, +c: Char, +h: {isunesc(c) == True{} : Bool}, +hx: {isunesc(x) == False{} : Bool}) -> {Char.is_eq(x, c) == False{} : Bool}:
  bcase({Char.is_eq(x, c) == False{} : Bool}, Char.is_eq(x, c),
    +kk => Empty.absurd({Char.is_eq(x, c) == False{} : Bool}, false_ne_true(Equal.trans(Bool, False{}, isunesc(c), True{}, Equal.trans(Bool, False{}, isunesc(x), isunesc(c), Equal.sym(Bool, isunesc(x), False{}, hx), Equal.cong(Char, Bool, z => isunesc(z), x, c, char_eq(x, c, kk))), h))),
    +kk => kk)

def charU(+c: Char, +hc: {isunesc(c) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("char"), SCon{c, SNil{}}) == True{} : Bool}:
  MBi("char", B_char, SCon{c, SNil{}}, {==}, altL(BK, ABNF.ref("unescaped"), [ABNF.seq([ABNF.ref("escape"), ESCT])], SCon{c, SNil{}},
    MBi("unescaped", B_unesc, SCon{c, SNil{}}, {==}, tt(ABNF.check(BK, B_unesc, SCon{c, SNil{}}), isunesc(c), unesc1(BK, c), hc))))

def charE(+c: Char, +a: String, +hc: {Char.is_eq('\\', c) == True{} : Bool}, +h: {ABNF.check(BK, ESCT, a) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("char"), SCon{c, a}) == True{} : Bool}:
  MBi("char", B_char, SCon{c, a}, {==}, altR(BK, ABNF.ref("unescaped"), [ABNF.seq([ABNF.ref("escape"), ESCT])], SCon{c, a},
    altL(BK, ABNF.seq([ABNF.ref("escape"), ESCT]), [], SCon{c, a}, seqI2(BK, ABNF.ref("escape"), ESCT, SCon{c, SNil{}}, a, refCi("escape", '\\', c, {==}, hc), h))))

def escA.go(+c: Char, -a: String, +a1: String, +a2: String, +e: {String.append(a1, a2) == a : String}, +hc: {Char.is_eq('\\', c) == True{} : Bool}, +h1: {ABNF.check(BK, ESCT, a1) == True{} : Bool}, +h2: {ABNF.check(BK, CHARS, a2) == True{} : Bool})
  -> {ABNF.check(BK, CHARS, SCon{c, a}) == True{} : Bool}:
  %Equal.sym(String, a, String.append(a1, a2), Equal.sym(String, String.append(a1, a2), a, e)) : {ABNF.check(BK, CHARS, SCon{c, _}) == True{} : Bool}
  starCons(BK, ABNF.ref("char"), SCon{c, a1}, a2, charE(c, a1, hc, h1), h2)

def escA(+c: Char, +a: String, +hc: {Char.is_eq('\\', c) == True{} : Bool}, +h: {ABNF.check(BK, ABNF.seq([ESCT, CHARS]), a) == True{} : Bool}) -> {ABNF.check(BK, CHARS, SCon{c, a}) == True{} : Bool}:
  seqE2({ABNF.check(BK, CHARS, SCon{c, a}) == True{} : Bool}, BK, ESCT, CHARS, a, h, +a1 => +a2 => +e => +h1 => +h2 => escA.go(c, a, a1, a2, e, hc, h1, h2))

def uescA.go(+c: Char, -a: String, +a1: String, +a2: String, +e: {String.append(a1, a2) == a : String}, +hc: {Char.is_eq('u', c) == True{} : Bool}, +h1: {ABNF.check(BK, ABNF.rep.exactly(4n, HEX), a1) == True{} : Bool}, +h2: {ABNF.check(BK, CHARS, a2) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ESCT, CHARS]), SCon{c, a}) == True{} : Bool}:
  %Equal.sym(String, a, String.append(a1, a2), Equal.sym(String, String.append(a1, a2), a, e)) : {ABNF.check(BK, ABNF.seq([ESCT, CHARS]), SCon{c, _}) == True{} : Bool}
  seqI2(BK, ESCT, CHARS, SCon{c, a1}, a2, altR(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, a1}, altR(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, a1}, altR(BK, ABNF.char('/'), [ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, a1}, altR(BK, ABNF.char('b'), [ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, a1}, altR(BK, ABNF.char('f'), [ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, a1}, altR(BK, ABNF.char('n'), [ABNF.char('r'), ABNF.char('t'), UESC], SCon{c, a1}, altR(BK, ABNF.char('r'), [ABNF.char('t'), UESC], SCon{c, a1}, altR(BK, ABNF.char('t'), [UESC], SCon{c, a1}, altL(BK, UESC, [], SCon{c, a1}, seqI2(BK, ABNF.char('u'), ABNF.rep.exactly(4n, HEX), SCon{c, SNil{}}, a1, tt(ABNF.check(BK, ABNF.char('u'), SCon{c, SNil{}}), Char.is_eq('u', c), ABNF.char.one(BK, 'u', c), hc), h1)))))))))), h2)

def uescA(+c: Char, +a: String, +hc: {Char.is_eq('u', c) == True{} : Bool}, +h: {ABNF.check(BK, ABNF.seq([ABNF.rep.exactly(4n, HEX), CHARS]), a) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ESCT, CHARS]), SCon{c, a}) == True{} : Bool}:
  seqE2({ABNF.check(BK, ABNF.seq([ESCT, CHARS]), SCon{c, a}) == True{} : Bool}, BK, ABNF.rep.exactly(4n, HEX), CHARS, a, h, +a1 => +a2 => +e => +h1 => +h2 => uescA.go(c, a, a1, a2, e, hc, h1, h2))

def hexA.go(+c: Char, +n: Nat, -a: String, +a1: String, +a2: String, +e: {String.append(a1, a2) == a : String}, +hc: {ishex(c) == True{} : Bool}, +h1: {ABNF.check(BK, ABNF.rep.exactly(1n+n, HEX), a1) == True{} : Bool}, +h2: {ABNF.check(BK, CHARS, a2) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.rep.exactly(1n+1n+n, HEX), CHARS]), SCon{c, a}) == True{} : Bool}:
  %Equal.sym(String, a, String.append(a1, a2), Equal.sym(String, String.append(a1, a2), a, e)) : {ABNF.check(BK, ABNF.seq([ABNF.rep.exactly(1n+1n+n, HEX), CHARS]), SCon{c, _}) == True{} : Bool}
  seqI2(BK, ABNF.rep.exactly(1n+1n+n, HEX), CHARS, SCon{c, a1}, a2, exSi(BK, 1n+n, HEX, SCon{c, a1}, seqI2(BK, HEX, ABNF.rep.exactly(1n+n, HEX), SCon{c, SNil{}}, a1, tt(ABNF.check(BK, HEX, SCon{c, SNil{}}), ishex(c), hex1(BK, c), hc), h1)), h2)

def hexA(+c: Char, +n: Nat, +a: String, +hc: {ishex(c) == True{} : Bool}, +h: {ABNF.check(BK, ABNF.seq([ABNF.rep.exactly(1n+n, HEX), CHARS]), a) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ABNF.rep.exactly(1n+1n+n, HEX), CHARS]), SCon{c, a}) == True{} : Bool}:
  seqE2({ABNF.check(BK, ABNF.seq([ABNF.rep.exactly(1n+1n+n, HEX), CHARS]), SCon{c, a}) == True{} : Bool}, BK, ABNF.rep.exactly(1n+n, HEX), CHARS, a, h, +a1 => +a2 => +e => +h1 => +h2 => hexA.go(c, n, a, a1, a2, e, hc, h1, h2))

def hexA0(+c: Char, +a: String, +hc: {ishex(c) == True{} : Bool}, +h: {ABNF.check(BK, CHARS, a) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ABNF.rep.exactly(1n, HEX), CHARS]), SCon{c, a}) == True{} : Bool}:
  seqI2(BK, ABNF.rep.exactly(1n, HEX), CHARS, SCon{c, SNil{}}, a, exSi(BK, 0n, HEX, SCon{c, SNil{}}, seqI2(BK, HEX, ABNF.rep.exactly(0n, HEX), SCon{c, SNil{}}, SNil{}, tt(ABNF.check(BK, HEX, SCon{c, SNil{}}), ishex(c), hex1(BK, c), hc), exZi(BK, HEX, SNil{}, ABNF.empty.nil(BK)))), h)

def strS.q(+c: Char, +t: String, +h: {Char.is_eq('"', c) == True{} : Bool}) -> SNS(str_scan(SCon{c, t}, SN{}), SCon{c, t}, STR(SN{})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SN{}), Some{SP{SNil{}, t}}, selT(Maybe<&2, SP>, Char.is_eq('"', c), u => Some{SP{SNil{}, t}}, u => sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), h)) : SNS(_, SCon{c, t}, STR(SN{}))
  (Equal.cong(Char, String, z => SCon{z, t}, '"', c, char_eq('"', c, h)), starNil(BK, ABNF.ref("char")))

def strS.bs(+c: Char, +t: String, +h: {Char.is_eq('"', c) == False{} : Bool}, +h2: {Char.is_eq('\\', c) == True{} : Bool}, ih: SNS(str_scan(t, SE{}), t, STR(SE{}))) -> SNS(str_scan(SCon{c, t}, SN{}), SCon{c, t}, STR(SN{})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SN{}), sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), selF(Maybe<&2, SP>, Char.is_eq('"', c), u => Some{SP{SNil{}, t}}, u => sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), h)) : SNS(_, SCon{c, t}, STR(SN{}))
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), prepM(c, str_scan(t, SE{})), selT(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}), h2)) : SNS(_, SCon{c, t}, STR(SN{}))
  SNSmap(c, str_scan(t, SE{}), t, STR(SE{}), CHARS, ih, +a => +ha => escA(c, a, h2, ha))

def strS.u(+c: Char, +t: String, +h: {Char.is_eq('"', c) == False{} : Bool}, +h2: {Char.is_eq('\\', c) == False{} : Bool}, +h3: {isunesc(c) == True{} : Bool}, ih: SNS(str_scan(t, SN{}), t, CHARS)) -> SNS(str_scan(SCon{c, t}, SN{}), SCon{c, t}, STR(SN{})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SN{}), sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), selF(Maybe<&2, SP>, Char.is_eq('"', c), u => Some{SP{SNil{}, t}}, u => sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), h)) : SNS(_, SCon{c, t}, STR(SN{}))
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}), selF(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}), h2)) : SNS(_, SCon{c, t}, STR(SN{}))
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}), prepM(c, str_scan(t, SN{})), selT(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}, h3)) : SNS(_, SCon{c, t}, STR(SN{}))
  SNSmap(c, str_scan(t, SN{}), t, CHARS, CHARS, ih, +a => +ha => starCons(BK, ABNF.ref("char"), SCon{c, SNil{}}, a, charU(c, h3), ha))

def strS.n(+c: Char, +t: String, +h: {Char.is_eq('"', c) == False{} : Bool}, +h2: {Char.is_eq('\\', c) == False{} : Bool}, +h3: {isunesc(c) == False{} : Bool}) -> SNS(str_scan(SCon{c, t}, SN{}), SCon{c, t}, STR(SN{})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SN{}), sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), selF(Maybe<&2, SP>, Char.is_eq('"', c), u => Some{SP{SNil{}, t}}, u => sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), h)) : SNS(_, SCon{c, t}, STR(SN{}))
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{})), sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}), selF(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(t, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}), h2)) : SNS(_, SCon{c, t}, STR(SN{}))
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}), None{}, selF(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(t, SN{})), u => None{}, h3)) : SNS(_, SCon{c, t}, STR(SN{}))
  Unit{}

def strS.es(+c: Char, +t: String, +h: {issimple(c) == True{} : Bool}, ih: SNS(str_scan(t, SN{}), t, CHARS)) -> SNS(str_scan(SCon{c, t}, SE{}), SCon{c, t}, STR(SE{})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SE{}), prepM(c, str_scan(t, SN{})), selT(Maybe<&2, SP>, issimple(c), u => prepM(c, str_scan(t, SN{})), u => sel(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}), h)) : SNS(_, SCon{c, t}, STR(SE{}))
  SNSmap(c, str_scan(t, SN{}), t, CHARS, ABNF.seq([ESCT, CHARS]), ih, +a => +ha => seqI2(BK, ESCT, CHARS, SCon{c, SNil{}}, a, esctS(c, h), ha))

def strS.eu(+c: Char, +t: String, +h: {issimple(c) == False{} : Bool}, +h2: {Char.is_eq('u', c) == True{} : Bool}, ih: SNS(str_scan(t, SH{3n}), t, STR(SH{3n}))) -> SNS(str_scan(SCon{c, t}, SE{}), SCon{c, t}, STR(SE{})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SE{}), sel(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}), selF(Maybe<&2, SP>, issimple(c), u => prepM(c, str_scan(t, SN{})), u => sel(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}), h)) : SNS(_, SCon{c, t}, STR(SE{}))
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}), prepM(c, str_scan(t, SH{3n})), selT(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}, h2)) : SNS(_, SCon{c, t}, STR(SE{}))
  SNSmap(c, str_scan(t, SH{3n}), t, STR(SH{3n}), ABNF.seq([ESCT, CHARS]), ih, +a => +ha => uescA(c, a, h2, ha))

def strS.en(+c: Char, +t: String, +h: {issimple(c) == False{} : Bool}, +h2: {Char.is_eq('u', c) == False{} : Bool}) -> SNS(str_scan(SCon{c, t}, SE{}), SCon{c, t}, STR(SE{})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SE{}), sel(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}), selF(Maybe<&2, SP>, issimple(c), u => prepM(c, str_scan(t, SN{})), u => sel(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}), h)) : SNS(_, SCon{c, t}, STR(SE{}))
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}), None{}, selF(Maybe<&2, SP>, Char.is_eq('u', c), u => prepM(c, str_scan(t, SH{3n})), u => None{}, h2)) : SNS(_, SCon{c, t}, STR(SE{}))
  Unit{}

def strS.h0(+c: Char, +t: String, +h: {ishex(c) == True{} : Bool}, ih: SNS(str_scan(t, SN{}), t, CHARS)) -> SNS(str_scan(SCon{c, t}, SH{0n}), SCon{c, t}, STR(SH{0n})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SH{0n}), prepM(c, str_scan(t, SN{})), selT(Maybe<&2, SP>, ishex(c), u => prepM(c, str_scan(t, SN{})), u => None{}, h)) : SNS(_, SCon{c, t}, STR(SH{0n}))
  SNSmap(c, str_scan(t, SN{}), t, CHARS, STR(SH{0n}), ih, +a => +ha => hexA0(c, a, h, ha))

def strS.h1(+c: Char, +n: Nat, +t: String, +h: {ishex(c) == True{} : Bool}, ih: SNS(str_scan(t, SH{n}), t, STR(SH{n}))) -> SNS(str_scan(SCon{c, t}, SH{1n+n}), SCon{c, t}, STR(SH{1n+n})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SH{1n+n}), prepM(c, str_scan(t, SH{n})), selT(Maybe<&2, SP>, ishex(c), u => prepM(c, str_scan(t, SH{n})), u => None{}, h)) : SNS(_, SCon{c, t}, STR(SH{1n+n}))
  SNSmap(c, str_scan(t, SH{n}), t, STR(SH{n}), STR(SH{1n+n}), ih, +a => +ha => hexA(c, n, a, h, ha))

def strS.hn(+c: Char, +n: Nat, +t: String, +h: {ishex(c) == False{} : Bool}) -> SNS(str_scan(SCon{c, t}, SH{n}), SCon{c, t}, STR(SH{n})):
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, t}, SH{n}), None{}, selF(Maybe<&2, SP>, ishex(c), u => prepM(c, str_scan(t, hnext(n))), u => None{}, h)) : SNS(_, SCon{c, t}, STR(SH{n}))
  Unit{}

# What str_scan reads is a string's text, up to its closing quote.
def strS(s: String, st: SS) -> SNS(str_scan(s, st), s, STR(st)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      match st:
        case SN{}:
          bcase(SNS(str_scan(SCon{c, t}, SN{}), SCon{c, t}, STR(SN{})), Char.is_eq('"', c), +h => strS.q(c, t, h),
            +h => bcase(SNS(str_scan(SCon{c, t}, SN{}), SCon{c, t}, STR(SN{})), Char.is_eq('\\', c), +h2 => strS.bs(c, t, h, h2, strS(t, SE{})),
              +h2 => bcase(SNS(str_scan(SCon{c, t}, SN{}), SCon{c, t}, STR(SN{})), isunesc(c), +h3 => strS.u(c, t, h, h2, h3, strS(t, SN{})), +h3 => strS.n(c, t, h, h2, h3))))
        case SE{}:
          bcase(SNS(str_scan(SCon{c, t}, SE{}), SCon{c, t}, STR(SE{})), issimple(c), +h => strS.es(c, t, h, strS(t, SN{})),
            +h => bcase(SNS(str_scan(SCon{c, t}, SE{}), SCon{c, t}, STR(SE{})), Char.is_eq('u', c), +h2 => strS.eu(c, t, h, h2, strS(t, SH{3n})), +h2 => strS.en(c, t, h, h2)))
        case SH{n}:
          match n:
            case 0n:
              bcase(SNS(str_scan(SCon{c, t}, SH{0n}), SCon{c, t}, STR(SH{0n})), ishex(c), +h => strS.h0(c, t, h, strS(t, SN{})), +h => strS.hn(c, 0n, t, h))
            case 1n+ +n1:
              bcase(SNS(str_scan(SCon{c, t}, SH{1n+n1}), SCon{c, t}, STR(SH{1n+n1})), ishex(c), +h => strS.h1(c, n1, t, h, strS(t, SH{n1})), +h => strS.hn(c, 1n+n1, t, h))

def prepApp(+c: Char, m: Maybe<&2, SP>) -> {prepM(c, m) == appM(SCon{c, SNil{}}, m) : Maybe<&2, SP>}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      {==}

def prepApp2(+c1: Char, +c2: Char, m: Maybe<&2, SP>) -> {prepM(c1, prepM(c2, m)) == appM(SCon{c1, SCon{c2, SNil{}}}, m) : Maybe<&2, SP>}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      {==}

def prepApp6(+c1: Char, +c2: Char, +c3: Char, +c4: Char, +c5: Char, +c6: Char, m: Maybe<&2, SP>) -> {prepM(c1, prepM(c2, prepM(c3, prepM(c4, prepM(c5, prepM(c6, m)))))) == appM(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}, m) : Maybe<&2, SP>}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      {==}

def strH(+x: Char, -X: String, +n: Nat, +h: {ishex(x) == True{} : Bool}) -> {str_scan(SCon{x, X}, SH{n}) == prepM(x, str_scan(X, hnext(n))) : Maybe<&2, SP>}:
  selT(Maybe<&2, SP>, ishex(x), u => prepM(x, str_scan(X, hnext(n))), u => None{}, h)

def strC1.u(+c: Char, -a: String, +R: String, +ec: {SCon{c, SNil{}} == a : String}, +hc: {isunesc(c) == True{} : Bool}) -> {str_scan(String.append(a, R), SN{}) == appM(a, str_scan(R, SN{})) : Maybe<&2, SP>}:
  %ec : {str_scan(String.append(_, R), SN{}) == appM(_, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{c, R}, SN{}), sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(R, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(R, SN{})), u => None{})), selF(Maybe<&2, SP>, Char.is_eq('"', c), u => Some{SP{SNil{}, R}}, u => sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(R, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(R, SN{})), u => None{})), unesc_ne('"', c, hc, {==}))) : {_ == appM(SCon{c, SNil{}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(R, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(R, SN{})), u => None{})), sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(R, SN{})), u => None{}), selF(Maybe<&2, SP>, Char.is_eq('\\', c), u => prepM(c, str_scan(R, SE{})), u => sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(R, SN{})), u => None{}), unesc_ne('\\', c, hc, {==}))) : {_ == appM(SCon{c, SNil{}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(R, SN{})), u => None{}), prepM(c, str_scan(R, SN{})), selT(Maybe<&2, SP>, isunesc(c), u => prepM(c, str_scan(R, SN{})), u => None{}, hc)) : {_ == appM(SCon{c, SNil{}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  prepApp(c, str_scan(R, SN{}))

def strC1.lit2(+l: Char, +R: String, +hl: {issimple(l) == True{} : Bool}) -> {str_scan(SCon{'\\', SCon{l, R}}, SN{}) == appM(SCon{'\\', SCon{l, SNil{}}}, str_scan(R, SN{})) : Maybe<&2, SP>}:
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{l, R}, SE{}), prepM(l, str_scan(R, SN{})), selT(Maybe<&2, SP>, issimple(l), u => prepM(l, str_scan(R, SN{})), u => sel(Maybe<&2, SP>, Char.is_eq('u', l), u => prepM(l, str_scan(R, SH{3n})), u => None{}), hl)) : {prepM('\\', _) == appM(SCon{'\\', SCon{l, SNil{}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  prepApp2('\\', l, str_scan(R, SN{}))

def strC1.lit(+l: Char, +x: Char, -e2: String, +R: String, +ex: {SCon{x, SNil{}} == e2 : String}, +hx: {ABNF.check(BK, ABNF.char(l), SCon{x, SNil{}}) == True{} : Bool}, +hl: {issimple(l) == True{} : Bool}) -> {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}:
  %ex : {str_scan(SCon{'\\', String.append(_, R)}, SN{}) == appM(SCon{'\\', _}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(Char, x, l, Equal.sym(Char, l, x, char_eq(l, x, tt.sym(ABNF.check(BK, ABNF.char(l), SCon{x, SNil{}}), Char.is_eq(l, x), ABNF.char.one(BK, l, x), hx)))) : {str_scan(SCon{'\\', SCon{_, R}}, SN{}) == appM(SCon{'\\', SCon{_, SNil{}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  strC1.lit2(l, R, hl)

def charIs.go(+ch: Char, -s: String, +x: Char, +ex: {SCon{x, SNil{}} == s : String}, +hx: {Char.is_eq(ch, x) == True{} : Bool}) -> {s == SCon{ch, SNil{}} : String}:
  %Equal.sym(String, s, SCon{x, SNil{}}, Equal.sym(String, SCon{x, SNil{}}, s, ex)) : {_ == SCon{ch, SNil{}} : String}
  %char_eq(ch, x, hx) : {SCon{_, SNil{}} == SCon{ch, SNil{}} : String}
  {==}

def charIs(+k: ABNF.Book, +ch: Char, +s: String, +h: {ABNF.check(k, ABNF.char(ch), s) == True{} : Bool}) -> {s == SCon{ch, SNil{}} : String}:
  one({s == SCon{ch, SNil{}} : String}, k, ABNF.char(ch), s, h, ABNF.char.nil(k, ch), x => y => z => ABNF.char.many(k, ch, x, y, z),
    +x => +ex => +hx => charIs.go(ch, s, x, ex, tt.sym(ABNF.check(k, ABNF.char(ch), SCon{x, SNil{}}), Char.is_eq(ch, x), ABNF.char.one(k, ch, x), hx)))

def hexPeel(-C: Type, +n: Nat, +s: String, +h: {ABNF.check(BK, ABNF.rep.exactly(1n+n, HEX), s) == True{} : Bool},
  f: @x: Char -> @r: String -> {SCon{x, r} == s : String} -> {ishex(x) == True{} : Bool} -> {ABNF.check(BK, ABNF.rep.exactly(n, HEX), r) == True{} : Bool} -> C) -> C:
  seqE2(C, BK, HEX, ABNF.rep.exactly(n, HEX), s, exSe(BK, n, HEX, s, h), +a => +r => +e => +ha => +hr =>
    one(C, BK, HEX, a, ha, hex0(BK), x => y => z => hex2(BK, x, y, z), +x => +ex => +hx =>
      f(x, r, Equal.trans(String, SCon{x, r}, String.append(a, r), s, app_congr(r, SCon{x, SNil{}}, a, ex), e), tt.sym(ABNF.check(BK, HEX, SCon{x, SNil{}}), ishex(x), hex1(BK, x), hx), hr)))

def strC1.ue.go(-e2: String, +R: String, -u1: String, -h4: String, +x1: Char, -r1: String, +x2: Char, -r2: String, +x3: Char, -r3: String, +x4: Char, -r4: String,
  +e: {String.append(u1, h4) == e2 : String}, +eu: {u1 == SCon{'u', SNil{}} : String}, +e1: {SCon{x1, r1} == h4 : String}, +e2b: {SCon{x2, r2} == r1 : String}, +e3: {SCon{x3, r3} == r2 : String}, +e4: {SCon{x4, r4} == r3 : String}, +e5: {r4 == SNil{} : String},
  +hx1: {ishex(x1) == True{} : Bool}, +hx2: {ishex(x2) == True{} : Bool}, +hx3: {ishex(x3) == True{} : Bool}, +hx4: {ishex(x4) == True{} : Bool}) -> {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}:
  %e : {str_scan(SCon{'\\', String.append(_, R)}, SN{}) == appM(SCon{'\\', _}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(String, u1, SCon{'u', SNil{}}, eu) : {str_scan(SCon{'\\', String.append(String.append(_, h4), R)}, SN{}) == appM(SCon{'\\', String.append(_, h4)}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %e1 : {str_scan(SCon{'\\', String.append(SCon{'u', _}, R)}, SN{}) == appM(SCon{'\\', SCon{'u', _}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %e2b : {str_scan(SCon{'\\', String.append(SCon{'u', SCon{x1, _}}, R)}, SN{}) == appM(SCon{'\\', SCon{'u', SCon{x1, _}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %e3 : {str_scan(SCon{'\\', String.append(SCon{'u', SCon{x1, SCon{x2, _}}}, R)}, SN{}) == appM(SCon{'\\', SCon{'u', SCon{x1, SCon{x2, _}}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %e4 : {str_scan(SCon{'\\', String.append(SCon{'u', SCon{x1, SCon{x2, SCon{x3, _}}}}, R)}, SN{}) == appM(SCon{'\\', SCon{'u', SCon{x1, SCon{x2, SCon{x3, _}}}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(String, r4, SNil{}, e5) : {str_scan(SCon{'\\', String.append(SCon{'u', SCon{x1, SCon{x2, SCon{x3, SCon{x4, _}}}}}, R)}, SN{}) == appM(SCon{'\\', SCon{'u', SCon{x1, SCon{x2, SCon{x3, SCon{x4, _}}}}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{x1, SCon{x2, SCon{x3, SCon{x4, R}}}}, SH{3n}), prepM(x1, str_scan(SCon{x2, SCon{x3, SCon{x4, R}}}, SH{2n})), strH(x1, SCon{x2, SCon{x3, SCon{x4, R}}}, 3n, hx1)) : {prepM('\\', prepM('u', _)) == appM(SCon{'\\', SCon{'u', SCon{x1, SCon{x2, SCon{x3, SCon{x4, SNil{}}}}}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{x2, SCon{x3, SCon{x4, R}}}, SH{2n}), prepM(x2, str_scan(SCon{x3, SCon{x4, R}}, SH{1n})), strH(x2, SCon{x3, SCon{x4, R}}, 2n, hx2)) : {prepM('\\', prepM('u', prepM(x1, _))) == appM(SCon{'\\', SCon{'u', SCon{x1, SCon{x2, SCon{x3, SCon{x4, SNil{}}}}}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{x3, SCon{x4, R}}, SH{1n}), prepM(x3, str_scan(SCon{x4, R}, SH{0n})), strH(x3, SCon{x4, R}, 1n, hx3)) : {prepM('\\', prepM('u', prepM(x1, prepM(x2, _)))) == appM(SCon{'\\', SCon{'u', SCon{x1, SCon{x2, SCon{x3, SCon{x4, SNil{}}}}}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, str_scan(SCon{x4, R}, SH{0n}), prepM(x4, str_scan(R, SN{})), strH(x4, R, 0n, hx4)) : {prepM('\\', prepM('u', prepM(x1, prepM(x2, prepM(x3, _))))) == appM(SCon{'\\', SCon{'u', SCon{x1, SCon{x2, SCon{x3, SCon{x4, SNil{}}}}}}}, str_scan(R, SN{})) : Maybe<&2, SP>}
  prepApp6('\\', 'u', x1, x2, x3, x4, str_scan(R, SN{}))

def strC1.ue(+e2: String, +R: String, +h: {ABNF.check(BK, UESC, e2) == True{} : Bool}) -> {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}:
  seqE2({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('u'), ABNF.rep.exactly(4n, HEX), e2, h, +u1 => +h4 => +e => +hu => +hh =>
    hexPeel({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, 3n, h4, hh, +x1 => +r1 => +e1 => +hx1 => +h1 =>
      hexPeel({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, 2n, r1, h1, +x2 => +r2 => +e2b => +hx2 => +h2 =>
        hexPeel({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, 1n, r2, h2, +x3 => +r3 => +e3 => +hx3 => +h3 =>
          hexPeel({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, 0n, r3, h3, +x4 => +r4 => +e4 => +hx4 => +h5 =>
            strC1.ue.go(e2, R, u1, h4, x1, r1, x2, r2, x3, r3, x4, r4, e, charIs(BK, 'u', u1, hu), e1, e2b, e3, e4, emptyE(BK, r4, exZe(BK, HEX, r4, h5)), hx1, hx2, hx3, hx4))))))

def strC1.esct(+e2: String, +R: String, +h2: {ABNF.check(BK, ESCT, e2) == True{} : Bool}) -> {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}:
  either(&2, &2, {ABNF.check(BK, ABNF.char('"'), e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, ABNF.char('"'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), tt.sym(ABNF.check(BK, ABNF.alt([ABNF.char('"'), ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), Bool.or(ABNF.check(BK, ABNF.char('"'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2)), ABNF.alt.con(BK, ABNF.char('"'), [ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], e2), h2)), +h0 => one({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('"'), e2, h0, ABNF.char.nil(BK, '"'), x => y => z => ABNF.char.many(BK, '"', x, y, z), +x => +ex => +hx => strC1.lit('"', x, e2, R, ex, hx, {==})), +g0 => either(&2, &2, {ABNF.check(BK, ABNF.char('\\'), e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, ABNF.char('\\'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), tt.sym(ABNF.check(BK, ABNF.alt([ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), Bool.or(ABNF.check(BK, ABNF.char('\\'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2)), ABNF.alt.con(BK, ABNF.char('\\'), [ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], e2), g0)), +h1 => one({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('\\'), e2, h1, ABNF.char.nil(BK, '\\'), x => y => z => ABNF.char.many(BK, '\\', x, y, z), +x => +ex => +hx => strC1.lit('\\', x, e2, R, ex, hx, {==})), +g1 => either(&2, &2, {ABNF.check(BK, ABNF.char('/'), e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, ABNF.char('/'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), tt.sym(ABNF.check(BK, ABNF.alt([ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), Bool.or(ABNF.check(BK, ABNF.char('/'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2)), ABNF.alt.con(BK, ABNF.char('/'), [ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], e2), g1)), +h2 => one({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('/'), e2, h2, ABNF.char.nil(BK, '/'), x => y => z => ABNF.char.many(BK, '/', x, y, z), +x => +ex => +hx => strC1.lit('/', x, e2, R, ex, hx, {==})), +g2 => either(&2, &2, {ABNF.check(BK, ABNF.char('b'), e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, ABNF.char('b'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), tt.sym(ABNF.check(BK, ABNF.alt([ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), Bool.or(ABNF.check(BK, ABNF.char('b'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2)), ABNF.alt.con(BK, ABNF.char('b'), [ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], e2), g2)), +h3 => one({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('b'), e2, h3, ABNF.char.nil(BK, 'b'), x => y => z => ABNF.char.many(BK, 'b', x, y, z), +x => +ex => +hx => strC1.lit('b', x, e2, R, ex, hx, {==})), +g3 => either(&2, &2, {ABNF.check(BK, ABNF.char('f'), e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, ABNF.char('f'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), tt.sym(ABNF.check(BK, ABNF.alt([ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), Bool.or(ABNF.check(BK, ABNF.char('f'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2)), ABNF.alt.con(BK, ABNF.char('f'), [ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC], e2), g3)), +h4 => one({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('f'), e2, h4, ABNF.char.nil(BK, 'f'), x => y => z => ABNF.char.many(BK, 'f', x, y, z), +x => +ex => +hx => strC1.lit('f', x, e2, R, ex, hx, {==})), +g4 => either(&2, &2, {ABNF.check(BK, ABNF.char('n'), e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.char('r'), ABNF.char('t'), UESC]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, ABNF.char('n'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('r'), ABNF.char('t'), UESC]), e2), tt.sym(ABNF.check(BK, ABNF.alt([ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), UESC]), e2), Bool.or(ABNF.check(BK, ABNF.char('n'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('r'), ABNF.char('t'), UESC]), e2)), ABNF.alt.con(BK, ABNF.char('n'), [ABNF.char('r'), ABNF.char('t'), UESC], e2), g4)), +h5 => one({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('n'), e2, h5, ABNF.char.nil(BK, 'n'), x => y => z => ABNF.char.many(BK, 'n', x, y, z), +x => +ex => +hx => strC1.lit('n', x, e2, R, ex, hx, {==})), +g5 => either(&2, &2, {ABNF.check(BK, ABNF.char('r'), e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.char('t'), UESC]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, ABNF.char('r'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('t'), UESC]), e2), tt.sym(ABNF.check(BK, ABNF.alt([ABNF.char('r'), ABNF.char('t'), UESC]), e2), Bool.or(ABNF.check(BK, ABNF.char('r'), e2), ABNF.check(BK, ABNF.alt([ABNF.char('t'), UESC]), e2)), ABNF.alt.con(BK, ABNF.char('r'), [ABNF.char('t'), UESC], e2), g5)), +h6 => one({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('r'), e2, h6, ABNF.char.nil(BK, 'r'), x => y => z => ABNF.char.many(BK, 'r', x, y, z), +x => +ex => +hx => strC1.lit('r', x, e2, R, ex, hx, {==})), +g6 => either(&2, &2, {ABNF.check(BK, ABNF.char('t'), e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([UESC]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, ABNF.char('t'), e2), ABNF.check(BK, ABNF.alt([UESC]), e2), tt.sym(ABNF.check(BK, ABNF.alt([ABNF.char('t'), UESC]), e2), Bool.or(ABNF.check(BK, ABNF.char('t'), e2), ABNF.check(BK, ABNF.alt([UESC]), e2)), ABNF.alt.con(BK, ABNF.char('t'), [UESC], e2), g6)), +h7 => one({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.char('t'), e2, h7, ABNF.char.nil(BK, 't'), x => y => z => ABNF.char.many(BK, 't', x, y, z), +x => +ex => +hx => strC1.lit('t', x, e2, R, ex, hx, {==})), +g7 => either(&2, &2, {ABNF.check(BK, UESC, e2) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([]), e2) == True{} : Bool}, {str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, or_elim(ABNF.check(BK, UESC, e2), ABNF.check(BK, ABNF.alt([]), e2), tt.sym(ABNF.check(BK, ABNF.alt([UESC]), e2), Bool.or(ABNF.check(BK, UESC, e2), ABNF.check(BK, ABNF.alt([]), e2)), ABNF.alt.con(BK, UESC, [], e2), g7)), +h8 => strC1.ue(e2, R, h8), +g8 => Empty.absurd({str_scan(SCon{'\\', String.append(e2, R)}, SN{}) == appM(SCon{'\\', e2}, str_scan(R, SN{})) : Maybe<&2, SP>}, false_ne_true(Equal.trans(Bool, False{}, ABNF.check(BK, ABNF.alt([]), e2), True{}, Equal.sym(Bool, ABNF.check(BK, ABNF.alt([]), e2), False{}, ABNF.alt.nil(BK, e2)), g8))))))))))))

def strC1.esc(-a: String, -e1: String, +e2: String, +R: String, +e: {String.append(e1, e2) == a : String}, +ee: {SCon{'\\', SNil{}} == e1 : String}, +h2: {ABNF.check(BK, ESCT, e2) == True{} : Bool})
  -> {str_scan(String.append(a, R), SN{}) == appM(a, str_scan(R, SN{})) : Maybe<&2, SP>}:
  %e : {str_scan(String.append(_, R), SN{}) == appM(_, str_scan(R, SN{})) : Maybe<&2, SP>}
  %ee : {str_scan(String.append(String.append(_, e2), R), SN{}) == appM(String.append(_, e2), str_scan(R, SN{})) : Maybe<&2, SP>}
  strC1.esct(e2, R, h2)

# Scanning one char of a string's text does not depend on what follows it.
def strC1(+a: String, +R: String, +h: {ABNF.check(BK, ABNF.ref("char"), a) == True{} : Bool}) -> {str_scan(String.append(a, R), SN{}) == appM(a, str_scan(R, SN{})) : Maybe<&2, SP>}:
  either(&2, &2, {ABNF.check(BK, ABNF.ref("unescaped"), a) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("escape"), ESCT])]), a) == True{} : Bool}, {str_scan(String.append(a, R), SN{}) == appM(a, str_scan(R, SN{})) : Maybe<&2, SP>},
    or_elim(ABNF.check(BK, ABNF.ref("unescaped"), a), ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("escape"), ESCT])]), a),
      tt.sym(ABNF.check(BK, B_char, a), Bool.or(ABNF.check(BK, ABNF.ref("unescaped"), a), ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("escape"), ESCT])]), a)), ABNF.alt.con(BK, ABNF.ref("unescaped"), [ABNF.seq([ABNF.ref("escape"), ESCT])], a), MBe("char", B_char, a, {==}, h))),
    +hu => unescM({str_scan(String.append(a, R), SN{}) == appM(a, str_scan(R, SN{})) : Maybe<&2, SP>}, a, hu, +c => +ec => +hc => strC1.u(c, a, R, ec, hc)),
    +hs => seqE2({str_scan(String.append(a, R), SN{}) == appM(a, str_scan(R, SN{})) : Maybe<&2, SP>}, BK, ABNF.ref("escape"), ESCT, a, tt.sym(ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("escape"), ESCT])]), a), ABNF.check(BK, ABNF.seq([ABNF.ref("escape"), ESCT]), a), altS(BK, ABNF.seq([ABNF.ref("escape"), ESCT]), a), hs),
      +e1 => +e2 => +e => +h1 => +h2 => strC1.esc(a, e1, e2, R, e, escM(e1, h1), h2)))

def strC.step(-x: String, +a: String, +b: String, +t: String, +e: {String.append(a, b) == x : String}, +ha: {ABNF.check(BK, ABNF.ref("char"), a) == True{} : Bool}, +ih: {str_scan(String.append(b, SCon{'"', t}), SN{}) == Some{SP{b, t}} : Maybe<&2, SP>})
  -> {str_scan(String.append(x, SCon{'"', t}), SN{}) == Some{SP{x, t}} : Maybe<&2, SP>}:
  %e : {str_scan(String.append(_, SCon{'"', t}), SN{}) == Some{SP{_, t}} : Maybe<&2, SP>}
  %Equal.sym(String, String.append(String.append(a, b), SCon{'"', t}), String.append(a, String.append(b, SCon{'"', t})), app3(a, b, SCon{'"', t})) : {str_scan(_, SN{}) == Some{SP{String.append(a, b), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, str_scan(String.append(a, String.append(b, SCon{'"', t})), SN{}), appM(a, str_scan(String.append(b, SCon{'"', t}), SN{})), strC1(a, String.append(b, SCon{'"', t}), ha)) : {_ == Some{SP{String.append(a, b), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, str_scan(String.append(b, SCon{'"', t}), SN{}), Some{SP{b, t}}, ih) : {appM(a, _) == Some{SP{String.append(a, b), t}} : Maybe<&2, SP>}
  {==}

def strC.m(m: Nat, +x: String, +t: String, +h: {ABNF.check(BK, ABNF.rep.exactly(m, ABNF.ref("char")), x) == True{} : Bool}) -> {str_scan(String.append(x, SCon{'"', t}), SN{}) == Some{SP{x, t}} : Maybe<&2, SP>}:
  match m:
    case 0n:
      %Equal.sym(String, x, SNil{}, emptyE(BK, x, exZe(BK, ABNF.ref("char"), x, h))) : {str_scan(String.append(_, SCon{'"', t}), SN{}) == Some{SP{_, t}} : Maybe<&2, SP>}
      {==}
    case 1n+ +m1:
      seqE2({str_scan(String.append(x, SCon{'"', t}), SN{}) == Some{SP{x, t}} : Maybe<&2, SP>}, BK, ABNF.ref("char"), ABNF.rep.exactly(m1, ABNF.ref("char")), x, exSe(BK, m1, ABNF.ref("char"), x, h),
        +a => +b => +e => +ha => +hb => strC.step(x, a, b, t, e, ha, strC.m(m1, b, t, hb)))

def strC.go(+x: String, +t: String, p: &m: Nat -> {ABNF.check(BK, ABNF.rep.exactly(m, ABNF.ref("char")), x) == True{} : Bool}) -> {str_scan(String.append(x, SCon{'"', t}), SN{}) == Some{SP{x, t}} : Maybe<&2, SP>}:
  (m, h) = p
  strC.m(m, x, t, h)

# A string's text scans to itself, whatever follows its closing quote.
def strC(+x: String, +t: String, +h: {ABNF.check(BK, CHARS, x) == True{} : Bool}) -> {str_scan(String.append(x, SCon{'"', t}), SN{}) == Some{SP{x, t}} : Maybe<&2, SP>}:
  strC.go(x, t, ABNF.rep.any.elim(BK, ABNF.ref("char"), x, h))

# Character classes
# =================

def isfol(+c: Char) -> Bool:
  Bool.or(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))))

# fol(t): t may follow a value: it is empty, or starts with whitespace, a comma or a closing bracket.
def fol(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{c, r}:
      isfol(c)

def nd(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{c, r}:
      Bool.not(isdig(c))

def notdot(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{c, r}:
      Bool.not(Char.is_eq('.', c))

def notminus(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{c, r}:
      Bool.not(Char.is_eq('-', c))

def fol_dig(+c: Char, +h: {isfol(c) == True{} : Bool}) -> {isdig(c) == False{} : Bool}:
  either(&2, &2, {isws(c) == True{} : Bool}, {Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))) == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), h), +h0_4 => either(&2, &2, {Char.is_eq(Chr{32}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))) == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{32}, c), Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))), h0_4), +h1_4 => Equal.trans(Bool, isdig(c), isdig(Chr{32}), False{}, Equal.cong(Char, Bool, z => isdig(z), c, Chr{32}, Equal.sym(Char, Chr{32}, c, char_eq(Chr{32}, c, h1_4))), {==}), +g1_4 => either(&2, &2, {Char.is_eq(Chr{9}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})) == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})), g1_4), +h1_3 => Equal.trans(Bool, isdig(c), isdig(Chr{9}), False{}, Equal.cong(Char, Bool, z => isdig(z), c, Chr{9}, Equal.sym(Char, Chr{9}, c, char_eq(Chr{9}, c, h1_3))), {==}), +g1_3 => either(&2, &2, {Char.is_eq(Chr{10}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{13}, c), False{}) == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}), g1_3), +h1_2 => Equal.trans(Bool, isdig(c), isdig(Chr{10}), False{}, Equal.cong(Char, Bool, z => isdig(z), c, Chr{10}, Equal.sym(Char, Chr{10}, c, char_eq(Chr{10}, c, h1_2))), {==}), +g1_2 => either(&2, &2, {Char.is_eq(Chr{13}, c) == True{} : Bool}, {False{} == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{13}, c), False{}, g1_2), +h1_1 => Equal.trans(Bool, isdig(c), isdig(Chr{13}), False{}, Equal.cong(Char, Bool, z => isdig(z), c, Chr{13}, Equal.sym(Char, Chr{13}, c, char_eq(Chr{13}, c, h1_1))), {==}), +g1_1 => Empty.absurd({isdig(c) == False{} : Bool}, false_ne_true(g1_1)))))), +g0_4 => either(&2, &2, {Char.is_eq(',', c) == True{} : Bool}, {Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})) == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})), g0_4), +h0_3 => Equal.trans(Bool, isdig(c), isdig(','), False{}, Equal.cong(Char, Bool, z => isdig(z), c, ',', Equal.sym(Char, ',', c, char_eq(',', c, h0_3))), {==}), +g0_3 => either(&2, &2, {Char.is_eq(']', c) == True{} : Bool}, {Bool.or(Char.is_eq('}', c), False{}) == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}), g0_3), +h0_2 => Equal.trans(Bool, isdig(c), isdig(']'), False{}, Equal.cong(Char, Bool, z => isdig(z), c, ']', Equal.sym(Char, ']', c, char_eq(']', c, h0_2))), {==}), +g0_2 => either(&2, &2, {Char.is_eq('}', c) == True{} : Bool}, {False{} == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq('}', c), False{}, g0_2), +h0_1 => Equal.trans(Bool, isdig(c), isdig('}'), False{}, Equal.cong(Char, Bool, z => isdig(z), c, '}', Equal.sym(Char, '}', c, char_eq('}', c, h0_1))), {==}), +g0_1 => Empty.absurd({isdig(c) == False{} : Bool}, false_ne_true(g0_1))))))

def fol_dot(+c: Char, +h: {isfol(c) == True{} : Bool}) -> {Char.is_eq('.', c) == False{} : Bool}:
  either(&2, &2, {isws(c) == True{} : Bool}, {Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))) == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), h), +h0_4 => either(&2, &2, {Char.is_eq(Chr{32}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))) == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq(Chr{32}, c), Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))), h0_4), +h1_4 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', Chr{32}), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, Chr{32}, Equal.sym(Char, Chr{32}, c, char_eq(Chr{32}, c, h1_4))), {==}), +g1_4 => either(&2, &2, {Char.is_eq(Chr{9}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})) == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})), g1_4), +h1_3 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', Chr{9}), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, Chr{9}, Equal.sym(Char, Chr{9}, c, char_eq(Chr{9}, c, h1_3))), {==}), +g1_3 => either(&2, &2, {Char.is_eq(Chr{10}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{13}, c), False{}) == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}), g1_3), +h1_2 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', Chr{10}), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, Chr{10}, Equal.sym(Char, Chr{10}, c, char_eq(Chr{10}, c, h1_2))), {==}), +g1_2 => either(&2, &2, {Char.is_eq(Chr{13}, c) == True{} : Bool}, {False{} == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq(Chr{13}, c), False{}, g1_2), +h1_1 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', Chr{13}), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, Chr{13}, Equal.sym(Char, Chr{13}, c, char_eq(Chr{13}, c, h1_1))), {==}), +g1_1 => Empty.absurd({Char.is_eq('.', c) == False{} : Bool}, false_ne_true(g1_1)))))), +g0_4 => either(&2, &2, {Char.is_eq(',', c) == True{} : Bool}, {Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})) == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})), g0_4), +h0_3 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', ','), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, ',', Equal.sym(Char, ',', c, char_eq(',', c, h0_3))), {==}), +g0_3 => either(&2, &2, {Char.is_eq(']', c) == True{} : Bool}, {Bool.or(Char.is_eq('}', c), False{}) == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}), g0_3), +h0_2 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', ']'), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, ']', Equal.sym(Char, ']', c, char_eq(']', c, h0_2))), {==}), +g0_2 => either(&2, &2, {Char.is_eq('}', c) == True{} : Bool}, {False{} == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq('}', c), False{}, g0_2), +h0_1 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', '}'), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, '}', Equal.sym(Char, '}', c, char_eq('}', c, h0_1))), {==}), +g0_1 => Empty.absurd({Char.is_eq('.', c) == False{} : Bool}, false_ne_true(g0_1))))))

def fol_e(+c: Char, +h: {isfol(c) == True{} : Bool}) -> {ise(c) == False{} : Bool}:
  either(&2, &2, {isws(c) == True{} : Bool}, {Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))) == True{} : Bool}, {ise(c) == False{} : Bool}, or_elim(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), h), +h0_4 => either(&2, &2, {Char.is_eq(Chr{32}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))) == True{} : Bool}, {ise(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{32}, c), Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))), h0_4), +h1_4 => Equal.trans(Bool, ise(c), ise(Chr{32}), False{}, Equal.cong(Char, Bool, z => ise(z), c, Chr{32}, Equal.sym(Char, Chr{32}, c, char_eq(Chr{32}, c, h1_4))), {==}), +g1_4 => either(&2, &2, {Char.is_eq(Chr{9}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})) == True{} : Bool}, {ise(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})), g1_4), +h1_3 => Equal.trans(Bool, ise(c), ise(Chr{9}), False{}, Equal.cong(Char, Bool, z => ise(z), c, Chr{9}, Equal.sym(Char, Chr{9}, c, char_eq(Chr{9}, c, h1_3))), {==}), +g1_3 => either(&2, &2, {Char.is_eq(Chr{10}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{13}, c), False{}) == True{} : Bool}, {ise(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}), g1_3), +h1_2 => Equal.trans(Bool, ise(c), ise(Chr{10}), False{}, Equal.cong(Char, Bool, z => ise(z), c, Chr{10}, Equal.sym(Char, Chr{10}, c, char_eq(Chr{10}, c, h1_2))), {==}), +g1_2 => either(&2, &2, {Char.is_eq(Chr{13}, c) == True{} : Bool}, {False{} == True{} : Bool}, {ise(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{13}, c), False{}, g1_2), +h1_1 => Equal.trans(Bool, ise(c), ise(Chr{13}), False{}, Equal.cong(Char, Bool, z => ise(z), c, Chr{13}, Equal.sym(Char, Chr{13}, c, char_eq(Chr{13}, c, h1_1))), {==}), +g1_1 => Empty.absurd({ise(c) == False{} : Bool}, false_ne_true(g1_1)))))), +g0_4 => either(&2, &2, {Char.is_eq(',', c) == True{} : Bool}, {Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})) == True{} : Bool}, {ise(c) == False{} : Bool}, or_elim(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})), g0_4), +h0_3 => Equal.trans(Bool, ise(c), ise(','), False{}, Equal.cong(Char, Bool, z => ise(z), c, ',', Equal.sym(Char, ',', c, char_eq(',', c, h0_3))), {==}), +g0_3 => either(&2, &2, {Char.is_eq(']', c) == True{} : Bool}, {Bool.or(Char.is_eq('}', c), False{}) == True{} : Bool}, {ise(c) == False{} : Bool}, or_elim(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}), g0_3), +h0_2 => Equal.trans(Bool, ise(c), ise(']'), False{}, Equal.cong(Char, Bool, z => ise(z), c, ']', Equal.sym(Char, ']', c, char_eq(']', c, h0_2))), {==}), +g0_2 => either(&2, &2, {Char.is_eq('}', c) == True{} : Bool}, {False{} == True{} : Bool}, {ise(c) == False{} : Bool}, or_elim(Char.is_eq('}', c), False{}, g0_2), +h0_1 => Equal.trans(Bool, ise(c), ise('}'), False{}, Equal.cong(Char, Bool, z => ise(z), c, '}', Equal.sym(Char, '}', c, char_eq('}', c, h0_1))), {==}), +g0_1 => Empty.absurd({ise(c) == False{} : Bool}, false_ne_true(g0_1))))))

def e_dig(+c: Char, +h: {ise(c) == True{} : Bool}) -> {isdig(c) == False{} : Bool}:
  either(&2, &2, {Char.is_eq('e', c) == True{} : Bool}, {Bool.or(Char.is_eq('E', c), False{}) == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{}), h), +h0_2 => Equal.trans(Bool, isdig(c), isdig('e'), False{}, Equal.cong(Char, Bool, z => isdig(z), c, 'e', Equal.sym(Char, 'e', c, char_eq('e', c, h0_2))), {==}), +g0_2 => either(&2, &2, {Char.is_eq('E', c) == True{} : Bool}, {False{} == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq('E', c), False{}, g0_2), +h0_1 => Equal.trans(Bool, isdig(c), isdig('E'), False{}, Equal.cong(Char, Bool, z => isdig(z), c, 'E', Equal.sym(Char, 'E', c, char_eq('E', c, h0_1))), {==}), +g0_1 => Empty.absurd({isdig(c) == False{} : Bool}, false_ne_true(g0_1))))

def e_dot(+c: Char, +h: {ise(c) == True{} : Bool}) -> {Char.is_eq('.', c) == False{} : Bool}:
  either(&2, &2, {Char.is_eq('e', c) == True{} : Bool}, {Bool.or(Char.is_eq('E', c), False{}) == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq('e', c), Bool.or(Char.is_eq('E', c), False{}), h), +h0_2 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', 'e'), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, 'e', Equal.sym(Char, 'e', c, char_eq('e', c, h0_2))), {==}), +g0_2 => either(&2, &2, {Char.is_eq('E', c) == True{} : Bool}, {False{} == True{} : Bool}, {Char.is_eq('.', c) == False{} : Bool}, or_elim(Char.is_eq('E', c), False{}, g0_2), +h0_1 => Equal.trans(Bool, Char.is_eq('.', c), Char.is_eq('.', 'E'), False{}, Equal.cong(Char, Bool, z => Char.is_eq('.', z), c, 'E', Equal.sym(Char, 'E', c, char_eq('E', c, h0_1))), {==}), +g0_1 => Empty.absurd({Char.is_eq('.', c) == False{} : Bool}, false_ne_true(g0_1))))

def sign_dig(+c: Char, +h: {issign(c) == True{} : Bool}) -> {isdig(c) == False{} : Bool}:
  either(&2, &2, {Char.is_eq('-', c) == True{} : Bool}, {Bool.or(Char.is_eq('+', c), False{}) == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq('-', c), Bool.or(Char.is_eq('+', c), False{}), h), +h0_2 => Equal.trans(Bool, isdig(c), isdig('-'), False{}, Equal.cong(Char, Bool, z => isdig(z), c, '-', Equal.sym(Char, '-', c, char_eq('-', c, h0_2))), {==}), +g0_2 => either(&2, &2, {Char.is_eq('+', c) == True{} : Bool}, {False{} == True{} : Bool}, {isdig(c) == False{} : Bool}, or_elim(Char.is_eq('+', c), False{}, g0_2), +h0_1 => Equal.trans(Bool, isdig(c), isdig('+'), False{}, Equal.cong(Char, Bool, z => isdig(z), c, '+', Equal.sym(Char, '+', c, char_eq('+', c, h0_1))), {==}), +g0_1 => Empty.absurd({isdig(c) == False{} : Bool}, false_ne_true(g0_1))))

def ws_num0(+c: Char, +h: {isws(c) == True{} : Bool}) -> {isnum0(c) == False{} : Bool}:
  either(&2, &2, {Char.is_eq(Chr{32}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))) == True{} : Bool}, {isnum0(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{32}, c), Bool.or(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}))), h), +h0_4 => Equal.trans(Bool, isnum0(c), isnum0(Chr{32}), False{}, Equal.cong(Char, Bool, z => isnum0(z), c, Chr{32}, Equal.sym(Char, Chr{32}, c, char_eq(Chr{32}, c, h0_4))), {==}), +g0_4 => either(&2, &2, {Char.is_eq(Chr{9}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})) == True{} : Bool}, {isnum0(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{9}, c), Bool.or(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{})), g0_4), +h0_3 => Equal.trans(Bool, isnum0(c), isnum0(Chr{9}), False{}, Equal.cong(Char, Bool, z => isnum0(z), c, Chr{9}, Equal.sym(Char, Chr{9}, c, char_eq(Chr{9}, c, h0_3))), {==}), +g0_3 => either(&2, &2, {Char.is_eq(Chr{10}, c) == True{} : Bool}, {Bool.or(Char.is_eq(Chr{13}, c), False{}) == True{} : Bool}, {isnum0(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{10}, c), Bool.or(Char.is_eq(Chr{13}, c), False{}), g0_3), +h0_2 => Equal.trans(Bool, isnum0(c), isnum0(Chr{10}), False{}, Equal.cong(Char, Bool, z => isnum0(z), c, Chr{10}, Equal.sym(Char, Chr{10}, c, char_eq(Chr{10}, c, h0_2))), {==}), +g0_2 => either(&2, &2, {Char.is_eq(Chr{13}, c) == True{} : Bool}, {False{} == True{} : Bool}, {isnum0(c) == False{} : Bool}, or_elim(Char.is_eq(Chr{13}, c), False{}, g0_2), +h0_1 => Equal.trans(Bool, isnum0(c), isnum0(Chr{13}), False{}, Equal.cong(Char, Bool, z => isnum0(z), c, Chr{13}, Equal.sym(Char, Chr{13}, c, char_eq(Chr{13}, c, h0_1))), {==}), +g0_1 => Empty.absurd({isnum0(c) == False{} : Bool}, false_ne_true(g0_1))))))

def not_ft(b: Bool, +h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      {==}

def not_tf(b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case False{}:
      {==}

# If c is x, then P(c) is what P(x) computes to.
def contraEq(+x: Char, +c: Char, -P: Char -> Bool, +hp: {P(c) == True{} : Bool}, +hx: {P(x) == False{} : Bool}) -> {Char.is_eq(x, c) == False{} : Bool}:
  bcase({Char.is_eq(x, c) == False{} : Bool}, Char.is_eq(x, c),
    +kk => Empty.absurd({Char.is_eq(x, c) == False{} : Bool}, false_ne_true(Equal.trans(Bool, False{}, P(x), True{}, Equal.sym(Bool, P(x), False{}, hx), Equal.trans(Bool, P(x), P(c), True{}, Equal.cong(Char, Bool, z => P(z), x, c, char_eq(x, c, kk)), hp)))),
    +kk => kk)

def dig_sign(+c: Char, +h: {isdig(c) == True{} : Bool}) -> {issign(c) == False{} : Bool}:
  bcase({issign(c) == False{} : Bool}, issign(c),
    +kk => Empty.absurd({issign(c) == False{} : Bool}, contra(isdig(c), h, sign_dig(c, kk))),
    +kk => kk)

def fol_nd(t: String, +h: {fol(t) == True{} : Bool}) -> {nd(t) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, r}:
      not_ft(isdig(c), fol_dig(c, h))

def fol_notdot(t: String, +h: {fol(t) == True{} : Bool}) -> {notdot(t) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, r}:
      not_ft(Char.is_eq('.', c), fol_dot(c, h))

# Numbers, back
# =============

def digC0(t: String, +ht: {nd(t) == True{} : Bool}) -> {digits(t) == SP{SNil{}, t} : SP}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      selF(SP, isdig(c), u => prepS(c, digits(r)), u => SP{SNil{}, SCon{c, r}}, not_tf(isdig(c), ht))

def digC.step(+c: Char, -x: String, +y: String, -a: String, +t: String, +e: {String.append(x, y) == a : String}, +ec: {SCon{c, SNil{}} == x : String}, +hc: {isdig(c) == True{} : Bool}, +ih: {digits(String.append(y, t)) == SP{y, t} : SP})
  -> {digits(String.append(a, t)) == SP{a, t} : SP}:
  %e : {digits(String.append(_, t)) == SP{_, t} : SP}
  %ec : {digits(String.append(String.append(_, y), t)) == SP{String.append(_, y), t} : SP}
  %Equal.sym(SP, digits(SCon{c, String.append(y, t)}), prepS(c, digits(String.append(y, t))), selT(SP, isdig(c), u => prepS(c, digits(String.append(y, t))), u => SP{SNil{}, SCon{c, String.append(y, t)}}, hc)) : {_ == SP{SCon{c, y}, t} : SP}
  %Equal.sym(SP, digits(String.append(y, t)), SP{y, t}, ih) : {prepS(c, _) == SP{SCon{c, y}, t} : SP}
  {==}

def digC.m(m: Nat, +a: String, +t: String, +h: {ABNF.check(BK, ABNF.rep.exactly(m, DIG), a) == True{} : Bool}, +ht: {nd(t) == True{} : Bool}) -> {digits(String.append(a, t)) == SP{a, t} : SP}:
  match m:
    case 0n:
      %Equal.sym(String, a, SNil{}, emptyE(BK, a, exZe(BK, DIG, a, h))) : {digits(String.append(_, t)) == SP{_, t} : SP}
      digC0(t, ht)
    case 1n+ +m1:
      seqE2({digits(String.append(a, t)) == SP{a, t} : SP}, BK, DIG, ABNF.rep.exactly(m1, DIG), a, exSe(BK, m1, DIG, a, h), +x => +y => +e => +hx => +hy =>
        one({digits(String.append(a, t)) == SP{a, t} : SP}, BK, DIG, x, hx, cd0(BK), z1 => z2 => z3 => cd2(BK, z1, z2, z3), +c => +ec => +hc =>
          digC.step(c, x, y, a, t, e, ec, tt.sym(ABNF.check(BK, DIG, SCon{c, SNil{}}), inR('0', '9', c), cd1(BK, c), hc), digC.m(m1, y, t, hy, ht))))

def digC.go(+a: String, +t: String, p: &m: Nat -> {ABNF.check(BK, ABNF.rep.exactly(m, DIG), a) == True{} : Bool}, +ht: {nd(t) == True{} : Bool}) -> {digits(String.append(a, t)) == SP{a, t} : SP}:
  (m, h) = p
  digC.m(m, a, t, h, ht)

# A run of digits followed by a non-digit is read whole.
def digC(+a: String, +t: String, +h: {ABNF.check(BK, ABNF.rep.any(DIG), a) == True{} : Bool}, +ht: {nd(t) == True{} : Bool}) -> {digits(String.append(a, t)) == SP{a, t} : SP}:
  digC.go(a, t, ABNF.rep.any.elim(BK, DIG, a, h), ht)

# AL1 decomposed: its first digit, and the rest.
def al1H(-C: Type, +a: String, +h: {ABNF.check(BK, AL1, a) == True{} : Bool}, f: @c: Char -> @y: String -> {SCon{c, y} == a : String} -> {isdig(c) == True{} : Bool} -> {ABNF.check(BK, ABNF.rep.any(DIG), y) == True{} : Bool} -> C) -> C:
  seqE2(C, BK, DIG, ABNF.rep.any(DIG), a, atl1E(BK, DIG, a, h), +x => +y => +e => +hx => +hy =>
    one(C, BK, DIG, x, hx, cd0(BK), z1 => z2 => z3 => cd2(BK, z1, z2, z3), +c => +ec => +hc =>
      f(c, y, Equal.trans(String, SCon{c, y}, String.append(x, y), a, app_congr(y, SCon{c, SNil{}}, x, ec), e), tt.sym(ABNF.check(BK, DIG, SCon{c, SNil{}}), inR('0', '9', c), cd1(BK, c), hc), hy)))

def dig1Cm.go(+c: Char, +y: String, -a: String, +t: String, +e: {SCon{c, y} == a : String}, +hc: {isdig(c) == True{} : Bool}, +hy: {digits(String.append(y, t)) == SP{y, t} : SP})
  -> {dig1(digits(String.append(a, t))) == Some{SP{a, t}} : Maybe<&2, SP>}:
  %e : {dig1(digits(String.append(_, t))) == Some{SP{_, t}} : Maybe<&2, SP>}
  %Equal.sym(SP, digits(SCon{c, String.append(y, t)}), prepS(c, digits(String.append(y, t))), selT(SP, isdig(c), u => prepS(c, digits(String.append(y, t))), u => SP{SNil{}, SCon{c, String.append(y, t)}}, hc)) : {dig1(_) == Some{SP{SCon{c, y}, t}} : Maybe<&2, SP>}
  %Equal.sym(SP, digits(String.append(y, t)), SP{y, t}, hy) : {dig1(prepS(c, _)) == Some{SP{SCon{c, y}, t}} : Maybe<&2, SP>}
  {==}

def dig1Cm(+a: String, +t: String, +h: {ABNF.check(BK, AL1, a) == True{} : Bool}, +ht: {nd(t) == True{} : Bool}) -> {dig1(digits(String.append(a, t))) == Some{SP{a, t}} : Maybe<&2, SP>}:
  al1H({dig1(digits(String.append(a, t))) == Some{SP{a, t}} : Maybe<&2, SP>}, a, h, +c => +y => +e => +hc => +hy => dig1Cm.go(c, y, a, t, e, hc, digC(y, t, hy, ht)))

def eref0() -> {ABNF.check(BK, ABNF.ref("e"), SNil{}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(BK, ABNF.ref("e"), SNil{}), ABNF.check(BK, ABNF.alt([ABNF.char('e'), ABNF.char('E')]), SNil{}), False{},
    MB("e", ABNF.alt([ABNF.char('e'), ABNF.char('E')]), SNil{}, {==}),
    alt2(BK, ABNF.char('e'), [ABNF.char('E')], SNil{}, False{}, False{}, ABNF.char.nil(BK, 'e'), alt2(BK, ABNF.char('E'), [], SNil{}, False{}, False{}, ABNF.char.nil(BK, 'E'), ABNF.alt.nil(BK, SNil{}))))

def eref2(+a: Char, +b: Char, +t: String) -> {ABNF.check(BK, ABNF.ref("e"), SCon{a, SCon{b, t}}) == False{} : Bool}:
  Equal.trans(Bool, ABNF.check(BK, ABNF.ref("e"), SCon{a, SCon{b, t}}), ABNF.check(BK, ABNF.alt([ABNF.char('e'), ABNF.char('E')]), SCon{a, SCon{b, t}}), False{},
    MB("e", ABNF.alt([ABNF.char('e'), ABNF.char('E')]), SCon{a, SCon{b, t}}, {==}),
    alt2(BK, ABNF.char('e'), [ABNF.char('E')], SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(BK, 'e', a, b, t), alt2(BK, ABNF.char('E'), [], SCon{a, SCon{b, t}}, False{}, False{}, ABNF.char.many(BK, 'E', a, b, t), ABNF.alt.nil(BK, SCon{a, SCon{b, t}}))))

def sign0() -> {ABNF.check(BK, SIGN, SNil{}) == False{} : Bool}:
  alt2(BK, ABNF.ref("minus"), [ABNF.ref("plus")], SNil{}, False{}, False{}, Equal.trans(Bool, ABNF.check(BK, ABNF.ref("minus"), SNil{}), ABNF.check(BK, ABNF.char('-'), SNil{}), False{}, MB("minus", ABNF.char('-'), SNil{}, {==}), ABNF.char.nil(BK, '-')),
    alt2(BK, ABNF.ref("plus"), [], SNil{}, False{}, False{}, Equal.trans(Bool, ABNF.check(BK, ABNF.ref("plus"), SNil{}), ABNF.check(BK, ABNF.char('+'), SNil{}), False{}, MB("plus", ABNF.char('+'), SNil{}, {==}), ABNF.char.nil(BK, '+')), ABNF.alt.nil(BK, SNil{})))

def sign2(+a: Char, +b: Char, +t: String) -> {ABNF.check(BK, SIGN, SCon{a, SCon{b, t}}) == False{} : Bool}:
  alt2(BK, ABNF.ref("minus"), [ABNF.ref("plus")], SCon{a, SCon{b, t}}, False{}, False{}, Equal.trans(Bool, ABNF.check(BK, ABNF.ref("minus"), SCon{a, SCon{b, t}}), ABNF.check(BK, ABNF.char('-'), SCon{a, SCon{b, t}}), False{}, MB("minus", ABNF.char('-'), SCon{a, SCon{b, t}}, {==}), ABNF.char.many(BK, '-', a, b, t)),
    alt2(BK, ABNF.ref("plus"), [], SCon{a, SCon{b, t}}, False{}, False{}, Equal.trans(Bool, ABNF.check(BK, ABNF.ref("plus"), SCon{a, SCon{b, t}}), ABNF.check(BK, ABNF.char('+'), SCon{a, SCon{b, t}}), False{}, MB("plus", ABNF.char('+'), SCon{a, SCon{b, t}}, {==}), ABNF.char.many(BK, '+', a, b, t)), ABNF.alt.nil(BK, SCon{a, SCon{b, t}})))

# exp decomposed: its e, sign and digits.
def expH(-C: Type, +x: String, +h: {ABNF.check(BK, ABNF.ref("exp"), x) == True{} : Bool},
  f: @c: Char -> @s1: String -> @d1: String -> {SCon{c, String.append(s1, d1)} == x : String} -> {ise(c) == True{} : Bool} -> {ABNF.check(BK, ABNF.opt(SIGN), s1) == True{} : Bool} -> {ABNF.check(BK, AL1, d1) == True{} : Bool} -> C) -> C:
  seqE3(C, BK, ABNF.ref("e"), ABNF.opt(SIGN), AL1, x, MBe("exp", B_exp, x, {==}, h), +e1 => +s1 => +d1 => +e => +he => +hs => +hd =>
    one(C, BK, ABNF.ref("e"), e1, he, eref0, z1 => z2 => z3 => eref2(z1, z2, z3), +c => +ec => +hc =>
      f(c, s1, d1, Equal.trans(String, SCon{c, String.append(s1, d1)}, String.append(e1, String.append(s1, d1)), x, app_congr(String.append(s1, d1), SCon{c, SNil{}}, e1, ec), e),
        tt.sym(ABNF.check(BK, ABNF.ref("e"), SCon{c, SNil{}}), ise(c), eref1(c), hc), hs, hd)))

def ndE.s(+c: Char, -s1: String, -d1: String, -x: String, +t: String, +e: {SCon{c, String.append(s1, d1)} == x : String}, +hc: {ise(c) == True{} : Bool}) -> {nd(String.append(x, t)) == True{} : Bool}:
  %e : {nd(String.append(_, t)) == True{} : Bool}
  not_ft(isdig(c), e_dig(c, hc))

# What follows int or frac is not a digit.
def ndE(+x: String, +t: String, +h: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), x) == True{} : Bool}, +ht: {fol(t) == True{} : Bool}) -> {nd(String.append(x, t)) == True{} : Bool}:
  optE({nd(String.append(x, t)) == True{} : Bool}, BK, ABNF.ref("exp"), x, h,
    +hn => Equal.trans(Bool, nd(String.append(x, t)), nd(t), True{}, Equal.cong(String, Bool, z => nd(String.append(z, t)), x, SNil{}, hn), fol_nd(t, ht)),
    +hs => expH({nd(String.append(x, t)) == True{} : Bool}, x, hs, +c => +s1 => +d1 => +e => +hc => +h1 => +h2 => ndE.s(c, s1, d1, x, t, e, hc)))

def notdotE.s(+c: Char, -s1: String, -d1: String, -x: String, +t: String, +e: {SCon{c, String.append(s1, d1)} == x : String}, +hc: {ise(c) == True{} : Bool}) -> {notdot(String.append(x, t)) == True{} : Bool}:
  %e : {notdot(String.append(_, t)) == True{} : Bool}
  not_ft(Char.is_eq('.', c), e_dot(c, hc))

def notdotE(+x: String, +t: String, +h: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), x) == True{} : Bool}, +ht: {fol(t) == True{} : Bool}) -> {notdot(String.append(x, t)) == True{} : Bool}:
  optE({notdot(String.append(x, t)) == True{} : Bool}, BK, ABNF.ref("exp"), x, h,
    +hn => Equal.trans(Bool, notdot(String.append(x, t)), notdot(t), True{}, Equal.cong(String, Bool, z => notdot(String.append(z, t)), x, SNil{}, hn), fol_notdot(t, ht)),
    +hs => expH({notdot(String.append(x, t)) == True{} : Bool}, x, hs, +c => +s1 => +d1 => +e => +hc => +h1 => +h2 => notdotE.s(c, s1, d1, x, t, e, hc)))

def nsignC.n.go(+c: Char, +y: String, -d1: String, +t: String, +e: {SCon{c, y} == d1 : String}, +hc: {isdig(c) == True{} : Bool}, +hd: {dig1(digits(String.append(d1, t))) == Some{SP{d1, t}} : Maybe<&2, SP>})
  -> {nsign(String.append(d1, t)) == Some{SP{d1, t}} : Maybe<&2, SP>}:
  %e : {nsign(String.append(_, t)) == Some{SP{_, t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nsign(SCon{c, String.append(y, t)}), dig1(digits(SCon{c, String.append(y, t)})), selF(Maybe<&2, SP>, issign(c), u => prepM(c, dig1(digits(String.append(y, t)))), u => dig1(digits(SCon{c, String.append(y, t)})), dig_sign(c, hc))) : {_ == Some{SP{SCon{c, y}, t}} : Maybe<&2, SP>}
  %Equal.sym(String, SCon{c, y}, d1, e) : {dig1(digits(String.append(_, t))) == Some{SP{_, t}} : Maybe<&2, SP>}
  hd

def nsignC.s(+c: Char, -s1: String, +d1: String, +t: String, +ec: {SCon{c, SNil{}} == s1 : String}, +hc: {issign(c) == True{} : Bool}, +hd: {dig1(digits(String.append(d1, t))) == Some{SP{d1, t}} : Maybe<&2, SP>})
  -> {nsign(String.append(s1, String.append(d1, t))) == Some{SP{String.append(s1, d1), t}} : Maybe<&2, SP>}:
  %ec : {nsign(String.append(_, String.append(d1, t))) == Some{SP{String.append(_, d1), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nsign(SCon{c, String.append(d1, t)}), prepM(c, dig1(digits(String.append(d1, t)))), selT(Maybe<&2, SP>, issign(c), u => prepM(c, dig1(digits(String.append(d1, t)))), u => dig1(digits(SCon{c, String.append(d1, t)})), hc)) : {_ == Some{SP{SCon{c, d1}, t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, dig1(digits(String.append(d1, t))), Some{SP{d1, t}}, hd) : {prepM(c, _) == Some{SP{SCon{c, d1}, t}} : Maybe<&2, SP>}
  {==}

def nsignC(+s1: String, +d1: String, +t: String, +hs: {ABNF.check(BK, ABNF.opt(SIGN), s1) == True{} : Bool}, +hd: {ABNF.check(BK, AL1, d1) == True{} : Bool}, +ht: {nd(t) == True{} : Bool})
  -> {nsign(String.append(s1, String.append(d1, t))) == Some{SP{String.append(s1, d1), t}} : Maybe<&2, SP>}:
  optE({nsign(String.append(s1, String.append(d1, t))) == Some{SP{String.append(s1, d1), t}} : Maybe<&2, SP>}, BK, SIGN, s1, hs,
    +hn => Equal.trans(Maybe<&2, SP>, nsign(String.append(s1, String.append(d1, t))), nsign(String.append(d1, t)), Some{SP{String.append(s1, d1), t}},
      Equal.cong(String, Maybe<&2, SP>, z => nsign(String.append(z, String.append(d1, t))), s1, SNil{}, hn),
      Equal.trans(Maybe<&2, SP>, nsign(String.append(d1, t)), Some{SP{d1, t}}, Some{SP{String.append(s1, d1), t}},
        al1H({nsign(String.append(d1, t)) == Some{SP{d1, t}} : Maybe<&2, SP>}, d1, hd, +c => +y => +e => +hc => +hy => nsignC.n.go(c, y, d1, t, e, hc, dig1Cm(d1, t, hd, ht))),
        Equal.cong(String, Maybe<&2, SP>, z => Some{SP{String.append(z, d1), t}}, SNil{}, s1, Equal.sym(String, s1, SNil{}, hn)))),
    +hg => one({nsign(String.append(s1, String.append(d1, t))) == Some{SP{String.append(s1, d1), t}} : Maybe<&2, SP>}, BK, SIGN, s1, hg, sign0, z1 => z2 => z3 => sign2(z1, z2, z3), +c => +ec => +hc =>
      nsignC.s(c, s1, d1, t, ec, tt.sym(ABNF.check(BK, SIGN, SCon{c, SNil{}}), issign(c), sign1(c), hc), dig1Cm(d1, t, hd, ht))))

def nexp0(t: String, +ht: {fol(t) == True{} : Bool}) -> {nexp(t) == Some{SP{SNil{}, t}} : Maybe<&2, SP>}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      selF(Maybe<&2, SP>, ise(c), u => prepM(c, nsign(r)), u => Some{SP{SNil{}, SCon{c, r}}}, fol_e(c, ht))

def nexpC.s(+c: Char, +s1: String, +d1: String, -x: String, +t: String, +e: {SCon{c, String.append(s1, d1)} == x : String}, +hc: {ise(c) == True{} : Bool}, +hn: {nsign(String.append(s1, String.append(d1, t))) == Some{SP{String.append(s1, d1), t}} : Maybe<&2, SP>})
  -> {nexp(String.append(x, t)) == Some{SP{x, t}} : Maybe<&2, SP>}:
  %e : {nexp(String.append(_, t)) == Some{SP{_, t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nexp(SCon{c, String.append(String.append(s1, d1), t)}), prepM(c, nsign(String.append(String.append(s1, d1), t))), selT(Maybe<&2, SP>, ise(c), u => prepM(c, nsign(String.append(String.append(s1, d1), t))), u => Some{SP{SNil{}, SCon{c, String.append(String.append(s1, d1), t)}}}, hc)) : {_ == Some{SP{SCon{c, String.append(s1, d1)}, t}} : Maybe<&2, SP>}
  %Equal.sym(String, String.append(String.append(s1, d1), t), String.append(s1, String.append(d1, t)), app3(s1, d1, t)) : {prepM(c, nsign(_)) == Some{SP{SCon{c, String.append(s1, d1)}, t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nsign(String.append(s1, String.append(d1, t))), Some{SP{String.append(s1, d1), t}}, hn) : {prepM(c, _) == Some{SP{SCon{c, String.append(s1, d1)}, t}} : Maybe<&2, SP>}
  {==}

def nexpC(+x: String, +t: String, +h: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), x) == True{} : Bool}, +ht: {fol(t) == True{} : Bool}) -> {nexp(String.append(x, t)) == Some{SP{x, t}} : Maybe<&2, SP>}:
  optE({nexp(String.append(x, t)) == Some{SP{x, t}} : Maybe<&2, SP>}, BK, ABNF.ref("exp"), x, h,
    +hn => Equal.trans(Maybe<&2, SP>, nexp(String.append(x, t)), nexp(t), Some{SP{x, t}}, Equal.cong(String, Maybe<&2, SP>, z => nexp(String.append(z, t)), x, SNil{}, hn),
      Equal.trans(Maybe<&2, SP>, nexp(t), Some{SP{SNil{}, t}}, Some{SP{x, t}}, nexp0(t, ht), Equal.cong(String, Maybe<&2, SP>, z => Some{SP{z, t}}, SNil{}, x, Equal.sym(String, x, SNil{}, hn)))),
    +hs => expH({nexp(String.append(x, t)) == Some{SP{x, t}} : Maybe<&2, SP>}, x, hs, +c => +s1 => +d1 => +e => +hc => +hg => +hd => nexpC.s(c, s1, d1, x, t, e, hc, nsignC(s1, d1, t, hg, hd, fol_nd(t, ht)))))

def nfracNE(X: String, +h: {notdot(X) == True{} : Bool}) -> {nfrac(X) == nexp(X) : Maybe<&2, SP>}:
  match X:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      selF(Maybe<&2, SP>, Char.is_eq('.', c), u => prepM(c, nfrac2(dig1(digits(r)))), u => nexp(SCon{c, r}), not_tf(Char.is_eq('.', c), h))

# frac decomposed: its point, and its digits.
def fracH(-C: Type, +f1: String, +h: {ABNF.check(BK, ABNF.ref("frac"), f1) == True{} : Bool}, f: @d: String -> {SCon{'.', d} == f1 : String} -> {ABNF.check(BK, AL1, d) == True{} : Bool} -> C) -> C:
  seqE2(C, BK, ABNF.ref("decimal-point"), AL1, f1, MBe("frac", B_frac, f1, {==}, h), +p1 => +d => +e => +hp => +hd =>
    f(d, Equal.trans(String, SCon{'.', d}, String.append(p1, d), f1, app_congr(d, SCon{'.', SNil{}}, p1, Equal.sym(String, p1, SCon{'.', SNil{}}, charIs(BK, '.', p1, MBe("decimal-point", ABNF.char('.'), p1, {==}, hp)))), e), hd))

def nfracC.n(-f1: String, +e1: String, +t: String, +hn: {f1 == SNil{} : String}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {nfrac(String.append(f1, String.append(e1, t))) == Some{SP{String.append(f1, e1), t}} : Maybe<&2, SP>}:
  %Equal.sym(String, f1, SNil{}, hn) : {nfrac(String.append(_, String.append(e1, t))) == Some{SP{String.append(_, e1), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nfrac(String.append(e1, t)), nexp(String.append(e1, t)), nfracNE(String.append(e1, t), notdotE(e1, t, he, ht))) : {_ == Some{SP{e1, t}} : Maybe<&2, SP>}
  nexpC(e1, t, he, ht)

def nfracC.s(-f1: String, +d: String, +e1: String, +t: String, +e: {SCon{'.', d} == f1 : String}, +hd: {ABNF.check(BK, AL1, d) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {nfrac(String.append(f1, String.append(e1, t))) == Some{SP{String.append(f1, e1), t}} : Maybe<&2, SP>}:
  %e : {nfrac(String.append(_, String.append(e1, t))) == Some{SP{String.append(_, e1), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, dig1(digits(String.append(d, String.append(e1, t)))), Some{SP{d, String.append(e1, t)}}, dig1Cm(d, String.append(e1, t), hd, ndE(e1, t, he, ht))) : {prepM('.', nfrac2(_)) == Some{SP{SCon{'.', String.append(d, e1)}, t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nexp(String.append(e1, t)), Some{SP{e1, t}}, nexpC(e1, t, he, ht)) : {prepM('.', appM(d, _)) == Some{SP{SCon{'.', String.append(d, e1)}, t}} : Maybe<&2, SP>}
  {==}

def nfracC(+f1: String, +e1: String, +t: String, +hf: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), f1) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {nfrac(String.append(f1, String.append(e1, t))) == Some{SP{String.append(f1, e1), t}} : Maybe<&2, SP>}:
  optE({nfrac(String.append(f1, String.append(e1, t))) == Some{SP{String.append(f1, e1), t}} : Maybe<&2, SP>}, BK, ABNF.ref("frac"), f1, hf,
    +hn => nfracC.n(f1, e1, t, hn, he, ht),
    +hs => fracH({nfrac(String.append(f1, String.append(e1, t))) == Some{SP{String.append(f1, e1), t}} : Maybe<&2, SP>}, f1, hs, +d => +e => +hd => nfracC.s(f1, d, e1, t, e, hd, he, ht)))

def ndF.s(-f1: String, -d: String, -X: String, +e: {SCon{'.', d} == f1 : String}) -> {nd(String.append(f1, X)) == True{} : Bool}:
  %e : {nd(String.append(_, X)) == True{} : Bool}
  {==}

# What follows int is not a digit.
def ndF(+f1: String, +e1: String, +t: String, +hf: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), f1) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {nd(String.append(f1, String.append(e1, t))) == True{} : Bool}:
  optE({nd(String.append(f1, String.append(e1, t))) == True{} : Bool}, BK, ABNF.ref("frac"), f1, hf,
    +hn => Equal.trans(Bool, nd(String.append(f1, String.append(e1, t))), nd(String.append(e1, t)), True{}, Equal.cong(String, Bool, z => nd(String.append(z, String.append(e1, t))), f1, SNil{}, hn), ndE(e1, t, he, ht)),
    +hs => fracH({nd(String.append(f1, String.append(e1, t))) == True{} : Bool}, f1, hs, +d => +e => +hd => ndF.s(f1, d, String.append(e1, t), e)))

def nintC.z(-i: String, +f1: String, +e1: String, +t: String, +ei: {i == SCon{'0', SNil{}} : String}, +hf: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), f1) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {nint(String.append(i, String.append(f1, String.append(e1, t)))) == Some{SP{String.append(i, String.append(f1, e1)), t}} : Maybe<&2, SP>}:
  %Equal.sym(String, i, SCon{'0', SNil{}}, ei) : {nint(String.append(_, String.append(f1, String.append(e1, t)))) == Some{SP{String.append(_, String.append(f1, e1)), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nfrac(String.append(f1, String.append(e1, t))), Some{SP{String.append(f1, e1), t}}, nfracC(f1, e1, t, hf, he, ht)) : {prepM('0', _) == Some{SP{SCon{'0', String.append(f1, e1)}, t}} : Maybe<&2, SP>}
  {==}

def nintC.nz(+c: Char, -x: String, +d: String, -i: String, +f1: String, +e1: String, +t: String, +e: {String.append(x, d) == i : String}, +ec: {SCon{c, SNil{}} == x : String}, +hc: {is19(c) == True{} : Bool},
  +hd: {ABNF.check(BK, ABNF.rep.any(DIG), d) == True{} : Bool}, +hf: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), f1) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {nint(String.append(i, String.append(f1, String.append(e1, t)))) == Some{SP{String.append(i, String.append(f1, e1)), t}} : Maybe<&2, SP>}:
  %e : {nint(String.append(_, String.append(f1, String.append(e1, t)))) == Some{SP{String.append(_, String.append(f1, e1)), t}} : Maybe<&2, SP>}
  %ec : {nint(String.append(String.append(_, d), String.append(f1, String.append(e1, t)))) == Some{SP{String.append(String.append(_, d), String.append(f1, e1)), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nint(SCon{c, String.append(d, String.append(f1, String.append(e1, t)))}), sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(String.append(d, String.append(f1, String.append(e1, t)))))), u => None{}),
    selF(Maybe<&2, SP>, Char.is_eq('0', c), u => prepM(c, nfrac(String.append(d, String.append(f1, String.append(e1, t))))), u => sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(String.append(d, String.append(f1, String.append(e1, t)))))), u => None{}), contraEq('0', c, z => is19(z), hc, {==}))) : {_ == Some{SP{SCon{c, String.append(d, String.append(f1, e1))}, t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(String.append(d, String.append(f1, String.append(e1, t)))))), u => None{}), prepM(c, nint2(digits(String.append(d, String.append(f1, String.append(e1, t)))))),
    selT(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(String.append(d, String.append(f1, String.append(e1, t)))))), u => None{}, hc)) : {_ == Some{SP{SCon{c, String.append(d, String.append(f1, e1))}, t}} : Maybe<&2, SP>}
  %Equal.sym(SP, digits(String.append(d, String.append(f1, String.append(e1, t)))), SP{d, String.append(f1, String.append(e1, t))}, digC(d, String.append(f1, String.append(e1, t)), hd, ndF(f1, e1, t, hf, he, ht))) : {prepM(c, nint2(_)) == Some{SP{SCon{c, String.append(d, String.append(f1, e1))}, t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nfrac(String.append(f1, String.append(e1, t))), Some{SP{String.append(f1, e1), t}}, nfracC(f1, e1, t, hf, he, ht)) : {prepM(c, appM(d, _)) == Some{SP{SCon{c, String.append(d, String.append(f1, e1))}, t}} : Maybe<&2, SP>}
  {==}

def nintC(+i: String, +f1: String, +e1: String, +t: String, +hi: {ABNF.check(BK, ABNF.ref("int"), i) == True{} : Bool}, +hf: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), f1) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {nint(String.append(i, String.append(f1, String.append(e1, t)))) == Some{SP{String.append(i, String.append(f1, e1)), t}} : Maybe<&2, SP>}:
  either(&2, &2, {ABNF.check(BK, ABNF.ref("zero"), i) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])]), i) == True{} : Bool}, {nint(String.append(i, String.append(f1, String.append(e1, t)))) == Some{SP{String.append(i, String.append(f1, e1)), t}} : Maybe<&2, SP>},
    or_elim(ABNF.check(BK, ABNF.ref("zero"), i), ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])]), i),
      tt.sym(ABNF.check(BK, B_int, i), Bool.or(ABNF.check(BK, ABNF.ref("zero"), i), ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])]), i)), ABNF.alt.con(BK, ABNF.ref("zero"), [ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])], i), MBe("int", B_int, i, {==}, hi))),
    +hz => nintC.z(i, f1, e1, t, charIs(BK, '0', i, MBe("zero", ABNF.char('0'), i, {==}, hz)), hf, he, ht),
    +hn => seqE2({nint(String.append(i, String.append(f1, String.append(e1, t)))) == Some{SP{String.append(i, String.append(f1, e1)), t}} : Maybe<&2, SP>}, BK, ABNF.ref("digit1-9"), ABNF.rep.any(DIG), i,
      tt.sym(ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])]), i), ABNF.check(BK, ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)]), i), altS(BK, ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)]), i), hn),
      +x => +d => +e => +hx => +hd =>
        one({nint(String.append(i, String.append(f1, String.append(e1, t)))) == Some{SP{String.append(i, String.append(f1, e1)), t}} : Maybe<&2, SP>}, BK, ABNF.range('1', '9'), x, MBe("digit1-9", ABNF.range('1', '9'), x, {==}, hx), rg0(BK, '1', '9'), z1 => z2 => z3 => rg2(BK, '1', '9', z1, z2, z3), +c => +ec => +hc =>
          nintC.nz(c, x, d, i, f1, e1, t, e, ec, tt.sym(ABNF.check(BK, ABNF.range('1', '9'), SCon{c, SNil{}}), inR('1', '9', c), rg1(BK, '1', '9', c), hc), hd, hf, he, ht))))

def assoc4(+a: String, +b: String, +c: String, +d: String, +t: String) -> {String.append(String.append(a, String.append(b, String.append(c, d))), t) == String.append(a, String.append(b, String.append(c, String.append(d, t)))) : String}:
  Equal.trans(String, String.append(String.append(a, String.append(b, String.append(c, d))), t), String.append(a, String.append(String.append(b, String.append(c, d)), t)), String.append(a, String.append(b, String.append(c, String.append(d, t)))),
    app3(a, String.append(b, String.append(c, d)), t),
    app_congl(a, String.append(String.append(b, String.append(c, d)), t), String.append(b, String.append(c, String.append(d, t))),
      Equal.trans(String, String.append(String.append(b, String.append(c, d)), t), String.append(b, String.append(String.append(c, d), t)), String.append(b, String.append(c, String.append(d, t))),
        app3(b, String.append(c, d), t), app_congl(b, String.append(String.append(c, d), t), String.append(c, String.append(d, t)), app3(c, d, t)))))

def numNM(X: String, +h: {notminus(X) == True{} : Bool}) -> {num_scan(X) == nint(X) : Maybe<&2, SP>}:
  match X:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      selF(Maybe<&2, SP>, Char.is_eq('-', c), u => prepM(c, nint(r)), u => nint(SCon{c, r}), not_tf(Char.is_eq('-', c), h))

def intNM.z(-i: String, -R: String, +ei: {i == SCon{'0', SNil{}} : String}) -> {notminus(String.append(i, R)) == True{} : Bool}:
  %Equal.sym(String, i, SCon{'0', SNil{}}, ei) : {notminus(String.append(_, R)) == True{} : Bool}
  {==}

def intNM.nz(+c: Char, -x: String, -d: String, -i: String, -R: String, +e: {String.append(x, d) == i : String}, +ec: {SCon{c, SNil{}} == x : String}, +hc: {is19(c) == True{} : Bool}) -> {notminus(String.append(i, R)) == True{} : Bool}:
  %e : {notminus(String.append(_, R)) == True{} : Bool}
  %ec : {notminus(String.append(String.append(_, d), R)) == True{} : Bool}
  not_ft(Char.is_eq('-', c), contraEq('-', c, z => is19(z), hc, {==}))

# An int does not start with a minus.
def intNM(+i: String, +R: String, +hi: {ABNF.check(BK, ABNF.ref("int"), i) == True{} : Bool}) -> {notminus(String.append(i, R)) == True{} : Bool}:
  either(&2, &2, {ABNF.check(BK, ABNF.ref("zero"), i) == True{} : Bool}, {ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])]), i) == True{} : Bool}, {notminus(String.append(i, R)) == True{} : Bool},
    or_elim(ABNF.check(BK, ABNF.ref("zero"), i), ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])]), i),
      tt.sym(ABNF.check(BK, B_int, i), Bool.or(ABNF.check(BK, ABNF.ref("zero"), i), ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])]), i)), ABNF.alt.con(BK, ABNF.ref("zero"), [ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])], i), MBe("int", B_int, i, {==}, hi))),
    +hz => intNM.z(i, R, charIs(BK, '0', i, MBe("zero", ABNF.char('0'), i, {==}, hz))),
    +hn => seqE2({notminus(String.append(i, R)) == True{} : Bool}, BK, ABNF.ref("digit1-9"), ABNF.rep.any(DIG), i,
      tt.sym(ABNF.check(BK, ABNF.alt([ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)])]), i), ABNF.check(BK, ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)]), i), altS(BK, ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(DIG)]), i), hn),
      +x => +d => +e => +hx => +hd =>
        one({notminus(String.append(i, R)) == True{} : Bool}, BK, ABNF.range('1', '9'), x, MBe("digit1-9", ABNF.range('1', '9'), x, {==}, hx), rg0(BK, '1', '9'), z1 => z2 => z3 => rg2(BK, '1', '9', z1, z2, z3), +c => +ec => +hc =>
          intNM.nz(c, x, d, i, R, e, ec, tt.sym(ABNF.check(BK, ABNF.range('1', '9'), SCon{c, SNil{}}), inR('1', '9', c), rg1(BK, '1', '9', c), hc)))))

def numC.n(-m1: String, +i: String, +f1: String, +e1: String, +t: String, +hn: {m1 == SNil{} : String}, +hi: {ABNF.check(BK, ABNF.ref("int"), i) == True{} : Bool}, +hf: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), f1) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {num_scan(String.append(m1, String.append(i, String.append(f1, String.append(e1, t))))) == Some{SP{String.append(m1, String.append(i, String.append(f1, e1))), t}} : Maybe<&2, SP>}:
  %Equal.sym(String, m1, SNil{}, hn) : {num_scan(String.append(_, String.append(i, String.append(f1, String.append(e1, t))))) == Some{SP{String.append(_, String.append(i, String.append(f1, e1))), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, num_scan(String.append(i, String.append(f1, String.append(e1, t)))), nint(String.append(i, String.append(f1, String.append(e1, t)))), numNM(String.append(i, String.append(f1, String.append(e1, t))), intNM(i, String.append(f1, String.append(e1, t)), hi))) : {_ == Some{SP{String.append(i, String.append(f1, e1)), t}} : Maybe<&2, SP>}
  nintC(i, f1, e1, t, hi, hf, he, ht)

def numC.m(-m1: String, +i: String, +f1: String, +e1: String, +t: String, +em: {m1 == SCon{'-', SNil{}} : String}, +hi: {ABNF.check(BK, ABNF.ref("int"), i) == True{} : Bool}, +hf: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), f1) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {num_scan(String.append(m1, String.append(i, String.append(f1, String.append(e1, t))))) == Some{SP{String.append(m1, String.append(i, String.append(f1, e1))), t}} : Maybe<&2, SP>}:
  %Equal.sym(String, m1, SCon{'-', SNil{}}, em) : {num_scan(String.append(_, String.append(i, String.append(f1, String.append(e1, t))))) == Some{SP{String.append(_, String.append(i, String.append(f1, e1))), t}} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nint(String.append(i, String.append(f1, String.append(e1, t)))), Some{SP{String.append(i, String.append(f1, e1)), t}}, nintC(i, f1, e1, t, hi, hf, he, ht)) : {prepM('-', _) == Some{SP{SCon{'-', String.append(i, String.append(f1, e1))}, t}} : Maybe<&2, SP>}
  {==}

def numC.go(+m1: String, +i: String, +f1: String, +e1: String, -n: String, +t: String, +e: {String.append(m1, String.append(i, String.append(f1, e1))) == n : String},
  +hm: {ABNF.check(BK, ABNF.opt(ABNF.ref("minus")), m1) == True{} : Bool}, +hi: {ABNF.check(BK, ABNF.ref("int"), i) == True{} : Bool}, +hf: {ABNF.check(BK, ABNF.opt(ABNF.ref("frac")), f1) == True{} : Bool}, +he: {ABNF.check(BK, ABNF.opt(ABNF.ref("exp")), e1) == True{} : Bool}, +ht: {fol(t) == True{} : Bool})
  -> {num_scan(String.append(n, t)) == Some{SP{n, t}} : Maybe<&2, SP>}:
  %e : {num_scan(String.append(_, t)) == Some{SP{_, t}} : Maybe<&2, SP>}
  %Equal.sym(String, String.append(String.append(m1, String.append(i, String.append(f1, e1))), t), String.append(m1, String.append(i, String.append(f1, String.append(e1, t)))), assoc4(m1, i, f1, e1, t)) : {num_scan(_) == Some{SP{String.append(m1, String.append(i, String.append(f1, e1))), t}} : Maybe<&2, SP>}
  optE({num_scan(String.append(m1, String.append(i, String.append(f1, String.append(e1, t))))) == Some{SP{String.append(m1, String.append(i, String.append(f1, e1))), t}} : Maybe<&2, SP>}, BK, ABNF.ref("minus"), m1, hm,
    +hn => numC.n(m1, i, f1, e1, t, hn, hi, hf, he, ht),
    +hs => numC.m(m1, i, f1, e1, t, charIs(BK, '-', m1, MBe("minus", ABNF.char('-'), m1, {==}, hs)), hi, hf, he, ht))

# A number followed by what may follow a value is read whole.
def numC(+n: String, +t: String, +h: {ABNF.check(BK, B_number, n) == True{} : Bool}, +ht: {fol(t) == True{} : Bool}) -> {num_scan(String.append(n, t)) == Some{SP{n, t}} : Maybe<&2, SP>}:
  seqE4({num_scan(String.append(n, t)) == Some{SP{n, t}} : Maybe<&2, SP>}, BK, ABNF.opt(ABNF.ref("minus")), ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp")), n, h,
    +m1 => +i => +f1 => +e1 => +e => +hm => +hi => +hf => +he => numC.go(m1, i, f1, e1, n, t, e, hm, hi, hf, he, ht))

# Parser soundness
# ================

def TM(m: Md) -> ABNF.Rule:
  match m:
    case MV{}:
      ABNF.ref("value")
    case MA{}:
      ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")])
    case MM{}:
      ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")])
    case MO{}:
      ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")])

# PSR(R, res, s): if res is a success, it read some y off s, y matches R, and what it built is valid.
def PSR(R: ABNF.Rule, res: Maybe<&2, PR>, s: String) -> Type:
  match res:
    case None{}:
      Unit
    case Some{p}:
      &y: String -> {String.append(y, prt(p)) == s : String} & {ABNF.check(BK, R, y) == True{} : Bool} & {wf(prr(p)) == True{} : Bool}

def val_false(+y: String, +h: {ABNF.check(BK, ABNF.ref("false"), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool}:
  MBi("value", B_value, y, {==}, altL(BK, ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, h))

def val_null(+y: String, +h: {ABNF.check(BK, ABNF.ref("null"), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool}:
  MBi("value", B_value, y, {==}, altR(BK, ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altL(BK, ABNF.ref("null"), [ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, h)))

def val_true(+y: String, +h: {ABNF.check(BK, ABNF.ref("true"), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool}:
  MBi("value", B_value, y, {==}, altR(BK, ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("null"), [ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altL(BK, ABNF.ref("true"), [ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, h))))

def val_object(+y: String, +h: {ABNF.check(BK, ABNF.ref("object"), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool}:
  MBi("value", B_value, y, {==}, altR(BK, ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("null"), [ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("true"), [ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altL(BK, ABNF.ref("object"), [ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, h)))))

def val_array(+y: String, +h: {ABNF.check(BK, ABNF.ref("array"), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool}:
  MBi("value", B_value, y, {==}, altR(BK, ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("null"), [ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("true"), [ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("object"), [ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altL(BK, ABNF.ref("array"), [ABNF.ref("number"), ABNF.ref("string")], y, h))))))

def val_number(+y: String, +h: {ABNF.check(BK, ABNF.ref("number"), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool}:
  MBi("value", B_value, y, {==}, altR(BK, ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("null"), [ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("true"), [ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("object"), [ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("array"), [ABNF.ref("number"), ABNF.ref("string")], y, altL(BK, ABNF.ref("number"), [ABNF.ref("string")], y, h)))))))

def val_string(+y: String, +h: {ABNF.check(BK, ABNF.ref("string"), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool}:
  MBi("value", B_value, y, {==}, altR(BK, ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("null"), [ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("true"), [ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("object"), [ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("array"), [ABNF.ref("number"), ABNF.ref("string")], y, altR(BK, ABNF.ref("number"), [ABNF.ref("string")], y, altL(BK, ABNF.ref("string"), [], y, h))))))))

def swDrop.go(+y: Char, +yt: String, +x: Char, +xt: String, +k: {Char.is_eq(x, y) == True{} : Bool}, +ih: {String.append(yt, String.drop(xt, String.length(yt))) == xt : String})
  -> {String.append(SCon{y, yt}, String.drop(SCon{x, xt}, String.length(SCon{y, yt}))) == SCon{x, xt} : String}:
  %char_eq(x, y, k) : {SCon{_, String.append(yt, String.drop(xt, String.length(yt)))} == SCon{x, xt} : String}
  cons_eq(x, String.append(yt, String.drop(xt, String.length(yt))), xt, ih)

def swDrop(p: String, t: String, +h: {String.starts_with(t, p) == True{} : Bool}) -> {String.append(p, String.drop(t, String.length(p))) == t : String}:
  match p t:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{x, xt}:
      {==}
    case SCon{y, yt} SNil{}:
      Empty.absurd({String.append(SCon{y, yt}, SNil{}) == SNil{} : String}, false_ne_true(h))
    case SCon{+y, +yt} SCon{+x, +xt}:
      bcase({String.append(SCon{y, yt}, String.drop(SCon{x, xt}, String.length(SCon{y, yt}))) == SCon{x, xt} : String}, Char.is_eq(x, y),
        +k => swDrop.go(y, yt, x, xt, k, swDrop(yt, xt, Equal.trans(Bool, String.starts_with(xt, yt), String.starts_with.go.if(yt, xt, Char.is_eq(x, y)), True{}, Equal.cong(Bool, Bool, z => String.starts_with.go.if(yt, xt, z), True{}, Char.is_eq(x, y), Equal.sym(Bool, Char.is_eq(x, y), True{}, k)), h))),
        +k => Empty.absurd({String.append(SCon{y, yt}, String.drop(SCon{x, xt}, String.length(SCon{y, yt}))) == SCon{x, xt} : String}, false_ne_true(Equal.trans(Bool, False{}, String.starts_with.go.if(yt, xt, Char.is_eq(x, y)), True{}, Equal.cong(Bool, Bool, z => String.starts_with.go.if(yt, xt, z), False{}, Char.is_eq(x, y), Equal.sym(Bool, Char.is_eq(x, y), False{}, k)), h))))

def litPS.t(+c: Char, +p: String, +t: String, +r: Raw, +h: {String.starts_with(t, p) == True{} : Bool}, +hv: {ABNF.check(BK, ABNF.ref("value"), SCon{c, p}) == True{} : Bool}, +hw: {wf(r) == True{} : Bool}) -> PSR(ABNF.ref("value"), lit(p, t, r), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, lit(p, t, r), Some{PR{r, String.drop(t, String.length(p))}}, selT(Maybe<&2, PR>, String.starts_with(t, p), u => Some{PR{r, String.drop(t, String.length(p))}}, u => None{}, h)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  (SCon{c, p}, cons_eq(c, String.append(p, String.drop(t, String.length(p))), t, swDrop(p, t, h)), hv, hw)

def litPS.f(+c: Char, +p: String, +t: String, +r: Raw, +h: {String.starts_with(t, p) == False{} : Bool}) -> PSR(ABNF.ref("value"), lit(p, t, r), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, lit(p, t, r), None{}, selF(Maybe<&2, PR>, String.starts_with(t, p), u => Some{PR{r, String.drop(t, String.length(p))}}, u => None{}, h)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  Unit{}

def litPS(+c: Char, +p: String, +t: String, +r: Raw, +hv: {ABNF.check(BK, ABNF.ref("value"), SCon{c, p}) == True{} : Bool}, +hw: {wf(r) == True{} : Bool}) -> PSR(ABNF.ref("value"), lit(p, t, r), SCon{c, t}):
  bcase(PSR(ABNF.ref("value"), lit(p, t, r), SCon{c, t}), String.starts_with(t, p), +h => litPS.t(c, p, t, r, h, hv, hw), +h => litPS.f(c, p, t, r, h))

def numokOf(+a: String, +h: {ABNF.check(BK, B_number, a) == True{} : Bool}) -> {numok(a) == True{} : Bool}:
  %Equal.sym(Maybe<&2, SP>, num_scan(a), Some{SP{a, SNil{}}}, Equal.trans(Maybe<&2, SP>, num_scan(a), num_scan(String.append(a, SNil{})), Some{SP{a, SNil{}}}, Equal.cong(String, Maybe<&2, SP>, z => num_scan(z), a, String.append(a, SNil{}), Equal.sym(String, String.append(a, SNil{}), a, append_nil(a))), numC(a, SNil{}, h, {==}))) : {okend(_) == True{} : Bool}
  {==}

def strokOf(+a: String, +h: {ABNF.check(BK, CHARS, a) == True{} : Bool}) -> {strok(a) == True{} : Bool}:
  %Equal.sym(Maybe<&2, SP>, str_scan(String.append(a, SCon{'"', SNil{}}), SN{}), Some{SP{a, SNil{}}}, strC(a, SNil{}, h)) : {okend(_) == True{} : Bool}
  {==}

def numvPS(m: Maybe<&2, SP>, -s: String, ns: NS(m, s, B_number)) -> PSR(ABNF.ref("value"), numv(m), s):
  match m:
    case None{}:
      Unit{}
    case Some{p}:
      match p:
        case SP{+a, u}:
          (e, +h) = ns
          (a, e, val_number(a, MBi("number", B_number, a, {==}, h)), numokOf(a, h))

def strText(+a: String, +h: {ABNF.check(BK, CHARS, a) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("string"), SCon{'"', String.append(a, SCon{'"', SNil{}})}) == True{} : Bool}:
  MBi("string", B_string, SCon{'"', String.append(a, SCon{'"', SNil{}})}, {==},
    seqI3(BK, ABNF.ref("quotation-mark"), CHARS, ABNF.ref("quotation-mark"), SCon{'"', SNil{}}, a, SCon{'"', SNil{}}, refCi("quotation-mark", '"', '"', {==}, {==}), h, refCi("quotation-mark", '"', '"', {==}, {==})))

def strvPS(m: Maybe<&2, SP>, -t: String, ns: SNS(m, t, CHARS)) -> PSR(ABNF.ref("value"), strv(m), SCon{'"', t}):
  match m:
    case None{}:
      Unit{}
    case Some{p}:
      match p:
        case SP{+a, +u}:
          (e, +h) = ns
          (SCon{'"', String.append(a, SCon{'"', SNil{}})}, cons_eq('"', String.append(String.append(a, SCon{'"', SNil{}}), u), t, Equal.trans(String, String.append(String.append(a, SCon{'"', SNil{}}), u), String.append(a, SCon{'"', u}), t, app3(a, SCon{'"', SNil{}}, u), e)),
            val_string(SCon{'"', String.append(a, SCon{'"', SNil{}})}, strText(a, h)), strokOf(a, h))

def wfAcons(+x: Raw, r: Raw, +hx: {wf(x) == True{} : Bool}, +hr: {wf(r) == True{} : Bool}) -> {wf(acons1(x, r)) == True{} : Bool}:
  match r:
    case RArr{xs}:
      and_intro(wf(x), wf(RArr{xs}), hx, hr)
    case RNull{}:
      and_intro(wf(x), True{}, hx, {==})
    case RBool{b}:
      and_intro(wf(x), True{}, hx, {==})
    case RNum{q}:
      and_intro(wf(x), True{}, hx, {==})
    case RStr{q}:
      and_intro(wf(x), True{}, hx, {==})
    case RObj{ms}:
      and_intro(wf(x), True{}, hx, {==})

def wfOcons(+k: String, +v: Raw, r: Raw, +hk: {strok(k) == True{} : Bool}, +hv: {wf(v) == True{} : Bool}, +hr: {wf(r) == True{} : Bool}) -> {wf(ocons1(k, v, r)) == True{} : Bool}:
  match r:
    case RObj{ms}:
      and_intro(strok(k), Bool.and(wf(v), wf(RObj{ms})), hk, and_intro(wf(v), wf(RObj{ms}), hv, hr))
    case RNull{}:
      and_intro(strok(k), Bool.and(wf(v), True{}), hk, and_intro(wf(v), True{}, hv, {==}))
    case RBool{b}:
      and_intro(strok(k), Bool.and(wf(v), True{}), hk, and_intro(wf(v), True{}, hv, {==}))
    case RNum{q}:
      and_intro(strok(k), Bool.and(wf(v), True{}), hk, and_intro(wf(v), True{}, hv, {==}))
    case RStr{q}:
      and_intro(strok(k), Bool.and(wf(v), True{}), hk, and_intro(wf(v), True{}, hv, {==}))
    case RArr{xs}:
      and_intro(strok(k), Bool.and(wf(v), True{}), hk, and_intro(wf(v), True{}, hv, {==}))

# Tokens absorb whitespace before them.
def tokAbs(+N: String, +ch: Char, +w: String, +b: String, +e: {gsel(GRAMMAR, N) == [TOK(ch)] : List<ABNF.Rule>}, +hch: {isws(ch) == False{} : Bool}, +hw: {wsall(w) == True{} : Bool}, +h: {ABNF.check(BK, ABNF.ref(N), b) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.ref(N), String.append(w, b)) == True{} : Bool}:
  tokI(N, ch, String.append(w, b), e, Equal.trans(Bool, tokb2(ch, skip_ws(String.append(w, b))), tokb2(ch, skip_ws(b)), True{}, Equal.cong(String, Bool, z => tokb2(ch, z), skip_ws(String.append(w, b)), skip_ws(b), WE(w, b, hw)), tokE(N, ch, b, e, hch, h)))

def assoc3(+w: String, +x: String, +r: String, +t: String) -> {String.append(String.append(String.append(w, x), r), t) == String.append(w, String.append(String.append(x, r), t)) : String}:
  Equal.trans(String, String.append(String.append(String.append(w, x), r), t), String.append(String.append(w, String.append(x, r)), t), String.append(w, String.append(String.append(x, r), t)),
    app_congr(t, String.append(String.append(w, x), r), String.append(w, String.append(x, r)), app3(w, x, r)), app3(w, String.append(x, r), t))

def absMA.n(+w: String, -y: String, -R: String, +E: String, +e: {String.append(R, E) == y : String}, +hn: {R == SNil{} : String}, +hw: {wsall(w) == True{} : Bool}, +hE: {ABNF.check(BK, ABNF.ref("end-array"), E) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, y)) == True{} : Bool}:
  %e : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, _)) == True{} : Bool}
  %Equal.sym(String, R, SNil{}, hn) : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, String.append(_, E))) == True{} : Bool}
  seqI2(BK, ABNF.rep.any(ITEM), ABNF.ref("end-array"), SNil{}, String.append(w, E), starNil(BK, ITEM), tokAbs("end-array", ']', w, E, {==}, {==}, hw, hE))

def absMA.c(+w: String, -y: String, -R: String, +E: String, -a: String, +R2: String, +vs: String, +v: String, +e: {String.append(R, E) == y : String}, +e2: {String.append(a, R2) == R : String}, +e3: {String.append(vs, v) == a : String},
  +hw: {wsall(w) == True{} : Bool}, +hvs: {ABNF.check(BK, ABNF.ref("value-separator"), vs) == True{} : Bool}, +hv: {ABNF.check(BK, ABNF.ref("value"), v) == True{} : Bool}, +hR2: {ABNF.check(BK, ABNF.rep.any(ITEM), R2) == True{} : Bool}, +hE: {ABNF.check(BK, ABNF.ref("end-array"), E) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, y)) == True{} : Bool}:
  %e : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, _)) == True{} : Bool}
  %e2 : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, String.append(_, E))) == True{} : Bool}
  %e3 : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, String.append(String.append(_, R2), E))) == True{} : Bool}
  chkTr(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(String.append(String.append(w, String.append(vs, v)), R2), E), String.append(w, String.append(String.append(String.append(vs, v), R2), E)), assoc3(w, String.append(vs, v), R2, E),
    seqI2(BK, ABNF.rep.any(ITEM), ABNF.ref("end-array"), String.append(String.append(w, String.append(vs, v)), R2), E,
      starCons(BK, ITEM, String.append(w, String.append(vs, v)), R2,
        chkTr(BK, ITEM, String.append(String.append(w, vs), v), String.append(w, String.append(vs, v)), app3(w, vs, v),
          seqI2(BK, ABNF.ref("value-separator"), ABNF.ref("value"), String.append(w, vs), v, tokAbs("value-separator", ',', w, vs, {==}, {==}, hw, hvs), hv)), hR2), hE))

def absMA(+w: String, +y: String, +hw: {wsall(w) == True{} : Bool}, +h: {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, y)) == True{} : Bool}:
  seqE2({ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, y)) == True{} : Bool}, BK, ABNF.rep.any(ITEM), ABNF.ref("end-array"), y, h, +R => +E => +e => +hR => +hE =>
    starCase({ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, y)) == True{} : Bool}, BK, ITEM, R, hR,
      +hn => absMA.n(w, y, R, E, e, hn, hw, hE),
      +a => +R2 => +e2 => +ha => +hR2 => seqE2({ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(w, y)) == True{} : Bool}, BK, ABNF.ref("value-separator"), ABNF.ref("value"), a, ha,
        +vs => +v => +e3 => +hvs => +hv => absMA.c(w, y, R, E, a, R2, vs, v, e, e2, e3, hw, hvs, hv, hR2, hE))))

def absMO.n(+w: String, -y: String, -R: String, +E: String, +e: {String.append(R, E) == y : String}, +hn: {R == SNil{} : String}, +hw: {wsall(w) == True{} : Bool}, +hE: {ABNF.check(BK, ABNF.ref("end-object"), E) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, y)) == True{} : Bool}:
  %e : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, _)) == True{} : Bool}
  %Equal.sym(String, R, SNil{}, hn) : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, String.append(_, E))) == True{} : Bool}
  seqI2(BK, ABNF.rep.any(MITEM), ABNF.ref("end-object"), SNil{}, String.append(w, E), starNil(BK, MITEM), tokAbs("end-object", '}', w, E, {==}, {==}, hw, hE))

def absMO.c(+w: String, -y: String, -R: String, +E: String, -a: String, +R2: String, +vs: String, +v: String, +e: {String.append(R, E) == y : String}, +e2: {String.append(a, R2) == R : String}, +e3: {String.append(vs, v) == a : String},
  +hw: {wsall(w) == True{} : Bool}, +hvs: {ABNF.check(BK, ABNF.ref("value-separator"), vs) == True{} : Bool}, +hv: {ABNF.check(BK, ABNF.ref("member"), v) == True{} : Bool}, +hR2: {ABNF.check(BK, ABNF.rep.any(MITEM), R2) == True{} : Bool}, +hE: {ABNF.check(BK, ABNF.ref("end-object"), E) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, y)) == True{} : Bool}:
  %e : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, _)) == True{} : Bool}
  %e2 : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, String.append(_, E))) == True{} : Bool}
  %e3 : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, String.append(String.append(_, R2), E))) == True{} : Bool}
  chkTr(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(String.append(String.append(w, String.append(vs, v)), R2), E), String.append(w, String.append(String.append(String.append(vs, v), R2), E)), assoc3(w, String.append(vs, v), R2, E),
    seqI2(BK, ABNF.rep.any(MITEM), ABNF.ref("end-object"), String.append(String.append(w, String.append(vs, v)), R2), E,
      starCons(BK, MITEM, String.append(w, String.append(vs, v)), R2,
        chkTr(BK, MITEM, String.append(String.append(w, vs), v), String.append(w, String.append(vs, v)), app3(w, vs, v),
          seqI2(BK, ABNF.ref("value-separator"), ABNF.ref("member"), String.append(w, vs), v, tokAbs("value-separator", ',', w, vs, {==}, {==}, hw, hvs), hv)), hR2), hE))

def absMO(+w: String, +y: String, +hw: {wsall(w) == True{} : Bool}, +h: {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, y)) == True{} : Bool}:
  seqE2({ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, y)) == True{} : Bool}, BK, ABNF.rep.any(MITEM), ABNF.ref("end-object"), y, h, +R => +E => +e => +hR => +hE =>
    starCase({ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, y)) == True{} : Bool}, BK, MITEM, R, hR,
      +hn => absMO.n(w, y, R, E, e, hn, hw, hE),
      +a => +R2 => +e2 => +ha => +hR2 => seqE2({ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(w, y)) == True{} : Bool}, BK, ABNF.ref("value-separator"), ABNF.ref("member"), a, ha,
        +vs => +v => +e3 => +hvs => +hv => absMO.c(w, y, R, E, a, R2, vs, v, e, e2, e3, hw, hvs, hv, hR2, hE))))

def itemEq(+y1: String, +u1: String, +y2: String, +u2: String, -v0: String, +e1: {String.append(y1, u1) == v0 : String}, +e2: {String.append(y2, u2) == skip_ws(u1) : String})
  -> {String.append(String.append(y1, String.append(wsp(u1), y2)), u2) == v0 : String}:
  %Equal.sym(String, String.append(String.append(y1, String.append(wsp(u1), y2)), u2), String.append(y1, String.append(String.append(wsp(u1), y2), u2)), app3(y1, String.append(wsp(u1), y2), u2)) : {_ == v0 : String}
  %Equal.sym(String, String.append(String.append(wsp(u1), y2), u2), String.append(wsp(u1), String.append(y2, u2)), app3(wsp(u1), y2, u2)) : {String.append(y1, _) == v0 : String}
  %Equal.sym(String, String.append(y2, u2), skip_ws(u1), e2) : {String.append(y1, String.append(wsp(u1), _)) == v0 : String}
  %Equal.sym(String, String.append(wsp(u1), skip_ws(u1)), u1, WI(u1)) : {String.append(y1, _) == v0 : String}
  e1

def elemsA(+y1: String, +Y: String, +hv: {ABNF.check(BK, ABNF.ref("value"), y1) == True{} : Bool}, +hY: {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), Y) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ELEMS, ABNF.ref("end-array")]), String.append(y1, Y)) == True{} : Bool}:
  seqE2({ABNF.check(BK, ABNF.seq([ELEMS, ABNF.ref("end-array")]), String.append(y1, Y)) == True{} : Bool}, BK, ABNF.rep.any(ITEM), ABNF.ref("end-array"), Y, hY, +R => +E => +e => +hR => +hE =>
    chkTr(BK, ABNF.seq([ELEMS, ABNF.ref("end-array")]), String.append(String.append(y1, R), E), String.append(y1, Y), Equal.trans(String, String.append(String.append(y1, R), E), String.append(y1, String.append(R, E)), String.append(y1, Y), app3(y1, R, E), app_congl(y1, String.append(R, E), Y, e)),
      seqI2(BK, ELEMS, ABNF.ref("end-array"), String.append(y1, R), E, seqI2(BK, ABNF.ref("value"), ABNF.rep.any(ITEM), y1, R, hv, hR), hE)))

def itemB2(-v0: String, +p1: PR, +y1: String, +e1: {String.append(y1, prt(p1)) == v0 : String}, +hv1: {ABNF.check(BK, ABNF.ref("value"), y1) == True{} : Bool}, +hw1: {wf(prr(p1)) == True{} : Bool},
  r2: Maybe<&2, PR>, ps2: PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), r2, skip_ws(prt(p1)))) -> PSR(ABNF.seq([ELEMS, ABNF.ref("end-array")]), acons(prr(p1), r2), v0):
  match r2:
    case None{}:
      Unit{}
    case Some{+p2}:
      (+y2, e2, h2, hw2) = ps2
      (String.append(y1, String.append(wsp(prt(p1)), y2)), itemEq(y1, prt(p1), y2, prt(p2), v0, e1, e2), elemsA(y1, String.append(wsp(prt(p1)), y2), hv1, absMA(wsp(prt(p1)), y2, WIa(prt(p1)), h2)), wfAcons(prr(p1), prr(p2), hw1, hw2))

# A value and what MA reads after it.
def itemB(+g: Nat, -v0: String, r1: Maybe<&2, PR>, ps1: PSR(ABNF.ref("value"), r1, v0), ihA: @w: String -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(g, MA{}, w), w)) -> PSR(ABNF.seq([ELEMS, ABNF.ref("end-array")]), Maybe.bind(&2, PR, PR, r1, +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), v0):
  match r1:
    case None{}:
      Unit{}
    case Some{+p1}:
      (+y1, e1, hv1, hw1) = ps1
      itemB2(v0, p1, y1, e1, hv1, hw1, pv(g, MA{}, skip_ws(prt(p1))), ihA(skip_ws(prt(p1))))

def arrayA(+t: String, +z: String, +hz: {ABNF.check(BK, ABNF.seq([ELEMS, ABNF.ref("end-array")]), z) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), SCon{'[', String.append(wsp(t), z)}) == True{} : Bool}:
  val_array(SCon{'[', String.append(wsp(t), z)}, MBi("array", B_array, SCon{'[', String.append(wsp(t), z)}, {==},
    seqE2({ABNF.check(BK, B_array, SCon{'[', String.append(wsp(t), z)}) == True{} : Bool}, BK, ELEMS, ABNF.ref("end-array"), z, hz, +Z1 => +E => +e => +h1 => +hE =>
      chkTr(BK, B_array, SCon{'[', String.append(wsp(t), String.append(Z1, E))}, SCon{'[', String.append(wsp(t), z)}, cons_eq('[', String.append(wsp(t), String.append(Z1, E)), String.append(wsp(t), z), app_congl(wsp(t), String.append(Z1, E), z, e)),
        seqI3(BK, ABNF.ref("begin-array"), ABNF.opt(ELEMS), ABNF.ref("end-array"), SCon{'[', wsp(t)}, Z1, E, tokI("begin-array", '[', SCon{'[', wsp(t)}, {==}, WIa(t)), optS(BK, ELEMS, Z1, h1), hE)))))

def bkEq(+o: Char, +t: String, +u: String, +z: String, +r: String, +eu: {skip_ws(t) == u : String}, +ez: {String.append(z, r) == u : String}) -> {String.append(SCon{o, String.append(wsp(t), z)}, r) == SCon{o, t} : String}:
  cons_eq(o, String.append(String.append(wsp(t), z), r), t, Equal.trans(String, String.append(String.append(wsp(t), z), r), String.append(wsp(t), String.append(z, r)), t, app3(wsp(t), z, r),
    Equal.trans(String, String.append(wsp(t), String.append(z, r)), String.append(wsp(t), skip_ws(t)), t, app_congl(wsp(t), String.append(z, r), skip_ws(t), Equal.trans(String, String.append(z, r), u, skip_ws(t), ez, Equal.sym(String, skip_ws(t), u, eu))), WI(t))))

def arrPS(+t: String, +u: String, +eu: {skip_ws(t) == u : String}, res: Maybe<&2, PR>, psi: PSR(ABNF.seq([ELEMS, ABNF.ref("end-array")]), res, u)) -> PSR(ABNF.ref("value"), res, SCon{'[', t}):
  match res:
    case None{}:
      Unit{}
    case Some{+p}:
      (+z, ez, hz, hw) = psi
      (SCon{'[', String.append(wsp(t), z)}, bkEq('[', t, u, z, prt(p), eu, ez), arrayA(t, z, hz), hw)

def bkNil(+o: Char, +cl: Char, +t: String, +x: Char, +w: String, +eu: {skip_ws(t) == SCon{x, w} : String}, +hx: {Char.is_eq(cl, x) == True{} : Bool}) -> {String.append(SCon{o, String.append(wsp(t), SCon{cl, SNil{}})}, w) == SCon{o, t} : String}:
  bkEq(o, t, SCon{x, w}, SCon{cl, SNil{}}, w, eu, Equal.cong(Char, String, zz => SCon{zz, w}, cl, x, char_eq(cl, x, hx)))

def arrNil(+t: String, +x: Char, +w: String, +eu: {skip_ws(t) == SCon{x, w} : String}, +hx: {Char.is_eq(']', x) == True{} : Bool}) -> PSR(ABNF.ref("value"), Some{PR{RArr{[]}, w}}, SCon{'[', t}):
  (SCon{'[', String.append(wsp(t), SCon{']', SNil{}})}, bkNil('[', ']', t, x, w, eu, hx),
    val_array(SCon{'[', String.append(wsp(t), SCon{']', SNil{}})}, MBi("array", B_array, SCon{'[', String.append(wsp(t), SCon{']', SNil{}})}, {==},
      seqI3(BK, ABNF.ref("begin-array"), ABNF.opt(ELEMS), ABNF.ref("end-array"), SCon{'[', wsp(t)}, SNil{}, SCon{']', SNil{}}, tokI("begin-array", '[', SCon{'[', wsp(t)}, {==}, WIa(t)), optN(BK, ELEMS), tokI("end-array", ']', SCon{']', SNil{}}, {==}, {==})))), {==})

def sArr.c(+t: String, +x: Char, +w: String, +eu: {skip_ws(t) == SCon{x, w} : String}, +h: {Char.is_eq(']', x) == True{} : Bool}, +g: Nat) -> PSR(ABNF.ref("value"), brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{'[', t}):
  %Equal.sym(Maybe<&2, PR>, brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), Some{PR{RArr{[]}, w}}, selT(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => Maybe.bind(&2, PR, PR, pv(g, MV{}, SCon{x, w}), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), h)) : PSR(ABNF.ref("value"), _, SCon{'[', t})
  arrNil(t, x, w, eu, h)

def sArr.o(+g: Nat, +t: String, +x: Char, +w: String, +eu: {skip_ws(t) == SCon{x, w} : String}, +h: {Char.is_eq(']', x) == False{} : Bool}, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihA: @w: String -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(g, MA{}, w), w)) -> PSR(ABNF.ref("value"), brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{'[', t}):
  %Equal.sym(Maybe<&2, PR>, brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(g, MV{}, SCon{x, w}), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), selF(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => Maybe.bind(&2, PR, PR, pv(g, MV{}, SCon{x, w}), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), h)) : PSR(ABNF.ref("value"), _, SCon{'[', t})
  arrPS(t, SCon{x, w}, eu, Maybe.bind(&2, PR, PR, pv(g, MV{}, SCon{x, w}), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), itemB(g, SCon{x, w}, pv(g, MV{}, SCon{x, w}), ihV(SCon{x, w}), ihA))

def sArr.go(+g: Nat, +t: String, u: String, +eu: {skip_ws(t) == u : String}, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihA: @w: String -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(g, MA{}, w), w)) -> PSR(ABNF.ref("value"), brk(']', u, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{'[', t}):
  match u:
    case SNil{}:
      arrPS(t, SNil{}, eu, Maybe.bind(&2, PR, PR, pv(g, MV{}, SNil{}), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), itemB(g, SNil{}, pv(g, MV{}, SNil{}), ihV(SNil{}), ihA))
    case SCon{+x, +w}:
      bcase(PSR(ABNF.ref("value"), brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{'[', t}), Char.is_eq(']', x), +h => sArr.c(t, x, w, eu, h, g), +h => sArr.o(g, t, x, w, eu, h, ihV, ihA))

def objectA(+t: String, +z: String, +hz: {ABNF.check(BK, ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), z) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("value"), SCon{'{', String.append(wsp(t), z)}) == True{} : Bool}:
  val_object(SCon{'{', String.append(wsp(t), z)}, MBi("object", B_object, SCon{'{', String.append(wsp(t), z)}, {==},
    seqE3({ABNF.check(BK, B_object, SCon{'{', String.append(wsp(t), z)}) == True{} : Bool}, BK, ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object"), z, hz, +mm => +R => +E => +e => +hm => +hR => +hE =>
      chkTr(BK, B_object, SCon{'{', String.append(wsp(t), String.append(String.append(mm, R), E))}, SCon{'{', String.append(wsp(t), z)}, cons_eq('{', String.append(wsp(t), String.append(String.append(mm, R), E)), String.append(wsp(t), z), app_congl(wsp(t), String.append(String.append(mm, R), E), z, Equal.trans(String, String.append(String.append(mm, R), E), String.append(mm, String.append(R, E)), z, app3(mm, R, E), e))),
        seqI3(BK, ABNF.ref("begin-object"), ABNF.opt(MEMBS), ABNF.ref("end-object"), SCon{'{', wsp(t)}, String.append(mm, R), E, tokI("begin-object", '{', SCon{'{', wsp(t)}, {==}, WIa(t)), optS(BK, MEMBS, String.append(mm, R), seqI2(BK, ABNF.ref("member"), ABNF.rep.any(MITEM), mm, R, hm, hR)), hE)))))

def objPS(+t: String, +u: String, +eu: {skip_ws(t) == u : String}, res: Maybe<&2, PR>, ps: PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), res, u)) -> PSR(ABNF.ref("value"), res, SCon{'{', t}):
  match res:
    case None{}:
      Unit{}
    case Some{+p}:
      (+z, ez, hz, hw) = ps
      (SCon{'{', String.append(wsp(t), z)}, bkEq('{', t, u, z, prt(p), eu, ez), objectA(t, z, hz), hw)

def objNil(+t: String, +x: Char, +w: String, +eu: {skip_ws(t) == SCon{x, w} : String}, +hx: {Char.is_eq('}', x) == True{} : Bool}) -> PSR(ABNF.ref("value"), Some{PR{RObj{[]}, w}}, SCon{'{', t}):
  (SCon{'{', String.append(wsp(t), SCon{'}', SNil{}})}, bkNil('{', '}', t, x, w, eu, hx),
    val_object(SCon{'{', String.append(wsp(t), SCon{'}', SNil{}})}, MBi("object", B_object, SCon{'{', String.append(wsp(t), SCon{'}', SNil{}})}, {==},
      seqI3(BK, ABNF.ref("begin-object"), ABNF.opt(MEMBS), ABNF.ref("end-object"), SCon{'{', wsp(t)}, SNil{}, SCon{'}', SNil{}}, tokI("begin-object", '{', SCon{'{', wsp(t)}, {==}, WIa(t)), optN(BK, MEMBS), tokI("end-object", '}', SCon{'}', SNil{}}, {==}, {==})))), {==})

def sObj.c(+t: String, +x: Char, +w: String, +eu: {skip_ws(t) == SCon{x, w} : String}, +h: {Char.is_eq('}', x) == True{} : Bool}, +g: Nat) -> PSR(ABNF.ref("value"), brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{'{', t}):
  %Equal.sym(Maybe<&2, PR>, brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), Some{PR{RObj{[]}, w}}, selT(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => pv(g, MM{}, SCon{x, w}), h)) : PSR(ABNF.ref("value"), _, SCon{'{', t})
  objNil(t, x, w, eu, h)

def sObj.o(+g: Nat, +t: String, +x: Char, +w: String, +eu: {skip_ws(t) == SCon{x, w} : String}, +h: {Char.is_eq('}', x) == False{} : Bool}, ihM: @w: String -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MM{}, w), w)) -> PSR(ABNF.ref("value"), brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{'{', t}):
  %Equal.sym(Maybe<&2, PR>, brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), pv(g, MM{}, SCon{x, w}), selF(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => pv(g, MM{}, SCon{x, w}), h)) : PSR(ABNF.ref("value"), _, SCon{'{', t})
  objPS(t, SCon{x, w}, eu, pv(g, MM{}, SCon{x, w}), ihM(SCon{x, w}))

def sObj.go(+g: Nat, +t: String, u: String, +eu: {skip_ws(t) == u : String}, ihM: @w: String -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MM{}, w), w)) -> PSR(ABNF.ref("value"), brk('}', u, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{'{', t}):
  match u:
    case SNil{}:
      objPS(t, SNil{}, eu, pv(g, MM{}, SNil{}), ihM(SNil{}))
    case SCon{+x, +w}:
      bcase(PSR(ABNF.ref("value"), brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{'{', t}), Char.is_eq('}', x), +h => sObj.c(t, x, w, eu, h, g), +h => sObj.o(g, t, x, w, eu, h, ihM))

def sepEq(+cl: Char, +x: Char, +w: String, +z: String, +r: String, +ez: {String.append(z, r) == skip_ws(w) : String}, +hx: {Char.is_eq(cl, x) == True{} : Bool})
  -> {String.append(SCon{cl, String.append(wsp(w), z)}, r) == SCon{x, w} : String}:
  scon_eq(cl, x, String.append(String.append(wsp(w), z), r), w, char_eq(cl, x, hx),
    Equal.trans(String, String.append(String.append(wsp(w), z), r), String.append(wsp(w), String.append(z, r)), w, app3(wsp(w), z, r),
      Equal.trans(String, String.append(wsp(w), String.append(z, r)), String.append(wsp(w), skip_ws(w)), w, app_congl(wsp(w), String.append(z, r), skip_ws(w), ez), WI(w))))

def maChk.go(+w: String, -z: String, -Z1: String, +E: String, +v: String, +R: String, +ez: {String.append(Z1, E) == z : String}, +e1: {String.append(v, R) == Z1 : String},
  +hv: {ABNF.check(BK, ABNF.ref("value"), v) == True{} : Bool}, +hR: {ABNF.check(BK, ABNF.rep.any(ITEM), R) == True{} : Bool}, +hE: {ABNF.check(BK, ABNF.ref("end-array"), E) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), SCon{',', String.append(wsp(w), z)}) == True{} : Bool}:
  %ez : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), SCon{',', String.append(wsp(w), _)}) == True{} : Bool}
  %e1 : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), SCon{',', String.append(wsp(w), String.append(_, E))}) == True{} : Bool}
  chkTr(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), String.append(String.append(String.append(SCon{',', wsp(w)}, v), R), E), SCon{',', String.append(wsp(w), String.append(String.append(v, R), E))}, assoc3(SCon{',', wsp(w)}, v, R, E),
    seqI2(BK, ABNF.rep.any(ITEM), ABNF.ref("end-array"), String.append(String.append(SCon{',', wsp(w)}, v), R), E,
      starCons(BK, ITEM, String.append(SCon{',', wsp(w)}, v), R, seqI2(BK, ABNF.ref("value-separator"), ABNF.ref("value"), SCon{',', wsp(w)}, v, tokI("value-separator", ',', SCon{',', wsp(w)}, {==}, WIa(w)), hv), hR), hE))

def maChk(+w: String, +z: String, +hz: {ABNF.check(BK, ABNF.seq([ELEMS, ABNF.ref("end-array")]), z) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), SCon{',', String.append(wsp(w), z)}) == True{} : Bool}:
  seqE2({ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), SCon{',', String.append(wsp(w), z)}) == True{} : Bool}, BK, ELEMS, ABNF.ref("end-array"), z, hz, +Z1 => +E => +ez => +h1 => +hE =>
    seqE2({ABNF.check(BK, ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), SCon{',', String.append(wsp(w), z)}) == True{} : Bool}, BK, ABNF.ref("value"), ABNF.rep.any(ITEM), Z1, h1, +v => +R => +e1 => +hv => +hR => maChk.go(w, z, Z1, E, v, R, ez, e1, hv, hR, hE)))

def maPS(+x: Char, +w: String, +hx: {Char.is_eq(',', x) == True{} : Bool}, res: Maybe<&2, PR>, psi: PSR(ABNF.seq([ELEMS, ABNF.ref("end-array")]), res, skip_ws(w))) -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), res, SCon{x, w}):
  match res:
    case None{}:
      Unit{}
    case Some{+p}:
      (+z, ez, hz, hw) = psi
      (SCon{',', String.append(wsp(w), z)}, sepEq(',', x, w, z, prt(p), ez, hx), maChk(w, z, hz), hw)

def sMA.e(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == True{} : Bool}) -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MA{}, SCon{x, w}), Some{PR{RArr{[]}, w}}, selT(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), h)) : PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), _, SCon{x, w})
  (SCon{']', SNil{}}, scon_eq(']', x, w, w, char_eq(']', x, h), {==}), seqI2(BK, ABNF.rep.any(ITEM), ABNF.ref("end-array"), SNil{}, SCon{']', SNil{}}, starNil(BK, ITEM), tokI("end-array", ']', SCon{']', SNil{}}, {==}, {==})), {==})

def sMA.c(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihA: @w: String -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(g, MA{}, w), w)) -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MA{}, SCon{x, w}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), selF(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), h)) : PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), _, SCon{x, w})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), selT(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}, h2)) : PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), _, SCon{x, w})
  maPS(x, w, h2, Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), itemB(g, skip_ws(w), pv(g, MV{}, skip_ws(w)), ihV(skip_ws(w)), ihA))

def sMA.n(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == False{} : Bool}) -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MA{}, SCon{x, w}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), selF(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), h)) : PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), _, SCon{x, w})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), None{}, selF(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}, h2)) : PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), _, SCon{x, w})
  Unit{}

def sMA(+g: Nat, s: String, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihA: @w: String -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(g, MA{}, w), w)) -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(1n+g, MA{}, s), s):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+x, +w}:
      bcase(PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}), Char.is_eq(']', x), +h => sMA.e(g, x, w, h),
        +h => bcase(PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}), Char.is_eq(',', x), +h2 => sMA.c(g, x, w, h, h2, ihV, ihA), +h2 => sMA.n(g, x, w, h, h2)))

def moChk.go(+w: String, -z: String, +mm: String, +R: String, +E: String, +ez: {String.append(mm, String.append(R, E)) == z : String},
  +hm: {ABNF.check(BK, ABNF.ref("member"), mm) == True{} : Bool}, +hR: {ABNF.check(BK, ABNF.rep.any(MITEM), R) == True{} : Bool}, +hE: {ABNF.check(BK, ABNF.ref("end-object"), E) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), SCon{',', String.append(wsp(w), z)}) == True{} : Bool}:
  %ez : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), SCon{',', String.append(wsp(w), _)}) == True{} : Bool}
  %app3(mm, R, E) : {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), SCon{',', String.append(wsp(w), _)}) == True{} : Bool}
  chkTr(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(String.append(String.append(SCon{',', wsp(w)}, mm), R), E), SCon{',', String.append(wsp(w), String.append(String.append(mm, R), E))}, assoc3(SCon{',', wsp(w)}, mm, R, E),
    seqI2(BK, ABNF.rep.any(MITEM), ABNF.ref("end-object"), String.append(String.append(SCon{',', wsp(w)}, mm), R), E,
      starCons(BK, MITEM, String.append(SCon{',', wsp(w)}, mm), R, seqI2(BK, ABNF.ref("value-separator"), ABNF.ref("member"), SCon{',', wsp(w)}, mm, tokI("value-separator", ',', SCon{',', wsp(w)}, {==}, WIa(w)), hm), hR), hE))

def moChk(+w: String, +z: String, +hz: {ABNF.check(BK, ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), z) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), SCon{',', String.append(wsp(w), z)}) == True{} : Bool}:
  seqE3({ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), SCon{',', String.append(wsp(w), z)}) == True{} : Bool}, BK, ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object"), z, hz, +mm => +R => +E => +ez => +hm => +hR => +hE => moChk.go(w, z, mm, R, E, ez, hm, hR, hE))

def moPS(+x: Char, +w: String, +hx: {Char.is_eq(',', x) == True{} : Bool}, res: Maybe<&2, PR>, ps: PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), res, skip_ws(w))) -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), res, SCon{x, w}):
  match res:
    case None{}:
      Unit{}
    case Some{+p}:
      (+z, ez, hz, hw) = ps
      (SCon{',', String.append(wsp(w), z)}, sepEq(',', x, w, z, prt(p), ez, hx), moChk(w, z, hz), hw)

def sMO.e(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == True{} : Bool}) -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MO{}, SCon{x, w}), Some{PR{RObj{[]}, w}}, selT(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), h)) : PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{x, w})
  (SCon{'}', SNil{}}, scon_eq('}', x, w, w, char_eq('}', x, h), {==}), seqI2(BK, ABNF.rep.any(MITEM), ABNF.ref("end-object"), SNil{}, SCon{'}', SNil{}}, starNil(BK, MITEM), tokI("end-object", '}', SCon{'}', SNil{}}, {==}, {==})), {==})

def sMO.c(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, ihM: @w: String -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MM{}, w), w)) -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MO{}, SCon{x, w}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), selF(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), h)) : PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{x, w})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), pv(g, MM{}, skip_ws(w)), selT(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}, h2)) : PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{x, w})
  moPS(x, w, h2, pv(g, MM{}, skip_ws(w)), ihM(skip_ws(w)))

def sMO.n(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == False{} : Bool}) -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MO{}, SCon{x, w}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), selF(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), h)) : PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{x, w})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), None{}, selF(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}, h2)) : PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{x, w})
  Unit{}

def sMO(+g: Nat, s: String, ihM: @w: String -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MM{}, w), w)) -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MO{}, s), s):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+x, +w}:
      bcase(PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}), Char.is_eq('}', x), +h => sMO.e(g, x, w, h),
        +h => bcase(PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}), Char.is_eq(',', x), +h2 => sMO.c(g, x, w, h, h2, ihM), +h2 => sMO.n(g, x, w, h, h2)))

def nsTok(+sq: String, +w: String) -> {tokb(':', String.append(wsp(sq), SCon{':', wsp(w)})) == True{} : Bool}:
  Equal.trans(Bool, tokb2(':', skip_ws(String.append(wsp(sq), SCon{':', wsp(w)}))), tokb2(':', skip_ws(SCon{':', wsp(w)})), True{}, Equal.cong(String, Bool, z => tokb2(':', z), skip_ws(String.append(wsp(sq), SCon{':', wsp(w)})), skip_ws(SCon{':', wsp(w)}), WE(wsp(sq), SCon{':', wsp(w)}, WIa(sq))), WIa(w))

def memText(+k: String, +sq: String, +w: String, +y1: String, +hk: {ABNF.check(BK, CHARS, k) == True{} : Bool}, +hv1: {ABNF.check(BK, ABNF.ref("value"), y1) == True{} : Bool}) -> {ABNF.check(BK, ABNF.ref("member"), String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1))) == True{} : Bool}:
  MBi("member", B_member, String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), {==}, seqI3(BK, ABNF.ref("string"), ABNF.ref("name-separator"), ABNF.ref("value"), SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(wsp(sq), SCon{':', wsp(w)}), y1, strText(k, hk), tokI("name-separator", ':', String.append(wsp(sq), SCon{':', wsp(w)}), {==}, nsTok(sq, w)), hv1))

def memChk(+k: String, +sq: String, +w: String, +y1: String, +Y: String, +hk: {ABNF.check(BK, CHARS, k) == True{} : Bool}, +hv1: {ABNF.check(BK, ABNF.ref("value"), y1) == True{} : Bool}, +hY: {ABNF.check(BK, ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), Y) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), Y)) == True{} : Bool}:
  seqE2({ABNF.check(BK, ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), Y)) == True{} : Bool}, BK, ABNF.rep.any(MITEM), ABNF.ref("end-object"), Y, hY, +R => +E => +e => +hR => +hE =>
    chkTr(BK, ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), String.append(R, E)), String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), Y), app_congl(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), String.append(R, E), Y, e),
      seqI3(BK, ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object"), String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), R, E, memText(k, sq, w, y1, hk, hv1), hR, hE)))

def memEq(+k: String, +sq: String, -t: String, +x: Char, +w: String, +y1: String, +u1: String, +y2: String, +u2: String, +eq1: {String.append(k, SCon{'"', sq}) == t : String}, +eu: {skip_ws(sq) == SCon{x, w} : String},
  +hx: {Char.is_eq(':', x) == True{} : Bool}, +e1: {String.append(y1, u1) == skip_ws(w) : String}, +e2: {String.append(y2, u2) == skip_ws(u1) : String})
  -> {String.append(String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), String.append(wsp(u1), y2)), u2) == SCon{'"', t} : String}:
  %Equal.sym(String, String.append(String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), String.append(wsp(u1), y2)), u2), String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), String.append(String.append(wsp(u1), y2), u2)), app3(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), String.append(wsp(u1), y2), u2)) : {_ == SCon{'"', t} : String}
  %Equal.sym(String, String.append(String.append(wsp(u1), y2), u2), String.append(wsp(u1), String.append(y2, u2)), app3(wsp(u1), y2, u2)) : {String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), _) == SCon{'"', t} : String}
  %Equal.sym(String, String.append(y2, u2), skip_ws(u1), e2) : {String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), String.append(wsp(u1), _)) == SCon{'"', t} : String}
  %Equal.sym(String, String.append(wsp(u1), skip_ws(u1)), u1, WI(u1)) : {String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), _) == SCon{'"', t} : String}
  %Equal.sym(String, String.append(String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1)), u1), String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1), u1)), app3(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1), u1)) : {_ == SCon{'"', t} : String}
  %Equal.sym(String, String.append(String.append(String.append(wsp(sq), SCon{':', wsp(w)}), y1), u1), String.append(String.append(wsp(sq), SCon{':', wsp(w)}), String.append(y1, u1)), app3(String.append(wsp(sq), SCon{':', wsp(w)}), y1, u1)) : {String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, _) == SCon{'"', t} : String}
  %Equal.sym(String, String.append(y1, u1), skip_ws(w), e1) : {String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), _)) == SCon{'"', t} : String}
  %Equal.sym(String, String.append(String.append(wsp(sq), SCon{':', wsp(w)}), skip_ws(w)), String.append(wsp(sq), String.append(SCon{':', wsp(w)}, skip_ws(w))), app3(wsp(sq), SCon{':', wsp(w)}, skip_ws(w))) : {String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, _) == SCon{'"', t} : String}
  %Equal.sym(String, String.append(wsp(w), skip_ws(w)), w, WI(w)) : {String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(wsp(sq), SCon{':', _})) == SCon{'"', t} : String}
  %Equal.sym(Char, ':', x, char_eq(':', x, hx)) : {String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(wsp(sq), SCon{_, w})) == SCon{'"', t} : String}
  %eu : {String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, String.append(wsp(sq), _)) == SCon{'"', t} : String}
  %Equal.sym(String, String.append(wsp(sq), skip_ws(sq)), sq, WI(sq)) : {String.append(SCon{'"', String.append(k, SCon{'"', SNil{}})}, _) == SCon{'"', t} : String}
  %Equal.sym(String, String.append(String.append(k, SCon{'"', SNil{}}), sq), String.append(k, String.append(SCon{'"', SNil{}}, sq)), app3(k, SCon{'"', SNil{}}, sq)) : {SCon{'"', _} == SCon{'"', t} : String}
  cons_eq('"', String.append(k, SCon{'"', sq}), t, eq1)

def memB4(-t: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, +x: Char, +w: String, +eu: {skip_ws(spt(q)) == SCon{x, w} : String}, +hx: {Char.is_eq(':', x) == True{} : Bool},
  +p1: PR, +y1: String, +e1: {String.append(y1, prt(p1)) == skip_ws(w) : String}, +hv1: {ABNF.check(BK, ABNF.ref("value"), y1) == True{} : Bool}, +hw1: {wf(prr(p1)) == True{} : Bool}, r2: Maybe<&2, PR>, ps2: PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), r2, skip_ws(prt(p1))))
  -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), ocons(spa(q), prr(p1), r2), SCon{'"', t}):
  match r2:
    case None{}:
      Unit{}
    case Some{+p2}:
      (+y2, e2, h2, hw2) = ps2
      (String.append(String.append(SCon{'"', String.append(spa(q), SCon{'"', SNil{}})}, String.append(String.append(wsp(spt(q)), SCon{':', wsp(w)}), y1)), String.append(wsp(prt(p1)), y2)), memEq(spa(q), spt(q), t, x, w, y1, prt(p1), y2, prt(p2), eq1, eu, hx, e1, e2),
        memChk(spa(q), spt(q), w, y1, String.append(wsp(prt(p1)), y2), hk, hv1, absMO(wsp(prt(p1)), y2, WIa(prt(p1)), h2)), wfOcons(spa(q), prr(p1), prr(p2), strokOf(spa(q), hk), hw1, hw2))

def memB3(+g: Nat, -t: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, +x: Char, +w: String, +eu: {skip_ws(spt(q)) == SCon{x, w} : String}, +hx: {Char.is_eq(':', x) == True{} : Bool},
  r1: Maybe<&2, PR>, ps1: PSR(ABNF.ref("value"), r1, skip_ws(w)), ihO: @w: String -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MO{}, w), w)) -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), Maybe.bind(&2, PR, PR, r1, +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))), SCon{'"', t}):
  match r1:
    case None{}:
      Unit{}
    case Some{+p1}:
      (+y1, e1, hv1, hw1) = ps1
      memB4(t, q, eq1, hk, x, w, eu, hx, p1, y1, e1, hv1, hw1, pv(g, MO{}, skip_ws(prt(p1))), ihO(skip_ws(prt(p1))))

def memB2.c(+g: Nat, -t: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, +x: Char, +w: String, +eu: {skip_ws(spt(q)) == SCon{x, w} : String}, +h: {Char.is_eq(':', x) == True{} : Bool}, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihO: @w: String -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MO{}, w), w))
  -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), SCon{'"', t}):
  %Equal.sym(Maybe<&2, PR>, colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))), selT(Maybe<&2, PR>, Char.is_eq(':', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))), z => None{}, h)) : PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{'"', t})
  memB3(g, t, q, eq1, hk, x, w, eu, h, pv(g, MV{}, skip_ws(w)), ihV(skip_ws(w)), ihO)

def memB2.n(+g: Nat, -t: String, +q: SP, +x: Char, +w: String, +h: {Char.is_eq(':', x) == False{} : Bool}) -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), SCon{'"', t}):
  %Equal.sym(Maybe<&2, PR>, colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), None{}, selF(Maybe<&2, PR>, Char.is_eq(':', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))), z => None{}, h)) : PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{'"', t})
  Unit{}

def memB2(+g: Nat, -t: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, u: String, +eu: {skip_ws(spt(q)) == u : String}, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihO: @w: String -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MO{}, w), w))
  -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), colon(u, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), SCon{'"', t}):
  match u:
    case SNil{}:
      Unit{}
    case SCon{+x, +w}:
      bcase(PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), SCon{'"', t}), Char.is_eq(':', x), +h => memB2.c(g, t, q, eq1, hk, x, w, eu, h, ihV, ihO), +h => memB2.n(g, t, q, x, w, h))

# An object member, from its opening quote on.
def memB(+g: Nat, -t: String, m1: Maybe<&2, SP>, sns: SNS(m1, t, CHARS), ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihO: @w: String -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MO{}, w), w)) -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), Maybe.bind(&2, SP, PR, m1, +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))))), SCon{'"', t}):
  match m1:
    case None{}:
      Unit{}
    case Some{+q}:
      (eq1, +hk) = sns
      memB2(g, t, q, eq1, hk, skip_ws(spt(q)), {==}, ihV, ihO)

def sMM.q(+g: Nat, +c: Char, +t: String, +h: {Char.is_eq('"', c) == True{} : Bool}, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihO: @w: String -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MO{}, w), w)) -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MM{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MM{}, SCon{c, t}), Maybe.bind(&2, SP, PR, str_scan(t, SN{}), +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))))), selT(Maybe<&2, PR>, Char.is_eq('"', c), u => Maybe.bind(&2, SP, PR, str_scan(t, SN{}), +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))))), u => None{}, h)) : PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{c, t})
  %char_eq('"', c, h) : PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), Maybe.bind(&2, SP, PR, str_scan(t, SN{}), +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))))), SCon{_, t})
  memB(g, t, str_scan(t, SN{}), strS(t, SN{}), ihV, ihO)

def sMM.n(+g: Nat, +c: Char, +t: String, +h: {Char.is_eq('"', c) == False{} : Bool}) -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MM{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MM{}, SCon{c, t}), None{}, selF(Maybe<&2, PR>, Char.is_eq('"', c), u => Maybe.bind(&2, SP, PR, str_scan(t, SN{}), +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))))), u => None{}, h)) : PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), _, SCon{c, t})
  Unit{}

def sMM(+g: Nat, +c: Char, +t: String, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihO: @w: String -> PSR(ABNF.seq([ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MO{}, w), w)) -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MM{}, SCon{c, t}), SCon{c, t}):
  bcase(PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(1n+g, MM{}, SCon{c, t}), SCon{c, t}), Char.is_eq('"', c), +h => sMM.q(g, c, t, h, ihV, ihO), +h => sMM.n(g, c, t, h))

def sMV.num(+g: Nat, +c: Char, +t: String, +h0: {isnum0(c) == True{} : Bool}) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t}), numv(num_scan(SCon{c, t})), selT(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  numvPS(num_scan(SCon{c, t}), SCon{c, t}, numS(SCon{c, t}))

def sMV.n(+g: Nat, +c: Char, +t: String, +h0: {isnum0(c) == False{} : Bool}, +h1: {Char.is_eq('n', c) == True{} : Bool}) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t}), sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), selF(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), lit("ull", t, RNull{}), selT(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), h1)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %char_eq('n', c, h1) : PSR(ABNF.ref("value"), lit("ull", t, RNull{}), SCon{_, t})
  litPS('n', "ull", t, RNull{}, val_null("null", MBi("null", ABNF.string.case_sensitive("null"), "null", {==}, csI(BK, "null"))), {==})

def sMV.t(+g: Nat, +c: Char, +t: String, +h0: {isnum0(c) == False{} : Bool}, +h1: {Char.is_eq('n', c) == False{} : Bool}, +h2: {Char.is_eq('t', c) == True{} : Bool}) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t}), sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), selF(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), selF(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), h1)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), lit("rue", t, RBool{True{}}), selT(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), h2)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %char_eq('t', c, h2) : PSR(ABNF.ref("value"), lit("rue", t, RBool{True{}}), SCon{_, t})
  litPS('t', "rue", t, RBool{True{}}, val_true("true", MBi("true", ABNF.string.case_sensitive("true"), "true", {==}, csI(BK, "true"))), {==})

def sMV.f(+g: Nat, +c: Char, +t: String, +h0: {isnum0(c) == False{} : Bool}, +h1: {Char.is_eq('n', c) == False{} : Bool}, +h2: {Char.is_eq('t', c) == False{} : Bool}, +h3: {Char.is_eq('f', c) == True{} : Bool}) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t}), sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), selF(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), selF(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), h1)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), selF(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), h2)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), lit("alse", t, RBool{False{}}), selT(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), h3)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %char_eq('f', c, h3) : PSR(ABNF.ref("value"), lit("alse", t, RBool{False{}}), SCon{_, t})
  litPS('f', "alse", t, RBool{False{}}, val_false("false", MBi("false", ABNF.string.case_sensitive("false"), "false", {==}, csI(BK, "false"))), {==})

def sMV.s(+g: Nat, +c: Char, +t: String, +h0: {isnum0(c) == False{} : Bool}, +h1: {Char.is_eq('n', c) == False{} : Bool}, +h2: {Char.is_eq('t', c) == False{} : Bool}, +h3: {Char.is_eq('f', c) == False{} : Bool}, +h4: {Char.is_eq('"', c) == True{} : Bool}) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t}), sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), selF(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), selF(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), h1)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), selF(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), h2)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), selF(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), h3)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), strv(str_scan(t, SN{})), selT(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), h4)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %char_eq('"', c, h4) : PSR(ABNF.ref("value"), strv(str_scan(t, SN{})), SCon{_, t})
  strvPS(str_scan(t, SN{}), t, strS(t, SN{}))

def sMV.a(+g: Nat, +c: Char, +t: String, +h0: {isnum0(c) == False{} : Bool}, +h1: {Char.is_eq('n', c) == False{} : Bool}, +h2: {Char.is_eq('t', c) == False{} : Bool}, +h3: {Char.is_eq('f', c) == False{} : Bool}, +h4: {Char.is_eq('"', c) == False{} : Bool}, +h5: {Char.is_eq('[', c) == True{} : Bool}, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihA: @w: String -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(g, MA{}, w), w)) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t}), sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), selF(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), selF(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), h1)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), selF(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), h2)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), selF(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), h3)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), selF(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), h4)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), selT(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), h5)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %char_eq('[', c, h5) : PSR(ABNF.ref("value"), brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{_, t})
  sArr.go(g, t, skip_ws(t), {==}, ihV, ihA)

def sMV.o(+g: Nat, +c: Char, +t: String, +h0: {isnum0(c) == False{} : Bool}, +h1: {Char.is_eq('n', c) == False{} : Bool}, +h2: {Char.is_eq('t', c) == False{} : Bool}, +h3: {Char.is_eq('f', c) == False{} : Bool}, +h4: {Char.is_eq('"', c) == False{} : Bool}, +h5: {Char.is_eq('[', c) == False{} : Bool}, +h6: {Char.is_eq('{', c) == True{} : Bool}, ihM: @w: String -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MM{}, w), w)) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t}), sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), selF(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), selF(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), h1)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), selF(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), h2)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), selF(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), h3)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), selF(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), h4)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), selF(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), h5)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), selT(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}, h6)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %char_eq('{', c, h6) : PSR(ABNF.ref("value"), brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{_, t})
  sObj.go(g, t, skip_ws(t), {==}, ihM)

def sMV.z(+g: Nat, +c: Char, +t: String, +h0: {isnum0(c) == False{} : Bool}, +h1: {Char.is_eq('n', c) == False{} : Bool}, +h2: {Char.is_eq('t', c) == False{} : Bool}, +h3: {Char.is_eq('f', c) == False{} : Bool}, +h4: {Char.is_eq('"', c) == False{} : Bool}, +h5: {Char.is_eq('[', c) == False{} : Bool}, +h6: {Char.is_eq('{', c) == False{} : Bool}) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t}), sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), selF(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), selF(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), h1)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), selF(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), h2)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), selF(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), h3)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), selF(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), h4)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), selF(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), h5)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), None{}, selF(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}, h6)) : PSR(ABNF.ref("value"), _, SCon{c, t})
  Unit{}

def sMV(+g: Nat, +c: Char, +t: String, ihV: @w: String -> PSR(ABNF.ref("value"), pv(g, MV{}, w), w), ihA: @w: String -> PSR(ABNF.seq([ABNF.rep.any(ITEM), ABNF.ref("end-array")]), pv(g, MA{}, w), w), ihM: @w: String -> PSR(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(MITEM), ABNF.ref("end-object")]), pv(g, MM{}, w), w)) -> PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}):
  bcase(PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}), isnum0(c), +h0 => sMV.num(g, c, t, h0), +h0 => bcase(PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}), Char.is_eq('n', c), +h1 => sMV.n(g, c, t, h0, h1), +h1 => bcase(PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}), Char.is_eq('t', c), +h2 => sMV.t(g, c, t, h0, h1, h2), +h2 => bcase(PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}), Char.is_eq('f', c), +h3 => sMV.f(g, c, t, h0, h1, h2, h3), +h3 => bcase(PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}), Char.is_eq('"', c), +h4 => sMV.s(g, c, t, h0, h1, h2, h3, h4), +h4 => bcase(PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}), Char.is_eq('[', c), +h5 => sMV.a(g, c, t, h0, h1, h2, h3, h4, h5, ihV, ihA), +h5 => bcase(PSR(ABNF.ref("value"), pv(1n+g, MV{}, SCon{c, t}), SCon{c, t}), Char.is_eq('{', c), +h6 => sMV.o(g, c, t, h0, h1, h2, h3, h4, h5, h6, ihM), +h6 => sMV.z(g, c, t, h0, h1, h2, h3, h4, h5, h6))))))))

# What pv reads matches the grammar, and what it builds is valid.
def Sound(f: Nat, m: Md, s: String) -> PSR(TM(m), pv(f, m, s), s):
  match f:
    case 0n:
      Unit{}
    case 1n+ +g:
      match m:
        case MV{}:
          match s:
            case SNil{}:
              Unit{}
            case SCon{+c, +t}:
              sMV(g, c, t, w => Sound(g, MV{}, w), w => Sound(g, MA{}, w), w => Sound(g, MM{}, w))
        case MA{}:
          sMA(g, s, w => Sound(g, MV{}, w), w => Sound(g, MA{}, w))
        case MM{}:
          match s:
            case SNil{}:
              Unit{}
            case SCon{+c, +t}:
              sMM(g, c, t, w => Sound(g, MV{}, w), w => Sound(g, MO{}, w))
        case MO{}:
          sMO(g, s, w => Sound(g, MM{}, w))

# Parser extension
# ================

def pvNil(g: Nat) -> {pv(g, MV{}, SNil{}) == None{} : Maybe<&2, PR>}:
  match g:
    case 0n:
      {==}
    case 1n+ +g1:
      {==}

def mvNE(g: Nat, z: String, -p: PR, +e: {pv(g, MV{}, z) == Some{p} : Maybe<&2, PR>}) -> {String.is_empty(z) == False{} : Bool}:
  match z:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(g, MV{}, SNil{}), Some{p}, Equal.sym(Maybe<&2, PR>, pv(g, MV{}, SNil{}), None{}, pvNil(g)), e)))
    case SCon{c, r}:
      {==}

def pvMANil(g: Nat) -> {pv(g, MA{}, SNil{}) == None{} : Maybe<&2, PR>}:
  match g:
    case 0n:
      {==}
    case 1n+ +g1:
      {==}

def pvMONil(g: Nat) -> {pv(g, MO{}, SNil{}) == None{} : Maybe<&2, PR>}:
  match g:
    case 0n:
      {==}
    case 1n+ +g1:
      {==}

def pvMMNil(g: Nat) -> {pv(g, MM{}, SNil{}) == None{} : Maybe<&2, PR>}:
  match g:
    case 0n:
      {==}
    case 1n+ +g1:
      {==}

def maNE(g: Nat, z: String, -p: PR, +e: {pv(g, MA{}, z) == Some{p} : Maybe<&2, PR>}) -> {String.is_empty(z) == False{} : Bool}:
  match z:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(g, MA{}, SNil{}), Some{p}, Equal.sym(Maybe<&2, PR>, pv(g, MA{}, SNil{}), None{}, pvMANil(g)), e)))
    case SCon{c, r}:
      {==}

def moNE(g: Nat, z: String, -p: PR, +e: {pv(g, MO{}, z) == Some{p} : Maybe<&2, PR>}) -> {String.is_empty(z) == False{} : Bool}:
  match z:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(g, MO{}, SNil{}), Some{p}, Equal.sym(Maybe<&2, PR>, pv(g, MO{}, SNil{}), None{}, pvMONil(g)), e)))
    case SCon{c, r}:
      {==}

def mmNE(g: Nat, z: String, -p: PR, +e: {pv(g, MM{}, z) == Some{p} : Maybe<&2, PR>}) -> {String.is_empty(z) == False{} : Bool}:
  match z:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(g, MM{}, SNil{}), Some{p}, Equal.sym(Maybe<&2, PR>, pv(g, MM{}, SNil{}), None{}, pvMMNil(g)), e)))
    case SCon{c, r}:
      {==}

def skipApp.go(+x: String, +t: String, y: String, +e: {skip_ws(x) == y : String}, +h: {String.is_empty(y) == False{} : Bool}) -> {skip_ws(String.append(x, t)) == String.append(y, t) : String}:
  match y:
    case SNil{}:
      Empty.absurd({skip_ws(String.append(x, t)) == String.append(SNil{}, t) : String}, false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case SCon{+c, +r}:
      SKA(x, t, c, r, e)

# When skip_ws leaves something, more text after it stays.
def skipApp(+x: String, +t: String, +h: {String.is_empty(skip_ws(x)) == False{} : Bool}) -> {skip_ws(String.append(x, t)) == String.append(skip_ws(x), t) : String}:
  skipApp.go(x, t, skip_ws(x), {==}, h)

def swSelf(p: String, -X: String) -> {String.starts_with(String.append(p, X), p) == True{} : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, char_refl(c)) : {String.starts_with.go.if(r, String.append(r, X), _) == True{} : Bool}
      swSelf(r, X)

def dropSelf(p: String, +X: String) -> {String.drop(String.append(p, X), String.length(p)) == X : String}:
  match p:
    case SNil{}:
      match X:
        case SNil{}:
          {==}
        case SCon{c, r}:
          {==}
    case SCon{c, +r}:
      dropSelf(r, X)

def EXT(m: Md, res: Maybe<&2, PR>, s: String, f: Nat) -> Type:
  match res:
    case None{}:
      Unit
    case Some{p}:
      @t: String -> @f2: Nat -> {fol(String.append(prt(p), t)) == True{} : Bool} -> {le(f, f2) == True{} : Bool} -> {pv(f2, m, String.append(s, t)) == Some{PR{prr(p), String.append(prt(p), t)}} : Maybe<&2, PR>}

def folMA.f(g: Nat, +c: Char, +r: String, -p: PR, +hc: {isws(c) == False{} : Bool}, +e: {pv(g, MA{}, SCon{c, r}) == Some{p} : Maybe<&2, PR>}) -> {isfol(c) == True{} : Bool}:
  match g:
    case 0n:
      Empty.absurd({isfol(c) == True{} : Bool}, none_ne_some(&2, PR, p, e))
    case 1n+ +g1:
      bcase({isfol(c) == True{} : Bool}, Char.is_eq(']', c),
        +k => or_r(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), or_r(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})), or_l(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}), k))),
        +k => bcase({isfol(c) == True{} : Bool}, Char.is_eq(',', c),
          +k2 => or_r(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), or_l(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})), k2)),
          +k2 => Empty.absurd({isfol(c) == True{} : Bool}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(1n+g1, MA{}, SCon{c, r}), Some{p},
            Equal.sym(Maybe<&2, PR>, pv(1n+g1, MA{}, SCon{c, r}), None{}, Equal.trans(Maybe<&2, PR>, pv(1n+g1, MA{}, SCon{c, r}), sel(Maybe<&2, PR>, Char.is_eq(',', c), z => Maybe.bind(&2, PR, PR, pv(g1, MV{}, skip_ws(r)), +p => acons(prr(p), pv(g1, MA{}, skip_ws(prt(p))))), z => None{}), None{},
              selF(Maybe<&2, PR>, Char.is_eq(']', c), z => Some{PR{RArr{[]}, r}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', c), z => Maybe.bind(&2, PR, PR, pv(g1, MV{}, skip_ws(r)), +p => acons(prr(p), pv(g1, MA{}, skip_ws(prt(p))))), z => None{}), k),
              selF(Maybe<&2, PR>, Char.is_eq(',', c), z => Maybe.bind(&2, PR, PR, pv(g1, MV{}, skip_ws(r)), +p => acons(prr(p), pv(g1, MA{}, skip_ws(prt(p))))), z => None{}, k2))), e)))))

def folMO.f(g: Nat, +c: Char, +r: String, -p: PR, +hc: {isws(c) == False{} : Bool}, +e: {pv(g, MO{}, SCon{c, r}) == Some{p} : Maybe<&2, PR>}) -> {isfol(c) == True{} : Bool}:
  match g:
    case 0n:
      Empty.absurd({isfol(c) == True{} : Bool}, none_ne_some(&2, PR, p, e))
    case 1n+ +g1:
      bcase({isfol(c) == True{} : Bool}, Char.is_eq('}', c),
        +k => or_r(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), or_r(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})), or_r(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}), or_l(Char.is_eq('}', c), False{}, k)))),
        +k => bcase({isfol(c) == True{} : Bool}, Char.is_eq(',', c),
          +k2 => or_r(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), or_l(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{})), k2)),
          +k2 => Empty.absurd({isfol(c) == True{} : Bool}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(1n+g1, MO{}, SCon{c, r}), Some{p},
            Equal.sym(Maybe<&2, PR>, pv(1n+g1, MO{}, SCon{c, r}), None{}, Equal.trans(Maybe<&2, PR>, pv(1n+g1, MO{}, SCon{c, r}), sel(Maybe<&2, PR>, Char.is_eq(',', c), z => pv(g1, MM{}, skip_ws(r)), z => None{}), None{},
              selF(Maybe<&2, PR>, Char.is_eq('}', c), z => Some{PR{RObj{[]}, r}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', c), z => pv(g1, MM{}, skip_ws(r)), z => None{}), k),
              selF(Maybe<&2, PR>, Char.is_eq(',', c), z => pv(g1, MM{}, skip_ws(r)), z => None{}, k2))), e)))))

# After a value, what MA reads starts with whitespace, a comma or a closing bracket.
def folMA(g: Nat, z0: String, -t: String, -p: PR, +e: {pv(g, MA{}, skip_ws(z0)) == Some{p} : Maybe<&2, PR>}) -> {fol(String.append(z0, t)) == True{} : Bool}:
  match z0:
    case SNil{}:
      Empty.absurd({fol(t) == True{} : Bool}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(g, MA{}, SNil{}), Some{p}, Equal.sym(Maybe<&2, PR>, pv(g, MA{}, SNil{}), None{}, pvMANil(g)), e)))
    case SCon{+c, +r}:
      bcase({isfol(c) == True{} : Bool}, isws(c),
        +k => or_l(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), k),
        +k => folMA.f(g, c, r, p, k, Equal.trans(Maybe<&2, PR>, pv(g, MA{}, SCon{c, r}), pv(g, MA{}, skip_ws(SCon{c, r})), Some{p}, Equal.cong(String, Maybe<&2, PR>, zz => pv(g, MA{}, zz), SCon{c, r}, skip_ws(SCon{c, r}), Equal.sym(String, skip_ws(SCon{c, r}), SCon{c, r}, skipF(c, r, k))), e)))

# After a value, what MO reads starts with whitespace, a comma or a closing bracket.
def folMO(g: Nat, z0: String, -t: String, -p: PR, +e: {pv(g, MO{}, skip_ws(z0)) == Some{p} : Maybe<&2, PR>}) -> {fol(String.append(z0, t)) == True{} : Bool}:
  match z0:
    case SNil{}:
      Empty.absurd({fol(t) == True{} : Bool}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(g, MO{}, SNil{}), Some{p}, Equal.sym(Maybe<&2, PR>, pv(g, MO{}, SNil{}), None{}, pvMONil(g)), e)))
    case SCon{+c, +r}:
      bcase({isfol(c) == True{} : Bool}, isws(c),
        +k => or_l(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), k),
        +k => folMO.f(g, c, r, p, k, Equal.trans(Maybe<&2, PR>, pv(g, MO{}, SCon{c, r}), pv(g, MO{}, skip_ws(SCon{c, r})), Some{p}, Equal.cong(String, Maybe<&2, PR>, zz => pv(g, MO{}, zz), SCon{c, r}, skip_ws(SCon{c, r}), Equal.sym(String, skip_ws(SCon{c, r}), SCon{c, r}, skipF(c, r, k))), e)))

def eNum.fin(+g: Nat, +c: Char, +t0: String, +h0: {isnum0(c) == True{} : Bool}, +a: String, +u: String, +e: {String.append(a, u) == SCon{c, t0} : String}, +hB: {ABNF.check(BK, B_number, a) == True{} : Bool},
  +t: String, f2: Nat, +hf: {fol(String.append(u, t)) == True{} : Bool}, +hl: {le(1n+g, f2) == True{} : Bool}) -> {pv(f2, MV{}, String.append(SCon{c, t0}, t)) == Some{PR{RNum{a}, String.append(u, t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MV{}, String.append(SCon{c, t0}, t)) == Some{PR{RNum{a}, String.append(u, t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(Maybe<&2, PR>, pv(1n+g2, MV{}, SCon{c, String.append(t0, t)}), numv(num_scan(SCon{c, String.append(t0, t)})), selT(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, String.append(t0, t)})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", String.append(t0, t), RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", String.append(t0, t), RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", String.append(t0, t), RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(String.append(t0, t), SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(String.append(t0, t)), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, w), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(String.append(t0, t)), w => Some{PR{RObj{[]}, w}}, w => pv(g2, MM{}, w)), u => None{})))))), h0)) : {_ == Some{PR{RNum{a}, String.append(u, t)}} : Maybe<&2, PR>}
      %Equal.trans(String, String.append(a, String.append(u, t)), String.append(String.append(a, u), t), SCon{c, String.append(t0, t)}, Equal.sym(String, String.append(String.append(a, u), t), String.append(a, String.append(u, t)), app3(a, u, t)), Equal.cong(String, String, zz => String.append(zz, t), String.append(a, u), SCon{c, t0}, e)) : {numv(num_scan(_)) == Some{PR{RNum{a}, String.append(u, t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, SP>, num_scan(String.append(a, String.append(u, t))), Some{SP{a, String.append(u, t)}}, numC(a, String.append(u, t), hB, hf)) : {numv(_) == Some{PR{RNum{a}, String.append(u, t)}} : Maybe<&2, PR>}
      {==}

def eNum(+g: Nat, +c: Char, +t0: String, +h0: {isnum0(c) == True{} : Bool}, m: Maybe<&2, SP>, ns: NS(m, SCon{c, t0}, B_number)) -> EXT(MV{}, numv(m), SCon{c, t0}, 1n+g):
  match m:
    case None{}:
      Unit{}
    case Some{q}:
      match q:
        case SP{+a, +u}:
          (e, +hB) = ns
          +t => f2 => +hf => +hl => eNum.fin(g, c, t0, h0, a, u, e, hB, t, f2, hf, hl)

def eLit.fin(+g: Nat, +ch: Char, +p: String, +t0: String, +r: Raw, +hs: {String.starts_with(t0, p) == True{} : Bool}, hd: @g2: Nat -> @X: String -> {pv(1n+g2, MV{}, SCon{ch, X}) == lit(p, X, r) : Maybe<&2, PR>},
  +t: String, f2: Nat, +hl: {le(1n+g, f2) == True{} : Bool}) -> {pv(f2, MV{}, String.append(SCon{ch, t0}, t)) == Some{PR{r, String.append(String.drop(t0, String.length(p)), t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MV{}, String.append(SCon{ch, t0}, t)) == Some{PR{r, String.append(String.drop(t0, String.length(p)), t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(Maybe<&2, PR>, pv(1n+g2, MV{}, SCon{ch, String.append(t0, t)}), lit(p, String.append(t0, t), r), hd(g2, String.append(t0, t))) : {_ == Some{PR{r, String.append(String.drop(t0, String.length(p)), t)}} : Maybe<&2, PR>}
      %swDrop(p, t0, hs) : {lit(p, String.append(_, t), r) == Some{PR{r, String.append(String.drop(t0, String.length(p)), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, String.append(String.append(p, String.drop(t0, String.length(p))), t), String.append(p, String.append(String.drop(t0, String.length(p)), t)), app3(p, String.drop(t0, String.length(p)), t)) : {lit(p, _, r) == Some{PR{r, String.append(String.drop(t0, String.length(p)), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, lit(p, String.append(p, String.append(String.drop(t0, String.length(p)), t)), r), Some{PR{r, String.drop(String.append(p, String.append(String.drop(t0, String.length(p)), t)), String.length(p))}}, selT(Maybe<&2, PR>, String.starts_with(String.append(p, String.append(String.drop(t0, String.length(p)), t)), p), u => Some{PR{r, String.drop(String.append(p, String.append(String.drop(t0, String.length(p)), t)), String.length(p))}}, u => None{}, swSelf(p, String.append(String.drop(t0, String.length(p)), t)))) : {_ == Some{PR{r, String.append(String.drop(t0, String.length(p)), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, String.drop(String.append(p, String.append(String.drop(t0, String.length(p)), t)), String.length(p)), String.append(String.drop(t0, String.length(p)), t), dropSelf(p, String.append(String.drop(t0, String.length(p)), t))) : {Some{PR{r, _}} == Some{PR{r, String.append(String.drop(t0, String.length(p)), t)}} : Maybe<&2, PR>}
      {==}

def eLit.t(+g: Nat, +ch: Char, +p: String, +t0: String, +r: Raw, +hs: {String.starts_with(t0, p) == True{} : Bool}, hd: @g2: Nat -> @X: String -> {pv(1n+g2, MV{}, SCon{ch, X}) == lit(p, X, r) : Maybe<&2, PR>}) -> EXT(MV{}, lit(p, t0, r), SCon{ch, t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, lit(p, t0, r), Some{PR{r, String.drop(t0, String.length(p))}}, selT(Maybe<&2, PR>, String.starts_with(t0, p), u => Some{PR{r, String.drop(t0, String.length(p))}}, u => None{}, hs)) : EXT(MV{}, _, SCon{ch, t0}, 1n+g)
  +t => f2 => +hf => +hl => eLit.fin(g, ch, p, t0, r, hs, hd, t, f2, hl)

def eLit.f(+g: Nat, +ch: Char, +p: String, +t0: String, +r: Raw, +hs: {String.starts_with(t0, p) == False{} : Bool}) -> EXT(MV{}, lit(p, t0, r), SCon{ch, t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, lit(p, t0, r), None{}, selF(Maybe<&2, PR>, String.starts_with(t0, p), u => Some{PR{r, String.drop(t0, String.length(p))}}, u => None{}, hs)) : EXT(MV{}, _, SCon{ch, t0}, 1n+g)
  Unit{}

def eLit(+g: Nat, +ch: Char, +p: String, +t0: String, +r: Raw, hd: @g2: Nat -> @X: String -> {pv(1n+g2, MV{}, SCon{ch, X}) == lit(p, X, r) : Maybe<&2, PR>}) -> EXT(MV{}, lit(p, t0, r), SCon{ch, t0}, 1n+g):
  bcase(EXT(MV{}, lit(p, t0, r), SCon{ch, t0}, 1n+g), String.starts_with(t0, p),
    +hs => eLit.t(g, ch, p, t0, r, hs, hd),
    +hs => eLit.f(g, ch, p, t0, r, hs))

def eStr.fin(+g: Nat, +t0: String, +a: String, +u: String, +e: {String.append(a, SCon{'"', u}) == t0 : String}, +h: {ABNF.check(BK, CHARS, a) == True{} : Bool}, +t: String, f2: Nat, +hl: {le(1n+g, f2) == True{} : Bool})
  -> {pv(f2, MV{}, String.append(SCon{'"', t0}, t)) == Some{PR{RStr{a}, String.append(u, t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MV{}, String.append(SCon{'"', t0}, t)) == Some{PR{RStr{a}, String.append(u, t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.trans(String, String.append(a, SCon{'"', String.append(u, t)}), String.append(String.append(a, SCon{'"', u}), t), String.append(t0, t), Equal.sym(String, String.append(String.append(a, SCon{'"', u}), t), String.append(a, String.append(SCon{'"', u}, t)), app3(a, SCon{'"', u}, t)), Equal.cong(String, String, zz => String.append(zz, t), String.append(a, SCon{'"', u}), t0, e)) : {strv(str_scan(_, SN{})) == Some{PR{RStr{a}, String.append(u, t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, SP>, str_scan(String.append(a, SCon{'"', String.append(u, t)}), SN{}), Some{SP{a, String.append(u, t)}}, strC(a, String.append(u, t), h)) : {strv(_) == Some{PR{RStr{a}, String.append(u, t)}} : Maybe<&2, PR>}
      {==}

def eStr(+g: Nat, +t0: String, m: Maybe<&2, SP>, ns: SNS(m, t0, CHARS)) -> EXT(MV{}, strv(m), SCon{'"', t0}, 1n+g):
  match m:
    case None{}:
      Unit{}
    case Some{q}:
      match q:
        case SP{+a, +u}:
          (e, +h) = ns
          +t => f2 => +hf => +hl => eStr.fin(g, t0, a, u, e, h, t, f2, hl)

def eArr.c.fin(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq(']', x) == True{} : Bool}, +t: String, f2: Nat, +hl: {le(1n+g, f2) == True{} : Bool})
  -> {pv(f2, MV{}, String.append(SCon{'[', t0}, t)) == Some{PR{RArr{[]}, String.append(w, t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MV{}, String.append(SCon{'[', t0}, t)) == Some{PR{RArr{[]}, String.append(w, t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(String, skip_ws(String.append(t0, t)), SCon{x, String.append(w, t)}, SKA(t0, t, x, w, eu)) : {brk(']', _, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, w), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p)))))) == Some{PR{RArr{[]}, String.append(w, t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, brk(']', SCon{x, String.append(w, t)}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, w), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p)))))), Some{PR{RArr{[]}, String.append(w, t)}}, selT(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, String.append(w, t)}}, z => Maybe.bind(&2, PR, PR, pv(g2, MV{}, SCon{x, String.append(w, t)}), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), h)) : {_ == Some{PR{RArr{[]}, String.append(w, t)}} : Maybe<&2, PR>}
      {==}

def eArr.c(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq(']', x) == True{} : Bool}) -> EXT(MV{}, brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{'[', t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), Some{PR{RArr{[]}, w}}, selT(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => Maybe.bind(&2, PR, PR, pv(g, MV{}, SCon{x, w}), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), h)) : EXT(MV{}, _, SCon{'[', t0}, 1n+g)
  +t => f2 => +hf => +hl => eArr.c.fin(g, t0, x, w, eu, h, t, f2, hl)

def eArr.fin(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq(']', x) == False{} : Bool}, +p1: PR, E1: @t: String -> @f2: Nat -> {fol(String.append(prt(p1), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MV{}, String.append(SCon{x, w}, t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>},
  +p2: PR, +e2: {pv(g, MA{}, skip_ws(prt(p1))) == Some{p2} : Maybe<&2, PR>}, E2: @t: String -> @f2: Nat -> {fol(String.append(prt(p2), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MA{}, String.append(skip_ws(prt(p1)), t)) == Some{PR{prr(p2), String.append(prt(p2), t)}} : Maybe<&2, PR>}, +t: String, f2: Nat, +hf: {fol(String.append(prt(p2), t)) == True{} : Bool}, +hl: {le(1n+g, f2) == True{} : Bool})
  -> {pv(f2, MV{}, String.append(SCon{'[', t0}, t)) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MV{}, String.append(SCon{'[', t0}, t)) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(String, skip_ws(String.append(t0, t)), SCon{x, String.append(w, t)}, SKA(t0, t, x, w, eu)) : {brk(']', _, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, w), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p)))))) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, brk(']', SCon{x, String.append(w, t)}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, w), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(g2, MV{}, SCon{x, String.append(w, t)}), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), selF(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, String.append(w, t)}}, z => Maybe.bind(&2, PR, PR, pv(g2, MV{}, SCon{x, String.append(w, t)}), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), h)) : {_ == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, pv(g2, MV{}, SCon{x, String.append(w, t)}), Some{PR{prr(p1), String.append(prt(p1), t)}}, E1(t, g2, folMA(g, prt(p1), t, p2, e2), hl)) : {Maybe.bind(&2, PR, PR, _, +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, skip_ws(String.append(prt(p1), t)), String.append(skip_ws(prt(p1)), t), skipApp(prt(p1), t, maNE(g, skip_ws(prt(p1)), p2, e2))) : {acons(prr(p1), pv(g2, MA{}, _)) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, pv(g2, MA{}, String.append(skip_ws(prt(p1)), t)), Some{PR{prr(p2), String.append(prt(p2), t)}}, E2(t, g2, hf, hl)) : {acons(prr(p1), _) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      {==}

def eArr.o2(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq(']', x) == False{} : Bool}, +p1: PR, E1: @t: String -> @f2: Nat -> {fol(String.append(prt(p1), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MV{}, String.append(SCon{x, w}, t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>},
  r2: Maybe<&2, PR>, +e2: {pv(g, MA{}, skip_ws(prt(p1))) == r2 : Maybe<&2, PR>}, E2: EXT(MA{}, r2, skip_ws(prt(p1)), g)) -> EXT(MV{}, acons(prr(p1), r2), SCon{'[', t0}, 1n+g):
  match r2:
    case None{}:
      Unit{}
    case Some{+p2}:
      +t => f2 => +hf => +hl => eArr.fin(g, t0, x, w, eu, h, p1, E1, p2, e2, E2, t, f2, hf, hl)

def eArr.o1(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq(']', x) == False{} : Bool}, r1: Maybe<&2, PR>, E1: EXT(MV{}, r1, SCon{x, w}, g), xA: @w: String -> EXT(MA{}, pv(g, MA{}, w), w, g))
  -> EXT(MV{}, Maybe.bind(&2, PR, PR, r1, +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), SCon{'[', t0}, 1n+g):
  match r1:
    case None{}:
      Unit{}
    case Some{+p1}:
      eArr.o2(g, t0, x, w, eu, h, p1, E1, pv(g, MA{}, skip_ws(prt(p1))), {==}, xA(skip_ws(prt(p1))))

def eArr.o(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq(']', x) == False{} : Bool}, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xA: @w: String -> EXT(MA{}, pv(g, MA{}, w), w, g)) -> EXT(MV{}, brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{'[', t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(g, MV{}, SCon{x, w}), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), selF(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => Maybe.bind(&2, PR, PR, pv(g, MV{}, SCon{x, w}), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), h)) : EXT(MV{}, _, SCon{'[', t0}, 1n+g)
  eArr.o1(g, t0, x, w, eu, h, pv(g, MV{}, SCon{x, w}), xV(SCon{x, w}), xA)

def eArr(+g: Nat, +t0: String, u0: String, +eu: {skip_ws(t0) == u0 : String}, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xA: @w: String -> EXT(MA{}, pv(g, MA{}, w), w, g)) -> EXT(MV{}, brk(']', u0, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{'[', t0}, 1n+g):
  match u0:
    case SNil{}:
      %Equal.sym(Maybe<&2, PR>, pv(g, MV{}, SNil{}), None{}, pvNil(g)) : EXT(MV{}, Maybe.bind(&2, PR, PR, _, +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), SCon{'[', t0}, 1n+g)
      Unit{}
    case SCon{+x, +w}:
      bcase(EXT(MV{}, brk(']', SCon{x, w}, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), SCon{'[', t0}, 1n+g), Char.is_eq(']', x), +h => eArr.c(g, t0, x, w, eu, h), +h => eArr.o(g, t0, x, w, eu, h, xV, xA))

def eObj.c.fin(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq('}', x) == True{} : Bool}, +t: String, f2: Nat, +hl: {le(1n+g, f2) == True{} : Bool})
  -> {pv(f2, MV{}, String.append(SCon{'{', t0}, t)) == Some{PR{RObj{[]}, String.append(w, t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MV{}, String.append(SCon{'{', t0}, t)) == Some{PR{RObj{[]}, String.append(w, t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(String, skip_ws(String.append(t0, t)), SCon{x, String.append(w, t)}, SKA(t0, t, x, w, eu)) : {brk('}', _, w => Some{PR{RObj{[]}, w}}, w => pv(g2, MM{}, w)) == Some{PR{RObj{[]}, String.append(w, t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, brk('}', SCon{x, String.append(w, t)}, w => Some{PR{RObj{[]}, w}}, w => pv(g2, MM{}, w)), Some{PR{RObj{[]}, String.append(w, t)}}, selT(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, String.append(w, t)}}, z => pv(g2, MM{}, SCon{x, String.append(w, t)}), h)) : {_ == Some{PR{RObj{[]}, String.append(w, t)}} : Maybe<&2, PR>}
      {==}

def eObj.c(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq('}', x) == True{} : Bool}) -> EXT(MV{}, brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{'{', t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), Some{PR{RObj{[]}, w}}, selT(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => pv(g, MM{}, SCon{x, w}), h)) : EXT(MV{}, _, SCon{'{', t0}, 1n+g)
  +t => f2 => +hf => +hl => eObj.c.fin(g, t0, x, w, eu, h, t, f2, hl)

def eObj.fin(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq('}', x) == False{} : Bool}, +p1: PR, E1: @t: String -> @f2: Nat -> {fol(String.append(prt(p1), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MM{}, String.append(SCon{x, w}, t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>},
  +t: String, f2: Nat, +hf: {fol(String.append(prt(p1), t)) == True{} : Bool}, +hl: {le(1n+g, f2) == True{} : Bool}) -> {pv(f2, MV{}, String.append(SCon{'{', t0}, t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MV{}, String.append(SCon{'{', t0}, t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(String, skip_ws(String.append(t0, t)), SCon{x, String.append(w, t)}, SKA(t0, t, x, w, eu)) : {brk('}', _, w => Some{PR{RObj{[]}, w}}, w => pv(g2, MM{}, w)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, brk('}', SCon{x, String.append(w, t)}, w => Some{PR{RObj{[]}, w}}, w => pv(g2, MM{}, w)), pv(g2, MM{}, SCon{x, String.append(w, t)}), selF(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, String.append(w, t)}}, z => pv(g2, MM{}, SCon{x, String.append(w, t)}), h)) : {_ == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}
      E1(t, g2, hf, hl)

def eObj.o1(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq('}', x) == False{} : Bool}, r1: Maybe<&2, PR>, E1: EXT(MM{}, r1, SCon{x, w}, g))
  -> EXT(MV{}, r1, SCon{'{', t0}, 1n+g):
  match r1:
    case None{}:
      Unit{}
    case Some{+p1}:
      +t => f2 => +hf => +hl => eObj.fin(g, t0, x, w, eu, h, p1, E1, t, f2, hf, hl)

def eObj.o(+g: Nat, +t0: String, +x: Char, +w: String, +eu: {skip_ws(t0) == SCon{x, w} : String}, +h: {Char.is_eq('}', x) == False{} : Bool}, xM: @w: String -> EXT(MM{}, pv(g, MM{}, w), w, g)) -> EXT(MV{}, brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{'{', t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), pv(g, MM{}, SCon{x, w}), selF(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => pv(g, MM{}, SCon{x, w}), h)) : EXT(MV{}, _, SCon{'{', t0}, 1n+g)
  eObj.o1(g, t0, x, w, eu, h, pv(g, MM{}, SCon{x, w}), xM(SCon{x, w}))

def eObj(+g: Nat, +t0: String, u0: String, +eu: {skip_ws(t0) == u0 : String}, xM: @w: String -> EXT(MM{}, pv(g, MM{}, w), w, g)) -> EXT(MV{}, brk('}', u0, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{'{', t0}, 1n+g):
  match u0:
    case SNil{}:
      %Equal.sym(Maybe<&2, PR>, pv(g, MM{}, SNil{}), None{}, pvMMNil(g)) : EXT(MV{}, _, SCon{'{', t0}, 1n+g)
      Unit{}
    case SCon{+x, +w}:
      bcase(EXT(MV{}, brk('}', SCon{x, w}, w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), SCon{'{', t0}, 1n+g), Char.is_eq('}', x), +h => eObj.c(g, t0, x, w, eu, h), +h => eObj.o(g, t0, x, w, eu, h, xM))

def eMV.num(+g: Nat, +c: Char, +t0: String, +h0: {isnum0(c) == True{} : Bool}) -> EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t0}), numv(num_scan(SCon{c, t0})), selT(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t0})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t0, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t0, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : EXT(MV{}, _, SCon{c, t0}, 1n+g)
  eNum(g, c, t0, h0, num_scan(SCon{c, t0}), numS(SCon{c, t0}))

def eMV.lit(+g: Nat, +c: Char, +t0: String, +ch: Char, +p: String, +r: Raw, +h: {Char.is_eq(ch, c) == True{} : Bool}, +hd0: {pv(1n+g, MV{}, SCon{ch, t0}) == lit(p, t0, r) : Maybe<&2, PR>}, hd: @g2: Nat -> @X: String -> {pv(1n+g2, MV{}, SCon{ch, X}) == lit(p, X, r) : Maybe<&2, PR>}) -> EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  %char_eq(ch, c, h) : EXT(MV{}, pv(1n+g, MV{}, SCon{_, t0}), SCon{_, t0}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{ch, t0}), lit(p, t0, r), hd0) : EXT(MV{}, _, SCon{ch, t0}, 1n+g)
  eLit(g, ch, p, t0, r, hd)

def eMV.s(+g: Nat, +c: Char, +t0: String, +h: {Char.is_eq('"', c) == True{} : Bool}) -> EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  %char_eq('"', c, h) : EXT(MV{}, pv(1n+g, MV{}, SCon{_, t0}), SCon{_, t0}, 1n+g)
  eStr(g, t0, str_scan(t0, SN{}), strS(t0, SN{}))

def eMV.a(+g: Nat, +c: Char, +t0: String, +h: {Char.is_eq('[', c) == True{} : Bool}, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xA: @w: String -> EXT(MA{}, pv(g, MA{}, w), w, g)) -> EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  %char_eq('[', c, h) : EXT(MV{}, pv(1n+g, MV{}, SCon{_, t0}), SCon{_, t0}, 1n+g)
  eArr(g, t0, skip_ws(t0), {==}, xV, xA)

def eMV.o(+g: Nat, +c: Char, +t0: String, +h: {Char.is_eq('{', c) == True{} : Bool}, xM: @w: String -> EXT(MM{}, pv(g, MM{}, w), w, g)) -> EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  %char_eq('{', c, h) : EXT(MV{}, pv(1n+g, MV{}, SCon{_, t0}), SCon{_, t0}, 1n+g)
  eObj(g, t0, skip_ws(t0), {==}, xM)

def eMV.z(+g: Nat, +c: Char, +t0: String, +h0: {isnum0(c) == False{} : Bool}, +h1: {Char.is_eq('n', c) == False{} : Bool}, +h2: {Char.is_eq('t', c) == False{} : Bool}, +h3: {Char.is_eq('f', c) == False{} : Bool}, +h4: {Char.is_eq('"', c) == False{} : Bool}, +h5: {Char.is_eq('[', c) == False{} : Bool}, +h6: {Char.is_eq('{', c) == False{} : Bool}) -> EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MV{}, SCon{c, t0}), sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t0, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t0, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), selF(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, t0})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t0, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t0, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), h0)) : EXT(MV{}, _, SCon{c, t0}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t0, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t0, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))))), sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t0, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), selF(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", t0, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t0, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), h1)) : EXT(MV{}, _, SCon{c, t0}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t0, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))))), sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), selF(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", t0, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), h2)) : EXT(MV{}, _, SCon{c, t0}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})))), sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), selF(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", t0, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), h3)) : EXT(MV{}, _, SCon{c, t0}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}))), sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), selF(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(t0, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), h4)) : EXT(MV{}, _, SCon{c, t0}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{})), sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), selF(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(t0), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, w), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), h5)) : EXT(MV{}, _, SCon{c, t0}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}), None{}, selF(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(t0), w => Some{PR{RObj{[]}, w}}, w => pv(g, MM{}, w)), u => None{}, h6)) : EXT(MV{}, _, SCon{c, t0}, 1n+g)
  Unit{}

def eMV(+g: Nat, +c: Char, +t0: String, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xA: @w: String -> EXT(MA{}, pv(g, MA{}, w), w, g), xM: @w: String -> EXT(MM{}, pv(g, MM{}, w), w, g)) -> EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  bcase(EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g), isnum0(c), +h0 => eMV.num(g, c, t0, h0), +h0 => bcase(EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g), Char.is_eq('n', c), +h1 => eMV.lit(g, c, t0, 'n', "ull", RNull{}, h1, {==}, g2 => X => {==}), +h1 => bcase(EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g), Char.is_eq('t', c), +h2 => eMV.lit(g, c, t0, 't', "rue", RBool{True{}}, h2, {==}, g2 => X => {==}), +h2 => bcase(EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g), Char.is_eq('f', c), +h3 => eMV.lit(g, c, t0, 'f', "alse", RBool{False{}}, h3, {==}, g2 => X => {==}), +h3 => bcase(EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g), Char.is_eq('"', c), +h4 => eMV.s(g, c, t0, h4), +h4 => bcase(EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g), Char.is_eq('[', c), +h5 => eMV.a(g, c, t0, h5, xV, xA), +h5 => bcase(EXT(MV{}, pv(1n+g, MV{}, SCon{c, t0}), SCon{c, t0}, 1n+g), Char.is_eq('{', c), +h6 => eMV.o(g, c, t0, h6, xM), +h6 => eMV.z(g, c, t0, h0, h1, h2, h3, h4, h5, h6))))))))

def eMA.e.fin(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == True{} : Bool}, +t: String, f2: Nat, +hl: {le(1n+g, f2) == True{} : Bool}) -> {pv(f2, MA{}, String.append(SCon{x, w}, t)) == Some{PR{RArr{[]}, String.append(w, t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MA{}, String.append(SCon{x, w}, t)) == Some{PR{RArr{[]}, String.append(w, t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(Maybe<&2, PR>, pv(1n+g2, MA{}, SCon{x, String.append(w, t)}), Some{PR{RArr{[]}, String.append(w, t)}}, selT(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, String.append(w, t)}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(String.append(w, t))), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), z => None{}), h)) : {_ == Some{PR{RArr{[]}, String.append(w, t)}} : Maybe<&2, PR>}
      {==}

def eMA.e(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == True{} : Bool}) -> EXT(MA{}, pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MA{}, SCon{x, w}), Some{PR{RArr{[]}, w}}, selT(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), h)) : EXT(MA{}, _, SCon{x, w}, 1n+g)
  +t => f2 => +hf => +hl => eMA.e.fin(g, x, w, h, t, f2, hl)

def eMA.n(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == False{} : Bool}) -> EXT(MA{}, pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MA{}, SCon{x, w}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), selF(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), h)) : EXT(MA{}, _, SCon{x, w}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), None{}, selF(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}, h2)) : EXT(MA{}, _, SCon{x, w}, 1n+g)
  Unit{}

def eMA.fin(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, +p1: PR, +e1: {pv(g, MV{}, skip_ws(w)) == Some{p1} : Maybe<&2, PR>}, E1: @t: String -> @f2: Nat -> {fol(String.append(prt(p1), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MV{}, String.append(skip_ws(w), t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>},
  +p2: PR, +e2: {pv(g, MA{}, skip_ws(prt(p1))) == Some{p2} : Maybe<&2, PR>}, E2: @t: String -> @f2: Nat -> {fol(String.append(prt(p2), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MA{}, String.append(skip_ws(prt(p1)), t)) == Some{PR{prr(p2), String.append(prt(p2), t)}} : Maybe<&2, PR>}, +t: String, f2: Nat, +hf: {fol(String.append(prt(p2), t)) == True{} : Bool}, +hl: {le(1n+g, f2) == True{} : Bool})
  -> {pv(f2, MA{}, String.append(SCon{x, w}, t)) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MA{}, String.append(SCon{x, w}, t)) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(Maybe<&2, PR>, pv(1n+g2, MA{}, SCon{x, String.append(w, t)}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(String.append(w, t))), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), z => None{}), selF(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, String.append(w, t)}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(String.append(w, t))), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), z => None{}), h)) : {_ == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(String.append(w, t))), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), z => None{}), Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(String.append(w, t))), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), selT(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(String.append(w, t))), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))), z => None{}, h2)) : {_ == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, skip_ws(String.append(w, t)), String.append(skip_ws(w), t), skipApp(w, t, mvNE(g, skip_ws(w), p1, e1))) : {Maybe.bind(&2, PR, PR, pv(g2, MV{}, _), +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, pv(g2, MV{}, String.append(skip_ws(w), t)), Some{PR{prr(p1), String.append(prt(p1), t)}}, E1(t, g2, folMA(g, prt(p1), t, p2, e2), hl)) : {Maybe.bind(&2, PR, PR, _, +p => acons(prr(p), pv(g2, MA{}, skip_ws(prt(p))))) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, skip_ws(String.append(prt(p1), t)), String.append(skip_ws(prt(p1)), t), skipApp(prt(p1), t, maNE(g, skip_ws(prt(p1)), p2, e2))) : {acons(prr(p1), pv(g2, MA{}, _)) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, pv(g2, MA{}, String.append(skip_ws(prt(p1)), t)), Some{PR{prr(p2), String.append(prt(p2), t)}}, E2(t, g2, hf, hl)) : {acons(prr(p1), _) == Some{PR{acons1(prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      {==}

def eMA.c2(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, +p1: PR, +e1: {pv(g, MV{}, skip_ws(w)) == Some{p1} : Maybe<&2, PR>}, E1: @t: String -> @f2: Nat -> {fol(String.append(prt(p1), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MV{}, String.append(skip_ws(w), t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>},
  r2: Maybe<&2, PR>, +e2: {pv(g, MA{}, skip_ws(prt(p1))) == r2 : Maybe<&2, PR>}, E2: EXT(MA{}, r2, skip_ws(prt(p1)), g)) -> EXT(MA{}, acons(prr(p1), r2), SCon{x, w}, 1n+g):
  match r2:
    case None{}:
      Unit{}
    case Some{+p2}:
      +t => f2 => +hf => +hl => eMA.fin(g, x, w, h, h2, p1, e1, E1, p2, e2, E2, t, f2, hf, hl)

def eMA.c1(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, r1: Maybe<&2, PR>, +e1: {pv(g, MV{}, skip_ws(w)) == r1 : Maybe<&2, PR>}, E1: EXT(MV{}, r1, skip_ws(w), g), xA: @w: String -> EXT(MA{}, pv(g, MA{}, w), w, g))
  -> EXT(MA{}, Maybe.bind(&2, PR, PR, r1, +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), SCon{x, w}, 1n+g):
  match r1:
    case None{}:
      Unit{}
    case Some{+p1}:
      eMA.c2(g, x, w, h, h2, p1, e1, E1, pv(g, MA{}, skip_ws(prt(p1))), {==}, xA(skip_ws(prt(p1))))

def eMA.c(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq(']', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xA: @w: String -> EXT(MA{}, pv(g, MA{}, w), w, g)) -> EXT(MA{}, pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MA{}, SCon{x, w}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), selF(Maybe<&2, PR>, Char.is_eq(']', x), z => Some{PR{RArr{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), h)) : EXT(MA{}, _, SCon{x, w}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}), Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), selT(Maybe<&2, PR>, Char.is_eq(',', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => acons(prr(p), pv(g, MA{}, skip_ws(prt(p))))), z => None{}, h2)) : EXT(MA{}, _, SCon{x, w}, 1n+g)
  eMA.c1(g, x, w, h, h2, pv(g, MV{}, skip_ws(w)), {==}, xV(skip_ws(w)), xA)

def eMA(+g: Nat, s: String, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xA: @w: String -> EXT(MA{}, pv(g, MA{}, w), w, g)) -> EXT(MA{}, pv(1n+g, MA{}, s), s, 1n+g):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+x, +w}:
      bcase(EXT(MA{}, pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}, 1n+g), Char.is_eq(']', x), +h => eMA.e(g, x, w, h),
        +h => bcase(EXT(MA{}, pv(1n+g, MA{}, SCon{x, w}), SCon{x, w}, 1n+g), Char.is_eq(',', x), +h2 => eMA.c(g, x, w, h, h2, xV, xA), +h2 => eMA.n(g, x, w, h, h2)))

def eMO.e.fin(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == True{} : Bool}, +t: String, f2: Nat, +hl: {le(1n+g, f2) == True{} : Bool}) -> {pv(f2, MO{}, String.append(SCon{x, w}, t)) == Some{PR{RObj{[]}, String.append(w, t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MO{}, String.append(SCon{x, w}, t)) == Some{PR{RObj{[]}, String.append(w, t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(Maybe<&2, PR>, pv(1n+g2, MO{}, SCon{x, String.append(w, t)}), Some{PR{RObj{[]}, String.append(w, t)}}, selT(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, String.append(w, t)}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g2, MM{}, skip_ws(String.append(w, t))), z => None{}), h)) : {_ == Some{PR{RObj{[]}, String.append(w, t)}} : Maybe<&2, PR>}
      {==}

def eMO.e(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == True{} : Bool}) -> EXT(MO{}, pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MO{}, SCon{x, w}), Some{PR{RObj{[]}, w}}, selT(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), h)) : EXT(MO{}, _, SCon{x, w}, 1n+g)
  +t => f2 => +hf => +hl => eMO.e.fin(g, x, w, h, t, f2, hl)

def eMO.n(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == False{} : Bool}) -> EXT(MO{}, pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MO{}, SCon{x, w}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), selF(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), h)) : EXT(MO{}, _, SCon{x, w}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), None{}, selF(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}, h2)) : EXT(MO{}, _, SCon{x, w}, 1n+g)
  Unit{}

def eMO.fin(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, +p1: PR, +e1: {pv(g, MM{}, skip_ws(w)) == Some{p1} : Maybe<&2, PR>}, E1: @t: String -> @f2: Nat -> {fol(String.append(prt(p1), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MM{}, String.append(skip_ws(w), t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>},
  +t: String, f2: Nat, +hf: {fol(String.append(prt(p1), t)) == True{} : Bool}, +hl: {le(1n+g, f2) == True{} : Bool}) -> {pv(f2, MO{}, String.append(SCon{x, w}, t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MO{}, String.append(SCon{x, w}, t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.sym(Maybe<&2, PR>, pv(1n+g2, MO{}, SCon{x, String.append(w, t)}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g2, MM{}, skip_ws(String.append(w, t))), z => None{}), selF(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, String.append(w, t)}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g2, MM{}, skip_ws(String.append(w, t))), z => None{}), h)) : {_ == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g2, MM{}, skip_ws(String.append(w, t))), z => None{}), pv(g2, MM{}, skip_ws(String.append(w, t))), selT(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g2, MM{}, skip_ws(String.append(w, t))), z => None{}, h2)) : {_ == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, skip_ws(String.append(w, t)), String.append(skip_ws(w), t), skipApp(w, t, mmNE(g, skip_ws(w), p1, e1))) : {pv(g2, MM{}, _) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}
      E1(t, g2, hf, hl)

def eMO.c1(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, r1: Maybe<&2, PR>, +e1: {pv(g, MM{}, skip_ws(w)) == r1 : Maybe<&2, PR>}, E1: EXT(MM{}, r1, skip_ws(w), g))
  -> EXT(MO{}, r1, SCon{x, w}, 1n+g):
  match r1:
    case None{}:
      Unit{}
    case Some{+p1}:
      +t => f2 => +hf => +hl => eMO.fin(g, x, w, h, h2, p1, e1, E1, t, f2, hf, hl)

def eMO.c(+g: Nat, +x: Char, +w: String, +h: {Char.is_eq('}', x) == False{} : Bool}, +h2: {Char.is_eq(',', x) == True{} : Bool}, xM: @w: String -> EXT(MM{}, pv(g, MM{}, w), w, g)) -> EXT(MO{}, pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MO{}, SCon{x, w}), sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), selF(Maybe<&2, PR>, Char.is_eq('}', x), z => Some{PR{RObj{[]}, w}}, z => sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), h)) : EXT(MO{}, _, SCon{x, w}, 1n+g)
  %Equal.sym(Maybe<&2, PR>, sel(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}), pv(g, MM{}, skip_ws(w)), selT(Maybe<&2, PR>, Char.is_eq(',', x), z => pv(g, MM{}, skip_ws(w)), z => None{}, h2)) : EXT(MO{}, _, SCon{x, w}, 1n+g)
  eMO.c1(g, x, w, h, h2, pv(g, MM{}, skip_ws(w)), {==}, xM(skip_ws(w)))

def eMO(+g: Nat, s: String, xM: @w: String -> EXT(MM{}, pv(g, MM{}, w), w, g)) -> EXT(MO{}, pv(1n+g, MO{}, s), s, 1n+g):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+x, +w}:
      bcase(EXT(MO{}, pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}, 1n+g), Char.is_eq('}', x), +h => eMO.e(g, x, w, h),
        +h => bcase(EXT(MO{}, pv(1n+g, MO{}, SCon{x, w}), SCon{x, w}, 1n+g), Char.is_eq(',', x), +h2 => eMO.c(g, x, w, h, h2, xM), +h2 => eMO.n(g, x, w, h, h2)))

def eMM.fin(+g: Nat, +t0: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t0 : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, +x: Char, +w: String, +eu: {skip_ws(spt(q)) == SCon{x, w} : String}, +hx: {Char.is_eq(':', x) == True{} : Bool},
  +p1: PR, +e1: {pv(g, MV{}, skip_ws(w)) == Some{p1} : Maybe<&2, PR>}, E1: @t: String -> @f2: Nat -> {fol(String.append(prt(p1), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MV{}, String.append(skip_ws(w), t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}, +p2: PR, +e2: {pv(g, MO{}, skip_ws(prt(p1))) == Some{p2} : Maybe<&2, PR>}, E2: @t: String -> @f2: Nat -> {fol(String.append(prt(p2), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MO{}, String.append(skip_ws(prt(p1)), t)) == Some{PR{prr(p2), String.append(prt(p2), t)}} : Maybe<&2, PR>},
  +t: String, f2: Nat, +hf: {fol(String.append(prt(p2), t)) == True{} : Bool}, +hl: {le(1n+g, f2) == True{} : Bool}) -> {pv(f2, MM{}, String.append(SCon{'"', t0}, t)) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}:
  match f2:
    case 0n:
      Empty.absurd({pv(0n, MM{}, String.append(SCon{'"', t0}, t)) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}, false_ne_true(hl))
    case 1n+ +g2:
      %Equal.trans(String, String.append(spa(q), SCon{'"', String.append(spt(q), t)}), String.append(String.append(spa(q), SCon{'"', spt(q)}), t), String.append(t0, t), Equal.sym(String, String.append(String.append(spa(q), SCon{'"', spt(q)}), t), String.append(spa(q), String.append(SCon{'"', spt(q)}, t)), app3(spa(q), SCon{'"', spt(q)}, t)), Equal.cong(String, String, zz => String.append(zz, t), String.append(spa(q), SCon{'"', spt(q)}), t0, eq1)) : {Maybe.bind(&2, SP, PR, str_scan(_, SN{}), +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g2, MO{}, skip_ws(prt(p))))))) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, SP>, str_scan(String.append(spa(q), SCon{'"', String.append(spt(q), t)}), SN{}), Some{SP{spa(q), String.append(spt(q), t)}}, strC(spa(q), String.append(spt(q), t), hk)) : {Maybe.bind(&2, SP, PR, _, +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g2, MO{}, skip_ws(prt(p))))))) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, skip_ws(String.append(spt(q), t)), SCon{x, String.append(w, t)}, SKA(spt(q), t, x, w, eu)) : {colon(_, w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g2, MO{}, skip_ws(prt(p)))))) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, colon(SCon{x, String.append(w, t)}, w => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g2, MO{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(String.append(w, t))), +p => ocons(spa(q), prr(p), pv(g2, MO{}, skip_ws(prt(p))))), selT(Maybe<&2, PR>, Char.is_eq(':', x), z => Maybe.bind(&2, PR, PR, pv(g2, MV{}, skip_ws(String.append(w, t))), +p => ocons(spa(q), prr(p), pv(g2, MO{}, skip_ws(prt(p))))), z => None{}, hx)) : {_ == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, skip_ws(String.append(w, t)), String.append(skip_ws(w), t), skipApp(w, t, mvNE(g, skip_ws(w), p1, e1))) : {Maybe.bind(&2, PR, PR, pv(g2, MV{}, _), +p => ocons(spa(q), prr(p), pv(g2, MO{}, skip_ws(prt(p))))) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, pv(g2, MV{}, String.append(skip_ws(w), t)), Some{PR{prr(p1), String.append(prt(p1), t)}}, E1(t, g2, folMO(g, prt(p1), t, p2, e2), hl)) : {Maybe.bind(&2, PR, PR, _, +p => ocons(spa(q), prr(p), pv(g2, MO{}, skip_ws(prt(p))))) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(String, skip_ws(String.append(prt(p1), t)), String.append(skip_ws(prt(p1)), t), skipApp(prt(p1), t, moNE(g, skip_ws(prt(p1)), p2, e2))) : {ocons(spa(q), prr(p1), pv(g2, MO{}, _)) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      %Equal.sym(Maybe<&2, PR>, pv(g2, MO{}, String.append(skip_ws(prt(p1)), t)), Some{PR{prr(p2), String.append(prt(p2), t)}}, E2(t, g2, hf, hl)) : {ocons(spa(q), prr(p1), _) == Some{PR{ocons1(spa(q), prr(p1), prr(p2)), String.append(prt(p2), t)}} : Maybe<&2, PR>}
      {==}

def eMM.v2(+g: Nat, +t0: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t0 : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, +x: Char, +w: String, +eu: {skip_ws(spt(q)) == SCon{x, w} : String}, +hx: {Char.is_eq(':', x) == True{} : Bool},
  +p1: PR, +e1: {pv(g, MV{}, skip_ws(w)) == Some{p1} : Maybe<&2, PR>}, E1: @t: String -> @f2: Nat -> {fol(String.append(prt(p1), t)) == True{} : Bool} -> {le(g, f2) == True{} : Bool} -> {pv(f2, MV{}, String.append(skip_ws(w), t)) == Some{PR{prr(p1), String.append(prt(p1), t)}} : Maybe<&2, PR>}, r2: Maybe<&2, PR>, +e2: {pv(g, MO{}, skip_ws(prt(p1))) == r2 : Maybe<&2, PR>}, E2: EXT(MO{}, r2, skip_ws(prt(p1)), g))
  -> EXT(MM{}, ocons(spa(q), prr(p1), r2), SCon{'"', t0}, 1n+g):
  match r2:
    case None{}:
      Unit{}
    case Some{+p2}:
      +t => f2 => +hf => +hl => eMM.fin(g, t0, q, eq1, hk, x, w, eu, hx, p1, e1, E1, p2, e2, E2, t, f2, hf, hl)

def eMM.v(+g: Nat, +t0: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t0 : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, +x: Char, +w: String, +eu: {skip_ws(spt(q)) == SCon{x, w} : String}, +hx: {Char.is_eq(':', x) == True{} : Bool},
  r1: Maybe<&2, PR>, +e1: {pv(g, MV{}, skip_ws(w)) == r1 : Maybe<&2, PR>}, E1: EXT(MV{}, r1, skip_ws(w), g), xO: @w: String -> EXT(MO{}, pv(g, MO{}, w), w, g)) -> EXT(MM{}, Maybe.bind(&2, PR, PR, r1, +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))), SCon{'"', t0}, 1n+g):
  match r1:
    case None{}:
      Unit{}
    case Some{+p1}:
      eMM.v2(g, t0, q, eq1, hk, x, w, eu, hx, p1, e1, E1, pv(g, MO{}, skip_ws(prt(p1))), {==}, xO(skip_ws(prt(p1))))

def eMM.c.t(+g: Nat, +t0: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t0 : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, +x: Char, +w: String, +eu: {skip_ws(spt(q)) == SCon{x, w} : String}, +h: {Char.is_eq(':', x) == True{} : Bool}, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xO: @w: String -> EXT(MO{}, pv(g, MO{}, w), w, g))
  -> EXT(MM{}, colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), SCon{'"', t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))), selT(Maybe<&2, PR>, Char.is_eq(':', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))), z => None{}, h)) : EXT(MM{}, _, SCon{'"', t0}, 1n+g)
  eMM.v(g, t0, q, eq1, hk, x, w, eu, h, pv(g, MV{}, skip_ws(w)), {==}, xV(skip_ws(w)), xO)

def eMM.c.f(+g: Nat, +t0: String, +q: SP, +x: Char, +w: String, +h: {Char.is_eq(':', x) == False{} : Bool}) -> EXT(MM{}, colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), SCon{'"', t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), None{}, selF(Maybe<&2, PR>, Char.is_eq(':', x), z => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))), z => None{}, h)) : EXT(MM{}, _, SCon{'"', t0}, 1n+g)
  Unit{}

def eMM.c(+g: Nat, +t0: String, +q: SP, +eq1: {String.append(spa(q), SCon{'"', spt(q)}) == t0 : String}, +hk: {ABNF.check(BK, CHARS, spa(q)) == True{} : Bool}, u: String, +eu: {skip_ws(spt(q)) == u : String}, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xO: @w: String -> EXT(MO{}, pv(g, MO{}, w), w, g))
  -> EXT(MM{}, colon(u, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), SCon{'"', t0}, 1n+g):
  match u:
    case SNil{}:
      Unit{}
    case SCon{+x, +w}:
      bcase(EXT(MM{}, colon(SCon{x, w}, w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p)))))), SCon{'"', t0}, 1n+g), Char.is_eq(':', x), +h => eMM.c.t(g, t0, q, eq1, hk, x, w, eu, h, xV, xO), +h => eMM.c.f(g, t0, q, x, w, h))

def eMM.q(+g: Nat, +t0: String, m1: Maybe<&2, SP>, sns: SNS(m1, t0, CHARS), xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xO: @w: String -> EXT(MO{}, pv(g, MO{}, w), w, g)) -> EXT(MM{}, Maybe.bind(&2, SP, PR, m1, +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))))), SCon{'"', t0}, 1n+g):
  match m1:
    case None{}:
      Unit{}
    case Some{+q}:
      (eq1, +hk) = sns
      eMM.c(g, t0, q, eq1, hk, skip_ws(spt(q)), {==}, xV, xO)

def eMM.t(+g: Nat, +c: Char, +t0: String, +h: {Char.is_eq('"', c) == True{} : Bool}, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xO: @w: String -> EXT(MO{}, pv(g, MO{}, w), w, g)) -> EXT(MM{}, pv(1n+g, MM{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  %char_eq('"', c, h) : EXT(MM{}, pv(1n+g, MM{}, SCon{_, t0}), SCon{_, t0}, 1n+g)
  eMM.q(g, t0, str_scan(t0, SN{}), strS(t0, SN{}), xV, xO)

def eMM.f(+g: Nat, +c: Char, +t0: String, +h: {Char.is_eq('"', c) == False{} : Bool}) -> EXT(MM{}, pv(1n+g, MM{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  %Equal.sym(Maybe<&2, PR>, pv(1n+g, MM{}, SCon{c, t0}), None{}, selF(Maybe<&2, PR>, Char.is_eq('"', c), u => Maybe.bind(&2, SP, PR, str_scan(t0, SN{}), +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(g, MO{}, skip_ws(prt(p))))))), u => None{}, h)) : EXT(MM{}, _, SCon{c, t0}, 1n+g)
  Unit{}

def eMM(+g: Nat, +c: Char, +t0: String, xV: @w: String -> EXT(MV{}, pv(g, MV{}, w), w, g), xO: @w: String -> EXT(MO{}, pv(g, MO{}, w), w, g)) -> EXT(MM{}, pv(1n+g, MM{}, SCon{c, t0}), SCon{c, t0}, 1n+g):
  bcase(EXT(MM{}, pv(1n+g, MM{}, SCon{c, t0}), SCon{c, t0}, 1n+g), Char.is_eq('"', c), +h => eMM.t(g, c, t0, h, xV, xO), +h => eMM.f(g, c, t0, h))

# Parsing more text after what was parsed changes nothing, given enough fuel.
def Ext(f: Nat, m: Md, s: String) -> EXT(m, pv(f, m, s), s, f):
  match f:
    case 0n:
      Unit{}
    case 1n+ +g:
      match m:
        case MV{}:
          match s:
            case SNil{}:
              Unit{}
            case SCon{+c, +t0}:
              eMV(g, c, t0, w => Ext(g, MV{}, w), w => Ext(g, MA{}, w), w => Ext(g, MM{}, w))
        case MA{}:
          eMA(g, s, w => Ext(g, MV{}, w), w => Ext(g, MA{}, w))
        case MM{}:
          match s:
            case SNil{}:
              Unit{}
            case SCon{+c, +t0}:
              eMM(g, c, t0, w => Ext(g, MV{}, w), w => Ext(g, MO{}, w))
        case MO{}:
          eMO(g, s, w => Ext(g, MM{}, w))

# Parser completeness
# ===================

def lePre(a: String, -b: String) -> {le(String.length(a), String.length(String.append(a, b))) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, r}:
      lePre(r, b)

def leSuf(a: String, +b: String) -> {le(String.length(b), String.length(String.append(a, b))) == True{} : Bool}:
  match a:
    case SNil{}:
      le_refl(String.length(b))
    case SCon{c, +r}:
      le_succ_r(String.length(b), String.length(String.append(r, b)), leSuf(r, b))

def leSkip(+x: String) -> {le(String.length(skip_ws(x)), String.length(x)) == True{} : Bool}:
  %Equal.sym(String, x, String.append(wsp(x), skip_ws(x)), Equal.sym(String, String.append(wsp(x), skip_ws(x)), x, WI(x))) : {le(String.length(skip_ws(x)), String.length(_)) == True{} : Bool}
  leSuf(wsp(x), skip_ws(x))

# skip_ws(A) is no longer than any text containing A.
def leOcc(+A: String, -B: String, +P: String, +Q: String, +e: {String.append(P, String.append(A, Q)) == B : String}) -> {le(String.length(skip_ws(A)), String.length(B)) == True{} : Bool}:
  %Equal.sym(String, B, String.append(P, String.append(A, Q)), Equal.sym(String, String.append(P, String.append(A, Q)), B, e)) : {le(String.length(skip_ws(A)), String.length(_)) == True{} : Bool}
  le_trans(String.length(skip_ws(A)), String.length(A), String.length(String.append(P, String.append(A, Q))), leSkip(A),
    le_trans(String.length(A), String.length(String.append(A, Q)), String.length(String.append(P, String.append(A, Q))), lePre(A, Q), leSuf(P, String.append(A, Q))))

def pvcSome(+m: Md, +S: String, res: Maybe<&2, PR>, E: EXT(m, res, S, 1n+String.length(S)), -r: Raw, -u: String, +eS: {res == Some{PR{r, u}} : Maybe<&2, PR>},
  +t: String, +f2: Nat, +hf: {fol(String.append(u, t)) == True{} : Bool}, +hl: {le(1n+String.length(S), f2) == True{} : Bool}) -> {pv(f2, m, String.append(S, t)) == Some{PR{r, String.append(u, t)}} : Maybe<&2, PR>}:
  match res:
    case None{}:
      Empty.absurd({pv(f2, m, String.append(S, t)) == Some{PR{r, String.append(u, t)}} : Maybe<&2, PR>}, none_ne_some(&2, PR, PR{r, u}, eS))
    case Some{+p}:
      %Equal.cong(PR, Raw, prr, p, PR{r, u}, some_inj(&2, PR, p, PR{r, u}, eS)) : {pv(f2, m, String.append(S, t)) == Some{PR{_, String.append(u, t)}} : Maybe<&2, PR>}
      %Equal.cong(PR, String, prt, p, PR{r, u}, some_inj(&2, PR, p, PR{r, u}, eS)) : {pv(f2, m, String.append(S, t)) == Some{PR{prr(p), String.append(_, t)}} : Maybe<&2, PR>}
      E(t, f2, Equal.trans(Bool, fol(String.append(prt(p), t)), fol(String.append(u, t)), True{}, Equal.cong(String, Bool, z => fol(String.append(z, t)), prt(p), u, Equal.cong(PR, String, prt, p, PR{r, u}, some_inj(&2, PR, p, PR{r, u}, eS))), hf), hl)

# A successful parse of S, read again with more text after it.
def extApply(+m: Md, +S: String, -r: Raw, -u: String, +eS: {pvc(m, S) == Some{PR{r, u}} : Maybe<&2, PR>}, +t: String, +f2: Nat, +hf: {fol(String.append(u, t)) == True{} : Bool}, +hl: {le(1n+String.length(S), f2) == True{} : Bool})
  -> {pv(f2, m, String.append(S, t)) == Some{PR{r, String.append(u, t)}} : Maybe<&2, PR>}:
  pvcSome(m, S, pv(1n+String.length(S), m, S), Ext(1n+String.length(S), m, S), r, u, eS, t, f2, hf, hl)

def folWs(u: String, +hw: {wsall(u) == True{} : Bool}) -> {fol(u) == True{} : Bool}:
  match u:
    case SNil{}:
      {==}
    case SCon{+c, r}:
      or_l(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), and_l(isws(c), wsall(r), hw))

def extNil(+m: Md, +S: String, -r: Raw, +u: String, +eS: {pvc(m, S) == Some{PR{r, u}} : Maybe<&2, PR>}, +f2: Nat, +hw: {wsall(u) == True{} : Bool}, +hl: {le(1n+String.length(S), f2) == True{} : Bool})
  -> {pv(f2, m, S) == Some{PR{r, u}} : Maybe<&2, PR>}:
  %Equal.sym(String, S, String.append(S, SNil{}), Equal.sym(String, String.append(S, SNil{}), S, append_nil(S))) : {pv(f2, m, _) == Some{PR{r, u}} : Maybe<&2, PR>}
  %Equal.sym(String, u, String.append(u, SNil{}), Equal.sym(String, String.append(u, SNil{}), u, append_nil(u))) : {pv(f2, m, String.append(S, SNil{})) == Some{PR{r, _}} : Maybe<&2, PR>}
  extApply(m, S, r, u, eS, SNil{}, f2, Equal.trans(Bool, fol(String.append(u, SNil{})), fol(u), True{}, Equal.cong(String, Bool, z => fol(z), String.append(u, SNil{}), u, append_nil(u)), folWs(u, hw)), hl)

def folWsPre(u: String, -X: String, +hw: {wsall(u) == True{} : Bool}, +hX: {fol(X) == True{} : Bool}) -> {fol(String.append(u, X)) == True{} : Bool}:
  match u:
    case SNil{}:
      hX
    case SCon{+c, r}:
      or_l(isws(c), Bool.or(Char.is_eq(',', c), Bool.or(Char.is_eq(']', c), Bool.or(Char.is_eq('}', c), False{}))), and_l(isws(c), wsall(r), hw))

def pvBr(f: Nat, -S: String) -> {pv(f, MV{}, SCon{']', S}) == None{} : Maybe<&2, PR>}:
  match f:
    case 0n:
      {==}
    case 1n+ +g:
      {==}

def pvBrO(f: Nat, -S: String) -> {pv(f, MM{}, SCon{'}', S}) == None{} : Maybe<&2, PR>}:
  match f:
    case 0n:
      {==}
    case 1n+ +g:
      {==}

type CMd is Data:
  CV{}
  CA{}
  CMM{}

def CMD(c: CMd) -> Md:
  match c:
    case CV{}:
      MV{}
    case CA{}:
      MA{}
    case CMM{}:
      MM{}

# CH(c, d, m, s): s matches, at depth d, a value (CV), what follows an array's
# first element with m more elements (CA), or a member with m more (CMM).
def CH(c: CMd, d: Nat, m: Nat, s: String) -> Type:
  match c:
    case CV{}:
      {ABNF.check(LB(d), ABNF.ref("value"), s) == True{} : Bool}
    case CA{}:
      {ABNF.check(LB(d), ABNF.seq([ABNF.rep.exactly(m, ITEM), ABNF.ref("end-array")]), s) == True{} : Bool}
    case CMM{}:
      {ABNF.check(LB(d), ABNF.seq([ABNF.ref("member"), ABNF.rep.exactly(m, MITEM), ABNF.ref("end-object")]), s) == True{} : Bool}

# CR(c, s): the parser reads s, leaving only whitespace.
def CR(c: CMd, s: String) -> Type:
  &r: Raw -> &u: String -> {pvc(CMD(c), skip_ws(s)) == Some{PR{r, u}} : Maybe<&2, PR>} & {wsall(u) == True{} : Bool}

def starE.go(-C: Type, -k: ABNF.Book, -r: ABNF.Rule, -s: String, p: &m: Nat -> {ABNF.check(k, ABNF.rep.exactly(m, r), s) == True{} : Bool}, f: @m: Nat -> {ABNF.check(k, ABNF.rep.exactly(m, r), s) == True{} : Bool} -> C) -> C:
  (m, h) = p
  f(m, h)

def starE(-C: Type, +k: ABNF.Book, +r: ABNF.Rule, +s: String, +h: {ABNF.check(k, ABNF.rep.any(r), s) == True{} : Bool}, f: @m: Nat -> {ABNF.check(k, ABNF.rep.exactly(m, r), s) == True{} : Bool} -> C) -> C:
  starE.go(C, k, r, s, ABNF.rep.any.elim(k, r, s, h), f)

def tokU0.go(+ch: Char, -b: String, x: String, +ex: {skip_ws(b) == x : String}, +h: {tokb2(ch, x) == True{} : Bool}) -> {skip_ws(b) == SCon{ch, str_tl(x)} : String}:
  match x:
    case SNil{}:
      Empty.absurd({skip_ws(b) == SCon{ch, SNil{}} : String}, false_ne_true(h))
    case SCon{+c, +y}:
      %Equal.sym(Char, ch, c, char_eq(ch, c, and_l(Char.is_eq(ch, c), wsall(y), h))) : {skip_ws(b) == SCon{_, y} : String}
      ex

def tokU0(+ch: Char, +b: String, +h: {tokb(ch, b) == True{} : Bool}) -> {skip_ws(b) == SCon{ch, str_tl(skip_ws(b))} : String}:
  tokU0.go(ch, b, skip_ws(b), {==}, h)

def cvFalse(-s: String, +e: {s == "false" : String}) -> CR(CV{}, s):
  %Equal.sym(String, s, "false", e) : CR(CV{}, _)
  (RBool{False{}}, SNil{}, {==}, {==})

def cvNull(-s: String, +e: {s == "null" : String}) -> CR(CV{}, s):
  %Equal.sym(String, s, "null", e) : CR(CV{}, _)
  (RNull{}, SNil{}, {==}, {==})

def cvTrue(-s: String, +e: {s == "true" : String}) -> CR(CV{}, s):
  %Equal.sym(String, s, "true", e) : CR(CV{}, _)
  (RBool{True{}}, SNil{}, {==}, {==})

def cvNum.eq(+c: Char, +s1: String, +hc: {isnum0(c) == True{} : Bool}, +en: {num_scan(SCon{c, s1}) == Some{SP{SCon{c, s1}, SNil{}}} : Maybe<&2, SP>}) -> {pvc(MV{}, skip_ws(SCon{c, s1})) == Some{PR{RNum{SCon{c, s1}}, SNil{}}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(SCon{c, s1}), SCon{c, s1}, skipF(c, s1, bcase({isws(c) == False{} : Bool}, isws(c), +k => Empty.absurd({isws(c) == False{} : Bool}, contra(isnum0(c), hc, ws_num0(c, k))), +k => k))) : {pv(1n+String.length(_), MV{}, _) == Some{PR{RNum{SCon{c, s1}}, SNil{}}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, pv(1n+String.length(SCon{c, s1}), MV{}, SCon{c, s1}), numv(num_scan(SCon{c, s1})), selT(Maybe<&2, PR>, isnum0(c), u => numv(num_scan(SCon{c, s1})), u => sel(Maybe<&2, PR>, Char.is_eq('n', c), u => lit("ull", s1, RNull{}), u => sel(Maybe<&2, PR>, Char.is_eq('t', c), u => lit("rue", s1, RBool{True{}}), u => sel(Maybe<&2, PR>, Char.is_eq('f', c), u => lit("alse", s1, RBool{False{}}), u => sel(Maybe<&2, PR>, Char.is_eq('"', c), u => strv(str_scan(s1, SN{})), u => sel(Maybe<&2, PR>, Char.is_eq('[', c), u => brk(']', skip_ws(s1), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(s1), MV{}, w), +p => acons(prr(p), pv(1n+String.length(s1), MA{}, skip_ws(prt(p)))))), u => sel(Maybe<&2, PR>, Char.is_eq('{', c), u => brk('}', skip_ws(s1), w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(s1), MM{}, w)), u => None{})))))), hc)) : {_ == Some{PR{RNum{SCon{c, s1}}, SNil{}}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, SP>, num_scan(SCon{c, s1}), Some{SP{SCon{c, s1}, SNil{}}}, en) : {numv(_) == Some{PR{RNum{SCon{c, s1}}, SNil{}}} : Maybe<&2, PR>}
  {==}

def cvNum.go(+c: Char, +s1: String, +hc: {isnum0(c) == True{} : Bool}, +en: {num_scan(SCon{c, s1}) == Some{SP{SCon{c, s1}, SNil{}}} : Maybe<&2, SP>}) -> CR(CV{}, SCon{c, s1}):
  (RNum{SCon{c, s1}}, SNil{}, cvNum.eq(c, s1, hc, en), {==})

def cvNum.nf(+c: Char, +s1: String, +hc: {isnum0(c) == False{} : Bool}) -> {num_scan(SCon{c, s1}) == None{} : Maybe<&2, SP>}:
  %Equal.sym(Maybe<&2, SP>, num_scan(SCon{c, s1}), nint(SCon{c, s1}), selF(Maybe<&2, SP>, Char.is_eq('-', c), u => prepM(c, nint(s1)), u => nint(SCon{c, s1}), or_false_l(Char.is_eq('-', c), Bool.or(Char.is_eq('0', c), is19(c)), hc))) : {_ == None{} : Maybe<&2, SP>}
  %Equal.sym(Maybe<&2, SP>, nint(SCon{c, s1}), sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(s1))), u => None{}), selF(Maybe<&2, SP>, Char.is_eq('0', c), u => prepM(c, nfrac(s1)), u => sel(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(s1))), u => None{}), or_false_l(Char.is_eq('0', c), is19(c), or_false_r(Char.is_eq('-', c), Bool.or(Char.is_eq('0', c), is19(c)), hc)))) : {_ == None{} : Maybe<&2, SP>}
  selF(Maybe<&2, SP>, is19(c), u => prepM(c, nint2(digits(s1))), u => None{}, or_false_r(Char.is_eq('0', c), is19(c), or_false_r(Char.is_eq('-', c), Bool.or(Char.is_eq('0', c), is19(c)), hc)))

def cvNum.s(s: String, +en: {num_scan(s) == Some{SP{s, SNil{}}} : Maybe<&2, SP>}) -> CR(CV{}, s):
  match s:
    case SNil{}:
      Empty.absurd(CR(CV{}, SNil{}), none_ne_some(&2, SP, SP{SNil{}, SNil{}}, en))
    case SCon{+c, +s1}:
      bcase(CR(CV{}, SCon{c, s1}), isnum0(c), +k => cvNum.go(c, s1, k, en),
        +k => Empty.absurd(CR(CV{}, SCon{c, s1}), none_ne_some(&2, SP, SP{SCon{c, s1}, SNil{}}, Equal.trans(Maybe<&2, SP>, None{}, num_scan(SCon{c, s1}), Some{SP{SCon{c, s1}, SNil{}}}, Equal.sym(Maybe<&2, SP>, num_scan(SCon{c, s1}), None{}, cvNum.nf(c, s1, k)), en))))

def cvNum(+s: String, +h: {ABNF.check(BK, B_number, s) == True{} : Bool}) -> CR(CV{}, s):
  cvNum.s(s, Equal.trans(Maybe<&2, SP>, num_scan(s), num_scan(String.append(s, SNil{})), Some{SP{s, SNil{}}}, Equal.cong(String, Maybe<&2, SP>, z => num_scan(z), s, String.append(s, SNil{}), Equal.sym(String, String.append(s, SNil{}), s, append_nil(s))), numC(s, SNil{}, h, {==})))

def cvStr.eq(+x: String, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}) -> {pvc(MV{}, skip_ws(SCon{'"', String.append(x, SCon{'"', SNil{}})})) == Some{PR{RStr{x}, SNil{}}} : Maybe<&2, PR>}:
  %Equal.sym(Maybe<&2, SP>, str_scan(String.append(x, SCon{'"', SNil{}}), SN{}), Some{SP{x, SNil{}}}, strC(x, SNil{}, hx)) : {strv(_) == Some{PR{RStr{x}, SNil{}}} : Maybe<&2, PR>}
  {==}

def cvStr.go(-s: String, -q1: String, +x: String, -q2: String, +e: {String.append(q1, String.append(x, q2)) == s : String}, +e1: {q1 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +e2: {q2 == SCon{'"', SNil{}} : String}) -> CR(CV{}, s):
  %e : CR(CV{}, _)
  %Equal.sym(String, q1, SCon{'"', SNil{}}, e1) : CR(CV{}, String.append(_, String.append(x, q2)))
  %Equal.sym(String, q2, SCon{'"', SNil{}}, e2) : CR(CV{}, SCon{'"', String.append(x, _)})
  (RStr{x}, SNil{}, cvStr.eq(x, hx), {==})

def cvStr(+s: String, +h: {ABNF.check(BK, B_string, s) == True{} : Bool}) -> CR(CV{}, s):
  seqE3(CR(CV{}, s), BK, ABNF.ref("quotation-mark"), CHARS, ABNF.ref("quotation-mark"), s, h, +q1 => +x => +q2 => +e => +h1 => +h2 => +h3 =>
    cvStr.go(s, q1, x, q2, e, charIs(BK, '"', q1, MBe("quotation-mark", ABNF.char('"'), q1, {==}, h1)), h2, charIs(BK, '"', q2, MBe("quotation-mark", ABNF.char('"'), q2, {==}, h3))))

def cvArr0.eq(+b: String, +e: String, +hb: {tokb('[', b) == True{} : Bool}, +he: {tokb(']', e) == True{} : Bool}) -> {pvc(MV{}, skip_ws(String.append(b, e))) == Some{PR{RArr{[]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(b, e)), SCon{'[', String.append(str_tl(skip_ws(b)), e)}, tokU('[', b, e, hb)) : {pv(1n+String.length(_), MV{}, _) == Some{PR{RArr{[]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), e)), skip_ws(e), WE(str_tl(skip_ws(b)), e, tokW('[', b, hb))) : {brk(']', _, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), e)), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), e)), MA{}, skip_ws(prt(p)))))) == Some{PR{RArr{[]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(e), SCon{']', str_tl(skip_ws(e))}, tokU0(']', e, he)) : {brk(']', _, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), e)), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), e)), MA{}, skip_ws(prt(p)))))) == Some{PR{RArr{[]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}
  {==}

def cvArr0(-s: String, +b: String, -o: String, +e: String, +es: {String.append(b, String.append(o, e)) == s : String}, +ho: {o == SNil{} : String}, +hb: {tokb('[', b) == True{} : Bool}, +he: {tokb(']', e) == True{} : Bool}) -> CR(CV{}, s):
  %es : CR(CV{}, _)
  %Equal.sym(String, o, SNil{}, ho) : CR(CV{}, String.append(b, String.append(_, e)))
  (RArr{[]}, str_tl(skip_ws(e)), cvArr0.eq(b, e, hb, he), tokW(']', e, he))

def cvObj0.eq(+b: String, +e: String, +hb: {tokb('{', b) == True{} : Bool}, +he: {tokb('}', e) == True{} : Bool}) -> {pvc(MV{}, skip_ws(String.append(b, e))) == Some{PR{RObj{[]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(b, e)), SCon{'{', String.append(str_tl(skip_ws(b)), e)}, tokU('{', b, e, hb)) : {pv(1n+String.length(_), MV{}, _) == Some{PR{RObj{[]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), e)), skip_ws(e), WE(str_tl(skip_ws(b)), e, tokW('{', b, hb))) : {brk('}', _, w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), e)), MM{}, w)) == Some{PR{RObj{[]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(e), SCon{'}', str_tl(skip_ws(e))}, tokU0('}', e, he)) : {brk('}', _, w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), e)), MM{}, w)) == Some{PR{RObj{[]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}
  {==}

def cvObj0(-s: String, +b: String, -o: String, +e: String, +es: {String.append(b, String.append(o, e)) == s : String}, +ho: {o == SNil{} : String}, +hb: {tokb('{', b) == True{} : Bool}, +he: {tokb('}', e) == True{} : Bool}) -> CR(CV{}, s):
  %es : CR(CV{}, _)
  %Equal.sym(String, o, SNil{}, ho) : CR(CV{}, String.append(b, String.append(_, e)))
  (RObj{[]}, str_tl(skip_ws(e)), cvObj0.eq(b, e, hb, he), tokW('}', e, he))

# The parse of a value followed by what MA reads.
def itemsCore(+G: Nat, +y1: String, +R2: String, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(y1)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool},
  -r2: Raw, +u2: String, +e2: {pvc(MA{}, skip_ws(R2)) == Some{PR{r2, u2}} : Maybe<&2, PR>}, +w2: {wsall(u2) == True{} : Bool},
  +hl1: {le(1n+String.length(skip_ws(y1)), G) == True{} : Bool}, +hl2: {le(1n+String.length(skip_ws(R2)), G) == True{} : Bool})
  -> {Maybe.bind(&2, PR, PR, pv(G, MV{}, skip_ws(String.append(y1, R2))), +p => acons(prr(p), pv(G, MA{}, skip_ws(prt(p))))) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(y1, R2)), String.append(skip_ws(y1), R2), skipApp(y1, R2, mvNE(1n+String.length(skip_ws(y1)), skip_ws(y1), PR{r1, u1}, e1))) : {Maybe.bind(&2, PR, PR, pv(G, MV{}, _), +p => acons(prr(p), pv(G, MA{}, skip_ws(prt(p))))) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, pv(G, MV{}, String.append(skip_ws(y1), R2)), Some{PR{r1, String.append(u1, R2)}}, extApply(MV{}, skip_ws(y1), r1, u1, e1, R2, G, folWsPre(u1, R2, w1, Equal.trans(Bool, fol(R2), fol(String.append(R2, SNil{})), True{}, Equal.cong(String, Bool, z => fol(z), R2, String.append(R2, SNil{}), Equal.sym(String, String.append(R2, SNil{}), R2, append_nil(R2))), folMA(1n+String.length(skip_ws(R2)), R2, SNil{}, PR{r2, u2}, e2))), hl1)) : {Maybe.bind(&2, PR, PR, _, +p => acons(prr(p), pv(G, MA{}, skip_ws(prt(p))))) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(u1, R2)), skip_ws(R2), WE(u1, R2, w1)) : {acons(r1, pv(G, MA{}, _)) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, pv(G, MA{}, skip_ws(R2)), Some{PR{r2, u2}}, extNil(MA{}, skip_ws(R2), r2, u2, e2, G, w2, hl2)) : {acons(r1, _) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  {==}

# A member's value followed by what MO reads.
def memCore(+g: Nat, +k: String, +y: String, +RE: String, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(y)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool},
  -rO: Raw, -uO: String, +hMO: {pv(g, MO{}, skip_ws(RE)) == Some{PR{rO, uO}} : Maybe<&2, PR>}, +hl1: {le(1n+String.length(skip_ws(y)), g) == True{} : Bool})
  -> {Maybe.bind(&2, PR, PR, pv(g, MV{}, skip_ws(String.append(y, RE))), +p => ocons(k, prr(p), pv(g, MO{}, skip_ws(prt(p))))) == Some{PR{ocons1(k, r1, rO), uO}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(y, RE)), String.append(skip_ws(y), RE), skipApp(y, RE, mvNE(1n+String.length(skip_ws(y)), skip_ws(y), PR{r1, u1}, e1))) : {Maybe.bind(&2, PR, PR, pv(g, MV{}, _), +p => ocons(k, prr(p), pv(g, MO{}, skip_ws(prt(p))))) == Some{PR{ocons1(k, r1, rO), uO}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, pv(g, MV{}, String.append(skip_ws(y), RE)), Some{PR{r1, String.append(u1, RE)}}, extApply(MV{}, skip_ws(y), r1, u1, e1, RE, g, folWsPre(u1, RE, w1, Equal.trans(Bool, fol(RE), fol(String.append(RE, SNil{})), True{}, Equal.cong(String, Bool, z => fol(z), RE, String.append(RE, SNil{}), Equal.sym(String, String.append(RE, SNil{}), RE, append_nil(RE))), folMO(g, RE, SNil{}, PR{rO, uO}, hMO))), hl1)) : {Maybe.bind(&2, PR, PR, _, +p => ocons(k, prr(p), pv(g, MO{}, skip_ws(prt(p))))) == Some{PR{ocons1(k, r1, rO), uO}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(u1, RE)), skip_ws(RE), WE(u1, RE, w1)) : {ocons(k, r1, pv(g, MO{}, _)) == Some{PR{ocons1(k, r1, rO), uO}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, pv(g, MO{}, skip_ws(RE)), Some{PR{rO, uO}}, hMO) : {ocons(k, r1, _) == Some{PR{ocons1(k, r1, rO), uO}} : Maybe<&2, PR>}
  {==}

def brkNot.go(f: Nat, S: String, -X: String, -kc: String -> Maybe<&2, PR>, -ko: String -> Maybe<&2, PR>, -p: PR, +e: {pv(f, MV{}, S) == Some{p} : Maybe<&2, PR>}) -> {brk(']', String.append(S, X), kc, ko) == ko(String.append(S, X)) : Maybe<&2, PR>}:
  match S:
    case SNil{}:
      Empty.absurd({brk(']', X, kc, ko) == ko(X) : Maybe<&2, PR>}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(f, MV{}, SNil{}), Some{p}, Equal.sym(Maybe<&2, PR>, pv(f, MV{}, SNil{}), None{}, pvNil(f)), e)))
    case SCon{+c, +S1}:
      bcase({brk(']', SCon{c, String.append(S1, X)}, kc, ko) == ko(SCon{c, String.append(S1, X)}) : Maybe<&2, PR>}, Char.is_eq(']', c),
        +k => Empty.absurd({brk(']', SCon{c, String.append(S1, X)}, kc, ko) == ko(SCon{c, String.append(S1, X)}) : Maybe<&2, PR>}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(f, MV{}, SCon{c, S1}), Some{p}, Equal.trans(Maybe<&2, PR>, None{}, pv(f, MV{}, SCon{']', S1}), pv(f, MV{}, SCon{c, S1}), Equal.sym(Maybe<&2, PR>, pv(f, MV{}, SCon{']', S1}), None{}, pvBr(f, S1)), Equal.cong(Char, Maybe<&2, PR>, z => pv(f, MV{}, SCon{z, S1}), ']', c, char_eq(']', c, k))), e))),
        +k => selF(Maybe<&2, PR>, Char.is_eq(']', c), z => kc(String.append(S1, X)), z => ko(SCon{c, String.append(S1, X)}), k))

# A value does not start with a closing bracket.
def brkNot(+y1: String, +R2: String, -kc: String -> Maybe<&2, PR>, -ko: String -> Maybe<&2, PR>, -r1: Raw, -u1: String, +e1: {pvc(MV{}, skip_ws(y1)) == Some{PR{r1, u1}} : Maybe<&2, PR>})
  -> {brk(']', skip_ws(String.append(y1, R2)), kc, ko) == ko(skip_ws(String.append(y1, R2))) : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(y1, R2)), String.append(skip_ws(y1), R2), skipApp(y1, R2, mvNE(1n+String.length(skip_ws(y1)), skip_ws(y1), PR{r1, u1}, e1))) : {brk(']', _, kc, ko) == ko(_) : Maybe<&2, PR>}
  brkNot.go(1n+String.length(skip_ws(y1)), skip_ws(y1), R2, kc, ko, PR{r1, u1}, e1)

def brkNotO.go(f: Nat, S: String, -kc: String -> Maybe<&2, PR>, -ko: String -> Maybe<&2, PR>, -p: PR, +e: {pv(f, MM{}, S) == Some{p} : Maybe<&2, PR>}) -> {brk('}', S, kc, ko) == ko(S) : Maybe<&2, PR>}:
  match S:
    case SNil{}:
      Empty.absurd({brk('}', SNil{}, kc, ko) == ko(SNil{}) : Maybe<&2, PR>}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(f, MM{}, SNil{}), Some{p}, Equal.sym(Maybe<&2, PR>, pv(f, MM{}, SNil{}), None{}, pvMMNil(f)), e)))
    case SCon{+c, +S1}:
      bcase({brk('}', SCon{c, S1}, kc, ko) == ko(SCon{c, S1}) : Maybe<&2, PR>}, Char.is_eq('}', c),
        +k => Empty.absurd({brk('}', SCon{c, S1}, kc, ko) == ko(SCon{c, S1}) : Maybe<&2, PR>}, none_ne_some(&2, PR, p, Equal.trans(Maybe<&2, PR>, None{}, pv(f, MM{}, SCon{c, S1}), Some{p}, Equal.trans(Maybe<&2, PR>, None{}, pv(f, MM{}, SCon{'}', S1}), pv(f, MM{}, SCon{c, S1}), Equal.sym(Maybe<&2, PR>, pv(f, MM{}, SCon{'}', S1}), None{}, pvBrO(f, S1)), Equal.cong(Char, Maybe<&2, PR>, z => pv(f, MM{}, SCon{z, S1}), '}', c, char_eq('}', c, k))), e))),
        +k => selF(Maybe<&2, PR>, Char.is_eq('}', c), z => kc(S1), z => ko(SCon{c, S1}), k))

def cvArr.eq(+b: String, +y1: String, +R: String, +e: String, +hb: {tokb('[', b) == True{} : Bool}, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(y1)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool},
  -r2: Raw, +u2: String, +e2: {pvc(MA{}, skip_ws(String.append(R, e))) == Some{PR{r2, u2}} : Maybe<&2, PR>}, +w2: {wsall(u2) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(b, String.append(String.append(y1, R), e)))) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(b, String.append(String.append(y1, R), e))), SCon{'[', String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))}, tokU('[', b, String.append(String.append(y1, R), e), hb)) : {pv(1n+String.length(_), MV{}, _) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), skip_ws(String.append(String.append(y1, R), e)), WE(str_tl(skip_ws(b)), String.append(String.append(y1, R), e), tokW('[', b, hb))) : {brk(']', _, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MA{}, skip_ws(prt(p)))))) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  %Equal.sym(String, String.append(String.append(y1, R), e), String.append(y1, String.append(R, e)), app3(y1, R, e)) : {brk(']', skip_ws(_), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MA{}, skip_ws(prt(p)))))) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, brk(']', skip_ws(String.append(y1, String.append(R, e))), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MA{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MV{}, skip_ws(String.append(y1, String.append(R, e)))), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MA{}, skip_ws(prt(p))))), brkNot(y1, String.append(R, e), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), MA{}, skip_ws(prt(p))))), r1, u1, e1)) : {_ == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  itemsCore(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e))), y1, String.append(R, e), r1, u1, e1, w1, r2, u2, e2, w2,
    leOcc(y1, String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e)), str_tl(skip_ws(b)), String.append(R, e), app_congl(str_tl(skip_ws(b)), String.append(y1, String.append(R, e)), String.append(String.append(y1, R), e), Equal.sym(String, String.append(String.append(y1, R), e), String.append(y1, String.append(R, e)), app3(y1, R, e)))),
    leOcc(String.append(R, e), String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e)), String.append(str_tl(skip_ws(b)), y1), SNil{}, Equal.trans(String, String.append(String.append(str_tl(skip_ws(b)), y1), String.append(String.append(R, e), SNil{})), String.append(str_tl(skip_ws(b)), String.append(y1, String.append(String.append(R, e), SNil{}))), String.append(str_tl(skip_ws(b)), String.append(String.append(y1, R), e)), app3(str_tl(skip_ws(b)), y1, String.append(String.append(R, e), SNil{})),
      app_congl(str_tl(skip_ws(b)), String.append(y1, String.append(String.append(R, e), SNil{})), String.append(String.append(y1, R), e), Equal.trans(String, String.append(y1, String.append(String.append(R, e), SNil{})), String.append(y1, String.append(R, e)), String.append(String.append(y1, R), e), app_congl(y1, String.append(String.append(R, e), SNil{}), String.append(R, e), append_nil(String.append(R, e))), Equal.sym(String, String.append(String.append(y1, R), e), String.append(y1, String.append(R, e)), app3(y1, R, e)))))))

def cvArr.go(-s: String, +b: String, -o: String, +e: String, +y1: String, +R: String, +es: {String.append(b, String.append(o, e)) == s : String}, +eo: {String.append(y1, R) == o : String}, +hb: {tokb('[', b) == True{} : Bool},
  +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(y1)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +r2: Raw, +u2: String, +e2: {pvc(MA{}, skip_ws(String.append(R, e))) == Some{PR{r2, u2}} : Maybe<&2, PR>}, +w2: {wsall(u2) == True{} : Bool}) -> CR(CV{}, s):
  %es : CR(CV{}, _)
  %eo : CR(CV{}, String.append(b, String.append(_, e)))
  (acons1(r1, r2), u2, cvArr.eq(b, y1, R, e, hb, r1, u1, e1, w1, r2, u2, e2, w2), w2)

def cvArr.d2(-s: String, +b: String, -o: String, +e: String, +y1: String, +R: String, +es: {String.append(b, String.append(o, e)) == s : String}, +eo: {String.append(y1, R) == o : String}, +hb: {tokb('[', b) == True{} : Bool},
  +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(y1)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, IHa: CR(CA{}, String.append(R, e))) -> CR(CV{}, s):
  (r2, u2, e2, w2) = IHa
  cvArr.go(s, b, o, e, y1, R, es, eo, hb, r1, u1, e1, w1, r2, u2, e2, w2)

def cvArr(-s: String, +b: String, -o: String, +e: String, +y1: String, +R: String, +es: {String.append(b, String.append(o, e)) == s : String}, +eo: {String.append(y1, R) == o : String}, +hb: {tokb('[', b) == True{} : Bool},
  IHv: CR(CV{}, y1), IHa: CR(CA{}, String.append(R, e))) -> CR(CV{}, s):
  (r1, u1, e1, w1) = IHv
  cvArr.d2(s, b, o, e, y1, R, es, eo, hb, r1, u1, e1, w1, IHa)

def cvObj.eq(+b: String, +mm: String, +R: String, +e: String, +hb: {tokb('{', b) == True{} : Bool}, -r: Raw, +u: String, +eM: {pvc(MM{}, skip_ws(String.append(mm, String.append(R, e)))) == Some{PR{r, u}} : Maybe<&2, PR>}, +w: {wsall(u) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(b, String.append(String.append(mm, R), e)))) == Some{PR{r, u}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(b, String.append(String.append(mm, R), e))), SCon{'{', String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e))}, tokU('{', b, String.append(String.append(mm, R), e), hb)) : {pv(1n+String.length(_), MV{}, _) == Some{PR{r, u}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e))), skip_ws(String.append(String.append(mm, R), e)), WE(str_tl(skip_ws(b)), String.append(String.append(mm, R), e), tokW('{', b, hb))) : {brk('}', _, w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e))), MM{}, w)) == Some{PR{r, u}} : Maybe<&2, PR>}
  %Equal.sym(String, String.append(String.append(mm, R), e), String.append(mm, String.append(R, e)), app3(mm, R, e)) : {brk('}', skip_ws(_), w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e))), MM{}, w)) == Some{PR{r, u}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, brk('}', skip_ws(String.append(mm, String.append(R, e))), w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e))), MM{}, w)), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e))), MM{}, skip_ws(String.append(mm, String.append(R, e)))), brkNotO.go(1n+String.length(skip_ws(String.append(mm, String.append(R, e)))), skip_ws(String.append(mm, String.append(R, e))), w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e))), MM{}, w), PR{r, u}, eM)) : {_ == Some{PR{r, u}} : Maybe<&2, PR>}
  extNil(MM{}, skip_ws(String.append(mm, String.append(R, e))), r, u, eM, 1n+String.length(String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e))), w, leOcc(String.append(mm, String.append(R, e)), String.append(str_tl(skip_ws(b)), String.append(String.append(mm, R), e)), str_tl(skip_ws(b)), SNil{}, app_congl(str_tl(skip_ws(b)), String.append(String.append(mm, String.append(R, e)), SNil{}), String.append(String.append(mm, R), e), Equal.trans(String, String.append(String.append(mm, String.append(R, e)), SNil{}), String.append(mm, String.append(R, e)), String.append(String.append(mm, R), e), append_nil(String.append(mm, String.append(R, e))), Equal.sym(String, String.append(String.append(mm, R), e), String.append(mm, String.append(R, e)), app3(mm, R, e))))))

def cvObj.go(-s: String, +b: String, -o: String, +e: String, +mm: String, +R: String, +es: {String.append(b, String.append(o, e)) == s : String}, +eo: {String.append(mm, R) == o : String}, +hb: {tokb('{', b) == True{} : Bool},
  +r: Raw, +u: String, +eM: {pvc(MM{}, skip_ws(String.append(mm, String.append(R, e)))) == Some{PR{r, u}} : Maybe<&2, PR>}, +w: {wsall(u) == True{} : Bool}) -> CR(CV{}, s):
  %es : CR(CV{}, _)
  %eo : CR(CV{}, String.append(b, String.append(_, e)))
  (r, u, cvObj.eq(b, mm, R, e, hb, r, u, eM, w), w)

def cvObj(-s: String, +b: String, -o: String, +e: String, +mm: String, +R: String, +es: {String.append(b, String.append(o, e)) == s : String}, +eo: {String.append(mm, R) == o : String}, +hb: {tokb('{', b) == True{} : Bool}, IH: CR(CMM{}, String.append(mm, String.append(R, e)))) -> CR(CV{}, s):
  (r, u, eM, w) = IH
  cvObj.go(s, b, o, e, mm, R, es, eo, hb, r, u, eM, w)

def ca0.eq(+E: String, +hE: {tokb(']', E) == True{} : Bool}) -> {pvc(MA{}, skip_ws(E)) == Some{PR{RArr{[]}, str_tl(skip_ws(E))}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(E), SCon{']', str_tl(skip_ws(E))}, tokU0(']', E, hE)) : {pv(1n+String.length(_), MA{}, _) == Some{PR{RArr{[]}, str_tl(skip_ws(E))}} : Maybe<&2, PR>}
  {==}

def ca0.go(-s: String, -a: String, +E: String, +es: {String.append(a, E) == s : String}, +ha: {a == SNil{} : String}, +hE: {tokb(']', E) == True{} : Bool}) -> CR(CA{}, s):
  %es : CR(CA{}, _)
  %Equal.sym(String, a, SNil{}, ha) : CR(CA{}, String.append(_, E))
  (RArr{[]}, str_tl(skip_ws(E)), ca0.eq(E, hE), tokW(']', E, hE))

def ca0(+d: Nat, +s: String, h: CH(CA{}, d, 0n, s)) -> CR(CA{}, s):
  seqE2(CR(CA{}, s), LB(d), ABNF.rep.exactly(0n, ITEM), ABNF.ref("end-array"), s, h, +a => +E => +es => +ha => +hE =>
    ca0.go(s, a, E, es, emptyE(LB(d), a, exZe(LB(d), ITEM, a, ha)), tokE("end-array", ']', E, {==}, {==}, toBK(d, ABNF.ref("end-array"), E, hE))))

def caS.eq(+vs: String, +v: String, +X2: String, +E: String, +hvs: {tokb(',', vs) == True{} : Bool}, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool},
  -r2: Raw, +u2: String, +e2: {pvc(MA{}, skip_ws(String.append(X2, E))) == Some{PR{r2, u2}} : Maybe<&2, PR>}, +w2: {wsall(u2) == True{} : Bool}) -> {pvc(MA{}, skip_ws(String.append(String.append(String.append(vs, v), X2), E))) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}:
  %Equal.sym(String, String.append(String.append(String.append(vs, v), X2), E), String.append(vs, String.append(v, String.append(X2, E))), Equal.trans(String, String.append(String.append(String.append(vs, v), X2), E), String.append(String.append(vs, v), String.append(X2, E)), String.append(vs, String.append(v, String.append(X2, E))), app3(String.append(vs, v), X2, E), app3(vs, v, String.append(X2, E)))) : {pv(1n+String.length(skip_ws(_)), MA{}, skip_ws(_)) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(vs, String.append(v, String.append(X2, E)))), SCon{',', String.append(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E)))}, tokU(',', vs, String.append(v, String.append(X2, E)), hvs)) : {pv(1n+String.length(_), MA{}, _) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E)))), skip_ws(String.append(v, String.append(X2, E))), WE(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E)), tokW(',', vs, hvs))) : {Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E)))), MV{}, _), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E)))), MA{}, skip_ws(prt(p))))) == Some{PR{acons1(r1, r2), u2}} : Maybe<&2, PR>}
  itemsCore(1n+String.length(String.append(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E)))), v, String.append(X2, E), r1, u1, e1, w1, r2, u2, e2, w2, leOcc(v, String.append(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E))), str_tl(skip_ws(vs)), String.append(X2, E), {==}),
    leOcc(String.append(X2, E), String.append(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E))), String.append(str_tl(skip_ws(vs)), v), SNil{}, Equal.trans(String, String.append(String.append(str_tl(skip_ws(vs)), v), String.append(String.append(X2, E), SNil{})), String.append(str_tl(skip_ws(vs)), String.append(v, String.append(String.append(X2, E), SNil{}))), String.append(str_tl(skip_ws(vs)), String.append(v, String.append(X2, E))), app3(str_tl(skip_ws(vs)), v, String.append(String.append(X2, E), SNil{})),
      app_congl(str_tl(skip_ws(vs)), String.append(v, String.append(String.append(X2, E), SNil{})), String.append(v, String.append(X2, E)), app_congl(v, String.append(String.append(X2, E), SNil{}), String.append(X2, E), append_nil(String.append(X2, E)))))))

def caS.go3(-s: String, -X: String, +E: String, -it: String, +X2: String, +vs: String, +v: String, +es: {String.append(X, E) == s : String}, +ex: {String.append(it, X2) == X : String}, +eit: {String.append(vs, v) == it : String}, +hvs: {tokb(',', vs) == True{} : Bool},
  +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +r2: Raw, +u2: String, +e2: {pvc(MA{}, skip_ws(String.append(X2, E))) == Some{PR{r2, u2}} : Maybe<&2, PR>}, +w2: {wsall(u2) == True{} : Bool}) -> CR(CA{}, s):
  %es : CR(CA{}, _)
  %ex : CR(CA{}, String.append(_, E))
  %eit : CR(CA{}, String.append(String.append(_, X2), E))
  (acons1(r1, r2), u2, caS.eq(vs, v, X2, E, hvs, r1, u1, e1, w1, r2, u2, e2, w2), w2)

def caS.go2(-s: String, -X: String, +E: String, -it: String, +X2: String, +vs: String, +v: String, +es: {String.append(X, E) == s : String}, +ex: {String.append(it, X2) == X : String}, +eit: {String.append(vs, v) == it : String}, +hvs: {tokb(',', vs) == True{} : Bool},
  +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, IHr: CR(CA{}, String.append(X2, E))) -> CR(CA{}, s):
  (r2, u2, e2, w2) = IHr
  caS.go3(s, X, E, it, X2, vs, v, es, ex, eit, hvs, r1, u1, e1, w1, r2, u2, e2, w2)

def caS.go(-s: String, -X: String, +E: String, -it: String, +X2: String, +vs: String, +v: String, +es: {String.append(X, E) == s : String}, +ex: {String.append(it, X2) == X : String}, +eit: {String.append(vs, v) == it : String}, +hvs: {tokb(',', vs) == True{} : Bool},
  IHv: CR(CV{}, v), IHr: CR(CA{}, String.append(X2, E))) -> CR(CA{}, s):
  (r1, u1, e1, w1) = IHv
  caS.go2(s, X, E, it, X2, vs, v, es, ex, eit, hvs, r1, u1, e1, w1, IHr)

def caS(+d: Nat, +m1: Nat, +s: String, h: CH(CA{}, d, 1n+m1, s), ihV: @y: String -> CH(CV{}, d, m1, y) -> CR(CV{}, y), ihR: @z: String -> CH(CA{}, d, m1, z) -> CR(CA{}, z)) -> CR(CA{}, s):
  seqE2(CR(CA{}, s), LB(d), ABNF.rep.exactly(1n+m1, ITEM), ABNF.ref("end-array"), s, h, +X => +E => +es => +hX => +hE =>
    seqE2(CR(CA{}, s), LB(d), ITEM, ABNF.rep.exactly(m1, ITEM), X, exSe(LB(d), m1, ITEM, X, hX), +it => +X2 => +ex => +hit => +hX2 =>
      seqE2(CR(CA{}, s), LB(d), ABNF.ref("value-separator"), ABNF.ref("value"), it, hit, +vs => +v => +eit => +hvs => +hv =>
        caS.go(s, X, E, it, X2, vs, v, es, ex, eit, tokE("value-separator", ',', vs, {==}, {==}, toBK(d, ABNF.ref("value-separator"), vs, hvs)),
          ihV(v, hv), ihR(String.append(X2, E), seqI2(LB(d), ABNF.rep.exactly(m1, ITEM), ABNF.ref("end-array"), X2, E, hX2, hE))))))

def altE(-C: Type, +k: ABNF.Book, +r: ABNF.Rule, rs: List<ABNF.Rule>, +s: String, +h: {ABNF.check(k, ABNF.alt(r <> rs), s) == True{} : Bool},
  fl: {ABNF.check(k, r, s) == True{} : Bool} -> C, fr: {ABNF.check(k, ABNF.alt(rs), s) == True{} : Bool} -> C) -> C:
  either(&2, &2, {ABNF.check(k, r, s) == True{} : Bool}, {ABNF.check(k, ABNF.alt(rs), s) == True{} : Bool}, C,
    or_elim(ABNF.check(k, r, s), ABNF.check(k, ABNF.alt(rs), s), tt.sym(ABNF.check(k, ABNF.alt(r <> rs), s), Bool.or(ABNF.check(k, r, s), ABNF.check(k, ABNF.alt(rs), s)), ABNF.alt.con(k, r, rs, s), h)),
    fl, fr)

def altNilE(-C: Type, +k: ABNF.Book, +s: String, +h: {ABNF.check(k, ABNF.alt([]), s) == True{} : Bool}) -> C:
  Empty.absurd(C, contra(ABNF.check(k, ABNF.alt([]), s), h, ABNF.alt.nil(k, s)))

def refZ(+N: String, +s: String, +h: {ABNF.check(LB(0n), ABNF.ref(N), s) == True{} : Bool}) -> Empty:
  contra(ABNF.check(LB(0n), ABNF.ref(N), s), h, ABNF.ref.zero(Laws.grammar, N, s))

# Nothing matches at depth 0.
def core0(+m: Nat, c: CMd, +s: String, h: CH(c, 0n, m, s)) -> CR(c, s):
  match c:
    case CV{}:
      Empty.absurd(CR(CV{}, s), refZ("value", s, h))
    case CA{}:
      seqE2(CR(CA{}, s), LB(0n), ABNF.rep.exactly(m, ITEM), ABNF.ref("end-array"), s, h, a => +E => es => ha => +hE => Empty.absurd(CR(CA{}, s), refZ("end-array", E, hE)))
    case CMM{}:
      seqE3(CR(CMM{}, s), LB(0n), ABNF.ref("member"), ABNF.rep.exactly(m, MITEM), ABNF.ref("end-object"), s, h, +M => X => E => es => +hM => hX => hE => Empty.absurd(CR(CMM{}, s), refZ("member", M, hM)))

def val0(+s: String) -> {ABNF.check(LB(0n), B_value, s) == False{} : Bool}:
  alt2(LB(0n), ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], s, False{}, False{}, ABNF.ref.zero(Laws.grammar, "false", s), alt2(LB(0n), ABNF.ref("null"), [ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], s, False{}, False{}, ABNF.ref.zero(Laws.grammar, "null", s), alt2(LB(0n), ABNF.ref("true"), [ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], s, False{}, False{}, ABNF.ref.zero(Laws.grammar, "true", s), alt2(LB(0n), ABNF.ref("object"), [ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], s, False{}, False{}, ABNF.ref.zero(Laws.grammar, "object", s), alt2(LB(0n), ABNF.ref("array"), [ABNF.ref("number"), ABNF.ref("string")], s, False{}, False{}, ABNF.ref.zero(Laws.grammar, "array", s), alt2(LB(0n), ABNF.ref("number"), [ABNF.ref("string")], s, False{}, False{}, ABNF.ref.zero(Laws.grammar, "number", s), alt2(LB(0n), ABNF.ref("string"), [], s, False{}, False{}, ABNF.ref.zero(Laws.grammar, "string", s), ABNF.alt.nil(LB(0n), s))))))))

# No value matches at depth 1.
def val1(+s: String, +h: {ABNF.check(LB(1n+0n), ABNF.ref("value"), s) == True{} : Bool}) -> Empty:
  contra(ABNF.check(LB(0n), B_value, s), tt.sym(ABNF.check(LB(1n+0n), ABNF.ref("value"), s), ABNF.check(LB(0n), B_value, s), refL(0n, "value", B_value, s, {==}), h), val0(s))

def cvArrB(+d2: Nat, -s: String, +b: String, +o: String, +e: String, +es: {String.append(b, String.append(o, e)) == s : String}, +hb: {tokb('[', b) == True{} : Bool},
  +ho: {ABNF.check(LB(d2), ABNF.opt(ELEMS), o) == True{} : Bool}, +he: {ABNF.check(LB(d2), ABNF.ref("end-array"), e) == True{} : Bool},
  kV: @y: String -> CH(CV{}, d2, 0n, y) -> CR(CV{}, y), kA: @m: Nat -> @z: String -> CH(CA{}, d2, m, z) -> CR(CA{}, z)) -> CR(CV{}, s):
  optE(CR(CV{}, s), LB(d2), ELEMS, o, ho,
    +h0 => cvArr0(s, b, o, e, es, h0, hb, tokE("end-array", ']', e, {==}, {==}, toBK(d2, ABNF.ref("end-array"), e, he))),
    +h1 => seqE2(CR(CV{}, s), LB(d2), ABNF.ref("value"), ABNF.rep.any(ITEM), o, h1, +y1 => +R => +eo => +hy => +hR0 =>
      starE(CR(CV{}, s), LB(d2), ITEM, R, hR0, +m => +hR =>
        cvArr(s, b, o, e, y1, R, es, eo, hb, kV(y1, hy), kA(m, String.append(R, e), seqI2(LB(d2), ABNF.rep.exactly(m, ITEM), ABNF.ref("end-array"), R, e, hR, he))))))

def cvArrCase(+d2: Nat, +s: String, +h: {ABNF.check(LB(d2), B_array, s) == True{} : Bool},
  kV: @y: String -> CH(CV{}, d2, 0n, y) -> CR(CV{}, y), kA: @m: Nat -> @z: String -> CH(CA{}, d2, m, z) -> CR(CA{}, z)) -> CR(CV{}, s):
  seqE3(CR(CV{}, s), LB(d2), ABNF.ref("begin-array"), ABNF.opt(ELEMS), ABNF.ref("end-array"), s, h, +b => +o => +e => +es => +hb => +ho => +he =>
    cvArrB(d2, s, b, o, e, es, tokE("begin-array", '[', b, {==}, {==}, toBK(d2, ABNF.ref("begin-array"), b, hb)), ho, he, kV, kA))

def cvObjB(+d2: Nat, -s: String, +b: String, +o: String, +e: String, +es: {String.append(b, String.append(o, e)) == s : String}, +hb: {tokb('{', b) == True{} : Bool},
  +ho: {ABNF.check(LB(d2), ABNF.opt(MEMBS), o) == True{} : Bool}, +he: {ABNF.check(LB(d2), ABNF.ref("end-object"), e) == True{} : Bool},
  kM: @m: Nat -> @z: String -> CH(CMM{}, d2, m, z) -> CR(CMM{}, z)) -> CR(CV{}, s):
  optE(CR(CV{}, s), LB(d2), MEMBS, o, ho,
    +h0 => cvObj0(s, b, o, e, es, h0, hb, tokE("end-object", '}', e, {==}, {==}, toBK(d2, ABNF.ref("end-object"), e, he))),
    +h1 => seqE2(CR(CV{}, s), LB(d2), ABNF.ref("member"), ABNF.rep.any(MITEM), o, h1, +mm => +R => +eo => +hm => +hR0 =>
      starE(CR(CV{}, s), LB(d2), MITEM, R, hR0, +m => +hR =>
        cvObj(s, b, o, e, mm, R, es, eo, hb, kM(m, String.append(mm, String.append(R, e)), seqI3(LB(d2), ABNF.ref("member"), ABNF.rep.exactly(m, MITEM), ABNF.ref("end-object"), mm, R, e, hm, hR, he))))))

def cvObjCase(+d2: Nat, +s: String, +h: {ABNF.check(LB(d2), B_object, s) == True{} : Bool},
  kM: @m: Nat -> @z: String -> CH(CMM{}, d2, m, z) -> CR(CMM{}, z)) -> CR(CV{}, s):
  seqE3(CR(CV{}, s), LB(d2), ABNF.ref("begin-object"), ABNF.opt(MEMBS), ABNF.ref("end-object"), s, h, +b => +o => +e => +es => +hb => +ho => +he =>
    cvObjB(d2, s, b, o, e, es, tokE("begin-object", '{', b, {==}, {==}, toBK(d2, ABNF.ref("begin-object"), b, hb)), ho, he, kM))

# A value at depth 2 or more, given the parts of arrays and objects.
def cvCase(+d2: Nat, +s: String, +h: {ABNF.check(LB(1n+1n+d2), ABNF.ref("value"), s) == True{} : Bool},
  kV: @y: String -> CH(CV{}, d2, 0n, y) -> CR(CV{}, y), kA: @m: Nat -> @z: String -> CH(CA{}, d2, m, z) -> CR(CA{}, z), kM: @m: Nat -> @z: String -> CH(CMM{}, d2, m, z) -> CR(CMM{}, z)) -> CR(CV{}, s):
  altE(CR(CV{}, s), LB(1n+d2), ABNF.ref("false"), [ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], s,
    tt.sym(ABNF.check(LB(1n+1n+d2), ABNF.ref("value"), s), ABNF.check(LB(1n+d2), B_value, s), refL(1n+d2, "value", B_value, s, {==}), h),
    +h1 => cvFalse(s, csE(BK, "false", s, MBe("false", ABNF.string.case_sensitive("false"), s, {==}, toBK(1n+d2, ABNF.ref("false"), s, h1)))),
    +r1 => altE(CR(CV{}, s), LB(1n+d2), ABNF.ref("null"), [ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], s, r1,
      +h2 => cvNull(s, csE(BK, "null", s, MBe("null", ABNF.string.case_sensitive("null"), s, {==}, toBK(1n+d2, ABNF.ref("null"), s, h2)))),
      +r2 => altE(CR(CV{}, s), LB(1n+d2), ABNF.ref("true"), [ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], s, r2,
        +h3 => cvTrue(s, csE(BK, "true", s, MBe("true", ABNF.string.case_sensitive("true"), s, {==}, toBK(1n+d2, ABNF.ref("true"), s, h3)))),
        +r3 => altE(CR(CV{}, s), LB(1n+d2), ABNF.ref("object"), [ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")], s, r3,
          +h4 => cvObjCase(d2, s, tt.sym(ABNF.check(LB(1n+d2), ABNF.ref("object"), s), ABNF.check(LB(d2), B_object, s), refL(d2, "object", B_object, s, {==}), h4), kM),
          +r4 => altE(CR(CV{}, s), LB(1n+d2), ABNF.ref("array"), [ABNF.ref("number"), ABNF.ref("string")], s, r4,
            +h5 => cvArrCase(d2, s, tt.sym(ABNF.check(LB(1n+d2), ABNF.ref("array"), s), ABNF.check(LB(d2), B_array, s), refL(d2, "array", B_array, s, {==}), h5), kV, kA),
            +r5 => altE(CR(CV{}, s), LB(1n+d2), ABNF.ref("number"), [ABNF.ref("string")], s, r5,
              +h6 => cvNum(s, MBe("number", B_number, s, {==}, toBK(1n+d2, ABNF.ref("number"), s, h6))),
              +r6 => altE(CR(CV{}, s), LB(1n+d2), ABNF.ref("string"), [], s, r6,
                +h7 => cvStr(s, MBe("string", B_string, s, {==}, toBK(1n+d2, ABNF.ref("string"), s, h7))),
                +r7 => altNilE(CR(CV{}, s), LB(1n+d2), s, r7))))))))

def memAssoc.go(x: String, +ns: String, -v: String, -RE: String) -> {String.append(String.append(String.append(x, SCon{'"', SNil{}}), String.append(ns, v)), RE) == String.append(x, SCon{'"', String.append(ns, String.append(v, RE))}) : String}:
  match x:
    case SNil{}:
      Equal.cong(String, String, z => SCon{'"', z}, String.append(String.append(ns, v), RE), String.append(ns, String.append(v, RE)), app3(ns, v, RE))
    case SCon{+c, r}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(String.append(String.append(r, SCon{'"', SNil{}}), String.append(ns, v)), RE), String.append(r, SCon{'"', String.append(ns, String.append(v, RE))}), memAssoc.go(r, ns, v, RE))

# CRO(s): the parser reads s after a member, leaving only whitespace.
def CRO(s: String) -> Type:
  &r: Raw -> &u: String -> {pvc(MO{}, skip_ws(s)) == Some{PR{r, u}} : Maybe<&2, PR>} & {wsall(u) == True{} : Bool}

def cmm.eq(+x: String, +ns: String, +v: String, +RE: String, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +hns: {tokb(':', ns) == True{} : Bool},
  -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool},
  -rO: Raw, +uO: String, +eO: {pvc(MO{}, skip_ws(RE)) == Some{PR{rO, uO}} : Maybe<&2, PR>}, +wO: {wsall(uO) == True{} : Bool})
  -> {pvc(MM{}, skip_ws(SCon{'"', String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})})) == Some{PR{ocons1(x, r1, rO), uO}} : Maybe<&2, PR>}:
  %Equal.sym(Maybe<&2, SP>, str_scan(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))}), SN{}), Some{SP{x, String.append(ns, String.append(v, RE))}}, strC(x, String.append(ns, String.append(v, RE)), hx)) : {Maybe.bind(&2, SP, PR, _, +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})), MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(1n+String.length(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})), MO{}, skip_ws(prt(p))))))) == Some{PR{ocons1(x, r1, rO), uO}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(ns, String.append(v, RE))), SCon{':', String.append(str_tl(skip_ws(ns)), String.append(v, RE))}, tokU(':', ns, String.append(v, RE), hns)) : {colon(_, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})), MV{}, skip_ws(w)), +p => ocons(x, prr(p), pv(1n+String.length(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})), MO{}, skip_ws(prt(p)))))) == Some{PR{ocons1(x, r1, rO), uO}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(ns)), String.append(v, RE))), skip_ws(String.append(v, RE)), WE(str_tl(skip_ws(ns)), String.append(v, RE), tokW(':', ns, hns))) : {Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})), MV{}, _), +p => ocons(x, prr(p), pv(1n+String.length(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})), MO{}, skip_ws(prt(p))))) == Some{PR{ocons1(x, r1, rO), uO}} : Maybe<&2, PR>}
  memCore(1n+String.length(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})), x, v, RE, r1, u1, e1, w1, rO, uO,
    extNil(MO{}, skip_ws(RE), rO, uO, eO, 1n+String.length(String.append(x, SCon{'"', String.append(ns, String.append(v, RE))})), wO,
      leOcc(RE, String.append(x, SCon{'"', String.append(ns, String.append(v, RE))}), String.append(x, SCon{'"', String.append(ns, v)}), SNil{},
        Equal.trans(String, String.append(String.append(x, SCon{'"', String.append(ns, v)}), String.append(RE, SNil{})), String.append(String.append(x, SCon{'"', String.append(ns, v)}), RE), String.append(x, SCon{'"', String.append(ns, String.append(v, RE))}),
          app_congl(String.append(x, SCon{'"', String.append(ns, v)}), String.append(RE, SNil{}), RE, append_nil(RE)),
          Equal.trans(String, String.append(String.append(x, SCon{'"', String.append(ns, v)}), RE), String.append(x, SCon{'"', String.append(String.append(ns, v), RE)}), String.append(x, SCon{'"', String.append(ns, String.append(v, RE))}),
            app3(x, SCon{'"', String.append(ns, v)}, RE),
            app_congl(x, SCon{'"', String.append(String.append(ns, v), RE)}, SCon{'"', String.append(ns, String.append(v, RE))}, Equal.cong(String, String, z => SCon{'"', z}, String.append(String.append(ns, v), RE), String.append(ns, String.append(v, RE)), app3(ns, v, RE))))))),
    leOcc(v, String.append(x, SCon{'"', String.append(ns, String.append(v, RE))}), String.append(x, SCon{'"', ns}), RE, app3(x, SCon{'"', ns}, String.append(v, RE))))

def cmm.go(-s: String, -M: String, +X: String, +E: String, -q: String, +ns: String, +v: String, -q1: String, +x: String, -q2: String,
  +es: {String.append(M, String.append(X, E)) == s : String}, +es2: {String.append(q, String.append(ns, v)) == M : String}, +es3: {String.append(q1, String.append(x, q2)) == q : String},
  +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +hns: {tokb(':', ns) == True{} : Bool},
  +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool},
  +rO: Raw, +uO: String, +eO: {pvc(MO{}, skip_ws(String.append(X, E))) == Some{PR{rO, uO}} : Maybe<&2, PR>}, +wO: {wsall(uO) == True{} : Bool}) -> CR(CMM{}, s):
  %es : CR(CMM{}, _)
  %es2 : CR(CMM{}, String.append(_, String.append(X, E)))
  %es3 : CR(CMM{}, String.append(String.append(_, String.append(ns, v)), String.append(X, E)))
  %Equal.sym(String, q1, SCon{'"', SNil{}}, eq1) : CR(CMM{}, String.append(String.append(String.append(_, String.append(x, q2)), String.append(ns, v)), String.append(X, E)))
  %Equal.sym(String, q2, SCon{'"', SNil{}}, eq2) : CR(CMM{}, SCon{'"', String.append(String.append(String.append(x, _), String.append(ns, v)), String.append(X, E))})
  %Equal.sym(String, String.append(String.append(String.append(x, SCon{'"', SNil{}}), String.append(ns, v)), String.append(X, E)), String.append(x, SCon{'"', String.append(ns, String.append(v, String.append(X, E)))}), memAssoc.go(x, ns, v, String.append(X, E))) : CR(CMM{}, SCon{'"', _})
  (ocons1(x, r1, rO), uO, cmm.eq(x, ns, v, String.append(X, E), hx, hns, r1, u1, e1, w1, rO, uO, eO, wO), wO)

def cmm.d2(-s: String, -M: String, +X: String, +E: String, -q: String, +ns: String, +v: String, -q1: String, +x: String, -q2: String,
  +es: {String.append(M, String.append(X, E)) == s : String}, +es2: {String.append(q, String.append(ns, v)) == M : String}, +es3: {String.append(q1, String.append(x, q2)) == q : String},
  +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +hns: {tokb(':', ns) == True{} : Bool},
  +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, IHO: CRO(String.append(X, E))) -> CR(CMM{}, s):
  (rO, uO, eO, wO) = IHO
  cmm.go(s, M, X, E, q, ns, v, q1, x, q2, es, es2, es3, eq1, eq2, hx, hns, r1, u1, e1, w1, rO, uO, eO, wO)

def cmm.d1(-s: String, -M: String, +X: String, +E: String, -q: String, +ns: String, +v: String, -q1: String, +x: String, -q2: String,
  +es: {String.append(M, String.append(X, E)) == s : String}, +es2: {String.append(q, String.append(ns, v)) == M : String}, +es3: {String.append(q1, String.append(x, q2)) == q : String},
  +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +hns: {tokb(':', ns) == True{} : Bool},
  IHV: CR(CV{}, v), IHO: CRO(String.append(X, E))) -> CR(CMM{}, s):
  (r1, u1, e1, w1) = IHV
  cmm.d2(s, M, X, E, q, ns, v, q1, x, q2, es, es2, es3, eq1, eq2, hx, hns, r1, u1, e1, w1, IHO)

# A member and what follows it, given its value and the rest.
def cmm(+d1: Nat, +m: Nat, +s: String, h: CH(CMM{}, 1n+d1, m, s), ihV: @y: String -> CH(CV{}, d1, 0n, y) -> CR(CV{}, y),
  ihO: @z: String -> {ABNF.check(LB(1n+d1), ABNF.seq([ABNF.rep.exactly(m, MITEM), ABNF.ref("end-object")]), z) == True{} : Bool} -> CRO(z)) -> CR(CMM{}, s):
  seqE3(CR(CMM{}, s), LB(1n+d1), ABNF.ref("member"), ABNF.rep.exactly(m, MITEM), ABNF.ref("end-object"), s, h, +M => +X => +E => +es => +hM => +hX => +hE =>
    seqE3(CR(CMM{}, s), LB(d1), ABNF.ref("string"), ABNF.ref("name-separator"), ABNF.ref("value"), M, tt.sym(ABNF.check(LB(1n+d1), ABNF.ref("member"), M), ABNF.check(LB(d1), B_member, M), refL(d1, "member", B_member, M, {==}), hM), +q => +ns => +v => +es2 => +hq => +hns => +hv =>
      seqE3(CR(CMM{}, s), BK, ABNF.ref("quotation-mark"), CHARS, ABNF.ref("quotation-mark"), q, MBe("string", B_string, q, {==}, toBK(d1, ABNF.ref("string"), q, hq)), +q1 => +x => +q2 => +es3 => +h1 => +h2 => +h3 =>
        cmm.d1(s, M, X, E, q, ns, v, q1, x, q2, es, es2, es3, charIs(BK, '"', q1, MBe("quotation-mark", ABNF.char('"'), q1, {==}, h1)), charIs(BK, '"', q2, MBe("quotation-mark", ABNF.char('"'), q2, {==}, h3)), h2,
          tokE("name-separator", ':', ns, {==}, {==}, toBK(d1, ABNF.ref("name-separator"), ns, hns)),
          ihV(v, hv), ihO(String.append(X, E), seqI2(LB(1n+d1), ABNF.rep.exactly(m, MITEM), ABNF.ref("end-object"), X, E, hX, hE))))))

def moZ.eq(+E: String, +hE: {tokb('}', E) == True{} : Bool}) -> {pvc(MO{}, skip_ws(E)) == Some{PR{RObj{[]}, str_tl(skip_ws(E))}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(E), SCon{'}', str_tl(skip_ws(E))}, tokU0('}', E, hE)) : {pv(1n+String.length(_), MO{}, _) == Some{PR{RObj{[]}, str_tl(skip_ws(E))}} : Maybe<&2, PR>}
  {==}

def moZ.go(-s: String, -a: String, +E: String, +es: {String.append(a, E) == s : String}, +ha: {a == SNil{} : String}, +hE: {tokb('}', E) == True{} : Bool}) -> CRO(s):
  %es : CRO(_)
  %Equal.sym(String, a, SNil{}, ha) : CRO(String.append(_, E))
  (RObj{[]}, str_tl(skip_ws(E)), moZ.eq(E, hE), tokW('}', E, hE))

# The end of an object.
def moZ(+d: Nat, +s: String, h: {ABNF.check(LB(d), ABNF.seq([ABNF.rep.exactly(0n, MITEM), ABNF.ref("end-object")]), s) == True{} : Bool}) -> CRO(s):
  seqE2(CRO(s), LB(d), ABNF.rep.exactly(0n, MITEM), ABNF.ref("end-object"), s, h, +a => +E => +es => +ha => +hE =>
    moZ.go(s, a, E, es, emptyE(LB(d), a, exZe(LB(d), MITEM, a, ha)), tokE("end-object", '}', E, {==}, {==}, toBK(d, ABNF.ref("end-object"), E, hE))))

def moS.eq(+vs: String, +mem: String, +X2: String, +E: String, +hvs: {tokb(',', vs) == True{} : Bool},
  -r: Raw, +u: String, +eM: {pvc(MM{}, skip_ws(String.append(mem, String.append(X2, E)))) == Some{PR{r, u}} : Maybe<&2, PR>}, +w: {wsall(u) == True{} : Bool})
  -> {pvc(MO{}, skip_ws(String.append(String.append(String.append(vs, mem), X2), E))) == Some{PR{r, u}} : Maybe<&2, PR>}:
  %Equal.sym(String, String.append(String.append(String.append(vs, mem), X2), E), String.append(vs, String.append(mem, String.append(X2, E))), Equal.trans(String, String.append(String.append(String.append(vs, mem), X2), E), String.append(String.append(vs, mem), String.append(X2, E)), String.append(vs, String.append(mem, String.append(X2, E))), app3(String.append(vs, mem), X2, E), app3(vs, mem, String.append(X2, E)))) : {pv(1n+String.length(skip_ws(_)), MO{}, skip_ws(_)) == Some{PR{r, u}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(vs, String.append(mem, String.append(X2, E)))), SCon{',', String.append(str_tl(skip_ws(vs)), String.append(mem, String.append(X2, E)))}, tokU(',', vs, String.append(mem, String.append(X2, E)), hvs)) : {pv(1n+String.length(_), MO{}, _) == Some{PR{r, u}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(vs)), String.append(mem, String.append(X2, E)))), skip_ws(String.append(mem, String.append(X2, E))), WE(str_tl(skip_ws(vs)), String.append(mem, String.append(X2, E)), tokW(',', vs, hvs))) : {pv(1n+String.length(String.append(str_tl(skip_ws(vs)), String.append(mem, String.append(X2, E)))), MM{}, _) == Some{PR{r, u}} : Maybe<&2, PR>}
  extNil(MM{}, skip_ws(String.append(mem, String.append(X2, E))), r, u, eM, 1n+String.length(String.append(str_tl(skip_ws(vs)), String.append(mem, String.append(X2, E)))), w,
    leOcc(String.append(mem, String.append(X2, E)), String.append(str_tl(skip_ws(vs)), String.append(mem, String.append(X2, E))), str_tl(skip_ws(vs)), SNil{}, app_congl(str_tl(skip_ws(vs)), String.append(String.append(mem, String.append(X2, E)), SNil{}), String.append(mem, String.append(X2, E)), append_nil(String.append(mem, String.append(X2, E))))))

def moS.go(-s: String, -X: String, +E: String, -it: String, +X2: String, +vs: String, +mem: String, +es: {String.append(X, E) == s : String}, +ex: {String.append(it, X2) == X : String}, +eit: {String.append(vs, mem) == it : String}, +hvs: {tokb(',', vs) == True{} : Bool},
  +r: Raw, +u: String, +eM: {pvc(MM{}, skip_ws(String.append(mem, String.append(X2, E)))) == Some{PR{r, u}} : Maybe<&2, PR>}, +w: {wsall(u) == True{} : Bool}) -> CRO(s):
  %es : CRO(_)
  %ex : CRO(String.append(_, E))
  %eit : CRO(String.append(String.append(_, X2), E))
  (r, u, moS.eq(vs, mem, X2, E, hvs, r, u, eM, w), w)

def moS.d(-s: String, -X: String, +E: String, -it: String, +X2: String, +vs: String, +mem: String, +es: {String.append(X, E) == s : String}, +ex: {String.append(it, X2) == X : String}, +eit: {String.append(vs, mem) == it : String}, +hvs: {tokb(',', vs) == True{} : Bool},
  IH: CR(CMM{}, String.append(mem, String.append(X2, E)))) -> CRO(s):
  (r, u, eM, w) = IH
  moS.go(s, X, E, it, X2, vs, mem, es, ex, eit, hvs, r, u, eM, w)

# A comma and the members after it.
def moS(+d: Nat, +m1: Nat, +s: String, h: {ABNF.check(LB(d), ABNF.seq([ABNF.rep.exactly(1n+m1, MITEM), ABNF.ref("end-object")]), s) == True{} : Bool}, ih: @w: String -> CH(CMM{}, d, m1, w) -> CR(CMM{}, w)) -> CRO(s):
  seqE2(CRO(s), LB(d), ABNF.rep.exactly(1n+m1, MITEM), ABNF.ref("end-object"), s, h, +X => +E => +es => +hX => +hE =>
    seqE2(CRO(s), LB(d), MITEM, ABNF.rep.exactly(m1, MITEM), X, exSe(LB(d), m1, MITEM, X, hX), +it => +X2 => +ex => +hit => +hX2 =>
      seqE2(CRO(s), LB(d), ABNF.ref("value-separator"), ABNF.ref("member"), it, hit, +vs => +mem => +eit => +hvs => +hmem =>
        moS.d(s, X, E, it, X2, vs, mem, es, ex, eit, tokE("value-separator", ',', vs, {==}, {==}, toBK(d, ABNF.ref("value-separator"), vs, hvs)),
          ih(String.append(mem, String.append(X2, E)), seqI3(LB(d), ABNF.ref("member"), ABNF.rep.exactly(m1, MITEM), ABNF.ref("end-object"), mem, X2, E, hmem, hX2, hE))))))

# Whatever matches the grammar at some depth, the parser reads.
def Core(d: Nat, m: Nat, c: CMd, +s: String, h: CH(c, d, m, s)) -> CR(c, s):
  match d:
    case 0n:
      core0(m, c, s, h)
    case 1n+ +d1:
      match d1:
        case 0n:
          match m:
            case 0n:
              match c:
                case CV{}:
                  Empty.absurd(CR(CV{}, s), val1(s, h))
                case CA{}:
                  ca0(1n+0n, s, h)
                case CMM{}:
                  cmm(0n, 0n, s, h, +y => hy => core0(0n, CV{}, y, hy), +z => hz => moZ(1n+0n, z, hz))
            case 1n+ +m1:
              match c:
                case CV{}:
                  Empty.absurd(CR(CV{}, s), val1(s, h))
                case CA{}:
                  caS(1n+0n, m1, s, h, +y => hy => Core(1n+0n, m1, CV{}, y, hy), +z => hz => Core(1n+0n, m1, CA{}, z, hz))
                case CMM{}:
                  cmm(0n, 1n+m1, s, h, +y => hy => core0(0n, CV{}, y, hy), +z => hz => moS(1n+0n, m1, z, hz, +w => hw => Core(1n+0n, m1, CMM{}, w, hw)))
        case 1n+ +d2:
          match m:
            case 0n:
              match c:
                case CV{}:
                  cvCase(d2, s, h, +y => hy => Core(d2, 0n, CV{}, y, hy), +k => +z => hz => Core(d2, k, CA{}, z, hz), +k => +z => hz => Core(d2, k, CMM{}, z, hz))
                case CA{}:
                  ca0(1n+1n+d2, s, h)
                case CMM{}:
                  cmm(1n+d2, 0n, s, h, +y => hy => Core(1n+d2, 0n, CV{}, y, hy), +z => hz => moZ(1n+1n+d2, z, hz))
            case 1n+ +m1:
              match c:
                case CV{}:
                  cvCase(d2, s, h, +y => hy => Core(d2, 0n, CV{}, y, hy), +k => +z => hz => Core(d2, k, CA{}, z, hz), +k => +z => hz => Core(d2, k, CMM{}, z, hz))
                case CA{}:
                  caS(1n+1n+d2, m1, s, h, +y => hy => Core(1n+1n+d2, m1, CV{}, y, hy), +z => hz => Core(1n+1n+d2, m1, CA{}, z, hz))
                case CMM{}:
                  cmm(1n+d2, 1n+m1, s, h, +y => hy => Core(1n+d2, 0n, CV{}, y, hy), +z => hz => moS(1n+1n+d2, m1, z, hz, +w => hw => Core(1n+1n+d2, m1, CMM{}, w, hw)))

# Dumping and loading
# ===================

def emptyOf(u: String, +h: {String.is_empty(u) == True{} : Bool}) -> {u == SNil{} : String}:
  match u:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Empty.absurd({SCon{c, t} == SNil{} : String}, false_ne_true(h))

def numK.go2(+a: String, u: String, -s: String, +e: {String.append(a, u) == s : String}, +ha: {ABNF.check(BK, B_number, a) == True{} : Bool}, +h: {String.is_empty(u) == True{} : Bool}) -> {ABNF.check(BK, B_number, s) == True{} : Bool}:
  match u:
    case SNil{}:
      %e : {ABNF.check(BK, B_number, _) == True{} : Bool}
      %Equal.sym(String, String.append(a, SNil{}), a, append_nil(a)) : {ABNF.check(BK, B_number, _) == True{} : Bool}
      ha
    case SCon{c, t}:
      Empty.absurd({ABNF.check(BK, B_number, s) == True{} : Bool}, false_ne_true(h))

def numK.go(m: Maybe<&2, SP>, -s: String, ns: NS(m, s, B_number), +h: {okend(m) == True{} : Bool}) -> {ABNF.check(BK, B_number, s) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({ABNF.check(BK, B_number, s) == True{} : Bool}, false_ne_true(h))
    case Some{p}:
      match p:
        case SP{+a, +u}:
          (e, +ha) = ns
          numK.go2(a, u, s, e, ha, h)

# A number's text that scans whole is a number.
def numK(+s: String, +h: {numok(s) == True{} : Bool}) -> {ABNF.check(BK, B_number, s) == True{} : Bool}:
  numK.go(num_scan(s), s, numS(s), h)

def strK.go2(+a: String, u: String, +s: String, +e: {String.append(a, SCon{'"', u}) == String.append(s, SCon{'"', SNil{}}) : String}, +ha: {ABNF.check(BK, CHARS, a) == True{} : Bool}, +h: {String.is_empty(u) == True{} : Bool}) -> {ABNF.check(BK, CHARS, s) == True{} : Bool}:
  match u:
    case SNil{}:
      %snoc_cancel(a, s, '"', e) : {ABNF.check(BK, CHARS, _) == True{} : Bool}
      ha
    case SCon{c, t}:
      Empty.absurd({ABNF.check(BK, CHARS, s) == True{} : Bool}, false_ne_true(h))

def strK.go(m: Maybe<&2, SP>, +s: String, ns: SNS(m, String.append(s, SCon{'"', SNil{}}), CHARS), +h: {okend(m) == True{} : Bool}) -> {ABNF.check(BK, CHARS, s) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({ABNF.check(BK, CHARS, s) == True{} : Bool}, false_ne_true(h))
    case Some{p}:
      match p:
        case SP{+a, +u}:
          (e, +ha) = ns
          strK.go2(a, u, s, e, ha, h)

# A string's text that scans whole is a run of chars.
def strK(+s: String, +h: {strok(s) == True{} : Bool}) -> {ABNF.check(BK, CHARS, s) == True{} : Bool}:
  strK.go(str_scan(String.append(s, SCon{'"', SNil{}}), SN{}), s, strS(String.append(s, SCon{'"', SNil{}}), SN{}), h)

def rtNum.s(s: String, +en: {num_scan(s) == Some{SP{s, SNil{}}} : Maybe<&2, SP>}) -> {pvc(MV{}, skip_ws(s)) == Some{PR{RNum{s}, SNil{}}} : Maybe<&2, PR>}:
  match s:
    case SNil{}:
      Empty.absurd({pvc(MV{}, skip_ws(SNil{})) == Some{PR{RNum{SNil{}}, SNil{}}} : Maybe<&2, PR>}, none_ne_some(&2, SP, SP{SNil{}, SNil{}}, en))
    case SCon{+c, +s1}:
      bcase({pvc(MV{}, skip_ws(SCon{c, s1})) == Some{PR{RNum{SCon{c, s1}}, SNil{}}} : Maybe<&2, PR>}, isnum0(c), +k => cvNum.eq(c, s1, k, en),
        +k => Empty.absurd({pvc(MV{}, skip_ws(SCon{c, s1})) == Some{PR{RNum{SCon{c, s1}}, SNil{}}} : Maybe<&2, PR>}, none_ne_some(&2, SP, SP{SCon{c, s1}, SNil{}}, Equal.trans(Maybe<&2, SP>, None{}, num_scan(SCon{c, s1}), Some{SP{SCon{c, s1}, SNil{}}}, Equal.sym(Maybe<&2, SP>, num_scan(SCon{c, s1}), None{}, cvNum.nf(c, s1, k)), en))))

def rtNum(+s: String, +h: {numok(s) == True{} : Bool}) -> {pvc(MV{}, skip_ws(s)) == Some{PR{RNum{s}, SNil{}}} : Maybe<&2, PR>}:
  rtNum.s(s, Equal.trans(Maybe<&2, SP>, num_scan(s), num_scan(String.append(s, SNil{})), Some{SP{s, SNil{}}}, Equal.cong(String, Maybe<&2, SP>, z => num_scan(z), s, String.append(s, SNil{}), Equal.sym(String, String.append(s, SNil{}), s, append_nil(s))), numC(s, SNil{}, numK(s, h), {==})))

# RTY(m, r): the parser reads back what pr(r, m) writes.
def RTY(m: PM, r: Raw) -> Data:
  match m:
    case PTop{}:
      {pvc(MV{}, skip_ws(pr(r, PTop{}))) == Some{PR{r, SNil{}}} : Maybe<&2, PR>}
    case PTail{}:
      match r:
        case RNull{}:
          Unit
        case RBool{b}:
          Unit
        case RNum{s}:
          Unit
        case RStr{s}:
          Unit
        case RArr{xs}:
          {pvc(MA{}, skip_ws(pr(RArr{xs}, PTail{}))) == Some{PR{RArr{xs}, SNil{}}} : Maybe<&2, PR>}
        case RObj{ms}:
          {pvc(MO{}, skip_ws(pr(RObj{ms}, PTail{}))) == Some{PR{RObj{ms}, SNil{}}} : Maybe<&2, PR>}

def rtArr(+x: Raw, +rest: List<&2, Raw>, +IH1: RTY(PTop{}, x), +IH2: RTY(PTail{}, RArr{rest})) -> RTY(PTop{}, RArr{x <> rest}):
  %Equal.sym(Maybe<&2, PR>, brk(']', skip_ws(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), MA{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), MV{}, skip_ws(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{})))), +p => acons(prr(p), pv(1n+String.length(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), MA{}, skip_ws(prt(p))))), brkNot(pr(x, PTop{}), pr(RArr{rest}, PTail{}), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), MA{}, skip_ws(prt(p))))), x, SNil{}, IH1)) : {_ == Some{PR{RArr{x <> rest}, SNil{}}} : Maybe<&2, PR>}
  itemsCore(1n+String.length(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), pr(x, PTop{}), pr(RArr{rest}, PTail{}), x, SNil{}, IH1, {==}, RArr{rest}, SNil{}, IH2, {==},
    leOcc(pr(x, PTop{}), String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{})), SNil{}, pr(RArr{rest}, PTail{}), {==}),
    leOcc(pr(RArr{rest}, PTail{}), String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{})), pr(x, PTop{}), SNil{}, app_congl(pr(x, PTop{}), String.append(pr(RArr{rest}, PTail{}), SNil{}), pr(RArr{rest}, PTail{}), append_nil(pr(RArr{rest}, PTail{})))))

def rtArrT(+x: Raw, +rest: List<&2, Raw>, +IH1: RTY(PTop{}, x), +IH2: RTY(PTail{}, RArr{rest})) -> RTY(PTail{}, RArr{x <> rest}):
  itemsCore(1n+String.length(String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{}))), pr(x, PTop{}), pr(RArr{rest}, PTail{}), x, SNil{}, IH1, {==}, RArr{rest}, SNil{}, IH2, {==},
    leOcc(pr(x, PTop{}), String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{})), SNil{}, pr(RArr{rest}, PTail{}), {==}),
    leOcc(pr(RArr{rest}, PTail{}), String.append(pr(x, PTop{}), pr(RArr{rest}, PTail{})), pr(x, PTop{}), SNil{}, app_congl(pr(x, PTop{}), String.append(pr(RArr{rest}, PTail{}), SNil{}), pr(RArr{rest}, PTail{}), append_nil(pr(RArr{rest}, PTail{})))))

# A member as pr writes it, and the members after it.
def rtMem(+k: String, +v: Raw, +rest: List<&2, RMem>, +hk: {strok(k) == True{} : Bool}, +IHv: RTY(PTop{}, v), +IHr: RTY(PTail{}, RObj{rest}))
  -> {pv(1n+String.length(SCon{'"', String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}})}), MM{}, SCon{'"', String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}})}) == Some{PR{RObj{RMem{k, v} <> rest}, SNil{}}} : Maybe<&2, PR>}:
  %Equal.sym(Maybe<&2, SP>, str_scan(String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}}), SN{}), Some{SP{k, SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}}}, strC(k, SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}, strK(k, hk))) : {Maybe.bind(&2, SP, PR, _, +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}})), MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(1n+String.length(String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}})), MO{}, skip_ws(prt(p))))))) == Some{PR{RObj{RMem{k, v} <> rest}, SNil{}}} : Maybe<&2, PR>}
  memCore(1n+String.length(String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}})), k, pr(v, PTop{}), pr(RObj{rest}, PTail{}), v, SNil{}, IHv, {==}, RObj{rest}, SNil{},
    extNil(MO{}, skip_ws(pr(RObj{rest}, PTail{})), RObj{rest}, SNil{}, IHr, 1n+String.length(String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}})), {==},
      leOcc(pr(RObj{rest}, PTail{}), String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}}), String.append(k, SCon{'"', SCon{':', pr(v, PTop{})}}), SNil{},
        Equal.trans(String, String.append(String.append(k, SCon{'"', SCon{':', pr(v, PTop{})}}), String.append(pr(RObj{rest}, PTail{}), SNil{})), String.append(String.append(k, SCon{'"', SCon{':', pr(v, PTop{})}}), pr(RObj{rest}, PTail{})), String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}}),
          app_congl(String.append(k, SCon{'"', SCon{':', pr(v, PTop{})}}), String.append(pr(RObj{rest}, PTail{}), SNil{}), pr(RObj{rest}, PTail{}), append_nil(pr(RObj{rest}, PTail{}))),
          app3(k, SCon{'"', SCon{':', pr(v, PTop{})}}, pr(RObj{rest}, PTail{}))))),
    leOcc(pr(v, PTop{}), String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}}), String.append(k, SCon{'"', SCon{':', SNil{}}}), pr(RObj{rest}, PTail{}), app3(k, SCon{'"', SCon{':', SNil{}}}, String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{})))))

def rtObj(+k: String, +v: Raw, +rest: List<&2, RMem>, +hk: {strok(k) == True{} : Bool}, +IHv: RTY(PTop{}, v), +IHr: RTY(PTail{}, RObj{rest})) -> RTY(PTop{}, RObj{RMem{k, v} <> rest}):
  %Equal.sym(String, String.append(String.append(k, String.append("\":", pr(v, PTop{}))), pr(RObj{rest}, PTail{})), String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}}), app3(k, String.append("\":", pr(v, PTop{})), pr(RObj{rest}, PTail{}))) : {pvc(MV{}, skip_ws(SCon{'{', SCon{'"', _}})) == Some{PR{RObj{RMem{k, v} <> rest}, SNil{}}} : Maybe<&2, PR>}
  rtMem(k, v, rest, hk, IHv, IHr)

def rtObjT(+k: String, +v: Raw, +rest: List<&2, RMem>, +hk: {strok(k) == True{} : Bool}, +IHv: RTY(PTop{}, v), +IHr: RTY(PTail{}, RObj{rest})) -> RTY(PTail{}, RObj{RMem{k, v} <> rest}):
  %Equal.sym(String, String.append(String.append(k, String.append("\":", pr(v, PTop{}))), pr(RObj{rest}, PTail{})), String.append(k, SCon{'"', SCon{':', String.append(pr(v, PTop{}), pr(RObj{rest}, PTail{}))}}), app3(k, String.append("\":", pr(v, PTop{})), pr(RObj{rest}, PTail{}))) : {pvc(MO{}, skip_ws(SCon{',', SCon{'"', _}})) == Some{PR{RObj{RMem{k, v} <> rest}, SNil{}}} : Maybe<&2, PR>}
  rtMem(k, v, rest, hk, IHv, IHr)

# What pr writes, the parser reads back.
def RT(r: Raw, m: PM, +h: IsTrue(wf(r))) -> RTY(m, r):
  match r:
    case RNull{}:
      match m:
        case PTop{}:
          {==}
        case PTail{}:
          Unit{}
    case RBool{b}:
      match b:
        case True{}:
          match m:
            case PTop{}:
              {==}
            case PTail{}:
              Unit{}
        case False{}:
          match m:
            case PTop{}:
              {==}
            case PTail{}:
              Unit{}
    case RNum{+s}:
      match m:
        case PTop{}:
          rtNum(s, ofTrue(numok(s), h))
        case PTail{}:
          Unit{}
    case RStr{+s}:
      match m:
        case PTop{}:
          cvStr.eq(s, strK(s, ofTrue(strok(s), h)))
        case PTail{}:
          Unit{}
    case RArr{xs}:
      match xs:
        case []:
          match m:
            case PTop{}:
              {==}
            case PTail{}:
              {==}
        case +x <> +rest:
          match m:
            case PTop{}:
              rtArr(x, rest, RT(x, PTop{}, andT1(wf(x), wf(RArr{rest}), h)), RT(RArr{rest}, PTail{}, andT2(wf(x), wf(RArr{rest}), h)))
            case PTail{}:
              rtArrT(x, rest, RT(x, PTop{}, andT1(wf(x), wf(RArr{rest}), h)), RT(RArr{rest}, PTail{}, andT2(wf(x), wf(RArr{rest}), h)))
    case RObj{ms}:
      match ms:
        case []:
          match m:
            case PTop{}:
              {==}
            case PTail{}:
              {==}
        case RMem{+k, +v} <> +rest:
          match m:
            case PTop{}:
              rtObj(k, v, rest, ofTrue(strok(k), andT1(strok(k), Bool.and(wf(v), wf(RObj{rest})), h)), RT(v, PTop{}, andT1(wf(v), wf(RObj{rest}), andT2(strok(k), Bool.and(wf(v), wf(RObj{rest})), h))), RT(RObj{rest}, PTail{}, andT2(wf(v), wf(RObj{rest}), andT2(strok(k), Bool.and(wf(v), wf(RObj{rest})), h))))
            case PTail{}:
              rtObjT(k, v, rest, ofTrue(strok(k), andT1(strok(k), Bool.and(wf(v), wf(RObj{rest})), h)), RT(v, PTop{}, andT1(wf(v), wf(RObj{rest}), andT2(strok(k), Bool.and(wf(v), wf(RObj{rest})), h))), RT(RObj{rest}, PTail{}, andT2(wf(v), wf(RObj{rest}), andT2(strok(k), Bool.and(wf(v), wf(RObj{rest})), h))))

def mkEq(+r: Raw, b: Bool, e: {wf(r) == b : Bool}, +h: IsTrue(wf(r))) -> {mk(r, b, e) == Some{J{r, h}} : Maybe<Js>}:
  match b:
    case True{}:
      Equal.cong(Js, Maybe<Js>, z => Some{z}, J{r, istrue(wf(r), e)}, J{r, h}, j_irr(r, istrue(wf(r), e), h))
    case False{}:
      Empty.absurd({mk(r, False{}, e) == Some{J{r, h}} : Maybe<Js>}, contra(wf(r), ofTrue(wf(r), h), e))

def Laws.dump.ok(j):
  match j:
    case J{+r, +h}:
      %Equal.sym(Maybe<&2, PR>, pvc(MV{}, skip_ws(pr(r, PTop{}))), Some{PR{r, SNil{}}}, RT(r, PTop{}, h)) : {fin(_) == Some{J{r, h}} : Maybe<Js>}
      mkEq(r, wf(r), {==}, h)

def finT(+r: Raw, b: Bool, +h: {Maybe.is_some(&1, Js, fin2(r, b)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))

def emptyWs(+t: String, +he: {String.is_empty(skip_ws(t)) == True{} : Bool}) -> {wsall(t) == True{} : Bool}:
  %WI(t) : {wsall(_) == True{} : Bool}
  %Equal.sym(String, skip_ws(t), SNil{}, emptyOf(skip_ws(t), he)) : {wsall(String.append(wsp(t), _)) == True{} : Bool}
  %Equal.sym(String, String.append(wsp(t), SNil{}), wsp(t), append_nil(wsp(t))) : {wsall(_) == True{} : Bool}
  WIa(t)

def loadF.q(+s: String, +t: String, +y: String, +ey: {String.append(y, t) == skip_ws(s) : String}, +hy: {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool}, +he: {String.is_empty(skip_ws(t)) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s) == True{} : Bool}:
  %WI(s) : {ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), _) == True{} : Bool}
  %ey : {ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), String.append(wsp(s), _)) == True{} : Bool}
  seqI3(BK, ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws"), wsp(s), y, t, wsI(wsp(s), WIa(s)), hy, wsI(t, emptyWs(t, he)))

def loadF.p(+s: String, +p: PR, P: &y: String -> {String.append(y, prt(p)) == skip_ws(s) : String} & {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool} & {wf(prr(p)) == True{} : Bool},
  +h: {Maybe.is_some(&1, Js, fin2(prr(p), String.is_empty(skip_ws(prt(p))))) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s) == True{} : Bool}:
  (y, ey, hy, hw) = P
  loadF.q(s, prt(p), y, ey, hy, finT(prr(p), String.is_empty(skip_ws(prt(p))), h))

def loadF.go(+s: String, res: Maybe<&2, PR>, P: PSR(ABNF.ref("value"), res, skip_ws(s)), +h: {Maybe.is_some(&1, Js, fin(res)) == True{} : Bool})
  -> {ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s) == True{} : Bool}:
  match res:
    case None{}:
      Empty.absurd({ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s) == True{} : Bool}, false_ne_true(h))
    case Some{+p}:
      loadF.p(s, p, P, h)

# What loads is JSON text.
def loadF(+s: String, +h: {Maybe.is_some(&1, Js, Laws.load(s)) == True{} : Bool}) -> {ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s) == True{} : Bool}:
  loadF.go(s, pvc(MV{}, skip_ws(s)), Sound(1n+String.length(skip_ws(s)), MV{}, skip_ws(s)), h)

def wsNil(s: String, +h: {wsall(s) == True{} : Bool}) -> {skip_ws(s) == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, skip_ws(SCon{c, t}), skip_ws(t), selT(String, isws(c), u => skip_ws(t), u => SCon{c, t}, and_l(isws(c), wsall(t), h))) : {_ == SNil{} : String}
      wsNil(t, and_r(isws(c), wsall(t), h))

def wfOf.p(-S: String, +p: PR, P: &y: String -> {String.append(y, prt(p)) == S : String} & {ABNF.check(BK, ABNF.ref("value"), y) == True{} : Bool} & {wf(prr(p)) == True{} : Bool}, -r: Raw, -u: String, +e: {Some{p} == Some{PR{r, u}} : Maybe<&2, PR>})
  -> {wf(r) == True{} : Bool}:
  (y, ey, hy, hw) = P
  Equal.trans(Bool, wf(r), wf(prr(p)), True{}, Equal.cong(PR, Bool, z => wf(prr(z)), PR{r, u}, p, Equal.sym(PR, p, PR{r, u}, some_inj(&2, PR, p, PR{r, u}, e))), hw)

def wfOf.go(-S: String, res: Maybe<&2, PR>, P: PSR(ABNF.ref("value"), res, S), -r: Raw, -u: String, +e: {res == Some{PR{r, u}} : Maybe<&2, PR>}) -> {wf(r) == True{} : Bool}:
  match res:
    case None{}:
      Empty.absurd({wf(r) == True{} : Bool}, none_ne_some(&2, PR, PR{r, u}, e))
    case Some{+p}:
      wfOf.p(S, p, P, r, u, e)

# What the parser builds from a value is valid.
def wfOf(+S: String, -r: Raw, -u: String, +e: {pvc(MV{}, S) == Some{PR{r, u}} : Maybe<&2, PR>}) -> {wf(r) == True{} : Bool}:
  wfOf.go(S, pvc(MV{}, S), Sound(1n+String.length(S), MV{}, S), r, u, e)

def mkSome(+r: Raw, b: Bool, e: {wf(r) == b : Bool}, +hb: {b == True{} : Bool}) -> {Maybe.is_some(&1, Js, mk(r, b, e)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Maybe.is_some(&1, Js, mk(r, False{}, e)) == True{} : Bool}, false_ne_true(hb))

def loadB.go(-s: String, +w1: String, +v: String, +w2: String, +es: {String.append(w1, String.append(v, w2)) == s : String}, +hw1: {wsall(w1) == True{} : Bool}, +hw2: {wsall(w2) == True{} : Bool},
  +r: Raw, +u: String, +e: {pvc(MV{}, skip_ws(v)) == Some{PR{r, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}) -> {Maybe.is_some(&1, Js, Laws.load(s)) == True{} : Bool}:
  %es : {Maybe.is_some(&1, Js, fin(pvc(MV{}, skip_ws(_)))) == True{} : Bool}
  %Equal.sym(String, skip_ws(String.append(w1, String.append(v, w2))), skip_ws(String.append(v, w2)), WE(w1, String.append(v, w2), hw1)) : {Maybe.is_some(&1, Js, fin(pvc(MV{}, _))) == True{} : Bool}
  %Equal.sym(String, skip_ws(String.append(v, w2)), String.append(skip_ws(v), w2), skipApp(v, w2, mvNE(1n+String.length(skip_ws(v)), skip_ws(v), PR{r, u}, e))) : {Maybe.is_some(&1, Js, fin(pvc(MV{}, _))) == True{} : Bool}
  %Equal.sym(Maybe<&2, PR>, pvc(MV{}, String.append(skip_ws(v), w2)), Some{PR{r, String.append(u, w2)}}, extApply(MV{}, skip_ws(v), r, u, e, w2, 1n+String.length(String.append(skip_ws(v), w2)), folWsPre(u, w2, wu, folWs(w2, hw2)), lePre(skip_ws(v), w2))) : {Maybe.is_some(&1, Js, fin(_)) == True{} : Bool}
  %Equal.sym(String, skip_ws(String.append(u, w2)), skip_ws(w2), WE(u, w2, wu)) : {Maybe.is_some(&1, Js, fin2(r, String.is_empty(_))) == True{} : Bool}
  %Equal.sym(String, skip_ws(w2), SNil{}, wsNil(w2, hw2)) : {Maybe.is_some(&1, Js, fin2(r, String.is_empty(_))) == True{} : Bool}
  mkSome(r, wf(r), {==}, wfOf(skip_ws(v), r, u, e))

def loadB.c(-s: String, +w1: String, +v: String, +w2: String, +es: {String.append(w1, String.append(v, w2)) == s : String}, +hw1: {wsall(w1) == True{} : Bool}, +hw2: {wsall(w2) == True{} : Bool}, c: CR(CV{}, v))
  -> {Maybe.is_some(&1, Js, Laws.load(s)) == True{} : Bool}:
  (r, u, e, wu) = c
  loadB.go(s, w1, v, w2, es, hw1, hw2, r, u, e, wu)

def loadB.d(-s: String, +w1: String, +v: String, +w2: String, +es: {String.append(w1, String.append(v, w2)) == s : String}, +hw1: {wsall(w1) == True{} : Bool}, +hw2: {wsall(w2) == True{} : Bool},
  p: &d: Nat -> {ABNF.check(ABNF.limit(d, Laws.grammar), ABNF.ref("value"), v) == True{} : Bool}) -> {Maybe.is_some(&1, Js, Laws.load(s)) == True{} : Bool}:
  (d, hd) = p
  loadB.c(s, w1, v, w2, es, hw1, hw2, Core(d, 0n, CV{}, v, hd))

# JSON text loads.
def loadB(+s: String, +h: {ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s) == True{} : Bool}) -> {Maybe.is_some(&1, Js, Laws.load(s)) == True{} : Bool}:
  seqE3({Maybe.is_some(&1, Js, Laws.load(s)) == True{} : Bool}, BK, ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws"), s, h, +w1 => +v => +w2 => +es => +h1 => +hv => +h3 =>
    loadB.d(s, w1, v, w2, es, wsE(w1, h1), wsE(w2, h3), ABNF.full.elim(Laws.grammar, ABNF.ref("value"), v, hv)))

def loadOk(+s: String) -> {Maybe.is_some(&1, Js, Laws.load(s)) == ABNF.matches(Laws.grammar, "JSON-text", s) : Bool}:
  %Equal.sym(Bool, ABNF.matches(Laws.grammar, "JSON-text", s), ABNF.check(BK, ABNF.ref("JSON-text"), s), ABNF.matches.ok(Laws.grammar, "JSON-text", s)) : {Maybe.is_some(&1, Js, Laws.load(s)) == _ : Bool}
  %Equal.sym(Bool, ABNF.check(BK, ABNF.ref("JSON-text"), s), ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s), MB("JSON-text", ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s, {==})) : {Maybe.is_some(&1, Js, Laws.load(s)) == _ : Bool}
  beq(Maybe.is_some(&1, Js, Laws.load(s)), ABNF.check(BK, ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")]), s), +h => loadF(s, h), +h => loadB(s, h))

def Laws.load.ok(s):
  loadOk(s)

# Shapes
# ======

def wsM(+s: String, +h: {ABNF.matches(Laws.grammar, "ws", s) == True{} : Bool}) -> {wsall(s) == True{} : Bool}:
  wsE(s, mt("ws", s, h))

def tokM(+N: String, +ch: Char, +b: String, +e: {gsel(GRAMMAR, N) == [TOK(ch)] : List<ABNF.Rule>}, +hch: {isws(ch) == False{} : Bool}, +h: {ABNF.matches(Laws.grammar, N, b) == True{} : Bool}) -> {tokb(ch, b) == True{} : Bool}:
  tokE(N, ch, b, e, hch, mt(N, b, h))

# A value between whitespace parses as the value.
def wrapWs(+w1: String, +v: String, +w2: String, +hw1: {wsall(w1) == True{} : Bool}, +hw2: {wsall(w2) == True{} : Bool}, +r: Raw, +u: String, +e: {pvc(MV{}, skip_ws(v)) == Some{PR{r, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(w1, String.append(v, w2)))) == Some{PR{r, String.append(u, w2)}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(w1, String.append(v, w2))), skip_ws(String.append(v, w2)), WE(w1, String.append(v, w2), hw1)) : {pvc(MV{}, _) == Some{PR{r, String.append(u, w2)}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(v, w2)), String.append(skip_ws(v), w2), skipApp(v, w2, mvNE(1n+String.length(skip_ws(v)), skip_ws(v), PR{r, u}, e))) : {pvc(MV{}, _) == Some{PR{r, String.append(u, w2)}} : Maybe<&2, PR>}
  extApply(MV{}, skip_ws(v), r, u, e, w2, 1n+String.length(String.append(skip_ws(v), w2)), folWsPre(u, w2, wu, folWs(w2, hw2)), lePre(skip_ws(v), w2))

# A text the parser reads loads as what it builds.
def finEq(+S: String, +r: Raw, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{r, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}) -> {Laws.load(S) == Some{J{r, istrue(wf(r), wfOf(skip_ws(S), r, u, e))}} : Maybe<Js>}:
  %Equal.sym(Maybe<&2, PR>, pvc(MV{}, skip_ws(S)), Some{PR{r, u}}, e) : {fin(_) == Some{J{r, istrue(wf(r), wfOf(skip_ws(S), r, u, e))}} : Maybe<Js>}
  %Equal.sym(String, skip_ws(u), SNil{}, wsNil(u, wu)) : {fin2(r, String.is_empty(_)) == Some{J{r, istrue(wf(r), wfOf(skip_ws(S), r, u, e))}} : Maybe<Js>}
  mkEq(r, wf(r), {==}, istrue(wf(r), wfOf(skip_ws(S), r, u, e)))

def jR(+S: String, -j: Js, +r: Raw, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{r, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}, +h: {Laws.load(S) == Some{j} : Maybe<Js>})
  -> {J{r, istrue(wf(r), wfOf(skip_ws(S), r, u, e))} == j : Js}:
  some_inj(&1, Js, J{r, istrue(wf(r), wfOf(skip_ws(S), r, u, e))}, j, Equal.trans(Maybe<Js>, Some{J{r, istrue(wf(r), wfOf(skip_ws(S), r, u, e))}}, Laws.load(S), Some{j}, Equal.sym(Maybe<Js>, Laws.load(S), Some{J{r, istrue(wf(r), wfOf(skip_ws(S), r, u, e))}}, finEq(S, r, u, e, wu)), h))

def litE(-w: String, -lit: String, -r: Raw, +e2: {w == lit : String}, +ok: {pvc(MV{}, skip_ws(lit)) == Some{PR{r, SNil{}}} : Maybe<&2, PR>}) -> {pvc(MV{}, skip_ws(w)) == Some{PR{r, SNil{}}} : Maybe<&2, PR>}:
  %Equal.sym(String, w, lit, e2) : {pvc(MV{}, skip_ws(_)) == Some{PR{r, SNil{}}} : Maybe<&2, PR>}
  ok

def quoteEq(-a: String, -c: String, +y: String, +ea: {a == SCon{'"', SNil{}} : String}, +ec: {c == SCon{'"', SNil{}} : String}) -> {SCon{'"', String.append(y, SCon{'"', SNil{}})} == String.append(a, String.append(y, c)) : String}:
  %Equal.sym(String, a, SCon{'"', SNil{}}, ea) : {SCon{'"', String.append(y, SCon{'"', SNil{}})} == String.append(_, String.append(y, c)) : String}
  %Equal.sym(String, c, SCon{'"', SNil{}}, ec) : {SCon{'"', String.append(y, SCon{'"', SNil{}})} == SCon{'"', String.append(y, _)} : String}
  {==}

def strX.go(-q1: String, +x: String, -q2: String, -a: String, +y: String, -c: String, +es: {String.append(a, String.append(y, c)) == String.append(q1, String.append(x, q2)) : String},
  +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +ea: {a == SCon{'"', SNil{}} : String}, +ec: {c == SCon{'"', SNil{}} : String}, +hy: {ABNF.check(BK, CHARS, y) == True{} : Bool}) -> {ABNF.check(BK, CHARS, x) == True{} : Bool}:
  %snoc_cancel(y, x, '"', scon_tl('"', '"', String.append(y, SCon{'"', SNil{}}), String.append(x, SCon{'"', SNil{}}),
    Equal.trans(String, SCon{'"', String.append(y, SCon{'"', SNil{}})}, String.append(a, String.append(y, c)), SCon{'"', String.append(x, SCon{'"', SNil{}})}, quoteEq(a, c, y, ea, ec),
      Equal.trans(String, String.append(a, String.append(y, c)), String.append(q1, String.append(x, q2)), SCon{'"', String.append(x, SCon{'"', SNil{}})}, es, Equal.sym(String, SCon{'"', String.append(x, SCon{'"', SNil{}})}, String.append(q1, String.append(x, q2)), quoteEq(q1, q2, x, eq1, eq2)))))) : {ABNF.check(BK, CHARS, _) == True{} : Bool}
  hy

# The text between a string's quotation marks is a run of chars.
def strX(+q1: String, +x: String, +q2: String, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, ABNF.ref("string"), String.append(q1, String.append(x, q2))) == True{} : Bool}) -> {ABNF.check(BK, CHARS, x) == True{} : Bool}:
  seqE3({ABNF.check(BK, CHARS, x) == True{} : Bool}, BK, ABNF.ref("quotation-mark"), CHARS, ABNF.ref("quotation-mark"), String.append(q1, String.append(x, q2)), MBe("string", B_string, String.append(q1, String.append(x, q2)), {==}, hx), +a => +y => +c => +es => +ha => +hy => +hc =>
    strX.go(q1, x, q2, a, y, c, es, eq1, eq2, charIs(BK, '"', a, MBe("quotation-mark", ABNF.char('"'), a, {==}, ha)), charIs(BK, '"', c, MBe("quotation-mark", ABNF.char('"'), c, {==}, hc)), hy))

def qmE(+q: String, +h: {ABNF.matches(Laws.grammar, "quotation-mark", q) == True{} : Bool}) -> {q == SCon{'"', SNil{}} : String}:
  charIs(BK, '"', q, MBe("quotation-mark", ABNF.char('"'), q, {==}, mt("quotation-mark", q, h)))

def strQ(-q1: String, +x: String, -q2: String, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(q1, String.append(x, q2)))) == Some{PR{RStr{x}, SNil{}}} : Maybe<&2, PR>}:
  %Equal.sym(String, q1, SCon{'"', SNil{}}, eq1) : {pvc(MV{}, skip_ws(String.append(_, String.append(x, q2)))) == Some{PR{RStr{x}, SNil{}}} : Maybe<&2, PR>}
  %Equal.sym(String, q2, SCon{'"', SNil{}}, eq2) : {pvc(MV{}, skip_ws(SCon{'"', String.append(x, _)})) == Some{PR{RStr{x}, SNil{}}} : Maybe<&2, PR>}
  cvStr.eq(x, hx)

def fin_null(+S: String, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{RNull{}, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}, -j: Js, +h: {Laws.load(S) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == Some{Unit{}} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %jR(S, j, RNull{}, u, e, wu, h) : {Laws.null(_) == Some{Unit{}} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == None{} : Maybe<List<&2, Js>>} & {Laws.object(_) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==}, {==})

def fin_true(+S: String, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{RBool{True{}}, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}, -j: Js, +h: {Laws.load(S) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == Some{True{}} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %jR(S, j, RBool{True{}}, u, e, wu, h) : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == Some{True{}} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == None{} : Maybe<List<&2, Js>>} & {Laws.object(_) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==}, {==})

def fin_false(+S: String, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{RBool{False{}}, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}, -j: Js, +h: {Laws.load(S) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == Some{False{}} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %jR(S, j, RBool{False{}}, u, e, wu, h) : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == Some{False{}} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == None{} : Maybe<List<&2, Js>>} & {Laws.object(_) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==}, {==})

def fin_number(+s: String, +S: String, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{RNum{s}, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}, -j: Js, +h: {Laws.load(S) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == Some{s} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %jR(S, j, RNum{s}, u, e, wu, h) : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == Some{s} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == None{} : Maybe<List<&2, Js>>} & {Laws.object(_) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==}, {==})

def fin_string(+s: String, +S: String, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{RStr{s}, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}, -j: Js, +h: {Laws.load(S) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == Some{Laws.decode(s)} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %jR(S, j, RStr{s}, u, e, wu, h) : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == Some{Laws.decode(s)} : Maybe<String>} & {Laws.array(_) == None{} : Maybe<List<&2, Js>>} & {Laws.object(_) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==}, {==})

def fin_anil(+S: String, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{RArr{[]}, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}, -j: Js, +h: {Laws.load(S) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{[]} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %jR(S, j, RArr{[]}, u, e, wu, h) : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == Some{[]} : Maybe<List<&2, Js>>} & {Laws.object(_) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==}, {==})

def fin_onil(+S: String, +u: String, +e: {pvc(MV{}, skip_ws(S)) == Some{PR{RObj{[]}, u}} : Maybe<&2, PR>}, +wu: {wsall(u) == True{} : Bool}, -j: Js, +h: {Laws.load(S) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{[]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %jR(S, j, RObj{[]}, u, e, wu, h) : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == None{} : Maybe<List<&2, Js>>} & {Laws.object(_) == Some{[]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==}, {==})

def lnull(+w1: String, +w2: String, +w3: String, +h1: {ABNF.matches(Laws.grammar, "ws", w1) == True{} : Bool}, +h2: {ABNF.matches(Laws.grammar, "null", w2) == True{} : Bool}, +h3: {ABNF.matches(Laws.grammar, "ws", w3) == True{} : Bool}, -j: Js, +h: {Laws.load(String.append(w1, String.append(w2, w3))) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == Some{Unit{}} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  fin_null(String.append(w1, String.append(w2, w3)), w3,
    wrapWs(w1, w2, w3, wsM(w1, h1), wsM(w3, h3), RNull{}, SNil{}, litE(w2, "null", RNull{}, csE(BK, "null", w2, MBe("null", ABNF.string.case_sensitive("null"), w2, {==}, mt("null", w2, h2))), {==}), {==}),
    wsM(w3, h3), j, h)

def Laws.load.null(w1, w2, w3, h1, h2, h3, j, h):
  lnull(w1, w2, w3, h1, h2, h3, j, h)

def ltrue(+w1: String, +w2: String, +w3: String, +h1: {ABNF.matches(Laws.grammar, "ws", w1) == True{} : Bool}, +h2: {ABNF.matches(Laws.grammar, "true", w2) == True{} : Bool}, +h3: {ABNF.matches(Laws.grammar, "ws", w3) == True{} : Bool}, -j: Js, +h: {Laws.load(String.append(w1, String.append(w2, w3))) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == Some{True{}} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  fin_true(String.append(w1, String.append(w2, w3)), w3,
    wrapWs(w1, w2, w3, wsM(w1, h1), wsM(w3, h3), RBool{True{}}, SNil{}, litE(w2, "true", RBool{True{}}, csE(BK, "true", w2, MBe("true", ABNF.string.case_sensitive("true"), w2, {==}, mt("true", w2, h2))), {==}), {==}),
    wsM(w3, h3), j, h)

def Laws.load.true(w1, w2, w3, h1, h2, h3, j, h):
  ltrue(w1, w2, w3, h1, h2, h3, j, h)

def lfalse(+w1: String, +w2: String, +w3: String, +h1: {ABNF.matches(Laws.grammar, "ws", w1) == True{} : Bool}, +h2: {ABNF.matches(Laws.grammar, "false", w2) == True{} : Bool}, +h3: {ABNF.matches(Laws.grammar, "ws", w3) == True{} : Bool}, -j: Js, +h: {Laws.load(String.append(w1, String.append(w2, w3))) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == Some{False{}} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  fin_false(String.append(w1, String.append(w2, w3)), w3,
    wrapWs(w1, w2, w3, wsM(w1, h1), wsM(w3, h3), RBool{False{}}, SNil{}, litE(w2, "false", RBool{False{}}, csE(BK, "false", w2, MBe("false", ABNF.string.case_sensitive("false"), w2, {==}, mt("false", w2, h2))), {==}), {==}),
    wsM(w3, h3), j, h)

def Laws.load.false(w1, w2, w3, h1, h2, h3, j, h):
  lfalse(w1, w2, w3, h1, h2, h3, j, h)

def lnum(+w1: String, +w2: String, +w3: String, +h1: {ABNF.matches(Laws.grammar, "ws", w1) == True{} : Bool}, +h2: {ABNF.matches(Laws.grammar, "number", w2) == True{} : Bool}, +h3: {ABNF.matches(Laws.grammar, "ws", w3) == True{} : Bool}, -j: Js, +h: {Laws.load(String.append(w1, String.append(w2, w3))) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == Some{w2} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  fin_number(w2, String.append(w1, String.append(w2, w3)), w3,
    wrapWs(w1, w2, w3, wsM(w1, h1), wsM(w3, h3), RNum{w2}, SNil{}, rtNum(w2, numokOf(w2, MBe("number", B_number, w2, {==}, mt("number", w2, h2)))), {==}),
    wsM(w3, h3), j, h)

def Laws.load.number(w1, w2, w3, h1, h2, h3, j, h):
  lnum(w1, w2, w3, h1, h2, h3, j, h)

def lstr.e(+w1: String, +q1: String, +x: String, +q2: String, +w3: String, +hw1: {wsall(w1) == True{} : Bool}, +hw3: {wsall(w3) == True{} : Bool}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(w1, String.append(q1, String.append(x, String.append(q2, w3)))))) == Some{PR{RStr{x}, w3}} : Maybe<&2, PR>}:
  %app_congl(w1, String.append(String.append(q1, String.append(x, q2)), w3), String.append(q1, String.append(x, String.append(q2, w3))), Equal.trans(String, String.append(String.append(q1, String.append(x, q2)), w3), String.append(q1, String.append(String.append(x, q2), w3)), String.append(q1, String.append(x, String.append(q2, w3))), app3(q1, String.append(x, q2), w3), app_congl(q1, String.append(String.append(x, q2), w3), String.append(x, String.append(q2, w3)), app3(x, q2, w3)))) : {pvc(MV{}, skip_ws(_)) == Some{PR{RStr{x}, w3}} : Maybe<&2, PR>}
  wrapWs(w1, String.append(q1, String.append(x, q2)), w3, hw1, hw3, RStr{x}, SNil{}, strQ(q1, x, q2, eq1, eq2, hx), {==})

def lstr(+w1: String, +q1: String, +x: String, +q2: String, +w3: String, +h1: {ABNF.matches(Laws.grammar, "ws", w1) == True{} : Bool}, +hq1: {ABNF.matches(Laws.grammar, "quotation-mark", q1) == True{} : Bool}, +hq2: {ABNF.matches(Laws.grammar, "quotation-mark", q2) == True{} : Bool},
  +hx: {ABNF.matches(Laws.grammar, "string", String.append(q1, String.append(x, q2))) == True{} : Bool}, +h3: {ABNF.matches(Laws.grammar, "ws", w3) == True{} : Bool}, -j: Js, +h: {Laws.load(String.append(w1, String.append(q1, String.append(x, String.append(q2, w3))))) == Some{j} : Maybe<Js>})
  -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == Some{Laws.decode(x)} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  fin_string(x, String.append(w1, String.append(q1, String.append(x, String.append(q2, w3)))), w3,
    lstr.e(w1, q1, x, q2, w3, wsM(w1, h1), wsM(w3, h3), qmE(q1, hq1), qmE(q2, hq2), strX(q1, x, q2, qmE(q1, hq1), qmE(q2, hq2), mt("string", String.append(q1, String.append(x, q2)), hx))),
    wsM(w3, h3), j, h)

def Laws.load.string(w1, q1, x, q2, w3, h1, hq1, hq2, hx, h3, j, h):
  lstr(w1, q1, x, q2, w3, h1, hq1, hq2, hx, h3, j, h)

def lanil(+b: String, +e: String, +hb: {ABNF.matches(Laws.grammar, "begin-array", b) == True{} : Bool}, +he: {ABNF.matches(Laws.grammar, "end-array", e) == True{} : Bool}, -j: Js, +h: {Laws.load(String.append(b, e)) == Some{j} : Maybe<Js>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{[]} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  fin_anil(String.append(b, e), str_tl(skip_ws(e)), cvArr0.eq(b, e, tokM("begin-array", '[', b, {==}, {==}, hb), tokM("end-array", ']', e, {==}, {==}, he)), tokW(']', e, tokM("end-array", ']', e, {==}, {==}, he)), j, h)

def lonil(+b: String, +e: String, +hb: {ABNF.matches(Laws.grammar, "begin-object", b) == True{} : Bool}, +he: {ABNF.matches(Laws.grammar, "end-object", e) == True{} : Bool}, -j: Js, +h: {Laws.load(String.append(b, e)) == Some{j} : Maybe<Js>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{[]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  fin_onil(String.append(b, e), str_tl(skip_ws(e)), cvObj0.eq(b, e, tokM("begin-object", '{', b, {==}, {==}, hb), tokM("end-object", '}', e, {==}, {==}, he)), tokW('}', e, tokM("end-object", '}', e, {==}, {==}, he)), j, h)

def Laws.load.array.nil(b, e, hb, he, j, h):
  lanil(b, e, hb, he, j, h)

def Laws.load.object.nil(b, e, hb, he, j, h):
  lonil(b, e, hb, he, j, h)

def withV.c(-C: Type, +v: String, c: CR(CV{}, v), k: @r: Raw -> @u: String -> {pvc(MV{}, skip_ws(v)) == Some{PR{r, u}} : Maybe<&2, PR>} -> {wsall(u) == True{} : Bool} -> C) -> C:
  (r, u, e, w) = c
  k(r, u, e, w)

def withV.d(-C: Type, +v: String, p: &d: Nat -> {ABNF.check(ABNF.limit(d, Laws.grammar), ABNF.ref("value"), v) == True{} : Bool}, k: @r: Raw -> @u: String -> {pvc(MV{}, skip_ws(v)) == Some{PR{r, u}} : Maybe<&2, PR>} -> {wsall(u) == True{} : Bool} -> C) -> C:
  (d, hd) = p
  withV.c(C, v, Core(d, 0n, CV{}, v, hd), k)

# A value parses.
def withV(-C: Type, +v: String, +hv: {ABNF.matches(Laws.grammar, "value", v) == True{} : Bool}, k: @r: Raw -> @u: String -> {pvc(MV{}, skip_ws(v)) == Some{PR{r, u}} : Maybe<&2, PR>} -> {wsall(u) == True{} : Bool} -> C) -> C:
  withV.d(C, v, ABNF.full.elim(Laws.grammar, ABNF.ref("value"), v, mt("value", v, hv)), k)

def arrOneE(+b: String, +v: String, +e: String, +hb: {tokb('[', b) == True{} : Bool}, +he: {tokb(']', e) == True{} : Bool}, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(b, String.append(v, e)))) == Some{PR{RArr{[r1]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}:
  %append_nil(v) : {pvc(MV{}, skip_ws(String.append(b, String.append(_, e)))) == Some{PR{RArr{[r1]}, str_tl(skip_ws(e))}} : Maybe<&2, PR>}
  cvArr.eq(b, v, SNil{}, e, hb, r1, u1, e1, w1, RArr{[]}, str_tl(skip_ws(e)), ca0.eq(e, he), tokW(']', e, he))

def arrOneFin(+r1: Raw, +hr: IsTrue(wf(RArr{[r1]})), +hv: IsTrue(wf(r1)), -j: Js, -jv: Js, +ej: {J{RArr{[r1]}, hr} == j : Js}, +ejv: {J{r1, hv} == jv : Js}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{[jv]} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %ej : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == Some{[jv]} : Maybe<List<&2, Js>>} & {Laws.object(_) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  %ejv : {Laws.null(J{RArr{[r1]}, hr}) == None{} : Maybe<Unit>} & {Laws.bool(J{RArr{[r1]}, hr}) == None{} : Maybe<Bool>} & {Laws.number(J{RArr{[r1]}, hr}) == None{} : Maybe<String>} & {Laws.string(J{RArr{[r1]}, hr}) == None{} : Maybe<String>} & {Laws.array(J{RArr{[r1]}, hr}) == Some{[_]} : Maybe<List<&2, Js>>} & {Laws.object(J{RArr{[r1]}, hr}) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, Equal.cong(Js, Maybe<List<&2, Js>>, z => Some{[z]}, J{r1, andT1(wf(r1), wf(RArr{[]}), hr)}, J{r1, hv}, j_irr(r1, andT1(wf(r1), wf(RArr{[]}), hr), hv)), {==})

def laOne.go(+b: String, +v: String, +e: String, +hb: {tokb('[', b) == True{} : Bool}, +he: {tokb(']', e) == True{} : Bool}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, e))) == Some{j} : Maybe<Js>},
  +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{[jv]} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  arrOneFin(r1, istrue(wf(RArr{[r1]}), wfOf(skip_ws(String.append(b, String.append(v, e))), RArr{[r1]}, str_tl(skip_ws(e)), arrOneE(b, v, e, hb, he, r1, u1, e1, w1))), istrue(wf(r1), wfOf(skip_ws(v), r1, u1, e1)), j, jv,
    jR(String.append(b, String.append(v, e)), j, RArr{[r1]}, str_tl(skip_ws(e)), arrOneE(b, v, e, hb, he, r1, u1, e1, w1), tokW(']', e, he), h), jR(v, jv, r1, u1, e1, w1, hjv))

def laOne(+b: String, +v: String, +e: String, +hb: {ABNF.matches(Laws.grammar, "begin-array", b) == True{} : Bool}, +hv: {ABNF.matches(Laws.grammar, "value", v) == True{} : Bool}, +he: {ABNF.matches(Laws.grammar, "end-array", e) == True{} : Bool}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, e))) == Some{j} : Maybe<Js>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{[jv]} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  withV({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{[jv]} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, v, hv, +r1 => +u1 => +e1 => +w1 =>
    laOne.go(b, v, e, tokM("begin-array", '[', b, {==}, {==}, hb), tokM("end-array", ']', e, {==}, {==}, he), jv, hjv, j, h, r1, u1, e1, w1))

def Laws.load.array.one(b, v, e, hb, hv, he, jv, hjv, j, h):
  laOne(b, v, e, hb, hv, he, jv, hjv, j, h)

# An object's text from its opening bracket, given its first member's parts.
def objText(+b: String, +x: String, +n: String, +v: String, +RE: String, +hb: {tokb('{', b) == True{} : Bool}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool},
  -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, -rO: Raw, +uO: String, +eO: {pvc(MO{}, skip_ws(RE)) == Some{PR{rO, uO}} : Maybe<&2, PR>}, +wO: {wsall(uO) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(b, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})}))) == Some{PR{ocons1(x, r1, rO), uO}} : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(b, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})})), SCon{'{', String.append(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})})}, tokU('{', b, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})}, hb)) : {pv(1n+String.length(_), MV{}, _) == Some{PR{ocons1(x, r1, rO), uO}} : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})})), skip_ws(SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})}), WE(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})}, tokW('{', b, hb))) : {brk('}', _, w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})})), MM{}, w)) == Some{PR{ocons1(x, r1, rO), uO}} : Maybe<&2, PR>}
  extNil(MM{}, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})}, ocons1(x, r1, rO), uO, cmm.eq(x, n, v, RE, hx, hn, r1, u1, e1, w1, rO, uO, eO, wO), 1n+String.length(String.append(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})})), wO,
    leSuf(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, RE))})}))

# The text of a member's name, with its parts.
def keyText(+b: String, -k: String, +q1: String, +x: String, +q2: String, +T: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String})
  -> {String.append(b, SCon{'"', String.append(x, SCon{'"', T})}) == String.append(b, String.append(k, T)) : String}:
  %es : {String.append(b, SCon{'"', String.append(x, SCon{'"', T})}) == String.append(b, String.append(_, T)) : String}
  %Equal.sym(String, q1, SCon{'"', SNil{}}, eq1) : {String.append(b, SCon{'"', String.append(x, SCon{'"', T})}) == String.append(b, String.append(String.append(_, String.append(x, q2)), T)) : String}
  %Equal.sym(String, q2, SCon{'"', SNil{}}, eq2) : {String.append(b, SCon{'"', String.append(x, SCon{'"', T})}) == String.append(b, SCon{'"', String.append(String.append(x, _), T)}) : String}
  app_congl(b, SCon{'"', String.append(x, SCon{'"', T})}, SCon{'"', String.append(String.append(x, SCon{'"', SNil{}}), T)}, Equal.cong(String, String, z => SCon{'"', z}, String.append(x, SCon{'"', T}), String.append(String.append(x, SCon{'"', SNil{}}), T), Equal.sym(String, String.append(String.append(x, SCon{'"', SNil{}}), T), String.append(x, SCon{'"', T}), app3(x, SCon{'"', SNil{}}, T))))

def loOneE(+b: String, +k: String, +q1: String, +x: String, +q2: String, +n: String, +v: String, +e: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String},
  +hb: {tokb('{', b) == True{} : Bool}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool}, +he: {tokb('}', e) == True{} : Bool}, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(b, String.append(k, String.append(n, String.append(v, e)))))) == Some{PR{ocons1(x, r1, RObj{[]}), str_tl(skip_ws(e))}} : Maybe<&2, PR>}:
  %keyText(b, k, q1, x, q2, String.append(n, String.append(v, e)), es, eq1, eq2) : {pvc(MV{}, skip_ws(_)) == Some{PR{ocons1(x, r1, RObj{[]}), str_tl(skip_ws(e))}} : Maybe<&2, PR>}
  objText(b, x, n, v, e, hb, hx, hn, r1, u1, e1, w1, RObj{[]}, str_tl(skip_ws(e)), moZ.eq(e, he), tokW('}', e, he))

def kE(-k: String, +q1: String, +x: String, +q2: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(k)) == Some{PR{RStr{x}, SNil{}}} : Maybe<&2, PR>}:
  %es : {pvc(MV{}, skip_ws(_)) == Some{PR{RStr{x}, SNil{}}} : Maybe<&2, PR>}
  strQ(q1, x, q2, eq1, eq2, hx)

def nameEq(+x: String, +hk: IsTrue(wf(RStr{x})), -jk: Js, +ej: {J{RStr{x}, hk} == jk : Js}, -name: String, +hname: {Laws.string(jk) == Some{name} : Maybe<String>}) -> {dec(x, DN{}, None{}) == name : String}:
  some_inj(&1, String, dec(x, DN{}, None{}), name, Equal.trans(Maybe<String>, Some{dec(x, DN{}, None{})}, Laws.string(jk), Some{name}, Equal.cong(Js, Maybe<String>, z => Laws.string(z), J{RStr{x}, hk}, jk, ej), hname))

def objOneFin(+x: String, +r1: Raw, +hr: IsTrue(wf(RObj{[RMem{x, r1}]})), +hv: IsTrue(wf(r1)), -j: Js, -jv: Js, -name: String, +ej: {J{RObj{[RMem{x, r1}]}, hr} == j : Js}, +ejv: {J{r1, hv} == jv : Js}, +en: {dec(x, DN{}, None{}) == name : String}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{[(name, jv)]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %ej : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == None{} : Maybe<List<&2, Js>>} & {Laws.object(_) == Some{[(name, jv)]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  %ejv : {Laws.null(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<Unit>} & {Laws.bool(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<Bool>} & {Laws.number(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<String>} & {Laws.string(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<String>} & {Laws.array(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<List<&2, Js>>} & {Laws.object(J{RObj{[RMem{x, r1}]}, hr}) == Some{[(name, _)]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  %en : {Laws.null(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<Unit>} & {Laws.bool(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<Bool>} & {Laws.number(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<String>} & {Laws.string(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<String>} & {Laws.array(J{RObj{[RMem{x, r1}]}, hr}) == None{} : Maybe<List<&2, Js>>} & {Laws.object(J{RObj{[RMem{x, r1}]}, hr}) == Some{[(_, J{r1, hv})]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==}, Equal.cong(Js, Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Some{[(dec(x, DN{}, None{}), z)]}, J{r1, andT1(wf(r1), wf(RObj{[]}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{[]})), hr))}, J{r1, hv}, j_irr(r1, andT1(wf(r1), wf(RObj{[]}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{[]})), hr)), hv)))

def loOne.go(+b: String, +k: String, +n: String, +v: String, +e: String, +hb: {tokb('{', b) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool}, +he: {tokb('}', e) == True{} : Bool},
  +q1: String, +x: String, +q2: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool},
  -jk: Js, +hjk: {Laws.load(k) == Some{jk} : Maybe<Js>}, -name: String, +hname: {Laws.string(jk) == Some{name} : Maybe<String>}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -j: Js, +h: {Laws.load(String.append(b, String.append(k, String.append(n, String.append(v, e))))) == Some{j} : Maybe<Js>},
  +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{[(name, jv)]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  objOneFin(x, r1, istrue(wf(RObj{[RMem{x, r1}]}), wfOf(skip_ws(String.append(b, String.append(k, String.append(n, String.append(v, e))))), RObj{[RMem{x, r1}]}, str_tl(skip_ws(e)), loOneE(b, k, q1, x, q2, n, v, e, es, eq1, eq2, hb, hx, hn, he, r1, u1, e1, w1))), istrue(wf(r1), wfOf(skip_ws(v), r1, u1, e1)), j, jv, name,
    jR(String.append(b, String.append(k, String.append(n, String.append(v, e)))), j, RObj{[RMem{x, r1}]}, str_tl(skip_ws(e)), loOneE(b, k, q1, x, q2, n, v, e, es, eq1, eq2, hb, hx, hn, he, r1, u1, e1, w1), tokW('}', e, he), h), jR(v, jv, r1, u1, e1, w1, hjv),
    nameEq(x, istrue(wf(RStr{x}), wfOf(skip_ws(k), RStr{x}, SNil{}, kE(k, q1, x, q2, es, eq1, eq2, hx))), jk, jR(k, jk, RStr{x}, SNil{}, kE(k, q1, x, q2, es, eq1, eq2, hx), {==}, hjk), name, hname))

def loOne(+b: String, +k: String, +n: String, +v: String, +e: String, +hb: {ABNF.matches(Laws.grammar, "begin-object", b) == True{} : Bool}, +hk: {ABNF.matches(Laws.grammar, "string", k) == True{} : Bool}, +hn: {ABNF.matches(Laws.grammar, "name-separator", n) == True{} : Bool}, +hv: {ABNF.matches(Laws.grammar, "value", v) == True{} : Bool}, +he: {ABNF.matches(Laws.grammar, "end-object", e) == True{} : Bool},
  -jk: Js, +hjk: {Laws.load(k) == Some{jk} : Maybe<Js>}, -name: String, +hname: {Laws.string(jk) == Some{name} : Maybe<String>}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -j: Js, +h: {Laws.load(String.append(b, String.append(k, String.append(n, String.append(v, e))))) == Some{j} : Maybe<Js>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{[(name, jv)]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  seqE3({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{[(name, jv)]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, BK, ABNF.ref("quotation-mark"), CHARS, ABNF.ref("quotation-mark"), k, MBe("string", B_string, k, {==}, mt("string", k, hk)), +q1 => +x => +q2 => +es => +h1 => +hx => +h3 =>
    withV({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{[(name, jv)]} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, v, hv, +r1 => +u1 => +e1 => +w1 =>
      loOne.go(b, k, n, v, e, tokM("begin-object", '{', b, {==}, {==}, hb), tokM("name-separator", ':', n, {==}, {==}, hn), tokM("end-object", '}', e, {==}, {==}, he),
        q1, x, q2, es, charIs(BK, '"', q1, MBe("quotation-mark", ABNF.char('"'), q1, {==}, h1)), charIs(BK, '"', q2, MBe("quotation-mark", ABNF.char('"'), q2, {==}, h3)), hx,
        jk, hjk, name, hname, jv, hjv, j, h, r1, u1, e1, w1)))

def Laws.load.object.one(b, k, n, v, e, hb, hk, hn, hv, he, jk, hjk, name, hname, jv, hjv, j, h):
  loOne(b, k, n, v, e, hb, hk, hn, hv, he, jk, hjk, name, hname, jv, hjv, j, h)

def emptyAbs(-C: Type, +h: {False{} == True{} : Bool}) -> C:
  Empty.absurd(C, false_ne_true(h))

def mkInv(-C: Type, +r: Raw, b: Bool, +e: {wf(r) == b : Bool}, -j: Js, +h: {mk(r, b, e) == Some{j} : Maybe<Js>}, k: @hq: IsTrue(wf(r)) -> {J{r, hq} == j : Js} -> C) -> C:
  match b:
    case True{}:
      k(istrue(wf(r), e), some_inj(&1, Js, J{r, istrue(wf(r), e)}, j, h))
    case False{}:
      Empty.absurd(C, none_ne_some(&1, Js, j, h))

def finInv2(-C: Type, +q: PR, b: Bool, +eb: {String.is_empty(skip_ws(prt(q))) == b : Bool}, -j: Js, +h: {fin2(prr(q), b) == Some{j} : Maybe<Js>}, k: {String.is_empty(skip_ws(prt(q))) == True{} : Bool} -> @hq: IsTrue(wf(prr(q))) -> {J{prr(q), hq} == j : Js} -> C) -> C:
  match b:
    case True{}:
      mkInv(C, prr(q), wf(prr(q)), {==}, j, h, k(eb))
    case False{}:
      Empty.absurd(C, none_ne_some(&1, Js, j, h))

# What a successful load read.
def finInv(-C: Type, m: Maybe<&2, PR>, -j: Js, +h: {fin(m) == Some{j} : Maybe<Js>}, k: @q: PR -> {m == Some{q} : Maybe<&2, PR>} -> {String.is_empty(skip_ws(prt(q))) == True{} : Bool} -> @hq: IsTrue(wf(prr(q))) -> {J{prr(q), hq} == j : Js} -> C) -> C:
  match m:
    case None{}:
      Empty.absurd(C, none_ne_some(&1, Js, j, h))
    case Some{+q}:
      finInv2(C, q, String.is_empty(skip_ws(prt(q))), {==}, j, h, k(q, {==}))

def aconsInv(-C: Type, -x: Raw, m: Maybe<&2, PR>, -q: PR, +h: {acons(x, m) == Some{q} : Maybe<&2, PR>}, k: @p: PR -> {m == Some{p} : Maybe<&2, PR>} -> {PR{acons1(x, prr(p)), prt(p)} == q : PR} -> C) -> C:
  match m:
    case None{}:
      Empty.absurd(C, none_ne_some(&2, PR, q, h))
    case Some{+p}:
      k(p, {==}, some_inj(&2, PR, PR{acons1(x, prr(p)), prt(p)}, q, h))

def oconsInv(-C: Type, -k: String, -x: Raw, m: Maybe<&2, PR>, -q: PR, +h: {ocons(k, x, m) == Some{q} : Maybe<&2, PR>}, kk: @p: PR -> {m == Some{p} : Maybe<&2, PR>} -> {PR{ocons1(k, x, prr(p)), prt(p)} == q : PR} -> C) -> C:
  match m:
    case None{}:
      Empty.absurd(C, none_ne_some(&2, PR, q, h))
    case Some{+p}:
      kk(p, {==}, some_inj(&2, PR, PR{ocons1(k, x, prr(p)), prt(p)}, q, h))

# A value and what MA reads after it.
def XInv(-C: Type, +F: Nat, +S: String, m: Maybe<&2, PR>, +em: {pv(F, MV{}, S) == m : Maybe<&2, PR>}, -q: PR, +h: {Maybe.bind(&2, PR, PR, m, +p => acons(prr(p), pv(F, MA{}, skip_ws(prt(p))))) == Some{q} : Maybe<&2, PR>},
  k: @p1: PR -> {pv(F, MV{}, S) == Some{p1} : Maybe<&2, PR>} -> @p2: PR -> {pv(F, MA{}, skip_ws(prt(p1))) == Some{p2} : Maybe<&2, PR>} -> {PR{acons1(prr(p1), prr(p2)), prt(p2)} == q : PR} -> C) -> C:
  match m:
    case None{}:
      Empty.absurd(C, none_ne_some(&2, PR, q, h))
    case Some{+p1}:
      aconsInv(C, prr(p1), pv(F, MA{}, skip_ws(prt(p1))), q, h, k(p1, em))

def XEq(+F: Nat, +S: String, -p1: PR, -p2: PR, +e1: {pv(F, MV{}, S) == Some{p1} : Maybe<&2, PR>}, +e2: {pv(F, MA{}, skip_ws(prt(p1))) == Some{p2} : Maybe<&2, PR>})
  -> {Maybe.bind(&2, PR, PR, pv(F, MV{}, S), +p => acons(prr(p), pv(F, MA{}, skip_ws(prt(p))))) == Some{PR{acons1(prr(p1), prr(p2)), prt(p2)}} : Maybe<&2, PR>}:
  %Equal.sym(Maybe<&2, PR>, pv(F, MV{}, S), Some{p1}, e1) : {Maybe.bind(&2, PR, PR, _, +p => acons(prr(p), pv(F, MA{}, skip_ws(prt(p))))) == Some{PR{acons1(prr(p1), prr(p2)), prt(p2)}} : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, pv(F, MA{}, skip_ws(prt(p1))), Some{p2}, e2) : {acons(prr(p1), _) == Some{PR{acons1(prr(p1), prr(p2)), prt(p2)}} : Maybe<&2, PR>}
  {==}

def prEta(p: PR) -> {PR{prr(p), prt(p)} == p : PR}:
  match p:
    case PR{r, t}:
      {==}

def mono.go(+f: Nat, +m: Md, +S: String, res: Maybe<&2, PR>, E: EXT(m, res, S, f), -p: PR, +e: {res == Some{p} : Maybe<&2, PR>}, +hf: {fol(prt(p)) == True{} : Bool}, +f2: Nat, +hl: {le(f, f2) == True{} : Bool}) -> {pv(f2, m, S) == Some{p} : Maybe<&2, PR>}:
  match res:
    case None{}:
      Empty.absurd({pv(f2, m, S) == Some{p} : Maybe<&2, PR>}, none_ne_some(&2, PR, p, e))
    case Some{+p0}:
      %some_inj(&2, PR, p0, p, e) : {pv(f2, m, S) == Some{_} : Maybe<&2, PR>}
      %prEta(p0) : {pv(f2, m, S) == Some{_} : Maybe<&2, PR>}
      %append_nil(S) : {pv(f2, m, _) == Some{PR{prr(p0), prt(p0)}} : Maybe<&2, PR>}
      %append_nil(prt(p0)) : {pv(f2, m, String.append(S, SNil{})) == Some{PR{prr(p0), _}} : Maybe<&2, PR>}
      E(SNil{}, f2, Equal.trans(Bool, fol(String.append(prt(p0), SNil{})), fol(prt(p)), True{}, Equal.trans(Bool, fol(String.append(prt(p0), SNil{})), fol(prt(p0)), fol(prt(p)), Equal.cong(String, Bool, z => fol(z), String.append(prt(p0), SNil{}), prt(p0), append_nil(prt(p0))), Equal.cong(PR, Bool, z => fol(prt(z)), p0, p, some_inj(&2, PR, p0, p, e))), hf), hl)

# A parse with some fuel gives the same result with more.
def mono(+f: Nat, +m: Md, +S: String, -p: PR, +e: {pv(f, m, S) == Some{p} : Maybe<&2, PR>}, +hf: {fol(prt(p)) == True{} : Bool}, +f2: Nat, +hl: {le(f, f2) == True{} : Bool}) -> {pv(f2, m, S) == Some{p} : Maybe<&2, PR>}:
  mono.go(f, m, S, pv(f, m, S), Ext(f, m, S), p, e, hf, f2, hl)

def brkNot0(f: Nat, +S: String, -kc: String -> Maybe<&2, PR>, -ko: String -> Maybe<&2, PR>, -p: PR, +e: {pv(f, MV{}, S) == Some{p} : Maybe<&2, PR>}) -> {brk(']', S, kc, ko) == ko(S) : Maybe<&2, PR>}:
  %append_nil(S) : {brk(']', _, kc, ko) == ko(_) : Maybe<&2, PR>}
  brkNot.go(f, S, SNil{}, kc, ko, p, e)

def tokFol(+s: String, +X: String, +hs: {tokb(',', s) == True{} : Bool}) -> {fol(String.append(s, X)) == True{} : Bool}:
  %WI(s) : {fol(String.append(_, X)) == True{} : Bool}
  %Equal.sym(String, String.append(String.append(wsp(s), skip_ws(s)), X), String.append(wsp(s), String.append(skip_ws(s), X)), app3(wsp(s), skip_ws(s), X)) : {fol(_) == True{} : Bool}
  %Equal.sym(String, skip_ws(s), SCon{',', str_tl(skip_ws(s))}, tokU0(',', s, hs)) : {fol(String.append(wsp(s), String.append(_, X))) == True{} : Bool}
  folWsPre(wsp(s), SCon{',', String.append(str_tl(skip_ws(s)), X)}, WIa(s), {==})

def leIns(B: String, +M: String, +R: String, +hM: {String.is_empty(M) == False{} : Bool}) -> {le(1n+String.length(String.append(B, R)), String.length(String.append(B, String.append(M, R)))) == True{} : Bool}:
  match B:
    case SNil{}:
      match M:
        case SNil{}:
          emptyAbs({le(1n+String.length(R), String.length(R)) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, hM))
        case SCon{c, M1}:
          leSuf(M1, R)
    case SCon{c, B1}:
      leIns(B1, M, R, hM)

def neVS(v: String, -s: String, +h: {String.is_empty(skip_ws(v)) == False{} : Bool}) -> {String.is_empty(String.append(v, s)) == False{} : Bool}:
  match v:
    case SNil{}:
      emptyAbs({String.is_empty(s) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case SCon{c, t}:
      {==}

def leCon(+B: String, +v: String, +s: String, +rest: String, +hv: {String.is_empty(skip_ws(v)) == False{} : Bool}) -> {le(1n+String.length(String.append(B, rest)), String.length(String.append(B, String.append(v, String.append(s, rest))))) == True{} : Bool}:
  %app3(v, s, rest) : {le(1n+String.length(String.append(B, rest)), String.length(String.append(B, _))) == True{} : Bool}
  leIns(B, String.append(v, s), rest, neVS(v, s, hv))

# Arrays with more elements
# =========================

# The parse of [v,rest: v, then what follows the comma.
def arrFull(+b: String, +v: String, +s: String, +rest: String, +hb: {tokb('[', b) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool})
  -> {pvc(MV{}, skip_ws(String.append(b, String.append(v, String.append(s, rest))))) == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(b, String.append(v, String.append(s, rest)))), SCon{'[', String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))}, tokU('[', b, String.append(v, String.append(s, rest)), hb)) : {pv(1n+String.length(_), MV{}, _) == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), skip_ws(String.append(v, String.append(s, rest))), WE(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)), tokW('[', b, hb))) : {brk(']', _, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, brk(']', skip_ws(String.append(v, String.append(s, rest))), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))), Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(String.append(v, String.append(s, rest)))), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p))))), brkNot(v, String.append(s, rest), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p))))), r1, u1, e1)) : {_ == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(v, String.append(s, rest))), String.append(skip_ws(v), String.append(s, rest)), skipApp(v, String.append(s, rest), mvNE(1n+String.length(skip_ws(v)), skip_ws(v), PR{r1, u1}, e1))) : {Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, _), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p))))) == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, String.append(skip_ws(v), String.append(s, rest))), Some{PR{r1, String.append(u1, String.append(s, rest))}}, extApply(MV{}, skip_ws(v), r1, u1, e1, String.append(s, rest), 1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), folWsPre(u1, String.append(s, rest), w1, tokFol(s, rest, hs)), leOcc(v, String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest))), str_tl(skip_ws(b)), String.append(s, rest), {==}))) : {Maybe.bind(&2, PR, PR, _, +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p))))) == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(u1, String.append(s, rest))), skip_ws(String.append(s, rest)), WE(u1, String.append(s, rest), w1)) : {acons(r1, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, _)) == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(s, rest)), SCon{',', String.append(str_tl(skip_ws(s)), rest)}, tokU(',', s, rest, hs)) : {acons(r1, pv(1n+String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, _)) == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(s)), rest)), skip_ws(rest), WE(str_tl(skip_ws(s)), rest, tokW(',', s, hs))) : {acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, _), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) == acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) : Maybe<&2, PR>}
  {==}

# The parse of [rest, when rest starts with a value.
def arrShort(+b: String, +rest: String, +hb: {tokb('[', b) == True{} : Bool}, f: Nat, -p0: PR, +e: {pv(f, MV{}, skip_ws(rest)) == Some{p0} : Maybe<&2, PR>}) -> {pvc(MV{}, skip_ws(String.append(b, rest))) == Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p))))) : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(b, rest)), SCon{'[', String.append(str_tl(skip_ws(b)), rest)}, tokU('[', b, rest, hb)) : {pv(1n+String.length(_), MV{}, _) == Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p))))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), rest)), skip_ws(rest), WE(str_tl(skip_ws(b)), rest, tokW('[', b, hb))) : {brk(']', _, w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p)))))) == Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p))))) : Maybe<&2, PR>}
  brkNot0(f, skip_ws(rest), w => Some{PR{RArr{[]}, w}}, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, w), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p))))), p0, e)

def arrConFin.a(+r1: Raw, +xs: List<&2, Raw>, +hq: IsTrue(wf(RArr{xs})), +hj: IsTrue(wf(RArr{r1 <> xs})), +hv: IsTrue(wf(r1)), -j: Js, -jv: Js, -jr: Js, -l: List<&2, Js>,
  +ej: {J{RArr{r1 <> xs}, hj} == j : Js}, +ejv: {J{r1, hv} == jv : Js}, +ejr: {J{RArr{xs}, hq} == jr : Js}, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %ej : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(_) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  %ejv : {Laws.null(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<Unit>} & {Laws.bool(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<Bool>} & {Laws.number(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<String>} & {Laws.string(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<String>} & {Laws.array(J{RArr{r1 <> xs}, hj}) == Some{_ <> l} : Maybe<List<&2, Js>>} & {Laws.object(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  %some_inj(&1, List<&2, Js>, wrapL(xs, hq), l, Equal.trans(Maybe<List<&2, Js>>, Some{wrapL(xs, hq)}, Laws.array(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Js>>, z => Laws.array(z), J{RArr{xs}, hq}, jr, ejr), hl)) : {Laws.null(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<Unit>} & {Laws.bool(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<Bool>} & {Laws.number(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<String>} & {Laws.string(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<String>} & {Laws.array(J{RArr{r1 <> xs}, hj}) == Some{J{r1, hv} <> _} : Maybe<List<&2, Js>>} & {Laws.object(J{RArr{r1 <> xs}, hj}) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==},
    Equal.trans(Maybe<List<&2, Js>>, Some{J{r1, andT1(wf(r1), wf(RArr{xs}), hj)} <> wrapL(xs, andT2(wf(r1), wf(RArr{xs}), hj))}, Some{J{r1, hv} <> wrapL(xs, andT2(wf(r1), wf(RArr{xs}), hj))}, Some{J{r1, hv} <> wrapL(xs, hq)},
      Equal.cong(Js, Maybe<List<&2, Js>>, z => Some{z <> wrapL(xs, andT2(wf(r1), wf(RArr{xs}), hj))}, J{r1, andT1(wf(r1), wf(RArr{xs}), hj)}, J{r1, hv}, j_irr(r1, andT1(wf(r1), wf(RArr{xs}), hj), hv)),
      Equal.cong(IsTrue(wf(RArr{xs})), Maybe<List<&2, Js>>, z => Some{J{r1, hv} <> wrapL(xs, z)}, andT2(wf(r1), wf(RArr{xs}), hj), hq, irr(wf(RArr{xs}), andT2(wf(r1), wf(RArr{xs}), hj), hq))),
    {==})

def arrConFin(+r1: Raw, rq: Raw, +hq: IsTrue(wf(rq)), +hj: IsTrue(wf(acons1(r1, rq))), +hv: IsTrue(wf(r1)), -j: Js, -jv: Js, -jr: Js, -l: List<&2, Js>,
  +ej: {J{acons1(r1, rq), hj} == j : Js}, +ejv: {J{r1, hv} == jv : Js}, +ejr: {J{rq, hq} == jr : Js}, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  match rq:
    case RNull{}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Js>, l, Equal.trans(Maybe<List<&2, Js>>, None{}, Laws.array(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Js>>, z => Laws.array(z), J{RNull{}, hq}, jr, ejr), hl)))
    case RBool{bb}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Js>, l, Equal.trans(Maybe<List<&2, Js>>, None{}, Laws.array(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Js>>, z => Laws.array(z), J{RBool{bb}, hq}, jr, ejr), hl)))
    case RNum{ns}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Js>, l, Equal.trans(Maybe<List<&2, Js>>, None{}, Laws.array(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Js>>, z => Laws.array(z), J{RNum{ns}, hq}, jr, ejr), hl)))
    case RStr{ss}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Js>, l, Equal.trans(Maybe<List<&2, Js>>, None{}, Laws.array(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Js>>, z => Laws.array(z), J{RStr{ss}, hq}, jr, ejr), hl)))
    case RArr{+xs}:
      arrConFin.a(r1, xs, hq, hj, hv, j, jv, jr, l, ej, ejv, ejr, hl)
    case RObj{ms}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Js>, l, Equal.trans(Maybe<List<&2, Js>>, None{}, Laws.array(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Js>>, z => Laws.array(z), J{RObj{ms}, hq}, jr, ejr), hl)))

def laCon.e(+b: String, +v: String, +s: String, +rest: String, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Js>, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, String.append(s, rest)))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool},
  +q: PR, +hemp: {String.is_empty(skip_ws(prt(q))) == True{} : Bool}, +hq: IsTrue(wf(prr(q))), +ejr: {J{prr(q), hq} == jr : Js}, +EF: {pvc(MV{}, skip_ws(String.append(b, String.append(v, String.append(s, rest))))) == Some{PR{acons1(r1, prr(q)), prt(q)}} : Maybe<&2, PR>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  arrConFin(r1, prr(q), hq, istrue(wf(acons1(r1, prr(q))), wfOf(skip_ws(String.append(b, String.append(v, String.append(s, rest)))), acons1(r1, prr(q)), prt(q), EF)), istrue(wf(r1), wfOf(skip_ws(v), r1, u1, e1)), j, jv, jr, l,
    jR(String.append(b, String.append(v, String.append(s, rest))), j, acons1(r1, prr(q)), prt(q), EF, emptyWs(prt(q), hemp), h), jR(v, jv, r1, u1, e1, w1, hjv), ejr, hl)

def laCon.d(+b: String, +v: String, +s: String, +rest: String, +hb: {tokb('[', b) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Js>, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, String.append(s, rest)))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +q: PR, +hemp: {String.is_empty(skip_ws(prt(q))) == True{} : Bool}, +hq: IsTrue(wf(prr(q))), +ejr: {J{prr(q), hq} == jr : Js},
  +p1: PR, +ep1: {pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, skip_ws(rest)) == Some{p1} : Maybe<&2, PR>}, +p2: PR, +ep2: {pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p1))) == Some{p2} : Maybe<&2, PR>}, +eqq: {PR{acons1(prr(p1), prr(p2)), prt(p2)} == q : PR}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  laCon.e(b, v, s, rest, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, q, hemp, hq, ejr,
    Equal.trans(Maybe<&2, PR>, pvc(MV{}, skip_ws(String.append(b, String.append(v, String.append(s, rest))))), acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))), Some{PR{acons1(r1, prr(q)), prt(q)}}, arrFull(b, v, s, rest, hb, hs, r1, u1, e1, w1), Equal.cong(Maybe<&2, PR>, Maybe<&2, PR>, z => acons(r1, z), Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p))))), Some{q},
      Equal.trans(Maybe<&2, PR>, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p))))), Some{PR{acons1(prr(p1), prr(p2)), prt(p2)}}, Some{q},
        XEq(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), skip_ws(rest), p1, p2,
          mono(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, skip_ws(rest), p1, ep1, Equal.trans(Bool, fol(prt(p1)), fol(String.append(prt(p1), SNil{})), True{}, Equal.cong(String, Bool, z => fol(z), prt(p1), String.append(prt(p1), SNil{}), Equal.sym(String, String.append(prt(p1), SNil{}), prt(p1), append_nil(prt(p1)))), folMA(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), prt(p1), SNil{}, p2, ep2)), String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), leCon(str_tl(skip_ws(b)), v, s, rest, mvNE(1n+String.length(skip_ws(v)), skip_ws(v), PR{r1, u1}, e1))),
          mono(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p1)), p2, ep2, Equal.trans(Bool, fol(prt(p2)), fol(prt(q)), True{}, Equal.cong(PR, Bool, z => fol(prt(z)), PR{acons1(prr(p1), prr(p2)), prt(p2)}, q, eqq), folWs(prt(q), emptyWs(prt(q), hemp))), String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), leCon(str_tl(skip_ws(b)), v, s, rest, mvNE(1n+String.length(skip_ws(v)), skip_ws(v), PR{r1, u1}, e1)))),
        Equal.cong(PR, Maybe<&2, PR>, z => Some{z}, PR{acons1(prr(p1), prr(p2)), prt(p2)}, q, eqq)))))

def laCon.c(+b: String, +v: String, +s: String, +rest: String, +hb: {tokb('[', b) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Js>, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, String.append(s, rest)))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, -p1f: PR, +e1f: {pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)) == Some{p1f} : Maybe<&2, PR>},
  +q: PR, +eq: {pvc(MV{}, skip_ws(String.append(b, rest))) == Some{q} : Maybe<&2, PR>}, +hemp: {String.is_empty(skip_ws(prt(q))) == True{} : Bool}, +hq: IsTrue(wf(prr(q))), +ejr: {J{prr(q), hq} == jr : Js}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  XInv({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, 1n+String.length(String.append(str_tl(skip_ws(b)), rest)), skip_ws(rest), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, skip_ws(rest)), {==}, q, Equal.trans(Maybe<&2, PR>, Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p))))), pvc(MV{}, skip_ws(String.append(b, rest))), Some{q}, Equal.sym(Maybe<&2, PR>, pvc(MV{}, skip_ws(String.append(b, rest))), Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MA{}, skip_ws(prt(p))))), arrShort(b, rest, hb, String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), p1f, e1f)), eq),
    +p1 => +ep1 => +p2 => +ep2 => +eqq => laCon.d(b, v, s, rest, hb, hs, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, q, hemp, hq, ejr, p1, ep1, p2, ep2, eqq))

def laCon.b(+b: String, +v: String, +s: String, +rest: String, +hb: {tokb('[', b) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Js>, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, String.append(s, rest)))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +hjr: {Laws.load(String.append(b, rest)) == Some{jr} : Maybe<Js>}, -p1f: PR, +e1f: {pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)) == Some{p1f} : Maybe<&2, PR>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  finInv({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, pvc(MV{}, skip_ws(String.append(b, rest))), jr, hjr, +q => +eq => +hemp => +hq => +ejr => laCon.c(b, v, s, rest, hb, hs, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, p1f, e1f, q, eq, hemp, hq, ejr))

def laCon.a(+b: String, +v: String, +s: String, +rest: String, +hb: {tokb('[', b) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Js>, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, String.append(s, rest)))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +hjr: {Laws.load(String.append(b, rest)) == Some{jr} : Maybe<Js>}, -qf: PR, +eqf: {acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))) == Some{qf} : Maybe<&2, PR>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  aconsInv({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p))))), qf, eqf, +p2f => +e2f => eq2f =>
    XInv({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), skip_ws(rest), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), {==}, p2f, e2f, +p1f => +e1f => p2x => e2x => eqx => laCon.b(b, v, s, rest, hb, hs, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, hjr, p1f, e1f)))

def laCon.go(+b: String, +v: String, +s: String, +rest: String, +hb: {tokb('[', b) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Js>, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, String.append(s, rest)))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +hjr: {Laws.load(String.append(b, rest)) == Some{jr} : Maybe<Js>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  finInv({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))), j, Equal.trans(Maybe<Js>, fin(acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p))))))), Laws.load(String.append(b, String.append(v, String.append(s, rest)))), Some{j}, Equal.cong(Maybe<&2, PR>, Maybe<Js>, z => fin(z), acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))), pvc(MV{}, skip_ws(String.append(b, String.append(v, String.append(s, rest))))), Equal.sym(Maybe<&2, PR>, pvc(MV{}, skip_ws(String.append(b, String.append(v, String.append(s, rest))))), acons(r1, Maybe.bind(&2, PR, PR, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MV{}, skip_ws(rest)), +p => acons(prr(p), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(v, String.append(s, rest)))), MA{}, skip_ws(prt(p)))))), arrFull(b, v, s, rest, hb, hs, r1, u1, e1, w1))), h),
    +qf => +eqf => hef => hqf => ejf => laCon.a(b, v, s, rest, hb, hs, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, hjr, qf, eqf))

def laCon(+b: String, +v: String, +s: String, +rest: String, +hb: {ABNF.matches(Laws.grammar, "begin-array", b) == True{} : Bool}, +hv: {ABNF.matches(Laws.grammar, "value", v) == True{} : Bool}, +hs: {ABNF.matches(Laws.grammar, "value-separator", s) == True{} : Bool}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, +hjr: {Laws.load(String.append(b, rest)) == Some{jr} : Maybe<Js>},
  -l: List<&2, Js>, +hl: {Laws.array(jr) == Some{l} : Maybe<List<&2, Js>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(v, String.append(s, rest)))) == Some{j} : Maybe<Js>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  withV({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == Some{jv <> l} : Maybe<List<&2, Js>>} & {Laws.object(j) == None{} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, v, hv, +r1 => +u1 => +e1 => +w1 =>
    laCon.go(b, v, s, rest, tokM("begin-array", '[', b, {==}, {==}, hb), tokM("value-separator", ',', s, {==}, {==}, hs), jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, hjr))

def Laws.load.array.con(b, v, s, rest, hb, hv, hs, jv, hjv, jr, hjr, l, hl, j, h):
  laCon(b, v, s, rest, hb, hv, hs, jv, hjv, jr, hjr, l, hl, j, h)

# Objects with more members
# =========================

def lenPos(A: String, -c: Char, -Q: String) -> {String.length(String.append(A, SCon{c, Q})) == 1n+String.length(String.append(A, Q)) : Nat}:
  match A:
    case SNil{}:
      {==}
    case SCon{d, A1}:
      Equal.cong(Nat, Nat, z => 1n+z, String.length(String.append(A1, SCon{c, Q})), 1n+String.length(String.append(A1, Q)), lenPos(A1, c, Q))

def neQ(x: String, -W: String) -> {String.is_empty(String.append(x, SCon{'"', W})) == False{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def leConO(+B: String, +x: String, +n: String, +v: String, +s: String, +rest: String) -> {le(1n+String.length(String.append(B, rest)), String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})))) == True{} : Bool}:
  %Equal.trans(String, String.append(String.append(x, SCon{'"', String.append(n, String.append(v, s))}), rest), String.append(x, SCon{'"', String.append(String.append(n, String.append(v, s)), rest)}), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}),
    app3(x, SCon{'"', String.append(n, String.append(v, s))}, rest),
    app_congl(x, SCon{'"', String.append(String.append(n, String.append(v, s)), rest)}, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}, Equal.cong(String, String, z => SCon{'"', z}, String.append(String.append(n, String.append(v, s)), rest), String.append(n, String.append(v, String.append(s, rest))),
      Equal.trans(String, String.append(String.append(n, String.append(v, s)), rest), String.append(n, String.append(String.append(v, s), rest)), String.append(n, String.append(v, String.append(s, rest))), app3(n, String.append(v, s), rest), app_congl(n, String.append(String.append(v, s), rest), String.append(v, String.append(s, rest)), app3(v, s, rest)))))) : {le(1n+String.length(String.append(B, rest)), String.length(String.append(B, _))) == True{} : Bool}
  leIns(B, String.append(x, SCon{'"', String.append(n, String.append(v, s))}), rest, neQ(x, String.append(n, String.append(v, s))))

# The parse of a member and a comma, from the member's opening quote on.
def objMM(+B: String, +x: String, +n: String, +v: String, +s: String, +rest: String, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool})
  -> {pv(1n+String.length(String.append(B, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})})), MM{}, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})}) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}:
  %Equal.sym(Nat, String.length(String.append(B, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})})), 1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), lenPos(B, '"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))) : {pv(1n+_, MM{}, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})}) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, SP>, str_scan(String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}), SN{}), Some{SP{x, String.append(n, String.append(v, String.append(s, rest)))}}, strC(x, String.append(n, String.append(v, String.append(s, rest))), hx)) : {Maybe.bind(&2, SP, PR, _, +q => colon(skip_ws(spt(q)), w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MV{}, skip_ws(w)), +p => ocons(spa(q), prr(p), pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MO{}, skip_ws(prt(p))))))) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(n, String.append(v, String.append(s, rest)))), SCon{':', String.append(str_tl(skip_ws(n)), String.append(v, String.append(s, rest)))}, tokU(':', n, String.append(v, String.append(s, rest)), hn)) : {colon(_, w => Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MV{}, skip_ws(w)), +p => ocons(x, prr(p), pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MO{}, skip_ws(prt(p)))))) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(n)), String.append(v, String.append(s, rest)))), skip_ws(String.append(v, String.append(s, rest))), WE(str_tl(skip_ws(n)), String.append(v, String.append(s, rest)), tokW(':', n, hn))) : {Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MV{}, _), +p => ocons(x, prr(p), pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MO{}, skip_ws(prt(p))))) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(v, String.append(s, rest))), String.append(skip_ws(v), String.append(s, rest)), skipApp(v, String.append(s, rest), mvNE(1n+String.length(skip_ws(v)), skip_ws(v), PR{r1, u1}, e1))) : {Maybe.bind(&2, PR, PR, pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MV{}, _), +p => ocons(x, prr(p), pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MO{}, skip_ws(prt(p))))) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(Maybe<&2, PR>, pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MV{}, String.append(skip_ws(v), String.append(s, rest))), Some{PR{r1, String.append(u1, String.append(s, rest))}}, extApply(MV{}, skip_ws(v), r1, u1, e1, String.append(s, rest), 1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), folWsPre(u1, String.append(s, rest), w1, tokFol(s, rest, hs)),
    leOcc(v, String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})), String.append(B, String.append(x, SCon{'"', n})), String.append(s, rest), Equal.trans(String, String.append(String.append(B, String.append(x, SCon{'"', n})), String.append(v, String.append(s, rest))), String.append(B, String.append(String.append(x, SCon{'"', n}), String.append(v, String.append(s, rest)))), String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})),
      app3(B, String.append(x, SCon{'"', n}), String.append(v, String.append(s, rest))), app_congl(B, String.append(String.append(x, SCon{'"', n}), String.append(v, String.append(s, rest))), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}), app3(x, SCon{'"', n}, String.append(v, String.append(s, rest)))))))) : {Maybe.bind(&2, PR, PR, _, +p => ocons(x, prr(p), pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MO{}, skip_ws(prt(p))))) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(u1, String.append(s, rest))), skip_ws(String.append(s, rest)), WE(u1, String.append(s, rest), w1)) : {ocons(x, r1, pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MO{}, _)) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(s, rest)), SCon{',', String.append(str_tl(skip_ws(s)), rest)}, tokU(',', s, rest, hs)) : {ocons(x, r1, pv(1n+String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MO{}, _)) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(s)), rest)), skip_ws(rest), WE(str_tl(skip_ws(s)), rest, tokW(',', s, hs))) : {ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, _)) == ocons(x, r1, pv(String.length(String.append(B, String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  {==}

def objFull(+b: String, +k: String, +q1: String, +x: String, +q2: String, +n: String, +v: String, +s: String, +rest: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String},
  +hb: {tokb('{', b) == True{} : Bool}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, -r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}) -> {pvc(MV{}, skip_ws(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest))))))) == ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}:
  %keyText(b, k, q1, x, q2, String.append(n, String.append(v, String.append(s, rest))), es, eq1, eq2) : {pvc(MV{}, skip_ws(_)) == ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(b, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})})), SCon{'{', String.append(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})})}, tokU('{', b, SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})}, hb)) : {pv(1n+String.length(_), MV{}, _) == ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})})), skip_ws(SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})}), WE(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})}, tokW('{', b, hb))) : {brk('}', _, w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), SCon{'"', String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))})})), MM{}, w)) == ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))) : Maybe<&2, PR>}
  objMM(str_tl(skip_ws(b)), x, n, v, s, rest, hx, hn, hs, r1, u1, e1, w1)

# The parse of {rest, when rest starts with a member.
def objShort(+b: String, +rest: String, +hb: {tokb('{', b) == True{} : Bool}, f: Nat, -p0: PR, +e: {pv(f, MM{}, skip_ws(rest)) == Some{p0} : Maybe<&2, PR>}) -> {pvc(MV{}, skip_ws(String.append(b, rest))) == pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MM{}, skip_ws(rest)) : Maybe<&2, PR>}:
  %Equal.sym(String, skip_ws(String.append(b, rest)), SCon{'{', String.append(str_tl(skip_ws(b)), rest)}, tokU('{', b, rest, hb)) : {pv(1n+String.length(_), MV{}, _) == pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MM{}, skip_ws(rest)) : Maybe<&2, PR>}
  %Equal.sym(String, skip_ws(String.append(str_tl(skip_ws(b)), rest)), skip_ws(rest), WE(str_tl(skip_ws(b)), rest, tokW('{', b, hb))) : {brk('}', _, w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MM{}, w)) == pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MM{}, skip_ws(rest)) : Maybe<&2, PR>}
  brkNotO.go(f, skip_ws(rest), w => Some{PR{RObj{[]}, w}}, w => pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MM{}, w), p0, e)

def objConFin.a(+x: String, +r1: Raw, +ms: List<&2, RMem>, +hq: IsTrue(wf(RObj{ms})), +hj: IsTrue(wf(RObj{RMem{x, r1} <> ms})), +hv: IsTrue(wf(r1)), -j: Js, -jv: Js, -jr: Js, -l: List<&2, Sigma<&2, &2, String, _ => Js>>, -name: String,
  +ej: {J{RObj{RMem{x, r1} <> ms}, hj} == j : Js}, +ejv: {J{r1, hv} == jv : Js}, +ejr: {J{RObj{ms}, hq} == jr : Js}, +hl: {Laws.object(jr) == Some{l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, +en: {dec(x, DN{}, None{}) == name : String}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  %ej : {Laws.null(_) == None{} : Maybe<Unit>} & {Laws.bool(_) == None{} : Maybe<Bool>} & {Laws.number(_) == None{} : Maybe<String>} & {Laws.string(_) == None{} : Maybe<String>} & {Laws.array(_) == None{} : Maybe<List<&2, Js>>} & {Laws.object(_) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  %ejv : {Laws.null(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<Unit>} & {Laws.bool(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<Bool>} & {Laws.number(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<String>} & {Laws.string(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<String>} & {Laws.array(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<List<&2, Js>>} & {Laws.object(J{RObj{RMem{x, r1} <> ms}, hj}) == Some{(name, _) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  %en : {Laws.null(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<Unit>} & {Laws.bool(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<Bool>} & {Laws.number(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<String>} & {Laws.string(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<String>} & {Laws.array(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<List<&2, Js>>} & {Laws.object(J{RObj{RMem{x, r1} <> ms}, hj}) == Some{(_, J{r1, hv}) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  %some_inj(&1, List<&2, Sigma<&2, &2, String, _ => Js>>, wrapO(ms, hq), l, Equal.trans(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, Some{wrapO(ms, hq)}, Laws.object(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Laws.object(z), J{RObj{ms}, hq}, jr, ejr), hl)) : {Laws.null(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<Unit>} & {Laws.bool(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<Bool>} & {Laws.number(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<String>} & {Laws.string(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<String>} & {Laws.array(J{RObj{RMem{x, r1} <> ms}, hj}) == None{} : Maybe<List<&2, Js>>} & {Laws.object(J{RObj{RMem{x, r1} <> ms}, hj}) == Some{(dec(x, DN{}, None{}), J{r1, hv}) <> _} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}
  ({==}, {==}, {==}, {==}, {==},
    Equal.trans(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, Some{(dec(x, DN{}, None{}), J{r1, andT1(wf(r1), wf(RObj{ms}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{ms})), hj))}) <> wrapO(ms, andT2(wf(r1), wf(RObj{ms}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{ms})), hj)))}, Some{(dec(x, DN{}, None{}), J{r1, hv}) <> wrapO(ms, andT2(wf(r1), wf(RObj{ms}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{ms})), hj)))}, Some{(dec(x, DN{}, None{}), J{r1, hv}) <> wrapO(ms, hq)},
      Equal.cong(Js, Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Some{(dec(x, DN{}, None{}), z) <> wrapO(ms, andT2(wf(r1), wf(RObj{ms}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{ms})), hj)))}, J{r1, andT1(wf(r1), wf(RObj{ms}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{ms})), hj))}, J{r1, hv}, j_irr(r1, andT1(wf(r1), wf(RObj{ms}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{ms})), hj)), hv)),
      Equal.cong(IsTrue(wf(RObj{ms})), Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Some{(dec(x, DN{}, None{}), J{r1, hv}) <> wrapO(ms, z)}, andT2(wf(r1), wf(RObj{ms}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{ms})), hj)), hq, irr(wf(RObj{ms}), andT2(wf(r1), wf(RObj{ms}), andT2(strok(x), Bool.and(wf(r1), wf(RObj{ms})), hj)), hq))))

def objConFin(+x: String, +r1: Raw, rq: Raw, +hq: IsTrue(wf(rq)), +hj: IsTrue(wf(ocons1(x, r1, rq))), +hv: IsTrue(wf(r1)), -j: Js, -jv: Js, -jr: Js, -l: List<&2, Sigma<&2, &2, String, _ => Js>>, -name: String,
  +ej: {J{ocons1(x, r1, rq), hj} == j : Js}, +ejv: {J{r1, hv} == jv : Js}, +ejr: {J{rq, hq} == jr : Js}, +hl: {Laws.object(jr) == Some{l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, +en: {dec(x, DN{}, None{}) == name : String}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  match rq:
    case RNull{}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Sigma<&2, &2, String, _ => Js>>, l, Equal.trans(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, None{}, Laws.object(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Laws.object(z), J{RNull{}, hq}, jr, ejr), hl)))
    case RBool{bb}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Sigma<&2, &2, String, _ => Js>>, l, Equal.trans(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, None{}, Laws.object(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Laws.object(z), J{RBool{bb}, hq}, jr, ejr), hl)))
    case RNum{ns}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Sigma<&2, &2, String, _ => Js>>, l, Equal.trans(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, None{}, Laws.object(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Laws.object(z), J{RNum{ns}, hq}, jr, ejr), hl)))
    case RStr{ss}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Sigma<&2, &2, String, _ => Js>>, l, Equal.trans(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, None{}, Laws.object(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Laws.object(z), J{RStr{ss}, hq}, jr, ejr), hl)))
    case RArr{xs}:
      Empty.absurd({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, none_ne_some(&1, List<&2, Sigma<&2, &2, String, _ => Js>>, l, Equal.trans(Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, None{}, Laws.object(jr), Some{l}, Equal.cong(Js, Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>, z => Laws.object(z), J{RArr{xs}, hq}, jr, ejr), hl)))
    case RObj{+ms}:
      objConFin.a(x, r1, ms, hq, hj, hv, j, jv, jr, l, name, ej, ejv, ejr, hl, en)

def loCon.e(+b: String, +k: String, +n: String, +v: String, +s: String, +rest: String, +hb: {tokb('{', b) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, +q1: String, +x: String, +q2: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, -jk: Js, +hjk: {Laws.load(k) == Some{jk} : Maybe<Js>}, -name: String, +hname: {Laws.string(jk) == Some{name} : Maybe<String>}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Sigma<&2, &2, String, _ => Js>>, +hl: {Laws.object(jr) == Some{l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest)))))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +q: PR, +hemp: {String.is_empty(skip_ws(prt(q))) == True{} : Bool}, +hq: IsTrue(wf(prr(q))), +ejr: {J{prr(q), hq} == jr : Js}, +EF: {pvc(MV{}, skip_ws(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest))))))) == Some{PR{ocons1(x, r1, prr(q)), prt(q)}} : Maybe<&2, PR>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  objConFin(x, r1, prr(q), hq, istrue(wf(ocons1(x, r1, prr(q))), wfOf(skip_ws(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest)))))), ocons1(x, r1, prr(q)), prt(q), EF)), istrue(wf(r1), wfOf(skip_ws(v), r1, u1, e1)), j, jv, jr, l, name,
    jR(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest))))), j, ocons1(x, r1, prr(q)), prt(q), EF, emptyWs(prt(q), hemp), h), jR(v, jv, r1, u1, e1, w1, hjv), ejr, hl,
    nameEq(x, istrue(wf(RStr{x}), wfOf(skip_ws(k), RStr{x}, SNil{}, kE(k, q1, x, q2, es, eq1, eq2, hx))), jk, jR(k, jk, RStr{x}, SNil{}, kE(k, q1, x, q2, es, eq1, eq2, hx), {==}, hjk), name, hname))

def loCon.c(+b: String, +k: String, +n: String, +v: String, +s: String, +rest: String, +hb: {tokb('{', b) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, +q1: String, +x: String, +q2: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, -jk: Js, +hjk: {Laws.load(k) == Some{jk} : Maybe<Js>}, -name: String, +hname: {Laws.string(jk) == Some{name} : Maybe<String>}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Sigma<&2, &2, String, _ => Js>>, +hl: {Laws.object(jr) == Some{l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest)))))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, -p1f: PR, +e1f: {pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest)) == Some{p1f} : Maybe<&2, PR>},
  +q: PR, +eq: {pvc(MV{}, skip_ws(String.append(b, rest))) == Some{q} : Maybe<&2, PR>}, +hemp: {String.is_empty(skip_ws(prt(q))) == True{} : Bool}, +hq: IsTrue(wf(prr(q))), +ejr: {J{prr(q), hq} == jr : Js}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  loCon.e(b, k, n, v, s, rest, hb, hn, hs, q1, x, q2, es, eq1, eq2, hx, jk, hjk, name, hname, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, q, hemp, hq, ejr,
    Equal.trans(Maybe<&2, PR>, pvc(MV{}, skip_ws(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest))))))), ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))), Some{PR{ocons1(x, r1, prr(q)), prt(q)}}, objFull(b, k, q1, x, q2, n, v, s, rest, es, eq1, eq2, hb, hx, hn, hs, r1, u1, e1, w1), Equal.cong(Maybe<&2, PR>, Maybe<&2, PR>, z => ocons(x, r1, z), pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest)), Some{q},
      mono(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MM{}, skip_ws(rest), q, Equal.trans(Maybe<&2, PR>, pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MM{}, skip_ws(rest)), pvc(MV{}, skip_ws(String.append(b, rest))), Some{q}, Equal.sym(Maybe<&2, PR>, pvc(MV{}, skip_ws(String.append(b, rest))), pv(1n+String.length(String.append(str_tl(skip_ws(b)), rest)), MM{}, skip_ws(rest)), objShort(b, rest, hb, String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), p1f, e1f)), eq),
        folWs(prt(q), emptyWs(prt(q), hemp)), String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), leConO(str_tl(skip_ws(b)), x, n, v, s, rest)))))

def loCon.b(+b: String, +k: String, +n: String, +v: String, +s: String, +rest: String, +hb: {tokb('{', b) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, +q1: String, +x: String, +q2: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, -jk: Js, +hjk: {Laws.load(k) == Some{jk} : Maybe<Js>}, -name: String, +hname: {Laws.string(jk) == Some{name} : Maybe<String>}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Sigma<&2, &2, String, _ => Js>>, +hl: {Laws.object(jr) == Some{l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest)))))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +hjr: {Laws.load(String.append(b, rest)) == Some{jr} : Maybe<Js>}, -p1f: PR, +e1f: {pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest)) == Some{p1f} : Maybe<&2, PR>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  finInv({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, pvc(MV{}, skip_ws(String.append(b, rest))), jr, hjr, +q => +eq => +hemp => +hq => +ejr => loCon.c(b, k, n, v, s, rest, hb, hn, hs, q1, x, q2, es, eq1, eq2, hx, jk, hjk, name, hname, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, p1f, e1f, q, eq, hemp, hq, ejr))

def loCon.go(+b: String, +k: String, +n: String, +v: String, +s: String, +rest: String, +hb: {tokb('{', b) == True{} : Bool}, +hn: {tokb(':', n) == True{} : Bool}, +hs: {tokb(',', s) == True{} : Bool}, +q1: String, +x: String, +q2: String, +es: {String.append(q1, String.append(x, q2)) == k : String}, +eq1: {q1 == SCon{'"', SNil{}} : String}, +eq2: {q2 == SCon{'"', SNil{}} : String}, +hx: {ABNF.check(BK, CHARS, x) == True{} : Bool}, -jk: Js, +hjk: {Laws.load(k) == Some{jk} : Maybe<Js>}, -name: String, +hname: {Laws.string(jk) == Some{name} : Maybe<String>}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, -l: List<&2, Sigma<&2, &2, String, _ => Js>>, +hl: {Laws.object(jr) == Some{l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest)))))) == Some{j} : Maybe<Js>}, +r1: Raw, +u1: String, +e1: {pvc(MV{}, skip_ws(v)) == Some{PR{r1, u1}} : Maybe<&2, PR>}, +w1: {wsall(u1) == True{} : Bool}, +hjr: {Laws.load(String.append(b, rest)) == Some{jr} : Maybe<Js>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  finInv({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))), j, Equal.trans(Maybe<Js>, fin(ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest)))), Laws.load(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest)))))), Some{j}, Equal.cong(Maybe<&2, PR>, Maybe<Js>, z => fin(z), ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))), pvc(MV{}, skip_ws(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest))))))), Equal.sym(Maybe<&2, PR>, pvc(MV{}, skip_ws(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest))))))), ocons(x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest))), objFull(b, k, q1, x, q2, n, v, s, rest, es, eq1, eq2, hb, hx, hn, hs, r1, u1, e1, w1))), h),
    +qf => +eqf => hef => hqf => ejf => oconsInv({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, x, r1, pv(String.length(String.append(str_tl(skip_ws(b)), String.append(x, SCon{'"', String.append(n, String.append(v, String.append(s, rest)))}))), MM{}, skip_ws(rest)), qf, eqf, +p1f => +e1f => eq1f => loCon.b(b, k, n, v, s, rest, hb, hn, hs, q1, x, q2, es, eq1, eq2, hx, jk, hjk, name, hname, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, hjr, p1f, e1f)))

def loCon(+b: String, +k: String, +n: String, +v: String, +s: String, +rest: String, +hb: {ABNF.matches(Laws.grammar, "begin-object", b) == True{} : Bool}, +hk: {ABNF.matches(Laws.grammar, "string", k) == True{} : Bool}, +hn: {ABNF.matches(Laws.grammar, "name-separator", n) == True{} : Bool}, +hv: {ABNF.matches(Laws.grammar, "value", v) == True{} : Bool}, +hs: {ABNF.matches(Laws.grammar, "value-separator", s) == True{} : Bool},
  -jk: Js, +hjk: {Laws.load(k) == Some{jk} : Maybe<Js>}, -name: String, +hname: {Laws.string(jk) == Some{name} : Maybe<String>}, -jv: Js, +hjv: {Laws.load(v) == Some{jv} : Maybe<Js>}, -jr: Js, +hjr: {Laws.load(String.append(b, rest)) == Some{jr} : Maybe<Js>}, -l: List<&2, Sigma<&2, &2, String, _ => Js>>, +hl: {Laws.object(jr) == Some{l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, -j: Js, +h: {Laws.load(String.append(b, String.append(k, String.append(n, String.append(v, String.append(s, rest)))))) == Some{j} : Maybe<Js>}) -> {Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}:
  seqE3({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, BK, ABNF.ref("quotation-mark"), CHARS, ABNF.ref("quotation-mark"), k, MBe("string", B_string, k, {==}, mt("string", k, hk)), +q1 => +x => +q2 => +es => +h1 => +hx => +h3 =>
    withV({Laws.null(j) == None{} : Maybe<Unit>} & {Laws.bool(j) == None{} : Maybe<Bool>} & {Laws.number(j) == None{} : Maybe<String>} & {Laws.string(j) == None{} : Maybe<String>} & {Laws.array(j) == None{} : Maybe<List<&2, Js>>} & {Laws.object(j) == Some{(name, jv) <> l} : Maybe<List<&2, Sigma<&2, &2, String, _ => Js>>>}, v, hv, +r1 => +u1 => +e1 => +w1 =>
      loCon.go(b, k, n, v, s, rest, tokM("begin-object", '{', b, {==}, {==}, hb), tokM("name-separator", ':', n, {==}, {==}, hn), tokM("value-separator", ',', s, {==}, {==}, hs),
        q1, x, q2, es, charIs(BK, '"', q1, MBe("quotation-mark", ABNF.char('"'), q1, {==}, h1)), charIs(BK, '"', q2, MBe("quotation-mark", ABNF.char('"'), q2, {==}, h3)), hx,
        jk, hjk, name, hname, jv, hjv, jr, l, hl, j, h, r1, u1, e1, w1, hjr)))

def Laws.load.object.con(b, k, n, v, s, rest, hb, hk, hn, hv, hs, jk, hjk, name, hname, jv, hjv, jr, hjr, l, hl, j, h):
  loCon(b, k, n, v, s, rest, hb, hk, hn, hv, hs, jk, hjk, name, hname, jv, hjv, jr, hjr, l, hl, j, h)
