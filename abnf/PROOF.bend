import Base
import ./LAWS.bend as Laws

# Rules
# =====

# A rule is a regular expression with references to named rules. ochk, the
# definition of check, first replaces each reference by its definition (see
# Grammars), then runs the resulting regular expression with Brzozowski
# derivatives: deriv(c, r) matches what r matches after c, and nullable(r) says
# r matches "". check itself runs chk, a fast equivalent (see Fast checking).

type Re is Data:
  RNone{}
  REps{}
  RChr{c: Char}
  RCat{a: Re, b: Re}
  RAlt{a: Re, b: Re}
  RStar{r: Re}
  RRef{n: String}
  RRange{lo: Char, hi: Char}

def nullable(r: Re) -> Bool:
  match r:
    case RNone{}:
      False{}
    case REps{}:
      True{}
    case RChr{c}:
      False{}
    case RCat{a, b}:
      Bool.and(nullable(a), nullable(b))
    case RAlt{a, b}:
      Bool.or(nullable(a), nullable(b))
    case RStar{r}:
      True{}
    case RRef{n}:
      False{}
    case RRange{lo, hi}:
      False{}

def when(b: Bool) -> Re:
  match b:
    case False{}:
      RNone{}
    case True{}:
      REps{}

# The number of characters from lo to hi.
def rcount(lo: Char, hi: Char) -> Nat:
  Nat.sub(1n+U32.to_nat(Char.to_u32(hi)), U32.to_nat(Char.to_u32(lo)))

# Whether c lies between lo and hi.
def inR(lo: Char, hi: Char, +c: Char) -> Bool:
  Bool.and(U32.is_le(Char.to_u32(lo), Char.to_u32(c)), U32.is_le(Char.to_u32(c), Char.to_u32(hi)))

def deriv.cat(n: Bool, da: Re, b: Re, db: Re) -> Re:
  match n:
    case False{}:
      RCat{da, b}
    case True{}:
      RAlt{RCat{da, b}, db}

def deriv(+c: Char, r: Re) -> Re:
  match r:
    case RNone{}:
      RNone{}
    case REps{}:
      RNone{}
    case RChr{x}:
      when(Char.is_eq(x, c))
    case RCat{+a, +b}:
      deriv.cat(nullable(a), deriv(c, a), b, deriv(c, b))
    case RAlt{a, b}:
      RAlt{deriv(c, a), deriv(c, b)}
    case RStar{+r}:
      RCat{deriv(c, r), RStar{r}}
    case RRef{n}:
      RNone{}
    case RRange{lo, hi}:
      when(inR(lo, hi, c))

def matches(s: String, r: Re) -> Bool:
  match s:
    case SNil{}:
      nullable(r)
    case SCon{c, t}:
      matches(t, deriv(c, r))

# Logic
# =====

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

def none_false(t: String) -> {matches(t, RNone{}) == False{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, u}:
      none_false(u)

def none_elim(-A: Type, t: String, h: {matches(t, RNone{}) == True{} : Bool}) -> A:
  Empty.absurd(A, false_ne_true(Equal.trans(Bool, False{}, matches(t, RNone{}), True{},
    Equal.sym(Bool, matches(t, RNone{}), False{}, none_false(t)), h)))

def nullable_when(b: Bool) -> {nullable(when(b)) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def deriv_when(b: Bool, -c: Char, t: String) -> {matches(t, deriv(c, when(b))) == False{} : Bool}:
  match b:
    case False{}:
      none_false(t)
    case True{}:
      none_false(t)

def eps_elim(s: String, h: {matches(s, REps{}) == True{} : Bool}) -> {s == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      none_elim({SCon{c, t} == SNil{} : String}, t, h)

# Alternation

def alt_or(s: String, x: Re, y: Re) -> {matches(s, RAlt{x, y}) == Bool.or(matches(s, x), matches(s, y)) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      alt_or(t, deriv(c, x), deriv(c, y))

def alt_l(+s: String, +x: Re, +y: Re, h: {matches(s, x) == True{} : Bool}) -> {matches(s, RAlt{x, y}) == True{} : Bool}:
  tt(matches(s, RAlt{x, y}), Bool.or(matches(s, x), matches(s, y)), alt_or(s, x, y),
    or_l(matches(s, x), matches(s, y), h))

def alt_r(+s: String, +x: Re, +y: Re, h: {matches(s, y) == True{} : Bool}) -> {matches(s, RAlt{x, y}) == True{} : Bool}:
  tt(matches(s, RAlt{x, y}), Bool.or(matches(s, x), matches(s, y)), alt_or(s, x, y),
    or_r(matches(s, x), matches(s, y), h))

def alt_elim(+s: String, +x: Re, +y: Re, h: {matches(s, RAlt{x, y}) == True{} : Bool})
  -> Either<&2, &2, {matches(s, x) == True{} : Bool}, {matches(s, y) == True{} : Bool}>:
  or_elim(matches(s, x), matches(s, y),
    tt.sym(matches(s, RAlt{x, y}), Bool.or(matches(s, x), matches(s, y)), alt_or(s, x, y), h))

# Concatenation

def Split(-s: String, -a: Re, -b: Re) -> Type:
  &s1: String -> &s2: String -> {String.append(s1, s2) == s : String} & {matches(s1, a) == True{} : Bool} & {matches(s2, b) == True{} : Bool}

def dcat_l(n: Bool, +t: String, +da: Re, +b: Re, +db: Re, h: {matches(t, RCat{da, b}) == True{} : Bool})
  -> {matches(t, deriv.cat(n, da, b, db)) == True{} : Bool}:
  match n:
    case False{}:
      h
    case True{}:
      alt_l(t, RCat{da, b}, db, h)

def dcat_r(n: Bool, hn: {n == True{} : Bool}, +t: String, +da: Re, +b: Re, +db: Re, h: {matches(t, db) == True{} : Bool})
  -> {matches(t, deriv.cat(n, da, b, db)) == True{} : Bool}:
  match n:
    case False{}:
      Empty.absurd({matches(t, RCat{da, b}) == True{} : Bool}, false_ne_true(hn))
    case True{}:
      alt_r(t, RCat{da, b}, db, h)

def dcat_elim(n: Bool, +t: String, +da: Re, +b: Re, +db: Re, h: {matches(t, deriv.cat(n, da, b, db)) == True{} : Bool})
  -> Either<&2, &2, {matches(t, RCat{da, b}) == True{} : Bool}, {Bool.and(n, matches(t, db)) == True{} : Bool}>:
  match n:
    case False{}:
      Inl{h}
    case True{}:
      alt_elim(t, RCat{da, b}, db, h)

def cat_null(s: String, +a: Re, +b: Re, hn: {nullable(a) == True{} : Bool}, hb: {matches(s, b) == True{} : Bool})
  -> {matches(s, RCat{a, b}) == True{} : Bool}:
  match s:
    case SNil{}:
      and_intro(nullable(a), nullable(b), hn, hb)
    case SCon{+c, +t}:
      dcat_r(nullable(a), hn, t, deriv(c, a), b, deriv(c, b), hb)

def cat_intro(s1: String, +a: Re, +b: Re, +s2: String, h1: {matches(s1, a) == True{} : Bool}, h2: {matches(s2, b) == True{} : Bool})
  -> {matches(String.append(s1, s2), RCat{a, b}) == True{} : Bool}:
  match s1:
    case SNil{}:
      cat_null(s2, a, b, h1, h2)
    case SCon{+c, +t}:
      dcat_l(nullable(a), String.append(t, s2), deriv(c, a), b, deriv(c, b), cat_intro(t, deriv(c, a), b, s2, h1, h2))

def cat_cons(+c: Char, -t: String, -a: Re, -b: Re, sp: Split(t, deriv(c, a), b)) -> Split(SCon{c, t}, a, b):
  (s1, s2, e, h1, h2) = sp
  (SCon{c, s1}, s2, cons_eq(c, String.append(s1, s2), t, e), h1, h2)

def cat_skip(c: Char, t: String, -a: Re, -b: Re, hn: {nullable(a) == True{} : Bool}, hb: {matches(t, deriv(c, b)) == True{} : Bool})
  -> Split(SCon{c, t}, a, b):
  (SNil{}, SCon{c, t}, {==}, hn, hb)

def cat_elim(s: String, +a: Re, +b: Re, +h: {matches(s, RCat{a, b}) == True{} : Bool}) -> Split(s, a, b):
  match s:
    case SNil{}:
      (SNil{}, SNil{}, {==}, and_l(nullable(a), nullable(b), h), and_r(nullable(a), nullable(b), h))
    case SCon{+c, +t}:
      either(&2, &2, {matches(t, RCat{deriv(c, a), b}) == True{} : Bool}, {Bool.and(nullable(a), matches(t, deriv(c, b))) == True{} : Bool},
        Split(SCon{c, t}, a, b),
        dcat_elim(nullable(a), t, deriv(c, a), b, deriv(c, b), h),
        k => cat_cons(c, t, a, b, cat_elim(t, deriv(c, a), b, k)),
        +k => cat_skip(c, t, a, b, and_l(nullable(a), matches(t, deriv(c, b)), k), and_r(nullable(a), matches(t, deriv(c, b)), k)))

def Split.elim(-s: String, -a: Re, -b: Re, -C: Type, sp: Split(s, a, b),
  f: @s1: String -> @s2: String -> {String.append(s1, s2) == s : String} -> {matches(s1, a) == True{} : Bool} -> {matches(s2, b) == True{} : Bool} -> C) -> C:
  (s1, s2, e, h1, h2) = sp
  f(s1, s2, e, h1, h2)

# Two-element sequences: seq([x, y]) is RCat{x, RCat{y, REps{}}}.

def s1_app(s1: String, -s2: String, e2: {s2 == SNil{} : String}) -> {s1 == String.append(s1, s2) : String}:
  %Equal.sym(String, s2, SNil{}, e2) : {s1 == String.append(s1, _) : String}
  Equal.sym(String, String.append(s1, SNil{}), s1, append_nil(s1))

def eps_tail_intro(+s: String, +y: Re, h: {matches(s, y) == True{} : Bool}) -> {matches(s, RCat{y, REps{}}) == True{} : Bool}:
  %append_nil(s) : {matches(_, RCat{y, REps{}}) == True{} : Bool}
  cat_intro(s, y, REps{}, SNil{}, h, {==})

def eps_tail_elim.go(-s: String, -y: Re, sp: Split(s, y, REps{})) -> {matches(s, y) == True{} : Bool}:
  (s1, +s2, e, h1, h2) = sp
  %Equal.trans(String, s1, String.append(s1, s2), s, s1_app(s1, s2, eps_elim(s2, h2)), e) : {matches(_, y) == True{} : Bool}
  h1

def eps_tail_elim(+s: String, +y: Re, h: {matches(s, RCat{y, REps{}}) == True{} : Bool}) -> {matches(s, y) == True{} : Bool}:
  eps_tail_elim.go(s, y, cat_elim(s, y, REps{}, h))

def seq2_intro(s1: String, +s2: String, -s: String, +x: Re, +y: Re, e: {String.append(s1, s2) == s : String},
  h1: {matches(s1, x) == True{} : Bool}, h2: {matches(s2, y) == True{} : Bool})
  -> {matches(s, RCat{x, RCat{y, REps{}}}) == True{} : Bool}:
  %e : {matches(_, RCat{x, RCat{y, REps{}}}) == True{} : Bool}
  cat_intro(s1, x, RCat{y, REps{}}, s2, h1, eps_tail_intro(s2, y, h2))

def seq2_elim.go(-s: String, -x: Re, +y: Re, sp: Split(s, x, RCat{y, REps{}})) -> Split(s, x, y):
  (s1, +s2, e, h1, h2) = sp
  (s1, s2, e, h1, eps_tail_elim(s2, y, h2))

def seq2_elim(+s: String, +x: Re, +y: Re, h: {matches(s, RCat{x, RCat{y, REps{}}}) == True{} : Bool}) -> Split(s, x, y):
  seq2_elim.go(s, x, y, cat_elim(s, x, RCat{y, REps{}}, h))

# Grammars
# ========

# A grammar is a list of entries. lookupE(G, ln) alternates every entry whose
# name lowercases to ln. A table holds the grammar with its references already
# replaced up to some depth: tbl(0, G) has no entries (every reference fails),
# and tbl(1+d, G) holds each entry with subst applied at depth d. TTop is a
# table whose references match every string (see Fast checking).

type Ent is Data:
  Ent{k: String, r: Re}

def lsel(b: Bool, r: Re, x: Re) -> Re:
  match b:
    case True{}:
      RAlt{r, x}
    case False{}:
      x

def lookupE(G: List<&2, Ent>, +ln: String) -> Re:
  match G:
    case []:
      RNone{}
    case Ent{k, r} <> rest:
      lsel(String.eq(String.to_lower(k), ln), r, lookupE(rest, ln))

def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, ones(p)}

# Every string matches SIG: it repeats the range of all characters.
def SIG() -> Re:
  RStar{RRange{Chr{U32{Word.zero(32n)}}, Chr{U32{ones(32n)}}}}

type Tb is Data:
  TDead{}
  TTop{}
  TLive{es: List<&2, Ent>}

def refv(T: Tb, ln: String) -> Re:
  match T:
    case TDead{}:
      RNone{}
    case TTop{}:
      SIG
    case TLive{es}:
      lookupE(es, ln)

def subst(r: Re, +T: Tb) -> Re:
  match r:
    case RNone{}:
      RNone{}
    case REps{}:
      REps{}
    case RChr{c}:
      RChr{c}
    case RCat{a, b}:
      RCat{subst(a, T), subst(b, T)}
    case RAlt{a, b}:
      RAlt{subst(a, T), subst(b, T)}
    case RStar{a}:
      RStar{subst(a, T)}
    case RRef{n}:
      refv(T, String.to_lower(n))
    case RRange{lo, hi}:
      RRange{lo, hi}

def tblRow(G: List<&2, Ent>, +T: Tb) -> List<&2, Ent>:
  match G:
    case []:
      []
    case Ent{k, r} <> rest:
      Ent{k, subst(r, T)} <> tblRow(rest, T)

def tbl(d: Nat, +G: List<&2, Ent>) -> Tb:
  match d:
    case 0n:
      TDead{}
    case 1n+p:
      TLive{tblRow(G, tbl(p, G))}

def conv(g: List<(String & Re)>) -> List<&2, Ent>:
  match g:
    case []:
      []
    case h <> t:
      (k, r) = h
      Ent{k, r} <> conv(t)

# The cells of a string s are every pair of an entry's body and a substring of
# s. bound(s, G) is one more than their number: a depth that suffices for s.

type Cell is Data:
  Cell{r: Re, w: String}

def gapp(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs:
    case []:
      ys
    case h <> t:
      h <> gapp(A, t, ys)

def consAll(+c: Char, ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case []:
      []
    case h <> t:
      SCon{c, h} <> consAll(c, t)

def prefixes(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{+c, t}:
      SNil{} <> consAll(c, prefixes(t))

def subs(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{+c, +t}:
      gapp(String, prefixes(SCon{c, t}), subs(t))

def row(+w: String, G: List<&2, Ent>) -> List<&2, Cell>:
  match G:
    case []:
      []
    case Ent{k, r} <> rest:
      Cell{r, w} <> row(w, rest)

def pairs(ws: List<&2, String>, +G: List<&2, Ent>) -> List<&2, Cell>:
  match ws:
    case []:
      []
    case w <> rest:
      gapp(Cell, row(w, G), pairs(rest, G))

def cells(s: String, +G: List<&2, Ent>) -> List<&2, Cell>:
  pairs(subs(s), G)

def clen(cs: List<&2, Cell>) -> Nat:
  match cs:
    case []:
      0n
    case c <> rest:
      1n+clen(rest)

def bound(s: String, +G: List<&2, Ent>) -> Nat:
  1n+clen(cells(s, G))

# A book is a grammar and a depth: the full grammar takes bound(s, G). ochk
# defines what check answers; it is far too slow to run on a full grammar.

type Bk is Data:
  BFull{g: List<&2, Ent>}
  BLim{d: Nat, g: List<&2, Ent>}

def tb(book: Bk, +s: String) -> Tb:
  match book:
    case BFull{+g}:
      tbl(bound(s, g), g)
    case BLim{d, +g}:
      tbl(d, g)

def ochk(book: Bk, r: Re, +s: String) -> Bool:
  matches(s, subst(r, tb(book, s)))

# Constructors
# ============

def Laws.Rule():
  Re

def Laws.Book():
  Bk

def Laws.limit(d, g):
  BLim{d, conv(g)}

def Laws.full(g):
  BFull{conv(g)}

def Laws.lookup(g, name):
  lookupE(conv(g), String.to_lower(name))

def Laws.ref(name):
  RRef{name}

def Laws.char(c):
  RChr{c}

def Laws.empty():
  REps{}

def Laws.seq(rs):
  match rs:
    case Nil{}:
      Laws.empty
    case Con{h, t}:
      RCat{h, Laws.seq(t)}

def Laws.alt(rs):
  match rs:
    case Nil{}:
      RNone{}
    case Con{h, t}:
      RAlt{h, Laws.alt(t)}

def chars.go(n: Nat, +c: Char) -> List<Re>:
  match n:
    case 0n:
      []
    case 1n+p:
      RChr{c} <> chars.go(p, Chr{(Char.to_u32(c) + 1 : U32)})

def Laws.chars(n, c):
  chars.go(n, c)

# A range is its own node, so that a wide range stays small until a character
# is matched against it.
def Laws.range(start, end):
  RRange{start, end}

def Laws.string.case_sensitive(lit):
  match lit:
    case SNil{}:
      Laws.empty
    case SCon{c, t}:
      Laws.seq([Laws.char(c), Laws.string.case_sensitive(t)])

def Laws.string.case_insensitive(lit):
  match lit:
    case SNil{}:
      Laws.empty
    case SCon{+c, t}:
      Laws.seq([Laws.alt([Laws.char(Char.to_lower(c)), Laws.char(Char.to_upper(c))]), Laws.string.case_insensitive(t)])

def exactly.go(n: Nat, +r: Re) -> Re:
  match n:
    case 0n:
      Laws.empty
    case 1n+p:
      Laws.seq([r, exactly.go(p, r)])

def Laws.rep.exactly(n, r):
  exactly.go(n, r)

def Laws.rep.any(r):
  RStar{r}

def at_least.go(n: Nat, +r: Re) -> Re:
  match n:
    case 0n:
      RStar{r}
    case 1n+p:
      Laws.seq([r, at_least.go(p, r)])

def Laws.rep.at_least(n, r):
  at_least.go(n, r)

def at_most.go(n: Nat, +r: Re) -> Re:
  match n:
    case 0n:
      Laws.empty
    case 1n+p:
      Laws.alt([Laws.empty, Laws.seq([r, at_most.go(p, r)])])

def Laws.rep.at_most(n, r):
  at_most.go(n, r)

def rep.go(a: Nat, b: Nat, +r: Re) -> Re:
  match a:
    case 0n:
      at_most.go(b, r)
    case 1n+ap:
      match b:
        case 0n:
          Laws.alt([])
        case 1n+bp:
          Laws.seq([r, rep.go(ap, bp, r)])

def Laws.rep(a, b, r):
  rep.go(a, b, r)

def Laws.opt(r):
  Laws.alt([Laws.empty, r])

# Repetition
# ==========

def zero_le(m: Nat) -> {Nat.is_le(0n, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def star_intro(s1: String, +s2: String, +r: Re, h1: {matches(s1, r) == True{} : Bool}, h2: {matches(s2, RStar{r}) == True{} : Bool})
  -> {matches(String.append(s1, s2), RStar{r}) == True{} : Bool}:
  match s1:
    case SNil{}:
      h2
    case SCon{+c, t}:
      cat_intro(t, deriv(c, r), RStar{r}, s2, h1, h2)

def StarSplit(-t: String, -x: Re, -r: Re) -> Type:
  &s1: String -> &s2: String -> &m: Nat -> {String.append(s1, s2) == t : String} & {matches(s1, x) == True{} : Bool} & {matches(s2, Laws.rep.exactly(m, r)) == True{} : Bool}

def StarSplit.elim(-t: String, -x: Re, -r: Re, -C: Type, sp: StarSplit(t, x, r),
  f: @s1: String -> @s2: String -> @m: Nat -> {String.append(s1, s2) == t : String} -> {matches(s1, x) == True{} : Bool} -> {matches(s2, Laws.rep.exactly(m, r)) == True{} : Bool} -> C) -> C:
  (s1, s2, m, e, h1, h2) = sp
  f(s1, s2, m, e, h1, h2)

def star_cons(+c: Char, -u: String, -x: Re, -r: Re, sp: StarSplit(u, deriv(c, x), r)) -> StarSplit(SCon{c, u}, x, r):
  (s1, s2, m, e, h1, h2) = sp
  (SCon{c, s1}, s2, m, cons_eq(c, String.append(s1, s2), u, e), h1, h2)

def star_skip(+c: Char, +u: String, -x: Re, +r: Re, hn: {nullable(x) == True{} : Bool}, sp: StarSplit(u, deriv(c, r), r))
  -> StarSplit(SCon{c, u}, x, r):
  (s1, +s2, +m, e, h1, h2) = sp
  (SNil{}, SCon{c, u}, 1n+m, {==}, hn,
    seq2_intro(SCon{c, s1}, s2, SCon{c, u}, r, Laws.rep.exactly(m, r), cons_eq(c, String.append(s1, s2), u, e), h1, h2))

# Splits a match of x followed by r* into x and some number of r.
def star_gen(t: String, +x: Re, +r: Re, +h: {matches(t, RCat{x, RStar{r}}) == True{} : Bool}) -> StarSplit(t, x, r):
  match t:
    case SNil{}:
      (SNil{}, SNil{}, 0n, {==}, and_l(nullable(x), True{}, h), {==})
    case SCon{+c, +u}:
      either(&2, &2, {matches(u, RCat{deriv(c, x), RStar{r}}) == True{} : Bool},
        {Bool.and(nullable(x), matches(u, RCat{deriv(c, r), RStar{r}})) == True{} : Bool},
        StarSplit(SCon{c, u}, x, r),
        dcat_elim(nullable(x), u, deriv(c, x), RStar{r}, RCat{deriv(c, r), RStar{r}}, h),
        k => star_cons(c, u, x, r, star_gen(u, deriv(c, x), r, k)),
        +k => star_skip(c, u, x, r, and_l(nullable(x), matches(u, RCat{deriv(c, r), RStar{r}}), k),
          star_gen(u, deriv(c, r), r, and_r(nullable(x), matches(u, RCat{deriv(c, r), RStar{r}}), k))))

def any_step(s1: String, +s2: String, -s: String, +r: Re, e: {String.append(s1, s2) == s : String},
  h1: {matches(s1, r) == True{} : Bool}, h2: {matches(s2, RStar{r}) == True{} : Bool}) -> {matches(s, RStar{r}) == True{} : Bool}:
  %e : {matches(_, RStar{r}) == True{} : Bool}
  star_intro(s1, s2, r, h1, h2)

def any_intro(m: Nat, +r: Re, +s: String, hs: {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool})
  -> {matches(s, RStar{r}) == True{} : Bool}:
  match m:
    case 0n:
      %Equal.sym(String, s, SNil{}, eps_elim(s, hs)) : {matches(_, RStar{r}) == True{} : Bool}
      {==}
    case 1n+ +p:
      Split.elim(s, r, Laws.rep.exactly(p, r), {matches(s, RStar{r}) == True{} : Bool},
        seq2_elim(s, r, Laws.rep.exactly(p, r), hs),
        s1 => +s2 => e => h1 => h2 => any_step(s1, s2, s, r, e, h1, any_intro(p, r, s2, h2)))

def ExAny(-r: Re, -s: String) -> Type:
  &m: Nat -> {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool}

def ExAny.elim(-r: Re, -s: String, -C: Type, p: ExAny(r, s), f: @m: Nat -> {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool} -> C) -> C:
  (m, h) = p
  f(m, h)

def any_elim(+r: Re, s: String, hs: {matches(s, RStar{r}) == True{} : Bool}) -> ExAny(r, s):
  match s:
    case SNil{}:
      (0n, {==})
    case SCon{+c, +t}:
      StarSplit.elim(t, deriv(c, r), r, ExAny(r, SCon{c, t}), star_gen(t, deriv(c, r), r, hs),
        s1 => +s2 => +m => e => h1 => h2 => (1n+m,
          seq2_intro(SCon{c, s1}, s2, SCon{c, t}, r, Laws.rep.exactly(m, r), cons_eq(c, String.append(s1, s2), t, e), h1, h2)))

def ExLo(-n: Nat, -r: Re, -s: String) -> Type:
  &m: Nat -> {Nat.is_le(n, m) == True{} : Bool} & {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool}

def ExLo.elim(-n: Nat, -r: Re, -s: String, -C: Type, p: ExLo(n, r, s),
  f: @m: Nat -> {Nat.is_le(n, m) == True{} : Bool} -> {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool} -> C) -> C:
  (m, le, h) = p
  f(m, le, h)

def ExHi(-n: Nat, -r: Re, -s: String) -> Type:
  &m: Nat -> {Nat.is_le(m, n) == True{} : Bool} & {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool}

def ExHi.elim(-n: Nat, -r: Re, -s: String, -C: Type, p: ExHi(n, r, s),
  f: @m: Nat -> {Nat.is_le(m, n) == True{} : Bool} -> {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool} -> C) -> C:
  (m, le, h) = p
  f(m, le, h)

def ExIn(-a: Nat, -b: Nat, -r: Re, -s: String) -> Type:
  &m: Nat -> {Nat.is_le(a, m) == True{} : Bool} & {Nat.is_le(m, b) == True{} : Bool} & {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool}

def ExIn.elim(-a: Nat, -b: Nat, -r: Re, -s: String, -C: Type, p: ExIn(a, b, r, s),
  f: @m: Nat -> {Nat.is_le(a, m) == True{} : Bool} -> {Nat.is_le(m, b) == True{} : Bool} -> {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool} -> C) -> C:
  (m, la, lb, h) = p
  f(m, la, lb, h)

def at_least_intro(n: Nat, m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}, +r: Re, +s: String,
  hs: {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool}) -> {matches(s, Laws.rep.at_least(n, r)) == True{} : Bool}:
  match n m:
    case 0n m:
      any_intro(m, r, s, hs)
    case 1n+np 0n:
      Empty.absurd({matches(s, Laws.rep.at_least(1n+np, r)) == True{} : Bool}, false_ne_true(h))
    case 1n+ +np 1n+ +mp:
      Split.elim(s, r, Laws.rep.exactly(mp, r), {matches(s, Laws.rep.at_least(1n+np, r)) == True{} : Bool},
        seq2_elim(s, r, Laws.rep.exactly(mp, r), hs),
        s1 => +s2 => e => h1 => h2 => seq2_intro(s1, s2, s, r, Laws.rep.at_least(np, r), e, h1, at_least_intro(np, mp, h, r, s2, h2)))

def at_least_elim(n: Nat, +r: Re, +s: String, hs: {matches(s, Laws.rep.at_least(n, r)) == True{} : Bool}) -> ExLo(n, r, s):
  match n:
    case 0n:
      ExAny.elim(r, s, ExLo(0n, r, s), any_elim(r, s, hs), +m => p => (m, zero_le(m), p))
    case 1n+ +np:
      Split.elim(s, r, Laws.rep.at_least(np, r), ExLo(1n+np, r, s), seq2_elim(s, r, Laws.rep.at_least(np, r), hs),
        s1 => +s2 => e => h1 => h2 => ExLo.elim(np, r, s2, ExLo(1n+np, r, s), at_least_elim(np, r, s2, h2),
          +m => le => p => (1n+m, le, seq2_intro(s1, s2, s, r, Laws.rep.exactly(m, r), e, h1, p))))

def at_most_intro(n: Nat, m: Nat, h: {Nat.is_le(m, n) == True{} : Bool}, +r: Re, +s: String,
  hs: {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool}) -> {matches(s, Laws.rep.at_most(n, r)) == True{} : Bool}:
  match n m:
    case 0n 0n:
      hs
    case 0n 1n+mp:
      Empty.absurd({matches(s, Laws.rep.at_most(0n, r)) == True{} : Bool}, false_ne_true(h))
    case 1n+ +np 0n:
      alt_l(s, REps{}, RAlt{Laws.seq([r, Laws.rep.at_most(np, r)]), RNone{}}, hs)
    case 1n+ +np 1n+ +mp:
      alt_r(s, REps{}, RAlt{Laws.seq([r, Laws.rep.at_most(np, r)]), RNone{}},
        alt_l(s, Laws.seq([r, Laws.rep.at_most(np, r)]), RNone{},
          Split.elim(s, r, Laws.rep.exactly(mp, r), {matches(s, Laws.seq([r, Laws.rep.at_most(np, r)])) == True{} : Bool},
            seq2_elim(s, r, Laws.rep.exactly(mp, r), hs),
            s1 => +s2 => e => h1 => h2 => seq2_intro(s1, s2, s, r, Laws.rep.at_most(np, r), e, h1, at_most_intro(np, mp, h, r, s2, h2)))))

def at_most_elim(n: Nat, +r: Re, +s: String, hs: {matches(s, Laws.rep.at_most(n, r)) == True{} : Bool}) -> ExHi(n, r, s):
  match n:
    case 0n:
      (0n, {==}, hs)
    case 1n+ +np:
      either(&2, &2, {matches(s, REps{}) == True{} : Bool}, {matches(s, RAlt{Laws.seq([r, Laws.rep.at_most(np, r)]), RNone{}}) == True{} : Bool},
        ExHi(1n+np, r, s),
        alt_elim(s, REps{}, RAlt{Laws.seq([r, Laws.rep.at_most(np, r)]), RNone{}}, hs),
        k => (0n, {==}, k),
        k => either(&2, &2, {matches(s, Laws.seq([r, Laws.rep.at_most(np, r)])) == True{} : Bool}, {matches(s, RNone{}) == True{} : Bool},
          ExHi(1n+np, r, s),
          alt_elim(s, Laws.seq([r, Laws.rep.at_most(np, r)]), RNone{}, k),
          k2 => Split.elim(s, r, Laws.rep.at_most(np, r), ExHi(1n+np, r, s), seq2_elim(s, r, Laws.rep.at_most(np, r), k2),
            s1 => +s2 => e => h1 => h2 => ExHi.elim(np, r, s2, ExHi(1n+np, r, s), at_most_elim(np, r, s2, h2),
              +m => le => p => (1n+m, le, seq2_intro(s1, s2, s, r, Laws.rep.exactly(m, r), e, h1, p)))),
          k3 => none_elim(ExHi(1n+np, r, s), s, k3)))

def rep_intro(a: Nat, b: Nat, m: Nat, ha: {Nat.is_le(a, m) == True{} : Bool}, hb: {Nat.is_le(m, b) == True{} : Bool},
  +r: Re, +s: String, hs: {matches(s, Laws.rep.exactly(m, r)) == True{} : Bool}) -> {matches(s, Laws.rep(a, b, r)) == True{} : Bool}:
  match a b m:
    case 0n b m:
      at_most_intro(b, m, hb, r, s, hs)
    case 1n+ap 0n 0n:
      Empty.absurd({matches(s, Laws.rep(1n+ap, 0n, r)) == True{} : Bool}, false_ne_true(ha))
    case 1n+ap 0n 1n+mp:
      Empty.absurd({matches(s, Laws.rep(1n+ap, 0n, r)) == True{} : Bool}, false_ne_true(hb))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({matches(s, Laws.rep(1n+ap, 1n+bp, r)) == True{} : Bool}, false_ne_true(ha))
    case 1n+ +ap 1n+ +bp 1n+ +mp:
      Split.elim(s, r, Laws.rep.exactly(mp, r), {matches(s, Laws.rep(1n+ap, 1n+bp, r)) == True{} : Bool},
        seq2_elim(s, r, Laws.rep.exactly(mp, r), hs),
        s1 => +s2 => e => h1 => h2 => seq2_intro(s1, s2, s, r, Laws.rep(ap, bp, r), e, h1, rep_intro(ap, bp, mp, ha, hb, r, s2, h2)))

def rep_elim(a: Nat, b: Nat, +r: Re, +s: String, hs: {matches(s, Laws.rep(a, b, r)) == True{} : Bool}) -> ExIn(a, b, r, s):
  match a b:
    case 0n b:
      ExHi.elim(b, r, s, ExIn(0n, b, r, s), at_most_elim(b, r, s, hs), +m => le => p => (m, zero_le(m), le, p))
    case 1n+ap 0n:
      none_elim(ExIn(1n+ap, 0n, r, s), s, hs)
    case 1n+ +ap 1n+ +bp:
      Split.elim(s, r, Laws.rep(ap, bp, r), ExIn(1n+ap, 1n+bp, r, s), seq2_elim(s, r, Laws.rep(ap, bp, r), hs),
        s1 => +s2 => e => h1 => h2 => ExIn.elim(ap, bp, r, s2, ExIn(1n+ap, 1n+bp, r, s), rep_elim(ap, bp, r, s2, h2),
          +m => la => lb => p => (1n+m, la, lb, seq2_intro(s1, s2, s, r, Laws.rep.exactly(m, r), e, h1, p))))

# Core rules
# ==========

def Laws.core.alpha():
  Laws.alt([Laws.range('A', 'Z'), Laws.range('a', 'z')])

def Laws.core.bit():
  Laws.alt([Laws.string.case_insensitive("0"), Laws.string.case_insensitive("1")])

def Laws.core.char():
  Laws.range(Chr{1}, Chr{127})

def Laws.core.cr():
  Laws.char('\r')

def Laws.core.lf():
  Laws.char('\n')

def Laws.core.crlf():
  Laws.seq([Laws.core.cr, Laws.core.lf])

def Laws.core.ctl():
  Laws.alt([Laws.range(Chr{0}, Chr{31}), Laws.char(Chr{127})])

def Laws.core.digit():
  Laws.range('0', '9')

def Laws.core.dquote():
  Laws.char('"')

def Laws.core.hexdig():
  Laws.alt([Laws.core.digit, Laws.string.case_insensitive("A"), Laws.string.case_insensitive("B"), Laws.string.case_insensitive("C"), Laws.string.case_insensitive("D"), Laws.string.case_insensitive("E"), Laws.string.case_insensitive("F")])

def Laws.core.htab():
  Laws.char('\t')

def Laws.core.sp():
  Laws.char(' ')

def Laws.core.wsp():
  Laws.alt([Laws.core.sp, Laws.core.htab])

def Laws.core.lwsp():
  Laws.rep.any(Laws.alt([Laws.core.wsp, Laws.seq([Laws.core.crlf, Laws.core.wsp])]))

def Laws.core.octet():
  Laws.range(Chr{0}, Chr{255})

def Laws.core.vchar():
  Laws.range('!', '~')

# More logic
# ==========

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

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

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

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, e)

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

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, plus_zero_r(b))
    case 1n+ +p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        succ_cong(Nat.add(p, b), Nat.add(b, p), add_comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), plus_succ_r(b, p)))

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

def le_add(a: Nat, +a2: Nat, +b: Nat, +b2: Nat, h1: {le(a, a2) == True{} : Bool}, h2: {le(b, b2) == True{} : Bool})
  -> {le(Nat.add(a, b), Nat.add(a2, b2)) == True{} : Bool}:
  match a a2:
    case 0n a2:
      le_trans(b, b2, Nat.add(a2, b2), h2, le_add_l(a2, b2))
    case 1n+p 0n:
      Empty.absurd({le(Nat.add(1n+p, b), Nat.add(0n, b2)) == True{} : Bool}, false_ne_true(h1))
    case 1n+p 1n+q:
      le_add(p, q, b, b2, h1, h2)

def antisym(a: Nat, b: Nat, h1: {le(a, b) == True{} : Bool}, h2: {le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, false_ne_true(h2))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, false_ne_true(h1))
    case 1n+p 1n+q:
      succ_cong(p, q, antisym(p, q, h1, h2))

def eqn_sound(a: Nat, b: Nat, h: {eqn(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, false_ne_true(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, false_ne_true(h))
    case 1n+p 1n+q:
      succ_cong(p, q, eqn_sound(p, q, h))

def eqn_refl(a: Nat) -> {eqn(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      eqn_refl(p)

def eqn_of_eq(+a: Nat, -b: Nat, e: {a == b : Nat}) -> {eqn(a, b) == True{} : Bool}:
  %e : {eqn(a, _) == True{} : Bool}
  eqn_refl(a)

def lt_of_ne(a: Nat, b: Nat, h1: {le(a, b) == True{} : Bool}, h2: {eqn(a, b) == False{} : Bool})
  -> {le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({le(1n, 0n) == True{} : Bool}, false_ne_true(Equal.sym(Bool, True{}, False{}, h2)))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({le(1n+1n+p, 0n) == True{} : Bool}, false_ne_true(h1))
    case 1n+p 1n+q:
      lt_of_ne(p, q, h1, h2)

def succ_le_absurd(a: Nat, h: {le(1n+a, a) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      false_ne_true(h)
    case 1n+p:
      succ_le_absurd(p, h)

def le_succ_ne.go(-c: Nat, -c2: Nat, h: {le(c, c2) == True{} : Bool}, e: {c == 1n+c2 : Nat})
  -> {le(1n+c2, c2) == True{} : Bool}:
  %e : {le(_, c2) == True{} : Bool}
  h

def le_succ_ne(-c: Nat, +c2: Nat, h: {le(c, c2) == True{} : Bool}, e: {c == 1n+c2 : Nat}) -> Empty:
  succ_le_absurd(c2, le_succ_ne.go(c, c2, h, e))

def b2n_le1(x: Bool) -> {le(b2n(x), 1n) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def le1_b2n(y: Bool, h: {y == True{} : Bool}) -> {le(1n, b2n(y)) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({le(1n, 0n) == True{} : Bool}, false_ne_true(h))

# A pointwise implication between two booleans orders their counts.
def bimp(x: Bool, y: Bool, f: {x == True{} : Bool} -> {y == True{} : Bool}) -> {le(b2n(x), b2n(y)) == True{} : Bool}:
  match x:
    case True{}:
      le1_b2n(y, f({==}))
    case False{}:
      {==}

# If two sums are equal and each term is at most its partner, the terms are equal.
def bsplit_l(x: Bool, y: Bool, a: Nat, +b: Nat, hxy: {le(b2n(x), b2n(y)) == True{} : Bool}, hab: {le(a, b) == True{} : Bool},
  e: {Nat.add(b2n(x), a) == Nat.add(b2n(y), b) : Nat}) -> {x == y : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(hxy))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, le_succ_ne(a, b, hab, e))
    case False{} False{}:
      {==}

def bsplit_r(x: Bool, y: Bool, a: Nat, +b: Nat, hxy: {le(b2n(x), b2n(y)) == True{} : Bool}, hab: {le(a, b) == True{} : Bool},
  e: {Nat.add(b2n(x), a) == Nat.add(b2n(y), b) : Nat}) -> {a == b : Nat}:
  match x y:
    case True{} True{}:
      succ_inj(a, b, e)
    case True{} False{}:
      Empty.absurd({a == b : Nat}, false_ne_true(hxy))
    case False{} True{}:
      Empty.absurd({a == b : Nat}, le_succ_ne(a, b, hab, e))
    case False{} False{}:
      e

def LeW(-d: Nat, -t: Nat) -> Type:
  &j: Nat -> {Nat.add(j, d) == 1n+t : Nat}

def LeW.elim(-d: Nat, -t: Nat, -C: Type, p: LeW(d, t), f: @j: Nat -> {Nat.add(j, d) == 1n+t : Nat} -> C) -> C:
  (j, e) = p
  f(j, e)

def GeW(-d: Nat, -t: Nat) -> Type:
  &i: Nat -> {d == 1n+Nat.add(i, t) : Nat}

def GeW.elim(-d: Nat, -t: Nat, -C: Type, p: GeW(d, t), f: @i: Nat -> {d == 1n+Nat.add(i, t) : Nat} -> C) -> C:
  (i, e) = p
  f(i, e)

def cmpN.up(-d: Nat, -t: Nat, +j: Nat, e: {Nat.add(j, d) == 1n+t : Nat}) -> {Nat.add(j, 1n+d) == 1n+1n+t : Nat}:
  Equal.trans(Nat, Nat.add(j, 1n+d), 1n+Nat.add(j, d), 1n+1n+t, plus_succ_r(j, d), succ_cong(Nat.add(j, d), 1n+t, e))

def cmpN.down(-d: Nat, -t: Nat, +i: Nat, e: {d == 1n+Nat.add(i, t) : Nat}) -> {1n+d == 1n+Nat.add(i, 1n+t) : Nat}:
  %Equal.sym(Nat, Nat.add(i, 1n+t), 1n+Nat.add(i, t), plus_succ_r(i, t)) : {1n+d == 1n+_ : Nat}
  succ_cong(d, 1n+Nat.add(i, t), e)

# Either d is at most 1+t, or it is above it.
def cmpN(d: Nat, t: Nat) -> Either<&1, &1, LeW(d, t), GeW(d, t)>:
  match d t:
    case 0n +t:
      Inl{(1n+t, plus_zero_r(1n+t))}
    case 1n+ +p 0n:
      Inr{(p, succ_cong(p, Nat.add(p, 0n), Equal.sym(Nat, Nat.add(p, 0n), p, plus_zero_r(p))))}
    case 1n+p 1n+q:
      either(&1, &1, LeW(p, q), GeW(p, q), Either<&1, &1, LeW(1n+p, 1n+q), GeW(1n+p, 1n+q)>, cmpN(p, q),
        x => LeW.elim(p, q, Either<&1, &1, LeW(1n+p, 1n+q), GeW(1n+p, 1n+q)>, x, +j => e => Inl{(j, cmpN.up(p, q, j, e))}),
        y => GeW.elim(p, q, Either<&1, &1, LeW(1n+p, 1n+q), GeW(1n+p, 1n+q)>, y, +i => e => Inr{(i, cmpN.down(p, q, i, e))}))

# Lists
# =====

def Mem(-A: Data, -x: A, xs: List<&2, A>) -> Data:
  match xs:
    case []:
      Empty
    case h <> t:
      Either<&2, &2, {h == x : A}, Mem(A, x, t)>

def mem_tr(-A: Data, -x: A, -xs: List<&2, A>, -ys: List<&2, A>, e: {xs == ys : List<&2, A>}, m: Mem(A, x, xs)) -> Mem(A, x, ys):
  %e : Mem(A, x, _)
  m

def mem_gapp_l(-A: Data, -x: A, xs: List<&2, A>, -ys: List<&2, A>, m: Mem(A, x, xs)) -> Mem(A, x, gapp(A, xs, ys)):
  match xs:
    case []:
      Empty.absurd(Mem(A, x, ys), m)
    case h <> t:
      match m:
        case Inl{e}:
          Inl{e}
        case Inr{m2}:
          Inr{mem_gapp_l(A, x, t, ys, m2)}

def mem_gapp_r(-A: Data, -x: A, xs: List<&2, A>, -ys: List<&2, A>, m: Mem(A, x, ys)) -> Mem(A, x, gapp(A, xs, ys)):
  match xs:
    case []:
      m
    case h <> t:
      Inr{mem_gapp_r(A, x, t, ys, m)}

def mem_gapp_elim.inr(-A: Data, -x: A, -h: A, -t: List<&2, A>, -ys: List<&2, A>,
  e: Either<&2, &2, Mem(A, x, t), Mem(A, x, ys)>) -> Either<&2, &2, Mem(A, x, h <> t), Mem(A, x, ys)>:
  match e:
    case Inl{m}:
      Inl{Inr{m}}
    case Inr{m}:
      Inr{m}

def mem_gapp_elim(-A: Data, -x: A, xs: List<&2, A>, -ys: List<&2, A>, m: Mem(A, x, gapp(A, xs, ys)))
  -> Either<&2, &2, Mem(A, x, xs), Mem(A, x, ys)>:
  match xs:
    case []:
      Inr{m}
    case h <> t:
      match m:
        case Inl{e}:
          Inl{Inl{e}}
        case Inr{m2}:
          mem_gapp_elim.inr(A, x, h, t, ys, mem_gapp_elim(A, x, t, ys, m2))

def gapp_snoc(-A: Data, pre: List<&2, A>, +c: A, -rest: List<&2, A>)
  -> {gapp(A, gapp(A, pre, [c]), rest) == gapp(A, pre, c <> rest) : List<&2, A>}:
  match pre:
    case []:
      {==}
    case h <> t:
      %gapp_snoc(A, t, c, rest) : {h <> gapp(A, gapp(A, t, [c]), rest) == h <> _ : List<&2, A>}
      {==}

def toCell(x: Ent, w: String) -> Cell:
  match x:
    case Ent{k, r}:
      Cell{r, w}

def cellW(c: Cell) -> String:
  match c:
    case Cell{r, w}:
      w

def mem_row(+w: String, -k: String, -r: Re, G: List<&2, Ent>, me: Mem(Ent, Ent{k, r}, G)) -> Mem(Cell, Cell{r, w}, row(w, G)):
  match G:
    case []:
      Empty.absurd(Mem(Cell, Cell{r, w}, []), me)
    case Ent{k2, r2} <> rest:
      match me:
        case Inl{e}:
          Inl{Equal.cong(Ent, Cell, x => toCell(x, w), Ent{k2, r2}, Ent{k, r}, e)}
        case Inr{m2}:
          Inr{mem_row(w, k, r, rest, m2)}

def row_inv(+w2: String, G: List<&2, Ent>, -r: Re, -w: String, m: Mem(Cell, Cell{r, w}, row(w2, G))) -> {w2 == w : String}:
  match G:
    case []:
      Empty.absurd({w2 == w : String}, m)
    case Ent{k2, r2} <> rest:
      match m:
        case Inl{e}:
          Equal.cong(Cell, String, cellW, Cell{r2, w2}, Cell{r, w}, e)
        case Inr{m2}:
          row_inv(w2, rest, r, w, m2)

def mem_pairs.here(+w2: String, -w: String, -r: Re, -k: String, G: List<&2, Ent>, e: {w2 == w : String}, me: Mem(Ent, Ent{k, r}, G))
  -> Mem(Cell, Cell{r, w}, row(w2, G)):
  %e : Mem(Cell, Cell{r, _}, row(w2, G))
  mem_row(w2, k, r, G, me)

def mem_pairs(-r: Re, -k: String, -w: String, ws: List<&2, String>, +G: List<&2, Ent>,
  mw: Mem(String, w, ws), me: Mem(Ent, Ent{k, r}, G)) -> Mem(Cell, Cell{r, w}, pairs(ws, G)):
  match ws:
    case []:
      Empty.absurd(Mem(Cell, Cell{r, w}, []), mw)
    case +w2 <> rest:
      match mw:
        case Inl{e}:
          mem_gapp_l(Cell, Cell{r, w}, row(w2, G), pairs(rest, G), mem_pairs.here(w2, w, r, k, G, e, me))
        case Inr{m2}:
          mem_gapp_r(Cell, Cell{r, w}, row(w2, G), pairs(rest, G), mem_pairs(r, k, w, rest, G, m2, me))

def mem_pairs_inv(-r: Re, -w: String, ws: List<&2, String>, +G: List<&2, Ent>, m: Mem(Cell, Cell{r, w}, pairs(ws, G))) -> Mem(String, w, ws):
  match ws:
    case []:
      Empty.absurd(Mem(String, w, []), m)
    case +w2 <> rest:
      either(&2, &2, Mem(Cell, Cell{r, w}, row(w2, G)), Mem(Cell, Cell{r, w}, pairs(rest, G)), Mem(String, w, w2 <> rest),
        mem_gapp_elim(Cell, Cell{r, w}, row(w2, G), pairs(rest, G), m),
        a => Inl{row_inv(w2, G, r, w, a)},
        b => Inr{mem_pairs_inv(r, w, rest, G, b)})

# Substrings
# ==========

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

def Sub.elim(-w: String, -s: String, -C: Type, p: Sub(w, s),
  f: @x: String -> @y: String -> {String.append(x, String.append(w, y)) == s : String} -> C) -> C:
  (x, y, e) = p
  f(x, y, e)

def sub_refl(+s: String) -> Sub(s, s):
  (SNil{}, SNil{}, append_nil(s))

def sub_l(+s1: String, +s2: String, -t: String, e: {String.append(s1, s2) == t : String}) -> Sub(s1, t):
  (SNil{}, s2, e)

def sub_r(+s1: String, +s2: String, -t: String, e: {String.append(s1, s2) == t : String}) -> Sub(s2, t):
  (s1, SNil{}, Equal.trans(String, String.append(s1, String.append(s2, SNil{})), String.append(s1, s2), t,
    app_congl(s1, String.append(s2, SNil{}), s2, append_nil(s2)), e))

def sub_trans.go(+x1: String, +y1: String, +u: String, -w: String, e1: {String.append(x1, String.append(u, y1)) == w : String},
  +x2: String, +y2: String, -s: String, e2: {String.append(x2, String.append(w, y2)) == s : String})
  -> {String.append(String.append(x2, x1), String.append(u, String.append(y1, y2))) == s : String}:
  %Equal.sym(String, String.append(String.append(x2, x1), String.append(u, String.append(y1, y2))), String.append(x2, String.append(x1, String.append(u, String.append(y1, y2)))), app_assoc(x2, x1, String.append(u, String.append(y1, y2)))) : {_ == s : String}
  %app_assoc(u, y1, y2) : {String.append(x2, String.append(x1, _)) == s : String}
  %app_assoc(x1, String.append(u, y1), y2) : {String.append(x2, _) == s : String}
  %Equal.sym(String, String.append(String.append(x1, String.append(u, y1)), y2), String.append(w, y2), app_congr(y2, String.append(x1, String.append(u, y1)), w, e1)) : {String.append(x2, _) == s : String}
  e2

def sub_trans(+u: String, -w: String, -s: String, a: Sub(u, w), b: Sub(w, s)) -> Sub(u, s):
  (+x1, +y1, e1) = a
  (+x2, +y2, e2) = b
  (String.append(x2, x1), String.append(y1, y2), sub_trans.go(x1, y1, u, w, e1, x2, y2, s, e2))

def pre_head(y: String) -> Mem(String, SNil{}, prefixes(y)):
  match y:
    case SNil{}:
      Inl{{==}}
    case SCon{c, t}:
      Inl{{==}}

def mem_consAll(+c: Char, -x: String, ws: List<&2, String>, m: Mem(String, x, ws)) -> Mem(String, SCon{c, x}, consAll(c, ws)):
  match ws:
    case []:
      Empty.absurd(Mem(String, SCon{c, x}, []), m)
    case h <> t:
      match m:
        case Inl{e}:
          Inl{cons_eq(c, h, x, e)}
        case Inr{m2}:
          Inr{mem_consAll(c, x, t, m2)}

def mem_pre(w: String, +y: String) -> Mem(String, w, prefixes(String.append(w, y))):
  match w:
    case SNil{}:
      pre_head(y)
    case SCon{+c, +t}:
      Inr{mem_consAll(c, t, prefixes(String.append(t, y)), mem_pre(t, y))}

def pre_subs(s: String, -w: String, m: Mem(String, w, prefixes(s))) -> Mem(String, w, subs(s)):
  match s:
    case SNil{}:
      m
    case SCon{+c, +t}:
      mem_gapp_l(String, w, prefixes(SCon{c, t}), subs(t), m)

def mem_subs(x: String, +w: String, +y: String) -> Mem(String, w, subs(String.append(x, String.append(w, y)))):
  match x:
    case SNil{}:
      pre_subs(String.append(w, y), w, mem_pre(w, y))
    case SCon{+c, +t}:
      mem_gapp_r(String, w, prefixes(SCon{c, String.append(t, String.append(w, y))}), subs(String.append(t, String.append(w, y))), mem_subs(t, w, y))

def mem_subs_via.go(+x: String, +w: String, +y: String, -s: String, e: {String.append(x, String.append(w, y)) == s : String})
  -> Mem(String, w, subs(s)):
  %e : Mem(String, w, subs(_))
  mem_subs(x, w, y)

def mem_subs_via(+w: String, -s: String, p: Sub(w, s)) -> Mem(String, w, subs(s)):
  Sub.elim(w, s, Mem(String, w, subs(s)), p, +x => +y => e => mem_subs_via.go(x, w, y, s, e))

def Pre(-w: String, -s: String) -> Type:
  &y: String -> {String.append(w, y) == s : String}

def Pre.elim(-w: String, -s: String, -C: Type, p: Pre(w, s), f: @y: String -> {String.append(w, y) == s : String} -> C) -> C:
  (y, e) = p
  f(y, e)

def CA(-c: Char, -w: String, -ws: List<&2, String>) -> Type:
  &w2: String -> {SCon{c, w2} == w : String} & Mem(String, w2, ws)

def CA.elim(-c: Char, -w: String, -ws: List<&2, String>, -C: Type, p: CA(c, w, ws),
  f: @w2: String -> {SCon{c, w2} == w : String} -> Mem(String, w2, ws) -> C) -> C:
  (w2, e, m) = p
  f(w2, e, m)

def consAll_inv(+c: Char, -w: String, ws: List<&2, String>, m: Mem(String, w, consAll(c, ws))) -> CA(c, w, ws):
  match ws:
    case []:
      Empty.absurd(CA(c, w, []), m)
    case +h <> t:
      match m:
        case Inl{e}:
          (h, e, Inl{{==}})
        case Inr{m2}:
          CA.elim(c, w, t, CA(c, w, h <> t), consAll_inv(c, w, t, m2), w2 => e => m3 => (w2, e, Inr{m3}))

def pre_inv.nil(-w: String, -y: String, e: {SNil{} == w : String}) -> {String.append(w, y) == y : String}:
  %e : {String.append(_, y) == y : String}
  {==}

def pre_inv.con(+c: Char, -w2: String, -w: String, +y: String, -t: String, e: {SCon{c, w2} == w : String}, e2: {String.append(w2, y) == t : String})
  -> {String.append(w, y) == SCon{c, t} : String}:
  %e : {String.append(_, y) == SCon{c, t} : String}
  cons_eq(c, String.append(w2, y), t, e2)

def pre_inv(s: String, -w: String, m: Mem(String, w, prefixes(s))) -> Pre(w, s):
  match s:
    case SNil{}:
      match m:
        case Inl{e}:
          (SNil{}, pre_inv.nil(w, SNil{}, e))
        case Inr{m2}:
          Empty.absurd(Pre(w, SNil{}), m2)
    case SCon{+c, +t}:
      match m:
        case Inl{e}:
          (SCon{c, t}, pre_inv.nil(w, SCon{c, t}, e))
        case Inr{m2}:
          CA.elim(c, w, prefixes(t), Pre(w, SCon{c, t}), consAll_inv(c, w, prefixes(t), m2),
            w2 => e => m3 => Pre.elim(w2, t, Pre(w, SCon{c, t}), pre_inv(t, w2, m3), +y => e2 => (y, pre_inv.con(c, w2, w, y, t, e, e2))))

def mem_subs_inv(s: String, -w: String, m: Mem(String, w, subs(s))) -> Sub(w, s):
  match s:
    case SNil{}:
      Pre.elim(w, SNil{}, Sub(w, SNil{}), pre_inv(SNil{}, w, m), y => e => (SNil{}, y, e))
    case SCon{+c, +t}:
      either(&2, &2, Mem(String, w, prefixes(SCon{c, t})), Mem(String, w, subs(t)), Sub(w, SCon{c, t}),
        mem_gapp_elim(String, w, prefixes(SCon{c, t}), subs(t), m),
        a => Pre.elim(w, SCon{c, t}, Sub(w, SCon{c, t}), pre_inv(SCon{c, t}, w, a), y => e => (SNil{}, y, e)),
        b => Sub.elim(w, t, Sub(w, SCon{c, t}), mem_subs_inv(t, w, b),
          +x => y => e => (SCon{c, x}, y, cons_eq(c, String.append(x, String.append(w, y)), t, e))))

# Words
# =====

# A U32 is a little-endian Word of 32 bits. These lemmas read words as numbers
# (Word.to_nat): comparing words compares their numbers, and adding 1 adds 1
# to the number unless the word is already the largest.

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

def ord_c(a: String, b: String, c: Cmp, h: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match a b c:
    case SNil{} SNil{} LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, false_ne_true(h))
    case SNil{} SNil{} EQ{}:
      {==}
    case SNil{} SNil{} GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, false_ne_true(h))
    case SNil{} SCon{x, t} LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, false_ne_true(h))
    case SNil{} SCon{x, t} EQ{}:
      {==}
    case SNil{} SCon{x, t} GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, false_ne_true(h))
    case SCon{x, t} SNil{} LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, false_ne_true(h))
    case SCon{x, t} SNil{} EQ{}:
      {==}
    case SCon{x, t} SNil{} GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, false_ne_true(h))
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, false_ne_true(h))
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} EQ{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, false_ne_true(h))

def scon_eq(-x: Char, -y: Char, -t1: String, -t2: String, e1: {x == y : Char}, e2: {t1 == t2 : String}) -> {SCon{x, t1} == SCon{y, t2} : String}:
  %e1 : {SCon{x, t1} == SCon{_, t2} : String}
  %e2 : {SCon{x, t1} == SCon{x, _} : String}
  {==}

def ord_sound(a: String, b: String, c: Cmp, +h: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}) -> {a == b : String}:
  match a b c:
    case SNil{} SNil{} c:
      {==}
    case SNil{} SCon{x, t} LT{}:
      Empty.absurd({SNil{} == SCon{x, t} : String}, false_ne_true(h))
    case SNil{} SCon{x, t} EQ{}:
      Empty.absurd({SNil{} == SCon{x, t} : String}, false_ne_true(h))
    case SNil{} SCon{x, t} GT{}:
      Empty.absurd({SNil{} == SCon{x, t} : String}, false_ne_true(h))
    case SCon{x, t} SNil{} LT{}:
      Empty.absurd({SCon{x, t} == SNil{} : String}, false_ne_true(h))
    case SCon{x, t} SNil{} EQ{}:
      Empty.absurd({SCon{x, t} == SNil{} : String}, false_ne_true(h))
    case SCon{x, t} SNil{} GT{}:
      Empty.absurd({SCon{x, t} == SNil{} : String}, false_ne_true(h))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2} LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, false_ne_true(h))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2} EQ{}:
      scon_eq(Chr{x}, Chr{y}, t1, t2, char_eq(Chr{x}, Chr{y}, ord_c(t1, t2, U32.cmp(x, y), h)), ord_sound(t1, t2, U32.cmp(x, y), h))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2} GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, false_ne_true(h))

def str_eq(a: String, b: String, h: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  ord_sound(a, b, EQ{}, h)

# Ranges
# ======

def mtr(-s: String, -X: Re, -Y: Re, e: {X == Y : Re}, h: {matches(s, X) == True{} : Bool}) -> {matches(s, Y) == True{} : Bool}:
  %e : {matches(s, _) == True{} : Bool}
  h

def mcong(-s: String, -X: Re, -Y: Re, e: {X == Y : Re}) -> {matches(s, X) == matches(s, Y) : Bool}:
  %e : {matches(s, X) == matches(s, _) : Bool}
  {==}

def nul_chars(n: Nat, +x: Char) -> {nullable(Laws.alt(chars.go(n, x))) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nul_chars(p, Chr{(Char.to_u32(x) + 1 : U32)})

def sub_chars(n: Nat, +x: Char, -T: Tb) -> {subst(Laws.alt(chars.go(n, x)), T) == Laws.alt(chars.go(n, x)) : Re}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %sub_chars(p, Chr{(Char.to_u32(x) + 1 : U32)}, T) : {RAlt{RChr{x}, subst(Laws.alt(chars.go(p, Chr{(Char.to_u32(x) + 1 : U32)})), T)} == RAlt{RChr{x}, _} : Re}
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

def when_or(a: Bool, b: Bool, t: String) -> {Bool.or(matches(t, when(a)), matches(t, when(b))) == matches(t, when(Bool.or(a, b))) : Bool}:
  match a b t:
    case False{} False{} SNil{}:
      {==}
    case False{} True{} SNil{}:
      {==}
    case True{} False{} SNil{}:
      {==}
    case True{} True{} SNil{}:
      {==}
    case False{} False{} SCon{d, +u}:
      %Equal.sym(Bool, matches(u, RNone{}), False{}, none_false(u)) : {Bool.or(_, _) == _ : Bool}
      {==}
    case False{} True{} SCon{d, +u}:
      %Equal.sym(Bool, matches(u, RNone{}), False{}, none_false(u)) : {Bool.or(_, _) == _ : Bool}
      {==}
    case True{} False{} SCon{d, +u}:
      %Equal.sym(Bool, matches(u, RNone{}), False{}, none_false(u)) : {Bool.or(_, _) == _ : Bool}
      {==}
    case True{} True{} SCon{d, +u}:
      %Equal.sym(Bool, matches(u, RNone{}), False{}, none_false(u)) : {Bool.or(_, _) == _ : Bool}
      {==}

def derM.go(+c: Char, +x: Char, +p: Nat, +t: String,
  ih: {matches(t, deriv(c, Laws.alt(chars.go(p, Chr{(Char.to_u32(x) + 1 : U32)})))) == matches(t, when(memb(c, p, Chr{(Char.to_u32(x) + 1 : U32)}))) : Bool})
  -> {Bool.or(matches(t, when(Char.is_eq(x, c))), matches(t, deriv(c, Laws.alt(chars.go(p, Chr{(Char.to_u32(x) + 1 : U32)}))))) == matches(t, when(memb(c, 1n+p, x))) : Bool}:
  %Equal.sym(Bool, matches(t, deriv(c, Laws.alt(chars.go(p, Chr{(Char.to_u32(x) + 1 : U32)})))), matches(t, when(memb(c, p, Chr{(Char.to_u32(x) + 1 : U32)}))), ih)
    : {Bool.or(matches(t, when(Char.is_eq(x, c))), _) == matches(t, when(memb(c, 1n+p, x))) : Bool}
  when_or(Char.is_eq(x, c), memb(c, p, Chr{(Char.to_u32(x) + 1 : U32)}), t)

# Matching one character against an alternation of characters is memb.
def derM(n: Nat, +c: Char, +x: Char, +t: String) -> {matches(t, deriv(c, Laws.alt(chars.go(n, x)))) == matches(t, when(memb(c, n, x))) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Bool, matches(t, deriv(c, Laws.alt(chars.go(1n+p, x)))),
        Bool.or(matches(t, when(Char.is_eq(x, c))), matches(t, deriv(c, Laws.alt(chars.go(p, Chr{(Char.to_u32(x) + 1 : U32)}))))),
        matches(t, when(memb(c, 1n+p, x))),
        alt_or(t, when(Char.is_eq(x, c)), deriv(c, Laws.alt(chars.go(p, Chr{(Char.to_u32(x) + 1 : U32)})))),
        derM.go(c, x, p, t, derM(p, c, Chr{(Char.to_u32(x) + 1 : U32)}, t)))

# A range matches what the alternation of its characters matches.
def range_ok(s: String, +lo: Char, +hi: Char) -> {matches(s, RRange{lo, hi}) == matches(s, Laws.alt(chars.go(rcount(lo, hi), lo))) : Bool}:
  match s:
    case SNil{}:
      Equal.sym(Bool, nullable(Laws.alt(chars.go(rcount(lo, hi), lo))), False{}, nul_chars(rcount(lo, hi), lo))
    case SCon{+c, +t}:
      %rangeB(lo, hi, c) : {matches(t, when(_)) == matches(t, deriv(c, Laws.alt(chars.go(rcount(lo, hi), lo)))) : Bool}
      Equal.sym(Bool, matches(t, deriv(c, Laws.alt(chars.go(rcount(lo, hi), lo)))), matches(t, when(memb(c, rcount(lo, hi), lo))), derM(rcount(lo, hi), c, lo, t))

def range_ok_b(+book: Bk, +lo: Char, +hi: Char, +s: String)
  -> {ochk(book, RRange{lo, hi}, s) == ochk(book, Laws.alt(chars.go(rcount(lo, hi), lo)), s) : Bool}:
  %Equal.sym(Re, subst(Laws.alt(chars.go(rcount(lo, hi), lo)), tb(book, s)), Laws.alt(chars.go(rcount(lo, hi), lo)), sub_chars(rcount(lo, hi), lo, tb(book, s))) : {matches(s, RRange{lo, hi}) == matches(s, _) : Bool}
  range_ok(s, lo, hi)

# Depth
# =====

# U(d, r) below means subst(r, tbl(d, G)): r with references unfolded d times.

def str_tr(-x: String, -y: String, -R: Re, e: {x == y : String}, h: {matches(x, R) == True{} : Bool}) -> {matches(y, R) == True{} : Bool}:
  %e : {matches(_, R) == True{} : Bool}
  h

def star_nil(-t: String, -X: Re, e: {t == SNil{} : String}) -> {matches(t, RStar{X}) == True{} : Bool}:
  %Equal.sym(String, t, SNil{}, e) : {matches(_, RStar{X}) == True{} : Bool}
  {==}

def alt_false_l(+t: String, +x: Re, +y: Re, h: {matches(t, RAlt{x, y}) == False{} : Bool}) -> {matches(t, x) == False{} : Bool}:
  or_false_l(matches(t, x), matches(t, y),
    Equal.trans(Bool, Bool.or(matches(t, x), matches(t, y)), matches(t, RAlt{x, y}), False{},
      Equal.sym(Bool, matches(t, RAlt{x, y}), Bool.or(matches(t, x), matches(t, y)), alt_or(t, x, y)), h))

def alt_false_r(+t: String, +x: Re, +y: Re, h: {matches(t, RAlt{x, y}) == False{} : Bool}) -> {matches(t, y) == False{} : Bool}:
  or_false_r(matches(t, x), matches(t, y),
    Equal.trans(Bool, Bool.or(matches(t, x), matches(t, y)), matches(t, RAlt{x, y}), False{},
      Equal.sym(Bool, matches(t, RAlt{x, y}), Bool.or(matches(t, x), matches(t, y)), alt_or(t, x, y)), h))

def lsel_t(-b: Bool, e: {b == True{} : Bool}, -r: Re, -x: Re, -w: String, -v: Bool, h: {matches(w, lsel(b, r, x)) == v : Bool})
  -> {matches(w, RAlt{r, x}) == v : Bool}:
  %e : {matches(w, lsel(_, r, x)) == v : Bool}
  h

def lsel_f(-b: Bool, e: {b == False{} : Bool}, -r: Re, -x: Re, -w: String, -v: Bool, h: {matches(w, lsel(b, r, x)) == v : Bool})
  -> {matches(w, x) == v : Bool}:
  %e : {matches(w, lsel(_, r, x)) == v : Bool}
  h

# PartT(T, r, m, t) is "t matches subst(r, T)", except that a match of a star
# is given with its number of repetitions m.
def PartT(-T: Tb, r: Re, -m: Nat, -t: String) -> Type:
  match r:
    case RNone{}:
      {matches(t, RNone{}) == True{} : Bool}
    case REps{}:
      {matches(t, REps{}) == True{} : Bool}
    case RChr{c}:
      {matches(t, RChr{c}) == True{} : Bool}
    case RCat{a, b}:
      {matches(t, subst(RCat{a, b}, T)) == True{} : Bool}
    case RAlt{a, b}:
      {matches(t, subst(RAlt{a, b}, T)) == True{} : Bool}
    case RStar{a}:
      {matches(t, Laws.rep.exactly(m, subst(a, T))) == True{} : Bool}
    case RRef{n}:
      {matches(t, subst(RRef{n}, T)) == True{} : Bool}
    case RRange{lo, hi}:
      {matches(t, RRange{lo, hi}) == True{} : Bool}

def PartEx(-T: Tb, -r: Re, -t: String) -> Type:
  &m: Nat -> PartT(T, r, m, t)

def PartEx.elim(-T: Tb, -r: Re, -t: String, -C: Type, p: PartEx(T, r, t),
  f: @m: Nat -> PartT(T, r, m, t) -> C) -> C:
  (m, h) = p
  f(m, h)

def toPart(r: Re, +T: Tb, +t: String, h: {matches(t, subst(r, T)) == True{} : Bool}) -> PartEx(T, r, t):
  match r:
    case RNone{}:
      (0n, h)
    case REps{}:
      (0n, h)
    case RChr{c}:
      (0n, h)
    case RCat{a, b}:
      (0n, h)
    case RAlt{a, b}:
      (0n, h)
    case RStar{a}:
      any_elim(subst(a, T), t, h)
    case RRef{n}:
      (0n, h)
    case RRange{lo, hi}:
      (0n, h)

# Wit(T, T2, t): some reference matches a substring of t under T but not under T2.
def Wit(-T: Tb, -T2: Tb, -t: String) -> Type:
  &n: String -> &w: String -> Sub(w, t) & {matches(w, subst(RRef{n}, T)) == True{} : Bool} & {matches(w, subst(RRef{n}, T2)) == False{} : Bool}

def Wit.elim(-T: Tb, -T2: Tb, -t: String, -C: Type, p: Wit(T, T2, t),
  f: @n: String -> @w: String -> Sub(w, t) -> {matches(w, subst(RRef{n}, T)) == True{} : Bool} -> {matches(w, subst(RRef{n}, T2)) == False{} : Bool} -> C) -> C:
  (n, w, sb, h1, h2) = p
  f(n, w, sb, h1, h2)

def wit_lift(-T: Tb, -T2: Tb, -u: String, -t: String, p: Wit(T, T2, u), sb: Sub(u, t)) -> Wit(T, T2, t):
  (n, +w, s2, h1, h2) = p
  (n, w, sub_trans(w, u, t, s2, sb), h1, h2)

# If r matches t under T but not under T2, a reference is to blame.
def Det(+r: Re, m: Nat, +T: Tb, +T2: Tb, +t: String, h: PartT(T, r, m, t),
  +h2: {matches(t, subst(r, T2)) == False{} : Bool}) -> Wit(T, T2, t):
  match r:
    case RNone{}:
      none_elim(Wit(T, T2, t), t, h)
    case REps{}:
      Empty.absurd(Wit(T, T2, t), contra(matches(t, REps{}), h, h2))
    case RChr{c}:
      Empty.absurd(Wit(T, T2, t), contra(matches(t, RChr{c}), h, h2))
    case RRef{n}:
      (n, t, sub_refl(t), h, h2)
    case RRange{lo, hi}:
      Empty.absurd(Wit(T, T2, t), contra(matches(t, RRange{lo, hi}), h, h2))
    case RAlt{a, b}:
      either(&2, &2, {matches(t, subst(a, T)) == True{} : Bool}, {matches(t, subst(b, T)) == True{} : Bool}, Wit(T, T2, t),
        alt_elim(t, subst(a, T), subst(b, T), h),
        ka => PartEx.elim(T, a, t, Wit(T, T2, t), toPart(a, T, t, ka),
          +m2 => p => Det(a, m2, T, T2, t, p, alt_false_l(t, subst(a, T2), subst(b, T2), h2))),
        kb => PartEx.elim(T, b, t, Wit(T, T2, t), toPart(b, T, t, kb),
          +m2 => p => Det(b, m2, T, T2, t, p, alt_false_r(t, subst(a, T2), subst(b, T2), h2))))
    case RCat{a, b}:
      Split.elim(t, subst(a, T), subst(b, T), Wit(T, T2, t), cat_elim(t, subst(a, T), subst(b, T), h),
        +s1 => +s2 => +e => h1 => hb1 => bcase(Wit(T, T2, t), matches(s1, subst(a, T2)),
          ka2 => bcase(Wit(T, T2, t), matches(s2, subst(b, T2)),
            kb2 => Empty.absurd(Wit(T, T2, t), contra(matches(t, subst(RCat{a, b}, T2)),
              str_tr(String.append(s1, s2), t, subst(RCat{a, b}, T2), e,
                cat_intro(s1, subst(a, T2), subst(b, T2), s2, ka2, kb2)), h2)),
            kb2 => wit_lift(T, T2, s2, t, PartEx.elim(T, b, s2, Wit(T, T2, s2), toPart(b, T, s2, hb1),
              +m2 => p => Det(b, m2, T, T2, s2, p, kb2)), sub_r(s1, s2, t, e))),
          ka2 => wit_lift(T, T2, s1, t, PartEx.elim(T, a, s1, Wit(T, T2, s1), toPart(a, T, s1, h1),
            +m2 => p => Det(a, m2, T, T2, s1, p, ka2)), sub_l(s1, s2, t, e))))
    case RStar{a}:
      match m:
        case 0n:
          Empty.absurd(Wit(T, T2, t), contra(matches(t, RStar{subst(a, T2)}), star_nil(t, subst(a, T2), eps_elim(t, h)), h2))
        case 1n+ +p:
          Split.elim(t, subst(a, T), Laws.rep.exactly(p, subst(a, T)), Wit(T, T2, t),
            seq2_elim(t, subst(a, T), Laws.rep.exactly(p, subst(a, T)), h),
            +s1 => +s2 => +e => h1 => hr => bcase(Wit(T, T2, t), matches(s1, subst(a, T2)),
              ka2 => bcase(Wit(T, T2, t), matches(s2, RStar{subst(a, T2)}),
                kr => Empty.absurd(Wit(T, T2, t), contra(matches(t, RStar{subst(a, T2)}),
                  str_tr(String.append(s1, s2), t, RStar{subst(a, T2)}, e,
                    star_intro(s1, s2, subst(a, T2), ka2, kr)), h2)),
                kr => wit_lift(T, T2, s2, t, Det(r, p, T, T2, s2, hr, kr), sub_r(s1, s2, t, e))),
              ka2 => wit_lift(T, T2, s1, t, PartEx.elim(T, a, s1, Wit(T, T2, s1), toPart(a, T, s1, h1),
                +m2 => q => Det(a, m2, T, T2, s1, q, ka2)), sub_l(s1, s2, t, e))))

# LW(G2, T, T2, w): some entry of G2 matches w under table T but not under T2.
def LW(-G2: List<&2, Ent>, -T: Tb, -T2: Tb, -w: String) -> Type:
  &k: String -> &r: Re -> Mem(Ent, Ent{k, r}, G2) & {matches(w, subst(r, T)) == True{} : Bool} & {matches(w, subst(r, T2)) == False{} : Bool}

def LW.elim(-G2: List<&2, Ent>, -T: Tb, -T2: Tb, -w: String, -C: Type, p: LW(G2, T, T2, w),
  f: @k: String -> @r: Re -> Mem(Ent, Ent{k, r}, G2) -> {matches(w, subst(r, T)) == True{} : Bool} -> {matches(w, subst(r, T2)) == False{} : Bool} -> C) -> C:
  (k, r, m, h1, h2) = p
  f(k, r, m, h1, h2)

def LW.cons(-e: Ent, -rest: List<&2, Ent>, -T: Tb, -T2: Tb, -w: String, p: LW(rest, T, T2, w)) -> LW(e <> rest, T, T2, w):
  (k, r, m, h1, h2) = p
  (k, r, Inr{m}, h1, h2)

# If a lookup matches w under T but not under T2, one of its entries is to blame.
def LkW(G2: List<&2, Ent>, +T: Tb, +T2: Tb, +w: String, +ln: String,
  +h: {matches(w, lookupE(tblRow(G2, T), ln)) == True{} : Bool},
  +h2: {matches(w, lookupE(tblRow(G2, T2), ln)) == False{} : Bool}) -> LW(G2, T, T2, w):
  match G2:
    case []:
      none_elim(LW([], T, T2, w), w, h)
    case Ent{+k, +r} <> +rest:
      bcase(LW(Ent{k, r} <> rest, T, T2, w), String.eq(String.to_lower(k), ln),
        +e => either(&2, &2, {matches(w, subst(r, T)) == True{} : Bool},
          {matches(w, lookupE(tblRow(rest, T), ln)) == True{} : Bool}, LW(Ent{k, r} <> rest, T, T2, w),
          alt_elim(w, subst(r, T), lookupE(tblRow(rest, T), ln),
            lsel_t(String.eq(String.to_lower(k), ln), e, subst(r, T), lookupE(tblRow(rest, T), ln), w, True{}, h)),
          kl => (k, r, Inl{{==}}, kl,
            alt_false_l(w, subst(r, T2), lookupE(tblRow(rest, T2), ln),
              lsel_t(String.eq(String.to_lower(k), ln), e, subst(r, T2), lookupE(tblRow(rest, T2), ln), w, False{}, h2))),
          kr => LW.cons(Ent{k, r}, rest, T, T2, w, LkW(rest, T, T2, w, ln, kr,
            alt_false_r(w, subst(r, T2), lookupE(tblRow(rest, T2), ln),
              lsel_t(String.eq(String.to_lower(k), ln), e, subst(r, T2), lookupE(tblRow(rest, T2), ln), w, False{}, h2))))),
        +e => LW.cons(Ent{k, r}, rest, T, T2, w, LkW(rest, T, T2, w, ln,
          lsel_f(String.eq(String.to_lower(k), ln), e, subst(r, T), lookupE(tblRow(rest, T), ln), w, True{}, h),
          lsel_f(String.eq(String.to_lower(k), ln), e, subst(r, T2), lookupE(tblRow(rest, T2), ln), w, False{}, h2))))

# Unfolding deeper never loses a match.
def mono1(d: Nat, +G: List<&2, Ent>, +t: String, +r: Re, h: {matches(t, subst(r, tbl(d, G))) == True{} : Bool})
  -> {matches(t, subst(r, tbl(1n+d, G))) == True{} : Bool}:
  match d:
    case 0n:
      bcase({matches(t, subst(r, tbl(1n, G))) == True{} : Bool}, matches(t, subst(r, tbl(1n, G))),
        k => k,
        +k => Empty.absurd({matches(t, subst(r, tbl(1n, G))) == True{} : Bool},
          PartEx.elim(tbl(0n, G), r, t, Empty, toPart(r, tbl(0n, G), t, h),
            +m => p => Wit.elim(tbl(0n, G), tbl(1n, G), t, Empty, Det(r, m, tbl(0n, G), tbl(1n, G), t, p, k),
              n => +w => sb => h1 => h2 => none_elim(Empty, w, h1)))))
    case 1n+ +p:
      bcase({matches(t, subst(r, tbl(1n+1n+p, G))) == True{} : Bool}, matches(t, subst(r, tbl(1n+1n+p, G))),
        k => k,
        +k => Empty.absurd({matches(t, subst(r, tbl(1n+1n+p, G))) == True{} : Bool},
          PartEx.elim(tbl(1n+p, G), r, t, Empty, toPart(r, tbl(1n+p, G), t, h),
            +m => q => Wit.elim(tbl(1n+p, G), tbl(1n+1n+p, G), t, Empty, Det(r, m, tbl(1n+p, G), tbl(1n+1n+p, G), t, q, k),
              +n => +w => sb => h1 => h2 => LW.elim(G, tbl(p, G), tbl(1n+p, G), w, Empty,
                LkW(G, tbl(p, G), tbl(1n+p, G), w, String.to_lower(n), h1, h2),
                k2 => +r2 => mem => e1 => e2 => contra(matches(w, subst(r2, tbl(1n+p, G))), mono1(p, G, w, r2, e1), e2))))))

def mono_add(j: Nat, +d: Nat, +G: List<&2, Ent>, +t: String, +r: Re, h: {matches(t, subst(r, tbl(d, G))) == True{} : Bool})
  -> {matches(t, subst(r, tbl(Nat.add(j, d), G))) == True{} : Bool}:
  match j:
    case 0n:
      h
    case 1n+ +p:
      mono1(Nat.add(p, d), G, t, r, mono_add(p, d, G, t, r, h))

# Bound
# =====

# A depth that suffices for s. evC(e, G, Cell{r, w}) says w matches U(e, r);
# cnt(e, ...) counts the cells of s that do. The count grows with e and is at
# most the number of cells, so it stops growing somewhere below that number.
# Once it stops growing, unfolding further changes nothing (rstep).

def evC(e: Nat, +G: List<&2, Ent>, c: Cell) -> Bool:
  match c:
    case Cell{r, w}:
      matches(w, subst(r, tbl(e, G)))

def cnt(+e: Nat, +G: List<&2, Ent>, cs: List<&2, Cell>) -> Nat:
  match cs:
    case []:
      0n
    case c <> rest:
      Nat.add(b2n(evC(e, G, c)), cnt(e, G, rest))

def cell_mono(+e: Nat, +G: List<&2, Ent>, c: Cell) -> {le(b2n(evC(e, G, c)), b2n(evC(1n+e, G, c))) == True{} : Bool}:
  match c:
    case Cell{+r, +w}:
      bimp(matches(w, subst(r, tbl(e, G))), matches(w, subst(r, tbl(1n+e, G))), k => mono1(e, G, w, r, k))

def cnt_mono(+e: Nat, +G: List<&2, Ent>, cs: List<&2, Cell>) -> {le(cnt(e, G, cs), cnt(1n+e, G, cs)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> +rest:
      le_add(b2n(evC(e, G, c)), b2n(evC(1n+e, G, c)), cnt(e, G, rest), cnt(1n+e, G, rest), cell_mono(e, G, c), cnt_mono(e, G, rest))

def cnt_le_len(+e: Nat, +G: List<&2, Ent>, cs: List<&2, Cell>) -> {le(cnt(e, G, cs), clen(cs)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> +rest:
      le_add(b2n(evC(e, G, c)), 1n, cnt(e, G, rest), clen(rest), b2n_le1(evC(e, G, c)), cnt_le_len(e, G, rest))

def ext.here(+e: Nat, +G: List<&2, Ent>, -c: Cell, -x: Cell, +ec: {c == x : Cell}, ex: {evC(e, G, c) == evC(1n+e, G, c) : Bool},
  h: {evC(1n+e, G, x) == True{} : Bool}) -> {evC(e, G, x) == True{} : Bool}:
  %ec : {evC(e, G, _) == True{} : Bool}
  %Equal.sym(Bool, evC(e, G, c), evC(1n+e, G, c), ex) : {_ == True{} : Bool}
  %Equal.sym(Cell, c, x, ec) : {evC(1n+e, G, _) == True{} : Bool}
  h

# If the count does not grow from e to 1+e, no cell starts matching.
def Ext(+e: Nat, +G: List<&2, Ent>, cs: List<&2, Cell>, -x: Cell, mem: Mem(Cell, x, cs),
  hc: {cnt(e, G, cs) == cnt(1n+e, G, cs) : Nat}, h: {evC(1n+e, G, x) == True{} : Bool}) -> {evC(e, G, x) == True{} : Bool}:
  match cs:
    case []:
      Empty.absurd({evC(e, G, x) == True{} : Bool}, mem)
    case +c <> +rest:
      match mem:
        case Inl{ec}:
          ext.here(e, G, c, x, ec,
            bsplit_l(evC(e, G, c), evC(1n+e, G, c), cnt(e, G, rest), cnt(1n+e, G, rest), cell_mono(e, G, c), cnt_mono(e, G, rest), hc), h)
        case Inr{m2}:
          Ext(e, G, rest, x, m2,
            bsplit_r(evC(e, G, c), evC(1n+e, G, c), cnt(e, G, rest), cnt(1n+e, G, rest), cell_mono(e, G, c), cnt_mono(e, G, rest), hc), h)

# If the count does not grow from f to 1+f, unfolding from depth 2+f to 1+f
# loses no match on a substring of s.
def rstep(+f: Nat, +G: List<&2, Ent>, +s: String, +r: Re, +t: String, sb: Sub(t, s),
  hc: {cnt(f, G, cells(s, G)) == cnt(1n+f, G, cells(s, G)) : Nat},
  h: {matches(t, subst(r, tbl(1n+1n+f, G))) == True{} : Bool}) -> {matches(t, subst(r, tbl(1n+f, G))) == True{} : Bool}:
  bcase({matches(t, subst(r, tbl(1n+f, G))) == True{} : Bool}, matches(t, subst(r, tbl(1n+f, G))),
    k => k,
    +k => Empty.absurd({matches(t, subst(r, tbl(1n+f, G))) == True{} : Bool},
      PartEx.elim(tbl(1n+1n+f, G), r, t, Empty, toPart(r, tbl(1n+1n+f, G), t, h),
        +m => p => Wit.elim(tbl(1n+1n+f, G), tbl(1n+f, G), t, Empty, Det(r, m, tbl(1n+1n+f, G), tbl(1n+f, G), t, p, k),
          +n => +w => sbw => h1 => h2 => LW.elim(G, tbl(1n+f, G), tbl(f, G), w, Empty,
            LkW(G, tbl(1n+f, G), tbl(f, G), w, String.to_lower(n), h1, h2),
            +k2 => +r2 => mem => e1 => e2 => contra(evC(f, G, Cell{r2, w}),
              Ext(f, G, cells(s, G), Cell{r2, w},
                mem_pairs(r2, k2, w, subs(s), G, mem_subs_via(w, s, sub_trans(w, t, s, sbw, sb)), mem), hc, e1), e2))))))

def cell_back(+e: Nat, +G: List<&2, Ent>, +s: String, x: Cell, mem: Mem(Cell, x, cells(s, G)),
  hc: {cnt(e, G, cells(s, G)) == cnt(1n+e, G, cells(s, G)) : Nat})
  -> {le(b2n(evC(1n+1n+e, G, x)), b2n(evC(1n+e, G, x))) == True{} : Bool}:
  match x:
    case Cell{+r, +w}:
      bimp(matches(w, subst(r, tbl(1n+1n+e, G))), matches(w, subst(r, tbl(1n+e, G))),
        k => rstep(e, G, s, r, w, mem_subs_inv(s, w, mem_pairs_inv(r, w, subs(s), G, mem)), hc, k))

def cnt_back(+e: Nat, +G: List<&2, Ent>, +s: String, cs: List<&2, Cell>, +pre: List<&2, Cell>,
  +hpre: {gapp(Cell, pre, cs) == cells(s, G) : List<&2, Cell>},
  +hc: {cnt(e, G, cells(s, G)) == cnt(1n+e, G, cells(s, G)) : Nat})
  -> {le(cnt(1n+1n+e, G, cs), cnt(1n+e, G, cs)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> +rest:
      le_add(b2n(evC(1n+1n+e, G, c)), b2n(evC(1n+e, G, c)), cnt(1n+1n+e, G, rest), cnt(1n+e, G, rest),
        cell_back(e, G, s, c, mem_tr(Cell, c, gapp(Cell, pre, c <> rest), cells(s, G), hpre, mem_gapp_r(Cell, c, pre, c <> rest, Inl{{==}})), hc),
        cnt_back(e, G, s, rest, gapp(Cell, pre, [c]),
          Equal.trans(List<&2, Cell>, gapp(Cell, gapp(Cell, pre, [c]), rest), gapp(Cell, pre, c <> rest), cells(s, G), gapp_snoc(Cell, pre, c, rest), hpre), hc))

def stab_step(+e: Nat, +G: List<&2, Ent>, +s: String, hc: {cnt(e, G, cells(s, G)) == cnt(1n+e, G, cells(s, G)) : Nat})
  -> {cnt(1n+e, G, cells(s, G)) == cnt(1n+1n+e, G, cells(s, G)) : Nat}:
  antisym(cnt(1n+e, G, cells(s, G)), cnt(1n+1n+e, G, cells(s, G)), cnt_mono(1n+e, G, cells(s, G)), cnt_back(e, G, s, cells(s, G), [], {==}, hc))

def prop(i: Nat, +e: Nat, +G: List<&2, Ent>, +s: String, hc: {cnt(e, G, cells(s, G)) == cnt(1n+e, G, cells(s, G)) : Nat})
  -> {cnt(Nat.add(i, e), G, cells(s, G)) == cnt(1n+Nat.add(i, e), G, cells(s, G)) : Nat}:
  match i:
    case 0n:
      hc
    case 1n+ +p:
      stab_step(Nat.add(p, e), G, s, prop(p, e, G, s, hc))

def grow.stable(+x: Nat, +G: List<&2, Ent>, +s: String, ex: {x == clen(cells(s, G)) : Nat},
  hs: {cnt(x, G, cells(s, G)) == cnt(1n+x, G, cells(s, G)) : Nat}) -> {eqn(cnt(clen(cells(s, G)), G, cells(s, G)), cnt(1n+clen(cells(s, G)), G, cells(s, G))) == True{} : Bool}:
  %ex : {eqn(cnt(_, G, cells(s, G)), cnt(1n+_, G, cells(s, G))) == True{} : Bool}
  eqn_of_eq(cnt(x, G, cells(s, G)), cnt(1n+x, G, cells(s, G)), hs)

def grow.unstable(+i: Nat, +G: List<&2, Ent>, +s: String, hc: {le(i, cnt(i, G, cells(s, G))) == True{} : Bool},
  k: {eqn(cnt(i, G, cells(s, G)), cnt(1n+i, G, cells(s, G))) == False{} : Bool}) -> {le(1n+i, cnt(1n+i, G, cells(s, G))) == True{} : Bool}:
  le_trans(1n+i, 1n+cnt(i, G, cells(s, G)), cnt(1n+i, G, cells(s, G)), hc,
    lt_of_ne(cnt(i, G, cells(s, G)), cnt(1n+i, G, cells(s, G)), cnt_mono(i, G, cells(s, G)), k))

def grow.last.go(-i: Nat, -G: List<&2, Ent>, -s: String, ei: {i == clen(cells(s, G)) : Nat},
  h: {le(1n+i, clen(cells(s, G))) == True{} : Bool}) -> {le(1n+i, i) == True{} : Bool}:
  %Equal.sym(Nat, i, clen(cells(s, G)), ei) : {le(1n+i, _) == True{} : Bool}
  h

def grow.last(+i: Nat, +G: List<&2, Ent>, +s: String, ei: {i == clen(cells(s, G)) : Nat},
  h: {le(1n+i, cnt(1n+i, G, cells(s, G))) == True{} : Bool}) -> Empty:
  succ_le_absurd(i, grow.last.go(i, G, s, ei, le_trans(1n+i, cnt(1n+i, G, cells(s, G)), clen(cells(s, G)), h, cnt_le_len(1n+i, G, cells(s, G)))))

# If the count still grows at the number of cells, it grew at every step
# before, so it would exceed the number of cells.
def grow(j: Nat, +i: Nat, +G: List<&2, Ent>, +s: String, +hT: {Nat.add(j, i) == clen(cells(s, G)) : Nat},
  +hn: {eqn(cnt(clen(cells(s, G)), G, cells(s, G)), cnt(1n+clen(cells(s, G)), G, cells(s, G))) == False{} : Bool},
  +hc: {le(i, cnt(i, G, cells(s, G))) == True{} : Bool}) -> Empty:
  match j:
    case 0n:
      bcase(Empty, eqn(cnt(i, G, cells(s, G)), cnt(1n+i, G, cells(s, G))),
        k => contra(eqn(cnt(clen(cells(s, G)), G, cells(s, G)), cnt(1n+clen(cells(s, G)), G, cells(s, G))),
          grow.stable(i, G, s, hT, eqn_sound(cnt(i, G, cells(s, G)), cnt(1n+i, G, cells(s, G)), k)), hn),
        k => grow.last(i, G, s, hT, grow.unstable(i, G, s, hc, k)))
    case 1n+ +p:
      bcase(Empty, eqn(cnt(i, G, cells(s, G)), cnt(1n+i, G, cells(s, G))),
        k => contra(eqn(cnt(clen(cells(s, G)), G, cells(s, G)), cnt(1n+clen(cells(s, G)), G, cells(s, G))),
          grow.stable(Nat.add(1n+p, i), G, s, hT, prop(1n+p, i, G, s, eqn_sound(cnt(i, G, cells(s, G)), cnt(1n+i, G, cells(s, G)), k))), hn),
        k => grow(p, 1n+i, G, s,
          Equal.trans(Nat, Nat.add(p, 1n+i), 1n+Nat.add(p, i), clen(cells(s, G)), plus_succ_r(p, i), hT), hn,
          grow.unstable(i, G, s, hc, k)))

# The count stops growing at the number of cells.
def stab_T(+G: List<&2, Ent>, +s: String) -> {cnt(clen(cells(s, G)), G, cells(s, G)) == cnt(1n+clen(cells(s, G)), G, cells(s, G)) : Nat}:
  bcase({cnt(clen(cells(s, G)), G, cells(s, G)) == cnt(1n+clen(cells(s, G)), G, cells(s, G)) : Nat},
    eqn(cnt(clen(cells(s, G)), G, cells(s, G)), cnt(1n+clen(cells(s, G)), G, cells(s, G))),
    k => eqn_sound(cnt(clen(cells(s, G)), G, cells(s, G)), cnt(1n+clen(cells(s, G)), G, cells(s, G)), k),
    k => Empty.absurd({cnt(clen(cells(s, G)), G, cells(s, G)) == cnt(1n+clen(cells(s, G)), G, cells(s, G)) : Nat},
      grow(clen(cells(s, G)), 0n, G, s, plus_zero_r(clen(cells(s, G))), k, {==})))

def up(i: Nat, +G: List<&2, Ent>, +s: String, +r: Re, h: {matches(s, subst(r, tbl(1n+Nat.add(i, clen(cells(s, G))), G))) == True{} : Bool})
  -> {matches(s, subst(r, tbl(1n+clen(cells(s, G)), G))) == True{} : Bool}:
  match i:
    case 0n:
      h
    case 1n+ +p:
      up(p, G, s, r, rstep(Nat.add(p, clen(cells(s, G))), G, s, r, s, sub_refl(s), prop(p, clen(cells(s, G)), G, s, stab_T(G, s)), h))

def dtr(-G: List<&2, Ent>, -s: String, -r: Re, -x: Nat, -y: Nat, e: {x == y : Nat}, h: {matches(s, subst(r, tbl(x, G))) == True{} : Bool})
  -> {matches(s, subst(r, tbl(y, G))) == True{} : Bool}:
  %e : {matches(s, subst(r, tbl(_, G))) == True{} : Bool}
  h

# Any depth that matches can be replaced by bound(s, G).
def shrink(+G: List<&2, Ent>, +s: String, +d: Nat, +r: Re, +h: {matches(s, subst(r, tbl(d, G))) == True{} : Bool})
  -> {matches(s, subst(r, tbl(bound(s, G), G))) == True{} : Bool}:
  either(&1, &1, LeW(d, clen(cells(s, G))), GeW(d, clen(cells(s, G))), {matches(s, subst(r, tbl(bound(s, G), G))) == True{} : Bool},
    cmpN(d, clen(cells(s, G))),
    x => LeW.elim(d, clen(cells(s, G)), {matches(s, subst(r, tbl(bound(s, G), G))) == True{} : Bool}, x,
      +j => e => dtr(G, s, r, Nat.add(j, d), 1n+clen(cells(s, G)), e, mono_add(j, d, G, s, r, h))),
    y => GeW.elim(d, clen(cells(s, G)), {matches(s, subst(r, tbl(bound(s, G), G))) == True{} : Bool}, y,
      +i => e => up(i, G, s, r, dtr(G, s, r, d, 1n+Nat.add(i, clen(cells(s, G))), e, h))))

# Books
# =====

def ex_comm(m: Nat, +r: Re, +T: Tb) -> {subst(exactly.go(m, r), T) == exactly.go(m, subst(r, T)) : Re}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      %ex_comm(p, r, T) : {subst(exactly.go(1n+p, r), T) == Laws.seq([subst(r, T), _]) : Re}
      {==}

def al_comm(n: Nat, +r: Re, +T: Tb) -> {subst(at_least.go(n, r), T) == at_least.go(n, subst(r, T)) : Re}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      %al_comm(p, r, T) : {subst(at_least.go(1n+p, r), T) == Laws.seq([subst(r, T), _]) : Re}
      {==}

def am_comm(n: Nat, +r: Re, +T: Tb) -> {subst(at_most.go(n, r), T) == at_most.go(n, subst(r, T)) : Re}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      %am_comm(p, r, T) : {subst(at_most.go(1n+p, r), T) == Laws.alt([Laws.empty, Laws.seq([subst(r, T), _])]) : Re}
      {==}

def rp_comm(a: Nat, b: Nat, +r: Re, +T: Tb) -> {subst(rep.go(a, b, r), T) == rep.go(a, b, subst(r, T)) : Re}:
  match a:
    case 0n:
      am_comm(b, r, T)
    case 1n+ +ap:
      match b:
        case 0n:
          {==}
        case 1n+ +bp:
          %rp_comm(ap, bp, r, T) : {subst(rep.go(1n+ap, 1n+bp, r), T) == Laws.seq([subst(r, T), _]) : Re}
          {==}

def lsel_comm(b: Bool, -r: Re, -x: Re, -T: Tb) -> {lsel(b, subst(r, T), subst(x, T)) == subst(lsel(b, r, x), T) : Re}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def lk_comm(G2: List<&2, Ent>, +T: Tb, +ln: String) -> {lookupE(tblRow(G2, T), ln) == subst(lookupE(G2, ln), T) : Re}:
  match G2:
    case []:
      {==}
    case Ent{+k, +r} <> rest:
      %Equal.sym(Re, lookupE(tblRow(rest, T), ln), subst(lookupE(rest, ln), T), lk_comm(rest, T, ln))
        : {lsel(String.eq(String.to_lower(k), ln), subst(r, T), _) == subst(lsel(String.eq(String.to_lower(k), ln), r, lookupE(rest, ln)), T) : Re}
      lsel_comm(String.eq(String.to_lower(k), ln), r, lookupE(rest, ln), T)

def lcon(b: Bool, r: Re, x: Re, +s: String, +T: Tb)
  -> {matches(s, subst(lsel(b, r, x), T)) == Bool.or(Bool.and(b, matches(s, subst(r, T))), matches(s, subst(x, T))) : Bool}:
  match b:
    case True{}:
      alt_or(s, subst(r, T), subst(x, T))
    case False{}:
      {==}

def alt_con_b(+book: Bk, +r: Re, +y: Re, +s: String) -> {ochk(book, RAlt{r, y}, s) == Bool.or(ochk(book, r, s), ochk(book, y, s)) : Bool}:
  alt_or(s, subst(r, tb(book, s)), subst(y, tb(book, s)))

def seq_intro_b(book: Bk, +r: Re, +y: Re, +s1: String, +s2: String, h1: {ochk(book, r, s1) == True{} : Bool}, h2: {ochk(book, y, s2) == True{} : Bool})
  -> {ochk(book, RCat{r, y}, String.append(s1, s2)) == True{} : Bool}:
  match book:
    case BLim{+d, +g}:
      cat_intro(s1, subst(r, tbl(d, g)), subst(y, tbl(d, g)), s2, h1, h2)
    case BFull{+g}:
      shrink(g, String.append(s1, s2), Nat.add(bound(s2, g), bound(s1, g)), RCat{r, y},
        cat_intro(s1, subst(r, tbl(Nat.add(bound(s2, g), bound(s1, g)), g)), subst(y, tbl(Nat.add(bound(s2, g), bound(s1, g)), g)), s2,
          mono_add(bound(s2, g), bound(s1, g), g, s1, r, h1),
          dtr(g, s2, y, Nat.add(bound(s1, g), bound(s2, g)), Nat.add(bound(s2, g), bound(s1, g)), add_comm(bound(s1, g), bound(s2, g)),
            mono_add(bound(s1, g), bound(s2, g), g, s2, y, h2))))

def seq_elim_b(book: Bk, +r: Re, +y: Re, +s: String, h: {ochk(book, RCat{r, y}, s) == True{} : Bool})
  -> &s1: String -> &s2: String -> {String.append(s1, s2) == s : String} & {ochk(book, r, s1) == True{} : Bool} & {ochk(book, y, s2) == True{} : Bool}:
  match book:
    case BLim{+d, +g}:
      cat_elim(s, subst(r, tbl(d, g)), subst(y, tbl(d, g)), h)
    case BFull{+g}:
      Split.elim(s, subst(r, tbl(bound(s, g), g)), subst(y, tbl(bound(s, g), g)),
        &s1: String -> &s2: String -> {String.append(s1, s2) == s : String} & {ochk(BFull{g}, r, s1) == True{} : Bool} & {ochk(BFull{g}, y, s2) == True{} : Bool},
        cat_elim(s, subst(r, tbl(bound(s, g), g)), subst(y, tbl(bound(s, g), g)), h),
        +s1 => +s2 => e => h1 => h2 => (s1, s2, e, shrink(g, s1, bound(s, g), r, h1), shrink(g, s2, bound(s, g), y, h2)))

def any_intro_b(+book: Bk, +m: Nat, +r: Re, +s: String, hs: {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool})
  -> {ochk(book, RStar{r}, s) == True{} : Bool}:
  any_intro(m, subst(r, tb(book, s)), s,
    mtr(s, subst(exactly.go(m, r), tb(book, s)), exactly.go(m, subst(r, tb(book, s))), ex_comm(m, r, tb(book, s)), hs))

def any_elim_b(+book: Bk, +r: Re, +s: String, hs: {ochk(book, RStar{r}, s) == True{} : Bool})
  -> &m: Nat -> {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  ExAny.elim(subst(r, tb(book, s)), s, &m: Nat -> {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool},
    any_elim(subst(r, tb(book, s)), s, hs),
    +m => p => (m, mtr(s, exactly.go(m, subst(r, tb(book, s))), subst(exactly.go(m, r), tb(book, s)),
      Equal.sym(Re, subst(exactly.go(m, r), tb(book, s)), exactly.go(m, subst(r, tb(book, s))), ex_comm(m, r, tb(book, s))), p)))

def al_intro_b(+book: Bk, +n: Nat, +m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}, +r: Re, +s: String,
  hs: {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}) -> {ochk(book, Laws.rep.at_least(n, r), s) == True{} : Bool}:
  mtr(s, at_least.go(n, subst(r, tb(book, s))), subst(at_least.go(n, r), tb(book, s)),
    Equal.sym(Re, subst(at_least.go(n, r), tb(book, s)), at_least.go(n, subst(r, tb(book, s))), al_comm(n, r, tb(book, s))),
    at_least_intro(n, m, h, subst(r, tb(book, s)), s,
      mtr(s, subst(exactly.go(m, r), tb(book, s)), exactly.go(m, subst(r, tb(book, s))), ex_comm(m, r, tb(book, s)), hs)))

def al_elim_b(+book: Bk, +n: Nat, +r: Re, +s: String, hs: {ochk(book, Laws.rep.at_least(n, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(n, m) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  ExLo.elim(n, subst(r, tb(book, s)), s, &m: Nat -> {Nat.is_le(n, m) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool},
    at_least_elim(n, subst(r, tb(book, s)), s,
      mtr(s, subst(at_least.go(n, r), tb(book, s)), at_least.go(n, subst(r, tb(book, s))), al_comm(n, r, tb(book, s)), hs)),
    +m => le => p => (m, le, mtr(s, exactly.go(m, subst(r, tb(book, s))), subst(exactly.go(m, r), tb(book, s)),
      Equal.sym(Re, subst(exactly.go(m, r), tb(book, s)), exactly.go(m, subst(r, tb(book, s))), ex_comm(m, r, tb(book, s))), p)))

def am_intro_b(+book: Bk, +n: Nat, +m: Nat, h: {Nat.is_le(m, n) == True{} : Bool}, +r: Re, +s: String,
  hs: {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}) -> {ochk(book, Laws.rep.at_most(n, r), s) == True{} : Bool}:
  mtr(s, at_most.go(n, subst(r, tb(book, s))), subst(at_most.go(n, r), tb(book, s)),
    Equal.sym(Re, subst(at_most.go(n, r), tb(book, s)), at_most.go(n, subst(r, tb(book, s))), am_comm(n, r, tb(book, s))),
    at_most_intro(n, m, h, subst(r, tb(book, s)), s,
      mtr(s, subst(exactly.go(m, r), tb(book, s)), exactly.go(m, subst(r, tb(book, s))), ex_comm(m, r, tb(book, s)), hs)))

def am_elim_b(+book: Bk, +n: Nat, +r: Re, +s: String, hs: {ochk(book, Laws.rep.at_most(n, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(m, n) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  ExHi.elim(n, subst(r, tb(book, s)), s, &m: Nat -> {Nat.is_le(m, n) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool},
    at_most_elim(n, subst(r, tb(book, s)), s,
      mtr(s, subst(at_most.go(n, r), tb(book, s)), at_most.go(n, subst(r, tb(book, s))), am_comm(n, r, tb(book, s)), hs)),
    +m => le => p => (m, le, mtr(s, exactly.go(m, subst(r, tb(book, s))), subst(exactly.go(m, r), tb(book, s)),
      Equal.sym(Re, subst(exactly.go(m, r), tb(book, s)), exactly.go(m, subst(r, tb(book, s))), ex_comm(m, r, tb(book, s))), p)))

def rep_intro_b(+book: Bk, +a: Nat, +b: Nat, +m: Nat, ha: {Nat.is_le(a, m) == True{} : Bool}, hb: {Nat.is_le(m, b) == True{} : Bool},
  +r: Re, +s: String, hs: {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}) -> {ochk(book, Laws.rep(a, b, r), s) == True{} : Bool}:
  mtr(s, rep.go(a, b, subst(r, tb(book, s))), subst(rep.go(a, b, r), tb(book, s)),
    Equal.sym(Re, subst(rep.go(a, b, r), tb(book, s)), rep.go(a, b, subst(r, tb(book, s))), rp_comm(a, b, r, tb(book, s))),
    rep_intro(a, b, m, ha, hb, subst(r, tb(book, s)), s,
      mtr(s, subst(exactly.go(m, r), tb(book, s)), exactly.go(m, subst(r, tb(book, s))), ex_comm(m, r, tb(book, s)), hs)))

def rep_elim_b(+book: Bk, +a: Nat, +b: Nat, +r: Re, +s: String, hs: {ochk(book, Laws.rep(a, b, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(a, m) == True{} : Bool} & {Nat.is_le(m, b) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  ExIn.elim(a, b, subst(r, tb(book, s)), s,
    &m: Nat -> {Nat.is_le(a, m) == True{} : Bool} & {Nat.is_le(m, b) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool},
    rep_elim(a, b, subst(r, tb(book, s)), s,
      mtr(s, subst(rep.go(a, b, r), tb(book, s)), rep.go(a, b, subst(r, tb(book, s))), rp_comm(a, b, r, tb(book, s)), hs)),
    +m => la => lb => p => (m, la, lb, mtr(s, exactly.go(m, subst(r, tb(book, s))), subst(exactly.go(m, r), tb(book, s)),
      Equal.sym(Re, subst(exactly.go(m, r), tb(book, s)), exactly.go(m, subst(r, tb(book, s))), ex_comm(m, r, tb(book, s))), p)))

def full_elim_b(+G: List<&2, Ent>, -r: Re, +s: String, h: {matches(s, subst(r, tbl(bound(s, G), G))) == True{} : Bool})
  -> &d: Nat -> {matches(s, subst(r, tbl(d, G))) == True{} : Bool}:
  (bound(s, G), h)

def lookup_con_b(+book: Bk, +k: String, +r: Re, +G: List<&2, Ent>, +ln: String, +s: String)
  -> {ochk(book, lookupE(Ent{k, r} <> G, ln), s) == Bool.or(Bool.and(String.eq(String.to_lower(k), ln), ochk(book, r, s)), ochk(book, lookupE(G, ln), s)) : Bool}:
  lcon(String.eq(String.to_lower(k), ln), r, lookupE(G, ln), s, tb(book, s))

def ref_succ_b(+d: Nat, +G: List<&2, Ent>, +ln: String, -s: String)
  -> {matches(s, lookupE(tblRow(G, tbl(d, G)), ln)) == matches(s, subst(lookupE(G, ln), tbl(d, G))) : Bool}:
  mcong(s, lookupE(tblRow(G, tbl(d, G)), ln), subst(lookupE(G, ln), tbl(d, G)), lk_comm(G, tbl(d, G), ln))

# Bounds
# ======

# tbB(B0, d, G) is tbl(d, G) with B0 in place of TDead at the bottom. With
# TTop at the bottom, references that run out of depth match every string, so
# that a string matching at any depth also matches there (upper).

def tbB(B0: Tb, d: Nat, +G: List<&2, Ent>) -> Tb:
  match d:
    case 0n:
      B0
    case 1n+p:
      TLive{tblRow(G, tbB(B0, p, G))}

def tbB_dead(d: Nat, +G: List<&2, Ent>) -> {tbB(TDead{}, d, G) == tbl(d, G) : Tb}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %tbB_dead(p, G) : {TLive{tblRow(G, tbB(TDead{}, p, G))} == TLive{tblRow(G, _)} : Tb}
      {==}

def fin_le(ab: Bool, bb: Bool, t: Cmp, ht: {Cmp.is_le(t) == True{} : Bool}, hb: {Cmp.is_le(Bool.cmp(ab, bb)) == True{} : Bool})
  -> {Cmp.is_le(Word.cmp.fin(ab, bb, t)) == True{} : Bool}:
  match t:
    case LT{}:
      {==}
    case EQ{}:
      hb
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, false_ne_true(ht))

def blt_f(b: Bool) -> {Cmp.is_le(Bool.cmp(False{}, b)) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def blt_t(b: Bool) -> {Cmp.is_le(Bool.cmp(b, True{})) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def wle_zero(n: Nat, w: Word(n)) -> {Cmp.is_le(Word.cmp(n, Word.zero(n), w)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{+b, +wt}:
          fin_le(False{}, b, Word.cmp(p, Word.zero(p), wt), wle_zero(p, wt), blt_f(b))

def wle_ones(n: Nat, w: Word(n)) -> {Cmp.is_le(Word.cmp(n, w, ones(n))) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{+b, +wt}:
          fin_le(b, True{}, Word.cmp(p, wt, ones(p)), wle_ones(p, wt), blt_t(b))

def all_in(c: Char) -> {inR(Chr{U32{Word.zero(32n)}}, Chr{U32{ones(32n)}}, c) == True{} : Bool}:
  match c:
    case Chr{U32{+w}}:
      and_intro(Cmp.is_le(Word.cmp(32n, Word.zero(32n), w)), Cmp.is_le(Word.cmp(32n, w, ones(32n))), wle_zero(32n, w), wle_ones(32n, w))

def sig_all(t: String) -> {matches(t, SIG) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      %Equal.sym(Bool, inR(Chr{U32{Word.zero(32n)}}, Chr{U32{ones(32n)}}, c), True{}, all_in(c)) : {matches(u, RCat{when(_), SIG}) == True{} : Bool}
      cat_null(u, REps{}, SIG, {==}, sig_all(u))

# Incl(T, T2): every reference matches under T2 whatever it matches under T.
def Incl(-T: Tb, -T2: Tb) -> Type:
  @ln: String -> @w: String -> {matches(w, refv(T, ln)) == True{} : Bool} -> {matches(w, refv(T2, ln)) == True{} : Bool}

# A table that matches more for every reference matches more for every rule.
def mono_tb(+r: Re, +T: Tb, +T2: Tb, +t: String, h: {matches(t, subst(r, T)) == True{} : Bool}, inc: Incl(T, T2))
  -> {matches(t, subst(r, T2)) == True{} : Bool}:
  bcase({matches(t, subst(r, T2)) == True{} : Bool}, matches(t, subst(r, T2)),
    k => k,
    +k => Empty.absurd({matches(t, subst(r, T2)) == True{} : Bool},
      PartEx.elim(T, r, t, Empty, toPart(r, T, t, h),
        +m => p => Wit.elim(T, T2, t, Empty, Det(r, m, T, T2, t, p, k),
          n => w => sb => h1 => h2 => contra(matches(w, subst(RRef{n}, T2)), inc(String.to_lower(n), w, h1), h2)))))

# Every depth is contained in every depth with TTop at the bottom.
def le_tb(D: Nat, d: Nat, +G: List<&2, Ent>, +ln: String, +w: String, h: {matches(w, refv(tbl(d, G), ln)) == True{} : Bool})
  -> {matches(w, refv(tbB(TTop{}, D, G), ln)) == True{} : Bool}:
  match D d:
    case 0n d:
      sig_all(w)
    case 1n+P 0n:
      none_elim({matches(w, refv(tbB(TTop{}, 1n+P, G), ln)) == True{} : Bool}, w, h)
    case 1n+ +P 1n+ +p:
      %Equal.sym(Re, lookupE(tblRow(G, tbB(TTop{}, P, G)), ln), subst(lookupE(G, ln), tbB(TTop{}, P, G)), lk_comm(G, tbB(TTop{}, P, G), ln))
        : {matches(w, _) == True{} : Bool}
      mono_tb(lookupE(G, ln), tbl(p, G), tbB(TTop{}, P, G), w,
        mtr(w, lookupE(tblRow(G, tbl(p, G)), ln), subst(lookupE(G, ln), tbl(p, G)), lk_comm(G, tbl(p, G), ln), h),
        ln2 => w2 => h2 => le_tb(P, p, G, ln2, w2, h2))

# What matches at some depth matches with TTop at the bottom.
def upper(+D: Nat, +d: Nat, +G: List<&2, Ent>, +r: Re, +s: String, h: {matches(s, subst(r, tbl(d, G))) == True{} : Bool})
  -> {matches(s, subst(r, tbB(TTop{}, D, G))) == True{} : Bool}:
  mono_tb(r, tbl(d, G), tbB(TTop{}, D, G), s, h, ln => w => k => le_tb(D, d, G, ln, w, k))

# Fast checking
# =============

# ochk unfolds a full grammar to bound(s, G), which is far too deep to run.
# chk instead compiles the grammar once: every reference becomes the position
# of its name's body in a list. Then it matches with derivatives that unfold a
# reference only when a character reaches it, each tagged with the depth it
# may still unfold. isem(top, B, d, x) is what such a compiled rule at depth d
# stands for: x with its references unfolded d times, and bot(top) below that.

type Cx is Data:
  CNone{}
  CEps{}
  CChr{c: Char}
  CCat{a: Cx, b: Cx}
  CAlt{a: Cx, b: Cx}
  CStar{r: Cx}
  CRef{i: Nat}
  CRange{lo: Char, hi: Char}

def lowerG(G: List<&2, Ent>) -> List<&2, Ent>:
  match G:
    case []:
      []
    case Ent{k, r} <> rest:
      Ent{String.to_lower(k), r} <> lowerG(rest)

# lookupE over a grammar whose names are already lowercase.
def lookupL(G: List<&2, Ent>, +ln: String) -> Re:
  match G:
    case []:
      RNone{}
    case Ent{k, r} <> rest:
      lsel(String.eq(k, ln), r, lookupL(rest, ln))

def keys(G: List<&2, Ent>) -> List<&2, String>:
  match G:
    case []:
      []
    case Ent{k, r} <> rest:
      k <> keys(rest)

def idx.f(b: Bool, j: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n+j

# The position of the first key equal to ln, or the number of keys.
def idx(Ks: List<&2, String>, +ln: String) -> Nat:
  match Ks:
    case []:
      0n
    case k <> rest:
      idx.f(String.eq(k, ln), idx(rest, ln))

def comp(+Ks: List<&2, String>, r: Re) -> Cx:
  match r:
    case RNone{}:
      CNone{}
    case REps{}:
      CEps{}
    case RChr{c}:
      CChr{c}
    case RCat{a, b}:
      CCat{comp(Ks, a), comp(Ks, b)}
    case RAlt{a, b}:
      CAlt{comp(Ks, a), comp(Ks, b)}
    case RStar{a}:
      CStar{comp(Ks, a)}
    case RRef{n}:
      CRef{idx(Ks, String.to_lower(n))}
    case RRange{lo, hi}:
      CRange{lo, hi}

# The body of every key's name, then one for names that are not keys.
def bodies(+Ks: List<&2, String>, +Gl: List<&2, Ent>, ks: List<&2, String>) -> List<&2, Cx>:
  match ks:
    case []:
      [comp(Ks, RNone{})]
    case k <> rest:
      comp(Ks, lookupL(Gl, k)) <> bodies(Ks, Gl, rest)

def nth(xs: List<&2, Cx>, i: Nat) -> Cx:
  match xs:
    case []:
      CNone{}
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+j:
          nth(rest, j)

def cks(G: List<&2, Ent>) -> List<&2, String>:
  keys(lowerG(G))

def cbs(+G: List<&2, Ent>) -> List<&2, Cx>:
  bodies(cks(G), lowerG(G), cks(G))

def bot(top: Bool) -> Re:
  match top:
    case False{}:
      RNone{}
    case True{}:
      SIG

def botT(top: Bool) -> Tb:
  match top:
    case False{}:
      TDead{}
    case True{}:
      TTop{}

def isem(+top: Bool, +B: List<&2, Cx>, +d: Nat, x: Cx) -> Re:
  match d:
    case 0n:
      match x:
        case CNone{}:
          RNone{}
        case CEps{}:
          REps{}
        case CChr{c}:
          RChr{c}
        case CCat{a, b}:
          RCat{isem(top, B, d, a), isem(top, B, d, b)}
        case CAlt{a, b}:
          RAlt{isem(top, B, d, a), isem(top, B, d, b)}
        case CStar{a}:
          RStar{isem(top, B, d, a)}
        case CRef{i}:
          bot(top)
        case CRange{lo, hi}:
          RRange{lo, hi}
    case 1n+p:
      match x:
        case CNone{}:
          RNone{}
        case CEps{}:
          REps{}
        case CChr{c}:
          RChr{c}
        case CCat{a, b}:
          RCat{isem(top, B, d, a), isem(top, B, d, b)}
        case CAlt{a, b}:
          RAlt{isem(top, B, d, a), isem(top, B, d, b)}
        case CStar{a}:
          RStar{isem(top, B, d, a)}
        case CRef{i}:
          isem(top, B, p, nth(B, i))
        case CRange{lo, hi}:
          RRange{lo, hi}

# Compiling
# ---------

def ll_eq(G: List<&2, Ent>, +ln: String) -> {lookupL(lowerG(G), ln) == lookupE(G, ln) : Re}:
  match G:
    case []:
      {==}
    case Ent{+k, +r} <> rest:
      %ll_eq(rest, ln) : {lsel(String.eq(String.to_lower(k), ln), r, lookupL(lowerG(rest), ln)) == lsel(String.eq(String.to_lower(k), ln), r, _) : Re}
      {==}

def fsel.go(b: Bool, A: Re, X: Re) -> Re:
  match b:
    case True{}:
      A
    case False{}:
      X

# fsel(G, A, ln) is A if some key of G is ln, and RNone otherwise.
def fsel(G: List<&2, Ent>, +A: Re, +ln: String) -> Re:
  match G:
    case []:
      RNone{}
    case Ent{k, r} <> rest:
      fsel.go(String.eq(k, ln), A, fsel(rest, A, ln))

def fs_eq(G: List<&2, Ent>, +ln: String) -> {fsel(G, lookupL(G, ln), ln) == lookupL(G, ln) : Re}:
  match G:
    case []:
      {==}
    case Ent{+k, +r} <> +rest:
      bcase({fsel(Ent{k, r} <> rest, lookupL(Ent{k, r} <> rest, ln), ln) == lookupL(Ent{k, r} <> rest, ln) : Re}, String.eq(k, ln),
        e => %Equal.sym(Bool, String.eq(k, ln), True{}, e)
            : {fsel.go(_, lsel(_, r, lookupL(rest, ln)), fsel(rest, lsel(_, r, lookupL(rest, ln)), ln)) == lsel(_, r, lookupL(rest, ln)) : Re}
          {==},
        e => %Equal.sym(Bool, String.eq(k, ln), False{}, e)
            : {fsel.go(_, lsel(_, r, lookupL(rest, ln)), fsel(rest, lsel(_, r, lookupL(rest, ln)), ln)) == lsel(_, r, lookupL(rest, ln)) : Re}
          fs_eq(rest, ln))

def bi(+Ks: List<&2, String>, +Gl: List<&2, Ent>, S: List<&2, Ent>, +ln: String)
  -> {nth(bodies(Ks, Gl, keys(S)), idx(keys(S), ln)) == comp(Ks, fsel(S, lookupL(Gl, ln), ln)) : Cx}:
  match S:
    case []:
      {==}
    case Ent{+k, r} <> +rest:
      bcase({nth(bodies(Ks, Gl, k <> keys(rest)), idx(k <> keys(rest), ln)) == comp(Ks, fsel(Ent{k, r} <> rest, lookupL(Gl, ln), ln)) : Cx}, String.eq(k, ln),
        +e => %Equal.sym(Bool, String.eq(k, ln), True{}, e)
            : {nth(comp(Ks, lookupL(Gl, k)) <> bodies(Ks, Gl, keys(rest)), idx.f(_, idx(keys(rest), ln))) == comp(Ks, fsel.go(_, lookupL(Gl, ln), fsel(rest, lookupL(Gl, ln), ln))) : Cx}
          %str_eq(k, ln, e) : {comp(Ks, lookupL(Gl, k)) == comp(Ks, lookupL(Gl, _)) : Cx}
          {==},
        e => %Equal.sym(Bool, String.eq(k, ln), False{}, e)
            : {nth(comp(Ks, lookupL(Gl, k)) <> bodies(Ks, Gl, keys(rest)), idx.f(_, idx(keys(rest), ln))) == comp(Ks, fsel.go(_, lookupL(Gl, ln), fsel(rest, lookupL(Gl, ln), ln))) : Cx}
          bi(Ks, Gl, rest, ln))

# A reference compiles to the position of its name's body.
def b_idx(+G: List<&2, Ent>, +ln: String) -> {nth(cbs(G), idx(cks(G), ln)) == comp(cks(G), lookupE(G, ln)) : Cx}:
  %ll_eq(G, ln) : {nth(cbs(G), idx(cks(G), ln)) == comp(cks(G), _) : Cx}
  %fs_eq(lowerG(G), ln) : {nth(cbs(G), idx(cks(G), ln)) == comp(cks(G), _) : Cx}
  bi(cks(G), lowerG(G), lowerG(G), ln)

def rcat_eq(-a1: Re, -a2: Re, -b1: Re, -b2: Re, e1: {a1 == a2 : Re}, e2: {b1 == b2 : Re}) -> {RCat{a1, b1} == RCat{a2, b2} : Re}:
  %e1 : {RCat{a1, b1} == RCat{_, b2} : Re}
  %e2 : {RCat{a1, b1} == RCat{a1, _} : Re}
  {==}

def ralt_eq(-a1: Re, -a2: Re, -b1: Re, -b2: Re, e1: {a1 == a2 : Re}, e2: {b1 == b2 : Re}) -> {RAlt{a1, b1} == RAlt{a2, b2} : Re}:
  %e1 : {RAlt{a1, b1} == RAlt{_, b2} : Re}
  %e2 : {RAlt{a1, b1} == RAlt{a1, _} : Re}
  {==}

def rstar_eq(-a1: Re, -a2: Re, e1: {a1 == a2 : Re}) -> {RStar{a1} == RStar{a2} : Re}:
  %e1 : {RStar{a1} == RStar{_} : Re}
  {==}

def bot_refv(top: Bool, -ln: String) -> {bot(top) == refv(botT(top), ln) : Re}:
  match top:
    case False{}:
      {==}
    case True{}:
      {==}

def cl.ref(+top: Bool, +G: List<&2, Ent>, +p: Nat, +ln: String,
  ih: {isem(top, cbs(G), p, comp(cks(G), lookupE(G, ln))) == subst(lookupE(G, ln), tbB(botT(top), p, G)) : Re})
  -> {isem(top, cbs(G), p, nth(cbs(G), idx(cks(G), ln))) == lookupE(tblRow(G, tbB(botT(top), p, G)), ln) : Re}:
  %Equal.sym(Re, lookupE(tblRow(G, tbB(botT(top), p, G)), ln), subst(lookupE(G, ln), tbB(botT(top), p, G)), lk_comm(G, tbB(botT(top), p, G), ln))
    : {isem(top, cbs(G), p, nth(cbs(G), idx(cks(G), ln))) == _ : Re}
  %Equal.sym(Cx, nth(cbs(G), idx(cks(G), ln)), comp(cks(G), lookupE(G, ln)), b_idx(G, ln))
    : {isem(top, cbs(G), p, _) == subst(lookupE(G, ln), tbB(botT(top), p, G)) : Re}
  ih

# Compiling keeps what a rule stands for, at every depth.
def cl(+top: Bool, +G: List<&2, Ent>, +d: Nat, r: Re) -> {isem(top, cbs(G), d, comp(cks(G), r)) == subst(r, tbB(botT(top), d, G)) : Re}:
  match d:
    case 0n:
      match r:
        case RNone{}:
          {==}
        case REps{}:
          {==}
        case RChr{c}:
          {==}
        case RCat{+a, +b}:
          rcat_eq(isem(top, cbs(G), d, comp(cks(G), a)), subst(a, tbB(botT(top), d, G)), isem(top, cbs(G), d, comp(cks(G), b)), subst(b, tbB(botT(top), d, G)),
            cl(top, G, d, a), cl(top, G, d, b))
        case RAlt{+a, +b}:
          ralt_eq(isem(top, cbs(G), d, comp(cks(G), a)), subst(a, tbB(botT(top), d, G)), isem(top, cbs(G), d, comp(cks(G), b)), subst(b, tbB(botT(top), d, G)),
            cl(top, G, d, a), cl(top, G, d, b))
        case RStar{+a}:
          rstar_eq(isem(top, cbs(G), d, comp(cks(G), a)), subst(a, tbB(botT(top), d, G)), cl(top, G, d, a))
        case RRef{n}:
          bot_refv(top, String.to_lower(n))
        case RRange{lo, hi}:
          {==}
    case 1n+ +p:
      match r:
        case RNone{}:
          {==}
        case REps{}:
          {==}
        case RChr{c}:
          {==}
        case RCat{+a, +b}:
          rcat_eq(isem(top, cbs(G), d, comp(cks(G), a)), subst(a, tbB(botT(top), d, G)), isem(top, cbs(G), d, comp(cks(G), b)), subst(b, tbB(botT(top), d, G)),
            cl(top, G, d, a), cl(top, G, d, b))
        case RAlt{+a, +b}:
          ralt_eq(isem(top, cbs(G), d, comp(cks(G), a)), subst(a, tbB(botT(top), d, G)), isem(top, cbs(G), d, comp(cks(G), b)), subst(b, tbB(botT(top), d, G)),
            cl(top, G, d, a), cl(top, G, d, b))
        case RStar{+a}:
          rstar_eq(isem(top, cbs(G), d, comp(cks(G), a)), subst(a, tbB(botT(top), d, G)), cl(top, G, d, a))
        case RRef{+n}:
          cl.ref(top, G, p, String.to_lower(n), cl(top, G, p, lookupE(G, String.to_lower(n))))
        case RRange{lo, hi}:
          {==}

# Nullable
# --------

# Whether a compiled rule matches "" at depth d depends on which bodies do at
# depth d-1. canon(top, B, d) holds that: NBase{top} at depth 0, and a table of
# one answer per body above. The tables stop changing after a few steps, so
# mkLad computes them until two agree, and lget looks one up.

type NE is Data:
  NBase{b: Bool}
  NTab{vs: List<&2, Bool>}

def nthB(xs: List<&2, Bool>, i: Nat) -> Bool:
  match xs:
    case []:
      False{}
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+j:
          nthB(rest, j)

def nlook(E: NE, i: Nat) -> Bool:
  match E:
    case NBase{b}:
      b
    case NTab{vs}:
      nthB(vs, i)

def nat(+E: NE, x: Cx) -> Bool:
  match x:
    case CNone{}:
      False{}
    case CEps{}:
      True{}
    case CChr{c}:
      False{}
    case CCat{a, b}:
      Bool.and(nat(E, a), nat(E, b))
    case CAlt{a, b}:
      Bool.or(nat(E, a), nat(E, b))
    case CStar{a}:
      True{}
    case CRef{i}:
      nlook(E, i)
    case CRange{lo, hi}:
      False{}

def nmap(+E: NE, B: List<&2, Cx>) -> List<&2, Bool>:
  match B:
    case []:
      []
    case x <> rest:
      nat(E, x) <> nmap(E, rest)

def nstep(+B: List<&2, Cx>, +E: NE) -> NE:
  NTab{nmap(E, B)}

def canon(+top: Bool, +B: List<&2, Cx>, d: Nat) -> NE:
  match d:
    case 0n:
      NBase{top}
    case 1n+p:
      nstep(B, canon(top, B, p))

def niter(+B: List<&2, Cx>, d: Nat, e: NE) -> NE:
  match d:
    case 0n:
      e
    case 1n+p:
      niter(B, p, nstep(B, e))

def bl_eq(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Bool.not(Bool.xor(x, y)), bl_eq(xt, yt))

def ne_eq(a: NE, b: NE) -> Bool:
  match a b:
    case NBase{x} NBase{y}:
      Bool.not(Bool.xor(x, y))
    case NBase{x} NTab{ys}:
      False{}
    case NTab{xs} NBase{y}:
      False{}
    case NTab{xs} NTab{ys}:
      bl_eq(xs, ys)

# LStop{e}: e at this depth and every greater one (a fixed point);
# LTail{e}: e here, greater depths computed on demand.
type Lad is Data:
  LStop{e: NE}
  LTail{e: NE}
  LStep{e: NE, next: Lad}

def build(+B: List<&2, Cx>, fuel: Nat, +e: NE, f: Bool) -> Lad:
  match fuel:
    case 0n:
      LTail{e}
    case 1n+q:
      match f:
        case True{}:
          LStop{e}
        case False{}:
          LStep{e, build(B, q, nstep(B, e), ne_eq(nstep(B, nstep(B, e)), nstep(B, e)))}

def blen(B: List<&2, Cx>) -> Nat:
  match B:
    case []:
      0n
    case h <> t:
      1n+blen(t)

def mkLad(+top: Bool, +B: List<&2, Cx>) -> Lad:
  build(B, 2n+blen(B), NBase{top}, ne_eq(nstep(B, NBase{top}), NBase{top}))

def lget(+B: List<&2, Cx>, L: Lad, d: Nat) -> NE:
  match L:
    case LStop{e}:
      e
    case LTail{e}:
      niter(B, d, e)
    case LStep{e, next}:
      match d:
        case 0n:
          e
        case 1n+p:
          lget(B, next, p)

def nth_nmap(+E: NE, B: List<&2, Cx>, i: Nat) -> {nthB(nmap(E, B), i) == nat(E, nth(B, i)) : Bool}:
  match B:
    case []:
      {==}
    case x <> rest:
      match i:
        case 0n:
          {==}
        case 1n+j:
          nth_nmap(E, rest, j)

def band_eq(-a1: Bool, -a2: Bool, -b1: Bool, -b2: Bool, e1: {a1 == a2 : Bool}, e2: {b1 == b2 : Bool}) -> {Bool.and(a1, b1) == Bool.and(a2, b2) : Bool}:
  %e1 : {Bool.and(a1, b1) == Bool.and(_, b2) : Bool}
  %e2 : {Bool.and(a1, b1) == Bool.and(a1, _) : Bool}
  {==}

def bor_eq(-a1: Bool, -a2: Bool, -b1: Bool, -b2: Bool, e1: {a1 == a2 : Bool}, e2: {b1 == b2 : Bool}) -> {Bool.or(a1, b1) == Bool.or(a2, b2) : Bool}:
  %e1 : {Bool.or(a1, b1) == Bool.or(_, b2) : Bool}
  %e2 : {Bool.or(a1, b1) == Bool.or(a1, _) : Bool}
  {==}

def bot_null(top: Bool) -> {top == nullable(bot(top)) : Bool}:
  match top:
    case False{}:
      {==}
    case True{}:
      {==}

# nat reads canon(top, B, d) correctly.
def na(+top: Bool, +B: List<&2, Cx>, +d: Nat, x: Cx) -> {nat(canon(top, B, d), x) == nullable(isem(top, B, d, x)) : Bool}:
  match d:
    case 0n:
      match x:
        case CNone{}:
          {==}
        case CEps{}:
          {==}
        case CChr{c}:
          {==}
        case CCat{+a, +b}:
          band_eq(nat(canon(top, B, d), a), nullable(isem(top, B, d, a)), nat(canon(top, B, d), b), nullable(isem(top, B, d, b)), na(top, B, d, a), na(top, B, d, b))
        case CAlt{+a, +b}:
          bor_eq(nat(canon(top, B, d), a), nullable(isem(top, B, d, a)), nat(canon(top, B, d), b), nullable(isem(top, B, d, b)), na(top, B, d, a), na(top, B, d, b))
        case CStar{a}:
          {==}
        case CRef{i}:
          bot_null(top)
        case CRange{lo, hi}:
          {==}
    case 1n+ +p:
      match x:
        case CNone{}:
          {==}
        case CEps{}:
          {==}
        case CChr{c}:
          {==}
        case CCat{+a, +b}:
          band_eq(nat(canon(top, B, d), a), nullable(isem(top, B, d, a)), nat(canon(top, B, d), b), nullable(isem(top, B, d, b)), na(top, B, d, a), na(top, B, d, b))
        case CAlt{+a, +b}:
          bor_eq(nat(canon(top, B, d), a), nullable(isem(top, B, d, a)), nat(canon(top, B, d), b), nullable(isem(top, B, d, b)), na(top, B, d, a), na(top, B, d, b))
        case CStar{a}:
          {==}
        case CRef{+i}:
          Equal.trans(Bool, nthB(nmap(canon(top, B, p), B), i), nat(canon(top, B, p), nth(B, i)), nullable(isem(top, B, p, nth(B, i))),
            nth_nmap(canon(top, B, p), B, i), na(top, B, p, nth(B, i)))
        case CRange{lo, hi}:
          {==}

# The ladder

def bx_eq(x: Bool, y: Bool, h: {Bool.not(Bool.xor(x, y)) == True{} : Bool}) -> {x == y : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case True{} True{}:
      {==}

def bcon_eq(-x: Bool, -y: Bool, -xt: List<&2, Bool>, -yt: List<&2, Bool>, e1: {x == y : Bool}, e2: {xt == yt : List<&2, Bool>})
  -> {x <> xt == y <> yt : List<&2, Bool>}:
  %e1 : {x <> xt == _ <> yt : List<&2, Bool>}
  %e2 : {x <> xt == x <> _ : List<&2, Bool>}
  {==}

def bl_sound(xs: List<&2, Bool>, ys: List<&2, Bool>, +h: {bl_eq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Bool>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({[] == y <> yt : List<&2, Bool>}, false_ne_true(h))
    case Con{x, xt} Nil{}:
      Empty.absurd({x <> xt == [] : List<&2, Bool>}, false_ne_true(h))
    case Con{+x, +xt} Con{+y, +yt}:
      bcon_eq(x, y, xt, yt,
        bx_eq(x, y, and_l(Bool.not(Bool.xor(x, y)), bl_eq(xt, yt), h)),
        bl_sound(xt, yt, and_r(Bool.not(Bool.xor(x, y)), bl_eq(xt, yt), h)))

def ne_sound(a: NE, b: NE, h: {ne_eq(a, b) == True{} : Bool}) -> {a == b : NE}:
  match a b:
    case NBase{+x} NBase{+y}:
      %bx_eq(x, y, h) : {NBase{x} == NBase{_} : NE}
      {==}
    case NBase{x} NTab{ys}:
      Empty.absurd({NBase{x} == NTab{ys} : NE}, false_ne_true(h))
    case NTab{xs} NBase{y}:
      Empty.absurd({NTab{xs} == NBase{y} : NE}, false_ne_true(h))
    case NTab{+xs} NTab{+ys}:
      %bl_sound(xs, ys, h) : {NTab{xs} == NTab{_} : NE}
      {==}

def niter_fix(+B: List<&2, Cx>, d: Nat, +e: NE, +fx: {nstep(B, e) == e : NE}) -> {e == niter(B, d, e) : NE}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(NE, nstep(B, e), e, fx) : {e == niter(B, p, _) : NE}
      niter_fix(B, p, e, fx)

def lg.step(+B: List<&2, Cx>, -e: NE, -next: Lad, d: Nat, ih: @p: Nat -> {lget(B, next, p) == niter(B, p, nstep(B, e)) : NE})
  -> {lget(B, LStep{e, next}, d) == niter(B, d, e) : NE}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      ih(p)

def lg.stop(+B: List<&2, Cx>, +e: NE, +d: Nat, f: Bool, k: {f == True{} : Bool}, h: {ne_eq(nstep(B, e), e) == f : Bool})
  -> {e == niter(B, d, e) : NE}:
  niter_fix(B, d, e, ne_sound(nstep(B, e), e, Equal.trans(Bool, ne_eq(nstep(B, e), e), f, True{}, h, k)))

# The ladder from e answers what iterating from e answers.
def lg(+B: List<&2, Cx>, fuel: Nat, +e: NE, +d: Nat) -> {lget(B, build(B, fuel, e, ne_eq(nstep(B, e), e)), d) == niter(B, d, e) : NE}:
  match fuel:
    case 0n:
      {==}
    case 1n+ +q:
      bcase({lget(B, build(B, 1n+q, e, ne_eq(nstep(B, e), e)), d) == niter(B, d, e) : NE}, ne_eq(nstep(B, e), e),
        +k => %Equal.sym(Bool, ne_eq(nstep(B, e), e), True{}, k) : {lget(B, build(B, 1n+q, e, _), d) == niter(B, d, e) : NE}
          lg.stop(B, e, d, True{}, {==}, k),
        k => %Equal.sym(Bool, ne_eq(nstep(B, e), e), False{}, k) : {lget(B, build(B, 1n+q, e, _), d) == niter(B, d, e) : NE}
          lg.step(B, e, build(B, q, nstep(B, e), ne_eq(nstep(B, nstep(B, e)), nstep(B, e))), d, p => lg(B, q, nstep(B, e), p)))

def niter_succ(+B: List<&2, Cx>, p: Nat, +e: NE) -> {niter(B, 1n+p, e) == nstep(B, niter(B, p, e)) : NE}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      niter_succ(B, q, nstep(B, e))

def niter_canon(+top: Bool, +B: List<&2, Cx>, d: Nat) -> {niter(B, d, NBase{top}) == canon(top, B, d) : NE}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      %niter_canon(top, B, p) : {niter(B, 1n+p, NBase{top}) == nstep(B, _) : NE}
      niter_succ(B, p, NBase{top})

def lget_ok(+top: Bool, +B: List<&2, Cx>, +d: Nat) -> {lget(B, mkLad(top, B), d) == canon(top, B, d) : NE}:
  Equal.trans(NE, lget(B, mkLad(top, B), d), niter(B, d, NBase{top}), canon(top, B, d),
    lg(B, 2n+blen(B), NBase{top}, d), niter_canon(top, B, d))

# What the fast matcher computes for "is x nullable at depth d".
def nat_ok(+top: Bool, +B: List<&2, Cx>, +d: Nat, +x: Cx) -> {nat(lget(B, mkLad(top, B), d), x) == nullable(isem(top, B, d, x)) : Bool}:
  %Equal.sym(NE, lget(B, mkLad(top, B), d), canon(top, B, d), lget_ok(top, B, d)) : {nat(_, x) == nullable(isem(top, B, d, x)) : Bool}
  na(top, B, d, x)

# Languages
# ---------

# Two rules that match the same strings, case by case.

def beq(x: Bool, y: Bool, i1: {x == True{} : Bool} -> {y == True{} : Bool}, i2: {y == True{} : Bool} -> {x == True{} : Bool}) -> {x == y : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(i1({==})))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(i2({==})))
    case False{} False{}:
      {==}

def or_f(-a: Bool, -b: Bool, e: {a == False{} : Bool}) -> {Bool.or(a, b) == b : Bool}:
  %Equal.sym(Bool, a, False{}, e) : {Bool.or(_, b) == b : Bool}
  {==}

def or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cat_none_l(t: String, +X: Re) -> {matches(t, RCat{RNone{}, X}) == False{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, u}:
      cat_none_l(u, X)

def cat_eps_l(t: String, +X: Re) -> {matches(t, RCat{REps{}, X}) == matches(t, X) : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      Equal.trans(Bool, matches(u, RAlt{RCat{RNone{}, X}, deriv(c, X)}), Bool.or(matches(u, RCat{RNone{}, X}), matches(u, deriv(c, X))), matches(u, deriv(c, X)),
        alt_or(u, RCat{RNone{}, X}, deriv(c, X)), or_f(matches(u, RCat{RNone{}, X}), matches(u, deriv(c, X)), cat_none_l(u, X)))

def cat_eps_r(+t: String, +X: Re) -> {matches(t, RCat{X, REps{}}) == matches(t, X) : Bool}:
  beq(matches(t, RCat{X, REps{}}), matches(t, X), k => eps_tail_elim(t, X, k), k => eps_tail_intro(t, X, k))

def cat_none_r(+t: String, +X: Re) -> {matches(t, RCat{X, RNone{}}) == False{} : Bool}:
  bcase({matches(t, RCat{X, RNone{}}) == False{} : Bool}, matches(t, RCat{X, RNone{}}),
    k => Split.elim(t, X, RNone{}, {matches(t, RCat{X, RNone{}}) == False{} : Bool}, cat_elim(t, X, RNone{}, k),
      s1 => +s2 => e => h1 => h2 => none_elim({matches(t, RCat{X, RNone{}}) == False{} : Bool}, s2, h2)),
    k => k)

def cat_assoc.f(+t: String, +P: Re, +Q: Re, +R: Re, h: {matches(t, RCat{RCat{P, Q}, R}) == True{} : Bool})
  -> {matches(t, RCat{P, RCat{Q, R}}) == True{} : Bool}:
  Split.elim(t, RCat{P, Q}, R, {matches(t, RCat{P, RCat{Q, R}}) == True{} : Bool}, cat_elim(t, RCat{P, Q}, R, h),
    +s12 => +s3 => e => h12 => h3 => Split.elim(s12, P, Q, {matches(t, RCat{P, RCat{Q, R}}) == True{} : Bool}, cat_elim(s12, P, Q, h12),
      +s1 => +s2 => e2 => h1 => h2 => str_tr(String.append(s1, String.append(s2, s3)), t, RCat{P, RCat{Q, R}},
        Equal.trans(String, String.append(s1, String.append(s2, s3)), String.append(String.append(s1, s2), s3), t,
          Equal.sym(String, String.append(String.append(s1, s2), s3), String.append(s1, String.append(s2, s3)), app_assoc(s1, s2, s3)),
          Equal.trans(String, String.append(String.append(s1, s2), s3), String.append(s12, s3), t, app_congr(s3, String.append(s1, s2), s12, e2), e)),
        cat_intro(s1, P, RCat{Q, R}, String.append(s2, s3), h1, cat_intro(s2, Q, R, s3, h2, h3)))))

def cat_assoc.b(+t: String, +P: Re, +Q: Re, +R: Re, h: {matches(t, RCat{P, RCat{Q, R}}) == True{} : Bool})
  -> {matches(t, RCat{RCat{P, Q}, R}) == True{} : Bool}:
  Split.elim(t, P, RCat{Q, R}, {matches(t, RCat{RCat{P, Q}, R}) == True{} : Bool}, cat_elim(t, P, RCat{Q, R}, h),
    +s1 => +s23 => e => h1 => h23 => Split.elim(s23, Q, R, {matches(t, RCat{RCat{P, Q}, R}) == True{} : Bool}, cat_elim(s23, Q, R, h23),
      +s2 => +s3 => e2 => h2 => h3 => str_tr(String.append(String.append(s1, s2), s3), t, RCat{RCat{P, Q}, R},
        Equal.trans(String, String.append(String.append(s1, s2), s3), String.append(s1, String.append(s2, s3)), t, app_assoc(s1, s2, s3),
          Equal.trans(String, String.append(s1, String.append(s2, s3)), String.append(s1, s23), t, app_congl(s1, String.append(s2, s3), s23, e2), e)),
        cat_intro(String.append(s1, s2), RCat{P, Q}, R, s3, cat_intro(s1, P, Q, s2, h1, h2), h3))))

def cat_assoc(+t: String, +P: Re, +Q: Re, +R: Re) -> {matches(t, RCat{RCat{P, Q}, R}) == matches(t, RCat{P, RCat{Q, R}}) : Bool}:
  beq(matches(t, RCat{RCat{P, Q}, R}), matches(t, RCat{P, RCat{Q, R}}), k => cat_assoc.f(t, P, Q, R, k), k => cat_assoc.b(t, P, Q, R, k))

def cat_imp_l(+t: String, +X: Re, +Y: Re, +R: Re, f: @s: String -> {matches(s, X) == True{} : Bool} -> {matches(s, Y) == True{} : Bool},
  h: {matches(t, RCat{X, R}) == True{} : Bool}) -> {matches(t, RCat{Y, R}) == True{} : Bool}:
  Split.elim(t, X, R, {matches(t, RCat{Y, R}) == True{} : Bool}, cat_elim(t, X, R, h),
    +s1 => +s2 => e => h1 => h2 => str_tr(String.append(s1, s2), t, RCat{Y, R}, e, cat_intro(s1, Y, R, s2, f(s1, h1), h2)))

def cat_imp_r(+t: String, +P: Re, +X: Re, +Y: Re, f: @s: String -> {matches(s, X) == True{} : Bool} -> {matches(s, Y) == True{} : Bool},
  h: {matches(t, RCat{P, X}) == True{} : Bool}) -> {matches(t, RCat{P, Y}) == True{} : Bool}:
  Split.elim(t, P, X, {matches(t, RCat{P, Y}) == True{} : Bool}, cat_elim(t, P, X, h),
    +s1 => +s2 => e => h1 => h2 => str_tr(String.append(s1, s2), t, RCat{P, Y}, e, cat_intro(s1, P, Y, s2, h1, f(s2, h2))))

def cat_cong_l(+t: String, +X: Re, +Y: Re, +R: Re,
  f: @s: String -> {matches(s, X) == True{} : Bool} -> {matches(s, Y) == True{} : Bool},
  g: @s: String -> {matches(s, Y) == True{} : Bool} -> {matches(s, X) == True{} : Bool})
  -> {matches(t, RCat{X, R}) == matches(t, RCat{Y, R}) : Bool}:
  beq(matches(t, RCat{X, R}), matches(t, RCat{Y, R}), k => cat_imp_l(t, X, Y, R, f, k), k => cat_imp_l(t, Y, X, R, g, k))

def cat_cong_r(+t: String, +P: Re, +X: Re, +Y: Re,
  f: @s: String -> {matches(s, X) == True{} : Bool} -> {matches(s, Y) == True{} : Bool},
  g: @s: String -> {matches(s, Y) == True{} : Bool} -> {matches(s, X) == True{} : Bool})
  -> {matches(t, RCat{P, X}) == matches(t, RCat{P, Y}) : Bool}:
  beq(matches(t, RCat{P, X}), matches(t, RCat{P, Y}), k => cat_imp_r(t, P, X, Y, f, k), k => cat_imp_r(t, P, Y, X, g, k))

# Matching states
# ---------------

# A state is what is left to match: XAt{d, x} is the compiled rule x at depth
# d, unfolded only as far as characters reach. The constructors below drop
# what can't match, keep concatenations nested to the right (so the front is
# one step away), and skip an alternative equal to one already there.

type Rx is Data:
  XNone{}
  XEps{}
  XAll{}
  XCat{a: Rx, b: Rx}
  XAlt{a: Rx, b: Rx}
  XAt{d: Nat, x: Cx}

def bsem(+top: Bool, +B: List<&2, Cx>, x: Rx) -> Re:
  match x:
    case XNone{}:
      RNone{}
    case XEps{}:
      REps{}
    case XAll{}:
      SIG
    case XCat{a, b}:
      RCat{bsem(top, B, a), bsem(top, B, b)}
    case XAlt{a, b}:
      RAlt{bsem(top, B, a), bsem(top, B, b)}
    case XAt{d, x}:
      isem(top, B, d, x)

def xcat.go(b: Rx, a: Rx) -> Rx:
  match a:
    case XNone{}:
      XNone{}
    case XEps{}:
      b
    case XAll{}:
      XCat{XAll{}, b}
    case XCat{p, q}:
      XCat{p, xcat.go(b, q)}
    case XAlt{p, q}:
      XCat{XAlt{p, q}, b}
    case XAt{d, x}:
      XCat{XAt{d, x}, b}

def xcat(a: Rx, b: Rx) -> Rx:
  match b:
    case XNone{}:
      XNone{}
    case XEps{}:
      a
    case XAll{}:
      xcat.go(XAll{}, a)
    case XCat{p, q}:
      xcat.go(XCat{p, q}, a)
    case XAlt{p, q}:
      xcat.go(XAlt{p, q}, a)
    case XAt{d, x}:
      xcat.go(XAt{d, x}, a)

def ceq(x: Cx, y: Cx) -> Bool:
  match x y:
    case CNone{} CNone{}:
      True{}
    case CEps{} CEps{}:
      True{}
    case CChr{a} CChr{b}:
      Char.is_eq(a, b)
    case CCat{a1, b1} CCat{a2, b2}:
      Bool.and(ceq(a1, a2), ceq(b1, b2))
    case CAlt{a1, b1} CAlt{a2, b2}:
      Bool.and(ceq(a1, a2), ceq(b1, b2))
    case CStar{a1} CStar{a2}:
      ceq(a1, a2)
    case CRef{i} CRef{j}:
      eqn(i, j)
    case CRange{l1, h1} CRange{l2, h2}:
      Bool.and(Char.is_eq(l1, l2), Char.is_eq(h1, h2))
    case _ _:
      False{}

def req(x: Rx, y: Rx) -> Bool:
  match x y:
    case XNone{} XNone{}:
      True{}
    case XEps{} XEps{}:
      True{}
    case XAll{} XAll{}:
      True{}
    case XCat{a1, b1} XCat{a2, b2}:
      Bool.and(req(a1, a2), req(b1, b2))
    case XAlt{a1, b1} XAlt{a2, b2}:
      Bool.and(req(a1, a2), req(b1, b2))
    case XAt{d1, x1} XAt{d2, x2}:
      Bool.and(eqn(d1, d2), ceq(x1, x2))
    case _ _:
      False{}

# Whether a is one of the alternatives of b.
def mem(+a: Rx, b: Rx) -> Bool:
  match b:
    case XAlt{b1, b2}:
      Bool.or(req(a, b1), mem(a, b2))
    case XNone{}:
      req(a, XNone{})
    case XEps{}:
      req(a, XEps{})
    case XAll{}:
      req(a, XAll{})
    case XCat{p, q}:
      req(a, XCat{p, q})
    case XAt{d, x}:
      req(a, XAt{d, x})

def xalt.ins(m: Bool, a: Rx, b: Rx) -> Rx:
  match m:
    case True{}:
      b
    case False{}:
      XAlt{a, b}

def xalt.go(a: Rx, +b: Rx) -> Rx:
  match a:
    case XNone{}:
      b
    case XAlt{a1, a2}:
      xalt.go(a1, xalt.go(a2, b))
    case XEps{}:
      xalt.ins(mem(XEps{}, b), XEps{}, b)
    case XAll{}:
      xalt.ins(mem(XAll{}, b), XAll{}, b)
    case XCat{+p, +q}:
      xalt.ins(mem(XCat{p, q}, b), XCat{p, q}, b)
    case XAt{+d, +x}:
      xalt.ins(mem(XAt{d, x}, b), XAt{d, x}, b)

def xalt(a: Rx, b: Rx) -> Rx:
  match b:
    case XNone{}:
      a
    case XEps{}:
      xalt.go(a, XEps{})
    case XAll{}:
      xalt.go(a, XAll{})
    case XCat{p, q}:
      xalt.go(a, XCat{p, q})
    case XAlt{p, q}:
      xalt.go(a, XAlt{p, q})
    case XAt{d, x}:
      xalt.go(a, XAt{d, x})

def xat(+d: Nat, x: Cx) -> Rx:
  match x:
    case CNone{}:
      XNone{}
    case CEps{}:
      XEps{}
    case CChr{c}:
      XAt{d, CChr{c}}
    case CCat{a, b}:
      XAt{d, CCat{a, b}}
    case CAlt{a, b}:
      XAt{d, CAlt{a, b}}
    case CStar{a}:
      XAt{d, CStar{a}}
    case CRef{i}:
      XAt{d, CRef{i}}
    case CRange{lo, hi}:
      XAt{d, CRange{lo, hi}}

def xwhen(b: Bool) -> Rx:
  match b:
    case False{}:
      XNone{}
    case True{}:
      XEps{}

def xbot(top: Bool) -> Rx:
  match top:
    case False{}:
      XNone{}
    case True{}:
      XAll{}

# The constructors keep what a state matches.

def xcat.go_ok(+top: Bool, +B: List<&2, Cx>, +b: Rx, a: Rx, +t: String)
  -> {matches(t, bsem(top, B, xcat.go(b, a))) == matches(t, RCat{bsem(top, B, a), bsem(top, B, b)}) : Bool}:
  match a:
    case XNone{}:
      Equal.trans(Bool, matches(t, RNone{}), False{}, matches(t, RCat{RNone{}, bsem(top, B, b)}),
        none_false(t), Equal.sym(Bool, matches(t, RCat{RNone{}, bsem(top, B, b)}), False{}, cat_none_l(t, bsem(top, B, b))))
    case XEps{}:
      Equal.sym(Bool, matches(t, RCat{REps{}, bsem(top, B, b)}), matches(t, bsem(top, B, b)), cat_eps_l(t, bsem(top, B, b)))
    case XAll{}:
      {==}
    case XCat{+p, +q}:
      Equal.trans(Bool, matches(t, RCat{bsem(top, B, p), bsem(top, B, xcat.go(b, q))}),
        matches(t, RCat{bsem(top, B, p), RCat{bsem(top, B, q), bsem(top, B, b)}}),
        matches(t, RCat{RCat{bsem(top, B, p), bsem(top, B, q)}, bsem(top, B, b)}),
        cat_cong_r(t, bsem(top, B, p), bsem(top, B, xcat.go(b, q)), RCat{bsem(top, B, q), bsem(top, B, b)},
          +s => k => tt.sym(matches(s, bsem(top, B, xcat.go(b, q))), matches(s, RCat{bsem(top, B, q), bsem(top, B, b)}), xcat.go_ok(top, B, b, q, s), k),
          +s => k => tt(matches(s, bsem(top, B, xcat.go(b, q))), matches(s, RCat{bsem(top, B, q), bsem(top, B, b)}), xcat.go_ok(top, B, b, q, s), k)),
        Equal.sym(Bool, matches(t, RCat{RCat{bsem(top, B, p), bsem(top, B, q)}, bsem(top, B, b)}), matches(t, RCat{bsem(top, B, p), RCat{bsem(top, B, q), bsem(top, B, b)}}),
          cat_assoc(t, bsem(top, B, p), bsem(top, B, q), bsem(top, B, b))))
    case XAlt{p, q}:
      {==}
    case XAt{d, x}:
      {==}

def xcat_ok(+top: Bool, +B: List<&2, Cx>, +a: Rx, b: Rx, +t: String)
  -> {matches(t, bsem(top, B, xcat(a, b))) == matches(t, RCat{bsem(top, B, a), bsem(top, B, b)}) : Bool}:
  match b:
    case XNone{}:
      Equal.trans(Bool, matches(t, RNone{}), False{}, matches(t, RCat{bsem(top, B, a), RNone{}}),
        none_false(t), Equal.sym(Bool, matches(t, RCat{bsem(top, B, a), RNone{}}), False{}, cat_none_r(t, bsem(top, B, a))))
    case XEps{}:
      Equal.sym(Bool, matches(t, RCat{bsem(top, B, a), REps{}}), matches(t, bsem(top, B, a)), cat_eps_r(t, bsem(top, B, a)))
    case XAll{}:
      xcat.go_ok(top, B, XAll{}, a, t)
    case XCat{+p, +q}:
      xcat.go_ok(top, B, XCat{p, q}, a, t)
    case XAlt{+p, +q}:
      xcat.go_ok(top, B, XAlt{p, q}, a, t)
    case XAt{+d, +x}:
      xcat.go_ok(top, B, XAt{d, x}, a, t)

def ccon2(-a1: Cx, -a2: Cx, -b1: Cx, -b2: Cx, e1: {a1 == a2 : Cx}, e2: {b1 == b2 : Cx}, -K: Cx -> Cx -> Cx) -> {K(a1, b1) == K(a2, b2) : Cx}:
  %e1 : {K(a1, b1) == K(_, b2) : Cx}
  %e2 : {K(a1, b1) == K(a1, _) : Cx}
  {==}

def ceq_ok(x: Cx, y: Cx, +h: {ceq(x, y) == True{} : Bool}) -> {x == y : Cx}:
  match x y:
    case CNone{} CNone{}:
      {==}
    case CEps{} CEps{}:
      {==}
    case CChr{+a} CChr{+b}:
      %char_eq(a, b, h) : {CChr{a} == CChr{_} : Cx}
      {==}
    case CCat{+a1, +b1} CCat{+a2, +b2}:
      ccon2(a1, a2, b1, b2, ceq_ok(a1, a2, and_l(ceq(a1, a2), ceq(b1, b2), h)), ceq_ok(b1, b2, and_r(ceq(a1, a2), ceq(b1, b2), h)), p => q => CCat{p, q})
    case CAlt{+a1, +b1} CAlt{+a2, +b2}:
      ccon2(a1, a2, b1, b2, ceq_ok(a1, a2, and_l(ceq(a1, a2), ceq(b1, b2), h)), ceq_ok(b1, b2, and_r(ceq(a1, a2), ceq(b1, b2), h)), p => q => CAlt{p, q})
    case CStar{+a1} CStar{+a2}:
      %ceq_ok(a1, a2, h) : {CStar{a1} == CStar{_} : Cx}
      {==}
    case CRef{+i} CRef{+j}:
      %eqn_sound(i, j, h) : {CRef{i} == CRef{_} : Cx}
      {==}
    case CRange{+l1, +h1} CRange{+l2, +h2}:
      %char_eq(l1, l2, and_l(Char.is_eq(l1, l2), Char.is_eq(h1, h2), h)) : {CRange{l1, h1} == CRange{_, h2} : Cx}
      %char_eq(h1, h2, and_r(Char.is_eq(l1, l2), Char.is_eq(h1, h2), h)) : {CRange{l1, h1} == CRange{l1, _} : Cx}
      {==}
    case CNone{} CEps{}:
      Empty.absurd({CNone{} == CEps{} : Cx}, false_ne_true(h))
    case CNone{} CChr{c2}:
      Empty.absurd({CNone{} == CChr{c2} : Cx}, false_ne_true(h))
    case CNone{} CCat{a2, b2}:
      Empty.absurd({CNone{} == CCat{a2, b2} : Cx}, false_ne_true(h))
    case CNone{} CAlt{a2, b2}:
      Empty.absurd({CNone{} == CAlt{a2, b2} : Cx}, false_ne_true(h))
    case CNone{} CStar{a2}:
      Empty.absurd({CNone{} == CStar{a2} : Cx}, false_ne_true(h))
    case CNone{} CRef{i2}:
      Empty.absurd({CNone{} == CRef{i2} : Cx}, false_ne_true(h))
    case CNone{} CRange{l2, h2}:
      Empty.absurd({CNone{} == CRange{l2, h2} : Cx}, false_ne_true(h))
    case CEps{} CNone{}:
      Empty.absurd({CEps{} == CNone{} : Cx}, false_ne_true(h))
    case CEps{} CChr{c2}:
      Empty.absurd({CEps{} == CChr{c2} : Cx}, false_ne_true(h))
    case CEps{} CCat{a2, b2}:
      Empty.absurd({CEps{} == CCat{a2, b2} : Cx}, false_ne_true(h))
    case CEps{} CAlt{a2, b2}:
      Empty.absurd({CEps{} == CAlt{a2, b2} : Cx}, false_ne_true(h))
    case CEps{} CStar{a2}:
      Empty.absurd({CEps{} == CStar{a2} : Cx}, false_ne_true(h))
    case CEps{} CRef{i2}:
      Empty.absurd({CEps{} == CRef{i2} : Cx}, false_ne_true(h))
    case CEps{} CRange{l2, h2}:
      Empty.absurd({CEps{} == CRange{l2, h2} : Cx}, false_ne_true(h))
    case CChr{c1} CNone{}:
      Empty.absurd({CChr{c1} == CNone{} : Cx}, false_ne_true(h))
    case CChr{c1} CEps{}:
      Empty.absurd({CChr{c1} == CEps{} : Cx}, false_ne_true(h))
    case CChr{c1} CCat{a2, b2}:
      Empty.absurd({CChr{c1} == CCat{a2, b2} : Cx}, false_ne_true(h))
    case CChr{c1} CAlt{a2, b2}:
      Empty.absurd({CChr{c1} == CAlt{a2, b2} : Cx}, false_ne_true(h))
    case CChr{c1} CStar{a2}:
      Empty.absurd({CChr{c1} == CStar{a2} : Cx}, false_ne_true(h))
    case CChr{c1} CRef{i2}:
      Empty.absurd({CChr{c1} == CRef{i2} : Cx}, false_ne_true(h))
    case CChr{c1} CRange{l2, h2}:
      Empty.absurd({CChr{c1} == CRange{l2, h2} : Cx}, false_ne_true(h))
    case CCat{a1, b1} CNone{}:
      Empty.absurd({CCat{a1, b1} == CNone{} : Cx}, false_ne_true(h))
    case CCat{a1, b1} CEps{}:
      Empty.absurd({CCat{a1, b1} == CEps{} : Cx}, false_ne_true(h))
    case CCat{a1, b1} CChr{c2}:
      Empty.absurd({CCat{a1, b1} == CChr{c2} : Cx}, false_ne_true(h))
    case CCat{a1, b1} CAlt{a2, b2}:
      Empty.absurd({CCat{a1, b1} == CAlt{a2, b2} : Cx}, false_ne_true(h))
    case CCat{a1, b1} CStar{a2}:
      Empty.absurd({CCat{a1, b1} == CStar{a2} : Cx}, false_ne_true(h))
    case CCat{a1, b1} CRef{i2}:
      Empty.absurd({CCat{a1, b1} == CRef{i2} : Cx}, false_ne_true(h))
    case CCat{a1, b1} CRange{l2, h2}:
      Empty.absurd({CCat{a1, b1} == CRange{l2, h2} : Cx}, false_ne_true(h))
    case CAlt{a1, b1} CNone{}:
      Empty.absurd({CAlt{a1, b1} == CNone{} : Cx}, false_ne_true(h))
    case CAlt{a1, b1} CEps{}:
      Empty.absurd({CAlt{a1, b1} == CEps{} : Cx}, false_ne_true(h))
    case CAlt{a1, b1} CChr{c2}:
      Empty.absurd({CAlt{a1, b1} == CChr{c2} : Cx}, false_ne_true(h))
    case CAlt{a1, b1} CCat{a2, b2}:
      Empty.absurd({CAlt{a1, b1} == CCat{a2, b2} : Cx}, false_ne_true(h))
    case CAlt{a1, b1} CStar{a2}:
      Empty.absurd({CAlt{a1, b1} == CStar{a2} : Cx}, false_ne_true(h))
    case CAlt{a1, b1} CRef{i2}:
      Empty.absurd({CAlt{a1, b1} == CRef{i2} : Cx}, false_ne_true(h))
    case CAlt{a1, b1} CRange{l2, h2}:
      Empty.absurd({CAlt{a1, b1} == CRange{l2, h2} : Cx}, false_ne_true(h))
    case CStar{a1} CNone{}:
      Empty.absurd({CStar{a1} == CNone{} : Cx}, false_ne_true(h))
    case CStar{a1} CEps{}:
      Empty.absurd({CStar{a1} == CEps{} : Cx}, false_ne_true(h))
    case CStar{a1} CChr{c2}:
      Empty.absurd({CStar{a1} == CChr{c2} : Cx}, false_ne_true(h))
    case CStar{a1} CCat{a2, b2}:
      Empty.absurd({CStar{a1} == CCat{a2, b2} : Cx}, false_ne_true(h))
    case CStar{a1} CAlt{a2, b2}:
      Empty.absurd({CStar{a1} == CAlt{a2, b2} : Cx}, false_ne_true(h))
    case CStar{a1} CRef{i2}:
      Empty.absurd({CStar{a1} == CRef{i2} : Cx}, false_ne_true(h))
    case CStar{a1} CRange{l2, h2}:
      Empty.absurd({CStar{a1} == CRange{l2, h2} : Cx}, false_ne_true(h))
    case CRef{i1} CNone{}:
      Empty.absurd({CRef{i1} == CNone{} : Cx}, false_ne_true(h))
    case CRef{i1} CEps{}:
      Empty.absurd({CRef{i1} == CEps{} : Cx}, false_ne_true(h))
    case CRef{i1} CChr{c2}:
      Empty.absurd({CRef{i1} == CChr{c2} : Cx}, false_ne_true(h))
    case CRef{i1} CCat{a2, b2}:
      Empty.absurd({CRef{i1} == CCat{a2, b2} : Cx}, false_ne_true(h))
    case CRef{i1} CAlt{a2, b2}:
      Empty.absurd({CRef{i1} == CAlt{a2, b2} : Cx}, false_ne_true(h))
    case CRef{i1} CStar{a2}:
      Empty.absurd({CRef{i1} == CStar{a2} : Cx}, false_ne_true(h))
    case CRef{i1} CRange{l2, h2}:
      Empty.absurd({CRef{i1} == CRange{l2, h2} : Cx}, false_ne_true(h))
    case CRange{l1, h1} CNone{}:
      Empty.absurd({CRange{l1, h1} == CNone{} : Cx}, false_ne_true(h))
    case CRange{l1, h1} CEps{}:
      Empty.absurd({CRange{l1, h1} == CEps{} : Cx}, false_ne_true(h))
    case CRange{l1, h1} CChr{c2}:
      Empty.absurd({CRange{l1, h1} == CChr{c2} : Cx}, false_ne_true(h))
    case CRange{l1, h1} CCat{a2, b2}:
      Empty.absurd({CRange{l1, h1} == CCat{a2, b2} : Cx}, false_ne_true(h))
    case CRange{l1, h1} CAlt{a2, b2}:
      Empty.absurd({CRange{l1, h1} == CAlt{a2, b2} : Cx}, false_ne_true(h))
    case CRange{l1, h1} CStar{a2}:
      Empty.absurd({CRange{l1, h1} == CStar{a2} : Cx}, false_ne_true(h))
    case CRange{l1, h1} CRef{i2}:
      Empty.absurd({CRange{l1, h1} == CRef{i2} : Cx}, false_ne_true(h))

def rcon2(-a1: Rx, -a2: Rx, -b1: Rx, -b2: Rx, e1: {a1 == a2 : Rx}, e2: {b1 == b2 : Rx}, -K: Rx -> Rx -> Rx) -> {K(a1, b1) == K(a2, b2) : Rx}:
  %e1 : {K(a1, b1) == K(_, b2) : Rx}
  %e2 : {K(a1, b1) == K(a1, _) : Rx}
  {==}

def req_ok(x: Rx, y: Rx, +h: {req(x, y) == True{} : Bool}) -> {x == y : Rx}:
  match x y:
    case XNone{} XNone{}:
      {==}
    case XEps{} XEps{}:
      {==}
    case XAll{} XAll{}:
      {==}
    case XCat{+a1, +b1} XCat{+a2, +b2}:
      rcon2(a1, a2, b1, b2, req_ok(a1, a2, and_l(req(a1, a2), req(b1, b2), h)), req_ok(b1, b2, and_r(req(a1, a2), req(b1, b2), h)), p => q => XCat{p, q})
    case XAlt{+a1, +b1} XAlt{+a2, +b2}:
      rcon2(a1, a2, b1, b2, req_ok(a1, a2, and_l(req(a1, a2), req(b1, b2), h)), req_ok(b1, b2, and_r(req(a1, a2), req(b1, b2), h)), p => q => XAlt{p, q})
    case XAt{+d1, +x1} XAt{+d2, +x2}:
      %eqn_sound(d1, d2, and_l(eqn(d1, d2), ceq(x1, x2), h)) : {XAt{d1, x1} == XAt{_, x2} : Rx}
      %ceq_ok(x1, x2, and_r(eqn(d1, d2), ceq(x1, x2), h)) : {XAt{d1, x1} == XAt{d1, _} : Rx}
      {==}
    case XNone{} XEps{}:
      Empty.absurd({XNone{} == XEps{} : Rx}, false_ne_true(h))
    case XNone{} XAll{}:
      Empty.absurd({XNone{} == XAll{} : Rx}, false_ne_true(h))
    case XNone{} XCat{a2, b2}:
      Empty.absurd({XNone{} == XCat{a2, b2} : Rx}, false_ne_true(h))
    case XNone{} XAlt{a2, b2}:
      Empty.absurd({XNone{} == XAlt{a2, b2} : Rx}, false_ne_true(h))
    case XNone{} XAt{d2, x2}:
      Empty.absurd({XNone{} == XAt{d2, x2} : Rx}, false_ne_true(h))
    case XEps{} XNone{}:
      Empty.absurd({XEps{} == XNone{} : Rx}, false_ne_true(h))
    case XEps{} XAll{}:
      Empty.absurd({XEps{} == XAll{} : Rx}, false_ne_true(h))
    case XEps{} XCat{a2, b2}:
      Empty.absurd({XEps{} == XCat{a2, b2} : Rx}, false_ne_true(h))
    case XEps{} XAlt{a2, b2}:
      Empty.absurd({XEps{} == XAlt{a2, b2} : Rx}, false_ne_true(h))
    case XEps{} XAt{d2, x2}:
      Empty.absurd({XEps{} == XAt{d2, x2} : Rx}, false_ne_true(h))
    case XAll{} XNone{}:
      Empty.absurd({XAll{} == XNone{} : Rx}, false_ne_true(h))
    case XAll{} XEps{}:
      Empty.absurd({XAll{} == XEps{} : Rx}, false_ne_true(h))
    case XAll{} XCat{a2, b2}:
      Empty.absurd({XAll{} == XCat{a2, b2} : Rx}, false_ne_true(h))
    case XAll{} XAlt{a2, b2}:
      Empty.absurd({XAll{} == XAlt{a2, b2} : Rx}, false_ne_true(h))
    case XAll{} XAt{d2, x2}:
      Empty.absurd({XAll{} == XAt{d2, x2} : Rx}, false_ne_true(h))
    case XCat{a1, b1} XNone{}:
      Empty.absurd({XCat{a1, b1} == XNone{} : Rx}, false_ne_true(h))
    case XCat{a1, b1} XEps{}:
      Empty.absurd({XCat{a1, b1} == XEps{} : Rx}, false_ne_true(h))
    case XCat{a1, b1} XAll{}:
      Empty.absurd({XCat{a1, b1} == XAll{} : Rx}, false_ne_true(h))
    case XCat{a1, b1} XAlt{a2, b2}:
      Empty.absurd({XCat{a1, b1} == XAlt{a2, b2} : Rx}, false_ne_true(h))
    case XCat{a1, b1} XAt{d2, x2}:
      Empty.absurd({XCat{a1, b1} == XAt{d2, x2} : Rx}, false_ne_true(h))
    case XAlt{a1, b1} XNone{}:
      Empty.absurd({XAlt{a1, b1} == XNone{} : Rx}, false_ne_true(h))
    case XAlt{a1, b1} XEps{}:
      Empty.absurd({XAlt{a1, b1} == XEps{} : Rx}, false_ne_true(h))
    case XAlt{a1, b1} XAll{}:
      Empty.absurd({XAlt{a1, b1} == XAll{} : Rx}, false_ne_true(h))
    case XAlt{a1, b1} XCat{a2, b2}:
      Empty.absurd({XAlt{a1, b1} == XCat{a2, b2} : Rx}, false_ne_true(h))
    case XAlt{a1, b1} XAt{d2, x2}:
      Empty.absurd({XAlt{a1, b1} == XAt{d2, x2} : Rx}, false_ne_true(h))
    case XAt{d1, x1} XNone{}:
      Empty.absurd({XAt{d1, x1} == XNone{} : Rx}, false_ne_true(h))
    case XAt{d1, x1} XEps{}:
      Empty.absurd({XAt{d1, x1} == XEps{} : Rx}, false_ne_true(h))
    case XAt{d1, x1} XAll{}:
      Empty.absurd({XAt{d1, x1} == XAll{} : Rx}, false_ne_true(h))
    case XAt{d1, x1} XCat{a2, b2}:
      Empty.absurd({XAt{d1, x1} == XCat{a2, b2} : Rx}, false_ne_true(h))
    case XAt{d1, x1} XAlt{a2, b2}:
      Empty.absurd({XAt{d1, x1} == XAlt{a2, b2} : Rx}, false_ne_true(h))

def rx_tr(-top: Bool, -B: List<&2, Cx>, -t: String, -a: Rx, -b: Rx, e: {a == b : Rx}, k: {matches(t, bsem(top, B, a)) == True{} : Bool})
  -> {matches(t, bsem(top, B, b)) == True{} : Bool}:
  %e : {matches(t, bsem(top, B, _)) == True{} : Bool}
  k

def mem_ok(+top: Bool, +B: List<&2, Cx>, +t: String, +a: Rx, b: Rx, h: {mem(a, b) == True{} : Bool}, +k: {matches(t, bsem(top, B, a)) == True{} : Bool})
  -> {matches(t, bsem(top, B, b)) == True{} : Bool}:
  match b:
    case XAlt{+b1, +b2}:
      either(&2, &2, {req(a, b1) == True{} : Bool}, {mem(a, b2) == True{} : Bool}, {matches(t, bsem(top, B, XAlt{b1, b2})) == True{} : Bool},
        or_elim(req(a, b1), mem(a, b2), h),
        r => alt_l(t, bsem(top, B, b1), bsem(top, B, b2), rx_tr(top, B, t, a, b1, req_ok(a, b1, r), k)),
        m => alt_r(t, bsem(top, B, b1), bsem(top, B, b2), mem_ok(top, B, t, a, b2, m, k)))
    case XNone{}:
      rx_tr(top, B, t, a, XNone{}, req_ok(a, XNone{}, h), k)
    case XEps{}:
      rx_tr(top, B, t, a, XEps{}, req_ok(a, XEps{}, h), k)
    case XAll{}:
      rx_tr(top, B, t, a, XAll{}, req_ok(a, XAll{}, h), k)
    case XCat{+p, +q}:
      rx_tr(top, B, t, a, XCat{p, q}, req_ok(a, XCat{p, q}, h), k)
    case XAt{+d, +x}:
      rx_tr(top, B, t, a, XAt{d, x}, req_ok(a, XAt{d, x}, h), k)

def xalt.ins_ok(m: Bool, +top: Bool, +B: List<&2, Cx>, +t: String, +a: Rx, +b: Rx, +hm: {mem(a, b) == m : Bool})
  -> {matches(t, bsem(top, B, xalt.ins(m, a, b))) == Bool.or(matches(t, bsem(top, B, a)), matches(t, bsem(top, B, b))) : Bool}:
  match m:
    case True{}:
      beq(matches(t, bsem(top, B, b)), Bool.or(matches(t, bsem(top, B, a)), matches(t, bsem(top, B, b))),
        k => or_r(matches(t, bsem(top, B, a)), matches(t, bsem(top, B, b)), k),
        k => either(&2, &2, {matches(t, bsem(top, B, a)) == True{} : Bool}, {matches(t, bsem(top, B, b)) == True{} : Bool}, {matches(t, bsem(top, B, b)) == True{} : Bool},
          or_elim(matches(t, bsem(top, B, a)), matches(t, bsem(top, B, b)), k),
          ka => mem_ok(top, B, t, a, b, hm, ka),
          kb => kb))
    case False{}:
      alt_or(t, bsem(top, B, a), bsem(top, B, b))

def xalt.go_ok(+top: Bool, +B: List<&2, Cx>, a: Rx, +b: Rx, +t: String)
  -> {matches(t, bsem(top, B, xalt.go(a, b))) == Bool.or(matches(t, bsem(top, B, a)), matches(t, bsem(top, B, b))) : Bool}:
  match a:
    case XNone{}:
      Equal.sym(Bool, Bool.or(matches(t, RNone{}), matches(t, bsem(top, B, b))), matches(t, bsem(top, B, b)),
        or_f(matches(t, RNone{}), matches(t, bsem(top, B, b)), none_false(t)))
    case XAlt{+a1, +a2}:
      Equal.trans(Bool, matches(t, bsem(top, B, xalt.go(a1, xalt.go(a2, b)))),
        Bool.or(matches(t, bsem(top, B, a1)), matches(t, bsem(top, B, xalt.go(a2, b)))),
        Bool.or(matches(t, RAlt{bsem(top, B, a1), bsem(top, B, a2)}), matches(t, bsem(top, B, b))),
        xalt.go_ok(top, B, a1, xalt.go(a2, b), t),
        Equal.trans(Bool, Bool.or(matches(t, bsem(top, B, a1)), matches(t, bsem(top, B, xalt.go(a2, b)))),
          Bool.or(matches(t, bsem(top, B, a1)), Bool.or(matches(t, bsem(top, B, a2)), matches(t, bsem(top, B, b)))),
          Bool.or(matches(t, RAlt{bsem(top, B, a1), bsem(top, B, a2)}), matches(t, bsem(top, B, b))),
          bor_eq(matches(t, bsem(top, B, a1)), matches(t, bsem(top, B, a1)), matches(t, bsem(top, B, xalt.go(a2, b))), Bool.or(matches(t, bsem(top, B, a2)), matches(t, bsem(top, B, b))),
            {==}, xalt.go_ok(top, B, a2, b, t)),
          Equal.trans(Bool, Bool.or(matches(t, bsem(top, B, a1)), Bool.or(matches(t, bsem(top, B, a2)), matches(t, bsem(top, B, b)))),
            Bool.or(Bool.or(matches(t, bsem(top, B, a1)), matches(t, bsem(top, B, a2))), matches(t, bsem(top, B, b))),
            Bool.or(matches(t, RAlt{bsem(top, B, a1), bsem(top, B, a2)}), matches(t, bsem(top, B, b))),
            or_assoc(matches(t, bsem(top, B, a1)), matches(t, bsem(top, B, a2)), matches(t, bsem(top, B, b))),
            bor_eq(Bool.or(matches(t, bsem(top, B, a1)), matches(t, bsem(top, B, a2))), matches(t, RAlt{bsem(top, B, a1), bsem(top, B, a2)}),
              matches(t, bsem(top, B, b)), matches(t, bsem(top, B, b)),
              Equal.sym(Bool, matches(t, RAlt{bsem(top, B, a1), bsem(top, B, a2)}), Bool.or(matches(t, bsem(top, B, a1)), matches(t, bsem(top, B, a2))),
                alt_or(t, bsem(top, B, a1), bsem(top, B, a2))), {==}))))
    case XEps{}:
      xalt.ins_ok(mem(XEps{}, b), top, B, t, XEps{}, b, {==})
    case XAll{}:
      xalt.ins_ok(mem(XAll{}, b), top, B, t, XAll{}, b, {==})
    case XCat{+p, +q}:
      xalt.ins_ok(mem(XCat{p, q}, b), top, B, t, XCat{p, q}, b, {==})
    case XAt{+d, +x}:
      xalt.ins_ok(mem(XAt{d, x}, b), top, B, t, XAt{d, x}, b, {==})

def xalt_ok(+top: Bool, +B: List<&2, Cx>, +a: Rx, b: Rx, +t: String)
  -> {matches(t, bsem(top, B, xalt(a, b))) == Bool.or(matches(t, bsem(top, B, a)), matches(t, bsem(top, B, b))) : Bool}:
  match b:
    case XNone{}:
      %Equal.sym(Bool, matches(t, RNone{}), False{}, none_false(t)) : {matches(t, bsem(top, B, a)) == Bool.or(matches(t, bsem(top, B, a)), _) : Bool}
      Equal.sym(Bool, Bool.or(matches(t, bsem(top, B, a)), False{}), matches(t, bsem(top, B, a)), or_false(matches(t, bsem(top, B, a))))
    case XEps{}:
      xalt.go_ok(top, B, a, XEps{}, t)
    case XAll{}:
      xalt.go_ok(top, B, a, XAll{}, t)
    case XCat{+p, +q}:
      xalt.go_ok(top, B, a, XCat{p, q}, t)
    case XAlt{+p, +q}:
      xalt.go_ok(top, B, a, XAlt{p, q}, t)
    case XAt{+d, +x}:
      xalt.go_ok(top, B, a, XAt{d, x}, t)

def xat_eq(+top: Bool, +B: List<&2, Cx>, +d: Nat, x: Cx) -> {bsem(top, B, xat(d, x)) == isem(top, B, d, x) : Re}:
  match d:
    case 0n:
      match x:
        case CNone{}:
          {==}
        case CEps{}:
          {==}
        case CChr{c}:
          {==}
        case CCat{a, b}:
          {==}
        case CAlt{a, b}:
          {==}
        case CStar{a}:
          {==}
        case CRef{i}:
          {==}
        case CRange{lo, hi}:
          {==}
    case 1n+p:
      match x:
        case CNone{}:
          {==}
        case CEps{}:
          {==}
        case CChr{c}:
          {==}
        case CCat{a, b}:
          {==}
        case CAlt{a, b}:
          {==}
        case CStar{a}:
          {==}
        case CRef{i}:
          {==}
        case CRange{lo, hi}:
          {==}

def xwhen_eq(b: Bool, -top: Bool, -B: List<&2, Cx>) -> {bsem(top, B, xwhen(b)) == when(b) : Re}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def xbot_eq(+top: Bool, -B: List<&2, Cx>) -> {bsem(top, B, xbot(top)) == bot(top) : Re}:
  match top:
    case False{}:
      {==}
    case True{}:
      {==}

# Matching fast
# -------------

# fl(B, L, d, x) is the flag dat needs on a concatenation: whether its first
# part matches "". Passing it in lets dat skip the second part when it can't.

def fl(+B: List<&2, Cx>, +L: Lad, +d: Nat, x: Cx) -> Bool:
  match x:
    case CCat{a, b}:
      nat(lget(B, L, d), a)
    case _:
      False{}

# The derivative of a compiled rule at depth d, as a state.
def dat(+top: Bool, +B: List<&2, Cx>, +L: Lad, +c: Char, +d: Nat, x: Cx, f: Bool) -> Rx:
  match d:
    case 0n:
      match x:
        case CNone{}:
          XNone{}
        case CEps{}:
          XNone{}
        case CChr{y}:
          xwhen(Char.is_eq(y, c))
        case CCat{+a, +b}:
          match f:
            case False{}:
              xcat(dat(top, B, L, c, d, a, fl(B, L, d, a)), xat(d, b))
            case True{}:
              xalt(xcat(dat(top, B, L, c, d, a, fl(B, L, d, a)), xat(d, b)), dat(top, B, L, c, d, b, fl(B, L, d, b)))
        case CAlt{+a, +b}:
          xalt(dat(top, B, L, c, d, a, fl(B, L, d, a)), dat(top, B, L, c, d, b, fl(B, L, d, b)))
        case CStar{+a}:
          xcat(dat(top, B, L, c, d, a, fl(B, L, d, a)), XAt{d, CStar{a}})
        case CRef{i}:
          xbot(top)
        case CRange{lo, hi}:
          xwhen(inR(lo, hi, c))
    case 1n+p:
      match x:
        case CNone{}:
          XNone{}
        case CEps{}:
          XNone{}
        case CChr{y}:
          xwhen(Char.is_eq(y, c))
        case CCat{+a, +b}:
          match f:
            case False{}:
              xcat(dat(top, B, L, c, d, a, fl(B, L, d, a)), xat(d, b))
            case True{}:
              xalt(xcat(dat(top, B, L, c, d, a, fl(B, L, d, a)), xat(d, b)), dat(top, B, L, c, d, b, fl(B, L, d, b)))
        case CAlt{+a, +b}:
          xalt(dat(top, B, L, c, d, a, fl(B, L, d, a)), dat(top, B, L, c, d, b, fl(B, L, d, b)))
        case CStar{+a}:
          xcat(dat(top, B, L, c, d, a, fl(B, L, d, a)), XAt{d, CStar{a}})
        case CRef{i}:
          +body = nth(B, i)
          dat(top, B, L, c, p, body, fl(B, L, p, body))
        case CRange{lo, hi}:
          xwhen(inR(lo, hi, c))

def nx(+B: List<&2, Cx>, +L: Lad, x: Rx) -> Bool:
  match x:
    case XNone{}:
      False{}
    case XEps{}:
      True{}
    case XAll{}:
      True{}
    case XCat{a, b}:
      Bool.and(nx(B, L, a), nx(B, L, b))
    case XAlt{a, b}:
      Bool.or(nx(B, L, a), nx(B, L, b))
    case XAt{d, x}:
      nat(lget(B, L, d), x)

def flx(+B: List<&2, Cx>, +L: Lad, x: Rx) -> Bool:
  match x:
    case XCat{a, b}:
      nx(B, L, a)
    case _:
      False{}

# The derivative of a state.
def dx(+top: Bool, +B: List<&2, Cx>, +L: Lad, +c: Char, x: Rx, f: Bool) -> Rx:
  match x:
    case XNone{}:
      XNone{}
    case XEps{}:
      XNone{}
    case XAll{}:
      XAll{}
    case XCat{+a, +b}:
      match f:
        case False{}:
          xcat(dx(top, B, L, c, a, flx(B, L, a)), b)
        case True{}:
          xalt(xcat(dx(top, B, L, c, a, flx(B, L, a)), b), dx(top, B, L, c, b, flx(B, L, b)))
    case XAlt{+a, +b}:
      xalt(dx(top, B, L, c, a, flx(B, L, a)), dx(top, B, L, c, b, flx(B, L, b)))
    case XAt{+d, +x}:
      dat(top, B, L, c, d, x, fl(B, L, d, x))

def run(+top: Bool, +B: List<&2, Cx>, +L: Lad, s: String, +x: Rx) -> Bool:
  match s:
    case SNil{}:
      nx(B, L, x)
    case SCon{+c, t}:
      run(top, B, L, t, dx(top, B, L, c, x, flx(B, L, x)))

def nx_ok(+top: Bool, +B: List<&2, Cx>, x: Rx) -> {nx(B, mkLad(top, B), x) == nullable(bsem(top, B, x)) : Bool}:
  match x:
    case XNone{}:
      {==}
    case XEps{}:
      {==}
    case XAll{}:
      {==}
    case XCat{+a, +b}:
      band_eq(nx(B, mkLad(top, B), a), nullable(bsem(top, B, a)), nx(B, mkLad(top, B), b), nullable(bsem(top, B, b)), nx_ok(top, B, a), nx_ok(top, B, b))
    case XAlt{+a, +b}:
      bor_eq(nx(B, mkLad(top, B), a), nullable(bsem(top, B, a)), nx(B, mkLad(top, B), b), nullable(bsem(top, B, b)), nx_ok(top, B, a), nx_ok(top, B, b))
    case XAt{+d, +x}:
      nat_ok(top, B, d, x)

# A concatenation whose first part may match "": derive both parts.
def cat_t(+top: Bool, +B: List<&2, Cx>, +c: Char, +t: String, +DA: Rx, +R: Rx, +DB: Rx, +A: Re, +BR: Re,
  hn: {nullable(A) == True{} : Bool}, eR: {bsem(top, B, R) == BR : Re},
  fa: @s: String -> {matches(s, bsem(top, B, DA)) == True{} : Bool} -> {matches(s, deriv(c, A)) == True{} : Bool},
  ga: @s: String -> {matches(s, deriv(c, A)) == True{} : Bool} -> {matches(s, bsem(top, B, DA)) == True{} : Bool},
  eb: {matches(t, bsem(top, B, DB)) == matches(t, deriv(c, BR)) : Bool})
  -> {matches(t, bsem(top, B, xalt(xcat(DA, R), DB))) == matches(t, deriv(c, RCat{A, BR})) : Bool}:
  %Equal.sym(Bool, nullable(A), True{}, hn) : {matches(t, bsem(top, B, xalt(xcat(DA, R), DB))) == matches(t, deriv.cat(_, deriv(c, A), BR, deriv(c, BR))) : Bool}
  %Equal.sym(Bool, matches(t, bsem(top, B, xalt(xcat(DA, R), DB))), Bool.or(matches(t, bsem(top, B, xcat(DA, R))), matches(t, bsem(top, B, DB))), xalt_ok(top, B, xcat(DA, R), DB, t))
    : {_ == matches(t, RAlt{RCat{deriv(c, A), BR}, deriv(c, BR)}) : Bool}
  %Equal.sym(Bool, matches(t, bsem(top, B, xcat(DA, R))), matches(t, RCat{bsem(top, B, DA), bsem(top, B, R)}), xcat_ok(top, B, DA, R, t))
    : {Bool.or(_, matches(t, bsem(top, B, DB))) == matches(t, RAlt{RCat{deriv(c, A), BR}, deriv(c, BR)}) : Bool}
  %Equal.sym(Re, bsem(top, B, R), BR, eR) : {Bool.or(matches(t, RCat{bsem(top, B, DA), _}), matches(t, bsem(top, B, DB))) == matches(t, RAlt{RCat{deriv(c, A), BR}, deriv(c, BR)}) : Bool}
  %Equal.sym(Bool, matches(t, RCat{bsem(top, B, DA), BR}), matches(t, RCat{deriv(c, A), BR}), cat_cong_l(t, bsem(top, B, DA), deriv(c, A), BR, fa, ga))
    : {Bool.or(_, matches(t, bsem(top, B, DB))) == matches(t, RAlt{RCat{deriv(c, A), BR}, deriv(c, BR)}) : Bool}
  %Equal.sym(Bool, matches(t, bsem(top, B, DB)), matches(t, deriv(c, BR)), eb) : {Bool.or(matches(t, RCat{deriv(c, A), BR}), _) == matches(t, RAlt{RCat{deriv(c, A), BR}, deriv(c, BR)}) : Bool}
  Equal.sym(Bool, matches(t, RAlt{RCat{deriv(c, A), BR}, deriv(c, BR)}), Bool.or(matches(t, RCat{deriv(c, A), BR}), matches(t, deriv(c, BR))), alt_or(t, RCat{deriv(c, A), BR}, deriv(c, BR)))

# A concatenation whose first part can't match "": derive only that part.
def cat_f(+top: Bool, +B: List<&2, Cx>, +c: Char, +t: String, +DA: Rx, +R: Rx, +A: Re, +BR: Re,
  hn: {nullable(A) == False{} : Bool}, eR: {bsem(top, B, R) == BR : Re},
  fa: @s: String -> {matches(s, bsem(top, B, DA)) == True{} : Bool} -> {matches(s, deriv(c, A)) == True{} : Bool},
  ga: @s: String -> {matches(s, deriv(c, A)) == True{} : Bool} -> {matches(s, bsem(top, B, DA)) == True{} : Bool})
  -> {matches(t, bsem(top, B, xcat(DA, R))) == matches(t, deriv(c, RCat{A, BR})) : Bool}:
  %Equal.sym(Bool, nullable(A), False{}, hn) : {matches(t, bsem(top, B, xcat(DA, R))) == matches(t, deriv.cat(_, deriv(c, A), BR, deriv(c, BR))) : Bool}
  %Equal.sym(Bool, matches(t, bsem(top, B, xcat(DA, R))), matches(t, RCat{bsem(top, B, DA), bsem(top, B, R)}), xcat_ok(top, B, DA, R, t))
    : {_ == matches(t, RCat{deriv(c, A), BR}) : Bool}
  %Equal.sym(Re, bsem(top, B, R), BR, eR) : {matches(t, RCat{bsem(top, B, DA), _}) == matches(t, RCat{deriv(c, A), BR}) : Bool}
  cat_cong_l(t, bsem(top, B, DA), deriv(c, A), BR, fa, ga)

def alt_d(+top: Bool, +B: List<&2, Cx>, +c: Char, +t: String, +DA: Rx, +DB: Rx, +A: Re, +BR: Re,
  ea: {matches(t, bsem(top, B, DA)) == matches(t, deriv(c, A)) : Bool}, eb: {matches(t, bsem(top, B, DB)) == matches(t, deriv(c, BR)) : Bool})
  -> {matches(t, bsem(top, B, xalt(DA, DB))) == matches(t, RAlt{deriv(c, A), deriv(c, BR)}) : Bool}:
  Equal.trans(Bool, matches(t, bsem(top, B, xalt(DA, DB))), Bool.or(matches(t, bsem(top, B, DA)), matches(t, bsem(top, B, DB))), matches(t, RAlt{deriv(c, A), deriv(c, BR)}),
    xalt_ok(top, B, DA, DB, t),
    Equal.trans(Bool, Bool.or(matches(t, bsem(top, B, DA)), matches(t, bsem(top, B, DB))), Bool.or(matches(t, deriv(c, A)), matches(t, deriv(c, BR))), matches(t, RAlt{deriv(c, A), deriv(c, BR)}),
      bor_eq(matches(t, bsem(top, B, DA)), matches(t, deriv(c, A)), matches(t, bsem(top, B, DB)), matches(t, deriv(c, BR)), ea, eb),
      Equal.sym(Bool, matches(t, RAlt{deriv(c, A), deriv(c, BR)}), Bool.or(matches(t, deriv(c, A)), matches(t, deriv(c, BR))), alt_or(t, deriv(c, A), deriv(c, BR)))))

def star_d(+top: Bool, +B: List<&2, Cx>, +c: Char, +t: String, +DA: Rx, +A: Re, +R: Rx, eR: {bsem(top, B, R) == RStar{A} : Re},
  fa: @s: String -> {matches(s, bsem(top, B, DA)) == True{} : Bool} -> {matches(s, deriv(c, A)) == True{} : Bool},
  ga: @s: String -> {matches(s, deriv(c, A)) == True{} : Bool} -> {matches(s, bsem(top, B, DA)) == True{} : Bool})
  -> {matches(t, bsem(top, B, xcat(DA, R))) == matches(t, RCat{deriv(c, A), RStar{A}}) : Bool}:
  %Equal.sym(Bool, matches(t, bsem(top, B, xcat(DA, R))), matches(t, RCat{bsem(top, B, DA), bsem(top, B, R)}), xcat_ok(top, B, DA, R, t))
    : {_ == matches(t, RCat{deriv(c, A), RStar{A}}) : Bool}
  %Equal.sym(Re, bsem(top, B, R), RStar{A}, eR) : {matches(t, RCat{bsem(top, B, DA), _}) == matches(t, RCat{deriv(c, A), RStar{A}}) : Bool}
  cat_cong_l(t, bsem(top, B, DA), deriv(c, A), RStar{A}, fa, ga)

def ref0_d(+top: Bool, -B: List<&2, Cx>, +c: Char, +t: String) -> {matches(t, bsem(top, B, xbot(top))) == matches(t, deriv(c, bot(top))) : Bool}:
  match top:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, matches(t, SIG), True{}, matches(SCon{c, t}, SIG), sig_all(t), Equal.sym(Bool, matches(SCon{c, t}, SIG), True{}, sig_all(SCon{c, t})))

# The derivative of a compiled rule matches what the derivative of its meaning does.
def dat_ok(+top: Bool, +B: List<&2, Cx>, +c: Char, +d: Nat, x: Cx, +t: String)
  -> {matches(t, bsem(top, B, dat(top, B, mkLad(top, B), c, d, x, fl(B, mkLad(top, B), d, x)))) == matches(t, deriv(c, isem(top, B, d, x))) : Bool}:
  match d:
    case 0n:
      match x:
        case CNone{}:
          {==}
        case CEps{}:
          {==}
        case CChr{+y}:
          mcong(t, bsem(top, B, xwhen(Char.is_eq(y, c))), when(Char.is_eq(y, c)), xwhen_eq(Char.is_eq(y, c), top, B))
        case CCat{+a, +b}:
          bcase({matches(t, bsem(top, B, dat(top, B, mkLad(top, B), c, d, CCat{a, b}, fl(B, mkLad(top, B), d, CCat{a, b})))) == matches(t, deriv(c, isem(top, B, d, CCat{a, b}))) : Bool}, nat(lget(B, mkLad(top, B), d), a),
            +k => %Equal.sym(Bool, nat(lget(B, mkLad(top, B), d), a), True{}, k)
                : {matches(t, bsem(top, B, dat(top, B, mkLad(top, B), c, d, CCat{a, b}, _))) == matches(t, deriv(c, isem(top, B, d, CCat{a, b}))) : Bool}
              cat_t(top, B, c, t, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)), xat(d, b), dat(top, B, mkLad(top, B), c, d, b, fl(B, mkLad(top, B), d, b)), isem(top, B, d, a), isem(top, B, d, b),
                Equal.trans(Bool, nullable(isem(top, B, d, a)), nat(lget(B, mkLad(top, B), d), a), True{}, Equal.sym(Bool, nat(lget(B, mkLad(top, B), d), a), nullable(isem(top, B, d, a)), nat_ok(top, B, d, a)), k),
                xat_eq(top, B, d, b),
                +s => h => tt.sym(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h),
                +s => h => tt(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h),
                dat_ok(top, B, c, d, b, t)),
            +k => %Equal.sym(Bool, nat(lget(B, mkLad(top, B), d), a), False{}, k)
                : {matches(t, bsem(top, B, dat(top, B, mkLad(top, B), c, d, CCat{a, b}, _))) == matches(t, deriv(c, isem(top, B, d, CCat{a, b}))) : Bool}
              cat_f(top, B, c, t, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)), xat(d, b), isem(top, B, d, a), isem(top, B, d, b),
                Equal.trans(Bool, nullable(isem(top, B, d, a)), nat(lget(B, mkLad(top, B), d), a), False{}, Equal.sym(Bool, nat(lget(B, mkLad(top, B), d), a), nullable(isem(top, B, d, a)), nat_ok(top, B, d, a)), k),
                xat_eq(top, B, d, b),
                +s => h => tt.sym(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h),
                +s => h => tt(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h)))
        case CAlt{+a, +b}:
          alt_d(top, B, c, t, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)), dat(top, B, mkLad(top, B), c, d, b, fl(B, mkLad(top, B), d, b)), isem(top, B, d, a), isem(top, B, d, b), dat_ok(top, B, c, d, a, t), dat_ok(top, B, c, d, b, t))
        case CStar{+a}:
          star_d(top, B, c, t, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)), isem(top, B, d, a), XAt{d, CStar{a}}, {==},
            +s => h => tt.sym(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h),
            +s => h => tt(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h))
        case CRange{+lo, +hi}:
          mcong(t, bsem(top, B, xwhen(inR(lo, hi, c))), when(inR(lo, hi, c)), xwhen_eq(inR(lo, hi, c), top, B))
        case CRef{i}:
          ref0_d(top, B, c, t)
    case 1n+ +p:
      match x:
        case CNone{}:
          {==}
        case CEps{}:
          {==}
        case CChr{+y}:
          mcong(t, bsem(top, B, xwhen(Char.is_eq(y, c))), when(Char.is_eq(y, c)), xwhen_eq(Char.is_eq(y, c), top, B))
        case CCat{+a, +b}:
          bcase({matches(t, bsem(top, B, dat(top, B, mkLad(top, B), c, d, CCat{a, b}, fl(B, mkLad(top, B), d, CCat{a, b})))) == matches(t, deriv(c, isem(top, B, d, CCat{a, b}))) : Bool}, nat(lget(B, mkLad(top, B), d), a),
            +k => %Equal.sym(Bool, nat(lget(B, mkLad(top, B), d), a), True{}, k)
                : {matches(t, bsem(top, B, dat(top, B, mkLad(top, B), c, d, CCat{a, b}, _))) == matches(t, deriv(c, isem(top, B, d, CCat{a, b}))) : Bool}
              cat_t(top, B, c, t, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)), xat(d, b), dat(top, B, mkLad(top, B), c, d, b, fl(B, mkLad(top, B), d, b)), isem(top, B, d, a), isem(top, B, d, b),
                Equal.trans(Bool, nullable(isem(top, B, d, a)), nat(lget(B, mkLad(top, B), d), a), True{}, Equal.sym(Bool, nat(lget(B, mkLad(top, B), d), a), nullable(isem(top, B, d, a)), nat_ok(top, B, d, a)), k),
                xat_eq(top, B, d, b),
                +s => h => tt.sym(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h),
                +s => h => tt(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h),
                dat_ok(top, B, c, d, b, t)),
            +k => %Equal.sym(Bool, nat(lget(B, mkLad(top, B), d), a), False{}, k)
                : {matches(t, bsem(top, B, dat(top, B, mkLad(top, B), c, d, CCat{a, b}, _))) == matches(t, deriv(c, isem(top, B, d, CCat{a, b}))) : Bool}
              cat_f(top, B, c, t, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)), xat(d, b), isem(top, B, d, a), isem(top, B, d, b),
                Equal.trans(Bool, nullable(isem(top, B, d, a)), nat(lget(B, mkLad(top, B), d), a), False{}, Equal.sym(Bool, nat(lget(B, mkLad(top, B), d), a), nullable(isem(top, B, d, a)), nat_ok(top, B, d, a)), k),
                xat_eq(top, B, d, b),
                +s => h => tt.sym(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h),
                +s => h => tt(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h)))
        case CAlt{+a, +b}:
          alt_d(top, B, c, t, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)), dat(top, B, mkLad(top, B), c, d, b, fl(B, mkLad(top, B), d, b)), isem(top, B, d, a), isem(top, B, d, b), dat_ok(top, B, c, d, a, t), dat_ok(top, B, c, d, b, t))
        case CStar{+a}:
          star_d(top, B, c, t, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)), isem(top, B, d, a), XAt{d, CStar{a}}, {==},
            +s => h => tt.sym(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h),
            +s => h => tt(matches(s, bsem(top, B, dat(top, B, mkLad(top, B), c, d, a, fl(B, mkLad(top, B), d, a)))), matches(s, deriv(c, isem(top, B, d, a))), dat_ok(top, B, c, d, a, s), h))
        case CRange{+lo, +hi}:
          mcong(t, bsem(top, B, xwhen(inR(lo, hi, c))), when(inR(lo, hi, c)), xwhen_eq(inR(lo, hi, c), top, B))
        case CRef{+i}:
          dat_ok(top, B, c, p, nth(B, i), t)

# The same for states.
def dx_ok(+top: Bool, +B: List<&2, Cx>, +c: Char, x: Rx, +t: String)
  -> {matches(t, bsem(top, B, dx(top, B, mkLad(top, B), c, x, flx(B, mkLad(top, B), x)))) == matches(t, deriv(c, bsem(top, B, x))) : Bool}:
  match x:
    case XNone{}:
      {==}
    case XEps{}:
      {==}
    case XAll{}:
      Equal.trans(Bool, matches(t, SIG), True{}, matches(SCon{c, t}, SIG), sig_all(t), Equal.sym(Bool, matches(SCon{c, t}, SIG), True{}, sig_all(SCon{c, t})))
    case XCat{+a, +b}:
      bcase({matches(t, bsem(top, B, dx(top, B, mkLad(top, B), c, XCat{a, b}, flx(B, mkLad(top, B), XCat{a, b})))) == matches(t, deriv(c, bsem(top, B, XCat{a, b}))) : Bool}, nx(B, mkLad(top, B), a),
        +k => %Equal.sym(Bool, nx(B, mkLad(top, B), a), True{}, k)
            : {matches(t, bsem(top, B, dx(top, B, mkLad(top, B), c, XCat{a, b}, _))) == matches(t, deriv(c, bsem(top, B, XCat{a, b}))) : Bool}
          cat_t(top, B, c, t, dx(top, B, mkLad(top, B), c, a, flx(B, mkLad(top, B), a)), b, dx(top, B, mkLad(top, B), c, b, flx(B, mkLad(top, B), b)), bsem(top, B, a), bsem(top, B, b),
            Equal.trans(Bool, nullable(bsem(top, B, a)), nx(B, mkLad(top, B), a), True{}, Equal.sym(Bool, nx(B, mkLad(top, B), a), nullable(bsem(top, B, a)), nx_ok(top, B, a)), k),
            {==},
            +s => h => tt.sym(matches(s, bsem(top, B, dx(top, B, mkLad(top, B), c, a, flx(B, mkLad(top, B), a)))), matches(s, deriv(c, bsem(top, B, a))), dx_ok(top, B, c, a, s), h),
            +s => h => tt(matches(s, bsem(top, B, dx(top, B, mkLad(top, B), c, a, flx(B, mkLad(top, B), a)))), matches(s, deriv(c, bsem(top, B, a))), dx_ok(top, B, c, a, s), h),
            dx_ok(top, B, c, b, t)),
        +k => %Equal.sym(Bool, nx(B, mkLad(top, B), a), False{}, k)
            : {matches(t, bsem(top, B, dx(top, B, mkLad(top, B), c, XCat{a, b}, _))) == matches(t, deriv(c, bsem(top, B, XCat{a, b}))) : Bool}
          cat_f(top, B, c, t, dx(top, B, mkLad(top, B), c, a, flx(B, mkLad(top, B), a)), b, bsem(top, B, a), bsem(top, B, b),
            Equal.trans(Bool, nullable(bsem(top, B, a)), nx(B, mkLad(top, B), a), False{}, Equal.sym(Bool, nx(B, mkLad(top, B), a), nullable(bsem(top, B, a)), nx_ok(top, B, a)), k),
            {==},
            +s => h => tt.sym(matches(s, bsem(top, B, dx(top, B, mkLad(top, B), c, a, flx(B, mkLad(top, B), a)))), matches(s, deriv(c, bsem(top, B, a))), dx_ok(top, B, c, a, s), h),
            +s => h => tt(matches(s, bsem(top, B, dx(top, B, mkLad(top, B), c, a, flx(B, mkLad(top, B), a)))), matches(s, deriv(c, bsem(top, B, a))), dx_ok(top, B, c, a, s), h)))
    case XAlt{+a, +b}:
      alt_d(top, B, c, t, dx(top, B, mkLad(top, B), c, a, flx(B, mkLad(top, B), a)), dx(top, B, mkLad(top, B), c, b, flx(B, mkLad(top, B), b)), bsem(top, B, a), bsem(top, B, b), dx_ok(top, B, c, a, t), dx_ok(top, B, c, b, t))
    case XAt{+d, +x}:
      dat_ok(top, B, c, d, x, t)

# Running the states over s matches s against the first state's meaning.
def run_ok(+top: Bool, +B: List<&2, Cx>, s: String, +x: Rx) -> {run(top, B, mkLad(top, B), s, x) == matches(s, bsem(top, B, x)) : Bool}:
  match s:
    case SNil{}:
      nx_ok(top, B, x)
    case SCon{+c, +u}:
      Equal.trans(Bool, run(top, B, mkLad(top, B), u, dx(top, B, mkLad(top, B), c, x, flx(B, mkLad(top, B), x))), matches(u, bsem(top, B, dx(top, B, mkLad(top, B), c, x, flx(B, mkLad(top, B), x)))), matches(u, deriv(c, bsem(top, B, x))),
        run_ok(top, B, u, dx(top, B, mkLad(top, B), c, x, flx(B, mkLad(top, B), x))), dx_ok(top, B, c, x, u))

# Checking
# --------

# fast(top, G, r, s, D) matches s against r at depth D, with bot(top) below.
def fast(+top: Bool, +G: List<&2, Ent>, r: Re, +s: String, D: Nat) -> Bool:
  +B = cbs(G)
  run(top, B, mkLad(top, B), s, XAt{D, comp(cks(G), r)})

def fast_ok(+top: Bool, +G: List<&2, Ent>, +r: Re, +s: String, +D: Nat)
  -> {fast(top, G, r, s, D) == matches(s, subst(r, tbB(botT(top), D, G))) : Bool}:
  Equal.trans(Bool, run(top, cbs(G), mkLad(top, cbs(G)), s, XAt{D, comp(cks(G), r)}), matches(s, isem(top, cbs(G), D, comp(cks(G), r))),
    matches(s, subst(r, tbB(botT(top), D, G))),
    run_ok(top, cbs(G), s, XAt{D, comp(cks(G), r)}),
    mcong(s, isem(top, cbs(G), D, comp(cks(G), r)), subst(r, tbB(botT(top), D, G)), cl(top, G, D, r)))

def fast_dead(+G: List<&2, Ent>, +r: Re, +s: String, +D: Nat) -> {fast(False{}, G, r, s, D) == matches(s, subst(r, tbl(D, G))) : Bool}:
  %tbB_dead(D, G) : {fast(False{}, G, r, s, D) == matches(s, subst(r, _)) : Bool}
  fast_ok(False{}, G, r, s, D)

def elen(G: List<&2, Ent>) -> Nat:
  match G:
    case []:
      0n
    case h <> t:
      1n+elen(t)

# The depth fast tries first. A derivation needs about one level per nested
# rule, so this is ample for any input of length n; when it isn't, chkF
# notices and falls back to bound(s, G).
def depth(+G: List<&2, Ent>, +s: String) -> Nat:
  1n+Nat.mul(1n+elen(G), 1n+String.length(s))

# Below depth D, matching nothing gives a lower answer and matching
# everything an upper one; the true answer lies between. So a True from the
# first or a False from the second is final. Otherwise check at bound(s, G).
def chkF.up(up: Bool, +G: List<&2, Ent>, r: Re, +s: String) -> Bool:
  match up:
    case False{}:
      False{}
    case True{}:
      fast(False{}, G, r, s, bound(s, G))

def chkF.lo(lo: Bool, +G: List<&2, Ent>, +r: Re, +s: String) -> Bool:
  match lo:
    case True{}:
      True{}
    case False{}:
      chkF.up(fast(True{}, G, r, s, depth(G, s)), G, r, s)

def chkF(+G: List<&2, Ent>, +r: Re, +s: String) -> Bool:
  chkF.lo(fast(False{}, G, r, s, depth(G, s)), G, r, s)

def chkF.up_ok(up: Bool, +G: List<&2, Ent>, +r: Re, +s: String, +hu: {up == matches(s, subst(r, tbB(TTop{}, depth(G, s), G))) : Bool})
  -> {chkF.up(up, G, r, s) == matches(s, subst(r, tbl(bound(s, G), G))) : Bool}:
  match up:
    case False{}:
      bcase({False{} == matches(s, subst(r, tbl(bound(s, G), G))) : Bool}, matches(s, subst(r, tbl(bound(s, G), G))),
        k => Empty.absurd({False{} == matches(s, subst(r, tbl(bound(s, G), G))) : Bool},
          false_ne_true(Equal.trans(Bool, False{}, matches(s, subst(r, tbB(TTop{}, depth(G, s), G))), True{}, hu, upper(depth(G, s), bound(s, G), G, r, s, k)))),
        k => Equal.sym(Bool, matches(s, subst(r, tbl(bound(s, G), G))), False{}, k))
    case True{}:
      fast_dead(G, r, s, bound(s, G))

def chkF.lo_ok(lo: Bool, +G: List<&2, Ent>, +r: Re, +s: String, +hl: {lo == matches(s, subst(r, tbl(depth(G, s), G))) : Bool})
  -> {chkF.lo(lo, G, r, s) == matches(s, subst(r, tbl(bound(s, G), G))) : Bool}:
  match lo:
    case True{}:
      Equal.sym(Bool, matches(s, subst(r, tbl(bound(s, G), G))), True{},
        shrink(G, s, depth(G, s), r, Equal.sym(Bool, True{}, matches(s, subst(r, tbl(depth(G, s), G))), hl)))
    case False{}:
      chkF.up_ok(fast(True{}, G, r, s, depth(G, s)), G, r, s, fast_ok(True{}, G, r, s, depth(G, s)))

# The fast check answers what the full grammar's definition does.
def chkF_ok(+G: List<&2, Ent>, +r: Re, +s: String) -> {chkF(G, r, s) == matches(s, subst(r, tbl(bound(s, G), G))) : Bool}:
  chkF.lo_ok(fast(False{}, G, r, s, depth(G, s)), G, r, s, fast_dead(G, r, s, depth(G, s)))

def chk(book: Bk, +r: Re, +s: String) -> Bool:
  match book:
    case BFull{+g}:
      chkF(g, r, s)
    case BLim{d, +g}:
      matches(s, subst(r, tbl(d, g)))

def chk_eq(book: Bk, +r: Re, +s: String) -> {ochk(book, r, s) == chk(book, r, s) : Bool}:
  match book:
    case BFull{+g}:
      Equal.sym(Bool, chkF(g, r, s), ochk(BFull{g}, r, s), chkF_ok(g, r, s))
    case BLim{d, +g}:
      {==}

# Proofs
# ======

def Laws.check(book, r, s):
  chk(book, r, s)

# Each law is proven for ochk, then carried over by chk_eq.

def c2o(+book: Bk, +r: Re, +s: String, -v: Bool, h: {chk(book, r, s) == v : Bool}) -> {ochk(book, r, s) == v : Bool}:
  Equal.trans(Bool, ochk(book, r, s), chk(book, r, s), v, chk_eq(book, r, s), h)

def o2c(+book: Bk, +r: Re, +s: String, -v: Bool, h: {ochk(book, r, s) == v : Bool}) -> {chk(book, r, s) == v : Bool}:
  Equal.trans(Bool, chk(book, r, s), ochk(book, r, s), v, Equal.sym(Bool, ochk(book, r, s), chk(book, r, s), chk_eq(book, r, s)), h)

def o2c2(+book: Bk, +x: Re, +y: Re, +s: String, h: {ochk(book, x, s) == ochk(book, y, s) : Bool}) -> {chk(book, x, s) == chk(book, y, s) : Bool}:
  %chk_eq(book, x, s) : {_ == chk(book, y, s) : Bool}
  %chk_eq(book, y, s) : {ochk(book, x, s) == _ : Bool}
  h

def none_c(+book: Bk, +s: String) -> {chk(book, RNone{}, s) == False{} : Bool}:
  o2c(book, RNone{}, s, False{}, none_false(s))

def eps_con_c(+book: Bk, +a: Char, +t: String) -> {chk(book, REps{}, SCon{a, t}) == False{} : Bool}:
  o2c(book, REps{}, SCon{a, t}, False{}, none_false(t))

def range_ok_c(+book: Bk, +lo: Char, +hi: Char, +s: String)
  -> {chk(book, RRange{lo, hi}, s) == chk(book, Laws.alt(chars.go(rcount(lo, hi), lo)), s) : Bool}:
  o2c2(book, RRange{lo, hi}, Laws.alt(chars.go(rcount(lo, hi), lo)), s, range_ok_b(book, lo, hi, s))

def lookup_con_c(+book: Bk, +k: String, +r: Re, +G: List<&2, Ent>, +ln: String, +s: String)
  -> {chk(book, lookupE(Ent{k, r} <> G, ln), s) == Bool.or(Bool.and(String.eq(String.to_lower(k), ln), chk(book, r, s)), chk(book, lookupE(G, ln), s)) : Bool}:
  %chk_eq(book, lookupE(Ent{k, r} <> G, ln), s) : {_ == Bool.or(Bool.and(String.eq(String.to_lower(k), ln), chk(book, r, s)), chk(book, lookupE(G, ln), s)) : Bool}
  %chk_eq(book, r, s) : {ochk(book, lookupE(Ent{k, r} <> G, ln), s) == Bool.or(Bool.and(String.eq(String.to_lower(k), ln), _), chk(book, lookupE(G, ln), s)) : Bool}
  %chk_eq(book, lookupE(G, ln), s) : {ochk(book, lookupE(Ent{k, r} <> G, ln), s) == Bool.or(Bool.and(String.eq(String.to_lower(k), ln), ochk(book, r, s)), _) : Bool}
  lookup_con_b(book, k, r, G, ln, s)

def alt_con_c(+book: Bk, +r: Re, +y: Re, +s: String) -> {chk(book, RAlt{r, y}, s) == Bool.or(chk(book, r, s), chk(book, y, s)) : Bool}:
  %chk_eq(book, RAlt{r, y}, s) : {_ == Bool.or(chk(book, r, s), chk(book, y, s)) : Bool}
  %chk_eq(book, r, s) : {ochk(book, RAlt{r, y}, s) == Bool.or(_, chk(book, y, s)) : Bool}
  %chk_eq(book, y, s) : {ochk(book, RAlt{r, y}, s) == Bool.or(ochk(book, r, s), _) : Bool}
  alt_con_b(book, r, y, s)

def full_intro_c(+d: Nat, +G: List<&2, Ent>, +r: Re, +s: String, h: {matches(s, subst(r, tbl(d, G))) == True{} : Bool})
  -> {chk(BFull{G}, r, s) == True{} : Bool}:
  o2c(BFull{G}, r, s, True{}, shrink(G, s, d, r, h))

def full_elim_c(+G: List<&2, Ent>, +r: Re, +s: String, h: {chk(BFull{G}, r, s) == True{} : Bool})
  -> &d: Nat -> {matches(s, subst(r, tbl(d, G))) == True{} : Bool}:
  full_elim_b(G, r, s, c2o(BFull{G}, r, s, True{}, h))

def char_one_c(+book: Bk, +c: Char, +x: Char) -> {chk(book, RChr{c}, SCon{x, SNil{}}) == Char.is_eq(c, x) : Bool}:
  o2c(book, RChr{c}, SCon{x, SNil{}}, Char.is_eq(c, x), nullable_when(Char.is_eq(c, x)))

def char_many_c(+book: Bk, +c: Char, +a: Char, +b: Char, +t: String) -> {chk(book, RChr{c}, SCon{a, SCon{b, t}}) == False{} : Bool}:
  o2c(book, RChr{c}, SCon{a, SCon{b, t}}, False{}, deriv_when(Char.is_eq(c, a), b, t))

def seq_intro_c(+book: Bk, +r: Re, +y: Re, +s1: String, +s2: String, h1: {chk(book, r, s1) == True{} : Bool}, h2: {chk(book, y, s2) == True{} : Bool})
  -> {chk(book, RCat{r, y}, String.append(s1, s2)) == True{} : Bool}:
  o2c(book, RCat{r, y}, String.append(s1, s2), True{}, seq_intro_b(book, r, y, s1, s2, c2o(book, r, s1, True{}, h1), c2o(book, y, s2, True{}, h2)))

def seq_elim_c.go(+book: Bk, +r: Re, +y: Re, -s: String,
  p: &s1: String -> &s2: String -> {String.append(s1, s2) == s : String} & {ochk(book, r, s1) == True{} : Bool} & {ochk(book, y, s2) == True{} : Bool})
  -> &s1: String -> &s2: String -> {String.append(s1, s2) == s : String} & {chk(book, r, s1) == True{} : Bool} & {chk(book, y, s2) == True{} : Bool}:
  (+s1, +s2, e, h1, h2) = p
  (s1, s2, e, o2c(book, r, s1, True{}, h1), o2c(book, y, s2, True{}, h2))

def seq_elim_c(+book: Bk, +r: Re, +y: Re, +s: String, h: {chk(book, RCat{r, y}, s) == True{} : Bool})
  -> &s1: String -> &s2: String -> {String.append(s1, s2) == s : String} & {chk(book, r, s1) == True{} : Bool} & {chk(book, y, s2) == True{} : Bool}:
  seq_elim_c.go(book, r, y, s, seq_elim_b(book, r, y, s, c2o(book, RCat{r, y}, s, True{}, h)))

def any_intro_c(+book: Bk, +m: Nat, +r: Re, +s: String, hs: {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool})
  -> {chk(book, RStar{r}, s) == True{} : Bool}:
  o2c(book, RStar{r}, s, True{}, any_intro_b(book, m, r, s, c2o(book, Laws.rep.exactly(m, r), s, True{}, hs)))

def any_elim_c.go(+book: Bk, +r: Re, +s: String, p: &m: Nat -> {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool})
  -> &m: Nat -> {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  (+m, h) = p
  (m, o2c(book, Laws.rep.exactly(m, r), s, True{}, h))

def any_elim_c(+book: Bk, +r: Re, +s: String, hs: {chk(book, RStar{r}, s) == True{} : Bool})
  -> &m: Nat -> {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  any_elim_c.go(book, r, s, any_elim_b(book, r, s, c2o(book, RStar{r}, s, True{}, hs)))

def al_intro_c(+book: Bk, +n: Nat, +m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}, +r: Re, +s: String,
  hs: {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}) -> {chk(book, Laws.rep.at_least(n, r), s) == True{} : Bool}:
  o2c(book, Laws.rep.at_least(n, r), s, True{}, al_intro_b(book, n, m, h, r, s, c2o(book, Laws.rep.exactly(m, r), s, True{}, hs)))

def lo_elim_c.go(+book: Bk, -n: Nat, +r: Re, +s: String, p: &m: Nat -> {Nat.is_le(n, m) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(n, m) == True{} : Bool} & {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  (+m, le, h) = p
  (m, le, o2c(book, Laws.rep.exactly(m, r), s, True{}, h))

def hi_elim_c.go(+book: Bk, -n: Nat, +r: Re, +s: String, p: &m: Nat -> {Nat.is_le(m, n) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(m, n) == True{} : Bool} & {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  (+m, le, h) = p
  (m, le, o2c(book, Laws.rep.exactly(m, r), s, True{}, h))

def in_elim_c.go(+book: Bk, -a: Nat, -b: Nat, +r: Re, +s: String,
  p: &m: Nat -> {Nat.is_le(a, m) == True{} : Bool} & {Nat.is_le(m, b) == True{} : Bool} & {ochk(book, Laws.rep.exactly(m, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(a, m) == True{} : Bool} & {Nat.is_le(m, b) == True{} : Bool} & {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  (+m, la, lb, h) = p
  (m, la, lb, o2c(book, Laws.rep.exactly(m, r), s, True{}, h))

def al_elim_c(+book: Bk, +n: Nat, +r: Re, +s: String, hs: {chk(book, Laws.rep.at_least(n, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(n, m) == True{} : Bool} & {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  lo_elim_c.go(book, n, r, s, al_elim_b(book, n, r, s, c2o(book, Laws.rep.at_least(n, r), s, True{}, hs)))

def am_intro_c(+book: Bk, +n: Nat, +m: Nat, h: {Nat.is_le(m, n) == True{} : Bool}, +r: Re, +s: String,
  hs: {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}) -> {chk(book, Laws.rep.at_most(n, r), s) == True{} : Bool}:
  o2c(book, Laws.rep.at_most(n, r), s, True{}, am_intro_b(book, n, m, h, r, s, c2o(book, Laws.rep.exactly(m, r), s, True{}, hs)))

def am_elim_c(+book: Bk, +n: Nat, +r: Re, +s: String, hs: {chk(book, Laws.rep.at_most(n, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(m, n) == True{} : Bool} & {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  hi_elim_c.go(book, n, r, s, am_elim_b(book, n, r, s, c2o(book, Laws.rep.at_most(n, r), s, True{}, hs)))

def rep_intro_c(+book: Bk, +a: Nat, +b: Nat, +m: Nat, ha: {Nat.is_le(a, m) == True{} : Bool}, hb: {Nat.is_le(m, b) == True{} : Bool},
  +r: Re, +s: String, hs: {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}) -> {chk(book, Laws.rep(a, b, r), s) == True{} : Bool}:
  o2c(book, Laws.rep(a, b, r), s, True{}, rep_intro_b(book, a, b, m, ha, hb, r, s, c2o(book, Laws.rep.exactly(m, r), s, True{}, hs)))

def rep_elim_c(+book: Bk, +a: Nat, +b: Nat, +r: Re, +s: String, hs: {chk(book, Laws.rep(a, b, r), s) == True{} : Bool})
  -> &m: Nat -> {Nat.is_le(a, m) == True{} : Bool} & {Nat.is_le(m, b) == True{} : Bool} & {chk(book, Laws.rep.exactly(m, r), s) == True{} : Bool}:
  in_elim_c.go(book, a, b, r, s, rep_elim_b(book, a, b, r, s, c2o(book, Laws.rep(a, b, r), s, True{}, hs)))

def Laws.full.intro(d, g, r, s, h):
  full_intro_c(d, conv(g), r, s, h)

def Laws.full.elim(g, r, s, h):
  full_elim_c(conv(g), r, s, h)

def Laws.lookup.nil(book, name, s):
  none_c(book, s)

def Laws.lookup.con(book, k, r, g, name, s):
  lookup_con_c(book, k, r, conv(g), String.to_lower(name), s)

def Laws.ref.zero(g, name, s):
  none_false(s)

def Laws.ref.succ(d, g, name, s):
  ref_succ_b(d, conv(g), String.to_lower(name), s)

def Laws.empty.nil(book):
  o2c(book, REps{}, SNil{}, True{}, {==})

def Laws.empty.con(book, a, t):
  eps_con_c(book, a, t)

def Laws.char.nil(book, c):
  o2c(book, RChr{c}, SNil{}, False{}, {==})

def Laws.char.one(book, c, x):
  char_one_c(book, c, x)

def Laws.char.many(book, c, a, b, t):
  char_many_c(book, c, a, b, t)

def Laws.seq.nil(book, s):
  {==}

def Laws.seq.con.intro(book, r, rs, s1, s2, h1, h2):
  seq_intro_c(book, r, Laws.seq(rs), s1, s2, h1, h2)

def Laws.seq.con.elim(book, r, rs, s, h):
  seq_elim_c(book, r, Laws.seq(rs), s, h)

def Laws.alt.nil(book, s):
  none_c(book, s)

def Laws.alt.con(book, r, rs, s):
  alt_con_c(book, r, Laws.alt(rs), s)

def Laws.chars.nil(c):
  {==}

def Laws.chars.con(n, c):
  {==}

def Laws.range.ok(book, start, end, s):
  range_ok_c(book, start, end, s)

def Laws.string.case_sensitive.nil(book, s):
  {==}

def Laws.string.case_sensitive.con(book, c, t, s):
  {==}

def Laws.string.case_insensitive.nil(book, s):
  {==}

def Laws.string.case_insensitive.con(book, c, t, s):
  {==}

def Laws.rep.exactly.zero(book, r, s):
  {==}

def Laws.rep.exactly.succ(book, n, r, s):
  {==}

def Laws.rep.any.intro(book, m, r, s, hs):
  any_intro_c(book, m, r, s, hs)

def Laws.rep.any.elim(book, r, s, hs):
  any_elim_c(book, r, s, hs)

def Laws.rep.at_least.intro(book, n, m, h, r, s, hs):
  al_intro_c(book, n, m, h, r, s, hs)

def Laws.rep.at_least.elim(book, n, r, s, hs):
  al_elim_c(book, n, r, s, hs)

def Laws.rep.at_most.intro(book, n, m, h, r, s, hs):
  am_intro_c(book, n, m, h, r, s, hs)

def Laws.rep.at_most.elim(book, n, r, s, hs):
  am_elim_c(book, n, r, s, hs)

def Laws.rep.intro(book, a, b, m, ha, hb, r, s, hs):
  rep_intro_c(book, a, b, m, ha, hb, r, s, hs)

def Laws.rep.elim(book, a, b, r, s, hs):
  rep_elim_c(book, a, b, r, s, hs)

def Laws.opt.ok(book, r, s):
  {==}

def Laws.core.alpha.ok(book, s):
  {==}

def Laws.core.bit.ok(book, s):
  {==}

def Laws.core.char.ok(book, s):
  {==}

def Laws.core.cr.ok(book, s):
  {==}

def Laws.core.crlf.ok(book, s):
  {==}

def Laws.core.ctl.ok(book, s):
  {==}

def Laws.core.digit.ok(book, s):
  {==}

def Laws.core.dquote.ok(book, s):
  {==}

def Laws.core.hexdig.ok(book, s):
  {==}

def Laws.core.htab.ok(book, s):
  {==}

def Laws.core.lf.ok(book, s):
  {==}

def Laws.core.lwsp.ok(book, s):
  {==}

def Laws.core.octet.ok(book, s):
  {==}

def Laws.core.sp.ok(book, s):
  {==}

def Laws.core.vchar.ok(book, s):
  {==}

def Laws.core.wsp.ok(book, s):
  {==}
