# ABNF, as specified by RFC 5234.
#
# Where the RFC is silent:
# - A string matches a rule only through a finite derivation (`full`, `limit`).
# - A name with no definition matches nothing.
# - A name defined more than once matches any of its definitions, as with `=/`.
# - A backwards range, or a repetition with minimum above maximum, matches nothing.
#
# Differences from the RFC:
# - Rule names may be any string, string literals may contain any character,
#   and `alt([])` is allowed. ABNF's syntax can't write these.
# - Terminal values are `Char`s, so they stop at 2^32-1.

import Base

law Rule:
  Data

# A book says what references mean: a grammar, and how deep they may unfold.
# limit(d, g) lets each path of a derivation pass through at most d references
# (ref.zero, ref.succ). For `as = "" / "a" as`, limit(1n) matches only "",
# limit(2n) also "a", and so on. full(g) is the grammar itself: a string
# matches when it matches at some depth (full.intro, full.elim). So every match
# is a finite derivation, and `a = a` matches nothing.
#
# Laws with "some x exists" come in intro/elim pairs: intro builds a match from
# a given x, and elim takes a match apart into some x. A plain equation that
# refers back to itself can't replace them. Take the grammar `a = a` and the law
#   check(full(g), ref("a"), s) == check(full(g), lookup(g, "a"), s)
# lookup(g, "a") matches what ref("a") matches, so the law reduces to
#   check(full(g), ref("a"), s) == check(full(g), ref("a"), s)
# which holds whether the answer is True or False: a check that says `a`
# matches every string satisfies it. elim closes this: a True must come with a
# depth d, and `a` matches nothing at any depth. rep.any is the same: with
# `*x = "" / x *x` and x matching "", "b" reduces to *x matching "b" again, so
# rep.any.elim asks for a number of repetitions instead.

law Book:
  Data

law check:
  for book: Book
  for r: Rule
  for s: String
  Bool

law limit:
  for d: Nat
  for g: List<(String & Rule)>
  Book

law full:
  for g: List<(String & Rule)>
  Book

law full.intro:
  for d: Nat
  for g: List<(String & Rule)>
  for r: Rule
  for s: String
  for h: {check(limit(d, g), r, s) == True{} : Bool}
  {check(full(g), r, s) == True{} : Bool}

law full.elim:
  for g: List<(String & Rule)>
  for r: Rule
  for s: String
  for h: {check(full(g), r, s) == True{} : Bool}
  exs d: Nat
  {check(limit(d, g), r, s) == True{} : Bool}

law lookup:
  for g: List<(String & Rule)>
  for name: String
  Rule

law lookup.nil:
  for book: Book
  for name: String
  for s: String
  {check(book, lookup([], name), s) == False{} : Bool}

law lookup.con:
  for book: Book
  for k: String
  for r: Rule
  for g: List<(String & Rule)>
  for name: String
  for s: String
  {check(book, lookup((k, r) <> g, name), s) == (String.eq(String.to_lower(k), String.to_lower(name)) && check(book, r, s)) || check(book, lookup(g, name), s) : Bool}

law ref:
  for name: String
  Rule

law ref.zero:
  for g: List<(String & Rule)>
  for name: String
  for s: String
  {check(limit(0n, g), ref(name), s) == False{} : Bool}

law ref.succ:
  for d: Nat
  for g: List<(String & Rule)>
  for name: String
  for s: String
  {check(limit(1n+d, g), ref(name), s) == check(limit(d, g), lookup(g, name), s) : Bool}

law matches:
  for g: List<(String & Rule)>
  for name: String
  for s: String
  Bool

law matches.ok:
  for g: List<(String & Rule)>
  for name: String
  for s: String
  {matches(g, name, s) == check(full(g), ref(name), s) : Bool}

law empty:
  Rule

law empty.nil:
  for book: Book
  {check(book, empty, SNil{}) == True{} : Bool}

law empty.con:
  for book: Book
  for a: Char
  for t: String
  {check(book, empty, SCon{a, t}) == False{} : Bool}

law char:
  for c: Char
  Rule

law char.nil:
  for book: Book
  for c: Char
  {check(book, char(c), SNil{}) == False{} : Bool}

law char.one:
  for book: Book
  for c: Char
  for x: Char
  {check(book, char(c), SCon{x, SNil{}}) == Char.is_eq(c, x) : Bool}

law char.many:
  for book: Book
  for c: Char
  for a: Char
  for b: Char
  for t: String
  {check(book, char(c), SCon{a, SCon{b, t}}) == False{} : Bool}

law seq:
  for rs: List<Rule>
  Rule

law seq.nil:
  for book: Book
  for s: String
  {check(book, seq([]), s) == check(book, empty, s) : Bool}

law seq.con.intro:
  for book: Book
  for r: Rule
  for rs: List<Rule>
  for s1: String
  for s2: String
  for h1: {check(book, r, s1) == True{} : Bool}
  for h2: {check(book, seq(rs), s2) == True{} : Bool}
  {check(book, seq(r <> rs), s1 ++ s2) == True{} : Bool}

law seq.con.elim:
  for book: Book
  for r: Rule
  for rs: List<Rule>
  for s: String
  for h: {check(book, seq(r <> rs), s) == True{} : Bool}
  exs s1: String
  exs s2: String
  {s1 ++ s2 == s : String} & {check(book, r, s1) == True{} : Bool} & {check(book, seq(rs), s2) == True{} : Bool}

law alt:
  for rs: List<Rule>
  Rule

law alt.nil:
  for book: Book
  for s: String
  {check(book, alt([]), s) == False{} : Bool}

law alt.con:
  for book: Book
  for r: Rule
  for rs: List<Rule>
  for s: String
  {check(book, alt(r <> rs), s) == check(book, r, s) || check(book, alt(rs), s) : Bool}

law chars:
  for n: Nat
  for c: Char
  List<Rule>

law chars.nil:
  for c: Char
  {chars(0n, c) == [] : List<Rule>}

law chars.con:
  for n: Nat
  for c: Char
  {chars(1n+n, c) == char(c) <> chars(n, Chr{(Char.to_u32(c) + 1 : U32)}) : List<Rule>}

law range:
  for start: Char
  for end: Char
  Rule

law range.ok:
  for book: Book
  for start: Char
  for end: Char
  for s: String
  {check(book, range(start, end), s) == check(book, alt(chars(Nat.sub(1n+U32.to_nat(Char.to_u32(end)), U32.to_nat(Char.to_u32(start))), start)), s) : Bool}

law string.case_sensitive:
  for lit: String
  Rule

law string.case_sensitive.nil:
  for book: Book
  for s: String
  {check(book, string.case_sensitive(SNil{}), s) == check(book, empty, s) : Bool}

law string.case_sensitive.con:
  for book: Book
  for c: Char
  for t: String
  for s: String
  {check(book, string.case_sensitive(SCon{c, t}), s) == check(book, seq([char(c), string.case_sensitive(t)]), s) : Bool}

law string.case_insensitive:
  for lit: String
  Rule

law string.case_insensitive.nil:
  for book: Book
  for s: String
  {check(book, string.case_insensitive(SNil{}), s) == check(book, empty, s) : Bool}

law string.case_insensitive.con:
  for book: Book
  for c: Char
  for t: String
  for s: String
  {check(book, string.case_insensitive(SCon{c, t}), s) == check(book, seq([alt([char(Char.to_lower(c)), char(Char.to_upper(c))]), string.case_insensitive(t)]), s) : Bool}

law rep.exactly:
  for n: Nat
  for r: Rule
  Rule

law rep.exactly.zero:
  for book: Book
  for r: Rule
  for s: String
  {check(book, rep.exactly(0n, r), s) == check(book, empty, s) : Bool}

law rep.exactly.succ:
  for book: Book
  for n: Nat
  for r: Rule
  for s: String
  {check(book, rep.exactly(1n+n, r), s) == check(book, seq([r, rep.exactly(n, r)]), s) : Bool}

law rep.any:
  for r: Rule
  Rule

law rep.any.intro:
  for book: Book
  for m: Nat
  for r: Rule
  for s: String
  for hs: {check(book, rep.exactly(m, r), s) == True{} : Bool}
  {check(book, rep.any(r), s) == True{} : Bool}

law rep.any.elim:
  for book: Book
  for r: Rule
  for s: String
  for hs: {check(book, rep.any(r), s) == True{} : Bool}
  exs m: Nat
  {check(book, rep.exactly(m, r), s) == True{} : Bool}

law rep.at_least:
  for n: Nat
  for r: Rule
  Rule

law rep.at_least.intro:
  for book: Book
  for n: Nat
  for m: Nat
  for h: {(n <= m : Nat) == True{} : Bool}
  for r: Rule
  for s: String
  for hs: {check(book, rep.exactly(m, r), s) == True{} : Bool}
  {check(book, rep.at_least(n, r), s) == True{} : Bool}

law rep.at_least.elim:
  for book: Book
  for n: Nat
  for r: Rule
  for s: String
  for hs: {check(book, rep.at_least(n, r), s) == True{} : Bool}
  exs m: Nat
  {(n <= m : Nat) == True{} : Bool} & {check(book, rep.exactly(m, r), s) == True{} : Bool}

law rep.at_most:
  for n: Nat
  for r: Rule
  Rule

law rep.at_most.intro:
  for book: Book
  for n: Nat
  for m: Nat
  for h: {(m <= n : Nat) == True{} : Bool}
  for r: Rule
  for s: String
  for hs: {check(book, rep.exactly(m, r), s) == True{} : Bool}
  {check(book, rep.at_most(n, r), s) == True{} : Bool}

law rep.at_most.elim:
  for book: Book
  for n: Nat
  for r: Rule
  for s: String
  for hs: {check(book, rep.at_most(n, r), s) == True{} : Bool}
  exs m: Nat
  {(m <= n : Nat) == True{} : Bool} & {check(book, rep.exactly(m, r), s) == True{} : Bool}

law rep:
  for a: Nat
  for b: Nat
  for r: Rule
  Rule

law rep.intro:
  for book: Book
  for a: Nat
  for b: Nat
  for m: Nat
  for ha: {(a <= m : Nat) == True{} : Bool}
  for hb: {(m <= b : Nat) == True{} : Bool}
  for r: Rule
  for s: String
  for hs: {check(book, rep.exactly(m, r), s) == True{} : Bool}
  {check(book, rep(a, b, r), s) == True{} : Bool}

law rep.elim:
  for book: Book
  for a: Nat
  for b: Nat
  for r: Rule
  for s: String
  for hs: {check(book, rep(a, b, r), s) == True{} : Bool}
  exs m: Nat
  {(a <= m : Nat) == True{} : Bool} & {(m <= b : Nat) == True{} : Bool} & {check(book, rep.exactly(m, r), s) == True{} : Bool}

law opt:
  for r: Rule
  Rule

law opt.ok:
  for book: Book
  for r: Rule
  for s: String
  {check(book, opt(r), s) == check(book, alt([empty, r]), s) : Bool}

law core.alpha:
  Rule

law core.alpha.ok:
  for book: Book
  for s: String
  {check(book, core.alpha, s) == check(book, alt([range('A', 'Z'), range('a', 'z')]), s) : Bool}

law core.bit:
  Rule

law core.bit.ok:
  for book: Book
  for s: String
  {check(book, core.bit, s) == check(book, alt([string.case_insensitive("0"), string.case_insensitive("1")]), s) : Bool}

law core.char:
  Rule

law core.char.ok:
  for book: Book
  for s: String
  {check(book, core.char, s) == check(book, range(Chr{1}, Chr{127}), s) : Bool}

law core.cr:
  Rule

law core.cr.ok:
  for book: Book
  for s: String
  {check(book, core.cr, s) == check(book, char('\r'), s) : Bool}

law core.crlf:
  Rule

law core.crlf.ok:
  for book: Book
  for s: String
  {check(book, core.crlf, s) == check(book, seq([core.cr, core.lf]), s) : Bool}

law core.ctl:
  Rule

law core.ctl.ok:
  for book: Book
  for s: String
  {check(book, core.ctl, s) == check(book, alt([range(Chr{0}, Chr{31}), char(Chr{127})]), s) : Bool}

law core.digit:
  Rule

law core.digit.ok:
  for book: Book
  for s: String
  {check(book, core.digit, s) == check(book, range('0', '9'), s) : Bool}

law core.dquote:
  Rule

law core.dquote.ok:
  for book: Book
  for s: String
  {check(book, core.dquote, s) == check(book, char('"'), s) : Bool}

law core.hexdig:
  Rule

law core.hexdig.ok:
  for book: Book
  for s: String
  {check(book, core.hexdig, s) == check(book, alt([core.digit, string.case_insensitive("A"), string.case_insensitive("B"), string.case_insensitive("C"), string.case_insensitive("D"), string.case_insensitive("E"), string.case_insensitive("F")]), s) : Bool}

law core.htab:
  Rule

law core.htab.ok:
  for book: Book
  for s: String
  {check(book, core.htab, s) == check(book, char('\t'), s) : Bool}

law core.lf:
  Rule

law core.lf.ok:
  for book: Book
  for s: String
  {check(book, core.lf, s) == check(book, char('\n'), s) : Bool}

law core.lwsp:
  Rule

law core.lwsp.ok:
  for book: Book
  for s: String
  {check(book, core.lwsp, s) == check(book, rep.any(alt([core.wsp, seq([core.crlf, core.wsp])])), s) : Bool}

law core.octet:
  Rule

law core.octet.ok:
  for book: Book
  for s: String
  {check(book, core.octet, s) == check(book, range(Chr{0}, Chr{255}), s) : Bool}

law core.sp:
  Rule

law core.sp.ok:
  for book: Book
  for s: String
  {check(book, core.sp, s) == check(book, char(' '), s) : Bool}

law core.vchar:
  Rule

law core.vchar.ok:
  for book: Book
  for s: String
  {check(book, core.vchar, s) == check(book, range('!', '~'), s) : Bool}

law core.wsp:
  Rule

law core.wsp.ok:
  for book: Book
  for s: String
  {check(book, core.wsp, s) == check(book, alt([core.sp, core.htab]), s) : Bool}
