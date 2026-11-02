# JSON, as specified by RFC 8259.
#
# A number is kept as the text it was written with, so no precision is lost.
# An object's members are kept in order, duplicate names included.
# Where the RFC is silent: an unpaired surrogate escape such as "\uD800" stands
# for that code point by itself (RFC 8259, section 8.2).

import Base
import ../abnf/LAWS.bend as ABNF
import ../base-extra/LAWS.bend as Extra

law grammar:
  List<(String & ABNF.Rule)>

law grammar.ok:
  for name: String
  for s: String
  {ABNF.matches(grammar, name, s) == ABNF.matches([
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
  ], name, s) : Bool}

law JSON:
  Data

law null:
  for j: JSON
  Maybe<Unit>

law bool:
  for j: JSON
  Maybe<Bool>

law number:
  for j: JSON
  Maybe<String>

law string:
  for j: JSON
  Maybe<String>

law array:
  for j: JSON
  Maybe<+List<JSON>>

law object:
  for j: JSON
  Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>

# field(j, key): the value of the first member of object j named key.
law field:
  for j: JSON
  for key: String
  Maybe<JSON>

law field.none:
  for j: JSON
  for key: String
  for h: {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}
  {field(j, key) == None{} : Maybe<JSON>}

law field.some:
  for j: JSON
  for key: String
  for ms: +List<Sigma<&2, &2, String, _ => JSON>>
  for h: {object(j) == Some{ms} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}
  {field(j, key) == lookup(ms, key) : Maybe<JSON>}

# lookup(ms, key): the value of the first member of ms named key.
law lookup:
  for ms: +List<Sigma<&2, &2, String, _ => JSON>>
  for key: String
  Maybe<JSON>

law lookup.nil:
  for key: String
  {lookup([], key) == None{} : Maybe<JSON>}

law lookup.hit:
  for key: String
  for v: JSON
  for rest: +List<Sigma<&2, &2, String, _ => JSON>>
  {lookup((key, v) <> rest, key) == Some{v} : Maybe<JSON>}

law lookup.miss:
  for k: String
  for v: JSON
  for rest: +List<Sigma<&2, &2, String, _ => JSON>>
  for key: String
  for h: {String.eq(k, key) == False{} : Bool}
  {lookup((k, v) <> rest, key) == lookup(rest, key) : Maybe<JSON>}

law load:
  for s: String
  Maybe<JSON>

law load.ok:
  for s: String
  {Maybe.is_some(&1, JSON, load(s)) == ABNF.matches(grammar, "JSON-text", s) : Bool}

law dump:
  for j: JSON
  String

law dump.ok:
  for j: JSON
  {load(dump(j)) == Some{j} : Maybe<JSON>}

law load.null:
  for w1: String
  for w2: String
  for w3: String
  for h1: {ABNF.matches(grammar, "ws", w1) == True{} : Bool}
  for h2: {ABNF.matches(grammar, "null", w2) == True{} : Bool}
  for h3: {ABNF.matches(grammar, "ws", w3) == True{} : Bool}
  for j: JSON
  for h: {load(w1 ++ w2 ++ w3) == Some{j} : Maybe<JSON>}
  {null(j) == Some{Unit{}} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == None{} : Maybe<+List<JSON>>}
  & {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.true:
  for w1: String
  for w2: String
  for w3: String
  for h1: {ABNF.matches(grammar, "ws", w1) == True{} : Bool}
  for h2: {ABNF.matches(grammar, "true", w2) == True{} : Bool}
  for h3: {ABNF.matches(grammar, "ws", w3) == True{} : Bool}
  for j: JSON
  for h: {load(w1 ++ w2 ++ w3) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == Some{True{}} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == None{} : Maybe<+List<JSON>>}
  & {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.false:
  for w1: String
  for w2: String
  for w3: String
  for h1: {ABNF.matches(grammar, "ws", w1) == True{} : Bool}
  for h2: {ABNF.matches(grammar, "false", w2) == True{} : Bool}
  for h3: {ABNF.matches(grammar, "ws", w3) == True{} : Bool}
  for j: JSON
  for h: {load(w1 ++ w2 ++ w3) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == Some{False{}} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == None{} : Maybe<+List<JSON>>}
  & {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.number:
  for w1: String
  for w2: String
  for w3: String
  for h1: {ABNF.matches(grammar, "ws", w1) == True{} : Bool}
  for h2: {ABNF.matches(grammar, "number", w2) == True{} : Bool}
  for h3: {ABNF.matches(grammar, "ws", w3) == True{} : Bool}
  for j: JSON
  for h: {load(w1 ++ w2 ++ w3) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == Some{w2} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == None{} : Maybe<+List<JSON>>}
  & {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.string:
  for w1: String
  for q1: String
  for x: String
  for q2: String
  for w3: String
  for h1: {ABNF.matches(grammar, "ws", w1) == True{} : Bool}
  for hq1: {ABNF.matches(grammar, "quotation-mark", q1) == True{} : Bool}
  for hq2: {ABNF.matches(grammar, "quotation-mark", q2) == True{} : Bool}
  for hx: {ABNF.matches(grammar, "string", q1 ++ x ++ q2) == True{} : Bool}
  for h3: {ABNF.matches(grammar, "ws", w3) == True{} : Bool}
  for j: JSON
  for h: {load(w1 ++ q1 ++ x ++ q2 ++ w3) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == Some{decode(x)} : Maybe<String>}
  & {array(j) == None{} : Maybe<+List<JSON>>}
  & {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.array.nil:
  for b: String
  for e: String
  for hb: {ABNF.matches(grammar, "begin-array", b) == True{} : Bool}
  for he: {ABNF.matches(grammar, "end-array", e) == True{} : Bool}
  for j: JSON
  for h: {load(b ++ e) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == Some{[]} : Maybe<+List<JSON>>}
  & {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.array.one:
  for b: String
  for v: String
  for e: String
  for hb: {ABNF.matches(grammar, "begin-array", b) == True{} : Bool}
  for hv: {ABNF.matches(grammar, "value", v) == True{} : Bool}
  for he: {ABNF.matches(grammar, "end-array", e) == True{} : Bool}
  for jv: JSON
  for hjv: {load(v) == Some{jv} : Maybe<JSON>}
  for j: JSON
  for h: {load(b ++ v ++ e) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == Some{[jv]} : Maybe<+List<JSON>>}
  & {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.array.con:
  for b: String
  for v: String
  for s: String
  for rest: String
  for hb: {ABNF.matches(grammar, "begin-array", b) == True{} : Bool}
  for hv: {ABNF.matches(grammar, "value", v) == True{} : Bool}
  for hs: {ABNF.matches(grammar, "value-separator", s) == True{} : Bool}
  for jv: JSON
  for hjv: {load(v) == Some{jv} : Maybe<JSON>}
  for jr: JSON
  for hjr: {load(b ++ rest) == Some{jr} : Maybe<JSON>}
  for l: +List<JSON>
  for hl: {array(jr) == Some{l} : Maybe<+List<JSON>>}
  for j: JSON
  for h: {load(b ++ v ++ s ++ rest) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == Some{jv <> l} : Maybe<+List<JSON>>}
  & {object(j) == None{} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.object.nil:
  for b: String
  for e: String
  for hb: {ABNF.matches(grammar, "begin-object", b) == True{} : Bool}
  for he: {ABNF.matches(grammar, "end-object", e) == True{} : Bool}
  for j: JSON
  for h: {load(b ++ e) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == None{} : Maybe<+List<JSON>>}
  & {object(j) == Some{[]} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.object.one:
  for b: String
  for k: String
  for n: String
  for v: String
  for e: String
  for hb: {ABNF.matches(grammar, "begin-object", b) == True{} : Bool}
  for hk: {ABNF.matches(grammar, "string", k) == True{} : Bool}
  for hn: {ABNF.matches(grammar, "name-separator", n) == True{} : Bool}
  for hv: {ABNF.matches(grammar, "value", v) == True{} : Bool}
  for he: {ABNF.matches(grammar, "end-object", e) == True{} : Bool}
  for jk: JSON
  for hjk: {load(k) == Some{jk} : Maybe<JSON>}
  for name: String
  for hname: {string(jk) == Some{name} : Maybe<String>}
  for jv: JSON
  for hjv: {load(v) == Some{jv} : Maybe<JSON>}
  for j: JSON
  for h: {load(b ++ k ++ n ++ v ++ e) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == None{} : Maybe<+List<JSON>>}
  & {object(j) == Some{[(name, jv)]} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law load.object.con:
  for b: String
  for k: String
  for n: String
  for v: String
  for s: String
  for rest: String
  for hb: {ABNF.matches(grammar, "begin-object", b) == True{} : Bool}
  for hk: {ABNF.matches(grammar, "string", k) == True{} : Bool}
  for hn: {ABNF.matches(grammar, "name-separator", n) == True{} : Bool}
  for hv: {ABNF.matches(grammar, "value", v) == True{} : Bool}
  for hs: {ABNF.matches(grammar, "value-separator", s) == True{} : Bool}
  for jk: JSON
  for hjk: {load(k) == Some{jk} : Maybe<JSON>}
  for name: String
  for hname: {string(jk) == Some{name} : Maybe<String>}
  for jv: JSON
  for hjv: {load(v) == Some{jv} : Maybe<JSON>}
  for jr: JSON
  for hjr: {load(b ++ rest) == Some{jr} : Maybe<JSON>}
  for l: +List<Sigma<&2, &2, String, _ => JSON>>
  for hl: {object(jr) == Some{l} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}
  for j: JSON
  for h: {load(b ++ k ++ n ++ v ++ s ++ rest) == Some{j} : Maybe<JSON>}
  {null(j) == None{} : Maybe<Unit>}
  & {bool(j) == None{} : Maybe<Bool>}
  & {number(j) == None{} : Maybe<String>}
  & {string(j) == None{} : Maybe<String>}
  & {array(j) == None{} : Maybe<+List<JSON>>}
  & {object(j) == Some{(name, jv) <> l} : Maybe<+List<Sigma<&2, &2, String, _ => JSON>>>}

law decode:
  for x: String
  String

law decode.nil:
  {decode("") == "" : String}

law decode.unescaped:
  for u: String
  for t: String
  for h: {ABNF.matches(grammar, "unescaped", u) == True{} : Bool}
  {decode(u ++ t) == u ++ decode(t) : String}

law decode.quotation_mark:
  for e: String
  for q: String
  for t: String
  for he: {ABNF.matches(grammar, "escape", e) == True{} : Bool}
  for hq: {ABNF.matches(grammar, "quotation-mark", q) == True{} : Bool}
  {decode(e ++ q ++ t) == q ++ decode(t) : String}

law decode.escape:
  for e: String
  for t: String
  for he: {ABNF.matches(grammar, "escape", e) == True{} : Bool}
  {decode(e ++ e ++ t) == e ++ decode(t) : String}
  & {decode(e ++ "/" ++ t) == "/" ++ decode(t) : String}
  & {decode(e ++ "b" ++ t) == SCon{Chr{8}, decode(t)} : String}
  & {decode(e ++ "f" ++ t) == SCon{Chr{12}, decode(t)} : String}
  & {decode(e ++ "n" ++ t) == SCon{Chr{10}, decode(t)} : String}
  & {decode(e ++ "r" ++ t) == SCon{Chr{13}, decode(t)} : String}
  & {decode(e ++ "t" ++ t) == SCon{Chr{9}, decode(t)} : String}

# \uXXXX that is not a high surrogate U+D800 to U+DBFF.
law decode.u:
  for e: String
  for x: String
  for t: String
  for he: {ABNF.matches(grammar, "escape", e) == True{} : Bool}
  for hx: {Extra.is_hex(x) == True{} : Bool}
  for lx: {String.length(x) == 4n : Nat}
  for hs: {(Extra.hex(x, hx) < 55296 : U32) || (Extra.hex(x, hx) > 56319 : U32) == True{} : Bool}
  {decode(e ++ "u" ++ x ++ t) == SCon{Chr{Extra.hex(x, hx)}, decode(t)} : String}

# A surrogate pair \uD800-\uDBFF \uDC00-\uDFFF stands for one character above U+FFFF.
law decode.pair:
  for e: String
  for x1: String
  for x2: String
  for t: String
  for he: {ABNF.matches(grammar, "escape", e) == True{} : Bool}
  for hx1: {Extra.is_hex(x1) == True{} : Bool}
  for lx1: {String.length(x1) == 4n : Nat}
  for hx2: {Extra.is_hex(x2) == True{} : Bool}
  for lx2: {String.length(x2) == 4n : Nat}
  for hs1: {(Extra.hex(x1, hx1) >= 55296 : U32) && (Extra.hex(x1, hx1) <= 56319 : U32) == True{} : Bool}
  for hs2: {(Extra.hex(x2, hx2) >= 56320 : U32) && (Extra.hex(x2, hx2) <= 57343 : U32) == True{} : Bool}
  {decode(e ++ "u" ++ x1 ++ e ++ "u" ++ x2 ++ t) == SCon{Chr{(65536 + (Extra.hex(x1, hx1) - 55296) * 1024 + (Extra.hex(x2, hx2) - 56320) : U32)}, decode(t)} : String}

# A high surrogate without a low one after it stands for itself.
law decode.high:
  for e: String
  for x: String
  for t: String
  for he: {ABNF.matches(grammar, "escape", e) == True{} : Bool}
  for hx: {Extra.is_hex(x) == True{} : Bool}
  for lx: {String.length(x) == 4n : Nat}
  for hs: {(Extra.hex(x, hx) >= 55296 : U32) && (Extra.hex(x, hx) <= 56319 : U32) == True{} : Bool}
  for ht: {String.starts_with(t, e ++ "u") == False{} : Bool}
  {decode(e ++ "u" ++ x ++ t) == SCon{Chr{Extra.hex(x, hx)}, decode(t)} : String}

law decode.high_u:
  for e: String
  for x1: String
  for x2: String
  for t: String
  for he: {ABNF.matches(grammar, "escape", e) == True{} : Bool}
  for hx1: {Extra.is_hex(x1) == True{} : Bool}
  for lx1: {String.length(x1) == 4n : Nat}
  for hx2: {Extra.is_hex(x2) == True{} : Bool}
  for lx2: {String.length(x2) == 4n : Nat}
  for hs1: {(Extra.hex(x1, hx1) >= 55296 : U32) && (Extra.hex(x1, hx1) <= 56319 : U32) == True{} : Bool}
  for hs2: {(Extra.hex(x2, hx2) < 56320 : U32) || (Extra.hex(x2, hx2) > 57343 : U32) == True{} : Bool}
  {decode(e ++ "u" ++ x1 ++ e ++ "u" ++ x2 ++ t) == SCon{Chr{Extra.hex(x1, hx1)}, decode(e ++ "u" ++ x2 ++ t)} : String}
