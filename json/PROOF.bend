import Base
import ./LAWS.bend as Laws
import ../abnf/LAWS.bend as ABNF
import ../abnf/PROOF.bend as ABNFProof

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

def Laws.grammar.ok():
  {==}

def Laws.check(s):
  ABNF.check(ABNF.full(Laws.grammar), ABNF.ref("JSON-text"), s)

def Laws.check.ok(s):
  {==}
