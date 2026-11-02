import Base
import ./LAWS.bend as Laws

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

def sel(-A: Type, b: Bool, x: Unit -> A, y: Unit -> A) -> A:
  match b:
    case True{}:
      x(Unit{})
    case False{}:
      y(Unit{})

# Numbers
# =======

def ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def zero_ne_succ(-p: Nat, e: {0n == 1n+p : Nat}) -> Empty:
  %e : ndisc(_)
  Unit{}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, e)

def succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def dbl_inj(a: Nat, b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, zero_ne_succ(1n+Nat.double(q), e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, zero_ne_succ(1n+Nat.double(p), Equal.sym(Nat, Nat.double(1n+p), 0n, e)))
    case 1n+p 1n+q:
      succ_cong(p, q, dbl_inj(p, q, succ_inj(Nat.double(p), Nat.double(q), succ_inj(1n+Nat.double(p), 1n+Nat.double(q), e))))

def odd_ne_dbl(a: Nat, b: Nat, e: {1n+Nat.double(a) == Nat.double(b) : Nat}) -> Empty:
  match a b:
    case 0n 0n:
      zero_ne_succ(0n, Equal.sym(Nat, 1n, 0n, e))
    case 0n 1n+q:
      zero_ne_succ(Nat.double(q), succ_inj(0n, 1n+Nat.double(q), e))
    case 1n+p 0n:
      zero_ne_succ(1n+1n+Nat.double(p), Equal.sym(Nat, 1n+1n+1n+Nat.double(p), 0n, e))
    case 1n+p 1n+q:
      odd_ne_dbl(p, q, succ_inj(1n+Nat.double(p), Nat.double(q), succ_inj(1n+1n+Nat.double(p), 1n+Nat.double(q), e)))

def wcon_eq(-p: Nat, -a: Bool, -at: Word(p), -bt: Word(p), e: {at == bt : Word(p)}) -> {WCon{a, at} == WCon{a, bt} : Word(1n+p)}:
  %e : {WCon{a, at} == WCon{a, _} : Word(1n+p)}
  {==}

# A word is determined by the number it reads as.
def word_inj(n: Nat, a: Word(n), b: Word(n), e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          wcon_eq(p, False{}, at, bt, word_inj(p, at, bt, dbl_inj(Word.to_nat(p, at), Word.to_nat(p, bt), e)))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)},
            odd_ne_dbl(Word.to_nat(p, bt), Word.to_nat(p, at), Equal.sym(Nat, Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt)), e)))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)},
            odd_ne_dbl(Word.to_nat(p, at), Word.to_nat(p, bt), e))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          wcon_eq(p, True{}, at, bt, word_inj(p, at, bt, dbl_inj(Word.to_nat(p, at), Word.to_nat(p, bt), succ_inj(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)), e))))

def u32_of_nat(a: U32, b: U32, e: {U32.to_nat(b) == U32.to_nat(a) : Nat}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %word_inj(32n, x, y, Equal.sym(Nat, Word.to_nat(32n, y), Word.to_nat(32n, x), e)) : {U32{x} == U32{_} : U32}
      {==}

def add_zero(p: Nat, a: Word(p)) -> {Word.adc(p, a, Word.zero(p), False{}, False{}) == a : Word(p)}:
  match p:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+q:
      match a:
        case WCon{False{}, +at}:
          %add_zero(q, at) : {WCon{False{}, Word.adc(q, at, Word.zero(q), False{}, False{})} == WCon{False{}, _} : Word(1n+q)}
          {==}
        case WCon{True{}, +at}:
          %add_zero(q, at) : {WCon{True{}, Word.adc(q, at, Word.zero(q), False{}, False{})} == WCon{True{}, _} : Word(1n+q)}
          {==}

def u32_zero_add(x: U32) -> {(0 + x : U32) == x : U32}:
  match x:
    case U32{+w}:
      %Word.add_comm(32n, w, Word.zero(32n)) : {U32{_} == U32{w} : U32}
      %Equal.sym(Word(32n), Word.adc(32n, w, Word.zero(32n), False{}, False{}), w, add_zero(32n, w)) : {U32{_} == U32{w} : U32}
      {==}

# Strings
# =======

def sdisc(s: String) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{c, t}:
      Empty

def nil_ne_con(-x: Char, e: {SNil{} == SCon{x, SNil{}} : String}) -> Empty:
  %e : sdisc(_)
  Unit{}

# Hexadecimal digits
# ==================

def TABLE() -> String:
  "0123456789abcdef"

# idx(t, d, i): i plus the position of the one-character string d in t.
def idx(t: String, +d: String, +i: U32) -> U32:
  match t:
    case SNil{}:
      i
    case SCon{h, r}:
      sel(U32, String.eq(SCon{h, SNil{}}, d), u => i, u => idx(r, d, (i + 1 : U32)))

# dv(c): the value of the hexadecimal digit c.
def dv(c: Char) -> U32:
  idx(TABLE, String.to_lower(SCon{c, SNil{}}), 0)

def dv_k(k: Nat, n: U32, e: {U32.to_nat(n) == k : Nat}, -x: Char, hk: {String.take(String.drop(TABLE, k), 1n) == SCon{x, SNil{}} : String})
  -> {idx(TABLE, String.take(String.drop(TABLE, k), 1n), 0) == n : U32}:
  match k:
    case 0n:
      u32_of_nat(0, n, e)
    case 1n+k1:
      match k1:
        case 0n:
          u32_of_nat(1, n, e)
        case 1n+k2:
          match k2:
            case 0n:
              u32_of_nat(2, n, e)
            case 1n+k3:
              match k3:
                case 0n:
                  u32_of_nat(3, n, e)
                case 1n+k4:
                  match k4:
                    case 0n:
                      u32_of_nat(4, n, e)
                    case 1n+k5:
                      match k5:
                        case 0n:
                          u32_of_nat(5, n, e)
                        case 1n+k6:
                          match k6:
                            case 0n:
                              u32_of_nat(6, n, e)
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  u32_of_nat(7, n, e)
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      u32_of_nat(8, n, e)
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          u32_of_nat(9, n, e)
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              u32_of_nat(10, n, e)
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  u32_of_nat(11, n, e)
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      u32_of_nat(12, n, e)
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          u32_of_nat(13, n, e)
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              u32_of_nat(14, n, e)
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  u32_of_nat(15, n, e)
                                                                case 1n+k16:
                                                                  match k16:
                                                                    case 0n:
                                                                      Empty.absurd({idx(TABLE, String.take(String.drop(TABLE, k), 1n), 0) == n : U32}, nil_ne_con(x, hk))
                                                                    case 1n+q:
                                                                      Empty.absurd({idx(TABLE, String.take(String.drop(TABLE, k), 1n), 0) == n : U32}, nil_ne_con(x, hk))

def dv_ok(+c: Char, +n: U32, +hn: {String.take(String.drop(TABLE, U32.to_nat(n)), 1n) == String.to_lower(SCon{c, SNil{}}) : String}) -> {dv(c) == n : U32}:
  %hn : {idx(TABLE, _, 0) == n : U32}
  dv_k(U32.to_nat(n), n, {==}, Char.to_lower(c), hn)

def hexv(x: String, acc: U32) -> U32:
  match x:
    case SNil{}:
      acc
    case SCon{c, t}:
      hexv(t, (acc * 16 + dv(c) : U32))

def hexv_app(x: String, acc: U32, -y: String) -> {hexv(String.append(x, y), acc) == hexv(y, hexv(x, acc)) : U32}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      hexv_app(t, (acc * 16 + dv(c) : U32), y)

# Laws
# ====

def is_hex(+x: String) -> Bool:
  Bool.not(String.is_empty(x)) && List.all(~&2, ~Char, ~(c => String.contains("0123456789abcdefABCDEF", SCon{c, SNil{}})), String.to_list(x))

def Laws.is_hex(x):
  is_hex(x)

def Laws.is_hex.ok(x):
  {==}

def Laws.hex(x, h):
  hexv(x, 0)

def Laws.hex.one(d, n, hd, hn, h):
  match d:
    case SNil{}:
      Empty.absurd({hexv(SNil{}, 0) == n : U32}, zero_ne_succ(0n, hd))
    case SCon{+c, t}:
      match t:
        case SNil{}:
          %Equal.sym(U32, (0 + dv(c) : U32), dv(c), u32_zero_add(dv(c))) : {_ == n : U32}
          dv_ok(c, n, hn)
        case SCon{c2, t2}:
          Empty.absurd({hexv(SCon{c, SCon{c2, t2}}, 0) == n : U32}, zero_ne_succ(String.length(t2), Equal.sym(Nat, 1n+String.length(t2), 0n, succ_inj(1n+String.length(t2), 0n, hd))))

def Laws.hex.snoc(x, d, n, hx, hd, hn, h):
  match d:
    case SNil{}:
      Empty.absurd({hexv(String.append(x, SNil{}), 0) == (hexv(x, 0) * 16 + n : U32) : U32}, zero_ne_succ(0n, hd))
    case SCon{+c, t}:
      match t:
        case SNil{}:
          %Equal.sym(U32, hexv(String.append(x, SCon{c, SNil{}}), 0), hexv(SCon{c, SNil{}}, hexv(x, 0)), hexv_app(x, 0, SCon{c, SNil{}})) : {_ == (hexv(x, 0) * 16 + n : U32) : U32}
          %Equal.sym(U32, dv(c), n, dv_ok(c, n, hn)) : {(hexv(x, 0) * 16 + _ : U32) == (hexv(x, 0) * 16 + n : U32) : U32}
          {==}
        case SCon{c2, t2}:
          Empty.absurd({hexv(String.append(x, SCon{c, SCon{c2, t2}}), 0) == (hexv(x, 0) * 16 + n : U32) : U32}, zero_ne_succ(String.length(t2), Equal.sym(Nat, 1n+String.length(t2), 0n, succ_inj(1n+String.length(t2), 0n, hd))))
