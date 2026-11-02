# Utilities that Base doesn't have yet.

import Base

# is_hex(x): x is one or more hexadecimal digits, in either case.
law is_hex:
  for x: String
  Bool

law is_hex.ok:
  for x: String
  {is_hex(x) == Bool.not(String.is_empty(x)) && List.all(~&2, ~Char, ~(c => String.contains("0123456789abcdefABCDEF", SCon{c, SNil{}})), String.to_list(x)) : Bool}

# hex(x, h): the value of the hexadecimal digits x, modulo 2^32.
law hex:
  for x: String
  for h: {is_hex(x) == True{} : Bool}
  U32

law hex.one:
  for d: String
  for n: U32
  for hd: {String.length(d) == 1n : Nat}
  for hn: {String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n) == String.to_lower(d) : String}
  for h: {is_hex(d) == True{} : Bool}
  {hex(d, h) == n : U32}

law hex.snoc:
  for x: String
  for d: String
  for n: U32
  for hx: {is_hex(x) == True{} : Bool}
  for hd: {String.length(d) == 1n : Nat}
  for hn: {String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n) == String.to_lower(d) : String}
  for h: {is_hex(x ++ d) == True{} : Bool}
  {hex(x ++ d, h) == (hex(x, hx) * 16 + n : U32) : U32}
