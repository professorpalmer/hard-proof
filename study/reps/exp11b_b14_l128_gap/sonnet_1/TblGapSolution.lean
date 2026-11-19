import Tbl
import TblLaws

open Tbl

namespace TblGap

set_option maxRecDepth 100000 in
def base (d : Bool) (c : Case) : Bool :=
  if c.b10 = true ∧ c.b7 = false ∧ c.b5 = true ∧ c.b8 = true ∧ c.b13 = false ∧ c.b2 = true ∧ c.b0 = true ∧ c.b12 = false ∧ c.b9 = true ∧ c.b4 = true ∧ c.b6 = false ∧ c.b11 = false then false else
  if c.b2 = false ∧ c.b13 = false ∧ c.b11 = false ∧ c.b12 = true ∧ c.b4 = true ∧ c.b0 = false then false else
  if c.b3 = false ∧ c.b2 = false ∧ c.b8 = true ∧ c.b11 = true ∧ c.b4 = true ∧ c.b7 = false ∧ c.b12 = true ∧ c.b13 = false ∧ c.b0 = true ∧ c.b10 = false ∧ c.b9 = false ∧ c.b6 = false ∧ c.b5 = true then false else
  if c.b5 = true ∧ c.b3 = false ∧ c.b0 = true ∧ c.b11 = false ∧ c.b8 = false ∧ c.b13 = false ∧ c.b10 = false ∧ c.b6 = false ∧ c.b9 = false ∧ c.b7 = false then false else
  if c.b1 = true ∧ c.b11 = true ∧ c.b5 = true ∧ c.b9 = true ∧ c.b8 = true ∧ c.b4 = true ∧ c.b3 = false ∧ c.b2 = true ∧ c.b0 = true ∧ c.b13 = false ∧ c.b6 = false ∧ c.b7 = true ∧ c.b10 = false then false else
  if c.b9 = false ∧ c.b7 = false ∧ c.b11 = false ∧ c.b6 = false ∧ c.b13 = false ∧ c.b10 = false ∧ c.b3 = true ∧ c.b8 = false ∧ c.b0 = true then true else
  if c.b13 = false ∧ c.b2 = false ∧ c.b5 = false ∧ c.b1 = false ∧ c.b4 = false ∧ c.b8 = false ∧ c.b0 = true ∧ c.b7 = true ∧ c.b9 = true ∧ c.b12 = false ∧ c.b3 = true then false else
  if c.b0 = true ∧ c.b7 = true ∧ c.b5 = false ∧ c.b12 = false ∧ c.b9 = true ∧ c.b4 = false ∧ c.b11 = true ∧ c.b2 = true ∧ c.b3 = false ∧ c.b1 = false ∧ c.b13 = false then false else
  if c.b10 = true ∧ c.b6 = true ∧ c.b11 = false ∧ c.b2 = true ∧ c.b0 = true ∧ c.b4 = true ∧ c.b13 = false ∧ c.b9 = true ∧ c.b5 = true ∧ c.b8 = true then true else
  if c.b13 = false ∧ c.b5 = false ∧ c.b1 = true ∧ c.b2 = true ∧ c.b0 = false then true else
  if c.b9 = true ∧ c.b11 = true ∧ c.b0 = true ∧ c.b10 = true ∧ c.b5 = true ∧ c.b1 = true ∧ c.b4 = true ∧ c.b2 = true ∧ c.b13 = false ∧ c.b7 = false ∧ c.b8 = true then false else
  if c.b11 = false ∧ c.b5 = true ∧ c.b1 = false ∧ c.b13 = false ∧ c.b9 = true ∧ c.b4 = false ∧ c.b3 = false ∧ c.b7 = true ∧ c.b8 = false ∧ c.b0 = true ∧ c.b12 = false then false else
  if c.b0 = true ∧ c.b5 = false ∧ c.b13 = false ∧ c.b9 = true ∧ c.b12 = false ∧ c.b1 = false ∧ c.b4 = true then true else
  if c.b0 = true ∧ c.b6 = false ∧ c.b5 = true ∧ c.b2 = true ∧ c.b7 = false ∧ c.b12 = true ∧ c.b1 = true ∧ c.b9 = true ∧ c.b10 = true ∧ c.b3 = true ∧ c.b8 = true ∧ c.b13 = false ∧ c.b4 = true ∧ c.b11 = false then true else
  if c.b7 = true ∧ c.b11 = false ∧ c.b0 = true ∧ c.b5 = true ∧ c.b2 = true ∧ c.b4 = false ∧ c.b13 = false ∧ c.b12 = true ∧ c.b10 = true ∧ c.b9 = true ∧ c.b8 = true then true else
  if c.b10 = false ∧ c.b3 = false ∧ c.b6 = true ∧ c.b7 = false ∧ c.b9 = false ∧ c.b11 = true ∧ c.b0 = true ∧ c.b13 = false ∧ c.b12 = false then false else
  if c.b0 = true ∧ c.b12 = true ∧ c.b13 = false ∧ c.b4 = false ∧ c.b9 = true ∧ c.b5 = false then false else
  if c.b3 = false ∧ c.b8 = false ∧ c.b10 = false ∧ c.b7 = false ∧ c.b9 = false ∧ c.b1 = false ∧ c.b5 = false ∧ c.b6 = false ∧ c.b12 = false ∧ c.b2 = true ∧ c.b11 = true ∧ c.b4 = false ∧ c.b13 = false ∧ c.b0 = true then true else
  if c.b9 = false ∧ c.b11 = true ∧ c.b6 = false ∧ c.b3 = false ∧ c.b5 = false ∧ c.b13 = false ∧ c.b10 = false ∧ c.b4 = true ∧ c.b0 = true then false else
  if c.b11 = true ∧ c.b13 = false ∧ c.b3 = false ∧ c.b0 = true ∧ c.b6 = false ∧ c.b12 = false ∧ c.b2 = false ∧ c.b8 = true ∧ c.b7 = true ∧ c.b10 = false ∧ c.b1 = true ∧ c.b4 = false ∧ c.b5 = true ∧ c.b9 = false then false else
  if c.b5 = false ∧ c.b0 = false ∧ c.b4 = false ∧ c.b2 = false ∧ c.b13 = false ∧ c.b7 = true then false else
  if c.b7 = false ∧ c.b10 = true ∧ c.b6 = false ∧ c.b1 = false ∧ c.b5 = true ∧ c.b11 = false ∧ c.b3 = true ∧ c.b12 = true ∧ c.b4 = true ∧ c.b13 = false ∧ c.b9 = true ∧ c.b2 = true ∧ c.b0 = true ∧ c.b8 = true then false else
  if c.b4 = false ∧ c.b13 = false ∧ c.b10 = false ∧ c.b12 = false ∧ c.b6 = false ∧ c.b2 = false ∧ c.b0 = true ∧ c.b8 = true ∧ c.b7 = false ∧ c.b1 = false ∧ c.b3 = false ∧ c.b11 = true ∧ c.b9 = false ∧ c.b5 = false then false else
  if c.b3 = false ∧ c.b2 = true ∧ c.b7 = false ∧ c.b0 = true ∧ c.b1 = true ∧ c.b4 = false ∧ c.b10 = false ∧ c.b5 = false ∧ c.b13 = false ∧ c.b11 = true ∧ c.b12 = false ∧ c.b9 = false ∧ c.b6 = false then false else
  if c.b5 = false ∧ c.b12 = true ∧ c.b13 = false ∧ c.b4 = true ∧ c.b9 = true ∧ c.b11 = false ∧ c.b0 = true then true else
  if c.b9 = true ∧ c.b4 = false ∧ c.b11 = true ∧ c.b5 = true ∧ c.b3 = true ∧ c.b13 = false ∧ c.b8 = false ∧ c.b0 = true ∧ c.b1 = false then false else
  if c.b6 = false ∧ c.b13 = false ∧ c.b9 = false ∧ c.b3 = true ∧ c.b10 = false ∧ c.b7 = true ∧ c.b11 = false ∧ c.b8 = false ∧ c.b0 = true then true else
  if c.b1 = true ∧ c.b12 = false ∧ c.b0 = true ∧ c.b9 = true ∧ c.b5 = false ∧ c.b2 = false ∧ c.b13 = false then true else
  if c.b9 = false ∧ c.b11 = false ∧ c.b10 = false ∧ c.b0 = true ∧ c.b4 = true ∧ c.b13 = false ∧ c.b8 = false ∧ c.b6 = true then false else
  if c.b12 = false ∧ c.b5 = false ∧ c.b7 = true ∧ c.b0 = true ∧ c.b10 = false ∧ c.b6 = false ∧ c.b13 = false ∧ c.b11 = true ∧ c.b9 = false ∧ c.b4 = false ∧ c.b3 = false then true else
  if c.b9 = false ∧ c.b5 = true ∧ c.b11 = true ∧ c.b0 = true ∧ c.b10 = false ∧ c.b4 = false ∧ c.b3 = true ∧ c.b13 = false then false else
  if c.b7 = true ∧ c.b10 = false ∧ c.b9 = true ∧ c.b4 = true ∧ c.b8 = true ∧ c.b0 = true ∧ c.b3 = true ∧ c.b2 = true ∧ c.b5 = true ∧ c.b1 = true ∧ c.b13 = false ∧ c.b6 = false ∧ c.b11 = true then true else
  if c.b7 = true ∧ c.b10 = false ∧ c.b2 = false ∧ c.b8 = false ∧ c.b3 = false ∧ c.b1 = true ∧ c.b6 = false ∧ c.b0 = true ∧ c.b9 = false ∧ c.b11 = true ∧ c.b5 = true ∧ c.b4 = true ∧ c.b13 = false ∧ c.b12 = false then true else
  if c.b5 = true ∧ c.b10 = true ∧ c.b7 = false ∧ c.b1 = true ∧ c.b8 = true ∧ c.b0 = true ∧ c.b13 = false ∧ c.b9 = true ∧ c.b11 = true ∧ c.b4 = false ∧ c.b2 = true then true else
  if c.b4 = true ∧ c.b13 = false ∧ c.b6 = false ∧ c.b5 = true ∧ c.b11 = false ∧ c.b12 = true ∧ c.b1 = true ∧ c.b9 = true ∧ c.b8 = true ∧ c.b7 = true ∧ c.b3 = true ∧ c.b10 = true ∧ c.b2 = true ∧ c.b0 = true then false else
  if c.b13 = false ∧ c.b6 = false ∧ c.b10 = false ∧ c.b0 = true ∧ c.b3 = false ∧ c.b12 = false ∧ c.b5 = false ∧ c.b8 = false ∧ c.b9 = false ∧ c.b2 = false ∧ c.b7 = false ∧ c.b4 = false ∧ c.b1 = false ∧ c.b11 = true then false else
  if c.b8 = false ∧ c.b11 = false ∧ c.b13 = false ∧ c.b9 = false ∧ c.b10 = false ∧ c.b3 = false ∧ c.b7 = true ∧ c.b5 = true ∧ c.b0 = true ∧ c.b6 = false then true else
  if c.b12 = false ∧ c.b9 = true ∧ c.b0 = true ∧ c.b4 = false ∧ c.b7 = true ∧ c.b13 = false ∧ c.b11 = false ∧ c.b5 = true ∧ c.b6 = false ∧ c.b3 = true ∧ c.b8 = false ∧ c.b1 = false then true else
  if c.b8 = false ∧ c.b3 = false ∧ c.b9 = false ∧ c.b13 = false ∧ c.b5 = false ∧ c.b11 = false ∧ c.b0 = true ∧ c.b10 = false ∧ c.b6 = false then false else
  if c.b0 = true ∧ c.b10 = false ∧ c.b1 = false ∧ c.b12 = false ∧ c.b2 = true ∧ c.b7 = false ∧ c.b3 = false ∧ c.b13 = false ∧ c.b9 = true ∧ c.b5 = false ∧ c.b4 = false ∧ c.b8 = false then false else
  if c.b7 = true ∧ c.b11 = true ∧ c.b4 = false ∧ c.b9 = false ∧ c.b10 = false ∧ c.b3 = false ∧ c.b5 = true ∧ c.b1 = true ∧ c.b13 = false ∧ c.b0 = true ∧ c.b6 = false ∧ c.b2 = false ∧ c.b12 = true ∧ c.b8 = true then true else
  if c.b12 = true ∧ c.b13 = true ∧ c.b2 = true ∧ c.b10 = false ∧ c.b5 = false then true else
  if c.b7 = false ∧ c.b11 = true ∧ c.b3 = false ∧ c.b4 = true ∧ c.b9 = false ∧ c.b0 = true ∧ c.b6 = false ∧ c.b2 = false ∧ c.b5 = true ∧ c.b13 = false ∧ c.b10 = false ∧ c.b12 = false then true else
  if c.b9 = true ∧ c.b0 = true ∧ c.b3 = true ∧ c.b8 = false ∧ c.b11 = true ∧ c.b1 = true ∧ c.b4 = false ∧ c.b13 = false ∧ c.b5 = true then true else
  if c.b12 = false ∧ c.b13 = true ∧ c.b8 = false ∧ c.b5 = false then true else
  if c.b10 = false ∧ c.b9 = false ∧ c.b0 = true ∧ c.b11 = false ∧ c.b6 = true ∧ c.b13 = false ∧ c.b8 = true then true else
  if c.b0 = true ∧ c.b1 = true ∧ c.b9 = false ∧ c.b5 = false ∧ c.b2 = false ∧ c.b11 = true ∧ c.b10 = false ∧ c.b6 = false ∧ c.b3 = false ∧ c.b4 = false ∧ c.b13 = false ∧ c.b12 = false ∧ c.b7 = false then true else
  if c.b12 = false ∧ c.b9 = true ∧ c.b6 = false ∧ c.b7 = true ∧ c.b5 = true ∧ c.b3 = true ∧ c.b11 = false ∧ c.b10 = true ∧ c.b2 = true ∧ c.b0 = true ∧ c.b4 = false ∧ c.b13 = false ∧ c.b8 = true then true else
  if c.b11 = true ∧ c.b3 = false ∧ c.b0 = true ∧ c.b2 = false ∧ c.b1 = true ∧ c.b13 = false ∧ c.b7 = true ∧ c.b10 = false ∧ c.b8 = true ∧ c.b5 = true ∧ c.b4 = true ∧ c.b6 = false ∧ c.b12 = true ∧ c.b9 = false then true else
  if c.b13 = false ∧ c.b5 = false ∧ c.b9 = false ∧ c.b10 = false ∧ c.b11 = true ∧ c.b12 = true ∧ c.b6 = true ∧ c.b0 = true ∧ c.b3 = false ∧ c.b7 = false then false else
  if c.b7 = false ∧ c.b4 = true ∧ c.b8 = true ∧ c.b2 = true ∧ c.b5 = true ∧ c.b0 = true ∧ c.b1 = false ∧ c.b11 = true ∧ c.b9 = true ∧ c.b13 = false ∧ c.b10 = true then true else
  if c.b11 = false ∧ c.b7 = true ∧ c.b3 = false ∧ c.b0 = true ∧ c.b9 = true ∧ c.b12 = false ∧ c.b13 = false ∧ c.b2 = true ∧ c.b1 = false ∧ c.b5 = false ∧ c.b4 = false then true else
  if c.b12 = false ∧ c.b4 = false ∧ c.b13 = false ∧ c.b8 = true ∧ c.b2 = false ∧ c.b7 = true ∧ c.b5 = false ∧ c.b1 = false ∧ c.b3 = true ∧ c.b9 = true ∧ c.b0 = true then true else
  if c.b10 = true ∧ c.b5 = false ∧ c.b12 = true ∧ c.b13 = true then true else
  if c.b10 = true ∧ c.b8 = true ∧ c.b13 = false ∧ c.b3 = false ∧ c.b11 = false ∧ c.b2 = true ∧ c.b9 = true ∧ c.b5 = true ∧ c.b4 = true ∧ c.b12 = true ∧ c.b0 = true ∧ c.b6 = false ∧ c.b1 = true ∧ c.b7 = true then false else
  if c.b12 = false ∧ c.b5 = false ∧ c.b13 = true ∧ c.b8 = true then true else
  if c.b8 = true ∧ c.b4 = true ∧ c.b10 = false ∧ c.b13 = false ∧ c.b6 = false ∧ c.b11 = false ∧ c.b5 = true ∧ c.b9 = false ∧ c.b0 = true then true else
  if c.b12 = false ∧ c.b8 = true ∧ c.b9 = true ∧ c.b1 = false ∧ c.b10 = false ∧ c.b0 = true ∧ c.b2 = true ∧ c.b5 = false ∧ c.b4 = false ∧ c.b3 = false ∧ c.b13 = false ∧ c.b7 = false then true else
  if c.b5 = true ∧ c.b0 = true ∧ c.b3 = false ∧ c.b9 = false ∧ c.b4 = false ∧ c.b10 = false ∧ c.b13 = false ∧ c.b11 = true ∧ c.b2 = false ∧ c.b6 = false ∧ c.b7 = false then true else
  if c.b11 = true ∧ c.b6 = true ∧ c.b7 = false ∧ c.b3 = false ∧ c.b9 = false ∧ c.b0 = true ∧ c.b13 = false ∧ c.b12 = true ∧ c.b5 = true ∧ c.b10 = false then false else
  if c.b3 = true ∧ c.b13 = false ∧ c.b10 = true ∧ c.b0 = true ∧ c.b9 = false then false else
  if c.b11 = true ∧ c.b13 = false ∧ c.b8 = false ∧ c.b3 = false ∧ c.b1 = true ∧ c.b9 = true ∧ c.b4 = false ∧ c.b5 = true ∧ c.b0 = true then false else
  if c.b9 = false ∧ c.b1 = false ∧ c.b3 = false ∧ c.b7 = true ∧ c.b2 = false ∧ c.b5 = true ∧ c.b11 = true ∧ c.b10 = false ∧ c.b6 = false ∧ c.b0 = true ∧ c.b4 = true ∧ c.b13 = false then false else
  if c.b2 = false ∧ c.b5 = true ∧ c.b9 = true ∧ c.b0 = true ∧ c.b13 = false ∧ c.b8 = true then true else
  if c.b11 = true ∧ c.b8 = true ∧ c.b0 = true ∧ c.b2 = true ∧ c.b10 = false ∧ c.b13 = false ∧ c.b1 = false ∧ c.b7 = true ∧ c.b9 = true ∧ c.b5 = true then true else
  if c.b7 = true ∧ c.b1 = true ∧ c.b2 = true ∧ c.b11 = true ∧ c.b5 = true ∧ c.b6 = true ∧ c.b8 = true ∧ c.b13 = false ∧ c.b10 = false ∧ c.b9 = true ∧ c.b0 = true then true else
  if c.b6 = false ∧ c.b2 = false ∧ c.b10 = false ∧ c.b5 = true ∧ c.b4 = false ∧ c.b11 = true ∧ c.b0 = true ∧ c.b8 = false ∧ c.b1 = true ∧ c.b3 = false ∧ c.b13 = false ∧ c.b12 = true ∧ c.b7 = true ∧ c.b9 = false then true else
  if c.b8 = true ∧ c.b11 = true ∧ c.b9 = true ∧ c.b5 = true ∧ c.b7 = false ∧ c.b13 = false ∧ c.b3 = false ∧ c.b2 = true ∧ c.b6 = false ∧ c.b10 = false ∧ c.b0 = true then false else
  if c.b4 = true ∧ c.b2 = false ∧ c.b0 = false ∧ c.b13 = false ∧ c.b11 = false ∧ c.b12 = false then false else
  if c.b4 = false ∧ c.b7 = false ∧ c.b0 = false ∧ c.b2 = false ∧ c.b13 = false then false else
  if c.b7 = true ∧ c.b6 = false ∧ c.b10 = false ∧ c.b5 = true ∧ c.b8 = false ∧ c.b3 = false ∧ c.b2 = false ∧ c.b0 = true ∧ c.b1 = true ∧ c.b11 = true ∧ c.b13 = false ∧ c.b12 = false ∧ c.b4 = false ∧ c.b9 = false then false else
  if c.b0 = true ∧ c.b13 = false ∧ c.b10 = true ∧ c.b9 = false ∧ c.b3 = false ∧ c.b11 = true then true else
  if c.b13 = false ∧ c.b5 = false ∧ c.b2 = true ∧ c.b4 = false ∧ c.b9 = true ∧ c.b3 = true ∧ c.b12 = false ∧ c.b0 = true ∧ c.b1 = false then true else
  if c.b2 = false ∧ c.b8 = false ∧ c.b6 = false ∧ c.b7 = false ∧ c.b9 = false ∧ c.b10 = false ∧ c.b4 = true ∧ c.b3 = false ∧ c.b13 = false ∧ c.b11 = true ∧ c.b12 = true ∧ c.b5 = true ∧ c.b0 = true then true else
  if c.b0 = true ∧ c.b5 = true ∧ c.b7 = true ∧ c.b10 = true ∧ c.b11 = true ∧ c.b9 = true ∧ c.b13 = false ∧ c.b2 = true ∧ c.b8 = true then true else
  if c.b9 = true ∧ c.b13 = false ∧ c.b12 = false ∧ c.b8 = false ∧ c.b11 = false ∧ c.b0 = true ∧ c.b7 = true ∧ c.b5 = true ∧ c.b1 = true ∧ c.b4 = false then true else
  if c.b7 = false ∧ c.b10 = false ∧ c.b5 = false ∧ c.b9 = false ∧ c.b12 = false ∧ c.b2 = true ∧ c.b6 = false ∧ c.b3 = false ∧ c.b0 = true ∧ c.b11 = true ∧ c.b1 = false ∧ c.b8 = true ∧ c.b13 = false ∧ c.b4 = false then true else
  if c.b0 = true ∧ c.b3 = false ∧ c.b10 = false ∧ c.b7 = true ∧ c.b9 = false ∧ c.b13 = false ∧ c.b11 = true ∧ c.b6 = true then true else
  if c.b10 = false ∧ c.b8 = true ∧ c.b0 = true ∧ c.b3 = true ∧ c.b13 = false ∧ c.b9 = true ∧ c.b11 = false ∧ c.b2 = true ∧ c.b5 = true then true else
  if c.b3 = false ∧ c.b7 = false ∧ c.b10 = true ∧ c.b9 = true ∧ c.b0 = true ∧ c.b12 = false ∧ c.b13 = false ∧ c.b2 = true ∧ c.b5 = false ∧ c.b1 = false ∧ c.b4 = false then true else
  if c.b5 = true ∧ c.b4 = true ∧ c.b12 = false ∧ c.b0 = true ∧ c.b9 = true ∧ c.b13 = false ∧ c.b8 = false then true else
  if c.b11 = false ∧ c.b4 = false ∧ c.b10 = false ∧ c.b6 = true ∧ c.b0 = true ∧ c.b13 = false ∧ c.b8 = false ∧ c.b9 = false then false else
  if c.b2 = true ∧ c.b8 = true ∧ c.b3 = false ∧ c.b11 = false ∧ c.b13 = false ∧ c.b5 = true ∧ c.b9 = true ∧ c.b10 = false ∧ c.b0 = true then false else
  if c.b8 = true ∧ c.b5 = true ∧ c.b1 = false ∧ c.b12 = true ∧ c.b2 = true ∧ c.b11 = false ∧ c.b6 = false ∧ c.b7 = true ∧ c.b3 = true ∧ c.b9 = true ∧ c.b13 = false ∧ c.b10 = true ∧ c.b0 = true ∧ c.b4 = true then false else
  if c.b2 = false ∧ c.b9 = false ∧ c.b6 = false ∧ c.b5 = false ∧ c.b10 = false ∧ c.b11 = true ∧ c.b12 = true ∧ c.b4 = false ∧ c.b3 = false ∧ c.b13 = false ∧ c.b0 = true then false else
  if c.b11 = false ∧ c.b9 = false ∧ c.b13 = false ∧ c.b10 = true ∧ c.b3 = false ∧ c.b0 = true then false else
  if c.b11 = false ∧ c.b0 = true ∧ c.b4 = true ∧ c.b12 = false ∧ c.b13 = false ∧ c.b6 = false ∧ c.b5 = true ∧ c.b8 = true ∧ c.b7 = true ∧ c.b2 = true ∧ c.b10 = true ∧ c.b9 = true then false else
  if c.b9 = true ∧ c.b0 = true ∧ c.b2 = true ∧ c.b13 = false ∧ c.b1 = false ∧ c.b11 = true ∧ c.b5 = true ∧ c.b7 = false ∧ c.b10 = true ∧ c.b4 = false ∧ c.b8 = true then false else
  if c.b0 = true ∧ c.b1 = true ∧ c.b6 = false ∧ c.b11 = true ∧ c.b10 = false ∧ c.b7 = true ∧ c.b2 = true ∧ c.b8 = true ∧ c.b9 = true ∧ c.b5 = true ∧ c.b4 = false ∧ c.b13 = false then false else
  if c.b8 = true ∧ c.b4 = true ∧ c.b12 = true ∧ c.b6 = false ∧ c.b9 = true ∧ c.b5 = true ∧ c.b11 = false ∧ c.b1 = false ∧ c.b10 = true ∧ c.b13 = false ∧ c.b3 = false ∧ c.b0 = true ∧ c.b2 = true then false else
  if c.b3 = true ∧ c.b8 = true ∧ c.b2 = true ∧ c.b11 = true ∧ c.b10 = false ∧ c.b9 = true ∧ c.b0 = true ∧ c.b7 = false ∧ c.b5 = true ∧ c.b6 = false ∧ c.b13 = false then true else
  if c.b9 = true ∧ c.b7 = true ∧ c.b5 = false ∧ c.b3 = false ∧ c.b12 = false ∧ c.b13 = false ∧ c.b1 = false ∧ c.b0 = true ∧ c.b2 = false ∧ c.b4 = false then true else
  if c.b0 = true ∧ c.b10 = false ∧ c.b13 = false ∧ c.b9 = false ∧ c.b4 = false ∧ c.b6 = false ∧ c.b7 = true ∧ c.b8 = true ∧ c.b11 = false then false else
  if c.b9 = false ∧ c.b13 = false ∧ c.b10 = false ∧ c.b11 = true ∧ c.b5 = false ∧ c.b0 = true ∧ c.b3 = true then false else
  if c.b9 = false ∧ c.b6 = false ∧ c.b11 = true ∧ c.b5 = true ∧ c.b3 = false ∧ c.b2 = true ∧ c.b0 = true ∧ c.b13 = false ∧ c.b10 = false then true else
  if c.b10 = false ∧ c.b4 = false ∧ c.b13 = false ∧ c.b0 = true ∧ c.b7 = true ∧ c.b2 = false ∧ c.b1 = false ∧ c.b6 = false ∧ c.b9 = false ∧ c.b3 = false ∧ c.b5 = true ∧ c.b11 = true then true else
  if c.b9 = true ∧ c.b10 = true ∧ c.b5 = true ∧ c.b0 = true ∧ c.b2 = true ∧ c.b7 = false ∧ c.b8 = true ∧ c.b6 = false ∧ c.b4 = false ∧ c.b13 = false ∧ c.b11 = false then true else
  if c.b9 = true ∧ c.b13 = false ∧ c.b1 = false ∧ c.b11 = true ∧ c.b8 = false ∧ c.b3 = false ∧ c.b2 = true ∧ c.b0 = true ∧ c.b5 = true ∧ c.b4 = false then true else
  if c.b9 = true ∧ c.b12 = false ∧ c.b1 = false ∧ c.b3 = true ∧ c.b2 = false ∧ c.b0 = true ∧ c.b13 = false ∧ c.b7 = false ∧ c.b4 = false ∧ c.b5 = false then false else
  if c.b11 = false ∧ c.b5 = true ∧ c.b2 = true ∧ c.b0 = true ∧ c.b13 = false ∧ c.b4 = false ∧ c.b3 = false ∧ c.b7 = true ∧ c.b10 = true ∧ c.b9 = true ∧ c.b6 = false ∧ c.b12 = false ∧ c.b8 = true then false else
  if c.b5 = true ∧ c.b0 = true ∧ c.b3 = false ∧ c.b12 = true ∧ c.b6 = false ∧ c.b7 = false ∧ c.b2 = true ∧ c.b10 = true ∧ c.b4 = true ∧ c.b8 = true ∧ c.b9 = true ∧ c.b11 = false ∧ c.b1 = true ∧ c.b13 = false then true else
  if c.b1 = true ∧ c.b12 = true ∧ c.b0 = true ∧ c.b6 = false ∧ c.b9 = false ∧ c.b11 = true ∧ c.b8 = false ∧ c.b5 = true ∧ c.b10 = false ∧ c.b4 = true ∧ c.b3 = false ∧ c.b13 = false ∧ c.b2 = false ∧ c.b7 = true then false else
  if c.b6 = false ∧ c.b1 = true ∧ c.b2 = true ∧ c.b13 = false ∧ c.b0 = false ∧ c.b5 = true then true else
  if c.b5 = true ∧ c.b4 = true ∧ c.b11 = true ∧ c.b10 = false ∧ c.b0 = true ∧ c.b3 = true ∧ c.b13 = false ∧ c.b9 = false then true else
  if c.b8 = false ∧ c.b7 = true ∧ c.b13 = false ∧ c.b1 = true ∧ c.b5 = true ∧ c.b12 = true ∧ c.b11 = false ∧ c.b4 = false ∧ c.b0 = true ∧ c.b9 = true then false else
  if c.b0 = false ∧ c.b13 = false ∧ c.b10 = true ∧ c.b1 = false ∧ c.b2 = true then true else
  if c.b10 = false ∧ c.b7 = false ∧ c.b4 = false ∧ c.b13 = false ∧ c.b9 = false ∧ c.b11 = false ∧ c.b6 = false ∧ c.b8 = true ∧ c.b0 = true then false else
  if c.b7 = false ∧ c.b5 = false ∧ c.b0 = true ∧ c.b13 = false ∧ c.b4 = false ∧ c.b2 = false ∧ c.b9 = true ∧ c.b12 = false ∧ c.b1 = false ∧ c.b3 = false then true else
  if c.b6 = false ∧ c.b13 = false ∧ c.b5 = false ∧ c.b12 = true ∧ c.b3 = false ∧ c.b11 = true ∧ c.b4 = false ∧ c.b2 = true ∧ c.b9 = false ∧ c.b0 = true ∧ c.b10 = false then false else
  if c.b10 = false ∧ c.b9 = true ∧ c.b2 = true ∧ c.b13 = false ∧ c.b1 = false ∧ c.b0 = false then false else
  if c.b3 = true ∧ c.b7 = true ∧ c.b8 = false ∧ c.b0 = true ∧ c.b9 = true ∧ c.b5 = true ∧ c.b1 = false ∧ c.b13 = false ∧ c.b4 = false ∧ c.b12 = false ∧ c.b11 = false ∧ c.b6 = true then false else
  if c.b9 = false ∧ c.b6 = false ∧ c.b4 = true ∧ c.b0 = true ∧ c.b8 = true ∧ c.b13 = false ∧ c.b5 = false ∧ c.b11 = false ∧ c.b10 = false then true else
  if c.b0 = true ∧ c.b11 = false ∧ c.b5 = true ∧ c.b8 = false ∧ c.b4 = false ∧ c.b1 = false ∧ c.b12 = true ∧ c.b7 = true ∧ c.b9 = true ∧ c.b13 = false then false else
  if c.b9 = true ∧ c.b13 = false ∧ c.b4 = true ∧ c.b5 = true ∧ c.b0 = true ∧ c.b12 = true ∧ c.b8 = false then false else
  if c.b0 = true ∧ c.b9 = true ∧ c.b6 = true ∧ c.b8 = true ∧ c.b5 = true ∧ c.b10 = false ∧ c.b11 = true ∧ c.b13 = false ∧ c.b7 = false ∧ c.b2 = true then true else
  if c.b13 = false ∧ c.b1 = true ∧ c.b0 = true ∧ c.b2 = true ∧ c.b5 = false ∧ c.b9 = true ∧ c.b12 = false then true else
  if c.b13 = false ∧ c.b2 = false ∧ c.b0 = false ∧ c.b11 = true ∧ c.b4 = true then false else
  if c.b5 = true ∧ c.b13 = true then true else
  if c.b13 = true ∧ c.b5 = false ∧ c.b2 = false ∧ c.b10 = false ∧ c.b12 = true then true else
  if c.b5 = true ∧ c.b4 = false ∧ c.b11 = false ∧ c.b0 = true ∧ c.b9 = true ∧ c.b8 = false ∧ c.b7 = false ∧ c.b13 = false then false else
  if c.b9 = true ∧ c.b1 = false ∧ c.b13 = false ∧ c.b3 = false ∧ c.b8 = false ∧ c.b11 = true ∧ c.b2 = false ∧ c.b0 = true ∧ c.b5 = true ∧ c.b4 = false then true else
  if c.b1 = true ∧ c.b2 = true ∧ c.b6 = true ∧ c.b5 = true ∧ c.b0 = false ∧ c.b13 = false then true else
  if c.b9 = false ∧ c.b2 = true ∧ c.b13 = false ∧ c.b10 = false ∧ c.b0 = false ∧ c.b1 = false then true else
  if c.b6 = true ∧ c.b2 = true ∧ c.b0 = true ∧ c.b9 = true ∧ c.b8 = true ∧ c.b5 = true ∧ c.b4 = false ∧ c.b11 = false ∧ c.b7 = false ∧ c.b10 = true ∧ c.b13 = false then false else
  if c.b7 = true ∧ c.b0 = true ∧ c.b9 = false ∧ c.b10 = false ∧ c.b11 = true ∧ c.b1 = true ∧ c.b6 = false ∧ c.b2 = false ∧ c.b5 = true ∧ c.b3 = false ∧ c.b8 = true ∧ c.b4 = true ∧ c.b12 = false ∧ c.b13 = false then true else
  if c.b5 = true ∧ c.b13 = false ∧ c.b0 = false ∧ c.b7 = true ∧ c.b2 = false ∧ c.b4 = false then false else
  if c.b5 = false ∧ c.b13 = false ∧ c.b12 = true ∧ c.b4 = true ∧ c.b11 = true ∧ c.b0 = true ∧ c.b9 = true then false else
  d

set_option maxRecDepth 100000 in
theorem base_passes (d : Bool) : Passes (base d) := by
  unfold Passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4
    simp [base, h0, h1, h2, h3, h4]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4
    simp [base, h0, h1, h2, h3, h4]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3
    simp [base, h0, h1, h2, h3]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3
    simp [base, h0, h1, h2, h3]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3
    simp [base, h0, h1, h2, h3]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4
    simp [base, h0, h1, h2, h3, h4]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4
    simp [base, h0, h1, h2, h3, h4]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4
    simp [base, h0, h1, h2, h3, h4]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]
  · intro c h0 h1 h2 h3 h4
    simp [base, h0, h1, h2, h3, h4]
  · intro c h0 h1
    simp [base, h0, h1]
  · intro c h0 h1 h2 h3 h4
    simp [base, h0, h1, h2, h3, h4]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp [base, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · intro c h0 h1 h2 h3 h4 h5
    simp [base, h0, h1, h2, h3, h4, h5]
  · intro c h0 h1 h2 h3 h4 h5 h6
    simp [base, h0, h1, h2, h3, h4, h5, h6]

def designA : Decide := base false
def designB : Decide := base true
def input : Case := ⟨true, false, true, false, false, true, true, true, true, true, true, false, false, false⟩
theorem a_passes : Passes designA := base_passes false
theorem b_passes : Passes designB := base_passes true
theorem differ : designA input ≠ designB input := by decide

end TblGap
