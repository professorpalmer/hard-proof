import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The rule tree from the laws. The missing leaf is the parameter `hole`. -/
def tree (hole : Bool) (c : Case) : Bool :=
  (bif c.b1 then (bif c.b0 then (bif c.b6 then (bif c.b10 then (bif c.b14 then (bif c.b2 then true else false) else (bif c.b9 then (bif c.b8 then (bif c.b7 then (bif c.b13 then (bif c.b4 then (bif c.b11 then (bif c.b12 then false else (bif c.b17 then (bif c.b3 then false else (bif c.b2 then true else true)) else true)) else false) else (bif c.b11 then (bif c.b12 then false else (bif c.b3 then (bif c.b16 then false else (bif c.b2 then (bif c.b5 then false else false) else false)) else false)) else (bif c.b12 then (bif c.b3 then false else false) else false))) else (bif c.b3 then (bif c.b11 then (bif c.b2 then false else false) else true) else (bif c.b17 then (bif c.b2 then false else false) else false))) else (bif c.b16 then true else (bif c.b11 then (bif c.b12 then (bif c.b13 then (bif c.b17 then (bif c.b5 then false else true) else false) else false) else (bif c.b13 then (bif c.b17 then (bif c.b15 then false else (bif c.b4 then true else true)) else false) else true)) else (bif c.b15 then false else (bif c.b5 then (bif c.b12 then false else true) else (bif c.b4 then true else false)))))) else (bif c.b2 then (bif c.b5 then (bif c.b7 then false else true) else (bif c.b7 then (bif c.b16 then (bif c.b17 then true else true) else (bif c.b3 then (bif c.b17 then (bif c.b11 then true else true) else false) else true)) else false)) else (bif c.b4 then (bif c.b7 then false else false) else (bif c.b3 then true else (bif c.b7 then true else (bif c.b12 then true else false)))))) else (bif c.b11 then (bif c.b16 then (bif c.b3 then true else (bif c.b12 then (bif c.b7 then false else false) else false)) else (bif c.b5 then false else false)) else (bif c.b17 then (bif c.b3 then false else false) else (bif c.b16 then false else false))))) else false) else (bif c.b7 then (bif c.b14 then (bif c.b15 then (bif c.b4 then false else true) else true) else (bif c.b4 then (bif c.b3 then (bif c.b5 then false else false) else (bif c.b12 then (bif c.b16 then false else (bif c.b15 then (bif c.b2 then false else false) else (bif c.b5 then true else (bif c.b13 then true else (bif c.b8 then false else (bif c.b2 then true else true)))))) else (bif c.b15 then (bif c.b13 then false else (bif c.b9 then true else false)) else (bif c.b10 then (bif c.b2 then (bif c.b13 then true else false) else false) else true)))) else (bif c.b8 then (bif c.b16 then false else false) else (bif c.b10 then (bif c.b15 then (bif c.b11 then (bif c.b2 then true else true) else (bif c.b5 then (bif c.b12 then (bif c.b16 then false else true) else (bif c.b3 then (bif c.b9 then (bif c.b16 then false else false) else false) else false)) else (bif c.b3 then (bif c.b13 then (bif c.b16 then false else false) else false) else false))) else (bif c.b13 then false else true)) else (bif c.b2 then (bif c.b13 then (bif c.b12 then false else false) else true) else true))))) else (bif c.b10 then (bif c.b12 then (bif c.b13 then false else true) else (bif c.b8 then (bif c.b14 then false else (bif c.b9 then true else true)) else (bif c.b16 then true else true))) else (bif c.b4 then (bif c.b14 then true else (bif c.b16 then true else (bif c.b8 then true else (bif c.b5 then false else false)))) else (bif c.b16 then (bif c.b9 then (bif c.b2 then true else true) else (bif c.b14 then (bif c.b13 then (bif c.b3 then false else false) else true) else (bif c.b2 then (bif c.b5 then true else (bif c.b15 then (bif c.b11 then false else false) else (bif c.b8 then true else true))) else (bif c.b8 then false else (bif c.b11 then (bif c.b3 then false else true) else false))))) else (bif c.b2 then false else (bif c.b15 then (bif c.b13 then false else false) else true))))))) else (bif c.b6 then (bif c.b10 then (bif c.b4 then (bif c.b7 then (bif c.b3 then true else false) else (bif c.b16 then true else (bif c.b2 then true else (bif c.b13 then false else false)))) else (bif c.b16 then (bif c.b13 then (bif c.b7 then (bif c.b3 then false else false) else false) else true) else (bif c.b8 then false else false))) else (bif c.b12 then (bif c.b9 then (bif c.b15 then (bif c.b4 then (bif c.b14 then (bif c.b2 then (bif c.b3 then true else (bif c.b5 then (bif c.b17 then (bif c.b11 then false else true) else (bif c.b13 then true else false)) else (bif c.b17 then (bif c.b16 then true else false) else false))) else (bif c.b5 then (bif c.b16 then (bif c.b11 then true else false) else true) else (bif c.b3 then false else (bif c.b7 then false else false)))) else (bif c.b5 then (bif c.b8 then false else true) else (bif c.b8 then (bif c.b7 then false else false) else (bif c.b3 then (bif c.b7 then (bif c.b16 then (bif c.b11 then true else false) else true) else false) else (bif c.b16 then (bif c.b7 then (bif c.b2 then (bif c.b17 then (bif c.b11 then true else false) else (bif c.b13 then (bif c.b11 then false else true) else false)) else (bif c.b11 then (bif c.b13 then false else (bif c.b17 then false else true)) else (bif c.b13 then true else (bif c.b17 then true else true)))) else (bif c.b11 then (bif c.b13 then (bif c.b17 then false else true) else false) else false)) else false))))) else true) else (bif c.b8 then (bif c.b11 then (bif c.b3 then (bif c.b7 then true else (bif c.b4 then true else true)) else (bif c.b7 then (bif c.b17 then false else false) else (bif c.b4 then true else (bif c.b13 then true else false)))) else (bif c.b16 then true else (bif c.b5 then (bif c.b4 then false else true) else (bif c.b2 then true else false)))) else (bif c.b11 then (bif c.b16 then false else (bif c.b2 then (bif c.b13 then true else false) else (bif c.b14 then false else (bif c.b4 then (bif c.b7 then true else true) else false)))) else false))) else (bif c.b11 then (bif c.b7 then (bif c.b2 then true else false) else (bif c.b13 then (bif c.b2 then true else true) else true)) else (bif c.b14 then false else (bif c.b15 then (bif c.b8 then (bif c.b16 then true else true) else (bif c.b3 then (bif c.b13 then false else false) else (bif c.b13 then (bif c.b7 then false else true) else true))) else (bif c.b13 then false else true))))) else (bif c.b17 then (bif c.b4 then (bif c.b2 then false else (bif c.b16 then (bif c.b14 then (bif c.b11 then false else (bif c.b3 then false else false)) else (bif c.b7 then false else true)) else (bif c.b9 then (bif c.b15 then false else true) else true))) else (bif c.b9 then (bif c.b16 then (bif c.b14 then (bif c.b5 then (bif c.b11 then true else false) else (bif c.b8 then false else (bif c.b15 then (bif c.b7 then false else false) else (bif c.b11 then false else (bif c.b13 then true else true))))) else (bif c.b15 then (bif c.b3 then false else true) else false)) else (bif c.b15 then false else (bif c.b13 then false else false))) else false)) else (bif c.b15 then (bif c.b2 then (bif c.b13 then (bif c.b4 then (bif c.b8 then (bif c.b9 then (bif c.b7 then true else (bif c.b5 then (bif c.b16 then false else true) else false)) else false) else true) else (bif c.b11 then true else false)) else (bif c.b3 then (bif c.b14 then true else true) else (bif c.b4 then true else false))) else (bif c.b13 then (bif c.b4 then (bif c.b8 then (bif c.b11 then true else false) else (bif c.b3 then true else false)) else false) else true)) else (bif c.b14 then (bif c.b7 then false else false) else (bif c.b3 then true else false)))))) else (bif c.b12 then (bif c.b7 then (bif c.b17 then (bif c.b5 then (bif c.b14 then (bif c.b13 then (bif c.b16 then (bif c.b2 then (bif c.b3 then false else (bif c.b11 then (bif c.b10 then (bif c.b4 then true else true) else (bif c.b8 then false else (bif c.b4 then (bif c.b15 then false else (bif c.b9 then true else true)) else (bif c.b9 then true else true)))) else (bif c.b15 then (bif c.b4 then (bif c.b8 then (bif c.b10 then false else true) else false) else true) else (bif c.b8 then hole else true)))) else true) else true) else (bif c.b15 then true else true)) else (bif c.b3 then (bif c.b4 then false else true) else (bif c.b10 then (bif c.b9 then true else true) else (bif c.b2 then false else true)))) else (bif c.b15 then (bif c.b10 then (bif c.b13 then (bif c.b4 then false else true) else (bif c.b16 then true else true)) else (bif c.b2 then (bif c.b4 then (bif c.b13 then (bif c.b11 then true else false) else (bif c.b14 then (bif c.b16 then true else false) else false)) else (bif c.b14 then true else (bif c.b8 then true else false))) else (bif c.b8 then (bif c.b16 then true else true) else true))) else true)) else (bif c.b10 then (bif c.b3 then (bif c.b4 then (bif c.b13 then true else (bif c.b8 then true else true)) else false) else (bif c.b16 then (bif c.b5 then (bif c.b14 then (bif c.b4 then false else (bif c.b11 then true else (bif c.b13 then true else false))) else false) else (bif c.b8 then (bif c.b9 then (bif c.b4 then (bif c.b13 then true else true) else (bif c.b14 then true else true)) else (bif c.b15 then (bif c.b11 then true else true) else (bif c.b13 then true else (bif c.b2 then true else true)))) else (bif c.b4 then false else (bif c.b14 then true else false)))) else (bif c.b9 then (bif c.b11 then (bif c.b4 then (bif c.b5 then false else true) else (bif c.b5 then false else true)) else (bif c.b8 then false else (bif c.b13 then (bif c.b15 then true else (bif c.b2 then true else true)) else (bif c.b5 then true else true)))) else (bif c.b11 then (bif c.b13 then (bif c.b14 then (bif c.b15 then (bif c.b5 then (bif c.b4 then (bif c.b8 then false else (bif c.b2 then true else false)) else true) else true) else (bif c.b2 then (bif c.b5 then true else false) else true)) else (bif c.b15 then (bif c.b4 then false else false) else true)) else (bif c.b14 then true else false)) else (bif c.b8 then (bif c.b14 then false else (bif c.b5 then (bif c.b4 then (bif c.b13 then (bif c.b15 then true else false) else (bif c.b15 then true else true)) else true) else (bif c.b15 then false else true))) else false))))) else (bif c.b11 then (bif c.b16 then (bif c.b8 then (bif c.b3 then false else (bif c.b2 then false else false)) else (bif c.b15 then false else false)) else (bif c.b2 then true else false)) else (bif c.b2 then true else (bif c.b9 then (bif c.b15 then (bif c.b13 then (bif c.b5 then false else false) else (bif c.b8 then (bif c.b16 then false else (bif c.b14 then (bif c.b3 then false else true) else false)) else (bif c.b3 then false else true))) else true) else (bif c.b13 then true else (bif c.b15 then (bif c.b16 then false else true) else (bif c.b16 then false else (bif c.b8 then true else (bif c.b5 then false else false)))))))))) else (bif c.b14 then (bif c.b10 then (bif c.b17 then (bif c.b5 then (bif c.b8 then (bif c.b4 then false else true) else false) else (bif c.b8 then (bif c.b13 then false else false) else (bif c.b13 then (bif c.b4 then true else true) else (bif c.b3 then false else (bif c.b9 then (bif c.b15 then false else true) else true))))) else true) else (bif c.b3 then false else false)) else (bif c.b16 then (bif c.b8 then (bif c.b2 then (bif c.b17 then (bif c.b11 then (bif c.b10 then (bif c.b13 then (bif c.b4 then true else false) else (bif c.b5 then false else (bif c.b9 then false else true))) else (bif c.b13 then true else (bif c.b5 then (bif c.b9 then (bif c.b15 then false else true) else (bif c.b3 then false else true)) else false))) else (bif c.b13 then (bif c.b10 then (bif c.b3 then (bif c.b9 then true else (bif c.b5 then (bif c.b4 then true else false) else false)) else true) else (bif c.b9 then true else (bif c.b4 then true else false))) else (bif c.b4 then true else false))) else (bif c.b4 then true else (bif c.b15 then (bif c.b13 then true else (bif c.b10 then false else true)) else (bif c.b9 then (bif c.b3 then (bif c.b5 then true else false) else (bif c.b11 then (bif c.b10 then false else true) else (bif c.b13 then true else (bif c.b10 then false else true)))) else false)))) else (bif c.b9 then (bif c.b10 then true else (bif c.b17 then true else (bif c.b11 then false else false))) else (bif c.b17 then (bif c.b15 then (bif c.b4 then (bif c.b13 then true else (bif c.b11 then false else true)) else true) else (bif c.b5 then (bif c.b3 then true else true) else (bif c.b10 then true else (bif c.b3 then (bif c.b11 then false else true) else true)))) else (bif c.b5 then true else true)))) else (bif c.b4 then (bif c.b15 then false else false) else true)) else (bif c.b13 then false else false)))) else (bif c.b16 then (bif c.b17 then (bif c.b4 then false else (bif c.b11 then true else false)) else (bif c.b15 then (bif c.b9 then true else (bif c.b4 then false else (bif c.b7 then false else true))) else false)) else (bif c.b4 then (bif c.b14 then (bif c.b11 then true else true) else true) else true))))) else (bif c.b3 then (bif c.b11 then (bif c.b16 then (bif c.b5 then (bif c.b6 then false else (bif c.b7 then (bif c.b0 then (bif c.b2 then (bif c.b8 then (bif c.b4 then true else true) else false) else (bif c.b8 then false else true)) else true) else true)) else (bif c.b17 then false else false)) else (bif c.b14 then (bif c.b5 then true else false) else false)) else (bif c.b16 then true else (bif c.b14 then false else (bif c.b9 then (bif c.b15 then true else false) else (bif c.b5 then (bif c.b13 then true else (bif c.b7 then true else false)) else (bif c.b4 then false else (bif c.b13 then false else true))))))) else (bif c.b7 then (bif c.b8 then true else false) else (bif c.b16 then (bif c.b4 then (bif c.b9 then (bif c.b13 then (bif c.b12 then false else false) else true) else (bif c.b12 then (bif c.b11 then true else false) else false)) else (bif c.b5 then (bif c.b15 then false else (bif c.b6 then false else (bif c.b12 then false else false))) else (bif c.b13 then false else false))) else (bif c.b6 then (bif c.b9 then true else (bif c.b12 then (bif c.b14 then true else true) else (bif c.b0 then (bif c.b11 then true else false) else true))) else (bif c.b13 then (bif c.b4 then false else (bif c.b17 then false else true)) else false))))))

/-- The first recovery rule. -/
def designA : Decide := tree true

/-- The second recovery rule. -/
def designB : Decide := tree false

/-- The case on which the two rules differ. -/
def input : Case := { b0 := false, b1 := true, b2 := true, b3 := false, b4 := false, b5 := true, b6 := false, b7 := true, b8 := true, b9 := false, b10 := false, b11 := false, b12 := true, b13 := true, b14 := true, b15 := false, b16 := true, b17 := true }

theorem tree_law0 (hole : Bool) : Law0 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law1 (hole : Bool) : Law1 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law2 (hole : Bool) : Law2 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law3 (hole : Bool) : Law3 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law4 (hole : Bool) : Law4 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law5 (hole : Bool) : Law5 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law6 (hole : Bool) : Law6 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law7 (hole : Bool) : Law7 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law8 (hole : Bool) : Law8 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law9 (hole : Bool) : Law9 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law10 (hole : Bool) : Law10 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law11 (hole : Bool) : Law11 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law12 (hole : Bool) : Law12 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law13 (hole : Bool) : Law13 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law14 (hole : Bool) : Law14 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law15 (hole : Bool) : Law15 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law16 (hole : Bool) : Law16 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law17 (hole : Bool) : Law17 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law18 (hole : Bool) : Law18 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law19 (hole : Bool) : Law19 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law20 (hole : Bool) : Law20 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law21 (hole : Bool) : Law21 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law22 (hole : Bool) : Law22 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law23 (hole : Bool) : Law23 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law24 (hole : Bool) : Law24 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law25 (hole : Bool) : Law25 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law26 (hole : Bool) : Law26 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law27 (hole : Bool) : Law27 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law28 (hole : Bool) : Law28 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law29 (hole : Bool) : Law29 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law30 (hole : Bool) : Law30 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law31 (hole : Bool) : Law31 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law32 (hole : Bool) : Law32 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law33 (hole : Bool) : Law33 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law34 (hole : Bool) : Law34 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law35 (hole : Bool) : Law35 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law36 (hole : Bool) : Law36 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law37 (hole : Bool) : Law37 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law38 (hole : Bool) : Law38 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law39 (hole : Bool) : Law39 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law40 (hole : Bool) : Law40 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law41 (hole : Bool) : Law41 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law42 (hole : Bool) : Law42 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law43 (hole : Bool) : Law43 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law44 (hole : Bool) : Law44 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law45 (hole : Bool) : Law45 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law46 (hole : Bool) : Law46 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law47 (hole : Bool) : Law47 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law48 (hole : Bool) : Law48 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law49 (hole : Bool) : Law49 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law50 (hole : Bool) : Law50 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law51 (hole : Bool) : Law51 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law52 (hole : Bool) : Law52 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law53 (hole : Bool) : Law53 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law54 (hole : Bool) : Law54 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law55 (hole : Bool) : Law55 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law56 (hole : Bool) : Law56 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law57 (hole : Bool) : Law57 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law58 (hole : Bool) : Law58 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law59 (hole : Bool) : Law59 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law60 (hole : Bool) : Law60 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law61 (hole : Bool) : Law61 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law62 (hole : Bool) : Law62 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law63 (hole : Bool) : Law63 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law64 (hole : Bool) : Law64 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law65 (hole : Bool) : Law65 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law66 (hole : Bool) : Law66 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law67 (hole : Bool) : Law67 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law68 (hole : Bool) : Law68 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law69 (hole : Bool) : Law69 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law70 (hole : Bool) : Law70 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law71 (hole : Bool) : Law71 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law72 (hole : Bool) : Law72 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law73 (hole : Bool) : Law73 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law74 (hole : Bool) : Law74 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law75 (hole : Bool) : Law75 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law76 (hole : Bool) : Law76 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law77 (hole : Bool) : Law77 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law78 (hole : Bool) : Law78 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law79 (hole : Bool) : Law79 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law80 (hole : Bool) : Law80 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law81 (hole : Bool) : Law81 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law82 (hole : Bool) : Law82 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law83 (hole : Bool) : Law83 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law84 (hole : Bool) : Law84 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law85 (hole : Bool) : Law85 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law86 (hole : Bool) : Law86 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law87 (hole : Bool) : Law87 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law88 (hole : Bool) : Law88 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law89 (hole : Bool) : Law89 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law90 (hole : Bool) : Law90 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law91 (hole : Bool) : Law91 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law92 (hole : Bool) : Law92 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law93 (hole : Bool) : Law93 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law94 (hole : Bool) : Law94 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law95 (hole : Bool) : Law95 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law96 (hole : Bool) : Law96 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law97 (hole : Bool) : Law97 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law98 (hole : Bool) : Law98 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law99 (hole : Bool) : Law99 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law100 (hole : Bool) : Law100 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law101 (hole : Bool) : Law101 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law102 (hole : Bool) : Law102 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law103 (hole : Bool) : Law103 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law104 (hole : Bool) : Law104 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law105 (hole : Bool) : Law105 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law106 (hole : Bool) : Law106 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law107 (hole : Bool) : Law107 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law108 (hole : Bool) : Law108 (tree hole) := by
  intro c h0 h1 h2 h3
  simp [tree, h0, h1, h2, h3]
theorem tree_law109 (hole : Bool) : Law109 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law110 (hole : Bool) : Law110 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law111 (hole : Bool) : Law111 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law112 (hole : Bool) : Law112 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law113 (hole : Bool) : Law113 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law114 (hole : Bool) : Law114 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law115 (hole : Bool) : Law115 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law116 (hole : Bool) : Law116 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law117 (hole : Bool) : Law117 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law118 (hole : Bool) : Law118 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law119 (hole : Bool) : Law119 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law120 (hole : Bool) : Law120 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law121 (hole : Bool) : Law121 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law122 (hole : Bool) : Law122 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law123 (hole : Bool) : Law123 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law124 (hole : Bool) : Law124 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law125 (hole : Bool) : Law125 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law126 (hole : Bool) : Law126 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law127 (hole : Bool) : Law127 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law128 (hole : Bool) : Law128 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law129 (hole : Bool) : Law129 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law130 (hole : Bool) : Law130 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law131 (hole : Bool) : Law131 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law132 (hole : Bool) : Law132 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law133 (hole : Bool) : Law133 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law134 (hole : Bool) : Law134 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law135 (hole : Bool) : Law135 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law136 (hole : Bool) : Law136 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law137 (hole : Bool) : Law137 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law138 (hole : Bool) : Law138 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law139 (hole : Bool) : Law139 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law140 (hole : Bool) : Law140 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law141 (hole : Bool) : Law141 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law142 (hole : Bool) : Law142 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law143 (hole : Bool) : Law143 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law144 (hole : Bool) : Law144 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law145 (hole : Bool) : Law145 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law146 (hole : Bool) : Law146 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law147 (hole : Bool) : Law147 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law148 (hole : Bool) : Law148 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law149 (hole : Bool) : Law149 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law150 (hole : Bool) : Law150 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law151 (hole : Bool) : Law151 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law152 (hole : Bool) : Law152 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law153 (hole : Bool) : Law153 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law154 (hole : Bool) : Law154 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law155 (hole : Bool) : Law155 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law156 (hole : Bool) : Law156 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law157 (hole : Bool) : Law157 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law158 (hole : Bool) : Law158 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law159 (hole : Bool) : Law159 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law160 (hole : Bool) : Law160 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law161 (hole : Bool) : Law161 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law162 (hole : Bool) : Law162 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law163 (hole : Bool) : Law163 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law164 (hole : Bool) : Law164 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law165 (hole : Bool) : Law165 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law166 (hole : Bool) : Law166 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law167 (hole : Bool) : Law167 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law168 (hole : Bool) : Law168 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law169 (hole : Bool) : Law169 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law170 (hole : Bool) : Law170 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law171 (hole : Bool) : Law171 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law172 (hole : Bool) : Law172 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law173 (hole : Bool) : Law173 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law174 (hole : Bool) : Law174 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law175 (hole : Bool) : Law175 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law176 (hole : Bool) : Law176 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law177 (hole : Bool) : Law177 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law178 (hole : Bool) : Law178 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law179 (hole : Bool) : Law179 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law180 (hole : Bool) : Law180 (tree hole) := by
  intro c h0 h1 h2 h3
  simp [tree, h0, h1, h2, h3]
theorem tree_law181 (hole : Bool) : Law181 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law182 (hole : Bool) : Law182 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law183 (hole : Bool) : Law183 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law184 (hole : Bool) : Law184 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law185 (hole : Bool) : Law185 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law186 (hole : Bool) : Law186 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law187 (hole : Bool) : Law187 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law188 (hole : Bool) : Law188 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law189 (hole : Bool) : Law189 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law190 (hole : Bool) : Law190 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law191 (hole : Bool) : Law191 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law192 (hole : Bool) : Law192 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law193 (hole : Bool) : Law193 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law194 (hole : Bool) : Law194 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law195 (hole : Bool) : Law195 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law196 (hole : Bool) : Law196 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law197 (hole : Bool) : Law197 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law198 (hole : Bool) : Law198 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law199 (hole : Bool) : Law199 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law200 (hole : Bool) : Law200 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law201 (hole : Bool) : Law201 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law202 (hole : Bool) : Law202 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law203 (hole : Bool) : Law203 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law204 (hole : Bool) : Law204 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law205 (hole : Bool) : Law205 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law206 (hole : Bool) : Law206 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law207 (hole : Bool) : Law207 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law208 (hole : Bool) : Law208 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law209 (hole : Bool) : Law209 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law210 (hole : Bool) : Law210 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law211 (hole : Bool) : Law211 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law212 (hole : Bool) : Law212 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law213 (hole : Bool) : Law213 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law214 (hole : Bool) : Law214 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law215 (hole : Bool) : Law215 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law216 (hole : Bool) : Law216 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law217 (hole : Bool) : Law217 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law218 (hole : Bool) : Law218 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law219 (hole : Bool) : Law219 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law220 (hole : Bool) : Law220 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law221 (hole : Bool) : Law221 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law222 (hole : Bool) : Law222 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law223 (hole : Bool) : Law223 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law224 (hole : Bool) : Law224 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law225 (hole : Bool) : Law225 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law226 (hole : Bool) : Law226 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law227 (hole : Bool) : Law227 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law228 (hole : Bool) : Law228 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law229 (hole : Bool) : Law229 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law230 (hole : Bool) : Law230 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law231 (hole : Bool) : Law231 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law232 (hole : Bool) : Law232 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law233 (hole : Bool) : Law233 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law234 (hole : Bool) : Law234 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law235 (hole : Bool) : Law235 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law236 (hole : Bool) : Law236 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law237 (hole : Bool) : Law237 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law238 (hole : Bool) : Law238 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law239 (hole : Bool) : Law239 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law240 (hole : Bool) : Law240 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law241 (hole : Bool) : Law241 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law242 (hole : Bool) : Law242 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law243 (hole : Bool) : Law243 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law244 (hole : Bool) : Law244 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law245 (hole : Bool) : Law245 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law246 (hole : Bool) : Law246 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law247 (hole : Bool) : Law247 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law248 (hole : Bool) : Law248 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law249 (hole : Bool) : Law249 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law250 (hole : Bool) : Law250 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law251 (hole : Bool) : Law251 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law252 (hole : Bool) : Law252 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law253 (hole : Bool) : Law253 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law254 (hole : Bool) : Law254 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law255 (hole : Bool) : Law255 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law256 (hole : Bool) : Law256 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law257 (hole : Bool) : Law257 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law258 (hole : Bool) : Law258 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law259 (hole : Bool) : Law259 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law260 (hole : Bool) : Law260 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law261 (hole : Bool) : Law261 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law262 (hole : Bool) : Law262 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law263 (hole : Bool) : Law263 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law264 (hole : Bool) : Law264 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law265 (hole : Bool) : Law265 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law266 (hole : Bool) : Law266 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law267 (hole : Bool) : Law267 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law268 (hole : Bool) : Law268 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law269 (hole : Bool) : Law269 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law270 (hole : Bool) : Law270 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law271 (hole : Bool) : Law271 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law272 (hole : Bool) : Law272 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law273 (hole : Bool) : Law273 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law274 (hole : Bool) : Law274 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law275 (hole : Bool) : Law275 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law276 (hole : Bool) : Law276 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law277 (hole : Bool) : Law277 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law278 (hole : Bool) : Law278 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law279 (hole : Bool) : Law279 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law280 (hole : Bool) : Law280 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law281 (hole : Bool) : Law281 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law282 (hole : Bool) : Law282 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law283 (hole : Bool) : Law283 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law284 (hole : Bool) : Law284 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law285 (hole : Bool) : Law285 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law286 (hole : Bool) : Law286 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law287 (hole : Bool) : Law287 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law288 (hole : Bool) : Law288 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law289 (hole : Bool) : Law289 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law290 (hole : Bool) : Law290 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5
  simp [tree, h0, h1, h2, h3, h4, h5]
theorem tree_law291 (hole : Bool) : Law291 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law292 (hole : Bool) : Law292 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law293 (hole : Bool) : Law293 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law294 (hole : Bool) : Law294 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law295 (hole : Bool) : Law295 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law296 (hole : Bool) : Law296 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law297 (hole : Bool) : Law297 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law298 (hole : Bool) : Law298 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law299 (hole : Bool) : Law299 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law300 (hole : Bool) : Law300 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law301 (hole : Bool) : Law301 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law302 (hole : Bool) : Law302 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law303 (hole : Bool) : Law303 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law304 (hole : Bool) : Law304 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law305 (hole : Bool) : Law305 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law306 (hole : Bool) : Law306 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law307 (hole : Bool) : Law307 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law308 (hole : Bool) : Law308 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law309 (hole : Bool) : Law309 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law310 (hole : Bool) : Law310 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law311 (hole : Bool) : Law311 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law312 (hole : Bool) : Law312 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law313 (hole : Bool) : Law313 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law314 (hole : Bool) : Law314 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law315 (hole : Bool) : Law315 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law316 (hole : Bool) : Law316 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law317 (hole : Bool) : Law317 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law318 (hole : Bool) : Law318 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law319 (hole : Bool) : Law319 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law320 (hole : Bool) : Law320 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law321 (hole : Bool) : Law321 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law322 (hole : Bool) : Law322 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law323 (hole : Bool) : Law323 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law324 (hole : Bool) : Law324 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law325 (hole : Bool) : Law325 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law326 (hole : Bool) : Law326 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law327 (hole : Bool) : Law327 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law328 (hole : Bool) : Law328 (tree hole) := by
  intro c h0 h1 h2 h3
  simp [tree, h0, h1, h2, h3]
theorem tree_law329 (hole : Bool) : Law329 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law330 (hole : Bool) : Law330 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law331 (hole : Bool) : Law331 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law332 (hole : Bool) : Law332 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law333 (hole : Bool) : Law333 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law334 (hole : Bool) : Law334 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law335 (hole : Bool) : Law335 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law336 (hole : Bool) : Law336 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law337 (hole : Bool) : Law337 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law338 (hole : Bool) : Law338 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law339 (hole : Bool) : Law339 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law340 (hole : Bool) : Law340 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law341 (hole : Bool) : Law341 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law342 (hole : Bool) : Law342 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law343 (hole : Bool) : Law343 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law344 (hole : Bool) : Law344 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law345 (hole : Bool) : Law345 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law346 (hole : Bool) : Law346 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law347 (hole : Bool) : Law347 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law348 (hole : Bool) : Law348 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law349 (hole : Bool) : Law349 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law350 (hole : Bool) : Law350 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law351 (hole : Bool) : Law351 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law352 (hole : Bool) : Law352 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law353 (hole : Bool) : Law353 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law354 (hole : Bool) : Law354 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law355 (hole : Bool) : Law355 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law356 (hole : Bool) : Law356 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law357 (hole : Bool) : Law357 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law358 (hole : Bool) : Law358 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law359 (hole : Bool) : Law359 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law360 (hole : Bool) : Law360 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law361 (hole : Bool) : Law361 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law362 (hole : Bool) : Law362 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law363 (hole : Bool) : Law363 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law364 (hole : Bool) : Law364 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law365 (hole : Bool) : Law365 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law366 (hole : Bool) : Law366 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law367 (hole : Bool) : Law367 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law368 (hole : Bool) : Law368 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law369 (hole : Bool) : Law369 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law370 (hole : Bool) : Law370 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law371 (hole : Bool) : Law371 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law372 (hole : Bool) : Law372 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law373 (hole : Bool) : Law373 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law374 (hole : Bool) : Law374 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law375 (hole : Bool) : Law375 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law376 (hole : Bool) : Law376 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law377 (hole : Bool) : Law377 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law378 (hole : Bool) : Law378 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law379 (hole : Bool) : Law379 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law380 (hole : Bool) : Law380 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law381 (hole : Bool) : Law381 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law382 (hole : Bool) : Law382 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law383 (hole : Bool) : Law383 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law384 (hole : Bool) : Law384 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law385 (hole : Bool) : Law385 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law386 (hole : Bool) : Law386 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law387 (hole : Bool) : Law387 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law388 (hole : Bool) : Law388 (tree hole) := by
  intro c h0 h1 h2 h3 h4
  simp [tree, h0, h1, h2, h3, h4]
theorem tree_law389 (hole : Bool) : Law389 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law390 (hole : Bool) : Law390 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law391 (hole : Bool) : Law391 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law392 (hole : Bool) : Law392 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law393 (hole : Bool) : Law393 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law394 (hole : Bool) : Law394 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law395 (hole : Bool) : Law395 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law396 (hole : Bool) : Law396 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law397 (hole : Bool) : Law397 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law398 (hole : Bool) : Law398 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law399 (hole : Bool) : Law399 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law400 (hole : Bool) : Law400 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law401 (hole : Bool) : Law401 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law402 (hole : Bool) : Law402 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law403 (hole : Bool) : Law403 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law404 (hole : Bool) : Law404 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law405 (hole : Bool) : Law405 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law406 (hole : Bool) : Law406 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law407 (hole : Bool) : Law407 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law408 (hole : Bool) : Law408 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law409 (hole : Bool) : Law409 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law410 (hole : Bool) : Law410 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law411 (hole : Bool) : Law411 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law412 (hole : Bool) : Law412 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law413 (hole : Bool) : Law413 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law414 (hole : Bool) : Law414 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law415 (hole : Bool) : Law415 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law416 (hole : Bool) : Law416 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law417 (hole : Bool) : Law417 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law418 (hole : Bool) : Law418 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law419 (hole : Bool) : Law419 (tree hole) := by
  intro c h0 h1 h2 h3
  simp [tree, h0, h1, h2, h3]
theorem tree_law420 (hole : Bool) : Law420 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law421 (hole : Bool) : Law421 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law422 (hole : Bool) : Law422 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law423 (hole : Bool) : Law423 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law424 (hole : Bool) : Law424 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law425 (hole : Bool) : Law425 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law426 (hole : Bool) : Law426 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law427 (hole : Bool) : Law427 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law428 (hole : Bool) : Law428 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law429 (hole : Bool) : Law429 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law430 (hole : Bool) : Law430 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law431 (hole : Bool) : Law431 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law432 (hole : Bool) : Law432 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law433 (hole : Bool) : Law433 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law434 (hole : Bool) : Law434 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law435 (hole : Bool) : Law435 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law436 (hole : Bool) : Law436 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law437 (hole : Bool) : Law437 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law438 (hole : Bool) : Law438 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law439 (hole : Bool) : Law439 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law440 (hole : Bool) : Law440 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law441 (hole : Bool) : Law441 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law442 (hole : Bool) : Law442 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law443 (hole : Bool) : Law443 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law444 (hole : Bool) : Law444 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law445 (hole : Bool) : Law445 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law446 (hole : Bool) : Law446 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law447 (hole : Bool) : Law447 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law448 (hole : Bool) : Law448 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law449 (hole : Bool) : Law449 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law450 (hole : Bool) : Law450 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law451 (hole : Bool) : Law451 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law452 (hole : Bool) : Law452 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law453 (hole : Bool) : Law453 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
theorem tree_law454 (hole : Bool) : Law454 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law455 (hole : Bool) : Law455 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law456 (hole : Bool) : Law456 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law457 (hole : Bool) : Law457 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law458 (hole : Bool) : Law458 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law459 (hole : Bool) : Law459 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law460 (hole : Bool) : Law460 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law461 (hole : Bool) : Law461 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law462 (hole : Bool) : Law462 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law463 (hole : Bool) : Law463 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law464 (hole : Bool) : Law464 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law465 (hole : Bool) : Law465 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law466 (hole : Bool) : Law466 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law467 (hole : Bool) : Law467 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law468 (hole : Bool) : Law468 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law469 (hole : Bool) : Law469 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law470 (hole : Bool) : Law470 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law471 (hole : Bool) : Law471 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law472 (hole : Bool) : Law472 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law473 (hole : Bool) : Law473 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law474 (hole : Bool) : Law474 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law475 (hole : Bool) : Law475 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law476 (hole : Bool) : Law476 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law477 (hole : Bool) : Law477 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law478 (hole : Bool) : Law478 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law479 (hole : Bool) : Law479 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law480 (hole : Bool) : Law480 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law481 (hole : Bool) : Law481 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law482 (hole : Bool) : Law482 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law483 (hole : Bool) : Law483 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law484 (hole : Bool) : Law484 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
theorem tree_law485 (hole : Bool) : Law485 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law486 (hole : Bool) : Law486 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law487 (hole : Bool) : Law487 (tree hole) := by
  intro c h0 h1 h2 h3 h4
  simp [tree, h0, h1, h2, h3, h4]
theorem tree_law488 (hole : Bool) : Law488 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law489 (hole : Bool) : Law489 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law490 (hole : Bool) : Law490 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law491 (hole : Bool) : Law491 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law492 (hole : Bool) : Law492 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8]
theorem tree_law493 (hole : Bool) : Law493 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law494 (hole : Bool) : Law494 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law495 (hole : Bool) : Law495 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law496 (hole : Bool) : Law496 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law497 (hole : Bool) : Law497 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law498 (hole : Bool) : Law498 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law499 (hole : Bool) : Law499 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law500 (hole : Bool) : Law500 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
theorem tree_law501 (hole : Bool) : Law501 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
theorem tree_law502 (hole : Bool) : Law502 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
theorem tree_law503 (hole : Bool) : Law503 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law504 (hole : Bool) : Law504 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
theorem tree_law505 (hole : Bool) : Law505 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
theorem tree_law506 (hole : Bool) : Law506 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7]
theorem tree_law507 (hole : Bool) : Law507 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
theorem tree_law508 (hole : Bool) : Law508 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
theorem tree_law509 (hole : Bool) : Law509 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6
  simp [tree, h0, h1, h2, h3, h4, h5, h6]
theorem tree_law510 (hole : Bool) : Law510 (tree hole) := by
  intro c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp [tree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem tree_passes (hole : Bool) : Passes (tree hole) :=
  ⟨⟨tree_law0 hole, tree_law1 hole, tree_law2 hole, tree_law3 hole, tree_law4 hole, tree_law5 hole, tree_law6 hole, tree_law7 hole, tree_law8 hole, tree_law9 hole, tree_law10 hole, tree_law11 hole, tree_law12 hole, tree_law13 hole, tree_law14 hole, tree_law15 hole⟩,
   ⟨tree_law16 hole, tree_law17 hole, tree_law18 hole, tree_law19 hole, tree_law20 hole, tree_law21 hole, tree_law22 hole, tree_law23 hole, tree_law24 hole, tree_law25 hole, tree_law26 hole, tree_law27 hole, tree_law28 hole, tree_law29 hole, tree_law30 hole, tree_law31 hole⟩,
   ⟨tree_law32 hole, tree_law33 hole, tree_law34 hole, tree_law35 hole, tree_law36 hole, tree_law37 hole, tree_law38 hole, tree_law39 hole, tree_law40 hole, tree_law41 hole, tree_law42 hole, tree_law43 hole, tree_law44 hole, tree_law45 hole, tree_law46 hole, tree_law47 hole⟩,
   ⟨tree_law48 hole, tree_law49 hole, tree_law50 hole, tree_law51 hole, tree_law52 hole, tree_law53 hole, tree_law54 hole, tree_law55 hole, tree_law56 hole, tree_law57 hole, tree_law58 hole, tree_law59 hole, tree_law60 hole, tree_law61 hole, tree_law62 hole, tree_law63 hole⟩,
   ⟨tree_law64 hole, tree_law65 hole, tree_law66 hole, tree_law67 hole, tree_law68 hole, tree_law69 hole, tree_law70 hole, tree_law71 hole, tree_law72 hole, tree_law73 hole, tree_law74 hole, tree_law75 hole, tree_law76 hole, tree_law77 hole, tree_law78 hole, tree_law79 hole⟩,
   ⟨tree_law80 hole, tree_law81 hole, tree_law82 hole, tree_law83 hole, tree_law84 hole, tree_law85 hole, tree_law86 hole, tree_law87 hole, tree_law88 hole, tree_law89 hole, tree_law90 hole, tree_law91 hole, tree_law92 hole, tree_law93 hole, tree_law94 hole, tree_law95 hole⟩,
   ⟨tree_law96 hole, tree_law97 hole, tree_law98 hole, tree_law99 hole, tree_law100 hole, tree_law101 hole, tree_law102 hole, tree_law103 hole, tree_law104 hole, tree_law105 hole, tree_law106 hole, tree_law107 hole, tree_law108 hole, tree_law109 hole, tree_law110 hole, tree_law111 hole⟩,
   ⟨tree_law112 hole, tree_law113 hole, tree_law114 hole, tree_law115 hole, tree_law116 hole, tree_law117 hole, tree_law118 hole, tree_law119 hole, tree_law120 hole, tree_law121 hole, tree_law122 hole, tree_law123 hole, tree_law124 hole, tree_law125 hole, tree_law126 hole, tree_law127 hole⟩,
   ⟨tree_law128 hole, tree_law129 hole, tree_law130 hole, tree_law131 hole, tree_law132 hole, tree_law133 hole, tree_law134 hole, tree_law135 hole, tree_law136 hole, tree_law137 hole, tree_law138 hole, tree_law139 hole, tree_law140 hole, tree_law141 hole, tree_law142 hole, tree_law143 hole⟩,
   ⟨tree_law144 hole, tree_law145 hole, tree_law146 hole, tree_law147 hole, tree_law148 hole, tree_law149 hole, tree_law150 hole, tree_law151 hole, tree_law152 hole, tree_law153 hole, tree_law154 hole, tree_law155 hole, tree_law156 hole, tree_law157 hole, tree_law158 hole, tree_law159 hole⟩,
   ⟨tree_law160 hole, tree_law161 hole, tree_law162 hole, tree_law163 hole, tree_law164 hole, tree_law165 hole, tree_law166 hole, tree_law167 hole, tree_law168 hole, tree_law169 hole, tree_law170 hole, tree_law171 hole, tree_law172 hole, tree_law173 hole, tree_law174 hole, tree_law175 hole⟩,
   ⟨tree_law176 hole, tree_law177 hole, tree_law178 hole, tree_law179 hole, tree_law180 hole, tree_law181 hole, tree_law182 hole, tree_law183 hole, tree_law184 hole, tree_law185 hole, tree_law186 hole, tree_law187 hole, tree_law188 hole, tree_law189 hole, tree_law190 hole, tree_law191 hole⟩,
   ⟨tree_law192 hole, tree_law193 hole, tree_law194 hole, tree_law195 hole, tree_law196 hole, tree_law197 hole, tree_law198 hole, tree_law199 hole, tree_law200 hole, tree_law201 hole, tree_law202 hole, tree_law203 hole, tree_law204 hole, tree_law205 hole, tree_law206 hole, tree_law207 hole⟩,
   ⟨tree_law208 hole, tree_law209 hole, tree_law210 hole, tree_law211 hole, tree_law212 hole, tree_law213 hole, tree_law214 hole, tree_law215 hole, tree_law216 hole, tree_law217 hole, tree_law218 hole, tree_law219 hole, tree_law220 hole, tree_law221 hole, tree_law222 hole, tree_law223 hole⟩,
   ⟨tree_law224 hole, tree_law225 hole, tree_law226 hole, tree_law227 hole, tree_law228 hole, tree_law229 hole, tree_law230 hole, tree_law231 hole, tree_law232 hole, tree_law233 hole, tree_law234 hole, tree_law235 hole, tree_law236 hole, tree_law237 hole, tree_law238 hole, tree_law239 hole⟩,
   ⟨tree_law240 hole, tree_law241 hole, tree_law242 hole, tree_law243 hole, tree_law244 hole, tree_law245 hole, tree_law246 hole, tree_law247 hole, tree_law248 hole, tree_law249 hole, tree_law250 hole, tree_law251 hole, tree_law252 hole, tree_law253 hole, tree_law254 hole, tree_law255 hole⟩,
   ⟨tree_law256 hole, tree_law257 hole, tree_law258 hole, tree_law259 hole, tree_law260 hole, tree_law261 hole, tree_law262 hole, tree_law263 hole, tree_law264 hole, tree_law265 hole, tree_law266 hole, tree_law267 hole, tree_law268 hole, tree_law269 hole, tree_law270 hole, tree_law271 hole⟩,
   ⟨tree_law272 hole, tree_law273 hole, tree_law274 hole, tree_law275 hole, tree_law276 hole, tree_law277 hole, tree_law278 hole, tree_law279 hole, tree_law280 hole, tree_law281 hole, tree_law282 hole, tree_law283 hole, tree_law284 hole, tree_law285 hole, tree_law286 hole, tree_law287 hole⟩,
   ⟨tree_law288 hole, tree_law289 hole, tree_law290 hole, tree_law291 hole, tree_law292 hole, tree_law293 hole, tree_law294 hole, tree_law295 hole, tree_law296 hole, tree_law297 hole, tree_law298 hole, tree_law299 hole, tree_law300 hole, tree_law301 hole, tree_law302 hole, tree_law303 hole⟩,
   ⟨tree_law304 hole, tree_law305 hole, tree_law306 hole, tree_law307 hole, tree_law308 hole, tree_law309 hole, tree_law310 hole, tree_law311 hole, tree_law312 hole, tree_law313 hole, tree_law314 hole, tree_law315 hole, tree_law316 hole, tree_law317 hole, tree_law318 hole, tree_law319 hole⟩,
   ⟨tree_law320 hole, tree_law321 hole, tree_law322 hole, tree_law323 hole, tree_law324 hole, tree_law325 hole, tree_law326 hole, tree_law327 hole, tree_law328 hole, tree_law329 hole, tree_law330 hole, tree_law331 hole, tree_law332 hole, tree_law333 hole, tree_law334 hole, tree_law335 hole⟩,
   ⟨tree_law336 hole, tree_law337 hole, tree_law338 hole, tree_law339 hole, tree_law340 hole, tree_law341 hole, tree_law342 hole, tree_law343 hole, tree_law344 hole, tree_law345 hole, tree_law346 hole, tree_law347 hole, tree_law348 hole, tree_law349 hole, tree_law350 hole, tree_law351 hole⟩,
   ⟨tree_law352 hole, tree_law353 hole, tree_law354 hole, tree_law355 hole, tree_law356 hole, tree_law357 hole, tree_law358 hole, tree_law359 hole, tree_law360 hole, tree_law361 hole, tree_law362 hole, tree_law363 hole, tree_law364 hole, tree_law365 hole, tree_law366 hole, tree_law367 hole⟩,
   ⟨tree_law368 hole, tree_law369 hole, tree_law370 hole, tree_law371 hole, tree_law372 hole, tree_law373 hole, tree_law374 hole, tree_law375 hole, tree_law376 hole, tree_law377 hole, tree_law378 hole, tree_law379 hole, tree_law380 hole, tree_law381 hole, tree_law382 hole, tree_law383 hole⟩,
   ⟨tree_law384 hole, tree_law385 hole, tree_law386 hole, tree_law387 hole, tree_law388 hole, tree_law389 hole, tree_law390 hole, tree_law391 hole, tree_law392 hole, tree_law393 hole, tree_law394 hole, tree_law395 hole, tree_law396 hole, tree_law397 hole, tree_law398 hole, tree_law399 hole⟩,
   ⟨tree_law400 hole, tree_law401 hole, tree_law402 hole, tree_law403 hole, tree_law404 hole, tree_law405 hole, tree_law406 hole, tree_law407 hole, tree_law408 hole, tree_law409 hole, tree_law410 hole, tree_law411 hole, tree_law412 hole, tree_law413 hole, tree_law414 hole, tree_law415 hole⟩,
   ⟨tree_law416 hole, tree_law417 hole, tree_law418 hole, tree_law419 hole, tree_law420 hole, tree_law421 hole, tree_law422 hole, tree_law423 hole, tree_law424 hole, tree_law425 hole, tree_law426 hole, tree_law427 hole, tree_law428 hole, tree_law429 hole, tree_law430 hole, tree_law431 hole⟩,
   ⟨tree_law432 hole, tree_law433 hole, tree_law434 hole, tree_law435 hole, tree_law436 hole, tree_law437 hole, tree_law438 hole, tree_law439 hole, tree_law440 hole, tree_law441 hole, tree_law442 hole, tree_law443 hole, tree_law444 hole, tree_law445 hole, tree_law446 hole, tree_law447 hole⟩,
   ⟨tree_law448 hole, tree_law449 hole, tree_law450 hole, tree_law451 hole, tree_law452 hole, tree_law453 hole, tree_law454 hole, tree_law455 hole, tree_law456 hole, tree_law457 hole, tree_law458 hole, tree_law459 hole, tree_law460 hole, tree_law461 hole, tree_law462 hole, tree_law463 hole⟩,
   ⟨tree_law464 hole, tree_law465 hole, tree_law466 hole, tree_law467 hole, tree_law468 hole, tree_law469 hole, tree_law470 hole, tree_law471 hole, tree_law472 hole, tree_law473 hole, tree_law474 hole, tree_law475 hole, tree_law476 hole, tree_law477 hole, tree_law478 hole, tree_law479 hole⟩,
   ⟨tree_law480 hole, tree_law481 hole, tree_law482 hole, tree_law483 hole, tree_law484 hole, tree_law485 hole, tree_law486 hole, tree_law487 hole, tree_law488 hole, tree_law489 hole, tree_law490 hole, tree_law491 hole, tree_law492 hole, tree_law493 hole, tree_law494 hole, tree_law495 hole⟩,
   ⟨tree_law496 hole, tree_law497 hole, tree_law498 hole, tree_law499 hole, tree_law500 hole, tree_law501 hole, tree_law502 hole, tree_law503 hole, tree_law504 hole, tree_law505 hole, tree_law506 hole, tree_law507 hole, tree_law508 hole, tree_law509 hole, tree_law510 hole⟩⟩

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := tree_passes true

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := tree_passes false

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by decide

end TblGap
