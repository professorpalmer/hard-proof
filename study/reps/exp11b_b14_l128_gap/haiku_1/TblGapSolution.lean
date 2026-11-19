/-
Hard Proof, experiment 11. Adversary solution: the gap.

Two rules pass every law in `TblLaws.lean`, and they differ on one case.
The laws leave the case `input` uncovered, so designB may answer true there.
-/
import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule. -/
def designA : Decide :=
  fun c =>
    (c.b0 && c.b3 && !c.b6 && !c.b7 && !c.b8 && !c.b9 && !c.b10 && !c.b11 && !c.b13)
    || (c.b0 && c.b2 && c.b4 && c.b5 && c.b6 && c.b8 && c.b9 && c.b10 && !c.b11 && !c.b13)
    || (!c.b0 && c.b1 && c.b2 && !c.b5 && !c.b13)
    || (c.b0 && !c.b1 && c.b4 && !c.b5 && c.b9 && !c.b12 && !c.b13)
    || (c.b0 && c.b1 && c.b2 && c.b3 && c.b4 && c.b5 && !c.b6 && !c.b7 && c.b8 && c.b9 && c.b10 && !c.b11 && c.b12 && !c.b13)
    || (c.b0 && c.b2 && !c.b4 && c.b5 && c.b7 && c.b8 && c.b9 && c.b10 && !c.b11 && c.b12 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && !c.b3 && !c.b4 && !c.b5 && !c.b6 && !c.b7 && !c.b8 && !c.b9 && !c.b10 && c.b11 && !c.b12 && !c.b13)
    || (c.b0 && c.b4 && !c.b5 && c.b9 && !c.b11 && c.b12 && !c.b13)
    || (c.b0 && c.b3 && !c.b6 && c.b7 && !c.b8 && !c.b9 && !c.b10 && !c.b11 && !c.b13)
    || (c.b0 && c.b1 && !c.b2 && !c.b5 && c.b9 && !c.b12 && !c.b13)
    || (c.b0 && !c.b3 && !c.b4 && !c.b5 && !c.b6 && c.b7 && !c.b9 && !c.b10 && c.b11 && !c.b12 && !c.b13)
    || (c.b0 && c.b1 && c.b2 && c.b3 && c.b4 && c.b5 && !c.b6 && c.b7 && c.b8 && c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && c.b1 && !c.b2 && !c.b3 && c.b4 && c.b5 && !c.b6 && c.b7 && !c.b8 && !c.b9 && !c.b10 && c.b11 && !c.b12 && !c.b13)
    || (c.b0 && c.b1 && c.b2 && !c.b4 && c.b5 && !c.b7 && c.b8 && c.b9 && c.b10 && c.b11 && !c.b13)
    || (c.b0 && !c.b3 && c.b5 && !c.b6 && c.b7 && !c.b8 && !c.b9 && !c.b10 && !c.b11 && !c.b13)
    || (c.b0 && !c.b1 && c.b3 && !c.b4 && c.b5 && !c.b6 && c.b7 && !c.b8 && c.b9 && !c.b11 && !c.b12 && !c.b13)
    || (c.b0 && c.b1 && !c.b2 && !c.b3 && !c.b4 && c.b5 && !c.b6 && c.b7 && c.b8 && !c.b9 && !c.b10 && c.b11 && c.b12 && !c.b13)
    || (c.b2 && !c.b5 && !c.b10 && c.b12 && c.b13)
    || (c.b0 && !c.b2 && !c.b3 && c.b4 && c.b5 && !c.b6 && !c.b7 && !c.b9 && !c.b10 && c.b11 && !c.b12 && !c.b13)
    || (c.b0 && c.b1 && c.b3 && !c.b4 && c.b5 && !c.b8 && c.b9 && c.b11 && !c.b13)
    || (!c.b5 && !c.b8 && !c.b12 && c.b13)
    || (c.b0 && c.b6 && c.b8 && !c.b9 && !c.b10 && !c.b11 && !c.b13)
    || (c.b0 && c.b1 && !c.b2 && !c.b3 && !c.b4 && !c.b5 && !c.b6 && !c.b7 && !c.b9 && !c.b10 && c.b11 && !c.b12 && !c.b13)
    || (c.b0 && c.b2 && c.b3 && !c.b4 && c.b5 && !c.b6 && c.b7 && c.b8 && c.b9 && c.b10 && !c.b11 && !c.b12 && !c.b13)
    || (c.b0 && c.b1 && !c.b2 && !c.b3 && c.b4 && c.b5 && !c.b6 && c.b7 && c.b8 && !c.b9 && !c.b10 && c.b11 && c.b12 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && c.b4 && c.b5 && !c.b7 && c.b8 && c.b9 && c.b10 && c.b11 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && !c.b3 && !c.b4 && !c.b5 && c.b7 && c.b9 && !c.b11 && !c.b12 && !c.b13)
    || (c.b0 && !c.b1 && !c.b2 && c.b3 && !c.b4 && !c.b5 && c.b7 && c.b8 && c.b9 && !c.b12 && !c.b13)
    || (!c.b5 && c.b10 && c.b12 && c.b13)
    || (!c.b5 && c.b8 && !c.b12 && c.b13)
    || (c.b0 && c.b4 && c.b5 && !c.b6 && c.b8 && !c.b9 && !c.b10 && !c.b11 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && !c.b3 && !c.b4 && !c.b5 && !c.b7 && c.b8 && c.b9 && !c.b10 && !c.b12 && !c.b13)
    || (c.b0 && !c.b2 && !c.b3 && !c.b4 && c.b5 && !c.b6 && !c.b7 && !c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && !c.b2 && c.b5 && c.b8 && c.b9 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && c.b5 && c.b7 && c.b8 && c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && c.b1 && c.b2 && c.b5 && c.b6 && c.b7 && c.b8 && c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && c.b1 && !c.b2 && !c.b3 && !c.b4 && c.b5 && !c.b6 && c.b7 && !c.b8 && !c.b9 && !c.b10 && c.b11 && c.b12 && !c.b13)
    || (c.b0 && !c.b3 && !c.b9 && c.b10 && c.b11 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && c.b3 && !c.b4 && !c.b5 && c.b9 && !c.b12 && !c.b13)
    || (c.b0 && !c.b2 && !c.b3 && c.b4 && c.b5 && !c.b6 && !c.b7 && !c.b8 && !c.b9 && !c.b10 && c.b11 && c.b12 && !c.b13)
    || (c.b0 && c.b2 && c.b5 && c.b7 && c.b8 && c.b9 && c.b10 && c.b11 && !c.b13)
    || (c.b0 && c.b1 && !c.b4 && c.b5 && c.b7 && !c.b8 && c.b9 && !c.b11 && !c.b12 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && !c.b3 && !c.b4 && !c.b5 && !c.b6 && !c.b7 && c.b8 && !c.b9 && !c.b10 && c.b11 && !c.b12 && !c.b13)
    || (c.b0 && !c.b3 && c.b6 && c.b7 && !c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && c.b2 && c.b3 && c.b5 && c.b8 && c.b9 && !c.b10 && !c.b11 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && !c.b3 && !c.b4 && !c.b5 && !c.b7 && c.b9 && c.b10 && !c.b12 && !c.b13)
    || (c.b0 && c.b4 && c.b5 && !c.b8 && c.b9 && !c.b12 && !c.b13)
    || (c.b0 && c.b2 && c.b3 && c.b5 && !c.b6 && !c.b7 && c.b8 && c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && !c.b1 && !c.b2 && !c.b3 && !c.b4 && !c.b5 && c.b7 && c.b9 && !c.b12 && !c.b13)
    || (c.b0 && c.b2 && !c.b3 && c.b5 && !c.b6 && !c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && !c.b1 && !c.b2 && !c.b3 && !c.b4 && c.b5 && !c.b6 && c.b7 && !c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && c.b2 && !c.b4 && c.b5 && !c.b6 && !c.b7 && c.b8 && c.b9 && c.b10 && !c.b11 && !c.b13)
    || (c.b0 && !c.b1 && c.b2 && !c.b3 && !c.b4 && c.b5 && !c.b8 && c.b9 && c.b11 && !c.b13)
    || (c.b0 && c.b1 && c.b2 && !c.b3 && c.b4 && c.b5 && !c.b6 && !c.b7 && c.b8 && c.b9 && c.b10 && !c.b11 && c.b12 && !c.b13)
    || (!c.b0 && c.b1 && c.b2 && c.b5 && !c.b6 && !c.b13)
    || (c.b0 && c.b3 && c.b4 && c.b5 && !c.b9 && !c.b10 && c.b11 && !c.b13)
    || (!c.b0 && !c.b1 && c.b2 && c.b10 && !c.b13)
    || (c.b0 && !c.b1 && !c.b2 && !c.b3 && !c.b4 && !c.b5 && !c.b7 && c.b9 && !c.b12 && !c.b13)
    || (c.b0 && c.b4 && !c.b5 && !c.b6 && c.b8 && !c.b9 && !c.b10 && !c.b11 && !c.b13)
    || (c.b0 && c.b2 && c.b5 && c.b6 && !c.b7 && c.b8 && c.b9 && !c.b10 && c.b11 && !c.b13)
    || (c.b0 && c.b1 && c.b2 && !c.b5 && c.b9 && !c.b12 && !c.b13)
    || (c.b5 && c.b13)
    || (!c.b2 && !c.b5 && !c.b10 && c.b12 && c.b13)
    || (c.b0 && !c.b1 && !c.b2 && !c.b3 && !c.b4 && c.b5 && !c.b8 && c.b9 && c.b11 && !c.b13)
    || (!c.b0 && c.b1 && c.b2 && c.b5 && c.b6 && !c.b13)
    || (!c.b0 && !c.b1 && c.b2 && !c.b9 && !c.b10 && !c.b13)
    || (c.b0 && c.b1 && !c.b2 && !c.b3 && c.b4 && c.b5 && !c.b6 && c.b7 && c.b8 && !c.b9 && !c.b10 && c.b11 && !c.b12 && !c.b13)
    || false

/-- The second recovery rule. -/
def designB : Decide := fun c => designA c || (c.b0 && !c.b1 && c.b2 && !c.b3 && !c.b4 && c.b5 && c.b6 && c.b7 && c.b8 && c.b9 && c.b10 && !c.b11 && !c.b12 && !c.b13)

/-- The case on which the two rules differ. -/
def input : Case := { b0 := true, b1 := false, b2 := true, b3 := false, b4 := false, b5 := true, b6 := true, b7 := true, b8 := true, b9 := true, b10 := true, b11 := false, b12 := false, b13 := false }

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  unfold Passes Law0 Law1 Law2 Law3 Law4 Law5 Law6 Law7 Law8 Law9 Law10 Law11 Law12 Law13 Law14 Law15 Law16 Law17 Law18 Law19 Law20 Law21 Law22 Law23 Law24 Law25 Law26 Law27 Law28 Law29 Law30 Law31 Law32 Law33 Law34 Law35 Law36 Law37 Law38 Law39 Law40 Law41 Law42 Law43 Law44 Law45 Law46 Law47 Law48 Law49 Law50 Law51 Law52 Law53 Law54 Law55 Law56 Law57 Law58 Law59 Law60 Law61 Law62 Law63 Law64 Law65 Law66 Law67 Law68 Law69 Law70 Law71 Law72 Law73 Law74 Law75 Law76 Law77 Law78 Law79 Law80 Law81 Law82 Law83 Law84 Law85 Law86 Law87 Law88 Law89 Law90 Law91 Law92 Law93 Law94 Law95 Law96 Law97 Law98 Law99 Law100 Law101 Law102 Law103 Law104 Law105 Law106 Law107 Law108 Law109 Law110 Law111 Law112 Law113 Law114 Law115 Law116 Law117 Law118 Law119 Law120 Law121 Law122 Law123 Law124 Law125 Law126
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro c
    intros
    simp_all [designA]

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes Law0 Law1 Law2 Law3 Law4 Law5 Law6 Law7 Law8 Law9 Law10 Law11 Law12 Law13 Law14 Law15 Law16 Law17 Law18 Law19 Law20 Law21 Law22 Law23 Law24 Law25 Law26 Law27 Law28 Law29 Law30 Law31 Law32 Law33 Law34 Law35 Law36 Law37 Law38 Law39 Law40 Law41 Law42 Law43 Law44 Law45 Law46 Law47 Law48 Law49 Law50 Law51 Law52 Law53 Law54 Law55 Law56 Law57 Law58 Law59 Law60 Law61 Law62 Law63 Law64 Law65 Law66 Law67 Law68 Law69 Law70 Law71 Law72 Law73 Law74 Law75 Law76 Law77 Law78 Law79 Law80 Law81 Law82 Law83 Law84 Law85 Law86 Law87 Law88 Law89 Law90 Law91 Law92 Law93 Law94 Law95 Law96 Law97 Law98 Law99 Law100 Law101 Law102 Law103 Law104 Law105 Law106 Law107 Law108 Law109 Law110 Law111 Law112 Law113 Law114 Law115 Law116 Law117 Law118 Law119 Law120 Law121 Law122 Law123 Law124 Law125 Law126
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro c
    intros
    simp_all [designB, designA]

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by
  decide

end TblGap
