import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The rule from the laws. The missing leaf takes the value `hole`. -/
def base (hole : Bool) (c : Case) : Bool :=
    if c.b13 then
      if c.b5 then
        true
      else
        if c.b12 then
          if c.b10 then
            true
          else
            if c.b2 then
              true
            else
              true
        else
          if c.b8 then
            true
          else
            true
    else
      if c.b0 then
        if c.b9 then
          if c.b5 then
            if c.b8 then
              if c.b2 then
                if c.b10 then
                  if c.b11 then
                    if c.b7 then
                      true
                    else
                      if c.b1 then
                        if c.b4 then
                          false
                        else
                          true
                      else
                        if c.b4 then
                          true
                        else
                          false
                  else
                    if c.b4 then
                      if c.b6 then
                        true
                      else
                        if c.b12 then
                          if c.b1 then
                            if c.b3 then
                              if c.b7 then
                                false
                              else
                                true
                            else
                              if c.b7 then
                                false
                              else
                                true
                          else
                            if c.b3 then
                              if c.b7 then
                                false
                              else
                                false
                            else
                              false
                        else
                          if c.b7 then
                            false
                          else
                            false
                    else
                      if c.b7 then
                        if c.b12 then
                          true
                        else
                          if c.b3 then
                            if c.b6 then
                              hole
                            else
                              true
                          else
                            if c.b6 then
                              hole
                            else
                              false
                      else
                        if c.b6 then
                          false
                        else
                          true
                else
                  if c.b11 then
                    if c.b7 then
                      if c.b1 then
                        if c.b6 then
                          true
                        else
                          if c.b4 then
                            if c.b3 then
                              true
                            else
                              false
                          else
                            false
                      else
                        true
                    else
                      if c.b6 then
                        true
                      else
                        if c.b3 then
                          true
                        else
                          false
                  else
                    if c.b3 then
                      true
                    else
                      false
              else
                true
            else
              if c.b4 then
                if c.b12 then
                  false
                else
                  true
              else
                if c.b11 then
                  if c.b1 then
                    if c.b3 then
                      true
                    else
                      false
                  else
                    if c.b3 then
                      false
                    else
                      if c.b2 then
                        true
                      else
                        true
                else
                  if c.b7 then
                    if c.b1 then
                      if c.b12 then
                        false
                      else
                        true
                    else
                      if c.b12 then
                        false
                      else
                        if c.b3 then
                          if c.b6 then
                            false
                          else
                            true
                        else
                          false
                  else
                    false
          else
            if c.b12 then
              if c.b4 then
                if c.b11 then
                  false
                else
                  true
              else
                false
            else
              if c.b1 then
                if c.b2 then
                  true
                else
                  true
              else
                if c.b4 then
                  true
                else
                  if c.b2 then
                    if c.b3 then
                      true
                    else
                      if c.b7 then
                        if c.b11 then
                          false
                        else
                          true
                      else
                        if c.b10 then
                          true
                        else
                          if c.b8 then
                            true
                          else
                            false
                  else
                    if c.b3 then
                      if c.b7 then
                        if c.b8 then
                          true
                        else
                          false
                      else
                        false
                    else
                      if c.b7 then
                        true
                      else
                        true
        else
          if c.b10 then
            if c.b3 then
              false
            else
              if c.b11 then
                true
              else
                false
          else
            if c.b11 then
              if c.b3 then
                if c.b5 then
                  if c.b4 then
                    true
                  else
                    false
                else
                  false
              else
                if c.b6 then
                  if c.b7 then
                    true
                  else
                    if c.b12 then
                      if c.b5 then
                        false
                      else
                        false
                    else
                      false
                else
                  if c.b5 then
                    if c.b2 then
                      true
                    else
                      if c.b4 then
                        if c.b7 then
                          if c.b1 then
                            if c.b8 then
                              if c.b12 then
                                true
                              else
                                true
                            else
                              if c.b12 then
                                false
                              else
                                true
                          else
                            false
                        else
                          if c.b12 then
                            if c.b8 then
                              false
                            else
                              true
                          else
                            true
                      else
                        if c.b7 then
                          if c.b1 then
                            if c.b8 then
                              if c.b12 then
                                true
                              else
                                false
                            else
                              if c.b12 then
                                true
                              else
                                false
                          else
                            true
                        else
                          true
                  else
                    if c.b4 then
                      false
                    else
                      if c.b12 then
                        if c.b2 then
                          false
                        else
                          false
                      else
                        if c.b7 then
                          true
                        else
                          if c.b1 then
                            if c.b2 then
                              false
                            else
                              true
                          else
                            if c.b2 then
                              if c.b8 then
                                true
                              else
                                true
                            else
                              if c.b8 then
                                false
                              else
                                false
            else
              if c.b6 then
                if c.b8 then
                  true
                else
                  if c.b4 then
                    false
                  else
                    false
              else
                if c.b8 then
                  if c.b4 then
                    if c.b5 then
                      true
                    else
                      true
                  else
                    if c.b7 then
                      false
                    else
                      false
                else
                  if c.b3 then
                    if c.b7 then
                      true
                    else
                      true
                  else
                    if c.b5 then
                      if c.b7 then
                        true
                      else
                        false
                    else
                      false
      else
        if c.b2 then
          if c.b1 then
            if c.b5 then
              if c.b6 then
                true
              else
                true
            else
              true
          else
            if c.b10 then
              true
            else
              if c.b9 then
                false
              else
                true
        else
          if c.b4 then
            if c.b11 then
              false
            else
              if c.b12 then
                false
              else
                false
          else
            if c.b7 then
              if c.b5 then
                false
              else
                false
            else
              false

/-- The first recovery rule. -/
def designA : Decide := base true

/-- The second recovery rule. -/
def designB : Decide := base false

/-- The case on which the two rules differ. -/
def input : Case := ⟨true, false, true, false, false, true, true, true, true, true, true, false, false, false⟩

theorem base_passes (hole : Bool) : Passes (base hole) := by
  unfold Passes Law0 Law1 Law2 Law3 Law4 Law5 Law6 Law7 Law8 Law9 Law10 Law11 Law12 Law13 Law14 Law15 Law16 Law17 Law18 Law19 Law20 Law21 Law22 Law23 Law24 Law25 Law26 Law27 Law28 Law29 Law30 Law31 Law32 Law33 Law34 Law35 Law36 Law37 Law38 Law39 Law40 Law41 Law42 Law43 Law44 Law45 Law46 Law47 Law48 Law49 Law50 Law51 Law52 Law53 Law54 Law55 Law56 Law57 Law58 Law59 Law60 Law61 Law62 Law63 Law64 Law65 Law66 Law67 Law68 Law69 Law70 Law71 Law72 Law73 Law74 Law75 Law76 Law77 Law78 Law79 Law80 Law81 Law82 Law83 Law84 Law85 Law86 Law87 Law88 Law89 Law90 Law91 Law92 Law93 Law94 Law95 Law96 Law97 Law98 Law99 Law100 Law101 Law102 Law103 Law104 Law105 Law106 Law107 Law108 Law109 Law110 Law111 Law112 Law113 Law114 Law115 Law116 Law117 Law118 Law119 Law120 Law121 Law122 Law123 Law124 Law125 Law126
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c <;> intros <;> simp_all [base]

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := base_passes true

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := base_passes false

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by decide

end TblGap
